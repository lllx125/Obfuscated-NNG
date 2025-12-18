#!/usr/bin/env python3
"""
Parse Lean theorem files (except Header.lean) and convert them into JSONL format for LLM training.
Output schema: {"id": int, "name": str, "statement": str, "proof": str, "known_theorems": list}
"""

import json
import re
from pathlib import Path
from typing import List, Dict, Set


def extract_imports(file_path):
    """Extract import statements from a Lean file."""
    imports = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line in f:
            line = line.strip()
            if line.startswith('import '):
                # Extract the module name (e.g., "MyNNG.Addition" from "import MyNNG.Addition")
                match = re.match(r'import\s+([\w.]+)', line)
                if match:
                    module = match.group(1)
                    # Skip Header since we handle it separately
                    if not module.endswith('.Header'):
                        imports.append(module)
            elif line.startswith('open '):
                # Stop at 'open' statement
                break
    return imports


def module_to_file_path(module_name, base_dir):
    """Convert module name to file path (e.g., MyNNG.Addition -> MyNNG/MyNNG/Addition.lean)."""
    parts = module_name.split('.')
    file_path = base_dir / '/'.join(parts[:-1]) / f"{parts[-1]}.lean"
    return file_path


def parse_theorems_from_file(file_path):
    """
    Parse theorems from a Lean file.
    Assumptions:
    - All theorems start with 'theorem'
    - All theorems are separated by 1 empty line
    - All statements are on the same line
    - Proofs start on the next line
    - First theorem starts 2 lines after 'open MyNat'
    """
    theorems = []

    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    # Find where theorems start (2 lines after "open MyNat")
    start_idx = 0
    for i, line in enumerate(lines):
        if line.strip().startswith('open '):
            start_idx = i + 2
            break

    i = start_idx
    while i < len(lines):
        line = lines[i].strip()

        # Look for theorem declarations
        if line.startswith('theorem '):
            # Extract the theorem name
            match = re.match(r'theorem\s+(\w+)', line)
            if not match:
                i += 1
                continue

            name = match.group(1)
            statement = line  # The entire theorem declaration line

            # Collect the proof (all lines until next theorem or end of file)
            proof_lines = []
            j = i + 1

            while j < len(lines):
                proof_line = lines[j].rstrip()
                # Check if we've hit the next theorem or end
                if lines[j].strip().startswith('theorem '):
                    break
                # Check if line is empty (separator between theorems)
                if lines[j].strip() == '':
                    # Check if next non-empty line is a theorem
                    k = j + 1
                    while k < len(lines) and lines[k].strip() == '':
                        k += 1
                    if k < len(lines) and lines[k].strip().startswith('theorem '):
                        break
                    else:
                        # This empty line is part of the proof
                        proof_lines.append(proof_line)
                        j += 1
                        continue

                proof_lines.append(proof_line)
                j += 1

            # Clean up the proof: remove leading/trailing empty lines
            while proof_lines and not proof_lines[0].strip():
                proof_lines.pop(0)
            while proof_lines and not proof_lines[-1].strip():
                proof_lines.pop()

            proof = '\n'.join(proof_lines)

            theorems.append({
                'name': name,
                'statement': statement,
                'proof': proof
            })

            i = j
        else:
            i += 1

    return theorems


def get_all_known_theorems(file_path, base_dir, visited=None):
    """
    Recursively get all known theorems from imports.
    Returns a list of theorem statements (no duplicates).
    """
    if visited is None:
        visited = set()

    # Avoid circular imports
    file_path_str = str(file_path)
    if file_path_str in visited:
        return []
    visited.add(file_path_str)

    known_theorems = []

    # Get imports
    imports = extract_imports(file_path)

    # Recursively get theorems from imported files
    for imp in imports:
        imp_file = module_to_file_path(imp, base_dir)
        if imp_file.exists():
            # Get theorems from imported file (recursively)
            imported_theorems = get_all_known_theorems(imp_file, base_dir, visited)
            known_theorems.extend(imported_theorems)

            # Get theorems defined in the imported file itself
            theorems = parse_theorems_from_file(imp_file)
            for thm in theorems:
                known_theorems.append(thm['statement'])

    return known_theorems


def parse_file_to_jsonl(file_path, base_dir):
    """Parse a single Lean file and convert to JSONL entries."""
    entries = []

    # Get all known theorems from imports (recursively)
    all_known_theorems = get_all_known_theorems(file_path, base_dir)

    # Remove duplicates while preserving order
    seen = set()
    known_theorems_unique = []
    for thm in all_known_theorems:
        if thm not in seen:
            seen.add(thm)
            known_theorems_unique.append(thm)

    # Parse theorems in this file
    theorems = parse_theorems_from_file(file_path)

    # Create entries for each theorem
    current_known = known_theorems_unique.copy()

    for idx, theorem in enumerate(theorems, start=1):
        entry = {
            "id": idx,
            "name": theorem['name'],
            "statement": theorem['statement'],
            "proof": theorem['proof'],
            "known_theorems": current_known.copy()
        }
        entries.append(entry)

        # Add this theorem to known theorems for the next theorem
        current_known.append(theorem['statement'])

    return entries


def create_theorems_dataset(output_dir=None, verbose=True):
    """
    Parse Lean theorem files and create theorems.jsonl.

    Args:
        output_dir: Directory to write the output file (default: dataset/original)
        verbose: Whether to print progress messages

    Returns:
        Path to the created theorems.jsonl file
    """
    if output_dir is None:
        output_dir = Path("dataset/original")

    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    base_dir = Path("MyNNG")
    lean_dir = base_dir / "MyNNG"
    output_file = output_dir / "theorems.jsonl"

    # Specific file order to guarantee dependencies
    file_order = [
        "Addition.lean",
        "Implication.lean",
        "Algorithm.lean",
        "Multiplication.lean",
        "Power.lean",
        "AdvAddition.lean",
        "LessOrEqual.lean",
        "AdvMultiplication.lean"
    ]

    # Build list of files in the specified order
    lean_files = []
    for filename in file_order:
        file_path = lean_dir / filename
        if file_path.exists():
            lean_files.append(file_path)
        else:
            if verbose:
                print(f"Warning: {filename} not found, skipping")

    if verbose:
        print(f"\nProcessing {len(lean_files)} Lean files (in dependency order):")
        for f in lean_files:
            print(f"  - {f.name}")

    # Process all files
    all_entries = []
    global_id = 1

    for lean_file in lean_files:
        if verbose:
            print(f"\nProcessing {lean_file.name}...")
        entries = parse_file_to_jsonl(lean_file, base_dir)

        # Update global IDs
        for entry in entries:
            entry['id'] = global_id
            global_id += 1

        all_entries.extend(entries)
        if verbose:
            print(f"  Extracted {len(entries)} theorems")

    # Write to JSONL
    with open(output_file, 'w', encoding='utf-8') as f:
        for entry in all_entries:
            f.write(json.dumps(entry, ensure_ascii=False) + '\n')

    if verbose:
        print(f"\n✓ Written {len(all_entries)} theorem entries to {output_file}")

        # Print a sample
        if all_entries:
            print("\nSample entry (first theorem):")
            sample = all_entries[0]
            print(f"ID: {sample['id']}")
            print(f"Name: {sample['name']}")
            print(f"Statement: {sample['statement']}")
            print(f"Proof preview: {sample['proof'][:100]}...")
            print(f"Known theorems: {len(sample['known_theorems'])} items")

    return output_file


def main():
    """Main entry point for command-line usage."""
    try:
        output_file = create_theorems_dataset(verbose=True)
        print(f"\n✓ Successfully created {output_file}")
    except Exception as e:
        print(f"✗ Error: {e}")
        import sys
        sys.exit(1)


if __name__ == "__main__":
    main()
