#!/usr/bin/env python3
"""
Parse Header.lean and convert all definitions, axioms, and theorems into JSONL format.
Output schema: {"name": str, "code": str, "category": str}
"""

import json
import re
from pathlib import Path


def parse_header_lean(file_path):
    """Parse Header.lean and extract axioms, definitions, and theorems."""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()

    entries = []

    # Split into lines for processing
    lines = content.split('\n')
    i = 0

    while i < len(lines):
        line = lines[i].strip()

        # Skip empty lines and imports
        if not line or line.startswith('import') or line.startswith('--'):
            i += 1
            continue

        # Parse inductive types
        if line.startswith('inductive '):
            # Collect the full inductive definition
            full_inductive = line
            j = i + 1

            # Collect all lines until we hit another top-level declaration
            while j < len(lines):
                next_line = lines[j]
                # Check if we've hit a new declaration (no leading space)
                if next_line.strip() and not next_line.startswith(' ') and not next_line.startswith('|'):
                    break
                # Add line to inductive definition
                if next_line.strip():
                    full_inductive += '\n' + next_line
                j += 1

            # Extract name
            match = re.match(r'inductive\s+(\w+)', line)
            if match:
                name = match.group(1)
                entries.append({
                    "name": name,
                    "code": full_inductive,
                    "category": "inductive"
                })

                # Also add constructors (zero and succ) separately as requested
                if name == "MyNat":
                    entries.append({
                        "name": "zero",
                        "code": "zero : MyNat",
                        "category": "constructor"
                    })
                    entries.append({
                        "name": "succ",
                        "code": "succ : MyNat → MyNat",
                        "category": "constructor"
                    })
            i = j
            continue

        # Parse axioms
        if line.startswith('axiom '):
            # Extract the full axiom declaration
            full_line = line
            # Check if declaration continues on next lines (unlikely for axioms, but just in case)
            j = i + 1
            while j < len(lines) and not lines[j].strip().startswith(('axiom', 'def', 'theorem', 'opaque', 'instance', 'inductive', 'namespace', 'end')):
                if lines[j].strip():
                    full_line += ' ' + lines[j].strip()
                    j += 1
                else:
                    break

            # Extract name
            match = re.match(r'axiom\s+(\w+)', line)
            if match:
                name = match.group(1)
                entries.append({
                    "name": name,
                    "code": full_line,
                    "category": "axiom"
                })
            i = j if j > i + 1 else i + 1
            continue

        # Parse definitions
        if line.startswith('def '):
            # Collect the full definition
            full_def = line
            j = i + 1

            # Collect all lines until we hit another top-level declaration
            while j < len(lines):
                next_line = lines[j]
                # Check if we've hit a new declaration
                if next_line.strip() and not next_line.startswith(' ') and not next_line.startswith('|'):
                    break
                # Add line to definition if it's part of the definition body
                if next_line.strip():
                    full_def += '\n' + next_line
                j += 1

            # Extract name
            match = re.match(r'def\s+(\w+)', line)
            if match:
                name = match.group(1)
                entries.append({
                    "name": name,
                    "code": full_def,
                    "category": "def"
                })
            i = j
            continue

        # Parse theorems
        if line.startswith('theorem '):
            # Collect the full theorem
            full_theorem = line
            j = i + 1

            # Collect all lines until we hit another top-level declaration
            while j < len(lines):
                next_line = lines[j]
                # Check if we've hit a new declaration
                if next_line.strip() and not next_line.startswith(' ') and re.match(r'^(theorem|axiom|def|opaque|instance|inductive|namespace|end)\s', next_line):
                    break
                # Add line to theorem
                if next_line.strip():
                    full_theorem += '\n' + next_line
                j += 1

            # Extract name
            match = re.match(r'theorem\s+(\w+)', line)
            if match:
                name = match.group(1)
                entries.append({
                    "name": name,
                    "code": full_theorem,
                    "category": "theorem"
                })
            i = j
            continue

        # Parse opaque declarations (like add, mul, pow)
        if line.startswith('opaque '):
            match = re.match(r'opaque\s+(\w+)\s*:\s*(.+)', line)
            if match:
                name = match.group(1)
                entries.append({
                    "name": name,
                    "code": line,
                    "category": "opaque"
                })
            i += 1
            continue

        # Parse instance declarations
        if line.startswith('instance'):
            # Collect the full instance
            full_instance = line
            j = i + 1

            # Collect all lines until we hit another top-level declaration
            while j < len(lines):
                next_line = lines[j]
                # Check if we've hit a new declaration
                if next_line.strip() and not next_line.startswith(' '):
                    break
                # Add line to instance
                if next_line.strip():
                    full_instance += '\n' + next_line
                j += 1

            # Extract name if it has one, otherwise use a generic name
            match = re.match(r'instance\s+(\w+)', line)
            if match:
                name = match.group(1)
            else:
                # For anonymous instances, extract the type
                if 'Add' in line:
                    name = 'instAdd'
                elif 'Mul' in line:
                    name = 'instMul'
                elif 'Pow' in line:
                    name = 'instPow'
                elif 'LE' in line:
                    name = 'instLE'
                elif 'LT' in line:
                    name = 'instLT'
                elif 'Inhabited' in line:
                    name = 'instInhabited'
                else:
                    name = f'instance_{i}'

            entries.append({
                "name": name,
                "code": full_instance,
                "category": "instance"
            })
            i = j
            continue

        i += 1

    return entries


def write_jsonl(entries, output_file):
    """Write entries to JSONL file."""
    with open(output_file, 'w', encoding='utf-8') as f:
        for entry in entries:
            f.write(json.dumps(entry, ensure_ascii=False) + '\n')


def create_header_definitions(output_dir=None, verbose=True):
    """
    Parse Header.lean and create header_definitions.jsonl.

    Args:
        output_dir: Directory to write the output file (default: dataset/original)
        verbose: Whether to print progress messages

    Returns:
        Path to the created header_definitions.jsonl file
    """
    if output_dir is None:
        output_dir = Path("dataset/original")

    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)

    header_file = Path("MyNNG/MyNNG/Header.lean")
    output_file = output_dir / "header_definitions.jsonl"

    if not header_file.exists():
        raise FileNotFoundError(f"{header_file} not found")

    if verbose:
        print(f"Parsing {header_file}...")

    entries = parse_header_lean(header_file)
    write_jsonl(entries, output_file)

    if verbose:
        # Print a few examples
        print("\nExample entries:")
        for entry in entries[:5]:
            print(f"  {entry['name']} ({entry['category']})")

    return output_file


def main():
    """Main entry point for command-line usage."""
    try:
        output_file = create_header_definitions(verbose=True)
        print(f"\n✓ Successfully created {output_file}")
    except Exception as e:
        print(f"✗ Error: {e}")
        import sys
        sys.exit(1)


if __name__ == "__main__":
    main()
