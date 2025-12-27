#!/usr/bin/env python3
"""
Patch obfuscated datasets to fix name mismatches introduced during obfuscation.

The obfuscation process can introduce mismatches between the 'name' field and the
actual name used in the 'statement' or 'code' field. This script fixes these
mismatches by updating the 'name' field to match what's in the code, and updates
the name_mapping.json accordingly.
"""

import json
import re
import sys
from pathlib import Path
from typing import Dict, List, Tuple


def load_jsonl(file_path: Path) -> List[Dict]:
    """Load JSONL file into a list of dictionaries."""
    entries = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                entries.append(json.loads(line))
    return entries


def save_jsonl(entries: List[Dict], file_path: Path):
    """Save entries to JSONL file."""
    with open(file_path, 'w', encoding='utf-8') as f:
        for entry in entries:
            f.write(json.dumps(entry, ensure_ascii=False) + '\n')


def extract_name_from_theorem_statement(statement: str) -> str:
    """
    Extract theorem name from a theorem statement.

    Args:
        statement: Theorem statement (e.g., "theorem add_comm (a b : MyNat) : ...")

    Returns:
        Theorem name extracted from the statement
    """
    match = re.search(r'theorem\s+([\w\u0370-\u03FF\u2100-\u214F\']+)', statement)
    if match:
        return match.group(1)
    raise ValueError(f"Could not extract theorem name from statement: {statement[:80]}")


def extract_name_from_code(code: str, category: str) -> str:
    """
    Extract name from header code based on category.

    Args:
        code: The code string
        category: The category (inductive, axiom, def, theorem, instance, opaque)

    Returns:
        Extracted name from the code
    """
    patterns = {
        'inductive': r'inductive\s+([\w\u0370-\u03FF\u2100-\u214F\']+)',
        'axiom': r'axiom\s+([\w\u0370-\u03FF\u2100-\u214F\']+)',
        'def': r'def\s+([\w\u0370-\u03FF\u2100-\u214F\']+)',
        'theorem': r'theorem\s+([\w\u0370-\u03FF\u2100-\u214F\']+)',
        'instance': r'instance\s+([\w\u0370-\u03FF\u2100-\u214F\']+)',
        'opaque': r'opaque\s+([\w\u0370-\u03FF\u2100-\u214F\']+)',
    }

    if category not in patterns:
        raise ValueError(f"Cannot extract name for category: {category}")

    match = re.search(patterns[category], code)
    if match:
        return match.group(1)
    raise ValueError(f"Could not extract name from {category} code: {code[:80]}")


def patch_theorems(theorems_file: Path, verbose: bool = True) -> Tuple[int, Dict[str, str]]:
    """
    Patch theorems.jsonl to fix name mismatches.

    Args:
        theorems_file: Path to theorems.jsonl file
        verbose: Whether to print progress messages

    Returns:
        Tuple of (num_fixed, name_corrections) where name_corrections is a dict
        mapping old names to new names
    """
    if not theorems_file.exists():
        raise FileNotFoundError(f"Theorems file not found: {theorems_file}")

    # Load theorems
    theorems = load_jsonl(theorems_file)

    # Check for mismatches and fix them
    num_fixed = 0
    name_corrections = {}

    for i, entry in enumerate(theorems):
        statement = entry['statement']
        name_field = entry['name']

        # Extract name from statement
        try:
            stmt_name = extract_name_from_theorem_statement(statement)
        except ValueError as e:
            if verbose:
                print(f"Warning: {e}")
            continue

        # Check if there's a mismatch
        if name_field != stmt_name:
            if verbose:
                print(f"  Fixed theorem {i+1}: '{name_field}' -> '{stmt_name}'")
            name_corrections[name_field] = stmt_name
            entry['name'] = stmt_name
            num_fixed += 1

    # Save the patched file
    if num_fixed > 0:
        save_jsonl(theorems, theorems_file)

    return num_fixed, name_corrections


def patch_header_definitions(header_file: Path, verbose: bool = True) -> Tuple[int, Dict[str, str]]:
    """
    Patch header_definitions.jsonl to fix name mismatches.

    Args:
        header_file: Path to header_definitions.jsonl file
        verbose: Whether to print progress messages

    Returns:
        Tuple of (num_fixed, name_corrections) where name_corrections is a dict
        mapping old names to new names
    """
    if not header_file.exists():
        raise FileNotFoundError(f"Header file not found: {header_file}")

    # Load header definitions
    headers = load_jsonl(header_file)

    # Check for mismatches and fix them
    num_fixed = 0
    name_corrections = {}

    for i, entry in enumerate(headers):
        code = entry['code']
        name_field = entry['name']
        category = entry['category']

        # Skip constructors - they don't have a declaration
        if category == 'constructor':
            continue

        # Extract name from code
        try:
            code_name = extract_name_from_code(code, category)
        except ValueError as e:
            if verbose:
                print(f"Warning: {e}")
            continue

        # Check if there's a mismatch
        if name_field != code_name:
            if verbose:
                print(f"  Fixed {category} {i+1}: '{name_field}' -> '{code_name}'")
            name_corrections[name_field] = code_name
            entry['name'] = code_name
            num_fixed += 1

    # Save the patched file
    if num_fixed > 0:
        save_jsonl(headers, header_file)

    return num_fixed, name_corrections


def update_name_mapping(mapping_file: Path, corrections: Dict[str, str], verbose: bool = True):
    """
    Update name_mapping.json with corrections.

    Args:
        mapping_file: Path to name_mapping.json file
        corrections: Dict mapping old obfuscated names to corrected obfuscated names
        verbose: Whether to print progress messages
    """
    if not mapping_file.exists():
        if verbose:
            print(f"Warning: Name mapping file not found: {mapping_file}")
        return

    # Load name mapping
    with open(mapping_file, 'r', encoding='utf-8') as f:
        name_mapping = json.load(f)

    # Update the mapping: for each original name, if its obfuscated name
    # was corrected, update it
    num_updated = 0
    for original_name, obfuscated_name in name_mapping.items():
        if obfuscated_name in corrections:
            new_name = corrections[obfuscated_name]
            name_mapping[original_name] = new_name
            num_updated += 1
            if verbose:
                print(f"  Updated mapping: {original_name} -> {new_name} (was {obfuscated_name})")

    # Save the updated mapping
    if num_updated > 0:
        with open(mapping_file, 'w', encoding='utf-8') as f:
            json.dump(name_mapping, f, indent=2, ensure_ascii=False)
        if verbose:
            print(f"Updated {num_updated} entries in name_mapping.json")


def patch_dataset(dataset_dir: Path, verbose: bool = True) -> bool:
    """
    Patch a dataset to fix name mismatches.

    Args:
        dataset_dir: Path to dataset directory (e.g., dataset/obfuscated_1)
        verbose: Whether to print progress messages

    Returns:
        True if any fixes were made, False otherwise
    """
    dataset_dir = Path(dataset_dir)

    if not dataset_dir.exists():
        raise FileNotFoundError(f"Dataset directory not found: {dataset_dir}")

    if verbose:
        print(f"\nPatching dataset: {dataset_dir}")

    all_corrections = {}
    total_fixed = 0

    # Patch theorems
    theorems_file = dataset_dir / "theorems.jsonl"
    if theorems_file.exists():
        if verbose:
            print("Checking theorems.jsonl...")
        num_fixed, corrections = patch_theorems(theorems_file, verbose=verbose)
        total_fixed += num_fixed
        all_corrections.update(corrections)
        if verbose and num_fixed > 0:
            print(f"Fixed {num_fixed} theorem name(s)")
        elif verbose:
            print("No mismatches found in theorems")

    # Patch header definitions
    header_file = dataset_dir / "header_definitions.jsonl"
    if header_file.exists():
        if verbose:
            print("\nChecking header_definitions.jsonl...")
        num_fixed, corrections = patch_header_definitions(header_file, verbose=verbose)
        total_fixed += num_fixed
        all_corrections.update(corrections)
        if verbose and num_fixed > 0:
            print(f"Fixed {num_fixed} header definition(s)")
        elif verbose:
            print("No mismatches found in headers")

    # Update name mapping
    if all_corrections:
        mapping_file = dataset_dir / "name_mapping.json"
        if verbose:
            print("\nUpdating name_mapping.json...")
        update_name_mapping(mapping_file, all_corrections, verbose=verbose)

    if verbose:
        if total_fixed > 0:
            print(f"\n✓ Patched {total_fixed} name(s) in {dataset_dir}")
        else:
            print(f"\n✓ No fixes needed for {dataset_dir}")

    return total_fixed > 0


def patch_all_datasets(verbose: bool = True) -> int:
    """
    Patch all obfuscated datasets.

    Args:
        verbose: Whether to print progress messages

    Returns:
        Total number of datasets patched
    """
    dataset_base = Path("dataset")

    if not dataset_base.exists():
        raise FileNotFoundError(f"Dataset directory not found: {dataset_base}")

    # Find all obfuscated datasets
    obfuscated_dirs = sorted(dataset_base.glob("obfuscated_*"))

    if not obfuscated_dirs:
        if verbose:
            print("No obfuscated datasets found")
        return 0

    if verbose:
        print(f"Found {len(obfuscated_dirs)} obfuscated dataset(s)")

    num_patched = 0
    for dataset_dir in obfuscated_dirs:
        try:
            was_patched = patch_dataset(dataset_dir, verbose=verbose)
            if was_patched:
                num_patched += 1
        except Exception as e:
            print(f"Error patching {dataset_dir}: {e}")
            if verbose:
                import traceback
                traceback.print_exc()

    if verbose:
        print(f"\n{'='*60}")
        print(f"✓ Patched {num_patched} dataset(s)")
        print(f"{'='*60}")

    return num_patched


def main():
    """Main entry point for the script."""
    import argparse

    parser = argparse.ArgumentParser(
        description="Patch obfuscated datasets to fix name mismatches"
    )
    parser.add_argument(
        "dataset",
        nargs="?",
        help="Dataset directory to patch (e.g., dataset/obfuscated_1). If not specified, patches all datasets."
    )
    parser.add_argument(
        "-q", "--quiet",
        action="store_true",
        help="Suppress progress messages"
    )

    args = parser.parse_args()

    try:
        if args.dataset:
            # Patch a specific dataset
            patch_dataset(Path(args.dataset), verbose=not args.quiet)
        else:
            # Patch all datasets
            patch_all_datasets(verbose=not args.quiet)

        sys.exit(0)

    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        if not args.quiet:
            import traceback
            traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
