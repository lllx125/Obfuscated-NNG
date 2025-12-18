#!/usr/bin/env python3
"""
Test the canonical tactic's ability to solve theorems from the dataset.
"""

import json
import re
import subprocess
import sys
from pathlib import Path
from typing import List, Dict, Set, Tuple

# Import functions from jsonl_verifier for reuse
sys.path.insert(0, str(Path(__file__).parent / 'verification'))
from jsonl_verifier import (
    load_jsonl,
    get_inductive_type_name,
    write_inductive_definition,
    write_header_definitions_in_namespace
)


def analyze_statement(statement: str) -> Set[str]:
    """Analyze the theorem statement to determine which operations are used."""
    operations = set()

    # Check for operations in statement
    if 'add' in statement:
        operations.add('add')
    if 'mul' in statement:
        operations.add('mul')
    if 'pow' in statement:
        operations.add('pow')
    if '≠' in statement or ' ≠ ' in statement:
        operations.add('neq')
    if '∃' in statement or 'exists' in statement.lower():
        operations.add('exists')
    if ' ∨ ' in statement or 'Or' in statement:
        operations.add('or')
    if ' ∧ ' in statement or 'And' in statement:
        operations.add('and')
    if 'le ' in statement or ' le(' in statement or ': le' in statement or '≤' in statement:
        operations.add('le')

    return operations


def get_base_premises() -> List[str]:
    """Get the base premises that are always included."""
    return ['MyNat.rec', 'Eq.refl', 'Eq.rec', 'succ_inj']


def get_premises_for_theorem(statement: str) -> List[str]:
    """Determine which premises to include for a theorem based on its statement."""
    premises = get_base_premises()
    operations = analyze_statement(statement)

    # Add operation-specific axioms
    if 'add' in operations:
        premises.extend(['add_succ', 'add_zero'])

    if 'mul' in operations:
        premises.extend(['mul_succ', 'mul_zero'])

    if 'pow' in operations:
        premises.extend(['pow_succ', 'pow_zero'])

    if 'neq' in operations:
        premises.extend(['False.rec', 'zero_ne_succ'])

    if 'exists' in operations:
        premises.extend(['Exists.intro', 'Exists.elim'])

    if 'or' in operations:
        premises.extend(['Or.inl', 'Or.inr', 'Or.elim'])

    if 'and' in operations:
        premises.extend(['And.intro', 'And.left', 'And.right'])

    if 'le' in operations:
        # le requires exists and add axioms
        if 'Exists.intro' not in premises:
            premises.extend(['Exists.intro', 'Exists.elim'])
        if 'add_succ' not in premises:
            premises.extend(['add_succ', 'add_zero'])
        premises.append('le')

    return premises


def obfuscate_premise(premise: str, name_map: Dict[str, str], dataset_name: str) -> str:
    """
    Obfuscate a premise name using the name mapping.

    Special handling for MyNat.rec which needs to use MyNat's name mapping.
    Other axioms use the name map, and names not in the map stay the same.
    """
    if premise == 'MyNat.rec':
        # Special handling for MyNat.rec
        mynat_name = name_map.get('MyNat', 'MyNat')
        return f'{mynat_name}.rec'

    # For other premises, use name mapping if available, otherwise keep original
    return name_map.get(premise, premise)


def load_name_mapping(filepath: str) -> Dict[str, str]:
    """Load name mapping from a JSON file."""
    with open(filepath, 'r') as f:
        return json.load(f)


def generate_all_premises(theorems: List[Dict]) -> List[List[str]]:
    """Generate premise lists for all theorems."""
    all_premises = []
    for theorem in theorems:
        premises = get_premises_for_theorem(theorem['statement'])
        all_premises.append(premises)
    return all_premises


def create_canonical_lean_file(
    dataset_name: str,
    header_entries: List[Dict],
    theorems: List[Dict],
    name_map: Dict[str, str],
    all_premises: List[List[str]],
    output_file: Path
) -> Path:
    """
    Create a Lean file with canonical tactics for a dataset.
    Reuses structure from jsonl_verifier.py but uses canonical instead of proofs.
    """
    # Get the inductive type name
    type_name = get_inductive_type_name(header_entries)
    if not type_name:
        print("Error: Could not find inductive type in header definitions")
        return None

    # Create output directory if it doesn't exist
    output_file.parent.mkdir(parents=True, exist_ok=True)

    with open(output_file, 'w') as f:
        # Write imports
        f.write("import Mathlib.Tactic.ApplyAt\n")
        f.write("import Mathlib.Tactic.NthRewrite\n")
        f.write("import Mathlib.Tactic.Contrapose\n")
        f.write("import Mathlib.Tactic.Use\n")
        f.write("import Mathlib.Tactic.Tauto\n")
        f.write("import Canonical\n\n")

        # Write inductive type definition (BEFORE namespace)
        write_inductive_definition(f, header_entries)

        # Write namespace
        f.write(f'namespace {type_name}\n\n')

        # Write all other header definitions (INSIDE namespace)
        write_header_definitions_in_namespace(f, header_entries)

        # Write open statement
        f.write(f'open {type_name}\n\n')

        # Write all theorems with canonical tactic
        for i, theorem in enumerate(theorems):
            # Get obfuscated premises
            original_premises = all_premises[i]
            obfuscated_premises = [
                obfuscate_premise(p, name_map, dataset_name)
                for p in original_premises
            ]

            # Format premises for canonical
            premises_str = ', '.join(obfuscated_premises)

            # Write theorem with canonical tactic
            f.write(f"-- Theorem {theorem['id']}: {theorem['name']}\n")
            f.write(f"{theorem['statement']}\n")
            f.write(f"  canonical 15 [{premises_str}]\n\n")

        # Close namespace
        f.write(f'end {type_name}\n')

    return output_file


def verify_lean_file(lean_file: Path) -> Tuple[bool, List[int], str]:
    """
    Verify a Lean file and return success status, failed theorem IDs, and output.
    Adapted from jsonl_verifier.py's verification approach.

    Returns:
        Tuple of (success, failed_theorem_ids, output)
    """
    try:
        # Run lake env lean on the file from the MyNNG directory
        project_dir = Path("/home/ubuntu/Obfuscated-NNG/MyNNG")
        relative_path = lean_file.relative_to(project_dir)

        result = subprocess.run(
            ['lake', 'env', 'lean', str(relative_path)],
            cwd=project_dir,
            capture_output=True,
            text=True,
            timeout=600  # 10 minute timeout
        )

        output = result.stdout + result.stderr

        # Parse output to find failed theorems
        failed_ids = []

        # Look for line numbers with errors (adapted from jsonl_verifier pattern)
        error_pattern = re.compile(r'Canonical_\w+\.lean:(\d+):\d+:\s*error')
        error_lines = []

        for match in error_pattern.finditer(output):
            line_num = int(match.group(1))
            error_lines.append(line_num)

        if error_lines:
            # Map line numbers to theorem IDs
            with open(lean_file, 'r') as f:
                lines = f.readlines()

            for error_line in error_lines:
                line_idx = error_line - 1  # 0-indexed
                # Search backwards from error line to find theorem comment
                for i in range(line_idx, -1, -1):
                    match = re.match(r'-- Theorem (\d+):', lines[i])
                    if match:
                        theorem_id = int(match.group(1))
                        if theorem_id not in failed_ids:
                            failed_ids.append(theorem_id)
                        break

        success = result.returncode == 0 and len(failed_ids) == 0
        return success, failed_ids, output

    except subprocess.TimeoutExpired:
        return False, [], "Timeout during verification"
    except Exception as e:
        return False, [], f"Error during verification: {str(e)}"


def replace_failed_with_sorry(lean_file: Path, failed_ids: List[int], theorems: List[Dict]) -> None:
    """Replace failed canonical tactics with sorry."""
    with open(lean_file, 'r') as f:
        content = f.read()

    # For each failed theorem, replace canonical with sorry
    for theorem_id in failed_ids:
        # Find the theorem by its comment
        pattern = rf'-- Theorem {theorem_id}:.*?\n(.*?)\n  canonical 15 \[.*?\]'

        def replace_with_sorry(match):
            return match.group(0).rsplit('canonical', 1)[0] + 'sorry'

        content = re.sub(pattern, replace_with_sorry, content, flags=re.DOTALL)

    with open(lean_file, 'w') as f:
        f.write(content)


def test_canonical_on_dataset(dataset_path: Path) -> Dict:
    """Test canonical on a single dataset."""

    dataset_name = dataset_path.name
    print(f"\n{'='*60}")
    print(f"Testing dataset: {dataset_name}")
    print(f"{'='*60}")

    # Load header definitions
    header_file = dataset_path / 'header_definitions.jsonl'
    if not header_file.exists():
        print(f"Error: {header_file} not found")
        return None

    header_entries = load_jsonl(header_file)
    print(f"Loaded {len(header_entries)} header definitions")

    # Load theorems
    theorems_file = dataset_path / 'theorems.jsonl'
    if not theorems_file.exists():
        print(f"Error: {theorems_file} not found")
        return None

    theorems = load_jsonl(theorems_file)
    print(f"Loaded {len(theorems)} theorems")

    # Load name mapping
    if dataset_name == 'original':
        # Create identity mapping for original
        name_map = {}
        for entry in header_entries:
            name = entry.get('name')
            if name:
                name_map[name] = name
        # Add standard Lean library names
        name_map['MyNat'] = 'MyNat'
    else:
        name_mapping_file = dataset_path / 'name_mapping.json'
        if not name_mapping_file.exists():
            print(f"Error: {name_mapping_file} not found")
            return None
        name_map = load_name_mapping(name_mapping_file)

    # Generate premises for all theorems
    all_premises = generate_all_premises(theorems)

    # Create Lean file in canonical_tests subfolder
    output_file = Path(f'/home/ubuntu/Obfuscated-NNG/MyNNG/MyNNG/canonical_tests/Canonical_{dataset_name}.lean')
    lean_file = create_canonical_lean_file(
        dataset_name,
        header_entries,
        theorems,
        name_map,
        all_premises,
        output_file
    )

    if not lean_file:
        return None

    print(f"Created Lean file: {lean_file}")

    # Verify the file
    print("Verifying with Lean...")
    success, failed_ids, output = verify_lean_file(lean_file)

    # If there are failures, replace with sorry
    if failed_ids:
        print(f"Found {len(failed_ids)} failed theorems: {failed_ids}")
        replace_failed_with_sorry(lean_file, failed_ids, theorems)
        print("Replaced failed theorems with sorry")

    return {
        'dataset': dataset_name,
        'total_theorems': len(theorems),
        'failed_theorems': len(failed_ids),
        'failed_ids': sorted(failed_ids),
        'success_rate': (len(theorems) - len(failed_ids)) / len(theorems) * 100,
        'lean_file': str(lean_file)
    }


def main():
    """Main function to test canonical on all datasets."""

    print("Canonical Tactic Ability Test")
    print("="*60)

    # Dataset paths
    dataset_base = Path('/home/ubuntu/Obfuscated-NNG/dataset')
    datasets = [
        'original',
        'obfuscated_1',
        'obfuscated_2',
        'obfuscated_3',
        'obfuscated_4',
        'obfuscated_5'
    ]

    results = []

    # Test each dataset
    for dataset_name in datasets:
        dataset_path = dataset_base / dataset_name
        if not dataset_path.exists():
            print(f"Warning: Dataset {dataset_name} not found, skipping...")
            continue

        result = test_canonical_on_dataset(dataset_path)
        if result:
            results.append(result)

    # Print summary
    print("\n" + "="*60)
    print("SUMMARY")
    print("="*60)
    print(f"{'Dataset':<20} {'Total':<10} {'Failed':<10} {'Success Rate':<15}")
    print("-"*60)

    for result in results:
        print(f"{result['dataset']:<20} {result['total_theorems']:<10} "
              f"{result['failed_theorems']:<10} {result['success_rate']:.1f}%")

    # Print failed theorem IDs for each dataset
    print("\n" + "="*60)
    print("FAILED THEOREM IDs BY DATASET")
    print("="*60)

    for result in results:
        if result['failed_ids']:
            print(f"\n{result['dataset']}:")
            print(f"  Failed IDs: {result['failed_ids']}")
        else:
            print(f"\n{result['dataset']}: All theorems passed!")

    # Save results to JSON
    results_file = Path('/home/ubuntu/Obfuscated-NNG/canonical_test_results.json')
    with open(results_file, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\n\nDetailed results saved to: {results_file}")


if __name__ == '__main__':
    main()
