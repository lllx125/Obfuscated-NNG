#!/usr/bin/env python3
"""
Test the canonical tactic's ability to solve theorems from the dataset.
"""

import json
import re
import subprocess
import sys
import time
from pathlib import Path
from typing import List, Dict, Set, Tuple

# Import functions from jsonl_verifier for reuse
sys.path.insert(0, str(Path(__file__).parent / 'verification'))
from verification.jsonl_verifier import (
    load_jsonl,
    get_inductive_type_name,
    write_inductive_definition,
    write_header_definitions_in_namespace
)

# Import Discord notification
sys.path.insert(0, str(Path(__file__).parent / 'utils'))
from utils.discord_notify import send_msg

# Global configuration
CANONICAL_TIMEOUT = 15  # seconds to wait for canonical to finish


def analyze_original_statement(statement: str) -> Set[str]:
    """
    Analyze the ORIGINAL theorem statement to determine which operations are used.
    This must be called on the original statement, not the obfuscated one.
    """
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


def get_theorems_used_in_proof(proof: str, all_theorem_names: List[str]) -> List[str]:
    """
    Identify which previous theorems are referenced in a proof.

    Args:
        proof: The proof text to analyze
        all_theorem_names: List of all available theorem names

    Returns:
        List of theorem names that appear in the proof
    """
    used_theorems = []

    for theorem_name in all_theorem_names:
        # Check if theorem name appears in the proof
        # Use word boundaries to avoid partial matches
        pattern = r'\b' + re.escape(theorem_name) + r'\b'
        if re.search(pattern, proof):
            used_theorems.append(theorem_name)

    return used_theorems


def get_premises_for_original_theorem(statement: str, proof: str, previous_theorem_names: List[str]) -> List[str]:
    """
    Determine which premises to include for a theorem based on the ORIGINAL statement and proof.
    This is the key function that should be called only on original theorems.

    Args:
        statement: The theorem statement
        proof: The proof text
        previous_theorem_names: List of theorem names that have been defined before this one
    """
    premises = get_base_premises()
    operations = analyze_original_statement(statement)

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

    # Add theorems that are used in the proof
    used_theorems = get_theorems_used_in_proof(proof, previous_theorem_names)
    for theorem in used_theorems:
        if theorem not in premises:
            premises.append(theorem)

    return premises


def generate_premises_from_original(original_theorems: List[Dict]) -> List[List[str]]:
    """
    Generate premise lists for all theorems from the ORIGINAL dataset.
    Returns a list of lists where each inner list is the premises for one theorem.
    """
    all_premises = []
    previous_theorem_names = []

    for theorem in original_theorems:
        premises = get_premises_for_original_theorem(
            theorem['statement'],
            theorem['proof'],
            previous_theorem_names
        )
        all_premises.append(premises)
        previous_theorem_names.append(theorem['name'])

    return all_premises


def obfuscate_premise_list(premises: List[str], name_map: Dict[str, str]) -> List[str]:
    """
    Obfuscate a list of premise names using the name mapping.

    Special handling for MyNat.rec which needs to use MyNat's name mapping.
    Other axioms use the name map, and names not in the map stay the same.
    """
    obfuscated = []
    for premise in premises:
        if premise == 'MyNat.rec':
            # Special handling for MyNat.rec
            mynat_name = name_map.get('MyNat', 'MyNat')
            obfuscated.append(f'{mynat_name}.rec')
        else:
            # For other premises, use name mapping if available, otherwise keep original
            obfuscated.append(name_map.get(premise, premise))
    return obfuscated


def load_name_mapping(filepath: str) -> Dict[str, str]:
    """Load name mapping from a JSON file."""
    with open(filepath, 'r') as f:
        return json.load(f)


def create_canonical_lean_file(
    dataset_name: str,
    header_entries: List[Dict],
    theorems: List[Dict],
    obfuscated_premises_list: List[List[str]],
    output_file: Path
) -> Path:
    """
    Create a Lean file with canonical tactics for a dataset.

    Args:
        dataset_name: Name of the dataset
        header_entries: Header definitions from header_definitions.jsonl
        theorems: Theorem entries (can be original or obfuscated)
        obfuscated_premises_list: Already-obfuscated premise lists for each theorem
        output_file: Path to output file
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
            # Get the already-obfuscated premises for this theorem
            obfuscated_premises = obfuscated_premises_list[i]

            # Format premises for canonical
            premises_str = ', '.join(obfuscated_premises)

            # Write theorem with canonical tactic
            f.write(f"-- Theorem {theorem['id']}: {theorem['name']}\n")
            f.write(f"{theorem['statement']}\n")
            f.write(f"  canonical {CANONICAL_TIMEOUT} [{premises_str}]\n\n")

        # Close namespace
        f.write(f'end {type_name}\n')

    return output_file

def verify_lean_file(lean_file: Path, num_theorems: int) -> Tuple[bool, List[int], str]:
    """
    Verify a Lean file using 'lake build' to ensure it waits for the full Canonical search.
    """
    try:
        # 1. Setup paths
        # Ensure we are in the root MyNNG directory where lakefile.toml/lean-toolchain are
        project_dir = Path("/home/ubuntu/Obfuscated-NNG/MyNNG")
        
        # Determine the module name for lake build (e.g., MyNNG.canonical_tests.Canonical_original)
        # This is more robust than a file path for lake build
        module_path = lean_file.stem  # Gets 'Canonical_original'
        module_name = f"MyNNG.canonical_tests.{module_path}"

        # 2. Configure Timeout
        # lake build is blocking. We wait (15s * N) + overhead.
        total_timeout = (15 * num_theorems) + 60

        print(f"  Wait: Actively searching via 'lake build' for {module_name}...")

        # 3. Execute 'lake build' from the project directory
        # This will stay alive until every 'by canonical' is either solved or fails.
        result = subprocess.run(
            ['lake', 'build', module_name],
            cwd=project_dir,
            capture_output=True,
            text=True,
            timeout=total_timeout
        )

        full_output = result.stdout + result.stderr

        # 4. Parse output for failures
        # Pattern: error: MyNNG/canonical_tests/Canonical_original.lean:155:2: No proof found.
        # We need to extract the line number (155) from this format
        failed_ids = []
        error_pattern = re.compile(r'error:.*?:(\d+):\d+:\s*No proof found', re.IGNORECASE)

        error_lines = [int(match.group(1)) for match in error_pattern.finditer(full_output)]

        if error_lines:
            with open(lean_file, 'r') as f:
                file_lines = f.readlines()
            for error_line in error_lines:
                # Lean line numbers are 1-indexed
                line_idx = error_line - 1
                # Search backwards for the theorem ID comment
                for i in range(line_idx, -1, -1):
                    match = re.match(r'-- Theorem (\d+):', file_lines[i])
                    if match:
                        tid = int(match.group(1))
                        if tid not in failed_ids:
                            failed_ids.append(tid)
                        break

        # 5. Determine success
        # Build fails (exit code 1) if a proof is not found.
        success = (result.returncode == 0) and (len(failed_ids) == 0)
        
        return success, failed_ids, full_output

    except subprocess.TimeoutExpired:
        return False, [], "BUILD TIMEOUT: Search exceeded the total allowed time."
    except Exception as e:
        return False, [], f"System Error: {str(e)}"

def generate_lean_file_for_dataset(
    dataset_path: Path,
    original_premises_list: List[List[str]]
) -> Tuple[Path, List[Dict], int]:
    """
    Generate Lean file for a dataset (without verification).

    Args:
        dataset_path: Path to the dataset
        original_premises_list: List of premise lists from the original dataset

    Returns:
        Tuple of (lean_file_path, theorems, num_theorems) or (None, None, 0) on error
    """

    dataset_name = dataset_path.name
    print(f"\n{'='*60}")
    print(f"Generating file for dataset: {dataset_name}")
    print(f"{'='*60}")

    # Load header definitions
    header_file = dataset_path / 'header_definitions.jsonl'
    if not header_file.exists():
        print(f"Error: {header_file} not found")
        return None, None, 0

    header_entries = load_jsonl(header_file)
    print(f"Loaded {len(header_entries)} header definitions")

    # Load theorems
    theorems_file = dataset_path / 'theorems.jsonl'
    if not theorems_file.exists():
        print(f"Error: {theorems_file} not found")
        return None, None, 0

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
        name_map['MyNat'] = 'MyNat'
    else:
        name_mapping_file = dataset_path / 'name_mapping.json'
        if not name_mapping_file.exists():
            print(f"Error: {name_mapping_file} not found")
            return None, None, 0
        name_map = load_name_mapping(name_mapping_file)

    # Obfuscate the premises list
    obfuscated_premises_list = []
    for original_premises in original_premises_list:
        obfuscated = obfuscate_premise_list(original_premises, name_map)
        obfuscated_premises_list.append(obfuscated)

    # Create Lean file in canonical_tests subfolder
    output_file = Path(f'/home/ubuntu/Obfuscated-NNG/MyNNG/MyNNG/canonical_tests/Canonical_{dataset_name}.lean')
    lean_file = create_canonical_lean_file(
        dataset_name,
        header_entries,
        theorems,
        obfuscated_premises_list,
        output_file
    )

    if not lean_file:
        return None, None, 0

    print(f"Created Lean file: {lean_file}")

    return lean_file, theorems, len(theorems)


def verify_dataset(
    dataset_name: str,
    lean_file: Path,
    theorems: List[Dict],
    num_theorems: int
) -> Dict:
    """
    Verify a generated Lean file for a dataset.

    Args:
        dataset_name: Name of the dataset
        lean_file: Path to the generated Lean file
        theorems: List of theorem entries
        num_theorems: Number of theorems in the file

    Returns:
        Dictionary with verification results
    """
    print(f"\n{'='*60}")
    print(f"Verifying dataset: {dataset_name}")
    print(f"{'='*60}")

    # Verify the file
    success, failed_ids, output = verify_lean_file(lean_file, num_theorems)

    # Report results
    if failed_ids:
        print(f"Found {len(failed_ids)} failed theorems (No proof found): {failed_ids}")
    else:
        print("All theorems passed!")

    return {
        'dataset': dataset_name,
        'total_theorems': num_theorems,
        'failed_theorems': len(failed_ids),
        'failed_ids': sorted(failed_ids),
        'success_rate': (num_theorems - len(failed_ids)) / num_theorems * 100,
        'lean_file': str(lean_file)
    }


def check_results_consistency(results: List[Dict]) -> bool:
    """
    Check if all datasets have identical failed theorem IDs.

    Returns:
        True if all datasets have identical results, False otherwise
    """
    if not results:
        return True

    # Get the first dataset's failed IDs as reference
    reference_failed_ids = set(results[0]['failed_ids'])

    # Compare all other datasets
    all_identical = True
    for result in results[1:]:
        if set(result['failed_ids']) != reference_failed_ids:
            all_identical = False
            break

    return all_identical


def main():
    """Main function to test canonical on all datasets."""

    start_time = time.time()

    # Send Discord notification that job started
    send_msg("🚀 **Canonical Tactic Test Started**\n"
             f"Testing canonical tactic on 6 datasets (68 theorems each)\n"
             f"Timeout: {CANONICAL_TIMEOUT}s per theorem\n"
             f"Estimated time: ~{CANONICAL_TIMEOUT * 68 // 60} minutes per dataset")

    print("Canonical Tactic Ability Test")
    print(f"Canonical timeout: {CANONICAL_TIMEOUT} seconds per theorem")
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

    try:
        # Step 1: Load original theorems and generate premises from them
        print("\nStep 1: Generating premises from ORIGINAL dataset...")
        original_path = dataset_base / 'original'
        original_theorems_file = original_path / 'theorems.jsonl'

        if not original_theorems_file.exists():
            print(f"Error: {original_theorems_file} not found")
            sys.exit(1)

        original_theorems = load_jsonl(original_theorems_file)
        print(f"Loaded {len(original_theorems)} original theorems")

        # Generate premises from original theorems
        original_premises_list = generate_premises_from_original(original_theorems)
        print(f"Generated premise lists for {len(original_premises_list)} theorems")

        # Step 2: Generate all Lean files first
        print("\n" + "="*60)
        print("Step 2: Generating all Lean files...")
        print("="*60)

        generated_files = {}  # dataset_name -> (lean_file, theorems, num_theorems)

        for dataset_name in datasets:
            dataset_path = dataset_base / dataset_name
            if not dataset_path.exists():
                print(f"Warning: Dataset {dataset_name} not found, skipping...")
                continue

            lean_file, theorems, num_theorems = generate_lean_file_for_dataset(
                dataset_path,
                original_premises_list
            )

            if lean_file:
                generated_files[dataset_name] = (lean_file, theorems, num_theorems)

        send_msg(f"📝 Generated {len(generated_files)} Lean files\n"
                f"Starting verification (each dataset takes ~{CANONICAL_TIMEOUT * len(original_theorems)} seconds)...")

        # Step 3: Verify all generated files
        print("\n" + "="*60)
        print("Step 3: Verifying all generated files...")
        print(f"This will take approximately {CANONICAL_TIMEOUT * len(original_theorems)} seconds per dataset")
        print("="*60)

        results = []

        for dataset_name, (lean_file, theorems, num_theorems) in generated_files.items():
            result = verify_dataset(dataset_name, lean_file, theorems, num_theorems)
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

        # Check if all datasets have identical results
        print("\n" + "="*60)
        print("CONSISTENCY CHECK")
        print("="*60)

        is_consistent = check_results_consistency(results)

        if is_consistent:
            print("✅ All datasets have IDENTICAL failed theorem IDs")
            consistency_msg = "✅ **Consistent Results**: All datasets failed on the same theorems"
        else:
            print("❌ WARNING: Datasets have DIFFERENT failed theorem IDs!")
            print("\nDifferences found:")
            for i, result in enumerate(results):
                print(f"  {result['dataset']}: {result['failed_ids']}")
            consistency_msg = "⚠️ **Inconsistent Results**: Datasets failed on different theorems!"

        # Save results to JSON
        results_file = Path('/home/ubuntu/Obfuscated-NNG/canonical_test_results.json')
        with open(results_file, 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\n\nDetailed results saved to: {results_file}")

        # Calculate total elapsed time
        elapsed_time = time.time() - start_time
        hours, remainder = divmod(int(elapsed_time), 3600)
        minutes, seconds = divmod(remainder, 60)
        time_str = f"{hours}h {minutes}m {seconds}s" if hours > 0 else f"{minutes}m {seconds}s"

        # Prepare summary for Discord
        total_failed = sum(r['failed_theorems'] for r in results)
        avg_success_rate = sum(r['success_rate'] for r in results) / len(results)

        summary_msg = (
            f"✅ **Canonical Tactic Test Complete**\n"
            f"⏱️ Time: {time_str}\n"
            f"📊 **Results Summary**:\n"
            f"  - Total datasets: {len(results)}\n"
            f"  - Total theorems: {results[0]['total_theorems']} per dataset\n"
            f"  - Average success rate: {avg_success_rate:.1f}%\n"
            f"  - Total failures: {total_failed}\n"
            f"\n{consistency_msg}\n"
        )

        # Add per-dataset breakdown
        summary_msg += "\n**Per-Dataset Results**:\n"
        for result in results:
            emoji = "✅" if result['failed_theorems'] == 0 else "❌"
            summary_msg += f"{emoji} `{result['dataset']}`: {result['failed_theorems']} failed ({result['success_rate']:.1f}% pass)\n"

        if total_failed > 0 and is_consistent:
            # Show which theorems failed
            failed_ids = results[0]['failed_ids']
            summary_msg += f"\n**Failed Theorem IDs** (consistent across all datasets):\n`{failed_ids}`"

        send_msg(summary_msg)

    except Exception as e:
        # Send error notification
        import traceback
        error_msg = "".join(traceback.format_exception(type(e), e, e.__traceback__))
        send_msg(f"🚨 **Canonical Test CRASHED**\n```python\n{error_msg[:1500]}\n```")
        raise


if __name__ == '__main__':
    main()
