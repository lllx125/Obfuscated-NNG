#!/usr/bin/env python3
"""
Verify individual dataset results by generating proofs and running verification.
Simplified interface for use with score_llm.py.
"""

import json
import sys
from pathlib import Path
from typing import Dict, List, Any

from verification.jsonl_generator import load_jsonl
from verification.lean_analyzer import analyze_lean_file


# Default Lean file output path
DEFAULT_OUTPUT_FILE = Path("MyNNG/MyNNG/Generated_Verification.lean")


def create_generated_proofs_file(
    result_file: Path,
    theorems_file: Path,
    output_file: Path
):
    """
    Create generated_proofs_n.jsonl file from result_n.jsonl and theorems.jsonl.

    Does line-by-line matching: takes JSON from theorem and replaces the "proof"
    property with "code" from result's JSON.

    Args:
        result_file: Path to result_n.jsonl
        theorems_file: Path to theorems.jsonl
        output_file: Path to output generated_proofs_n.jsonl
    """
    # Load results
    results = load_jsonl(result_file)

    # Load theorems
    theorems = load_jsonl(theorems_file)

    # If the lines don't match, use only the same number as the lines in result file
    num_lines = len(results)

    if len(results) != len(theorems):
        print(f"Warning: Number of results ({len(results)}) doesn't match theorems ({len(theorems)})")
        print(f"Using first {num_lines} entries")

    # Create generated proofs by matching line-by-line
    generated_proofs = []

    for i in range(num_lines):
        # Take JSON from theorem and replace "proof" property with "code" from result
        theorem = theorems[i] if i < len(theorems) else {}
        result = results[i]

        # Copy theorem entry and replace proof
        proof_entry = theorem.copy()
        proof_entry["proof"] = result.get("code", "sorry")

        generated_proofs.append(proof_entry)

    # Write to output file (overwrite if exists)
    with open(output_file, 'w', encoding='utf-8') as f:
        for entry in generated_proofs:
            f.write(json.dumps(entry, ensure_ascii=False))
            f.write('\n')

    print(f"Created {output_file} with {len(generated_proofs)} proofs")


def verify_dataset(
    header_path: str,
    theorems_path: str,
    verbose: bool = False,
    output_file: Path = DEFAULT_OUTPUT_FILE
) -> tuple:
    """
    Verify a dataset by header and theorems file paths.

    Args:
        header_path: Path to header_definitions.jsonl file
        theorems_path: Path to theorems.jsonl file
        verbose: Whether to print progress messages
        output_file: Path to output Lean file

    Returns:
        Tuple of (error_ids, sorry_ids, banned_tactics_usage, error_details):
        - error_ids: List of theorem IDs that have incorrect proofs
        - sorry_ids: List of theorem IDs that contain 'sorry' after successful verification
        - banned_tactics_usage: Dict mapping theorem IDs to lists of banned tactics used
        - error_details: Dict mapping theorem IDs to error messages from Lean
    """
    from verification.jsonl_generator import generate_lean_for_theorems

    header_path = Path(header_path)
    theorems_path = Path(theorems_path)

    # Check if input files exist
    if not header_path.exists():
        raise FileNotFoundError(f"{header_path} not found")

    if not theorems_path.exists():
        raise FileNotFoundError(f"{theorems_path} not found")

    # Load JSONL files
    if verbose:
        print(f"Loading {header_path}...")
    header_entries = load_jsonl(header_path)
    if verbose:
        print(f"  Loaded {len(header_entries)} header definitions")

    if verbose:
        print(f"\nLoading {theorems_path}...")
    theorems_entries = load_jsonl(theorems_path)
    if verbose:
        print(f"  Loaded {len(theorems_entries)} theorems")

    if verbose:
        print("\n" + "="*60)
        print("Starting verification...")
        print("="*60)

    # Generate initial Lean file
    generate_lean_for_theorems(header_entries, theorems_entries, output_file)

    # Analyze the Lean file
    analysis = analyze_lean_file(output_file, theorems_entries, header_entries)

    if verbose:
        print("\n" + "="*60)
        print("VERIFICATION COMPLETE")
        print("="*60)

        if analysis['error_ids']:
            print(f"\nFound {len(analysis['error_ids'])} theorem(s) with incorrect proofs:")
            print(f"  IDs: {analysis['error_ids']}")
        else:
            print("\n✓ All proofs are correct!")
            if analysis['sorry_ids']:
                print(f"\n⚠ Found {len(analysis['sorry_ids'])} proof(s) containing 'sorry':")
                print(f"  IDs: {analysis['sorry_ids']}")

        if analysis['banned_tactics_usage']:
            print(f"\n⚠ Found {len(analysis['banned_tactics_usage'])} proof(s) using banned tactics:")
            for theorem_id, tactics in sorted(analysis['banned_tactics_usage'].items()):
                print(f"  ID {theorem_id}: {', '.join(tactics)}")

        print("="*60)

    return analysis['error_ids'], analysis['sorry_ids'], analysis['banned_tactics_usage'], analysis['error_details']


def verify_individual_dataset(
    result_file: Path,
    repo_folder: str = ".",
    output_file: Path = DEFAULT_OUTPUT_FILE
) -> Dict[str, Any]:
    """
    Verify a single result file for a specific dataset.

    Args:
        result_file: Path to result_n.jsonl file (e.g., results/gpt-4o/obfuscated_1/result_1.jsonl)
        repo_folder: Repository root folder
        output_file: Path to output Lean file

    Returns:
        Dictionary with verification results:
        {
            "run": int,
            "total": int,
            "correct": int,
            "incorrect": int,
            "error_ids": List[int],
            "sorry_ids": List[int],
            "banned_tactics_usage": Dict[int, List[str]],
            "banned_count": int,
            "correct_rate": float,
            "error_details": Dict[int, str]
        }
    """
    repo_path = Path(repo_folder)
    result_file = Path(result_file)

    # Parse dataset name from path: results/llm_name/dataset_name/result_n.jsonl
    dataset_folder = result_file.parent
    dataset_name = dataset_folder.name
    run_num = int(result_file.stem.split('_')[1])

    # Get corresponding header and theorems files
    orig_dataset_path = repo_path / "dataset" / dataset_name
    header_file = orig_dataset_path / "header_definitions.jsonl"
    theorems_file = orig_dataset_path / "theorems.jsonl"

    if not header_file.exists():
        raise FileNotFoundError(f"Header file not found: {header_file}")

    if not theorems_file.exists():
        raise FileNotFoundError(f"Theorems file not found: {theorems_file}")

    # Create generated_proofs file
    generated_proofs_file = dataset_folder / f"generated_proofs_{run_num}.jsonl"
    create_generated_proofs_file(result_file, theorems_file, generated_proofs_file)

    # Verify the generated proofs
    print(f"Verifying {generated_proofs_file}...")
    error_ids, sorry_ids, banned_tactics_usage, error_details = verify_dataset(
        str(header_file),
        str(generated_proofs_file),
        verbose=False,
        output_file=output_file
    )

    # Load generated proofs to count total
    generated_proofs = load_jsonl(generated_proofs_file)
    total_proofs = len(generated_proofs)

    # Count unique incorrect IDs (some IDs may appear in both error_ids and sorry_ids)
    incorrect_ids = set(error_ids) | set(sorry_ids)
    incorrect_count = len(incorrect_ids)
    correct_count = total_proofs - incorrect_count
    correct_rate = correct_count / total_proofs if total_proofs > 0 else 0.0

    # Count banned tactics usage
    banned_count = len(banned_tactics_usage) if banned_tactics_usage else 0

    # Return results
    return {
        "run": run_num,
        "total": total_proofs,
        "correct": correct_count,
        "incorrect": incorrect_count,
        "error_ids": error_ids,
        "sorry_ids": sorry_ids,
        "banned_tactics_usage": banned_tactics_usage,
        "banned_count": banned_count,
        "correct_rate": correct_rate,
        "error_details": error_details
    }


def main():
    """
    Main function to verify a single dataset result.
    Usage: python -m verification.verify_individual results/gpt-4o/obfuscated_1/result_1.jsonl
    """
    if len(sys.argv) < 2:
        print("Usage: python -m verification.verify_individual <result_file>")
        print("Example: python -m verification.verify_individual results/gpt-4o/obfuscated_1/result_1.jsonl")
        print("\nThe dataset name is automatically parsed from the file path.")
        sys.exit(1)

    result_file = sys.argv[1]

    print(f"Verifying {result_file}...")

    try:
        stats = verify_individual_dataset(result_file)

        # Print results
        print(f"\n{'='*60}")
        print(f"VERIFICATION RESULTS")
        print(f"{'='*60}")
        print(f"Total proofs: {stats['total']}")
        print(f"Correct: {stats['correct']}")
        print(f"Incorrect: {stats['incorrect']}")
        print(f"Correct rate: {stats['correct_rate']*100:.2f}%")

        if stats['banned_count'] > 0:
            print(f"⚠ Using banned tactics: {stats['banned_count']}")

        if stats['error_ids']:
            print(f"\nError IDs: {stats['error_ids']}")

        if stats['sorry_ids']:
            print(f"Sorry IDs: {stats['sorry_ids']}")

        if stats['banned_tactics_usage']:
            print(f"\nBanned tactics usage:")
            for proof_id, tactics in stats['banned_tactics_usage'].items():
                print(f"  ID {proof_id}: {', '.join(tactics)}")

        if stats['error_details']:
            print(f"\nError details:")
            for proof_id, error_msg in stats['error_details'].items():
                # Truncate long error messages
                error_preview = error_msg[:150] + "..." if len(error_msg) > 150 else error_msg
                print(f"  ID {proof_id}: {error_preview}")

        print(f"{'='*60}")

    except Exception as e:
        print(f"Error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    main()
