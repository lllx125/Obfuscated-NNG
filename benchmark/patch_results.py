#!/usr/bin/env python3
"""
Patch Results Script
Scans result files for "sorry" responses and retries them using the LLM.
"""

import json
import os
import sys
import time
from pathlib import Path
from typing import Dict, List, Tuple

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from benchmark.llm_interface import ModelInterface


def load_jsonl(file_path: Path) -> List[Dict]:
    """Load a JSONL file into a list of dictionaries."""
    entries = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                entries.append(json.loads(line))
    return entries


def save_jsonl(file_path: Path, entries: List[Dict]):
    """Save a list of dictionaries to a JSONL file."""
    with open(file_path, 'w', encoding='utf-8') as f:
        for entry in entries:
            f.write(json.dumps(entry, ensure_ascii=False))
            f.write('\n')


def find_sorry_entries(results: List[Dict]) -> List[Tuple[int, Dict]]:
    """
    Find all entries where the "code" field is exactly "sorry" (failed LLM responses).
    Does NOT match code that contains "sorry" as part of a valid proof.

    Returns:
        List of tuples (line_number, entry) where line_number is 0-indexed
    """
    sorry_entries = []
    for idx, entry in enumerate(results):
        code = entry.get("code", "").strip()
        # Only match if code is EXACTLY "sorry" (case-insensitive)
        # This catches failed LLM responses but not proofs that use sorry as a tactic
        if code.lower() == "sorry":
            sorry_entries.append((idx, entry))
    return sorry_entries


def scan_all_sorry_entries(repo_folder: str = ".") -> Dict[str, List]:
    """
    Scan all LLM results and report 'sorry' entries without patching.

    Returns:
        Dictionary mapping llm_name -> list of sorry entry info
    """
    repo_path = Path(repo_folder)
    results_base = repo_path / "results"

    if not results_base.exists():
        print(f"Results folder not found: {results_base}")
        return {}

    all_sorry_info = {}

    # Find all LLM folders
    llm_folders = [f for f in results_base.iterdir() if f.is_dir()]

    for llm_folder in sorted(llm_folders):
        llm_name = llm_folder.name
        sorry_list = []

        # Find all dataset folders
        dataset_folders = [f for f in llm_folder.iterdir() if f.is_dir()]

        for dataset_folder in sorted(dataset_folders):
            dataset_name = dataset_folder.name

            # Find all result files
            result_files = sorted(dataset_folder.glob("result_*.jsonl"))

            for result_file in result_files:
                run_num = int(result_file.stem.split('_')[1])

                # Load results
                results = load_jsonl(result_file)

                # Find sorry entries
                sorry_entries = find_sorry_entries(results)

                for line_idx, entry in sorry_entries:
                    sorry_list.append({
                        'dataset': dataset_name,
                        'run': run_num,
                        'line_idx': line_idx,
                        'theorem_id': line_idx,
                        'entry': entry
                    })

        if sorry_list:
            all_sorry_info[llm_name] = sorry_list

    return all_sorry_info


def patch_results(
    llm_name: str,
    max_retries: int = 3,
    repo_folder: str = ".",
    dry_run: bool = False
):
    """
    Scan all result files for a given LLM and patch "sorry" responses.

    Args:
        llm_name: The LLM name
        max_retries: Maximum number of retry attempts per sorry entry
        repo_folder: Repository root folder
        dry_run: If True, only report errors without attempting to fix
    """
    repo_path = Path(repo_folder)
    results_base = repo_path / "results" / llm_name
    dataset_base = repo_path / "dataset"

    if not results_base.exists():
        print(f"Results folder not found: {results_base}")
        return

    # Check if this is a local model
    is_local_model = llm_name in ["deepseek-prover-v2-local", "goedel-prover-v2"]

    if is_local_model and not dry_run:
        print(f"[!] WARNING: {llm_name} is a local model - skipping patch (requires GPU)")
        dry_run = True

    # Initialize the model interface only if not in dry_run mode
    engine = None
    if not dry_run:
        print(f"[*] Initializing Model: {llm_name}")
        try:
            engine = ModelInterface(llm_name, max_retry=max_retries)
        except Exception as e:
            print(f"[!] Failed to initialize model: {e}")
            print(f"[!] Switching to dry-run mode")
            dry_run = True

    # Find all dataset folders
    dataset_folders = [f for f in results_base.iterdir() if f.is_dir()]

    total_patched = 0
    total_failed = 0

    for dataset_folder in dataset_folders:
        dataset_name = dataset_folder.name
        print(f"\n{'='*60}")
        print(f"Processing dataset: {dataset_name}")
        print(f"{'='*60}")

        # Get corresponding queries file
        queries_file = dataset_base / dataset_name / "queries.jsonl"

        if not queries_file.exists():
            print(f"Queries file not found: {queries_file}")
            continue

        # Load queries
        queries = load_jsonl(queries_file)

        # Find all result files
        result_files = sorted(dataset_folder.glob("result_*.jsonl"))

        if not result_files:
            print(f"No result files found in {dataset_folder}")
            continue

        for result_file in result_files:
            run_num = int(result_file.stem.split('_')[1])
            time_file = dataset_folder / f"time_{run_num}.json"

            print(f"\nProcessing Run {run_num}:")
            print(f"  Result file: {result_file}")

            # Load results and times
            results = load_jsonl(result_file)

            times = []
            if time_file.exists():
                with open(time_file, 'r') as f:
                    times = json.load(f)
            else:
                # Initialize times array if it doesn't exist
                times = [0.0] * len(results)

            # Find sorry entries
            sorry_entries = find_sorry_entries(results)

            if not sorry_entries:
                print(f"  No 'sorry' entries found in run {run_num}")
                continue

            print(f"  Found {len(sorry_entries)} 'sorry' entries")

            # First pass: Print all error IDs
            print(f"\n  Error IDs in run {run_num}:")
            for line_idx, entry in sorry_entries:
                if line_idx < len(queries):
                    query = queries[line_idx]
                    theorem_id = line_idx
                    if isinstance(query, list):
                        for msg in query:
                            if isinstance(msg, dict) and 'id' in msg:
                                theorem_id = msg['id']
                                break
                    elif isinstance(query, dict):
                        theorem_id = query.get('id', line_idx)

                    print(f"    - Line {line_idx}, Theorem ID: {theorem_id}")

            # If dry run, skip patching
            if dry_run:
                continue

            # Process each sorry entry
            for line_idx, entry in sorry_entries:
                # Get the theorem ID from the query
                if line_idx >= len(queries):
                    print(f"  Warning: Line {line_idx} out of range for queries")
                    continue

                query = queries[line_idx]

                # Extract theorem_id from the query if it exists
                # Query is a list of message dicts, extract id from user message if present
                theorem_id = line_idx
                if isinstance(query, list):
                    for msg in query:
                        if isinstance(msg, dict) and 'id' in msg:
                            theorem_id = msg['id']
                            break
                elif isinstance(query, dict):
                    theorem_id = query.get('id', line_idx)

                print(f"\n  Patching entry {line_idx} (theorem_id: {theorem_id})")
                print(f"    LLM: {llm_name}")
                print(f"    Dataset: {dataset_name}")
                print(f"    Run: {run_num}")

                # Retry with the LLM
                success = False
                for attempt in range(max_retries):
                    print(f"    Attempt {attempt + 1}/{max_retries}...")

                    start_time = time.time()
                    try:
                        # Use the query to call the LLM
                        response = engine.generate(query)
                        elapsed_time = time.time() - start_time

                        # Check if the response is valid (not "sorry")
                        if response.get("code", "").strip() != "sorry":
                            print(f"    ✓ Success! Patched in {elapsed_time:.2f}s")

                            # Update the result and time
                            results[line_idx] = response
                            times[line_idx] = elapsed_time

                            success = True
                            total_patched += 1
                            break
                        else:
                            print(f"    ✗ Still got 'sorry' response")

                    except Exception as e:
                        print(f"    ✗ Error: {e}")
                        elapsed_time = time.time() - start_time

                if not success:
                    print(f"    ✗ Failed to patch after {max_retries} attempts")
                    total_failed += 1

            # Write updated results and times back to files
            print(f"\n  Saving updated results to {result_file}")
            save_jsonl(result_file, results)

            print(f"  Saving updated times to {time_file}")
            with open(time_file, 'w') as f:
                json.dump(times, f, indent=4)

    # Print summary
    print(f"\n{'='*60}")
    print(f"SUMMARY FOR {llm_name}")
    print(f"{'='*60}")
    if dry_run:
        print(f"Mode: DRY RUN (scan only)")
        print(f"Total 'sorry' entries found: {total_patched + total_failed}")
    else:
        print(f"Mode: PATCH")
        print(f"Total patched: {total_patched}")
        print(f"Total failed: {total_failed}")

    # Cleanup model
    if engine and hasattr(engine, 'unload_model'):
        engine.unload_model()


def main():
    """Main function to patch LLM results."""
    import argparse

    parser = argparse.ArgumentParser(
        description='Patch "sorry" responses in LLM result files'
    )
    parser.add_argument(
        'llm_name',
        type=str,
        nargs='?',
        default='all',
        help='Name of the LLM (must match folder name in results/), or "all" to scan all LLMs (default: all)'
    )
    parser.add_argument(
        '--max-retries',
        type=int,
        default=3,
        help='Maximum number of retry attempts per sorry entry (default: 3)'
    )
    parser.add_argument(
        '--repo-folder',
        type=str,
        default='.',
        help='Path to repository root (default: current directory)'
    )
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='Only scan and report errors without attempting to fix them'
    )
    parser.add_argument(
        '--fix',
        action='store_true',
        help='Actually fix the errors (without this flag, only reports errors)'
    )

    args = parser.parse_args()

    # Default to dry-run unless --fix is specified
    dry_run = not args.fix or args.dry_run

    if args.llm_name == 'all':
        # Scan all LLMs
        print("Scanning all LLMs for 'sorry' entries...\n")
        all_sorry_info = scan_all_sorry_entries(args.repo_folder)

        if not all_sorry_info:
            print("No 'sorry' entries found in any LLM results!")
            return

        # Print summary
        print(f"\n{'='*60}")
        print(f"SORRY ENTRIES SUMMARY (ALL LLMs)")
        print(f"{'='*60}\n")

        for llm_name, sorry_list in sorted(all_sorry_info.items()):
            print(f"{llm_name}: {len(sorry_list)} 'sorry' entries")

            # Group by dataset
            by_dataset = {}
            for info in sorry_list:
                dataset = info['dataset']
                if dataset not in by_dataset:
                    by_dataset[dataset] = []
                by_dataset[dataset].append(info)

            for dataset, entries in sorted(by_dataset.items()):
                print(f"  {dataset}:")

                # Group by run
                by_run = {}
                for info in entries:
                    run = info['run']
                    if run not in by_run:
                        by_run[run] = []
                    by_run[run].append(info)

                for run, run_entries in sorted(by_run.items()):
                    line_nums = [e['line_idx'] for e in run_entries]
                    print(f"    Run {run}: {len(run_entries)} errors at lines {line_nums}")
            print()

        print(f"\nTotal LLMs with errors: {len(all_sorry_info)}")
        print(f"Total 'sorry' entries across all LLMs: {sum(len(v) for v in all_sorry_info.values())}")

        if not args.fix:
            print(f"\nTo fix these entries, run with --fix flag for specific LLMs")
            print(f"Example: python3 benchmark/patch_results.py gpt-4o --fix")
    else:
        # Process single LLM
        patch_results(
            llm_name=args.llm_name,
            max_retries=args.max_retries,
            repo_folder=args.repo_folder,
            dry_run=dry_run
        )


if __name__ == "__main__":
    main()
