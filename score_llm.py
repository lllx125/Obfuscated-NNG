#!/usr/bin/env python3
"""
Score LLM results by verifying generated proofs and computing statistics.
"""

import json
import os
import sys
from pathlib import Path
from typing import Dict, List, Tuple, Any
import matplotlib.pyplot as plt
import numpy as np

# Import the verifier
from verification.jsonl_verifier import verify_dataset


def load_jsonl(file_path: Path) -> List[Dict]:
    """Load a JSONL file into a list of dictionaries."""
    entries = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                entries.append(json.loads(line))
    return entries


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


def verify_all_runs(
    llm_name: str,
    repo_folder: str = "."
) -> Dict[str, Any]:
    """
    Verify all generated proofs for a given LLM across all datasets and runs.

    Args:
        llm_name: The LLM name
        repo_folder: Repository root folder

    Returns:
        Dictionary with verification results and statistics
    """
    repo_path = Path(repo_folder)
    results_base = repo_path / "results" / llm_name
    dataset_base = repo_path / "dataset"

    if not results_base.exists():
        print(f"Results folder not found: {results_base}")
        return {}

    all_stats = {
        "datasets": {},
        "overall_correct_rate": 0.0,
        "overall_avg_time": 0.0
    }

    # Find all dataset folders
    dataset_folders = [f for f in results_base.iterdir() if f.is_dir()]

    for dataset_folder in dataset_folders:
        dataset_name = dataset_folder.name
        print(f"\n{'='*60}")
        print(f"Processing dataset: {dataset_name}")
        print(f"{'='*60}")

        # Get corresponding header and theorems files
        orig_dataset_path = dataset_base / dataset_name
        header_file = orig_dataset_path / "header_definitions.jsonl"
        theorems_file = orig_dataset_path / "theorems.jsonl"

        if not header_file.exists():
            print(f"Header file not found: {header_file}")
            continue

        if not theorems_file.exists():
            print(f"Theorems file not found: {theorems_file}")
            continue

        # Load original theorems for comparison
        original_theorems = {}
        if theorems_file.exists():
            theorems = load_jsonl(theorems_file)
            original_theorems = {t['id']: t for t in theorems}

        # Clean up old generated_proofs files to ensure fresh start
        old_generated_files = list(dataset_folder.glob("generated_proofs_*.jsonl"))
        if old_generated_files:
            for old_file in old_generated_files:
                old_file.unlink()
            print(f"Cleaned up {len(old_generated_files)} old generated_proofs file(s)")

        # Find all result files
        result_files = sorted(dataset_folder.glob("result_*.jsonl"))

        if not result_files:
            print(f"No result files found in {dataset_folder}")
            continue

        dataset_stats = {
            "runs": [],
            "correct_rates": [],
            "avg_times": []
        }

        for result_file in result_files:
            run_num = int(result_file.stem.split('_')[1])
            print(f"\nRun {run_num}:")

            # Create generated_proofs file
            generated_proofs_file = dataset_folder / f"generated_proofs_{run_num}.jsonl"
            create_generated_proofs_file(result_file, theorems_file, generated_proofs_file)

            # Verify the generated proofs
            print(f"Verifying {generated_proofs_file}...")
            try:
                error_ids, sorry_ids, banned_tactics_usage = verify_dataset(
                    str(header_file),
                    str(generated_proofs_file),
                    verbose=False
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

                # Load timing information
                time_file = dataset_folder / f"time_{run_num}.json"
                avg_time = 0.0
                if time_file.exists():
                    with open(time_file, 'r') as f:
                        times = json.load(f)
                        avg_time = np.mean(times) if times else 0.0

                # Print results
                print(f"  Total proofs: {total_proofs}")
                print(f"  Correct: {correct_count}")
                print(f"  Incorrect: {incorrect_count}")
                print(f"  Correct rate: {correct_rate*100:.2f}%")
                print(f"  Average time: {avg_time:.2f}s")
                if banned_count > 0:
                    print(f"  ⚠ Using banned tactics: {banned_count}")

                # Print incorrect proof details
                if incorrect_ids:
                    print(f"\n  Incorrect proof IDs:")
                    all_incorrect = sorted(incorrect_ids)
                    for proof_id in all_incorrect:
                        # Find the proof in generated proofs
                        for proof in generated_proofs:
                            if proof['id'] == proof_id:
                                print(f"    ID {proof_id}: {proof['name']}")
                                # Print original statement if available
                                if proof_id in original_theorems:
                                    orig_stmt = original_theorems[proof_id]['statement']
                                    print(f"      Original: {orig_stmt}")
                                break

                # Print banned tactics details
                if banned_tactics_usage:
                    print(f"\n  ⚠ Proofs using banned tactics:")
                    for proof_id in sorted(banned_tactics_usage.keys()):
                        tactics_list = ', '.join(banned_tactics_usage[proof_id])
                        # Find the proof in generated proofs
                        for proof in generated_proofs:
                            if proof['id'] == proof_id:
                                print(f"    ID {proof_id}: {proof['name']} - used: {tactics_list}")
                                break

                # Store stats
                run_stats = {
                    "run": run_num,
                    "total": total_proofs,
                    "correct": correct_count,
                    "incorrect": incorrect_count,
                    "error_ids": error_ids,
                    "sorry_ids": sorry_ids,
                    "banned_tactics_usage": banned_tactics_usage,
                    "banned_count": banned_count,
                    "correct_rate": correct_rate,
                    "avg_time": avg_time
                }
                dataset_stats["runs"].append(run_stats)
                dataset_stats["correct_rates"].append(correct_rate)
                dataset_stats["avg_times"].append(avg_time)

            except Exception as e:
                print(f"  Error during verification: {e}")
                import traceback
                traceback.print_exc()

        # Compute dataset averages
        if dataset_stats["correct_rates"]:
            dataset_avg_correct = np.mean(dataset_stats["correct_rates"])
            dataset_avg_time = np.mean(dataset_stats["avg_times"])

            print(f"\n{dataset_name} Summary:")
            print(f"  Average correct rate: {dataset_avg_correct*100:.2f}%")
            print(f"  Average time per proof: {dataset_avg_time:.2f}s")

            dataset_stats["avg_correct_rate"] = dataset_avg_correct
            dataset_stats["overall_avg_time"] = dataset_avg_time

        all_stats["datasets"][dataset_name] = dataset_stats

    # Compute overall averages
    all_correct_rates = []
    all_avg_times = []
    for dataset_stats in all_stats["datasets"].values():
        if "avg_correct_rate" in dataset_stats:
            all_correct_rates.append(dataset_stats["avg_correct_rate"])
        if "overall_avg_time" in dataset_stats:
            all_avg_times.append(dataset_stats["overall_avg_time"])

    if all_correct_rates:
        all_stats["overall_correct_rate"] = np.mean(all_correct_rates)
    if all_avg_times:
        all_stats["overall_avg_time"] = np.mean(all_avg_times)

    return all_stats


def plot_average_times(stats: Dict[str, Any], llm_name: str, results_base_dir: Path):
    """
    Plot average run times across all problems.
    Stores plots in the same folder as time_n.json files.

    Args:
        stats: Statistics dictionary
        llm_name: LLM name
        results_base_dir: Base results directory (results/{llm_name})
    """
    for dataset_name, dataset_stats in stats["datasets"].items():
        if not dataset_stats.get("runs"):
            continue

        # Output directory is the same as where time_n.json files are stored
        dataset_dir = results_base_dir / dataset_name
        dataset_dir.mkdir(parents=True, exist_ok=True)

        # Get times from all runs
        all_times = []
        for run_stats in dataset_stats["runs"]:
            time_file = dataset_dir / f"time_{run_stats['run']}.json"
            if time_file.exists():
                with open(time_file, 'r') as f:
                    times = json.load(f)
                    all_times.append(times)

        if not all_times:
            continue

        # Compute average time for each problem across all runs
        num_problems = len(all_times[0])
        avg_times_per_problem = []

        for i in range(num_problems):
            times_for_problem = [run_times[i] for run_times in all_times if i < len(run_times)]
            if times_for_problem:
                avg_times_per_problem.append(np.mean(times_for_problem))

        # Create bar chart
        fig, ax = plt.subplots(figsize=(12, 6))
        problem_ids = list(range(1, len(avg_times_per_problem) + 1))
        ax.bar(problem_ids, avg_times_per_problem)
        ax.set_xlabel('Problem ID')
        ax.set_ylabel('Average Time (s)')
        ax.set_title(f'Average Solving Time per Problem\n{llm_name} - {dataset_name}')
        ax.grid(axis='y', alpha=0.3)

        # Save plot in the same folder as time_n.json files (overwrite if exists)
        plot_file = dataset_dir / "avg_times.png"
        plt.tight_layout()
        plt.savefig(plot_file, dpi=150)
        plt.close()

        print(f"Saved plot: {plot_file}")


def main():
    """Main function to score LLM results."""
    llm_name = LLM_NAME

    print(f"{'='*60}")
    print(f"Scoring LLM: {llm_name}")
    print(f"{'='*60}")

    # Verify all runs and collect statistics
    stats = verify_all_runs(llm_name)

    if not stats or not stats["datasets"]:
        print("\nNo results found to process")
        return

    # Print overall summary
    print(f"\n{'='*60}")
    print(f"OVERALL SUMMARY")
    print(f"{'='*60}")
    print(f"LLM: {llm_name}")
    print(f"Overall average correct rate: {stats['overall_correct_rate']*100:.2f}%")
    print(f"Overall average time per proof: {stats['overall_avg_time']:.2f}s")

    # Create plots
    results_dir = Path("results") / llm_name
    plot_average_times(stats, llm_name, results_dir)

    # Save statistics to JSON (overwrite if exists)
    stats_file = results_dir / "statistics.json"
    with open(stats_file, 'w', encoding='utf-8') as f:
        json.dump(stats, f, indent=2)
    print(f"\nStatistics saved to: {stats_file}")


# ============================================================================
# CONFIGURATION
# ============================================================================

# LLM to score - must match one of the LLM names used in query_llm.py
LLM_NAME = os.getenv("LLM_NAME", "none")


if __name__ == "__main__":
    main()
