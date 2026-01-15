#!/usr/bin/env python3
"""
Score LLM results by verifying generated proofs and computing statistics.
"""

import json
import os
import sys
from pathlib import Path
from typing import Dict, List, Any

from verification.verify_individual import verify_individual_dataset
from verification.jsonl_generator import load_jsonl
from verification.record_time import load_time_data, compute_average_time, plot_average_times
from utils.discord_notify import send_msg


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

            # Send notification for run start
            send_msg(f"🔄 **Processing {dataset_name} - Run {run_num}/{len(result_files)}**")

            # Verify the result file
            try:
                run_stats = verify_individual_dataset(result_file, repo_folder)

                # Load timing information
                time_file = dataset_folder / f"time_{run_num}.json"
                avg_time = 0.0
                if time_file.exists():
                    times = load_time_data(time_file)
                    avg_time = compute_average_time(times)

                # Add avg_time to run_stats
                run_stats["avg_time"] = avg_time

                # Print results
                print(f"  Total proofs: {run_stats['total']}")
                print(f"  Correct: {run_stats['correct']}")
                print(f"  Incorrect: {run_stats['incorrect']}")
                print(f"  Correct rate: {run_stats['correct_rate']*100:.2f}%")
                print(f"  Average time: {avg_time:.2f}s")
                if run_stats['banned_count'] > 0:
                    print(f"  ⚠ Using banned tactics: {run_stats['banned_count']}")

                # Print incorrect proof details
                incorrect_ids = set(run_stats['error_ids']) | set(run_stats['sorry_ids'])
                if incorrect_ids:
                    print(f"\n  Incorrect proof IDs:")
                    all_incorrect = sorted(incorrect_ids)
                    # Load generated proofs for detailed info
                    generated_proofs_file = dataset_folder / f"generated_proofs_{run_num}.jsonl"
                    generated_proofs = load_jsonl(generated_proofs_file)

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
                if run_stats['banned_tactics_usage']:
                    print(f"\n  ⚠ Proofs using banned tactics:")
                    generated_proofs_file = dataset_folder / f"generated_proofs_{run_num}.jsonl"
                    generated_proofs = load_jsonl(generated_proofs_file)

                    for proof_id in sorted(run_stats['banned_tactics_usage'].keys()):
                        tactics_list = ', '.join(run_stats['banned_tactics_usage'][proof_id])
                        # Find the proof in generated proofs
                        for proof in generated_proofs:
                            if proof['id'] == proof_id:
                                print(f"    ID {proof_id}: {proof['name']} - used: {tactics_list}")
                                break

                # Store stats
                dataset_stats["runs"].append(run_stats)
                dataset_stats["correct_rates"].append(run_stats['correct_rate'])
                dataset_stats["avg_times"].append(avg_time)

                # Send notification after each run
                send_msg(
                    f"✅ **{dataset_name} - Run {run_num} Complete**\n"
                    f"Correct: {run_stats['correct']}/{run_stats['total']} ({run_stats['correct_rate']*100:.2f}%)\n"
                    f"Avg time: {avg_time:.2f}s"
                )

            except Exception as e:
                send_msg(f"❌ Error during verification: {e}")
                import traceback
                traceback.print_exc()

        # Compute dataset averages
        if dataset_stats["correct_rates"]:
            import numpy as np
            dataset_avg_correct = np.mean(dataset_stats["correct_rates"])
            dataset_avg_time = np.mean(dataset_stats["avg_times"])

            print(f"\n{dataset_name} Summary:")
            print(f"  Average correct rate: {dataset_avg_correct*100:.2f}%")
            print(f"  Average time per proof: {dataset_avg_time:.2f}s")

            dataset_stats["avg_correct_rate"] = dataset_avg_correct
            dataset_stats["overall_avg_time"] = dataset_avg_time

            # Send Discord notification for completed dataset
            send_msg(
                f"📊 **Dataset Completed: {dataset_name}**\n"
                f"✅ Average correct rate: **{dataset_avg_correct*100:.2f}%**\n"
                f"⏱️ Average time per proof: **{dataset_avg_time:.2f}s**\n"
                f"🔄 Total runs: {len(dataset_stats['runs'])}"
            )

        all_stats["datasets"][dataset_name] = dataset_stats

    # Compute overall averages
    import numpy as np
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


def score_llm(llm_name: str):
    """Score a single LLM."""
    print(f"{'='*60}")
    print(f"Scoring LLM: {llm_name}")
    print(f"{'='*60}")

    # Send start notification
    send_msg(f"🚀 **Scoring Started for {llm_name}**")

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
    for dataset_name, dataset_stats in stats["datasets"].items():
        if dataset_stats.get("runs"):
            dataset_dir = results_dir / dataset_name
            try:
                plot_file = plot_average_times(dataset_dir, llm_name, dataset_name, dataset_stats["runs"])
                print(f"Saved plot: {plot_file}")
            except Exception as e:
                print(f"Error creating plot for {dataset_name}: {e}")

    # Save statistics to JSON (overwrite if exists)
    stats_file = results_dir / "statistics.json"
    with open(stats_file, 'w', encoding='utf-8') as f:
        json.dump(stats, f, indent=2)
    print(f"\nStatistics saved to: {stats_file}")

    # Send final Discord notification
    send_msg(
        f"🎉 **All Datasets Completed**\n"
        f"✅ Overall average correct rate: **{stats['overall_correct_rate']*100:.2f}%**\n"
        f"⏱️ Overall average time per proof: **{stats['overall_avg_time']:.2f}s**\n"
        f"📁 Total datasets processed: {len(stats['datasets'])}"
    )


def main():
    """Main function to score LLM results."""
    # Check if LLM_NAME is set, if so use it for single LLM mode
    if LLM_NAME and LLM_NAME != "none":
        score_llm(LLM_NAME)
    else:
        # Run multiple LLMs consecutively
        llm_list = [ "gpt-5", "claude-sonnet-4.5"]

        for llm_name in llm_list:
            score_llm(llm_name)
            print("\n" * 3)  # Add spacing between LLMs


# ============================================================================
# CONFIGURATION
# ============================================================================

# LLM to score - must match one of the LLM names used in query_llm.py
LLM_NAME = os.getenv("LLM_NAME", "none")


if __name__ == "__main__":
    main()
