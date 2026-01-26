#!/usr/bin/env python3
"""
Analyze LLM benchmark results across datasets and generate comparative plots.

This is the main analyzer that orchestrates various analysis modules.
All analysis modules are located in utils/analysis_modules.py
"""

from pathlib import Path
from typing import Dict

# Import analysis modules
from utils.analysis_modules import (
    load_statistics,
    compute_avg_and_std,
    compute_proof_lengths,
    compute_proof_length_stats,
    perform_stat_test,
    plot_combined_analysis,
    plot_all_llms_combined
)


def analyze_results(
    llm_name: str,
    repo_folder: str = ".",
    print_stats: bool = True,
    run_all_analyses: bool = True
) -> Dict:
    """
    Complete analysis pipeline for a single LLM.

    This function runs each analysis module sequentially:
    1. Load statistics
    2. Compute averages and standard errors for scores/times
    3. Plot rate and time with error bars
    4. Plot correction rate per problem across runs
    5. Compute and plot proof plan length analysis

    Args:
        llm_name: The LLM name
        repo_folder: Repository root folder
        print_stats: Whether to print statistics table
        run_all_analyses: Whether to run all analysis modules

    Returns:
        Dictionary containing all computed metrics
    """
    results = {}
    save_dir = Path(repo_folder) / "results" / llm_name

    # Load statistics
    try:
        stats = load_statistics(llm_name, repo_folder)
        results['stats'] = stats
    except FileNotFoundError as e:
        print(f"Error: {e}")
        return results

    # Compute averages and standard errors
    metrics = compute_avg_and_std(
        llm_name=llm_name,
        stats=stats,
        repo_folder=repo_folder,
        print_results=print_stats
    )
    results['metrics'] = metrics

    # Perform Welch's t-tests for correct rates and times
    if print_stats and metrics:
        dataset_order = ["original", "obfuscated_1", "obfuscated_2", "obfuscated_3",
                         "obfuscated_4", "obfuscated_5"]

        # Extract means and standard errors for datasets present
        score_means = []
        score_ses = []
        time_means = []
        time_ses = []

        for dataset_name in dataset_order:
            if dataset_name in metrics:
                m = metrics[dataset_name]
                score_means.append(m["avg_score"])
                score_ses.append(m["score_stderr"])
                time_means.append(m["avg_time"])
                time_ses.append(m["time_stderr"])

        # Run statistical tests
        if len(score_means) > 1:
            print(f"\n{'='*60}")
            print(f"One-Way ANOVA Results for {llm_name}")
            print(f"{'='*60}\n")

            perform_stat_test("Correct Rate (%)", score_means, score_ses)
            print()
            perform_stat_test("Average Time (s)", time_means, time_ses)
            print()

    if not run_all_analyses:
        return results

    # Compute proof plan length stats
    proof_lengths = compute_proof_lengths(
        llm_name=llm_name,
        repo_folder=repo_folder
    )
    proof_length_stats = compute_proof_length_stats(proof_lengths)

    # Delete old individual plot files if they exist
    old_plots = [
        save_dir / f"{llm_name}_analysis.png",
        save_dir / f"{llm_name}_analysis.pdf",
        save_dir / f"{llm_name}_correction_rate_per_problem.png",
        save_dir / f"{llm_name}_proof_length.png"
    ]
    for old_plot in old_plots:
        if old_plot.exists():
            old_plot.unlink()
            print(f"Deleted old plot: {old_plot}")

    # Create combined 1x3 plot
    if metrics and proof_length_stats:
        plot_combined_analysis(
            llm_name=llm_name,
            metrics=metrics,
            proof_length_stats=proof_length_stats,
            save_dir=save_dir,
            repo_folder=repo_folder
        )
        print(f"Created combined analysis plot for {llm_name}")

    # Perform Welch's t-test for proof plan lengths
    if print_stats and proof_length_stats:
        dataset_order = ["original", "obfuscated_1", "obfuscated_2", "obfuscated_3",
                         "obfuscated_4", "obfuscated_5"]

        length_means = []
        length_ses = []

        for dataset_name in dataset_order:
            if dataset_name in proof_length_stats:
                stats_data = proof_length_stats[dataset_name]
                length_means.append(stats_data["avg_length"])
                length_ses.append(stats_data["length_stderr"])

        if len(length_means) > 1:
            print(f"{'='*60}")
            print(f"One-Way ANOVA Results for Proof Plan Length")
            print(f"{'='*60}\n")
            perform_stat_test("Proof Plan Length (characters)", length_means, length_ses)
            print()

    return results


def main():
    """Main function to analyze results for multiple LLMs."""
    # List of LLMs to analyze
    llm_list = [
        "gpt-4o",
        "claude-sonnet-4.5",
        "deepseek-r1",
        "gpt-5",
        "deepseek-prover-v2",
    ]

    repo_folder = "."

    all_results = {}

    for llm_name in llm_list:
        try:
            results = analyze_results(
                llm_name=llm_name,
                repo_folder=repo_folder,
                print_stats=True,
                run_all_analyses=True
            )
            all_results[llm_name] = results
        except Exception as e:
            print(f"\nError analyzing {llm_name}: {e}")
            import traceback
            traceback.print_exc()

    # Create combined plot for all LLMs
    print("\n" + "="*60)
    print("Creating combined plot for all LLMs")
    print("="*60)
    try:
        plot_all_llms_combined(llm_list, repo_folder)
    except Exception as e:
        print(f"\nError creating combined plot: {e}")
        import traceback
        traceback.print_exc()

    return all_results


if __name__ == "__main__":
    main()
