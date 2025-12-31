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
    plot_rate_and_time,
    plot_correction_rate_per_problem,
    plot_proof_length_analysis
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
    5. Compute and plot proof length analysis

    Args:
        llm_name: The LLM name
        repo_folder: Repository root folder
        print_stats: Whether to print statistics table
        run_all_analyses: Whether to run all analysis modules

    Returns:
        Dictionary containing all computed metrics
    """
    print(f"\n{'='*60}")
    print(f"Analyzing LLM: {llm_name}")
    print(f"{'='*60}")

    results = {}
    save_dir = Path(repo_folder) / "results" / llm_name

    # ========================================================================
    # Module 1: Load statistics
    # ========================================================================
    print("\n[Module 1] Loading statistics...")
    try:
        stats = load_statistics(llm_name, repo_folder)
        results['stats'] = stats
    except FileNotFoundError as e:
        print(f"Error: {e}")
        return results

    # ========================================================================
    # Module 2: Compute averages and standard errors
    # ========================================================================
    print("\n[Module 2] Computing averages and standard errors...")
    metrics = compute_avg_and_std(
        llm_name=llm_name,
        stats=stats,
        repo_folder=repo_folder,
        print_results=print_stats
    )
    results['metrics'] = metrics

    if not run_all_analyses:
        return results

    # ========================================================================
    # Module 3: Plot rate and time
    # ========================================================================
    print("\n[Module 3] Plotting rate and time analysis...")
    if metrics:
        plot_rate_and_time(
            llm_name=llm_name,
            metrics=metrics,
            save_dir=save_dir,
            repo_folder=repo_folder
        )

    # ========================================================================
    # Module 4: Plot correction rate per problem
    # ========================================================================
    print("\n[Module 4] Plotting correction rate per problem...")
    plot_correction_rate_per_problem(
        llm_name=llm_name,
        stats=stats,
        save_dir=save_dir,
        repo_folder=repo_folder
    )

    # ========================================================================
    # Module 5: Proof length analysis
    # ========================================================================
    print("\n[Module 5] Computing proof lengths...")
    proof_lengths = compute_proof_lengths(
        llm_name=llm_name,
        repo_folder=repo_folder
    )

    proof_length_stats = compute_proof_length_stats(proof_lengths)
        
    plot_proof_length_analysis(
        llm_name=llm_name,
        proof_length_stats=proof_length_stats,
        save_dir=save_dir,
        repo_folder=repo_folder
    )

    print(f"\n{'='*60}")
    print(f"Analysis complete for {llm_name}")
    print(f"{'='*60}\n")

    return results


def main():
    """Main function to analyze results for multiple LLMs."""
    # List of LLMs to analyze
    llm_list = [
        "deepseek-r1",
        "deepseek-prover-v2",
        "gpt-4o"
    ]

    repo_folder = "."

    print("="*60)
    print("Starting comprehensive analysis of LLM benchmark results...")
    print(f"Repository folder: {Path(repo_folder).resolve()}")
    print("="*60)

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

    print("\n" + "="*60)
    print("Analysis complete for all LLMs")
    print("="*60)

    return all_results


if __name__ == "__main__":
    main()
