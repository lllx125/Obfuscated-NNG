#!/usr/bin/env python3
"""
Analysis modules for LLM benchmark results.

This module provides various analysis functions for processing and visualizing
LLM theorem proving benchmark results.
"""

import json
import numpy as np
import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend to avoid display issues
import matplotlib.pyplot as plt
from pathlib import Path
from typing import Dict, List, Tuple, Optional
from scipy import stats


# ============================================================================
# Data Loading
# ============================================================================

def load_statistics(llm_name: str, repo_folder: str = ".") -> Dict:
    """
    Load statistics.json for a given LLM.

    Args:
        llm_name: The LLM name
        repo_folder: Repository root folder

    Returns:
        Statistics dictionary
    """
    stats_file = Path(repo_folder) / "results" / llm_name / "statistics.json"

    if not stats_file.exists():
        raise FileNotFoundError(f"Statistics file not found: {stats_file}")

    with open(stats_file, 'r', encoding='utf-8') as f:
        return json.load(f)


def load_result_file(result_file: Path) -> List[Dict]:
    """
    Load a result JSONL file.

    Args:
        result_file: Path to result_n.jsonl file

    Returns:
        List of result dictionaries
    """
    results = []
    with open(result_file, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                results.append(json.loads(line))
    return results


# ============================================================================
# Statistics Computation
# ============================================================================

def compute_avg_and_std(
    llm_name: str,
    stats: Dict,
    repo_folder: str = ".",
    print_results: bool = True
) -> Dict[str, Dict[str, float]]:
    """
    Compute average score, average time, and their standard errors for all datasets.

    Args:
        llm_name: The LLM name
        stats: Statistics dictionary from load_statistics()
        repo_folder: Repository root folder
        print_results: Whether to print the results table

    Returns:
        Dictionary mapping dataset names to their metrics:
        {
            "dataset_name": {
                "avg_score": float,
                "score_stderr": float,
                "avg_time": float,
                "time_stderr": float
            }
        }
    """
    dataset_order = ["original", "obfuscated_1", "obfuscated_2", "obfuscated_3",
                     "obfuscated_4", "obfuscated_5"]

    results = {}

    # Print header if requested
    if print_results:
        print(f"\n{'='*60}")
        print(f"Statistics for {llm_name}")
        print(f"{'='*60}\n")
        print(f"{'Dataset':<15} {'Score (%)':<15} {'Std Error':<15} {'Time (s)':<15} {'Std Error':<15}")
        print("-" * 75)

    for dataset_name in dataset_order:
        if dataset_name in stats["datasets"]:
            dataset_stats = stats["datasets"][dataset_name]

            # Check if dataset has runs
            if "runs" not in dataset_stats or not dataset_stats["runs"]:
                continue

            runs = dataset_stats["runs"]

            # Extract correct rates (as percentages) and times
            scores = [run["correct_rate"] * 100 for run in runs]
            times = [run["avg_time"] for run in runs]

            # Compute averages
            avg_score = np.mean(scores)
            avg_time = np.mean(times)

            # Compute standard errors (SEM = std / sqrt(n))
            score_stderr = np.std(scores, ddof=1) / np.sqrt(len(scores)) if len(scores) > 1 else 0.0
            time_stderr = np.std(times, ddof=1) / np.sqrt(len(times)) if len(times) > 1 else 0.0

            # Store results
            results[dataset_name] = {
                "avg_score": avg_score,
                "score_stderr": score_stderr,
                "avg_time": avg_time,
                "time_stderr": time_stderr
            }

            # Print if requested
            if print_results:
                print(f"{dataset_name:<15} {avg_score:>8.2f}        "
                      f"{score_stderr:>8.2f}        "
                      f"{avg_time:>8.2f}        "
                      f"{time_stderr:>8.2f}")

    if print_results:
        print()

    return results


def compute_proof_lengths(
    llm_name: str,
    repo_folder: str = "."
) -> np.ndarray:
    """
    Compute proof lengths (length of "draft" field) for each problem across all datasets and runs.

    Args:
        llm_name: The LLM name
        repo_folder: Repository root folder

    Returns:
        numpy array with shape (num_datasets, num_runs, num_problems)
        where num_datasets includes original (index 0) plus obfuscated_1 to obfuscated_5
        original dataset values are set to 0 as specified
    """
    dataset_order = ["original", "obfuscated_1", "obfuscated_2", "obfuscated_3",
                     "obfuscated_4", "obfuscated_5"]

    results_base = Path(repo_folder) / "results" / llm_name

    # First, determine dimensions by scanning available data
    max_runs = 0
    max_problems = 0

    for dataset_name in dataset_order:
        dataset_dir = results_base / dataset_name
        if not dataset_dir.exists():
            continue

        result_files = sorted(dataset_dir.glob("result_*.jsonl"))
        max_runs = max(max_runs, len(result_files))

        for result_file in result_files:
            results = load_result_file(result_file)
            max_problems = max(max_problems, len(results))

    if max_runs == 0 or max_problems == 0:
        print(f"No result files found for {llm_name}")
        return np.array([])

    # Initialize array with zeros
    proof_lengths = np.zeros((len(dataset_order), max_runs, max_problems))

    # Fill in the data
    for dataset_idx, dataset_name in enumerate(dataset_order):
        dataset_dir = results_base / dataset_name

        if not dataset_dir.exists():
            continue

        result_files = sorted(dataset_dir.glob("result_*.jsonl"))

        for run_idx, result_file in enumerate(result_files):
            results = load_result_file(result_file)

            for problem_idx, result in enumerate(results):
                if "draft" in result:
                    proof_lengths[dataset_idx, run_idx, problem_idx] = len(result["draft"])

    return proof_lengths


def compute_proof_length_stats(
    proof_lengths: np.ndarray
) -> Dict[str, Dict[str, float]]:
    """
    Compute average proof length and standard error for each dataset.

    Args:
        proof_lengths: numpy array from compute_proof_lengths()
                      shape: (num_datasets, num_runs, num_problems)

    Returns:
        Dictionary mapping dataset names to their metrics:
        {
            "dataset_name": {
                "avg_length": float,
                "length_stderr": float
            }
        }
    """
    dataset_order = ["original", "obfuscated_1", "obfuscated_2", "obfuscated_3",
                     "obfuscated_4", "obfuscated_5"]

    results = {}

    print(f"\n{'='*60}")
    print(f"Proof Length Statistics")
    print(f"{'='*60}\n")
    print(f"{'Dataset':<15} {'Avg Length':<15} {'Std Error':<15}")
    print("-" * 45)

    for dataset_idx, dataset_name in enumerate(dataset_order):
        if dataset_idx >= proof_lengths.shape[0]:
            break

        # Get all lengths for this dataset (across all runs and problems)
        # Flatten across runs and problems
        dataset_lengths = proof_lengths[dataset_idx].flatten()

        # Remove zeros (which could be missing data)
        dataset_lengths = dataset_lengths[dataset_lengths > 0]

        if len(dataset_lengths) == 0:
            continue

        # Compute average and standard error
        avg_length = np.mean(dataset_lengths)
        length_stderr = np.std(dataset_lengths, ddof=1) / np.sqrt(len(dataset_lengths)) if len(dataset_lengths) > 1 else 0.0

        results[dataset_name] = {
            "avg_length": avg_length,
            "length_stderr": length_stderr
        }

        print(f"{dataset_name:<15} {avg_length:>8.2f}        {length_stderr:>8.2f}")

    print()
    return results


def perform_stat_test(name: str, means: List[float], ses: List[float], n: int = 5):
    """
    Perform One-Way ANOVA using means and standard errors.

    Args:
        name: Name of the metric being tested (e.g., "Correct Rate", "Proof Length")
        means: List of mean values [original, obfuscated_1, ..., obfuscated_5]
        ses: List of standard errors [original, obfuscated_1, ..., obfuscated_5]
        n: Number of runs (default: 5)
    """
    print(f"--- Analysis for {name} ---")

    k = len(means)  # Number of datasets (6)
    N = n * k       # Total number of observations

    # Calculate variances (Var = SE^2 * n)
    variances = [(se**2) * n for se in ses]

    # 1. Grand Mean
    grand_mean = np.mean(means)

    # 2. Sum of Squares Between (SSB) - measures variation between datasets
    ss_between = n * sum((m - grand_mean)**2 for m in means)
    ms_between = ss_between / (k - 1)

    # 3. Sum of Squares Within (SSW) - measures noise/variance within the 5 runs
    ss_within = sum((n - 1) * v for v in variances)
    ms_within = ss_within / (N - k)

    # 4. F-statistic and P-value
    f_stat = ms_between / ms_within
    p_value = stats.f.sf(f_stat, k - 1, N - k)

    status = "SIGNIFICANT" if p_value < 0.05 else "not significant"
    print(f"F-statistic = {f_stat:.4f}, p-value = {p_value:.4f} ({status})")


# ============================================================================
# Plotting Functions
# ============================================================================

def plot_rate_and_time(
    llm_name: str,
    metrics: Dict[str, Dict[str, float]],
    save_dir: Path,
    repo_folder: str = "."
) -> Optional[Path]:
    """
    Create a dual-axis plot showing correct rates and times across datasets.

    Args:
        llm_name: The LLM name
        metrics: Dictionary of metrics from compute_avg_and_std()
        save_dir: Directory to save the plot
        repo_folder: Repository root folder

    Returns:
        Path to saved plot file, or None if no data available
    """
    # Dataset order: original, obfuscated_1, ..., obfuscated_5
    dataset_order = ["original", "obfuscated_1", "obfuscated_2", "obfuscated_3",
                     "obfuscated_4", "obfuscated_5"]

    # Prepare data
    datasets_present = []
    scores = []
    score_errors = []
    times = []
    time_errors = []

    for dataset_name in dataset_order:
        if dataset_name in metrics:
            m = metrics[dataset_name]
            datasets_present.append(dataset_name)
            scores.append(m["avg_score"])
            score_errors.append(m["score_stderr"])
            times.append(m["avg_time"])
            time_errors.append(m["time_stderr"])

    if not datasets_present:
        print(f"No datasets found for {llm_name}")
        return None

    # Create plot
    fig, ax1 = plt.subplots(figsize=(12, 6))

    # X-axis positions
    x_pos = np.arange(len(datasets_present))

    # Plot scores on left y-axis (no connecting line)
    color1 = 'tab:blue'
    ax1.set_xlabel('Dataset', fontsize=12)
    ax1.set_ylabel('Correct Rate (%)', color=color1, fontsize=12)
    ax1.errorbar(x_pos, scores, yerr=score_errors,
                 fmt='o', color=color1, capsize=5, capthick=2,
                 markersize=8, linestyle='', label='Correct Rate')
    ax1.tick_params(axis='y', labelcolor=color1)
    ax1.set_ylim(0, 100)
    ax1.grid(True, alpha=0.3)

    # Plot times on right y-axis (no connecting line)
    ax2 = ax1.twinx()
    color2 = 'tab:orange'
    ax2.set_ylabel('Average Time (s)', color=color2, fontsize=12)
    ax2.errorbar(x_pos, times, yerr=time_errors,
                 fmt='s', color=color2, capsize=5, capthick=2,
                 markersize=8, linestyle='', label='Avg Time')
    ax2.tick_params(axis='y', labelcolor=color2)

    # Set time y-axis to start from 0
    y2_min, y2_max = ax2.get_ylim()
    ax2.set_ylim(0, y2_max * 1.1)

    # Set x-axis labels
    ax1.set_xticks(x_pos)
    ax1.set_xticklabels(datasets_present, rotation=15, ha='right')

    # Title
    plt.title(f'{llm_name} Performance Across Datasets', fontsize=14, fontweight='bold', pad=20)

    # Add legends
    lines1, labels1 = ax1.get_legend_handles_labels()
    lines2, labels2 = ax2.get_legend_handles_labels()
    ax1.legend(lines1 + lines2, labels1 + labels2, loc='upper left', fontsize=10)

    # Tight layout
    fig.tight_layout()

    # Save plot
    save_path = save_dir / f"{llm_name}_analysis.png"
    plt.savefig(str(save_path), dpi=300, bbox_inches='tight')
    plt.close()

    return save_path


def plot_correction_rate_per_problem(
    llm_name: str,
    stats: Dict,
    save_dir: Path,
    repo_folder: str = "."
) -> Optional[Path]:
    """
    Plot line chart showing correction rate for each problem across 5 runs.
    Creates 6 subplots (2 rows × 3 columns) - one for each dataset.

    Args:
        llm_name: The LLM name
        stats: Statistics dictionary from load_statistics()
        save_dir: Directory to save the plot
        repo_folder: Repository root folder

    Returns:
        Path to saved plot file, or None if no data available
    """
    dataset_order = ["original", "obfuscated_1", "obfuscated_2", "obfuscated_3",
                     "obfuscated_4", "obfuscated_5"]

    # Colors for different datasets
    colors = ['#1f77b4', '#ff7f0e', '#2ca02c', '#d62728', '#9467bd', '#8c564b']

    # Create 2x3 subplots
    fig, axes = plt.subplots(2, 3, figsize=(18, 10))
    axes = axes.flatten()  # Flatten to 1D array for easier indexing

    datasets_plotted = []

    for dataset_idx, dataset_name in enumerate(dataset_order):
        ax = axes[dataset_idx]

        if dataset_name not in stats["datasets"]:
            ax.set_visible(False)
            continue

        dataset_stats = stats["datasets"][dataset_name]

        if "runs" not in dataset_stats or not dataset_stats["runs"]:
            ax.set_visible(False)
            continue

        runs = dataset_stats["runs"]

        # Determine the number of problems (from first run)
        if not runs:
            ax.set_visible(False)
            continue

        # Get generated_proofs file to determine number of problems and their IDs
        results_base = Path(repo_folder) / "results" / llm_name / dataset_name
        generated_proofs_file = results_base / "generated_proofs_1.jsonl"

        if not generated_proofs_file.exists():
            ax.set_visible(False)
            continue

        # Load to get problem IDs
        from verification.jsonl_generator import load_jsonl
        proofs = load_jsonl(generated_proofs_file)
        num_problems = len(proofs)

        if num_problems == 0:
            ax.set_visible(False)
            continue

        # For each problem, compute correction rate across runs
        # correction_rates[problem_idx] = number of runs where problem was correct / total runs
        correction_rates = np.zeros(num_problems)

        for run in runs:
            # Determine which problems were correct in this run
            correct_ids = set(range(1, num_problems + 1))  # Start with all IDs
            correct_ids -= set(run.get("error_ids", []))
            correct_ids -= set(run.get("sorry_ids", []))

            for problem_idx in range(num_problems):
                problem_id = problem_idx + 1  # IDs are 1-indexed
                if problem_id in correct_ids:
                    correction_rates[problem_idx] += 1

        # Convert to percentage
        correction_rates = (correction_rates / len(runs)) * 100

        # Plot as line
        problem_indices = np.arange(1, num_problems + 1)
        ax.plot(problem_indices, correction_rates,
                color=colors[dataset_idx % len(colors)],
                linewidth=2, marker='o', markersize=3,
                alpha=0.7)

        # Styling for this subplot
        ax.set_xlabel('Problem ID', fontsize=10)
        ax.set_ylabel('Correction Rate (%)', fontsize=10)
        ax.set_title(dataset_name, fontsize=12, fontweight='bold')
        ax.set_ylim(0, 100)
        ax.grid(True, alpha=0.3)

        datasets_plotted.append(dataset_name)

    if not datasets_plotted:
        print(f"No data available for {llm_name}")
        plt.close(fig)
        return None

    # Overall title
    fig.suptitle(f'{llm_name} - Problem Correction Rate Across Runs',
                 fontsize=16, fontweight='bold', y=0.995)

    fig.tight_layout()

    # Save plot
    save_path = save_dir / f"{llm_name}_correction_rate_per_problem.png"
    plt.savefig(str(save_path), dpi=300, bbox_inches='tight')
    plt.close()

    return save_path


def plot_proof_length_analysis(
    llm_name: str,
    proof_length_stats: Dict[str, Dict[str, float]],
    save_dir: Path,
    repo_folder: str = "."
) -> Optional[Path]:
    """
    Plot average proof length with error bars across datasets.

    Args:
        llm_name: The LLM name
        proof_length_stats: Dictionary from compute_proof_length_stats()
        save_dir: Directory to save the plot
        repo_folder: Repository root folder

    Returns:
        Path to saved plot file, or None if no data available
    """
    dataset_order = ["original", "obfuscated_1", "obfuscated_2", "obfuscated_3",
                     "obfuscated_4", "obfuscated_5"]

    # Prepare data
    datasets_present = []
    avg_lengths = []
    length_errors = []

    for dataset_name in dataset_order:
        if dataset_name in proof_length_stats:
            stats = proof_length_stats[dataset_name]
            datasets_present.append(dataset_name)
            avg_lengths.append(stats["avg_length"])
            length_errors.append(stats["length_stderr"])

    if not datasets_present:
        print(f"No proof length data available for {llm_name}")
        return None

    # Create plot
    fig, ax = plt.subplots(figsize=(12, 6))

    # X-axis positions
    x_pos = np.arange(len(datasets_present))

    # Plot average proof lengths with error bars
    ax.errorbar(x_pos, avg_lengths, yerr=length_errors,
                fmt='o', color='tab:green', capsize=5, capthick=2,
                markersize=8, linestyle='', label='Avg Proof Length')

    # Styling
    ax.set_xlabel('Dataset', fontsize=12)
    ax.set_ylabel('Average Proof Length (characters)', fontsize=12)
    ax.set_title(f'{llm_name} - Average Proof Length Across Datasets',
                 fontsize=14, fontweight='bold', pad=20)
    ax.set_xticks(x_pos)
    ax.set_xticklabels(datasets_present, rotation=15, ha='right')
    ax.grid(True, alpha=0.3)
    ax.legend(loc='best', fontsize=10)

    # Auto-adjust y-axis for better viewing
    # Set y-axis to show data with some padding (10% below min, 10% above max)
    min_length = min(avg_lengths)
    max_length = max(avg_lengths)
    max_error = max(length_errors) if length_errors else 0

    y_range = max_length - min_length
    y_padding = max(y_range * 0.1, max_error * 2)  # At least 10% or 2x max error bar

    ax.set_ylim(bottom=max(0, min_length - y_padding),
                top=max_length + y_padding)

    fig.tight_layout()

    # Save plot
    save_path = save_dir / f"{llm_name}_proof_length.png"
    plt.savefig(str(save_path), dpi=300, bbox_inches='tight')
    plt.close()

    return save_path


def plot_combined_analysis(
    llm_name: str,
    metrics: Dict,
    proof_length_stats: Dict[str, Dict[str, float]],
    save_dir: Path,
    repo_folder: str = "."
) -> Optional[Path]:
    """
    Create a combined 3x1 plot showing score, time, and proof length separately.

    Args:
        llm_name: The LLM name
        metrics: Dictionary of metrics from compute_avg_and_std()
        proof_length_stats: Dictionary from compute_proof_length_stats()
        save_dir: Directory to save the plot
        repo_folder: Repository root folder

    Returns:
        Path to saved plot file, or None if no data available
    """
    dataset_order = ["original", "obfuscated_1", "obfuscated_2", "obfuscated_3",
                     "obfuscated_4", "obfuscated_5"]

    # Prepare data for rate/time plot
    datasets_present = []
    scores = []
    score_errors = []
    times = []
    time_errors = []

    for dataset_name in dataset_order:
        if dataset_name in metrics:
            m = metrics[dataset_name]
            datasets_present.append(dataset_name)
            scores.append(m["avg_score"])
            score_errors.append(m["score_stderr"])
            times.append(m["avg_time"])
            time_errors.append(m["time_stderr"])

    # Prepare data for proof length plot
    avg_lengths = []
    length_errors = []

    for dataset_name in datasets_present:
        if dataset_name in proof_length_stats:
            stats = proof_length_stats[dataset_name]
            avg_lengths.append(stats["avg_length"])
            length_errors.append(stats["length_stderr"])
        else:
            avg_lengths.append(0)
            length_errors.append(0)

    if not datasets_present:
        print(f"No datasets found for {llm_name}")
        return None

    # Create 3x1 subplots (vertical layout)
    fig, (ax1, ax2, ax3) = plt.subplots(3, 1, figsize=(12, 12))

    # X-axis positions
    x_pos = np.arange(len(datasets_present))

    # ========== Subplot 1: Correct Rate ==========
    color1 = 'tab:blue'
    ax1.errorbar(x_pos, scores, yerr=score_errors,
                 fmt='o', color=color1, capsize=5, capthick=2,
                 markersize=8, linestyle='', label='Correct Rate')
    ax1.set_ylabel('Correct Rate (%)', fontsize=12)
    ax1.set_ylim(0, 100)
    ax1.grid(True, alpha=0.3)
    ax1.set_xticks(x_pos)
    ax1.set_xticklabels(datasets_present, rotation=15, ha='right')
    ax1.set_title('Correct Rate', fontsize=13, fontweight='bold', pad=10)
    ax1.legend(loc='best', fontsize=10)

    # ========== Subplot 2: Average Time ==========
    color2 = 'tab:orange'
    ax2.errorbar(x_pos, times, yerr=time_errors,
                 fmt='o', color=color2, capsize=5, capthick=2,
                 markersize=8, linestyle='', label='Avg Time')
    ax2.set_ylabel('Average Time (s)', fontsize=12)
    ax2.grid(True, alpha=0.3)
    ax2.set_xticks(x_pos)
    ax2.set_xticklabels(datasets_present, rotation=15, ha='right')
    ax2.set_title('Average Time', fontsize=13, fontweight='bold', pad=10)
    ax2.legend(loc='best', fontsize=10)

    # Set time y-axis to start from 0
    y2_min, y2_max = ax2.get_ylim()
    ax2.set_ylim(0, y2_max * 1.1)

    # ========== Subplot 3: Proof Length ==========
    color3 = 'tab:green'
    ax3.errorbar(x_pos, avg_lengths, yerr=length_errors,
                 fmt='o', color=color3, capsize=5, capthick=2,
                 markersize=8, linestyle='', label='Avg Proof Length')
    ax3.set_xlabel('Dataset', fontsize=12)
    ax3.set_ylabel('Avg Proof Length (chars)', fontsize=12)
    ax3.set_xticks(x_pos)
    ax3.set_xticklabels(datasets_present, rotation=15, ha='right')
    ax3.grid(True, alpha=0.3)
    ax3.legend(loc='best', fontsize=10)
    ax3.set_title('Proof Length', fontsize=13, fontweight='bold', pad=10)

    # Auto-adjust y-axis for proof length
    if avg_lengths and max(avg_lengths) > 0:
        min_length = min([l for l in avg_lengths if l > 0])
        max_length = max(avg_lengths)
        max_error = max(length_errors) if length_errors else 0
        y_range = max_length - min_length
        y_padding = max(y_range * 0.1, max_error * 2)
        ax3.set_ylim(bottom=max(0, min_length - y_padding),
                     top=max_length + y_padding)

    # Overall title
    fig.suptitle(f'{llm_name} - Complete Analysis', fontsize=16, fontweight='bold')

    fig.tight_layout()

    # Save plot
    save_path = save_dir / f"{llm_name}_analysis.png"
    plt.savefig(str(save_path), dpi=300, bbox_inches='tight')
    plt.close()

    return save_path
