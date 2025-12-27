#!/usr/bin/env python3
"""
Time recording and analysis utilities.
Handles timing data for LLM proof generation benchmarks.
"""

import json
from pathlib import Path
from typing import List, Dict, Any
import matplotlib.pyplot as plt
import numpy as np


def load_time_data(time_file: Path) -> List[float]:
    """
    Load timing data from a time_n.json file.

    Args:
        time_file: Path to time_n.json file

    Returns:
        List of times (in seconds)
    """
    with open(time_file, 'r') as f:
        return json.load(f)


def compute_average_time(times: List[float]) -> float:
    """
    Compute average time from a list of times.

    Args:
        times: List of times

    Returns:
        Average time
    """
    return np.mean(times) if times else 0.0


def plot_average_times(
    dataset_dir: Path,
    llm_name: str,
    dataset_name: str,
    run_stats: List[Dict[str, Any]]
) -> Path:
    """
    Plot average run times across all problems.
    Stores plots in the same folder as time_n.json files.

    Args:
        dataset_dir: Directory containing time_n.json files
        llm_name: LLM name
        dataset_name: Dataset name
        run_stats: List of run statistics

    Returns:
        Path to the saved plot file
    """
    # Get times from all runs
    all_times = []
    for run_stat in run_stats:
        time_file = dataset_dir / f"time_{run_stat['run']}.json"
        if time_file.exists():
            times = load_time_data(time_file)
            all_times.append(times)

    if not all_times:
        raise ValueError("No timing data found")

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

    return plot_file


def aggregate_time_stats(dataset_dir: Path, num_runs: int) -> Dict[str, float]:
    """
    Aggregate timing statistics across multiple runs.

    Args:
        dataset_dir: Directory containing time_n.json files
        num_runs: Number of runs

    Returns:
        Dictionary with timing statistics
    """
    all_times = []
    for run_num in range(1, num_runs + 1):
        time_file = dataset_dir / f"time_{run_num}.json"
        if time_file.exists():
            times = load_time_data(time_file)
            all_times.extend(times)

    if not all_times:
        return {
            "avg_time": 0.0,
            "median_time": 0.0,
            "min_time": 0.0,
            "max_time": 0.0
        }

    return {
        "avg_time": float(np.mean(all_times)),
        "median_time": float(np.median(all_times)),
        "min_time": float(np.min(all_times)),
        "max_time": float(np.max(all_times))
    }
