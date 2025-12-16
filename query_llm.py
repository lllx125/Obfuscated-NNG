#!/usr/bin/env python3
"""
DeepSeek/Goedel Prover Experiment Runner
Automated querying of LLMs on theorem datasets with retry logic and result aggregation.
"""

import json
import time
import os
from pathlib import Path
from tqdm import tqdm
from llm_interface import ModelInterface

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

# LLM Selection: 
# "deepseek-prover-v2", "goedel-prover-v2"
# "deepseek-r1", "gemini-pro", "gpt-4o", "gemini-flash"
LLM_NAME = "deepseek-r1"

# Experiment Settings
MAX_RETRY = 3       # Max retries if output format is wrong
NUM_RUNS = 2        # How many full passes to run
START_RUN = 1       # Start index for run filenames (e.g., result_0.jsonl)

# Dataset folders to process
TARGET_DATASETS = [
    "original", 
    "obfuscated_1", 
    "obfuscated_2", 
    "obfuscated_3", 
    "obfuscated_4", 
    "obfuscated_5"
]

# ============================================================================
# CORE LOGIC
# ============================================================================

def run_experiment(llm_name: str, max_retry: int, num_runs: int, start_run: int, target_datasets: list):
    repo_folder = Path(".").resolve()
    dataset_base = repo_folder / "dataset"

    # Initialize Model with retry mechanism
    engine = ModelInterface(llm_name, max_retry)

    for run_idx in range(start_run, start_run + num_runs):
        print(f"\n{'#'*60}\nStarting Global RUN {run_idx}\n{'#'*60}\n")

        for ds_name in target_datasets:
            ds_path = dataset_base / ds_name
            queries_path = ds_path / "queries.jsonl"

            if not queries_path.exists():
                print(f"[!] Skipping {ds_name}: queries.jsonl not found.")
                continue

            # Setup Output Files
            output_dir = repo_folder / "results" / llm_name / ds_name
            output_dir.mkdir(parents=True, exist_ok=True)
            result_file_path = output_dir / f"result_{run_idx}.jsonl"
            time_file_path = output_dir / f"time_{run_idx}.json"

            # Clear existing files for this run to avoid appending to old runs
            if result_file_path.exists(): result_file_path.unlink()
            if time_file_path.exists(): time_file_path.unlink()

            with open(queries_path, "r", encoding="utf-8") as f:
                queries = [json.loads(line) for line in f if line.strip()]

            print(f"--> Processing: {ds_name} | Queries: {len(queries)}")

            times_buffer = [] # We keep this in memory to dump the full list every time

            pbar = tqdm(queries, desc=f"Run {run_idx}/{ds_name}", unit="thm")

            for query_data in pbar:
                # Generate response (retry logic is now inside llm_interface)
                start_t = time.time()
                valid_response = engine.generate(query_data)
                solve_time = time.time() - start_t

                # 1. Update Time Buffer
                times_buffer.append(solve_time)

                # 2. Write Result Immediately (Append Mode)
                with open(result_file_path, "a", encoding="utf-8") as f_res:
                    f_res.write(json.dumps(valid_response) + "\n")

                # 3. Update Time File Immediately (Overwrite with current list)
                with open(time_file_path, "w", encoding="utf-8") as f_time:
                    json.dump(times_buffer, f_time, indent=4)

            # End of Dataset Loop
            print(f"    ✓ Completed {ds_name}. Saved to {result_file_path}")

            # Cool-down Period
            print("    [zZz] Cooling down laptop for 2 minutes...")
            time.sleep(120)
            print("    [!] Resuming...")

if __name__ == "__main__":
    if not os.path.exists("dataset"):
        print("Error: 'dataset' folder not found.")
    else:
        run_experiment(LLM_NAME, MAX_RETRY, NUM_RUNS, START_RUN, TARGET_DATASETS)