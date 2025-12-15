#!/usr/bin/env python3
"""
DeepSeek/Goedel Prover Experiment Runner
Automated querying of LLMs on theorem datasets with retry logic and result aggregation.
"""

import json
import time
import os
import re
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from tqdm import tqdm
from llm_interface import ModelInterface

# Imports for local models
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig

# ============================================================================
# GLOBAL CONFIGURATION
# ============================================================================

# LLM Selection: 
# "deepseek-prover-v2", "goedel-prover-v2", "deepseek-r1", 
# "gemini-2.5", "gpt-4o-mini", "gemini-1.5-flash"
LLM_NAME = "deepseek-prover-v2"

# Experiment Settings
MAX_RETRY = 3       # Max retries if output format is wrong
NUM_RUNS = 1        # How many full passes to run
START_RUN = 0       # Start index for run filenames (e.g., result_0.jsonl)

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
# UTILITIES
# ============================================================================

def extract_json_from_response(text: str) -> Dict[str, Any]:
    """
    Robustly extracts JSON from text, handling markdown blocks and chatter.
    """
    try:
        # 1. Attempt clean parse
        return json.loads(text)
    except json.JSONDecodeError:
        pass

    # 2. Remove markdown code blocks (```json ... ```)
    clean_text = re.sub(r'```(?:json)?\s*', '', text)
    clean_text = re.sub(r'\s*```', '', clean_text)
    try:
        return json.loads(clean_text)
    except json.JSONDecodeError:
        pass

    # 3. Regex search for the outermost curly braces
    match = re.search(r'\{.*\}', text, re.DOTALL)
    if match:
        try:
            return json.loads(match.group(0))
        except json.JSONDecodeError:
            pass
            
    # 4. Fallback: Try to reconstruct if keys exist but structure is broken
    # (Simple heuristic for common failures)
    return None

def validate_schema(data: Any) -> bool:
    """Checks if the JSON has exactly the required fields."""
    if not isinstance(data, dict):
        return False
    return "draft" in data and "code" in data

# ============================================================================
# CORE LOGIC
# ============================================================================

def run_experiment(
    llm_name: str, 
    max_retry: int, 
    num_runs: int, 
    start_run: int
):
    """
    Main experiment controller.
    """
    repo_folder = Path(".").resolve()
    dataset_base = repo_folder / "dataset"
    
    # Initialize Model (Done once to save time)
    engine = ModelInterface(llm_name)

    # Loop through Runs
    for run_idx in range(start_run, start_run + num_runs):
        print(f"\n{'#'*60}")
        print(f"Starting Global RUN {run_idx}")
        print(f"{'#'*60}\n")

        # Loop through Datasets
        for ds_name in TARGET_DATASETS:
            ds_path = dataset_base / ds_name
            queries_path = ds_path / "queries.jsonl"
            
            if not queries_path.exists():
                print(f"[!] Skipping {ds_name}: queries.jsonl not found.")
                continue

            # Prepare Output Directories
            output_dir = repo_folder / "results" / llm_name / ds_name
            output_dir.mkdir(parents=True, exist_ok=True)
            
            result_file_path = output_dir / f"result_{run_idx}.jsonl"
            time_file_path = output_dir / f"time_{run_idx}.json"

            # Load Queries
            with open(queries_path, "r", encoding="utf-8") as f:
                queries = [json.loads(line) for line in f if line.strip()]
            
            print(f"--> Processing: {ds_name} | Queries: {len(queries)}")

            results_buffer = []
            times_buffer = []

            # Progress Bar
            pbar = tqdm(queries, desc=f"Run {run_idx}/{ds_name}", unit="thm")

            for query_data in pbar:
                # query_data is expected to be a list of messages: [{"role":..., "content":...}, ...]
                
                valid_response = None
                solve_time = 0.0
                
                # Retry Loop
                for attempt in range(max_retry + 1):
                    start_t = time.time()
                    raw_output = engine.generate(query_data)
                    duration = time.time() - start_t
                    
                    parsed_json = extract_json_from_response(raw_output)
                    
                    if validate_schema(parsed_json):
                        solve_time = duration # We record time of the successful generation
                        valid_response = parsed_json
                        break # Success
                    else:
                        # Update description to show retry
                        pbar.set_postfix({"status": f"Retry {attempt+1}/{max_retry}"})
                
                # Finalize Result
                if valid_response:
                    results_buffer.append(valid_response)
                    times_buffer.append(solve_time)
                else:
                    # Failed after max retries
                    results_buffer.append({
                        "draft": "failed",
                        "code": "sorry"
                    })
                    times_buffer.append(0.0) # 0.0 indicates failure/timeout

            # Save Results
            with open(result_file_path, "w", encoding="utf-8") as f:
                for res in results_buffer:
                    f.write(json.dumps(res) + "\n")
            
            with open(time_file_path, "w", encoding="utf-8") as f:
                json.dump(times_buffer, f, indent=4)

            print(f"    Saved: {result_file_path}")

# ============================================================================
# MAIN
# ============================================================================

def main():
    # Ensure dataset structure exists roughly before starting
    if not os.path.exists("dataset"):
        print("Error: 'dataset' folder not found in current directory.")
        return

    try:
        run_experiment(
            llm_name=LLM_NAME,
            max_retry=MAX_RETRY,
            num_runs=NUM_RUNS,
            start_run=START_RUN
        )
        print("\n[=] All experiments completed successfully.")
        
    except KeyboardInterrupt:
        print("\n[!] Execution interrupted by user.")
    except Exception as e:
        print(f"\n[!] Fatal Error: {e}")
        raise e

if __name__ == "__main__":
    main()