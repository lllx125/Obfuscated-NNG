#!/usr/bin/env python3
"""
Query LLMs on all dataset queries and generate results.
"""

import json
import time
import os
from pathlib import Path
from typing import Dict, List, Any
import re
import torch
from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig

# ============================================================================
# LLM SETTINGS
# ============================================================================
# Modify these settings to configure which LLM to use and run parameters

# LLM selection - choose one of the following:
# - "deepseek-prover-v2"
# - "goedel-prover-v2"
# - "deepseek-r1"
# - "gemini-2.5"
# - "gpt-4o-mini"
# - "gemini-1.5-flash"
LLM_NAME = "deepseek-prover-v2"

# Run configuration
MAX_RETRY = 3  # Maximum retries for format validation
NUM_RUNS = 1   # Number of complete runs
START_RUN = 0  # Starting run number (for continuing experiments)

# ============================================================================
# MODEL CACHE
# ============================================================================
# Cache loaded models to avoid reloading
_model_cache = {}


def load_prover_model(model_id: str):
    """
    Load a prover model with 4-bit quantization.
    Uses caching to avoid reloading the same model.

    Args:
        model_id: HuggingFace model ID (e.g., "deepseek-ai/DeepSeek-Prover-V2-7B")

    Returns:
        Tuple of (model, tokenizer)
    """
    if model_id in _model_cache:
        return _model_cache[model_id]

    print(f"Loading model: {model_id}")

    # Configure 4-bit quantization (from llm_test.py)
    quantization_config = BitsAndBytesConfig(
        load_in_4bit=True,
        bnb_4bit_quant_type="nf4",
        bnb_4bit_compute_dtype=torch.bfloat16,
        bnb_4bit_use_double_quant=True
    )

    # Load tokenizer & fix warnings (from llm_test.py)
    tokenizer = AutoTokenizer.from_pretrained(model_id, trust_remote_code=True)
    # Fix: Explicitly tell the model to use EOS as PAD
    tokenizer.pad_token = tokenizer.eos_token
    tokenizer.pad_token_id = tokenizer.eos_token_id

    # Load model
    model = AutoModelForCausalLM.from_pretrained(
        model_id,
        quantization_config=quantization_config,
        device_map="auto",
        trust_remote_code=True
    )

    _model_cache[model_id] = (model, tokenizer)
    print(f"✓ Model loaded: {model_id}")

    return model, tokenizer


def query_llm_with_retry(prompt: str, llm: str, max_retry: int) -> Dict[str, str]:
    """
    Query LLM with retry logic for format validation.

    Args:
        prompt: The prompt to send to the LLM
        llm: The LLM name/identifier
        max_retry: Maximum number of retries for format validation

    Returns:
        Dict with 'draft' and 'code' keys, or failure response
    """
    for attempt in range(max_retry + 1):
        try:
            # TODO: Implement actual LLM API call here
            # For now, this is a placeholder that would be replaced with actual API calls
            response_text = call_llm_api(prompt, llm)

            # Try to parse JSON response
            result = parse_llm_response(response_text)

            # Validate format
            if isinstance(result, dict) and 'draft' in result and 'code' in result:
                return result

        except Exception as e:
            if attempt == max_retry:
                # Max retries reached, return failure
                break

    # Return failure response
    return {
        "draft": "failed",
        "code": "sorry"
    }


def call_llm_api(prompt: str, llm: str) -> str:
    """
    Call the LLM API.

    Args:
        prompt: The prompt to send (should be JSON string containing query structure)
        llm: The LLM identifier

    Returns:
        The LLM response as a string
    """
    llm_lower = llm.lower()

    if "deepseek-prover-v2" in llm_lower:
        # DeepSeek-Prover-V2-7B
        model_id = "deepseek-ai/DeepSeek-Prover-V2-7B"
        return call_prover_model(prompt, model_id)

    elif "goedel-prover-v2" in llm_lower:
        # Goedel-Prover-V2-8B
        model_id = "Goedel-LM/Goedel-Prover-V2-8B"
        return call_prover_model(prompt, model_id)

    elif "deepseek-r1" in llm_lower:
        # TODO: Call DeepSeek-R1 API
        raise NotImplementedError("DeepSeek-R1 API not yet implemented")

    elif "gemini-2.5" in llm_lower:
        # TODO: Call Gemini-2.5 API
        raise NotImplementedError("Gemini-2.5 API not yet implemented")

    elif "gpt-4o-mini" in llm_lower:
        # TODO: Call GPT-4o Mini API
        raise NotImplementedError("GPT-4o Mini API not yet implemented")

    elif "gemini-1.5-flash" in llm_lower:
        # TODO: Call Gemini-1.5 Flash API
        raise NotImplementedError("Gemini-1.5 Flash API not yet implemented")

    else:
        raise ValueError(f"Unknown LLM: {llm}")


def call_prover_model(prompt: str, model_id: str) -> str:
    """
    Call a prover model (DeepSeek-Prover-V2 or Goedel-Prover-V2).

    Args:
        prompt: JSON string containing the query structure
        model_id: HuggingFace model ID

    Returns:
        The model's response as a string
    """
    # Parse the query structure
    query = json.loads(prompt)

    # Extract the actual prompt content
    # The query has 'system_prompt' and 'user_prompt' fields
    system_content = query.get('system_prompt', '')
    user_content = query.get('user_prompt', '')

    # Format as chat messages
    chat = [
        {"role": "user", "content": f"{system_content}\n\n{user_content}"}
    ]

    # Load model and tokenizer
    model, tokenizer = load_prover_model(model_id)

    # Apply chat template and tokenize
    inputs = tokenizer.apply_chat_template(
        chat,
        tokenize=True,
        add_generation_prompt=True,
        return_tensors="pt"
    ).to(model.device)

    # Generate response (from llm_test.py: max_new_tokens=8192)
    outputs = model.generate(inputs, max_new_tokens=8192)

    # Decode the output
    response = tokenizer.batch_decode(outputs, skip_special_tokens=True)[0]

    return response


def parse_llm_response(response_text: str) -> Dict[str, str]:
    """
    Parse LLM response to extract JSON.

    Args:
        response_text: Raw response from LLM

    Returns:
        Parsed dict with 'draft' and 'code' keys
    """
    # Try to find JSON in the response
    # Remove markdown code blocks if present
    cleaned = response_text.strip()

    # Remove ```json and ``` markers
    if cleaned.startswith("```"):
        lines = cleaned.split('\n')
        if lines[0].startswith("```"):
            lines = lines[1:]
        if lines and lines[-1].strip() == "```":
            lines = lines[:-1]
        cleaned = '\n'.join(lines)

    # Try to parse as JSON
    try:
        result = json.loads(cleaned)
        return result
    except json.JSONDecodeError:
        # Try to find JSON object in the text
        # Look for { ... } pattern
        match = re.search(r'\{[^{}]*"draft"[^{}]*"code"[^{}]*\}', cleaned, re.DOTALL)
        if match:
            try:
                result = json.loads(match.group(0))
                return result
            except:
                pass

        raise ValueError("Could not parse JSON from response")


def run_queries_on_dataset(
    dataset_path,
    llm: str,
    max_retry: int,
    num_runs: int,
    start_run: int,
):
    """
    Run all queries from a dataset folder.

    Args:
        dataset_path: Path to dataset folder (e.g., "dataset/obfuscated_1")
        llm: The LLM identifier
        max_retry: Maximum number of retries for format validation
        num_runs: Number of runs to perform
        start_run: Starting run number
        repo_folder: Repository root folder
    """
    dataset_path = Path(dataset_path)
    queries_file = dataset_path / "queries.jsonl"

    if not queries_file.exists():
        print(f"Queries file not found: {queries_file}")
        return

    # Load all queries
    queries = []
    with open(queries_file, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                queries.append(json.loads(line))

    print(f"Loaded {len(queries)} queries from {queries_file}")

    # Determine dataset type from path
    dataset_name = dataset_path.name  # e.g., "obfuscated_1" or "original"

    # Create results directory
    results_dir = Path("results") / llm / dataset_name
    results_dir.mkdir(parents=True, exist_ok=True)

    # Run for each run number
    for run_num in range(start_run, start_run + num_runs):
        print(f"\n{'='*60}")
        print(f"Run {run_num} - {llm} - {dataset_name}")
        print(f"{'='*60}")

        results = []
        times = []

        for idx, query in enumerate(queries):
            print(f"Processing query {idx + 1}/{len(queries)}...", end=" ")

            # Extract the prompt (the system and user messages form the complete prompt)
            prompt = json.dumps(query)  # The entire query structure is the prompt

            # Time the query
            start_time = time.time()
            result = query_llm_with_retry(prompt, llm, max_retry)
            end_time = time.time()

            elapsed = end_time - start_time
            times.append(elapsed)
            results.append(result)

            print(f"✓ ({elapsed:.2f}s)")

        # Save results
        result_file = results_dir / f"result_{run_num}.jsonl"
        with open(result_file, 'w', encoding='utf-8') as f:
            for result in results:
                f.write(json.dumps(result, ensure_ascii=False))
                f.write('\n')

        # Save times
        time_file = results_dir / f"time_{run_num}.json"
        with open(time_file, 'w', encoding='utf-8') as f:
            json.dump(times, f, indent=2)

        print(f"\nResults saved to {result_file}")
        print(f"Times saved to {time_file}")
        print(f"Average time: {sum(times)/len(times):.2f}s")


def main():
    # Configuration
    llm = LLM_NAME  # Set from global variable below
    max_retry = MAX_RETRY
    num_runs = NUM_RUNS
    start_run = START_RUN

    # Get all dataset folders
    dataset_base = Path("dataset")
    if not dataset_base.exists():
        print(f"Dataset folder not found: {dataset_base}")
        return

    # Find all dataset folders with queries.jsonl
    dataset_folders = []
    for folder in dataset_base.iterdir():
        if folder.is_dir() and (folder / "queries.jsonl").exists():
            dataset_folders.append(folder)

    if not dataset_folders:
        print("No dataset folders with queries.jsonl found")
        return

    print(f"Found {len(dataset_folders)} dataset folders:")
    for folder in dataset_folders:
        print(f"  - {folder}")

    # Run queries on each dataset
    for dataset_folder in dataset_folders:
        run_queries_on_dataset(
            dataset_path=str(dataset_folder),
            llm=llm,
            max_retry=max_retry,
            num_runs=num_runs,
            start_run=start_run,
            repo_folder="."
        )

if __name__ == "__main__":
    main()
