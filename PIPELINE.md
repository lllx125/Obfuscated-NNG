# Obfuscated-NNG Pipeline

This document describes the codebase organization and pipeline for generating obfuscated theorem datasets and benchmarking LLM theorem provers.

## Pipeline Overview

The pipeline follows this logical flow:

```
Parse Lean Files → Obfuscate Names → Generate Queries → Create Dataset → Verify in Lean → Benchmark LLMs → Score Results
```

## Folder Structure

```
.
├── parsing/              # Stage 1: Parse Lean theorem files
│   ├── parse_theorems.py       # Parse theorems from Lean files
│   └── parse_header.py         # Parse header definitions from Header.lean
│
├── obfuscation/          # Stage 2: Obfuscate theorem names
│   └── obfuscate_names.py      # Create obfuscated datasets with randomized names
│
├── queries/              # Stage 3: Generate LLM queries
│   └── generate_queries.py     # Create training queries from datasets
│
├── verification/         # Stage 4: Verify proofs in Lean
│   ├── jsonl_verifier.py       # Verify JSONL datasets by generating Lean files
│   └── test_verifier.py        # Test script for verification
│
├── benchmark/            # Stage 5: Benchmark LLMs
│   ├── llm_interface.py        # Unified interface for all LLMs (local + API)
│   ├── query_llm.py            # Run experiments on LLM models
│   ├── async_benchmark.py      # Async parallel benchmark runner (not used)
│   └── debug_llm.py            # Debug/test single theorem queries
│
├── utils/                # Utilities
│   ├── parse_output.py         # Parse LLM outputs (JSON/Lean code)
│   └── discord_notify.py       # Discord webhook notifications
│
├── generate_dataset.py   # Main: Generate all datasets (original + obfuscated)
├── parallel_benchmark.py # Main: Run benchmarks (kept in root as requested)
└── score_llm.py          # Main: Score and verify LLM results (kept in root as requested)
```

## File Descriptions (Logical Order)

### Stage 1: Parsing
- **[parse_theorems.py](parsing/parse_theorems.py)**: Parses Lean theorem files and converts them into JSONL format. Extracts theorem statements, proofs, and known theorems from imports. Creates `theorems.jsonl`.

- **[parse_header.py](parsing/parse_header.py)**: Parses `Header.lean` to extract all definitions, axioms, and theorems. Creates `header_definitions.jsonl` with categories (inductive, axiom, def, theorem, etc.).

### Stage 2: Obfuscation
- **[obfuscate_names.py](obfuscation/obfuscate_names.py)**: Obfuscates theorem and definition names using character-level augmentation (nlpaug). Creates multiple obfuscated datasets with different randomness levels. Preserves proof correctness while making names unrecognizable.

### Stage 3: Query Generation
- **[generate_queries.py](queries/generate_queries.py)**: Generates LLM training queries from datasets. Creates system prompts with header context and available theorems, plus user prompts for specific theorems. Outputs `queries.jsonl`.

### Stage 4: Verification
- **[jsonl_verifier.py](verification/jsonl_verifier.py)**: Verifies JSONL datasets by generating Lean files and running the Lean compiler. Sequentially identifies incorrect proofs, detects 'sorry' usage, and flags banned tactics. Core verification logic.

- **[test_verifier.py](verification/test_verifier.py)**: Test script for the verifier with a sample dataset.

### Stage 5: Benchmarking
- **[llm_interface.py](benchmark/llm_interface.py)**: Unified interface for all LLMs (local models like DeepSeek-Prover-V2, Goedel-Prover, and API models like GPT-4o, Gemini, DeepSeek-R1). Handles generation with retry logic and memory management.

- **[query_llm.py](benchmark/query_llm.py)**: Experiment runner that queries LLMs on theorem datasets. Handles multiple runs, retry logic, and saves results incrementally. Supports progress callbacks.

- **[async_benchmark.py](benchmark/async_benchmark.py)**: Asynchronous benchmark runner for parallel execution across multiple LLMs and datasets. Not currently used but available for future parallel runs.

- **[debug_llm.py](benchmark/debug_llm.py)**: Simple test script to debug a single theorem query. Useful for testing LLM behavior on specific problems.

### Stage 6: Scoring
- **[score_llm.py](score_llm.py)**: Scores LLM results by verifying generated proofs and computing statistics. Creates `generated_proofs_n.jsonl` files from results, verifies them, and generates plots and statistics.

### Utilities
- **[parse_output.py](utils/parse_output.py)**: Parses LLM outputs. Extracts JSON or Lean code from responses, handles malformed outputs, and validates schemas.

- **[discord_notify.py](utils/discord_notify.py)**: Discord webhook notification system. Sends progress updates and crash reports during long-running jobs.

### Main Entry Points
- **[generate_dataset.py](generate_dataset.py)**: Comprehensive dataset generation script. Creates obfuscated datasets with queries and updates the original dataset. Main entry point for dataset creation.

- **[parallel_benchmark.py](parallel_benchmark.py)**: Parallel LLM benchmark runner. Main entry point for running benchmarks across multiple LLMs and datasets.

- **[score_llm.py](score_llm.py)**: Main entry point for scoring and analyzing LLM results.

## Usage

### 1. Generate Datasets
```bash
python3 generate_dataset.py
```
This will:
- Parse Lean files (Header.lean and theorem files)
- Create original dataset in `dataset/original/`
- Generate 5 obfuscated datasets with varying randomness levels
- Create queries for all datasets

### 2. Run Benchmarks
```bash
export LLM_NAME="deepseek-r1"
export NUM_RUNS="5"
export START_RUN="1"
python3 parallel_benchmark.py
```

### 3. Score Results
```bash
export LLM_NAME="deepseek-r1"
python3 score_llm.py
```

## Dataset Structure

Each dataset folder contains:
- `header_definitions.jsonl`: All definitions, axioms, and theorems from Header.lean
- `theorems.jsonl`: All theorems with statements, proofs, and known theorems
- `queries.jsonl`: LLM training queries
- `name_mapping.json`: Mapping from original to obfuscated names (obfuscated datasets only)

## Results Structure

Results are saved in `results/{llm_name}/{dataset_name}/`:
- `result_n.jsonl`: LLM outputs for run n
- `time_n.json`: Timing information for run n
- `generated_proofs_n.jsonl`: Verified proofs for run n
- `statistics.json`: Overall statistics
- `avg_times.png`: Plot of average solving times
