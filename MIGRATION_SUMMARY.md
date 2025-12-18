# Code Organization Migration Summary

## Overview
Successfully reorganized the Obfuscated-NNG codebase into logical folders following the pipeline stages.

## Changes Made

### 1. Folder Structure Created
```
.
├── parsing/              # Stage 1: Parse Lean theorem files
├── obfuscation/          # Stage 2: Obfuscate theorem names
├── queries/              # Stage 3: Generate LLM queries
├── verification/         # Stage 4: Verify proofs in Lean
├── benchmark/            # Stage 5: Benchmark LLMs
├── utils/                # Utilities
├── generate_dataset.py   # Main: Generate datasets
├── parallel_benchmark.py # Main: Run benchmarks
└── score_llm.py          # Main: Score results
```

### 2. Files Moved

**parsing/**
- parse_theorems.py (from root)
- parse_header.py (from root)

**obfuscation/**
- obfuscate_names.py (from root)

**queries/**
- generate_queries.py (from root)

**verification/**
- jsonl_verifier.py (from root)
- test_verifier.py (from root)

**benchmark/**
- llm_interface.py (from root)
- query_llm.py (from root)
- debug_llm.py (from root)

**utils/**
- parse_output.py (from root)
- discord_notify.py (from root)

### 3. Import Updates

All imports have been updated to use the new module paths:

**generate_dataset.py:**
- `from jsonl_verifier import` → `from verification.jsonl_verifier import`
- `from obfuscate_names import` → `from obfuscation.obfuscate_names import`
- `from generate_queries import` → `from queries.generate_queries import`
- `from parse_header import` → `from parsing.parse_header import`
- `from parse_theorems import` → `from parsing.parse_theorems import`

**parallel_benchmark.py:**
- `from query_llm import` → `from benchmark.query_llm import`
- `from discord_notify import` → `from utils.discord_notify import`

**score_llm.py:**
- `from jsonl_verifier import` → `from verification.jsonl_verifier import`

**benchmark/query_llm.py:**
- `from llm_interface import` → `from benchmark.llm_interface import`

**benchmark/llm_interface.py:**
- `from parse_output import` → `from utils.parse_output import`

**benchmark/debug_llm.py:**
- `from llm_interface import` → `from benchmark.llm_interface import`

**verification/test_verifier.py:**
- `from jsonl_verifier import` → `from verification.jsonl_verifier import`

### 4. Files Kept in Root
As requested, only these three main entry points remain in the root directory:
- generate_dataset.py
- parallel_benchmark.py
- score_llm.py

### 5. Documentation Added
- **PIPELINE.md**: Comprehensive documentation of the pipeline, file descriptions, and usage instructions

## Verification
All main Python files compile successfully with the new import structure:
```bash
python3 -m py_compile generate_dataset.py parallel_benchmark.py score_llm.py
✓ All main files compile successfully
```

## Benefits
1. **Logical Organization**: Files are grouped by their stage in the pipeline
2. **Clear Structure**: Easy to understand the flow from parsing → obfuscation → queries → verification → benchmark → scoring
3. **Better Maintainability**: Related files are together, making them easier to find and modify
4. **Clean Root**: Only main entry points in root directory, reducing clutter
5. **Documented**: PIPELINE.md provides clear documentation of the entire codebase structure

## Next Steps
Run the pipeline to ensure everything works correctly:
```bash
python3 generate_dataset.py
python3 parallel_benchmark.py
python3 score_llm.py
```
