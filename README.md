# Obfuscated-NNG

**Testing whether LLMs truly understand mathematical reasoning or just memorize training data.**

## What is this?

Large Language Models achieve impressive results on formal theorem proving benchmarks like MiniF2F. But is this real mathematical reasoning, or just pattern matching from training data contamination?

This project answers that question by testing frontier LLMs (GPT-4o, Claude 3.5 Sonnet, DeepSeek-R1) on the Lean Natural Number Game using **semantics-preserving obfuscation** — we systematically rename axioms, types, and theorem names while preserving the underlying logical structure.

## The Key Insight

If LLMs truly understand the mathematics, performance should remain consistent when names change. If they rely on memorization, performance degrades significantly under obfuscation — revealing a "robustness gap."

## What's Inside

-   **Dataset Generation**: Parse Lean files, create obfuscated versions with varying randomness levels
-   **Benchmarking Pipeline**: Test multiple LLMs across original and obfuscated datasets
-   **Verification System**: Automatically verify proof correctness using Lean compiler
-   **Analysis Tools**: Score results and quantify the robustness gap

## Quick Start

```bash
# Generate datasets
python3 generate_dataset.py

# Run benchmarks
export LLM_NAME="deepseek-r1"
python3 parallel_benchmark.py

# Score results
python3 score_llm.py
```

See [PIPELINE.md](PIPELINE.md) for complete documentation.

## Research Goal

Provide a rigorous metric for true mathematical understanding in neural theorem provers and expose the limitations of current static benchmarks.

## Results

```


============================================================
Statistics for deepseek-r1
============================================================

## Dataset Score (%) Std Error Time (s) Std Error

original 47.06 1.23 107.53 1.88
obfuscated_1 50.88 1.84 145.83 3.60
obfuscated_2 62.65 1.00 150.52 4.61
obfuscated_3 59.41 3.74 161.60 3.65
obfuscated_4 51.47 2.42 173.04 3.44
obfuscated_5 63.82 1.28 163.88 4.77

============================================================
Statistics for deepseek-prover-v2
============================================================

## Dataset Score (%) Std Error Time (s) Std Error

original 31.47 1.36 72.50 2.56
obfuscated_1 27.06 1.65 68.03 1.96
obfuscated_2 44.71 0.88 69.16 0.58
obfuscated_3 42.94 0.98 77.60 1.36
obfuscated_4 32.06 1.08 79.25 1.56
obfuscated_5 40.81 1.93 90.65 0.91

============================================================
Statistics for gpt-4o
============================================================

## Dataset Score (%) Std Error Time (s) Std Error

original 14.41 0.55 4.32 0.09
obfuscated_1 13.24 0.47 5.16 0.25
obfuscated_2 12.94 0.55 4.76 0.07
obfuscated_3 13.82 0.88 5.63 0.17
obfuscated_4 10.59 0.86 5.60 0.32
obfuscated_5 12.65 1.00 5.81 0.28

```
