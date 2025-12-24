# Obfuscated-NNG

**Testing whether LLMs truly understand mathematical reasoning or just memorize training data.**

## What is this?

Large Language Models achieve impressive results on formal theorem proving benchmarks like MiniF2F. But is this real mathematical reasoning, or just pattern matching from training data contamination?

This project answers that question by testing frontier LLMs (GPT-4o, Claude 3.5 Sonnet, DeepSeek-R1) on the Lean Natural Number Game using **semantics-preserving obfuscation** — we systematically rename axioms, types, and theorem names while preserving the underlying logical structure.

## The Key Insight

If LLMs truly understand the mathematics, performance should remain consistent when names change. If they rely on memorization, performance degrades significantly under obfuscation — revealing a "robustness gap."

## What's Inside

- **Dataset Generation**: Parse Lean files, create obfuscated versions with varying randomness levels
- **Benchmarking Pipeline**: Test multiple LLMs across original and obfuscated datasets
- **Verification System**: Automatically verify proof correctness using Lean compiler
- **Analysis Tools**: Score results and quantify the robustness gap

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
