# Obfuscated-NNG

## Introduction

This repository facilitates a research project. The following is the abstract:

> While Large Language Models have achieved significant success on formal mathematics benchmarks such as MiniF2F, it remains unclear whether these results stem from genuine logical reasoning or semantic pattern matching against pre-training data. This paper identifies Architectural Reasoning—the ability to synthesize formal proofs using exclusively local axioms and definitions within an alien math system—as the key ability for future automated theorem discovery AI. We use the Obfuscated Natural Number Game, a novel benchmark to evaluate Architectural Reasoning. By renaming identifiers in the Natural Number Game math system in Lean 4, we created a zero-knowledge, closed environment. We evaluate frontier models, finding a universal latency tax where obfuscation significantly increases inference time. The results also reveal a divergence in robustness: while general models (Claude-Sonnet-4.5, GPT-4o) suffer significant performance degradation, reasoning models (DeepSeek-R1, GPT-5, DeepSeek-Prover-V2) maintain the same accuracy despite the absence of semantic cues. These findings provide a rigorous metric for assessing the true capacity for mathematical reasoning.

## Main Funalities

- `MyNNG` is a sub-repository that contains the implementation of the Natural Number Game in Lean 4. It includes 68 problems and their solutions organized into different levels. It provides a more organized structure for parsing.
- `generate_dataset.py` generates obfuscated datasets and queries for benchmarking. Note that this program cannot be generalized to other Lean projects without modifications. LeanDojo is recommended for more general Lean code parsing.
- `parallel_benchmark.py` feeds the query to LLMs with multi-threads using the `benchmark/llm_interface.py` as configuration for APIs.
- `score_llm.py` scores the results returned by LLMs using the Lean compiler.

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

Note: This repository contains files (`canonical` and `graph_analysis`) irrelevant to the main research project, they are for experimental purposes only.
