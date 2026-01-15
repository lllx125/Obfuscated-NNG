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

Dataset         Score (%)       Std Error       Time (s)        Std Error
---------------------------------------------------------------------------
original           67.35            1.64          107.53            1.88
obfuscated_1       70.88            1.57          145.83            3.60
obfuscated_2       73.53            1.23          150.52            4.61
obfuscated_3       68.53            3.21          161.60            3.65
obfuscated_4       72.35            0.86          173.04            3.44
obfuscated_5       71.76            1.08          163.88            4.77


============================================================
One-Way ANOVA Results for deepseek-r1
============================================================

--- Analysis for Correct Rate (%) ---
F-statistic = 1.7697, p-value = 0.1573 (not significant)

--- Analysis for Average Time (s) ---
F-statistic = 37.5487, p-value = 0.0000 (SIGNIFICANT)


============================================================
Proof Length Statistics
============================================================

Dataset         Avg Length      Std Error
---------------------------------------------
original         1023.34           18.36
obfuscated_1     1023.36           17.21
obfuscated_2      975.73           16.52
obfuscated_3     1038.27           18.82
obfuscated_4      987.55           17.74
obfuscated_5     1008.04           19.14

Deleted old plot: results/deepseek-r1/deepseek-r1_analysis.png
Created combined analysis plot for deepseek-r1
============================================================
One-Way ANOVA Results for Proof Length
============================================================

--- Analysis for Proof Length (characters) ---
F-statistic = 1.7525, p-value = 0.1611 (not significant)


============================================================
Statistics for deepseek-prover-v2
============================================================

Dataset         Score (%)       Std Error       Time (s)        Std Error
---------------------------------------------------------------------------
original           42.35            1.50           72.50            2.56
obfuscated_1       41.18            1.40           68.03            1.96
obfuscated_2       45.59            1.04           69.16            0.58
obfuscated_3       43.53            1.00           77.60            1.36
obfuscated_4       43.24            1.10           79.25            1.56
obfuscated_5       41.91            1.95           90.65            0.91


============================================================
One-Way ANOVA Results for deepseek-prover-v2
============================================================

--- Analysis for Correct Rate (%) ---
F-statistic = 1.2733, p-value = 0.3077 (not significant)

--- Analysis for Average Time (s) ---
F-statistic = 26.4882, p-value = 0.0000 (SIGNIFICANT)


============================================================
Proof Length Statistics
============================================================

Dataset         Avg Length      Std Error
---------------------------------------------
original         1892.26           24.38
obfuscated_1     1892.90           26.81
obfuscated_2     1842.09           24.43
obfuscated_3     1891.21           27.81
obfuscated_4     1851.43           27.79
obfuscated_5     1827.82           25.03

Deleted old plot: results/deepseek-prover-v2/deepseek-prover-v2_analysis.png
Created combined analysis plot for deepseek-prover-v2
============================================================
One-Way ANOVA Results for Proof Length
============================================================

--- Analysis for Proof Length (characters) ---
F-statistic = 1.2610, p-value = 0.3128 (not significant)


============================================================
Statistics for gpt-4o
============================================================

Dataset         Score (%)       Std Error       Time (s)        Std Error
---------------------------------------------------------------------------
original           15.59            0.59            4.32            0.09
obfuscated_1       14.71            0.47            5.16            0.25
obfuscated_2       12.94            0.55            4.76            0.07
obfuscated_3       13.82            0.88            5.63            0.17
obfuscated_4       12.06            0.86            5.60            0.32
obfuscated_5       12.65            1.00            5.81            0.28


============================================================
One-Way ANOVA Results for gpt-4o
============================================================

--- Analysis for Correct Rate (%) ---
F-statistic = 3.1795, p-value = 0.0242 (SIGNIFICANT)

--- Analysis for Average Time (s) ---
F-statistic = 7.0089, p-value = 0.0004 (SIGNIFICANT)


============================================================
Proof Length Statistics
============================================================

Dataset         Avg Length      Std Error
---------------------------------------------
original          662.70            9.11
obfuscated_1      663.84            8.06
obfuscated_2      665.56            7.83
obfuscated_3      688.75            8.57
obfuscated_4      669.23            8.28
obfuscated_5      708.52            8.83

Deleted old plot: results/gpt-4o/gpt-4o_analysis.png
Created combined analysis plot for gpt-4o
============================================================
One-Way ANOVA Results for Proof Length
============================================================

--- Analysis for Proof Length (characters) ---
F-statistic = 4.7465, p-value = 0.0037 (SIGNIFICANT)


============================================================
Statistics for gpt-5
============================================================

Dataset         Score (%)       Std Error       Time (s)        Std Error
---------------------------------------------------------------------------
original           67.65            2.03           38.90            1.20
obfuscated_1       65.59            2.31           45.62            1.49
obfuscated_2       65.59            0.75           35.56            0.95
obfuscated_3       57.94            2.96           68.65            8.74
obfuscated_4       62.65            0.88           65.48            6.58
obfuscated_5       63.53            3.37           54.89            1.55


============================================================
One-Way ANOVA Results for gpt-5
============================================================

--- Analysis for Correct Rate (%) ---
F-statistic = 2.2118, p-value = 0.0863 (not significant)

--- Analysis for Average Time (s) ---
F-statistic = 8.9925, p-value = 0.0001 (SIGNIFICANT)


============================================================
Proof Length Statistics
============================================================

Dataset         Avg Length      Std Error
---------------------------------------------
original          569.41           12.92
obfuscated_1      622.83           15.52
obfuscated_2      627.74           15.48
obfuscated_3      634.97           16.17
obfuscated_4      636.04           15.92
obfuscated_5      640.56           16.07

Deleted old plot: results/gpt-5/gpt-5_analysis.png
Created combined analysis plot for gpt-5
============================================================
One-Way ANOVA Results for Proof Length
============================================================

--- Analysis for Proof Length (characters) ---
F-statistic = 2.9648, p-value = 0.0319 (SIGNIFICANT)


============================================================
Statistics for claude-sonnet-4.5
============================================================

Dataset         Score (%)       Std Error       Time (s)        Std Error
---------------------------------------------------------------------------
original           55.88            2.08            7.39            0.07
obfuscated_1       54.71            1.27            7.98            0.45
obfuscated_2       42.06            2.21            8.46            0.47
obfuscated_3       48.53            1.23            8.28            0.14
obfuscated_4       47.94            1.36            9.53            0.13
obfuscated_5       45.59            2.03           10.10            0.07


============================================================
One-Way ANOVA Results for claude-sonnet-4.5
============================================================

--- Analysis for Correct Rate (%) ---
F-statistic = 9.2482, p-value = 0.0001 (SIGNIFICANT)

--- Analysis for Average Time (s) ---
F-statistic = 12.8889, p-value = 0.0000 (SIGNIFICANT)


============================================================
Proof Length Statistics
============================================================

Dataset         Avg Length      Std Error
---------------------------------------------
original          673.66           19.07
obfuscated_1      636.74           16.33
obfuscated_2      698.46           20.57
obfuscated_3      662.15           18.52
obfuscated_4      791.14           34.34
obfuscated_5      726.38           22.22

Deleted old plot: results/claude-sonnet-4.5/claude-sonnet-4.5_analysis.png
Created combined analysis plot for claude-sonnet-4.5
============================================================
One-Way ANOVA Results for Proof Length
============================================================

--- Analysis for Proof Length (characters) ---
F-statistic = 5.9080, p-value = 0.0011 (SIGNIFICANT)

```
