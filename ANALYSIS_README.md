# LLM Results Analysis Tool

## Overview

The `analyze_results.py` script is a comprehensive, modular analysis tool for LLM benchmark results. It processes data across different datasets (original and obfuscated versions), computes statistics, and generates multiple types of visualizations.

## Architecture

The tool is organized into two main components:

### 1. Main Analyzer (`analyze_results.py`)
- Orchestrates the analysis pipeline
- Runs each module sequentially
- Handles workflow and output coordination

### 2. Analysis Modules (`utils/analysis_modules.py`)
All core functionality is modularized into reusable functions:

#### Data Loading
- `load_statistics()` - Load statistics.json files
- `load_result_file()` - Load result JSONL files

#### Statistics Computation
- `compute_avg_and_std()` - Compute score/time averages and standard errors
- `compute_proof_lengths()` - Extract proof lengths from result files
- `compute_proof_length_stats()` - Compute proof length statistics

#### Visualization
- `plot_rate_and_time()` - Dual-axis scatter plot of scores and times
- `plot_correction_rate_per_problem()` - Line chart of per-problem correction rates
- `plot_proof_length_analysis()` - Proof length analysis with error bars

## Analysis Pipeline

For each LLM, the analyzer runs **5 sequential modules**:

### Module 1: Load Statistics
- Loads `statistics.json` from `results/{llm_name}/`
- Contains aggregated results across all datasets and runs

### Module 2: Compute Averages and Standard Errors
- Computes average scores (%) and times (s) for each dataset
- Calculates standard errors (SEM = std/√n)
- Optional printing of results table

### Module 3: Plot Rate and Time
- Creates dual-axis scatter plot
- **Left Y-axis**: Correct rate percentage (blue circles)
- **Right Y-axis**: Average time in seconds (orange squares)
- **X-axis**: Datasets from original to obfuscated_5
- Error bars show standard error
- No connecting lines (scatter style)

### Module 4: Plot Correction Rate Per Problem
- **NEW**: Line chart showing correction rate for each problem across 5 runs
- All 5 datasets plotted on same graph for comparison
- **X-axis**: Problem ID (1 to N)
- **Y-axis**: Correction rate percentage (0-100%)
- Each dataset shown as different colored line
- Helps identify which problems are consistently solved or failed

### Module 5: Proof Length Analysis
Consists of three sub-modules:

#### 5a: Compute Proof Lengths
- Extracts length of "draft" field from each result file
- Returns numpy array with shape: `(datasets, runs, problems)`
- Original dataset values set to 0 as specified

#### 5b: Compute Proof Length Statistics
- Calculates average proof length per dataset
- Computes standard error across all runs and problems
- Prints statistics table

#### 5c: Plot Proof Length Analysis
- Scatter plot with error bars
- **X-axis**: Datasets from original to obfuscated_5
- **Y-axis**: Average proof length (characters)
- Shows how proof verbosity changes with obfuscation

## Usage

### Basic Usage

```bash
python3 analyze_results.py
```

This runs the complete analysis pipeline for all configured LLMs.

### Programmatic Usage

You can import and use individual modules:

```python
from utils.analysis_modules import (
    load_statistics,
    compute_avg_and_std,
    compute_proof_lengths,
    plot_correction_rate_per_problem
)

# Load statistics
stats = load_statistics("gpt-4o")

# Compute metrics without printing
metrics = compute_avg_and_std("gpt-4o", stats, print_results=False)

# Analyze proof lengths
proof_lengths = compute_proof_lengths("gpt-4o")
print(f"Proof lengths shape: {proof_lengths.shape}")

# Generate specific plots
from pathlib import Path
plot_correction_rate_per_problem("gpt-4o", stats, Path("results/gpt-4o"))
```

### Customizing LLM List

Edit the `llm_list` variable in `main()`:

```python
def main():
    llm_list = [
        "deepseek-r1",
        "deepseek-prover-v2",
        "gpt-4o",
        # Add more LLMs here
    ]
    ...
```

### Configuration Options

The `analyze_results()` function accepts parameters:

```python
analyze_results(
    llm_name="gpt-4o",
    repo_folder=".",
    print_stats=True,      # Print statistics tables
    run_all_analyses=True  # Run all 5 modules
)
```

## Output

### Console Output

For each LLM, the analyzer prints:

1. **Score and Time Statistics Table**
   ```
   ============================================================
   Statistics for deepseek-r1
   ============================================================

   Dataset         Score (%)       Std Error       Time (s)        Std Error
   ---------------------------------------------------------------------------
   original           47.06            1.23          107.53            1.88
   obfuscated_1       50.88            1.84          145.83            3.60
   ...
   ```

2. **Proof Length Statistics Table**
   ```
   ============================================================
   Proof Length Statistics for deepseek-r1
   ============================================================

   Dataset         Avg Length      Std Error
   ---------------------------------------------
   obfuscated_1     1023.36           17.21
   obfuscated_2      975.73           16.52
   ...
   ```

### Generated Plots

For each LLM, **3 plots** are generated in `results/{llm_name}/`:

1. **`{llm_name}_analysis.png`**
   - Dual-axis scatter plot of scores and times
   - Shows overall performance trends

2. **`{llm_name}_correction_rate_per_problem.png`** ⭐ NEW
   - Line chart comparing all datasets
   - Per-problem correction rates across runs
   - Identifies problematic theorems

3. **`{llm_name}_proof_length.png`** ⭐ NEW
   - Proof length analysis with error bars
   - Shows verbosity trends across obfuscation levels

All plots are saved at **300 DPI** for publication quality.

## Requirements

- Python 3.7+
- numpy
- matplotlib

Install dependencies:
```bash
pip install numpy matplotlib
```

## File Structure

```
.
├── analyze_results.py              # Main analyzer
├── utils/
│   └── analysis_modules.py         # All analysis modules
└── results/
    └── {llm_name}/
        ├── statistics.json                              # Input
        ├── {dataset}/
        │   ├── result_1.jsonl                          # Input
        │   ├── result_2.jsonl                          # Input
        │   └── ...
        ├── {llm_name}_analysis.png                     # Output
        ├── {llm_name}_correction_rate_per_problem.png  # Output
        └── {llm_name}_proof_length.png                 # Output
```

## Statistics Calculation

### Scores and Times
- **Average Score**: Mean of `correct_rate * 100` across all runs
- **Average Time**: Mean of `avg_time` across all runs
- **Standard Error**: `std(values, ddof=1) / sqrt(n)`
  - Uses Bessel's correction (ddof=1) for unbiased estimate
  - Smaller error bars = more consistent performance

### Proof Lengths
- **Proof Length**: Number of characters in the "draft" field
- **Average Length**: Mean across all runs and problems
- **Standard Error**: SEM across all non-zero measurements
- **Note**: Original dataset values are set to 0 (not plotted)

### Correction Rates
- **Per-Problem Correction Rate**: `(correct_runs / total_runs) * 100`
- A problem is "correct" if it appears in neither `error_ids` nor `sorry_ids`
- Computed independently for each dataset

## Modular Design Benefits

1. **Separation of Concerns**: Analysis logic separated from orchestration
2. **Reusability**: Import individual functions into other scripts
3. **Testability**: Each module can be tested independently
4. **Maintainability**: Easy to update or add new analysis modules
5. **Flexibility**: Run specific analyses without full pipeline

## Example Workflows

### Workflow 1: Full Analysis
```python
from analyze_results import analyze_results

# Run complete pipeline with all 5 modules
results = analyze_results("deepseek-r1", print_stats=True, run_all_analyses=True)
```

### Workflow 2: Statistics Only (No Plots)
```python
from analyze_results import analyze_results

# Run modules 1-2 only
results = analyze_results("gpt-4o", print_stats=True, run_all_analyses=False)
```

### Workflow 3: Custom Analysis
```python
from utils.analysis_modules import (
    load_statistics,
    compute_proof_lengths,
    compute_proof_length_stats
)

# Custom workflow: analyze only proof lengths
stats = load_statistics("deepseek-prover-v2")
lengths = compute_proof_lengths("deepseek-prover-v2")
length_stats = compute_proof_length_stats(lengths)
```

### Workflow 4: Silent Processing
```python
from analyze_results import analyze_results

# Run without printing tables
results = analyze_results("gpt-4o", print_stats=False, run_all_analyses=True)
```

## Interpreting Results

### Rate and Time Plot
- **Decreasing scores** across obfuscation levels suggest memorization
- **Stable scores** suggest genuine reasoning capability
- **Increasing times** may indicate search/backtracking strategies

### Correction Rate Per Problem Plot
- **Horizontal lines at 100%**: Always-solved problems
- **Horizontal lines at 0%**: Never-solved problems
- **Convergence of datasets**: Problem difficulty independent of obfuscation
- **Divergence of datasets**: Obfuscation-sensitive problems

### Proof Length Plot
- **Increasing lengths**: More verbose explanations needed
- **Decreasing lengths**: More concise proofs (or giving up)
- **Stable lengths**: Consistent proof strategy

## Example Output

After running, you'll find plots like:
- `results/deepseek-r1/deepseek-r1_analysis.png`
- `results/deepseek-r1/deepseek-r1_correction_rate_per_problem.png` ⭐
- `results/deepseek-r1/deepseek-r1_proof_length.png` ⭐
- `results/deepseek-prover-v2/...`
- `results/gpt-4o/...`

Each LLM gets a complete set of 3 plots for comprehensive analysis.
