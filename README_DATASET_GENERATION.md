# Dataset Generation System

Comprehensive system for generating obfuscated and original datasets with LLM training queries.

## Overview

This system provides reusable functions and a main orchestration script for:
1. Creating obfuscated datasets with configurable randomness
2. Generating LLM training queries for each dataset
3. Verifying dataset correctness with Lean compiler
4. Batch generation of multiple datasets with progress tracking

## File Structure

### Core Scripts (Refactored with Reusable Functions)

#### `jsonl_verifier.py`
- **Function**: `verify_dataset(folder_path, verbose=True) -> List[int]`
  - Verifies a dataset by running Lean compiler
  - Returns list of theorem IDs with incorrect proofs (empty if all correct)
  - Raises exceptions on errors

- **Command-line**: `python3 jsonl_verifier.py`
  - Uses paths from HEADER_PATH and THEOREMS_PATH constants

#### `obfuscate_names.py`
- **Function**: `create_obfuscated_dataset(set_number, randomness_level, verbose=True) -> Path`
  - Creates obfuscated dataset with specified randomness
  - Returns path to created dataset folder
  - Automatically copies to dataset/original/ if not exists

- **Command-line**: `python3 obfuscate_names.py`
  - Uses RANDOMNESS_LEVEL and OBFUSCATION_SET constants

#### `generate_queries.py`
- **Function**: `generate_queries_for_dataset(folder_path, verbose=True) -> Path`
  - Generates LLM training queries for a dataset
  - Returns path to created queries.jsonl file

- **Command-line**: `python3 generate_queries.py <folder_path>`

### Main Orchestration Script

#### `generate_dataset.py`
Comprehensive dataset generation with progress tracking.

**Functions:**

1. **`create_dataset(set_number, randomness_level, show_progress=True)`**
   - Creates complete dataset (obfuscation + queries)
   - Returns tuple of (obfuscated_dir, queries_file)

2. **`update_original_with_queries()`**
   - Generates queries for original (non-obfuscated) dataset
   - Returns path to queries.jsonl

3. **`generate_all_datasets()`**
   - Generates 5 obfuscated datasets + 1 original
   - Randomness levels: 0.2, 0.4, 0.6, 0.8, 1.0
   - Shows progress bar with tqdm
   - Returns success boolean

**Command-line:**
```bash
python3 generate_dataset.py
```

## Usage Examples

### 1. Generate All Datasets (Recommended)

```bash
python3 generate_dataset.py
```

This creates:
- `dataset/original/` - Original dataset with queries
- `dataset/obfuscated_1/` - Randomness 0.2
- `dataset/obfuscated_2/` - Randomness 0.4
- `dataset/obfuscated_3/` - Randomness 0.6
- `dataset/obfuscated_4/` - Randomness 0.8
- `dataset/obfuscated_5/` - Randomness 1.0

Each dataset contains:
- `header_definitions.jsonl` - 37 header definitions
- `theorems.jsonl` - 69 theorems
- `queries.jsonl` - 69 LLM training queries
- `name_mapping.json` - Name mapping (obfuscated only)

### 2. Programmatic Usage

```python
from generate_dataset import create_dataset, update_original_with_queries
from jsonl_verifier import verify_dataset

# Create a single obfuscated dataset
obf_dir, queries_file = create_dataset(set_number=6, randomness_level=0.75)
print(f"Created: {obf_dir}")
print(f"Queries: {queries_file}")

# Verify the dataset
error_ids = verify_dataset(obf_dir, verbose=False)
if error_ids:
    print(f"Found errors in theorems: {error_ids}")
else:
    print("All proofs correct!")

# Update original dataset
original_queries = update_original_with_queries()
print(f"Original queries: {original_queries}")
```

### 3. Individual Operations

```python
from obfuscate_names import create_obfuscated_dataset
from generate_queries import generate_queries_for_dataset

# Create obfuscated dataset only
obf_dir = create_obfuscated_dataset(set_number=7, randomness_level=0.5, verbose=True)

# Generate queries for existing dataset
queries_file = generate_queries_for_dataset("dataset/obfuscated_7", verbose=True)
```

### 4. Verification

```python
from jsonl_verifier import verify_dataset

# Verify dataset and get error IDs
error_ids = verify_dataset("dataset/obfuscated_1", verbose=True)

if not error_ids:
    print("Dataset is valid!")
else:
    print(f"Theorems with errors: {error_ids}")
```

## Output Format

### Dataset Folder Structure

```
dataset/
├── original/
│   ├── header_definitions.jsonl
│   ├── theorems.jsonl
│   └── queries.jsonl
├── obfuscated_1/
│   ├── header_definitions.jsonl
│   ├── theorems.jsonl
│   ├── queries.jsonl
│   └── name_mapping.json
├── obfuscated_2/
│   └── ...
...
```

### Query Format (queries.jsonl)

Each line is a JSON array with system and user messages:

```json
[
  {
    "role": "system",
    "content": "### ROLE AND CONTEXT\nYou are a highly specialized AI...\n### THE ALIEN SYSTEM DEFINITIONS (Context)\n...\n### Available theorems\n..."
  },
  {
    "role": "user",
    "content": "### THEOREM TO PROVE\ntheorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by\n\nProvide a detailed proof plan (draft) and the resulting Lean code (code) in the requested JSON format."
  }
]
```

## Progress Bar

The main script uses `tqdm` for progress tracking:

```
Overall Progress:  40%|████      | 2/5 [01:23<02:05, 41.7s/dataset]
✓ Dataset 1 (randomness=0.2): dataset/obfuscated_1
✓ Dataset 2 (randomness=0.4): dataset/obfuscated_2
```

## Error Handling

All functions raise appropriate exceptions:
- `FileNotFoundError` - Missing required files
- `RuntimeError` - Verification failures
- Other exceptions propagate with context

Command-line tools exit with appropriate codes:
- 0 = Success
- 1 = Error

## Randomness Levels

| Set | Randomness | Character Replacement | Name Length Change |
|-----|------------|----------------------|-------------------|
| 1   | 0.2        | ~20% of characters   | Small changes     |
| 2   | 0.4        | ~40% of characters   | Moderate changes  |
| 3   | 0.6        | ~60% of characters   | Significant changes|
| 4   | 0.8        | ~80% of characters   | Large changes     |
| 5   | 1.0        | All characters       | Maximum obfuscation|

## System Requirements

- Python 3.7+
- tqdm library: `pip install tqdm`
- Lean 4 with lake (for verification)

## Notes

- Datasets are deterministic (same set_number = same output)
- Original dataset is automatically created on first obfuscation
- Verification uses sequential error detection (finds first error, fixes, repeats)
- Reserved names (Lean keywords, struct fields) are never obfuscated
- Safe Unicode characters only (excludes λ, Λ, Σ, Π)
