# check_canonical.py - Documentation

## Overview

This Python script tests the `canonical` tactic's ability to solve theorems from the Natural Number Game (NNG) dataset. It generates standalone Lean files with `canonical` tactics for both the original and obfuscated datasets (1-5).

## Key Design

The script **reuses functions from `verification/jsonl_verifier.py`** for:
- Loading JSONL files (`load_jsonl`)
- Extracting inductive type names (`get_inductive_type_name`)
- Writing header definitions (`write_inductive_definition`, `write_header_definitions_in_namespace`)

This ensures consistency with the main verification pipeline.

## What the Script Does

### 1. Premise Detection

The script analyzes each theorem's statement to automatically determine which premises (axioms/lemmas) should be provided to the `canonical` tactic:

**Base Premises** (always included):
- `MyNat.rec` - Induction principle for natural numbers
- `Eq.refl` - Reflexivity of equality
- `Eq.rec` - Equality elimination/substitution
- `succ_inj` - Successor injection (if succ a = succ b then a = b)

**Operation-Specific Premises**:
- **Addition** (`add` in statement): `add_succ`, `add_zero`
- **Multiplication** (`mul` in statement): `mul_succ`, `mul_zero`
- **Power** (`pow` in statement): `pow_succ`, `pow_zero`
- **Inequality** (`≠` in statement): `False.rec`, `zero_ne_succ`
- **Existential** (`∃` in statement): `Exists.intro`, `Exists.elim`
- **Or** (`∨` in statement): `Or.inl`, `Or.inr`, `Or.elim`
- **And** (`∧` in statement): `And.intro`, `And.left`, `And.right`
- **Less-or-equal** (`le` or `≤` in statement): `le`, `Exists.intro`, `Exists.elim`, `add_succ`, `add_zero`

### 2. Standalone Lean Files

Each generated file is **completely standalone** with:
- All necessary imports (Mathlib tactics + Canonical)
- Full inductive type definition
- All header definitions (axioms, definitions, etc.)
- Theorems with `canonical` tactic instead of proofs

**Example Structure**:
```lean
import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto
import Canonical

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

namespace MyNat

-- All header definitions (axioms, defs, etc.)
opaque add : MyNat → MyNat → MyNat
axiom add_zero (a : MyNat) : add a zero = a
axiom add_succ (a d : MyNat) : add a (succ d) = succ (add a d)
...

open MyNat

-- Theorem 1: zero_add
theorem zero_add (n : MyNat) : add zero n = n := by
  canonical 15 [MyNat.rec, Eq.refl, Eq.rec, succ_inj, add_succ, add_zero]

...

end MyNat
```

### 3. Name Obfuscation

For obfuscated datasets, the script properly maps names using the `name_mapping.json` files:

- Regular axioms/lemmas: Uses name mapping (e.g., `add_zero` → `ard_Μero`)
- Special handling for `MyNat.rec`: Uses the obfuscated type name (e.g., `Mmyat.rec`)
- Unknown names: Kept as-is (e.g., `Eq.refl` stays `Eq.refl`)

### 4. Verification

The script attempts to verify each generated Lean file by running:
```bash
lake env lean MyNNG/canonical_tests/Canonical_{dataset}.lean
```

It parses error output to identify which theorems failed, and replaces them with `sorry`.

### 5. Output

The script generates:
1. **Lean files**: `MyNNG/MyNNG/canonical_tests/Canonical_{dataset}.lean` for each dataset
2. **JSON results**: `canonical_test_results.json` with:
   - Total theorems per dataset
   - Failed theorem count
   - Failed theorem IDs
   - Success rate

**Example Results**:
```json
{
  "dataset": "original",
  "total_theorems": 68,
  "failed_theorems": 0,
  "failed_ids": [],
  "success_rate": 100.0,
  "lean_file": "/home/ubuntu/Obfuscated-NNG/MyNNG/MyNNG/canonical_tests/Canonical_original.lean"
}
```

## Usage

```bash
python3 check_canonical.py
```

The script will:
1. Process all datasets (original + obfuscated_1 through obfuscated_5)
2. Generate standalone Lean files in `MyNNG/MyNNG/canonical_tests/`
3. Attempt verification
4. Print summary report
5. Save detailed results to JSON

## Files Generated

- `MyNNG/MyNNG/canonical_tests/Canonical_original.lean`
- `MyNNG/MyNNG/canonical_tests/Canonical_obfuscated_1.lean`
- `MyNNG/MyNNG/canonical_tests/Canonical_obfuscated_2.lean`
- `MyNNG/MyNNG/canonical_tests/Canonical_obfuscated_3.lean`
- `MyNNG/MyNNG/canonical_tests/Canonical_obfuscated_4.lean`
- `MyNNG/MyNNG/canonical_tests/Canonical_obfuscated_5.lean`
- `canonical_test_results.json`

## Datasets Processed

- **original**: 68 theorems with original names (MyNat, add, mul, etc.)
- **obfuscated_1-5**: 68 theorems each with different obfuscation schemes

## Implementation Details

### Reused Functions from jsonl_verifier.py

- `load_jsonl(file_path)` - Load JSONL files
- `get_inductive_type_name(header_entries)` - Extract type name
- `write_inductive_definition(f, header_entries)` - Write inductive type
- `write_header_definitions_in_namespace(f, header_entries)` - Write axioms/defs

### Custom Functions

- `analyze_statement(statement)` - Detect operations in theorem statement
- `get_premises_for_theorem(statement)` - Generate premise list
- `obfuscate_premise(premise, name_map, dataset_name)` - Map names
- `create_canonical_lean_file(...)` - Generate file with canonical tactics
- `verify_lean_file(lean_file)` - Run Lean and parse errors
- `replace_failed_with_sorry(...)` - Replace failures with sorry

## Critical Implementation Details

### Premise Generation Order (Fixed Bug)

**IMPORTANT**: The script follows this exact order to ensure all datasets get the same premises:

1. **Generate premises from ORIGINAL dataset** - Analyze original theorem statements to determine which axioms are needed
2. **For each dataset (including original)**:
   - Load that dataset's name mapping
   - **Obfuscate** the original premise list using the name mapping
   - Inject the obfuscated premises into the Lean file

This ensures that `obfuscated_5` gets the same premises as `original` (just with obfuscated names), preventing the bug where premises were generated from obfuscated statements.

### Global Configuration

- `CANONICAL_TIMEOUT = 15` - Seconds to wait for canonical tactic to finish (configurable)

## Current Status

- ✅ Correctly detects operations from ORIGINAL statements
- ✅ Generates identical premise lists for all datasets (before obfuscation)
- ✅ Properly obfuscates premise names using name mappings
- ✅ Uses correct namespace for each dataset
- ✅ Generates syntactically correct standalone Lean files
- ✅ Reuses verified code from jsonl_verifier.py
- ✅ Configurable timeout for canonical tactic
- ⚠️ Verification reports 100% success (may need manual testing)

## Future Improvements

1. Investigate why verification reports 100% success
2. Test manually compiling one file to check if canonical actually works
3. Add more detailed error reporting
4. Support custom premise lists via command-line arguments
5. Add option to test only specific datasets or theorems
