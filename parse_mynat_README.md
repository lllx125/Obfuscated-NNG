# MyNat Definitions Parser

## Overview

This script parses all Lean 4 files in the `externals/NNG4/Game/MyNat/` directory and extracts definitions, axioms, theorems, and instances into a JSONL (JSON Lines) format.

## Usage

```bash
python3 parse_mynat_definitions.py
```

## Output

The script generates `mynat_definitions.jsonl` with one JSON object per line.

### JSON Schema

Each entry has three fields:

```json
{
    "full_name": "theorem_name",
    "code": "theorem theorem_name (args) : type := sorry",
    "category": "axiom|theorem|definition|instance|inductive"
}
```

### Categories

- **axiom**: Foundational axioms (add_zero, add_succ, mul_zero, mul_succ, pow_zero, pow_succ)
- **theorem**: Proven theorems (succ_inj, zero_ne_succ, one_eq_succ_zero, etc.)
- **definition**: Type and function definitions (one, le, lt_myNat)
- **instance**: Type class instances (Add, Mul, LE, LT, DecidableEq, Inhabited, etc.)
- **inductive**: Inductive type definitions (MyNat)

## Statistics

After running, you'll see:

```
✓ Saved 31 definitions to mynat_definitions.jsonl

Summary:
  axiom: 6
  definition: 4
  inductive: 1
  instance: 10
  theorem: 10
```

## Examples

### Axiom
```json
{"full_name": "add_zero", "code": "axiom add_zero (a: MyNat) : a + 0 = a", "category": "axiom"}
```

### Theorem
```json
{"full_name": "succ_inj", "code": "theorem succ_inj (a b : ℕ) (h : succ a = succ b) : a = b := sorry", "category": "theorem"}
```

### Instance
```json
{"full_name": "instAdd", "code": "instance instAdd : Add MyNat where := sorry", "category": "instance"}
```

## Features

- ✅ Parses all MyNat folder files automatically
- ✅ Handles multi-line declarations
- ✅ Removes comments to avoid parsing errors
- ✅ Replaces proofs with `sorry` for consistency
- ✅ Outputs valid JSONL format
- ✅ Provides summary statistics

## Files Processed

- Addition.lean
- DecidableEq.lean
- DecidableTests.lean
- Definition.lean
- Inequality.lean
- LE.lean
- Multiplication.lean
- PeanoAxioms.lean
- Power.lean
- TutorialLemmas.lean

## Next Steps

This output can be used to:
1. Generate a MyNat header file for LLM testing
2. Create name mappings for obfuscation
3. Build a catalog of available theorems/axioms
4. Construct context for level datasets
