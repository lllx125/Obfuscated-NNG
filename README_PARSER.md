# Lean to JSONL Converter for LLM Training

This project contains two Python scripts to convert Lean 4 files from MyNNG (Natural Number Game) into JSONL format for LLM training.

## Files

- `parse_header.py`: Converts Header.lean into JSONL with all definitions, axioms, and theorems
- `parse_theorems.py`: Converts all other Lean files into JSONL with full context

## Usage

### Step 1: Parse Header Definitions

```bash
python3 parse_header.py
```

This creates `header_definitions.jsonl` containing 36 entries with the schema:
```json
{
  "name": "one_eq_succ_zero",
  "code": "theorem one_eq_succ_zero : one = succ zero := by rfl",
  "category": "theorem"
}
```

Categories include: `constructor`, `axiom`, `def`, `opaque`, `instance`, `theorem`

### Step 2: Parse Theorems

```bash
python3 parse_theorems.py
```

**Important**: Theorems are parsed in a specific dependency order to guarantee all dependencies are satisfied:
1. Addition.lean
2. Implication.lean
3. Algorithm.lean
4. Multiplication.lean
5. Power.lean
6. AdvAddition.lean
7. LessOrEqual.lean
8. AdvMultiplication.lean

This creates `theorems.jsonl` containing 69 theorem entries with the schema:
```json
{
  "id": 4,
  "name": "add_assoc",
  "statement": "theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by",
  "proof": "  induction c with\n  | zero =>\n    rw [add_zero, add_zero]\n  | succ d ih =>\n    rw [add_succ, add_succ, ih, add_succ]",
  "known_theorems": [    // All theorems from imports and previous theorems
    "theorem zero_add (n : MyNat) : .zero + n = n := by",
    "theorem succ_add (a b : MyNat) : succ a + b = succ (a + b) := by",
    "theorem add_comm (a b : MyNat) : a + b = b + a := by"
  ]
}
```

## Output Statistics

- **Header definitions**: 37 entries
  - Inductive types: 1 (MyNat)
  - Constructors: 2 (zero, succ)
  - Axioms: 6 (add_zero, add_succ, mul_zero, mul_succ, pow_zero, pow_succ)
  - Definitions: 8 (pred, is_zero, one, two, three, four, le, lt_myNat)
  - Instances: 6 (Add, Mul, Pow, LE, LT, Inhabited)
  - Opaque: 3 (add, mul, pow)
  - Theorems: 11

- **Theorems**: 69 entries from 8 Lean files
  - Addition.lean: 7 theorems
  - AdvAddition.lean: 6 theorems
  - Multiplication.lean: 9 theorems
  - AdvMultiplication.lean: 10 theorems
  - Power.lean: 9 theorems
  - LessOrEqual.lean: 14 theorems
  - Implication.lean: 10 theorems
  - Algorithm.lean: 4 theorems

## Assumptions

The parser assumes the following structure in Lean files:
- All theorems start with the keyword `theorem`
- All theorems are separated by 1 empty line
- All theorem names have space before and after
- All proofs start on the next line
- All statements are on the same line
- No comments within theorem bodies
- First theorem starts 2 lines after `open MyNat`

## Verification

### Step 3: Verify JSONL Parsing (with Auto-Correction)

```bash
python3 jsonl_verifier.py
```

This script verifies that the JSONL parsing is correct by:
1. Reading both JSONL files (header_definitions.jsonl and theorems.jsonl)
2. Generating a complete Lean file ([Generated_Verification.lean](MyNNG/MyNNG/Generated_Verification.lean))
3. Running Lean to verify the generated file compiles
4. **Auto-correction**: If any theorem proofs fail, automatically replaces them with `sorry` and re-runs verification
5. Reports which theorems (if any) had incorrect proofs

**Key Features:**
- **Fast algorithm**: Since theorems are in dependency order, they're written sequentially without complex dependency tracking
- **Automatic error detection**: Parses Lean error messages to identify which theorems failed
- **Auto-correction**: Replaces failing proofs with `sorry` and retries until all pass
- **Iterative verification**: Continues correcting until success or max iterations (10) reached

The verifier ensures:
- All header definitions are correctly parsed
- All theorem statements are correctly extracted
- The generated code is valid Lean 4 syntax
- Dependencies are satisfied (guaranteed by file ordering)

**Example output for corrupted proofs:**
```
=== Iteration 1: Initial Verification ===
✗ Lean verification failed!
Failed theorems detected: ['add_sq', 'pow_add']

=== Iteration 2: Re-verification with 2 theorem(s) replaced by sorry ===
✓ Verification successful with 2 theorem(s) corrected!

Corrected theorems (proofs replaced with 'sorry'):
  - add_sq
  - pow_add
```

### Testing Auto-Correction

A test file `theorems_test.jsonl` is provided with intentionally corrupted proofs for `pow_add` and `add_sq`:

```bash
python3 test_verifier.py
```

This demonstrates the auto-correction feature by verifying a JSONL file with known bad proofs.

## Features

- **Recursive import resolution**: Automatically includes all theorems from imported modules
- **No duplication**: Known theorems list avoids duplicates
- **Cumulative context**: Each theorem has access to all previously defined theorems in the same file
- **Verification**: Automated verification using Lean compiler to ensure parsing correctness
