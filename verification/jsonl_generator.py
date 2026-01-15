#!/usr/bin/env python3
"""
JSONL to Lean file generator.
Handles generation of Lean verification files from header and theorem JSONL files.
"""

import json
import re
from pathlib import Path
from typing import Dict, List, Set, Optional
from code_normalize import normalize_lean_code


# Lean code snippet to inject at the beginning of the generated file
LEAN_SNIPPET = '''import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto'''


def load_jsonl(file_path: Path) -> List[Dict]:
    """Load JSONL file into a list of dictionaries."""
    entries = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                entries.append(json.loads(line))
    return entries


def get_inductive_type_name(header_entries: List[Dict]) -> Optional[str]:
    """Extract the inductive type name from header (should be MyNat)."""
    for entry in header_entries:
        if entry.get('category') == 'inductive':
            return entry['name']
    return None


def parse_theorem_code(code: str) -> tuple:
    """
    Parse theorem code to extract statement, proof, and name.

    Args:
        code: Full theorem code including statement and proof

    Returns:
        Tuple of (name, statement, proof)
    """
    lines = code.split('\n')

    # Find the theorem declaration line
    theorem_line = None
    for i, line in enumerate(lines):
        if line.strip().startswith('theorem '):
            theorem_line = i
            break

    if theorem_line is None:
        raise ValueError(f"Could not find theorem declaration in code: {code[:100]}")

    # Extract theorem name from declaration
    # Pattern: theorem <name> ...
    match = re.match(r'theorem\s+([\w\u0370-\u03FF\u2100-\u214F\']+)', lines[theorem_line].strip())
    if not match:
        raise ValueError(f"Could not parse theorem name from: {lines[theorem_line]}")

    name = match.group(1)

    # Statement is the theorem declaration line
    statement = lines[theorem_line]

    # Proof is everything after the theorem declaration
    proof_lines = lines[theorem_line + 1:]
    proof = '\n'.join(proof_lines)

    return name, statement, proof


def generate_lean_for_theorems(
    header_entries: List[Dict],
    theorems_entries: List[Dict],
    output_file: Path,
    use_sorry_for: Optional[Set[str]] = None
) -> bool:
    """
    Generate a Lean verification file from header and theorem entries.

    Args:
        header_entries: List of header definition entries
        theorems_entries: List of theorem entries
        output_file: Path to output Lean file
        use_sorry_for: Set of theorem names to replace with 'sorry'

    Returns:
        True if successful, False otherwise
    """
    # Get the inductive type name
    type_name = get_inductive_type_name(header_entries)
    if not type_name:
        print("Error: Could not find inductive type in header definitions")
        return False

    if use_sorry_for is None:
        use_sorry_for = set()

    # Create the Lean file
    with open(output_file, 'w', encoding='utf-8') as f:
        # Write Lean snippet (imports and other code)
        f.write(LEAN_SNIPPET)
        f.write('\n\n')

        # Write inductive type definition (BEFORE namespace)
        for entry in header_entries:
            if entry['category'] == 'inductive':
                f.write(entry['code'])
                f.write('\n\n')
                break

        # Write namespace
        f.write(f'namespace {type_name}\n\n')

        # Write all other header definitions (INSIDE namespace)
        for entry in header_entries:
            category = entry['category']
            code = entry['code']

            # Skip inductive types and constructors (they're handled separately)
            if category in ['inductive', 'constructor']:
                continue

            # Write the code with proper spacing
            f.write(code)
            f.write('\n\n')

        # Write open statement
        f.write(f'open {type_name}\n\n')

        # Write all theorems in order (they're already in dependency order)
        for entry in theorems_entries:
            # Handle both old format (statement/proof/name) and new format (code)
            if 'statement' in entry:
                statement = entry['statement']
                proof = normalize_lean_code(entry['proof'])
                name = entry['name']
            elif 'code' in entry:
                # Parse code to extract statement, proof, and name
                name, statement, proof_raw = parse_theorem_code(entry['code'])
                proof = normalize_lean_code(proof_raw)
                # Store the name back in the entry for later use
                entry['name'] = name
            elif 'proof' in entry:
                # Parse code to extract statement, proof, and name
                name, statement, proof_raw = parse_theorem_code(entry['proof'])
                proof = normalize_lean_code(proof_raw)
                # Store the name back in the entry for later use
                entry['name'] = name
            else:
                raise ValueError(f"Entry missing both 'statement' and 'code' fields: {entry}")

            # Write the theorem statement
            f.write(statement)
            f.write('\n')

            # Write proof: use 'sorry' if requested, otherwise normal proof
            if name in use_sorry_for:
                f.write('  sorry\n\n')
            else:
                f.write(proof)
                f.write('\n\n')

        # Close namespace
        f.write(f'end {type_name}\n')

    return True


def generate_lean_for_results(
    header_file: Path,
    result_file: Path,
    theorems_file: Path,
    output_file: Path
) -> int:
    """
    Generate Lean file for verification from results_n.jsonl.

    Creates a generated_proofs_n.jsonl file by matching results with theorems,
    then generates the Lean verification file.

    Args:
        header_file: Path to header_definitions.jsonl
        result_file: Path to result_n.jsonl
        theorems_file: Path to theorems.jsonl
        output_file: Path to output Lean file

    Returns:
        Number of proofs generated
    """
    # Load files
    header_entries = load_jsonl(header_file)
    results = load_jsonl(result_file)
    theorems = load_jsonl(theorems_file)

    # Create generated proofs by matching line-by-line
    num_lines = len(results)

    if len(results) != len(theorems):
        print(f"Warning: Number of results ({len(results)}) doesn't match theorems ({len(theorems)})")
        print(f"Using first {num_lines} entries")

    # Create generated proofs entries
    generated_proofs = []
    for i in range(num_lines):
        # Take JSON from theorem and replace "proof" property with "code" from result
        theorem = theorems[i] if i < len(theorems) else {}
        result = results[i]

        # Copy theorem entry and replace proof
        proof_entry = theorem.copy()
        proof_entry["proof"] = result.get("code", result.get("proof", "sorry"))

        generated_proofs.append(proof_entry)

    # Generate Lean file
    generate_lean_for_theorems(header_entries, generated_proofs, output_file)

    return len(generated_proofs)

if __name__ == "__main__":
    generate_lean_for_results(
        header_file=Path("dataset/original/header_definitions.jsonl"),
        result_file=Path("dataset/original/theorems.jsonl"),
        theorems_file=Path("dataset/original/theorems.jsonl"),
        output_file=Path("generated_proofs.lean")
    )