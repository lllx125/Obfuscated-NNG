#!/usr/bin/env python3
"""
Generate LLM training queries from obfuscated dataset.
Creates a JSONL file with system/user prompts for each theorem.
"""

import json
from pathlib import Path
import sys


# Allowed tactics
ALLOWED_TACTICS = [
    "rw", "repeat rw", "nth_rewrite", "symm", "intro", "exact",
    "apply", "use", "trivial", "contradiction", "cases", "induction",
    "tauto", "contrapose!", "simp only", "revert", "split", "left", "right"
]
TACTIC_STRING = ", ".join(ALLOWED_TACTICS)


def load_jsonl(file_path):
    """Load JSONL file into a list of dictionaries."""
    entries = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                entries.append(json.loads(line))
    return entries


def generate_system_prompt(header_entries, available_theorems):
    """Generate the system prompt with full context."""
    # Build header context from all header entries
    header_context = "\n\n".join([entry['code'] for entry in header_entries])

    # Build available theorems string
    theorems_str = "\n".join(available_theorems)

    system_prompt = f"""### ROLE AND CONTEXT
You are a highly specialized AI designed for formal theorem proving in Lean 4.
Your goal is to solve a theorem within an alien mathematical system, strictly using the provided definitions and axioms.
Your knowledge of external libraries (like Mathlib) is IGNORED. You must base your proof ONLY on the definitions and theorems provided.

### CONSTRAINTS
- **Goal:** Produce a complete, formally verifiable Lean 4 proof for the given theorem.
- **Allowed Tactics:** You are limited to the following basic Lean tactics: {TACTIC_STRING}
- **Output:** Your entire response must be a single, raw JSON object. Do NOT wrap the JSON object in markdown blocks (e.g., ```json or ```lean).
- **SCHEMA:** The JSON object MUST contain exactly two fields: "draft" and "code".
  * **"draft" (string):** Your detailed, natural language proof plan and step-by-step reasoning.
  * **"code" (string):** The final, executable Lean 4 tactic code (everything after `:= by`).
  
  Example format:
  {{
    "draft": "The proof plan goes here. I will use induction on 'n'...",
    "code": "induction n with d hd\nrw [adXfkzΚro]"
  }}
### THE ALIEN SYSTEM DEFINITIONS (Context)
{header_context}

### Available theorems
{theorems_str}"""

    return system_prompt


def generate_user_prompt(theorem_statement):
    """Generate the user prompt for a specific theorem."""
    user_prompt = f"""### THEOREM TO PROVE
{theorem_statement}

Provide a detailed proof plan (draft) and the resulting Lean code (code) in the requested JSON format."""

    return user_prompt


def generate_query(header_entries, theorem_entry):
    """Generate a single query for a theorem."""
    system_prompt = generate_system_prompt(header_entries, theorem_entry['known_theorems'])
    user_prompt = generate_user_prompt(theorem_entry['statement'])

    return [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": user_prompt}
    ]


def generate_queries_for_dataset(folder_path, verbose=True):
    """
    Generate LLM queries for a dataset.

    Args:
        folder_path: Path to folder containing header_definitions.jsonl and theorems.jsonl
        verbose: Whether to print progress messages

    Returns:
        Path to the created queries.jsonl file
    """
    folder = Path(folder_path)

    if not folder.exists():
        raise FileNotFoundError(f"Folder {folder} does not exist")

    header_file = folder / "header_definitions.jsonl"
    theorems_file = folder / "theorems.jsonl"

    if not header_file.exists() or not theorems_file.exists():
        raise FileNotFoundError(f"Missing header_definitions.jsonl or theorems.jsonl in {folder}")

    if verbose:
        print(f"=== Generating LLM Queries from {folder} ===\n")

    # Load data
    if verbose:
        print("Loading data...")
    header_entries = load_jsonl(header_file)
    theorem_entries = load_jsonl(theorems_file)
    if verbose:
        print(f"  Loaded {len(header_entries)} header definitions")
        print(f"  Loaded {len(theorem_entries)} theorems\n")

    # Generate queries
    if verbose:
        print("Generating queries...")
    queries = []
    for theorem_entry in theorem_entries:
        query = generate_query(header_entries, theorem_entry)
        queries.append(query)

    if verbose:
        print(f"  Generated {len(queries)} queries\n")

    # Save to file
    output_file = folder / "queries.jsonl"
    if verbose:
        print(f"Saving to {output_file}...")
    with open(output_file, 'w', encoding='utf-8') as f:
        for query in queries:
            f.write(json.dumps(query, ensure_ascii=False) + '\n')

    if verbose:
        print(f"✓ Saved {len(queries)} queries")
        print(f"✓ Query generation complete!")
        print(f"Output: {output_file}\n")

    return output_file


def main():
    if len(sys.argv) < 2:
        print("Usage: python3 generate_queries.py <folder_name>")
        print("Example: python3 generate_queries.py dataset/obfuscated_1")
        sys.exit(1)

    folder_name = sys.argv[1]

    try:
        generate_queries_for_dataset(folder_name, verbose=True)
    except Exception as e:
        print(f"✗ Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
