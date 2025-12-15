#!/usr/bin/env python3
"""
Obfuscate theorem and definition names in JSONL files for LLM training.
Creates randomized names while preserving proof correctness.
Uses nlpaug for character-level augmentation.
"""

import json
import random
import re
import shutil
import sys
from pathlib import Path
from typing import Dict, Set
import nlpaug.augmenter.char as nac


# Configuration
RANDOMNESS_LEVEL = 1  # 0 = no randomness, 1 = maximum randomness
OBFUSCATION_SET = 2     # Which obfuscation set to create (1, 2, 3, ...)

# Lean-allowed characters for identifiers
# Avoid characters with special meaning in Lean syntax (λ Λ, Σ, Π)
LEAN_LETTERS = list("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")
LEAN_DIGITS = list("0123456789")
LEAN_SPECIAL = list("_'")
# Use only safe Unicode characters - removed: λ Λ Σ Π which have special meanings in Lean
LEAN_UNICODE = list("αβγδεζηθικμνξοπρστυφχψωΑΒΓΔΕΖΗΘΙΚΜΝΞΟΡΤΥΦΧΨΩℕℤℚℝℂ")

# All allowed characters (first char cannot be a digit or apostrophe)
# Apostrophe ' can only appear after the first character (used for primes like x')
FIRST_CHAR_ALLOWED = LEAN_LETTERS + ['_'] + LEAN_UNICODE
ALL_CHARS = LEAN_LETTERS + LEAN_SPECIAL + LEAN_UNICODE
ALL_CHARS_WITH_DIGITS = LEAN_LETTERS + LEAN_DIGITS + LEAN_SPECIAL + LEAN_UNICODE


# Names that should NOT be obfuscated (built-in Lean keywords and tactics)
RESERVED_NAMES = {
    'by', 'rfl', 'rw', 'intro', 'exact', 'apply', 'cases', 'induction',
    'simp', 'trivial', 'symm', 'sorry', 'with', 'at', 'repeat',
    'use', 'contrapose', 'tauto', 'True', 'False', 'Prop', 'Type',
    'fun', 'let', 'if', 'then', 'else', 'match', 'do', 'return',
    'where', 'import', 'namespace', 'open', 'end', 'def', 'theorem',
    'axiom', 'instance', 'inductive', 'opaque', 'Inhabited', 'default',
    'Add', 'Mul', 'Pow', 'LE', 'LT', 'Iff', 'HPow',
    # Structure field names that must match Lean stdlib (can't be obfuscated)
    'add', 'mul', 'pow', 'le', 'lt'
}


class NameObfuscator:
    """Handles name obfuscation using nlpaug augmenters."""

    def __init__(self, randomness_level: float):
        """
        Initialize the obfuscator with augmenters.

        Args:
            randomness_level: 0.0 = no randomness, 1.0 = maximum randomness
        """
        self.randomness_level = randomness_level
        self.vocab = ALL_CHARS_WITH_DIGITS

        # Calculate p_score using the specified formula
        p_score = randomness_level ** 2.5

        # Create substitute augmenter
        self.sub_aug = nac.RandomCharAug(
            action="substitute",
            aug_char_p=p_score,
            aug_word_p=1.0,           # Apply to the single word/identifier provided
            candidates=self.vocab,    # Use strictly Lean-allowed characters
            include_numeric=True,
            spec_char=ALL_CHARS_WITH_DIGITS  # Disable default symbols like @#$%
        )

        # Create insert augmenter
        self.ins_aug = nac.RandomCharAug(
            action="insert",
            aug_char_p=p_score * 0.4,  # Insertions happen less often than swaps
            aug_word_p=1.0,
            candidates=self.vocab
        )

        # Create delete augmenter
        self.del_aug = nac.RandomCharAug(
            action="delete",
            aug_char_p=p_score * 0.3,  # Delete cautiously
            aug_word_p=1.0
        )

    def obfuscate(self, original_name: str, used_names: Set[str]) -> str:
        """
        Obfuscate a name using nlpaug augmenters.

        Args:
            original_name: The original identifier name
            used_names: Set of already used names to avoid collisions

        Returns:
            Obfuscated name that is unique and valid
        """
        if self.randomness_level == 0.0:
            return original_name

        name = original_name

        # Apply augmentations in sequence: substitute -> insert -> delete
        try:
            # Step 1: Substitute characters
            name = self.sub_aug.augment(name)[0] if isinstance(self.sub_aug.augment(name), list) else self.sub_aug.augment(name)

            # Step 2: Insert characters
            name = self.ins_aug.augment(name)[0] if isinstance(self.ins_aug.augment(name), list) else self.ins_aug.augment(name)

            # Step 3: Delete characters
            name = self.del_aug.augment(name)[0] if isinstance(self.del_aug.augment(name), list) else self.del_aug.augment(name)

        except Exception as e:
            # If augmentation fails, fall back to original name with a suffix
            print(f"Warning: Augmentation failed for '{original_name}': {e}")
            name = original_name

        # Ensure name is not empty
        if not name or len(name.strip()) == 0:
            name = random.choice(LEAN_LETTERS) + original_name[:3]

        # Ensure name starts with a valid character (not digit or apostrophe)
        if name[0].isdigit() or name[0] == "'":
            name = random.choice(LEAN_LETTERS) + name

        # Ensure name contains only valid Lean characters
        name = ''.join(c for c in name if c in ALL_CHARS_WITH_DIGITS)
        if not name:
            name = random.choice(LEAN_LETTERS) + original_name[:3]

        # Ensure uniqueness
        base_name = name
        counter = 1
        while name in used_names or name in RESERVED_NAMES:
            name = f"{base_name}{counter}"
            counter += 1

        return name


def load_jsonl(file_path):
    """Load JSONL file into a list of dictionaries."""
    entries = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                entries.append(json.loads(line))
    return entries


def save_jsonl(entries, file_path):
    """Save entries to JSONL file."""
    file_path.parent.mkdir(parents=True, exist_ok=True)
    with open(file_path, 'w', encoding='utf-8') as f:
        for entry in entries:
            f.write(json.dumps(entry, ensure_ascii=False) + '\n')


def extract_all_names(header_entries, theorem_entries):
    """Extract all definition and theorem names that need to be obfuscated."""
    names = set()

    # Extract from header
    for entry in header_entries:
        name = entry['name']
        if name not in RESERVED_NAMES:
            names.add(name)

    # Extract from theorems
    for entry in theorem_entries:
        name = entry['name']
        if name not in RESERVED_NAMES:
            names.add(name)

    return names


def create_name_mapping(names: Set[str], randomness: float) -> Dict[str, str]:
    """Create a mapping from original names to obfuscated names."""
    mapping = {}
    used_names = set(RESERVED_NAMES)

    # Create obfuscator
    obfuscator = NameObfuscator(randomness)

    # Sort names for consistent ordering (important for deterministic obfuscation)
    sorted_names = sorted(names)

    for original_name in sorted_names:
        obfuscated = obfuscator.obfuscate(original_name, used_names)
        mapping[original_name] = obfuscated
        used_names.add(obfuscated)

    return mapping


def replace_name_in_text(text: str, name_mapping: Dict[str, str]) -> str:
    """
    Replace all occurrences of names in text.
    Uses word boundaries to avoid partial replacements.
    """
    # Sort by length (descending) to replace longer names first
    sorted_names = sorted(name_mapping.keys(), key=len, reverse=True)

    for original in sorted_names:
        obfuscated = name_mapping[original]
        # Use word boundaries to avoid partial replacements
        # \b doesn't work well with Unicode, so we use a custom pattern
        pattern = r'(?<![a-zA-Z0-9_\'])' + re.escape(original) + r'(?![a-zA-Z0-9_\'])'
        text = re.sub(pattern, obfuscated, text)

    return text


def obfuscate_header_entry(entry: dict, name_mapping: Dict[str, str]) -> dict:
    """Obfuscate a header entry."""
    obfuscated = entry.copy()

    # Replace name
    if entry['name'] in name_mapping:
        obfuscated['name'] = name_mapping[entry['name']]

    # Replace in code
    obfuscated['code'] = replace_name_in_text(entry['code'], name_mapping)

    return obfuscated


def obfuscate_theorem_entry(entry: dict, name_mapping: Dict[str, str]) -> dict:
    """Obfuscate a theorem entry."""
    obfuscated = entry.copy()

    # Replace name
    if entry['name'] in name_mapping:
        obfuscated['name'] = name_mapping[entry['name']]

    # Replace in statement
    obfuscated['statement'] = replace_name_in_text(entry['statement'], name_mapping)

    # Replace in proof
    obfuscated['proof'] = replace_name_in_text(entry['proof'], name_mapping)

    # Replace in known_theorems
    obfuscated['known_theorems'] = [
        replace_name_in_text(thm, name_mapping)
        for thm in entry['known_theorems']
    ]

    return obfuscated


def create_obfuscated_dataset(set_number, randomness_level, verbose=True):
    """
    Create an obfuscated dataset.

    Args:
        set_number: Dataset number (1, 2, 3, ...)
        randomness_level: Randomness level (0.0 to 1.0)
        verbose: Whether to print progress messages

    Returns:
        Path to the created obfuscated dataset folder
    """
    if verbose:
        print(f"=== Name Obfuscation (Randomness: {randomness_level}, Set: {set_number}) ===\n")

    # Setup directories
    original_dir = Path("dataset/original")
    obfuscated_dir = Path(f"dataset/obfuscated_{set_number}")

    # Load from original directory if it exists, otherwise from current directory
    if (original_dir / "header_definitions.jsonl").exists():
        original_header = original_dir / "header_definitions.jsonl"
        original_theorems = original_dir / "theorems.jsonl"
    else:
        original_header = Path("header_definitions.jsonl")
        original_theorems = Path("theorems.jsonl")

    # Copy original files to dataset/original (if not already there)
    if not (original_dir / "header_definitions.jsonl").exists():
        if verbose:
            print("Copying original files to dataset/original/...")
        original_dir.mkdir(parents=True, exist_ok=True)
        shutil.copy(original_header, original_dir / "header_definitions.jsonl")
        shutil.copy(original_theorems, original_dir / "theorems.jsonl")
        if verbose:
            print("✓ Original files copied\n")

    # Load original files
    if verbose:
        print("Loading original files...")
    header_entries = load_jsonl(original_header)
    theorem_entries = load_jsonl(original_theorems)
    if verbose:
        print(f"  Loaded {len(header_entries)} header definitions")
        print(f"  Loaded {len(theorem_entries)} theorems\n")

    # Extract all names
    if verbose:
        print("Extracting names to obfuscate...")
    names = extract_all_names(header_entries, theorem_entries)
    if verbose:
        print(f"  Found {len(names)} names to obfuscate\n")

    # Create name mapping
    if verbose:
        print(f"Creating name mapping (randomness: {randomness_level})...")
    random.seed(set_number)  # Use set number as seed for reproducibility
    name_mapping = create_name_mapping(names, randomness_level)

    # Show some examples
    if verbose:
        print("  Example mappings:")
        for original, obfuscated in list(name_mapping.items())[:5]:
            print(f"    {original} → {obfuscated}")
        print()

    # Obfuscate entries
    if verbose:
        print("Obfuscating entries...")
    obfuscated_header = [obfuscate_header_entry(e, name_mapping) for e in header_entries]
    obfuscated_theorems = [obfuscate_theorem_entry(e, name_mapping) for e in theorem_entries]
    if verbose:
        print("✓ Obfuscation complete\n")

    # Save obfuscated files
    if verbose:
        print(f"Saving to {obfuscated_dir}/...")
    save_jsonl(obfuscated_header, obfuscated_dir / "header_definitions.jsonl")
    save_jsonl(obfuscated_theorems, obfuscated_dir / "theorems.jsonl")

    # Save name mapping for reference
    mapping_file = obfuscated_dir / "name_mapping.json"
    with open(mapping_file, 'w', encoding='utf-8') as f:
        json.dump(name_mapping, f, indent=2, ensure_ascii=False)

    if verbose:
        print(f"✓ Saved obfuscated files")
        print(f"✓ Saved name mapping to {mapping_file}\n")
        print("="*60)
        print("✓ Obfuscation complete!")
        print(f"\nObfuscated files: {obfuscated_dir}/")
        print("="*60)

    return obfuscated_dir


def main():
    print(f"=== Name Obfuscation (Randomness: {RANDOMNESS_LEVEL}, Set: {OBFUSCATION_SET}) ===\n")

    try:
        obfuscated_dir = create_obfuscated_dataset(OBFUSCATION_SET, RANDOMNESS_LEVEL, verbose=True)
        print(f"\nTo verify, run:")
        print(f"  python3 generate_queries.py {obfuscated_dir}")
    except Exception as e:
        print(f"✗ Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
