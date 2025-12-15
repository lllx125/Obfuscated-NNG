#!/usr/bin/env python3
"""
Comprehensive dataset generation script.
Creates obfuscated datasets with queries and updates original dataset.
"""

import sys
from pathlib import Path
from jsonl_verifier import verify_dataset

# Try to import tqdm, but make it optional
try:
    from tqdm import tqdm
    HAS_TQDM = True
except ImportError:
    HAS_TQDM = False
    # Dummy tqdm for when the module is not available
    class tqdm:
        def __init__(self, *args, **kwargs):
            self.total = kwargs.get('total', 0)
            self.n = 0
        def __enter__(self):
            return self
        def __exit__(self, *args):
            pass
        def update(self, n=1):
            self.n += n
        def write(self, msg):
            print(msg)
        def set_description(self, desc):
            pass

# Import functions from other modules
from obfuscate_names import create_obfuscated_dataset
from generate_queries import generate_queries_for_dataset


def create_dataset(set_number, randomness_level, show_progress=True):
    """
    Create a complete dataset with obfuscation and queries.

    Args:
        set_number: Dataset number (1, 2, 3, ...)
        randomness_level: Randomness level (0.0 to 1.0)
        show_progress: Whether to show progress bar

    Returns:
        Tuple of (obfuscated_dir, queries_file)
    """
    if show_progress:
        print(f"\n{'='*60}")
        print(f"Creating Dataset {set_number} (Randomness: {randomness_level})")
        print(f"{'='*60}\n")

    # Create obfuscated dataset
    if show_progress:
        print(f"[1/2] Creating obfuscated dataset...")
    obfuscated_dir = create_obfuscated_dataset(set_number, randomness_level, verbose=False)
    if show_progress:
        print(f"✓ Obfuscated dataset created: {obfuscated_dir}\n")

    # Generate queries
    if show_progress:
        print(f"[2/2] Generating queries...")
    queries_file = generate_queries_for_dataset(obfuscated_dir, verbose=False)
    if show_progress:
        print(f"✓ Queries generated: {queries_file}\n")

    if show_progress:
        print(f"{'='*60}")
        print(f"✓ Dataset {set_number} complete!")
        print(f"{'='*60}")

    return obfuscated_dir, queries_file


def update_original_with_queries():
    """
    Create the original dataset and queries.
    This parses the Lean files and generates header_definitions.jsonl,
    theorems.jsonl, and queries.jsonl.

    Returns:
        Path to queries.jsonl file
    """
    from parse_header import create_header_definitions
    from parse_theorems import create_theorems_dataset

    original_dir = Path("dataset/original")

    # Create header_definitions.jsonl
    header_file = create_header_definitions(output_dir=original_dir, verbose=False)


    # Create theorems.jsonl
    theorems_file = create_theorems_dataset(output_dir=original_dir, verbose=False)


    # Generate queries
    queries_file = generate_queries_for_dataset(original_dir, verbose=False)


    error_id,sorry_id = verify_dataset( Path(original_dir/"header_definitions.jsonl"),
                                           Path(original_dir/"theorems.jsonl"))
    if error_id or sorry_id:
        print(f"✗ Original dataset verification failed.")


def generate_all_datasets():
     # Update original dataset
    print(f"\nUpdating original dataset with queries...")
    try:
        update_original_with_queries()
    except Exception as e:
        print(f"✗ Failed to update original dataset: {e}")

    # Dataset configurations
    datasets = [
        (1, 0.2),
        (2, 0.4),
        (3, 0.6),
        (4, 0.8),
        (5, 1.0),
    ]

    # Create obfuscated datasets
    for set_num, randomness in datasets:
        print(f"\nGenerating Dataset {set_num} with randomness {randomness}...")
        obfuscated_dir, _ = create_dataset(set_num, randomness, show_progress=False)
        error_id,sorry_id = verify_dataset(Path(obfuscated_dir / "header_definitions.jsonl"),
                                          Path(obfuscated_dir / "theorems.jsonl"))
        if error_id or sorry_id:
            print(f"✗ Dataset {set_num} verification failed.")
    
    print(f"\nAll datasets generated and verified successfully!")

if __name__ == "__main__":
    generate_all_datasets()
