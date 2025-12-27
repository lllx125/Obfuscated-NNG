#!/usr/bin/env python3
"""
Test JSONL verification by creating an error set with:
- Incorrect proofs (by swapping proofs between theorems)
- Sorry usage
- Banned tactics

Verifies that the analyzer correctly detects all error types.
"""

import json
import sys
from pathlib import Path
from typing import List, Dict

from verification.jsonl_generator import load_jsonl
from verification.verify_individual import verify_dataset


def create_error_dataset(
    header_path: Path,
    theorems_path: Path,
    output_path: Path,
    num_errors: int = 3,
    num_sorry: int = 2,
    num_banned: int = 2
) -> Dict[str, List[int]]:
    """
    Create a test dataset with intentional errors.

    Args:
        header_path: Path to header_definitions.jsonl
        theorems_path: Path to theorems.jsonl
        output_path: Path to output error dataset
        num_errors: Number of incorrect proofs to create (by swapping)
        num_sorry: Number of proofs to replace with 'sorry'
        num_banned: Number of proofs to inject banned tactics into

    Returns:
        Dictionary with expected error IDs:
        {
            "error_ids": List[int],
            "sorry_ids": List[int],
            "banned_ids": List[int]
        }
    """
    # Load theorems
    theorems = load_jsonl(theorems_path)

    if len(theorems) < max(num_errors * 2, num_sorry, num_banned):
        raise ValueError("Not enough theorems to create error set")

    # Track which IDs we modify
    expected_errors = {
        "error_ids": [],
        "sorry_ids": [],
        "banned_ids": []
    }

    # Create error proofs by swapping
    # Swap proofs between pairs of theorems
    for i in range(0, num_errors * 2, 2):
        if i + 1 < len(theorems):
            # Swap proofs
            theorems[i]['proof'], theorems[i + 1]['proof'] = theorems[i + 1]['proof'], theorems[i]['proof']
            # Record both as errors
            expected_errors["error_ids"].append(theorems[i]['id'])
            expected_errors["error_ids"].append(theorems[i + 1]['id'])

    # Add sorry to some proofs (use theorems after the swapped ones)
    sorry_start = num_errors * 2
    for i in range(sorry_start, min(sorry_start + num_sorry, len(theorems))):
        theorems[i]['proof'] = "  sorry"
        expected_errors["sorry_ids"].append(theorems[i]['id'])

    # Add banned tactics to some proofs (use theorems after the sorry ones)
    banned_start = sorry_start + num_sorry
    for i in range(banned_start, min(banned_start + num_banned, len(theorems))):
        # Inject 'simp' into the proof
        original_proof = theorems[i]['proof']
        # Add simp at the beginning of the proof
        theorems[i]['proof'] = "  simp\n" + original_proof
        expected_errors["banned_ids"].append(theorems[i]['id'])

    # Write error dataset
    with open(output_path, 'w', encoding='utf-8') as f:
        for theorem in theorems:
            f.write(json.dumps(theorem, ensure_ascii=False))
            f.write('\n')

    print(f"Created error dataset: {output_path}")
    print(f"  Expected errors: {len(expected_errors['error_ids'])} IDs")
    print(f"  Expected sorry: {len(expected_errors['sorry_ids'])} IDs")
    print(f"  Expected banned: {len(expected_errors['banned_ids'])} IDs")

    return expected_errors


def test_error_detection():
    """
    Main test function.
    Creates an error dataset and verifies that the analyzer detects all errors correctly.
    """
    # Paths
    header_path = Path("dataset/original/header_definitions.jsonl")
    theorems_path = Path("dataset/original/theorems.jsonl")
    error_dataset_path = Path("verification/test_error_dataset.jsonl")

    # Check if files exist
    if not header_path.exists():
        print(f"Error: {header_path} not found")
        print("Please run from the repository root")
        sys.exit(1)

    if not theorems_path.exists():
        print(f"Error: {theorems_path} not found")
        print("Please run from the repository root")
        sys.exit(1)

    print("="*60)
    print("JSONL Verification Test")
    print("="*60)

    # Create error dataset
    print("\n[1/2] Creating error dataset...")
    expected = create_error_dataset(
        header_path,
        theorems_path,
        error_dataset_path,
        num_errors=3,  # Will create 6 errors (3 pairs swapped)
        num_sorry=2,
        num_banned=2
    )

    # Verify the error dataset
    print("\n[2/2] Verifying error dataset...")
    try:
        error_ids, sorry_ids, banned_tactics_usage = verify_dataset(
            str(header_path),
            str(error_dataset_path),
            verbose=True
        )

        # Check results
        print("\n" + "="*60)
        print("TEST RESULTS")
        print("="*60)

        # Sort for comparison
        expected_error_ids = sorted(expected["error_ids"])
        expected_sorry_ids = sorted(expected["sorry_ids"])
        expected_banned_ids = sorted(expected["banned_ids"])
        detected_error_ids = sorted(error_ids)
        detected_sorry_ids = sorted(sorry_ids)
        detected_banned_ids = sorted(list(banned_tactics_usage.keys()))

        # Check errors
        print("\n1. Error Detection:")
        print(f"   Expected: {expected_error_ids}")
        print(f"   Detected: {detected_error_ids}")
        if detected_error_ids == expected_error_ids:
            print("   ✓ PASS")
            errors_pass = True
        else:
            print("   ✗ FAIL")
            errors_pass = False

        # Check sorry
        print("\n2. Sorry Detection:")
        print(f"   Expected: {expected_sorry_ids}")
        print(f"   Detected: {detected_sorry_ids}")
        if detected_sorry_ids == expected_sorry_ids:
            print("   ✓ PASS")
            sorry_pass = True
        else:
            print("   ✗ FAIL")
            sorry_pass = False

        # Check banned tactics
        print("\n3. Banned Tactics Detection:")
        print(f"   Expected: {expected_banned_ids}")
        print(f"   Detected: {detected_banned_ids}")
        if detected_banned_ids == expected_banned_ids:
            print("   ✓ PASS")
            banned_pass = True
        else:
            print("   ✗ FAIL")
            banned_pass = False

        # Overall result
        print("\n" + "="*60)
        if errors_pass and sorry_pass and banned_pass:
            print("✓ ALL TESTS PASSED")
            print("="*60)
            return True
        else:
            print("✗ SOME TESTS FAILED")
            print("="*60)
            return False

    except Exception as e:
        print(f"\n✗ TEST FAILED WITH EXCEPTION: {e}")
        import traceback
        traceback.print_exc()
        return False
    finally:
        # Clean up error dataset
        if error_dataset_path.exists():
            error_dataset_path.unlink()
            print(f"\nCleaned up: {error_dataset_path}")


def main():
    """Main entry point."""
    success = test_error_detection()
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
