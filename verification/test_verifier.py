#!/usr/bin/env python3
"""Test script for jsonl_verifier.py with theorems_test.jsonl"""

from verification.jsonl_verifier import verify_dataset

print("=== Testing jsonl_verifier.py with theorems_test.jsonl ===\n")

header_path = "dataset/original/header_definitions.jsonl"
theorems_path = "theorems_test.jsonl"

try:
    error_ids, sorry_ids = verify_dataset(header_path, theorems_path, verbose=True)

    print("\n=== TEST RESULTS ===")
    print(f"Error IDs: {error_ids}")
    print(f"Sorry IDs: {sorry_ids}")

    # Expect to find ID 1 (zero_add) in sorry_ids since it has "sorry" as proof
    if 1 in sorry_ids or 1 in error_ids:
        print("\n✓ TEST PASSED: zero_add with 'sorry' was correctly identified")
    else:
        print("\n✗ TEST FAILED: zero_add with 'sorry' was not identified")

except Exception as e:
    print(f"\n✗ TEST FAILED with exception: {e}")
    import traceback
    traceback.print_exc()
