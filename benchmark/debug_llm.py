import json
from pathlib import Path
from benchmark.llm_interface import ModelInterface
import time

TARGET_LLM = "gemini-pro"          # LLM to test
DATASET_NAME = "original"          # Folder name in /dataset/
THEOREM_ID = 1                    # The line number in queries.jsonl (1-indexed)
MAX_RETRY = 1                      # Number of retries for parsing

def test_llm(llm_name, dataset="original", thm_id=1, max_retry=1, verbose=True):
    """
    Test an LLM on a specific theorem.

    Args:
        llm_name: Name of the LLM to test
        dataset: Dataset name (default: "original")
        thm_id: Theorem ID (1-indexed, default: 1)
        max_retry: Number of retries for parsing (default: 1)
        verbose: Print detailed output (default: True)

    Returns:
        dict: Result with 'draft' and 'code' fields if successful
        None: If there was an error

    Raises:
        Exception: If LLM fails to generate a response
    """
    try:
        engine = ModelInterface(llm_name, max_retry)

        # 1. Load Query
        query_path = Path(f"dataset/{dataset}/queries.jsonl")
        if not query_path.exists():
            if verbose:
                print(f"Error: File {query_path} not found.")
            raise FileNotFoundError(f"Query file not found: {query_path}")

        with open(query_path, 'r') as f:
            lines = f.readlines()
            if thm_id > len(lines) or thm_id < 1:
                if verbose:
                    print(f"Error: Theorem ID {thm_id} out of range (Valid: 1-{len(lines)})")
                raise ValueError(f"Theorem ID {thm_id} out of range (Valid: 1-{len(lines)})")
            query_data = json.loads(lines[thm_id-1])

        if verbose:
            print(f"[*] Loaded Theorem ID {thm_id} from {dataset}")
            print(f"[*] Using model: {llm_name} with max_retry={max_retry}")

        # 2. Generate response (now returns dict with 'draft' and 'code' fields)
        start_time = time.time()
        result = engine.generate(query_data)

        if verbose:
            print("\n--- FINAL OUTPUT ---")
            print(json.dumps(result, indent=2, ensure_ascii=False))

            print("\n--- DRAFT ---")
            print(result['draft'])

            print("\n--- CODE ---")
            print(result['code'])

            print("\n--- TIME TAKEN ---")
            print(f"{time.time() - start_time:.2f} seconds")

        return result

    except Exception as e:
        if verbose:
            print(f"Error testing LLM '{llm_name}': {str(e)}")
        raise

def validate_llm(llm_name):
    """
    Validate that an LLM is working properly by running a quick test.

    Args:
        llm_name: Name of the LLM to validate

    Returns:
        bool: True if LLM is working, False otherwise
    """
    try:
        test_llm(llm_name, dataset="original", thm_id=1, max_retry=1, verbose=False)
        return True
    except Exception:
        return False

if __name__ == "__main__":
    test_llm(TARGET_LLM, DATASET_NAME, THEOREM_ID, MAX_RETRY)