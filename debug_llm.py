import json
from pathlib import Path
from llm_interface import ModelInterface
import time

TARGET_LLM = "deepseek-r1"          # LLM to test
DATASET_NAME = "obfuscated_1"          # Folder name in /dataset/
THEOREM_ID = 67                    # The line number in queries.jsonl (1-indexed)
MAX_RETRY = 1                      # Number of retries for parsing

def test_llm(llm_name, dataset, thm_id, max_retry):
    engine = ModelInterface(llm_name, max_retry)

    # 1. Load Query
    query_path = Path(f"dataset/{dataset}/queries.jsonl")
    if not query_path.exists():
        print(f"Error: File {query_path} not found.")
        return

    with open(query_path, 'r') as f:
        lines = f.readlines()
        if thm_id > len(lines) or thm_id < 1:
            print(f"Error: Theorem ID {thm_id} out of range (Valid: 1-{len(lines)})")
            return
        query_data = json.loads(lines[thm_id-1])

    print(f"[*] Loaded Theorem ID {thm_id} from {dataset}")
    print(f"[*] Using model: {llm_name} with max_retry={max_retry}")

    # 2. Generate response (now returns dict with 'draft' and 'code' fields)
    start_time = time.time()
    result = engine.generate(query_data)

    print("\n--- FINAL OUTPUT ---")
    print(json.dumps(result, indent=2, ensure_ascii=False))

    print("\n--- DRAFT ---")
    print(result['draft'])

    print("\n--- CODE ---")
    print(result['code'])
    
    print("\n--- TIME TAKEN ---")
    print(f"{time.time() - start_time:.2f} seconds")

if __name__ == "__main__":
    test_llm(TARGET_LLM, DATASET_NAME, THEOREM_ID, MAX_RETRY)