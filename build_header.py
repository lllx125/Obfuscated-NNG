import json
import os
from lean_dojo import *

# --- Configuration ---
REPO = LeanGitRepo("https://github.com/leanprover-community/NNG4", "e55da341a671ee4a4debcffe77efbff2c3d3316f")

# The Files we want FULL CODE from (The Core Library)
CORE_FILES = [
    "Game/MyNat/Definition.lean",
    "Game/MyNat/PeanoAxioms.lean",
    "Game/MyNat/Addition.lean",
    "Game/MyNat/Multiplication.lean",
    "Game/MyNat/TutorialLemmas.lean",
    "Game/MyNat/Power.lean",
    "Game/MyNat/LE.lean",
    "Game/MyNat/Inequality.lean",
    "Game/MyNat/DecidableEq.lean",  
]

# Mock dependencies: Theorems we want to convert to "axioms" so that DecidableEQ compiles
mock_axioms = [
    {
        'full_name': 'succ_ne_succ',
        'code': 'theorem succ_ne_succ (m n : MyNat) (h : m ≠ n) : succ m ≠ succ n := sorry' 
    },
    {
        'full_name': 'zero_ne_succ',
        'code': 'theorem zero_ne_succ (n : MyNat) : 0 ≠ succ n := sorry'
    },
    {
        'full_name': 'succ_ne_zero',
        'code': 'theorem succ_ne_zero (n : MyNat) : succ n ≠ 0 := sorry'
    }
]


def main():
    print("[-] Loading cached repo...")
    traced_repo = trace(REPO) # Loads instantly from cache
    print("[+] Repo loaded.")

    header_elements = []
    
    # --- STEP 1: Add Mock Axioms ---
    print("[-] Adding Mock Axioms...")
    header_elements.extend(mock_axioms)

    # --- STEP 2: Extract Core Library ---
    print("[-] Extracting Core Library...")
    for filepath in CORE_FILES:
        traced_file = traced_repo.get_traced_file(filepath)
        premise_definitons = traced_file.get_premise_definitions()
        for pd in premise_definitons:
            pd.pop('start')
            pd.pop('end')
            pd.pop('kind')
            header_elements.append(pd)
        print(f"    [+] Extracted {filepath}")

    # --- STEP 3: Save Header JSON ---
    output = {"header_blocks": header_elements}
    with open("header.json", "w") as f:
        json.dump(output, f, indent=2)
    print("[SUCCESS] header.json created.")

if __name__ == "__main__":
    main()