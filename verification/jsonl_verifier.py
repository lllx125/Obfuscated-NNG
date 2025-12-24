#!/usr/bin/env python3
"""
Verify JSONL parsing by generating a Lean file and running Lean to verify it.
Sequentially identifies incorrect proofs by fixing one at a time.
"""

import json
import subprocess
import sys
import re
from pathlib import Path


# Configuration
HEADER_PATH = Path("dataset/obfuscated_3/header_definitions.jsonl")
THEOREMS_PATH = Path("theorems_test.jsonl")

OUTPUT_LEAN_FILE = Path("MyNNG/MyNNG/Generated_Verification.lean")

# Lean code snippet to inject at the beginning of the generated file
LEAN_SNIPPET = '''import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto'''

# Banned tactics that should be reported but not marked as errors
BANNED_TACTICS = ['simp']

def fix_indentation(code: str) -> str:
    """
    Stage 1: Fix Indentation and Structure
    Lean 4 is whitespace-sensitive (especially with by blocks and multi-line tactics).
    """
    # 1. Standardize indentation to two spaces per level (assuming LLM uses spaces/tabs mixed)
    code = code.replace('\t', '  ')

    # 2. Fix 'by' structure: Ensure 'by' is on its own line or followed by a newline/space
    # This addresses cases like "theorem T := by exact H"
    # FIXED: Calculate proper indentation by capturing leading whitespace and adding 2 spaces
    def fix_by_indentation(match):
        leading_ws = match.group(1)  # Capture any leading whitespace before :=
        by_part = match.group(2)     # The ':= by ' part
        tactic = match.group(3)      # The tactic after 'by'
        # Calculate indentation: count spaces in leading_ws, add 2 more
        indent_count = len(leading_ws)
        new_indent = ' ' * (indent_count + 2)
        return f'{leading_ws}{by_part}\n{new_indent}{tactic}'

    code = re.sub(r'^(\s*)(:=\s*by\s+)([^\n])', fix_by_indentation, code, flags=re.MULTILINE)

    # 3. Add indentation after block starters (e.g., induction, cases, repeat)
    # Target: induction n with d hd => rw [h]
    code = re.sub(r'(induction|cases|match|have|suffices)\s+.*?\s*=>\s*([^\n])',
                  lambda m: m.group(0).replace(m.group(2), f'\n  {m.group(2)}'), code, flags=re.DOTALL)

    # 4. Standardize 'with' blocks (often misformatted by LLMs)
    # Target: | zero => rw [h]
    code = re.sub(r'(\s*\|\s*[\w\d]+\s*=>\s*)([^\n])', r'\1\n  \2', code)

    # Only strip trailing whitespace, preserve leading indentation
    return code.rstrip()


def fix_syntax(code: str) -> str:
    """
    Stage 2: Fix Versioning and Syntax
    This addresses issues where the LLM is trained on old Lean 4 versions or Mathlib code.
    """
    # 1. Old Mathlib.Tactic.Use vs Lean Core 'exists'
    # NNG uses 'use', but if the LLM defaults to the old way, fix it.
    code = code.replace('exists ', 'use ')

    # 2. Lean 3/Early Lean 4 vs Modern Lean 4
    code = code.replace('begin', 'by')
    code = code.replace('end', '')  # Modern Lean 4 often doesn't need 'end' markers

    # 3. Remove excess 'show' keywords (often superfluous in modern Lean)
    code = re.sub(r'show\s+.*?,\s*', '', code)

    # 4. Remove unnecessary parentheses around single terms
    code = re.sub(r'\((\w+)\)', r'\1', code)

    return code



def strip_theorem_declaration(code: str) -> str:
    """
    Stage 0: Strip Theorem Declaration
    Remove the theorem declaration line and all lines above it.
    This should be done before all other normalizations.

    Args:
        code: Raw Lean code string potentially containing theorem declaration

    Returns:
        Code with theorem declaration and preceding lines removed
    """
    lines = code.split('\n')

    # Find the line containing the theorem statement name
    # Look for pattern: theorem <name> ... := by
    theorem_line_idx = -1
    for idx, line in enumerate(lines):
        # Match theorem declaration (theorem keyword followed by name)
        if "theorem " in line:
            theorem_line_idx = idx

    # If we found a theorem declaration, remove it and all lines above it
    if theorem_line_idx >= 0:
        
        # Keep only lines after the theorem declaration
        remaining_lines = lines[theorem_line_idx + 1:]
        return '\n'.join(remaining_lines)

    # If no theorem declaration found, return code as-is
    return code

def normalize_lean_code(code: str) -> str:
    """
    Normalize Lean code by fixing indentation and syntax issues.

    Args:
        code: Raw Lean code string

    Returns:
        Normalized Lean code string
    """
    # Stage 0: Strip theorem declaration (done first, before all normalizations)
    code = strip_theorem_declaration(code)

    # Stage 1: Fix indentation
    code = fix_indentation(code)

    # Stage 2: Fix syntax
    code = fix_syntax(code)

    return code


def load_jsonl(file_path):
    """Load JSONL file into a list of dictionaries."""
    entries = []
    with open(file_path, 'r', encoding='utf-8') as f:
        for line in f:
            if line.strip():
                entries.append(json.loads(line))
    return entries

def get_inductive_type_name(header_entries):
    """Extract the inductive type name from header (should be MyNat)."""
    for entry in header_entries:
        if entry.get('category') == 'inductive':
            return entry['name']
    return None


def write_inductive_definition(f, header_entries):
    """Write only the inductive type definition."""
    for entry in header_entries:
        if entry['category'] == 'inductive':
            f.write(entry['code'])
            f.write('\n\n')
            return


def write_header_definitions_in_namespace(f, header_entries):
    """Write all header definitions (except inductive and constructors) inside namespace."""
    for entry in header_entries:
        category = entry['category']
        code = entry['code']

        # Skip inductive types and constructors (they're handled separately)
        if category in ['inductive', 'constructor']:
            continue

        # Write the code with proper spacing
        f.write(code)
        f.write('\n\n')


def parse_theorem_code(code):
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


def generate_lean_file(header_entries, theorems_entries, use_sorry_for=None, original_proofs=None):
    """
    Generate the Lean verification file.
    use_sorry_for: set of theorem names to replace with 'sorry'
    original_proofs: dict mapping theorem names to their original incorrect proofs (for replacement)
    """
    # Get the inductive type name
    type_name = get_inductive_type_name(header_entries)
    if not type_name:
        print("Error: Could not find inductive type in header definitions")
        return False

    if use_sorry_for is None:
        use_sorry_for = set()
    if original_proofs is None:
        original_proofs = {}

    # Create the Lean file
    with open(OUTPUT_LEAN_FILE, 'w', encoding='utf-8') as f:
        # Write Lean snippet (imports and other code)
        f.write(LEAN_SNIPPET)
        f.write('\n\n')

        # Write inductive type definition (BEFORE namespace)
        write_inductive_definition(f, header_entries)

        # Write namespace
        f.write(f'namespace {type_name}\n\n')

        # Write all other header definitions (INSIDE namespace)
        write_header_definitions_in_namespace(f, header_entries)

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
            else:
                raise ValueError(f"Entry missing both 'statement' and 'code' fields: {entry}")

            # Write the theorem statement
            f.write(statement)
            f.write('\n')

            # Write proof: use original incorrect proof if available, otherwise 'sorry' if requested, otherwise normal proof
            if name in use_sorry_for:
                if name in original_proofs:
                    # Use original incorrect proof
                    f.write(original_proofs[name])
                    f.write('\n\n')
                else:
                    f.write('  sorry\n\n')
            else:
                f.write(proof)
                f.write('\n\n')

        # Close namespace
        f.write(f'end {type_name}\n')

    return True


def get_theorem_line_map(theorems_entries, header_entries):
    """
    Build a mapping from line numbers to theorem names by reading the generated file.
    """
    line_to_theorem = {}

    # Read the generated file
    if not OUTPUT_LEAN_FILE.exists():
        return line_to_theorem

    with open(OUTPUT_LEAN_FILE, 'r') as f:
        lines = f.readlines()

    # Find theorems by looking for "theorem" keyword
    current_theorem = None
    for line_num, line in enumerate(lines, start=1):
        # Check if this line starts a theorem
        if line.strip().startswith('theorem '):
            # Extract theorem name (supports Unicode and apostrophes)
            # Lean identifiers can contain letters, digits, underscores, apostrophes, and Unicode
            match = re.match(r'theorem\s+([\w\u0370-\u03FF\u2100-\u214F\']+)', line.strip())
            if match:
                current_theorem = match.group(1)

        # If we're in a theorem, map this line to it
        if current_theorem:
            line_to_theorem[line_num] = current_theorem

            # Check if this is the end of the theorem (next blank line after proof)
            if line.strip() == '' and line_num > 0:
                # Look ahead to see if next non-blank line is a new theorem or end
                found_end = False
                for future_line in lines[line_num:line_num+3]:
                    if future_line.strip():
                        if future_line.strip().startswith('theorem ') or future_line.strip().startswith('end '):
                            found_end = True
                            break
                if found_end:
                    current_theorem = None

    return line_to_theorem


def verify_with_lean_and_get_first_error(theorems_entries, header_entries):
    """
    Run Lean to verify the generated file.
    Returns (success, first_failed_theorem_name).
    If successful, first_failed_theorem_name is None.
    If failed, returns the name of the first theorem that failed.
    """
    # Change to MyNNG directory where lake configuration is
    project_dir = Path("MyNNG")

    # Run lean command to check the file
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(OUTPUT_LEAN_FILE.relative_to(project_dir))],
            cwd=project_dir,
            capture_output=True,
            text=True,
            timeout=60
        )

        if result.returncode == 0:
            return True, None

        # Parse errors to find the first failing theorem
        output = result.stdout + result.stderr

        # Find all error line numbers
        error_pattern = re.compile(r'Generated_Verification\.lean:(\d+):\d+:\s*error')
        error_lines = []

        for match in error_pattern.finditer(output):
            line_num = int(match.group(1))
            error_lines.append(line_num)

        if not error_lines:
            # Couldn't parse errors
            return False, None

        # Get the FIRST error line
        first_error_line = min(error_lines)

        # Map line to theorem
        line_to_theorem = get_theorem_line_map(theorems_entries, header_entries)

        if first_error_line in line_to_theorem:
            return False, line_to_theorem[first_error_line]
        else:
            return False, None

    except subprocess.TimeoutExpired:
        print("  ✗ Timeout (>60s)")
        return False, None
    except FileNotFoundError:
        print("✗ Error: 'lake' command not found. Make sure Lean is installed.")
        sys.exit(1)
    except Exception as e:
        print(f"✗ Error running Lean: {e}")
        return False, None


def count_sorries_in_proofs(theorems_entries):
    """
    Count proofs that contain 'sorry' keyword in their proof field.

    Returns:
        List of theorem IDs that contain 'sorry' in their proof
    """
    sorry_ids = []

    # For each theorem, check if its proof contains 'sorry' keyword
    for idx, entry in enumerate(theorems_entries):
        # Handle both old format (proof field) and new format (code field)
        if 'proof' in entry:
            proof = entry.get('proof', '')
        elif 'code' in entry:
            proof = entry.get('code', '')
        else:
            proof = ''

        # Use id if available, otherwise use index
        theorem_id = entry.get('id', idx)

        # Check if 'sorry' exists as a keyword in the proof
        # Use word boundaries to match 'sorry' as a whole word
        if re.search(r'\bsorry\b', proof):
            sorry_ids.append(theorem_id)

    return sorry_ids


def detect_banned_tactics(theorems_entries, banned_tactics=None):
    """
    Detect usage of banned tactics in proofs.

    Args:
        theorems_entries: List of theorem entries
        banned_tactics: List of banned tactic names (defaults to BANNED_TACTICS)

    Returns:
        Dictionary mapping theorem IDs to lists of banned tactics found
    """
    if banned_tactics is None:
        banned_tactics = BANNED_TACTICS

    banned_usage = {}

    for idx, entry in enumerate(theorems_entries):
        # Handle both old format (proof field) and new format (code field)
        if 'proof' in entry:
            proof = entry.get('proof', '')
        elif 'code' in entry:
            proof = entry.get('code', '')
        else:
            proof = ''

        # Use id if available, otherwise use index
        theorem_id = entry.get('id', idx)
        found_tactics = []

        for tactic in banned_tactics:
            # Match tactic as a whole word (with word boundaries)
            # This prevents matching "simp" inside "simplify" for example
            pattern = r'\b' + re.escape(tactic) + r'\b'
            if re.search(pattern, proof):
                found_tactics.append(tactic)

        if found_tactics:
            banned_usage[theorem_id] = found_tactics

    return banned_usage


def verify_dataset(header_path, theorems_path, verbose=False):
    """
    Verify a dataset by header and theorems file paths.

    Args:
        header_path: Path to header_definitions.jsonl file
        theorems_path: Path to theorems.jsonl file
        verbose: Whether to print progress messages

    Returns:
        Tuple of (error_ids, sorry_ids, banned_tactics_usage):
        - error_ids: List of theorem IDs that have incorrect proofs (empty if all correct)
        - sorry_ids: List of theorem IDs that contain 'sorry' after successful verification
        - banned_tactics_usage: Dict mapping theorem IDs to lists of banned tactics used
    """
    header_path = Path(header_path)
    theorems_path = Path(theorems_path)

    # Check if input files exist
    if not header_path.exists():
        raise FileNotFoundError(f"{header_path} not found")

    if not theorems_path.exists():
        raise FileNotFoundError(f"{theorems_path} not found")

    # Load JSONL files
    if verbose:
        print(f"Loading {header_path}...")
    header_entries = load_jsonl(header_path)
    if verbose:
        print(f"  Loaded {len(header_entries)} header definitions")

    if verbose:
        print(f"\nLoading {theorems_path}...")
    theorems_entries = load_jsonl(theorems_path)
    if verbose:
        print(f"  Loaded {len(theorems_entries)} theorems")

    # Get the inductive type name
    type_name = get_inductive_type_name(header_entries)
    if verbose:
        print(f"  Inductive type: {type_name}")

    # Keep track of incorrect proofs and their original proofs
    incorrect_proofs = set()
    original_proofs = {}  # Maps theorem name to original proof
    max_iterations = 100  # Safety limit
    last_failed_theorem = None
    same_failure_count = 0

    if verbose:
        print("\n" + "="*60)
        print("Starting verification...")
        print("="*60)

    for iteration in range(1, max_iterations + 1):
        # Generate Lean file (use sorry during verification)
        generate_lean_file(header_entries, theorems_entries, use_sorry_for=incorrect_proofs)

        # Verify
        if verbose:
            if iteration == 1:
                print(f"\nIteration {iteration}: Testing all original proofs...")
            else:
                print(f"\nIteration {iteration}: Re-testing with {len(incorrect_proofs)} theorem(s) marked as incorrect...")

        success, first_failed = verify_with_lean_and_get_first_error(theorems_entries, header_entries)

        if success:
            # Success!
            if verbose:
                print("✓ Lean verification successful!")
            break
        elif first_failed:
            # Check if we're stuck on the same theorem
            if first_failed == last_failed_theorem:
                same_failure_count += 1
                if same_failure_count >= 3:
                    # Same theorem failing 3 times in a row - likely a bug in error detection
                    if verbose:
                        print(f"✗ ERROR: Theorem '{first_failed}' keeps failing even after being marked incorrect!")
                        print(f"   This indicates the error might be elsewhere or the line mapping is incorrect.")
                    raise RuntimeError(f"Stuck in loop on theorem '{first_failed}' - error detection may be inaccurate")
            else:
                same_failure_count = 0
                last_failed_theorem = first_failed

            # Found a failing theorem - store its original proof
            if verbose:
                print(f"✗ Found incorrect proof: {first_failed}")

            # Find and store the original proof
            for entry in theorems_entries:
                # Get name - might already be set by generate_lean_file, or need to parse
                entry_name = entry.get('name')
                if not entry_name and 'code' in entry:
                    entry_name, _, _ = parse_theorem_code(entry['code'])
                    entry['name'] = entry_name

                if entry_name == first_failed:
                    # Get the proof - handle both formats
                    if 'proof' in entry:
                        original_proofs[first_failed] = entry['proof']
                    elif 'code' in entry:
                        _, _, proof_raw = parse_theorem_code(entry['code'])
                        original_proofs[first_failed] = proof_raw
                    break

            incorrect_proofs.add(first_failed)
        else:
            # Failed but couldn't identify the theorem
            if verbose:
                print("✗ Lean failed but couldn't identify which theorem")
            raise RuntimeError("Verification failed but couldn't identify which theorem")

    else:
        # Reached max iterations
        raise RuntimeError(f"Maximum iterations ({max_iterations}) reached")

    # After successful verification, generate final file with original incorrect proofs instead of sorry
    if incorrect_proofs:
        generate_lean_file(header_entries, theorems_entries, use_sorry_for=incorrect_proofs, original_proofs=original_proofs)

    # Convert theorem names to IDs
    error_ids = []
    for name in incorrect_proofs:
        for idx, entry in enumerate(theorems_entries):
            # Get name - might already be set by generate_lean_file, or need to parse
            entry_name = entry.get('name')
            if not entry_name and 'code' in entry:
                entry_name, _, _ = parse_theorem_code(entry['code'])
                entry['name'] = entry_name

            if entry_name == name:
                # Use id if available, otherwise use index
                error_ids.append(entry.get('id', idx))
                break

    # Count sorries in proofs (always check, even if there were errors)
    sorry_ids = count_sorries_in_proofs(theorems_entries)

    # Detect banned tactics usage (not counted as errors)
    banned_tactics_usage = detect_banned_tactics(theorems_entries)

    if verbose:
        print("\n" + "="*60)
        print("VERIFICATION COMPLETE")
        print("="*60)

        if error_ids:
            print(f"\nFound {len(error_ids)} theorem(s) with incorrect proofs:\n")
            for name in sorted(incorrect_proofs):
                for idx, entry in enumerate(theorems_entries):
                    # Get name - might already be set
                    entry_name = entry.get('name')
                    if not entry_name and 'code' in entry:
                        entry_name, _, _ = parse_theorem_code(entry['code'])

                    if entry_name == name:
                        # Use id if available, otherwise use index
                        theorem_id = entry.get('id', idx)
                        print(f"  - {name} (ID: {theorem_id})")
                        break
        else:
            print("\n✓ All proofs are correct!")
            if sorry_ids:
                print(f"\n⚠ Found {len(sorry_ids)} proof(s) containing 'sorry':")
                print(f"  IDs: {sorry_ids}")

        if banned_tactics_usage:
            print(f"\n⚠ Found {len(banned_tactics_usage)} proof(s) using banned tactics:")
            for theorem_id in sorted(banned_tactics_usage.keys()):
                tactics_list = ', '.join(banned_tactics_usage[theorem_id])
                # Find theorem name
                theorem_name = None
                for idx, entry in enumerate(theorems_entries):
                    # Use id if available, otherwise use index
                    entry_id = entry.get('id', idx)
                    if entry_id == theorem_id:
                        # Get name - might already be set
                        theorem_name = entry.get('name')
                        if not theorem_name and 'code' in entry:
                            theorem_name, _, _ = parse_theorem_code(entry['code'])
                        break
                if theorem_name:
                    print(f"  - ID {theorem_id} ({theorem_name}): {tactics_list}")
                else:
                    print(f"  - ID {theorem_id}: {tactics_list}")

        print("="*60)

    return sorted(error_ids), sorted(sorry_ids), banned_tactics_usage


def main():
    print("=== JSONL Verifier (Sequential Error Detection) ===\n")

    try:
        error_ids, sorry_ids, banned_tactics_usage = verify_dataset(HEADER_PATH, THEOREMS_PATH, verbose=True)

        if error_ids:
            print(f"\nError theorem IDs: {error_ids}")
            print(f"\nThese proofs have been replaced with their original incorrect versions in:")
            print(f"  {OUTPUT_LEAN_FILE}")

        if sorry_ids:
            print(f"\n⚠ Warning: Found proofs with 'sorry': {sorry_ids}")

        if banned_tactics_usage:
            print(f"\n⚠ Warning: Found proofs using banned tactics:")
            print(f"  {banned_tactics_usage}")


    except Exception as e:
        print(f"✗ Error: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()