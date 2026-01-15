#!/usr/bin/env python3
"""
Lean analyzer for error detection and reporting.
Analyzes generated Lean files and reports errors, sorry usage, and banned tactics.
"""

import json
import re
import subprocess
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional
from verification.jsonl_generator import load_jsonl, parse_theorem_code, get_inductive_type_name


# Banned tactics that should be reported but not marked as errors
BANNED_TACTICS = ['simp']

# Default Lean file output path
DEFAULT_OUTPUT_FILE = Path("MyNNG/MyNNG/Generated_Verification.lean")


def get_theorem_line_map(theorems_entries: List[Dict], lean_file: Path) -> Dict[int, str]:
    """
    Build a mapping from line numbers to theorem names by reading the generated file.

    Args:
        theorems_entries: List of theorem entries
        lean_file: Path to the generated Lean file

    Returns:
        Dictionary mapping line numbers to theorem names
    """
    line_to_theorem = {}

    # Read the generated file
    if not lean_file.exists():
        return line_to_theorem

    with open(lean_file, 'r') as f:
        lines = f.readlines()

    # Find theorems by looking for "theorem" keyword
    current_theorem = None
    theorem_start_line = None

    for line_num, line in enumerate(lines, start=1):
        # Check if this line starts a theorem
        if line.strip().startswith('theorem '):
            # Extract theorem name (supports Unicode and apostrophes)
            match = re.match(r'theorem\s+([\w\u0370-\u03FF\u2100-\u214F\']+)', line.strip())
            if match:
                current_theorem = match.group(1)
                theorem_start_line = line_num

        # If we're in a theorem, map this line to it
        if current_theorem:
            line_to_theorem[line_num] = current_theorem

            # Check if this is the end of the theorem
            # A theorem ends when we see a blank line followed by either:
            # - Another theorem declaration
            # - End of namespace
            # - End of file
            # - Another top-level definition
            if line.strip() == '' and line_num > theorem_start_line:
                # Look ahead to see if next non-blank line is a new theorem or end
                found_end = False
                for i in range(line_num, min(line_num + 5, len(lines))):
                    future_line = lines[i] if i < len(lines) else ""
                    if future_line.strip():
                        if (future_line.strip().startswith('theorem ') or
                            future_line.strip().startswith('end ') or
                            future_line.strip().startswith('def ') or
                            future_line.strip().startswith('axiom ') or
                            future_line.strip().startswith('opaque ')):
                            found_end = True
                            break
                if found_end:
                    current_theorem = None
                    theorem_start_line = None

    return line_to_theorem


def verify_lean_file(lean_file: Path, timeout: int = 60) -> Tuple[bool, str]:
    """
    Run Lean to verify the generated file.

    Args:
        lean_file: Path to the Lean file to verify
        timeout: Timeout in seconds

    Returns:
        Tuple of (success, output)
    """
    # Change to MyNNG directory where lake configuration is
    project_dir = Path("MyNNG")

    # Run lean command to check the file
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(lean_file.relative_to(project_dir))],
            cwd=project_dir,
            capture_output=True,
            text=True,
            timeout=timeout
        )

        if result.returncode == 0:
            return True, ""

        # Return error output
        return False, result.stdout + result.stderr

    except subprocess.TimeoutExpired:
        return False, f"Timeout (>{timeout}s)"
    except FileNotFoundError:
        return False, "'lake' command not found. Make sure Lean is installed."
    except Exception as e:
        return False, f"Error running Lean: {e}"


def parse_first_error(output: str, line_to_theorem: Dict[int, str]) -> Optional[Tuple[str, int, str]]:
    """
    Parse the first error from Lean output.

    Args:
        output: Lean compiler output
        line_to_theorem: Mapping from line numbers to theorem names

    Returns:
        Tuple of (theorem_name, line_number, error_message) or None if no error found
    """
    # Find all error line numbers
    # Match both "error:" and "error(...)" formats
    error_pattern = re.compile(r'Generated_Verification\.lean:(\d+):\d+:\s*error(?:\([^)]+\))?:(.+?)(?=\n(?:\S|$))', re.DOTALL)
    errors = []

    for match in error_pattern.finditer(output):
        line_num = int(match.group(1))
        error_msg = match.group(2).strip()
        errors.append((line_num, error_msg))

    if not errors:
        return None

    # Get the FIRST error line
    first_error_line, error_msg = min(errors, key=lambda x: x[0])

    # Map line to theorem - try to find the closest preceding theorem
    if first_error_line in line_to_theorem:
        return line_to_theorem[first_error_line], first_error_line, error_msg
    else:
        # If exact match not found, try to find the closest preceding line that has a theorem
        # This handles cases where the error is on a line after the theorem declaration
        closest_line = None
        for line_num in sorted(line_to_theorem.keys(), reverse=True):
            if line_num <= first_error_line:
                closest_line = line_num
                break

        if closest_line is not None:
            return line_to_theorem[closest_line], first_error_line, error_msg
        else:
            # Error is before any theorem (likely in header/imports)
            return None


def count_sorries_in_proofs(theorems_entries: List[Dict]) -> List[int]:
    """
    Count proofs that contain 'sorry' keyword.

    Args:
        theorems_entries: List of theorem entries

    Returns:
        List of theorem IDs that contain 'sorry' in their proof
    """
    sorry_ids = []

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
        if re.search(r'\bsorry\b', proof):
            sorry_ids.append(theorem_id)

    return sorry_ids


def detect_banned_tactics(theorems_entries: List[Dict], banned_tactics: Optional[List[str]] = None) -> Dict[int, List[str]]:
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
            pattern = r'\b' + re.escape(tactic) + r'\b'
            if re.search(pattern, proof):
                found_tactics.append(tactic)

        if found_tactics:
            banned_usage[theorem_id] = found_tactics

    return banned_usage


def analyze_lean_file(
    lean_file: Path,
    theorems_entries: List[Dict],
    header_entries: List[Dict],
    max_iterations: int = 100
) -> Dict:
    """
    Analyze a generated Lean file for errors, sorry usage, and banned tactics.

    This function iteratively finds incorrect proofs by replacing them with sorry
    until the file compiles successfully.

    Args:
        lean_file: Path to the generated Lean file
        theorems_entries: List of theorem entries
        header_entries: List of header entries
        max_iterations: Maximum number of iterations for error detection

    Returns:
        Dictionary with analysis results:
        {
            "error_ids": List[int],           # IDs of theorems with incorrect proofs
            "sorry_ids": List[int],           # IDs of theorems with 'sorry' in proof
            "banned_tactics_usage": Dict[int, List[str]],  # Banned tactics by ID
            "error_details": Dict[int, str]   # Error messages by ID
        }
    """
    from verification.jsonl_generator import generate_lean_for_theorems

    # Keep track of incorrect proofs
    incorrect_proofs = set()
    error_details = {}    # Maps theorem ID to error message
    last_failed_theorem = None
    same_failure_count = 0

    for iteration in range(1, max_iterations + 1):
        # Generate Lean file (use sorry for known incorrect proofs)
        generate_lean_for_theorems(header_entries, theorems_entries, lean_file,
                                   use_sorry_for=incorrect_proofs)

        # Verify
        success, output = verify_lean_file(lean_file)

        if success:
            # Success!
            break
        else:
            # Parse errors
            line_to_theorem = get_theorem_line_map(theorems_entries, lean_file)
            error_info = parse_first_error(output, line_to_theorem)

            if error_info:
                first_failed, line_num, error_msg = error_info

                # Check if we're stuck on the same theorem
                if first_failed == last_failed_theorem:
                    same_failure_count += 1
                    if same_failure_count >= 3:
                        raise RuntimeError(f"Stuck in loop on theorem '{first_failed}' - error detection may be inaccurate")
                else:
                    same_failure_count = 0
                    last_failed_theorem = first_failed

                # Find and store error message
                for idx, entry in enumerate(theorems_entries):
                    # Get name - might already be set by generate_lean_for_theorems, or need to parse
                    entry_name = entry.get('name')
                    if not entry_name and 'code' in entry:
                        entry_name, _, _ = parse_theorem_code(entry['code'])
                        entry['name'] = entry_name

                    if entry_name == first_failed:
                        # Store error message
                        theorem_id = entry.get('id', idx)
                        error_details[theorem_id] = error_msg
                        break

                incorrect_proofs.add(first_failed)
            else:
                # Failed but couldn't identify the theorem - provide diagnostic info
                # Save full error output to a debug file
                debug_file = lean_file.parent / "debug_error_output.txt"
                with open(debug_file, 'w') as f:
                    f.write(f"=== Iteration {iteration} ===\n")
                    f.write(f"Current incorrect proofs: {incorrect_proofs}\n\n")
                    f.write("=== Full Lean Output ===\n")
                    f.write(output)
                    f.write("\n\n=== Line to Theorem Map ===\n")
                    for line_num in sorted(line_to_theorem.keys()):
                        f.write(f"Line {line_num}: {line_to_theorem[line_num]}\n")

                # Extract first few lines of error for debugging
                error_preview = output[:500] if len(output) > 500 else output

                # Try to extract the error line number
                error_pattern = re.compile(r'Generated_Verification\.lean:(\d+):\d+:\s*error')
                match = error_pattern.search(output)

                if match:
                    error_line = int(match.group(1))
                    raise RuntimeError(
                        f"Verification failed but couldn't identify which theorem. "
                        f"Error at line {error_line}. "
                        f"This may be an error in the header/imports section. "
                        f"Debug output saved to: {debug_file}\n"
                        f"Error preview: {error_preview}"
                    )
                else:
                    raise RuntimeError(
                        f"Verification failed but couldn't parse error format. "
                        f"Debug output saved to: {debug_file}\n"
                        f"Output: {error_preview}"
                    )
    else:
        # Reached max iterations
        raise RuntimeError(f"Maximum iterations ({max_iterations}) reached")

    # After successful verification, generate final file with sorry for incorrect proofs
    if incorrect_proofs:
        generate_lean_for_theorems(header_entries, theorems_entries, lean_file,
                                   use_sorry_for=incorrect_proofs)

    # Convert theorem names to IDs
    error_ids = []
    for name in incorrect_proofs:
        for idx, entry in enumerate(theorems_entries):
            # Get name - might already be set
            entry_name = entry.get('name')
            if not entry_name and 'code' in entry:
                entry_name, _, _ = parse_theorem_code(entry['code'])
                entry['name'] = entry_name

            if entry_name == name:
                # Use id if available, otherwise use index
                error_ids.append(entry.get('id', idx))
                break

    # Count sorries in proofs
    sorry_ids = count_sorries_in_proofs(theorems_entries)

    # Detect banned tactics usage
    banned_tactics_usage = detect_banned_tactics(theorems_entries)

    return {
        "error_ids": sorted(error_ids),
        "sorry_ids": sorted(sorry_ids),
        "banned_tactics_usage": banned_tactics_usage,
        "error_details": error_details
    }
