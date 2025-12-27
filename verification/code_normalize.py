#!/usr/bin/env python3
"""
Code normalization utilities for Lean 4 proofs.
Handles indentation, syntax fixes, and theorem declaration stripping.
"""

import re


def fix_indentation(code: str) -> str:
    """
    Fix Indentation and Structure.
    Lean 4 is whitespace-sensitive (especially with by blocks and multi-line tactics).
    """
    # Standardize indentation to two spaces per level
    code = code.replace('\t', '  ')

    # Fix 'by' structure: Ensure proper indentation after ':= by'
    def fix_by_indentation(match):
        leading_ws = match.group(1)  # Capture any leading whitespace before :=
        by_part = match.group(2)     # The ':= by ' part
        tactic = match.group(3)      # The tactic after 'by'
        # Calculate indentation: count spaces in leading_ws, add 2 more
        indent_count = len(leading_ws)
        new_indent = ' ' * (indent_count + 2)
        return f'{leading_ws}{by_part}\n{new_indent}{tactic}'

    code = re.sub(r'^(\s*)(:=\s*by\s+)([^\n])', fix_by_indentation, code, flags=re.MULTILINE)

    # Add indentation after block starters (e.g., induction, cases, repeat)
    code = re.sub(r'(induction|cases|match|have|suffices)\s+.*?\s*=>\s*([^\n])',
                  lambda m: m.group(0).replace(m.group(2), f'\n  {m.group(2)}'), code, flags=re.DOTALL)

    # Standardize 'with' blocks (often misformatted by LLMs)
    code = re.sub(r'(\s*\|\s*[\w\d]+\s*=>\s*)([^\n])', r'\1\n  \2', code)

    # Only strip trailing whitespace, preserve leading indentation
    return code.rstrip()


def fix_syntax(code: str) -> str:
    """
    Fix Versioning and Syntax.
    Addresses issues where LLM is trained on old Lean 4 versions or Mathlib code.
    """
    # Old Mathlib.Tactic.Use vs Lean Core 'exists'
    code = code.replace('exists ', 'use ')

    # Lean 3/Early Lean 4 vs Modern Lean 4
    code = code.replace('begin', 'by')
    code = code.replace('end', '')  # Modern Lean 4 often doesn't need 'end' markers

    # Remove excess 'show' keywords (often superfluous in modern Lean)
    code = re.sub(r'show\s+.*?,\s*', '', code)

    # Remove unnecessary parentheses around single terms
    code = re.sub(r'\((\w+)\)', r'\1', code)

    return code


def strip_theorem_declaration(code: str) -> str:
    """
    Strip Theorem Declaration.
    Remove the theorem declaration line and all lines above it.

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
