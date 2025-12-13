"""
Parse MyNat Definitions and Axioms

This script extracts all definitions, axioms, and theorems from the MyNat folder
in the NNG4 repository and outputs them to a JSONL file.

Each entry contains:
- full_name: The identifier name (e.g., 'zero_add', 'succ_ne_zero')
- code: The complete Lean code with 'sorry' for proofs
- category: Type of declaration ('definition', 'axiom', 'theorem', 'inductive', 'instance')

Output: mynat_definitions.jsonl
"""

import re
import json
from pathlib import Path
from typing import List, Dict, Optional


class MyNatParser:
    """Parser for extracting definitions and axioms from MyNat Lean files."""

    def __init__(self, mynat_dir: str = "externals/NNG4/Game/MyNat"):
        """
        Initialize parser with path to MyNat directory.

        Args:
            mynat_dir: Path to the Game/MyNat directory
        """
        self.mynat_dir = Path(mynat_dir)
        self.definitions = []

    def parse_all_files(self) -> List[Dict[str, str]]:
        """
        Parse all .lean files in the MyNat directory in dependency order.

        Returns:
            List of dictionaries containing parsed definitions/axioms
        """
        if not self.mynat_dir.exists():
            raise FileNotFoundError(f"MyNat directory not found: {self.mynat_dir}")

        # Add mock axioms FIRST (needed by DecidableEq)
        print("Adding mock axioms...")
        self.add_mock_axioms()

        # Process files in dependency order
        file_order = [
            "Definition.lean",
            "PeanoAxioms.lean",
            "Addition.lean",
            "Multiplication.lean",
            "TutorialLemmas.lean",
            "Power.lean",
            "LE.lean",
            "Inequality.lean",
            "DecidableEq.lean",
            "DecidableTests.lean"
        ]

        for filename in file_order:
            filepath = self.mynat_dir / filename
            if filepath.exists():
                print(f"Processing: {filename}")
                self.parse_file(filepath)
            else:
                print(f"Warning: {filename} not found")

        return self.definitions

    def add_mock_axioms(self) -> None:
        """
        Add mock axioms/theorems that are needed for completeness but might be missing.
        These are marked with 'sorry' to indicate they're placeholders.
        """
        # Get existing theorem names
        existing_names = {d['full_name'] for d in self.definitions}

        # Mock axioms needed for DecidableEq
        # Note: zero_ne_succ exists with real proof in PeanoAxioms.lean
        mock_declarations = [
            {
                'full_name': 'succ_ne_succ',
                'code': 'theorem succ_ne_succ (m n : MyNat) (h : m ≠ n) : succ m ≠ succ n := sorry',
                'category': 'axiom'
            },
            {
                'full_name': 'succ_ne_zero',
                'code': 'axiom succ_ne_zero (n : MyNat) : succ n ≠ 0',
                'category': 'axiom'
            }
        ]

        # Add declarations at the beginning
        for mock in reversed(mock_declarations):
            self.definitions.insert(0, mock)
            print(f"  Added mock axiom: {mock['full_name']}")

    def parse_file(self, file_path: Path) -> None:
        """
        Parse a single Lean file and extract definitions/axioms.

        Args:
            file_path: Path to the .lean file to parse
        """
        content = file_path.read_text(encoding='utf-8')

        # Remove comments to avoid parsing issues
        content = self.remove_comments(content)

        # Extract different types of declarations
        self.extract_inductive_types(content, file_path.name)
        self.extract_opaque_defs(content, file_path.name)
        self.extract_definitions(content, file_path.name)
        self.extract_axioms(content, file_path.name)
        self.extract_theorems(content, file_path.name)
        self.extract_lemmas(content, file_path.name)
        self.extract_instances(content, file_path.name)

    def remove_comments(self, content: str) -> str:
        """
        Remove Lean comments (both -- and /- ... -/) from content.

        Args:
            content: File content

        Returns:
            Content with comments removed
        """
        # Remove multi-line comments /- ... -/
        content = re.sub(r'/-.*?-/', '', content, flags=re.DOTALL)

        # Remove single-line comments --
        content = re.sub(r'--[^\n]*', '', content)

        return content

    def extract_inductive_types(self, content: str, filename: str) -> None:
        """
        Extract inductive type definitions (e.g., MyNat) with all constructors.

        Pattern: inductive TypeName where | constructor : Type

        Args:
            content: File content
            filename: Name of source file
        """
        # Match: inductive MyNat where ... (capture all constructors)
        lines = content.split('\n')
        i = 0

        while i < len(lines):
            line = lines[i].strip()

            if line.startswith('inductive '):
                match = re.match(r'inductive\s+(\w+)', line)
                if not match:
                    i += 1
                    continue

                type_name = match.group(1)

                # Collect full inductive definition
                full_inductive = line
                j = i + 1

                # Continue until we hit a non-constructor line
                while j < len(lines):
                    next_line = lines[j]
                    stripped = next_line.strip()

                    # Stop at comments or next declaration
                    if (stripped.startswith(('--', 'attribute', 'notation', '@[',
                                            'namespace', 'instance', 'def', 'theorem')) or
                        (stripped and not stripped.startswith('|') and 'where' not in full_inductive)):
                        break

                    if stripped.startswith('|') or 'where' in next_line:
                        full_inductive += '\n' + next_line

                    j += 1
                    if j - i > 10:
                        break

                code = full_inductive.strip()

                # Store the complete inductive type
                self.definitions.append({
                    'full_name': type_name,
                    'code': code,
                    'category': 'inductive'
                })

                i = j
            else:
                i += 1

    def extract_opaque_defs(self, content: str, filename: str) -> None:
        """
        Extract opaque definitions (e.g., add, mul, pow).

        Pattern: opaque name : Type

        Args:
            content: File content
            filename: Name of source file
        """
        # Match: opaque name : type
        pattern = r'opaque\s+(\w+)\s*:\s*([^\n]+)'

        for match in re.finditer(pattern, content):
            name = match.group(1)
            opaque_type = match.group(2).strip()

            code = f"opaque {name} : {opaque_type}"

            self.definitions.append({
                'full_name': name,
                'code': code,
                'category': 'opaque'
            })

    def extract_definitions(self, content: str, filename: str) -> None:
        """
        Extract def declarations with their original bodies.

        Pattern: def name (args) : Type := body

        Args:
            content: File content
            filename: Name of source file
        """
        lines = content.split('\n')
        i = 0

        while i < len(lines):
            line = lines[i].strip()

            # Check if line starts with 'def'
            if line.startswith('def '):
                # Extract definition name
                match = re.match(r'def\s+(\w+)', line)
                if not match:
                    i += 1
                    continue

                name = match.group(1)

                # Collect the full definition including body
                full_def = line
                j = i + 1

                found_assignment = ':=' in full_def

                # Continue collecting lines until we hit the end
                while j < len(lines):
                    next_line = lines[j]
                    full_def += '\n' + next_line

                    if ':=' in next_line and not found_assignment:
                        found_assignment = True

                    if found_assignment:
                        stripped = next_line.strip()
                        # Stop at next top-level declaration or blank line
                        if stripped.startswith(('def ', 'theorem ', 'axiom ', 'instance ',
                                               'attribute ', 'end ', 'namespace ', '@[', 'lemma ')):
                            # Remove the last line
                            full_def = '\n'.join(full_def.split('\n')[:-1])
                            break
                        # Check for pattern matching completion (lines starting with |)
                        # If we're in a match block and hit a non-match line, we're likely done
                        if '| ' in full_def and stripped and not stripped.startswith('|') and j > i + 2:
                            break
                        # Stop at blank line after pattern matching
                        if not stripped and '|' in full_def and j > i + 2:
                            break
                        # For simple definitions (no pattern matching), stop at first blank line
                        if not stripped and ':=' in full_def and '|' not in full_def and 'match' not in full_def:
                            break

                    j += 1
                    if j - i > 30:
                        break

                code = full_def.strip()

                self.definitions.append({
                    'full_name': name,
                    'code': code,
                    'category': 'definition'
                })

                i = j
            else:
                i += 1

    def extract_axioms(self, content: str, filename: str) -> None:
        """
        Extract axiom declarations.

        Pattern: axiom name (args) : Type

        Args:
            content: File content
            filename: Name of source file
        """
        # Match: axiom name (args) : type
        pattern = r'axiom\s+(\w+)\s*([^:]*?):\s*([^\n]+)'

        for match in re.finditer(pattern, content):
            name = match.group(1)
            args = match.group(2).strip()
            axiom_type = match.group(3).strip()

            # Axioms don't have proofs, but we add sorry for consistency
            code = f"axiom {name} {args}: {axiom_type}"

            self.definitions.append({
                'full_name': name,
                'code': code,
                'category': 'axiom'
            })

    def extract_theorems(self, content: str, filename: str) -> None:
        """
        Extract theorem declarations with their original proofs.

        Pattern: theorem name (args) : Type := proof

        Args:
            content: File content
            filename: Name of source file
        """
        # Match: theorem name ... : type := proof_body
        lines = content.split('\n')
        i = 0

        while i < len(lines):
            line = lines[i].strip()

            # Check if line starts with 'theorem'
            if line.startswith('theorem '):
                # Extract theorem name
                match = re.match(r'theorem\s+(\w+)', line)
                if not match:
                    i += 1
                    continue

                name = match.group(1)

                # Collect the full theorem including proof
                full_theorem = line
                j = i + 1

                # Track brace depth to find end of proof
                # Continue until we reach the end of the theorem block
                brace_depth = 0
                found_assignment = ':=' in full_theorem

                while j < len(lines):
                    next_line = lines[j]
                    full_theorem += '\n' + next_line

                    # Track assignment operator
                    if ':=' in next_line and not found_assignment:
                        found_assignment = True

                    # Simple heuristic: theorem ends when we hit a blank line or new top-level declaration
                    # after finding the assignment
                    if found_assignment:
                        stripped = next_line.strip()
                        # Stop at next top-level declaration
                        if stripped.startswith(('theorem ', 'def ', 'axiom ', 'instance ',
                                               'attribute ', 'end ', 'namespace ', 'section ', 'lemma ')):
                            # Remove the last line (it's the next declaration)
                            full_theorem = '\n'.join(full_theorem.split('\n')[:-1])
                            break
                        # Also stop at blank line after substantive content
                        if not stripped and j > i + 2:
                            break

                    j += 1
                    # Safety limit
                    if j - i > 50:
                        break

                # Clean up the theorem code
                code = full_theorem.strip()

                self.definitions.append({
                    'full_name': name,
                    'code': code,
                    'category': 'theorem'
                })

                i = j
            else:
                i += 1

    def extract_lemmas(self, content: str, filename: str) -> None:
        """
        Extract lemma declarations with their original proofs.
        Lemmas are treated as theorems.

        Pattern: lemma name (args) : Type := proof

        Args:
            content: File content
            filename: Name of source file
        """
        lines = content.split('\n')
        i = 0

        while i < len(lines):
            line = lines[i].strip()

            # Check if line starts with 'lemma'
            if line.startswith('lemma '):
                # Extract lemma name
                match = re.match(r'lemma\s+(\w+)', line)
                if not match:
                    i += 1
                    continue

                name = match.group(1)

                # Collect the full lemma including proof
                full_lemma = line
                j = i + 1

                found_assignment = ':=' in full_lemma

                while j < len(lines):
                    next_line = lines[j]
                    full_lemma += '\n' + next_line

                    if ':=' in next_line and not found_assignment:
                        found_assignment = True

                    if found_assignment:
                        stripped = next_line.strip()
                        # Stop at next top-level declaration
                        if stripped.startswith(('theorem ', 'def ', 'axiom ', 'instance ',
                                               'attribute ', 'end ', 'namespace ', 'section ', 'lemma ')):
                            full_lemma = '\n'.join(full_lemma.split('\n')[:-1])
                            break
                        # Stop at blank line after substantive content
                        if not stripped and j > i + 2:
                            break

                    j += 1
                    if j - i > 30:
                        break

                code = full_lemma.strip()

                self.definitions.append({
                    'full_name': name,
                    'code': code,
                    'category': 'lemma'
                })

                i = j
            else:
                i += 1

    def extract_instances(self, content: str, filename: str) -> None:
        """
        Extract instance declarations with their original implementations.

        Pattern: instance name : Type := body or instance : Type where ...

        Args:
            content: File content
            filename: Name of source file
        """
        lines = content.split('\n')
        i = 0

        while i < len(lines):
            line = lines[i].strip()

            # Check if line starts with 'instance'
            if line.startswith('instance '):
                # Try to extract instance name (may be anonymous)
                match = re.match(r'instance\s+(?:(\w+)\s+)?', line)
                if not match:
                    i += 1
                    continue

                name = match.group(1) if match.group(1) else "anonymous_instance"

                # Collect the full instance including body
                full_instance = line
                j = i + 1

                found_where_or_assign = ('where' in full_instance or ':=' in full_instance)

                while j < len(lines):
                    next_line = lines[j]
                    full_instance += '\n' + next_line

                    if ('where' in next_line or ':=' in next_line) and not found_where_or_assign:
                        found_where_or_assign = True

                    if found_where_or_assign:
                        stripped = next_line.strip()
                        # Stop at next declaration
                        if stripped.startswith(('instance ', 'def ', 'theorem ', 'axiom ',
                                               'attribute ', '@[', 'namespace ', 'end ')):
                            full_instance = '\n'.join(full_instance.split('\n')[:-1])
                            break
                        # Instance with 'where' ends after the fields
                        if 'where' in full_instance and stripped and not stripped.startswith(('|', 'default', 'ofNat', 'toString')) and j > i + 2:
                            break

                    j += 1
                    if j - i > 20:
                        break

                code = full_instance.strip()

                self.definitions.append({
                    'full_name': name,
                    'code': code,
                    'category': 'instance'
                })

                i = j
            else:
                i += 1

    def save_to_jsonl(self, output_path: str = "mynat_definitions.jsonl") -> None:
        """
        Save parsed definitions to a JSONL file.

        Each line is a JSON object with:
        - full_name: Identifier name
        - code: Lean code with sorry
        - category: Type of declaration

        Args:
            output_path: Path to output JSONL file
        """
        output_file = Path(output_path)

        with open(output_file, 'w', encoding='utf-8') as f:
            for definition in self.definitions:
                json_line = json.dumps(definition, ensure_ascii=False)
                f.write(json_line + '\n')

        print(f"\n✓ Saved {len(self.definitions)} definitions to {output_file}")

        # Print summary statistics
        categories = {}
        for defn in self.definitions:
            cat = defn['category']
            categories[cat] = categories.get(cat, 0) + 1

        print("\nSummary:")
        for category, count in sorted(categories.items()):
            print(f"  {category}: {count}")


def main():
    """Main function to parse MyNat definitions and save to JSONL."""

    print("=" * 60)
    print("MyNat Definitions and Axioms Parser")
    print("=" * 60)
    print()

    # Initialize parser
    parser = MyNatParser(mynat_dir="externals/NNG4/Game/MyNat")

    # Parse all files
    try:
        definitions = parser.parse_all_files()

        # Save to JSONL
        parser.save_to_jsonl("mynat_definitions.jsonl")

        # Print sample entries
        print("\nSample entries:")
        print("-" * 60)
        for defn in definitions[:3]:
            print(f"\nName: {defn['full_name']}")
            print(f"Category: {defn['category']}")
            print(f"Code: {defn['code']}")

    except FileNotFoundError as e:
        print(f"Error: {e}")
        print("\nPlease ensure the NNG4 repository is cloned in externals/NNG4/")
        return 1

    return 0


if __name__ == "__main__":
    exit(main())
