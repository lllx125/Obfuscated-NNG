"""
Build Level Dataset for LLM Training

This script extracts all levels from the NNG4 Game/Levels directory and creates
a JSONL dataset where each entry contains:
- id: Level number (1-147)
- header: All MyNat definitions from mynat_definitions.jsonl
- statement: The theorem/lemma statement to prove
- ground_truth: The actual proof

Usage:
    python3 build_level_dataset.py
    python3 build_level_dataset.py --output nng_levels.jsonl
"""

import json
import re
from pathlib import Path
from typing import List, Dict, Optional
import argparse


class LevelExtractor:
    """Extract theorem statements and proofs from NNG4 level files."""

    def __init__(self, levels_dir: str = "externals/NNG4/Game/Levels"):
        """
        Initialize extractor with path to Levels directory.

        Args:
            levels_dir: Path to the Game/Levels directory
        """
        self.levels_dir = Path(levels_dir)
        self.levels = []

    def find_all_level_files(self) -> List[Path]:
        """
        Find all .lean level files in the Levels directory.

        Returns:
            List of Path objects for level files
        """
        if not self.levels_dir.exists():
            raise FileNotFoundError(f"Levels directory not found: {self.levels_dir}")

        # Find all .lean files recursively
        level_files = []
        for lean_file in sorted(self.levels_dir.rglob("*.lean")):
            # Skip files in hidden directories or backup directories
            if any(part.startswith('.') or part in ['Old', 'Backup', 'WIP']
                   for part in lean_file.parts):
                continue

            # Skip WIP files
            if lean_file.name.startswith('WIP'):
                continue

            # Include all remaining .lean files
            level_files.append(lean_file)

        return sorted(level_files)

    def extract_theorem_from_file(self, file_path: Path) -> Optional[Dict[str, str]]:
        """
        Extract the main theorem/lemma statement and proof from a level file.

        NNG4 level files use the format:
        Statement theorem_name (args) : statement := by
          proof

        Args:
            file_path: Path to the level .lean file

        Returns:
            Dictionary with 'statement' and 'proof' keys, or None if not found
        """
        content = file_path.read_text(encoding='utf-8')

        # Look for Statement declarations (NNG4 specific format)
        lines = content.split('\n')

        for i, line in enumerate(lines):
            stripped = line.strip()

            # Check for Statement keyword (NNG4 format)
            if stripped.startswith('Statement '):
                return self.extract_statement(lines, i)

            # Also check for regular theorem or lemma (just in case)
            if stripped.startswith(('theorem ', 'lemma ')):
                return self.extract_declaration(lines, i)

        return None

    def extract_statement(self, lines: List[str], start_idx: int) -> Optional[Dict[str, str]]:
        """
        Extract a Statement declaration (NNG4 specific format).

        Args:
            lines: All lines in the file
            start_idx: Index where the Statement starts

        Returns:
            Dictionary with 'statement' and 'proof'
        """
        # Statement format: Statement name (args) : type := by
        statement_lines = [lines[start_idx]]
        i = start_idx

        # Find where the proof starts (look for :=)
        # Check if := is on the first line itself
        found_proof_start = ':=' in lines[start_idx]

        if not found_proof_start:
            i += 1
            while i < len(lines) and not found_proof_start:
                line = lines[i]
                statement_lines.append(line)

                if ':=' in line:
                    found_proof_start = True
                    break

                i += 1
                if i - start_idx > 15:  # Safety limit for statement
                    break

        if not found_proof_start:
            return None

        # Join statement lines and extract the part before :=
        full_statement_line = '\n'.join(statement_lines)

        # Split at :=
        if ':=' in full_statement_line:
            parts = full_statement_line.split(':=', 1)
            statement_part = parts[0].strip()
            # Remove 'by' if it's at the start of proof
            after_eq = parts[1].strip()
            if after_eq.startswith('by'):
                after_eq = after_eq[2:].strip()
        else:
            return None

        # Now collect the proof (everything after := by until we hit certain keywords)
        proof_lines = []
        if after_eq and not after_eq.startswith(('Hint', 'Branch')):
            # If there's code on the same line as :=, include it
            proof_lines.append(after_eq)

        i += 1  # Start from next line after :=

        while i < len(lines):
            line = lines[i]
            stripped = line.strip()

            # Stop at next top-level declaration
            if stripped.startswith(('Statement ', 'theorem ', 'lemma ', 'TheoremTab',
                                   'Conclusion', 'NewTactic', 'end ', 'World ', 'Level ',
                                   'TacticDoc', 'Introduction')):
                break

            # Include the line in proof
            proof_lines.append(line)

            i += 1
            if i - start_idx > 200:  # Safety limit
                break

        proof = '\n'.join(proof_lines).strip()

        return {
            'statement': statement_part,
            'proof': proof
        }

    def extract_declaration(self, lines: List[str], start_idx: int) -> Optional[Dict[str, str]]:
        """
        Extract a theorem/lemma declaration starting at the given line.

        Args:
            lines: All lines in the file
            start_idx: Index where the theorem/lemma starts

        Returns:
            Dictionary with 'statement' and 'proof'
        """
        full_text = lines[start_idx]
        i = start_idx + 1

        # Collect lines until we find the complete declaration
        found_assignment = ':=' in full_text
        proof_start_idx = -1

        while i < len(lines):
            line = lines[i]
            full_text += '\n' + line

            if ':=' in line and not found_assignment:
                found_assignment = True
                proof_start_idx = i

            if found_assignment:
                stripped = line.strip()
                # Stop at next declaration or end of namespace
                if stripped.startswith(('theorem ', 'lemma ', 'def ', 'end ', 'namespace ')):
                    # Remove the last line
                    full_text = '\n'.join(full_text.split('\n')[:-1])
                    break
                # Stop at blank line after substantive content
                if not stripped and i > start_idx + 2:
                    break

            i += 1
            if i - start_idx > 100:  # Safety limit
                break

        # Now split into statement and proof
        if ':=' not in full_text:
            return None

        parts = full_text.split(':=', 1)
        if len(parts) != 2:
            return None

        statement = parts[0].strip()
        proof = parts[1].strip()

        # Clean up proof - remove "by" if it's at the start
        if proof.startswith('by'):
            proof = proof[2:].strip()

        return {
            'statement': statement,
            'proof': proof
        }

    def remove_comments(self, content: str) -> str:
        """
        Remove Lean comments from content.

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

    def extract_all_levels(self) -> List[Dict]:
        """
        Extract all levels from the Levels directory.

        Returns:
            List of level dictionaries
        """
        level_files = self.find_all_level_files()

        print(f"Found {len(level_files)} level files")

        levels = []
        level_id = 1

        for file_path in level_files:
            print(f"Processing: {file_path.relative_to(self.levels_dir)}")

            result = self.extract_theorem_from_file(file_path)

            if result:
                levels.append({
                    'id': level_id,
                    'file': str(file_path.relative_to(self.levels_dir)),
                    'statement': result['statement'],
                    'proof': result['proof']
                })
                level_id += 1
            else:
                print(f"  Warning: No theorem found in {file_path.name}")

        return levels


class DatasetBuilder:
    """Build the final JSONL dataset with headers and level data."""

    def __init__(self, mynat_jsonl: str = "mynat_definitions.jsonl"):
        """
        Initialize builder.

        Args:
            mynat_jsonl: Path to MyNat definitions JSONL file
        """
        self.mynat_jsonl = Path(mynat_jsonl)
        self.header_definitions = []

    def load_header(self) -> List[Dict[str, str]]:
        """
        Load all MyNat definitions from JSONL to use as header.

        Returns:
            List of definition dictionaries
        """
        if not self.mynat_jsonl.exists():
            raise FileNotFoundError(f"MyNat definitions file not found: {self.mynat_jsonl}")

        print(f"Loading header from: {self.mynat_jsonl}")

        with open(self.mynat_jsonl, 'r', encoding='utf-8') as f:
            for line in f:
                entry = json.loads(line.strip())
                self.header_definitions.append(entry)

        print(f"Loaded {len(self.header_definitions)} header definitions")
        return self.header_definitions

    def build_dataset(self, levels: List[Dict]) -> List[Dict]:
        """
        Build the final dataset by combining header with each level.

        Args:
            levels: List of extracted levels

        Returns:
            List of dataset entries
        """
        dataset = []

        for level in levels:
            entry = {
                'id': level['id'],
                'file': level['file'],
                'header': self.header_definitions,
                'statement': level['statement'],
                'ground_truth': level['proof']
            }
            dataset.append(entry)

        return dataset

    def save_to_jsonl(self, dataset: List[Dict], output_path: str):
        """
        Save dataset to JSONL file.

        Args:
            dataset: List of dataset entries
            output_path: Path to output JSONL file
        """
        output_file = Path(output_path)

        with open(output_file, 'w', encoding='utf-8') as f:
            for entry in dataset:
                json.dump(entry, f, ensure_ascii=False)
                f.write('\n')

        print(f"\n✓ Saved dataset to: {output_file}")
        print(f"  Total entries: {len(dataset)}")


def main():
    """Main function to build the level dataset."""

    parser = argparse.ArgumentParser(
        description='Build NNG4 level dataset for LLM training'
    )
    parser.add_argument(
        '--levels-dir',
        default='externals/NNG4/Game/Levels',
        help='Path to the Game/Levels directory (default: externals/NNG4/Game/Levels)'
    )
    parser.add_argument(
        '--header',
        default='mynat_definitions.jsonl',
        help='Path to MyNat definitions JSONL (default: mynat_definitions.jsonl)'
    )
    parser.add_argument(
        '-o', '--output',
        default='nng_level_dataset.jsonl',
        help='Output JSONL file path (default: nng_level_dataset.jsonl)'
    )

    args = parser.parse_args()

    print("="*70)
    print("NNG4 Level Dataset Builder")
    print("="*70)
    print()

    # Step 1: Extract all levels
    print("STEP 1: Extracting levels from Lean files")
    print("-"*70)
    extractor = LevelExtractor(args.levels_dir)
    levels = extractor.extract_all_levels()

    if not levels:
        print("Error: No levels extracted!")
        return 1

    print(f"\n✓ Extracted {len(levels)} levels")

    # Step 2: Load header and build dataset
    print("\n" + "="*70)
    print("STEP 2: Building dataset with headers")
    print("-"*70)
    builder = DatasetBuilder(args.header)

    try:
        builder.load_header()
    except FileNotFoundError as e:
        print(f"Error: {e}")
        print("Please run parse_mynat_definitions.py first to generate the header file.")
        return 1

    dataset = builder.build_dataset(levels)

    # Step 3: Save to JSONL
    print("\n" + "="*70)
    print("STEP 3: Saving dataset")
    print("-"*70)
    builder.save_to_jsonl(dataset, args.output)

    # Print summary
    print("\n" + "="*70)
    print("SUMMARY")
    print("="*70)
    print(f"Total levels: {len(dataset)}")
    print(f"Header definitions: {len(builder.header_definitions)}")
    print(f"Output file: {args.output}")

    # Show first few examples
    print("\nFirst 5 levels:")
    for i, entry in enumerate(dataset[:5], 1):
        print(f"  {i}. {entry['file']}")
        print(f"     Statement: {entry['statement'][:60]}...")
        print(f"     Proof length: {len(entry['ground_truth'])} chars")

    print("\n" + "="*70)
    print("✓ Dataset build complete!")
    print("="*70)

    return 0


if __name__ == "__main__":
    import sys
    sys.exit(main())
