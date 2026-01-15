import json
import numpy as np
import re
from pathlib import Path
from typing import List, Dict, Tuple, Optional


class GraphGenerator:
    """
    Generates a directed graph from the NNG dataset.

    The graph represents dependencies between theorems and definitions:
    - Default direction: If A uses B, then B -> A (dependency points to user)
    - Can be toggled to reverse direction
    """

    def __init__(self, dataset_path: str = "dataset/original", reverse_direction: bool = False):
        """
        Initialize the graph generator.

        Args:
            dataset_path: Path to the dataset folder containing header_definitions.jsonl and theorems.jsonl
            reverse_direction: If True, reverse edge direction (A -> B means A uses B)
        """
        self.dataset_path = Path(dataset_path)
        self.reverse_direction = reverse_direction
        self.nodes: List[Dict] = []
        self.node_names: List[str] = []
        self.node_to_idx: Dict[str, int] = {}
        self.adjacency_matrix: Optional[np.ndarray] = None

    def load_dataset(self) -> None:
        """Load nodes from header_definitions.jsonl and theorems.jsonl"""
        self.nodes = []
        self.node_names = []

        # Load header definitions
        header_file = self.dataset_path / "header_definitions.jsonl"
        with open(header_file, 'r') as f:
            for line in f:
                node = json.loads(line)
                node['source'] = 'header'
                self.nodes.append(node)
                self.node_names.append(node['name'])

        # Load theorems
        theorems_file = self.dataset_path / "theorems.jsonl"
        with open(theorems_file, 'r') as f:
            for line in f:
                node = json.loads(line)
                node['source'] = 'theorem'
                self.nodes.append(node)
                self.node_names.append(node['name'])

        # Create name to index mapping
        self.node_to_idx = {name: idx for idx, name in enumerate(self.node_names)}

    def _extract_identifiers(self, code: str) -> set:
        """
        Extract potential identifiers (names) used in code/proof.
        Uses simple regex to find word-like tokens that could be references.
        """
        # Match valid Lean identifiers (letters, digits, underscores, apostrophes)
        pattern = r'\b[a-zA-Z_][a-zA-Z0-9_\']*\b'
        identifiers = set(re.findall(pattern, code))

        # Filter out Lean keywords
        keywords = {
            'theorem', 'axiom', 'def', 'inductive', 'instance', 'where',
            'with', 'by', 'rw', 'exact', 'apply', 'at', 'induction',
            'opaque', 'MyNat', 'let', 'have', 'show', 'if', 'then', 'else',
            'match', 'fun', 'λ', 'forall', '∀', 'exists', '∃', 'sorry',
            'rfl', 'simp', 'intro', 'intros', 'cases', 'revert', 'constructor'
        }

        return identifiers - keywords

    def _find_dependencies(self, node: Dict) -> List[str]:
        """
        Find which other nodes this node depends on (uses in its code/proof).

        Args:
            node: Node dictionary

        Returns:
            List of node names that this node depends on
        """
        # Only analyze theorems (skip axioms and definitions per requirements)
        if node.get('category') in ['axiom', 'def', 'inductive', 'constructor', 'instance', 'opaque']:
            return []

        # Get the code to analyze
        if node['source'] == 'header':
            code = node.get('code', '')
        else:  # theorem
            code = node.get('proof', '')

        # Extract identifiers used in the code
        used_identifiers = self._extract_identifiers(code)

        # Find which of these identifiers are actual nodes in our graph
        dependencies = []
        for identifier in used_identifiers:
            if identifier in self.node_to_idx and identifier != node['name']:
                dependencies.append(identifier)

        return dependencies

    def build_graph(self) -> np.ndarray:
        """
        Build the adjacency matrix for the dependency graph.

        Returns:
            N x N numpy array where N is the number of nodes.
            adjacency_matrix[i][j] = 1 means there's an edge from node i to node j
        """
        n = len(self.nodes)
        self.adjacency_matrix = np.zeros((n, n), dtype=int)

        for idx, node in enumerate(self.nodes):
            dependencies = self._find_dependencies(node)

            for dep_name in dependencies:
                dep_idx = self.node_to_idx[dep_name]

                if self.reverse_direction:
                    # Reverse direction: user points to dependency (A uses B -> A->B)
                    self.adjacency_matrix[idx][dep_idx] = 1
                else:
                    # Default: dependency points to user (A uses B -> B->A)
                    self.adjacency_matrix[dep_idx][idx] = 1

        return self.adjacency_matrix

    def get_graph(self) -> np.ndarray:
        """
        Get the adjacency matrix. If not built yet, builds it first.

        Returns:
            N x N numpy adjacency matrix
        """
        if self.adjacency_matrix is None:
            self.load_dataset()
            self.build_graph()
        return self.adjacency_matrix

    def get_nodes(self) -> List[Dict]:
        """Get the list of nodes"""
        if not self.nodes:
            self.load_dataset()
        return self.nodes

    def get_node_names(self) -> List[str]:
        """Get the list of node names"""
        if not self.node_names:
            self.load_dataset()
        return self.node_names

    def get_graph_info(self) -> Dict:
        """
        Get comprehensive graph information.

        Returns:
            Dictionary with graph metadata
        """
        if self.adjacency_matrix is None:
            self.get_graph()

        num_edges = np.sum(self.adjacency_matrix)

        return {
            'num_nodes': len(self.nodes),
            'num_edges': int(num_edges),
            'num_header_nodes': sum(1 for n in self.nodes if n['source'] == 'header'),
            'num_theorem_nodes': sum(1 for n in self.nodes if n['source'] == 'theorem'),
            'reverse_direction': self.reverse_direction,
            'node_names': self.node_names
        }


def main():
    """Example usage"""
    # Create graph with default direction
    graph_gen = GraphGenerator(dataset_path="dataset/original", reverse_direction=False)

    # Get the adjacency matrix
    adj_matrix = graph_gen.get_graph()

    # Get graph info
    info = graph_gen.get_graph_info()

    print(f"Graph Statistics:")
    print(f"  Total nodes: {info['num_nodes']}")
    print(f"  Header definitions: {info['num_header_nodes']}")
    print(f"  Theorems: {info['num_theorem_nodes']}")
    print(f"  Total edges: {info['num_edges']}")
    print(f"  Direction: {'Reversed (A uses B -> A->B)' if info['reverse_direction'] else 'Default (A uses B -> B->A)'}")
    print(f"\nAdjacency matrix shape: {adj_matrix.shape}")


if __name__ == "__main__":
    main()
