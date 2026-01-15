"""
Prestige Centrality Analysis for Theorem Dependencies

This script calculates the prestige centrality (PageRank) for every theorem and lemma
in the dependency graph. The algorithm treats main theorems (sinks in the DAG) as
sources of prestige and lets that prestige flow backwards through dependency edges.

The prestige flow is: Theorem -> Lemma (theorem votes for the lemmas it depends on)
"""

import numpy as np
from typing import Dict, List, Tuple
from generate_graph import GraphGenerator


class PrestigeCentrality:
    """
    Calculate prestige centrality using PageRank algorithm on the dependency graph.

    The prestige flows from theorems to the lemmas/axioms they depend on.
    """

    def __init__(self, damping_factor: float = 0.85, max_iterations: int = 100,
                 tolerance: float = 1e-6):
        """
        Initialize the Prestige Centrality calculator.

        Args:
            damping_factor: Probability of following a link (default 0.85)
            max_iterations: Maximum number of iterations (default 100)
            tolerance: Convergence threshold (default 1e-6)
        """
        self.damping_factor = damping_factor
        self.max_iterations = max_iterations
        self.tolerance = tolerance

        self.prestige_scores = None
        self.iterations_run = 0
        self.converged = False

    def calculate(self, graph_gen: GraphGenerator) -> np.ndarray:
        """
        Calculate prestige centrality scores for all nodes.

        Args:
            graph_gen: GraphGenerator instance with loaded graph

        Returns:
            Array of prestige scores for each node
        """
        # Get graph data
        adj_matrix = graph_gen.get_graph()
        nodes = graph_gen.get_nodes()
        N = len(nodes)

        print(f"Calculating Prestige Centrality for {N} nodes...")
        print(f"Damping factor: {self.damping_factor}")
        print(f"Max iterations: {self.max_iterations}")
        print(f"Tolerance: {self.tolerance}")

        # 1. INITIALIZATION
        prestige_scores = np.ones(N, dtype=np.float64) / N

        # 2. PRE-PROCESSING: Calculate out-degrees
        # Note: In our graph, edge B->A means A uses B
        # For prestige flow, we want A to share prestige with B (what it depends on)
        # So we need to use the transpose: if A uses B, A shares prestige with B

        # Out-degree: how many nodes does this node share prestige with
        # In our case: how many dependencies does this node have
        out_degrees = np.sum(adj_matrix, axis=0)  # Column sum (incoming edges in original)

        # For prestige flow: we want to know "who depends on me"
        # So we actually need row sums (outgoing edges in original)
        out_degrees = np.sum(adj_matrix, axis=1)  # Row sum (outgoing edges)

        # 3. POWER ITERATION
        d = self.damping_factor
        teleport = (1 - d) / N

        for iteration in range(self.max_iterations):
            new_scores = np.full(N, teleport, dtype=np.float64)

            # For each node T
            for T in range(N):
                if out_degrees[T] > 0:
                    # Share T's prestige among nodes that T points to
                    share = (d * prestige_scores[T]) / out_degrees[T]

                    # Find all nodes that T points to
                    for L in range(N):
                        if adj_matrix[T][L] == 1:
                            new_scores[L] += share
                else:
                    # Axiom/dead-end: redistribute prestige to all nodes
                    new_scores += (d * prestige_scores[T]) / N

            # Check for convergence (L1 norm)
            diff = np.sum(np.abs(new_scores - prestige_scores))

            if (iteration + 1) % 10 == 0:
                print(f"  Iteration {iteration + 1}: diff = {diff:.2e}")

            if diff < self.tolerance:
                self.converged = True
                self.iterations_run = iteration + 1
                print(f"✓ Converged after {self.iterations_run} iterations (diff={diff:.2e})")
                prestige_scores = new_scores
                break

            prestige_scores = new_scores
        else:
            self.iterations_run = self.max_iterations
            print(f"⚠ Did not converge after {self.max_iterations} iterations (diff={diff:.2e})")

        # Normalize scores to sum to 1
        prestige_scores = prestige_scores / np.sum(prestige_scores)

        self.prestige_scores = prestige_scores
        return prestige_scores

    def get_ranked_nodes(self, graph_gen: GraphGenerator,
                        top_k: int = None) -> List[Tuple[int, str, float, str]]:
        """
        Get nodes ranked by prestige score.

        Args:
            graph_gen: GraphGenerator instance
            top_k: Return only top k nodes (None for all)

        Returns:
            List of tuples: (rank, name, score, statement/code)
        """
        if self.prestige_scores is None:
            raise ValueError("Must call calculate() first")

        nodes = graph_gen.get_nodes()
        node_names = graph_gen.get_node_names()

        # Sort by score descending
        sorted_indices = np.argsort(self.prestige_scores)[::-1]

        ranked = []
        for rank, idx in enumerate(sorted_indices, 1):
            if top_k and rank > top_k:
                break

            node = nodes[idx]
            name = node_names[idx]
            score = self.prestige_scores[idx]

            # Get statement or code
            if 'statement' in node:
                statement = node['statement']
            elif 'code' in node:
                statement = node['code']
            else:
                statement = f"[{node.get('category', 'unknown')}]"

            ranked.append((rank, name, score, statement))

        return ranked


class OptimizedPrestigeCentrality(PrestigeCentrality):
    """
    Optimized version using matrix operations for better performance.
    """

    def calculate(self, graph_gen: GraphGenerator) -> np.ndarray:
        """
        Calculate prestige centrality using vectorized operations.

        Args:
            graph_gen: GraphGenerator instance with loaded graph

        Returns:
            Array of prestige scores for each node
        """
        # Get graph data
        adj_matrix = graph_gen.get_graph()
        N = adj_matrix.shape[0]

        print(f"Calculating Prestige Centrality (Optimized) for {N} nodes...")
        print(f"Damping factor: {self.damping_factor}")
        print(f"Max iterations: {self.max_iterations}")
        print(f"Tolerance: {self.tolerance}")

        # Convert to float for numerical stability
        adj_matrix = adj_matrix.astype(np.float64)

        # Calculate out-degrees (row sums)
        out_degrees = np.sum(adj_matrix, axis=1)

        # Create transition matrix M
        # M[i,j] = 1/out_degree[i] if there's an edge i->j, else 0
        M = np.zeros_like(adj_matrix, dtype=np.float64)

        for i in range(N):
            if out_degrees[i] > 0:
                M[i, :] = adj_matrix[i, :] / out_degrees[i]

        # Handle dangling nodes (axioms with no dependencies)
        dangling_mask = (out_degrees == 0)
        num_dangling = np.sum(dangling_mask)

        # Initialize prestige
        prestige = np.ones(N, dtype=np.float64) / N

        d = self.damping_factor
        teleport_vector = np.ones(N, dtype=np.float64) / N

        # Power iteration
        for iteration in range(self.max_iterations):
            # Regular PageRank update: d * M^T @ prestige
            new_prestige = d * (M.T @ prestige)

            # Handle dangling nodes: redistribute their mass
            if num_dangling > 0:
                dangling_mass = d * np.sum(prestige[dangling_mask])
                new_prestige += dangling_mass * teleport_vector

            # Add teleportation
            new_prestige += (1 - d) * teleport_vector

            # Check convergence
            diff = np.sum(np.abs(new_prestige - prestige))

            if (iteration + 1) % 10 == 0:
                print(f"  Iteration {iteration + 1}: diff = {diff:.2e}")

            if diff < self.tolerance:
                self.converged = True
                self.iterations_run = iteration + 1
                print(f"✓ Converged after {self.iterations_run} iterations (diff={diff:.2e})")
                prestige = new_prestige
                break

            prestige = new_prestige
        else:
            self.iterations_run = self.max_iterations
            print(f"⚠ Did not converge after {self.max_iterations} iterations (diff={diff:.2e})")

        # Normalize
        prestige = prestige / np.sum(prestige)

        self.prestige_scores = prestige
        return prestige


def analyze_and_report(dataset_path: str = "dataset/original",
                      top_k: int = 50,
                      use_optimized: bool = True,
                      output_file: str = None):
    """
    Analyze the graph and generate a prestige report.

    Args:
        dataset_path: Path to dataset folder
        top_k: Number of top results to print (None for all)
        use_optimized: Use optimized matrix operations
        output_file: Path to save full results (None to skip)
    """
    print("=" * 80)
    print("PRESTIGE CENTRALITY ANALYSIS")
    print("=" * 80)

    # Load graph
    print("\n[1] Loading graph...")
    graph_gen = GraphGenerator(dataset_path=dataset_path, reverse_direction=True)
    adj_matrix = graph_gen.get_graph()
    nodes = graph_gen.get_nodes()

    print(f"    Loaded {len(nodes)} nodes with {np.sum(adj_matrix)} edges")

    # Calculate prestige
    print(f"\n[2] Calculating prestige centrality...")
    if use_optimized:
        pc = OptimizedPrestigeCentrality()
    else:
        pc = PrestigeCentrality()

    scores = pc.calculate(graph_gen)

    # Get rankings
    print(f"\n[3] Generating rankings...")
    ranked = pc.get_ranked_nodes(graph_gen, top_k=None)

    # Print top results
    print("\n" + "=" * 80)
    print(f"TOP {min(top_k, len(ranked))} MOST PRESTIGIOUS THEOREMS/LEMMAS")
    print("=" * 80)

    for rank, name, score, statement in ranked[:top_k]:
        # Truncate long statements
        if len(statement) > 100:
            statement = statement[:97] + "..."

        print(f"\n[{rank}] {name}")
        print(f"    Score: {score:.6e} ({score*len(nodes):.4f}x average)")
        print(f"    {statement}")

    # Statistics
    print("\n" + "=" * 80)
    print("STATISTICS")
    print("=" * 80)
    print(f"Total nodes: {len(nodes)}")
    print(f"Average score: {1.0/len(nodes):.6e}")
    print(f"Max score: {np.max(scores):.6e} ({nodes[np.argmax(scores)]['name']})")
    print(f"Min score: {np.min(scores):.6e}")
    print(f"Std dev: {np.std(scores):.6e}")
    print(f"Converged: {pc.converged}")
    print(f"Iterations: {pc.iterations_run}")

    # Save full results if requested
    if output_file:
        print(f"\n[4] Saving full results to {output_file}...")
        with open(output_file, 'w') as f:
            f.write("# Prestige Centrality Rankings\n")
            f.write(f"# Total nodes: {len(nodes)}\n")
            f.write(f"# Converged: {pc.converged} after {pc.iterations_run} iterations\n")
            f.write("#\n")
            f.write("# Rank | Name | Score | Statement\n")
            f.write("#" + "=" * 78 + "\n\n")

            for rank, name, score, statement in ranked:
                f.write(f"[{rank}] {name}\n")
                f.write(f"Score: {score:.6e}\n")
                f.write(f"{statement}\n")
                f.write("\n" + "-" * 80 + "\n\n")

        print(f"    ✓ Saved {len(ranked)} rankings")

    return pc, ranked


def main():
    """Command-line interface"""
    import argparse

    parser = argparse.ArgumentParser(description='Calculate prestige centrality for theorem dependencies')
    parser.add_argument('--dataset', type=str, default='dataset/original',
                       help='Path to dataset folder')
    parser.add_argument('--top', type=int, default=50,
                       help='Number of top results to print')
    parser.add_argument('--output', type=str, default="prestige_rankings.txt",
                       help='Output file for full rankings')
    parser.add_argument('--damping', type=float, default=0.85,
                       help='Damping factor (default: 0.85)')
    parser.add_argument('--max-iter', type=int, default=200,
                       help='Maximum iterations (default: 200)')
    parser.add_argument('--tolerance', type=float, default=1e-8,
                       help='Convergence tolerance (default: 1e-8)')
    parser.add_argument('--no-optimize', action='store_true',
                       help='Disable optimized matrix operations')

    args = parser.parse_args()

    # Run analysis
    analyze_and_report(
        dataset_path=args.dataset,
        top_k=args.top,
        use_optimized=not args.no_optimize,
        output_file=args.output
    )


if __name__ == "__main__":
    main()
