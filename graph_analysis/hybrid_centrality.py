"""
Hybrid Centrality Analysis
--------------------------
Calculates "Meaningfulness" by combining:
1. Standard PageRank (Complexity/Depth)
2. Reversed PageRank (Foundational/Utility)

Metric = Sqrt(Standard_Score * Reversed_Score)
"""

import numpy as np
from typing import List, Tuple
from generate_graph import GraphGenerator

class HybridCentrality:
    def __init__(self, damping_factor: float = 0.85, max_iterations: int = 100, tolerance: float = 1e-6):
        self.damping_factor = damping_factor
        self.max_iterations = max_iterations
        self.tolerance = tolerance

    def _calculate_pagerank_vector(self, adj_matrix: np.ndarray) -> np.ndarray:
        """
        Internal method to calculate PageRank for a specific adjacency matrix.
        Uses optimized matrix operations.
        """
        N = adj_matrix.shape[0]
        
        # specific check for empty graph
        if N == 0:
            return np.array([])

        # Convert to float
        M = adj_matrix.astype(np.float64)
        
        # Calculate out-degrees (row sums)
        out_degrees = np.sum(M, axis=1)
        
        # Create transition matrix (normalize rows)
        # Avoid division by zero
        with np.errstate(divide='ignore', invalid='ignore'):
            M = M / out_degrees[:, None]
            M[np.isnan(M)] = 0.0
            
        # Handle dangling nodes (nodes with no outgoing edges)
        dangling_mask = (out_degrees == 0)
        
        # Initialize scores uniformly
        scores = np.ones(N, dtype=np.float64) / N
        teleport = np.ones(N, dtype=np.float64) / N
        d = self.damping_factor

        for _ in range(self.max_iterations):
            prev_scores = scores.copy()
            
            # 1. Flow through edges: (d * M.T @ scores)
            new_scores = d * (M.T @ scores)
            
            # 2. Distribute dangling mass (nodes that lead nowhere vote for everyone)
            dangling_mass = d * np.sum(scores[dangling_mask])
            new_scores += dangling_mass * teleport
            
            # 3. Add random teleportation (1-d)
            new_scores += (1 - d) * teleport
            
            # Check convergence
            diff = np.sum(np.abs(new_scores - prev_scores))
            scores = new_scores
            
            if diff < self.tolerance:
                break
                
        return scores / np.sum(scores)

    def calculate_hybrid(self, dataset_path: str = "dataset/original") -> Tuple[List[Tuple], np.ndarray]:
        """
        Runs the dual analysis and returns the ranked list.
        """
        print(f"Loading graph from {dataset_path}...")
        
        # 1. Calculate Standard PageRank (Measures Complexity/Depth)
        # This finds the "sinks" (advanced theorems)
        print("1. Calculating Complexity Score (Standard PageRank)...")
        gen_std = GraphGenerator(dataset_path=dataset_path, reverse_direction=False)
        adj_std = gen_std.get_graph()
        scores_std = self._calculate_pagerank_vector(adj_std)
        
        # 2. Calculate Reversed PageRank (Measures Foundation/Utility)
        # This finds the "sources" (axioms/tools)
        print("2. Calculating Foundation Score (Reversed PageRank)...")
        gen_rev = GraphGenerator(dataset_path=dataset_path, reverse_direction=True)
        adj_rev = gen_rev.get_graph()
        scores_rev = self._calculate_pagerank_vector(adj_rev)

        # 3. Combine Scores (Geometric Mean)
        # Metric = sqrt(Complexity * Foundation)
        print("3. Computing Hybrid 'Meaningfulness' Score...")
        
        # Get nodes and names (assuming same order for both generators)
        nodes = gen_std.get_nodes()
        names = gen_std.get_node_names()
        N = len(nodes)
        
        hybrid_scores = np.sqrt(scores_std * scores_rev)
        
        # Normalize result for readability
        hybrid_scores = hybrid_scores / np.sum(hybrid_scores)

        # 4. Rank Results
        ranked_indices = np.argsort(hybrid_scores)[::-1]
        
        results = []
        for rank, idx in enumerate(ranked_indices, 1):
            name = names[idx]
            score = hybrid_scores[idx]
            
            # Get code snippet
            node_data = nodes[idx]
            code = node_data.get('statement', node_data.get('code', ''))
            
            # Add partial scores for analysis
            debug_info = {
                'std': scores_std[idx],
                'rev': scores_rev[idx]
            }
            
            results.append((rank, name, score, code, debug_info))
            
        return results, hybrid_scores

def main():
    analyzer = HybridCentrality()
    rankings, _ = analyzer.calculate_hybrid()

    print("\n" + "="*90)
    print(f"{'Rank':<5} | {'Name':<20} | {'Score':<8} | {'Complexity (Std)':<16} | {'Foundation (Rev)':<16}")
    print("="*90)
    
    # Print Top 20
    for rank, name, score, code, debug in rankings[:]:
        print(f"{rank:<5} | {name:<20} | {score:.4f}   | {debug['std']:.4f}           | {debug['rev']:.4f}")
        
    print("\nTop 5 Most Meaningful Theorems (Code):")
    print("-" * 40)
    for i in range(5):
        print(f"[{i+1}] {rankings[i][1]}")
        print(f"    {rankings[i][3][:80]}...")
        print("-" * 40)

if __name__ == "__main__":
    main()