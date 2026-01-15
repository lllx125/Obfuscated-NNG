"""
Betweenness Centrality Analysis
-------------------------------
Calculates the "Bridge Status" of every theorem.
It measures how often a node appears on the shortest path between
two other nodes in the graph.

High Score = This theorem is a critical structural "bottleneck" or "bridge".
             It connects the axioms to the complex results.
"""

import networkx as nx
import numpy as np
from generate_graph import GraphGenerator

def calculate_betweenness(dataset_path="dataset/original"):
    print(f"Loading graph from {dataset_path}...")
    
    # 1. Load Graph
    # We use reverse_direction=True so edges point from Dependency -> Dependent
    # This models the "Flow of Truth" (Axioms -> Lemmas -> Theorems)
    graph_gen = GraphGenerator(dataset_path=dataset_path, reverse_direction=True)
    adj_matrix = graph_gen.get_graph()
    nodes = graph_gen.get_nodes()
    names = graph_gen.get_node_names()
    
    # 2. Convert to NetworkX Directed Graph
    # nx.from_numpy_array automatically handles the adjacency matrix
    G = nx.from_numpy_array(adj_matrix, create_using=nx.DiGraph)
    
    print(f"Graph loaded: {G.number_of_nodes()} nodes, {G.number_of_edges()} edges.")
    print("Calculating Betweenness Centrality (this may take a moment)...")
    
    # 3. Calculate Betweenness Centrality
    # normalized=True ensures scores are between 0 and 1
    scores = nx.betweenness_centrality(G, normalized=True)
    
    # 4. Sort Results
    # Sort dictionary by value in descending order
    ranked_indices = sorted(scores, key=scores.get, reverse=True)
    
    # 5. Print Report
    print("\n" + "="*80)
    print(f"{'Rank':<5} | {'Name':<25} | {'Score':<8} | {'Statement Snippet'}")
    print("="*80)
    
    for i, idx in enumerate(ranked_indices):
        name = names[idx]
        score = scores[idx]
        
        # Get code/statement
        node_data = nodes[idx]
        code = node_data.get('statement', node_data.get('code', ''))
        code_snippet = code.split(':=')[0].strip()  # Clean up formatting
        if len(code_snippet) > 40:
            code_snippet = code_snippet[:37] + "..."
            
        print(f"{i+1:<5} | {name:<25} | {score:.4f}   | {code_snippet}")
        
    print("-" * 80)
    print("INTERPRETATION:")
    print("High Betweenness = 'The Bridge'. These theorems connect the")
    print("foundational axioms to the advanced algebraic results.")
    print("They are the 'waist' of the hourglass.")

if __name__ == "__main__":
    # Ensure networkx is installed
    try:
        import networkx
        calculate_betweenness()
    except ImportError:
        print("Error: This script requires networkx.")
        print("Please install it via: pip install networkx")