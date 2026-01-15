"""
Example usage of the graph analysis tools.

This script demonstrates how to:
1. Generate a dependency graph from the NNG dataset
2. Access the adjacency matrix
3. Get graph statistics
4. Visualize the graph
"""

from generate_graph import GraphGenerator
from draw_graph import plot_graph
import numpy as np


def example_basic_usage():
    """Basic usage: create graph and get adjacency matrix"""
    print("=" * 60)
    print("Example 1: Basic Usage - Get Adjacency Matrix")
    print("=" * 60)

    # Create graph generator with default direction
    graph_gen = GraphGenerator(dataset_path="dataset/original", reverse_direction=False)

    # Get the adjacency matrix
    adj_matrix = graph_gen.get_graph()

    print(f"Adjacency matrix shape: {adj_matrix.shape}")
    print(f"Adjacency matrix type: {type(adj_matrix)}")
    print(f"Total edges: {np.sum(adj_matrix)}")
    print()


def example_graph_info():
    """Get detailed graph information"""
    print("=" * 60)
    print("Example 2: Graph Information and Statistics")
    print("=" * 60)

    graph_gen = GraphGenerator(dataset_path="dataset/original", reverse_direction=False)
    info = graph_gen.get_graph_info()

    print(f"Total nodes: {info['num_nodes']}")
    print(f"  - Header definitions: {info['num_header_nodes']}")
    print(f"  - Theorems: {info['num_theorem_nodes']}")
    print(f"Total edges: {info['num_edges']}")
    print(f"Direction reversed: {info['reverse_direction']}")
    print(f"\nFirst 10 node names:")
    for i, name in enumerate(info['node_names'][:10]):
        print(f"  {i}: {name}")
    print()


def example_reversed_direction():
    """Create graph with reversed edge direction"""
    print("=" * 60)
    print("Example 3: Reversed Direction Graph")
    print("=" * 60)

    # Create graph with reversed direction
    graph_gen = GraphGenerator(dataset_path="dataset/original", reverse_direction=True)
    adj_matrix = graph_gen.get_graph()
    info = graph_gen.get_graph_info()

    print(f"Direction: {'Reversed (dep → user)' if info['reverse_direction'] else 'Default (user → dep)'}")
    print(f"Total nodes: {info['num_nodes']}")
    print(f"Total edges: {info['num_edges']}")
    print()


def example_inspect_specific_node():
    """Inspect dependencies for a specific node"""
    print("=" * 60)
    print("Example 4: Inspect Specific Node Dependencies")
    print("=" * 60)

    graph_gen = GraphGenerator(dataset_path="dataset/original", reverse_direction=False)
    adj_matrix = graph_gen.get_graph()
    nodes = graph_gen.get_nodes()
    node_names = graph_gen.get_node_names()

    # Find a specific theorem (e.g., "add_comm")
    target_name = "add_comm"
    if target_name in node_names:
        idx = node_names.index(target_name)
        node = nodes[idx]

        print(f"Node: {target_name}")
        print(f"Source: {node['source']}")
        if 'category' in node:
            print(f"Category: {node['category']}")
        if 'id' in node:
            print(f"ID: {node['id']}")

        # Find what this node depends on (outgoing edges)
        dependencies = [node_names[j] for j in range(len(adj_matrix)) if adj_matrix[idx][j] == 1]
        print(f"\nDepends on ({len(dependencies)} nodes):")
        for dep in dependencies[:10]:  # Show first 10
            print(f"  - {dep}")

        # Find what depends on this node (incoming edges)
        dependents = [node_names[i] for i in range(len(adj_matrix)) if adj_matrix[i][idx] == 1]
        print(f"\nUsed by ({len(dependents)} nodes):")
        for dep in dependents[:10]:  # Show first 10
            print(f"  - {dep}")
    else:
        print(f"Node '{target_name}' not found in graph")
    print()


def example_visualize_graph():
    """Visualize the graph"""
    print("=" * 60)
    print("Example 5: Visualize Graph")
    print("=" * 60)

    print("Creating visualization...")
    print("Note: This will save the graph to 'graph_analysis/dependency_graph.png'")

    # Create and plot graph
    plot_graph(
        dataset_path="dataset/original",
        reverse_direction=False,
        figsize=(24, 16),
        save_path="graph_analysis/dependency_graph.png",
        show_labels=True,
        label_header_only=True,  # Only label header nodes, use IDs for theorems
        node_size=400,
        font_size=7
    )

    print("Graph visualization saved!")
    print()


def example_adjacency_matrix_access():
    """Direct access to adjacency matrix for custom analysis"""
    print("=" * 60)
    print("Example 6: Custom Analysis Using Adjacency Matrix")
    print("=" * 60)

    graph_gen = GraphGenerator(dataset_path="dataset/original", reverse_direction=False)
    adj_matrix = graph_gen.get_graph()
    node_names = graph_gen.get_node_names()

    # Find nodes with most dependencies (most outgoing edges)
    out_degrees = np.sum(adj_matrix, axis=1)
    top_5_idx = np.argsort(out_degrees)[-5:][::-1]

    print("Top 5 nodes with most dependencies (most things they use):")
    for idx in top_5_idx:
        print(f"  {node_names[idx]}: {out_degrees[idx]} dependencies")

    # Find most depended-upon nodes (most incoming edges)
    in_degrees = np.sum(adj_matrix, axis=0)
    top_5_idx = np.argsort(in_degrees)[-5:][::-1]

    print("\nTop 5 most used nodes (most things that use them):")
    for idx in top_5_idx:
        print(f"  {node_names[idx]}: {in_degrees[idx]} usages")

    # Find isolated nodes (no edges)
    isolated = np.where((in_degrees == 0) & (out_degrees == 0))[0]
    print(f"\nIsolated nodes (no dependencies): {len(isolated)}")
    if len(isolated) > 0:
        print("  Examples:", [node_names[i] for i in isolated[:5]])

    print()


if __name__ == "__main__":
    # Run all examples
    example_basic_usage()
    example_graph_info()
    example_reversed_direction()
    example_inspect_specific_node()
    example_adjacency_matrix_access()

    # Visualization example (commented out by default as it requires display)
    # Uncomment the line below to generate a visualization
    # example_visualize_graph()

    print("=" * 60)
    print("All examples completed!")
    print("=" * 60)
