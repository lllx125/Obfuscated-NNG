import matplotlib.pyplot as plt
import networkx as nx
import numpy as np
from generate_graph import GraphGenerator
from typing import Optional, Tuple


def create_networkx_graph(adj_matrix: np.ndarray, node_names: list) -> nx.DiGraph:
    """
    Convert adjacency matrix to NetworkX directed graph.

    Args:
        adj_matrix: N x N adjacency matrix
        node_names: List of node names

    Returns:
        NetworkX directed graph
    """
    G = nx.DiGraph()

    # Add nodes with their names
    for idx, name in enumerate(node_names):
        G.add_node(idx, name=name)

    # Add edges based on adjacency matrix
    for i in range(len(adj_matrix)):
        for j in range(len(adj_matrix[i])):
            if adj_matrix[i][j] == 1:
                G.add_edge(i, j)

    return G


def get_hierarchical_layout(G: nx.DiGraph, nodes_info: list) -> dict:
    """
    Create a hierarchical layout where parent nodes (those with no incoming edges)
    are positioned on the left, and dependencies flow to the right.

    Args:
        G: NetworkX directed graph
        nodes_info: List of node information dictionaries

    Returns:
        Dictionary mapping node indices to (x, y) positions
    """
    # Use topological generations for hierarchical layout
    try:
        # Get nodes at each level of the DAG
        generations = list(nx.topological_generations(G))

        pos = {}
        max_nodes_in_level = max(len(gen) for gen in generations) if generations else 1

        for level_idx, generation in enumerate(generations):
            num_nodes = len(generation)
            # Spread nodes vertically
            y_offset = (max_nodes_in_level - num_nodes) / 2

            for i, node in enumerate(generation):
                x = level_idx  # Level determines x position (left to right)
                y = y_offset + i  # Vertical spread
                pos[node] = (x, y)

    except nx.NetworkXError:
        # Graph has cycles, fall back to spring layout
        print("Warning: Graph contains cycles. Using spring layout instead.")
        pos = nx.spring_layout(G, k=2, iterations=50)

    return pos


def plot_graph(
    graph_gen: Optional[GraphGenerator] = None,
    dataset_path: str = "dataset/original",
    reverse_direction: bool = False,
    figsize: Tuple[int, int] = (20, 12),
    save_path: Optional[str] = None,
    show_labels: bool = True,
    label_header_only: bool = True,
    node_size: int = 300,
    font_size: int = 6,
    max_label_length: int = 20
) -> None:
    """
    Plot the directed dependency graph.

    Args:
        graph_gen: GraphGenerator instance (if None, creates a new one)
        dataset_path: Path to dataset folder
        reverse_direction: Whether to reverse edge direction
        figsize: Figure size as (width, height)
        save_path: Path to save the figure (if None, just displays)
        show_labels: Whether to show node labels
        label_header_only: If True, only label header nodes (not theorem nodes)
        node_size: Size of nodes in the plot
        font_size: Font size for labels
        max_label_length: Maximum length for node labels (truncate if longer)
    """
    # Create or use provided graph generator
    if graph_gen is None:
        graph_gen = GraphGenerator(dataset_path=dataset_path, reverse_direction=reverse_direction)

    # Get graph data
    adj_matrix = graph_gen.get_graph()
    nodes_info = graph_gen.get_nodes()
    node_names = graph_gen.get_node_names()

    # Create NetworkX graph
    G = create_networkx_graph(adj_matrix, node_names)

    # Get graph info
    info = graph_gen.get_graph_info()

    # Create figure
    fig, ax = plt.subplots(figsize=figsize)

    # Get hierarchical layout
    pos = get_hierarchical_layout(G, nodes_info)

    # Prepare node colors based on source (header vs theorem)
    node_colors = []
    for node in nodes_info:
        if node['source'] == 'header':
            # Different colors for different categories in header
            category = node.get('category', 'unknown')
            if category == 'theorem':
                node_colors.append('#FF6B6B')  # Red for header theorems
            elif category == 'axiom':
                node_colors.append('#4ECDC4')  # Teal for axioms
            elif category in ['def', 'opaque']:
                node_colors.append('#95E1D3')  # Light teal for definitions
            elif category in ['inductive', 'constructor']:
                node_colors.append('#F38181')  # Pink for inductive types
            else:
                node_colors.append('#FFE66D')  # Yellow for others
        else:  # theorem
            node_colors.append('#A8E6CF')  # Light green for theorem file

    # Draw nodes
    nx.draw_networkx_nodes(
        G, pos,
        node_color=node_colors,
        node_size=node_size,
        alpha=0.9,
        ax=ax
    )

    # Draw edges
    nx.draw_networkx_edges(
        G, pos,
        edge_color='gray',
        arrows=True,
        arrowsize=10,
        arrowstyle='->',
        alpha=0.5,
        width=1,
        ax=ax
    )

    # Draw labels
    if show_labels:
        labels = {}
        for idx, node_info in enumerate(nodes_info):
            # Decide whether to label this node
            if label_header_only and node_info['source'] != 'header':
                # Use ID for theorem nodes if available
                label = str(node_info.get('id', ''))
            else:
                # Use name for header nodes
                name = node_info['name']
                # Truncate long names
                if len(name) > max_label_length:
                    label = name[:max_label_length] + '...'
                else:
                    label = name

            labels[idx] = label

        nx.draw_networkx_labels(
            G, pos,
            labels,
            font_size=font_size,
            font_weight='bold',
            ax=ax
        )

    # Add title with statistics
    direction_text = "Reversed (dep → user)" if reverse_direction else "Default (user → dep)"
    title = f"NNG Dependency Graph\n"
    title += f"Nodes: {info['num_nodes']} (Headers: {info['num_header_nodes']}, Theorems: {info['num_theorem_nodes']}) | "
    title += f"Edges: {info['num_edges']} | Direction: {direction_text}"
    plt.title(title, fontsize=14, pad=20)

    # Add legend
    from matplotlib.patches import Patch
    legend_elements = [
        Patch(facecolor='#FF6B6B', label='Header Theorem'),
        Patch(facecolor='#4ECDC4', label='Axiom'),
        Patch(facecolor='#95E1D3', label='Definition/Opaque'),
        Patch(facecolor='#F38181', label='Inductive/Constructor'),
        Patch(facecolor='#FFE66D', label='Other Header'),
        Patch(facecolor='#A8E6CF', label='Theorem File')
    ]
    ax.legend(handles=legend_elements, loc='upper left', fontsize=10)

    ax.axis('off')
    plt.tight_layout()

    # Save or show
    if save_path:
        plt.savefig(save_path, dpi=300, bbox_inches='tight')
        print(f"Graph saved to {save_path}")
    else:
        plt.show()


def main():
    """Example usage with different configurations"""
    import argparse

    parser = argparse.ArgumentParser(description='Draw NNG dependency graph')
    parser.add_argument('--dataset', type=str, default='dataset/original',
                        help='Path to dataset folder')
    parser.add_argument('--reverse', action='store_true',
                        help='Reverse edge direction')
    parser.add_argument('--save', type=str, default=None,
                        help='Path to save the figure')
    parser.add_argument('--figsize', type=int, nargs=2, default=[20, 12],
                        help='Figure size (width height)')
    parser.add_argument('--no-labels', action='store_true',
                        help='Hide node labels')
    parser.add_argument('--label-all', action='store_true',
                        help='Label all nodes (not just headers)')
    parser.add_argument('--node-size', type=int, default=300,
                        help='Node size')
    parser.add_argument('--font-size', type=int, default=6,
                        help='Font size for labels')

    args = parser.parse_args()

    # Create and plot graph
    plot_graph(
        dataset_path=args.dataset,
        reverse_direction=args.reverse,
        figsize=tuple(args.figsize),
        save_path=args.save,
        show_labels=not args.no_labels,
        label_header_only=not args.label_all,
        node_size=args.node_size,
        font_size=args.font_size
    )


if __name__ == "__main__":
    main()
