# Graph Analysis for NNG Dataset

This module provides tools to analyze and visualize the dependency graph of the Natural Number Game (NNG) dataset.

## Overview

The graph represents dependencies between theorems and definitions in the NNG dataset:
- **Nodes**: Each definition/theorem from `header_definitions.jsonl` and `theorems.jsonl`
- **Edges**: Directed edges representing usage/dependency relationships
- **Direction**: Configurable (default: if A uses B, then B → A; dependency points to user)

## Files

- **`generate_graph.py`**: Core module for building the dependency graph
- **`draw_graph.py`**: Visualization module for plotting the graph
- **`analyze_graph.py`**: Prestige centrality (PageRank) analysis to identify influential theorems
- **`example_usage.py`**: Examples demonstrating how to use the tools

## Installation

Required packages:
```bash
pip install numpy matplotlib networkx
```

## Quick Start

### 1. Generate Graph and Get Adjacency Matrix

```python
from generate_graph import GraphGenerator

# Create graph generator
graph_gen = GraphGenerator(dataset_path="dataset/original", reverse_direction=False)

# Get adjacency matrix (numpy array)
adj_matrix = graph_gen.get_graph()
print(f"Graph shape: {adj_matrix.shape}")

# Get graph information
info = graph_gen.get_graph_info()
print(f"Nodes: {info['num_nodes']}, Edges: {info['num_edges']}")
```

### 2. Visualize the Graph

```python
from draw_graph import plot_graph

# Create and save visualization
plot_graph(
    dataset_path="dataset/original",
    reverse_direction=False,
    save_path="my_graph.png",
    figsize=(20, 12)
)
```

Or use command line:
```bash
python draw_graph.py --save dependency_graph.png
```

## Features

### GraphGenerator Class

**Initialization:**
```python
GraphGenerator(dataset_path="dataset/original", reverse_direction=False)
```
- `dataset_path`: Path to folder containing `header_definitions.jsonl` and `theorems.jsonl`
- `reverse_direction`: Toggle edge direction (False = A uses B → B→A, True = A uses B → A→B)

**Methods:**
- `get_graph()`: Returns N×N numpy adjacency matrix
- `get_nodes()`: Returns list of node dictionaries
- `get_node_names()`: Returns list of node names
- `get_graph_info()`: Returns dictionary with graph statistics

**Adjacency Matrix:**
- Type: `numpy.ndarray` with shape (N, N) where N is number of nodes
- Values: `1` indicates an edge exists, `0` indicates no edge
- `adj_matrix[i][j] = 1` means there's an edge from node i to node j

### Edge Detection Rules

1. **Only theorems create dependencies** (axioms and definitions have no outgoing edges)
2. **Exact name matching** in code/proof text
3. For header nodes: analyze the `code` field
4. For theorem nodes: analyze the `proof` field
5. Filters out Lean keywords to avoid false positives

### Visualization Features

**Node Colors:**
- Red: Header theorems
- Teal: Axioms
- Light teal: Definitions/Opaque
- Pink: Inductive types/Constructors
- Yellow: Other header items
- Light green: Theorem file entries

**Layout:**
- Hierarchical layout with dependencies on the left
- Uses topological ordering when graph is acyclic
- Falls back to spring layout if cycles detected

**Labels:**
- Header nodes: labeled with names
- Theorem nodes: labeled with IDs (configurable)

## Usage Examples

### Example 1: Basic Graph Access
```python
from generate_graph import GraphGenerator
import numpy as np

graph_gen = GraphGenerator()
adj_matrix = graph_gen.get_graph()

# Check if there's an edge from node i to node j
i, j = 5, 10
if adj_matrix[i][j] == 1:
    print(f"Edge from node {i} to node {j}")

# Count outgoing edges from a node
num_outgoing = np.sum(adj_matrix[i])
print(f"Node {i} has {num_outgoing} outgoing edges")
```

### Example 2: Reversed Direction
```python
# Reverse edge direction: if A uses B, create edge A → B
graph_gen = GraphGenerator(reverse_direction=True)
adj_matrix = graph_gen.get_graph()
```

### Example 3: Find Most Used Nodes
```python
import numpy as np
from generate_graph import GraphGenerator

graph_gen = GraphGenerator()
adj_matrix = graph_gen.get_graph()
node_names = graph_gen.get_node_names()

# Count incoming edges (how many nodes use each node)
in_degrees = np.sum(adj_matrix, axis=0)

# Get top 5 most used nodes
top_5 = np.argsort(in_degrees)[-5:][::-1]
for idx in top_5:
    print(f"{node_names[idx]}: used by {in_degrees[idx]} nodes")
```

### Example 4: Custom Visualization
```python
from draw_graph import plot_graph

plot_graph(
    dataset_path="dataset/original",
    reverse_direction=False,
    figsize=(24, 16),
    save_path="custom_graph.png",
    show_labels=True,
    label_header_only=False,  # Label all nodes
    node_size=500,
    font_size=8
)
```

### Example 5: Command Line Usage
```bash
# Basic usage
python draw_graph.py

# Save to file
python draw_graph.py --save output.png

# Reverse direction
python draw_graph.py --reverse --save reversed_graph.png

# Custom sizing
python draw_graph.py --figsize 30 20 --node-size 400 --font-size 8

# Show all labels
python draw_graph.py --label-all --save all_labels.png
```

## Run Examples

```bash
# Run all examples
python example_usage.py

# This will show:
# - Basic adjacency matrix access
# - Graph statistics
# - Reversed direction example
# - Specific node inspection
# - Custom analysis examples
```

## Graph Statistics

Example output from a typical run:
```
Total nodes: 99
  - Header definitions: 31
  - Theorems: 68
Total edges: 258
Direction: Default (A uses B)
```

## API Reference

### GraphGenerator

```python
class GraphGenerator:
    def __init__(self, dataset_path: str = "dataset/original",
                 reverse_direction: bool = False)

    def load_dataset(self) -> None
    def build_graph(self) -> np.ndarray
    def get_graph(self) -> np.ndarray
    def get_nodes(self) -> List[Dict]
    def get_node_names(self) -> List[str]
    def get_graph_info(self) -> Dict
```

### plot_graph Function

```python
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
) -> None
```

## Prestige Centrality Analysis

### Overview

The `analyze_graph.py` module implements **Prestige Centrality** (PageRank) to identify the most influential foundational lemmas and theorems. It treats main theorems as sources of prestige and lets that prestige flow backwards through dependency edges.

**Key Concept**: If many important theorems depend on a lemma, that lemma gets high prestige.

### Quick Start

```bash
# Analyze and show top 30 most prestigious theorems
python analyze_graph.py --top 30

# Save full rankings to file
python analyze_graph.py --top 50 --output rankings.txt

# Customize parameters
python analyze_graph.py --damping 0.85 --max-iter 100 --tolerance 1e-6
```

### Python API

```python
from analyze_graph import OptimizedPrestigeCentrality
from generate_graph import GraphGenerator

# Load graph
graph_gen = GraphGenerator(dataset_path="dataset/original")

# Calculate prestige
pc = OptimizedPrestigeCentrality(damping_factor=0.85, max_iterations=100, tolerance=1e-6)
scores = pc.calculate(graph_gen)

# Get rankings
ranked = pc.get_ranked_nodes(graph_gen, top_k=20)

for rank, name, score, statement in ranked:
    print(f"[{rank}] {name}: {score:.6e}")
```

### Algorithm Details

1. **Initialization**: All nodes start with equal prestige (1/N)
2. **Power Iteration**: Prestige flows from theorems to their dependencies
   - If theorem T uses lemma L, T "votes" for L
   - Votes are weighted by T's current prestige divided by number of dependencies
3. **Damping Factor** (0.85): Prevents prestige from getting trapped
4. **Convergence**: Iterates until changes fall below tolerance (1e-6)

### Example Results

Top 5 most prestigious theorems from NNG dataset:
1. **mul_right_eq_one** (5.25x average) - Most foundational multiplication theorem
2. **add_sq** (4.61x average) - Square of sum formula
3. **le_mul_right** (3.43x average) - Multiplication preserves inequality
4. **mul_right_eq_self** (2.64x average) - Multiplicative identity property
5. **mul_left_cancel** (2.15x average) - Cancellation law

## Notes

- Only theorem nodes create dependencies (axioms and definitions are considered "leaf" or "source" nodes)
- The graph may contain cycles depending on the theorem structure
- Large graphs may take time to visualize; adjust `figsize` and `node_size` as needed
- Edge detection uses regex-based identifier extraction from code/proof and statement text
- Prestige centrality converges quickly (typically <20 iterations)

## Troubleshooting

**Graph is too dense to visualize:**
- Increase `figsize`: `--figsize 30 20`
- Reduce `node_size`: `--node-size 200`
- Disable labels for theorems: `--label-header-only` (default)

**FileNotFoundError:**
- Run from project root directory
- Check that `dataset/original/` exists with both JSONL files

**Graph has unexpected edges:**
- Check the identifier extraction in `_extract_identifiers()`
- Some edges may come from function names mentioned in proofs
- Adjust keyword filtering if needed
