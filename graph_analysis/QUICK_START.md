# Quick Start Guide

## Installation

```bash
cd graph_analysis
pip install -r requirements.txt
```

## Usage

### 1. Get Adjacency Matrix (Interface)

```python
from graph_analysis import GraphGenerator

# Create graph generator
graph_gen = GraphGenerator(
    dataset_path="dataset/original",
    reverse_direction=False  # Toggle: False = A uses B → B→A, True = A→B
)

# Get numpy adjacency matrix
adj_matrix = graph_gen.get_graph()
# adj_matrix[i][j] = 1 means edge from node i to node j
# adj_matrix[i][j] = 0 means no edge

# Get node names
node_names = graph_gen.get_node_names()
```

### 2. Draw Graph

```python
from graph_analysis import plot_graph

# Visualize and save
plot_graph(
    dataset_path="dataset/original",
    reverse_direction=False,
    save_path="my_graph.png"
)
```

Or from command line:
```bash
python draw_graph.py --save output.png
python draw_graph.py --reverse --save reversed.png
```

### 3. Run Examples

```bash
python example_usage.py
python test_visualization.py
```

## Key Features

✅ **Adjacency matrix** stored as numpy array
✅ **Toggle direction** with `reverse_direction` parameter
✅ **Exact name matching** for dependency detection
✅ **Only theorems** create edges (axioms/definitions don't)
✅ **Clean interface** via `get_graph()` method
✅ **Hierarchical layout** with dependencies on the left
✅ **Color-coded nodes** by category
✅ **Labels** using names (headers) or IDs (theorems)
✅ **Prestige centrality** analysis to identify influential theorems

## Graph Statistics

From the current dataset:
- **99 nodes** (31 headers + 68 theorems)
- **258 edges** (dependencies)
- **Direction**: Configurable (default: dependency → user)

## Files Created

```
graph_analysis/
├── __init__.py              # Package initialization
├── generate_graph.py        # Graph generation logic
├── draw_graph.py            # Visualization
├── analyze_graph.py         # Prestige centrality analysis
├── example_usage.py         # Usage examples
├── requirements.txt         # Dependencies
├── README.md                # Full documentation
├── QUICK_START.md          # This file
└── SUMMARY.md              # Implementation summary
```
