# Prestige Centrality Analysis

## Overview

This document explains the Prestige Centrality (PageRank) implementation for identifying the most influential theorems and lemmas in the NNG dataset.

## Algorithm: PageRank for Theorem Dependencies

### Intuition

**Question**: Which lemmas are most foundational/influential?

**Answer**: The ones that many important theorems depend on!

### How It Works

1. **Prestige flows backwards** through dependencies:
   - If Theorem T uses Lemma L → L gains prestige from T
   - More users = more prestige
   - More prestigious users = even more prestige

2. **PageRank Formula**:
   ```
   Prestige(L) = (1-d)/N + d × Σ(Prestige(T) / OutDegree(T))
                                 for all T that use L
   ```
   Where:
   - `d = 0.85` (damping factor)
   - `N` = total number of nodes
   - `OutDegree(T)` = number of dependencies T has

3. **Convergence**: Iterate until scores stabilize (typically 10-20 iterations)

### Implementation Details

**Two Versions Provided**:

1. **`PrestigeCentrality`** (loop-based, clear logic)
   ```python
   for each iteration:
       for each theorem T:
           share prestige among dependencies
       check convergence
   ```

2. **`OptimizedPrestigeCentrality`** (matrix-based, faster)
   ```python
   Build transition matrix M
   for each iteration:
       prestige = d * (M^T @ prestige) + teleportation
       check convergence
   ```

**Special Handling**:
- **Axioms** (no outgoing edges): Redistribute their prestige to all nodes
- **Damping factor**: Prevents prestige from accumulating in cycles
- **Normalization**: Scores sum to 1.0

## Results on NNG Dataset

### Top 10 Most Prestigious Theorems

| Rank | Name | Score | Relative | Description |
|------|------|-------|----------|-------------|
| 1 | mul_right_eq_one | 5.30e-02 | 5.25x | Most foundational multiplication theorem |
| 2 | add_sq | 4.65e-02 | 4.61x | Square of sum formula |
| 3 | le_mul_right | 3.46e-02 | 3.43x | Multiplication preserves inequality |
| 4 | mul_right_eq_self | 2.66e-02 | 2.64x | Multiplicative identity property |
| 5 | mul_left_cancel | 2.17e-02 | 2.15x | Cancellation law |
| 6 | le_antisymm | 2.15e-02 | 2.12x | Antisymmetry of ≤ |
| 7 | pow_pow | 2.10e-02 | 2.08x | Power of a power |
| 8 | le_total | 1.76e-02 | 1.74x | Totality of ≤ |
| 9 | pow_two | 1.73e-02 | 1.72x | Square as power |
| 10 | le_two | 1.64e-02 | 1.62x | Characterization of ≤ 2 |

**Note**: Average score = 1/99 ≈ 1.01e-02. Scores above average indicate higher prestige.

### Statistics

- **Total nodes**: 99
- **Total edges**: 382
- **Converged**: Yes (13 iterations)
- **Max score**: 5.30e-02 (mul_right_eq_one)
- **Min score**: 5.35e-03
- **Std dev**: 7.59e-03

### Insights

1. **Multiplication theorems dominate**: 6 of top 10 involve multiplication
2. **Inequality lemmas** are highly foundational (le_antisymm, le_total)
3. **Power theorems** appear frequently in top rankings
4. **Basic axioms** (zero, succ, add_zero) have lower scores because they're leaves

## Usage Examples

### Command Line

```bash
# Show top 30 most prestigious theorems
python analyze_graph.py --top 30

# Save full rankings
python analyze_graph.py --output full_rankings.txt

# Custom parameters
python analyze_graph.py --damping 0.90 --max-iter 200 --tolerance 1e-8
```

### Python API

```python
from graph_analysis.analyze_graph import OptimizedPrestigeCentrality
from graph_analysis.generate_graph import GraphGenerator

# Load graph
graph_gen = GraphGenerator(dataset_path="dataset/original")

# Calculate prestige
pc = OptimizedPrestigeCentrality(
    damping_factor=0.85,
    max_iterations=100,
    tolerance=1e-6
)
scores = pc.calculate(graph_gen)

# Get top 20
ranked = pc.get_ranked_nodes(graph_gen, top_k=20)

for rank, name, score, statement in ranked:
    print(f"[{rank}] {name}: {score:.6e}")
    print(f"    {statement[:80]}...")
```

### Integration with Other Tools

```python
# Combine with visualization
from graph_analysis import GraphGenerator, plot_graph, OptimizedPrestigeCentrality

graph_gen = GraphGenerator()
pc = OptimizedPrestigeCentrality()
scores = pc.calculate(graph_gen)

# Find most prestigious
top_idx = np.argmax(scores)
print(f"Most prestigious: {graph_gen.get_node_names()[top_idx]}")

# Visualize
plot_graph(graph_gen=graph_gen, save_path="graph.png")
```

## Parameters

### Damping Factor (d)

- **Default**: 0.85
- **Range**: 0.0 - 1.0
- **Effect**:
  - Higher (0.9): More prestige flows through edges
  - Lower (0.5): More uniform distribution

### Max Iterations

- **Default**: 100
- **Typical convergence**: 10-20 iterations
- **Increase if**: Graph is very large or complex

### Tolerance

- **Default**: 1e-6
- **Smaller tolerance**: More accurate but slower
- **Larger tolerance**: Faster but less precise

## Interpretation

### What High Prestige Means

A high prestige score indicates:
1. **Many theorems depend on it** (direct usage)
2. **Important theorems depend on it** (indirect prestige)
3. **Central to the theorem structure**

### What Low Prestige Means

A low prestige score indicates:
- Leaf node (axiom, constructor, definition)
- Specialized theorem used rarely
- Recent addition not yet widely used

### Comparing Scores

- **>2x average**: Highly foundational
- **1-2x average**: Important supporting theorem
- **<1x average**: Specialized or leaf node

## Performance

### Complexity

- **Time**: O(iterations × edges)
- **Space**: O(nodes²) for adjacency matrix
- **Typical runtime**: <1 second for 100 nodes

### Optimization

The `OptimizedPrestigeCentrality` class uses:
- Numpy vectorized operations
- Matrix multiplication for prestige propagation
- Pre-computed transition matrix
- **~10x faster** than loop-based version for large graphs

### Scalability

For **100,000+ nodes** (Lean Mathlib scale):
- Use `OptimizedPrestigeCentrality`
- Consider sparse matrix representation
- May need 50-100 iterations
- Expected runtime: 1-5 minutes

## Output Format

### Console Output

```
[Rank] Name
    Score: <scientific notation> (<relative to average>x average)
    <statement or code snippet>
```

### File Output

```
# Prestige Centrality Rankings
# Total nodes: 99
# Converged: True after 13 iterations
#
# Rank | Name | Score | Statement
#==============================================================================

[1] mul_right_eq_one
Score: 5.298826e-02
theorem mul_right_eq_one (x y : MyNat) (h : mul x y = one) : x = one := by

--------------------------------------------------------------------------------
```

## References

- **PageRank Algorithm**: Original Google search ranking algorithm
- **Prestige Centrality**: Network analysis measure of importance
- **Power Iteration**: Numerical method for finding eigenvectors

## See Also

- [README.md](README.md) - Full documentation
- [QUICK_START.md](QUICK_START.md) - Quick reference
- [analyze_graph.py](analyze_graph.py) - Implementation
- [prestige_rankings.txt](prestige_rankings.txt) - Full results
