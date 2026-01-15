# Prestige Centrality Analysis

## Overview

This document explains the Prestige Centrality (PageRank) implementation for identifying the most influential theorems and lemmas in the NNG dataset.

## Folder Structure

-   `generated_proofs.lean`: the lean file for the experiment. More structured file is in the `MyNNG` subfolder.
-   `graph_analysis/`: contains all analysis code.
    -   `generate_graph.py`: code to generate the theorem dependency graph.
    -   `draw_graph.py`: code to visualize the graph.
    -   `analyze_graph.py`: contains the Prestige Centrality implementations.
    -   `hybrid_centrality.py`: alternative centrality measures. That values lemma and end theorems the same time. The ordinary Prestige Centrality only values either lemmas or end theorems.
    -   `betweenness.py`: alternative centrality measure.Did not perform well in experiments.

## How to use

-   Run the python program and the result will be printed on the console.

## Algorithm: PageRank for Theorem Dependencies

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
