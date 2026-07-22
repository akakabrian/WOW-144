#!/usr/bin/env python3
"""Refute the discarded multicyclic path-plus-girth shortcut exactly.

The false auxiliary inequality was

    largest induced tree order >= girth - 1 + floor((largest induced path - 1) / 2)

for every graph of cycle rank at least two.  Balanced theta graphs refute it,
while still satisfying the actual WOW II Conjecture 144 bound because their
center depth is zero.

Reproduce:
    python3 search/refute_path_plus_girth_bound.py \
      > search/refute_path_plus_girth_bound.json
"""

from __future__ import annotations

import collections
import itertools
import json

import networkx as nx


def theta_graph(lengths: tuple[int, int, int]) -> nx.Graph:
    """Three internally disjoint u-v paths with the given edge lengths."""
    graph = nx.Graph()
    u, v, next_vertex = 0, 1, 2
    for length in lengths:
        previous = u
        for _ in range(length - 1):
            current = next_vertex
            next_vertex += 1
            graph.add_edge(previous, current)
            previous = current
        graph.add_edge(previous, v)
    return graph


def graph_girth(graph: nx.Graph) -> int:
    best = 10**9
    for root in graph:
        distance = {root: 0}
        parent = {root: None}
        queue = collections.deque([root])
        while queue:
            vertex = queue.popleft()
            for neighbor in graph[vertex]:
                if neighbor not in distance:
                    distance[neighbor] = distance[vertex] + 1
                    parent[neighbor] = vertex
                    queue.append(neighbor)
                elif parent[vertex] != neighbor:
                    best = min(best, distance[vertex] + distance[neighbor] + 1)
    return best


def center_depth(graph: nx.Graph) -> int:
    eccentricity = nx.eccentricity(graph)
    radius = min(eccentricity.values())
    center = [vertex for vertex, value in eccentricity.items() if value == radius]
    distance = nx.multi_source_dijkstra_path_length(graph, center)
    return max((distance[v] for v in graph if v not in center), default=0)


def induced_tree_and_path_orders(graph: nx.Graph) -> tuple[int, int]:
    vertices = list(graph)
    best_tree = 0
    best_path = 0
    for order in range(len(vertices), 0, -1):
        for subset in itertools.combinations(vertices, order):
            induced = graph.subgraph(subset)
            if not nx.is_connected(induced) or induced.number_of_edges() != order - 1:
                continue
            if best_tree == 0:
                best_tree = order
            if best_path == 0 and max(dict(induced.degree()).values(), default=0) <= 2:
                best_path = order
            if best_tree and best_path:
                return best_tree, best_path
    raise AssertionError("Every nonempty graph has induced trees and paths")


def record(lengths: tuple[int, int, int]) -> dict[str, object]:
    graph = theta_graph(lengths)
    girth = graph_girth(graph)
    tree_order, path_order = induced_tree_and_path_orders(graph)
    depth = center_depth(graph)
    false_bound = girth - 1 + (path_order - 1) // 2
    actual_target = girth - 1 + depth
    return {
        "lengths": lengths,
        "graph6": nx.to_graph6_bytes(graph, header=False).decode().strip(),
        "n": graph.number_of_nodes(),
        "m": graph.number_of_edges(),
        "cycle_rank": graph.number_of_edges() - graph.number_of_nodes() + 1,
        "girth": girth,
        "center_depth": depth,
        "largest_induced_tree": tree_order,
        "largest_induced_path": path_order,
        "discarded_auxiliary_bound": false_bound,
        "discarded_auxiliary_slack": tree_order - false_bound,
        "conjecture144_target": actual_target,
        "conjecture144_slack": tree_order - actual_target,
    }


def main() -> None:
    witnesses = [record((4, 4, 4)), record((6, 6, 6))]
    assert all(item["discarded_auxiliary_slack"] < 0 for item in witnesses)
    assert all(item["conjecture144_slack"] >= 0 for item in witnesses)
    print(json.dumps({
        "method": "exact exhaustive vertex-subset search on explicit theta graphs",
        "networkx_version": nx.__version__,
        "false_statement":
            "t >= g - 1 + floor((p - 1) / 2) for all cycle-rank-at-least-two graphs",
        "actual_conjecture_broken": False,
        "witnesses": witnesses,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
