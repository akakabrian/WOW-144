#!/usr/bin/env python3
"""Exact verification of WOW II Conjecture 144 on the NetworkX graph atlas.

Enumerates every connected unlabeled graph on 2 through 7 vertices (995 graphs).
For each graph, computes girth, radius, diameter, center-depth `q`, largest
induced tree order, and largest induced path order by exhaustive vertex-subset
search.  The output is deterministic JSON.

Reproduce:
    python3 search/exhaustive_atlas.py > search/exhaustive_atlas.json
"""

from __future__ import annotations

import collections
import itertools
import json
from typing import Iterable

import networkx as nx


def graph_girth(graph: nx.Graph) -> int:
    if nx.is_forest(graph):
        return 0
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


def center_depth(graph: nx.Graph) -> tuple[int, list[int], int, int]:
    eccentricity = nx.eccentricity(graph)
    radius = min(eccentricity.values())
    diameter = max(eccentricity.values())
    center = sorted(vertex for vertex, value in eccentricity.items() if value == radius)
    distance = nx.multi_source_dijkstra_path_length(graph, center)
    depth = max((distance[vertex] for vertex in graph if vertex not in center), default=0)
    return depth, center, radius, diameter


def largest_induced_tree(graph: nx.Graph) -> tuple[int, list[int]]:
    vertices = list(graph)
    for order in range(len(vertices), 0, -1):
        for subset in itertools.combinations(vertices, order):
            if nx.is_tree(graph.subgraph(subset)):
                return order, list(subset)
    raise AssertionError("Every nonempty graph has a one-vertex induced tree")


def largest_induced_path(graph: nx.Graph) -> tuple[int, list[int]]:
    vertices = list(graph)
    for order in range(len(vertices), 0, -1):
        for subset in itertools.combinations(vertices, order):
            induced = graph.subgraph(subset)
            if (nx.is_connected(induced)
                    and induced.number_of_edges() == order - 1
                    and max((degree for _, degree in induced.degree()), default=0) <= 2):
                return order, list(subset)
    raise AssertionError("Every nonempty graph has a one-vertex induced path")


def main() -> None:
    connected = [
        graph.copy()
        for graph in nx.graph_atlas_g()
        if graph.number_of_nodes() >= 2 and nx.is_connected(graph)
    ]
    records = []
    for graph in connected:
        girth = graph_girth(graph)
        depth, center, radius, diameter = center_depth(graph)
        tree_order, tree_witness = largest_induced_tree(graph)
        path_order, path_witness = largest_induced_path(graph)
        target = girth - 1 + depth
        records.append({
            "graph6": nx.to_graph6_bytes(graph, header=False).decode().strip(),
            "n": graph.number_of_nodes(),
            "m": graph.number_of_edges(),
            "girth": girth,
            "center_depth": depth,
            "center": center,
            "radius": radius,
            "diameter": diameter,
            "cycle_rank": graph.number_of_edges() - graph.number_of_nodes() + 1,
            "biconnected": nx.is_biconnected(graph),
            "largest_induced_tree": tree_order,
            "tree_witness": tree_witness,
            "largest_induced_path": path_order,
            "path_witness": path_witness,
            "target": target,
            "slack": tree_order - target,
        })

    counterexamples = [record for record in records if record["slack"] < 0]
    tight = [record for record in records if record["slack"] == 0]
    center_depth_exceeds_diameter_minus_radius = [
        record for record in records
        if record["center_depth"] > record["diameter"] - record["radius"]
    ]
    payload = {
        "method": "NetworkX graph atlas; exact exhaustive vertex-subset search",
        "networkx_version": nx.__version__,
        "connected_graph_count": len(records),
        "cyclic_graph_count": sum(record["girth"] > 0 for record in records),
        "counterexample_count": len(counterexamples),
        "tight_count": len(tight),
        "minimum_slack": min(record["slack"] for record in records),
        "center_depth_exceeds_diameter_minus_radius_count":
            len(center_depth_exceeds_diameter_minus_radius),
        "counterexamples": counterexamples,
        "center_depth_exceeds_diameter_minus_radius":
            center_depth_exceeds_diameter_minus_radius,
        "tight_instances": tight,
        "records": records,
    }
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
