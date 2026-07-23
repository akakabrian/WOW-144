#!/usr/bin/env python3
"""Exact/seeded test of the remaining girth-four metric residual.

Candidate tested (evidence only):
If G is connected with girth four, positive center depth q, and
    diameter(G) = q + 1,
then
    largestInducedTreeSize(G) >= diameter(G) + 2.

Why this matters: the checked bounds
    q + 1 <= diameter(G)
and
    diameter(G) + 1 <= largestInducedTreeSize(G)
already prove Conjecture 144 at girth four unless diameter = q + 1.  The
candidate above closes exactly that residual.

Reproduce:
    python3 search/test_girth_four_residual.py \
      > search/test_girth_four_residual.json
"""

from __future__ import annotations

import collections
import itertools
import json
import random

import networkx as nx

SEED = 14404
RANDOM_ORDERS = range(8, 13)
RANDOM_REQUESTED_PER_ORDER = 150
RANDOM_ATTEMPTS_PER_SAMPLE = 500


def graph_girth(graph: nx.Graph) -> int:
    if nx.is_forest(graph):
        return 0
    best = 10**9
    for root in graph:
        distance = {root: 0}
        parent = {root: None}
        queue: collections.deque[int] = collections.deque([root])
        while queue:
            vertex = queue.popleft()
            for neighbor in graph[vertex]:
                if neighbor not in distance:
                    distance[neighbor] = distance[vertex] + 1
                    parent[neighbor] = vertex
                    queue.append(neighbor)
                elif parent[vertex] != neighbor:
                    best = min(
                        best,
                        distance[vertex] + distance[neighbor] + 1,
                    )
    return best


def center_depth(graph: nx.Graph) -> int:
    eccentricity = nx.eccentricity(graph)
    radius = min(eccentricity.values())
    center = {
        vertex for vertex, value in eccentricity.items() if value == radius
    }
    distance = nx.multi_source_dijkstra_path_length(graph, center)
    return max(
        (distance[vertex] for vertex in graph if vertex not in center),
        default=0,
    )


def largest_induced_tree_size(graph: nx.Graph) -> int:
    vertices = list(graph.nodes())
    for size in range(len(vertices), 0, -1):
        for subset in itertools.combinations(vertices, size):
            if nx.is_tree(graph.subgraph(subset)):
                return size
    return 0


def random_connected_girth_four(
    order: int,
    probability: float,
    rng: random.Random,
) -> nx.Graph | None:
    for _ in range(RANDOM_ATTEMPTS_PER_SAMPLE):
        graph = nx.gnp_random_graph(
            order,
            probability,
            seed=rng.randrange(1 << 30),
        )
        if nx.is_connected(graph) and graph_girth(graph) == 4:
            return graph
    return None


def record(graph: nx.Graph) -> dict[str, object]:
    q = center_depth(graph)
    diameter = nx.diameter(graph)
    tree = largest_induced_tree_size(graph)
    return {
        "graph6": nx.to_graph6_bytes(graph, header=False).decode().strip(),
        "n": graph.number_of_nodes(),
        "m": graph.number_of_edges(),
        "q": q,
        "diameter": diameter,
        "tree": tree,
        "required_tree": diameter + 2,
        "passes": tree >= diameter + 2,
    }


def main() -> None:
    atlas_checked = 0
    atlas_residual: list[dict[str, object]] = []
    for graph in nx.graph_atlas_g():
        if (
            graph.number_of_nodes() > 0
            and nx.is_connected(graph)
            and graph_girth(graph) == 4
        ):
            atlas_checked += 1
            q = center_depth(graph)
            diameter = nx.diameter(graph)
            if q > 0 and diameter == q + 1:
                atlas_residual.append(record(graph))

    rng = random.Random(SEED)
    random_checked = 0
    random_residual: list[dict[str, object]] = []
    for order in RANDOM_ORDERS:
        for _ in range(RANDOM_REQUESTED_PER_ORDER):
            graph = random_connected_girth_four(
                order,
                rng.uniform(0.12, 0.30),
                rng,
            )
            if graph is None:
                continue
            random_checked += 1
            q = center_depth(graph)
            diameter = nx.diameter(graph)
            if q > 0 and diameter == q + 1:
                random_residual.append(record(graph))

    payload = {
        "candidate_lemma": (
            "If G is connected with girth 4, positive center depth q, "
            "and diameter q+1, then largest induced tree size is at "
            "least diameter+2."
        ),
        "status": "computational evidence only",
        "networkx_version": nx.__version__,
        "seed": SEED,
        "atlas_girth4_graphs_checked": atlas_checked,
        "atlas_residual_count": len(atlas_residual),
        "atlas_failures": [x for x in atlas_residual if not x["passes"]],
        "atlas_residual": atlas_residual,
        "random_order_range": [min(RANDOM_ORDERS), max(RANDOM_ORDERS)],
        "random_requested_per_order": RANDOM_REQUESTED_PER_ORDER,
        "random_attempts_per_sample": RANDOM_ATTEMPTS_PER_SAMPLE,
        "random_girth4_graphs_checked": random_checked,
        "random_residual_count": len(random_residual),
        "random_failures": [x for x in random_residual if not x["passes"]],
        "random_residual": random_residual,
    }

    assert atlas_checked == 55
    assert len(atlas_residual) == 2
    assert random_checked == 742
    assert len(random_residual) == 29
    assert not payload["atlas_failures"]
    assert not payload["random_failures"]

    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
