#!/usr/bin/env python3
"""Test the constructive girth-four residual lemma.

Candidate tested (computational evidence only):
If G is connected, has girth four, positive center depth q, and
`diameter(G) = q + 1`, then some diametral geodesic P has an outside vertex
with exactly one neighbor on P.

Adding that vertex to P gives an induced tree on `diameter + 2 = q + 3`
vertices, exactly the Conjecture 144 target at girth four.

The script also tests the contrapositive structural clue:
if no diametral geodesic has such a one-neighbor extension, then
`centerDepth(G) <= diameter(G) - 2`.

Reproduce:
    python3 search/test_girth_four_diametral_extension.py \
      > search/test_girth_four_diametral_extension.json
"""

from __future__ import annotations

import collections
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


def has_one_neighbor_diametral_extension(
    graph: nx.Graph,
) -> tuple[bool, list[int] | None, int | None]:
    diameter = nx.diameter(graph)
    for left in graph:
        for right in graph:
            if left >= right:
                continue
            if nx.shortest_path_length(graph, left, right) != diameter:
                continue
            for path in nx.all_shortest_paths(graph, left, right):
                path_set = set(path)
                for vertex in set(graph) - path_set:
                    path_neighbor_count = sum(
                        neighbor in path_set for neighbor in graph[vertex]
                    )
                    if path_neighbor_count == 1:
                        return True, list(path), vertex
    return False, None, None


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


def inspect(graph: nx.Graph) -> dict[str, object]:
    q = center_depth(graph)
    diameter = nx.diameter(graph)
    extendable, path, vertex = has_one_neighbor_diametral_extension(graph)
    return {
        "graph6": nx.to_graph6_bytes(graph, header=False).decode().strip(),
        "n": graph.number_of_nodes(),
        "m": graph.number_of_edges(),
        "q": q,
        "diameter": diameter,
        "extendable": extendable,
        "witness_path": path,
        "witness_vertex": vertex,
        "residual": q > 0 and diameter == q + 1,
        "contrapositive_passes": extendable or q <= diameter - 2,
    }


def main() -> None:
    atlas_records: list[dict[str, object]] = []
    for graph in nx.graph_atlas_g():
        if (
            graph.number_of_nodes() > 0
            and nx.is_connected(graph)
            and graph_girth(graph) == 4
        ):
            atlas_records.append(inspect(graph))

    rng = random.Random(SEED)
    random_records: list[dict[str, object]] = []
    for order in RANDOM_ORDERS:
        for _ in range(RANDOM_REQUESTED_PER_ORDER):
            graph = random_connected_girth_four(
                order,
                rng.uniform(0.12, 0.30),
                rng,
            )
            if graph is not None:
                random_records.append(inspect(graph))

    atlas_residual = [record for record in atlas_records if record["residual"]]
    random_residual = [record for record in random_records if record["residual"]]
    atlas_nonextendable = [
        record for record in atlas_records if not record["extendable"]
    ]
    random_nonextendable = [
        record for record in random_records if not record["extendable"]
    ]

    payload = {
        "candidate_lemma": (
            "At girth four, if q>0 and diameter=q+1, some diametral "
            "geodesic has an outside vertex with exactly one path neighbor."
        ),
        "contrapositive_candidate": (
            "If no diametral geodesic has a one-neighbor outside extension, "
            "then center depth is at most diameter-2."
        ),
        "status": "computational evidence only",
        "networkx_version": nx.__version__,
        "seed": SEED,
        "atlas_girth4_graphs_checked": len(atlas_records),
        "atlas_residual_count": len(atlas_residual),
        "atlas_residual_failures": [
            record for record in atlas_residual if not record["extendable"]
        ],
        "atlas_nonextendable_count": len(atlas_nonextendable),
        "atlas_contrapositive_failures": [
            record
            for record in atlas_nonextendable
            if not record["contrapositive_passes"]
        ],
        "random_order_range": [min(RANDOM_ORDERS), max(RANDOM_ORDERS)],
        "random_requested_per_order": RANDOM_REQUESTED_PER_ORDER,
        "random_attempts_per_sample": RANDOM_ATTEMPTS_PER_SAMPLE,
        "random_girth4_graphs_checked": len(random_records),
        "random_residual_count": len(random_residual),
        "random_residual_failures": [
            record for record in random_residual if not record["extendable"]
        ],
        "random_nonextendable_count": len(random_nonextendable),
        "random_contrapositive_failures": [
            record
            for record in random_nonextendable
            if not record["contrapositive_passes"]
        ],
        "atlas_residual": atlas_residual,
        "random_residual": random_residual,
    }

    assert len(atlas_records) == 55
    assert len(atlas_residual) == 2
    assert len(atlas_nonextendable) == 14
    assert len(random_records) == 742
    assert len(random_residual) == 29
    assert len(random_nonextendable) == 16
    assert not payload["atlas_residual_failures"]
    assert not payload["random_residual_failures"]
    assert not payload["atlas_contrapositive_failures"]
    assert not payload["random_contrapositive_failures"]

    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
