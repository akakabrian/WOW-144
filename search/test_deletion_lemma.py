#!/usr/bin/env python3
"""Seeded adversarial stress test for the remaining deletion lemma.

Candidate lemma tested:
For every connected graph G with girth at least five and cycle rank at least
two, some vertex v satisfies all three conditions:

1. G - v is connected;
2. girth(G - v) = girth(G);
3. centerDepth(G - v) >= centerDepth(G).

The generator starts from a random small multicyclic kernel, heavily subdivides
its edges to force larger girth, and attaches a random tree.  This is evidence,
not a proof.

Reproduce:
    python3 search/test_deletion_lemma.py > search/test_deletion_lemma.json
"""

from __future__ import annotations

import collections
import json
import random

import networkx as nx

SEED = 144987654
TRIALS = 10_000


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


def center_depth(graph: nx.Graph) -> int:
    eccentricity = nx.eccentricity(graph)
    radius = min(eccentricity.values())
    center = {vertex for vertex, value in eccentricity.items() if value == radius}
    distance = nx.multi_source_dijkstra_path_length(graph, center)
    return max((distance[vertex] for vertex in graph if vertex not in center), default=0)


def subdivide_graph(kernel: nx.Graph, lengths: list[int]) -> nx.Graph:
    graph = nx.Graph()
    next_vertex = max(kernel.nodes(), default=-1) + 1
    for (u, v), length in zip(kernel.edges(), lengths):
        previous = u
        for _ in range(length - 1):
            graph.add_edge(previous, next_vertex)
            previous = next_vertex
            next_vertex += 1
        graph.add_edge(previous, v)
    return graph


def attach_random_tree(graph: nx.Graph, count: int, rng: random.Random) -> nx.Graph:
    result = graph.copy()
    next_vertex = max(result.nodes(), default=-1) + 1
    for _ in range(count):
        root = rng.choice(list(result.nodes()))
        result.add_edge(root, next_vertex)
        next_vertex += 1
    return result


def deletion_witness(graph: nx.Graph, girth: int, depth: int) -> int | None:
    for vertex in list(graph):
        reduced = graph.copy()
        reduced.remove_node(vertex)
        if reduced.number_of_nodes() == 0 or not nx.is_connected(reduced):
            continue
        if graph_girth(reduced) != girth:
            continue
        if center_depth(reduced) >= depth:
            return vertex
    return None


def main() -> None:
    rng = random.Random(SEED)
    bucket_counts: collections.Counter[tuple[int, int]] = collections.Counter()
    witness_types: collections.Counter[tuple[int, bool]] = collections.Counter()
    failures = []
    eligible = 0

    for trial in range(TRIALS):
        kernel_order = rng.randint(4, 10)
        kernel = nx.random_labeled_tree(kernel_order, seed=rng.randrange(1 << 30))
        max_extra = kernel_order * (kernel_order - 1) // 2 - (kernel_order - 1)
        extra = rng.randint(2, min(8, max_extra))
        nonedges = list(nx.non_edges(kernel))
        rng.shuffle(nonedges)
        kernel.add_edges_from(nonedges[:extra])

        lengths = [rng.randint(1, 5) for _ in kernel.edges()]
        graph = subdivide_graph(kernel, lengths)
        graph = attach_random_tree(graph, rng.randint(0, 15), rng)

        if graph.number_of_nodes() > 100 or not nx.is_connected(graph):
            continue
        girth = graph_girth(graph)
        cycle_rank = graph.number_of_edges() - graph.number_of_nodes() + 1
        if girth < 5 or cycle_rank < 2:
            continue

        eligible += 1
        order_bucket = min(graph.number_of_nodes() // 10 * 10, 100)
        rank_bucket = min(cycle_rank, 8)
        bucket_counts[(order_bucket, rank_bucket)] += 1

        depth = center_depth(graph)
        witness = deletion_witness(graph, girth, depth)
        if witness is None:
            failures.append({
                "trial": trial,
                "n": graph.number_of_nodes(),
                "m": graph.number_of_edges(),
                "girth": girth,
                "center_depth": depth,
                "cycle_rank": cycle_rank,
                "graph6": nx.to_graph6_bytes(graph, header=False).decode().strip(),
            })
            break

        center = set(nx.center(graph))
        witness_types[(graph.degree(witness), witness in center)] += 1

    payload = {
        "candidate_lemma": (
            "For connected G with girth >= 5 and cycle rank >= 2, there exists v "
            "such that G-v is connected, girth(G-v)=girth(G), and "
            "centerDepth(G-v)>=centerDepth(G)."
        ),
        "status": "computational evidence only",
        "networkx_version": nx.__version__,
        "seed": SEED,
        "trials": TRIALS,
        "eligible_graphs": eligible,
        "failure_count": len(failures),
        "failures": failures,
        "generator": {
            "kernel_order": [4, 10],
            "extra_kernel_edges": [2, 8],
            "subdivision_length_per_edge": [1, 5],
            "attached_tree_vertices": [0, 15],
            "maximum_order": 100,
            "filters": ["connected", "girth >= 5", "cycle rank >= 2"],
        },
        "bucket_counts": {
            f"n={order_bucket},rank={rank_bucket}": count
            for (order_bucket, rank_bucket), count in sorted(bucket_counts.items())
        },
        "witness_types": {
            f"degree={degree},is_center={str(is_center).lower()}": count
            for (degree, is_center), count in sorted(witness_types.items())
        },
    }

    assert eligible == 8_830
    assert not failures
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
