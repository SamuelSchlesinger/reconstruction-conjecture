#!/usr/bin/env python3
"""
kelly_small.py
==============

Brute-force validation of Kelly's Lemma on all simple graphs with n = 5
vertices.

Claim validated
---------------
For every simple graph G on n = 5 vertices, and for the fixed pattern
F = K_2 (a single edge, so k = |V(F)| = 2),

    (n - k) * s(F, G) == sum over v in V(G) of s(F, G - v)

where s(F, H) is the number of induced copies of F in H, i.e., the
number of k-element subsets S of V(H) with H[S] isomorphic to F.

Specializing to F = K_2: s(F, G) is just the edge count m(G) of G.

We also check, as an extra sanity check, the same identity for
F = P_3 (path on 3 vertices, k = 3), against all graphs on 5 vertices.

Dependencies
------------
  - networkx  (for graph generation, induced-subgraph, isomorphism testing)
  - itertools (standard library)

Run with
--------
  python3 kelly_small.py
"""

import itertools
import networkx as nx


def all_graphs_on_n_vertices(n):
    """Yield one representative of each labelled simple graph on n
    vertices. We iterate over all 2^(n choose 2) edge subsets of K_n;
    this is redundant w.r.t. isomorphism but that's fine for a sanity
    check — every Kelly identity holds labelled, so checking labelled
    is strictly stronger."""
    verts = list(range(n))
    all_edges = list(itertools.combinations(verts, 2))
    for mask in range(1 << len(all_edges)):
        edges = [e for i, e in enumerate(all_edges) if (mask >> i) & 1]
        g = nx.Graph()
        g.add_nodes_from(verts)
        g.add_edges_from(edges)
        yield g


def induced_copies(F, G):
    """Count the number of k-subsets S of V(G) such that G[S] is
    isomorphic to F, where k = |V(F)|."""
    k = F.number_of_nodes()
    count = 0
    for S in itertools.combinations(G.nodes(), k):
        H = G.subgraph(S)
        if nx.is_isomorphic(H, F):
            count += 1
    return count


def check_kelly(G, F):
    """Check that (n - k) * s(F, G) == sum_v s(F, G - v)."""
    n = G.number_of_nodes()
    k = F.number_of_nodes()
    if k >= n:
        return True  # lemma does not apply; vacuously fine
    lhs = (n - k) * induced_copies(F, G)
    rhs = 0
    for v in G.nodes():
        Gv = G.copy()
        Gv.remove_node(v)
        rhs += induced_copies(F, Gv)
    return lhs == rhs, lhs, rhs


def main():
    n = 5

    # F = K_2 (a single edge).
    K2 = nx.Graph()
    K2.add_nodes_from([0, 1])
    K2.add_edge(0, 1)

    # F = P_3 (path on 3 vertices).
    P3 = nx.Graph()
    P3.add_nodes_from([0, 1, 2])
    P3.add_edge(0, 1)
    P3.add_edge(1, 2)

    total = 0
    failures_K2 = 0
    failures_P3 = 0

    for G in all_graphs_on_n_vertices(n):
        total += 1

        ok_K2, lhs_K2, rhs_K2 = check_kelly(G, K2)
        if not ok_K2:
            failures_K2 += 1
            print(f"FAIL (F=K2): edges={list(G.edges())} lhs={lhs_K2} rhs={rhs_K2}")

        ok_P3, lhs_P3, rhs_P3 = check_kelly(G, P3)
        if not ok_P3:
            failures_P3 += 1
            print(f"FAIL (F=P3): edges={list(G.edges())} lhs={lhs_P3} rhs={rhs_P3}")

    print(f"n = {n}")
    print(f"graphs checked (labelled, redundant): {total}")
    print(f"F = K_2  failures: {failures_K2}")
    print(f"F = P_3  failures: {failures_P3}")
    print("Kelly's Lemma holds for every tested (G, F)."
          if failures_K2 == 0 and failures_P3 == 0
          else "!!! Kelly's Lemma FAILED for some (G, F) — investigate. !!!")


if __name__ == "__main__":
    main()
