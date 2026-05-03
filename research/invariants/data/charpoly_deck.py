#!/usr/bin/env python3
"""
charpoly_deck.py
================

Validation of the characteristic-polynomial derivative identity used in
Tutte's reconstruction of the adjacency characteristic polynomial.

Claim validated
---------------
For every simple graph G on n vertices,

    d/dx [phi(G, x)]  ==  sum over v in V(G) of phi(G - v, x)

as an identity in Z[x], where phi(H, x) = det(xI - A(H)) is the
characteristic polynomial of the adjacency matrix of H.

We verify this for every labelled simple graph on n vertices with
n in {2, 3, 4, 5, 6}. Pass a larger n as argv[1] to extend the range
(runtime scales as 2^(n choose 2), so n = 7 is already expensive).

Dependencies
------------
  - sympy   (symbolic polynomials, determinant)
  - networkx (graph generation + adjacency matrix)

Run with
--------
  python3 charpoly_deck.py
"""

import itertools
import sys
import networkx as nx
import sympy as sp


x = sp.symbols("x")


def charpoly(G):
    """Return the characteristic polynomial phi(G, x) = det(xI - A(G))
    as a sympy polynomial in x (with integer coefficients).

    Uses sympy's Matrix.charpoly (Berkowitz algorithm), which is about
    two orders of magnitude faster than sp.det(x*I - A) for our sizes.
    """
    n = G.number_of_nodes()
    if n == 0:
        return sp.Integer(1)
    # Use a fixed node ordering.
    nodes = sorted(G.nodes())
    A = [[1 if G.has_edge(u, v) else 0 for v in nodes] for u in nodes]
    M = sp.Matrix(A)
    return M.charpoly(x).as_expr()


def all_graphs_on_n(n):
    verts = list(range(n))
    all_edges = list(itertools.combinations(verts, 2))
    for mask in range(1 << len(all_edges)):
        edges = [e for i, e in enumerate(all_edges) if (mask >> i) & 1]
        g = nx.Graph()
        g.add_nodes_from(verts)
        g.add_edges_from(edges)
        yield g


def check_identity(G):
    phi = charpoly(G)
    phi_prime = sp.diff(phi, x)

    rhs = sp.Integer(0)
    for v in list(G.nodes()):
        Gv = G.copy()
        Gv.remove_node(v)
        rhs += charpoly(Gv)
    rhs = sp.expand(rhs)

    return sp.expand(phi_prime - rhs) == 0, phi, phi_prime, rhs


def main():
    max_n = 6
    if len(sys.argv) > 1:
        max_n = int(sys.argv[1])

    grand_failures = 0
    for n in range(2, max_n + 1):
        total = 0
        failures = 0
        for G in all_graphs_on_n(n):
            total += 1
            ok, _, _, _ = check_identity(G)
            if not ok:
                failures += 1
                print(f"FAIL (n={n}): edges={list(G.edges())}")
        grand_failures += failures
        print(f"n = {n}:  checked {total} graphs (labelled),  "
              f"failures = {failures}")

    print("Derivative identity holds on all tested graphs."
          if grand_failures == 0
          else "!!! identity failed somewhere — investigate !!!")


if __name__ == "__main__":
    main()
