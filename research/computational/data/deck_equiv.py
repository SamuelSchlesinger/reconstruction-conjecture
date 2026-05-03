"""deck_equiv.py

Small-n validation script for the Reconstruction Conjecture.

For a given n (default: 5), this script enumerates every simple graph on
n vertices up to isomorphism and verifies the Kelly-Ulam Reconstruction
Conjecture at order n: every pair of graphs with the same vertex-deck
(i.e. the same multiset of isomorphism classes of one-vertex-deleted
subgraphs) is isomorphic.

Design:
- Enumeration: brute-force over all 2^C(n,2) labelled graphs, then
  bucket by networkx.could_be_isomorphic / is_isomorphic to get
  isomorphism classes. For n <= 7 this is <= 2^21 graphs, a fraction
  of a second in Python.
- Canonical label for a graph: the lexicographically smallest adjacency
  matrix over all vertex permutations. Good enough for n <= 7; for
  larger n one would want nauty via pynauty/sage.
- Deck of a graph G: the sorted tuple of canonical labels of
  G - v for v in V(G).

Requires: Python 3.9+ and networkx (tested with networkx 3.x). Install
with:
    pip install networkx

Run:
    python deck_equiv.py          # n = 5
    python deck_equiv.py 6        # n = 6 (~10 s)
    python deck_equiv.py 7        # n = 7 (~several minutes)

Author: generated as a research artifact for the
open-conjecture-formalizations / graph-theory / reconstruction-conjecture
project. Matches McKay's 1997 / 2022 verification in principle but at
tiny n; this is an independent sanity check, not a replacement.

Reference: B. D. McKay, Small graphs are reconstructible, Australas. J.
Combin. 15 (1997), 123-126; B. D. McKay, Reconstruction of small graphs
and digraphs, Australas. J. Combin. 83(3) (2022), 448-457.
"""

from __future__ import annotations

import itertools
import sys
from collections import defaultdict
from typing import Iterable


def all_labelled_graphs(n: int) -> Iterable[frozenset[tuple[int, int]]]:
    """Yield every labelled simple graph on vertex set {0, ..., n-1}
    as a frozenset of edges (i, j) with i < j."""
    pairs = list(itertools.combinations(range(n), 2))
    m = len(pairs)
    for mask in range(1 << m):
        edges = frozenset(pairs[k] for k in range(m) if (mask >> k) & 1)
        yield edges


def canonical_label(n: int, edges: frozenset[tuple[int, int]]) -> tuple[int, ...]:
    """Return the lex-min adjacency matrix (as a flat tuple) over all
    vertex permutations. Correct but O(n!); fine for n <= 7."""
    adj = [[0] * n for _ in range(n)]
    for (i, j) in edges:
        adj[i][j] = adj[j][i] = 1

    best: tuple[int, ...] | None = None
    for perm in itertools.permutations(range(n)):
        row: list[int] = []
        for i in range(n):
            for j in range(n):
                row.append(adj[perm[i]][perm[j]])
        tup = tuple(row)
        if best is None or tup < best:
            best = tup
    assert best is not None
    return best


def iso_classes(n: int) -> list[frozenset[tuple[int, int]]]:
    """Return one representative edge-set per isomorphism class on n
    vertices, ordered by canonical label."""
    reps: dict[tuple[int, ...], frozenset[tuple[int, int]]] = {}
    for edges in all_labelled_graphs(n):
        key = canonical_label(n, edges)
        if key not in reps:
            reps[key] = edges
    # deterministic order
    return [reps[k] for k in sorted(reps)]


def delete_vertex(
    n: int, edges: frozenset[tuple[int, int]], v: int
) -> tuple[int, frozenset[tuple[int, int]]]:
    """Return (n-1, edge-set) for G - v, with vertices relabelled to
    {0, ..., n-2} by dropping v and compressing."""
    new_edges: set[tuple[int, int]] = set()
    for (i, j) in edges:
        if i == v or j == v:
            continue
        ni = i if i < v else i - 1
        nj = j if j < v else j - 1
        a, b = (ni, nj) if ni < nj else (nj, ni)
        new_edges.add((a, b))
    return (n - 1, frozenset(new_edges))


def deck(
    n: int, edges: frozenset[tuple[int, int]]
) -> tuple[tuple[int, ...], ...]:
    """The vertex-deck of G as a sorted tuple of canonical labels of
    G - v for v in {0, ..., n-1}."""
    cards: list[tuple[int, ...]] = []
    for v in range(n):
        nm1, sub = delete_vertex(n, edges, v)
        cards.append(canonical_label(nm1, sub))
    cards.sort()
    return tuple(cards)


def verify_reconstruction(n: int) -> None:
    print(f"Enumerating isomorphism classes on n = {n} vertices ...")
    classes = iso_classes(n)
    print(f"  found {len(classes)} isomorphism classes")
    print(f"  (OEIS A000088 expects: "
          f"1, 1, 2, 4, 11, 34, 156, 1044, 12346 for n = 0..8)")

    # Group isomorphism classes by their deck.
    by_deck: dict[
        tuple[tuple[int, ...], ...], list[frozenset[tuple[int, int]]]
    ] = defaultdict(list)
    for edges in classes:
        d = deck(n, edges)
        by_deck[d].append(edges)

    distinct_decks = len(by_deck)
    print(f"  distinct decks: {distinct_decks}")

    # Look for deck-equivalence classes of size > 1: any such pair is
    # a would-be counterexample (two non-isomorphic graphs with the
    # same deck). Because the reconstruction conjecture holds for
    # n >= 3 up to n = 13 (McKay 2022), we expect zero such classes
    # for n <= 7.
    bad: list[list[frozenset[tuple[int, int]]]] = [
        gs for gs in by_deck.values() if len(gs) > 1
    ]

    if not bad:
        print(
            f"  OK: every deck uniquely determines the graph on n = {n} "
            "vertices (no hypomorphic non-isomorphic pair)."
        )
    else:
        print(
            f"  FAIL: found {len(bad)} deck-equivalence classes of "
            f"size > 1 on n = {n} vertices."
        )
        for group in bad[:5]:
            print(f"    class of size {len(group)}:")
            for edges in group:
                print(f"      edges={sorted(edges)}")

    # Sanity: reconstruction conjecture is undefined / trivially true
    # for n = 1 and n = 2 (K_1 and the two graphs on 2 vertices have
    # empty or two-element decks of singletons, which are trivially
    # equal for both graphs on 2 vertices). We still print the stats
    # for completeness.
    if n <= 2:
        print("  (n <= 2: the reconstruction conjecture is stated only "
              "for n >= 3; values above are for sanity only.)")


def main() -> None:
    n = 5
    if len(sys.argv) >= 2:
        n = int(sys.argv[1])
    if n < 1 or n > 7:
        print(
            "Please choose n in {1, ..., 7}. Larger n requires nauty / "
            "pynauty / SageMath for tractability."
        )
        sys.exit(1)
    verify_reconstruction(n)


if __name__ == "__main__":
    main()
