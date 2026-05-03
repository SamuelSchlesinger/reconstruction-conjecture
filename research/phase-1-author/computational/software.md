# Software used for reconstruction verification

The workhorse for every published verification of the reconstruction
conjecture is Brendan McKay's **`nauty`** package, with the
`gtools` suite (including `geng`, `directg`, `showg`, `genbg`) used for
enumeration [nauty-manual][nauty-manual][mckayp14][mckayp14].
The following ingredients matter for deck-equivalence testing.

## Canonical labelling (nauty)

`nauty` computes, for any graph `G`, a **canonical label** `canon(G)`
such that `canon(G) = canon(H)` iff `G ≅ H`. The implementation is the
celebrated individualization–refinement algorithm; see
[mckayp14][mckayp14] for the current algorithmic
description.

For reconstruction verification, `nauty` is used two ways:

1. As a **string key** for isomorphism classes: two graphs are tested
   for isomorphism by comparing their canonical labels as bit-strings
   in the compact `graph6` format.
2. As a **canonical-deletion oracle**: from `G`, pick the unique
   vertex `v*` that is the *lexicographically least* image under
   `Aut(G)` (or any canonical choice); then `G - v*` is a canonical
   card, and the deck `D(G)` is
   `{ canon(G - v) : v ∈ V(G) }` as a sorted multiset of
   canonical labels.

## Generating graphs (geng)

`geng n [e_min:e_max]` emits every non-isomorphic simple graph on
`n` vertices with edge count in `[e_min, e_max]`, printing one
`graph6` string per line. Typical throughput is in the range
`10^5`–`10^7` graphs per CPU-second depending on `n` and the density
window. `geng` supports split-by-residue flags so the output can be
parallelized across cores and nodes without duplication.

Related tools:

- `genbg` — bipartite graphs (by bipartition sizes `n1, n2`).
- `directg` — convert undirected `graph6` into all non-isomorphic
  orientations (digraph6).
- `gentourng` / `gentreeg` / `genrang` — tournaments, trees, random
  graphs.
- `showg` — pretty-print `graph6`/`sparse6` to adjacency lists.
- `labelg` — canonical relabelling in place.

## Deck-equivalence test

In pseudocode, using `nauty` utilities:

```
for G in geng(n):
    deck = []
    for v in V(G):
        Gv = delete_vertex(G, v)
        deck.append(canon_g6(Gv))        # nauty canonical label
    deck.sort()
    key = hash(tuple(deck))
    if key in table:
        for G_prev in table[key]:
            if full_deck_match(G_prev, deck):
                if canon_g6(G) != canon_g6(G_prev):
                    report_counterexample(G, G_prev)
        table[key].append(G)
    else:
        table[key] = [G]
```

Memory is the bottleneck at large `n`: the table of all deck-hashes
for `n = 13` has about `5 · 10^{13}` entries, far beyond RAM, so the
actual verification is organized along a **generation tree** where
each deck-class is examined while building a canonical extension to
one more vertex, and the table can be streamed rather than held in
full. This is the canonical-deletion trick
[mckay97][mckay97].

## Invariants used as pre-filters

Fast invariants that are reconstructible from the deck
([../invariants/index.md](../invariants/index.md)):

- Degree sequence
- Number of edges
- Number of triangles, `C_4`, `K_{1,3}`, ..., each small subgraph
- Number of connected components; sizes of components
- Characteristic polynomial of the adjacency matrix (and hence
  eigenvalues with multiplicities)

Bucketing by the first three eliminates almost all candidate pairs
instantly; the remainder are checked by full deck comparison.

## `graph6` format (briefly)

A `graph6` string encodes a simple graph on `n` vertices as
`n` in 1–4 bytes followed by the upper-triangle bitmap
packed 6 bits per printable ASCII character. Every `nauty` tool reads
and emits this. The format is documented at
[https://users.cecs.anu.edu.au/~bdm/data/formats.txt](https://users.cecs.anu.edu.au/~bdm/data/formats.txt).

## Tools beyond nauty

Occasional verification is done in:

- **SageMath** ([https://www.sagemath.org](https://www.sagemath.org))
  wraps `nauty` and `bliss` as Python-accessible graph-isomorphism
  backends, and is convenient for prototyping
  the deck-equivalence pipeline at small `n` (see
  [`data/deck_equiv.py`](data/deck_equiv.py)).
- **bliss** (Junttila and Kaski,
  [https://users.aalto.fi/~tjunttil/bliss/](https://users.aalto.fi/~tjunttil/bliss/))
  — an alternative canonical-labelling library, sometimes faster than
  `nauty` on sparse graphs.
- **Traces** (Piperno), bundled with `nauty`, uses a different
  refinement strategy and often outperforms `nauty` on structured
  graphs (strongly regular graphs, Cayley graphs).

## References

- [mckay97][mckay97] — the `n ≤ 11` run.
- [mckay22][mckay22] — the `n ≤ 13` run; describes the
  algorithmic refinements.
- [mckayp14][mckayp14] — the practical-graph-isomorphism
  algorithm inside `nauty` v2.
- [nauty-manual][nauty-manual] — user's guide for
  `nauty` and `Traces` with full `gtools` documentation.

[mckay97]: ../sources.md#mckay97
[mckay22]: ../sources.md#mckay22
[mckayp14]: ../sources.md#mckayp14
[nauty-manual]: ../sources.md#nauty-manual
