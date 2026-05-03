# Edge Reconstruction (Harary 1964)

Harary [harary64][harary64] introduced the edge-analogue of the
Reconstruction Conjecture:

**Edge-Reconstruction Conjecture.** Every graph with at least four edges
is determined up to isomorphism by its multiset of edge-deleted
subgraphs `{ [G - e] : e ∈ E(G) }`.

This problem is strictly easier than (vertex-)reconstruction: vertex
reconstruction implies edge reconstruction for `n ≥ 4` modulo small
cases (Greenwell 1971, Harary), but the converse is not known. Large
portions of the edge-reconstruction problem *are* settled.

## Density results

- **Lovász 1972** [lovasz72][lovasz72]. If `|E(G)| > (1/2) · C(n, 2) =
  n(n-1)/4`, then `G` is edge-reconstructible. Short proof via a
  counting identity on the subgraph-count vector.
- **Müller 1977** [muller77][muller77]. If `|E(G)| > n · log_2 n`
  (equivalently, if the complement is not too dense), then `G` is
  edge-reconstructible. This is the strongest general density bound
  known.
- **Nash-Williams 1978** [nashwilliams78][nashwilliams78]. Gave a
  sweeping counting framework (sometimes called "Nash-Williams' lemma")
  that subsumes Lovász's argument and yields further classes.

## Structural results

- **Disconnected graphs with ≥ 4 edges** — edge-reconstructible (Manvel,
  Harary).
- **Graphs with a vertex of degree `n - 1`** — edge-reconstructible
  (straightforward; a dominating vertex touches every edge).
- **Bipartite graphs**. Edge-reconstructible via various counting
  arguments; see [bondy91][bondy91] Section "Edge reconstruction in
  bipartite graphs" (primary attribution should be verified).
- **Graphs with more than `n · log_2 n` edges** (Müller, above) —
  dense regime.

## Nash-Williams' Lemma

Let `G` and `H` be graphs on the same edge set such that for every
`e ∈ E`, `G - e ≅ H - e`. Let `X` be a set of graphs and `s(F, G)` the
count of subgraphs isomorphic to `F`. Then:

```
  Σ_{F ∈ X} α(F) · s(F, G) = Σ_{F ∈ X} α(F) · s(F, H)
```

for any integer combination `α` for which the sum telescopes under the
edge-deletion operation. Choosing `X` and `α` cleverly yields the
Lovász and Müller theorems as special cases. See
[../invariants/index.md](../invariants/index.md) for the statement in
detail.

## What's still open for edge reconstruction

- **Sparse graphs.** Below the `n · log_2 n` threshold, general
  edge reconstruction is open. In particular, sparse random graphs and
  sparse regular graphs are not covered by Müller.
- **General graphs with `m = Θ(n)`.** A "linear-density" edge-
  reconstruction theorem (covering all `m ≥ c n`) is not known.

## Relationship to vertex reconstruction

- **Greenwell 1971.** The truth of the vertex-reconstruction conjecture
  implies the truth of the edge-reconstruction conjecture for `n ≥ 4`.
- The reverse implication is *not* known.
- If vertex reconstruction fails, edge reconstruction might still hold.

## Lean 4 angle

- Nash-Williams' lemma is a clean counting identity and would be a
  natural Mathlib-friendly target (assuming a `SimpleGraph.edgeDeck`
  definition). It packages every specific density theorem as a corollary.
- Lovász's density bound is a ~1-page proof and is accessible; might
  be a good first milestone inside the sibling Lean project.

[harary64]: ../sources.md#harary64
[lovasz72]: ../sources.md#lovasz72
[muller77]: ../sources.md#muller77
[nashwilliams78]: ../sources.md#nashwilliams78
[bondy91]: ../sources.md#bondy91
