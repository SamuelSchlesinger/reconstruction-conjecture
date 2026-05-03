# Edge Reconstruction Conjecture

## Statement

Let `G = (V, E)` be a simple graph with `|E(G)| ≥ 4`. For each edge
`e ∈ E(G)`, let `G − e` denote the edge-deleted subgraph; the
**edge-deck** of `G` is the multiset `D_E(G) := {G − e : e ∈ E(G)}` of
isomorphism classes.

**Edge Reconstruction Conjecture (Harary, 1964)** [harary64][harary64].
Every graph `G` with `|E(G)| ≥ 4` is determined up to isomorphism by
`D_E(G)`.

## Why `≥ 4` edges

Small-edge examples rule out reconstruction:

- **Two edges (`m = 2`).** The two non-isomorphic 2-edge graphs
  `K_2 ∪ K_2` (two disjoint edges) and `P_3` (a 3-vertex path, two
  edges sharing a vertex) have identical edge-decks: deleting either
  edge from either graph leaves a single `K_2` (plus an isolated
  vertex or two, depending on the isolated-vertex convention). So at
  `m = 2` edge reconstruction already fails.
- **Three edges (`m = 3`).** The triangle `K_3` and the star
  `K_{1,3}` are non-isomorphic, yet as *edge-decks* both produce the
  multiset `{P_2, P_2, P_2}` (three cards, each a 2-edge path on three
  vertices, ignoring isolated vertices). So edge reconstruction also
  fails at `m = 3`.

Harary's threshold `m ≥ 4` rules out exactly these small degenerate
cases; at `m = 4` edge reconstruction is verified by direct
enumeration.

## Relation to the (vertex) Reconstruction Conjecture

- **Greenwell (1971)** [greenwell71][greenwell71]: if `G` has no
  isolated vertices and is vertex-reconstructible, then `G` is
  edge-reconstructible. Equivalently, the edge-deck can be
  recovered from the vertex-deck for graphs with `δ(G) ≥ 1`.
- **Converse (ERC ⇒ RC)**: **open**. Several partial reductions exist,
  e.g. for triangle-free graphs and for graphs of sufficiently high
  minimum degree, but the general implication is unresolved.

## Major partial results

### Müller's bound (1977)

[muller77][muller77] proved that ERC holds whenever
`|E(G)| ≥ n · log₂ n`, where `n = |V(G)|`.

> **Theorem (Müller).** If `m ≥ n log₂ n` then every graph on `n`
> vertices and `m` edges is edge-reconstructible.

The proof uses a probabilistic/counting argument (Lovász-style
weighted deck identities) showing that the number of labelled
reconstructions from the edge-deck grows faster than the number of
distinct graphs could allow unless reconstruction is unique.

### Lovász's bound (1972)

[lovasz72][lovasz72] gave the first substantive bound, showing ERC is
true whenever `|E(G)| > \binom{n}{2}/2`, i.e. for more than half of the
complete graph's edges. This uses a direct inclusion–exclusion
(permanent of an incidence-type matrix) and is strictly weaker than
Müller's result. It is remarkable in that the proof is extremely short
and entirely algebraic.

### Nash-Williams' weighted deck lemma

[nashwilliams78][nashwilliams78] refined the counting machinery. For
graphs `F` and `G`, write `s(F, G)` for the number of *subgraphs* of
`G` isomorphic to `F` (equivalently, the number of injective
homomorphisms `F → G` divided by `|Aut(F)|`). Similarly write
`e(F, G)` for the number of *embeddings* (injective homs, counted
without dividing).

> **Nash-Williams' Lemma (precise form).** Let `G` and `H` be simple
> graphs with `|E(G)| = |E(H)| = m`. If the edge-decks `D_E(G)` and
> `D_E(H)` are equal as multisets of isomorphism classes, then for
> every graph `F` with `|E(F)| < m`,
>
> ```
> s(F, G) = s(F, H)   (equivalently e(F, G) = e(F, H)).
> ```

The proof is a Möbius-inversion / double-counting identity over the
poset of edge-subsets: counts of embeddings into `G` with strictly
fewer than `m` edges are determined by the edge-deck, because each
such `F → G` embedding misses at least one edge of `G` and therefore
factors through some card `G − e`.

The **weighted form** (Lovász 1972 [lovasz72][lovasz72], Nash-Williams
1978) assigns a weight `α(F)` to each iso class `F` and considers

```
w_α(G) := Σ_{F : |E(F)| < m} α(F) · s(F, G).
```

Then `w_α(G) = w_α(H)` whenever `G` and `H` have equal edge-decks, for
every `α`. Choosing `α` so that `w_α` concentrates on a single target
graph (Möbius inversion on the lattice of subgraphs of `K_n`) lets one
solve for `s(G, G)` itself, yielding Lovász's bound:

> **Lovász (1972).** `m > (1/2) · C(n, 2)` ⇒ ERC.

Müller 1977 refines the same scheme with a sharper Möbius estimate to
reach the `m ≥ n log₂ n` bound.

### Classes where ERC is known

- Regular graphs (Nash-Williams, class-based argument).
- Graphs with `δ(G) > \log₂ n` (follows from Müller).
- Planar graphs with at least 4 edges (follows from general vertex
  reconstruction on graphs with treewidth ≤ small; or directly via
  face-counting arguments — see [bondy91][bondy91]).
- Bipartite graphs (partial: via matching polynomial reconstructibility
  plus class determination).
- Unicyclic graphs with isolated vertices removed — recent work by
  Pizzimenti and Rakhimov (2024) [arxiv2411_03133][arxiv2411_03133]
  completes a long-standing gap for edge-deleted unicyclic graphs.

## Infinite-graph case

For **infinite graphs**, ERC is *false*: counterexamples were
constructed by Fisher, Graham and Harary (ScienceDirect article,
*Counterexamples to the edge reconstruction conjecture for infinite
graphs*, Discrete Math. 1977) — URL:
<https://www.sciencedirect.com/science/article/pii/0012365X7790111X>
(verify). This highlights a structural difference: finiteness is
essential for the conjecture to have a chance.

## Formalization targets

For Lean 4:

1. **Define the edge-deck** and show the `≥ 4` threshold is necessary
   by exhibiting the small counterexamples.
2. **Formalize Greenwell's theorem** (RC + `δ ≥ 1` ⇒ ERC). Short,
   self-contained; excellent entry project.
3. **Formalize Lovász's bound** `m > \binom{n}{2}/2 ⇒ ERC`. Uses
   linear algebra / permanent arguments that translate naturally to
   `Matrix` over `ℚ`.
4. **Formalize Müller's bound** (`m ≥ n log₂ n ⇒ ERC`). Harder,
   requires counting lemmas and probabilistic combinatorics infrastructure.
   A realistic long-term target.
5. **Formalize Nash-Williams' weighted deck framework** as a reusable
   API; Kelly's Lemma and weighted identities have uniform interface.

[harary64]: ../sources.md#harary64
[lovasz72]: ../sources.md#lovasz72
[muller77]: ../sources.md#muller77
[nashwilliams78]: ../sources.md#nashwilliams78
[greenwell71]: ../sources.md#greenwell71
[bondy91]: ../sources.md#bondy91
[arxiv2411_03133]: ../sources.md#arxiv2411_03133
