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

On three edges there are two non-isomorphic graphs with the same
edge-deck: `K_3` and `K_{1,3}` both yield the multiset `{3·P_3}` (three
copies of `P_3`) once we allow isolated vertices, or more classically
`K_3` and the disjoint union of `K_2` with an isolated edge-pair. The
threshold `≥ 4` rules out these small degenerate cases.

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
each graph `F` and graph `G`, write `c(F, G)` for the number of
subgraphs of `G` isomorphic to `F`. Nash-Williams' key identity says
that these counts for `|F| < |G|` are deck-reconstructible (this is
essentially Kelly's Lemma, but extended with multiplicities). The
**weighted deck**:

```
w(G) := Σ_{F ≤ G} α(F) · c(F, G)
```

is deck-reconstructible for any weight function `α`, and by choosing
`α` cleverly one can recover structural invariants (number of edges,
triangles, spanning subgraphs of fixed type). Müller's bound is a
corollary of extracting enough information from `w(G)` when the edge
count is large.

### Classes where ERC is known

- Regular graphs (Nash-Williams, class-based argument).
- Graphs with `δ(G) > \log₂ n` (follows from Müller).
- Planar graphs with at least 4 edges (follows from general vertex
  reconstruction on graphs with treewidth ≤ small; or directly via
  face-counting arguments — see [bondy91][bondy91]).
- Bipartite graphs (partial: via matching polynomial reconstructibility
  plus class determination).
- Unicyclic graphs with isolated vertices removed — recent work
  [arxiv2411_03133][arxiv2411_03133] completes a long-standing gap for
  edge-deleted unicyclic graphs.

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
