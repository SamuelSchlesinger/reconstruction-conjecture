# Digraph and Tournament Reconstruction

## Reconstruction Conjecture — digraph form (refuted)

Define the vertex-deck of a digraph `D = (V, A)` as the multiset
`{D − v : v ∈ V}` of induced subdigraphs (arcs inherit direction).

**Digraph Reconstruction Conjecture** (originally: the natural
analogue of Kelly–Ulam for digraphs). Every digraph on `n ≥ 3`
vertices is determined by its vertex-deck.

### Refutation

**Stockmeyer (1977)** [stockmeyer77][stockmeyer77] constructed
non-reconstructible tournaments:

> **Theorem (Stockmeyer).** For all `s, t` with `0 ≤ s < t`, there
> exist pairs of non-isomorphic tournaments on `2^s + 2^t` vertices
> with the same vertex-deck.

Special cases: orders `3` (= `2⁰+2¹`), `5`, `6`, `9`, `10`, `12`,
`17`, `18`, ...  Concrete counterexamples include certain *doubly
regular* tournaments.

**Note**: the original 1977 proof contains a small flaw identified
later, but the constructions themselves are correct (verified
independently; see the Erratum, ResearchGate link).

Stockmeyer later extended the constructions to non-tournament
digraphs, yielding infinite families of non-reconstructible digraphs
of several structural types.

## Tournament Reconstruction

A **tournament** is an orientation of `K_n`. The deck of a tournament
has a restricted structure (each card is itself a tournament on
`n−1` vertices).

**Tournament Reconstruction Conjecture.** Every tournament on `n ≥ 5`
vertices is determined by its deck. — **False** by Stockmeyer's
theorem above.

Nonetheless, *many* tournament classes are known to be reconstructible:

- **Strongly connected tournaments** (partial results).
- **Non-doubly-regular tournaments** (most tournaments are reconstructible).
- Computational surveys: [mckay22][mckay22] (arXiv:2102.01942)
  enumerates non-reconstructible tournaments of small order; the
  known non-reconstructible tournaments form a finite list up to the
  largest verified `n`, extendable by Stockmeyer's doubling
  construction.

## The New Digraph Reconstruction Conjecture

Stockmeyer's refutation prompted a salvage program.

**New Digraph Reconstruction Conjecture (Ramachandran, ca. 1981)**
[ramachandran81][ramachandran81]. Let `D` and `E` be digraphs on the
same vertex set, and let `f : V(D) → V(E)` be a bijection such that:

1. **Vertex-deck match with pairing.** For every `v ∈ V(D)`,
   `D − v ≅ E − f(v)`.
2. **Degree-pair match.** For every `v ∈ V(D)`,
   `(od_D(v), id_D(v)) = (od_E(f(v)), id_E(f(v)))`, where `od`, `id`
   denote out- and in-degrees.

Then `D ≅ E`.

Equivalently: the deck plus degree-sequence information (as matched
to each card) determines the digraph.

### Why this is a natural salvage

Stockmeyer's counterexamples share deck structure but differ in how
the "degree profile of the deleted vertex" interacts with the rest.
By enforcing a matching on the degree pair `(od, id)` of the deleted
vertex, the New Digraph RC precisely rules out the known
counterexample mechanism while remaining as close as possible to the
original formulation.

### Status

**Open.** No counterexample known; no proof known. The 2022 paper
*A property of most of the known non-reconstructible digraphs*
[tandfrecon22][tandfrecon22] shows that known counterexamples to the
plain digraph RC all share a specific structural property that does
*not* contradict the New Digraph RC, giving some evidence of its
robustness.

### Relation to the undirected RC

**Stronger than RC.** Every graph `G` corresponds to a symmetric
digraph `G*` (each edge becomes two opposing arcs); the New Digraph RC
applied to `G*` yields RC for `G`. So:

> `(New Digraph RC) ⇒ (RC)`.

This gives a natural generalization; a proof of the digraph version
would resolve the graph version.

## Switching reconstruction of digraphs

A *switching* at a vertex `v` reverses every arc incident with `v`.

**Open problem** (Bondy–Mercier 2011 [bondymercier11][bondymercier11],
McKay–Schweitzer [mckayschweitzer18][mckayschweitzer18]): is every
digraph on `n ≥ n₀` vertices switching-reconstructible?

Known:
- Non-switching-reconstructible digraphs of order 8 exist.
- No non-switching-reconstructible digraphs of order `≥ 9` are known;
  existence for any fixed larger order is open.

## Formalization targets

For Lean 4:

1. **Stockmeyer's counterexamples**: a concrete pair of tournaments on
   3 vertices (or 5) with the same deck but non-isomorphic. Excellent
   "refutation" target; small enough to `decide` once the graph API
   is in place.
2. **New Digraph Reconstruction Conjecture** — formalize the *statement*
   and prove the implication to RC.
3. **Degree-pair recovery** — show that the multiset of degree pairs of
   the deleted vertices is recoverable from the deck of an undirected
   graph (Kelly's Lemma). This is an infrastructure lemma reusable
   across variants.

[stockmeyer77]: ../sources.md#stockmeyer77
[ramachandran81]: ../sources.md#ramachandran81
[mckay22]: ../sources.md#mckay22
[bondymercier11]: ../sources.md#bondymercier11
[mckayschweitzer18]: ../sources.md#mckayschweitzer18
[tandfrecon22]: ../sources.md#tandfrecon22
