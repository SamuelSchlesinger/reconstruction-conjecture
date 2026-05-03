# Almost Every Graph Is Reconstructible — Bollobás 1990

Bollobás's probabilistic theorem [bollobas90][bollobas90] is the strongest
"most graphs are fine" result known for reconstruction, and is one of the
key pieces of evidence that the conjecture is true. It is also noteworthy
because it gives a **reconstruction number** bound of just three for almost
every graph: the full deck is overkill for a random graph.

## Statement

Let `G(n, 1/2)` denote the Erdős–Rényi random graph on `n` labeled vertices
with each edge included independently with probability `1/2`.

**Theorem (Bollobás 1990).** For `G = G(n, 1/2)`, with probability
`1 - o(1)` as `n → ∞`, there exist three vertices `v_1, v_2, v_3` such that
the three cards `G - v_1`, `G - v_2`, `G - v_3` together determine `G` up
to isomorphism among all graphs on `n` vertices.

In particular, **almost every graph** on `n` vertices has **reconstruction
number** `rn(G) = 3` (the minimum size of a sub-deck that still determines
`G`). In fact Bollobás shows the stronger statement that any three cards
suffice for almost every graph, which in turn means the full deck of
`n` cards is vastly redundant for the "typical" graph.

## Why three?

- **Lower bound of three.** Two cards never suffice in general, because
  any graph and its "twin" obtained by swapping two vertices of equal
  "card type" share two cards.
- **Upper bound of three.** Bollobás's argument couples concentration of
  degree sequences with a counting of automorphisms: a random graph
  `G(n, 1/2)` is rigid (trivial automorphism group) w.h.p., its degree
  sequence is reconstructible, and then three generic cards pin down the
  neighbourhoods of all but a vanishing fraction of vertices.

## Proof sketch

1. **Rigidity.** A.a.s. `G(n, 1/2)` has no non-trivial automorphism
   (Erdős–Rényi 1963; also in Bollobás's **Random Graphs** book).
2. **Unique degrees.** A.a.s. the degrees of most vertices are distinct
   within a narrow window, so the deck essentially labels its cards by
   which vertex was deleted.
3. **Three-card Kelly-type argument.** For any three vertices, the
   induced subgraphs on the remaining `n - 1` vertices overlap in
   `n - 3` vertices, and a double-counting argument recovers the
   adjacencies of the three deleted vertices with high probability.

The original paper gives a short argument; Müller had earlier shown a
similar flavour of result with a larger (but still constant) number of
cards — see [muller76][muller76], which predates and inspired Bollobás.

## Later refinements

- **Exact reconstruction numbers.** Bollobás's result has been refined
  to show that for `G(n, 1/2)`, the reconstruction number is *exactly*
  three w.h.p.; two cards do not suffice even for a random graph.
- **Sparse random graphs.** For `G(n, p)` with `p` below a threshold,
  reconstruction becomes more delicate because the graph can be
  disconnected with many isolated vertices; see Lauri–Scapellato
  [laurisc16][laurisc16] chapter on probabilistic methods.
- **Random regular graphs.** Open in full but partial results exist.

## Important caveat

"Almost every graph is reconstructible" does **not** settle the
conjecture: the conjecture is a statement about **every** graph, and the
graphs that resist reconstruction (if any) are precisely the
"exceptional" graphs whose measure under `G(n, 1/2)` is zero — highly
symmetric, degree-balanced, or otherwise structured graphs. This is
why so much attention has gone into structural classes like regular
graphs, strongly-regular graphs, and highly symmetric families: those
are exactly where the probabilistic bounds give no information.

## Connection to edge reconstruction

Müller's earlier result [muller77][muller77] that graphs with more than
`(n-1) log_2 n` edges are edge-reconstructible uses a similar spirit
(count automorphisms, count compatible amalgamations) and covers the
dense regime by brute arithmetic rather than probabilistically.

## Lean 4 angle

A fully formalized Bollobás-style proof would require:

- A definition of `G(n, 1/2)` in Mathlib's probability layer (partial
  coverage exists via `Pmf` and `Random`).
- The rigidity-of-random-graphs lemma (nontrivial, but a named theorem).
- Concentration-of-measure / Chernoff bounds (available in Mathlib).

This is *not* a near-term target — it would require formalizing a fair
chunk of the random-graphs literature first. Simpler deterministic
targets (trees, disconnected graphs, regular graphs with extra hypotheses)
are better first steps.

[bollobas90]: ../sources.md#bollobas90
[muller76]: ../sources.md#muller76
[muller77]: ../sources.md#muller77
[laurisc16]: ../sources.md#laurisc16
