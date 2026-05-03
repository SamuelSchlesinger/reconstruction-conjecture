# Counterexample Search

## Summary of verified bounds

The Reconstruction Conjecture has been computationally verified up to
a small number of vertices. The historical milestones (all bounds to be
confirmed against primary sources):

| Year | Bound | Authors | Notes |
|---|---|---|---|
| 1970s | $n \le 7$ | various | Early hand enumeration |
| 1970s | $n \le 9$ | Imrich (URL unknown — verify) | First large-scale |
| 1997 | $n \le 11$ | McKay [mckay97][mckay97] | Uses `nauty`; canonical labeling |
| 2022 | $n \le 13$ | McKay [mckay22][mckay22] | "Reconstruction of small graphs and digraphs", *Australasian J. Combinatorics* 83(3), 448–457; extends the 1997 verification |

The canonical reference is McKay 1997 [mckay97][mckay97], *Small Graphs
are Reconstructible*. Subsequent advances have come from better
isomorphism-class enumeration (e.g. `nauty`, `bliss`, `traces`) and
more-parallel deck-matching, not from deeper ideas.

## Why automated search has not produced a counterexample

Three reinforcing reasons:

1. **Exponential growth of the search space.** The number of
   non-isomorphic graphs on $n$ vertices grows roughly as
   $2^{\binom{n}{2}}/n!$. The exact OEIS A000088 values give
   approximately $1.65 \times 10^{11}$ unlabeled graphs on $n = 12$
   vertices and $5.05 \times 10^{13}$ on $n = 13$. Checking each
   graph's deck against every other graph's deck is infeasible without
   strong pre-filtering by invariants.
2. **Kelly-reconstructible invariants prune aggressively.** Candidate
   counterexample pairs must be **cospectral**, **chromatically
   equivalent**, **Tutte-equivalent**, have identical **degree
   sequences**, identical **subgraph-count vectors** up to size
   $n-1$, and match on every known deck-reconstructible parameter.
   The combined constraint is extraordinarily tight; empirically, the
   pool of graph pairs passing all such filters is small, and every
   such pair inspected so far has been distinguished by its actual
   deck.
3. **Theoretical support.** Bollobás 1990 [bollobas90][bollobas90]
   shows that random graphs — which dominate the count at large $n$ —
   are reconstructible from 3 cards. The probabilistic argument leaves
   only measure-0 families as candidates; these are highly structured
   (regular, symmetric, cospectral) and have been explicitly searched.

As a consequence, a computational counterexample seems unlikely to
appear below $n \approx 20$. The absence of a counterexample in this
range is often cited as *positive* evidence for the conjecture.

## Tools and infrastructure

- **`nauty`** (McKay): canonical labeling, orbit enumeration,
  isomorphism testing. The de facto tool for generating
  isomorphism-class-unique graphs up to moderate $n$.
- **`bliss`** and **`traces`**: alternative canonical-labeling tools
  with different engineering trade-offs.
- **`geng`** (part of `nauty`): generates non-isomorphic graphs on
  $n$ vertices, with optional edge-count and minimum-degree filters.

See [`../computational/index.md`](../computational/index.md) for the
full infrastructure discussion.

## Targeted searches

Because brute-force enumeration is infeasible beyond small $n$,
targeted searches focus on families hypothesized to be the "hard" cases:

- **Strongly regular graphs.** A large finite catalog of parameters;
  each parameter set admits a known (small) set of non-isomorphic
  realizers. All such realizers have been pair-wise checked for
  reconstructibility.
- **Schwenk cospectral trees.** Though cospectral, their *decks*
  differ, confirming that Tutte's charpoly result is strictly weaker
  than full reconstruction and providing a test-bed for hybrid
  spectral-combinatorial strategies.
- **Cubic and 4-regular graphs** of small order. Systematically
  enumerated and checked.
- **Bipartite regular graphs** (including incidence graphs of
  symmetric designs). Checked up to moderate size.

No family has produced a counterexample.

## Failure modes of counterexample search

- **Graphs of order 2.** $K_2$ and $\overline{K_2}$ have the same deck
  (two copies of $K_1$); this is why the conjecture is stated for
  $n \ge 3$. Not a counterexample, but a reminder that the hypothesis
  is tight.
- **Digraphs.** Stockmeyer 1977 [stockmeyer77][stockmeyer77] exhibited
  infinite families of non-reconstructible tournaments, showing that
  the conjecture fails in the directed setting. This means any
  eventual proof of the undirected case must use a genuinely
  undirected feature; purely "symbolic" arguments risk transferring
  to the directed setting and being falsified.
- **Hypergraphs and multigraphs.** Also known to have
  non-reconstructible families.

## Lean formalization angle

Per-$n$ finite verification in Lean is feasible with the following
architecture:

1. **External enumeration.** Run `geng` (or equivalent) to emit the
   complete list of isomorphism-class-unique graphs on $n$ vertices.
2. **Deck-hash certificates.** Compute a canonical hash of each
   graph's deck; group graphs by hash collisions.
3. **Lean audit.** In Lean, for each small $n$, verify that no two
   non-isomorphic graphs share a hash; equivalently, prove a finite
   statement

   $$\forall\, G, H : \mathrm{Graph}_n,\;
   \mathrm{deck}(G) = \mathrm{deck}(H) \Rightarrow G \cong H.$$

   This is a finite conjunction over a concrete finite set and is in
   principle provable by `decide` or `native_decide` — but note the
   project convention forbids `native_decide` on unbounded domains, so
   any such Lean artifact must fix $n$ and produce a per-$n$ theorem.

4. **Limits.** For $n \ge 10$ the size of the finite set of graphs
   makes straight `decide` infeasible. A certified enumeration via
   tagged isomorphism classes (from `nauty` output, audited in Lean)
   is the only practical route. See
   [`../formalization/index.md`](../formalization/index.md) and
   [`../computational/index.md`](../computational/index.md).

[mckay97]: ../sources.md#mckay97
[mckay22]: ../sources.md#mckay22
[bollobas90]: ../sources.md#bollobas90
[stockmeyer77]: ../sources.md#stockmeyer77
