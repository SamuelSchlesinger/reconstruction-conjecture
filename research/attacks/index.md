# Attack Strategies for the Reconstruction Conjecture

## Overview

The Kelly–Ulam Reconstruction Conjecture asserts that every finite simple
graph on at least three vertices is determined (up to isomorphism) by its
**deck** of vertex-deleted subgraphs. Attacks fall into several broad
families — **counting arguments** in the Kelly tradition, **spectral /
algebraic polynomial reconstructibility**, **probabilistic and random-graph**
methods, **structural reductions** to restricted graph classes, and
**computational counterexample search**. No single approach has resolved the
conjecture; the present document surveys each, ranks them by near-term
tractability per graph class, tables what partial results would imply the
full conjecture, and flags approaches whose proof structure is amenable to
Lean 4 formalization.

## Strategy ladder (by graph class)

The table ranks the most promising *in-principle* approach per class; for
each cell, **P** = has a published proof of reconstructibility, **C** =
conjecturally reconstructible by the listed method, **O** = open or only
sporadic results. Cross-check with
[`../state-of-the-art/index.md`](../state-of-the-art/index.md).

| Class | Best current handle | Status | Tractability of attack |
|-------|--------------------|--------|------------------------|
| Trees | Kelly counting; induction on leaves | P (Kelly 1957) | High |
| Disconnected graphs | Kelly's connectivity recognition | P (Kelly 1957) | High |
| Regular graphs | Deck recognizes regularity; Kelly counting | P (several) | High |
| Unit-interval / interval graphs | Structural / Kelly | P | Medium |
| Maximal planar | Edge-count + Kelly | P (Lauri) | Medium |
| Outerplanar | Structural decomposition | P (Giles 1976) | Medium |
| Separable graphs (with cut vertex) | Bondy decomposition | P (Bondy 1969) | Medium |
| Graphs with $m > \binom{n}{2}/2$ edges | Lovász edge-reconstruction | P (Lovász 1972 [lovasz72][lovasz72]) | — |
| Graphs with $m > n \cdot \log_2 n$ edges | Müller edge-reconstruction (asymptotically stronger) | P (Müller 1977 [muller77][muller77]) | — |
| Almost every graph | Random 3-card argument | P (Bollobás 1990) | — |
| Bipartite graphs | Kelly + spectral partial results | O | High payoff (see below) |
| 3-regular (cubic) graphs | Structural / Kelly; 2-reconstructibility known (Kostochka–Nahvi–West–Zirlin 2021 [kostochkanahviwestzirlin21][kostochkanahviwestzirlin21]) | O | High payoff |
| Triangle-free graphs | Kelly counting of small subgraphs | O | Medium |
| Strongly regular graphs | Parameter reconstructibility | O | Low (cospectral obstruction) |
| General graphs | Composite of all above | O | Very low (no single lever) |

Detail docs:

- [Counting / Kelly-style approaches](counting-approach.md)
- [Spectral / algebraic approaches](spectral-approach.md)
- [Random and probabilistic approaches](random-and-probabilistic.md)
- [Structural reductions](structural-reductions.md)
- [Counterexample search](counterexample-search.md)

## What would suffice to prove

Several restricted classes are known, or widely believed, to **imply** the
full conjecture. The table records the best-known implications; the "Source"
column cites the original reduction.

| If one proves … | … then it implies | Source |
|---|---|---|
| Every 2-connected graph is reconstructible | Reconstruction Conjecture (via Bondy's separable reduction) | Bondy 1969 [bondy69][bondy69] |
| Every bipartite graph is reconstructible | Widely believed to imply the general conjecture; not a formal reduction, but a canonical stress test | folklore; see Bondy 1991 [bondy91][bondy91] |
| Every 3-regular graph is reconstructible | A classical "hard" subclass; a structural reduction is not known, but failure here would likely yield the first counterexample | Harary's problem list |
| Edge-reconstruction of graphs with $m \le n \cdot \log_2 n$ edges | Closes the remaining gap to Müller 1977 [muller77][muller77] | Nash-Williams 1978 [nashwilliams78][nashwilliams78] |
| Reconstruction of the characteristic polynomial of **weighted** line graphs | Would extend Tutte 1979 [tutte79][tutte79] past Schwenk's barrier | — |
| A polynomial invariant finer than Tutte that is deck-reconstructible and isomorphism-complete | Immediately proves the conjecture | conjectural |

## Recent angles

- **Algorithmic reconstruction (Babai 2016).** Babai's quasi-polynomial
  GI algorithm [babai16][babai16] makes pairwise deck-checking
  quasi-polynomial-time; this is *not* polynomial and does **not** give
  any information-theoretic leverage on the conjecture itself. It is a
  computational convenience when comparing candidate reconstructions,
  nothing more.
- **Model theory / homogeneous structures.** Fraïssé-style limits and
  amalgamation classes hint at infinite analogues; the relevant finite
  question is whether a sufficiently rich Fraïssé class has the
  "deck-determination" property. This is exploratory.
- **Spectral + combinatorial hybrids.** Combining the charpoly with
  subgraph counts obtainable from Kelly's Lemma sidesteps Schwenk's
  cospectral obstruction in many cases; see [spectral-approach.md](spectral-approach.md).

## Open subproblems whose resolution would be major progress

1. Reconstruction of **bipartite graphs** (open even for bipartite of
   bounded degree).
2. Reconstruction of **3-regular** (cubic) graphs.
3. Reconstruction of **triangle-free** graphs.
4. Closing the Müller edge-reconstruction gap for edge counts
   $m \le n \cdot \log_2 n$.
5. Finding any deck-reconstructible polynomial invariant that separates
   all of Schwenk's cospectral families.
6. A structural characterization of hypothetical *minimally
   non-reconstructible* graphs (MNR atoms — see
   [structural-reductions.md](structural-reductions.md)).

## Where formalization could help

Several of the strategies have proofs that are combinatorial,
finitary, and free of real/functional-analytic machinery — these are good
Lean 4 targets. See [`../formalization/index.md`](../formalization/index.md)
for the current state of the sibling Lean project and concrete lemma lists.
Short list:

- **Kelly's Lemma** for subgraph counts, and its corollaries
  (degree sequence, number of edges, number of triangles,
  complement of the deck).  Pure counting, fits Mathlib's
  `SimpleGraph` and `Finset` API.
- **Bondy's separability reduction**: disconnected + separable graphs are
  reconstructible. Combinatorial induction, no analysis.
- **Tutte's charpoly reconstruction** (Tutte 1979 [tutte79][tutte79]):
  proof uses finite linear algebra over $\mathbb{Q}$; Mathlib has
  `Matrix.charpoly`, `Polynomial`, and enough linear algebra. A good
  "headline" target.
- **Müller's $m > n \cdot \log_2 n$ edge-count theorem**
  [muller77][muller77]: entropy / counting inequality; the probabilistic
  step reduces to explicit finite sums and Stirling-type bounds, which
  Mathlib supports.
- **Edge-reconstruction for graphs with many edges** via
  Lovász 1972 [lovasz72][lovasz72] (every graph with $m > \binom{n}{2}/2$
  edges is edge-reconstructible): elementary Möbius / inclusion–exclusion;
  very clean Lean target.
- **McKay-style finite verification up to $n = 11$** (or the current
  verified bound): `native_decide` is *not* appropriate on unbounded
  domains, but per-$n$ finite certificates, produced externally by nauty
  and audited in Lean via a hash-verified enumeration, are feasible. See
  [`../computational/index.md`](../computational/index.md).

What is **not** a good Lean target in the near term:

- Bollobás's random 3-card proof — requires a careful probabilistic
  argument over random permutations; Mathlib's probability layer can
  carry it, but the argument is delicate and the payoff is a
  "measure-1" statement rather than a structural theorem.
- Any fully general reconstruction result — there isn't one to formalize.

[bondy69]: ../sources.md#bondy69
[bondy91]: ../sources.md#bondy91
[tutte79]: ../sources.md#tutte79
[bollobas90]: ../sources.md#bollobas90
[muller77]: ../sources.md#muller77
[nashwilliams78]: ../sources.md#nashwilliams78
[babai16]: ../sources.md#babai16
[schwenk73]: ../sources.md#schwenk73
[mckay97]: ../sources.md#mckay97
[stockmeyer77]: ../sources.md#stockmeyer77
[kelly57]: ../sources.md#kelly57
[lovasz72]: ../sources.md#lovasz72
[kostochkanahviwestzirlin21]: ../sources.md#kostochkanahviwestzirlin21
