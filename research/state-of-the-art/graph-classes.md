# Reconstructible Structural Classes

This document collects the structural classes other than trees and
random graphs that are known to be reconstructible from their
vertex-decks. Proof sketches follow Bondy's survey
[bondy91][bondy91] and Lauri–Scapellato [laurisc16][laurisc16]; year
and attribution should be cross-checked against MathSciNet/Zbl where
flagged.

## Disconnected graphs (Harary 1964; Manvel 1970)

**Theorem** [harary64][harary64]. If `G` has at least two non-trivial
connected components, `G` is reconstructible.

**Idea.** Kelly's Lemma recovers the number of subgraphs isomorphic to
each connected graph `F` on `< n` vertices. Thus the *multiset of
components* of `G` is reconstructible (the components are exactly the
maximal connected `F` with multiplicity equal to their count as
components). Disjoint union of the reconstructed components yields `G`.

Extensions:

- **Manvel (1970).** Removed the "non-trivial" hypothesis modulo
  handling isolated vertices [manvel70][manvel70].
- **Kelly 1957.** The tree result is a special case once you know all
  components are trees.

## Regular graphs (Bondy–Hemminger 1977)

**Theorem (Bondy–Hemminger 1977)** [bondyhemminger77][bondyhemminger77].
Every regular graph is reconstructible.

**Idea.** The degree sequence is reconstructible (it is just the
multiset of `deg(v) = |E(G)| - |E(G-v)|` values, which are readable off
each card's edge count). Once you know `G` is `r`-regular and know
`n`, Kelly's Lemma counts every small subgraph, and a standard
reconstructive matching argument recovers `G`. The argument appears in
the Bondy–Hemminger survey [bondyhemminger77][bondyhemminger77] and is
also attributed to Nash-Williams (1978) [nashwilliams78][nashwilliams78]
as an accepted reference. In particular, cubic (3-regular) graphs are
reconstructible.

## Separable graphs without endvertices (Bondy 1969)

A graph is **separable** if it has a cut-vertex. An **endvertex**
(pendant) has degree 1.

**Theorem (Bondy 1969)** [bondy69][bondy69]. If `G` is separable and
has no pendant vertex, `G` is reconstructible.

**Idea.** The block-cut-tree of `G` is reconstructible from the deck,
and the absence of pendants means each block contributes at least two
vertices. Kelly's Lemma recovers the blocks themselves.

## Maximal planar graphs (Fiorini–Lauri 1981)

**Theorem (Fiorini–Lauri 1981)** [fiorinilauri81][fiorinilauri81]. Every
maximal planar graph on `n ≥ 4` vertices is reconstructible.

**Idea.** Maximal planar graphs on `≥ 4` vertices are 3-connected.
Whitney's theorem says 3-connected planar graphs have a unique planar
embedding up to reflection. The deck recovers the degree sequence and
all small-subgraph counts; one then shows the combinatorial map is
determined by this data.

## Outerplanar graphs (Giles 1974)

**Theorem (Giles 1974)** [giles74][giles74]. Every outerplanar graph
is reconstructible.

**Idea.** Outerplanar graphs have a canonical "outer face"; Giles shows
that enough of the outer face structure is visible in each card that
the boundary cycle and inner chords can be reassembled.

## Unit interval graphs

**Theorem.** Unit interval graphs are reconstructible.

Exact attribution is uncertain — often credited to **von Rimscha**
(1980s) in surveys, but the primary paper should be verified against
MathSciNet/Zbl. Idea: unit interval graphs have a canonical linear
order of their vertices (determined by the left endpoints of the
intervals), and Kelly's Lemma recovers the order plus the adjacencies
around each vertex.

## Interval graphs (Heinrich et al. 2025)

**Theorem (Heinrich et al. 2025)** [heinrich25][heinrich25]. Every
interval graph is reconstructible.

This 2025 arXiv preprint (arXiv:2504.02353) settles the interval-graph
case, going beyond the earlier unit-interval result. Chordal graphs in
general remain open.

## Squares of graphs (Manvel)

**Theorem (Manvel, early 1970s).** If `G = H^2` is the square of some
graph `H`, then `G` is reconstructible.

Exact citation uncertain — Manvel has multiple papers in this area;
verify against [bondy91][bondy91] Section on power-graph reconstruction.

## Graphs with many dominating vertices (Manvel 1975)

A vertex `v` is **dominating** if `deg(v) = n - 1`.

**Theorem (Manvel 1975)** [manvel76][manvel76]. If `G` has at least
`n - 3` dominating vertices, `G` is reconstructible.

**Idea.** Such graphs are "close to complete"; their complement has at
most `3` non-isolated vertices, and the complement is trivially
reconstructible.

## Graphs without endvertices of a given type

Several results of the form "if `G` has no pendant of type `X`, then
`G` is reconstructible" appear in Bondy [bondy69][bondy69], Manvel
[manvel70][manvel70], and Nash-Williams [nashwilliams78][nashwilliams78].
The unifying theme: pendants are the principal obstruction to Kelly's
Lemma's recovery power.

## Line graphs (partial)

Whitney's theorem (1932) says that a connected graph is determined by
its line graph except for the well-known `K_3`/`K_{1,3}` ambiguity.
Various authors have shown that line graphs of particular classes are
reconstructible:

- **Hemminger (1969).** Line graphs of graphs other than `K_3` are
  edge-reconstructible (verify).
- **Ellingham (1988).** Line graphs of regular graphs (exact citation
  uncertain — verify).

Full line-graph reconstruction is **open** in general.

## Claw-free, `K_4`-free, and other forbidden-subgraph classes

Most results here are partial. Bondy's survey [bondy91][bondy91]
catalogues them; Lauri–Scapellato [laurisc16][laurisc16] gives a more
recent compilation.

## Summary table

| Class | Reconstructible? | Primary citation |
|-------|------------------|------------------|
| Trees | Yes | Kelly 1957 [kelly57][kelly57] |
| Forests | Yes | follows from Kelly + Harary |
| Disconnected with ≥ 2 nontrivial components | Yes | Harary 1964 [harary64][harary64] |
| Regular graphs (all) | Yes | Bondy–Hemminger 1977 [bondyhemminger77][bondyhemminger77] |
| 3-regular (cubic) in full generality | Yes | Bondy–Hemminger 1977 [bondyhemminger77][bondyhemminger77] |
| Separable without pendants | Yes | Bondy 1969 [bondy69][bondy69] |
| Maximal planar | Yes | Fiorini–Lauri 1981 [fiorinilauri81][fiorinilauri81] |
| Outerplanar | Yes | Giles 1974 [giles74][giles74] |
| Planar (general) | Open | — |
| Bipartite (general) | Open | — |
| Unit interval | Yes | (attribution uncertain) |
| Interval | Yes | Heinrich et al. 2025 [heinrich25][heinrich25] |
| Chordal (general) | Open | — |
| Squares of graphs | Yes | Manvel (early 70s) |
| `G` with ≥ `n - 3` dominating vertices | Yes | Manvel 1975 [manvel76][manvel76] |
| Line graphs (general) | Open | — |

[bondy91]: ../sources.md#bondy91
[kelly57]: ../sources.md#kelly57
[harary64]: ../sources.md#harary64
[manvel70]: ../sources.md#manvel70
[manvel76]: ../sources.md#manvel76
[bondy69]: ../sources.md#bondy69
[fiorinilauri81]: ../sources.md#fiorinilauri81
[giles74]: ../sources.md#giles74
[nashwilliams78]: ../sources.md#nashwilliams78
[laurisc16]: ../sources.md#laurisc16
[bondyhemminger77]: ../sources.md#bondyhemminger77
[heinrich25]: ../sources.md#heinrich25
