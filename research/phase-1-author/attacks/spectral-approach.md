# Spectral / Algebraic Approaches

## Tutte's characteristic-polynomial reconstruction

Tutte 1979 [tutte79][tutte79] proved that the **characteristic polynomial**
$\phi_G(x) = \det(xI - A(G))$ of a graph's adjacency matrix is
deck-reconstructible. The proof uses Kelly-style counting of small
subgraphs together with Harary's coefficient formula

$$\phi_G(x) = \sum_{k=0}^{n} c_k x^{n-k},
\qquad c_k = \sum_{H} (-1)^{p(H)} \, 2^{\,c(H)},$$

where the inner sum ranges over "elementary" spanning subgraphs $H$ of
$G$ on $k$ vertices (disjoint unions of edges and cycles), $p(H)$ is the
number of components, and $c(H)$ the number of cycle-components. Each
$c_k$ is a $\mathbb Z$-linear combination of counts of proper subgraphs
of $G$ and is therefore Kelly-reconstructible (see
[counting-approach.md](counting-approach.md)).

Tutte further showed reconstructibility of the **matching polynomial**,
the **chromatic polynomial**, the **dichromatic polynomial**, and the
full **Tutte polynomial** $T_G(x, y)$ by the same coefficient-counting
machinery.

## Why the charpoly is *not* enough

Schwenk 1973 [schwenk73][schwenk73] constructed infinitely many pairs of
**cospectral non-isomorphic trees** — graphs with identical
characteristic polynomials but different isomorphism types. Indeed
Schwenk showed that almost every tree has a cospectral mate. Hence:

> **Obstruction.** No invariant that is a function of $\phi_G$ alone
> can prove the Reconstruction Conjecture.

This rules out the entire "diagonalize and read off the spectrum"
approach, for trees and therefore for general graphs.

## Do richer polynomials help?

- **Matching polynomial $\mu_G(x)$.** Deck-reconstructible (Tutte 1979).
  Cospectral trees can be constructed to also share the matching
  polynomial. Hence matching spectrum is not a complete invariant.
- **Chromatic polynomial $P_G(k)$.** Deck-reconstructible (Tutte 1979).
  But many non-isomorphic graphs share the chromatic polynomial
  (chromatically equivalent graphs form infinite families).
- **Tutte polynomial $T_G(x,y)$.** Deck-reconstructible; strictly finer
  than the chromatic and flow polynomials jointly. Still not an
  isomorphism invariant — e.g. two non-isomorphic graphs on the same
  ground matroid share $T_G$.
- **Ihara zeta function / Bartholdi zeta function.** Determined by the
  spectrum of the edge-adjacency (Hashimoto) operator; again not
  isomorphism-complete.

No known "natural" graph polynomial is simultaneously
(a) deck-reconstructible and (b) a complete isomorphism invariant.
Finding one would immediately prove the conjecture. Most researchers
regard this as unlikely, but no impossibility theorem rules it out.

## Algebraic hybrid strategies

Two-step strategies combining spectral and combinatorial data:

1. **Spectrum + degree sequence + triangle count.** Recovers isomorphism
   for many graph classes but fails on Schwenk's cospectral pairs which
   can be chosen to share degree sequence.
2. **Generalized characteristic polynomial** $\det(xI - A - tD)$ for a
   parameter $t$. Cvetković showed this is strictly finer than $\phi_G$
   for some classes. Its deck-reconstructibility status is partially
   worked out; see Cvetković–Doob–Sachs (URL unknown — verify).
3. **Graph Laplacian spectrum.** For regular graphs the Laplacian
   spectrum is equivalent to the adjacency spectrum, so Schwenk's
   obstruction carries over. For irregular graphs they differ, but
   Laplacian-cospectral non-isomorphic graphs also exist (Haemers–Spence
   constructions).
4. **Normalized Laplacian / random walks.** Spectra again admit
   non-isomorphic cospectral mates.

## Where this leaves the spectral route

The honest summary: **spectral methods are a rich source of
deck-reconstructible invariants but cannot, by themselves, resolve the
conjecture.** The remaining spectral questions of interest are:

- Are all *strongly regular* graphs reconstructible?  Their
  two-eigenvalue structure means the charpoly determines the parameters
  but not the graph; pure spectrum cannot suffice, and no other deck
  lever has been identified.
- Is there a *weighted* or *multivariate* polynomial that separates
  all Schwenk pairs and is also deck-reconstructible?
- Can one reconstruct the **adjacency matrix up to signed permutation
  similarity** from the deck?  This is equivalent to the conjecture and
  so is not itself a simplification, but framing it algebraically may
  surface tools from representation theory.

## Lean formalization pointers

- **Harary's coefficient formula for $\phi_G(x)$.** Requires
  `Matrix.det`, `Matrix.charpoly`, and a bijection between permutation
  expansions and elementary subgraph configurations. Mathlib has the
  determinant expansion; the combinatorial bijection is the new content.
- **Tutte 1979 reconstruction of $\phi_G$.** Once Kelly's Lemma and
  the coefficient formula are in Lean, the reconstruction step is a
  direct $\sum$-manipulation — a very clean target, maybe 500–1000 lines.
- **Schwenk's cospectral tree construction.** A concrete counterexample
  to "charpoly determines the graph". Formalizing it proves that any
  *formalized* charpoly-only strategy cannot close the conjecture — a
  useful sanity result in Lean. The construction uses two specific
  trees and a gluing lemma; should be tractable.

[tutte79]: ../sources.md#tutte79
[schwenk73]: ../sources.md#schwenk73
[bondy91]: ../sources.md#bondy91
