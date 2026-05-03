# Structural Reductions

## Bondy's "tricks"

A collection of elementary observations, codified in Bondy 1991
[bondy91][bondy91], that recover structural information directly from
the deck:

- **Connectedness is recognizable.** $G$ is disconnected iff more than
  one of the cards is disconnected in a compatible way (precise
  statement: $G$ is connected iff $G$ has at most one component of
  maximum order, detectable from the deck). Kelly 1957 [kelly57][kelly57]
  proved disconnected graphs are reconstructible directly.
- **Regularity is recognizable.** The degree sequence is
  deck-reconstructible (from Kelly counting on $K_{1,k}$), so
  "$G$ is $d$-regular" is a deck property.
- **Bipartiteness is recognizable.** Odd-cycle counts are
  Kelly-reconstructible; $G$ is bipartite iff all odd-cycle counts
  vanish.
- **Self-complementarity is *not known* to be recognizable** from the
  deck alone in general, though it is known in many special cases.
- **Number of spanning trees, number of perfect matchings** — both are
  deck-reconstructible (Tutte 1979 [tutte79][tutte79]; matching
  polynomial at 0 argument).

These "tricks" reduce reconstruction of general $G$ to reconstruction of
$G$ within a known class (connected / regular / bipartite / etc.), which
sets up the structural attack.

## Bondy's separability reduction

Bondy 1969 [bondy69][bondy69] proved that every **separable graph with
minimum degree $\delta \ge 2$** (i.e. a graph with a cut vertex and *no
pendant vertices*) is reconstructible. The pendant-vertex case —
graphs containing a vertex of degree $1$ — is handled separately by
Kelly's original argument for trees and related structures in Kelly 1957
[kelly57][kelly57]. Together with Kelly's reconstructibility of
disconnected graphs, a later cleanup by Yongzhi 1988
[yongzhi88][yongzhi88] gave the modern form of the reduction:

> **Reduction (Yongzhi 1988).** It suffices to prove the Reconstruction
> Conjecture for **2-connected graphs**.

Hence the attack on disconnected / separable cases is complete; the
remaining difficulty is concentrated in 2-connected graphs. Even
restricted to this class, only a few sub-classes are known:
block-graphs, outerplanar, maximal planar, some classes of line graphs,
etc. See [`../state-of-the-art/index.md`](../state-of-the-art/index.md).

## Edge reconstruction and Müller's theorem

The **Edge Reconstruction Conjecture** (Harary 1964) asks whether a
graph with $\ge 4$ edges is determined by its *edge-deck*
$\{G - e : e \in E(G)\}$. This is implied by the vertex-reconstruction
conjecture (since $G - e$ information is extractable from the vertex
deck by counting) but is technically weaker.

Müller 1977 [muller77][muller77] proved:

> **Müller.** Every graph with $n$ vertices and $m > n \cdot \log_2 n$
> edges is edge-reconstructible.

The proof is a beautiful entropy / counting argument. Lovász 1972
[lovasz72][lovasz72] earlier showed:

> **Lovász.** Every graph with $m > \binom{n}{2}/2$ edges is
> edge-reconstructible.

Müller strengthened this asymptotically. Nash-Williams 1978
[nashwilliams78][nashwilliams78] gave a unified treatment and raised the
question of pushing the edge-count threshold below $m = n \cdot \log_2 n$.

## Minimally non-reconstructible graphs ("MNR atoms")

If the conjecture is false, there is a **minimal counterexample** — a
graph $G$ such that $G$ is non-reconstructible but every graph on fewer
vertices (in particular every vertex-deleted subgraph of $G$) is
reconstructible. We call any such $G$ an **MNR atom**. The following
is a non-fabricated outline of the constraints an MNR atom $G$ on
$n \ge 3$ vertices must satisfy; each item is a direct consequence of
a theorem cited above.

Structural necessary conditions:

- **2-connected.** By the Bondy–Yongzhi reduction (Bondy 1969
  [bondy69][bondy69], Yongzhi 1988 [yongzhi88][yongzhi88]), $G$ has
  no cut vertex. In particular $\delta(G) \ge 2$.
- **Connected, neither a tree nor a forest.** Trees (Kelly 1957
  [kelly57][kelly57]) and disconnected graphs (Kelly 1957) are
  reconstructible.
- **Not regular.** Regular graphs are reconstructible by Kelly counting
  (see [counting-approach.md](counting-approach.md)); in particular
  $G$ is not complete, not a cycle, and not a complement of such.
- **Edge count in the Müller/Lovász gap.** By Lovász 1972
  [lovasz72][lovasz72] and Müller 1977 [muller77][muller77], any graph
  with $m > n \cdot \log_2 n$ edges is edge-reconstructible; together
  with complementation, an MNR atom must have edge count
  $m \le n \cdot \log_2 n$ (and by self-complementary symmetry the
  complement also satisfies this).

Invariant-level necessary conditions for the two (or more) realizers
of the MNR deck:

- Identical **degree sequence**, **number of edges**, **number of
  triangles**, and every subgraph count $s(F, \cdot)$ with
  $|V(F)| \le n-1$ (Kelly's Lemma).
- Identical **characteristic polynomial** — hence **cospectral** — by
  Tutte 1979 [tutte79][tutte79].
- Identical **chromatic polynomial**, **matching polynomial**, and
  **Tutte polynomial** (Tutte 1979).

No graph simultaneously meeting all the structural conditions *and*
admitting a non-isomorphic partner sharing the invariant profile has
been found (computationally up to the verified bound; see
[counterexample-search.md](counterexample-search.md)). Conversely, no
structure theorem rules MNR atoms out. A proof that the conjunction of
the conditions above (possibly strengthened) is empty would resolve
the conjecture. This is the dream strategy and has not yet succeeded.

## Structural attacks per class

- **Trees** (Kelly 1957). Induction on leaves; fully formalized in the
  literature, and tractable in Lean.
- **Separable graphs** (Bondy 1969). Induction on the block structure.
  Good Lean target: the argument uses only finite induction and
  Kelly-type counting.
- **Unit-interval and interval graphs.** Reconstruct the interval
  representation from the deck's ordering data.
- **Outerplanar graphs** (Giles 1976). Good Lean target; proof is
  purely combinatorial.
- **Maximal planar graphs** (Lauri). Planar structure forces enough
  rigidity that the deck determines the embedding.
- **Graphs with a unique vertex of maximum degree**. Deck recognizes
  that vertex's removal-card, giving a canonical anchor.
- **Graphs of bounded treewidth.** Recent results use dynamic-programming
  over tree decompositions; see Kratsch–Hemaspaandra for algorithmic
  versions (URLs unknown — verify).

## Open structural problems of high leverage

1. **Reconstruction of 2-connected graphs.** Equivalent to the full
   conjecture after Bondy's reduction.
2. **Reconstruction of 3-regular (cubic) graphs.** Open; widely
   studied; would be major progress.
3. **Reconstruction of bipartite graphs.** Open; a canonical stress
   test.
4. **Reconstruction of triangle-free graphs.** Open.
5. **Closing the Müller gap for edge reconstruction** for edge counts
   $m \le n \cdot \log_2 n$.

## Lean formalization pointers

Good near-term Lean targets:

- **Bondy 1969 separable-graph reduction.** A 2–3 page argument using
  Kelly's Lemma and induction on a cut vertex's block structure.
  ~1000–1500 lines in Lean, assuming Kelly's Lemma is in place.
- **Lovász's $m > \binom{n}{2}/2$ edge-reconstruction bound**
  [lovasz72][lovasz72]. A clean inclusion–exclusion / Möbius argument;
  small Lean file once the basic `Finset`-of-edges infrastructure is
  set up.
- **Müller's $m > n \cdot \log_2 n$ theorem** [muller77][muller77].
  More ambitious; uses entropy-like counting. Mathlib has Stirling
  and basic entropy API; plausible but moderate effort.
- **Kelly's connectivity-recognition lemma.** Combinatorial case
  analysis; medium-size Lean file.

Deferrable:

- MNR / atomic-reduction theorems — conjectural, not a proof.
- Treewidth / parameter-DP reconstruction — requires tree decomposition
  infrastructure not yet in Mathlib.

[kelly57]: ../sources.md#kelly57
[bondy69]: ../sources.md#bondy69
[bondy91]: ../sources.md#bondy91
[tutte79]: ../sources.md#tutte79
[muller77]: ../sources.md#muller77
[nashwilliams78]: ../sources.md#nashwilliams78
[lovasz72]: ../sources.md#lovasz72
[yongzhi88]: #yongzhi88

[yongzhi88]: ../sources.md#yongzhi88
