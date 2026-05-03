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

Bondy 1969 [bondy69][bondy69] proved that every **separable graph** (a
graph with a cut vertex) is reconstructible. Combined with Kelly's
theorem that disconnected graphs are reconstructible, the conjecture
reduces to:

> **Reduction.** It suffices to prove the Reconstruction Conjecture for
> **2-connected graphs**.

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

> **Müller.** Every graph with $n$ vertices and more than
> $\tfrac{1}{2} n \log_2 n$ edges is edge-reconstructible.

The proof is a beautiful entropy / counting argument. Lovász earlier
showed:

> **Lovász.** Every graph with more than $\binom{n}{2}/2$ edges is
> edge-reconstructible.

Müller strengthened this significantly. Nash-Williams 1978
[nashwilliams78][nashwilliams78] gave a unified treatment and raised the
question of pushing the edge-count threshold below $n \log n / 2$.

## Minimally non-reconstructible graphs ("MNR atoms")

If the conjecture is false, there is a **minimal counterexample** — a
graph $G$ such that $G$ is non-reconstructible but every proper
subgraph and every vertex-deleted subgraph of $G$ is reconstructible.
Properties of such an MNR graph $G$ would include:

- $G$ must be 2-connected (by Bondy's reduction);
- Every card $G - v$ is reconstructible (so the deck "recomposes"
  consistently) but the deck admits at least two non-isomorphic
  realizers;
- Any two realizers share every Kelly-reconstructible invariant —
  degree sequence, number of edges, charpoly, Tutte polynomial, and
  so on;
- Any two realizers must be *cospectral* (by Tutte 1979
  [tutte79][tutte79]).

No such "atom" has been found; conversely, no structure theorem rules
them out. A proof that MNR graphs must lie in an intersection of
exclusion conditions that is empty would resolve the conjecture. This
is the dream strategy and has not yet succeeded.

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
5. **Closing the Müller gap for edge reconstruction** between
   $\tfrac{1}{2} n \log_2 n$ and $\binom{n-1}{2}+1$ edges.

## Lean formalization pointers

Good near-term Lean targets:

- **Bondy 1969 separable-graph reduction.** A 2–3 page argument using
  Kelly's Lemma and induction on a cut vertex's block structure.
  ~1000–1500 lines in Lean, assuming Kelly's Lemma is in place.
- **Lovász's $\binom{n}{2}/2$ edge-reconstruction bound.** A clean
  inclusion–exclusion / Möbius argument; small Lean file once the
  basic `Finset`-of-edges infrastructure is set up.
- **Müller's $\tfrac{1}{2} n \log_2 n$ theorem.** More ambitious;
  uses entropy-like counting. Mathlib has Stirling and basic entropy
  API; plausible but moderate effort.
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
