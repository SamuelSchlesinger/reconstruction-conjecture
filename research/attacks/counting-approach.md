# Counting / Kelly-style Approaches

## Kelly's Lemma

Kelly 1957 [kelly57][kelly57] proved the foundational counting identity: for
any graph $F$ with $|V(F)| < |V(G)|$, the number of subgraphs of $G$
isomorphic to $F$ is determined by the deck of $G$. Explicitly, if
$s(F, G)$ denotes the count of (labelled or unlabelled, consistently chosen)
copies of $F$ in $G$, then

$$s(F, G) = \frac{1}{|V(G)| - |V(F)|} \sum_{v \in V(G)} s(F, G - v).$$

Every $s(F, G-v)$ is determined by the deck (we may choose any representative
from the card because $F$ is strictly smaller, so $s(F,\cdot)$ is an
isomorphism invariant). Hence $s(F,G)$ is deck-reconstructible for every
proper subgraph $F$.

This one lemma powers almost every positive reconstruction result in the
literature. Its proof is entirely finite and combinatorial — the cleanest
**Lean target** in the area.

## Immediate consequences

From Kelly's Lemma alone, the following are deck-reconstructible:

- **Number of edges** $|E(G)|$ — take $F = K_2$.
- **Degree sequence** — counts of $K_{1,k}$ for each $k$ recover the
  multiset of degrees.
- **Number of triangles, paths of length $k$, cycles of length $k$** for
  $k < n$ — each is a count of a fixed small subgraph.
- **Connectivity** — Kelly showed a graph is connected iff its deck
  contains at least two connected cards and an appropriate counting
  condition holds; see also Bondy 1991 [bondy91][bondy91].
- **Regularity and the common degree** — deck determines the degree
  sequence.

## Bondy's "legitimate decks"

Bondy 1991 [bondy91][bondy91] systematizes the counting method via
*legitimate decks*: a deck $\mathcal D$ is legitimate if there is *some*
graph $G$ with $\mathcal D(G) = \mathcal D$. The conjecture is equivalent
to: every legitimate deck has a unique realizer.

The Kelly-counting program attempts to list sufficiently many invariants
$I_1, I_2, \dots$ such that any two graphs with the same deck have the
same $I_j$ for all $j$, and then argue that the joint invariant
$(I_1, I_2, \dots)$ is a complete isomorphism invariant. This is *almost
certainly insufficient alone*: Schwenk's construction (see
[spectral-approach.md](spectral-approach.md)) produces non-isomorphic
graphs with identical characteristic polynomials — hence identical
walk-count spectra, which is a large subclass of Kelly-computable
invariants. So pure subgraph counts plus spectral data are not enough.

## Ceiling of pure Kelly counting

Kelly's Lemma gives subgraph counts for all **proper** subgraphs, but not
for $G$ itself. Any invariant expressible as a $\mathbb Z$-linear (or
polynomial) combination of proper-subgraph counts is Kelly-reconstructible.
The class of such invariants is large but **not** isomorphism-complete:

- Two regular non-isomorphic graphs with the same parameters (e.g. the two
  strongly regular $(16,6,2,2)$ graphs — the Shrikhande graph and the
  $4\times4$ rook graph) are cospectral, share the same triangle and
  closed-walk counts, and are distinguished by their induced-$K_{1,1,2}$
  counts (equivalently by their 4-vertex induced-subgraph profile). For
  the reconstruction problem this is not a counterexample — the deck
  itself contains more data than just low-order subgraph counts — but it
  bounds *pure counting*.
- More sharply, cospectral non-isomorphic graphs (Schwenk 1973
  [schwenk73][schwenk73]) share all closed-walk counts, which are linear
  combinations of subgraph homomorphism counts. So subgraph *homomorphism*
  counts alone cannot resolve reconstruction.

The true deck carries *structural* information beyond subgraph counts:
the actual isomorphism types of the cards, not just how many copies of
each smaller graph appear. That is why the conjecture is plausible even
though pure Kelly counting cannot prove it.

## What Kelly counting alone has achieved

- Reconstructibility of:
  - disconnected graphs (Kelly 1957);
  - trees (Kelly 1957);
  - regular graphs (several authors; see Bondy 1991 [bondy91][bondy91]);
  - graphs with a cut vertex (Bondy 1969 [bondy69][bondy69]);
  - unit-interval graphs and several other combinatorial classes.
- Reconstruction of numerous invariants (chromatic polynomial — Tutte's
  deeper result builds on this; matching polynomial; degree sequence;
  and more — see [`../invariants/index.md`](../invariants/index.md)).

## Open targets approachable by refined counting

- **Bipartite graphs.** The bipartition is deck-recognizable (bipartiteness
  is a monotone property detected by the absence of odd cycles, and odd
  cycle counts are Kelly-reconstructible). Reconstructing the biadjacency
  matrix from the deck's biadjacency-card-matrices is the hard step.
- **Triangle-free graphs.** Triangle-freeness is deck-recognizable
  (triangles in $G$ count, and $=0$ iff $G$ is triangle-free). The hard
  step is what *else* the deck constrains in the triangle-free regime.

## Lean formalization pointers

- Kelly's Lemma: a finite-sum identity over `SimpleGraph` / `Finset`.
  Mathlib has `SimpleGraph.card`, subgraph API, and inclusion sums. No
  new axioms needed. **Primary target.**
- Edge-count, degree-sequence, triangle-count reconstruction: corollaries
  of Kelly's Lemma; each is a ~30–100 line Lean lemma once the main
  lemma is in place.
- Connectivity reconstruction (Kelly): requires a case analysis on the
  number of connected components and a counting argument; ~200–400 lines.

See [`../formalization/index.md`](../formalization/index.md) for current
status of the sibling Lean project.

[kelly57]: ../sources.md#kelly57
[bondy69]: ../sources.md#bondy69
[bondy91]: ../sources.md#bondy91
[schwenk73]: ../sources.md#schwenk73
