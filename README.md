# Reconstruction Conjecture: Formalization in Lean 4

A Lean 4 formalization of the [Reconstruction Conjecture](https://en.wikipedia.org/wiki/Reconstruction_conjecture)
(Kelly 1942, Ulam 1960), one of the foremost open problems in graph theory.

## The Conjecture

Every simple graph on at least 3 vertices is determined up to isomorphism by
its **deck** — the multiset of vertex-deleted subgraphs considered up to
isomorphism.

Given a graph $G$ on vertex set $V$ with $|V| \geq 3$, delete each vertex $v$
to obtain a "card" $G - v$. The collection of all cards (as a multiset of
isomorphism classes) is the deck of $G$. The conjecture asserts:

$$\text{deck}(G) = \text{deck}(H) \implies G \cong H$$

## Formalization

We define `SameDeck G H` to mean there exists a bijection $\sigma : V \simeq V$
such that $G - v \cong H - \sigma(v)$ for all $v \in V$.

### What We Prove

| Result | File |
|--------|------|
| `SameDeck` is reflexive | [`Basic.lean`](Reconstruction/Basic.lean) |
| `SameDeck` is symmetric | [`Basic.lean`](Reconstruction/Basic.lean) |
| `SameDeck` is transitive | [`Basic.lean`](Reconstruction/Basic.lean) |
| Complement deck is reconstructible: $G \sim_{\text{deck}} H \Rightarrow G^c \sim_{\text{deck}} H^c$ (reconstructibility closed under complementation) | [`Basic.lean`](Reconstruction/Basic.lean) |
| $\|E(G-v)\| + \deg(v) = \|E(G)\|$ | [`EdgeCount.lean`](Reconstruction/EdgeCount.lean) |
| $\deg(v) = \|E(G)\| - \|E(G-v)\|$ | [`EdgeCount.lean`](Reconstruction/EdgeCount.lean) |
| $\sum_v \|E(G-v)\| = (|V|-2)\|E(G)\|$ | [`EdgeCount.lean`](Reconstruction/EdgeCount.lean) |
| Edge count is reconstructible | [`EdgeCount.lean`](Reconstruction/EdgeCount.lean) |
| Degree sequence is reconstructible | [`DegreeSequence.lean`](Reconstruction/DegreeSequence.lean) |
| Kelly's counting identity: $(n-k) \cdot s(F,G) = \sum_v s(F, G-v)$ | [`KellyLemma.lean`](Reconstruction/KellyLemma.lean) |
| Subgraph count is reconstructible (Kelly's Lemma) | [`KellyLemma.lean`](Reconstruction/KellyLemma.lean) |
| Kocay-style finite-index cover counts, target cover numbers, product-count identity grouped by induced-subgraph isomorphism class, and reconstructible finite products of subgraph counts | [`Kocay.lean`](Reconstruction/Kocay.lean) |
| Connectivity is reconstructible | [`ConnectedComponents.lean`](Reconstruction/ConnectedComponents.lean) |
| Number of connected components is reconstructible | [`ConnectedComponents.lean`](Reconstruction/ConnectedComponents.lean) |
| Component-count triangular identity: copies of connected $F$ are $F$-components plus copies inside larger components | [`Disconnected/ComponentCount.lean`](Reconstruction/Disconnected/ComponentCount.lean) |
| Local component-multiset induction step: matched larger components recover the $F$-component count | [`Disconnected/ComponentCount.lean`](Reconstruction/Disconnected/ComponentCount.lean) |
| Component iso-class matching: equal per-class component counts produce a component bijection preserving component isomorphism classes | [`Disconnected/ComponentCount.lean`](Reconstruction/Disconnected/ComponentCount.lean) |
| Same-deck disconnected component counts agree by descending triangular induction | [`Disconnected/ComponentCount.lean`](Reconstruction/Disconnected/ComponentCount.lean) |
| Componentwise assembly: matched connected components with per-component isomorphisms assemble to a global graph isomorphism | [`Disconnected.lean`](Reconstruction/Disconnected.lean) |
| Component-count assembly: equal component multiplicities for every component type imply a global graph isomorphism | [`Disconnected.lean`](Reconstruction/Disconnected.lean) |
| Disconnected graphs are reconstructible (Kelly 1942) | [`Disconnected.lean`](Reconstruction/Disconnected.lean) |
| Vertex separators, cut vertices, and 2-connectivity (separator-decomposition programme) | [`Separator.lean`](Reconstruction/Separator.lean) |
| Separators — hence cut vertices and 2-connectivity — are isomorphism invariants | [`Separator.lean`](Reconstruction/Separator.lean) |
| Separator reassembly engine: a piecewise-adjacency-preserving, piece-matching bijection is a global isomorphism (amalgamation over a shared separator; generalizes the disjoint-union/component assembly) | [`Separator.lean`](Reconstruction/Separator.lean) |
| Cut-vertex reassembly: a card isomorphism $G-v \cong H-v$ preserving the link of $v$ extends to $G \cong H$ | [`Separator.lean`](Reconstruction/Separator.lean) |
| Data-carrying component assembly with vertex-action lemma (`componentIso`, `componentIso_apply`) | [`Disconnected.lean`](Reconstruction/Disconnected.lean) |
| Cut-vertex reconstruction reduces to a piece-matching of $G-v$ agreeing on $v$'s attachment (complete structural reduction for Bondy's case) | [`Separator.lean`](Reconstruction/Separator.lean) |
| **Graphs with a universal (dominating) vertex are reconstructible** (Manvel's method, simplest case) | [`Separator.lean`](Reconstruction/Separator.lean) |
| One-card extension API: adding a new vertex with chosen neighbors recovers the card after deleting the new vertex, and every same-deck reconstruction lies in this search space | [`Search.lean`](Reconstruction/Search.lean) |
| Adjacency matrix of induced subgraph = principal submatrix | [`Spectral.lean`](Reconstruction/Spectral.lean) |
| Isomorphic graphs have equal characteristic polynomials | [`Spectral.lean`](Reconstruction/Spectral.lean) |
| $\varphi'(G) = \sum_v \varphi(G-v)$ (derivative formula) | [`Spectral.lean`](Reconstruction/Spectral.lean) |
| Characteristic polynomial derivative is reconstructible | [`Spectral.lean`](Reconstruction/Spectral.lean) |
| Non-constant char. poly. coefficients are reconstructible | [`Spectral.lean`](Reconstruction/Spectral.lean) |
| Newton/Faddeev-LeVerrier trace identity | [`Newton.lean`](Reconstruction/Newton.lean) |
| $\operatorname{tr}(A^k)$ is reconstructible for $k < |V|$ | [`TraceReconstruction.lean`](Reconstruction/TraceReconstruction.lean) |
| Top-trace support split: closed walks are partitioned into proper-support and full-support pieces, with the proper part expanded as a sum over exact vertex supports | [`TopTrace.lean`](Reconstruction/TopTrace.lean) |
| Conditional constant-term reduction: `c_0` follows from equality of $\operatorname{tr}(A^{|V|})$ | [`CharPolyFull.lean`](Reconstruction/CharPolyFull.lean) |
| Conditional constant-term reduction from equality of the two top-trace support-count pieces | [`CharPolyFull.lean`](Reconstruction/CharPolyFull.lean) |

### Reconstructible Invariants

We prove reconstructibility results from Kelly's lemma and spectral graph theory:

1. **Subgraph counts — Kelly's Lemma** (`SameDeck.subgraphCount_eq`): For any graph
   $F$ with $|V(F)| < |V(G)|$, the number of induced copies of $F$ in $G$ is
   reconstructible from the deck. This is the central counting tool in reconstruction
   theory, proved via the double-counting identity
   $(n - k) \cdot s(F, G) = \sum_v s(F, G - v)$.

2. **Edge count** (`SameDeck.card_edgeFinset_eq`): Each edge appears in exactly
   $n - 2$ of the $n$ vertex-deleted subgraphs, so the total edge count can be
   recovered from the deck.

3. **Degree sequence** (`SameDeck.degreeMultiset_eq`): Since
   $\deg(v) = |E(G)| - |E(G - v)|$ and both quantities are determined by the
   deck, the full degree multiset is reconstructible.

4. **Characteristic polynomial derivative** (`SameDeck.charPoly_derivative_eq`):
   The derivative formula $\varphi'(G, x) = \sum_v \varphi(G-v, x)$ shows that
   same deck implies same characteristic polynomial derivative.

5. **Non-constant coefficients** (`SameDeck.charPoly_coeff_eq`): Since the
   derivative determines all coefficients of degree $\geq 1$, same deck implies
   agreement on all non-constant characteristic polynomial coefficients.

### Why the Conjecture is Hard

These results show we can reconstruct a lot — edge count, degree sequence — but
knowing these invariants does not determine the graph up to isomorphism. For
example, many non-isomorphic graphs share the same degree sequence (e.g., the
5-cycle $C_5$ and the bull graph both have 5 vertices and 5 edges). For any
$d \geq 3$ there are exponentially many non-isomorphic $d$-regular graphs on $n$
vertices. The gap between "reconstructible invariants" and "full structural
determination" is where the difficulty lies.

### What Remains Open

Current open declarations (`sorry`) are:

- [`reconstruction_conjecture`](Reconstruction/Basic.lean) (the main conjecture)
- [`SameDeck.charPoly_coeff_zero_eq`](Reconstruction/CharPolyFull.lean)

Core deck machinery (`SameDeck`, Kelly's lemma, edge count, degree sequence,
connected-component count, the componentwise Sigma assembly theorem, Kelly's
disconnected-graph reconstruction theorem, trace reconstruction below the
vertex count, the top-trace support split, component iso-class matching from per-class counts,
larger-component matching above a size threshold, and non-constant
characteristic-polynomial coefficients) is proved. The remaining internal
staged target is the constant-term characteristic-polynomial reconstruction;
it is now reduced to proving equality of the top-length proper-support and
full-support closed-walk counts.
the full reconstruction conjecture itself remains open mathematics.

The project's **active attack** is the separator-decomposition programme
(`research/attacks/separator-decomposition.md`): reconstruct class by class up a
ladder of separator size, reusing the component-decomposition machinery.
`Separator.lean` lays the vocabulary layer (cut vertices, separators,
2-connectivity, and their isomorphism-invariance); the next targets are Bondy's
cut-vertex reduction (`BondySeparableReconstructible`) and, beyond it, chordal
graphs via clique separators (open mathematics). This direction was adopted
after a strategy review found the spectral, flag-algebra, and Weisfeiler–Leman
attacks either barred by known obstructions or equivalent to Kelly counting, and
after the centered-extension/fixed-host campaign's low-slice target was refuted
(`research/attacks/fixed-host-t-empty.md`).

## File Structure

```
Reconstruction/
  Defs.lean            -- SimpleGraph.deleteVert, SimpleGraph.SameDeck
  Basic.lean           -- SameDeck equivalence relation, reconstruction_conjecture (sorry)
  EdgeCount.lean       -- Edge count formula, edge count is reconstructible
  DegreeSequence.lean  -- Degree multiset definition, degree sequence is reconstructible
  KellyLemma.lean      -- Kelly's Lemma: subgraph counting identity and reconstructibility
  KellyEdgeCount.lean  -- Alternate edge-count reconstruction via Kelly's Lemma
  Kocay.lean           -- Kocay-style cover-counting identities
  Regular.lean         -- Regularity is reconstructible from degree sequence
  ConnectedComponents.lean -- Number of connected components is reconstructible
  Disconnected.lean    -- Disconnected-case reconstruction theorem
  Separator.lean       -- Cut vertices, separators, 2-connectivity; iso-invariance (separator-decomposition programme)
  Trees.lean           -- Tree-case consequences from component machinery
  Search.lean          -- One-card extension search-space API
  Spectral.lean        -- Characteristic polynomial, derivative formula, spectral reconstructibility
  TraceReconstruction.lean -- Trace(A^k) reconstructibility for k < |V|
  TopTrace.lean        -- Top-trace support split and exact-support expansion
  Newton.lean          -- Newton/Faddeev-LeVerrier trace identity
  CharPolyFull.lean    -- Constant-term + full charpoly reconstruction target (sorry)
```

## Building

Requires Lean 4.28.0 and Mathlib 4.28.0.

```sh
lake build
```

## References

- Kelly, P. J. (1942). "On isometric transformations". PhD thesis, University of Wisconsin.
- Kocay, W. L. (1981). "Some new methods in reconstruction theory". Lecture Notes in Mathematics 884.
- McKay, B. D. (1998). "Isomorph-free exhaustive generation". Journal of Algorithms 26.
- Ulam, S. M. (1960). *A Collection of Mathematical Problems*. Interscience.
- Bondy, J. A. (1991). "A graph reconstructor's manual". In *Surveys in Combinatorics*.
