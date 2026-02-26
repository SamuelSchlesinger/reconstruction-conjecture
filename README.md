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
| $\|E(G-v)\| + \deg(v) = \|E(G)\|$ | [`EdgeCount.lean`](Reconstruction/EdgeCount.lean) |
| Edge count is reconstructible | [`EdgeCount.lean`](Reconstruction/EdgeCount.lean) |
| Degree sequence is reconstructible | [`DegreeSequence.lean`](Reconstruction/DegreeSequence.lean) |
| Kelly's counting identity: $(n-k) \cdot s(F,G) = \sum_v s(F, G-v)$ | [`KellyLemma.lean`](Reconstruction/KellyLemma.lean) |
| Subgraph count is reconstructible (Kelly's Lemma) | [`KellyLemma.lean`](Reconstruction/KellyLemma.lean) |
| Adjacency matrix of induced subgraph = principal submatrix | [`Spectral.lean`](Reconstruction/Spectral.lean) |
| Isomorphic graphs have equal characteristic polynomials | [`Spectral.lean`](Reconstruction/Spectral.lean) |
| $\varphi'(G) = \sum_v \varphi(G-v)$ (derivative formula) | [`Spectral.lean`](Reconstruction/Spectral.lean) |
| Characteristic polynomial derivative is reconstructible | [`Spectral.lean`](Reconstruction/Spectral.lean) |
| Non-constant char. poly. coefficients are reconstructible | [`Spectral.lean`](Reconstruction/Spectral.lean) |

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
- [`SameDeck.numComponents_eq`](Reconstruction/ConnectedComponents.lean)
- [`SameDeck.iso_of_not_connected`](Reconstruction/Disconnected.lean)
- [`SameDeck.trace_adjMatrix_pow_eq`](Reconstruction/TraceReconstruction.lean)
- [`Matrix.newton_trace_charpoly`](Reconstruction/Newton.lean)
- [`SameDeck.charPoly_coeff_zero_eq`](Reconstruction/CharPolyFull.lean)

Core deck machinery (`SameDeck`, Kelly's lemma, edge count, degree sequence,
and non-constant characteristic-polynomial coefficients) is proved. The open
items are staged extensions toward stronger reconstruction results.

## File Structure

```
Reconstruction/
  Defs.lean            -- SimpleGraph.deleteVert, SimpleGraph.SameDeck
  Basic.lean           -- SameDeck equivalence relation, reconstruction_conjecture (sorry)
  EdgeCount.lean       -- Edge count formula, edge count is reconstructible
  DegreeSequence.lean  -- Degree multiset definition, degree sequence is reconstructible
  KellyLemma.lean      -- Kelly's Lemma: subgraph counting identity and reconstructibility
  KellyEdgeCount.lean  -- Alternate edge-count reconstruction via Kelly's Lemma
  Regular.lean         -- Regularity is reconstructible from degree sequence
  ConnectedComponents.lean -- Component-count reconstructibility target (sorry)
  Disconnected.lean    -- Disconnected-case reconstruction target (sorry)
  Trees.lean           -- Tree-case consequences from component machinery
  Spectral.lean        -- Characteristic polynomial, derivative formula, spectral reconstructibility
  TraceReconstruction.lean -- Trace(A^k) reconstructibility target (sorry)
  Newton.lean          -- Newton/Faddeev-LeVerrier identity target (sorry)
  CharPolyFull.lean    -- Constant-term + full charpoly reconstruction target (sorry)
```

## Building

Requires Lean 4.28.0 and Mathlib 4.28.0.

```sh
lake build
```

## References

- Kelly, P. J. (1942). "On isometric transformations". PhD thesis, University of Wisconsin.
- Ulam, S. M. (1960). *A Collection of Mathematical Problems*. Interscience.
- Bondy, J. A. (1991). "A graph reconstructor's manual". In *Surveys in Combinatorics*.
