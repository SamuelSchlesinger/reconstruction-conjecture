# Mathlib API Survey — Graph Reconstruction

This document audits the Mathlib 4 API relevant to the reconstruction
conjecture. Declarations are cited with their module path; commit-pinned
existence has been checked against the Mathlib tree at the project's pinned
`v4.28.0`.

## Core graph API

### `SimpleGraph` and constructors

- `SimpleGraph V` — `Mathlib.Combinatorics.SimpleGraph.Basic`. Simple graph
  on an arbitrary vertex type `V`.
- `SimpleGraph.Adj G v w : Prop` — adjacency predicate.
- `SimpleGraph.top`, `SimpleGraph.bot`, `SimpleGraph.completeGraph V` — the
  usual constants.

### Homomorphisms, embeddings, isomorphisms

- `SimpleGraph.Hom G G'` — adjacency-preserving function (`G →g G'`).
- `SimpleGraph.Embedding G G'` — injective hom (`G ↪g G'`).
- `SimpleGraph.Iso G G'` — bijection on vertices preserving adjacency
  (`G ≃g G'`). *Location:* `Mathlib.Combinatorics.SimpleGraph.Maps`,
  `abbrev Iso`.
- `Iso.refl`, `Iso.symm`, `Iso.trans`, `Iso.toEquiv`, `Iso.map_rel_iff` —
  standard lemmas.
- `Iso.card_edgeFinset_eq` — graph isomorphisms preserve edge count.
  *Location:* `Mathlib.Combinatorics.SimpleGraph.Finite`.
- `Iso.connected_iff` — isomorphism preserves connectivity.

### Vertex / edge operations

- `SimpleGraph.comap f G : SimpleGraph V`, where `f : V → W` and
  `G : SimpleGraph W`. *Location:* `Mathlib.Combinatorics.SimpleGraph.Maps`.
- `SimpleGraph.map f G : SimpleGraph W`, where `f : V ↪ W`.
- `SimpleGraph.induce s G : SimpleGraph s` — the induced subgraph on
  `s : Set V`. Declared as `abbrev`, so instance propagation works.
  *Location:* `Mathlib.Combinatorics.SimpleGraph.Maps`, line 215
  (`abbrev induce`).
- `induce_adj` — `(G.induce s).Adj u v ↔ G.Adj u v` for `u v : s`.
- `SimpleGraph.induceHom`, `induceHomOfLE`, `induceUnivIso` — homomorphisms
  relating induced subgraphs.
- `SimpleGraph.deleteEdges G s : SimpleGraph V` for `s : Set (Sym2 V)`.
  *Location:* `Mathlib.Combinatorics.SimpleGraph.DeleteEdges`.

### Vertex deletion (gap)

Mathlib has `SimpleGraph.Subgraph.deleteVerts` (`Subgraph G → Set V →
Subgraph G`) in
`Mathlib.Combinatorics.SimpleGraph.Subgraph` (line 1284), but **there is
no ambient-graph `deleteVert` on `SimpleGraph` itself**. The sibling
project's `Defs.lean` supplies

```lean
abbrev SimpleGraph.deleteVert (G : SimpleGraph V) (v : V) :
    SimpleGraph {w : V // w ≠ v} :=
  G.induce {w | w ≠ v}
```

which is the correct formulation for deck-style arguments (vertex type
changes to the subtype `{w // w ≠ v}`). This abbreviation is a clean
candidate for upstreaming to
`Mathlib.Combinatorics.SimpleGraph.Maps` as `SimpleGraph.deleteVert`.

### Subgraph / spanning coe

- `SimpleGraph.Subgraph G` — pair `(V' ⊆ V, E' ⊆ E|_{V'})`.
  *Location:* `Mathlib.Combinatorics.SimpleGraph.Subgraph`.
- `Subgraph.spanningCoe G' : SimpleGraph V` — the `V`-indexed simple graph
  underlying the subgraph (line 168).
- `Subgraph.coe G' : SimpleGraph G'.verts` — the subgraph as a genuine
  simple graph on its vertex set.
- `spanningCoe_top`, `spanningCoe_bot`, `spanningCoe_deleteEdges`,
  `spanningCoe_le_of_le` — expected lemmas.

### Counting copies

- `SimpleGraph.copyCount G H : ℕ` (`Mathlib.Combinatorics.SimpleGraph.Copy`,
  line 481) — number of unlabelled copies of `H` in `G`.
- `SimpleGraph.Copy H G` — the type of *copies*: an `H ↪g G`
  modulo `H`-automorphisms (roughly).
- `labelledCopyCount` — labelled variant; a.k.a. Mathlib's version of
  `s(F,G)` but in the `Hom` / `↪g` direction rather than the induced-subset
  direction.
- `copyCount_pos`, `copyCount_eq_zero`, `copyCount_le_labelledCopyCount` —
  key lemmas.

**Gap for reconstruction.** Mathlib's `copyCount` counts copies as
*subgraphs* via `Copy.toSubgraph`, not as *induced* subgraphs. Kelly's
Lemma concerns **induced** subgraph counts (`s(F,G)` = number of
`k`-subsets `S ⊆ V(G)` with `G[S] ≅ F`), which is what the sibling
project's `subgraphCount` measures. The two agree only when `F` is
*closed* under induction (e.g., for `F = K_k`) — in general they differ.
A bridge lemma `subgraphCount_eq_copyCount_of_induced_closed` would be
valuable; so would upstreaming `subgraphCount` itself to Mathlib.

### Degree / edge counts

- `SimpleGraph.degree`, `SimpleGraph.edgeFinset`, `SimpleGraph.incidenceFinset`.
- `SimpleGraph.sum_degrees_eq_twice_card_edges` — handshaking lemma.
  *Location:* `Mathlib.Combinatorics.SimpleGraph.DegreeSum`.
- `SimpleGraph.card_incidenceFinset_eq_degree`.
- `SimpleGraph.map_edgeFinset_induce` — used in the sibling project's
  edge-count proof.

### Connectivity

- `SimpleGraph.Reachable`, `SimpleGraph.Connected`, `SimpleGraph.Preconnected`.
  *Location:* `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`.
- `SimpleGraph.ConnectedComponent` (line 384) — `Quot G.Reachable`.
- `SimpleGraph.connectedComponentMk` — quotient map.
- `ConnectedComponent.map` — functoriality under homomorphisms.
- `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial` —
  *every connected graph on ≥ 2 vertices has a non-cut vertex*.
  *Location:* `Mathlib.Combinatorics.SimpleGraph.Acyclic`, line 561.
- `SimpleGraph.Walk` and `IsPath` machinery — standard.
- `SimpleGraph.IsTree`, `isTree_iff_connected_and_card`,
  `IsTree.card_edgeFinset` — *Location:*
  `Mathlib.Combinatorics.SimpleGraph.Acyclic`.

### Matrix side

- `SimpleGraph.adjMatrix α` (*Location:*
  `Mathlib.Combinatorics.SimpleGraph.AdjMatrix`, line 182) — adjacency
  matrix over a type `α` with `Zero` and `One`.
- `SimpleGraph.trace_adjMatrix` — trace is 0 (no self-loops).
- `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` — walk-counting
  interpretation of `A^n`.
- `SimpleGraph.lapMatrix` — graph Laplacian
  (`Mathlib.Combinatorics.SimpleGraph.LapMatrix`); supports the
  Matrix-Tree theorem (present in Mathlib).
- `Matrix.charmatrix M` — `X · I − M` as a polynomial matrix.
  *Location:* `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`.
- `Matrix.charpoly M := det M.charmatrix` — characteristic polynomial
  (line 132 of `Charpoly/Basic.lean`).
- `Matrix.charpoly_reindex` (line 168) — permuting indices preserves
  `charpoly`. This powers `SimpleGraph.charPoly_eq_of_iso` in the sibling
  project.
- `Matrix.charpoly_monic`, `Matrix.charpoly_natDegree_eq_dim`,
  `Matrix.charpoly_degree_eq_dim`. *Location:*
  `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`.
- `Matrix.aeval_self_charpoly` (line 211 of `Charpoly/Basic.lean`) —
  **Cayley–Hamilton**: `aeval M M.charpoly = 0`.
- `Matrix.adjugate`, `Matrix.mul_adjugate` — the adjugate and its defining
  identity `M · adjugate M = det M · I`.
- `Matrix.submatrix`, `Matrix.submatrix_apply` — index restriction /
  reindexing. Used heavily for principal submatrices in `Spectral.lean`
  and `Newton.lean`.
- `Matrix.trace`, `Matrix.trace_sum`, `Matrix.trace_smul`.
- `Polynomial.derivative`, `Polynomial.coeff_derivative`,
  `Polynomial.derivative_prod_finset`. *Location:*
  `Mathlib.Algebra.Polynomial.Derivative`.

### Equivalences, permutations

- `Equiv.Perm.subtypePerm`, `Equiv.Perm.ofSubtype`,
  `Equiv.Perm.ofSubtype_subtypePerm`, `Equiv.Perm.subtypePerm_ofSubtype` —
  used to biject `{σ ∈ Perm n | σ k = k}` with `Perm {j : n // j ≠ k}`.
  Central to the derivative-of-determinant identity in
  `Spectral.derivative_det_charmatrix`.
- `Equiv.sum_comp` — reindexing `∑ v, f v = ∑ v, f (σ v)` for `σ : V ≃ V`.

### Double-counting / bipartite sum

- `Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow` —
  double-counting identity used in `subgraphCount_sum`.
  *Location:* `Mathlib.Combinatorics.Enumerative.DoubleCounting`.

## Confirmed gaps

The following are either absent from Mathlib (under any name we have
searched for) or exist only in a form that needs a bridge:

1. **Ambient-graph `deleteVert`.** Mathlib has
   `Subgraph.deleteVerts`, but not the subtype-valued `deleteVert` used
   in the sibling project. An upstream PR adding
   `SimpleGraph.deleteVert` to
   `Mathlib.Combinatorics.SimpleGraph.Maps` would be universally useful.
2. **Induced subgraph count.** `SimpleGraph.copyCount` is close but
   counts *subgraphs* via `Copy`, not *induced* subgraphs. Kelly's Lemma
   needs the latter. Either add an `induceCount` / `inducedSubgraphCount`
   declaration, or add a `isInduced` predicate on `Copy` and a filtering
   lemma.
3. **Newton's identities / Faddeev–LeVerrier.** Entirely absent from
   Mathlib as of `v4.28.0` (verify). The sibling project's
   `Newton.lean` supplies a clean proof (~460 lines) that could be
   upstreamed as-is with minor renaming to
   `Mathlib.LinearAlgebra.Matrix.Charpoly.Newton`.
4. **Derivative formula for charpoly.**
   `Matrix.derivative_charpoly_eq_sum_submatrix_charpoly` (modulo name)
   is not in Mathlib. This is
   `SimpleGraph.derivative_det_charmatrix` in the sibling project; it
   has broader interest than just reconstruction (Jacobi's formula for
   `d/dt det(tI - M)`).
5. **Multiset deck / deck type.** There is no `SimpleGraph.deck`
   declaration in Mathlib. Declaring it in Mathlib-acceptable form
   requires quotienting subgraphs by isomorphism, which in turn wants an
   `IsomorphismClass` type (not present for `SimpleGraph` — verify;
   might exist in `Mathlib.CategoryTheory` under a different name).
6. **Sachs coefficient theorem.**
   `charpoly.coeff (n − k) = Σ ε(S) · 2^{cyc(S)}` summed over elementary
   subgraphs `S` of size `k`. Absent. Needed to close S6 via Schwenk's
   approach.
7. **Isomorphism between "three `SameDeck` definitions".** Hypomorphism
   via a fixed bijection, multiset equality, and card-multiset equality
   are three `SameDeck`-style statements that coincide for vertex-deck
   but the equivalence is not formalized.

## Near-gaps (things the sibling project has but Mathlib should)

Each of the following appears only in
[`graph-theory/reconstruction-conjecture`](../../reconstruction-conjecture)
and is general-purpose enough to live in Mathlib:

- `SimpleGraph.deleteVert` (Defs.lean).
- `SimpleGraph.charPoly R := (G.adjMatrix R).charpoly` — a 1-liner; only
  present in `Spectral.lean`.
- `SimpleGraph.adjMatrix_induce` — adjacency matrix of induced subgraph
  is the principal submatrix. General Mathlib-style lemma.
- `SimpleGraph.charPoly_deleteVert` — specialisation of the above.
- `SimpleGraph.charPoly_eq_of_iso` — isomorphic graphs have equal charpolys.
  **Clean upstreaming target.**
- `Matrix.derivative_det_charmatrix` (currently in `SimpleGraph`
  namespace for historical reasons).
- `Matrix.newton_trace_charpoly`, `Matrix.cayley_hamilton_trace`.
- `SimpleGraph.subgraphCount`, `copyFinset`, `subgraphCount_sum`,
  `subgraphCount_eq_of_iso`, `subgraphCount_deleteVert` — **Kelly's Lemma
  infrastructure**.
- `SimpleGraph.degreeMultiset` — the multiset of vertex degrees.

A single Mathlib PR bundling these would be a meaningful contribution and
would also *remove the private sibling project's current dependence on
its own home-grown copies*.

## Cross-links

- Current sibling-project state: [`sibling-project.md`](sibling-project.md).
- Ranked next-step targets: [`next-targets.md`](next-targets.md).
- Invariant-by-invariant math status:
  [`../invariants/index.md`](../invariants/index.md).

Full bibliographic details live in
[`../sources.md`](../sources.md). The Mathlib declarations above are
cited by their module path in the Mathlib source tree; to audit, run
`grep -rn 'theorem ‹name›' $(lake env) Mathlib/...` against the pinned
`v4.28.0` tree.
