# Sibling Project Inventory — `graph-theory/reconstruction-conjecture`

This file catalogues the current state of the Lean 4 project at
[`../../reconstruction-conjecture`](../../reconstruction-conjecture),
enumerating (a) theorems that are proved with no `sorry` dependencies and
(b) remaining `sorry`s, with their file, mathematical content, and the
immediate prerequisite for closing each.

As of the latest audit, the project builds on **Lean 4.28.0 /
Mathlib 4.28.0** (see
[`lean-toolchain`](../../reconstruction-conjecture/lean-toolchain) and
[`lakefile.toml`](../../reconstruction-conjecture/lakefile.toml)), and
grep for `sorry` across `Reconstruction/*.lean` returns exactly **two**
matches: `Basic.lean` and `CharPolyFull.lean`.
`SameDeck.numComponents_eq` (`ConnectedComponents.lean`) and
`SameDeck.iso_of_not_connected` (`Disconnected.lean`) are now **closed**;
`Matrix.newton_trace_charpoly` and `SameDeck.trace_adjMatrix_pow_eq` were
closed earlier.

## Module graph

```
Reconstruction/
  Defs.lean           ── SimpleGraph.deleteVert, SimpleGraph.SameDeck
  Basic.lean          ── SameDeck equivalence, reconstruction_conjecture (sorry)
  EdgeCount.lean      ── |E(G-v)| + deg(v) = |E(G)|; edge count reconstructible
  DegreeSequence.lean ── degreeMultiset; degree multiset reconstructible
  KellyLemma.lean     ── subgraphCount; Kelly counting identity; reconstructible
  KellyEdgeCount.lean ── Edge count via Kelly (as s(K₂,G) = |E(G)|)
  Regular.lean        ── Regularity-as-predicate is reconstructible
  ConnectedComponents.lean ── numComponents; SameDeck.connected; SameDeck.numComponents_eq (all proved)
  Disconnected.lean   ── isoSigmaComponents; SameDeck.iso_of_not_connected (proved)
  Trees.lean          ── IsTree is reconstructible
  Spectral.lean       ── charPoly; adjMatrix_induce; derivative formula;
                        SameDeck.charPoly_derivative_eq; charPoly_coeff_eq (k≥1)
  TraceReconstruction.lean ── SameDeck.trace_adjMatrix_pow_eq (proved)
  Newton.lean         ── newton_trace_charpoly (proved); cayley_hamilton_trace
  CharPolyFull.lean   ── charPoly_coeff_zero_eq (sorry); charPoly_eq (depends on sorry)
```

## What is proved (no `sorry`s in dependency closure)

Each item below is theorem-level and closed:

### `Defs.lean` + `Basic.lean`

- `SimpleGraph.deleteVert` — `abbrev` for `G.induce {w | w ≠ v}`. The
  `abbrev` lets Lean propagate `DecidableRel`/`Fintype` via `induce`.
- `SimpleGraph.SameDeck` — `∃ σ : V ≃ V, ∀ v, Nonempty (G.deleteVert v ≃g
  H.deleteVert (σ v))`.
- `SameDeck.refl`, `SameDeck.symm`, `SameDeck.trans` — `SameDeck` is an
  equivalence relation.

### `EdgeCount.lean`

- `deleteVert_edgeFinset_card_add_degree` — `|E(G − v)| + deg_G(v) = |E(G)|`.
- `sum_card_edgeFinset_deleteVert_add` —
  `Σ_v |E(G − v)| + 2 · |E(G)| = |V| · |E(G)|`.
- `SameDeck.card_edgeFinset_eq` — **Edge count is reconstructible.**

### `DegreeSequence.lean`

- `degree_eq_of_card_edgeFinset_eq_of_deleteVert_iso` — pointwise degree
  equality when edge counts and a card-iso agree.
- `SameDeck.degree_eq` — pointwise via the bijection σ.
- `SameDeck.degreeMultiset_eq` — **Degree multiset is reconstructible.**

### `KellyLemma.lean`

- `SimpleGraph.copyFinset`, `subgraphCount` — define the number of induced
  copies of `F` in `G`.
- `subgraphCount_eq_of_iso` — isomorphism invariance of `subgraphCount`.
- `subgraphCount_deleteVert` — bridge lemma: copies in `G − v` biject with
  `v`-avoiding copies in `G`.
- `subgraphCount_sum` — **Kelly's counting identity**
  `(n − k) · s(F,G) = Σ_v s(F, G − v)`.
- `SameDeck.subgraphCount_eq` — **Kelly's Lemma: subgraph count
  reconstructible** for `|V(F)| < |V(G)|`.

### `KellyEdgeCount.lean`

- `subgraphCount_completeGraph_two` — `s(K₂, G) = |E(G)|`.
- `SameDeck.card_edgeFinset_eq'` — edge count reconstructible as a corollary
  of Kelly's Lemma. (A second proof; the "primary" proof is in `EdgeCount`.)

### `Regular.lean`

- `SameDeck.isRegularOfDegree` — the **predicate** "is regular of
  degree `d`" is deck-reconstructible: same-deck graphs are either
  both regular of degree `d` or both not. This is a statement about
  *the regularity property*, not a reconstruction of regular graphs
  *as graphs*; the latter (showing a regular graph is isomorphic to
  its deck-mate) is not proved here and in general would require the
  full Reconstruction Conjecture restricted to the regular case.
  The proof proceeds by appealing to the reconstructible degree
  multiset plus existence of `d`.

### `Spectral.lean`

- `adjMatrix_induce` — adjacency matrix of an induced subgraph is the
  principal submatrix.
- `charPoly` — `G.charPoly R := (G.adjMatrix R).charpoly`.
- `charPoly_deleteVert` — `(G.deleteVert v).charPoly R` is the charpoly of
  the principal submatrix.
- `charPoly_eq_of_iso` — isomorphic graphs have equal charpolys.
- `derivative_charmatrix_apply_eq` / `_ne` — derivatives of charmatrix entries.
- `charmatrix_submatrix` — charmatrix and `submatrix` commute for injective
  reindexings.
- `derivative_det_charmatrix` — **derivative-of-determinant-of-charmatrix**
  identity: `(det M.charmatrix)' = Σ_k det (principal submatrix).`
  This is the linear-algebra core.
- `charPoly_derivative_eq_sum` — **graph-theoretic derivative formula**
  `φ'(G) = Σ_v φ(G − v)`.
- `SameDeck.charPoly_derivative_eq` — **charpoly derivative reconstructible**.
- `SameDeck.charPoly_coeff_eq` — **non-constant coefficients reconstructible**
  (for `R` an integral domain of characteristic zero; uses `Nat.cast_ne_zero`
  to divide through `n + 1`).

### `Newton.lean`

- `Matrix.cayley_hamilton_trace` —
  `Σ_{i=0}^{n} c_i · tr(A^i) = 0` via `Matrix.aeval_self_charpoly`.
- `Matrix.newton_trace_charpoly` — **Newton's identity at step `k`**:
  `tr(A^k) + Σ_{j=1}^{k−1} c_{N−j} · tr(A^{k−j}) + k · c_{N−k} = 0`
  for `1 ≤ k ≤ N`.
  **Closed** (confirmed 2026-04-16): both the `k < N` branch (via the
  adjugate / Faddeev–LeVerrier recurrence `adjCoeff_recurrence` and
  the explicit sum formula `adjCoeff_eq_sum`) and the `k = N` branch
  (direct reduction to Cayley–Hamilton) are proved.

### `TraceReconstruction.lean`

- `closedWalkCount k := tr(A^k)`.
- `SameDeck.trace_adjMatrix_pow_eq` —
  `tr(A_G^k) = tr(A_H^k)` for `k < |V|`. **Closed** (confirmed
  2026-04-16).

### `Trees.lean`

- `SameDeck.isTree` — **Tree property is reconstructible**
  (composes `connected` + `card_edgeFinset_eq` + `isTree_iff_connected_and_card`).

### `ConnectedComponents.lean`

- `numComponents G := Fintype.card G.ConnectedComponent`.
- `SameDeck.connected` — **Connectivity is reconstructible.** Uses
  `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`
  (Mathlib) plus degree-positivity.
- `SameDeck.numComponents_eq` — **Number of components is reconstructible.**
  (Closed 2026-04-17.) Three-way case split: (i) G connected → both
  have one component, (ii) G has isolated vertex → Option-lift bijection
  gives `c(G-v) = c(G)+1`, isolated-vertex existence transfers via
  `SameDeck.degree_eq`, (iii) no isolated vertex → extract a non-cut
  vertex from a component via `Connected.exists_connected_induce_...`
  applied to `ConnectedComponent.toSimpleGraph`, then biject components
  through the deleteVert-to-component map.

### `Disconnected.lean`

- `componentSigmaGraph G` — the Sigma-type graph on
  `Σ c : G.ConnectedComponent, c.supp` with component-internal adjacency.
- `componentSigmaEquiv G : V ≃ Σ c, c.supp` — the underlying vertex
  equivalence.
- `isoSigmaComponents G : G ≃g componentSigmaGraph G` — **every graph
  is iso to the disjoint union of its connected components.** (Proved
  2026-04-17.) This is the structural "assembly" tool for the
  disconnected-reconstruction proof.
- `componentSigmaGraphIsoOfComponentIso` and `isoOfComponentIsoEquiv` —
  **componentwise isomorphisms assemble to a global graph isomorphism.**
  (Proved 2026-04-30.) This closes the formal Sigma-assembly step once the
  component multiset has been matched.
- `SameDeck.iso_of_not_connected` — **disconnected graphs are
  reconstructible** (Kelly 1942). The proof obtains matching component
  isomorphism-class multiplicities from
  `SameDeck.componentCount_eq_components_of_not_connected`, then applies
  `isoOfComponentCountEq`.

## Remaining `sorry`s

Grep of `Reconstruction/*.lean` now returns two `sorry` matches, listed
below. S1 is the statement-level landmark for the open conjecture itself;
S6 is the remaining genuinely-open internal target. S2
(`numComponents_eq`) and S3 (`iso_of_not_connected`) are closed.

| # | Declaration | File:line (approx) | Difficulty |
|---|-------------|--------------------|-----------|
| S1 | `reconstruction_conjecture` | `Basic.lean` ~65 | — (open problem) |
| S6 | `SameDeck.charPoly_coeff_zero_eq` | `CharPolyFull.lean` ~66 | Medium (conditional on the now-closed trace reconstruction S5) |

### S1 — `reconstruction_conjecture`

The full conjecture statement. Unresolvable in the near term; we carry a
named `sorry` as a landmark so the rest of the code can build toward it.

### S3 — `SameDeck.iso_of_not_connected` — closed

This theorem is now proved in `Disconnected.lean`.

Mathematical content: Kelly's 1942 proof that disconnected graphs are
reconstructible. The formal proof uses `SimpleGraph.ConnectedComponent` to
index components, a descending triangular induction over component size to
recover component isomorphism-class multiplicities, and the Sigma-component
assembly theorem to build `Nonempty (G ≃g H)`.

Key closed declarations:

- `SameDeck.componentCount_eq_components_of_not_connected`
- `componentEquivOfComponentCountEq`
- `isoOfComponentCountEq`
- `SameDeck.iso_of_not_connected`

### S6 — `SameDeck.charPoly_coeff_zero_eq`

```
theorem SameDeck.charPoly_coeff_zero_eq (h : G.SameDeck H)
    (hV : 3 ≤ Fintype.card V) :
    (G.charPoly ℤ).coeff 0 = (H.charPoly ℤ).coeff 0 := by sorry
```

Mathematical content: the constant term of the characteristic polynomial
(which equals `(−1)^n · det(A_G)`) is deck-reconstructible.

Strategy via **Cayley–Hamilton trace identity**
(`cayley_hamilton_trace`):
`Σ_{i=0}^{n} c_i · tr(A^i) = 0`.
Then
`n · c_0 = − Σ_{i=1}^{n} c_i · tr(A^i)`,
and dividing by `n` (in characteristic 0 or over `ℤ` using
`Nat.cast_ne_zero`) recovers `c_0`. Each factor on the right is
reconstructible:

- `c_i` for `i = 1, …, n − 1` from `SameDeck.charPoly_coeff_eq`.
- `c_n = 1` (charpoly is monic).
- `tr(A^k)` for `k < n` from `SameDeck.trace_adjMatrix_pow_eq` (now
  closed).
- `tr(A^n)` — **the missing piece** — is not directly covered by Kelly's
  Lemma, which requires `|V(F)| < n`.

**Current scaffold:** `SameDeck.charPoly_coeff_zero_eq_of_trace_card_eq` is
proved. It formalizes the Cayley-Hamilton reduction: if the top trace
`tr(A^n)` agrees, then the constant coefficient agrees. `TopTrace.lean`
now proves the trace/closed-walk count identity, splits top-length closed
walks into proper-support and full-support pieces, expands the proper
piece over exact supports, and proves
`SameDeck.charPoly_coeff_zero_eq_of_support_counts_eq`.

Two routes in the literature to recover `tr(A^n)`:

- **Schwenk (1974)** via Sachs coefficients: `c_{n-k} = Σ_S (−1)^{c(S)} 2^{r(S)}`
  summed over "elementary spanning subgraphs" `S` of order `k`
  (unions of vertex-disjoint edges and cycles). For `k < n` each term is a
  subgraph count recoverable by Kelly; for `k = n` the "elementary spanning
  subgraphs" are exactly those with no isolated vertex, which in the
  disconnected case can still be bounded via component sizes.
- **Walk decomposition**: closed walks of length `n` decompose over their
  vertex supports; proper-support walks are now formally expressed as an
  exact-support sum, while full-support walks form the Hamilton-cycle sector
  targeted by the Kocay campaign.

**Prerequisites to close:** the Sachs / walk argument to cover `tr(A^n)`;
the trace reconstruction for `k < n` (S5) is already closed.

Once S6 is closed, `SameDeck.charPoly_eq` in the same file goes from
`sorry`-dependent to fully closed.

## Action-item summary

Immediate (next work-cycle):

1. Close S6 via Sachs or walk decomposition.

Medium (following cycle):

2. Bundle the above into a headline theorem
   `SameDeck.charPoly_eq_and_disconnected_reconstructible` and write
   the project README to reflect the new landmarks.

Completed:

- S2 (`numComponents_eq`) — closed.
- `isoSigmaComponents` structural scaffold — added.
- S3 (`iso_of_not_connected`) — closed.

## Cross-links

- Mathematical context for each `sorry`:
  [`../invariants/index.md`](../invariants/index.md),
  [`../attacks/spectral-approach.md`](../attacks/spectral-approach.md) (if present),
  [`../state-of-the-art/graph-classes.md`](../state-of-the-art/graph-classes.md).
- Mathlib API prerequisites: [`mathlib-api.md`](mathlib-api.md).
- 1-page sketches for the next targets: [`next-targets.md`](next-targets.md).

[kelly57]: ../sources.md#kelly57
[tutte79]: ../sources.md#tutte79
[schwenk74]: ../sources.md#schwenk74
[schwenk79]: ../sources.md#schwenk79
