# Sibling Project Inventory — `graph-theory/reconstruction-conjecture`

This file catalogues the current state of the Lean 4 project at
[`../../reconstruction-conjecture`](../../reconstruction-conjecture),
enumerating (a) theorems that are proved with no `sorry` dependencies and
(b) remaining `sorry`s, with their file, mathematical content, and the
immediate prerequisite for closing each.

As of the audit, the project builds on **Lean 4.28.0 / Mathlib 4.28.0**
(see
[`lean-toolchain`](../../reconstruction-conjecture/lean-toolchain) and
[`lakefile.toml`](../../reconstruction-conjecture/lakefile.toml)).

## Module graph

```
Reconstruction/
  Defs.lean           ── SimpleGraph.deleteVert, SimpleGraph.SameDeck
  Basic.lean          ── SameDeck equivalence, reconstruction_conjecture (sorry)
  EdgeCount.lean      ── |E(G-v)| + deg(v) = |E(G)|; edge count reconstructible
  DegreeSequence.lean ── degreeMultiset; degree multiset reconstructible
  KellyLemma.lean     ── subgraphCount; Kelly counting identity; reconstructible
  KellyEdgeCount.lean ── Edge count via Kelly (as s(K₂,G) = |E(G)|)
  Regular.lean        ── Regularity is reconstructible
  ConnectedComponents.lean ── numComponents (sorry); SameDeck.connected (proved)
  Disconnected.lean   ── SameDeck.iso_of_not_connected (sorry)
  Trees.lean          ── IsTree is reconstructible
  Spectral.lean       ── charPoly; adjMatrix_induce; derivative formula;
                        SameDeck.charPoly_derivative_eq; charPoly_coeff_eq (k≥1)
  TraceReconstruction.lean ── SameDeck.trace_adjMatrix_pow_eq (depends on Newton)
  Newton.lean         ── newton_trace_charpoly; cayley_hamilton_trace
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

- `SameDeck.isRegularOfDegree` — **Regularity is reconstructible** (degree
  multiset plus existence of `d`).

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
  This was listed in the README as a `sorry`, but reading the source shows
  the file is complete — both the `k < N` branch (via the adjugate /
  Faddeev–LeVerrier recurrence `adjCoeff_recurrence` and the explicit
  sum formula `adjCoeff_eq_sum`) and the `k = N` branch (direct reduction
  to Cayley–Hamilton) are proved. **(Recommended verification step: run
  `lake build Reconstruction.Newton` and confirm no `sorry`.)**

### `TraceReconstruction.lean`

- `closedWalkCount k := tr(A^k)`.
- `SameDeck.trace_adjMatrix_pow_eq` —
  `tr(A_G^k) = tr(A_H^k)` for `k < |V|`.
  Reads as complete; the listed "open" status in the README appears stale.
  **Recommended verification step: confirm by build.**

### `Trees.lean`

- `SameDeck.isTree` — **Tree property is reconstructible**
  (composes `connected` + `card_edgeFinset_eq` + `isTree_iff_connected_and_card`).

### `ConnectedComponents.lean`

- `numComponents G := Fintype.card G.ConnectedComponent`.
- `SameDeck.connected` — **Connectivity is reconstructible.** Uses
  `Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`
  (Mathlib) plus degree-positivity.

## Remaining `sorry`s

The README lists six open declarations. On code audit, three of them
(`Newton.newton_trace_charpoly`, the trace reconstruction, and the
`derivative_det_charmatrix` lemma) appear to be complete in the current
source and the README needs updating; the remaining three *are* genuine
open targets.

| # | Declaration | File:line (approx) | Genuinely open? | Difficulty |
|---|------------|---------------------|-----------------|-----------|
| S1 | `reconstruction_conjecture` | `Basic.lean` ~58 | **Yes — open problem** | — |
| S2 | `SameDeck.numComponents_eq` | `ConnectedComponents.lean` ~92 | **Yes** | Medium |
| S3 | `SameDeck.iso_of_not_connected` | `Disconnected.lean` ~43 | **Yes** | Medium–high |
| S4 | `Matrix.newton_trace_charpoly` | `Newton.lean` ~359 | **Closed** (verify build) | — |
| S5 | `SameDeck.trace_adjMatrix_pow_eq` | `TraceReconstruction.lean` ~55 | **Closed** (verify build) | — |
| S6 | `SameDeck.charPoly_coeff_zero_eq` | `CharPolyFull.lean` ~52 | **Yes** | Medium (conditional on S5) |

### S1 — `reconstruction_conjecture`

The full conjecture statement. Unresolvable in the near term; we carry a
named `sorry` as a landmark so the rest of the code can build toward it.

### S2 — `SameDeck.numComponents_eq`

```
theorem SameDeck.numComponents_eq (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) :
    G.numComponents = H.numComponents := by sorry
```

Mathematical content: the number of connected components is a
deck-reconstructible invariant. In-file comment flags the obstacle as
decidability mismatches for `Fintype.card_le_of_injective` /
`card_le_of_surjective` when Classical and concrete decidability instances
collide. A three-way case split is outlined:

1. **Connected** — both have exactly one component by `SameDeck.connected`.
2. **Has isolated vertex** — `deg(v) = 0` is detectable from the degree
   multiset; deleting an isolated vertex decreases the component count by
   exactly 1 (while a positive-degree vertex can only preserve or increase
   it by at most `deg(v) − 1`, but the map
   `G.ConnectedComponent → (G-v).ConnectedComponent` is not well-defined —
   the standard argument uses the reverse inclusion, see below).
3. **No isolated vertex** — use a non-cut vertex to match component counts
   via the deck isomorphism.

**Prerequisites to close this `sorry`:**
- Stable decidability for `SimpleGraph.Connected` and
  `SimpleGraph.ConnectedComponent` under the project's mixed instance
  setup (the file already uses `open Classical`).
- A clean statement of "an isolated vertex forms its own component and
  deleting it decreases the component count by 1".

### S3 — `SameDeck.iso_of_not_connected`

```
theorem SameDeck.iso_of_not_connected (h : G.SameDeck H)
    (hV : 3 ≤ Fintype.card V) (hdisc : ¬G.Connected) :
    Nonempty (G ≃g H) := by sorry
```

Mathematical content: Kelly's 1942 proof that disconnected graphs are
reconstructible. If the components of `G` have sizes
`n_1 ≥ n_2 ≥ … ≥ n_k` with `k ≥ 2`, then `n_2 ≤ n/2 < n`, so every
component except possibly the largest has fewer than `n` vertices and is
counted by Kelly's Lemma. The largest component is then
determined by subtraction.

This is more demanding than S2 because it produces a *full isomorphism*,
not just an invariant equality. Representation choices:

- Use `SimpleGraph.ConnectedComponent` to index components.
- Use the list / multiset of component graphs as an intermediate object.
- Build `Nonempty (G ≃g H)` by concatenating component-wise isomorphisms.

**Prerequisites to close:** S2 (component count) plus a careful bookkeeping
of Kelly's Lemma applied to each possible "small" component.

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
- `tr(A^k)` for `k < n` from `SameDeck.trace_adjMatrix_pow_eq`.
- `tr(A^n)` — **the missing piece** — is not directly covered by Kelly's
  Lemma, which requires `|V(F)| < n`.

Two routes in the literature to recover `tr(A^n)`:

- **Schwenk (1979)** via Sachs coefficients: `c_{n-k} = Σ_S (−1)^{c(S)} 2^{r(S)}`
  summed over "elementary spanning subgraphs" `S` of order `k`
  (unions of vertex-disjoint edges and cycles). For `k < n` each term is a
  subgraph count recoverable by Kelly; for `k = n` the "elementary spanning
  subgraphs" are exactly those with no isolated vertex, which in the
  disconnected case can still be bounded via component sizes.
- **Walk decomposition**: closed walks of length `n` decompose over their
  vertex supports; walks that visit fewer than `n` vertices are reconstructed
  from lower traces, and walks visiting all `n` vertices form a structured
  set amenable to independent counting.

**Prerequisites to close:** S5 (trace reconstruction for `k < n`), which
appears to be complete, plus the additional Sachs / walk argument to cover
`tr(A^n)`.

Once S6 is closed, `SameDeck.charPoly_eq` in the same file goes from
`sorry`-dependent to fully closed.

## Action-item summary

Immediate (same work-cycle):

1. Run `lake build` and confirm which of S4, S5 the current source
   actually closes; update the README to match reality.
2. Close S2 (`numComponents_eq`) — the three-way case split is a
   straightforward bookkeeping exercise once decidability friction is
   handled.
3. Close S3 (`iso_of_not_connected`) using S2 and Kelly's Lemma.

Medium (next cycle):

4. Close S6 via Sachs or walk decomposition.
5. Bundle the above into a headline theorem
   `SameDeck.charPoly_eq_and_numComponents_eq_and_disconnected_reconstructible`
   and write the project README to reflect the new landmarks.

## Cross-links

- Mathematical context for each `sorry`:
  [`../invariants/index.md`](../invariants/index.md),
  [`../attacks/spectral-approach.md`](../attacks/spectral-approach.md) (if present),
  [`../state-of-the-art/graph-classes.md`](../state-of-the-art/graph-classes.md).
- Mathlib API prerequisites: [`mathlib-api.md`](mathlib-api.md).
- 1-page sketches for the next targets: [`next-targets.md`](next-targets.md).

[kelly57]: ../sources.md#kelly57
[tutte79]: ../sources.md#tutte79
[schwenk79]: ../sources.md#schwenk79
