# Next-Step Formalization Targets — 1-Page Sketches

Five concrete targets that a developer can start from, ranked by a combined
*mathematical payoff × formalization tractability* score. Each sketch is
intended to fit in a single Lean work cycle (rough upper bound: 500–1500
lines of Lean, excluding Mathlib prerequisites).

See [`index.md`](index.md) for the overall context and target table,
[`sibling-project.md`](sibling-project.md) for the sibling project's
current `sorry` inventory, and [`mathlib-api.md`](mathlib-api.md) for
API details.

---

## #A — Close `SameDeck.charPoly_coeff_zero_eq`

**Payoff.** Upgrades the headline spectral result from
"non-constant charpoly coefficients are reconstructible" to "the full
characteristic polynomial (and hence the full adjacency spectrum) is
reconstructible" — i.e., Tutte's 1979 theorem, fully formalized.

**File.** `Reconstruction/CharPolyFull.lean`.

**Difficulty.** Medium; ~400–800 lines depending on which route we take.

**Prereqs already in repo.**
- `Matrix.cayley_hamilton_trace`
  ([`Newton.lean`](../../reconstruction-conjecture/Reconstruction/Newton.lean)).
- `SameDeck.charPoly_coeff_eq` (k ≥ 1)
  ([`Spectral.lean`](../../reconstruction-conjecture/Reconstruction/Spectral.lean)).
- `SameDeck.trace_adjMatrix_pow_eq` for `k < |V|`
  ([`TraceReconstruction.lean`](../../reconstruction-conjecture/Reconstruction/TraceReconstruction.lean)).

**Mathematical sketch.** Cayley–Hamilton gives
`Σ_{i=0}^{n} c_i · tr(A^i) = 0`.
Extract the `i = 0` term (`c_0 · n`) and rearrange:
`n · c_0 = − Σ_{i=1}^{n} c_i · tr(A^i)`.

Every term on the right has at least one of `c_i` (`1 ≤ i ≤ n-1`, all
reconstructible) or `tr(A^i)` (`1 ≤ i ≤ n-1`, reconstructible); the single
problem term is `c_n · tr(A^n) = 1 · tr(A^n)` (since `c_n = 1`).

**Route 1: Sachs coefficient formula.**
`c_{n-k} = Σ_S (−1)^{p(S)} · 2^{c(S)}`,
where `S` ranges over "elementary spanning subgraphs" of `G` on `k`
vertices — disjoint unions of edges and cycles — `p(S)` is the number of
components of `S`, and `c(S)` is the number of cycle components. For
`k < n` each such `S` is a proper induced subgraph pattern counted by
Kelly's Lemma, so `c_{n-k}` is reconstructible — *but we already have this
from the derivative formula*. The novelty at `k = n`: elementary
*spanning* subgraphs of `G` have exactly `n` vertices, so Kelly's Lemma
does not apply directly. **However,** an elementary spanning subgraph on
`n` vertices is a disjoint union of edges / cycles covering all of `V`;
its *multiset of component sizes* lies in a controlled set (all sizes ≥ 1
summing to `n`, with each size-1 component impossible — edges and cycles
have size ≥ 2). The count of such `S` with a prescribed component-size
multiset is a *Kelly-style count over the component structure*, where
each component can be identified as an induced subgraph of `G` of size
`< n` (since we have `≥ 2` components in the non-trivial cases). Assemble
by cases on "number of spanning-cycle components".

**Route 2: walk decomposition.**
`tr(A^n) = Σ_v |closed walks of length n at v|`. Partition walks by their
vertex support `S ⊆ V`. For `|S| < n`, the contribution is a sum over
induced subgraphs and is reconstructible. For `|S| = n` (walks that visit
every vertex), bound by a combinatorial argument involving
`tr(A^{n-1}) · max deg`. This route is messier but more elementary than
Sachs.

**Lean plan (Route 1 recommended).**

1. Define `SimpleGraph.elementarySubgraphCount G k : ℕ` — the number of
   elementary subgraphs of order `k`.
2. Prove `(G.charPoly ℤ).coeff (n - k) = Σ_S (−1)^{p(S)} 2^{c(S)}` for a
   Sachs-style sum; this is a significant algebraic result in its own
   right and may deserve its own file (`Reconstruction/Sachs.lean`).
3. Prove that `elementarySubgraphCount G k` is reconstructible for
   `k ≤ n`, using Kelly's Lemma plus induction on component count.
4. Derive `SameDeck.charPoly_coeff_zero_eq` as the `k = n` case.

**Risk.** The Sachs formula itself is a non-trivial formalization;
step 2 alone is ~600 lines. Route 2 may be shorter but is less
structurally clean.

**Verification.** Build succeeds; `charPoly_eq` is fully closed (its only
`sorry` was `charPoly_coeff_zero_eq`).

---

## #B — Close `SameDeck.numComponents_eq`

**Payoff.** Unlocks the tree-case result (already proved modulo this) and
`SameDeck.iso_of_not_connected` (target #C). Also the obvious first
"graph-theory-side" reconstructibility lemma left unclosed.

**File.** `Reconstruction/ConnectedComponents.lean`.

**Difficulty.** Medium; ~200–400 lines.

**Prereqs in repo.**
- `SameDeck.connected`
  ([`ConnectedComponents.lean`](../../reconstruction-conjecture/Reconstruction/ConnectedComponents.lean)).
- `SameDeck.degreeMultiset_eq`
  ([`DegreeSequence.lean`](../../reconstruction-conjecture/Reconstruction/DegreeSequence.lean)).

**Mathematical sketch.**

**Case 1 — both connected.** By `SameDeck.connected`,
`H.Connected`, so `numComponents G = 1 = numComponents H`.

**Case 2 — `G` has an isolated vertex.** The degree multiset is
reconstructible, so `H` also has a vertex of degree 0. Let `v` be
isolated in `G`; then `G − v` has exactly `numComponents G − 1`
components. Card isomorphism `G − v ≅ H − σv`, so
`numComponents (H − σv) = numComponents G − 1`. Since `σv` has degree 0
in `H` (degrees transfer along σ),
`numComponents H = numComponents (H − σv) + 1 = numComponents G`.

**Case 3 — no isolated vertices in `G`.** Choose a non-cut vertex
`w` in some component of `G` (exists because every component has ≥ 2
vertices — no isolated vertex — and every connected graph on ≥ 2
vertices has a non-cut vertex,
`Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`).
Then `numComponents (G − w) = numComponents G`. Transfer via the deck
isomorphism: `numComponents (H − σw) = numComponents (G − w) =
numComponents G`. Now argue `numComponents H ≤ numComponents (H − σw)`
(deleting a vertex can only merge or split components in a controlled
way; specifically, the inclusion
`H.ConnectedComponent ← (H − σw).ConnectedComponent ∪ {σw}` is
surjective, giving the inequality). Symmetrically,
`numComponents G ≤ numComponents H`.

**Lean plan.**

1. Develop three helper lemmas:
   - `numComponents_deleteVert_isolated`:
     `deg v = 0 → numComponents (G − v) = numComponents G − 1`.
   - `numComponents_deleteVert_le`:
     `numComponents G ≤ numComponents (G − v) + 1`.
   - `numComponents_deleteVert_non_cut`:
     for `v` a non-cut vertex of its component,
     `numComponents (G − v) = numComponents G`.
2. Case split on (connected / has isolated vertex / no isolated vertex)
   using `SameDeck.connected` and the reconstructible degree multiset.
3. Conclude the theorem.

**Risk.** The in-file TODO notes decidability friction with
`Fintype.card_le_of_injective` / `_of_surjective`. Resolve by
`haveI := Classical.decEq V; haveI := Classical.decPred G.Connected`
inside the proof, or by upstreaming a Classical-friendly version of
the surjection lemma.

**Verification.** Tree case (`SameDeck.isTree`) continues to build;
stop passing through `SameDeck.connected` specifically and start using
`numComponents_eq` for cleaner proofs.

---

## #C — Close `SameDeck.iso_of_not_connected` (Kelly 1942)

**Payoff.** A full-reconstruction result — produces `Nonempty (G ≃g H)`,
not just an invariant equality. Kelly's 1942 original theorem. A
headline achievement for the project.

**File.** `Reconstruction/Disconnected.lean`.

**Difficulty.** Medium–high; ~800–1200 lines. The jump from invariant
equality to "and therefore isomorphism" is where the work lives.

**Prereqs.**
- **#B** closed (`numComponents_eq`).
- `SameDeck.subgraphCount_eq` (Kelly's Lemma, proved in
  [`KellyLemma.lean`](../../reconstruction-conjecture/Reconstruction/KellyLemma.lean)).
- `SimpleGraph.ConnectedComponent` and the quotient API.

**Mathematical sketch.** Suppose `G` has components of sizes
`n_1 ≥ n_2 ≥ … ≥ n_k` with `k ≥ 2`. Since the sum is `n` and there are
`≥ 2` components, `n_2 ≤ n/2 ≤ n/2 < n`, so every component *except
possibly the largest* has fewer than `n` vertices.

For each connected graph `F` on `< n` vertices, Kelly's Lemma gives
`subgraphCount F G = subgraphCount F H`. In particular, if `F` is the
actual shape of one of `G`'s non-largest components,
`H` has the same number of *induced* copies of `F` — which, for a
*connected* `F`, correspond to connected components of the graph
containing them (not just induced subgraphs). A concrete technical step:

- **Lemma.** If `F` is a connected graph on `k < n` vertices and `F`
  appears as a connected component of `G`, the number of induced copies
  of `F` in `G` equals the number of times `F` occurs as a connected
  component of `G`, plus a correction of zero because any induced copy
  of a connected `F` that lies inside a component of size > `|V(F)|`
  would require the copy to extend to its full component — which fails
  for `F` connected maximal. (Make this precise.)

After counting each small component on both sides, the *multiset of small
components* agrees. The remaining vertices in `G` and `H` form the
"largest-component" sector, which is `G`'s one remaining component (and
similarly for `H`), and has the same size on both sides. But we do **not
yet know** the largest component is reconstructible — this is where the
argument closes: for `k ≥ 2`, `n_1 ≤ n - n_2 < n`, so the largest component
also has `< n` vertices and is counted by Kelly's Lemma too.

In particular, *all* components are counted by Kelly's Lemma in the
disconnected case. Build `G ≃g H` by matching component-wise
isomorphisms.

**Lean plan.**

1. Introduce `SimpleGraph.componentMultiset G : Multiset (Σ' (s : Set V),
   SimpleGraph s)` quotiented by `Iso`. (A `Multiset (ConnectedGraph)` if
   such a type exists in Mathlib; otherwise use `Sigma` + explicit
   isomorphism quotient.)
2. Prove `SameDeck → componentMultiset G = componentMultiset H` (modulo
   iso) via Kelly applied component-by-component.
3. Assemble `G ≃g H` from a component-wise matching:
   choose a bijection between component sets preserving isomorphism type,
   then glue the component-level `≃g` maps into a single graph iso.

**Risk.** Step 3 (assembling the iso) is the delicate part. Mathlib has
`SimpleGraph.sum` / `Sum` operations (see
`Mathlib.Combinatorics.SimpleGraph.Sum`) that may help; otherwise build
the bijection by hand on the component sigma-type.

**Verification.** `SameDeck.iso_of_not_connected` builds; downstream
`Disconnected.md` research document updated to reflect the new formal
status.

---

## #D — Edge-reconstruction API and Lovász's bound

**Payoff.** Opens an entirely new direction. Edge reconstruction is
a more tractable variant than vertex reconstruction, and multiple
density-threshold results (Lovász 1972, Müller 1977, Nash-Williams 1978)
have elementary proofs that would make clean Lean content. Mathematically
novel for formalization as far as we can tell.

**File(s).** `Reconstruction/EdgeDeck.lean` (new),
`Reconstruction/LovaszBound.lean` (new).

**Difficulty.** Medium; ~500–1000 lines for the API + Lovász's bound.

**Prereqs.**
- `SimpleGraph.deleteEdges`
  (`Mathlib.Combinatorics.SimpleGraph.DeleteEdges`).
- Kelly-style double counting adapted to edge-decks.

**Mathematical sketch (API).** Define
```lean
def SimpleGraph.SameEdgeDeck (G H : SimpleGraph V) : Prop :=
  ∃ σ : G.edgeSet ≃ H.edgeSet, ∀ e : G.edgeSet,
    Nonempty (G.deleteEdges {↑e} ≃g H.deleteEdges {↑σ e})
```
and the basic `refl / symm / trans` bookkeeping.

**Sketch (Lovász).** Lovász's theorem: if
`|E(G)| > ½ · C(n, 2)`, then `G` is edge-reconstructible. Proof
(elementary, ~1 page in the original):

Let `m = |E(G)|` and `m' = |E(H)|` for a graph `H` with the same edge
deck. By double counting, `m = m'`. For each `(n, m)`-graph `G'`, the
number of edge-deleted subgraphs that can equal a fixed graph `F` on
`n` vertices and `m - 1` edges is a coefficient expressible via Möbius
inversion. When `m > ½ C(n,2)`, the inversion is non-singular and
invertible, so `G` is determined.

**Lean plan.**

1. Define `EdgeDeck` as a multiset of iso-classes of `(n, m-1)`-graphs.
2. Formalize the Möbius / inclusion–exclusion argument over the
   edge-deletion lattice.
3. Prove Lovász's threshold.
4. (Stretch) Prove Nash-Williams' extension to `m > (1/2) n(n-1)`.

**Risk.** Edge-deck machinery doesn't exist in Mathlib, so step 1 is
pure infrastructure. Mathlib has `SimpleGraph.deleteEdges` but not
`SimpleGraph.SameEdgeDeck`.

**Verification.** A headline theorem
`SameEdgeDeck.iso_of_dense : m > C(n, 2) / 2 → Nonempty (G ≃g H)` in
`LovaszBound.lean` with a clean proof.

---

## #E — Small-`n` computational verification (`decide`)

**Payoff.** A sorry-free, reproducible, `decide`-based proof of the
reconstruction conjecture for `n ≤ 5` or `n ≤ 6`. Matches McKay's
computer search for very small `n` but with a machine-checked proof
rather than a trusted-search witness.

**File.** `Reconstruction/SmallCases.lean` (new).

**Difficulty.** Medium (engineering); ~300–500 lines.

**Prereqs.**
- Decidable `SimpleGraph.Iso` over `Fin n`.
- Computable `subgraphCount` or at least a computable
  `SameDeck`-checker over `Fin n`.

**Mathematical sketch.** For fixed `n ∈ {3, 4, 5, 6}`:

1. Enumerate all `SimpleGraph (Fin n)` via `DecidableEq (SimpleGraph
   (Fin n))` (finite because adjacency is a `Fin n → Fin n → Bool` map).
2. For each pair `(G, H)` with `SameDeck G H`, verify `Nonempty (G ≃g H)`.

This reduces to a decidable proposition on a finite domain and can be
discharged by `decide`. **Critical constraint:** the project forbids
`native_decide` on unbounded domains; for fixed `n ≤ 6`, the domain is
bounded (`2^{n(n-1)/2}` graphs) and `decide` is in-scope per project
policy.

**Complexity.** `n = 6` has `2^15 = 32768` graphs. Pair enumeration is
`~2^30 ≈ 10^9`, too large. **Optimise by bucketing**: compute the deck
of each graph, sort by `decodeToDeck` → canonical form, and check each
bucket is a single iso-class. This reduces the inner check to
`bucketSize^2` pairs per bucket, typically manageable. `n = 5` is a
warm-up (`1024` graphs, trivial).

**Lean plan.**

1. Make `SimpleGraph (Fin n)` `DecidableEq` and provide a `Fintype`
   instance.
2. Make `SimpleGraph.Iso` `Decidable` via `Fintype (V ≃ V)`.
3. Define a computable `deck : SimpleGraph (Fin n) → Multiset
   (SimpleGraph (Fin (n-1)))` up to iso.
4. State and prove by `decide`:
   `∀ G H : SimpleGraph (Fin n), G.SameDeck H → Nonempty (G ≃g H)`.

Alternative (simpler): prove the equivalent statement for each fixed
isomorphism *representative* using canonical forms; this avoids
quotient types but needs a canonical labelling.

**Risk.** `decide` compilation time for `n = 6` may be prohibitive;
`n = 5` should be fast. Budget: if `n = 6` fails, ship `n ≤ 5`.

**Verification.** `lake build` succeeds with no `native_decide` (verify
against project policy in
[`CLAUDE.md`](../../../CLAUDE.md#lean-coding-conventions)); a single
theorem `reconstruction_conjecture_small : ∀ G H : SimpleGraph (Fin n),
3 ≤ n → n ≤ 5 → G.SameDeck H → Nonempty (G ≃g H)` certified by `decide`.

---

## Summary ranking for "what to attack first"

| Rank | Target | Rationale |
|------|--------|-----------|
| 1 | **#B** — `numComponents_eq` | Short, unlocks #C, purely bookkeeping. |
| 2 | **#C** — `iso_of_not_connected` | Headline result (Kelly 1942), builds on #B. |
| 3 | **#A** — `charPoly_coeff_zero_eq` | Upgrades the spectral half to "full charpoly". |
| 4 | **#E** — `decide`-certified small `n` | Reproducible witness; engineering. |
| 5 | **#D** — edge-deck API + Lovász | Opens a new direction but largest scope. |

Cross-links:

- [`index.md`](index.md) — overall formalization dashboard.
- [`sibling-project.md`](sibling-project.md) — line-by-line `sorry` state.
- [`mathlib-api.md`](mathlib-api.md) — prerequisites from Mathlib.
- [`../invariants/index.md`](../invariants/index.md) — mathematical
  reconstructibility status per invariant.
- [`../attacks/index.md`](../attacks/index.md) — high-level strategy
  taxonomy.
- [`../state-of-the-art/index.md`](../state-of-the-art/index.md) — what
  is known in the literature.
- [`../computational/index.md`](../computational/index.md) — McKay's
  computer verification and small-`n` data.

[kelly57]: ../sources.md#kelly57
[tutte79]: ../sources.md#tutte79
[schwenk79]: ../sources.md#schwenk79
[lovasz72]: ../sources.md#lovasz72
[muller77]: ../sources.md#muller77
[nashwilliams78]: ../sources.md#nashwilliams78
