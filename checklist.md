# Reconstruction Formalization Checklist

This checklist tracks the Lean work suggested by the deck-accounting,
optimization, and fixed-host singleton viewpoints. Items are checked only when
the Lean code builds and the corresponding theorem, API, computation, or
writeup is actually in place.

## Current Campaign: Fixed-Host Singleton / Local Obstruction

Target theorem:

```lean
def LowSliceZeroStarPairConjecture (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  LowSliceSameDeck K S T a b → LowSliceZeroStarPair K S T a b
```

Equivalent target:

```lean
LowSliceSameDeck K S T a b → FixedHostSingletonSolved K S T a b
```

Current proof posture: refute the local obstruction.  We have already shown
that the failure of an active zero-star pair is exactly a family of local
first-error witnesses over two-hole colored cards.  The next autonomous work is
to make the deck-counting and descent consequences of that obstruction precise.

### A. Baseline And Hygiene

- [x] Verify `lake build Reconstruction.FixedHost`.
- [x] Verify full `lake build`.
- [x] Keep `proof_sketch.tex` compiling with `pdflatex`.
- [x] Remove generated TeX/cache artifacts after verification.
- [x] Re-run `lake build Reconstruction.FixedHost` after every Lean batch.
- [x] Re-run `pdflatex -interaction=nonstopmode proof_sketch.tex` after every
      proof-sketch batch.
- [x] Keep `Reconstruction/FixedHost.lean` under the line-length/style gate for
      newly edited lines.

### B. Active Zero-Star Pair Package

- [x] Define chosen card isomorphisms as `FixedHostCardIsoData`.
- [x] Define deleted-star error and concrete star mismatches.
- [x] Prove zero star error is equivalent to absence of star mismatches.
- [x] Prove a zero-star active card match extends to a full fixed-host
      singleton solution.
- [x] Prove any full solution restricts to an active zero-star pair.
- [x] Prove
      `LowSliceZeroStarPair K S T a b ↔ FixedHostSingletonSolved K S T a b`.
- [x] Define perfect zero-star matchings and prove they are equivalent to the
      one-pair formulation.

### C. Formal Local Obstruction

- [x] Define `LowSliceCardFirstError` as a first mismatch plus its two-hole
      restriction.
- [x] Define `LowSliceLocalObstruction`.
- [x] Prove
      `LowSliceLocalObstruction K S T a b ↔ ¬ LowSliceZeroStarPair K S T a b`.
- [x] Prove first-error witnesses preserve passive first color.
- [x] Prove first-error witnesses preserve active/inactive status.
- [x] Prove every first error is either active-active or inactive-inactive.
- [x] Define named predicates for active first errors and inactive first errors.
- [x] Prove the active/inactive case split for `LowSliceLocalObstruction` in a
      reusable theorem form.
- [x] Record the same case split in `proof_sketch.tex`.

### D. Make Card-Visible Status Explicit

- [x] Prove finite cardinality lemmas for deleted colors:
      `Fintype.card {w // w ≠ x ∧ w ∈ S}` differs from `Fintype.card S` exactly
      according to whether `x ∈ S`.
- [x] Prove first-color deleted status is visible from a first-color-preserving
      card isomorphism: in finite hosts, a `FixedHostCardIsoData` forces
      `x ∈ S ↔ y ∈ S`.
- [x] Use that lemma to remove the explicit `hFirst` burden from low-slice
      obstruction statements whenever `[Finite V]`.
- [x] Add a short English explanation that the passive color status is visible
      and the deleted star is the only hidden datum.

### E. Low-Slice Equality To Obstruction Data

- [x] Define a chosen low-slice matching with automatically visible first
      status in finite hosts.
- [x] From `LowSliceSameDeck`, extract a `LowSliceIsoData` or equivalent
      chosen matching.
- [x] Under the no-pair assumption, convert every edge of that chosen matching
      to a `LowSliceCardFirstError`.
- [x] Define the total star-error count of a chosen low-slice matching.
- [x] Define a minimum-error low-slice matching for finite hosts.
- [x] Prove a minimum-error matching has no zero-error edge exactly under the
      no-pair assumption.

### F. Descent/Contradiction Campaign

- [x] Split minimum-error obstruction into active-active first errors and
      inactive-inactive first errors.
- [ ] Active-active branch:
      - [x] Formalize the transport/recentering operation that follows an
            active first error.
      - [x] Define the active exchange successor and the coherent/noncoherent
            split for active first errors.
      - [x] Prove coherent active steps rewrite as two-hole transports deleting
            matched active pairs.
      - [x] Define the active exchange relation and its noncoherent subrelation.
      - [x] Define the active observer-successor relation.
      - [x] Prove noncoherent active exchange edges are loop-free.
      - [x] Prove active first-error sources and targets are genuinely distinct
            from their deleted bases.
      - [x] Prove every noncoherent active step is a three-distinct-vertex
            configuration.
      - [x] Formalize chosen active observer systems.
      - [x] Prove an all-active obstruction yields a nontrivial finite observer
            cycle.
      - [x] Package active observer cycles and prove their consecutive vertices
            are observer-relation edges.
      - [x] Split packaged active observer cycles into all-coherent or
            has-noncoherent-index cases.
      - [x] Prove a noncoherent index gives a noncoherent correction edge.
      - [x] Prove the active observer-cycle fork reduces to all-coherent and
            noncoherent-cycle subforks.
      - [x] Prove coherent selected active edges carry matched two-hole
            transports to their observer successors.
      - [x] Prove all-coherent active cycles carry matched two-hole transports
            along every cycle edge.
      - [ ] Prove coherent active steps are removable side-cycle matches, unless
            they expose a smaller fixed-host obstruction.
      - [ ] Prove noncoherent active steps assemble into a lowering exchange
            path or a closed active correction cycle.
      - [ ] Prove recentering either produces a zero-star pair or strictly
            lowers total error.
      - [ ] If lowering fails, extract a closed active first-error cycle.
      - [ ] Prove a closed active cycle composes to a zero-star pair or a
            smaller obstruction.
- [ ] Inactive-inactive branch:
      - [x] Formalize the complementary two-hole witness produced by an
            inactive first error.
      - [x] Split inactive first errors into endpoint-exposing and outer-core
            residual cases.
      - [x] Prove non-endpoint-exposing inactive errors are exactly outer-core
            residuals.
      - [x] Formalize chosen inactive observer systems and the endpoint/outer
            fork.
      - [x] Prove the inactive endpoint/outer fork reduces to all-endpoint and
            outer-residual subforks.
      - [ ] Prove restricted Kelly counts see the inactive residual.
      - [ ] Show a purely inactive residual cannot support a minimum-error
            obstruction, or isolate the exact counterexample pattern.
- [ ] Mixed/choice branch:
      - [x] Prove every positive obstruction is all-active, all-inactive, or
            genuinely mixed.
      - [x] Package the strategic fork: active observer cycle, all-inactive
            endpoint/outer split, or mixed branches.
      - [x] Prove no-positive-obstruction follows from ruling out the three
            strategic forks.
      - [x] Prove no-positive-obstruction follows from ruling out the refined
            five subforks.
      - [ ] Show the choice of first mismatch can be made consistently enough
            for descent.
      - [ ] If not, formulate the finite selection obstruction explicitly and
            test it computationally.

### G. Computational Checks

- [x] Implement active zero-star pair search in
      `research/computational/data/fixed_host_singleton_search.py`.
- [x] Record `n=5` exhaustive and sampled higher-order evidence in
      `fixed_host_singleton_n5.txt`.
- [x] Add a probe that classifies first errors as active-active or
      inactive-inactive for all minimum-error matches.
- [x] Search for a no-descent minimum-error obstruction in small finite hosts.
- [x] If a candidate obstruction appears, dump it as a reproducible fixture.
      - No positive minimum-error candidate appeared in the exhaustive n=5 atlas
        run, so there is currently no fixture to dump.
- [x] If no candidate appears, record the counts and refine the English descent
      conjecture.

### H. Proof Sketch Maintenance

- [x] Record the active zero-star pair target.
- [x] Record the first-error localization lemma.
- [x] Record the formal local obstruction proposition.
- [x] Add a precise “status visibility” lemma.
- [x] Add a precise “minimum-error obstruction” definition matching the Lean
      structure.
- [x] Prove no-positive-minimum-obstruction is equivalent to the
      minimum-error-zero route.
- [x] Add the active-active and inactive-inactive branch lemmas as conjectural
      waypoints.
- [ ] When a branch fails, record the exact obstruction and change direction.

### I. Success/Failure Criteria

- [ ] Success: prove `LowSliceZeroStarPairConjecture`.
- [ ] Success: derive `LowSliceOrbitReconstruction` from the zero-star pair
      theorem.
- [ ] Partial success: prove one branch of the local obstruction cannot occur.
- [ ] Productive failure: produce a concrete finite obstruction to the descent
      strategy and document why the approach must be strengthened.
- [ ] Quality gate: no new `sorry`, `lake build` passes, proof sketch compiles,
      computational artifacts are reproducible.

---

The sections below are older project-wide formalization tracks retained for
context.

## 0. Baseline

- [x] Run `lake build` in `reconstruction-conjecture` and record the current
      open proof obligations.
      - Baseline build succeeds.
      - Current intentional `sorry`s after the disconnected-case work:
        `reconstruction_conjecture` and `SameDeck.charPoly_coeff_zero_eq`.
      - Literature status:
        `reconstruction_conjecture` is open mathematics.
        `SameDeck.charPoly_coeff_zero_eq` follows from the known
        reconstructibility of the characteristic polynomial (classically
        attributed in the reconstruction literature to Tutte).
- [x] Keep `Reconstruction.lean` imports in sync with any new modules.
      - Added `Reconstruction.TopTrace` to the import surface.
- [x] Keep module doc-comments and `README.md` status aligned with the code.
      - Added the triangular component-count identity to both the module
        doc-comment and project README.

## 1. Disconnected Graphs: Component Multiset Recovery

- [x] Audit the existing component-count infrastructure in
      `Reconstruction/Disconnected/ComponentCount.lean`.
- [x] Prove helper lemmas relating `componentCount F G` to
      `subgraphCount F G` through larger connected components.
      - Added `subgraphCount_eq_zero_of_card_lt`.
      - Added `subgraphCount_eq_one_or_zero_of_card_eq`.
      - Added `componentCount_eq_sum_ite`.
      - Added `componentCount_eq_sum_same_card_subgraphCount`.
      - Added `subgraphCount_eq_componentCount_add_larger`.
- [x] Formalize the triangular induction that recovers, for every connected
      graph `F` with `< |V|` vertices, the number of connected components of
      `G` isomorphic to `F`.
      - Added `largerComponentSubgraphCount_sum_eq_of_isoEquiv`: an
        isomorphism pairing of larger components gives equality of the larger
        triangular error terms.
      - Added `SameDeck.componentCount_eq_of_larger_component_isoEquiv`: the
        local induction step recovering the `F`-component count once larger
        components have been matched.
      - Added `largerComponentEquivOfComponentCountEq` and
        `largerComponentEquivOfComponentCountEq_iso`: equal counts for all
        component types above a size threshold now produce the exact
        larger-component matching required by the local triangular step.
      - Added `ConnectedComponent.card_supp_lt_of_not_connected`: every
        component of a finite disconnected graph is strictly smaller than the
        host, supplying the Kelly-size side condition for component graphs.
      - Added `SameDeck.componentCount_eq_components_of_not_connected`: a
        descending induction over component size recovering every represented
        component isomorphism class in two same-deck disconnected graphs.
- [x] Prove component-count equality under `SameDeck` for all connected
      component types in disconnected graphs.
- [x] Package recovered per-class component counts into a global component
      matching.
      - Added `componentEquivOfComponentCountEq`: equal component counts for
        every represented component type give a bijection between connected
        components preserving component isomorphism classes.
      - Added `componentEquivOfComponentCountEq_iso`: the chosen component
        bijection maps each component to an isomorphic component.
      - Added `isoOfComponentCountEq`: equal component multiplicities for
        every component type now assemble directly into `Nonempty (G ≃g H)`.
- [x] Assemble a global graph isomorphism using `isoSigmaComponents`.
      - Added `componentSigmaGraphIsoOfComponentIso` and
        `isoOfComponentIsoEquiv`: a component equivalence plus per-component
        isomorphisms now assembles into a global graph isomorphism.
- [x] Close `SimpleGraph.SameDeck.iso_of_not_connected`.
      - Closed using `SameDeck.componentCount_eq_components_of_not_connected`
        plus `isoOfComponentCountEq`; this formalizes Kelly's theorem that
        disconnected graphs are reconstructible.

## 2. One-Card Extension Search API

- [x] Create `Reconstruction/Search.lean`.
- [x] Define the graph obtained by adding one new vertex to a card with an
      attachment subset.
- [x] Prove the deleted-new-vertex card is isomorphic to the original card.
- [x] Recover the original edge count from the deck and the deleted vertex
      degree from a card.
      - Exported `sum_card_edgeFinset_deleteVert`.
      - Exported `degree_eq_card_edgeFinset_sub_deleteVert`.
- [x] Prove every reconstruction extending a fixed card is represented by one
      attachment subset.
      - Added `deleteVertAttachment`.
      - Added `addVertex_deleteVert_iso`.
- [x] State and prove the exact zero-loss/search-space equivalence in terms of
      `SameDeck`.
      - Added `cardAttachment` and `addVertex_card_iso` for transported card
        isomorphisms.
      - Added `SameDeck.exists_addVertexWithNeighbors_iso`: any same-deck
        reconstruction lies in the one-card extension search space of each
        matched card.

## 3. Kocay-Style Cover Identities

- [x] Create `Reconstruction/Kocay.lean`.
- [x] Define finite covers of a graph by induced copies of a list of patterns.
      - Added `coverFinset`, a finite-index typed cover finset grouped by
        actual covered vertex set.
      - Kept `pairCoverFinset` as the ordered two-pattern specialization.
- [x] Define the cover number `c((F_i), X)` for a target graph `X`.
      - Added `coverCount` for the in-host, covered-vertex-set version.
      - Added `coverTypeCount` for the finite-index all-vertices target graph
        cover number.
      - Added `pairCoverCount` and `pairCoverTypeCount` for the typed
        two-pattern versions.
- [x] Prove the product-count identity
      `∏ i, subgraphCount (F_i) G = ∑ X, c((F_i), X) * subgraphCount X G`
      in a finite, typed form.
      - Proved the finite-index vertex-set precursor `coverCount_sum`.
      - Proved `coverCount_eq_coverTypeCount_induce` and
        `coverTypeCount_sum_induce`, the finite-index target-graph form
        grouped by the actual induced graph on each covered vertex set.
      - Added `coverTypeCount_eq_of_iso`, `InducedSetIsoClass`, and
        `coverTypeCount_sum_inducedIsoClass`, grouping the finite-index
        identity by induced-subgraph isomorphism classes in the typed quotient
        form `∏ i s(F_i,G) = ∑_X c((F_i),X) * s(X,G)`.
      - Proved the ordered-pair typed precursor
        `pairCoverCount_sum`.
      - Proved `pairCoverCount_eq_pairCoverTypeCount_induce` and
        `pairCoverTypeCount_sum_induce`, the ordered-pair target-graph form
        grouped by the actual induced graph on each covered vertex set.
- [x] Derive reconstructible linear constraints from `SameDeck`.
      - Added `SameDeck.subgraphCount_mul_eq` for products of two
        Kelly-reconstructible counts.
      - Added `SameDeck.subgraphCount_prod_eq` for finite indexed products of
        Kelly-reconstructible counts.
- [x] Add doc-comments explaining the connection to Kocay's lemma.

## 4. Full Characteristic Polynomial

- [x] Decide whether the proof route is Sachs/Kocay or closed-walk
      decomposition.
      - Chosen route: build Kocay/Sachs-style cover identities first, then use
        them for the constant-term characteristic-polynomial target.
- [ ] Add any missing finite-support/walk decomposition lemmas.
      - Added `Reconstruction/TopTrace.lean`.
      - Added `rootedClosedWalkCount` and proved it is the trace of the
        adjacency-matrix power.
      - Added `properSupportClosedWalkCount`, `fullSupportClosedWalkCount`,
        and `rootedClosedWalkCount_eq_proper_add_full`.
      - Added `exactSupportClosedWalkCount` and
        `properSupportClosedWalkCount_eq_sum_exactSupport`, expanding the
        proper-support contribution as a sum over exact proper vertex
        supports.
- [ ] Prove the missing `trace(A^n)` or constant-term reconstruction
      ingredient.
      - Added `SameDeck.charPoly_coeff_zero_eq_of_trace_card_eq`: the
        constant coefficient is now reduced to the single remaining top-trace
        equality `tr(A^|V|)`.
      - Added `trace_adjMatrix_card_eq_of_support_counts_eq`: the top trace
        equality is reduced to equality of the proper-support and full-support
        top-length closed-walk counts.
      - Added `SameDeck.charPoly_coeff_zero_eq_of_support_counts_eq`: the
        constant coefficient follows from those two support-count equalities.
- [ ] Close `SimpleGraph.SameDeck.charPoly_coeff_zero_eq`.
      - Literature status: proven; the full adjacency characteristic
        polynomial is reconstructible from the deck, so the constant term is
        reconstructible. Remaining work is formalizing the constant-term
        ingredient.
- [ ] Confirm `SimpleGraph.SameDeck.charPoly_eq` is fully closed.

## 5. Final Quality Gate

- [x] No new `sorry` outside the main open reconstruction conjecture unless
      explicitly documented as a staged target.
      - No new `sorry` was introduced. Existing staged `sorry`s remain:
        `reconstruction_conjecture` and `SameDeck.charPoly_coeff_zero_eq`.
- [x] `lake build` succeeds.
      - Verified after the latest changes.
- [x] `README.md` and research notes mention the newly closed items.
      - `README.md` updated for Kocay finite products and the componentwise
        Sigma assembly theorem, plus the component iso-class matching bridge.
      - `README.md` updated for the Kocay isomorphism-class grouped
        product-count identity.
      - Research notes updated with the formalization status of
        `coverTypeCount_sum_inducedIsoClass`.
      - Research notes previously recorded that Sigma assembly was closed;
        they now also record that the disconnected-graph theorem itself is
        closed.
      - `README.md` and research notes updated to record that
        `SameDeck.iso_of_not_connected` is closed.
      - `README.md` and research notes updated with the `TopTrace` support
        split and support-count conditional reduction.
- [x] References for Kelly, Kocay, McKay, Schwenk/Tutte are cited where used.
      - Added Kocay and McKay references to the project README and Kocay
        reference to `Kocay.lean`.
