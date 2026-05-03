# Reconstruction Formalization Checklist

This checklist tracks the Lean work suggested by the deck-accounting and
optimization viewpoint. Items are checked only when the Lean code builds and
the corresponding theorem or API is actually in place.

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
