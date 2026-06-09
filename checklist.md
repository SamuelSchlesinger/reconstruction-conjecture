# Reconstruction Formalization Checklist

This checklist tracks the Lean work suggested by the deck-accounting,
optimization, and fixed-host singleton viewpoints. Items are checked only when
the Lean code builds and the corresponding theorem, API, computation, or
writeup is actually in place.

## Current Programme: Separator Decomposition (active)

The project's primary attack is now **reconstruction by separator
decomposition** — see [`research/attacks/separator-decomposition.md`](research/attacks/separator-decomposition.md).
Reconstruct class by class up a ladder of separator size, reusing the existing
component-decomposition machinery (`Disconnected.lean`):

- **Rung 0 — components (`S = ∅`):** done (`SameDeck.iso_of_not_connected`).
- **Rung 1 — cut vertices / blocks (`|S| = 1`):** Bondy 1969 reduction. **Active.**
  Done in `Reconstruction/Separator.lean` (all builds, no `sorry`, standard
  axioms only):
  - [x] Primitives: `IsSeparator`, `IsCutVertex`, `NoCutVertex`,
        `TwoConnected`, `MinDegreeTwo`.
  - [x] Iso-invariance of all predicates (`IsSeparator.map`, `IsCutVertex.map`,
        `MinDegreeTwo.map`, `TwoConnected.map`) via `Iso.induceImage`.
  - [x] **Separator reassembly engine** `isoOfSamePiece` / `isoOfSamePiece'`,
        with the structural lemma `adj_samePiece` (every edge lies in one
        piece) and the helper `mem_iff_of_fixOn`. This is the amalgamation-over-
        `S` generalization of `isoOfComponentIsoEquiv`.
  - [x] **Deleted-vertex reassembly constructor** `isoOfDeleteVertIso` (+ the
        `extendMap` combinator and its `apply` lemmas): a *card* isomorphism
        `G − v ≃g H − w` that preserves the link extends to a global `G ≃g H`
        sending `v` to `w`. The deleted vertices `v`, `w` may differ — exactly
        what a deck matching gives (it matches `v` to `σ v`). Uses only
        `propext`, `Quot.sound`.
  - [x] **Data-carrying component assembly** in `Disconnected.lean`:
        `componentSigmaGraphIso`, `componentIso`, and the action lemma
        `componentIso_apply` (`componentIso e ι x = ι (component of x) x`,
        provable by `rfl`). This is the `Nonempty`-free assembly needed for
        link-tracking.
  - [x] **Complete structural reduction** `nonempty_iso_of_cutVertex_pieces`:
        a bijection of `G − v` components, per-component induced-subgraph isos,
        and the link condition (each piece iso preserves adjacency to `v`)
        assemble into `Nonempty (G ≃g H)`. This finishes the **entire
        structural side** of rung 1: `G ≅ H` is reduced to a piece-matching of
        `G − v` that agrees on `v`'s attachment.
  - [x] **2-connectedness is deck-recognizable** (`SeparatorComponents.lean`):
        `isCutVertex_iff_not_connected_deleteVert` (a vertex of a connected
        graph is a cut vertex iff its card is disconnected),
        `twoConnected_iff_forall_deleteVert_connected` (2-connected ⟺
        connected with all cards connected), and `SameDeck.twoConnected_iff`
        (same-deck graphs agree on 2-connectivity). This is the recognition
        half of rung 1; the recovery half (below) is the open content.
  - [ ] Deck recovery (Bondy 1969, *purely deck-theoretic*): from `SameDeck`
        and a cut vertex, produce the component bijection `e`, the per-component
        isos `ι`, and the link condition `hlink` that
        `nonempty_iso_of_cutVertex_pieces` consumes. This is the substantive
        1969 argument (recognizing the cut vertex's card, recovering the
        component-with-attachment pieces and their matching from deck counts).
  - [ ] Prove `BondySeparableReconstructible`; derive the Yongzhi reduction.
- **First deck-level reconstruction theorem from the machinery:**
  `nonempty_iso_of_universal_vertex` — **graphs with a universal (dominating)
  vertex are reconstructible** (Manvel's method, simplest case). The link
  condition is automatic for a universal vertex, and degree-reconstructibility
  (`SameDeck.card_edgeFinset_eq` + `degree_eq_of_card_edgeFinset_eq_of_deleteVert_iso`)
  forces the matched-card vertex `σ v` to be universal in `H`, so
  `isoOfDeleteVertIso` applies. Supporting: `IsUniversal`, `isUniversal_iff_degree`,
  `nonempty_iso_of_universal_card_iso`. Validates the constructor on a real
  reconstruction result while the cut-vertex deck recovery is developed.
- **Foundations expanded (parallel fan-out):** four independent modules added,
  each builds, zero `sorry`, standard axioms:
  - `SeparatorChar.lean` — `Separates` predicate + `isSeparator_iff_separates`,
    `isCutVertex_iff_separates` (the missing separator-theory primitive).
  - `SeparatorComponents.lean` — `IsCutVertex.not_connected_deleteVert`,
    `nonempty_deleteVert`, `two_le_card_components`.
  - `SeparatorDegree.lean` — `IsUniversal.map`, `minDegreeTwo_iff`,
    `isUniversal_complete`, `minDegreeTwo_complete`.
  - `SeparatorDual.lean` — `IsIsolated`, `isUniversal_iff_compl_isIsolated`,
    `IsIsolated.not_connected`, **`nonempty_iso_of_isolated_vertex`**, and
    `nonempty_iso_of_universal_vertex_via_compl` (the complement re-derivation).
  - `CliqueSeparator.lean` — `IsSimplicial`(+`.map`), `IsCliqueSeparator`(+`.map`,
    projections), `isClique_image_of_iso`, `IsCliqueSeparator.adj_of_mem`.
- **Multi-vertex separator assembler — DONE** (`SeparatorAssembler.lean`):
  `extendFixingSet` (extend a permutation of `Sᶜ` to `V` fixing `S`),
  `nonempty_iso_of_induce_compl_iso` (a card iso `G − S ≃g H − S` preserving the
  separator's internal edges and the `S`-to-`Sᶜ` attachment extends to
  `G ≃g H`), and `nonempty_iso_of_separator_pieces` (the per-component form).
  This generalizes `nonempty_iso_of_cutVertex_pieces` from `S = {v}` to an
  arbitrary separator and is the structural core of Heinrich et al.'s
  Reconstruction-by-Separation (Lemma 24). The **structural reassembly side of
  rungs 2–3 is now complete**; what remains for any class is the deck-theoretic
  recovery (separator + component matching + attachment).
- **Rung 2 — multi-vertex separators:** Heinrich et al. 2025 (interval graphs).
  See [`research/attacks/rung-2-3-plan.md`](research/attacks/rung-2-3-plan.md):
  reassembly is done (above); the wall is deck recovery (a ~50-page resilient
  structure theory). Next concrete targets are the chordal structure layer
  (Dirac clique-separator existence, PEO) — see the plan's ordered lemma list.
- **Rung 3 — clique separators (chordal graphs):** OPEN mathematics. Needs the
  chordal/PEO/Dirac/clique-tree layer (entirely absent from Mathlib); see the
  rung-2/3 plan for the ordered lemma list.
  - [x] **Chordal structure layer started** (`Chordal.lean`): `IsChordal`
        (no induced `≥ 4`-cycle, defined as `IsEmpty (cycleGraph n ↪g G)` for
        `n ≥ 4` — a graph embedding reflects adjacency, so this is exactly "no
        induced `Cₙ`"), `IsChordal.map` (iso-invariance), `IsChordal.induce`
        (hereditary), `isChordal_of_card_le_three` and `isChordal_bot`
        (small-graph / edgeless base cases).
        plus `IsChordal.deleteVert` (deleting any vertex stays chordal — the PEO
        recursion step). Simplicial base cases proved:
        `isSimplicial_of_subsingleton_neighborSet` (isolated/leaf vertices are
        simplicial — axiom-free) and `isSimplicial_top` (complete-graph case).
        Dirac's theorems stated as targets: `DiracSimplicial` (chordal ⇒ has a
        simplicial vertex), `DiracCliqueSeparator` (non-complete chordal ⇒ has a
        clique separator — the structural input that makes the reassembly
        engine's hypothesis available), and the crux `MinimalSeparatorClique`
        (a minimal separator of a chordal graph induces a clique).
  - [x] **Induced-cycle-extraction foundations — DONE** (the novel,
        no-Mathlib-support core; all build, standard axioms only):
        - `Geodesic.lean`: `Walk.geodesic_not_adj_of_lt` (+ symm) — a shortest
          path is chordless (the linchpin: a chord would shortcut it).
        - `InducedCycle.lean`: `cycleGraph_adj_val` (value-level cycleGraph
          adjacency = consecutive-or-wrap, via `Fin.coe_int_sub_eq_ite`+
          `fin_omega`) and **`inducedCycleEmbedding`** (a chordless `IsCycle`
          walk of length `n ≥ 4` ⟶ `cycleGraph n ↪g G`, the bridge to the
          embedding-based `IsChordal`).
        - `CycleFromPaths.lean`: `Walk.isCycle_append_reverse` — two
          internally-disjoint paths glue into a cycle.
  - [x] **Minimality ⇒ neighbour in each component — DONE**
        (`MinimalSeparator.lean`): `exists_adj_mem_component` — from
        inclusion-minimality and a separated pair `u₀, w₀`, every `x ∈ S` has a
        neighbour in `u₀`'s component. The delicate reachability surgery (a walk
        from `u₀` in `G − (S\{x})` can't escape its component) done cleanly via
        `reachable_iff_reflTransGen` + `ReflTransGen` `tail`-induction. Standard
        axioms.
  - [x] **`MinimalSeparatorClique` — PROVED** (`MinimalSeparatorClique.lean`,
        `minimalSeparatorClique`; standard axioms only). In a chordal graph an
        inclusion-minimal separator is a clique. Final assembly:
        - `inducedCycleEmbedding_of_paths` (`InducedCycle.lean`): the two-arc
          induced-cycle bridge — two internally-disjoint chordless arcs `x → y`
          with no cross-edges glue to `cycleGraph (|P|+|Q|) ↪g G`. Carries the
          glued-cycle `Fin n` getVert index bookkeeping (4 index regions, WLOG
          `a ≤ b`, each reducing to chordless-P/Q, no-cross, or wrap/diagonal).
        - `exists_chordless_arc` (`MinimalSeparatorClique.lean`): a chordless
          `x`–`y` arc through a prescribed component — a geodesic in
          `G[component ∪ {x,y}]` (built by `Walk.induce` of the assembled
          connecting walk, then `Reachable.exists_walk_length_eq_dist`), mapped
          to `G`; chordless via `geodesic_not_adj_of_lt` + `map_adj_iff`, its
          interior confined by the induced subgraph.
        - `minimalSeparatorClique`: glues the two arcs (through `u₀`'s and
          `w₀`'s components, distinct since `S` separates them), discharging
          cross-edges by `adj_connectedComponentMk_eq` and edge/interior
          disjointness by the shared-only-`x,y` support characterization,
          contradicting `IsChordal`.
  - [x] **`DiracCliqueSeparator` — PROVED** (`Dirac.lean`,
        `diracCliqueSeparator`, under `[Finite V]`; standard axioms). A finite
        chordal connected non-complete graph has a clique separator: a
        non-complete connected graph has a separator (`{a,b}ᶜ` for a non-adjacent
        pair, whose induced `{a,b}` is edgeless — `reachable_bot`); a
        `⊆`-minimal one exists (`Set.Finite.exists_minimal`,
        `exists_minimal_separator`), and is a clique by `minimalSeparatorClique`.
        This is the structural input the reassembly engine needs (rung 3).
  - [x] `isSimplicial_of_induce` (`Dirac.lean`; axiom-free) — the
        simplicial-vertex transfer lemma (a vertex simplicial in `G[T]` with all
        its `G`-neighbours in `T` is simplicial in `G`); the bridge for the
        `DiracSimplicial` induction.
  - [x] **`DiracSimplicial` — PROVED** (`Dirac.lean`, `diracSimplicial`;
        standard axioms). A finite nonempty chordal graph has a simplicial vertex
        (Dirac 1961). Type-polymorphic strong induction on `|V|` (`dirac_aux`, one
        named universe so the induced-subgraph recursion stays in type) of the
        strong form "complete, or two non-adjacent simplicial vertices":
        `exists_simplicial_of_induce_disj` extracts a simplicial vertex of a set
        `T'` from the inductive dichotomy on `G[T]` (a clique `T \ T'` ⇒ the two
        non-adjacent simplicial vertices can't both avoid `T'`); a connected
        non-complete graph peels a component across a clique separator
        (`diracCliqueSeparator`) and recurses on `G[component ∪ S]`, a
        disconnected graph peels two whole components, transferring via
        `isSimplicial_of_induce`.
  - [x] **`isChordal_iff_hasPEO` — PROVED** (`PEO.lean`; standard axioms). The
        full Dirac/Fulkerson–Gross characterization: a finite graph is chordal
        **iff** it has a perfect elimination ordering. `IsPEO l`: `l` enumerates
        the vertices so each suffix `v :: rest` has `v`'s later neighbours forming
        a clique.
        - `hasPEO_of_chordal` (⟹): induction (`peo_aux`) peeling a
          `G[s]`-simplicial vertex (`diracSimplicial`) off the front of the list
          for the remaining `Finset s`, its `s`-neighbourhood a clique by
          `isClique_neighbors_of_isSimplicial_induce`.
        - `isChordal_of_hasPEO` (⟸): in any induced `≥ 4`-cycle, the PEO-earliest
          vertex (`exists_earliest_suffix`) has both cycle neighbours later, so
          the PEO forces them adjacent — contradicting the cycle's chordlessness
          (`cycleGraph_not_adj_pred_succ`, the `Fin n` modular facts handled by
          `abel` + `Nat.mod_eq_of_lt` flattening for `omega`).
        Next: clique trees, `treewidth = ω − 1`.
- **Symmetry-breaking programme (user-directed, 2026-06) — see
  [`research/attacks/symmetry-breaking.md`](research/attacks/symmetry-breaking.md):**
  - [x] **Regular graphs are reconstructible — PROVED**
        (`RegularReconstruction.lean`; standard axioms):
        `nonempty_iso_of_regular`, via the deficit stamp
        (`degree_deleteVert`: deleting `v` lowers degrees exactly on `N(v)`;
        `IsRegularOfDegree.adj_iff_degree_deleteVert_ne`: in a `d`-regular
        graph the stamp is legible as card-degree `≠ d`) and the
        `isoOfDeleteVertIso` assembler. Base case of the deficit-marking
        mechanism; also corrects the attacks-index row that conflated the
        open cubic **2-deck** problem with the closed 1-deck case.
  - [x] **Rigid-card criterion — PROVED** (`RegularReconstruction.lean`;
        standard axioms): `RigidVertex` (every degree-data-matched card iso
        is correctable by a card automorphism to respect attachments) and
        `nonempty_iso_of_rigidVertex` — **one rigid vertex ⟹
        reconstructible**. `IsRegularOfDegree.rigidVertex` shows every
        vertex of a regular graph is rigid; regular reconstruction is now
        the corollary. "Graphs with a rigid vertex" is the project's first
        new formally-verified reconstructible class.
  - [x] **Shift-recurrence lemma (Discovery A) — PROVED in count form**
        (`SameDeck.nbrCount_eq`, `ValueSeparated.lean`; standard axioms):
        same-deck graphs admit a matching `σ` with, for every `v` and every
        card-degree value `t`, equal neighbour and non-neighbour counts at
        `t` — the neighbour-degree profile is deck-forced; the only
        labelling freedom is which vertices *within* a class are neighbours
        (no Hall condition needed; the imagined level-2 obstruction
        dissolves).
  - [x] **Value-separated ⟹ rigid — PROVED** (Discovery B;
        `ValueSeparated.lean`, standard axioms): `ValueSeparated.rigidVertex`
        via the telescoping induction `nbr_nonNbr_transfer` over value-class
        counts (`classCount_transfer` from the card iso,
        `fullDegCount_transfer` from the degree multiset and deleted degree,
        `fullDegCount_eq`/`classCount_eq`/`shiftNbrCount_succ` from the
        deficit stamp). Corollary `nonempty_iso_of_valueSeparated`: **graphs
        with a value-separated vertex are reconstructible** — strictly
        extends regular graphs (`IsRegularOfDegree.valueSeparated`).
  - [x] Corollary: **injective-degree cards force reconstruction**
        (`nonempty_iso_of_injective_card_degrees`) — a size-≤1 class is
        never mixed.
  - [ ] Twin-flexible rung (2½, spec in `symmetry-breaking.md`): mixed
        classes that are twin classes are automorphism-correctable; new
        class theorem via twin transpositions + disjoint-support
        composition + `SameDeck.nbrCount_eq`.
  - [ ] Rigidity census (computational): enumerate `n ≤ 10` graphs without
        a rigid vertex — the enumerated wall.
- **Deck recovery (the frontier) — see
  [`research/attacks/deck-recovery.md`](research/attacks/deck-recovery.md):**
  - [x] Forced-structure cases done: disconnected, **`Gᶜ` disconnected (joins /
        decomposable graphs)** (`nonempty_iso_of_compl_not_connected`, the
        complement-dual of Kelly), isolated vertex, universal vertex. These
        exhaust what recovery gives "for free" (`S = ∅` in `G` or `Gᶜ`, no
        attachment data needed).
  - [ ] Attachment recovery — the wall: cut-vertex `δ ≥ 2` (Bondy end-block
        analysis), 2-connected (Yongzhi target), interval (Heinrich 50-page
        structure theory), chordal (open mathematics). The reduction
        "recovered data ⇒ `G ≃g H`" is done (the assembler); the existential
        recovery of the separator + component matching + attachment is the open
        content.

Mathlib gap: it has `Connected`/`ConnectedComponent`/`induce` but **no** cut
vertices, vertex separators, `k`-vertex-connectivity, or blocks — all must be
defined. Staged targets are stated as `def … : Prop`, never `theorem … := sorry`.

**Core foundation added:** `SameDeck.compl` (in `Basic.lean`) — the complement
deck is reconstructible, so reconstructibility is closed under complementation
(classical; Bondy's manual). Built from `Iso.compl` (complement of a graph iso)
and `compl_deleteVert` (`Gᶜ - v = (G - v)ᶜ`). Uses only `propext`, `Quot.sound`.
This dualizes every positive result (e.g. universal-vertex ↔ isolated-vertex,
dense ↔ sparse) and is a basic tool the project previously lacked.

## Superseded Campaign: Fixed-Host Singleton / Local Obstruction

> **STATUS: low-slice target REFUTED (2026-05).** The note
> [`research/attacks/fixed-host-t-empty.md`](research/attacks/fixed-host-t-empty.md)
> exhibits a 9-vertex host (`S = ∅`, `T = ∅`) with `K − a ≅ K − b` of minimum
> star error `2` and trivial `Aut(K)` that does **not** satisfy the full
> singleton-colored deck equality. This is a counterexample to the two targets
> below — `LowSliceZeroStarPairConjecture` and `LowSliceOrbitReconstruction`
> are **false as stated** (the low slice alone cannot reconstruct the orbit).
> The full-deck `FixedHostSingletonConjecture` (which also assumes the
> *complementary* slice) is untouched and remains open. The `FixedHost.lean`
> infrastructure (3469 lines, zero `sorry`) is correct and retained; the
> all-active `T = ∅` branch was closed precisely because no observer cycle can
> exist when `|T ∪ {a}| = 1`, so the live obstruction is the inactive branch,
> which is exactly what the counterexample realizes. The corrected target is
> the transition-cycle closure (full slice), recorded in the note — but the
> project's primary effort has moved to the separator-decomposition programme
> above.

Refuted target theorem:

```lean
def LowSliceZeroStarPairConjecture (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  LowSliceSameDeck K S T a b → LowSliceZeroStarPair K S T a b
```

Refuted equivalent target:

```lean
LowSliceSameDeck K S T a b → FixedHostSingletonSolved K S T a b
```

Original proof posture (now known unattainable via the low slice alone): refute
the local obstruction.  We had shown that the failure of an active zero-star
pair is exactly a family of local first-error witnesses over two-hole colored
cards.  The low-slice descent consequence of that obstruction is false; the
complementary slice is mathematically necessary.

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
      - [x] Prove the cycle adjacency-mismatch lemma: on an all-coherent active
            observer cycle, the host adjacency between two consecutive cycle
            bases disagrees with the host adjacency between their matched
            mates under the chosen minimum matching
            (`ActiveObserverCycle.adjacency_mismatch_at`).
      - [x] Prove the matching moves at least one cycle vertex on an
            all-coherent cycle (`ActiveObserverCycle.exists_moved_by_matching`)
            and cannot fix two consecutive cycle vertices
            (`ActiveObserverCycle.matching_moves_consecutive_at`).
      - [x] Prove the parity lemma for star error:
            `FixedHostCardIsoData.starErrorCount_even` —
            the per-card star error count is always even, since the card iso
            forces equal degrees and the symmetric-difference count is then
            twice the off-diagonal piece.
      - [x] Derive `totalStarErrorCount_even` and
            `cardIso_starErrorCount_ge_two`: in a positive minimum-error
            obstruction, each chosen card iso has star error count ≥ 2,
            so total star error ≥ 2.
      - [x] Formalize twin-difference set and `AreTwins` predicate
            (`twinDifferenceSet`, `AreTwins`, `twinDifferenceSet_comm`,
            `AreTwins.refl`, `AreTwins.symm`).
      - [x] Prove `totalStarErrorCount_ge_two_mul_ncard`: in a positive
            obstruction, total star error ≥ 2 * |singletonLeft|.
      - [x] Prove `LowSliceMinimumErrorMatching.totalStarErrorCount_zero_or_ge`:
            the star-error gap — every minimum-error matching has total error
            either 0 or ≥ 2 * |singletonLeft|.
      - [x] Prove the active observer cycle bounds:
            `minimalPeriod_le_ncard_singletonLeft` and
            `ncard_singletonLeft_ge_two_of_cycle` — observer cycles exist only
            when |singletonLeft| ≥ 2.
      - [x] Close the `T = ∅` special case for the all-active branch:
            `not_allActiveBranches_of_T_empty`.
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
      - [x] **Proper-support sector PROVED** (`SupportCount.lean`;
        standard axioms): `SameDeck.properSupportClosedWalkCount_eq`.
        Machinery: `exactSupportClosedWalkCount_eq_fullSupport_induce`
        (exact-support walks = full-support walks of the induced subgraph,
        via Mathlib's `Walk.induce`/`Walk.map` with a two-injection counting
        argument), `fullSupportClosedWalkCount_eq_of_iso` (iso-invariance),
        `GraphIsoClass` (isomorphism classes of graphs on `Fin m` as a
        finite quotient), and `sum_fullSupport_induce_eq` (regrouping
        subset sums into Kelly-count-weighted class sums).
      - [x] **Full-support sector identified as the Hamiltonian sector**
        (`HamiltonianWalk.lean`; standard axioms):
        `fullSupportClosedWalkCount_card_eq_hamiltonianHomCount` — a closed
        `|V|`-walk with full support has no room to repeat a vertex, so it
        traverses a Hamiltonian cycle; `hamiltonianHomCount` counts the
        injective homs `cycleGraph |V| →g G` (= 2·|V| per Hamiltonian
        cycle). Machinery: `walkOfFn` (walks from vertex sequences),
        `walk_ext_getVert` (walks are determined by their vertex
        sequences), `homRCW` (unrolling an injective hom to a rooted
        closed walk).
      - Added `SameDeck.charPoly_coeff_zero_eq_of_fullSupport_eq` and
        `SameDeck.charPoly_coeff_zero_eq_of_hamiltonianHomCount_eq`: the
        constant term now follows from the **single** hypothesis that the
        Hamiltonian homomorphism counts agree — exactly Tutte's 1979
        theorem, staged as `HamiltonianHomCountReconstructible`.
      - [ ] Prove `HamiltonianHomCountReconstructible` via Kocay: (i)
        Möbius/triangular induction over `coverTypeCount_sum_inducedIsoClass`
        to reconstruct all disconnected spanning-subgraph counts (the
        descending-induction pattern of `Disconnected/ComponentCount.lean`);
        (ii) extract the Hamiltonian count from products of path counts
        (Stark 2025 arXiv:2509.02604 gives the modern elementary route).
        - [x] **Keystone PROVED — Kocay's lemma, deck form**
          (`KocayHost.lean`; standard axioms):
          `SameDeck.coverTypeCount_eq` — host cover counts are
          reconstructible for every pattern family on `< |V|` vertices.
          Via `prod_subgraphCount_eq_coverTypeCount_add` (Kocay's identity
          with the host term isolated) and
          `sum_coverTypeCount_induce_eq` (regrouping proper subsets by
          `GraphIsoClass` with Kelly weights).
        - [x] **Subgraph-copy (non-induced) counting layer — PROVED**
          (`HomCount.lean`; standard axioms): `SameDeck.injHomCount_eq` —
          injective-homomorphism copy counts (= `|Aut F|` × subgraph-copy
          counts) are reconstructible for `|F| < n`. Via the
          partition-by-image identity `injHomCount_eq_sum_induce`
          (`injHomCount F G = ∑_{|U|=|F|} injHomCount F (G[U])`), target-iso
          invariance, and the third instantiation of the `GraphIsoClass`
          regrouping (`sum_injHomCount_induce_eq`).
        - [ ] Vertex-disjointness collapse: for disconnected `D` on `n`
          vertices with components `D₁ … D_m`, every spanning union of
          copies of the `Dᵢ` is `≅ D` (component sizes sum to `n`), so
          `∏ s'(Dᵢ,G)` determines `s'(D,G)` — all disconnected spanning
          subgraph counts in one step.
          - [x] **Tuple layer + staged target landed**
            (`SpanningTuple.lean`; standard axioms): `injTupleCount` with
            the product formula `injTupleCount_eq_prod` and deck-invariance
            `SameDeck.injTupleCount_eq`; the collapse itself stated
            precisely as the `Prop`-valued staged target
            `DisjointSpanningTupleCountReconstructible` (pairwise-disjoint
            spanning placement tuples), with the intended proof recorded:
            partition tuples by image union, regroup by `GraphIsoClass` as
            in `KocayHost.lean`, isolate the full-vertex-set fiber.
        - [ ] Hamiltonian extraction: two-path families `a + b = n + 2`
          and triangular elimination over spanning tree/unicyclic types,
          or Stark's endpoint-refined Hamiltonian-path route.
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
