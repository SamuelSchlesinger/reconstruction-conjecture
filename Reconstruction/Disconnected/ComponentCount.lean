import Reconstruction.KellyLemma
import Reconstruction.ConnectedComponents

set_option autoImplicit false

/-!
# Component Counts and Subgraph Counts

This module develops the **component-count ↔ subgraph-count** machinery needed
for Kelly's 1942 multiset-recovery induction in the reconstruction of
disconnected graphs. The centerpiece is a decomposition identity: for any
connected graph `F`, the number of induced copies of `F` in `G` equals the sum
of induced copies of `F` in each connected component of `G`.

## Main definitions

* `SimpleGraph.componentCount` — for a (connected) graph `F` and a graph `G`,
  the number of connected components of `G` whose induced subgraph is
  isomorphic to `F`.

## Main results

* `SimpleGraph.componentCount_eq_of_iso` — component counts are iso-invariants.
* `SimpleGraph.ConnectedComponent.card_supp_lt_of_not_connected` — in a finite
  disconnected graph, every connected component has fewer vertices than the
  host.
* `SimpleGraph.subgraphCount_eq_sum_over_components` — if `F` is connected,
  `subgraphCount F G = ∑ c, subgraphCount F (G.induce c.supp)`. This is the
  structural identity that lets the reconstruction induction turn subgraph
  counts (given by Kelly's Lemma) into component counts.
* `SimpleGraph.subgraphCount_eq_componentCount_add_larger` — the triangular
  accounting identity: copies of a connected `F` in `G` are the components
  isomorphic to `F`, plus copies lying inside strictly larger components.
* `SimpleGraph.componentIsoClassEquivOfComponentCountEq` — equal component
  counts for a fixed connected-component type give an equivalence between the
  corresponding component fibers.
* `SimpleGraph.componentEquivOfComponentCountEq` — equal component counts for
  every component type assemble into a global component bijection preserving
  component isomorphism classes.
* `SimpleGraph.largerComponentEquivOfComponentCountEq` — equal component counts
  for every component type above a size threshold assemble into the restricted
  larger-component matching used by the triangular induction.
* `SimpleGraph.SameDeck.componentCount_eq_components_of_not_connected` — the
  descending triangular induction recovering every represented component
  isomorphism class in two same-deck disconnected graphs.

## References

* Kelly, P. J. (1942). "On isometric transformations".
-/

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical

variable {W V : Type*} [Fintype W] [Fintype V]

/-- The number of connected components of `G` whose induced subgraph
`G.induce c.supp` is isomorphic to the reference graph `F`. -/
def componentCount (F : SimpleGraph W) (G : SimpleGraph V) : ℕ :=
  Fintype.card
    { c : G.ConnectedComponent // Nonempty (G.induce (c.supp : Set V) ≃g F) }

/-! ### Component size in disconnected graphs -/

omit [Fintype V] in
/-- If one connected component contains every vertex, then the graph is
connected. -/
theorem connected_of_component_supp_eq_univ {G : SimpleGraph V}
    (C : G.ConnectedComponent) (hC : C.supp = Set.univ) : G.Connected := by
  haveI : Nonempty V := by
    obtain ⟨v, _hv⟩ := C.nonempty_supp
    exact ⟨v⟩
  refine ⟨?_⟩
  intro u v
  have hu : u ∈ C.supp := by rw [hC]; simp
  have hv : v ∈ C.supp := by rw [hC]; simp
  exact C.reachable_of_mem_supp hu hv

/-- In a disconnected finite graph, every connected component is a proper
vertex subset. In particular, component graphs are small enough for Kelly's
Lemma whenever the host graph is disconnected. -/
theorem ConnectedComponent.card_supp_lt_of_not_connected {G : SimpleGraph V}
    (hG : ¬ G.Connected) (C : G.ConnectedComponent) :
    Fintype.card C.supp < Fintype.card V := by
  by_cases hC : C.supp = Set.univ
  · exact (hG (connected_of_component_supp_eq_univ C hC)).elim
  · have hout : ∃ v : V, v ∉ C.supp := by
      contrapose! hC
      ext v
      simp [hC v]
    obtain ⟨v, hv⟩ := hout
    exact Fintype.card_subtype_lt (p := fun v : V => v ∈ C.supp) hv

/-! ### Isomorphism invariance of `componentCount` -/

section IsoInvariance

variable {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
variable {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}

/-- Transport the induced subgraph under a component bijection: if
`φ : G₁ ≃g G₂` and `C : G₁.ConnectedComponent`, then
`G₁.induce C.supp ≃g G₂.induce (φ.connectedComponentEquiv C).supp`. -/
private def induceSuppIso (φ : G₁ ≃g G₂) (C : G₁.ConnectedComponent) :
    G₁.induce (C.supp : Set V₁) ≃g
      G₂.induce ((φ.connectedComponentEquiv C).supp : Set V₂) where
  toEquiv := ConnectedComponent.isoEquivSupp φ C
  map_rel_iff' {a b} := φ.map_rel_iff (a := a.1) (b := b.1)

omit [Fintype W] in
/-- Component counts are invariant under graph isomorphism. -/
theorem componentCount_eq_of_iso (F : SimpleGraph W) (φ : G₁ ≃g G₂) :
    componentCount F G₁ = componentCount F G₂ := by
  unfold componentCount
  refine Fintype.card_congr ?_
  refine
    { toFun := fun ⟨C, hC⟩ => ⟨φ.connectedComponentEquiv C, ?_⟩
      invFun := fun ⟨D, hD⟩ => ⟨φ.connectedComponentEquiv.symm D, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact hC.map ((induceSuppIso φ C).symm.trans ·)
  · -- `induceSuppIso φ.symm D : G₂.induce D.supp ≃g G₁.induce ((φ.symm.ce) D).supp`.
    have hD' :
        Nonempty (G₁.induce
          ((φ.symm.connectedComponentEquiv D).supp : Set V₁) ≃g F) := by
      refine hD.map ((induceSuppIso φ.symm D).symm.trans ·)
    -- rewrite back using `connectedComponentEquiv_symm`
    have heq :
        φ.symm.connectedComponentEquiv D = φ.connectedComponentEquiv.symm D := by
      rw [Iso.connectedComponentEquiv_symm]
    rwa [heq] at hD'
  · rintro ⟨C, _⟩
    apply Subtype.ext
    exact Equiv.symm_apply_apply _ C
  · rintro ⟨D, _⟩
    apply Subtype.ext
    exact Equiv.apply_symm_apply _ D

end IsoInvariance

/-! ### Small host and equal-size host counts -/

/-- If the host graph has fewer vertices than `F`, then it has no induced
copies of `F`. -/
theorem subgraphCount_eq_zero_of_card_lt (F : SimpleGraph W) (G : SimpleGraph V)
    (hcard : Fintype.card V < Fintype.card W) :
    F.subgraphCount G = 0 := by
  unfold subgraphCount
  rw [Finset.card_eq_zero]
  rw [Finset.eq_empty_iff_forall_notMem]
  intro S hS
  have hS_card := F.copyFinset_card G hS
  have hS_le : S.card ≤ Fintype.card V := by
    simpa using S.card_le_univ
  omega

/-- If the host graph and `F` have the same number of vertices, then the
induced-copy count is all-or-nothing: it is `1` if the whole host is
isomorphic to `F`, and `0` otherwise. -/
theorem subgraphCount_eq_one_or_zero_of_card_eq
    (F : SimpleGraph W) (G : SimpleGraph V)
    (hcard : Fintype.card W = Fintype.card V) :
    F.subgraphCount G = if Nonempty (G ≃g F) then 1 else 0 := by
  unfold subgraphCount
  by_cases hIso : Nonempty (G ≃g F)
  · rw [if_pos hIso]
    have hcopy : F.copyFinset G = {Finset.univ} := by
      ext S
      rw [mem_copyFinset]
      simp only [Finset.mem_singleton]
      constructor
      · intro hS
        exact (Finset.card_eq_iff_eq_univ S).mp (by simpa [hcard] using hS.1)
      · intro hS
        subst hS
        refine ⟨by simp [hcard], ?_⟩
        change Nonempty (G.induce (↑(Finset.univ : Finset V) : Set V) ≃g F)
        rw [show (↑(Finset.univ : Finset V) : Set V) = Set.univ by
          ext x
          simp]
        exact hIso.map (fun iso => (induceUnivIso G).trans iso)
    rw [hcopy, Finset.card_singleton]
  · rw [if_neg hIso]
    rw [Finset.card_eq_zero]
    rw [Finset.eq_empty_iff_forall_notMem]
    intro S hS
    have hS' := (mem_copyFinset F G S).mp hS
    have hSuniv : S = Finset.univ :=
      (Finset.card_eq_iff_eq_univ S).mp (by simpa [hcard] using hS'.1)
    subst hSuniv
    apply hIso
    have hcopy : Nonempty (G.induce Set.univ ≃g F) := by
      rw [← show (↑(Finset.univ : Finset V) : Set V) = Set.univ by
        ext x
        simp]
      exact hS'.2
    exact hcopy.map (fun iso => (induceUnivIso G).symm.trans iso)

/-! ### Component decomposition of `subgraphCount`

For `F` connected and `G` arbitrary, every copy of `F` in `G` sits inside a
single connected component of `G`. We prove this and then show
`subgraphCount F G = ∑ c, subgraphCount F (G.induce c.supp)`.
-/

section ComponentDecomposition

variable [DecidableEq V]
variable (F : SimpleGraph W) (G : SimpleGraph V)

omit [Fintype V] [DecidableEq V] in
/-- If `G.induce S` is (pre-)connected and nonempty, then all vertices of `S`
lie in a single connected component of `G`. -/
private lemma exists_comp_supset_of_induce_connected
    {S : Finset V} (hne : S.Nonempty)
    (hconn : (G.induce (S : Set V)).Preconnected) :
    ∃ c : G.ConnectedComponent, ∀ v ∈ S, v ∈ c.supp := by
  -- Pick a witness vertex from S and build the component from it.
  obtain ⟨v₀, hv₀⟩ := hne
  refine ⟨G.connectedComponentMk v₀, fun v hv => ?_⟩
  -- We must show `G.connectedComponentMk v = G.connectedComponentMk v₀`.
  -- Use reachability inside `G.induce S` and the embedding `Embedding.induce`.
  have hreach_sub : (G.induce (S : Set V)).Reachable ⟨v, hv⟩ ⟨v₀, hv₀⟩ :=
    hconn ⟨v, hv⟩ ⟨v₀, hv₀⟩
  -- Map the walk into `G`.
  have hreach : G.Reachable v v₀ :=
    hreach_sub.map (Embedding.induce (S : Set V)).toHom
  -- Hence `v ∈ connectedComponentMk v₀`.
  exact ConnectedComponent.eq.mpr hreach

omit [DecidableEq V] in
/-- If `F` is connected and `S ∈ F.copyFinset G`, then all vertices of `S` lie
in a single connected component of `G`. -/
private lemma exists_comp_supset_of_mem_copyFinset
    (hF : F.Connected) {S : Finset V} (hS : S ∈ F.copyFinset G) :
    ∃ c : G.ConnectedComponent, ∀ v ∈ S, v ∈ c.supp := by
  obtain ⟨hcard, ⟨iso⟩⟩ := (mem_copyFinset F G S).mp hS
  -- `S` is nonempty because `W` is nonempty (from `F.Connected`).
  haveI : Nonempty W := hF.nonempty
  have hWpos : 0 < Fintype.card W := Fintype.card_pos
  have hSpos : 0 < S.card := hcard ▸ hWpos
  have hne : S.Nonempty := Finset.card_pos.mp hSpos
  -- `G.induce ↑S` is connected (via the iso to `F`).
  have hconn_sub : (G.induce (S : Set V)).Connected := iso.connected_iff.mpr hF
  exact exists_comp_supset_of_induce_connected G hne hconn_sub.preconnected

/-- The classifying component of a copy `S ∈ F.copyFinset G`. -/
private noncomputable def classifyComp
    (hF : F.Connected) {S : Finset V} (hS : S ∈ F.copyFinset G) :
    G.ConnectedComponent :=
  (exists_comp_supset_of_mem_copyFinset F G hF hS).choose

omit [DecidableEq V] in
private lemma classifyComp_spec (hF : F.Connected)
    {S : Finset V} (hS : S ∈ F.copyFinset G) :
    ∀ v ∈ S, v ∈ (classifyComp F G hF hS).supp :=
  (exists_comp_supset_of_mem_copyFinset F G hF hS).choose_spec

/-- For a fixed component `c`, the fiber of copies `S` with all vertices in
`c.supp` bijects with `F.copyFinset (G.induce c.supp)`. -/
private theorem fiber_bij_copyFinset_induce (_hF : F.Connected)
    (c : G.ConnectedComponent) :
    ((F.copyFinset G).filter (fun S => ∀ v ∈ S, v ∈ c.supp)).card =
      F.subgraphCount (G.induce (c.supp : Set V)) := by
  unfold subgraphCount
  -- Build a bijection: a finset `S` of V with all vertices in c.supp
  -- corresponds to `S.subtype (· ∈ c.supp) : Finset c.supp`.
  refine Finset.card_bij'
    (fun S _ => S.subtype (· ∈ c.supp))
    (fun T _ => T.map (Function.Embedding.subtype _))
    (fun S hS => ?fwd) (fun T hT => ?bwd) (fun S hS => ?linv) (fun T hT => ?rinv)
  case fwd =>
    rw [Finset.mem_filter] at hS
    obtain ⟨hS_mem, hS_sub⟩ := hS
    have hS' := (mem_copyFinset F G S).mp hS_mem
    rw [mem_copyFinset]
    -- Cardinality: S.subtype has card = S.filter (· ∈ c.supp) which equals S.
    have hfilt : S.filter (fun v => v ∈ c.supp) = S :=
      Finset.filter_true_of_mem (fun v hv => hS_sub v hv)
    refine ⟨by rw [Finset.card_subtype, hfilt]; exact hS'.1, ?_⟩
    -- Need: (G.induce c.supp).induce ↑(S.subtype _) ≃g F.
    -- Use the iso on ↑S and build a subtype equivalence.
    exact hS'.2.map fun iso => by
      -- Forward on underlying sets: elements of the subtype landing in the
      -- induced graph are wrapped twice; forget the wrapping.
      let fwd :
          (↑(S.subtype (· ∈ c.supp)) : Set c.supp) →
            (↑S : Set V) := fun x =>
        ⟨x.1.1, by
          have : x.1 ∈ S.subtype (· ∈ c.supp) :=
            Finset.mem_coe.mp x.2
          rw [Finset.mem_subtype] at this
          exact Finset.mem_coe.mpr this⟩
      let bwd :
          (↑S : Set V) → (↑(S.subtype (· ∈ c.supp)) : Set c.supp) := fun y =>
        ⟨⟨y.1, hS_sub y.1 (Finset.mem_coe.mp y.2)⟩, by
          rw [Finset.mem_coe, Finset.mem_subtype]
          exact Finset.mem_coe.mp y.2⟩
      have hleft : Function.LeftInverse bwd fwd := fun x => by ext; rfl
      have hright : Function.RightInverse bwd fwd := fun y => by ext; rfl
      exact ({ toEquiv := ⟨fwd, bwd, hleft, hright⟩, map_rel_iff' := Iff.rfl } :
        (G.induce (c.supp : Set V)).induce
            (↑(S.subtype (· ∈ c.supp)) : Set c.supp) ≃g
          G.induce (↑S : Set V)).trans iso
  case bwd =>
    have hT' := (mem_copyFinset F (G.induce (c.supp : Set V)) T).mp hT
    rw [Finset.mem_filter]
    refine ⟨(mem_copyFinset F G _).mpr
      ⟨by rw [Finset.card_map]; exact hT'.1, ?_⟩, ?_⟩
    · -- Need: G.induce ↑(T.map subtype) ≃g F.
      exact hT'.2.map fun iso => by
        let fwd :
            (↑(T.map (Function.Embedding.subtype (· ∈ c.supp))) : Set V) →
              (↑T : Set c.supp) := fun x =>
          ⟨⟨x.1,
            by
              have hx := Finset.mem_coe.mp x.2
              rw [Finset.mem_map] at hx
              obtain ⟨⟨w, hw⟩, _, heq⟩ := hx
              simp only [Function.Embedding.subtype_apply] at heq
              subst heq
              exact hw⟩,
            by
              have hx := Finset.mem_coe.mp x.2
              rw [Finset.mem_map] at hx
              obtain ⟨⟨w, hw⟩, hT_mem, heq⟩ := hx
              simp only [Function.Embedding.subtype_apply] at heq
              -- heq : w = x.1. After subst, the membership witness uses the
              -- same underlying value.
              subst heq
              exact Finset.mem_coe.mpr hT_mem⟩
        let bwd :
            (↑T : Set c.supp) →
              (↑(T.map (Function.Embedding.subtype (· ∈ c.supp))) : Set V) :=
          fun y => ⟨y.1.1,
            Finset.mem_coe.mpr (Finset.mem_map.mpr
              ⟨y.1, Finset.mem_coe.mp y.2, rfl⟩)⟩
        have hleft : Function.LeftInverse bwd fwd := fun x => by ext; rfl
        have hright : Function.RightInverse bwd fwd := fun y => by ext; rfl
        exact ({ toEquiv := ⟨fwd, bwd, hleft, hright⟩, map_rel_iff' := Iff.rfl } :
          G.induce (↑(T.map (Function.Embedding.subtype (· ∈ c.supp)))) ≃g
            (G.induce (c.supp : Set V)).induce (↑T : Set c.supp)).trans iso
    · -- All vertices of T.map subtype lie in c.supp.
      intro v hv
      rw [Finset.mem_map] at hv
      obtain ⟨⟨w, hw⟩, _, rfl⟩ := hv
      exact hw
  case linv =>
    -- S.subtype then map subtype = S (since S ⊆ c.supp).
    rw [Finset.mem_filter] at hS
    obtain ⟨_, hS_sub⟩ := hS
    change (S.subtype (· ∈ c.supp)).map (Function.Embedding.subtype _) = S
    rw [Finset.subtype_map]
    exact Finset.filter_true_of_mem (fun v hv => hS_sub v hv)
  case rinv =>
    -- map subtype then subtype = T.
    ext ⟨w, hw⟩
    simp only [Finset.mem_subtype, Finset.mem_map, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨⟨w', hw'⟩, ht, heq⟩
      cases heq
      exact ht
    · intro h
      exact ⟨⟨w, hw⟩, h, rfl⟩

/-- **Component decomposition for subgraph counts.** If `F` is connected, the
number of induced copies of `F` in `G` equals the sum, over connected
components `c` of `G`, of the number of induced copies of `F` in the
component-induced subgraph `G.induce c.supp`. -/
theorem subgraphCount_eq_sum_over_components (hF : F.Connected) :
    F.subgraphCount G =
    ∑ c : G.ConnectedComponent,
      F.subgraphCount (G.induce (c.supp : Set V)) := by
  -- Step 1: Rewrite the LHS as a sum of fiber cardinalities over components,
  -- using that every copy lies in a single component.
  have hfib :
      (F.copyFinset G).card =
        ∑ c : G.ConnectedComponent,
          ((F.copyFinset G).filter (fun S => ∀ v ∈ S, v ∈ c.supp)).card := by
    classical
    -- Case split on whether V is empty.
    by_cases hne : Nonempty V
    · -- When V is nonempty, pick a default vertex and build a total classifier.
      obtain ⟨v₀⟩ := hne
      set default_comp : G.ConnectedComponent := G.connectedComponentMk v₀
      refine (Finset.card_eq_sum_card_fiberwise
        (f := fun S => if h : S ∈ F.copyFinset G
                       then classifyComp F G hF h
                       else default_comp)
        (s := F.copyFinset G) (t := (Finset.univ : Finset G.ConnectedComponent))
        ?_).trans ?_
      · intro S _; exact Finset.mem_univ _
      · refine Finset.sum_congr rfl fun c _ => ?_
        -- Fiber {S | classify S = c} (restricted to copyFinset) equals
        -- {S ∈ copyFinset | ∀ v ∈ S, v ∈ c.supp}.
        congr 1
        ext S
        simp only [Finset.mem_filter]
        refine and_congr_right ?_
        intro hS
        rw [dif_pos hS]
        constructor
        · intro hclass v hv
          have := classifyComp_spec F G hF hS v hv
          rw [hclass] at this
          exact this
        · intro hall
          -- classifyComp's component contains v for any v ∈ S; v ∈ c.supp;
          -- components are disjoint, so they coincide.
          have h1 := classifyComp_spec F G hF hS
          -- pick a witness vertex v in S
          haveI : Nonempty W := hF.nonempty
          have hWpos : 0 < Fintype.card W := Fintype.card_pos
          have hSpos : 0 < S.card := by
            rw [((mem_copyFinset F G S).mp hS).1]; exact hWpos
          obtain ⟨v, hv⟩ := Finset.card_pos.mp hSpos
          have hv_classify : v ∈ (classifyComp F G hF hS).supp := h1 v hv
          have hv_c : v ∈ c.supp := hall v hv
          rw [ConnectedComponent.mem_supp_iff] at hv_classify hv_c
          exact hv_classify.symm.trans hv_c
    · -- When V is empty, both sides are 0 (no copies, no components).
      rw [not_nonempty_iff] at hne
      have hempty : F.copyFinset G = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro S hS
        -- A copy has ≥ 1 vertex (since F is connected → W is nonempty).
        haveI : Nonempty W := hF.nonempty
        have : 0 < S.card := by
          rw [((mem_copyFinset F G S).mp hS).1]; exact Fintype.card_pos
        obtain ⟨v, _⟩ := Finset.card_pos.mp this
        exact hne.false v
      rw [hempty, Finset.card_empty]
      haveI : IsEmpty G.ConnectedComponent :=
        ⟨fun c => c.ind (fun v => hne.false v)⟩
      exact (Finset.sum_of_isEmpty _).symm
  -- Step 2: Rewrite each fiber via the bijection with copyFinset in the
  -- component-induced subgraph.
  unfold subgraphCount
  rw [hfib]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact fiber_bij_copyFinset_induce F G hF c

/-! ### Triangular component-count accounting -/

omit [Fintype W] in
/-- Component counts as a sum of indicator functions over connected
components. This is the cardinality form used when separating equal-size
components from larger components. -/
theorem componentCount_eq_sum_ite (F : SimpleGraph W) (G : SimpleGraph V) :
    F.componentCount G =
      ∑ c : G.ConnectedComponent,
        if Nonempty (G.induce (c.supp : Set V) ≃g F) then 1 else 0 := by
  unfold componentCount
  rw [Fintype.card_subtype]
  let p : G.ConnectedComponent → Prop := fun c =>
    Nonempty (G.induce (c.supp : Set V) ≃g F)
  change (Finset.univ.filter p).card =
    ∑ c : G.ConnectedComponent, if p c then 1 else 0
  exact (Finset.sum_boole p (Finset.univ : Finset G.ConnectedComponent)).symm

/-- On components with the same number of vertices as `F`, the induced-copy
sum is exactly the component count for `F`. -/
theorem componentCount_eq_sum_same_card_subgraphCount
    (F : SimpleGraph W) (G : SimpleGraph V) :
    F.componentCount G =
      ∑ c ∈ ((Finset.univ : Finset G.ConnectedComponent).filter
          fun c => Fintype.card c.supp = Fintype.card W),
        F.subgraphCount (G.induce (c.supp : Set V)) := by
  rw [componentCount_eq_sum_ite]
  let p : G.ConnectedComponent → Prop := fun c => Fintype.card c.supp = Fintype.card W
  let I : G.ConnectedComponent → ℕ := fun c =>
    if Nonempty (G.induce (c.supp : Set V) ≃g F) then 1 else 0
  change (∑ c : G.ConnectedComponent, I c) =
    ∑ c ∈ (Finset.univ.filter p), F.subgraphCount (G.induce (c.supp : Set V))
  calc
    (∑ c : G.ConnectedComponent, I c)
        = ∑ c : G.ConnectedComponent, if p c then I c else 0 := by
          apply Finset.sum_congr rfl
          intro c _
          by_cases hp : p c
          · simp [hp]
          · simp only [hp, if_false]
            unfold I
            by_cases hIso : Nonempty (G.induce (c.supp : Set V) ≃g F)
            · simp only [hIso, if_true]
              exfalso
              exact hp (Fintype.card_congr hIso.some.toEquiv)
            · simp [hIso]
      _ = ∑ c ∈ (Finset.univ.filter p), I c := by
          simpa using (Finset.sum_filter
            (s := (Finset.univ : Finset G.ConnectedComponent)) (p := p)
            (f := I)).symm
      _ = ∑ c ∈ (Finset.univ.filter p),
            F.subgraphCount (G.induce (c.supp : Set V)) := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [Finset.mem_filter] at hc
          have hcard : Fintype.card W = Fintype.card c.supp := hc.2.symm
          rw [subgraphCount_eq_one_or_zero_of_card_eq
            F (G.induce (c.supp : Set V)) hcard]

/-- **Triangular component-count accounting.** If `F` is connected, then every
induced copy of `F` in `G` is either an entire connected component isomorphic
to `F`, or it lies inside a strictly larger connected component. This identity
is the bookkeeping step behind Kelly's disconnected-graph reconstruction
induction. -/
theorem subgraphCount_eq_componentCount_add_larger (hF : F.Connected) :
    F.subgraphCount G =
      F.componentCount G +
        ∑ c ∈ ((Finset.univ : Finset G.ConnectedComponent).filter
            fun c => Fintype.card W < Fintype.card c.supp),
          F.subgraphCount (G.induce (c.supp : Set V)) := by
  rw [subgraphCount_eq_sum_over_components F G hF]
  rw [componentCount_eq_sum_same_card_subgraphCount F G]
  let f : G.ConnectedComponent → ℕ := fun c =>
    F.subgraphCount (G.induce (c.supp : Set V))
  let pEq : G.ConnectedComponent → Prop := fun c =>
    Fintype.card c.supp = Fintype.card W
  let pGt : G.ConnectedComponent → Prop := fun c =>
    Fintype.card W < Fintype.card c.supp
  change (∑ c : G.ConnectedComponent, f c) =
    (∑ c ∈ (Finset.univ.filter pEq), f c) +
      ∑ c ∈ (Finset.univ.filter pGt), f c
  calc
    (∑ c : G.ConnectedComponent, f c)
        = ∑ c : G.ConnectedComponent,
            ((if pEq c then f c else 0) + (if pGt c then f c else 0)) := by
          apply Finset.sum_congr rfl
          intro c _
          by_cases heq : pEq c
          · have hnot_gt : ¬ pGt c := by omega
            simp [heq, hnot_gt]
          · by_cases hgt : pGt c
            · simp [heq, hgt]
            · have hlt : Fintype.card c.supp < Fintype.card W := by omega
              have hfzero : f c = 0 := by
                unfold f
                exact subgraphCount_eq_zero_of_card_lt
                  F (G.induce (c.supp : Set V)) hlt
              simp [heq, hgt, hfzero]
      _ = (∑ c : G.ConnectedComponent, if pEq c then f c else 0) +
            ∑ c : G.ConnectedComponent, if pGt c then f c else 0 := by
          rw [Finset.sum_add_distrib]
      _ = (∑ c ∈ (Finset.univ.filter pEq), f c) +
            ∑ c ∈ (Finset.univ.filter pGt), f c := by
          rw [Finset.sum_filter, Finset.sum_filter]

end ComponentDecomposition

section ReconstructibilityStep

variable [DecidableEq V]
variable {G H : SimpleGraph V}

/-- If the strictly larger components of `G` and `H` can be paired by
isomorphism, then they make the same contribution to the triangular
component-count identity for `F`.

This is the bookkeeping form of the induction hypothesis in Kelly's
component-multiset recovery: once all components larger than `F` have been
matched by isomorphism, the larger-component error term is known to agree. -/
theorem largerComponentSubgraphCount_sum_eq_of_isoEquiv
    (F : SimpleGraph W)
    (e :
      { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } ≃
      { c : H.ConnectedComponent // Fintype.card W < Fintype.card c.supp })
    (hiso :
      ∀ c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp },
        Nonempty
          (G.induce ((c : G.ConnectedComponent).supp : Set V) ≃g
            H.induce (((e c : H.ConnectedComponent).supp : Set V)))) :
    (∑ c ∈ ((Finset.univ : Finset G.ConnectedComponent).filter
        fun c => Fintype.card W < Fintype.card c.supp),
      F.subgraphCount (G.induce (c.supp : Set V))) =
    (∑ c ∈ ((Finset.univ : Finset H.ConnectedComponent).filter
        fun c => Fintype.card W < Fintype.card c.supp),
      F.subgraphCount (H.induce (c.supp : Set V))) := by
  let pG : G.ConnectedComponent → Prop := fun c =>
    Fintype.card W < Fintype.card c.supp
  let pH : H.ConnectedComponent → Prop := fun c =>
    Fintype.card W < Fintype.card c.supp
  let fG : G.ConnectedComponent → ℕ := fun c =>
    F.subgraphCount (G.induce (c.supp : Set V))
  let fH : H.ConnectedComponent → ℕ := fun c =>
    F.subgraphCount (H.induce (c.supp : Set V))
  change (∑ c ∈ (Finset.univ.filter pG), fG c) =
    ∑ c ∈ (Finset.univ.filter pH), fH c
  rw [Finset.sum_subtype (s := (Finset.univ : Finset G.ConnectedComponent).filter pG)
      (p := pG) (f := fG) (by intro c; simp [pG]),
    Finset.sum_subtype (s := (Finset.univ : Finset H.ConnectedComponent).filter pH)
      (p := pH) (f := fH) (by intro c; simp [pH])]
  calc
    (∑ c : { c : G.ConnectedComponent // pG c }, fG c)
        = ∑ c : { c : G.ConnectedComponent // pG c }, fH (e c) := by
          apply Finset.sum_congr rfl
          intro c _
          exact subgraphCount_eq_of_iso F (hiso c).some
    _ = ∑ c : { c : H.ConnectedComponent // pH c }, fH c :=
          e.sum_comp (fun c : { c : H.ConnectedComponent // pH c } => fH c)

/-- The cancellative step for the disconnected-graph induction. If the
strictly-larger-component contribution for a connected graph `F` is already
known to agree for two same-deck graphs, then the number of connected
components isomorphic to `F` agrees as well. -/
theorem SameDeck.componentCount_eq_of_larger_sum_eq
    (h : G.SameDeck H) (F : SimpleGraph W) (hF : F.Connected)
    (hcard : Fintype.card W < Fintype.card V)
    (hlarger :
      (∑ c ∈ ((Finset.univ : Finset G.ConnectedComponent).filter
          fun c => Fintype.card W < Fintype.card c.supp),
        F.subgraphCount (G.induce (c.supp : Set V))) =
      (∑ c ∈ ((Finset.univ : Finset H.ConnectedComponent).filter
          fun c => Fintype.card W < Fintype.card c.supp),
        F.subgraphCount (H.induce (c.supp : Set V)))) :
    F.componentCount G = F.componentCount H := by
  have hsub := h.subgraphCount_eq F hcard
  have hG := subgraphCount_eq_componentCount_add_larger (F := F) (G := G) hF
  have hH := subgraphCount_eq_componentCount_add_larger (F := F) (G := H) hF
  rw [hG, hH] at hsub
  rw [hlarger] at hsub
  exact Nat.add_right_cancel hsub

/-- The local triangular induction step for component-multiset recovery.

For a connected graph `F` with fewer vertices than the host graphs, suppose
that all strictly larger components of `G` and `H` have already been paired by
isomorphism. Then the number of connected components isomorphic to `F` agrees
between `G` and `H`. -/
theorem SameDeck.componentCount_eq_of_larger_component_isoEquiv
    (h : G.SameDeck H) (F : SimpleGraph W) (hF : F.Connected)
    (hcard : Fintype.card W < Fintype.card V)
    (e :
      { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } ≃
      { c : H.ConnectedComponent // Fintype.card W < Fintype.card c.supp })
    (hiso :
      ∀ c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp },
        Nonempty
          (G.induce ((c : G.ConnectedComponent).supp : Set V) ≃g
            H.induce (((e c : H.ConnectedComponent).supp : Set V)))) :
    F.componentCount G = F.componentCount H :=
  h.componentCount_eq_of_larger_sum_eq F hF hcard
    (largerComponentSubgraphCount_sum_eq_of_isoEquiv (G := G) (H := H) F e hiso)

end ReconstructibilityStep

section ComponentClassMatching

variable {G H : SimpleGraph V}

/-! The next few private definitions build a common quotient of the connected
components of `G` and `H` by component-graph isomorphism. The public theorem
below then uses fiberwise cardinal equality over this quotient to assemble a
global component matching. -/

/-- The disjoint union of the component sets of two graphs. -/
private abbrev ComponentSide (G H : SimpleGraph V) :=
  G.ConnectedComponent ⊕ H.ConnectedComponent

/-- Two components, possibly from different graphs, are equivalent when their
induced component graphs are isomorphic. -/
private def componentSideIsoRel (G H : SimpleGraph V) :
    ComponentSide G H → ComponentSide G H → Prop
  | Sum.inl c, Sum.inl c' =>
      Nonempty (G.induce (c.supp : Set V) ≃g G.induce (c'.supp : Set V))
  | Sum.inl c, Sum.inr d =>
      Nonempty (G.induce (c.supp : Set V) ≃g H.induce (d.supp : Set V))
  | Sum.inr d, Sum.inl c =>
      Nonempty (H.induce (d.supp : Set V) ≃g G.induce (c.supp : Set V))
  | Sum.inr d, Sum.inr d' =>
      Nonempty (H.induce (d.supp : Set V) ≃g H.induce (d'.supp : Set V))

/-- Component-graph isomorphism is an equivalence relation on the combined
component set of `G` and `H`. -/
private def componentSideSetoid (G H : SimpleGraph V) : Setoid (ComponentSide G H) where
  r := componentSideIsoRel G H
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro x
      cases x <;> exact ⟨RelIso.refl _⟩
    · intro x y hxy
      cases x <;> cases y <;> exact hxy.map RelIso.symm
    · intro x y z hxy hyz
      cases x <;> cases y <;> cases z <;> exact ⟨hxy.some.trans hyz.some⟩

/-- The common finite set of component isomorphism classes represented in
either `G` or `H`. -/
private abbrev ComponentIsoClass (G H : SimpleGraph V) :=
  Quotient (componentSideSetoid G H)

private def componentIsoClassOfG (c : G.ConnectedComponent) : ComponentIsoClass G H :=
  Quotient.mk (componentSideSetoid G H) (Sum.inl c)

private def componentIsoClassOfH (d : H.ConnectedComponent) : ComponentIsoClass G H :=
  Quotient.mk (componentSideSetoid G H) (Sum.inr d)

private noncomputable def componentIsoClassFiberGEquiv (c : G.ConnectedComponent) :
    { c' : G.ConnectedComponent // componentIsoClassOfG (G := G) (H := H) c' =
        componentIsoClassOfG (G := G) (H := H) c } ≃
      { c' : G.ConnectedComponent //
        Nonempty (G.induce (c'.supp : Set V) ≃g G.induce (c.supp : Set V)) } where
  toFun c' := ⟨c'.1, Quotient.exact c'.2⟩
  invFun c' := ⟨c'.1, Quotient.sound c'.2⟩
  left_inv c' := by ext; rfl
  right_inv c' := by ext; rfl

private noncomputable def componentIsoClassFiberHOverGEquiv (c : G.ConnectedComponent) :
    { d : H.ConnectedComponent // componentIsoClassOfH (G := G) (H := H) d =
        componentIsoClassOfG (G := G) (H := H) c } ≃
      { d : H.ConnectedComponent //
        Nonempty (H.induce (d.supp : Set V) ≃g G.induce (c.supp : Set V)) } where
  toFun d := ⟨d.1, Quotient.exact d.2⟩
  invFun d := ⟨d.1, Quotient.sound d.2⟩
  left_inv d := by ext; rfl
  right_inv d := by ext; rfl

private noncomputable def componentIsoClassFiberGOverHEquiv (d : H.ConnectedComponent) :
    { c : G.ConnectedComponent // componentIsoClassOfG (G := G) (H := H) c =
        componentIsoClassOfH (G := G) (H := H) d } ≃
      { c : G.ConnectedComponent //
        Nonempty (G.induce (c.supp : Set V) ≃g H.induce (d.supp : Set V)) } where
  toFun c := ⟨c.1, Quotient.exact c.2⟩
  invFun c := ⟨c.1, Quotient.sound c.2⟩
  left_inv c := by ext; rfl
  right_inv c := by ext; rfl

private noncomputable def componentIsoClassFiberHEquiv (d : H.ConnectedComponent) :
    { d' : H.ConnectedComponent // componentIsoClassOfH (G := G) (H := H) d' =
        componentIsoClassOfH (G := G) (H := H) d } ≃
      { d' : H.ConnectedComponent //
        Nonempty (H.induce (d'.supp : Set V) ≃g H.induce (d.supp : Set V)) } where
  toFun d' := ⟨d'.1, Quotient.exact d'.2⟩
  invFun d' := ⟨d'.1, Quotient.sound d'.2⟩
  left_inv d' := by ext; rfl
  right_inv d' := by ext; rfl

private theorem componentIsoClassFiberG_card (c : G.ConnectedComponent) :
    Fintype.card
        { c' : G.ConnectedComponent // componentIsoClassOfG (G := G) (H := H) c' =
          componentIsoClassOfG (G := G) (H := H) c } =
      (G.induce (c.supp : Set V)).componentCount G := by
  unfold componentCount
  exact Fintype.card_congr (componentIsoClassFiberGEquiv (G := G) (H := H) c)

private theorem componentIsoClassFiberH_over_G_card (c : G.ConnectedComponent) :
    Fintype.card
        { d : H.ConnectedComponent // componentIsoClassOfH (G := G) (H := H) d =
          componentIsoClassOfG (G := G) (H := H) c } =
      (G.induce (c.supp : Set V)).componentCount H := by
  unfold componentCount
  exact Fintype.card_congr (componentIsoClassFiberHOverGEquiv (G := G) (H := H) c)

private theorem componentIsoClassFiberG_over_H_card (d : H.ConnectedComponent) :
    Fintype.card
        { c : G.ConnectedComponent // componentIsoClassOfG (G := G) (H := H) c =
          componentIsoClassOfH (G := G) (H := H) d } =
      (H.induce (d.supp : Set V)).componentCount G := by
  unfold componentCount
  exact Fintype.card_congr (componentIsoClassFiberGOverHEquiv (G := G) (H := H) d)

private theorem componentIsoClassFiberH_card (d : H.ConnectedComponent) :
    Fintype.card
        { d' : H.ConnectedComponent // componentIsoClassOfH (G := G) (H := H) d' =
          componentIsoClassOfH (G := G) (H := H) d } =
      (H.induce (d.supp : Set V)).componentCount H := by
  unfold componentCount
  exact Fintype.card_congr (componentIsoClassFiberHEquiv (G := G) (H := H) d)

private theorem componentIsoClassFiber_card_eq
    (hGcount : ∀ c : G.ConnectedComponent,
      (G.induce (c.supp : Set V)).componentCount G =
        (G.induce (c.supp : Set V)).componentCount H)
    (hHcount : ∀ d : H.ConnectedComponent,
      (H.induce (d.supp : Set V)).componentCount G =
        (H.induce (d.supp : Set V)).componentCount H)
    (q : ComponentIsoClass G H) :
    Fintype.card
        { c : G.ConnectedComponent // componentIsoClassOfG (G := G) (H := H) c = q } =
      Fintype.card
        { d : H.ConnectedComponent // componentIsoClassOfH (G := G) (H := H) d = q } := by
  refine Quotient.inductionOn q ?_
  rintro (c | d)
  · calc
      Fintype.card
          { c' : G.ConnectedComponent // componentIsoClassOfG (G := G) (H := H) c' =
            componentIsoClassOfG (G := G) (H := H) c }
          = (G.induce (c.supp : Set V)).componentCount G :=
              componentIsoClassFiberG_card (G := G) (H := H) c
      _ = (G.induce (c.supp : Set V)).componentCount H := hGcount c
      _ = Fintype.card
          { d : H.ConnectedComponent // componentIsoClassOfH (G := G) (H := H) d =
            componentIsoClassOfG (G := G) (H := H) c } :=
              (componentIsoClassFiberH_over_G_card (G := G) (H := H) c).symm
  · calc
      Fintype.card
          { c : G.ConnectedComponent // componentIsoClassOfG (G := G) (H := H) c =
            componentIsoClassOfH (G := G) (H := H) d }
          = (H.induce (d.supp : Set V)).componentCount G :=
              componentIsoClassFiberG_over_H_card (G := G) (H := H) d
      _ = (H.induce (d.supp : Set V)).componentCount H := hHcount d
      _ = Fintype.card
          { d' : H.ConnectedComponent // componentIsoClassOfH (G := G) (H := H) d' =
            componentIsoClassOfH (G := G) (H := H) d } :=
              (componentIsoClassFiberH_card (G := G) (H := H) d).symm

private noncomputable def componentIsoClassFiberEquiv
    (hGcount : ∀ c : G.ConnectedComponent,
      (G.induce (c.supp : Set V)).componentCount G =
        (G.induce (c.supp : Set V)).componentCount H)
    (hHcount : ∀ d : H.ConnectedComponent,
      (H.induce (d.supp : Set V)).componentCount G =
        (H.induce (d.supp : Set V)).componentCount H)
    (q : ComponentIsoClass G H) :
    { c : G.ConnectedComponent // componentIsoClassOfG (G := G) (H := H) c = q } ≃
      { d : H.ConnectedComponent // componentIsoClassOfH (G := G) (H := H) d = q } :=
  Fintype.equivOfCardEq
    (componentIsoClassFiber_card_eq (G := G) (H := H) hGcount hHcount q)

/-- Equal component counts for every component isomorphism class assemble into
a global bijection between the connected components of `G` and `H`. -/
noncomputable def componentEquivOfComponentCountEq
    (hGcount : ∀ c : G.ConnectedComponent,
      (G.induce (c.supp : Set V)).componentCount G =
        (G.induce (c.supp : Set V)).componentCount H)
    (hHcount : ∀ d : H.ConnectedComponent,
      (H.induce (d.supp : Set V)).componentCount G =
        (H.induce (d.supp : Set V)).componentCount H) :
    G.ConnectedComponent ≃ H.ConnectedComponent :=
  Equiv.ofFiberEquiv (componentIsoClassFiberEquiv (G := G) (H := H) hGcount hHcount)

/-- The component bijection obtained from per-class component-count equality
preserves the component isomorphism class. -/
theorem componentEquivOfComponentCountEq_iso
    (hGcount : ∀ c : G.ConnectedComponent,
      (G.induce (c.supp : Set V)).componentCount G =
        (G.induce (c.supp : Set V)).componentCount H)
    (hHcount : ∀ d : H.ConnectedComponent,
      (H.induce (d.supp : Set V)).componentCount G =
        (H.induce (d.supp : Set V)).componentCount H)
    (c : G.ConnectedComponent) :
    Nonempty
      (G.induce (c.supp : Set V) ≃g
        H.induce (((componentEquivOfComponentCountEq
          (G := G) (H := H) hGcount hHcount c).supp) : Set V)) := by
  have hclass :
      componentIsoClassOfH (G := G) (H := H)
          (componentEquivOfComponentCountEq (G := G) (H := H) hGcount hHcount c) =
        componentIsoClassOfG (G := G) (H := H) c :=
    Equiv.ofFiberEquiv_map
      (componentIsoClassFiberEquiv (G := G) (H := H) hGcount hHcount) c
  exact Quotient.exact hclass.symm

omit [Fintype W] in
/-- Equal component counts for a fixed component type `F` produce a bijection
between the components of `G` and `H` whose induced component graphs are
isomorphic to `F`.

This packages the cardinal equality supplied by the triangular recovery step
into the actual matching object needed for the later global assembly. -/
noncomputable def componentIsoClassEquivOfComponentCountEq
    (F : SimpleGraph W) (hcount : F.componentCount G = F.componentCount H) :
    { c : G.ConnectedComponent // Nonempty (G.induce (c.supp : Set V) ≃g F) } ≃
      { c : H.ConnectedComponent // Nonempty (H.induce (c.supp : Set V) ≃g F) } := by
  exact Fintype.equivOfCardEq (by
    simpa [componentCount] using hcount)

/-! ### Matching components above a size threshold

The local triangular recovery step only needs an isomorphism-preserving
matching between the components strictly larger than the current connected
graph `F`. The following restricted version of the component-class matching
API packages exactly that induction hypothesis. -/

private noncomputable def largerComponentIsoClassFiberGEquiv
    {W : Type*} [Fintype W]
    (c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp }) :
    { c' : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } //
        componentIsoClassOfG (G := G) (H := H) (c'.1 : G.ConnectedComponent) =
          componentIsoClassOfG (G := G) (H := H) c.1 } ≃
      { c' : G.ConnectedComponent //
        Nonempty (G.induce (c'.supp : Set V) ≃g G.induce (c.1.supp : Set V)) } where
  toFun c' := ⟨(c'.1 : G.ConnectedComponent), Quotient.exact c'.2⟩
  invFun c' := by
    refine ⟨⟨c'.1, ?_⟩, Quotient.sound c'.2⟩
    have hcard : Fintype.card c'.1.supp = Fintype.card c.1.supp :=
      Fintype.card_congr c'.2.some.toEquiv
    omega
  left_inv c' := by ext; rfl
  right_inv c' := by ext; rfl

private noncomputable def largerComponentIsoClassFiberHOverGEquiv
    {W : Type*} [Fintype W]
    (c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp }) :
    { d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp } //
        componentIsoClassOfH (G := G) (H := H) (d.1 : H.ConnectedComponent) =
          componentIsoClassOfG (G := G) (H := H) c.1 } ≃
      { d : H.ConnectedComponent //
        Nonempty (H.induce (d.supp : Set V) ≃g G.induce (c.1.supp : Set V)) } where
  toFun d := ⟨(d.1 : H.ConnectedComponent), Quotient.exact d.2⟩
  invFun d := by
    refine ⟨⟨d.1, ?_⟩, Quotient.sound d.2⟩
    have hcard : Fintype.card d.1.supp = Fintype.card c.1.supp :=
      Fintype.card_congr d.2.some.toEquiv
    omega
  left_inv d := by ext; rfl
  right_inv d := by ext; rfl

private noncomputable def largerComponentIsoClassFiberGOverHEquiv
    {W : Type*} [Fintype W]
    (d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp }) :
    { c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } //
        componentIsoClassOfG (G := G) (H := H) (c.1 : G.ConnectedComponent) =
          componentIsoClassOfH (G := G) (H := H) d.1 } ≃
      { c : G.ConnectedComponent //
        Nonempty (G.induce (c.supp : Set V) ≃g H.induce (d.1.supp : Set V)) } where
  toFun c := ⟨(c.1 : G.ConnectedComponent), Quotient.exact c.2⟩
  invFun c := by
    refine ⟨⟨c.1, ?_⟩, Quotient.sound c.2⟩
    have hcard : Fintype.card c.1.supp = Fintype.card d.1.supp :=
      Fintype.card_congr c.2.some.toEquiv
    omega
  left_inv c := by ext; rfl
  right_inv c := by ext; rfl

private noncomputable def largerComponentIsoClassFiberHEquiv
    {W : Type*} [Fintype W]
    (d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp }) :
    { d' : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp } //
        componentIsoClassOfH (G := G) (H := H) (d'.1 : H.ConnectedComponent) =
          componentIsoClassOfH (G := G) (H := H) d.1 } ≃
      { d' : H.ConnectedComponent //
        Nonempty (H.induce (d'.supp : Set V) ≃g H.induce (d.1.supp : Set V)) } where
  toFun d' := ⟨(d'.1 : H.ConnectedComponent), Quotient.exact d'.2⟩
  invFun d' := by
    refine ⟨⟨d'.1, ?_⟩, Quotient.sound d'.2⟩
    have hcard : Fintype.card d'.1.supp = Fintype.card d.1.supp :=
      Fintype.card_congr d'.2.some.toEquiv
    omega
  left_inv d' := by ext; rfl
  right_inv d' := by ext; rfl

private theorem largerComponentIsoClassFiberG_card
    {W : Type*} [Fintype W]
    (c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp }) :
    Fintype.card
        { c' : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } //
          componentIsoClassOfG (G := G) (H := H) (c'.1 : G.ConnectedComponent) =
            componentIsoClassOfG (G := G) (H := H) c.1 } =
      (G.induce (c.1.supp : Set V)).componentCount G := by
  unfold componentCount
  exact Fintype.card_congr (largerComponentIsoClassFiberGEquiv (G := G) (H := H) c)

private theorem largerComponentIsoClassFiberH_over_G_card
    {W : Type*} [Fintype W]
    (c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp }) :
    Fintype.card
        { d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp } //
          componentIsoClassOfH (G := G) (H := H) (d.1 : H.ConnectedComponent) =
            componentIsoClassOfG (G := G) (H := H) c.1 } =
      (G.induce (c.1.supp : Set V)).componentCount H := by
  unfold componentCount
  exact Fintype.card_congr
    (largerComponentIsoClassFiberHOverGEquiv (G := G) (H := H) c)

private theorem largerComponentIsoClassFiberG_over_H_card
    {W : Type*} [Fintype W]
    (d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp }) :
    Fintype.card
        { c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } //
          componentIsoClassOfG (G := G) (H := H) (c.1 : G.ConnectedComponent) =
            componentIsoClassOfH (G := G) (H := H) d.1 } =
      (H.induce (d.1.supp : Set V)).componentCount G := by
  unfold componentCount
  exact Fintype.card_congr
    (largerComponentIsoClassFiberGOverHEquiv (G := G) (H := H) d)

private theorem largerComponentIsoClassFiberH_card
    {W : Type*} [Fintype W]
    (d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp }) :
    Fintype.card
        { d' : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp } //
          componentIsoClassOfH (G := G) (H := H) (d'.1 : H.ConnectedComponent) =
            componentIsoClassOfH (G := G) (H := H) d.1 } =
      (H.induce (d.1.supp : Set V)).componentCount H := by
  unfold componentCount
  exact Fintype.card_congr (largerComponentIsoClassFiberHEquiv (G := G) (H := H) d)

private theorem largerComponentIsoClassFiber_card_eq
    {W : Type*} [Fintype W]
    (hGcount :
      ∀ c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp },
        (G.induce (c.1.supp : Set V)).componentCount G =
          (G.induce (c.1.supp : Set V)).componentCount H)
    (hHcount :
      ∀ d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp },
        (H.induce (d.1.supp : Set V)).componentCount G =
          (H.induce (d.1.supp : Set V)).componentCount H)
    (q : ComponentIsoClass G H) :
    Fintype.card
        { c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } //
          componentIsoClassOfG (G := G) (H := H) c.1 = q } =
      Fintype.card
        { d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp } //
          componentIsoClassOfH (G := G) (H := H) d.1 = q } := by
  by_cases hqG :
      ∃ c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp },
        componentIsoClassOfG (G := G) (H := H) c.1 = q
  · obtain ⟨c, hcq⟩ := hqG
    subst q
    calc
      Fintype.card
          { c' : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } //
            componentIsoClassOfG (G := G) (H := H) c'.1 =
              componentIsoClassOfG (G := G) (H := H) c.1 }
          = (G.induce (c.1.supp : Set V)).componentCount G :=
              largerComponentIsoClassFiberG_card (G := G) (H := H) c
      _ = (G.induce (c.1.supp : Set V)).componentCount H := hGcount c
      _ = Fintype.card
          { d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp } //
            componentIsoClassOfH (G := G) (H := H) d.1 =
              componentIsoClassOfG (G := G) (H := H) c.1 } :=
              (largerComponentIsoClassFiberH_over_G_card (G := G) (H := H) c).symm
  · by_cases hqH :
        ∃ d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp },
          componentIsoClassOfH (G := G) (H := H) d.1 = q
    · obtain ⟨d, hdq⟩ := hqH
      subst q
      calc
        Fintype.card
            { c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } //
              componentIsoClassOfG (G := G) (H := H) c.1 =
                componentIsoClassOfH (G := G) (H := H) d.1 }
            = (H.induce (d.1.supp : Set V)).componentCount G :=
                largerComponentIsoClassFiberG_over_H_card (G := G) (H := H) d
        _ = (H.induce (d.1.supp : Set V)).componentCount H := hHcount d
        _ = Fintype.card
            { d' : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp } //
              componentIsoClassOfH (G := G) (H := H) d'.1 =
                componentIsoClassOfH (G := G) (H := H) d.1 } :=
                (largerComponentIsoClassFiberH_card (G := G) (H := H) d).symm
    · have hleft0 :
          Fintype.card
              { c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } //
                componentIsoClassOfG (G := G) (H := H) c.1 = q } = 0 := by
        rw [Fintype.card_eq_zero_iff]
        exact ⟨fun c => hqG ⟨c.1, c.2⟩⟩
      have hright0 :
          Fintype.card
              { d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp } //
                componentIsoClassOfH (G := G) (H := H) d.1 = q } = 0 := by
        rw [Fintype.card_eq_zero_iff]
        exact ⟨fun d => hqH ⟨d.1, d.2⟩⟩
      rw [hleft0, hright0]

private noncomputable def largerComponentIsoClassFiberEquiv
    {W : Type*} [Fintype W]
    (hGcount :
      ∀ c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp },
        (G.induce (c.1.supp : Set V)).componentCount G =
          (G.induce (c.1.supp : Set V)).componentCount H)
    (hHcount :
      ∀ d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp },
        (H.induce (d.1.supp : Set V)).componentCount G =
          (H.induce (d.1.supp : Set V)).componentCount H)
    (q : ComponentIsoClass G H) :
    { c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } //
      componentIsoClassOfG (G := G) (H := H) c.1 = q } ≃
      { d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp } //
        componentIsoClassOfH (G := G) (H := H) d.1 = q } :=
  Fintype.equivOfCardEq
    (largerComponentIsoClassFiber_card_eq (G := G) (H := H) hGcount hHcount q)

/-- Equal component counts for every component above a size threshold assemble
into a bijection between the larger-component subtypes. -/
noncomputable def largerComponentEquivOfComponentCountEq
    {W : Type*} [Fintype W]
    (hGcount :
      ∀ c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp },
        (G.induce (c.1.supp : Set V)).componentCount G =
          (G.induce (c.1.supp : Set V)).componentCount H)
    (hHcount :
      ∀ d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp },
        (H.induce (d.1.supp : Set V)).componentCount G =
          (H.induce (d.1.supp : Set V)).componentCount H) :
    { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp } ≃
      { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp } :=
  Equiv.ofFiberEquiv
    (largerComponentIsoClassFiberEquiv (G := G) (H := H) hGcount hHcount)

/-- The larger-component bijection obtained from component-count equality
preserves component isomorphism classes. -/
theorem largerComponentEquivOfComponentCountEq_iso
    {W : Type*} [Fintype W]
    (hGcount :
      ∀ c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp },
        (G.induce (c.1.supp : Set V)).componentCount G =
          (G.induce (c.1.supp : Set V)).componentCount H)
    (hHcount :
      ∀ d : { d : H.ConnectedComponent // Fintype.card W < Fintype.card d.supp },
        (H.induce (d.1.supp : Set V)).componentCount G =
          (H.induce (d.1.supp : Set V)).componentCount H)
    (c : { c : G.ConnectedComponent // Fintype.card W < Fintype.card c.supp }) :
    Nonempty
      (G.induce (c.1.supp : Set V) ≃g
        H.induce ((((largerComponentEquivOfComponentCountEq
          (G := G) (H := H) hGcount hHcount c).1).supp) : Set V)) := by
  have hclass :
      componentIsoClassOfH (G := G) (H := H)
          (largerComponentEquivOfComponentCountEq
            (G := G) (H := H) hGcount hHcount c).1 =
        componentIsoClassOfG (G := G) (H := H) c.1 :=
    Equiv.ofFiberEquiv_map
      (largerComponentIsoClassFiberEquiv (G := G) (H := H) hGcount hHcount) c
  exact Quotient.exact hclass.symm

/-! ### Descending recovery of represented component classes -/

/-- In two same-deck disconnected graphs, every component isomorphism class
represented in either graph has the same multiplicity in both graphs.

This is the triangular induction in Kelly's disconnected-graph reconstruction
argument. The induction descends by component size: for a component type `F`,
Kelly's Lemma recovers the induced-subgraph count of `F`, and all strictly
larger component contributions have already been matched by the induction
hypothesis. -/
theorem SameDeck.componentCount_eq_components_of_not_connected
    (h : G.SameDeck H) (hGdisc : ¬ G.Connected) (hHdisc : ¬ H.Connected) :
    (∀ c : G.ConnectedComponent,
      (G.induce (c.supp : Set V)).componentCount G =
        (G.induce (c.supp : Set V)).componentCount H) ∧
    (∀ d : H.ConnectedComponent,
      (H.induce (d.supp : Set V)).componentCount G =
        (H.induce (d.supp : Set V)).componentCount H) := by
  classical
  have hrec :
      ∀ n : ℕ,
        (∀ c : G.ConnectedComponent,
          Fintype.card V - Fintype.card c.supp = n →
            (G.induce (c.supp : Set V)).componentCount G =
              (G.induce (c.supp : Set V)).componentCount H) ∧
        (∀ d : H.ConnectedComponent,
          Fintype.card V - Fintype.card d.supp = n →
            (H.induce (d.supp : Set V)).componentCount G =
              (H.induce (d.supp : Set V)).componentCount H) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      constructor
      · intro c hc_n
        let F : SimpleGraph c.supp := G.induce (c.supp : Set V)
        have hF : F.Connected := c.connected_toSimpleGraph
        have hcard : Fintype.card c.supp < Fintype.card V :=
          c.card_supp_lt_of_not_connected hGdisc
        let hGcount :
            ∀ c' : { c' : G.ConnectedComponent // Fintype.card c.supp < Fintype.card c'.supp },
              (G.induce (c'.1.supp : Set V)).componentCount G =
                (G.induce (c'.1.supp : Set V)).componentCount H := by
          intro c'
          have hc'_ltV : Fintype.card c'.1.supp < Fintype.card V :=
            c'.1.card_supp_lt_of_not_connected hGdisc
          have hdiff :
              Fintype.card V - Fintype.card c'.1.supp < n := by
            omega
          exact (ih (Fintype.card V - Fintype.card c'.1.supp) hdiff).1 c'.1 rfl
        let hHcount :
            ∀ d' : { d' : H.ConnectedComponent // Fintype.card c.supp < Fintype.card d'.supp },
              (H.induce (d'.1.supp : Set V)).componentCount G =
                (H.induce (d'.1.supp : Set V)).componentCount H := by
          intro d'
          have hd'_ltV : Fintype.card d'.1.supp < Fintype.card V :=
            d'.1.card_supp_lt_of_not_connected hHdisc
          have hdiff :
              Fintype.card V - Fintype.card d'.1.supp < n := by
            omega
          exact (ih (Fintype.card V - Fintype.card d'.1.supp) hdiff).2 d'.1 rfl
        exact h.componentCount_eq_of_larger_component_isoEquiv F hF hcard
          (largerComponentEquivOfComponentCountEq
            (G := G) (H := H) hGcount hHcount)
          (largerComponentEquivOfComponentCountEq_iso
            (G := G) (H := H) hGcount hHcount)
      · intro d hd_n
        let F : SimpleGraph d.supp := H.induce (d.supp : Set V)
        have hF : F.Connected := d.connected_toSimpleGraph
        have hcard : Fintype.card d.supp < Fintype.card V :=
          d.card_supp_lt_of_not_connected hHdisc
        let hGcount :
            ∀ c' : { c' : G.ConnectedComponent // Fintype.card d.supp < Fintype.card c'.supp },
              (G.induce (c'.1.supp : Set V)).componentCount G =
                (G.induce (c'.1.supp : Set V)).componentCount H := by
          intro c'
          have hc'_ltV : Fintype.card c'.1.supp < Fintype.card V :=
            c'.1.card_supp_lt_of_not_connected hGdisc
          have hdiff :
              Fintype.card V - Fintype.card c'.1.supp < n := by
            omega
          exact (ih (Fintype.card V - Fintype.card c'.1.supp) hdiff).1 c'.1 rfl
        let hHcount :
            ∀ d' : { d' : H.ConnectedComponent // Fintype.card d.supp < Fintype.card d'.supp },
              (H.induce (d'.1.supp : Set V)).componentCount G =
                (H.induce (d'.1.supp : Set V)).componentCount H := by
          intro d'
          have hd'_ltV : Fintype.card d'.1.supp < Fintype.card V :=
            d'.1.card_supp_lt_of_not_connected hHdisc
          have hdiff :
              Fintype.card V - Fintype.card d'.1.supp < n := by
            omega
          exact (ih (Fintype.card V - Fintype.card d'.1.supp) hdiff).2 d'.1 rfl
        exact h.componentCount_eq_of_larger_component_isoEquiv F hF hcard
          (largerComponentEquivOfComponentCountEq
            (G := G) (H := H) hGcount hHcount)
          (largerComponentEquivOfComponentCountEq_iso
            (G := G) (H := H) hGcount hHcount)
  exact ⟨fun c => (hrec (Fintype.card V - Fintype.card c.supp)).1 c rfl,
    fun d => (hrec (Fintype.card V - Fintype.card d.supp)).2 d rfl⟩

end ComponentClassMatching

end

end SimpleGraph
