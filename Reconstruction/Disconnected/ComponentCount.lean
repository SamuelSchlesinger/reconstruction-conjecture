import Reconstruction.KellyLemma
import Reconstruction.ConnectedComponents

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
* `SimpleGraph.subgraphCount_eq_sum_over_components` — if `F` is connected,
  `subgraphCount F G = ∑ c, subgraphCount F (G.induce c.supp)`. This is the
  structural identity that lets the reconstruction induction turn subgraph
  counts (given by Kelly's Lemma) into component counts.

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
  map_rel_iff' {a b} := φ.map_rel_iff

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

/-! ### Component decomposition of `subgraphCount`

For `F` connected and `G` arbitrary, every copy of `F` in `G` sits inside a
single connected component of `G`. We prove this and then show
`subgraphCount F G = ∑ c, subgraphCount F (G.induce c.supp)`.
-/

section ComponentDecomposition

variable [DecidableEq V]
variable (F : SimpleGraph W) (G : SimpleGraph V)

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

private lemma classifyComp_spec (hF : F.Connected)
    {S : Finset V} (hS : S ∈ F.copyFinset G) :
    ∀ v ∈ S, v ∈ (classifyComp F G hF hS).supp :=
  (exists_comp_supset_of_mem_copyFinset F G hF hS).choose_spec

/-- For a fixed component `c`, the fiber of copies `S` with all vertices in
`c.supp` bijects with `F.copyFinset (G.induce c.supp)`. -/
private theorem fiber_bij_copyFinset_induce (hF : F.Connected)
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

end ComponentDecomposition

end

end SimpleGraph
