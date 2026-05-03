import Reconstruction.KellyLemma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi

/-!
# Kocay-Style Cover Counting

This module starts a typed version of the Kocay cover-counting machinery.  The
fully classical statement groups covers by isomorphism type of the covered
subgraph.  Here we first group finite indexed tuples of induced copies by
their actual covered vertex set inside a fixed host graph.

This is the finite bookkeeping core behind Kocay-style linear constraints.

## Main definitions

* `SimpleGraph.coverFinset` — finite indexed tuples of induced copies whose
  vertex-set union is a fixed `U`.
* `SimpleGraph.coverCount` — the number of such finite indexed covers.
* `SimpleGraph.coverTypeCount` — Kocay's target cover number: covers of all
  vertices of a target graph `X`.
* `SimpleGraph.InducedSetIsoClass` — isomorphism classes of induced subgraphs
  appearing as vertex subsets of a fixed host graph.
* `SimpleGraph.coverCount_sum` — the product of the indexed subgraph counts is
  the sum of cover counts over covered vertex sets.
* `SimpleGraph.pairCoverFinset` — ordered pairs of induced copies of `F₁` and
  `F₂` whose vertex-set union is a fixed `U`.
* `SimpleGraph.pairCoverCount` — the number of such ordered covers.
* `SimpleGraph.pairCoverTypeCount` — the two-pattern target cover number.

## Main results

* `SimpleGraph.coverTypeCount_sum_induce` — the finite-index cover identity
  grouped by the actual induced target graph `G[U]`.
* `SimpleGraph.coverTypeCount_sum_inducedIsoClass` — the finite-index cover
  identity grouped by induced-subgraph isomorphism classes:
  `∏ i s(Fᵢ,G) = ∑_X c((Fᵢ),X) * s(X,G)` in typed quotient form.
* `SimpleGraph.pairCoverCount_sum` — the product
  `subgraphCount F₁ G * subgraphCount F₂ G` is the sum of these cover counts
  over all vertex subsets `U`.
* `SimpleGraph.pairCoverTypeCount_sum_induce` — the same ordered-pair identity
  grouped by the actual induced target graph `G[U]`.
* `SimpleGraph.SameDeck.subgraphCount_prod_eq` — finite indexed products of
  Kelly-reconstructible subgraph counts are reconstructible.
* `SimpleGraph.SameDeck.subgraphCount_mul_eq` — products of reconstructible
  subgraph counts are reconstructible.

## References

* Kocay, W. L. (1981). "Some new methods in reconstruction theory".
-/

set_option autoImplicit false

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical

variable {W₁ W₂ V : Type*}
variable [Fintype W₁] [Fintype W₂] [Fintype V] [DecidableEq V]

/-! ### Finite indexed cover tuples -/

section FiniteCovers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {W : ι → Type*} [∀ i, Fintype (W i)]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The vertex set covered by an indexed tuple of copies. -/
def coverUnion (S : (i : ι) → Finset V) : Finset V :=
  (Finset.univ : Finset ι).biUnion S

/-- Finite indexed tuples of induced copies of the patterns `F i` whose
vertex-set union is `U`.

This is the typed, in-host cover object behind Kocay's lemma. The later
isomorphism-type grouping should quotient or regroup these covers by the graph
induced on `U`; this definition deliberately keeps the first finite
bookkeeping layer concrete. -/
def coverFinset (F : (i : ι) → SimpleGraph (W i))
    (G : SimpleGraph V) (U : Finset V) : Finset ((i : ι) → Finset V) :=
  (Fintype.piFinset fun i => (F i).copyFinset G).filter fun S =>
    coverUnion S = U

/-- The number of finite indexed covers of `U` by induced copies of `F i`. -/
def coverCount (F : (i : ι) → SimpleGraph (W i))
    (G : SimpleGraph V) (U : Finset V) : ℕ :=
  (coverFinset F G U).card

/-- Kocay's target cover finset `C((F_i), X)`: indexed induced copies of
the patterns `F i` in the target graph `XG` whose union covers every vertex of
`XG`. -/
def coverTypeFinset (F : (i : ι) → SimpleGraph (W i))
    (XG : SimpleGraph X) : Finset ((i : ι) → Finset X) :=
  coverFinset F XG (Finset.univ : Finset X)

/-- Kocay's target cover number `c((F_i), X)`: the number of indexed induced
copies of `F i` that cover all vertices of the target graph `XG`. -/
def coverTypeCount (F : (i : ι) → SimpleGraph (W i))
    (XG : SimpleGraph X) : ℕ :=
  (coverTypeFinset F XG).card

@[simp] theorem coverTypeCount_eq_coverCount_univ
    (F : (i : ι) → SimpleGraph (W i)) (XG : SimpleGraph X) :
    coverTypeCount F XG = coverCount F XG (Finset.univ : Finset X) := rfl

/-- The finite indexed Kocay bookkeeping identity, grouped by the actual
covered vertex set in the host graph.

The left side counts tuples of induced copies independently. The right side
classifies the same tuples by the union of their vertex sets. -/
theorem coverCount_sum (F : (i : ι) → SimpleGraph (W i))
    (G : SimpleGraph V) :
    (∏ i, (F i).subgraphCount G) =
      ∑ U ∈ (Finset.univ : Finset V).powerset, coverCount F G U := by
  unfold coverCount coverFinset coverUnion subgraphCount
  have hcard :
      (Fintype.piFinset fun i => (F i).copyFinset G).card =
        ∏ i, ((F i).copyFinset G).card := by
    unfold Fintype.piFinset
    rw [Finset.card_map, Finset.card_pi]
  rw [← hcard]
  refine (Finset.card_eq_sum_card_fiberwise
    (f := fun S : (i : ι) → Finset V => (Finset.univ : Finset ι).biUnion S)
    (s := Fintype.piFinset fun i => (F i).copyFinset G)
    (t := (Finset.univ : Finset V).powerset) ?_).trans ?_
  · intro S _hS
    simp
  · apply Finset.sum_congr rfl
    intro _U _hU
    rfl

end FiniteCovers

/-! ### Target-cover counts up to isomorphism -/

section CoverTypeIso

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {W : ι → Type*} [∀ i, Fintype (W i)]
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
variable {XG : SimpleGraph X} {YG : SimpleGraph Y}

private def coverInduceMapIso (φ : XG ≃g YG) (S : Finset X) :
    XG.induce (↑S : Set X) ≃g
      YG.induce (↑(S.map φ.toEquiv.toEmbedding) : Set Y) where
  toEquiv := Equiv.subtypeEquiv φ.toEquiv (fun v => by simp)
  map_rel_iff' {a b} := φ.map_rel_iff

omit [DecidableEq X] [DecidableEq Y] in
private theorem copyFinset_map_mem_of_iso {W₀ : Type*} [Fintype W₀]
    {F : SimpleGraph W₀} (φ : XG ≃g YG) {S : Finset X}
    (hS : S ∈ F.copyFinset XG) :
    S.map φ.toEquiv.toEmbedding ∈ F.copyFinset YG := by
  have hS' := (mem_copyFinset F XG S).mp hS
  exact (mem_copyFinset F YG _).mpr
    ⟨by rw [Finset.card_map]; exact hS'.1,
      hS'.2.map ((coverInduceMapIso φ S).symm.trans ·)⟩

/-- Target-cover counts depend only on the isomorphism type of the target
graph. This is the well-definedness bridge needed to group Kocay covers by
isomorphism class rather than by concrete vertex subsets. -/
theorem coverTypeCount_eq_of_iso
    (F : (i : ι) → SimpleGraph (W i)) (φ : XG ≃g YG) :
    coverTypeCount F XG = coverTypeCount F YG := by
  unfold coverTypeCount coverTypeFinset coverFinset
  refine Finset.card_bij'
    (fun S _ => fun i => (S i).map φ.toEquiv.toEmbedding)
    (fun T _ => fun i => (T i).map φ.symm.toEquiv.toEmbedding)
    (fun S hS => ?fwd) (fun T hT => ?bwd)
    (fun S _ => ?linv) (fun T _ => ?rinv)
  case fwd =>
    rw [Finset.mem_filter] at hS ⊢
    obtain ⟨hS_pi, hS_union⟩ := hS
    rw [Fintype.mem_piFinset] at hS_pi ⊢
    refine ⟨?_, ?_⟩
    · intro i
      exact copyFinset_map_mem_of_iso φ (hS_pi i)
    · ext y
      constructor
      · intro _
        simp
      · intro _
        have hx : φ.symm y ∈ coverUnion S := by
          rw [hS_union]
          simp
        rw [coverUnion, Finset.mem_biUnion] at hx
        obtain ⟨i, hi, hxi⟩ := hx
        rw [coverUnion, Finset.mem_biUnion]
        refine ⟨i, hi, ?_⟩
        exact Finset.mem_map.mpr ⟨φ.symm y, hxi, by simp⟩
  case bwd =>
    rw [Finset.mem_filter] at hT ⊢
    obtain ⟨hT_pi, hT_union⟩ := hT
    rw [Fintype.mem_piFinset] at hT_pi ⊢
    refine ⟨?_, ?_⟩
    · intro i
      exact copyFinset_map_mem_of_iso φ.symm (hT_pi i)
    · ext x
      constructor
      · intro _
        simp
      · intro _
        have hy : φ x ∈ coverUnion T := by
          rw [hT_union]
          simp
        rw [coverUnion, Finset.mem_biUnion] at hy
        obtain ⟨i, hi, hyi⟩ := hy
        rw [coverUnion, Finset.mem_biUnion]
        refine ⟨i, hi, ?_⟩
        exact Finset.mem_map.mpr ⟨φ x, hyi, by simp⟩
  case linv =>
    funext i
    simp only [Finset.map_map]
    convert Finset.map_refl (s := S i) using 2
    ext x
    simp
  case rinv =>
    funext i
    simp only [Finset.map_map]
    convert Finset.map_refl (s := T i) using 2
    ext y
    simp

end CoverTypeIso

/-! ### Ordered two-pattern cover tuples -/

/-- Ordered pairs of induced copies of `F₁` and `F₂` whose vertex-set union is
`U`. This is a typed, in-host version of the cover tuples appearing in Kocay's
lemma. -/
def pairCoverFinset (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂)
    (G : SimpleGraph V) (U : Finset V) : Finset (Finset V × Finset V) :=
  ((F₁.copyFinset G).product (F₂.copyFinset G)).filter fun p => p.1 ∪ p.2 = U

/-- The number of ordered pairs of induced copies of `F₁` and `F₂` covering
the vertex set `U`. -/
def pairCoverCount (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂)
    (G : SimpleGraph V) (U : Finset V) : ℕ :=
  (pairCoverFinset F₁ F₂ G U).card

section PairTargetCovers

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Ordered pairs of induced copies in the target graph `XG` covering every
vertex of `XG`. -/
def pairCoverTypeFinset (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂)
    (XG : SimpleGraph X) : Finset (Finset X × Finset X) :=
  pairCoverFinset F₁ F₂ XG (Finset.univ : Finset X)

/-- The ordered two-pattern target cover number `c((F₁, F₂), X)`. -/
def pairCoverTypeCount (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂)
    (XG : SimpleGraph X) : ℕ :=
  (pairCoverTypeFinset F₁ F₂ XG).card

@[simp] theorem pairCoverTypeCount_eq_pairCoverCount_univ
    (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂) (XG : SimpleGraph X) :
    pairCoverTypeCount F₁ F₂ XG =
      pairCoverCount F₁ F₂ XG (Finset.univ : Finset X) := rfl

end PairTargetCovers

section InducedTargetCovers

variable {W : Type*} [Fintype W]

private theorem copyFinset_subtype_mem (F : SimpleGraph W) (G : SimpleGraph V)
    (U : Finset V) {S : Finset V}
    (hS : S ∈ F.copyFinset G) (hsub : S ⊆ U) :
    S.subtype (fun v => v ∈ U) ∈ F.copyFinset (G.induce (U : Set V)) := by
  have hS' := (mem_copyFinset F G S).mp hS
  rw [mem_copyFinset]
  have hfilt : S.filter (fun v => v ∈ U) = S :=
    Finset.filter_true_of_mem (fun v hv => hsub hv)
  refine ⟨by rw [Finset.card_subtype, hfilt]; exact hS'.1, ?_⟩
  exact hS'.2.map fun iso => by
    let fwd :
        (↑(S.subtype (fun v => v ∈ U)) : Set {v // v ∈ U}) →
          (↑S : Set V) := fun x =>
      ⟨x.1.1, Finset.mem_coe.mpr (Finset.mem_subtype.mp x.2)⟩
    let bwd :
        (↑S : Set V) →
          (↑(S.subtype (fun v => v ∈ U)) : Set {v // v ∈ U}) := fun x =>
      ⟨⟨x.1, hsub (Finset.mem_coe.mp x.2)⟩,
        Finset.mem_coe.mpr (Finset.mem_subtype.mpr (Finset.mem_coe.mp x.2))⟩
    have hleft : Function.LeftInverse bwd fwd := fun x => by ext; rfl
    have hright : Function.RightInverse bwd fwd := fun x => by ext; rfl
    exact ({ toEquiv := ⟨fwd, bwd, hleft, hright⟩, map_rel_iff' := Iff.rfl } :
      (G.induce (U : Set V)).induce
          (↑(S.subtype (fun v => v ∈ U)) : Set {v // v ∈ U}) ≃g
        G.induce (↑S : Set V)).trans iso

omit [DecidableEq V] in
private theorem copyFinset_map_subtype_mem (F : SimpleGraph W) (G : SimpleGraph V)
    (U : Finset V) {T : Finset {v // v ∈ U}}
    (hT : T ∈ F.copyFinset (G.induce (U : Set V))) :
    T.map (Function.Embedding.subtype (fun v => v ∈ U)) ∈ F.copyFinset G := by
  have hT' := (mem_copyFinset F (G.induce (U : Set V)) T).mp hT
  rw [mem_copyFinset]
  refine ⟨by rw [Finset.card_map]; exact hT'.1, ?_⟩
  exact hT'.2.map fun iso => by
    let fwd :
        (↑(T.map (Function.Embedding.subtype (fun v => v ∈ U))) : Set V) →
          (↑T : Set {v // v ∈ U}) := fun x =>
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
          obtain ⟨⟨w, _hw⟩, hT_mem, heq⟩ := hx
          simp only [Function.Embedding.subtype_apply] at heq
          subst heq
          exact Finset.mem_coe.mpr hT_mem⟩
    let bwd :
        (↑T : Set {v // v ∈ U}) →
          (↑(T.map (Function.Embedding.subtype (fun v => v ∈ U))) : Set V) :=
      fun y => ⟨y.1.1,
        Finset.mem_coe.mpr (Finset.mem_map.mpr
          ⟨y.1, Finset.mem_coe.mp y.2, rfl⟩)⟩
    have hleft : Function.LeftInverse bwd fwd := fun x => by ext; rfl
    have hright : Function.RightInverse bwd fwd := fun y => by ext; rfl
    exact ({ toEquiv := ⟨fwd, bwd, hleft, hright⟩, map_rel_iff' := Iff.rfl } :
      G.induce
          (↑(T.map (Function.Embedding.subtype (fun v => v ∈ U))) : Set V) ≃g
        (G.induce (U : Set V)).induce (↑T : Set {v // v ∈ U})).trans iso

/-- Counting indexed covers of a concrete vertex set `U` in `G` is the same as
counting target covers of the induced graph `G[U]`. -/
theorem coverCount_eq_coverTypeCount_induce
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : ι → Type*} [∀ i, Fintype (W i)]
    (F : (i : ι) → SimpleGraph (W i)) (G : SimpleGraph V) (U : Finset V) :
    coverCount F G U = coverTypeCount F (G.induce (U : Set V)) := by
  unfold coverCount coverTypeCount coverTypeFinset
  refine Finset.card_bij'
    (fun S _ => fun i => (S i).subtype (fun v => v ∈ U))
    (fun T _ => fun i => (T i).map (Function.Embedding.subtype (fun v => v ∈ U)))
    (fun S hS => ?fwd) (fun T hT => ?bwd)
    (fun S hS => ?linv) (fun T hT => ?rinv)
  case fwd =>
    rw [coverFinset, Finset.mem_filter] at hS
    change (fun i => (S i).subtype (fun v => v ∈ U)) ∈
      coverFinset F (G.induce (U : Set V)) (Finset.univ : Finset {v // v ∈ U})
    rw [coverFinset, Finset.mem_filter]
    obtain ⟨hS_pi, hS_union⟩ := hS
    rw [Fintype.mem_piFinset] at hS_pi ⊢
    refine ⟨?_, ?_⟩
    · intro i
      have hsub : S i ⊆ U := by
        intro v hv
        have hv_union : v ∈ coverUnion S := by
          unfold coverUnion
          exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩
        rwa [hS_union] at hv_union
      exact copyFinset_subtype_mem (F i) G U (hS_pi i) hsub
    · ext x
      simp only [coverUnion, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_subtype]
      constructor
      · intro _h
        trivial
      · intro _h
        have hx_union : x.1 ∈ coverUnion S := by
          rw [hS_union]
          exact x.2
        unfold coverUnion at hx_union
        rw [Finset.mem_biUnion] at hx_union
        obtain ⟨i, _hi, hxi⟩ := hx_union
        exact ⟨i, hxi⟩
  case bwd =>
    rw [coverFinset, Finset.mem_filter] at hT
    change (fun i => (T i).map (Function.Embedding.subtype (fun v => v ∈ U))) ∈
      coverFinset F G U
    rw [coverFinset, Finset.mem_filter]
    obtain ⟨hT_pi, hT_union⟩ := hT
    rw [Fintype.mem_piFinset] at hT_pi ⊢
    refine ⟨?_, ?_⟩
    · intro i
      exact copyFinset_map_subtype_mem (F i) G U (hT_pi i)
    · ext v
      simp only [coverUnion, Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_map, Function.Embedding.subtype_apply]
      constructor
      · rintro ⟨i, ⟨⟨w, hw⟩, _hmem, hval⟩⟩
        cases hval
        exact hw
      · intro hv
        have hx_union : (⟨v, hv⟩ : {v // v ∈ U}) ∈ coverUnion T := by
          rw [hT_union]
          simp
        unfold coverUnion at hx_union
        rw [Finset.mem_biUnion] at hx_union
        obtain ⟨i, _hi, hxi⟩ := hx_union
        exact ⟨i, ⟨⟨v, hv⟩, hxi, rfl⟩⟩
  case linv =>
    rw [coverFinset, Finset.mem_filter] at hS
    obtain ⟨_hS_pi, hS_union⟩ := hS
    funext i
    have hsub : S i ⊆ U := by
      intro v hv
      have hv_union : v ∈ coverUnion S := by
        unfold coverUnion
        exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩
      rwa [hS_union] at hv_union
    change ((S i).subtype (fun v => v ∈ U)).map
        (Function.Embedding.subtype (fun v => v ∈ U)) = S i
    rw [Finset.subtype_map]
    exact Finset.filter_true_of_mem (fun v hv => hsub hv)
  case rinv =>
    funext i
    ext x
    simp only [Finset.mem_subtype, Finset.mem_map, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨⟨w, hw⟩, hmem, hval⟩
      cases hval
      exact hmem
    · intro hmem
      exact ⟨x, hmem, rfl⟩

/-- Finite-index Kocay bookkeeping grouped by the actual induced target graph
on each covered vertex set. -/
theorem coverTypeCount_sum_induce
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : ι → Type*} [∀ i, Fintype (W i)]
    (F : (i : ι) → SimpleGraph (W i)) (G : SimpleGraph V) :
    (∏ i, (F i).subgraphCount G) =
      ∑ U ∈ (Finset.univ : Finset V).powerset,
        coverTypeCount F (G.induce (U : Set V)) := by
  rw [coverCount_sum F G]
  apply Finset.sum_congr rfl
  intro U _hU
  exact coverCount_eq_coverTypeCount_induce F G U

omit [DecidableEq V] in
/-- Pattern isomorphism preserves induced-subgraph counts in a fixed host. -/
theorem subgraphCount_eq_of_pattern_iso
    {F₁ : SimpleGraph W₁} {F₂ : SimpleGraph W₂} (φ : F₁ ≃g F₂)
    (G : SimpleGraph V) :
    F₁.subgraphCount G = F₂.subgraphCount G := by
  unfold subgraphCount
  congr 1
  ext S
  rw [mem_copyFinset, mem_copyFinset]
  constructor
  · rintro ⟨hcard, hIso⟩
    refine ⟨?_, hIso.map (fun e => e.trans φ)⟩
    rw [hcard]
    exact Fintype.card_congr φ.toEquiv
  · rintro ⟨hcard, hIso⟩
    refine ⟨?_, hIso.map (fun e => e.trans φ.symm)⟩
    rw [hcard]
    exact (Fintype.card_congr φ.toEquiv).symm

section InducedIsoClassProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {W : ι → Type*} [∀ i, Fintype (W i)]

/-- Vertex subsets of a host graph are equivalent when they induce isomorphic
subgraphs. -/
def InducedSetIsoRel (G : SimpleGraph V) : Finset V → Finset V → Prop :=
  fun U U' => Nonempty (G.induce (U : Set V) ≃g G.induce (U' : Set V))

/-- The setoid on vertex subsets generated by induced-subgraph isomorphism. -/
def InducedSetIsoSetoid (G : SimpleGraph V) : Setoid (Finset V) where
  r := InducedSetIsoRel G
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro U
      exact ⟨RelIso.refl _⟩
    · intro U U' h
      exact h.map RelIso.symm
    · intro U U' U'' h h'
      exact ⟨h.some.trans h'.some⟩

/-- Isomorphism classes of induced subgraphs appearing as vertex subsets of
`G`. -/
abbrev InducedSetIsoClass (G : SimpleGraph V) :=
  Quotient (InducedSetIsoSetoid G)

noncomputable instance inducedSetIsoClassFintype (G : SimpleGraph V) :
    Fintype (InducedSetIsoClass G) :=
  Fintype.ofFinite _

/-- The induced-subgraph isomorphism class of a concrete vertex subset. -/
def inducedSetIsoClassOf (G : SimpleGraph V) (U : Finset V) :
    InducedSetIsoClass G :=
  Quotient.mk (InducedSetIsoSetoid G) U

/-- The Kocay cover number attached to an induced-subgraph isomorphism class. -/
noncomputable def inducedClassCoverTypeCount
    (F : (i : ι) → SimpleGraph (W i)) (G : SimpleGraph V)
    (q : InducedSetIsoClass G) : ℕ :=
  Quotient.lift
    (fun U : Finset V => coverTypeCount F (G.induce (U : Set V)))
    (by
      intro U U' h
      exact coverTypeCount_eq_of_iso F h.some)
    q

/-- The number of induced copies in `G` of an induced-subgraph isomorphism
class. -/
noncomputable def inducedClassSubgraphCount (G : SimpleGraph V)
    (q : InducedSetIsoClass G) : ℕ :=
  Quotient.lift
    (fun U : Finset V => (G.induce (U : Set V)).subgraphCount G)
    (by
      intro U U' h
      exact subgraphCount_eq_of_pattern_iso h.some G)
    q

omit [DecidableEq V] in
theorem inducedSetIsoClass_fiber_card (G : SimpleGraph V)
    (q : InducedSetIsoClass G) :
    ((Finset.univ : Finset V).powerset.filter
      (fun U => inducedSetIsoClassOf G U = q)).card =
      inducedClassSubgraphCount G q := by
  refine Quotient.inductionOn q ?_
  intro U
  change ((Finset.univ : Finset V).powerset.filter
      (fun S => inducedSetIsoClassOf G S = inducedSetIsoClassOf G U)).card =
    (G.induce (U : Set V)).subgraphCount G
  have hfilter :
      ((Finset.univ : Finset V).powerset.filter
        (fun S => inducedSetIsoClassOf G S = inducedSetIsoClassOf G U)) =
        (G.induce (U : Set V)).copyFinset G := by
    ext S
    rw [Finset.mem_filter, mem_copyFinset]
    constructor
    · rintro ⟨_hSpow, hclass⟩
      have hIso : Nonempty (G.induce (S : Set V) ≃g G.induce (U : Set V)) :=
        Quotient.exact hclass
      refine ⟨?_, hIso⟩
      have hcard := Fintype.card_congr hIso.some.toEquiv
      simpa using hcard
    · rintro ⟨_hcard, hIso⟩
      exact ⟨by simp, Quotient.sound hIso⟩
  rw [hfilter]
  rfl

/-- Kocay's finite product-count identity, grouped by induced-subgraph
isomorphism classes. This is the typed quotient form of
`∏ i s(Fᵢ, G) = ∑_X c((Fᵢ), X) * s(X, G)`: the quotient ranges over the
isomorphism classes of induced subgraphs actually appearing in the host. -/
theorem coverTypeCount_sum_inducedIsoClass
    (F : (i : ι) → SimpleGraph (W i)) (G : SimpleGraph V) :
    (∏ i, (F i).subgraphCount G) =
      ∑ q : InducedSetIsoClass G,
        inducedClassCoverTypeCount F G q * inducedClassSubgraphCount G q := by
  rw [coverTypeCount_sum_induce F G]
  let cls : Finset V → InducedSetIsoClass G := inducedSetIsoClassOf G
  let c : InducedSetIsoClass G → ℕ := inducedClassCoverTypeCount F G
  calc
    (∑ U ∈ (Finset.univ : Finset V).powerset,
        coverTypeCount F (G.induce (U : Set V))) =
        ∑ U ∈ (Finset.univ : Finset V).powerset, c (cls U) := by
          apply Finset.sum_congr rfl
          intro U _hU
          rfl
    _ = ∑ q : InducedSetIsoClass G,
          ∑ U ∈ (Finset.univ : Finset V).powerset with cls U = q, c q := by
          exact (Finset.sum_fiberwise'
            (s := (Finset.univ : Finset V).powerset) (g := cls) (f := c)).symm
    _ = ∑ q : InducedSetIsoClass G,
          c q * inducedClassSubgraphCount G q := by
          apply Finset.sum_congr rfl
          intro q _hq
          rw [Finset.sum_const_nat (m := c q) (f := fun _ => c q)
            (by intro U _hU; rfl)]
          rw [inducedSetIsoClass_fiber_card]
          exact Nat.mul_comm _ _

end InducedIsoClassProduct

/-- Counting ordered covers of a concrete vertex set `U` in `G` is the same as
counting ordered target covers of the induced graph `G[U]`. -/
theorem pairCoverCount_eq_pairCoverTypeCount_induce
    (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂)
    (G : SimpleGraph V) (U : Finset V) :
    pairCoverCount F₁ F₂ G U =
      pairCoverTypeCount F₁ F₂ (G.induce (U : Set V)) := by
  unfold pairCoverCount pairCoverTypeCount pairCoverFinset pairCoverTypeFinset
  refine Finset.card_bij'
    (fun p _ => (p.1.subtype (fun v => v ∈ U), p.2.subtype (fun v => v ∈ U)))
    (fun q _ =>
      (q.1.map (Function.Embedding.subtype (fun v => v ∈ U)),
       q.2.map (Function.Embedding.subtype (fun v => v ∈ U))))
    (fun p hp => ?fwd) (fun q hq => ?bwd)
    (fun p hp => ?linv) (fun q hq => ?rinv)
  case fwd =>
    rw [Finset.mem_filter] at hp
    change (p.1.subtype (fun v => v ∈ U), p.2.subtype (fun v => v ∈ U)) ∈
      ((F₁.copyFinset (G.induce (U : Set V))).product
        (F₂.copyFinset (G.induce (U : Set V)))).filter
          (fun q => q.1 ∪ q.2 = (Finset.univ : Finset {v // v ∈ U}))
    rw [Finset.mem_filter]
    obtain ⟨hp_prod, hp_union⟩ := hp
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp_prod
    have hsub₁ : p.1 ⊆ U := by
      intro v hv
      have hvu : v ∈ p.1 ∪ p.2 := Finset.mem_union.mpr (Or.inl hv)
      rwa [hp_union] at hvu
    have hsub₂ : p.2 ⊆ U := by
      intro v hv
      have hvu : v ∈ p.1 ∪ p.2 := Finset.mem_union.mpr (Or.inr hv)
      rwa [hp_union] at hvu
    refine ⟨?_, ?_⟩
    · rw [Finset.product_eq_sprod, Finset.mem_product]
      exact ⟨copyFinset_subtype_mem F₁ G U hp_prod.1 hsub₁,
        copyFinset_subtype_mem F₂ G U hp_prod.2 hsub₂⟩
    ext x
    simp only [Finset.mem_union, Finset.mem_subtype, Finset.mem_univ]
    constructor
    · intro _h
      trivial
    · intro _h
      have hx_union : x.1 ∈ p.1 ∪ p.2 := by
        rw [hp_union]
        exact x.2
      simpa [Finset.mem_union] using hx_union
  case bwd =>
    rw [pairCoverFinset, Finset.mem_filter] at hq
    change (q.1.map (Function.Embedding.subtype (fun v => v ∈ U)),
        q.2.map (Function.Embedding.subtype (fun v => v ∈ U))) ∈
      ((F₁.copyFinset G).product (F₂.copyFinset G)).filter
        (fun p => p.1 ∪ p.2 = U)
    rw [Finset.mem_filter]
    obtain ⟨hq_prod, hq_union⟩ := hq
    rw [Finset.product_eq_sprod, Finset.mem_product] at hq_prod
    refine ⟨?_, ?_⟩
    · rw [Finset.product_eq_sprod, Finset.mem_product]
      exact ⟨copyFinset_map_subtype_mem F₁ G U hq_prod.1,
        copyFinset_map_subtype_mem F₂ G U hq_prod.2⟩
    ext v
    simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.subtype_apply]
    constructor
    · rintro (⟨⟨w, hw⟩, _hmem, hval⟩ | ⟨⟨w, hw⟩, _hmem, hval⟩) <;>
        cases hval <;> exact hw
    · intro hv
      have hx_union : (⟨v, hv⟩ : {v // v ∈ U}) ∈ q.1 ∪ q.2 := by
        rw [hq_union]
        simp
      rw [Finset.mem_union] at hx_union
      rcases hx_union with hx | hx
      · exact Or.inl ⟨⟨v, hv⟩, hx, rfl⟩
      · exact Or.inr ⟨⟨v, hv⟩, hx, rfl⟩
  case linv =>
    rw [Finset.mem_filter] at hp
    obtain ⟨_hp_prod, hp_union⟩ := hp
    have hsub₁ : p.1 ⊆ U := by
      intro v hv
      have hvu : v ∈ p.1 ∪ p.2 := Finset.mem_union.mpr (Or.inl hv)
      rwa [hp_union] at hvu
    have hsub₂ : p.2 ⊆ U := by
      intro v hv
      have hvu : v ∈ p.1 ∪ p.2 := Finset.mem_union.mpr (Or.inr hv)
      rwa [hp_union] at hvu
    apply Prod.ext
    · change (p.1.subtype (fun v => v ∈ U)).map
          (Function.Embedding.subtype (fun v => v ∈ U)) = p.1
      rw [Finset.subtype_map]
      exact Finset.filter_true_of_mem (fun v hv => hsub₁ hv)
    · change (p.2.subtype (fun v => v ∈ U)).map
          (Function.Embedding.subtype (fun v => v ∈ U)) = p.2
      rw [Finset.subtype_map]
      exact Finset.filter_true_of_mem (fun v hv => hsub₂ hv)
  case rinv =>
    apply Prod.ext
    · ext x
      simp only [Finset.mem_subtype, Finset.mem_map, Function.Embedding.subtype_apply]
      constructor
      · rintro ⟨⟨w, hw⟩, hmem, hval⟩
        cases hval
        exact hmem
      · intro hmem
        exact ⟨x, hmem, rfl⟩
    · ext x
      simp only [Finset.mem_subtype, Finset.mem_map, Function.Embedding.subtype_apply]
      constructor
      · rintro ⟨⟨w, hw⟩, hmem, hval⟩
        cases hval
        exact hmem
      · intro hmem
        exact ⟨x, hmem, rfl⟩

end InducedTargetCovers

/-- The ordered-pair Kocay bookkeeping identity, grouped by covered vertex
set. -/
theorem pairCoverCount_sum (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂)
    (G : SimpleGraph V) :
    F₁.subgraphCount G * F₂.subgraphCount G =
      ∑ U ∈ (Finset.univ : Finset V).powerset, pairCoverCount F₁ F₂ G U := by
  unfold pairCoverCount pairCoverFinset subgraphCount
  rw [← Finset.card_product]
  refine (Finset.card_eq_sum_card_fiberwise
    (f := fun p : Finset V × Finset V => p.1 ∪ p.2)
    (s := (F₁.copyFinset G).product (F₂.copyFinset G))
    (t := (Finset.univ : Finset V).powerset) ?_).trans ?_
  · intro p _hp
    simp
  · apply Finset.sum_congr rfl
    intro _U _hU
    rfl

/-- Ordered two-pattern cover identity grouped by the actual induced target
graph on each covered vertex set. -/
theorem pairCoverTypeCount_sum_induce
    (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂) (G : SimpleGraph V) :
    F₁.subgraphCount G * F₂.subgraphCount G =
      ∑ U ∈ (Finset.univ : Finset V).powerset,
        pairCoverTypeCount F₁ F₂ (G.induce (U : Set V)) := by
  rw [pairCoverCount_sum F₁ F₂ G]
  apply Finset.sum_congr rfl
  intro U _hU
  exact pairCoverCount_eq_pairCoverTypeCount_induce F₁ F₂ G U

section Reconstructibility

variable {G H : SimpleGraph V}

omit [DecidableEq V] in
/-- Finite indexed products of reconstructible induced-subgraph counts are
reconstructible. This is the product side of the finite-index Kocay identity. -/
theorem SameDeck.subgraphCount_prod_eq
    {ι : Type*} [Fintype ι]
    {W : ι → Type*} [∀ i, Fintype (W i)]
    (h : G.SameDeck H) (F : (i : ι) → SimpleGraph (W i))
    (hcard : ∀ i, Fintype.card (W i) < Fintype.card V) :
    (∏ i, (F i).subgraphCount G) =
      ∏ i, (F i).subgraphCount H := by
  exact Finset.prod_congr rfl fun i _ => h.subgraphCount_eq (F i) (hcard i)

omit [DecidableEq V] in
/-- Products of reconstructible induced-subgraph counts are reconstructible.
This is the simplest Kocay-style linear constraint supplied by Kelly's lemma. -/
theorem SameDeck.subgraphCount_mul_eq (h : G.SameDeck H)
    (F₁ : SimpleGraph W₁) (F₂ : SimpleGraph W₂)
    (hcard₁ : Fintype.card W₁ < Fintype.card V)
    (hcard₂ : Fintype.card W₂ < Fintype.card V) :
    F₁.subgraphCount G * F₂.subgraphCount G =
      F₁.subgraphCount H * F₂.subgraphCount H := by
  rw [h.subgraphCount_eq F₁ hcard₁, h.subgraphCount_eq F₂ hcard₂]

end Reconstructibility

end

end SimpleGraph
