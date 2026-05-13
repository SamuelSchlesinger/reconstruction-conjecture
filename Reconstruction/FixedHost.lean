import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Find
import Reconstruction.Defs

/-!
# Fixed-Host Colored Deletion Decks

This module starts the Lean infrastructure for the fixed-host singleton
analysis in `proof_sketch.tex`.

The fixed-host problem keeps one graph `K` fixed and compares subsets
`U V : Set V` by the colored vertex-deletion decks of `(K, S, U)` and
`(K, S, V)`, where `S` is a passive first color and `U`/`V` are the active
second colors.

The definitions here are intentionally modest: colored card isomorphisms,
deleted colors, fixed-host same-deck, and the one-hole/two-hole cards used in
the low/complementary rectangular boundary.
-/

set_option autoImplicit false

namespace SimpleGraph

variable {V W : Type*}

/-- A finite nonempty self-map has a positive-period orbit point.  This is the
generic finite-dynamics fact used below for chosen active successor systems. -/
theorem exists_positive_iterate_eq_self_of_finite
    {α : Type*} [Finite α] [Nonempty α] (f : α → α) :
    ∃ x : α, ∃ n : ℕ, 0 < n ∧ f^[n] x = x := by
  classical
  let x0 : α := Classical.arbitrary α
  obtain ⟨n, m, hne, heq⟩ :
      ∃ n m : ℕ, n ≠ m ∧ f^[n] x0 = f^[m] x0 :=
    Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => f^[k] x0)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨f^[n] x0, m - n, Nat.sub_pos_of_lt hlt, ?_⟩
    calc
      f^[m - n] (f^[n] x0) = f^[(m - n) + n] x0 := by
        exact (Function.iterate_add_apply f (m - n) n x0).symm
      _ = f^[m] x0 := by rw [Nat.sub_add_cancel hlt.le]
      _ = f^[n] x0 := heq.symm
  · refine ⟨f^[m] x0, n - m, Nat.sub_pos_of_lt hgt, ?_⟩
    calc
      f^[n - m] (f^[m] x0) = f^[(n - m) + m] x0 := by
        exact (Function.iterate_add_apply f (n - m) m x0).symm
      _ = f^[n] x0 := by rw [Nat.sub_add_cancel hgt.le]
      _ = f^[m] x0 := heq

/-- A graph isomorphism preserving two vertex colors. -/
structure TwoColorIso (G : SimpleGraph V) (H : SimpleGraph W)
    (S T : Set V) (S' T' : Set W) where
  iso : G ≃g H
  map_first : ∀ v : V, v ∈ S ↔ iso.toEquiv v ∈ S'
  map_second : ∀ v : V, v ∈ T ↔ iso.toEquiv v ∈ T'

namespace TwoColorIso

/-- The identity two-colored isomorphism. -/
def refl (G : SimpleGraph V) (S T : Set V) : TwoColorIso G G S T S T where
  iso := Iso.refl
  map_first := by
    intro v
    rfl
  map_second := by
    intro v
    rfl

/-- Reverse a two-colored isomorphism. -/
def symm {G : SimpleGraph V} {H : SimpleGraph W}
    {S T : Set V} {S' T' : Set W}
    (e : TwoColorIso G H S T S' T') :
    TwoColorIso H G S' T' S T where
  iso := e.iso.symm
  map_first := by
    intro w
    constructor
    · intro hw
      have h := (e.map_first (e.iso.symm.toEquiv w)).mpr (by simpa using hw)
      simpa using h
    · intro hw
      have h := (e.map_first (e.iso.symm.toEquiv w)).mp hw
      simpa using h
  map_second := by
    intro w
    constructor
    · intro hw
      have h := (e.map_second (e.iso.symm.toEquiv w)).mpr (by simpa using hw)
      simpa using h
    · intro hw
      have h := (e.map_second (e.iso.symm.toEquiv w)).mp hw
      simpa using h

/-- Compose two two-colored isomorphisms. -/
def trans {X : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {L : SimpleGraph X}
    {S T : Set V} {S' T' : Set W} {S'' T'' : Set X}
    (e₁ : TwoColorIso G H S T S' T')
    (e₂ : TwoColorIso H L S' T' S'' T'') :
    TwoColorIso G L S T S'' T'' where
  iso := e₁.iso.trans e₂.iso
  map_first := by
    intro v
    exact (e₁.map_first v).trans (e₂.map_first (e₁.iso.toEquiv v))
  map_second := by
    intro v
    exact (e₁.map_second v).trans (e₂.map_second (e₁.iso.toEquiv v))

end TwoColorIso

section FixedHost

/-- Delete a vertex from a vertex color. -/
def deleteColor (A : Set V) (z : V) : Set {w : V // w ≠ z} :=
  {w | w.1 ∈ A}

@[simp] theorem mem_deleteColor (A : Set V) (z : V) (w : {w : V // w ≠ z}) :
    w ∈ deleteColor A z ↔ w.1 ∈ A :=
  Iff.rfl

/-- The fixed-host colored card obtained from `(K, S, U)` by deleting `z`. -/
abbrev fixedHostCardGraph (K : SimpleGraph V) (z : V) : SimpleGraph {w : V // w ≠ z} :=
  K.deleteVert z

/-- Two fixed-host colored cards are isomorphic. -/
def FixedHostCardIso (K : SimpleGraph V) (S U V' : Set V) (z w : V) : Prop :=
  Nonempty
    (TwoColorIso (K.deleteVert z) (K.deleteVert w)
      (deleteColor S z) (deleteColor U z)
      (deleteColor S w) (deleteColor V' w))

/-- Fixed-host colored card isomorphism is symmetric. -/
theorem FixedHostCardIso.symm {K : SimpleGraph V} {S U V' : Set V} {z w : V}
    (h : FixedHostCardIso K S U V' z w) :
    FixedHostCardIso K S V' U w z := by
  rcases h with ⟨e⟩
  exact ⟨e.symm⟩

/-- Equality of fixed-host two-colored deletion decks, represented by a
matching of deleted vertices. -/
def FixedHostSameDeck (K : SimpleGraph V) (S U V' : Set V) : Prop :=
  ∃ σ : V ≃ V, ∀ z : V, FixedHostCardIso K S U V' z (σ z)

/-- Equality of restricted fixed-host two-colored deletion decks.  The deleted
vertices on the left are restricted to `R`, and the deleted vertices on the
right are restricted to `R'`.

This is the Lean object corresponding to a single color-size slice in the
fixed-host singleton argument. -/
def FixedHostSameSubdeck (K : SimpleGraph V) (S U V' R R' : Set V) : Prop :=
  ∃ σ : R ≃ R', ∀ z : R, FixedHostCardIso K S U V' z.1 (σ z).1

/-- Fixed-host same-deck is reflexive. -/
theorem FixedHostSameDeck.refl (K : SimpleGraph V) (S U : Set V) :
    FixedHostSameDeck K S U U := by
  refine ⟨Equiv.refl V, ?_⟩
  intro z
  exact ⟨TwoColorIso.refl (K.deleteVert z) (deleteColor S z) (deleteColor U z)⟩

/-- Fixed-host same-deck is symmetric. -/
theorem FixedHostSameDeck.symm {K : SimpleGraph V} {S U V' : Set V}
    (h : FixedHostSameDeck K S U V') :
    FixedHostSameDeck K S V' U := by
  rcases h with ⟨σ, hσ⟩
  refine ⟨σ.symm, ?_⟩
  intro z
  simpa using (hσ (σ.symm z)).symm

/-- Restricted fixed-host same-deck is reflexive. -/
theorem FixedHostSameSubdeck.refl (K : SimpleGraph V) (S U R : Set V) :
    FixedHostSameSubdeck K S U U R R := by
  refine ⟨Equiv.refl R, ?_⟩
  intro z
  exact ⟨TwoColorIso.refl (K.deleteVert z.1) (deleteColor S z.1) (deleteColor U z.1)⟩

/-- Restricted fixed-host same-deck is symmetric. -/
theorem FixedHostSameSubdeck.symm {K : SimpleGraph V} {S U V' R R' : Set V}
    (h : FixedHostSameSubdeck K S U V' R R') :
    FixedHostSameSubdeck K S V' U R' R := by
  rcases h with ⟨σ, hσ⟩
  refine ⟨σ.symm, ?_⟩
  intro z
  simpa using (hσ (σ.symm z)).symm

/-- The left singleton second color `T ∪ {a}`. -/
def singletonLeft (T : Set V) (a : V) : Set V :=
  T ∪ {a}

@[simp] theorem mem_singletonLeft (T : Set V) (a x : V) :
    x ∈ singletonLeft T a ↔ x ∈ T ∨ x = a := by
  constructor
  · intro h
    rcases h with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  · intro h
    rcases h with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx

/-- The right singleton second color `T ∪ {b}`. -/
def singletonRight (T : Set V) (b : V) : Set V :=
  T ∪ {b}

@[simp] theorem mem_singletonRight (T : Set V) (b x : V) :
    x ∈ singletonRight T b ↔ x ∈ T ∨ x = b := by
  constructor
  · intro h
    rcases h with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  · intro h
    rcases h with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx

/-- The outside set `O = V(K) \ (T ∪ {a,b})` in the singleton switch. -/
def singletonOutside (T : Set V) (a b : V) : Set V :=
  {x | x ∉ T ∧ x ≠ a ∧ x ≠ b}

@[simp] theorem mem_singletonOutside (T : Set V) (a b x : V) :
    x ∈ singletonOutside T a b ↔ x ∉ T ∧ x ≠ a ∧ x ≠ b :=
  Iff.rfl

/-- Vertices deleted in the complementary slice on the `a`-side:
`O ∪ {b}`. -/
def complementaryDeleteLeft (T : Set V) (a b : V) : Set V :=
  singletonOutside T a b ∪ {b}

@[simp] theorem mem_complementaryDeleteLeft (T : Set V) (a b x : V) :
    x ∈ complementaryDeleteLeft T a b ↔
      x ∈ singletonOutside T a b ∨ x = b := by
  constructor
  · intro h
    rcases h with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  · intro h
    rcases h with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx

/-- Vertices deleted in the complementary slice on the `b`-side:
`O ∪ {a}`. -/
def complementaryDeleteRight (T : Set V) (a b : V) : Set V :=
  singletonOutside T a b ∪ {a}

@[simp] theorem mem_complementaryDeleteRight (T : Set V) (a b x : V) :
    x ∈ complementaryDeleteRight T a b ↔
      x ∈ singletonOutside T a b ∨ x = a := by
  constructor
  · intro h
    rcases h with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  · intro h
    rcases h with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx

/-- The fixed-host singleton hypotheses: the active second color changes from
`T ∪ {a}` to `T ∪ {b}` and the fixed-host colored decks agree. -/
def FixedHostSingletonState (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  a ∉ T ∧ b ∉ T ∧ a ≠ b ∧
    FixedHostSameDeck K S (singletonLeft T a) (singletonRight T b)

/-- The desired singleton conclusion: a color-preserving automorphism of the
fixed host carries `T ∪ {a}` to `T ∪ {b}`. -/
def FixedHostSingletonSolved (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  Nonempty (TwoColorIso K K S (singletonLeft T a) S (singletonRight T b))

/-- The fixed-host singleton conjecture as a Lean proposition. -/
def FixedHostSingletonConjecture (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  FixedHostSingletonState K S T a b → FixedHostSingletonSolved K S T a b

/-- Equality of the low color-size slice
`{{H_a}} + {{A_t : t ∈ T}} = {{H_b}} + {{B_t : t ∈ T}}`, represented by a
matching between the second-colored deletion vertices. -/
def LowSliceSameDeck (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  FixedHostSameSubdeck K S (singletonLeft T a) (singletonRight T b)
    (singletonLeft T a) (singletonRight T b)

/-- Equality of the complementary color-size slice
`{{C_b^a}} + {{C_o^a : o ∈ O}} = {{C_a^b}} + {{C_o^b : o ∈ O}}`, represented
by a matching between the non-second-colored deletion vertices. -/
def ComplementarySliceSameDeck (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  FixedHostSameSubdeck K S (singletonLeft T a) (singletonRight T b)
    (complementaryDeleteLeft T a b) (complementaryDeleteRight T a b)

/-- A sharper possible route: the low slice alone reconstructs the fixed-host
orbit of the singleton color set. -/
def LowSliceOrbitReconstruction (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  LowSliceSameDeck K S T a b → FixedHostSingletonSolved K S T a b

/-- A chosen fixed-host card isomorphism.  Unlike `FixedHostCardIso`, this
remembers the actual card map, so we can ask whether its deleted-vertex star
extends correctly. -/
structure FixedHostCardIsoData (K : SimpleGraph V) (S U U' : Set V) (x y : V) where
  cardIso : TwoColorIso (K.deleteVert x) (K.deleteVert y)
    (deleteColor S x) (deleteColor U x)
    (deleteColor S y) (deleteColor U' y)

namespace FixedHostCardIsoData

/-- A chosen fixed-host card isomorphism gives the corresponding existential
card isomorphism. -/
theorem cardIsoProp {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) :
    FixedHostCardIso K S U U' x y :=
  ⟨e.cardIso⟩

/-- The deleted-vertex star error is zero when the card isomorphism transports
the neighbors of the left deleted vertex to the neighbors of the right deleted
vertex. -/
def ZeroStarError {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) : Prop :=
  ∀ z : {w : V // w ≠ x}, K.Adj x z.1 ↔ K.Adj y (e.cardIso.iso.toEquiv z).1

/-- A concrete failed adjacency in the deleted star of a chosen card
isomorphism. -/
def StarMismatch {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) (z : {w : V // w ≠ x}) : Prop :=
  ¬(K.Adj x z.1 ↔ K.Adj y (e.cardIso.iso.toEquiv z).1)

/-- A star mismatch whose source endpoint remains active after deleting `x`. -/
def ActiveStarMismatch {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) (z : {w : V // w ≠ x}) : Prop :=
  e.StarMismatch z ∧ z.1 ∈ U

/-- Zero star error is the same as having no concrete star mismatch. -/
theorem zeroStarError_iff_no_starMismatch
    {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) :
    e.ZeroStarError ↔ ∀ z : {w : V // w ≠ x}, ¬ e.StarMismatch z := by
  classical
  constructor
  · intro h z hz
    exact hz (h z)
  · intro h z
    exact Classical.not_not.mp (h z)

/-- A nonzero star error has a concrete witness. -/
theorem exists_starMismatch_of_not_zeroStarError
    {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y)
    (h : ¬ e.ZeroStarError) :
    ∃ z : {w : V // w ≠ x}, e.StarMismatch z := by
  classical
  by_contra hnone
  apply h
  exact (e.zeroStarError_iff_no_starMismatch).2 (by
    intro z hz
    exact hnone ⟨z, hz⟩)

/-- If every concrete mismatch is absent, the star error is zero. -/
theorem zeroStarError_of_no_starMismatch
    {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y)
    (h : ∀ z : {w : V // w ≠ x}, ¬ e.StarMismatch z) :
    e.ZeroStarError :=
  (e.zeroStarError_iff_no_starMismatch).2 h

/-- The chosen card map preserves the first color away from the deleted
vertices. -/
theorem map_first_iff {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) (z : {w : V // w ≠ x}) :
    z.1 ∈ S ↔ (e.cardIso.iso.toEquiv z).1 ∈ S := by
  simpa [deleteColor] using e.cardIso.map_first z

/-- The chosen card map carries the left second color to the right second
color away from the deleted vertices. -/
theorem map_second_iff {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) (z : {w : V // w ≠ x}) :
    z.1 ∈ U ↔ (e.cardIso.iso.toEquiv z).1 ∈ U' := by
  simpa [deleteColor] using e.cardIso.map_second z

/-- The number of deleted-star adjacencies on which a chosen card isomorphism
fails to extend. -/
noncomputable def starErrorCount [Finite V]
    {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) : ℕ := by
  classical
  letI := Fintype.ofFinite V
  exact Fintype.card {z : {w : V // w ≠ x} // e.StarMismatch z}

/-- The star-error count is zero exactly when the deleted star is transported
correctly. -/
theorem starErrorCount_eq_zero_iff [Finite V]
    {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) :
    e.starErrorCount = 0 ↔ e.ZeroStarError := by
  classical
  letI := Fintype.ofFinite V
  constructor
  · intro h
    dsimp [starErrorCount] at h
    have hEmpty : IsEmpty {z : {w : V // w ≠ x} // e.StarMismatch z} :=
      Fintype.card_eq_zero_iff.mp h
    exact e.zeroStarError_of_no_starMismatch (by
      intro z hz
      exact hEmpty.false ⟨z, hz⟩)
  · intro h
    dsimp [starErrorCount]
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun z => (e.zeroStarError_iff_no_starMismatch.mp h z.1) z.2⟩

/-- Positive star-error count is the same as nonzero deleted-star error. -/
theorem starErrorCount_pos_iff [Finite V]
    {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) :
    0 < e.starErrorCount ↔ ¬ e.ZeroStarError := by
  rw [← e.starErrorCount_eq_zero_iff, Nat.pos_iff_ne_zero]

/-- If the deleted vertex is first-colored, then the first-colored part of the
deleted card is strictly smaller than the full first color. -/
theorem deletedFirstColor_card_lt_of_mem
    [Fintype V] [DecidableEq V]
    {S : Set V} [DecidablePred (fun w : V => w ∈ S)] {x : V}
    (hx : x ∈ S) :
    Fintype.card {w : V // w ≠ x ∧ w ∈ S} <
      Fintype.card {w : V // w ∈ S} := by
  let f : {w : V // w ≠ x ∧ w ∈ S} → {w : V // w ∈ S} :=
    fun w => ⟨w.1, w.2.2⟩
  have hf : Function.Injective f := by
    intro u v huv
    have hval : (f u).1 = (f v).1 :=
      congrArg (fun q : {w : V // w ∈ S} => q.1) huv
    exact Subtype.ext hval
  have hnot : (⟨x, hx⟩ : {w : V // w ∈ S}) ∉ Set.range f := by
    rintro ⟨w, hw⟩
    have hxw : x = w.1 :=
      congrArg (fun q : {w : V // w ∈ S} => q.1) hw.symm
    exact w.2.1 hxw.symm
  exact Fintype.card_lt_of_injective_of_notMem f hf hnot

/-- If the deleted vertex is not first-colored, then deleting it does not change
the size of the first-colored part of the card. -/
theorem deletedFirstColor_card_eq_of_not_mem
    [Fintype V] [DecidableEq V]
    {S : Set V} [DecidablePred (fun w : V => w ∈ S)] {x : V}
    (hx : x ∉ S) :
    Fintype.card {w : V // w ≠ x ∧ w ∈ S} =
      Fintype.card {w : V // w ∈ S} := by
  refine Fintype.card_congr ?_
  refine
    { toFun := fun w => ⟨w.1, w.2.2⟩
      invFun := fun w => ⟨w.1, ?_, w.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro h
    exact hx (h ▸ w.2)
  · intro w
    apply Subtype.ext
    rfl
  · intro w
    apply Subtype.ext
    rfl

/-- A first-color-preserving card isomorphism identifies the cardinalities of
the first-colored parts of the two deleted cards. -/
theorem card_firstColor_eq
    [Fintype V] [DecidableEq V]
    {K : SimpleGraph V} {S U U' : Set V}
    [DecidablePred (fun w : V => w ∈ S)] {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) :
    Fintype.card {w : V // w ≠ x ∧ w ∈ S} =
      Fintype.card {w : V // w ≠ y ∧ w ∈ S} := by
  refine Fintype.card_congr ?_
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro w
    let z : {w : V // w ≠ x} := ⟨w.1, w.2.1⟩
    exact ⟨(e.cardIso.iso.toEquiv z).1, (e.cardIso.iso.toEquiv z).2,
      (e.map_first_iff z).mp w.2.2⟩
  · intro w
    let z : {w : V // w ≠ y} := ⟨w.1, w.2.1⟩
    exact ⟨(e.cardIso.iso.symm.toEquiv z).1,
      (e.cardIso.iso.symm.toEquiv z).2,
      (e.map_first_iff (e.cardIso.iso.symm.toEquiv z)).mpr (by
        simpa using w.2.2)⟩
  · intro w
    apply Subtype.ext
    simp
  · intro w
    apply Subtype.ext
    simp

/-- In a finite host, the first-color status of the deleted vertex is visible
from any first-color-preserving card isomorphism. -/
theorem firstColor_deleted_status_iff
    [Finite V] {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) :
    x ∈ S ↔ y ∈ S := by
  classical
  letI := Fintype.ofFinite V
  constructor
  · intro hx
    by_contra hy
    have hEq := card_firstColor_eq (S := S) e
    have hlt := deletedFirstColor_card_lt_of_mem (S := S) (x := x) hx
    have hright := deletedFirstColor_card_eq_of_not_mem (S := S) (x := y) hy
    rw [hEq, hright] at hlt
    exact (Nat.lt_irrefl _) hlt
  · intro hy
    by_contra hx
    have hEq := card_firstColor_eq (S := S) e
    have hleft := deletedFirstColor_card_eq_of_not_mem (S := S) (x := x) hx
    have hlt := deletedFirstColor_card_lt_of_mem (S := S) (x := y) hy
    rw [← hEq, hleft] at hlt
    exact (Nat.lt_irrefl _) hlt

section Extension

variable [DecidableEq V]

/-- Extend a card bijection between `K - x` and `K - y` to the full vertex set
by sending the left deleted vertex `x` to the right deleted vertex `y`. -/
def extendedEquiv {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) : V ≃ V :=
  (Equiv.optionSubtypeNe x).symm.trans
    ((Equiv.optionCongr e.cardIso.iso.toEquiv).trans (Equiv.optionSubtypeNe y))

@[simp] theorem extendedEquiv_apply_deleted
    {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) :
    e.extendedEquiv x = y := by
  simp [extendedEquiv]

theorem extendedEquiv_apply_ne {K : SimpleGraph V} {S U U' : Set V} {x y z : V}
    (e : FixedHostCardIsoData K S U U' x y) (hz : z ≠ x) :
    e.extendedEquiv z = (e.cardIso.iso.toEquiv ⟨z, hz⟩).1 := by
  simp [extendedEquiv, hz]

/-- A zero-star-error card isomorphism extends to a graph automorphism of the
fixed host, sending the deleted vertex on the left to the deleted vertex on the
right. -/
def extendIsoOfZeroStarError {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y) (hstar : e.ZeroStarError) :
    K ≃g K where
  toEquiv := e.extendedEquiv
  map_rel_iff' := by
    intro p q
    by_cases hp : p = x
    · subst p
      by_cases hq : q = x
      · subst q
        simp
      · simpa [extendedEquiv_apply_ne e hq] using (hstar ⟨q, hq⟩).symm
    · by_cases hq : q = x
      · subst q
        simpa [extendedEquiv_apply_ne e hp, SimpleGraph.adj_comm] using
          (hstar ⟨p, hp⟩).symm
      · simpa [SimpleGraph.deleteVert, extendedEquiv_apply_ne e hp, extendedEquiv_apply_ne e hq]
          using e.cardIso.iso.map_rel_iff (a := ⟨p, hp⟩) (b := ⟨q, hq⟩)

/-- If the deleted vertices have matching color status, then a zero-star-error
card isomorphism extends to a two-colored automorphism of the full fixed host. -/
def extendTwoColorIsoOfZeroStarError {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y)
    (hFirst : x ∈ S ↔ y ∈ S)
    (hSecond : x ∈ U ↔ y ∈ U')
    (hstar : e.ZeroStarError) :
    TwoColorIso K K S U S U' where
  iso := e.extendIsoOfZeroStarError hstar
  map_first := by
    intro z
    change z ∈ S ↔ e.extendedEquiv z ∈ S
    by_cases hz : z = x
    · subst z
      simpa using hFirst
    · simpa [extendedEquiv_apply_ne e hz] using e.map_first_iff ⟨z, hz⟩
  map_second := by
    intro z
    change z ∈ U ↔ e.extendedEquiv z ∈ U'
    by_cases hz : z = x
    · subst z
      simpa using hSecond
    · simpa [extendedEquiv_apply_ne e hz] using e.map_second_iff ⟨z, hz⟩

end Extension

/-- Nonempty wrapper for the general zero-star card-extension lemma. -/
theorem nonempty_twoColorIso_of_zeroStarError
    {K : SimpleGraph V} {S U U' : Set V} {x y : V}
    (e : FixedHostCardIsoData K S U U' x y)
    (hFirst : x ∈ S ↔ y ∈ S)
    (hSecond : x ∈ U ↔ y ∈ U')
    (hstar : e.ZeroStarError) :
    Nonempty (TwoColorIso K K S U S U') := by
  classical
  exact ⟨e.extendTwoColorIsoOfZeroStarError hFirst hSecond hstar⟩

/-- Restrict a full two-colored automorphism to the card obtained by deleting
`x` and its image. -/
def ofTwoColorIso {K : SimpleGraph V} {S U U' : Set V}
    (e : TwoColorIso K K S U S U') (x : V) :
    FixedHostCardIsoData K S U U' x (e.iso.toEquiv x) where
  cardIso := {
    iso := {
      toEquiv := {
        toFun z := ⟨e.iso.toEquiv z.1, by
          intro hz
          exact z.2 (e.iso.toEquiv.injective hz)⟩
        invFun z := ⟨e.iso.symm.toEquiv z.1, by
          intro hz
          exact z.2 (by
            calc z.1 = e.iso.toEquiv (e.iso.symm.toEquiv z.1) := by simp
              _ = e.iso.toEquiv x := by rw [hz])⟩
        left_inv := by
          intro z
          apply Subtype.ext
          simp
        right_inv := by
          intro z
          apply Subtype.ext
          simp }
      map_rel_iff' := by
        intro z w
        simpa [SimpleGraph.deleteVert] using
          e.iso.map_rel_iff (a := z.1) (b := w.1) }
    map_first := by
      intro z
      simpa [deleteColor] using e.map_first z.1
    map_second := by
      intro z
      simpa [deleteColor] using e.map_second z.1 }

/-- The card restriction of a full automorphism has zero deleted-star error. -/
theorem ofTwoColorIso_zeroStarError {K : SimpleGraph V} {S U U' : Set V}
    (e : TwoColorIso K K S U S U') (x : V) :
    (ofTwoColorIso e x).ZeroStarError := by
  intro z
  simpa [ofTwoColorIso, ZeroStarError] using
    (e.iso.map_rel_iff (a := x) (b := z.1)).symm

/-- Singleton-switch specialization of the general zero-star card-extension
lemma for a low-slice step deleting active vertices on both sides. -/
theorem solved_singleton_of_zeroStarError_active
    {K : SimpleGraph V} {S T : Set V} {a b x y : V}
    (e : FixedHostCardIsoData K S (singletonLeft T a) (singletonRight T b) x y)
    (hFirst : x ∈ S ↔ y ∈ S)
    (hxActive : x ∈ singletonLeft T a)
    (hyActive : y ∈ singletonRight T b)
    (hstar : e.ZeroStarError) :
    FixedHostSingletonSolved K S T a b := by
  have hSecond : x ∈ singletonLeft T a ↔ y ∈ singletonRight T b :=
    ⟨fun _ => hyActive, fun _ => hxActive⟩
  exact e.nonempty_twoColorIso_of_zeroStarError hFirst hSecond hstar

end FixedHostCardIsoData

/-- A chosen matching of two restricted fixed-host subdecks, including the
actual card isomorphism for each matched deleted vertex. -/
structure FixedHostSubdeckIsoData
    (K : SimpleGraph V) (S U U' R R' : Set V) where
  toEquiv : R ≃ R'
  cardIso : ∀ z : R, FixedHostCardIsoData K S U U' z.1 (toEquiv z).1

namespace FixedHostSubdeckIsoData

/-- A chosen restricted subdeck matching gives the corresponding existential
same-subdeck proposition. -/
theorem sameSubdeck {K : SimpleGraph V} {S U U' R R' : Set V}
    (e : FixedHostSubdeckIsoData K S U U' R R') :
    FixedHostSameSubdeck K S U U' R R' := by
  refine ⟨e.toEquiv, ?_⟩
  intro z
  exact (e.cardIso z).cardIsoProp

/-- Choose concrete card isomorphisms from an existential restricted subdeck
matching. -/
noncomputable def ofSameSubdeck {K : SimpleGraph V} {S U U' R R' : Set V}
    (h : FixedHostSameSubdeck K S U U' R R') :
    FixedHostSubdeckIsoData K S U U' R R' where
  toEquiv := Classical.choose h
  cardIso := fun z => ⟨Classical.choice (Classical.choose_spec h z)⟩

end FixedHostSubdeckIsoData

/-- A chosen low-slice matching for the singleton switch. -/
abbrev LowSliceIsoData (K : SimpleGraph V) (S T : Set V) (a b : V) :=
  FixedHostSubdeckIsoData K S (singletonLeft T a) (singletonRight T b)
    (singletonLeft T a) (singletonRight T b)

/-- The active zero-star pair target: some low-slice card match deletes an
active vertex on each side, has matching first-color status, and has zero
deleted-star error. -/
def LowSliceZeroStarPair (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  ∃ x : singletonLeft T a,
    ∃ y : singletonRight T b,
      ∃ e : FixedHostCardIsoData K S (singletonLeft T a) (singletonRight T b) x.1 y.1,
        (x.1 ∈ S ↔ y.1 ∈ S) ∧ e.ZeroStarError

/-- A perfect zero-star matching of the active deletion deck.  This is the
global version of `LowSliceZeroStarPair`: every active deleted vertex is
matched to an active deleted vertex by a card isomorphism whose deleted-star
error is zero. -/
structure LowSliceZeroStarMatching (K : SimpleGraph V) (S T : Set V) (a b : V) where
  toEquiv : singletonLeft T a ≃ singletonRight T b
  cardIso : ∀ x : singletonLeft T a,
    FixedHostCardIsoData K S (singletonLeft T a) (singletonRight T b) x.1 (toEquiv x).1
  first_status : ∀ x : singletonLeft T a, x.1 ∈ S ↔ (toEquiv x).1 ∈ S
  zero_star : ∀ x : singletonLeft T a, (cardIso x).ZeroStarError

namespace LowSliceZeroStarMatching

/-- A perfect zero-star matching solves the singleton switch. -/
theorem solved {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceZeroStarMatching K S T a b) :
    FixedHostSingletonSolved K S T a b := by
  let x : singletonLeft T a := ⟨a, by simp⟩
  exact (m.cardIso x).solved_singleton_of_zeroStarError_active
    (m.first_status x) x.2 (m.toEquiv x).2 (m.zero_star x)

/-- Any full solution induces a perfect zero-star matching of the active
deletion deck. -/
noncomputable def of_solved {K : SimpleGraph V} {S T : Set V} {a b : V}
    (h : FixedHostSingletonSolved K S T a b) :
    LowSliceZeroStarMatching K S T a b := by
  classical
  let e := Classical.choice h
  refine
    { toEquiv := ?_
      cardIso := ?_
      first_status := ?_
      zero_star := ?_ }
  · refine
      { toFun := fun x => ⟨e.iso.toEquiv x.1, (e.map_second x.1).mp x.2⟩
        invFun := fun y => ⟨e.iso.symm.toEquiv y.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · exact (e.map_second (e.iso.symm.toEquiv y.1)).mpr (by simp [y.2])
    · intro x
      apply Subtype.ext
      simp
    · intro y
      apply Subtype.ext
      simp
  · intro x
    exact FixedHostCardIsoData.ofTwoColorIso e x.1
  · intro x
    exact e.map_first x.1
  · intro x
    exact FixedHostCardIsoData.ofTwoColorIso_zeroStarError e x.1

/-- Existence of a perfect zero-star matching is equivalent to the desired
orbit conclusion. -/
theorem nonempty_iff_solved {K : SimpleGraph V} {S T : Set V} {a b : V} :
    Nonempty (LowSliceZeroStarMatching K S T a b) ↔ FixedHostSingletonSolved K S T a b := by
  constructor
  · rintro ⟨m⟩
    exact m.solved
  · intro h
    exact ⟨of_solved h⟩

/-- A perfect zero-star matching contains, in particular, an active zero-star
pair. -/
theorem to_pair {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceZeroStarMatching K S T a b) :
    LowSliceZeroStarPair K S T a b := by
  let x : singletonLeft T a := ⟨a, by simp⟩
  exact ⟨x, m.toEquiv x, m.cardIso x, m.first_status x, m.zero_star x⟩

end LowSliceZeroStarMatching

namespace LowSliceZeroStarPair

/-- An active zero-star pair is enough to solve the singleton switch. -/
theorem solved {K : SimpleGraph V} {S T : Set V} {a b : V}
    (h : LowSliceZeroStarPair K S T a b) :
    FixedHostSingletonSolved K S T a b := by
  rcases h with ⟨x, y, e, hFirst, hstar⟩
  exact e.solved_singleton_of_zeroStarError_active hFirst x.2 y.2 hstar

/-- Conversely, any full solution restricts to an active zero-star pair.  Thus
`LowSliceZeroStarPair` is the orbit conclusion packaged as a deck-visible
witness. -/
theorem of_solved {K : SimpleGraph V} {S T : Set V} {a b : V}
    (h : FixedHostSingletonSolved K S T a b) :
    LowSliceZeroStarPair K S T a b := by
  rcases h with ⟨e⟩
  let x : singletonLeft T a := ⟨a, by simp⟩
  let y : singletonRight T b := ⟨e.iso.toEquiv a, by
    exact (e.map_second a).mp (by simp)⟩
  refine ⟨x, y, FixedHostCardIsoData.ofTwoColorIso e a, ?_, ?_⟩
  · simpa [x, y] using e.map_first a
  · simpa [x, y] using FixedHostCardIsoData.ofTwoColorIso_zeroStarError e a

/-- Active zero-star pairs are equivalent to the desired fixed-host singleton
orbit conclusion. -/
theorem iff_solved {K : SimpleGraph V} {S T : Set V} {a b : V} :
    LowSliceZeroStarPair K S T a b ↔ FixedHostSingletonSolved K S T a b :=
  ⟨solved, of_solved⟩

/-- The one-pair and perfect-matching zero-star formulations are equivalent.
The perfect matching is not extra mathematics: a full solution induces one,
and any one of its edges is already enough. -/
theorem iff_nonempty_zeroStarMatching
    {K : SimpleGraph V} {S T : Set V} {a b : V} :
    LowSliceZeroStarPair K S T a b ↔
      Nonempty (LowSliceZeroStarMatching K S T a b) :=
  iff_solved.trans LowSliceZeroStarMatching.nonempty_iff_solved.symm

/-- In a no-zero-star-pair obstruction, every active card match has a concrete
deleted-star mismatch. -/
theorem exists_starMismatch_of_no_pair
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (hno : ¬ LowSliceZeroStarPair K S T a b)
    (x : singletonLeft T a) (y : singletonRight T b)
    (e : FixedHostCardIsoData K S (singletonLeft T a) (singletonRight T b) x.1 y.1)
    (hFirst : x.1 ∈ S ↔ y.1 ∈ S) :
    ∃ z : {w : V // w ≠ x.1}, e.StarMismatch z := by
  classical
  by_contra hnone
  apply hno
  refine ⟨x, y, e, hFirst, ?_⟩
  exact e.zeroStarError_of_no_starMismatch (by
    intro z hz
    exact hnone ⟨z, hz⟩)

/-- Normal form for the local obstruction: there is no active zero-star pair
exactly when every active card match has a concrete deleted-star mismatch. -/
theorem no_pair_iff_all_matches_have_starMismatch
    {K : SimpleGraph V} {S T : Set V} {a b : V} :
    (¬ LowSliceZeroStarPair K S T a b) ↔
      ∀ (x : singletonLeft T a) (y : singletonRight T b),
        ∀ e : FixedHostCardIsoData K S
            (singletonLeft T a) (singletonRight T b) x.1 y.1,
          (x.1 ∈ S ↔ y.1 ∈ S) →
            ∃ z : {w : V // w ≠ x.1}, e.StarMismatch z := by
  constructor
  · intro hno x y e hFirst
    exact exists_starMismatch_of_no_pair hno x y e hFirst
  · intro hall hpair
    rcases hpair with ⟨x, y, e, hFirst, hzero⟩
    rcases hall x y e hFirst with ⟨z, hz⟩
    exact (e.zeroStarError_iff_no_starMismatch.mp hzero z) hz

end LowSliceZeroStarPair

/-- The current focused local conjecture: low-slice equality exposes an active
zero-star pair. -/
def LowSliceZeroStarPairConjecture (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  LowSliceSameDeck K S T a b → LowSliceZeroStarPair K S T a b

/-- The active zero-star pair conjecture implies the low-slice orbit
reconstruction target. -/
theorem LowSliceOrbitReconstruction.of_zeroStarPair
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (h : LowSliceZeroStarPairConjecture K S T a b) :
    LowSliceOrbitReconstruction K S T a b := by
  intro hlow
  exact (h hlow).solved

/-- The active-zero-star formulation is equivalent to low-slice orbit
reconstruction; it is a local witness formulation of the same target. -/
theorem LowSliceZeroStarPairConjecture.iff_orbitReconstruction
    {K : SimpleGraph V} {S T : Set V} {a b : V} :
    LowSliceZeroStarPairConjecture K S T a b ↔
      LowSliceOrbitReconstruction K S T a b := by
  constructor
  · exact LowSliceOrbitReconstruction.of_zeroStarPair
  · intro h hlow
    exact LowSliceZeroStarPair.of_solved (h hlow)

namespace LowSliceIsoData

/-- Choose a concrete low-slice matching from low-slice deck equality. -/
noncomputable def ofSameDeck {K : SimpleGraph V} {S T : Set V} {a b : V}
    (h : LowSliceSameDeck K S T a b) :
    LowSliceIsoData K S T a b :=
  FixedHostSubdeckIsoData.ofSameSubdeck h

/-- In finite hosts, every chosen low-slice card match has matching passive
first-color status. -/
theorem first_status [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (e : LowSliceIsoData K S T a b) (x : singletonLeft T a) :
    x.1 ∈ S ↔ (e.toEquiv x).1 ∈ S :=
  (e.cardIso x).firstColor_deleted_status_iff

/-- If one matched low-slice card has zero star error and the two deleted
vertices have the same passive first-color status, then that single card match
extends to a full solution of the singleton switch. -/
theorem solved_of_zeroStarError_at
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (e : LowSliceIsoData K S T a b) (x : singletonLeft T a)
    (hFirst : x.1 ∈ S ↔ (e.toEquiv x).1 ∈ S)
    (hstar : (e.cardIso x).ZeroStarError) :
    FixedHostSingletonSolved K S T a b :=
  (e.cardIso x).solved_singleton_of_zeroStarError_active
    hFirst x.2 (e.toEquiv x).2 hstar

/-- If every chosen low-slice card match has zero star error and matching
first-color status, then the chosen low-slice matching is a perfect zero-star
matching. -/
def toZeroStarMatching
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (e : LowSliceIsoData K S T a b)
    (hFirst : ∀ x : singletonLeft T a, x.1 ∈ S ↔ (e.toEquiv x).1 ∈ S)
    (hstar : ∀ x : singletonLeft T a, (e.cardIso x).ZeroStarError) :
    LowSliceZeroStarMatching K S T a b where
  toEquiv := e.toEquiv
  cardIso := e.cardIso
  first_status := hFirst
  zero_star := hstar

end LowSliceIsoData

/-- A chosen complementary-slice matching for the singleton switch. -/
abbrev ComplementarySliceIsoData (K : SimpleGraph V) (S T : Set V) (a b : V) :=
  FixedHostSubdeckIsoData K S (singletonLeft T a) (singletonRight T b)
    (complementaryDeleteLeft T a b) (complementaryDeleteRight T a b)

/-- The two-hole vertex type obtained by deleting `t` and `o`. -/
abbrev deleteTwoVertex (t o : V) :=
  {x : V // x ≠ t ∧ x ≠ o}

/-- The graph `K - {t,o}`. -/
def deleteTwo (K : SimpleGraph V) (t o : V) : SimpleGraph (deleteTwoVertex t o) :=
  K.induce {x | x ≠ t ∧ x ≠ o}

/-- Delete two vertices from a color. -/
def deleteTwoColor (A : Set V) (t o : V) : Set (deleteTwoVertex t o) :=
  {x | x.1 ∈ A}

@[simp] theorem mem_deleteTwoColor (A : Set V) (t o : V) (x : deleteTwoVertex t o) :
    x ∈ deleteTwoColor A t o ↔ x.1 ∈ A :=
  Iff.rfl

namespace FixedHostCardIsoData

/-- Restrict a chosen one-card isomorphism to the two-hole card obtained by
also deleting a surviving vertex `z`.  This is the formal version of isolating
a star-error witness in a common two-hole base. -/
def restrictDeleteTwo {K : SimpleGraph V} {S U U' : Set V} {x y z : V}
    (e : FixedHostCardIsoData K S U U' x y) (hz : z ≠ x) :
    TwoColorIso (deleteTwo K x z)
      (deleteTwo K y (e.cardIso.iso.toEquiv ⟨z, hz⟩).1)
      (deleteTwoColor S x z) (deleteTwoColor U x z)
      (deleteTwoColor S y (e.cardIso.iso.toEquiv ⟨z, hz⟩).1)
      (deleteTwoColor U' y (e.cardIso.iso.toEquiv ⟨z, hz⟩).1) where
  iso := {
    toEquiv := {
      toFun w := ⟨(e.cardIso.iso.toEquiv ⟨w.1, w.2.1⟩).1,
        by exact (e.cardIso.iso.toEquiv ⟨w.1, w.2.1⟩).2,
        by
          intro h
          have hsub :
              e.cardIso.iso.toEquiv ⟨w.1, w.2.1⟩ =
                e.cardIso.iso.toEquiv ⟨z, hz⟩ := Subtype.ext h
          have hwz : w.1 = z := congrArg Subtype.val (e.cardIso.iso.toEquiv.injective hsub)
          exact w.2.2 hwz⟩
      invFun w := ⟨(e.cardIso.iso.symm.toEquiv ⟨w.1, w.2.1⟩).1,
        by exact (e.cardIso.iso.symm.toEquiv ⟨w.1, w.2.1⟩).2,
        by
          intro h
          have hpre :
              e.cardIso.iso.symm.toEquiv ⟨w.1, w.2.1⟩ = ⟨z, hz⟩ :=
            Subtype.ext h
          have hval :
              w.1 = (e.cardIso.iso.toEquiv ⟨z, hz⟩).1 := by
            have hmap := congrArg Subtype.val (congrArg e.cardIso.iso.toEquiv hpre)
            simpa using hmap
          exact w.2.2 hval⟩
      left_inv := by
        intro w
        apply Subtype.ext
        simp
      right_inv := by
        intro w
        apply Subtype.ext
        simp }
    map_rel_iff' := by
      intro p q
      simpa [deleteTwo, SimpleGraph.deleteVert] using
        e.cardIso.iso.map_rel_iff (a := ⟨p.1, p.2.1⟩) (b := ⟨q.1, q.2.1⟩) }
  map_first := by
    intro w
    simpa [deleteTwoColor, deleteColor] using e.cardIso.map_first ⟨w.1, w.2.1⟩
  map_second := by
    intro w
    simpa [deleteTwoColor, deleteColor] using e.cardIso.map_second ⟨w.1, w.2.1⟩

end FixedHostCardIsoData

/-- A localized first star error for one active low-slice card match.  The
witness records both the failed deleted-star adjacency and the common two-hole
colored card obtained by deleting the failed surviving vertex as well. -/
structure LowSliceCardFirstError
    (K : SimpleGraph V) (S T : Set V) (a b : V)
    (x : singletonLeft T a) (y : singletonRight T b)
    (e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1) where
  z : {w : V // w ≠ x.1}
  mismatch : e.StarMismatch z
  twoHoleIso :
    TwoColorIso (deleteTwo K x.1 z.1)
      (deleteTwo K y.1 (e.cardIso.iso.toEquiv z).1)
      (deleteTwoColor S x.1 z.1)
      (deleteTwoColor (singletonLeft T a) x.1 z.1)
      (deleteTwoColor S y.1 (e.cardIso.iso.toEquiv z).1)
      (deleteTwoColor (singletonRight T b) y.1
        (e.cardIso.iso.toEquiv z).1)

namespace LowSliceCardFirstError

/-- The image of the first-error vertex on the right card. -/
def imageZ {K : SimpleGraph V} {S T : Set V} {a b : V}
    {x : singletonLeft T a} {y : singletonRight T b}
    {e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1}
    (E : LowSliceCardFirstError K S T a b x y e) : V :=
  (e.cardIso.iso.toEquiv E.z).1

/-- The first-error witness is active when its source vertex is still in the
left active color after deleting `x`. -/
def Active {K : SimpleGraph V} {S T : Set V} {a b : V}
    {x : singletonLeft T a} {y : singletonRight T b}
    {e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1}
    (E : LowSliceCardFirstError K S T a b x y e) : Prop :=
  E.z.1 ∈ singletonLeft T a

/-- The first-error witness is inactive when its source vertex is outside the
left active color after deleting `x`. -/
def Inactive {K : SimpleGraph V} {S T : Set V} {a b : V}
    {x : singletonLeft T a} {y : singletonRight T b}
    {e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1}
    (E : LowSliceCardFirstError K S T a b x y e) : Prop :=
  E.z.1 ∉ singletonLeft T a

/-- The localized target vertex is still present in the right card. -/
theorem imageZ_ne_deleted {K : SimpleGraph V} {S T : Set V} {a b : V}
    {x : singletonLeft T a} {y : singletonRight T b}
    {e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1}
    (E : LowSliceCardFirstError K S T a b x y e) :
    E.imageZ ≠ y.1 := by
  simpa [imageZ] using (e.cardIso.iso.toEquiv E.z).2

/-- The first-error witness has the same active-color status on the two
localized cards. -/
theorem sourceActive_iff_targetActive
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {x : singletonLeft T a} {y : singletonRight T b}
    {e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1}
    (E : LowSliceCardFirstError K S T a b x y e) :
    E.z.1 ∈ singletonLeft T a ↔ E.imageZ ∈ singletonRight T b := by
  simpa [imageZ] using e.map_second_iff E.z

/-- Equivalently, inactive first-error witnesses also stay inactive. -/
theorem sourceInactive_iff_targetInactive
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {x : singletonLeft T a} {y : singletonRight T b}
    {e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1}
    (E : LowSliceCardFirstError K S T a b x y e) :
    E.z.1 ∉ singletonLeft T a ↔ E.imageZ ∉ singletonRight T b :=
  not_congr E.sourceActive_iff_targetActive

/-- Every localized first error is either active-active or inactive-inactive. -/
theorem active_or_inactive
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {x : singletonLeft T a} {y : singletonRight T b}
    {e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1}
    (E : LowSliceCardFirstError K S T a b x y e) :
    (E.Active ∧ E.imageZ ∈ singletonRight T b) ∨
      (E.Inactive ∧ E.imageZ ∉ singletonRight T b) := by
  classical
  by_cases h : E.z.1 ∈ singletonLeft T a
  · exact Or.inl ⟨h, E.sourceActive_iff_targetActive.mp h⟩
  · exact Or.inr ⟨h, E.sourceInactive_iff_targetInactive.mp h⟩

/-- Every localized first error is, in source terms, active or inactive. -/
theorem active_or_inactive_source
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {x : singletonLeft T a} {y : singletonRight T b}
    {e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1}
    (E : LowSliceCardFirstError K S T a b x y e) :
    E.Active ∨ E.Inactive := by
  classical
  exact em E.Active

/-- Recenter an active first-error witness at its source first-error vertex. -/
def sourceActiveVertex
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {x : singletonLeft T a} {y : singletonRight T b}
    {e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1}
    (E : LowSliceCardFirstError K S T a b x y e) (hE : E.Active) :
    singletonLeft T a :=
  ⟨E.z.1, hE⟩

/-- Recenter an active first-error witness at its target first-error vertex. -/
def targetActiveVertex
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {x : singletonLeft T a} {y : singletonRight T b}
    {e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1}
    (E : LowSliceCardFirstError K S T a b x y e) (hE : E.Active) :
    singletonRight T b :=
  ⟨E.imageZ, E.sourceActive_iff_targetActive.mp hE⟩

/-- The first-error witness has the same passive first-color status on the two
localized cards. -/
theorem sourceFirst_iff_targetFirst
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {x : singletonLeft T a} {y : singletonRight T b}
    {e : FixedHostCardIsoData K S
      (singletonLeft T a) (singletonRight T b) x.1 y.1}
    (E : LowSliceCardFirstError K S T a b x y e) :
    E.z.1 ∈ S ↔ E.imageZ ∈ S := by
  simpa [imageZ] using e.map_first_iff E.z

end LowSliceCardFirstError

/-- The local obstruction form: every visible active card match with matching
first-color status has a concrete first star error above a common two-hole
colored card. -/
def LowSliceLocalObstruction
    (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  ∀ (x : singletonLeft T a) (y : singletonRight T b),
    ∀ e : FixedHostCardIsoData K S
        (singletonLeft T a) (singletonRight T b) x.1 y.1,
      (x.1 ∈ S ↔ y.1 ∈ S) →
        Nonempty (LowSliceCardFirstError K S T a b x y e)

namespace LowSliceZeroStarPair

/-- In a no-zero-star-pair obstruction, every active card match localizes to a
two-hole card together with a concrete star mismatch over that two-hole base. -/
theorem exists_starMismatch_with_twoHole_of_no_pair
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (hno : ¬ LowSliceZeroStarPair K S T a b)
    (x : singletonLeft T a) (y : singletonRight T b)
    (e : FixedHostCardIsoData K S (singletonLeft T a) (singletonRight T b) x.1 y.1)
    (hFirst : x.1 ∈ S ↔ y.1 ∈ S) :
    ∃ z : {w : V // w ≠ x.1},
      e.StarMismatch z ∧
        Nonempty
          (TwoColorIso (deleteTwo K x.1 z.1)
            (deleteTwo K y.1 (e.cardIso.iso.toEquiv z).1)
            (deleteTwoColor S x.1 z.1)
            (deleteTwoColor (singletonLeft T a) x.1 z.1)
            (deleteTwoColor S y.1 (e.cardIso.iso.toEquiv z).1)
            (deleteTwoColor (singletonRight T b) y.1
              (e.cardIso.iso.toEquiv z).1)) := by
  rcases exists_starMismatch_of_no_pair hno x y e hFirst with ⟨z, hz⟩
  exact ⟨z, hz, ⟨e.restrictDeleteTwo z.2⟩⟩

/-- In a no-zero-star-pair obstruction, every visible active card match has a
packaged first-error witness. -/
theorem cardFirstError_of_no_pair
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (hno : ¬ LowSliceZeroStarPair K S T a b)
    (x : singletonLeft T a) (y : singletonRight T b)
    (e : FixedHostCardIsoData K S (singletonLeft T a) (singletonRight T b) x.1 y.1)
    (hFirst : x.1 ∈ S ↔ y.1 ∈ S) :
    Nonempty (LowSliceCardFirstError K S T a b x y e) := by
  rcases exists_starMismatch_of_no_pair hno x y e hFirst with ⟨z, hz⟩
  exact ⟨
    { z := z
      mismatch := hz
      twoHoleIso := e.restrictDeleteTwo z.2 }⟩

/-- The absence of an active zero-star pair is equivalent to the local
first-error obstruction. -/
theorem localObstruction_iff_no_pair
    {K : SimpleGraph V} {S T : Set V} {a b : V} :
    LowSliceLocalObstruction K S T a b ↔
      ¬ LowSliceZeroStarPair K S T a b := by
  constructor
  · intro hlocal hpair
    rcases hpair with ⟨x, y, e, hFirst, hzero⟩
    rcases hlocal x y e hFirst with ⟨E⟩
    exact (e.zeroStarError_iff_no_starMismatch.mp hzero E.z) E.mismatch
  · intro hno x y e hFirst
    exact cardFirstError_of_no_pair hno x y e hFirst

/-- Restatement in the direction used by the proof campaign: if there is no
active zero-star pair, then the obstruction can be worked with locally above
each active card edge. -/
theorem localObstruction_of_no_pair
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (hno : ¬ LowSliceZeroStarPair K S T a b) :
    LowSliceLocalObstruction K S T a b :=
  localObstruction_iff_no_pair.mpr hno

end LowSliceZeroStarPair

namespace LowSliceIsoData

/-- Under a no-zero-star-pair assumption, every edge of a chosen finite
low-slice matching has a packaged first-error witness. -/
theorem firstError_of_no_pair [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (e : LowSliceIsoData K S T a b)
    (hno : ¬ LowSliceZeroStarPair K S T a b)
    (x : singletonLeft T a) :
    Nonempty
      (LowSliceCardFirstError K S T a b x (e.toEquiv x) (e.cardIso x)) :=
  LowSliceZeroStarPair.cardFirstError_of_no_pair hno x (e.toEquiv x)
    (e.cardIso x) (e.first_status x)

/-- The total deleted-star error of a chosen low-slice matching. -/
noncomputable def totalStarErrorCount [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (e : LowSliceIsoData K S T a b) : ℕ := by
  classical
  letI := Fintype.ofFinite V
  exact ∑ x : singletonLeft T a,
    FixedHostCardIsoData.starErrorCount (e.cardIso x)

/-- Total star error is zero exactly when every matched low-slice card has zero
star error. -/
theorem totalStarErrorCount_eq_zero_iff [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (e : LowSliceIsoData K S T a b) :
    e.totalStarErrorCount = 0 ↔
      ∀ x : singletonLeft T a, (e.cardIso x).ZeroStarError := by
  classical
  letI := Fintype.ofFinite V
  dsimp [totalStarErrorCount]
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · simp [FixedHostCardIsoData.starErrorCount_eq_zero_iff]
  · intro x hx
    exact Nat.zero_le _

/-- A zero-total-error low-slice matching is a perfect zero-star matching. -/
def toZeroStarMatchingOfTotalErrorZero [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (e : LowSliceIsoData K S T a b)
    (hzero : e.totalStarErrorCount = 0) :
    LowSliceZeroStarMatching K S T a b :=
  e.toZeroStarMatching e.first_status (e.totalStarErrorCount_eq_zero_iff.mp hzero)

/-- Forget the zero-star fields of a perfect zero-star matching, keeping only
the underlying chosen low-slice matching. -/
def ofZeroStarMatching {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceZeroStarMatching K S T a b) :
    LowSliceIsoData K S T a b where
  toEquiv := m.toEquiv
  cardIso := m.cardIso

/-- The low-slice matching underlying a perfect zero-star matching has total
star error zero. -/
theorem totalStarErrorCount_ofZeroStarMatching [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceZeroStarMatching K S T a b) :
    (ofZeroStarMatching m).totalStarErrorCount = 0 :=
  ((ofZeroStarMatching m).totalStarErrorCount_eq_zero_iff).mpr m.zero_star

/-- A chosen low-slice matching has no zero-star edge. -/
def NoZeroStarEdge {K : SimpleGraph V} {S T : Set V} {a b : V}
    (e : LowSliceIsoData K S T a b) : Prop :=
  ∀ x : singletonLeft T a, ¬ (e.cardIso x).ZeroStarError

/-- No zero-star edge is equivalent to every matched card carrying positive
star error. -/
theorem noZeroStarEdge_iff_forall_pos [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (e : LowSliceIsoData K S T a b) :
    e.NoZeroStarEdge ↔
      ∀ x : singletonLeft T a,
        0 < FixedHostCardIsoData.starErrorCount (e.cardIso x) := by
  simp [NoZeroStarEdge, FixedHostCardIsoData.starErrorCount_pos_iff]

/-- A chosen low-slice matching has minimum total star error among all chosen
low-slice matchings. -/
def IsMinimumStarError [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (e : LowSliceIsoData K S T a b) : Prop :=
  ∀ e' : LowSliceIsoData K S T a b,
    e.totalStarErrorCount ≤ e'.totalStarErrorCount

end LowSliceIsoData

/-- A minimum-error chosen low-slice matching.  This is the formal counterpart
of choosing a minimum-error active-card matching in the proof sketch. -/
structure LowSliceMinimumErrorMatching
    (K : SimpleGraph V) (S T : Set V) (a b : V) [Finite V] where
  toIsoData : LowSliceIsoData K S T a b
  minimum : toIsoData.IsMinimumStarError

namespace LowSliceMinimumErrorMatching

/-- Low-slice equality admits a minimum-error chosen matching.  The proof uses
well-ordering of `ℕ` on the set of total star-error values, not finiteness of
the space of card isomorphisms. -/
theorem exists_of_sameDeck [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (hlow : LowSliceSameDeck K S T a b) :
    Nonempty (LowSliceMinimumErrorMatching K S T a b) := by
  classical
  let e0 : LowSliceIsoData K S T a b := LowSliceIsoData.ofSameDeck hlow
  let P : ℕ → Prop :=
    fun n => ∃ e : LowSliceIsoData K S T a b, e.totalStarErrorCount = n
  have hP : ∃ n, P n := ⟨e0.totalStarErrorCount, e0, rfl⟩
  let nmin := Nat.find hP
  rcases Nat.find_spec hP with ⟨emin, hemin⟩
  refine ⟨{ toIsoData := emin, minimum := ?_ }⟩
  intro e'
  have hle : nmin ≤ e'.totalStarErrorCount := Nat.find_min' hP ⟨e', rfl⟩
  rw [hemin]
  exact hle

/-- An active first-error witness above one edge of a minimum-error matching. -/
structure ActiveFirstError [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceMinimumErrorMatching K S T a b)
    (x : singletonLeft T a) where
  error :
    LowSliceCardFirstError K S T a b x
      (m.toIsoData.toEquiv x) (m.toIsoData.cardIso x)
  active : error.Active

/-- An inactive first-error witness above one edge of a minimum-error matching. -/
structure InactiveFirstError [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceMinimumErrorMatching K S T a b)
    (x : singletonLeft T a) where
  error :
    LowSliceCardFirstError K S T a b x
      (m.toIsoData.toEquiv x) (m.toIsoData.cardIso x)
  inactive : error.Inactive

namespace ActiveFirstError

/-- The active source vertex reached by following this first error. -/
def source [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x) :
    singletonLeft T a :=
  E.error.sourceActiveVertex E.active

/-- The active target vertex reached by following this first error. -/
def target [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x) :
    singletonRight T b :=
  E.error.targetActiveVertex E.active

/-- The left vertex currently matched to the active target of this first error.
This is the successor vertex in the alternating exchange graph. -/
def nextLeft [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x) :
    singletonLeft T a :=
  m.toIsoData.toEquiv.symm E.target

@[simp] theorem toEquiv_nextLeft [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x) :
    m.toIsoData.toEquiv E.nextLeft = E.target := by
  simp [nextLeft]

/-- A coherent active first error points at the right mate of its own active
source.  These are the side-cycle cases in the exchange picture. -/
def Coherent [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x) : Prop :=
  E.source = E.nextLeft

/-- A noncoherent active first error is a genuine alternating exchange step. -/
def Noncoherent [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x) : Prop :=
  E.source ≠ E.nextLeft

theorem coherent_or_noncoherent [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x) :
    E.Coherent ∨ E.Noncoherent := by
  exact eq_or_ne E.source E.nextLeft

/-- In the coherent case, the active target is exactly the matched mate of the
active source. -/
theorem target_eq_toEquiv_source_of_coherent [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x)
    (h : E.Coherent) :
    E.target = m.toIsoData.toEquiv E.source := by
  rw [Coherent] at h
  rw [h]
  exact E.toEquiv_nextLeft.symm

/-- The active first-error source is genuinely different from the deleted base
of the card where it was found. -/
theorem source_ne_base [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x) :
    E.source ≠ x := by
  intro h
  exact E.error.z.2 (by simpa [source] using congrArg Subtype.val h)

/-- The active first-error target is genuinely different from the deleted
right-hand base of the card where it was found. -/
theorem target_ne_baseTarget [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x) :
    E.target ≠ m.toIsoData.toEquiv x := by
  intro h
  exact E.error.imageZ_ne_deleted
    (by simpa [target] using congrArg Subtype.val h)

/-- The successor of an active first error is also different from the deleted
base where the error was found. -/
theorem nextLeft_ne_base [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x) :
    E.nextLeft ≠ x := by
  intro h
  exact E.target_ne_baseTarget (by simpa [h] using E.toEquiv_nextLeft.symm)

/-- Following an active first error carries a concrete two-hole transport from
the old edge to the recentered active pair. -/
def recenteredTwoHoleIso [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x) :
    TwoColorIso (deleteTwo K x.1 E.source.1)
      (deleteTwo K (m.toIsoData.toEquiv x).1 E.target.1)
      (deleteTwoColor S x.1 E.source.1)
      (deleteTwoColor (singletonLeft T a) x.1 E.source.1)
      (deleteTwoColor S (m.toIsoData.toEquiv x).1 E.target.1)
      (deleteTwoColor (singletonRight T b)
        (m.toIsoData.toEquiv x).1 E.target.1) := by
  simpa [source, target, LowSliceCardFirstError.imageZ] using E.error.twoHoleIso

/-- In the coherent case, the recentered two-hole transport deletes a matched
active pair on the right. -/
def coherentTwoHoleIso [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : ActiveFirstError m x)
    (h : E.Coherent) :
    TwoColorIso (deleteTwo K x.1 E.source.1)
      (deleteTwo K (m.toIsoData.toEquiv x).1
        (m.toIsoData.toEquiv E.source).1)
      (deleteTwoColor S x.1 E.source.1)
      (deleteTwoColor (singletonLeft T a) x.1 E.source.1)
      (deleteTwoColor S (m.toIsoData.toEquiv x).1
        (m.toIsoData.toEquiv E.source).1)
      (deleteTwoColor (singletonRight T b)
        (m.toIsoData.toEquiv x).1
        (m.toIsoData.toEquiv E.source).1) := by
  have htarget := E.target_eq_toEquiv_source_of_coherent h
  rw [← htarget]
  exact E.recenteredTwoHoleIso

end ActiveFirstError

namespace InactiveFirstError

/-- The complementary-side source vertex reached by following an inactive first
error. -/
def source [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) :
    complementaryDeleteLeft T a b := by
  refine ⟨E.error.z.1, ?_⟩
  have hnot : E.error.z.1 ∉ T ∪ {a} := E.inactive
  have hT : E.error.z.1 ∉ T := fun h => hnot (Or.inl h)
  have ha : E.error.z.1 ≠ a := fun h => hnot (Or.inr h)
  by_cases hb : E.error.z.1 = b
  · exact Or.inr hb
  · exact Or.inl ⟨hT, ha, hb⟩

/-- The complementary-side target vertex reached by following an inactive first
error. -/
def target [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) :
    complementaryDeleteRight T a b := by
  refine ⟨E.error.imageZ, ?_⟩
  have hnot : E.error.imageZ ∉ T ∪ {b} :=
    E.error.sourceInactive_iff_targetInactive.mp E.inactive
  have hT : E.error.imageZ ∉ T := fun h => hnot (Or.inl h)
  have hb : E.error.imageZ ≠ b := fun h => hnot (Or.inr h)
  by_cases ha : E.error.imageZ = a
  · exact Or.inr ha
  · exact Or.inl ⟨hT, ha, hb⟩

/-- Following an inactive first error carries a concrete two-hole transport from
the old active edge to a complementary-side recentering. -/
def recenteredTwoHoleIso [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) :
    TwoColorIso (deleteTwo K x.1 E.source.1)
      (deleteTwo K (m.toIsoData.toEquiv x).1 E.target.1)
      (deleteTwoColor S x.1 E.source.1)
      (deleteTwoColor (singletonLeft T a) x.1 E.source.1)
      (deleteTwoColor S (m.toIsoData.toEquiv x).1 E.target.1)
      (deleteTwoColor (singletonRight T b)
        (m.toIsoData.toEquiv x).1 E.target.1) := by
  simpa [source, target, LowSliceCardFirstError.imageZ] using E.error.twoHoleIso

/-- The inactive source lies in the outside core `O`. -/
def SourceOutsideCore [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) : Prop :=
  E.source.1 ∉ T ∧ E.source.1 ≠ a ∧ E.source.1 ≠ b

/-- The inactive source is the opposite endpoint `b`. -/
def SourceAtB [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) : Prop :=
  E.source.1 = b

/-- The inactive target lies in the outside core `O`. -/
def TargetOutsideCore [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) : Prop :=
  E.target.1 ∉ T ∧ E.target.1 ≠ a ∧ E.target.1 ≠ b

/-- The inactive target is the opposite endpoint `a`. -/
def TargetAtA [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) : Prop :=
  E.target.1 = a

theorem source_outside_or_atB [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) :
    E.SourceOutsideCore ∨ E.SourceAtB := by
  have hnot : E.error.z.1 ∉ T ∪ {a} := E.inactive
  have hT : E.error.z.1 ∉ T := fun h => hnot (Or.inl h)
  have ha : E.error.z.1 ≠ a := fun h => hnot (Or.inr h)
  by_cases hb : E.error.z.1 = b
  · right
    simp [SourceAtB, source, hb]
  · left
    simp [SourceOutsideCore, source, hT, ha, hb]

theorem target_outside_or_atA [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) :
    E.TargetOutsideCore ∨ E.TargetAtA := by
  have hnot : E.error.imageZ ∉ T ∪ {b} :=
    E.error.sourceInactive_iff_targetInactive.mp E.inactive
  have hT : E.error.imageZ ∉ T := fun h => hnot (Or.inl h)
  have hb : E.error.imageZ ≠ b := fun h => hnot (Or.inr h)
  by_cases ha : E.error.imageZ = a
  · right
    simp [TargetAtA, target, ha]
  · left
    simp [TargetOutsideCore, target, hT, ha, hb]

/-- An inactive first error exposes one of the opposite endpoints. -/
def EndpointExposing [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) : Prop :=
  E.SourceAtB ∨ E.TargetAtA

/-- An inactive first error stays entirely in the outside core. -/
def OuterResidual [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) : Prop :=
  E.SourceOutsideCore ∧ E.TargetOutsideCore

theorem endpointExposing_or_outerResidual [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) :
    E.EndpointExposing ∨ E.OuterResidual := by
  rcases E.source_outside_or_atB with hs | hb
  · rcases E.target_outside_or_atA with ht | ha
    · exact Or.inr ⟨hs, ht⟩
    · exact Or.inl (Or.inr ha)
  · exact Or.inl (Or.inl hb)

/-- A purely outer inactive residual does not expose either endpoint. -/
theorem outerResidual_not_endpointExposing [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x)
    (h : E.OuterResidual) :
    ¬ E.EndpointExposing := by
  intro hend
  rcases h with ⟨hsource, htarget⟩
  rcases hend with hb | ha
  · exact hsource.2.2 hb
  · exact htarget.2.1 ha

/-- Inactive first errors not seen at the endpoints are exactly outer residuals. -/
theorem not_endpointExposing_iff_outerResidual [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {m : LowSliceMinimumErrorMatching K S T a b}
    {x : singletonLeft T a} (E : InactiveFirstError m x) :
    ¬ E.EndpointExposing ↔ E.OuterResidual := by
  constructor
  · intro hnot
    rcases E.endpointExposing_or_outerResidual with hend | houter
    · exact False.elim (hnot hend)
    · exact houter
  · exact E.outerResidual_not_endpointExposing

end InactiveFirstError

/-- A minimum-error matching has total error zero whenever an active zero-star
pair exists. -/
theorem totalStarErrorCount_eq_zero_of_pair [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceMinimumErrorMatching K S T a b)
    (hpair : LowSliceZeroStarPair K S T a b) :
    m.toIsoData.totalStarErrorCount = 0 := by
  let zsm := LowSliceZeroStarMatching.of_solved hpair.solved
  let e0 := LowSliceIsoData.ofZeroStarMatching zsm
  have hzero : e0.totalStarErrorCount = 0 :=
    LowSliceIsoData.totalStarErrorCount_ofZeroStarMatching zsm
  have hle := m.minimum e0
  rw [hzero] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- For a minimum-error matching, total error zero is equivalent to the active
zero-star pair target. -/
theorem totalStarErrorCount_eq_zero_iff_pair [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceMinimumErrorMatching K S T a b) :
    m.toIsoData.totalStarErrorCount = 0 ↔ LowSliceZeroStarPair K S T a b := by
  constructor
  · intro hzero
    exact (m.toIsoData.toZeroStarMatchingOfTotalErrorZero hzero).to_pair
  · exact m.totalStarErrorCount_eq_zero_of_pair

/-- For a minimum-error matching, positive total error is exactly the no-pair
obstruction. -/
theorem totalStarErrorCount_pos_iff_no_pair [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceMinimumErrorMatching K S T a b) :
    0 < m.toIsoData.totalStarErrorCount ↔ ¬ LowSliceZeroStarPair K S T a b := by
  rw [← m.totalStarErrorCount_eq_zero_iff_pair, Nat.pos_iff_ne_zero]

/-- For a minimum-error matching, having no zero-star edge is exactly the local
no-pair obstruction. -/
theorem noZeroStarEdge_iff_no_pair [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceMinimumErrorMatching K S T a b) :
    m.toIsoData.NoZeroStarEdge ↔ ¬ LowSliceZeroStarPair K S T a b := by
  constructor
  · intro hnoEdge hpair
    have htotal := m.totalStarErrorCount_eq_zero_of_pair hpair
    have hall := m.toIsoData.totalStarErrorCount_eq_zero_iff.mp htotal
    let x : singletonLeft T a := ⟨a, by simp [singletonLeft]⟩
    exact (hnoEdge x) (hall x)
  · intro hno x hzero
    exact hno
      ⟨x, m.toIsoData.toEquiv x, m.toIsoData.cardIso x,
        m.toIsoData.first_status x, hzero⟩

/-- Under the no-pair obstruction, every edge of a minimum-error matching has a
packaged first-error witness. -/
theorem firstError_of_no_pair [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceMinimumErrorMatching K S T a b)
    (hno : ¬ LowSliceZeroStarPair K S T a b)
    (x : singletonLeft T a) :
    Nonempty
      (LowSliceCardFirstError K S T a b x
        (m.toIsoData.toEquiv x) (m.toIsoData.cardIso x)) :=
  m.toIsoData.firstError_of_no_pair hno x

/-- Every first-error witness above a minimum-error no-pair obstruction is in
one of the two color-compatible branches: active-active or inactive-inactive. -/
theorem firstError_active_or_inactive_of_no_pair [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (m : LowSliceMinimumErrorMatching K S T a b)
    (hno : ¬ LowSliceZeroStarPair K S T a b)
    (x : singletonLeft T a) :
    Nonempty (ActiveFirstError m x) ∨ Nonempty (InactiveFirstError m x) := by
  rcases m.firstError_of_no_pair hno x with ⟨E⟩
  rcases E.active_or_inactive_source with hE | hE
  · exact Or.inl ⟨⟨E, hE⟩⟩
  · exact Or.inr ⟨⟨E, hE⟩⟩

end LowSliceMinimumErrorMatching

/-- The strengthened minimum-error route: every low-slice equality has a
minimum-error matching of total star error zero. -/
def LowSliceMinimumErrorZeroConjecture [Finite V]
    (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  LowSliceSameDeck K S T a b →
    ∃ m : LowSliceMinimumErrorMatching K S T a b,
      m.toIsoData.totalStarErrorCount = 0

/-- A fully packaged positive minimum-error obstruction to the current route. -/
structure LowSlicePositiveMinimumObstruction
    (K : SimpleGraph V) (S T : Set V) (a b : V) [Finite V] where
  low : LowSliceSameDeck K S T a b
  min : LowSliceMinimumErrorMatching K S T a b
  positive : 0 < min.toIsoData.totalStarErrorCount

/-- The exact no-positive-obstruction form of the minimum-error route. -/
def NoLowSlicePositiveMinimumObstruction [Finite V]
    (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  ¬ Nonempty (LowSlicePositiveMinimumObstruction K S T a b)

/-- The minimum-error-zero route implies the active zero-star-pair conjecture. -/
theorem LowSliceZeroStarPairConjecture.of_minimumErrorZero
    [Finite V] {K : SimpleGraph V} {S T : Set V} {a b : V}
    (h : LowSliceMinimumErrorZeroConjecture K S T a b) :
    LowSliceZeroStarPairConjecture K S T a b := by
  intro hlow
  rcases h hlow with ⟨m, hzero⟩
  exact m.totalStarErrorCount_eq_zero_iff_pair.mp hzero

/-- The minimum-error-zero formulation is equivalent to the active zero-star
pair formulation. -/
theorem LowSliceMinimumErrorZeroConjecture.iff_zeroStarPairConjecture
    [Finite V] {K : SimpleGraph V} {S T : Set V} {a b : V} :
    LowSliceMinimumErrorZeroConjecture K S T a b ↔
      LowSliceZeroStarPairConjecture K S T a b := by
  constructor
  · exact LowSliceZeroStarPairConjecture.of_minimumErrorZero
  · intro h hlow
    rcases LowSliceMinimumErrorMatching.exists_of_sameDeck hlow with ⟨m⟩
    exact ⟨m, m.totalStarErrorCount_eq_zero_iff_pair.mpr (h hlow)⟩

/-- Failing the minimum-error-zero route is equivalent to exhibiting a positive
minimum-error obstruction. -/
theorem LowSlicePositiveMinimumObstruction.nonempty_iff_not_minimumErrorZero
    [Finite V] {K : SimpleGraph V} {S T : Set V} {a b : V} :
    Nonempty (LowSlicePositiveMinimumObstruction K S T a b) ↔
      ¬ LowSliceMinimumErrorZeroConjecture K S T a b := by
  constructor
  · rintro ⟨o⟩ hzero
    rcases hzero o.low with ⟨m0, hm0⟩
    have hle := o.min.minimum m0.toIsoData
    rw [hm0] at hle
    exact (not_lt_of_ge hle) o.positive
  · intro hnot
    classical
    by_contra hnone
    apply hnot
    intro hlow
    rcases LowSliceMinimumErrorMatching.exists_of_sameDeck hlow with ⟨m⟩
    by_cases hm : m.toIsoData.totalStarErrorCount = 0
    · exact ⟨m, hm⟩
    · exfalso
      apply hnone
      exact ⟨
        { low := hlow
          min := m
          positive := Nat.pos_of_ne_zero hm }⟩

/-- Ruling out positive minimum-error obstructions is exactly the
minimum-error-zero route. -/
theorem NoLowSlicePositiveMinimumObstruction.iff_minimumErrorZero
    [Finite V] {K : SimpleGraph V} {S T : Set V} {a b : V} :
    NoLowSlicePositiveMinimumObstruction K S T a b ↔
      LowSliceMinimumErrorZeroConjecture K S T a b := by
  classical
  constructor
  · intro hnone
    by_contra hnot
    exact hnone
      (LowSlicePositiveMinimumObstruction.nonempty_iff_not_minimumErrorZero.mpr
        hnot)
  · intro hzero hobs
    exact
      (LowSlicePositiveMinimumObstruction.nonempty_iff_not_minimumErrorZero.mp
        hobs) hzero

namespace LowSlicePositiveMinimumObstruction

/-- A positive minimum-error obstruction has no active zero-star pair. -/
theorem no_pair [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b) :
    ¬ LowSliceZeroStarPair K S T a b :=
  o.min.totalStarErrorCount_pos_iff_no_pair.mp o.positive

/-- A positive minimum-error obstruction has no zero-star edge in its chosen
minimum matching. -/
theorem noZeroStarEdge [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b) :
    o.min.toIsoData.NoZeroStarEdge :=
  o.min.noZeroStarEdge_iff_no_pair.mpr o.no_pair

/-- Every edge of a positive minimum-error obstruction splits into the active or
inactive first-error branch. -/
theorem firstError_active_or_inactive [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b)
    (x : singletonLeft T a) :
    Nonempty (LowSliceMinimumErrorMatching.ActiveFirstError o.min x) ∨
      Nonempty (LowSliceMinimumErrorMatching.InactiveFirstError o.min x) :=
  o.min.firstError_active_or_inactive_of_no_pair o.no_pair x

/-- The active branch is available above the matched edge `x`. -/
def HasActiveBranch [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b)
    (x : singletonLeft T a) : Prop :=
  Nonempty (LowSliceMinimumErrorMatching.ActiveFirstError o.min x)

/-- The inactive branch is available above the matched edge `x`. -/
def HasInactiveBranch [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b)
    (x : singletonLeft T a) : Prop :=
  Nonempty (LowSliceMinimumErrorMatching.InactiveFirstError o.min x)

theorem hasActive_or_hasInactive [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b)
    (x : singletonLeft T a) :
    o.HasActiveBranch x ∨ o.HasInactiveBranch x :=
  o.firstError_active_or_inactive x

/-- All matched edges admit an active first-error branch. -/
def AllActiveBranches [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b) : Prop :=
  ∀ x : singletonLeft T a, o.HasActiveBranch x

/-- All matched edges admit an inactive first-error branch. -/
def AllInactiveBranches [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b) : Prop :=
  ∀ x : singletonLeft T a, o.HasInactiveBranch x

/-- A positive obstruction has both active and inactive first-error branches
somewhere in the chosen minimum matching. -/
def HasMixedBranches [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b) : Prop :=
  (∃ x : singletonLeft T a, o.HasActiveBranch x) ∧
    ∃ x : singletonLeft T a, o.HasInactiveBranch x

/-- If a positive obstruction is not active everywhere, it has an inactive
branch somewhere. -/
theorem exists_inactiveBranch_of_not_allActive [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b)
    (hnot : ¬ o.AllActiveBranches) :
    ∃ x : singletonLeft T a, o.HasInactiveBranch x := by
  classical
  by_contra hnone
  apply hnot
  intro x
  rcases o.hasActive_or_hasInactive x with hactive | hinactive
  · exact hactive
  · exact False.elim (hnone ⟨x, hinactive⟩)

/-- If a positive obstruction is not inactive everywhere, it has an active
branch somewhere. -/
theorem exists_activeBranch_of_not_allInactive [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b)
    (hnot : ¬ o.AllInactiveBranches) :
    ∃ x : singletonLeft T a, o.HasActiveBranch x := by
  classical
  by_contra hnone
  apply hnot
  intro x
  rcases o.hasActive_or_hasInactive x with hactive | hinactive
  · exact False.elim (hnone ⟨x, hactive⟩)
  · exact hinactive

/-- Every positive minimum-error obstruction is all-active, all-inactive, or
genuinely mixed. -/
theorem branch_trichotomy [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b) :
    o.AllActiveBranches ∨ o.AllInactiveBranches ∨ o.HasMixedBranches := by
  classical
  by_cases hactive : o.AllActiveBranches
  · exact Or.inl hactive
  · right
    by_cases hinactive : o.AllInactiveBranches
    · exact Or.inl hinactive
    · exact Or.inr
        ⟨o.exists_activeBranch_of_not_allInactive hinactive,
          o.exists_inactiveBranch_of_not_allActive hactive⟩

/-- A packaged active exchange step inside a positive minimum-error obstruction. -/
structure ActiveTransportStep [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b) where
  base : singletonLeft T a
  witness : LowSliceMinimumErrorMatching.ActiveFirstError o.min base

/-- A chosen active first-error witness over every matched edge of a positive
minimum-error obstruction. -/
structure ActiveObserverSystem [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b) where
  witness : ∀ x : singletonLeft T a,
    LowSliceMinimumErrorMatching.ActiveFirstError o.min x

namespace ActiveObserverSystem

/-- Choose an active observer system from the proposition that every edge has an
active branch. -/
noncomputable def ofAllActiveBranches [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (h : o.AllActiveBranches) : ActiveObserverSystem o where
  witness x := Classical.choice (h x)

/-- The active transport step selected at `x`. -/
def step [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) :
    ActiveTransportStep o :=
  { base := x
    witness := B.witness x }

/-- The defect source selected at `x`. -/
def source [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) :
    singletonLeft T a :=
  (B.witness x).source

/-- The observer successor selected at `x`. -/
def next [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) :
    singletonLeft T a :=
  (B.witness x).nextLeft

/-- The self-map on active vertices obtained by following selected observer
successors. -/
def observerMap [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) : singletonLeft T a → singletonLeft T a :=
  fun x => B.next x

@[simp] theorem observerMap_apply [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) :
    B.observerMap x = B.next x :=
  rfl

/-- A selected active source is never the deleted base where it is observed. -/
theorem source_ne_self [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) :
    B.source x ≠ x :=
  (B.witness x).source_ne_base

/-- The selected observer successor is never the same as the deleted base. -/
theorem next_ne_self [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) :
    B.next x ≠ x :=
  (B.witness x).nextLeft_ne_base

/-- The selected observer map has no fixed point. -/
theorem observerMap_ne_self [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) :
    B.observerMap x ≠ x :=
  B.next_ne_self x

/-- The selected active witness at `x` is coherent. -/
def CoherentAt [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) : Prop :=
  (B.witness x).Coherent

/-- The selected active witness at `x` is noncoherent. -/
def NoncoherentAt [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) : Prop :=
  (B.witness x).Noncoherent

theorem coherentAt_or_noncoherentAt [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) :
    B.CoherentAt x ∨ B.NoncoherentAt x :=
  (B.witness x).coherent_or_noncoherent

/-- At a coherent selected active witness, the defect source is the observer
successor. -/
theorem source_eq_next_of_coherentAt [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) {x : singletonLeft T a}
    (h : B.CoherentAt x) :
    B.source x = B.next x := by
  simpa [CoherentAt, source, next,
    LowSliceMinimumErrorMatching.ActiveFirstError.Coherent] using h

/-- A coherent selected active witness is a matched two-hole transport from the
base to its observer successor. -/
def coherentMatchedTwoHoleIsoAt [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a)
    (h : B.CoherentAt x) :
    TwoColorIso (deleteTwo K x.1 (B.next x).1)
      (deleteTwo K (o.min.toIsoData.toEquiv x).1
        (o.min.toIsoData.toEquiv (B.next x)).1)
      (deleteTwoColor S x.1 (B.next x).1)
      (deleteTwoColor (singletonLeft T a) x.1 (B.next x).1)
      (deleteTwoColor S (o.min.toIsoData.toEquiv x).1
        (o.min.toIsoData.toEquiv (B.next x)).1)
      (deleteTwoColor (singletonRight T b)
        (o.min.toIsoData.toEquiv x).1
        (o.min.toIsoData.toEquiv (B.next x)).1) := by
  have hs :
      (B.witness x).source = (B.witness x).nextLeft := by
    simpa [CoherentAt,
      LowSliceMinimumErrorMatching.ActiveFirstError.Coherent] using h
  have hIso := (B.witness x).coherentTwoHoleIso h
  rw [hs] at hIso
  simpa [next] using hIso

/-- A selected observer cycle for an active observer system. -/
def HasObserverCycle [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) : Prop :=
  ∃ x : singletonLeft T a, ∃ n : ℕ,
    1 < n ∧ B.observerMap^[n] x = x

/-- Any chosen active observer system has a nontrivial finite observer cycle. -/
theorem exists_observerCycle [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) :
    B.HasObserverCycle := by
  classical
  letI : Nonempty (singletonLeft T a) :=
    ⟨⟨a, by simp [singletonLeft]⟩⟩
  rcases exists_positive_iterate_eq_self_of_finite B.observerMap with
    ⟨x, n, hpos, hcycle⟩
  have hn_ne_one : n ≠ 1 := by
    intro hn
    subst n
    exact B.observerMap_ne_self x (by simpa using hcycle)
  exact ⟨x, n, lt_of_le_of_ne (Nat.succ_le_of_lt hpos) hn_ne_one.symm,
    hcycle⟩

end ActiveObserverSystem

/-- If every edge of a positive obstruction has an active branch, then one can
choose active first errors so as to get a nontrivial observer cycle. -/
theorem exists_activeObserverCycle_of_allActiveBranches [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (h : o.AllActiveBranches) :
    ∃ B : ActiveObserverSystem o, B.HasObserverCycle := by
  classical
  let B := ActiveObserverSystem.ofAllActiveBranches h
  exact ⟨B, B.exists_observerCycle⟩

/-- A chosen inactive first-error witness over every matched edge of a positive
minimum-error obstruction. -/
structure InactiveObserverSystem [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b) where
  witness : ∀ x : singletonLeft T a,
    LowSliceMinimumErrorMatching.InactiveFirstError o.min x

namespace InactiveObserverSystem

/-- Choose an inactive observer system from the proposition that every edge has
an inactive branch. -/
noncomputable def ofAllInactiveBranches [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (h : o.AllInactiveBranches) : InactiveObserverSystem o where
  witness x := Classical.choice (h x)

/-- The selected inactive source at `x`. -/
def source [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : InactiveObserverSystem o) (x : singletonLeft T a) :
    complementaryDeleteLeft T a b :=
  (B.witness x).source

/-- The selected inactive target at `x`. -/
def target [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : InactiveObserverSystem o) (x : singletonLeft T a) :
    complementaryDeleteRight T a b :=
  (B.witness x).target

/-- The selected inactive witness at `x` exposes an endpoint. -/
def EndpointExposingAt [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : InactiveObserverSystem o) (x : singletonLeft T a) : Prop :=
  (B.witness x).EndpointExposing

/-- The selected inactive witness at `x` remains in the outside core. -/
def OuterResidualAt [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : InactiveObserverSystem o) (x : singletonLeft T a) : Prop :=
  (B.witness x).OuterResidual

theorem endpointExposingAt_or_outerResidualAt [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : InactiveObserverSystem o) (x : singletonLeft T a) :
    B.EndpointExposingAt x ∨ B.OuterResidualAt x :=
  (B.witness x).endpointExposing_or_outerResidual

/-- Every selected inactive witness exposes an endpoint. -/
def AllEndpointExposing [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : InactiveObserverSystem o) : Prop :=
  ∀ x : singletonLeft T a, B.EndpointExposingAt x

/-- Some selected inactive witness remains entirely in the outside core. -/
def HasOuterResidual [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : InactiveObserverSystem o) : Prop :=
  ∃ x : singletonLeft T a, B.OuterResidualAt x

/-- A chosen all-inactive system is either endpoint-exposing everywhere or has
an explicit outer residual. -/
theorem allEndpointExposing_or_hasOuterResidual [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : InactiveObserverSystem o) :
    B.AllEndpointExposing ∨ B.HasOuterResidual := by
  classical
  by_cases hall : B.AllEndpointExposing
  · exact Or.inl hall
  · right
    by_contra hnone
    apply hall
    intro x
    rcases B.endpointExposingAt_or_outerResidualAt x with hend | houter
    · exact hend
    · exact False.elim (hnone ⟨x, houter⟩)

end InactiveObserverSystem

/-- If every edge of a positive obstruction has an inactive branch, then one can
choose inactive first errors and split them into endpoint and outer cases. -/
theorem exists_inactiveObserverSystem_of_allInactiveBranches [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (h : o.AllInactiveBranches) :
    ∃ B : InactiveObserverSystem o,
      B.AllEndpointExposing ∨ B.HasOuterResidual := by
  classical
  let B := InactiveObserverSystem.ofAllInactiveBranches h
  exact ⟨B, B.allEndpointExposing_or_hasOuterResidual⟩

/-- The current strategic fork for any positive minimum-error obstruction:
active observer cycle, all-inactive endpoint/outer split, or mixed branches. -/
theorem strategy_fork [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b) :
    (∃ B : ActiveObserverSystem o, B.HasObserverCycle) ∨
      (∃ B : InactiveObserverSystem o,
        B.AllEndpointExposing ∨ B.HasOuterResidual) ∨
      o.HasMixedBranches := by
  rcases o.branch_trichotomy with hactive | hinactive | hmixed
  · exact Or.inl (exists_activeObserverCycle_of_allActiveBranches hactive)
  · exact Or.inr (Or.inl
      (exists_inactiveObserverSystem_of_allInactiveBranches hinactive))
  · exact Or.inr (Or.inr hmixed)

/-- The active-cycle fork is impossible. -/
def NoActiveObserverCycleFork [Finite V]
    (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  ∀ o : LowSlicePositiveMinimumObstruction K S T a b,
    ¬ ∃ B : ActiveObserverSystem o, B.HasObserverCycle

/-- The all-inactive endpoint/outer fork is impossible. -/
def NoInactiveEndpointOuterFork [Finite V]
    (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  ∀ o : LowSlicePositiveMinimumObstruction K S T a b,
    ¬ ∃ B : InactiveObserverSystem o,
      B.AllEndpointExposing ∨ B.HasOuterResidual

/-- The genuinely mixed active/inactive branch fork is impossible. -/
def NoMixedBranchFork [Finite V]
    (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  ∀ o : LowSlicePositiveMinimumObstruction K S T a b,
    ¬ o.HasMixedBranches

/-- Ruling out the three concrete strategy forks rules out every positive
minimum-error obstruction. -/
theorem NoLowSlicePositiveMinimumObstruction.of_no_strategy_forks [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (hactive : NoActiveObserverCycleFork K S T a b)
    (hinactive : NoInactiveEndpointOuterFork K S T a b)
    (hmixed : NoMixedBranchFork K S T a b) :
    NoLowSlicePositiveMinimumObstruction K S T a b := by
  rintro ⟨o⟩
  rcases o.strategy_fork with hA | hI | hM
  · exact hactive o hA
  · exact hinactive o hI
  · exact hmixed o hM

namespace ActiveTransportStep

/-- The source of a packaged active exchange step. -/
def source [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) : singletonLeft T a :=
  A.witness.source

/-- The target of a packaged active exchange step. -/
def target [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) : singletonRight T b :=
  A.witness.target

/-- The next base vertex obtained by pulling the target back through the chosen
minimum matching. -/
def nextBase [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) : singletonLeft T a :=
  A.witness.nextLeft

@[simp] theorem toEquiv_nextBase [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) :
    o.min.toIsoData.toEquiv A.nextBase = A.target := by
  simp [nextBase, target]

/-- A coherent packaged active step is a side-cycle step. -/
def Coherent [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) : Prop :=
  A.witness.Coherent

/-- A noncoherent packaged active step is a genuine alternating exchange step. -/
def Noncoherent [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) : Prop :=
  A.witness.Noncoherent

theorem coherent_or_noncoherent [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) :
    A.Coherent ∨ A.Noncoherent :=
  A.witness.coherent_or_noncoherent

theorem coherent_iff_source_eq_nextBase [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) :
    A.Coherent ↔ A.source = A.nextBase := by
  rfl

/-- A packaged active step is noncoherent exactly when its source and successor
are distinct. -/
theorem noncoherent_iff_source_ne_nextBase [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) :
    A.Noncoherent ↔ A.source ≠ A.nextBase := by
  rfl

/-- The source of an active exchange step is not its base card. -/
theorem source_ne_base [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) :
    A.source ≠ A.base :=
  A.witness.source_ne_base

/-- The successor of an active exchange step is not its base card. -/
theorem nextBase_ne_base [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) :
    A.nextBase ≠ A.base :=
  A.witness.nextLeft_ne_base

/-- A noncoherent active step is a three-distinct-vertex configuration. -/
theorem three_distinct_of_noncoherent [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) (hA : A.Noncoherent) :
    A.source ≠ A.base ∧ A.nextBase ≠ A.base ∧ A.source ≠ A.nextBase :=
  ⟨A.source_ne_base, A.nextBase_ne_base,
    A.noncoherent_iff_source_ne_nextBase.mp hA⟩

end ActiveTransportStep

/-- The directed active exchange relation carried by active first-error steps.
An edge points from the defect source to the left vertex matched to its target. -/
def ActiveExchangeRel [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b)
    (u v : singletonLeft T a) : Prop :=
  ∃ A : ActiveTransportStep o, A.source = u ∧ A.nextBase = v

/-- The observer-successor relation carried by active first-error steps.  This
edge points from the deleted base card to the left vertex matched to the
first-error target. -/
def ActiveObserverRel [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b)
    (u v : singletonLeft T a) : Prop :=
  ∃ A : ActiveTransportStep o, A.base = u ∧ A.nextBase = v

/-- The noncoherent part of the active exchange relation.  These are the
candidate descent or correction-cycle edges. -/
def ActiveNoncoherentRel [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b)
    (u v : singletonLeft T a) : Prop :=
  ∃ A : ActiveTransportStep o,
    A.source = u ∧ A.nextBase = v ∧ A.Noncoherent

theorem activeExchangeRel_of_step [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) :
    o.ActiveExchangeRel A.source A.nextBase :=
  ⟨A, rfl, rfl⟩

theorem activeObserverRel_of_step [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) :
    o.ActiveObserverRel A.base A.nextBase :=
  ⟨A, rfl, rfl⟩

theorem activeNoncoherentRel_of_step [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (A : ActiveTransportStep o) (hA : A.Noncoherent) :
    o.ActiveNoncoherentRel A.source A.nextBase :=
  ⟨A, rfl, rfl, hA⟩

/-- The noncoherent active exchange relation has no loops. -/
theorem not_activeNoncoherentRel_self [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b)
    (u : singletonLeft T a) :
    ¬ o.ActiveNoncoherentRel u u := by
  rintro ⟨A, hsource, hnext, hA⟩
  have hne := A.noncoherent_iff_source_ne_nextBase.mp hA
  apply hne
  rw [hsource, hnext]

/-- Every noncoherent active exchange edge connects distinct active vertices. -/
theorem activeNoncoherentRel_ne [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    {u v : singletonLeft T a}
    (h : o.ActiveNoncoherentRel u v) :
    u ≠ v := by
  intro huv
  subst huv
  exact o.not_activeNoncoherentRel_self u h

/-- A selected noncoherent active witness gives a noncoherent correction edge. -/
theorem activeNoncoherentRel_of_noncoherentAt [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a)
    (h : B.NoncoherentAt x) :
    o.ActiveNoncoherentRel (B.source x) (B.observerMap x) := by
  simpa [ActiveObserverSystem.step, ActiveObserverSystem.source,
    ActiveObserverSystem.observerMap, ActiveObserverSystem.next,
    ActiveTransportStep.source, ActiveTransportStep.nextBase,
    ActiveTransportStep.Noncoherent] using
    activeNoncoherentRel_of_step (B.step x) h

/-- Observer-successor active edges also have no loops. -/
theorem not_activeObserverRel_self [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b)
    (u : singletonLeft T a) :
    ¬ o.ActiveObserverRel u u := by
  rintro ⟨A, hbase, hnext⟩
  have hne := A.nextBase_ne_base
  apply hne
  exact hnext.trans hbase.symm

/-- Every observer-successor active edge connects distinct active vertices. -/
theorem activeObserverRel_ne [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    {u v : singletonLeft T a}
    (h : o.ActiveObserverRel u v) :
    u ≠ v := by
  intro huv
  subst huv
  exact o.not_activeObserverRel_self u h

/-- A selected active observer system gives an observer edge from every base to
its selected successor. -/
theorem activeObserverRel_observerMap [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) :
    o.ActiveObserverRel x (B.observerMap x) := by
  simpa [ActiveObserverSystem.step, ActiveObserverSystem.observerMap,
    ActiveObserverSystem.next, ActiveTransportStep.nextBase] using
    activeObserverRel_of_step (B.step x)

/-- Consecutive vertices along the selected active observer orbit form observer
relation edges. -/
theorem activeObserverRel_iterate [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (B : ActiveObserverSystem o) (x : singletonLeft T a) (n : ℕ) :
    o.ActiveObserverRel (B.observerMap^[n] x)
      (B.observerMap^[n + 1] x) := by
  have h := activeObserverRel_observerMap B (B.observerMap^[n] x)
  have hnext :
      B.observerMap^[n + 1] x =
        B.observerMap (B.observerMap^[n] x) := by
    rw [Nat.add_comm n 1]
    simpa using Function.iterate_add_apply B.observerMap 1 n x
  rw [hnext]
  exact h

/-- A packaged nontrivial cycle in a selected active observer system. -/
structure ActiveObserverCycle [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (o : LowSlicePositiveMinimumObstruction K S T a b) where
  system : ActiveObserverSystem o
  base : singletonLeft T a
  period : ℕ
  period_gt_one : 1 < period
  closes : system.observerMap^[period] base = base

namespace ActiveObserverCycle

/-- The selected witness at index `n` of the cycle is coherent. -/
def CoherentAtIndex [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) (n : ℕ) : Prop :=
  C.system.CoherentAt (C.system.observerMap^[n] C.base)

/-- The selected witness at index `n` of the cycle is noncoherent. -/
def NoncoherentAtIndex [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) (n : ℕ) : Prop :=
  C.system.NoncoherentAt (C.system.observerMap^[n] C.base)

theorem coherent_or_noncoherent_at_index [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) (n : ℕ) :
    C.CoherentAtIndex n ∨ C.NoncoherentAtIndex n :=
  C.system.coherentAt_or_noncoherentAt _

/-- Every selected witness on the active observer cycle is coherent. -/
def AllCoherent [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) : Prop :=
  ∀ n : ℕ, C.CoherentAtIndex n

/-- Some selected witness on the active observer cycle is noncoherent. -/
def HasNoncoherent [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) : Prop :=
  ∃ n : ℕ, C.NoncoherentAtIndex n

theorem allCoherent_or_hasNoncoherent [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) :
    C.AllCoherent ∨ C.HasNoncoherent := by
  classical
  by_cases hall : C.AllCoherent
  · exact Or.inl hall
  · right
    by_contra hnone
    apply hall
    intro n
    rcases C.coherent_or_noncoherent_at_index n with hcoh | hnon
    · exact hcoh
    · exact False.elim (hnone ⟨n, hnon⟩)

/-- Consecutive vertices on an active observer cycle are observer-relation edges. -/
theorem edge_at [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) (n : ℕ) :
    o.ActiveObserverRel (C.system.observerMap^[n] C.base)
      (C.system.observerMap^[n + 1] C.base) :=
  activeObserverRel_iterate C.system C.base n

/-- The last edge of the cycle returns to the base after using the closing
equation. -/
theorem last_edge_to_base [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) :
    o.ActiveObserverRel (C.system.observerMap^[C.period - 1] C.base) C.base := by
  have h := C.edge_at (C.period - 1)
  have hsucc : C.period - 1 + 1 = C.period :=
    Nat.sub_add_cancel C.period_gt_one.le
  simpa [hsucc, C.closes] using h

/-- A noncoherent index on the observer cycle gives a noncoherent correction
edge from the defect source to the next observer vertex. -/
theorem noncoherentCorrectionEdge_at [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) {n : ℕ}
    (h : C.NoncoherentAtIndex n) :
    o.ActiveNoncoherentRel
      (C.system.source (C.system.observerMap^[n] C.base))
      (C.system.observerMap^[n + 1] C.base) := by
  have hrel :=
    activeNoncoherentRel_of_noncoherentAt C.system
      (C.system.observerMap^[n] C.base) h
  have hnext :
      C.system.observerMap^[n + 1] C.base =
        C.system.observerMap (C.system.observerMap^[n] C.base) := by
    rw [Nat.add_comm n 1]
    simpa using Function.iterate_add_apply C.system.observerMap 1 n C.base
  rw [hnext]
  exact hrel

/-- On an all-coherent active observer cycle, every cycle edge carries a matched
two-hole transport between consecutive active vertices and their matched mates. -/
def coherentMatchedTwoHoleIso_at [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) (hall : C.AllCoherent) (n : ℕ) :
    TwoColorIso
      (deleteTwo K (C.system.observerMap^[n] C.base).1
        (C.system.observerMap^[n + 1] C.base).1)
      (deleteTwo K
        (o.min.toIsoData.toEquiv (C.system.observerMap^[n] C.base)).1
        (o.min.toIsoData.toEquiv
          (C.system.observerMap^[n + 1] C.base)).1)
      (deleteTwoColor S (C.system.observerMap^[n] C.base).1
        (C.system.observerMap^[n + 1] C.base).1)
      (deleteTwoColor (singletonLeft T a)
        (C.system.observerMap^[n] C.base).1
        (C.system.observerMap^[n + 1] C.base).1)
      (deleteTwoColor S
        (o.min.toIsoData.toEquiv (C.system.observerMap^[n] C.base)).1
        (o.min.toIsoData.toEquiv
          (C.system.observerMap^[n + 1] C.base)).1)
      (deleteTwoColor (singletonRight T b)
        (o.min.toIsoData.toEquiv (C.system.observerMap^[n] C.base)).1
        (o.min.toIsoData.toEquiv
          (C.system.observerMap^[n + 1] C.base)).1) := by
  let u := C.system.observerMap^[n] C.base
  have hnext :
      C.system.observerMap^[n + 1] C.base =
        C.system.observerMap u := by
    rw [Nat.add_comm n 1]
    simpa [u] using Function.iterate_add_apply C.system.observerMap 1 n C.base
  rw [hnext]
  exact C.system.coherentMatchedTwoHoleIsoAt u (hall n)

/-- On an all-coherent active observer cycle, the host adjacency between two
consecutive cycle bases disagrees with the host adjacency between their matched
mates under the chosen minimum matching.  This is the geometric content of the
coherent active first error: the only "missing" adjacency information on each
side is exactly the edge between the deleted base and the next cycle vertex,
and that information disagrees. -/
theorem adjacency_mismatch_at [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) (hall : C.AllCoherent) (n : ℕ) :
    ¬ (K.Adj (C.system.observerMap^[n] C.base).1
            (C.system.observerMap^[n + 1] C.base).1 ↔
        K.Adj (o.min.toIsoData.toEquiv
                  (C.system.observerMap^[n] C.base)).1
              (o.min.toIsoData.toEquiv
                  (C.system.observerMap^[n + 1] C.base)).1) := by
  set u : singletonLeft T a := C.system.observerMap^[n] C.base with hu_def
  have hnext :
      C.system.observerMap^[n + 1] C.base =
        C.system.observerMap u := by
    rw [Nat.add_comm n 1]
    simpa [hu_def] using
      Function.iterate_add_apply C.system.observerMap 1 n C.base
  rw [hnext]
  set E : LowSliceMinimumErrorMatching.ActiveFirstError o.min u :=
    C.system.witness u with hE_def
  have hobs : C.system.observerMap u = E.nextLeft := rfl
  have hcoh : E.Coherent := hall n
  rw [hobs]
  have hsrc : E.source = E.nextLeft := by
    unfold LowSliceMinimumErrorMatching.ActiveFirstError.Coherent at hcoh
    exact hcoh
  rw [← hsrc]
  have hmis : ¬ (K.Adj u.1 E.error.z.1 ↔
      K.Adj (o.min.toIsoData.toEquiv u).1
        ((o.min.toIsoData.cardIso u).cardIso.iso.toEquiv E.error.z).1) :=
    E.error.mismatch
  have hsrc_val : E.source.1 = E.error.z.1 := by
    simp [LowSliceMinimumErrorMatching.ActiveFirstError.source,
      LowSliceCardFirstError.sourceActiveVertex]
  have htarget : E.target = o.min.toIsoData.toEquiv E.source :=
    E.target_eq_toEquiv_source_of_coherent hcoh
  have himg : ((o.min.toIsoData.cardIso u).cardIso.iso.toEquiv E.error.z).1 =
      (o.min.toIsoData.toEquiv E.source).1 := by
    have hh : E.target.1 = (o.min.toIsoData.toEquiv E.source).1 :=
      congrArg Subtype.val htarget
    simpa [LowSliceMinimumErrorMatching.ActiveFirstError.target,
      LowSliceCardFirstError.targetActiveVertex,
      LowSliceCardFirstError.imageZ] using hh
  rw [hsrc_val, ← himg]
  exact hmis

/-- On an all-coherent active observer cycle, the chosen matching cannot fix
two consecutive cycle vertices pointwise: at every index, at least one of the
two consecutive matched mates is genuinely different from the cycle vertex
itself.  This is the parity obstruction to the matching being "trivial" on the
cycle. -/
theorem matching_moves_consecutive_at [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) (hall : C.AllCoherent) (n : ℕ) :
    ¬ ((o.min.toIsoData.toEquiv
            (C.system.observerMap^[n] C.base)).1 =
          (C.system.observerMap^[n] C.base).1 ∧
        (o.min.toIsoData.toEquiv
            (C.system.observerMap^[n + 1] C.base)).1 =
          (C.system.observerMap^[n + 1] C.base).1) := by
  rintro ⟨h1, h2⟩
  apply C.adjacency_mismatch_at hall n
  rw [h1, h2]

/-- On an all-coherent active observer cycle, the chosen matching moves at
least one cycle vertex: there is some index where the matched mate differs from
the cycle vertex on the host. -/
theorem exists_moved_by_matching [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (C : ActiveObserverCycle o) (hall : C.AllCoherent) :
    ∃ n : ℕ,
      (o.min.toIsoData.toEquiv (C.system.observerMap^[n] C.base)).1 ≠
        (C.system.observerMap^[n] C.base).1 := by
  by_contra h
  push_neg at h
  exact C.matching_moves_consecutive_at hall 0 ⟨h 0, h 1⟩

end ActiveObserverCycle

/-- The all-active branch yields a packaged active observer cycle. -/
theorem exists_activeObserverCycleStructure_of_allActiveBranches [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    {o : LowSlicePositiveMinimumObstruction K S T a b}
    (h : o.AllActiveBranches) :
    Nonempty (ActiveObserverCycle o) := by
  rcases exists_activeObserverCycle_of_allActiveBranches h with
    ⟨B, x, n, hn, hcycle⟩
  exact ⟨
    { system := B
      base := x
      period := n
      period_gt_one := hn
      closes := hcycle }⟩

/-- The all-coherent active observer-cycle fork is impossible. -/
def NoAllCoherentActiveCycleFork [Finite V]
    (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  ∀ o : LowSlicePositiveMinimumObstruction K S T a b,
    ∀ C : ActiveObserverCycle o, ¬ C.AllCoherent

/-- The active observer-cycle fork with a noncoherent index is impossible. -/
def NoNoncoherentActiveCycleFork [Finite V]
    (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  ∀ o : LowSlicePositiveMinimumObstruction K S T a b,
    ∀ C : ActiveObserverCycle o, ¬ C.HasNoncoherent

/-- Ruling out the all-coherent and noncoherent active cycle subforks rules out
the active observer-cycle fork. -/
theorem NoActiveObserverCycleFork.of_no_active_cycle_subforks [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (hcoh : NoAllCoherentActiveCycleFork K S T a b)
    (hnon : NoNoncoherentActiveCycleFork K S T a b) :
    NoActiveObserverCycleFork K S T a b := by
  intro o hcycle
  rcases hcycle with ⟨B, x, n, hn, hcloses⟩
  let C : ActiveObserverCycle o :=
    { system := B
      base := x
      period := n
      period_gt_one := hn
      closes := hcloses }
  rcases C.allCoherent_or_hasNoncoherent with hC | hC
  · exact hcoh o C hC
  · exact hnon o C hC

/-- The all-inactive fork where every selected witness exposes an endpoint is
impossible. -/
def NoAllEndpointExposingInactiveFork [Finite V]
    (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  ∀ o : LowSlicePositiveMinimumObstruction K S T a b,
    ∀ B : InactiveObserverSystem o, ¬ B.AllEndpointExposing

/-- The all-inactive fork with an explicit outer residual is impossible. -/
def NoOuterResidualInactiveFork [Finite V]
    (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  ∀ o : LowSlicePositiveMinimumObstruction K S T a b,
    ∀ B : InactiveObserverSystem o, ¬ B.HasOuterResidual

/-- Ruling out the endpoint-exposing and outer-residual inactive subforks rules
out the all-inactive endpoint/outer fork. -/
theorem NoInactiveEndpointOuterFork.of_no_inactive_subforks [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (hend : NoAllEndpointExposingInactiveFork K S T a b)
    (houter : NoOuterResidualInactiveFork K S T a b) :
    NoInactiveEndpointOuterFork K S T a b := by
  intro o hfork
  rcases hfork with ⟨B, hall | hres⟩
  · exact hend o B hall
  · exact houter o B hres

/-- The refined five-branch reduction for the minimum-error obstruction route. -/
theorem NoLowSlicePositiveMinimumObstruction.of_no_refined_forks [Finite V]
    {K : SimpleGraph V} {S T : Set V} {a b : V}
    (hcoh : NoAllCoherentActiveCycleFork K S T a b)
    (hnon : NoNoncoherentActiveCycleFork K S T a b)
    (hend : NoAllEndpointExposingInactiveFork K S T a b)
    (houter : NoOuterResidualInactiveFork K S T a b)
    (hmixed : NoMixedBranchFork K S T a b) :
    NoLowSlicePositiveMinimumObstruction K S T a b :=
  NoLowSlicePositiveMinimumObstruction.of_no_strategy_forks
    (NoActiveObserverCycleFork.of_no_active_cycle_subforks hcoh hnon)
    (NoInactiveEndpointOuterFork.of_no_inactive_subforks hend houter)
    hmixed

end LowSlicePositiveMinimumObstruction

/-- The `a`-side two-hole second color
`(T \ {t}) ∪ {a}` on `K - {t,o}`. -/
def twoHoleASecondColor (T : Set V) (a t o : V) : Set (deleteTwoVertex t o) :=
  deleteTwoColor (singletonLeft T a) t o

@[simp] theorem mem_twoHoleASecondColor
    (T : Set V) (a t o : V) (x : deleteTwoVertex t o) :
    x ∈ twoHoleASecondColor T a t o ↔ x.1 ∈ T ∨ x.1 = a := by
  simp [twoHoleASecondColor]

/-- The `b`-side two-hole second color
`(T \ {t}) ∪ {b}` on `K - {t,o}`. -/
def twoHoleBSecondColor (T : Set V) (b t o : V) : Set (deleteTwoVertex t o) :=
  deleteTwoColor (singletonRight T b) t o

@[simp] theorem mem_twoHoleBSecondColor
    (T : Set V) (b t o : V) (x : deleteTwoVertex t o) :
    x ∈ twoHoleBSecondColor T b t o ↔ x.1 ∈ T ∨ x.1 = b := by
  simp [twoHoleBSecondColor]

/-- A two-hole match `D^a_{t,o} ≅ D^b_{t',o'}`. -/
def TwoHoleMatch (K : SimpleGraph V) (S T : Set V)
    (a b t o t' o' : V) : Type _ :=
  TwoColorIso (deleteTwo K t o) (deleteTwo K t' o')
    (deleteTwoColor S t o) (twoHoleASecondColor T a t o)
    (deleteTwoColor S t' o') (twoHoleBSecondColor T b t' o')

namespace TwoHoleMatch

/-- Under a two-hole match, the image of the moved `a`-vertex is
second-colored on the `b`-side.  This is the Lean version of the first
two-hole port bookkeeping statement. -/
theorem image_a_mem_right {K : SimpleGraph V} {S T : Set V}
    {a b t o t' o' : V}
    (e : TwoHoleMatch K S T a b t o t' o') (hat : a ≠ t) (hao : a ≠ o) :
    (e.iso.toEquiv ⟨a, hat, hao⟩).1 ∈ T ∨ (e.iso.toEquiv ⟨a, hat, hao⟩).1 = b := by
  have hmem :
      (⟨a, hat, hao⟩ : deleteTwoVertex t o) ∈ twoHoleASecondColor T a t o := by
    simp
  exact (e.map_second ⟨a, hat, hao⟩).mp hmem

/-- Under a two-hole match, the image of any second-colored vertex is
second-colored on the `b`-side. -/
theorem image_second_mem_right {K : SimpleGraph V} {S T : Set V}
    {a b t o t' o' : V}
    (e : TwoHoleMatch K S T a b t o t' o') (x : deleteTwoVertex t o)
    (hx : x.1 ∈ T ∨ x.1 = a) :
    (e.iso.toEquiv x).1 ∈ T ∨ (e.iso.toEquiv x).1 = b := by
  exact (e.map_second x).mp (by simpa using hx)

/-- Under a two-hole match, the image of a non-second-colored vertex is
non-second-colored on the `b`-side. -/
theorem image_not_second_mem_right {K : SimpleGraph V} {S T : Set V}
    {a b t o t' o' : V}
    (e : TwoHoleMatch K S T a b t o t' o') (x : deleteTwoVertex t o)
    (hx : x.1 ∉ T) (hxa : x.1 ≠ a) :
    (e.iso.toEquiv x).1 ∉ T ∧ (e.iso.toEquiv x).1 ≠ b := by
  have hxnot : x ∉ twoHoleASecondColor T a t o := by
    simpa [not_or] using And.intro hx hxa
  have hnot := mt (e.map_second x).mpr hxnot
  simpa [not_or] using hnot

/-- Under a two-hole match, the preimage of the moved `b`-vertex is
second-colored on the `a`-side. -/
theorem preimage_b_mem_left {K : SimpleGraph V} {S T : Set V}
    {a b t o t' o' : V}
    (e : TwoHoleMatch K S T a b t o t' o') (hbt' : b ≠ t') (hbo' : b ≠ o') :
    (e.iso.symm.toEquiv ⟨b, hbt', hbo'⟩).1 ∈ T ∨
      (e.iso.symm.toEquiv ⟨b, hbt', hbo'⟩).1 = a := by
  have hmem :
      (⟨b, hbt', hbo'⟩ : deleteTwoVertex t' o') ∈ twoHoleBSecondColor T b t' o' := by
    simp
  have hleft := (e.map_second (e.iso.symm.toEquiv ⟨b, hbt', hbo'⟩)).mpr (by
    simp [hmem])
  simpa using hleft

/-- If a two-hole match sends the moved `a`-vertex to the moved `b`-vertex,
then every old `T`-vertex still maps to an old `T`-vertex.  This is the
Lean-facing easy half of "name coherence means side coherence". -/
theorem image_T_of_maps_a_to_b {K : SimpleGraph V} {S T : Set V}
    {a b t o t' o' : V}
    (e : TwoHoleMatch K S T a b t o t' o') (hat : a ≠ t) (hao : a ≠ o)
    (haT : a ∉ T)
    (hab : (e.iso.toEquiv ⟨a, hat, hao⟩).1 = b)
    (x : deleteTwoVertex t o) (hxT : x.1 ∈ T) :
    (e.iso.toEquiv x).1 ∈ T := by
  have hsec := image_second_mem_right e x (Or.inl hxT)
  rcases hsec with hT | hb
  · exact hT
  · exfalso
    have himg : e.iso.toEquiv x = e.iso.toEquiv ⟨a, hat, hao⟩ :=
      Subtype.ext (hb.trans hab.symm)
    have hx : x = ⟨a, hat, hao⟩ := e.iso.toEquiv.injective himg
    have hxval : x.1 = a := congrArg Subtype.val hx
    exact haT (by simpa [hxval] using hxT)

/-- If a two-hole match sends the moved uncolored `b`-vertex to the moved
uncolored `a`-vertex, then outside vertices stay outside. -/
theorem image_outside_of_maps_b_to_a {K : SimpleGraph V} {S T : Set V}
    {a b t o t' o' : V}
    (e : TwoHoleMatch K S T a b t o t' o') (hbt : b ≠ t) (hbo : b ≠ o)
    (hba : (e.iso.toEquiv ⟨b, hbt, hbo⟩).1 = a)
    (x : deleteTwoVertex t o) (hxO : x.1 ∈ singletonOutside T a b) :
    (e.iso.toEquiv x).1 ∈ singletonOutside T a b := by
  rcases hxO with ⟨hxT, hxa, hxb⟩
  have hnot := image_not_second_mem_right e x hxT hxa
  refine ⟨hnot.1, ?_, hnot.2⟩
  intro hxa_img
  have himg : e.iso.toEquiv x = e.iso.toEquiv ⟨b, hbt, hbo⟩ :=
    Subtype.ext (hxa_img.trans hba.symm)
  have hx : x = ⟨b, hbt, hbo⟩ := e.iso.toEquiv.injective himg
  have hxval : x.1 = b := congrArg Subtype.val hx
  exact hxb hxval

end TwoHoleMatch

end FixedHost

end SimpleGraph
