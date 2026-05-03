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

/-- Equality of fixed-host two-colored deletion decks, represented by a
matching of deleted vertices. -/
def FixedHostSameDeck (K : SimpleGraph V) (S U V' : Set V) : Prop :=
  ∃ σ : V ≃ V, ∀ z : V, FixedHostCardIso K S U V' z (σ z)

/-- Fixed-host same-deck is reflexive. -/
theorem FixedHostSameDeck.refl (K : SimpleGraph V) (S U : Set V) :
    FixedHostSameDeck K S U U := by
  refine ⟨Equiv.refl V, ?_⟩
  intro z
  exact ⟨TwoColorIso.refl (K.deleteVert z) (deleteColor S z) (deleteColor U z)⟩

/-- The left singleton second color `T ∪ {a}`. -/
def singletonLeft (T : Set V) (a : V) : Set V :=
  T ∪ {a}

/-- The right singleton second color `T ∪ {b}`. -/
def singletonRight (T : Set V) (b : V) : Set V :=
  T ∪ {b}

/-- The outside set `O = V(K) \ (T ∪ {a,b})` in the singleton switch. -/
def singletonOutside (T : Set V) (a b : V) : Set V :=
  {x | x ∉ T ∧ x ≠ a ∧ x ≠ b}

@[simp] theorem mem_singletonOutside (T : Set V) (a b x : V) :
    x ∈ singletonOutside T a b ↔ x ∉ T ∧ x ≠ a ∧ x ≠ b :=
  Iff.rfl

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

/-- The low direct-shadow cancellation `H_a ≅ H_b`. -/
def LowDirectCancellation (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  FixedHostCardIso K S T T a b

/-- The complementary direct cancellation `C_b^a ≅ C_a^b`. -/
def ComplementaryDirectCancellation (K : SimpleGraph V) (S T : Set V) (a b : V) : Prop :=
  FixedHostCardIso K S (singletonLeft T a) (singletonRight T b) b a

/-- The graph underlying a natural low shadow `K-z`. -/
abbrev lowShadowGraph (K : SimpleGraph V) (z : V) : SimpleGraph {w : V // w ≠ z} :=
  K.deleteVert z

/-- Low-slice `A_t = (K-t, S-t, (T-t) ∪ {a})`. -/
def lowCardASecondColor (T : Set V) (a t : V) : Set {w : V // w ≠ t} :=
  deleteColor (singletonLeft T a) t

/-- Low-slice `B_t = (K-t, S-t, (T-t) ∪ {b})`. -/
def lowCardBSecondColor (T : Set V) (b t : V) : Set {w : V // w ≠ t} :=
  deleteColor (singletonRight T b) t

/-- Complementary-slice `C_o^a = (K-o, S-o, T ∪ {a})`. -/
def compCardASecondColor (T : Set V) (a o : V) : Set {w : V // w ≠ o} :=
  deleteColor (singletonLeft T a) o

/-- Complementary-slice `C_o^b = (K-o, S-o, T ∪ {b})`. -/
def compCardBSecondColor (T : Set V) (b o : V) : Set {w : V // w ≠ o} :=
  deleteColor (singletonRight T b) o

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

/-- The `a`-side two-hole second color
`(T \ {t}) ∪ {a}` on `K - {t,o}`. -/
def twoHoleASecondColor (T : Set V) (a t o : V) : Set (deleteTwoVertex t o) :=
  deleteTwoColor (singletonLeft T a) t o

/-- The `b`-side two-hole second color
`(T \ {t}) ∪ {b}` on `K - {t,o}`. -/
def twoHoleBSecondColor (T : Set V) (b t o : V) : Set (deleteTwoVertex t o) :=
  deleteTwoColor (singletonRight T b) t o

/-- A two-hole match `D^a_{t,o} ≅ D^b_{t',o'}`. -/
def TwoHoleMatch (K : SimpleGraph V) (S T : Set V)
    (a b t o t' o' : V) : Type _ :=
  TwoColorIso (deleteTwo K t o) (deleteTwo K t' o')
    (deleteTwoColor S t o) (twoHoleASecondColor T a t o)
    (deleteTwoColor S t' o') (twoHoleBSecondColor T b t' o')

end FixedHost

end SimpleGraph
