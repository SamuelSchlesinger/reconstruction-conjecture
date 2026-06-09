import Reconstruction.ValueSeparated

/-!
# Twins and Twin Transpositions

Step (i) of the twin-flexible rung of the symmetry-breaking programme
(`research/attacks/symmetry-breaking.md`): two vertices are **twins** if
they have the same neighbours apart from each other, and the transposition
of a twin pair is a graph automorphism (`twinSwapIso`).

In the marking picture: if a mixed card-degree class consists of pairwise
twins, the choice of *which* class members are the deleted vertex's
neighbours can be re-pointed freely by composing twin transpositions —
the ambiguity that mixed classes leave (after `SameDeck.nbrCount_eq` fixes
their sizes) is absorbed by card automorphisms. The class-by-class
assembly is the next layer; this module provides the verified swap.
-/

set_option autoImplicit false

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Two vertices are **twins** if every other vertex sees them identically.
No condition is placed on the edge between them, so this covers both twin
flavours at once. -/
def AreTwinVertices (G : SimpleGraph V) (u u' : V) : Prop :=
  ∀ z : V, z ≠ u → z ≠ u' → (G.Adj u z ↔ G.Adj u' z)

theorem AreTwinVertices.symm {u u' : V} (h : G.AreTwinVertices u u') :
    G.AreTwinVertices u' u := fun z hzu' hzu => (h z hzu hzu').symm

/-- **A twin transposition is an automorphism.** Swapping a twin pair
preserves adjacency: pairs disjoint from `{u, u'}` are untouched, the pair
`(u, u')` maps to `(u', u)` (symmetry), and a mixed pair `(u, z)` maps to
`(u', z)` (twin property). -/
def twinSwapIso [DecidableEq V] {u u' : V} (h : G.AreTwinVertices u u') :
    G ≃g G where
  toEquiv := Equiv.swap u u'
  map_rel_iff' := by
    intro x y
    rcases eq_or_ne x u with hx | hxu
    · rw [hx]
      rcases eq_or_ne y u with hy | hyu
      · rw [hy]
        simp
      · rcases eq_or_ne y u' with hy' | hyu'
        · rw [hy']
          simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
          exact G.adj_comm u' u
        · simp only [Equiv.swap_apply_left,
            Equiv.swap_apply_of_ne_of_ne hyu hyu']
          exact (h y hyu hyu').symm
    · rcases eq_or_ne x u' with hx' | hxu'
      · rw [hx']
        rcases eq_or_ne y u with hy | hyu
        · rw [hy]
          simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
          exact G.adj_comm u u'
        · rcases eq_or_ne y u' with hy' | hyu'
          · rw [hy']
            simp
          · simp only [Equiv.swap_apply_right,
              Equiv.swap_apply_of_ne_of_ne hyu hyu']
            exact h y hyu hyu'
      · rcases eq_or_ne y u with hy | hyu
        · rw [hy]
          simp only [Equiv.swap_apply_left,
            Equiv.swap_apply_of_ne_of_ne hxu hxu']
          exact (G.adj_comm x u').trans
            (((h x hxu hxu').symm).trans (G.adj_comm u x))
        · rcases eq_or_ne y u' with hy' | hyu'
          · rw [hy']
            simp only [Equiv.swap_apply_right,
              Equiv.swap_apply_of_ne_of_ne hxu hxu']
            exact (G.adj_comm x u).trans
              ((h x hxu hxu').trans (G.adj_comm u' x))
          · simp only [Equiv.swap_apply_of_ne_of_ne hxu hxu',
              Equiv.swap_apply_of_ne_of_ne hyu hyu']

@[simp] theorem twinSwapIso_apply [DecidableEq V] {u u' : V}
    (h : G.AreTwinVertices u u') (x : V) :
    twinSwapIso h x = Equiv.swap u u' x := rfl

end SimpleGraph
