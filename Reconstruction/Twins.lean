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

/-! ### Twin-supported involutions are automorphisms -/

/-- **An involution that only moves vertices to their twins preserves
adjacency.** The generalization of `twinSwapIso` from one transposition to
any twin-supported involution; involutivity closes the corner where the
two moved pairs collide (`y = f x` forces `f y = x`). -/
theorem twin_involution_map_rel {f : V → V} (hinv : Function.Involutive f)
    (hmove : ∀ x : V, f x ≠ x → G.AreTwinVertices x (f x)) (x y : V) :
    G.Adj (f x) (f y) ↔ G.Adj x y := by
  by_cases hfx : f x = x
  · by_cases hfy : f y = y
    · rw [hfx, hfy]
    · -- `x` fixed, `y` moved: `x ∉ {y, f y}`
      have hxy : x ≠ y := fun h => hfy (by rw [← h, hfx])
      have hxfy : x ≠ f y := fun h => hfy (by
        have h2 := congrArg f h
        rw [hinv y] at h2
        rw [hfx] at h2
        rw [← h]
        exact h2)
      rw [hfx]
      have ht := hmove y hfy
      exact (G.adj_comm x (f y)).trans
        ((ht x hxy hxfy).symm.trans (G.adj_comm y x))
  · by_cases hfy : f y = y
    · -- `y` fixed, `x` moved
      have hyx : y ≠ x := fun h => hfx (by rw [← h, hfy])
      have hyfx : y ≠ f x := fun h => hfx (by
        have h2 := congrArg f h
        rw [hinv x] at h2
        rw [hfy] at h2
        rw [← h]
        exact h2)
      rw [hfy]
      have ht := hmove x hfx
      exact (ht y hyx hyfx).symm
    · -- both moved
      rcases eq_or_ne y x with hyx | hyx
      · rw [hyx]
        simp
      · rcases eq_or_ne y (f x) with hyfx | hyfx
        · -- colliding pairs: `y = f x`, hence `f y = x`
          have hfyx : f y = x := by rw [hyfx, hinv x]
          rw [hfyx, hyfx]
          exact G.adj_comm (f x) x
        · -- generic: two twin steps
          have hfyne : f y ≠ x := fun h => hyfx (by
            have h2 := congrArg f h
            rw [hinv y] at h2
            exact h2)
          have hfyfx : f y ≠ f x := fun h => hyx (by
            have h2 := congrArg f h
            rw [hinv y, hinv x] at h2
            exact h2)
          have step1 : G.Adj (f x) (f y) ↔ G.Adj x (f y) :=
            (hmove x hfx (f y) hfyne hfyfx).symm
          have step2 : G.Adj x (f y) ↔ G.Adj x y := by
            have ht := hmove y hfy
            have hxny : x ≠ y := hyx.symm
            have hxnfy : x ≠ f y := fun h => hfyne h.symm
            exact (G.adj_comm x (f y)).trans
              ((ht x hxny hxnfy).symm.trans (G.adj_comm y x))
          exact step1.trans step2

/-- Package a twin-supported involution as a graph automorphism. -/
def twinInvolutionIso {f : V → V} (hinv : Function.Involutive f)
    (hmove : ∀ x : V, f x ≠ x → G.AreTwinVertices x (f x)) : G ≃g G where
  toEquiv := hinv.toPerm f
  map_rel_iff' := by
    intro x y
    exact twin_involution_map_rel hinv hmove x y

end SimpleGraph
