import Reconstruction.DegreeSequence

/-!
# Reconstruction Conjecture — Regular Graphs

Regular graphs are a reconstructible graph class: if `G` is `d`-regular and
has the same deck as `H` (on ≥ 3 vertices), then `H` is also `d`-regular.

## Main results

* `SimpleGraph.SameDeck.isRegularOfDegree` — regularity is reconstructible

## References

* Kelly, P. J. (1942). "On isometric transformations".
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- **Regular graphs are reconstructible.** If `G` is `d`-regular and has the same
deck as `H` (on ≥ 3 vertices), then `H` is also `d`-regular.

The degree multiset of a `d`-regular graph consists entirely of `d`'s. Since the
degree multiset is reconstructible (`SameDeck.degreeMultiset_eq`), `H` has the same
degree multiset, hence is also `d`-regular. -/
theorem SameDeck.isRegularOfDegree (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V)
    {d : ℕ} (hreg : G.IsRegularOfDegree d) : H.IsRegularOfDegree d := by
  obtain ⟨σ, hdeg⟩ := h.degree_eq hV
  intro w
  have key := hdeg (σ.symm w)
  rw [σ.apply_symm_apply] at key
  rw [← key, hreg]

end SimpleGraph
