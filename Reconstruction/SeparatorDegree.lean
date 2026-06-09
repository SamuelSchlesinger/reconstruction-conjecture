import Reconstruction.Separator
import Reconstruction.Basic
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Separator/degree bridge lemmas

This module collects small bridge lemmas connecting the instance-free structural
predicates of `Reconstruction.Separator` to the finite, degree-based vocabulary
used by the deck-reconstruction machinery.

## Main results

* `SimpleGraph.IsUniversal.map` — universal vertices are isomorphism invariants.
* `SimpleGraph.minDegreeTwo_iff` — the combinatorial `MinDegreeTwo` predicate is
  equivalent to "every vertex has degree at least 2".
* `SimpleGraph.isUniversal_complete` — every vertex of the complete graph is
  universal.
-/

namespace SimpleGraph

variable {V : Type*} {W : Type*}

/-- **Universal vertices are isomorphism invariants.** If `v` is adjacent to
every other vertex of `G` and `e : G ≃g H`, then `e v` is adjacent to every
other vertex of `H`. For `y ≠ e v` we have `e.symm y ≠ v`, so `G.Adj v (e.symm y)`,
which transports across `e`. -/
theorem IsUniversal.map {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {v : V} (h : G.IsUniversal v) : H.IsUniversal (e v) := by
  intro y hy
  have hsy : e.symm y ≠ v := by
    intro hcontra
    apply hy
    rw [← e.apply_symm_apply y, hcontra]
  have hadj : G.Adj v (e.symm y) := h (e.symm y) hsy
  have := e.map_rel_iff.mpr hadj
  rwa [e.apply_symm_apply] at this

/-- **`MinDegreeTwo` is the degree-≥-2 condition.** The instance-free predicate
"every vertex has two distinct neighbours" is equivalent to "every vertex has
degree at least 2", via the cardinality of the neighbour finset. -/
theorem minDegreeTwo_iff [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.MinDegreeTwo ↔ ∀ v, 2 ≤ G.degree v := by
  classical
  constructor
  · intro h v
    obtain ⟨a, b, hab, hva, hvb⟩ := h v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    rw [Nat.succ_le_iff, Finset.one_lt_card_iff]
    exact ⟨a, b, (SimpleGraph.mem_neighborFinset G v a).mpr hva,
      (SimpleGraph.mem_neighborFinset G v b).mpr hvb, hab⟩
  · intro h v
    have hdeg := h v
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Nat.succ_le_iff,
      Finset.one_lt_card_iff] at hdeg
    obtain ⟨a, b, ha, hb, hab⟩ := hdeg
    exact ⟨a, b, hab, (SimpleGraph.mem_neighborFinset G v a).mp ha,
      (SimpleGraph.mem_neighborFinset G v b).mp hb⟩

/-- **Every vertex of the complete graph is universal.** In `⊤`, distinct
vertices are always adjacent, so each vertex is adjacent to every other. -/
theorem isUniversal_complete (v : V) : (⊤ : SimpleGraph V).IsUniversal v := by
  intro x hx
  rw [top_adj]
  exact (Ne.symm hx)

/-- **The complete graph has minimum degree ≥ 2 once it has ≥ 3 vertices.**
Each vertex has every other vertex as a neighbour, so with at least three
vertices in total there are two distinct neighbours. -/
theorem minDegreeTwo_complete [Fintype V] (hV : 3 ≤ Fintype.card V) :
    (⊤ : SimpleGraph V).MinDegreeTwo := by
  classical
  intro v
  -- there are at least two vertices distinct from `v`
  have h2 : 1 < (Finset.univ.erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    omega
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp h2
  refine ⟨a, b, hab, ?_, ?_⟩
  · rw [top_adj]; exact (Finset.ne_of_mem_erase ha).symm
  · rw [top_adj]; exact (Finset.ne_of_mem_erase hb).symm

end SimpleGraph
