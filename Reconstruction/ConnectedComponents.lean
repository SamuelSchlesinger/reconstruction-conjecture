import Reconstruction.KellyLemma
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting

/-!
# Reconstruction Conjecture — Connected Components

The number of connected components and the property of being connected
are reconstructible graph invariants.

## Main definitions

* `SimpleGraph.numComponents` — the number of connected components

## Main results

* `SimpleGraph.SameDeck.numComponents_eq` — number of components is reconstructible
* `SimpleGraph.SameDeck.connected` — connectivity is reconstructible

## Proof outline

The number of connected components can be recovered from the deck via
Kelly's Lemma. Let `E_k` be the edgeless graph on `k` vertices. Then
`s(E_k, G) = ∑_C C(|C|, k)` where the sum is over connected components `C`.
Since `s(E_k, G)` is reconstructible for `k < n` by Kelly's Lemma, this
system of equations determines the multiset of component sizes, hence the
number of components.

## References

* Kelly, P. J. (1942). "On isometric transformations".
-/

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of connected components of a graph. -/
def numComponents (G : SimpleGraph V) : ℕ :=
  Fintype.card G.ConnectedComponent

variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- **The number of connected components is reconstructible.**

The proof uses Kelly's Lemma: the number of induced copies of the edgeless
graph on `k` vertices equals `∑_C C(|C|, k)` summed over connected components
`C`. For `k = 1, ..., n-1`, all these counts are reconstructible. This system
of polynomial equations determines the multiset of component sizes, hence the
number of components. -/
theorem SameDeck.numComponents_eq (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) :
    G.numComponents = H.numComponents := by
  -- TODO: Counting argument via Kelly's Lemma. The number of induced copies of the
  -- edgeless graph on k vertices equals ∑_C C(|C|,k) summed over connected
  -- components C. Kelly's Lemma gives these counts for k < n, and the resulting
  -- system of binomial equations determines the multiset of component sizes (via
  -- Vandermonde-style inversion), hence the number of components.
  -- This sorry propagates to `connected` and transitively to `isTree`.
  sorry

omit [DecidableEq V] [DecidableRel G.Adj] [DecidableRel H.Adj] in
/-- **Connectivity is reconstructible.** If `G` is connected and has the same
deck as `H` (on ≥ 3 vertices), then `H` is connected.

A graph is connected iff it has exactly one connected component. Since the
number of components is reconstructible, connectivity follows. -/
theorem SameDeck.connected (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) : H.Connected := by
  have hne : Nonempty V := by rw [← Fintype.card_pos_iff]; omega
  -- G has 1 connected component (it's connected)
  have hG_one : G.numComponents = 1 := by
    simp only [numComponents]
    haveI := hconn.preconnected.subsingleton_connectedComponent
    have hle := Fintype.card_le_one_iff_subsingleton.mpr ‹_›
    have hpos : 0 < Fintype.card G.ConnectedComponent :=
      Fintype.card_pos_iff.mpr ⟨G.connectedComponentMk hconn.nonempty.some⟩
    omega
  -- H has 1 connected component (reconstructible)
  have hH_one : H.numComponents = 1 := hG_one ▸ (h.numComponents_eq hV).symm
  -- H is connected: Preconnected + Nonempty
  rw [connected_iff]
  constructor
  · intro u v
    have hsub : Subsingleton H.ConnectedComponent := by
      rw [← Fintype.card_le_one_iff_subsingleton]
      simp only [numComponents] at hH_one
      omega
    exact ConnectedComponent.exact (Subsingleton.elim _ _)
  · exact hne

end

end SimpleGraph
