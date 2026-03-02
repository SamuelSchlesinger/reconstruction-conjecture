import Reconstruction.KellyLemma
import Reconstruction.DegreeSequence
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Reconstruction Conjecture — Connected Components

The number of connected components and the property of being connected
are reconstructible graph invariants.

## Main results

* `SimpleGraph.SameDeck.connected` — connectivity is reconstructible
* `SimpleGraph.SameDeck.numComponents_eq` — number of components is reconstructible

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

private theorem reachable_of_deleteVert {v : V}
    {a b : V} (ha : a ≠ v) (hb : b ≠ v)
    (h : (G.deleteVert v).Reachable ⟨a, ha⟩ ⟨b, hb⟩) : G.Reachable a b :=
  h.map ⟨Subtype.val, fun h => h⟩

omit [DecidableEq V] [DecidableRel G.Adj] [DecidableRel H.Adj] in
/-- **Connectivity is reconstructible.** If `G` is connected and has the same
deck as `H` (on ≥ 3 vertices), then `H` is connected.

The proof finds a non-cut vertex `v` in `G` (which exists in any connected
graph on ≥ 2 vertices). The deck isomorphism gives `G - v ≅ H - σ(v)`, so
`H - σ(v)` is connected. Since every vertex of `H` has positive degree
(degree sequence is reconstructible), `σ(v)` has a neighbor in `H`, and
we can extend connectivity of `H - σ(v)` to all of `H`. -/
theorem SameDeck.connected (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) : H.Connected := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hG_deg : ∀ u : V, 0 < G.degree u := by
    intro u; by_contra hc
    obtain ⟨w, hw⟩ := exists_ne u
    obtain ⟨p⟩ := hconn.preconnected u w
    cases p with
    | nil => exact hw rfl
    | cons hadj _ => exact hc ((G.degree_pos_iff_exists_adj u).mpr ⟨_, hadj⟩)
  have hH_deg : ∀ w : V, 0 < H.degree w := by
    obtain ⟨τ, hτ⟩ := h.degree_eq hV; intro w
    have h1 := hτ (τ.symm w); rw [τ.apply_symm_apply] at h1
    have h2 := hG_deg (τ.symm w); omega
  obtain ⟨v, hv_conn⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  obtain ⟨σ, hσ⟩ := h; obtain ⟨iso⟩ := hσ v
  have hH_del : (H.deleteVert (σ v)).Connected := iso.connected_iff.mp hv_conn
  obtain ⟨x, hx⟩ := (H.degree_pos_iff_exists_adj (σ v)).mp (hH_deg (σ v))
  have hxv : x ≠ σ v := Ne.symm hx.ne
  rw [connected_iff]; refine ⟨fun a b => ?_, ‹Nonempty V›⟩
  by_cases ha : a = σ v <;> by_cases hb : b = σ v
  · subst ha; subst hb; exact ⟨Walk.nil⟩
  · subst ha; exact (Adj.reachable hx).trans
      (reachable_of_deleteVert hxv hb (hH_del.preconnected ⟨x, hxv⟩ ⟨b, hb⟩))
  · subst hb; exact (reachable_of_deleteVert ha hxv
      (hH_del.preconnected ⟨a, ha⟩ ⟨x, hxv⟩)).trans (Adj.reachable hx).symm
  · exact reachable_of_deleteVert ha hb (hH_del.preconnected ⟨a, ha⟩ ⟨b, hb⟩)

/-- **The number of connected components is reconstructible.**

The proof proceeds by cases:
- **Connected case**: both graphs have 1 component (by `SameDeck.connected`).
- **Isolated vertex case**: if some vertex has degree 0, use the fact that
  removing an isolated vertex drops the component count by 1, while removing
  a non-isolated vertex can only increase it. The deck gives
  `c(G-v) = c(H-σv)`, and degree reconstructibility identifies isolated vertices.
- **No isolated vertices**: find a non-cut vertex `w₀` (exists in every component
  of a graph with no isolated vertices) whose removal preserves the component
  count. Then `c(G) = c(G-w₀) = c(H-σw₀) ≥ c(H)` and symmetrically. -/
theorem SameDeck.numComponents_eq (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) :
    G.numComponents = H.numComponents := by
  -- TODO: Three-way case split (connected / isolated vertex / no isolated vertices).
  -- The connected case follows from `SameDeck.connected` + component count = 1.
  -- The isolated vertex case uses c(G-v) + 1 = c(G) when deg(v) = 0 and
  -- c(G) ≤ c(G-v) when deg(v) > 0 (inclusion map on components is surjective).
  -- The no-isolated-vertices case uses existence of non-cut vertices to get
  -- c(G) = c(G-w₀) for some w₀, then the deck isomorphism transfers this to H.
  -- Known issues with the attempted proof: Decidable instance mismatches in
  -- Fintype.card_le_of_injective/surjective when mixing Classical and concrete
  -- decidability, and out_eq direction for Quot.exists_rep.
  sorry

end

end SimpleGraph
