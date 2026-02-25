import Reconstruction.Defs
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Reconstruction Conjecture — Edge Count

We prove that the number of edges is a reconstructible graph invariant:
if two graphs on the same finite vertex set (≥ 3 vertices) have the same deck,
they have the same number of edges.

## Main results

* `SimpleGraph.deleteVert_edgeFinset_card_add_degree` — `|E(G - v)| + deg(v) = |E(G)|`
* `SimpleGraph.sum_card_edgeFinset_deleteVert_add` — `∑ v, |E(G-v)| + 2|E(G)| = n · |E(G)|`
* `SimpleGraph.SameDeck.card_edgeFinset_eq` — same deck → same edge count

## References

* Kelly, P. J. (1942). "On isometric transformations".
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

section EdgeCount

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edges of `G.edgeFinset` not in `s.toFinset.sym2` are exactly the edges
incident to `v`, when `s = {w | w ≠ v}`. -/
private theorem edgeFinset_sdiff_sym2_eq_incidenceFinset (v : V) :
    G.edgeFinset \ ({w : V | w ≠ v} : Set V).toFinset.sym2 = G.incidenceFinset v := by
  rw [incidenceFinset_eq_filter]
  ext e
  simp only [Finset.mem_sdiff, mem_edgeFinset, Finset.mem_sym2_iff,
    Set.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter]
  constructor
  · rintro ⟨he, hne⟩
    push_neg at hne
    obtain ⟨a, ha, rfl⟩ := hne
    exact ⟨he, ha⟩
  · rintro ⟨he, hv⟩
    exact ⟨he, fun h => h v hv rfl⟩

/-- Deleting vertex `v` removes exactly `deg(v)` edges:
`|E(G - v)| + deg_G(v) = |E(G)|`. -/
theorem deleteVert_edgeFinset_card_add_degree (v : V) :
    (G.deleteVert v).edgeFinset.card + G.degree v = G.edgeFinset.card := by
  set s : Set V := {w | w ≠ v}
  have hcard : (G.deleteVert v).edgeFinset.card =
      (G.edgeFinset ∩ s.toFinset.sym2).card := by
    have h2 : (G.induce s).edgeFinset.map
        (Function.Embedding.subtype (· ∈ s)).sym2Map =
        G.edgeFinset ∩ s.toFinset.sym2 :=
      G.map_edgeFinset_induce
    rw [← h2, Finset.card_map]
  have hdeg : G.degree v = (G.edgeFinset \ s.toFinset.sym2).card := by
    rw [← card_incidenceFinset_eq_degree, edgeFinset_sdiff_sym2_eq_incidenceFinset]
  have hpart := Finset.card_sdiff_add_card_inter G.edgeFinset s.toFinset.sym2
  omega

/-- Summing the per-vertex edge count formula over all vertices:
`∑ v, |E(G - v)| + 2|E(G)| = |V| · |E(G)|`.

Equivalently, each edge appears in exactly `|V| - 2` of the `|V|` cards. -/
theorem sum_card_edgeFinset_deleteVert_add :
    ∑ v : V, (G.deleteVert v).edgeFinset.card + 2 * G.edgeFinset.card =
    Fintype.card V * G.edgeFinset.card := by
  have key : ∑ v : V, ((G.deleteVert v).edgeFinset.card + G.degree v) =
      ∑ _v : V, G.edgeFinset.card :=
    Finset.sum_congr rfl fun v _ => G.deleteVert_edgeFinset_card_add_degree v
  rw [Finset.sum_add_distrib, sum_degrees_eq_twice_card_edges] at key
  simpa [Finset.sum_const, Finset.card_univ] using key

end EdgeCount

section Reconstructibility

variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- **Edge count is reconstructible.** If two graphs on ≥ 3 vertices have the
same deck, they have the same number of edges.

This is a consequence of Kelly's counting lemma: each edge appears in
exactly `n - 2` of the `n` vertex-deleted subgraphs. -/
theorem SameDeck.card_edgeFinset_eq (h : G.SameDeck H)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeFinset.card = H.edgeFinset.card := by
  obtain ⟨σ, hσ⟩ := h
  have hcard : ∀ v, (G.deleteVert v).edgeFinset.card =
      (H.deleteVert (σ v)).edgeFinset.card :=
    fun v => (hσ v).some.card_edgeFinset_eq
  have hsum : ∑ v : V, (G.deleteVert v).edgeFinset.card =
      ∑ v : V, (H.deleteVert v).edgeFinset.card := by
    calc ∑ v, (G.deleteVert v).edgeFinset.card
        = ∑ v, (H.deleteVert (σ v)).edgeFinset.card :=
          Finset.sum_congr rfl fun v _ => hcard v
      _ = ∑ v, (H.deleteVert v).edgeFinset.card :=
          σ.sum_comp (fun w => (H.deleteVert w).edgeFinset.card)
  -- Factor: ∑ |E(K-v)| = (|V| - 2) * |E(K)| for any graph K
  have h_restore : Fintype.card V - 2 + 2 = Fintype.card V :=
    Nat.sub_add_cancel (by omega : 2 ≤ Fintype.card V)
  have sum_factor : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      ∑ v : V, (K.deleteVert v).edgeFinset.card =
      (Fintype.card V - 2) * K.edgeFinset.card := by
    intro K inst
    letI : DecidableRel K.Adj := inst
    have hsplit : (Fintype.card V - 2) * K.edgeFinset.card + 2 * K.edgeFinset.card =
        Fintype.card V * K.edgeFinset.card := by rw [← add_mul, h_restore]
    exact Nat.add_right_cancel (K.sum_card_edgeFinset_deleteVert_add.trans hsplit.symm)
  -- Cancel (|V| - 2) ≥ 1
  have hmul : (Fintype.card V - 2) * G.edgeFinset.card =
      (Fintype.card V - 2) * H.edgeFinset.card :=
    (sum_factor G).symm.trans (hsum.trans (sum_factor H))
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < Fintype.card V - 2) hmul

-- See `Reconstruction/Spectral.lean` for spectral graph theory results, including
-- the derivative formula φ'(G) = Σ_v φ(G-v) and the reconstructibility of
-- non-constant characteristic polynomial coefficients.

end Reconstructibility

end SimpleGraph
