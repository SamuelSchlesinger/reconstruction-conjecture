import Reconstruction.EdgeCount

/-!
# Reconstruction Conjecture — Degree Sequence

We prove that the degree sequence (as a multiset) is a reconstructible
graph invariant: if two graphs on ≥ 3 vertices have the same deck,
they have the same degree multiset.

## Main results

* `SimpleGraph.SameDeck.degree_eq` — same deck → matching degrees through σ
* `SimpleGraph.SameDeck.degreeMultiset_eq` — same deck → equal degree multisets

## References

* Kelly, P. J. (1942). "On isometric transformations".
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree multiset of a graph: the multiset of all vertex degrees. -/
def degreeMultiset (G : SimpleGraph V) [DecidableRel G.Adj] : Multiset ℕ :=
  Finset.univ.val.map fun v => G.degree v

section Reconstructibility

variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- If two graphs have equal edge counts and isomorphic vertex-deleted subgraphs
at vertices `v` and `w`, then `deg(v) = deg(w)`. -/
theorem degree_eq_of_card_edgeFinset_eq_of_deleteVert_iso
    (he : G.edgeFinset.card = H.edgeFinset.card)
    {v : V} {w : V}
    (iso : G.deleteVert v ≃g H.deleteVert w) :
    G.degree v = H.degree w := by
  have h1 := G.deleteVert_edgeFinset_card_add_degree v
  have h2 := H.deleteVert_edgeFinset_card_add_degree w
  have h3 := iso.card_edgeFinset_eq
  omega

/-- **Degrees are reconstructible.** If two graphs on ≥ 3 vertices have the
same deck via bijection σ, then `deg_G(v) = deg_H(σ v)` for all v. -/
theorem SameDeck.degree_eq (h : G.SameDeck H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ σ : V ≃ V, ∀ v : V, G.degree v = H.degree (σ v) := by
  have he := h.card_edgeFinset_eq hV
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun v => ?_⟩
  exact degree_eq_of_card_edgeFinset_eq_of_deleteVert_iso he (hσ v).some

/-- **Degree multiset is reconstructible.** If two graphs on ≥ 3 vertices have
the same deck, their degree multisets are equal. -/
theorem SameDeck.degreeMultiset_eq (h : G.SameDeck H)
    (hV : 3 ≤ Fintype.card V) :
    G.degreeMultiset = H.degreeMultiset := by
  obtain ⟨σ, hdeg⟩ := h.degree_eq hV
  unfold degreeMultiset
  calc Finset.univ.val.map (fun v => G.degree v)
      = Finset.univ.val.map (fun v => H.degree (σ v)) :=
        Multiset.map_congr rfl fun v _ => hdeg v
    _ = (Finset.univ.val.map ⇑σ).map (fun v => H.degree v) :=
        (Multiset.map_map (fun v => H.degree v) ⇑σ Finset.univ.val).symm
    _ = Finset.univ.val.map (fun v => H.degree v) := by
        congr 1
        have := congrArg Finset.val (Finset.map_univ_equiv σ)
        rw [Finset.map_val] at this
        exact this

end Reconstructibility

end SimpleGraph
