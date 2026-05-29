import Reconstruction.Defs

/-!
# Reconstruction Conjecture — Statement and Basic Properties

The Reconstruction Conjecture states that every simple graph on at least
3 vertices is determined up to isomorphism by its deck — the multiset of
vertex-deleted subgraphs considered up to isomorphism.

## Main results

* `SimpleGraph.SameDeck.refl` — `SameDeck` is reflexive
* `SimpleGraph.SameDeck.symm` — `SameDeck` is symmetric
* `SimpleGraph.SameDeck.trans` — `SameDeck` is transitive
* `reconstruction_conjecture` — the conjecture statement (open problem, `sorry`)

## References

* Kelly, P. J. (1942). "On isometric transformations".
* Ulam, S. M. (1960). *A Collection of Mathematical Problems*.
-/

variable {V : Type*}

namespace SimpleGraph

/-- `SameDeck` is reflexive: every graph has the same deck as itself. -/
theorem SameDeck.refl (G : SimpleGraph V) : G.SameDeck G :=
  ⟨Equiv.refl V, fun _ => ⟨RelIso.refl _⟩⟩

/-- `SameDeck` is symmetric. -/
theorem SameDeck.symm {G H : SimpleGraph V} (h : G.SameDeck H) : H.SameDeck G := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ.symm, fun v => ?_⟩
  have key := hσ (σ.symm v)
  rw [σ.apply_symm_apply] at key
  exact key.map RelIso.symm

/-- `SameDeck` is transitive. -/
theorem SameDeck.trans {G H K : SimpleGraph V}
    (h₁ : G.SameDeck H) (h₂ : H.SameDeck K) : G.SameDeck K := by
  obtain ⟨σ₁, hσ₁⟩ := h₁
  obtain ⟨σ₂, hσ₂⟩ := h₂
  refine ⟨σ₁.trans σ₂, fun v => ?_⟩
  obtain ⟨iso₁⟩ := hσ₁ v
  obtain ⟨iso₂⟩ := hσ₂ (σ₁ v)
  exact ⟨iso₁.trans iso₂⟩

/-! ### Complementation

Reconstructibility is closed under complementation: `G` is reconstructible iff
its complement `Gᶜ` is. This is a classical observation (Bondy's
"reconstructor's manual") and a basic tool — it lets every positive result be
dualized (e.g. universal-vertex ↔ isolated-vertex, dense ↔ sparse). -/

/-- An isomorphism of graphs induces an isomorphism of their complements (same
vertex map, adjacency negated). -/
def Iso.compl {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    change Hᶜ.Adj (e a) (e b) ↔ Gᶜ.Adj a b
    simp only [SimpleGraph.compl_adj, ne_eq, (EquivLike.injective e).eq_iff,
      e.map_rel_iff]

/-- Deleting a vertex commutes with complementation: `Gᶜ - v = (G - v)ᶜ`. -/
lemma compl_deleteVert (G : SimpleGraph V) (v : V) :
    Gᶜ.deleteVert v = (G.deleteVert v)ᶜ := by
  ext x y
  simp only [SimpleGraph.compl_adj, SimpleGraph.induce_adj, ne_eq, Subtype.coe_inj]

/-- **The complement deck is reconstructible.** If `G` and `H` have the same
deck, so do their complements. Hence reconstructibility is closed under
complementation. -/
theorem SameDeck.compl {G H : SimpleGraph V} (h : G.SameDeck H) :
    Gᶜ.SameDeck Hᶜ := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨σ, fun v => ?_⟩
  obtain ⟨e⟩ := hσ v
  refine ⟨?_⟩
  rw [compl_deleteVert, compl_deleteVert]
  exact e.compl

end SimpleGraph

/-- **The Reconstruction Conjecture** (Kelly 1942, Ulam 1960).

Every simple graph on a finite vertex set with at least 3 vertices is
determined up to isomorphism by its deck: if `G` and `H` have the same
deck, then `G ≅ H`.

This is one of the foremost open problems in graph theory. -/
theorem reconstruction_conjecture
    [Fintype V] (hV : 3 ≤ Fintype.card V)
    (G H : SimpleGraph V) (h : G.SameDeck H) :
    Nonempty (G ≃g H) := by
  -- TODO: This is the full Ulam–Kelly reconstruction conjecture — an open problem
  -- in mathematics since 1942. It asserts that every graph on ≥ 3 vertices is
  -- determined up to isomorphism by its deck. No proof or counterexample is known.
  sorry
