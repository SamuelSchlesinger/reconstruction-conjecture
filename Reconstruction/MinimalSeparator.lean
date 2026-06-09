import Reconstruction.SeparatorChar
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Minimal separators: neighbours in each component

The delicate separator-side lemma behind `MinimalSeparatorClique`: in an
inclusion-minimal separator `S`, every vertex `x ∈ S` has a neighbour in every
component of `G − S`. Proof: if `x` had no neighbour in the component of `u₀`,
then `S \ {x}` would still separate `u₀` from `w₀` (a walk from `u₀` in
`G − (S \ {x})` can never leave that component — its only escape would be `x`,
which has no neighbour there), contradicting minimality.

## Main result

* `SimpleGraph.exists_adj_mem_component` — from minimality and a separated pair
  `u₀, w₀`, every `x ∈ S` has a neighbour in `u₀`'s component of `G − S`.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **A minimal separator's vertices reach every component.** If `S` is
inclusion-minimal among separators and `u₀, w₀` are separated by `S`, then any
`x ∈ S` has a neighbour `a` in the same `G − S` component as `u₀`. -/
theorem exists_adj_mem_component {S : Set V} (hconn : G.Connected)
    (hmin : ∀ T : Set V, T ⊂ S → ¬ G.IsSeparator T)
    {x u₀ w₀ : V} (hx : x ∈ S) (hu₀ : u₀ ∉ S) (hw₀ : w₀ ∉ S)
    (hsep : ¬ (G.induce Sᶜ).Reachable ⟨u₀, hu₀⟩ ⟨w₀, hw₀⟩) :
    ∃ a, ∃ (ha : a ∉ S),
      (G.induce Sᶜ).connectedComponentMk ⟨a, ha⟩
        = (G.induce Sᶜ).connectedComponentMk ⟨u₀, hu₀⟩ ∧ G.Adj x a := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ a (ha : a ∉ S), comp ⟨a,ha⟩ = comp ⟨u₀⟩ → ¬ G.Adj x a`
  have hu₀' : u₀ ∉ S \ {x} := fun h => hu₀ h.1
  have hw₀' : w₀ ∉ S \ {x} := fun h => hw₀ h.1
  -- the unreachability that makes `S \ {x}` separate `u₀` from `w₀`
  have hunreach : ¬ (G.induce (S \ {x})ᶜ).Reachable ⟨u₀, hu₀'⟩ ⟨w₀, hw₀'⟩ := by
    intro hr
    rw [reachable_iff_reflTransGen] at hr
    -- every vertex reachable from `u₀` is in `Sᶜ` and in `u₀`'s component
    have key : ∀ z : ↥(S \ {x})ᶜ,
        Relation.ReflTransGen (G.induce (S \ {x})ᶜ).Adj ⟨u₀, hu₀'⟩ z →
        ∃ (h : z.val ∉ S),
          (G.induce Sᶜ).connectedComponentMk ⟨z.val, h⟩
            = (G.induce Sᶜ).connectedComponentMk ⟨u₀, hu₀⟩ := by
      intro z hz
      induction hz with
      | refl => exact ⟨hu₀, rfl⟩
      | @tail b c _ hadj ih =>
        obtain ⟨hb, hbc⟩ := ih
        rw [induce_adj] at hadj
        -- `hadj : G.Adj b.val c.val`, `c.val ∈ (S \ {x})ᶜ`
        have hcmem : c.val ∉ S ∨ c.val = x := by
          have := c.2
          simp only [Set.mem_compl_iff, Set.mem_diff, Set.mem_singleton_iff,
            not_and, not_not] at this
          tauto
        rcases hcmem with hcS | hcx
        · -- stays in `Sᶜ`: same component as `b`, hence as `u₀`
          refine ⟨hcS, ?_⟩
          rw [← adj_connectedComponentMk_eq hadj hb hcS, hbc]
        · -- would give `x` a neighbour in `u₀`'s component — impossible
          exact absurd (hcx ▸ hadj).symm (hcon b.val hb hbc)
    obtain ⟨_, hwc⟩ := key ⟨w₀, hw₀'⟩ hr
    exact hsep (ConnectedComponent.eq.mp hwc.symm)
  exact hmin (S \ {x}) (Set.diff_singleton_ssubset.mpr hx)
    ((isSeparator_iff_separates G (S \ {x})).mpr ⟨hconn, u₀, w₀, hu₀', hw₀', hunreach⟩)

end SimpleGraph
