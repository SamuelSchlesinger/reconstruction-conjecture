import Reconstruction.Separator
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Multi-vertex Separator Reassembly

This module generalizes the cut-vertex reassembly constructor
(`Reconstruction.Separator.isoOfDeleteVertIso` / `nonempty_iso_of_cutVertex_pieces`,
the `S = {v}` case) to an **arbitrary separator set** `S`. It is the structural
core of the higher rungs of the separator-decomposition programme: it is exactly
the reassembly half of Heinrich et al.'s "Reconstruction-by-Separation"
(Lemma 24) for interval graphs, and the same statement is what chordal-graph
reconstruction would consume once a clique separator is located.

## Main definitions

* `SimpleGraph.extendFixingSet S ψ` — extend a permutation `ψ` of the
  non-separator vertices `Sᶜ` to a permutation of all of `V` that fixes `S`
  pointwise.

## Main results

* `SimpleGraph.nonempty_iso_of_induce_compl_iso` — a card isomorphism
  `ψ : G − S ≃g H − S` (an isomorphism of the separator-deleted graphs) that
  preserves the separator's internal edges (`hSadj`) and the attachment of `S`
  to `Sᶜ` (`hattach`) extends to a global isomorphism `G ≃g H`. The structural
  generalization of `isoOfDeleteVertIso` from `|S| = 1` to arbitrary `S`.
* `SimpleGraph.nonempty_iso_of_separator_pieces` — the same conclusion from
  per-component data: a bijection of `(G − S)`-components, per-component
  isomorphisms, the separator-edge match, and the attachment match. The card
  isomorphism is assembled with `componentIso`. This is the multi-vertex
  generalization of `nonempty_iso_of_cutVertex_pieces`.

In both, `S` is shared between `G` and `H` and the assembled isomorphism fixes
`S` pointwise (the natural "common separator" form, mirroring the cut-vertex
case where the deleted vertex is shared). The remaining work for any concrete
class is the deck-theoretic recovery of the separator, the component matching,
and the attachment data — none of which lives here.

## References

* Heinrich, Kiyomi, Otachi, Schweitzer (2025). "Interval graphs are
  reconstructible." arXiv:2504.02353 (Reconstruction-by-Separation, Lemma 24).
-/

namespace SimpleGraph

variable {V : Type*}

/-- Extend a permutation `ψ` of the non-separator vertices `Sᶜ` to a permutation
of all of `V` that fixes every vertex of `S`. -/
def extendFixingSet (S : Set V) [DecidablePred (· ∈ S)]
    (ψ : ↥Sᶜ ≃ ↥Sᶜ) : V ≃ V where
  toFun x := if h : x ∈ S then x else (ψ ⟨x, h⟩ : V)
  invFun y := if h : y ∈ S then y else (ψ.symm ⟨y, h⟩ : V)
  left_inv x := by
    by_cases h : x ∈ S
    · simp [dif_pos h]
    · have hx : ((ψ ⟨x, h⟩ : ↥Sᶜ) : V) ∉ S := (ψ ⟨x, h⟩).2
      simp [dif_neg h, dif_neg hx, Equiv.symm_apply_apply]
  right_inv y := by
    by_cases h : y ∈ S
    · simp [dif_pos h]
    · have hy : ((ψ.symm ⟨y, h⟩ : ↥Sᶜ) : V) ∉ S := (ψ.symm ⟨y, h⟩).2
      simp [dif_neg h, dif_neg hy, Equiv.apply_symm_apply]

@[simp] theorem extendFixingSet_apply_mem {S : Set V} [DecidablePred (· ∈ S)]
    (ψ : ↥Sᶜ ≃ ↥Sᶜ) {x : V} (h : x ∈ S) : extendFixingSet S ψ x = x :=
  dif_pos h

theorem extendFixingSet_apply_not_mem {S : Set V} [DecidablePred (· ∈ S)]
    (ψ : ↥Sᶜ ≃ ↥Sᶜ) {x : V} (h : x ∉ S) :
    extendFixingSet S ψ x = (ψ ⟨x, h⟩ : V) :=
  dif_neg h

/-- **Multi-vertex separator reassembly (card-isomorphism form).** A graph
isomorphism `ψ : G − S ≃g H − S` of the separator-deleted graphs that

* preserves the separator's internal edges (`hSadj`), and
* preserves the attachment of each separator vertex to `Sᶜ` (`hattach`),

extends to a global isomorphism `G ≃g H` fixing `S` pointwise. The within-`Sᶜ`
adjacency is handled automatically because `ψ` is a *card* isomorphism (any two
non-separator vertices are adjacent in `G` iff adjacent in `G − S`). -/
theorem nonempty_iso_of_induce_compl_iso {G H : SimpleGraph V} {S : Set V}
    (ψ : G.induce Sᶜ ≃g H.induce Sᶜ)
    (hSadj : ∀ u w, u ∈ S → w ∈ S → (G.Adj u w ↔ H.Adj u w))
    (hattach : ∀ u, u ∈ S → ∀ x : ↥Sᶜ, G.Adj u x.1 ↔ H.Adj u (ψ x : V)) :
    Nonempty (G ≃g H) := by
  classical
  refine ⟨⟨extendFixingSet S ψ.toEquiv, ?_⟩⟩
  intro a b
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S
  · rw [extendFixingSet_apply_mem _ ha, extendFixingSet_apply_mem _ hb]
    exact (hSadj a b ha hb).symm
  · rw [extendFixingSet_apply_mem _ ha, extendFixingSet_apply_not_mem _ hb]
    exact (hattach a ha ⟨b, hb⟩).symm
  · rw [extendFixingSet_apply_mem _ hb, extendFixingSet_apply_not_mem _ ha,
      G.adj_comm a b, H.adj_comm (ψ.toEquiv ⟨a, ha⟩ : V) b]
    exact (hattach b hb ⟨a, ha⟩).symm
  · rw [extendFixingSet_apply_not_mem _ ha, extendFixingSet_apply_not_mem _ hb]
    calc H.Adj (ψ.toEquiv ⟨a, ha⟩ : V) (ψ.toEquiv ⟨b, hb⟩ : V)
        ↔ (H.induce Sᶜ).Adj (ψ.toEquiv ⟨a, ha⟩) (ψ.toEquiv ⟨b, hb⟩) := induce_adj.symm
      _ ↔ (G.induce Sᶜ).Adj ⟨a, ha⟩ ⟨b, hb⟩ := ψ.map_rel_iff
      _ ↔ G.Adj a b := induce_adj

/-- **Multi-vertex separator reassembly (per-component form).** Given a bijection
`e` of the components of `G − S` with those of `H − S`, per-component
isomorphisms `ι`, a separator-edge match (`hSadj`), and an attachment match
(`hattach`, phrased per component), the graphs `G` and `H` are isomorphic. The
card isomorphism is assembled with `componentIso`; the conclusion is then
`nonempty_iso_of_induce_compl_iso`.

This is the multi-vertex generalization of `nonempty_iso_of_cutVertex_pieces`
and the structural core of Heinrich et al.'s Lemma 24. -/
theorem nonempty_iso_of_separator_pieces {G H : SimpleGraph V} {S : Set V}
    (e : (G.induce Sᶜ).ConnectedComponent ≃ (H.induce Sᶜ).ConnectedComponent)
    (ι : ∀ c : (G.induce Sᶜ).ConnectedComponent,
      (G.induce Sᶜ).induce c.supp ≃g (H.induce Sᶜ).induce (e c).supp)
    (hSadj : ∀ u w, u ∈ S → w ∈ S → (G.Adj u w ↔ H.Adj u w))
    (hattach : ∀ u, u ∈ S → ∀ (c : (G.induce Sᶜ).ConnectedComponent) (x : ↥c.supp),
      G.Adj u x.1.1 ↔ H.Adj u (ι c x).1.1) :
    Nonempty (G ≃g H) := by
  refine nonempty_iso_of_induce_compl_iso (componentIso e ι) hSadj ?_
  intro u hu x
  rw [componentIso_apply]
  exact hattach u hu ((G.induce Sᶜ).connectedComponentMk x)
    ⟨x, ConnectedComponent.connectedComponentMk_mem⟩

end SimpleGraph
