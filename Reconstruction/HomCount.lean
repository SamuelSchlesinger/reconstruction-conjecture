import Reconstruction.SupportCount

/-!
# Injective-Homomorphism Copy Counts are Reconstructible

Kelly's Lemma (`Reconstruction.KellyLemma`) reconstructs **induced** copy
counts. The Tutte/Kocay programme (strategy note R1) needs the
*not-necessarily-induced* copy counts: the number of subgraph copies of a
pattern `F`, counted here as **injective graph homomorphisms** `F →g G`
(which is the subgraph-copy count times `|Aut F|`, a constant of `F`). This
module proves they are deck-reconstructible for patterns on `< |V|` vertices
(`SameDeck.injHomCount_eq`):

* an injective homomorphism with `|F|`-element image lands in the induced
  subgraph on its image, giving the partition identity
  `injHomCount F G = ∑_{|U| = |F|} injHomCount F (G[U])`
  (`injHomCount_eq_sum_induce`);
* the count into a target is a target-isomorphism invariant
  (`injHomCount_eq_of_iso`);
* regrouping by the isomorphism class of `G[U]` (the `GraphIsoClass` engine
  of `Reconstruction.SupportCount`) turns the sum into Kelly-weighted class
  sums (`sum_injHomCount_induce_eq`), and Kelly's Lemma finishes.

This is the "subgraph-copy counting layer" prerequisite for the
disconnected-spanning-subgraph step of Tutte's theorem (checklist §4): for
spanning patterns the same identity isolates the full-vertex-set summand,
exactly as `Reconstruction.KocayHost` does for cover counts.

## References

* Kelly, P. J. (1942). "On isometric transformations".
* Kocay, W. L. (1981). "Some new methods in reconstruction theory".
-/

set_option autoImplicit false

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {W : Type*} [Fintype W]

omit [Fintype V] [DecidableEq V] in
private theorem card_coe_set' (U : Finset V) :
    Fintype.card ↥(↑U : Set V) = U.card := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun x => Finset.mem_coe)]
  exact Fintype.card_coe U

/-- Graph homomorphisms from a finite graph into a finite graph form a
finite type (they are determined by their underlying functions). -/
noncomputable instance {F : SimpleGraph W} {G : SimpleGraph V} :
    Fintype (F →g G) :=
  Fintype.ofInjective (fun f => ⇑f) DFunLike.coe_injective

/-- The number of **injective homomorphism copies** of `F` in `G`. This is
`|Aut F|` times the number of subgraph copies of `F`, so its
reconstructibility is equivalent to that of the subgraph-copy count. -/
def injHomCount (F : SimpleGraph W) (G : SimpleGraph V) : ℕ :=
  Fintype.card {f : F →g G // Function.Injective f}

/-- `injHomCount` is invariant under isomorphisms of the target. -/
theorem injHomCount_eq_of_iso {V₂ : Type*} [Fintype V₂] [DecidableEq V₂]
    (F : SimpleGraph W)
    {G₁ : SimpleGraph V} {G₂ : SimpleGraph V₂} (φ : G₁ ≃g G₂) :
    injHomCount F G₁ = injHomCount F G₂ := by
  refine Fintype.card_congr ⟨fun g => ⟨φ.toHom.comp g.1, fun a b hab => g.2 ?_⟩,
    fun g => ⟨φ.symm.toHom.comp g.1, fun a b hab => g.2 ?_⟩, fun g => ?_, fun g => ?_⟩
  · exact φ.toEquiv.injective hab
  · exact φ.symm.toEquiv.injective hab
  · refine Subtype.ext (DFunLike.ext _ _ fun a => ?_)
    exact φ.symm_apply_apply _
  · refine Subtype.ext (DFunLike.ext _ _ fun a => ?_)
    exact φ.apply_symm_apply _

variable (F : SimpleGraph W) (G : SimpleGraph V)

set_option linter.flexible false in
-- The flexible `simp at` calls normalize coerced filter memberships whose
-- normal form is version-sensitive; stating them rigidly would be brittle.
/-- **Partition by image.** Every injective homomorphism copy of `F` lands in
the induced subgraph on its (`|F|`-element) image, and conversely every
injective homomorphism into some `G[U]` with `|U| = |F|` is such a copy. -/
theorem injHomCount_eq_sum_induce :
    injHomCount F G =
      ∑ U ∈ (Finset.univ : Finset V).powersetCard (Fintype.card W),
        injHomCount F (G.induce (↑U : Set V)) := by
  rw [injHomCount, Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun f : F →g G => Finset.image (⇑f) Finset.univ)
    (t := (Finset.univ : Finset V).powersetCard (Fintype.card W)) (by
      intro f hf
      simp only [Finset.coe_filter] at hf
      simp at hf
      simp only [Finset.mem_coe, Finset.mem_powersetCard_univ]
      rw [Finset.card_image_of_injective Finset.univ hf, Finset.card_univ])]
  refine Finset.sum_congr rfl fun U hU => ?_
  rw [Finset.mem_powersetCard_univ] at hU
  rw [injHomCount, Fintype.card_subtype]
  -- the total map: post-compose with the induced-subgraph inclusion
  refine le_antisymm
    (Finset.card_le_card_of_surjOn
      (fun g => (Embedding.induce (↑U : Set V)).toHom.comp g) ?_)
    (Finset.card_le_card_of_injOn
      (fun g => (Embedding.induce (↑U : Set V)).toHom.comp g) ?_ ?_)
  · -- surjectivity: an injective copy with image `U` restricts into `G[U]`
    rintro f hf
    simp at hf
    obtain ⟨hinj, himg⟩ := hf
    have hmem : ∀ a : W, f a ∈ (↑U : Set V) := by
      intro a
      rw [← himg]
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
      exact ⟨a, rfl⟩
    refine ⟨⟨fun a => ⟨f a, hmem a⟩, fun {a b} hab => f.map_adj hab⟩, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      intro a b hab
      exact hinj (congrArg Subtype.val hab)
    · refine DFunLike.ext _ _ fun a => rfl
  · -- the composite has image exactly `U`
    intro g hg
    simp at hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcomp : Function.Injective
        (⇑((Embedding.induce (↑U : Set V)).toHom.comp g)) :=
      fun a b hab => hg (Subtype.ext hab)
    refine ⟨hcomp, ?_⟩
    -- the composite is injective from a `|U|`-element type into `U`
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨a, rfl⟩ := hx
      exact Finset.mem_coe.mp (g a).2
    · rw [Finset.card_image_of_injective Finset.univ hcomp, Finset.card_univ, hU]
  · -- post-composition with the inclusion is injective
    rintro g - g' - heq
    refine DFunLike.ext _ _ fun a => ?_
    have := congrArg (fun h : F →g G => h a) heq
    exact Subtype.ext this

variable {G}

set_option maxHeartbeats 1000000 in
-- The class-indexed sum mixes `Quotient.out` representatives with
-- classical instances; the extra budget covers the resulting unification.
/-- **Regrouping by isomorphism class**: the third instantiation of the
`GraphIsoClass` pattern (after walk counts and cover counts). -/
theorem sum_injHomCount_induce_eq (m : ℕ) :
    ∑ U ∈ (Finset.univ : Finset V).powersetCard m,
        injHomCount F (G.induce (↑U : Set V)) =
      ∑ q : GraphIsoClass m,
        (Quotient.out q).subgraphCount G * injHomCount F (Quotient.out q) := by
  rw [← Finset.sum_fiberwise ((Finset.univ : Finset V).powersetCard m)
    (G.inducedIsoClass m) fun U => injHomCount F (G.induce (↑U : Set V))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [G.filter_inducedIsoClass_eq_copyFinset m q]
  have hbody : ∀ U ∈ (Quotient.out q).copyFinset G,
      injHomCount F (G.induce (↑U : Set V)) =
        injHomCount F (Quotient.out q) := by
    intro U hU
    obtain ⟨e⟩ := ((mem_copyFinset _ _ _).mp hU).2
    exact injHomCount_eq_of_iso F e
  rw [Finset.sum_congr rfl hbody, Finset.sum_const, smul_eq_mul]
  rfl

variable {H : SimpleGraph V}

/-- **Injective-homomorphism (subgraph-copy) counts are reconstructible** for
patterns on fewer vertices than the host. Together with Kelly's Lemma for
induced copies, this completes the counting toolkit of reconstruction theory:
induced counts, products (`Kocay.lean`), host cover counts
(`KocayHost.lean`), and now arbitrary-copy counts. -/
theorem SameDeck.injHomCount_eq (h : G.SameDeck H)
    (hcard : Fintype.card W < Fintype.card V) :
    injHomCount F G = injHomCount F H := by
  rw [injHomCount_eq_sum_induce F G, injHomCount_eq_sum_induce F H,
    sum_injHomCount_induce_eq F (Fintype.card W),
    sum_injHomCount_induce_eq F (Fintype.card W)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [h.subgraphCount_eq (Quotient.out q) (by simpa using hcard)]

end

end SimpleGraph
