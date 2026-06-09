import Reconstruction.SupportCount
import Reconstruction.Kocay

/-!
# Kocay's Lemma, Deck Form: Host Cover Counts are Reconstructible

This module proves the deck-level form of **Kocay's lemma**: for every finite
family `F = (F i)` of pattern graphs, each on fewer vertices than the host,
the number of ways to cover the *entire host* by induced copies of the `F i`
is reconstructible (`SameDeck.coverTypeCount_eq`).

This is the keystone of the Tutte/Kocay programme (target `R1` of
`research/attacks/strategy-2026-06.md`): in the induced-copy world the Kocay
identity `∏ᵢ s(Fᵢ, G) = ∑_U c(F, G[U])` has exactly one summand that Kelly's
Lemma cannot see — the full-vertex-set term `c(F, G)`. The product on the
left is reconstructible (`SameDeck.subgraphCount_prod_eq`), and every proper
summand regroups by the isomorphism class of `G[U]` into Kelly-weighted class
sums via the `GraphIsoClass` engine of `Reconstruction.SupportCount`. The
host term is therefore deck-determined.

Downstream (per the strategy note), host cover counts for path/cycle families
are the raw material from which the disconnected-spanning-subgraph counts and
ultimately the Hamiltonian count (`HamiltonianHomCountReconstructible`,
Tutte 1979) are to be extracted.

## References

* Kocay, W. L. (1981). "Some new methods in reconstruction theory".
* Tutte, W. T. (1979). "All the king's horses".
* Stark, P. (2025). "Generalization and power of Kocay's lemma in graph
  reconstruction". arXiv:2509.02604.
-/

set_option autoImplicit false

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {W : ι → Type*} [∀ i, Fintype (W i)]

/-- **Regrouping host-subset cover counts by isomorphism class.** The total
cover count over all `m`-element induced subgraphs is the sum over
isomorphism classes `q` of graphs on `m` vertices of the Kelly subgraph count
of `q` times the cover count of `q`. The clone of
`sum_fullSupport_induce_eq` with the iso-invariant
`coverTypeCount F` in place of the walk count. -/
theorem sum_coverTypeCount_induce_eq (G : SimpleGraph V)
    (F : (i : ι) → SimpleGraph (W i)) (m : ℕ) :
    ∑ U ∈ (Finset.univ : Finset V).powersetCard m,
        coverTypeCount F (G.induce (↑U : Set V)) =
      ∑ q : GraphIsoClass m,
        (Quotient.out q).subgraphCount G * coverTypeCount F (Quotient.out q) := by
  rw [← Finset.sum_fiberwise ((Finset.univ : Finset V).powersetCard m)
    (G.inducedIsoClass m) fun U => coverTypeCount F (G.induce (↑U : Set V))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [G.filter_inducedIsoClass_eq_copyFinset m q]
  have hbody : ∀ U ∈ (Quotient.out q).copyFinset G,
      coverTypeCount F (G.induce (↑U : Set V)) =
        coverTypeCount F (Quotient.out q) := by
    intro U hU
    obtain ⟨e⟩ := ((mem_copyFinset _ _ _).mp hU).2
    exact coverTypeCount_eq_of_iso F e
  rw [Finset.sum_congr rfl hbody, Finset.sum_const, smul_eq_mul]
  rfl

/-- **Kocay's identity, host-isolated form.** The product of the Kelly counts
splits as the host cover count plus Kelly-weighted class sums over all proper
sizes. Every term of the double sum is deck-reconstructible, so this isolates
the host term. -/
theorem prod_subgraphCount_eq_coverTypeCount_add (G : SimpleGraph V)
    (F : (i : ι) → SimpleGraph (W i)) :
    (∏ i, (F i).subgraphCount G) =
      coverTypeCount F G +
        ∑ m ∈ Finset.range (Fintype.card V), ∑ q : GraphIsoClass m,
          (Quotient.out q).subgraphCount G * coverTypeCount F (Quotient.out q) := by
  rw [coverTypeCount_sum_induce F G,
    ← Finset.add_sum_erase ((Finset.univ : Finset V).powerset)
      (fun U => coverTypeCount F (G.induce (↑U : Set V)))
      (Finset.mem_powerset_self _)]
  congr 1
  · -- the full-vertex-set term is the host cover count
    refine coverTypeCount_eq_of_iso F ?_
    rw [Finset.coe_univ]
    exact G.induceUnivIso
  · -- the proper terms regroup by size and isomorphism class
    have herase : ((Finset.univ : Finset V).powerset).erase Finset.univ =
        (Finset.range (Fintype.card V)).biUnion
          fun m => (Finset.univ : Finset V).powersetCard m := by
      ext U
      simp only [Finset.mem_erase, Finset.mem_powerset, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard_univ]
      constructor
      · rintro ⟨hne, hsub⟩
        refine ⟨U.card, ?_, rfl⟩
        have hss : U ⊂ Finset.univ := hsub.ssubset_of_ne hne
        simpa using Finset.card_lt_card hss
      · rintro ⟨m, hlt, hcard⟩
        refine ⟨fun heq => ?_, Finset.subset_univ U⟩
        rw [heq] at hcard
        simp only [Finset.card_univ] at hcard
        omega
    rw [herase, Finset.sum_biUnion ?hdisj]
    case hdisj =>
      intro m₁ _ m₂ _ hne
      refine Finset.disjoint_left.mpr fun U hU₁ hU₂ => hne ?_
      rw [Finset.mem_powersetCard_univ] at hU₁ hU₂
      rw [← hU₁, ← hU₂]
    exact Finset.sum_congr rfl fun m _ => G.sum_coverTypeCount_induce_eq F m

variable {G H : SimpleGraph V}

/-- **Kocay's lemma, deck form: host cover counts are reconstructible.** For
every finite family of patterns, each on fewer vertices than the host,
same-deck graphs admit the same number of indexed coverings of their full
vertex set by induced copies of the patterns.

This strictly extends `SameDeck.subgraphCount_prod_eq`: the product of Kelly
counts is the *sum* of cover counts over all vertex subsets, and this theorem
pins the one summand (the full subset) that Kelly's Lemma cannot reach. It is
the entry point for the Tutte/Kocay extraction of spanning-structure counts
(disconnected spanning subgraphs, and ultimately the Hamiltonian count). -/
theorem SameDeck.coverTypeCount_eq (h : G.SameDeck H)
    (F : (i : ι) → SimpleGraph (W i))
    (hcard : ∀ i, Fintype.card (W i) < Fintype.card V) :
    coverTypeCount F G = coverTypeCount F H := by
  have hG := G.prod_subgraphCount_eq_coverTypeCount_add F
  have hH := H.prod_subgraphCount_eq_coverTypeCount_add F
  have hprod : (∏ i, (F i).subgraphCount G) = ∏ i, (F i).subgraphCount H :=
    h.subgraphCount_prod_eq F hcard
  have hproper :
      (∑ m ∈ Finset.range (Fintype.card V), ∑ q : GraphIsoClass m,
          (Quotient.out q).subgraphCount G * coverTypeCount F (Quotient.out q)) =
        ∑ m ∈ Finset.range (Fintype.card V), ∑ q : GraphIsoClass m,
          (Quotient.out q).subgraphCount H * coverTypeCount F (Quotient.out q) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [h.subgraphCount_eq (Quotient.out q) (by simpa using Finset.mem_range.mp hm)]
  omega

end

end SimpleGraph
