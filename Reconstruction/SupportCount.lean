import Reconstruction.TopTrace
import Reconstruction.KellyLemma

/-!
# Proper-Support Closed-Walk Counts are Reconstructible

This module closes the **proper-support half** of the top-trace programme from
`Reconstruction.TopTrace`. The trace of `A^k` counts rooted closed walks of
length `k`; the walks whose support misses at least one vertex are confined to
a proper induced subgraph, and Kelly's Lemma reconstructs how many induced
subgraphs of each isomorphism type `G` has. Grouping exact supports by
isomorphism type therefore makes the whole proper-support count a function of
deck data:

* a rooted closed walk with support exactly `U` *is* a full-support rooted
  closed walk of the induced graph `G[U]`
  (`exactSupportClosedWalkCount_eq_fullSupport_induce`);
* the full-support count is a graph-isomorphism invariant
  (`fullSupportClosedWalkCount_eq_of_iso`);
* summing over all `m`-element subsets and regrouping by the isomorphism class
  of the induced subgraph turns the sum into
  `∑ classes q, s(q, G) * fullCount(q)` (`sum_fullSupport_induce_eq`), where
  `s(q, G)` is the Kelly subgraph count;
* Kelly's Lemma (`SameDeck.subgraphCount_eq`) matches `s(q, G) = s(q, H)`
  for every class on `m < |V|` vertices, hence
  `SameDeck.properSupportClosedWalkCount_eq`.

Combined with `charPoly_coeff_zero_eq_of_support_counts_eq`, the remaining
content of the constant-coefficient (Tutte) reconstruction is exactly the
full-support count — the Hamiltonian-cycle sector.

## References

* Kelly, P. J. (1942). "On isometric transformations".
* Tutte, W. T. (1979). "All the king's horses".
* Kocay, W. L. (1981). "Some new methods in reconstruction theory".
-/

set_option autoImplicit false

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### List/Finset support bookkeeping -/

private theorem list_toFinset_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (l : List α) : (l.map f).toFinset = l.toFinset.image f := by
  ext x; simp

omit [Fintype V] in
private theorem univ_image_val (U : Finset V) :
    (Finset.univ : Finset ↥(↑U : Set V)).image Subtype.val = U := by
  ext x; simp

omit [Fintype V] [DecidableEq V] in
private theorem card_coe_set (U : Finset V) :
    Fintype.card ↥(↑U : Set V) = U.card := by
  rw [Fintype.card_congr (Equiv.subtypeEquivRight fun x => Finset.mem_coe)]
  exact Fintype.card_coe U

omit [Fintype V] [DecidableEq V] in
/-- The length of a walk restricted to an induced subgraph. Mathlib has
`Walk.map_induce` but no length lemma; we recover it by mapping back. -/
private theorem length_induce {G : SimpleGraph V} {s : Set V} {u v : V}
    (p : G.Walk u v) (hp : ∀ x ∈ p.support, x ∈ s) :
    (p.induce s hp).length = p.length := by
  conv_rhs => rw [← Walk.map_induce p hp]
  rw [Walk.length_map]

/-! ### The full-support count is an isomorphism invariant -/

section IsoInvariance

variable {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]
variable {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
variable [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]

private theorem fullSupport_count_le (φ : G₁ ≃g G₂) (k : ℕ) :
    G₁.fullSupportClosedWalkCount k ≤ G₂.fullSupportClosedWalkCount k := by
  have hinj : Function.Injective (⇑φ.toHom) := fun a b hab => φ.toEquiv.injective hab
  unfold fullSupportClosedWalkCount
  refine Finset.card_le_card_of_injOn
    (fun wp => ⟨φ wp.1, ⟨wp.2.1.map φ.toHom, by rw [Walk.length_map]; exact wp.2.2⟩⟩) ?_ ?_
  · rintro ⟨v, p, hp⟩ hwp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hwp ⊢
    rw [Walk.support_map, list_toFinset_map,
      Finset.card_image_of_injective _ hinj, hwp]
    exact Fintype.card_congr φ.toEquiv
  · rintro ⟨v, p, hp⟩ - ⟨v', p', hp'⟩ - heq
    simp only [Sigma.mk.injEq] at heq
    obtain ⟨hv, hsnd⟩ := heq
    have hvv : v = v' := φ.toEquiv.injective hv
    subst hvv
    rw [heq_iff_eq, Subtype.mk.injEq] at hsnd
    have hpp : p = p' := Walk.map_injective_of_injective hinj v v hsnd
    subst hpp
    rfl

/-- The full-support rooted-closed-walk count is a graph-isomorphism
invariant. -/
theorem fullSupportClosedWalkCount_eq_of_iso (φ : G₁ ≃g G₂) (k : ℕ) :
    G₁.fullSupportClosedWalkCount k = G₂.fullSupportClosedWalkCount k :=
  le_antisymm (fullSupport_count_le φ k) (fullSupport_count_le φ.symm k)

end IsoInvariance

/-! ### Exact-support walks are full-support walks of the induced subgraph -/

section ExactSupport

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A rooted closed walk of `G` with support exactly `U` is the same thing as
a full-support rooted closed walk of the induced subgraph `G[U]`. The
counting map pushes a walk of `G[U]` forward along the inclusion
(`Walk.map`); surjectivity onto the exact-support walks is `Walk.induce` +
`Walk.map_induce`. -/
theorem exactSupportClosedWalkCount_eq_fullSupport_induce (k : ℕ) (U : Finset V) :
    G.exactSupportClosedWalkCount k U =
      (G.induce (↑U : Set V)).fullSupportClosedWalkCount k := by
  have hval : Function.Injective
      (⇑(Embedding.induce (↑U : Set V) : G.induce (↑U : Set V) ↪g G).toHom) :=
    fun a b hab => Subtype.ext hab
  unfold exactSupportClosedWalkCount fullSupportClosedWalkCount
  -- the total counting map: push a walk of `G[U]` forward along the inclusion
  refine le_antisymm (Finset.card_le_card_of_surjOn
      (fun wq => ⟨wq.1.1, ⟨wq.2.1.map (Embedding.induce (↑U : Set V)).toHom,
        by rw [Walk.length_map]; exact wq.2.2⟩⟩) ?_)
    (Finset.card_le_card_of_injOn
      (fun wq => ⟨wq.1.1, ⟨wq.2.1.map (Embedding.induce (↑U : Set V)).toHom,
        by rw [Walk.length_map]; exact wq.2.2⟩⟩) ?_ ?_)
  · -- surjectivity onto exact-support walks: restrict with `Walk.induce`
    rintro ⟨v, p, hp⟩ hwp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hwp
    have hmem : ∀ x ∈ p.support, x ∈ (↑U : Set V) := by
      intro x hx
      have hx' : x ∈ p.support.toFinset := List.mem_toFinset.mpr hx
      rw [hwp] at hx'
      exact hx'
    have hsupp : ((p.induce (↑U : Set V) hmem).support.map
        (⇑(Embedding.induce (↑U : Set V) : G.induce (↑U : Set V) ↪g G).toHom)) =
          p.support := by
      rw [← Walk.support_map, Walk.map_induce]
    refine ⟨⟨⟨v, hmem v p.start_mem_support⟩,
      ⟨p.induce (↑U : Set V) hmem, by rw [length_induce]; exact hp⟩⟩, ?_, ?_⟩
    · -- the restricted walk has full support in `G[U]`
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
      have hcard : (p.induce (↑U : Set V) hmem).support.toFinset.card
          = p.support.toFinset.card := by
        rw [← hsupp, list_toFinset_map, Finset.card_image_of_injective _ hval]
      rw [hcard, hwp, card_coe_set]
    · -- pushing forward recovers the original walk
      simp only
      congr 1
      exact Subtype.ext (Walk.map_induce p hmem)
  · -- the pushforward of a full-support walk has support exactly `U`
    rintro ⟨a, q, hq⟩ hwq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hwq ⊢
    rw [Walk.support_map, list_toFinset_map]
    have huniv : q.support.toFinset = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hwq, card_coe_set])
    rw [huniv]
    exact univ_image_val U
  · -- injectivity of the pushforward
    rintro ⟨a, q, hq⟩ - ⟨a', q', hq'⟩ - heq
    simp only [Sigma.mk.injEq] at heq
    obtain ⟨ha, hsnd⟩ := heq
    have haa : a = a' := Subtype.ext ha
    subst haa
    rw [heq_iff_eq, Subtype.mk.injEq] at hsnd
    have hqq : q = q' := Walk.map_injective_of_injective hval a a hsnd
    subst hqq
    rfl

end ExactSupport

/-! ### Isomorphism classes of graphs on `m` labelled vertices -/

/-- Graph isomorphism, as a setoid on the simple graphs over `Fin m`. -/
def graphIsoSetoid (m : ℕ) : Setoid (SimpleGraph (Fin m)) where
  r F F' := Nonempty (F ≃g F')
  iseqv := ⟨fun _ => ⟨RelIso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ => ⟨e.trans e'⟩⟩

attribute [local instance] graphIsoSetoid

/-- Isomorphism classes of simple graphs on `m` labelled vertices. The
proper-support regrouping sums over this (finite) index. -/
def GraphIsoClass (m : ℕ) : Type :=
  Quotient (graphIsoSetoid m)

noncomputable instance (m : ℕ) : Fintype (GraphIsoClass m) :=
  @Quotient.fintype (SimpleGraph (Fin m)) _ (graphIsoSetoid m)
    fun _ _ => Classical.propDecidable _

/-- Two graphs on `Fin m` represent the same class iff they are isomorphic. -/
theorem graphIsoClass_mk_eq_mk {m : ℕ} {F F' : SimpleGraph (Fin m)} :
    (⟦F⟧ : GraphIsoClass m) = ⟦F'⟧ ↔ Nonempty (F ≃g F') :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

variable (G : SimpleGraph V)

/-- The graph induced on an `m`-element vertex subset, transported to `Fin m`
along an arbitrary equivalence. Only its isomorphism class is ever used. -/
def inducedFinGraph {m : ℕ} (U : Finset V) (h : U.card = m) : SimpleGraph (Fin m) :=
  (G.induce (↑U : Set V)).comap
    ⇑((finCongr (h ▸ card_coe_set U : Fintype.card ↥(↑U : Set V) = m)).symm.trans
      (Fintype.equivFin ↥(↑U : Set V)).symm)

/-- The transported graph is isomorphic to the induced subgraph it came from. -/
def inducedFinGraphIso {m : ℕ} (U : Finset V) (h : U.card = m) :
    G.inducedFinGraph U h ≃g G.induce (↑U : Set V) :=
  ⟨(finCongr (h ▸ card_coe_set U : Fintype.card ↥(↑U : Set V) = m)).symm.trans
      (Fintype.equivFin ↥(↑U : Set V)).symm, Iff.rfl⟩

/-- The isomorphism class of the subgraph induced on `U`, as a point of
`GraphIsoClass m` (junk value if `U` does not have `m` elements). -/
def inducedIsoClass (m : ℕ) (U : Finset V) : GraphIsoClass m :=
  if h : U.card = m then ⟦G.inducedFinGraph U h⟧ else ⟦⊥⟧

omit [DecidableEq V] in
/-- The fiber of `inducedIsoClass` over a class `q` is exactly Kelly's
`copyFinset` of any representative of `q`: the `m`-subsets whose induced
subgraph realizes the class. -/
theorem filter_inducedIsoClass_eq_copyFinset (m : ℕ) (q : GraphIsoClass m) :
    (((Finset.univ : Finset V).powersetCard m).filter
        fun U => G.inducedIsoClass m U = q) =
      (Quotient.out q).copyFinset G := by
  ext U
  simp only [Finset.mem_filter, Finset.mem_powersetCard_univ, mem_copyFinset,
    Fintype.card_fin]
  constructor
  · rintro ⟨hcard, hclass⟩
    refine ⟨hcard, ?_⟩
    rw [inducedIsoClass, dif_pos hcard, ← Quotient.out_eq q,
      graphIsoClass_mk_eq_mk] at hclass
    obtain ⟨e⟩ := hclass
    exact ⟨(G.inducedFinGraphIso U hcard).symm.trans e⟩
  · rintro ⟨hcard, ⟨e⟩⟩
    refine ⟨hcard, ?_⟩
    rw [inducedIsoClass, dif_pos hcard, ← Quotient.out_eq q,
      graphIsoClass_mk_eq_mk]
    exact ⟨(G.inducedFinGraphIso U hcard).trans e⟩

variable [DecidableRel G.Adj]

/-- **Regrouping by isomorphism class.** The total number of full-support
rooted closed walks over all `m`-element induced subgraphs is the sum, over
isomorphism classes `q` of graphs on `m` vertices, of the Kelly subgraph count
of `q` times the full-support walk count of `q`. This is the bridge from walk
counts to deck-reconstructible data. -/
theorem sum_fullSupport_induce_eq (k m : ℕ) :
    ∑ U ∈ (Finset.univ : Finset V).powersetCard m,
        (G.induce (↑U : Set V)).fullSupportClosedWalkCount k =
      ∑ q : GraphIsoClass m,
        (Quotient.out q).subgraphCount G *
          (Quotient.out q).fullSupportClosedWalkCount k := by
  rw [← Finset.sum_fiberwise ((Finset.univ : Finset V).powersetCard m)
    (G.inducedIsoClass m)
    fun U => (G.induce (↑U : Set V)).fullSupportClosedWalkCount k]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [G.filter_inducedIsoClass_eq_copyFinset m q]
  have hbody : ∀ U ∈ (Quotient.out q).copyFinset G,
      (G.induce (↑U : Set V)).fullSupportClosedWalkCount k =
        (Quotient.out q).fullSupportClosedWalkCount k := by
    intro U hU
    obtain ⟨e⟩ := ((mem_copyFinset _ _ _).mp hU).2
    exact fullSupportClosedWalkCount_eq_of_iso e k
  rw [Finset.sum_congr rfl hbody, Finset.sum_const, smul_eq_mul]
  rfl

/-- The proper-support closed-walk count, regrouped as a Kelly-weighted sum
over isomorphism classes of induced subgraphs of each size `m < |V|`. Every
term on the right is deck-reconstructible. -/
theorem properSupport_eq_sum_isoClasses (k : ℕ) :
    G.properSupportClosedWalkCount k =
      ∑ m ∈ Finset.range (Fintype.card V), ∑ q : GraphIsoClass m,
        (Quotient.out q).subgraphCount G *
          (Quotient.out q).fullSupportClosedWalkCount k := by
  rw [properSupportClosedWalkCount_eq_sum_exactSupport]
  have hsplit :
      (Finset.univ : Finset V).powerset.filter (fun U => U.card < Fintype.card V) =
        (Finset.range (Fintype.card V)).biUnion fun m => Finset.univ.powersetCard m := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard_univ]
    constructor
    · rintro ⟨-, hlt⟩
      exact ⟨U.card, hlt, rfl⟩
    · rintro ⟨m, hlt, hcard⟩
      exact ⟨Finset.subset_univ U, hcard ▸ hlt⟩
  rw [hsplit, Finset.sum_biUnion ?hdisj]
  case hdisj =>
    intro m₁ _ m₂ _ hne
    refine Finset.disjoint_left.mpr fun U hU₁ hU₂ => hne ?_
    rw [Finset.mem_powersetCard_univ] at hU₁ hU₂
    rw [← hU₁, ← hU₂]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← G.sum_fullSupport_induce_eq k m]
  exact Finset.sum_congr rfl fun U _ =>
    G.exactSupportClosedWalkCount_eq_fullSupport_induce k U

variable {G} in
/-- **The proper-support closed-walk count is reconstructible.** Same-deck
graphs have, for every length `k`, the same number of rooted closed `k`-walks
whose support misses at least one vertex: regroup by exact support, identify
each sector with full-support walks of the induced subgraph, group by
isomorphism class, and apply Kelly's Lemma to each class. This discharges the
proper-support hypothesis of
`SameDeck.charPoly_coeff_zero_eq_of_support_counts_eq`; the full-support
(Hamiltonian) sector is the only remaining obstacle to the constant
coefficient. -/
theorem SameDeck.properSupportClosedWalkCount_eq {H : SimpleGraph V}
    [DecidableRel H.Adj] (h : G.SameDeck H) (k : ℕ) :
    G.properSupportClosedWalkCount k = H.properSupportClosedWalkCount k := by
  rw [properSupport_eq_sum_isoClasses, properSupport_eq_sum_isoClasses]
  refine Finset.sum_congr rfl fun m hm => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [h.subgraphCount_eq (Quotient.out q) (by simpa using Finset.mem_range.mp hm)]

end

end SimpleGraph
