import Reconstruction.HomCount

/-!
# Placement Tuples and the Disconnected-Spanning Staged Target

The Tutte/Kocay extraction (strategy note R1, checklist §4) proceeds through
**tuples of placements**: for a family `D i` of patterns, a tuple of injective
homomorphisms `D i →g G`. This module provides the tuple layer over
`Reconstruction.HomCount`:

* `injTupleCount` — the number of placement tuples, with the product formula
  `injTupleCount_eq_prod` and its deck-invariance `SameDeck.injTupleCount_eq`
  (each pattern on `< |V|` vertices);
* `DisjointSpanningTupleCountReconstructible` — the staged target: the number
  of **pairwise-vertex-disjoint spanning** placement tuples is
  deck-determined. When the pattern sizes sum to exactly `|V|`, a spanning
  tuple is automatically pairwise disjoint, and a pairwise-disjoint tuple of
  the components of a disconnected graph `D` is exactly an injective
  homomorphism placement of `D` itself — this is the vertex-disjointness
  collapse that makes all disconnected-spanning-subgraph counts
  reconstructible in one step, the engine of Tutte's theorem.

## References

* Kocay, W. L. (1981). "Some new methods in reconstruction theory".
* Tutte, W. T. (1979). "All the king's horses".
-/

set_option autoImplicit false

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {W : ι → Type*} [∀ i, Fintype (W i)]

/-- The number of **placement tuples** of the family `D`: independent choices
of an injective homomorphism copy of each pattern. -/
def injTupleCount (D : (i : ι) → SimpleGraph (W i)) (G : SimpleGraph V) : ℕ :=
  Fintype.card (∀ i, {f : D i →g G // Function.Injective f})

/-- Placement tuples are counted by the product of the individual placement
counts. -/
theorem injTupleCount_eq_prod (D : (i : ι) → SimpleGraph (W i))
    (G : SimpleGraph V) :
    injTupleCount D G = ∏ i, injHomCount (D i) G := by
  rw [injTupleCount, Fintype.card_pi]
  rfl

variable {G H : SimpleGraph V}

/-- **Placement-tuple counts are reconstructible** for pattern families on
`< |V|` vertices: immediate from `SameDeck.injHomCount_eq` and the product
formula. -/
theorem SameDeck.injTupleCount_eq (h : G.SameDeck H)
    (D : (i : ι) → SimpleGraph (W i))
    (hcard : ∀ i, Fintype.card (W i) < Fintype.card V) :
    injTupleCount D G = injTupleCount D H := by
  rw [injTupleCount_eq_prod, injTupleCount_eq_prod]
  exact Finset.prod_congr rfl fun i _ => h.injHomCount_eq (D i) (hcard i)

/-! ### The vertex-disjointness collapse -/

omit [Fintype V] [DecidableEq ι] in
/-- **The collapse, abstractly.** A family of finsets whose cardinalities sum
to `|V|` covers the whole vertex set **iff** it is pairwise disjoint: the
union of the family has at most `∑ |r i|` elements, with equality exactly in
the disjoint case, so at total size `|V|` covering and disjointness coincide.
All arithmetic is kept additive so that `omega` discharges it. -/
theorem pairwise_disjoint_iff_biUnion_eq_univ [Fintype V]
    (r : ι → Finset V) (hsum : ∑ i, (r i).card = Fintype.card V) :
    (Pairwise fun i j => Disjoint (r i) (r j)) ↔
      Finset.univ.biUnion r = Finset.univ := by
  constructor
  · intro hdisj
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_biUnion fun i _ j _ hij => hdisj hij]
    exact hsum
  · intro hcover
    by_contra hnd
    rw [Pairwise] at hnd
    push_neg at hnd
    obtain ⟨i, j, hij, hndisj⟩ := hnd
    obtain ⟨x, hx⟩ := Finset.not_disjoint_iff_nonempty_inter.mp hndisj
    -- peel `i` and `j` off the index set
    have hji : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    have hsplit₁ : Finset.univ.biUnion r = r i ∪ (Finset.univ.erase i).biUnion r := by
      conv_lhs => rw [← Finset.insert_erase (Finset.mem_univ i), Finset.biUnion_insert]
    have hsplit₂ : (Finset.univ.erase i).biUnion r =
        r j ∪ ((Finset.univ.erase i).erase j).biUnion r := by
      conv_lhs => rw [← Finset.insert_erase hji, Finset.biUnion_insert]
    -- additive bookkeeping
    have hcard₁ : (r i ∪ r j).card + (r i ∩ r j).card = (r i).card + (r j).card :=
      Finset.card_union_add_card_inter _ _
    have hcard₂ : 1 ≤ (r i ∩ r j).card := Finset.card_pos.mpr ⟨x, hx⟩
    have hcard₃ : (((Finset.univ.erase i).erase j).biUnion r).card ≤
        ∑ k ∈ (Finset.univ.erase i).erase j, (r k).card :=
      Finset.card_biUnion_le
    have hsum₁ : (r i).card + ∑ k ∈ Finset.univ.erase i, (r k).card =
        Fintype.card V := by
      rw [Finset.add_sum_erase Finset.univ (fun k => (r k).card) (Finset.mem_univ i)]
      exact hsum
    have hsum₂ : (r j).card + ∑ k ∈ (Finset.univ.erase i).erase j, (r k).card =
        ∑ k ∈ Finset.univ.erase i, (r k).card := by
      rw [Finset.add_sum_erase (Finset.univ.erase i) (fun k => (r k).card) hji]
    have hbig : (Finset.univ.biUnion r).card ≤
        (r i ∪ r j).card + (((Finset.univ.erase i).erase j).biUnion r).card := by
      calc (Finset.univ.biUnion r).card
          = (r i ∪ (r j ∪ ((Finset.univ.erase i).erase j).biUnion r)).card := by
            rw [hsplit₁, hsplit₂]
        _ = ((r i ∪ r j) ∪ ((Finset.univ.erase i).erase j).biUnion r).card := by
            rw [Finset.union_assoc]
        _ ≤ _ := Finset.card_union_le _ _
    have hn : (Finset.univ.biUnion r).card = Fintype.card V := by
      rw [hcover, Finset.card_univ]
    omega

omit [DecidableEq ι] in
/-- **The vertex-disjointness collapse for placement tuples.** When the
pattern sizes sum to exactly `|V|`, a placement tuple is pairwise
vertex-disjoint **iff** its images cover every vertex. This closes the
combinatorial half of `DisjointSpanningTupleCountReconstructible`: the
disjoint-tuple count *is* the spanning-tuple count, whose deck-invariance is
the remaining (regrouping) half. -/
theorem tuple_pairwise_disjoint_iff_spanning
    (D : (i : ι) → SimpleGraph (W i))
    (hsum : (∑ i, Fintype.card (W i)) = Fintype.card V)
    (t : ∀ i, {f : D i →g G // Function.Injective f}) :
    (Pairwise fun i j => Disjoint (Set.range ⇑(t i).1) (Set.range ⇑(t j).1)) ↔
      Finset.univ.biUnion (fun i => Finset.image ⇑(t i).1 Finset.univ) =
        Finset.univ := by
  classical
  have hrange : ∀ i, Set.range ⇑(t i).1 =
      ↑(Finset.image ⇑(t i).1 Finset.univ) := by
    intro i
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hpair : (Pairwise fun i j =>
      Disjoint (Set.range ⇑(t i).1) (Set.range ⇑(t j).1)) ↔
      Pairwise fun i j => Disjoint (Finset.image ⇑(t i).1 Finset.univ)
        (Finset.image ⇑(t j).1 Finset.univ) := by
    constructor <;> intro hp i j hij
    · rw [← Finset.disjoint_coe, ← hrange i, ← hrange j]
      exact hp hij
    · rw [hrange i, hrange j, Finset.disjoint_coe]
      exact hp hij
  rw [hpair]
  refine pairwise_disjoint_iff_biUnion_eq_univ _ ?_
  calc ∑ i, (Finset.image ⇑(t i).1 Finset.univ).card
      = ∑ i, Fintype.card (W i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.card_image_of_injective _ (t i).2, Finset.card_univ]
    _ = Fintype.card V := hsum

end

/-- **Staged target (the vertex-disjointness collapse).** For a pattern
family whose sizes sum to exactly `|V|` (each pattern smaller than the host),
the number of pairwise-vertex-disjoint placement tuples — equivalently, of
*spanning* placement tuples, since total size `|V|` forces disjoint images to
cover and covering images to be disjoint — is deck-reconstructible.

Taking the family to be the components of a disconnected graph `D` on `|V|`
vertices, a pairwise-disjoint tuple is exactly an injective placement of `D`
itself, so this target yields **Kocay's theorem that all disconnected
spanning subgraph counts are reconstructible** — the engine of Tutte's
characteristic-polynomial and Hamiltonian-count reconstruction. The intended
proof: partition all tuples (`SameDeck.injTupleCount_eq`) by the union of
their images and regroup by `GraphIsoClass` as in `Reconstruction.KocayHost`;
the full-vertex-set fiber is this count. Stated as a `Prop`-valued definition
per the project's staged-target convention. -/
def DisjointSpanningTupleCountReconstructible : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {W : ι → Type} [∀ i, Fintype (W i)]
    (D : (i : ι) → SimpleGraph (W i)) (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj],
    (∀ i, Fintype.card (W i) < Fintype.card V) →
    (∑ i, Fintype.card (W i)) = Fintype.card V →
    3 ≤ Fintype.card V → G.SameDeck H →
      Nat.card {t : ∀ i, {f : D i →g G // Function.Injective f} //
          Pairwise fun i j => Disjoint (Set.range ⇑(t i).1) (Set.range ⇑(t j).1)} =
        Nat.card {t : ∀ i, {f : D i →g H // Function.Injective f} //
          Pairwise fun i j => Disjoint (Set.range ⇑(t i).1) (Set.range ⇑(t j).1)}

end SimpleGraph
