import Reconstruction.RegularReconstruction

/-!
# Value-Separated Vertices are Rigid — the Telescoping Argument

Discovery B of the symmetry-breaking programme
(`research/attacks/symmetry-breaking.md`): call a vertex `v`
**value-separated** if no non-neighbour of `v` shares a card-degree with a
neighbour of `v`. Then `v` is rigid, hence any graph possessing such a
vertex is reconstructible — a strict extension of the regular case (where
every card-degree class is trivially all-neighbours or all-non-neighbours).

The proof is the telescoping argument: for each card-degree value `t`, the
counts of neighbours (`nbrCount`), non-neighbours (`nonNbrCount`), the full
class (`classCount`), and the `G`-degree classes (`fullDegCount`) satisfy

* `classCount t = nbrCount t + nonNbrCount t` (partition);
* `fullDegCount t = shiftNbrCount t + nonNbrCount t` where
  `shiftNbrCount (t+1) = nbrCount t`, `shiftNbrCount 0 = 0` (the deficit
  stamp, pointwise);

and the deck matches `classCount` (via the card isomorphism) and
`fullDegCount` (via the degree multiset and the deleted degree) across the
two graphs. Induction on `t` then forces the neighbour counts to agree
classwise, and value-separation upgrades classwise agreement to the
pointwise link condition.

## Main results

* `SimpleGraph.ValueSeparated` — the separation predicate;
* `SimpleGraph.ValueSeparated.rigidVertex` — value-separated vertices are
  rigid;
* `SimpleGraph.nonempty_iso_of_valueSeparated` — **graphs with a
  value-separated vertex are reconstructible**.
-/

set_option autoImplicit false

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- `v` is **value-separated** if no non-neighbour shares a card-degree
value with a neighbour: every card-degree class of `G − v` is
all-neighbours or all-non-neighbours of `v`. -/
def ValueSeparated (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Prop :=
  ∀ x y : {w : V // w ≠ v}, ¬ G.Adj v ↑x → G.Adj v ↑y →
    (G.deleteVert v).degree x ≠ (G.deleteVert v).degree y

/-! ### Value-class counts on a card -/

section Counts

variable (G) (v : V)

/-- Number of neighbours of the deleted vertex with card-degree `t`. -/
private def nbrCount (t : ℕ) : ℕ :=
  ((Finset.univ : Finset {w : V // w ≠ v}).filter
    fun x : {w : V // w ≠ v} =>
      (G.deleteVert v).degree x = t ∧ G.Adj v ↑x).card

/-- Number of non-neighbours of the deleted vertex with card-degree `t`. -/
private def nonNbrCount (t : ℕ) : ℕ :=
  ((Finset.univ : Finset {w : V // w ≠ v}).filter
    fun x : {w : V // w ≠ v} =>
      (G.deleteVert v).degree x = t ∧ ¬ G.Adj v ↑x).card

/-- Size of the card-degree-`t` class. -/
private def classCount (t : ℕ) : ℕ :=
  ((Finset.univ : Finset {w : V // w ≠ v}).filter
    fun x : {w : V // w ≠ v} => (G.deleteVert v).degree x = t).card

/-- Number of card vertices whose **`G`-degree** is `t`. -/
private def fullDegCount (t : ℕ) : ℕ :=
  ((Finset.univ : Finset {w : V // w ≠ v}).filter
    fun x : {w : V // w ≠ v} => G.degree ↑x = t).card

/-- Number of neighbours whose card-degree shifts to `t` (i.e. with
`G`-degree `t`); empty at `t = 0`. -/
private def shiftNbrCount (t : ℕ) : ℕ :=
  ((Finset.univ : Finset {w : V // w ≠ v}).filter
    fun x : {w : V // w ≠ v} =>
      (G.deleteVert v).degree x + 1 = t ∧ G.Adj v ↑x).card

/-- Partition of a value class into neighbours and non-neighbours. -/
private theorem classCount_eq (t : ℕ) :
    classCount G v t = nbrCount G v t + nonNbrCount G v t := by
  unfold classCount nbrCount nonNbrCount
  rw [← Finset.filter_filter, ← Finset.filter_filter]
  exact (Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset {w : V // w ≠ v}).filter
      fun x : {w : V // w ≠ v} => (G.deleteVert v).degree x = t)
    (p := fun x : {w : V // w ≠ v} => G.Adj v ↑x)).symm

/-- The deficit stamp, classwise: the `G`-degree-`t` class among card
vertices consists of the shifted neighbours and the same-value
non-neighbours. -/
private theorem fullDegCount_eq (t : ℕ) :
    fullDegCount G v t = shiftNbrCount G v t + nonNbrCount G v t := by
  unfold fullDegCount shiftNbrCount nonNbrCount
  rw [← Finset.filter_filter, ← Finset.filter_filter]
  rw [← Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset {w : V // w ≠ v}).filter
      fun x : {w : V // w ≠ v} => G.degree ↑x = t)
    (p := fun x : {w : V // w ≠ v} => G.Adj v ↑x)]
  congr 1
  · -- neighbours: `G`-degree `t` ⟺ card-degree `+ 1 = t`
    rw [Finset.filter_filter, Finset.filter_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := degree_deleteVert_add_one_of_adj (G := G) h2
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      have h3 := degree_deleteVert_add_one_of_adj (G := G) h2
      exact ⟨by omega, h2⟩
  · -- non-neighbours: `G`-degree `t` ⟺ card-degree `= t`
    rw [Finset.filter_filter, Finset.filter_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := degree_deleteVert_of_not_adj (G := G) h2
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      have h3 := degree_deleteVert_of_not_adj (G := G) h2
      exact ⟨by omega, h2⟩

private theorem shiftNbrCount_zero : shiftNbrCount G v 0 = 0 := by
  unfold shiftNbrCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x - ⟨h1, -⟩
  omega

private theorem shiftNbrCount_succ (t : ℕ) :
    shiftNbrCount G v (t + 1) = nbrCount G v t := by
  unfold shiftNbrCount nbrCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

end Counts

/-! ### Transfer across a degree-matched card isomorphism -/

section Transfer

variable {v w : V} (ψ : G.deleteVert v ≃g H.deleteVert w)

include ψ

/-- The card isomorphism matches the card-degree classes. -/
private theorem classCount_transfer (t : ℕ) :
    classCount G v t = classCount H w t := by
  unfold classCount
  refine Finset.card_bij' (fun x _ => ψ x) (fun y _ => ψ.symm y) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, by rw [iso_degree_eq ψ x]; exact hx.2⟩
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [iso_degree_eq ψ.symm y]
    exact hy.2
  · intro x _
    exact ψ.symm_apply_apply x
  · intro y _
    exact ψ.apply_symm_apply y

omit ψ in
/-- The degree multiset and the deleted degree match the `G`-degree classes
among card vertices. -/
private theorem fullDegCount_transfer
    (hmul : G.degreeMultiset = H.degreeMultiset)
    (hdeg : G.degree v = H.degree w) (t : ℕ) :
    fullDegCount G v t = fullDegCount H w t := by
  have key : ∀ (K : SimpleGraph V) (inst : DecidableRel K.Adj) (u : V),
      fullDegCount K u t + (if K.degree u = t then 1 else 0) =
        Multiset.count t K.degreeMultiset := by
    intro K _ u
    have hbridge : Multiset.count t K.degreeMultiset =
        ((Finset.univ : Finset V).filter fun x : V => K.degree x = t).card := by
      rw [degreeMultiset, Multiset.count_map]
      have hflip : ((Finset.univ : Finset V).filter
          fun x : V => K.degree x = t).val =
          Multiset.filter (fun a : V => t = K.degree a) Finset.univ.val := by
        rw [Finset.filter_val]
        exact Multiset.filter_congr fun a _ => eq_comm
      rw [← hflip]
      rfl
    rw [hbridge]
    have himg : Finset.image Subtype.val
        ((Finset.univ : Finset {z : V // z ≠ u}).filter
          fun x : {z : V // z ≠ u} => K.degree ↑x = t) =
        ((Finset.univ : Finset V).filter fun x : V => K.degree x = t).erase u := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_erase,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, hz⟩
      · rintro ⟨hyu, hdy⟩
        exact ⟨⟨y, hyu⟩, hdy, rfl⟩
    have hcard : fullDegCount K u t =
        (((Finset.univ : Finset V).filter fun x : V => K.degree x = t).erase u).card := by
      rw [fullDegCount, ← himg,
        Finset.card_image_of_injective _ Subtype.val_injective]
    rw [hcard]
    by_cases hu : K.degree u = t
    · rw [if_pos hu]
      exact Finset.card_erase_add_one
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩)
    · rw [if_neg hu, Finset.erase_eq_self.mpr
        (show u ∉ (Finset.univ : Finset V).filter (fun x : V => K.degree x = t)
          from fun hmem => hu (Finset.mem_filter.mp hmem).2)]
      omega
  have hG := key G ‹_› v
  have hH := key H ‹_› w
  rw [hmul] at hG
  rw [hdeg] at hG
  omega

/-- **The telescoping step**: the neighbour and non-neighbour class counts
agree across the two cards, by induction on the card-degree value. -/
private theorem nbr_nonNbr_transfer
    (hmul : G.degreeMultiset = H.degreeMultiset)
    (hdeg : G.degree v = H.degree w) (t : ℕ) :
    nbrCount G v t = nbrCount H w t ∧
      nonNbrCount G v t = nonNbrCount H w t := by
  induction t with
  | zero =>
    have h1 := fullDegCount_eq G v 0
    have h2 := fullDegCount_eq H w 0
    have h3 := shiftNbrCount_zero G v
    have h4 := shiftNbrCount_zero H w
    have h5 := classCount_eq G v 0
    have h6 := classCount_eq H w 0
    have h7 := fullDegCount_transfer (G := G) (H := H) (v := v) (w := w) hmul hdeg 0
    have h8 := classCount_transfer ψ 0
    omega
  | succ t ih =>
    have h1 := fullDegCount_eq G v (t + 1)
    have h2 := fullDegCount_eq H w (t + 1)
    have h3 := shiftNbrCount_succ G v t
    have h4 := shiftNbrCount_succ H w t
    have h5 := classCount_eq G v (t + 1)
    have h6 := classCount_eq H w (t + 1)
    have h7 := fullDegCount_transfer (G := G) (H := H) (v := v) (w := w) hmul hdeg (t + 1)
    have h8 := classCount_transfer ψ (t + 1)
    obtain ⟨ih1, ih2⟩ := ih
    omega

end Transfer

/-! ### Value-separated vertices are rigid -/

/-- **Value-separated vertices are rigid** (Discovery B): classwise neighbour
counts are forced by the telescoping recurrence, and value-separation makes
classwise agreement pointwise — the identity correction works. -/
theorem ValueSeparated.rigidVertex {v : V} (hsep : G.ValueSeparated v) :
    G.RigidVertex v := by
  classical
  intro H hH w ψ hmul hdeg
  refine ⟨RelIso.refl _, fun x => ?_⟩
  simp only [RelIso.refl_apply]
  have key := nbr_nonNbr_transfer ψ hmul hdeg ((G.deleteVert v).degree x)
  unfold nbrCount nonNbrCount at key
  have hdx : (H.deleteVert w).degree (ψ x) = (G.deleteVert v).degree x :=
    iso_degree_eq ψ x
  constructor
  · intro hadj
    by_contra hno
    have hpos : 0 < ((Finset.univ : Finset {u : V // u ≠ w}).filter
        fun y : {u : V // u ≠ w} =>
          (H.deleteVert w).degree y = (G.deleteVert v).degree x ∧
            ¬ H.Adj w ↑y).card :=
      Finset.card_pos.mpr ⟨ψ x, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hdx, hno⟩⟩
    rw [← key.2] at hpos
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hz
    exact hsep z x hz.2.2 hadj hz.2.1
  · intro hHadj
    by_contra hno
    have hpos : 0 < ((Finset.univ : Finset {u : V // u ≠ w}).filter
        fun y : {u : V // u ≠ w} =>
          (H.deleteVert w).degree y = (G.deleteVert v).degree x ∧
            H.Adj w ↑y).card :=
      Finset.card_pos.mpr ⟨ψ x, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hdx, hHadj⟩⟩
    rw [← key.1] at hpos
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hy
    exact hsep x y hno hy.2.2 hy.2.1.symm

omit [DecidableRel H.Adj] in
/-- **Graphs with a value-separated vertex are reconstructible** — Discovery
B combined with the rigid-card criterion. Strictly extends
`nonempty_iso_of_regular`. -/
theorem nonempty_iso_of_valueSeparated {v : V} (hsep : G.ValueSeparated v)
    (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) :
    Nonempty (G ≃g H) :=
  nonempty_iso_of_rigidVertex hsep.rigidVertex h hV

/-- Every vertex of a regular graph is value-separated: non-neighbours keep
card-degree `d`, neighbours drop to `d − 1`. -/
theorem IsRegularOfDegree.valueSeparated {d : ℕ}
    (hreg : G.IsRegularOfDegree d) (v : V) : G.ValueSeparated v := by
  intro x y hx hy
  have h1 := degree_deleteVert_of_not_adj (G := G) hx
  have h2 := degree_deleteVert_add_one_of_adj (G := G) hy
  rw [hreg ↑x] at h1
  rw [hreg ↑y] at h2
  omega

end

end SimpleGraph
