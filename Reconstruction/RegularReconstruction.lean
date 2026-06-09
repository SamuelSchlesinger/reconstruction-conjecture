import Reconstruction.Separator
import Reconstruction.Regular

/-!
# Regular Graphs are Reconstructible — Deficit Marking

**Regular graphs are reconstructible** (folklore, Kelly-era): if `G` is
`d`-regular, then in any card `G - v` the neighbours of the deleted vertex
are exactly the vertices of card-degree `≠ d` (they lost one edge; everyone
else still has degree `d`). The deleted vertex's attachment is therefore
*visible in the unlabeled card*, and the card isomorphism supplied by
`SameDeck` automatically preserves it, so `isoOfDeleteVertIso` reassembles a
global isomorphism.

This is the base case of the **deficit-marking mechanism** for canonical
symmetry breaking (see `research/attacks/symmetry-breaking.md`): deleting a
vertex *stamps its neighbourhood into the card* as a degree deficit. In a
regular graph the stamp is fully legible; the general programme is to
characterize when the stamp can be canonically decoded (marking rigidity)
in irregular graphs.

## Main results

* `SimpleGraph.degree_deleteVert` — the degree of a card vertex drops by one
  exactly on the deleted vertex's neighbourhood;
* `SimpleGraph.IsRegularOfDegree.adj_iff_degree_deleteVert_ne` — in a
  `d`-regular graph, adjacency to the deleted vertex is equivalent to
  card-degree `≠ d` (stated with `≠` so the edgeless case `d = 0` needs no
  special handling);
* `SimpleGraph.nonempty_iso_of_regular` — **regular graphs are
  reconstructible**.

## References

* Kelly, P. J. (1957). "A congruence theorem for trees" (the surrounding
  folklore); see also Bondy (1991), "A graph reconstructor's manual".
-/

set_option autoImplicit false

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Deleting `v` lowers the degree of exactly its neighbours by one: the
**deficit stamp** of the deleted vertex on its card. -/
theorem degree_deleteVert (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (x : {w : V // w ≠ v}) :
    (G.deleteVert v).degree x =
      if G.Adj ↑x v then G.degree ↑x - 1 else G.degree ↑x := by
  have himg : Finset.image Subtype.val ((G.deleteVert v).neighborFinset x) =
      (G.neighborFinset ↑x).erase v := by
    ext y
    simp only [Finset.mem_image, mem_neighborFinset, Finset.mem_erase]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
    · rintro ⟨hyv, hadj⟩
      exact ⟨⟨y, hyv⟩, hadj, rfl⟩
  have hcard : (G.deleteVert v).degree x = ((G.neighborFinset ↑x).erase v).card := by
    rw [← himg, Finset.card_image_of_injective _ Subtype.val_injective]
    rfl
  rw [hcard]
  by_cases hadj : G.Adj ↑x v
  · rw [if_pos hadj, Finset.card_erase_of_mem ((mem_neighborFinset G ↑x v).mpr hadj)]
    rfl
  · rw [if_neg hadj,
      Finset.erase_eq_self.mpr fun hmem => hadj ((mem_neighborFinset G ↑x v).mp hmem)]
    rfl

/-- Pointwise core of the shift recurrence (Discovery A,
`research/attacks/symmetry-breaking.md`): a **non-neighbour** of the deleted
vertex keeps its degree on the card. -/
theorem degree_deleteVert_of_not_adj {v : V} {x : {w : V // w ≠ v}}
    (h : ¬ G.Adj v ↑x) : (G.deleteVert v).degree x = G.degree ↑x := by
  rw [degree_deleteVert, if_neg fun hadj => h (G.adj_comm .. |>.mp hadj)]

/-- Pointwise core of the shift recurrence (Discovery A): a **neighbour** of
the deleted vertex drops exactly one degree on the card. Stated additively
(`card-degree + 1 = degree`) so no truncated subtraction appears. -/
theorem degree_deleteVert_add_one_of_adj {v : V} {x : {w : V // w ≠ v}}
    (h : G.Adj v ↑x) : (G.deleteVert v).degree x + 1 = G.degree ↑x := by
  have hadj : G.Adj ↑x v := (G.adj_comm ..).mp h
  have hpos : 0 < G.degree ↑x := by
    rw [← card_neighborSet_eq_degree]
    exact Fintype.card_pos_iff.mpr ⟨⟨v, hadj⟩⟩
  rw [degree_deleteVert, if_pos hadj]
  omega

/-- In a `d`-regular graph the deficit stamp is fully legible: a card vertex
is a neighbour of the deleted vertex **iff** its card-degree differs from
`d`. Stated with `≠ d` so that the edgeless case `d = 0` (where `d - 1`
would wrap) is automatic. -/
theorem IsRegularOfDegree.adj_iff_degree_deleteVert_ne {d : ℕ}
    (hreg : G.IsRegularOfDegree d) (v : V) (x : {w : V // w ≠ v}) :
    G.Adj ↑x v ↔ (G.deleteVert v).degree x ≠ d := by
  rw [degree_deleteVert]
  by_cases hadj : G.Adj ↑x v
  · have hd1 : 1 ≤ d := by
      have : 0 < G.degree ↑x := by
        rw [← card_neighborSet_eq_degree]
        exact Fintype.card_pos_iff.mpr ⟨⟨v, hadj⟩⟩
      rw [hreg ↑x] at this
      omega
    rw [if_pos hadj, hreg ↑x]
    simp only [hadj, true_iff]
    omega
  · rw [if_neg hadj, hreg ↑x]
    simp [hadj]

/-- Degree is invariant under graph isomorphisms (helper, by transporting
the neighbour set along the isomorphism). -/
private theorem iso_degree_eq {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    {A : SimpleGraph V₁} {B : SimpleGraph V₂}
    [DecidableRel A.Adj] [DecidableRel B.Adj]
    (φ : A ≃g B) (a : V₁) : B.degree (φ a) = A.degree a := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  refine Fintype.card_congr
    ⟨fun y => ⟨φ.symm ↑y, φ.map_rel_iff.mp (by rw [φ.apply_symm_apply]; exact y.2)⟩,
     fun y => ⟨φ ↑y, φ.map_rel_iff.mpr y.2⟩, fun y => ?_, fun y => ?_⟩
  · exact Subtype.ext (φ.apply_symm_apply ↑y)
  · exact Subtype.ext (φ.symm_apply_apply ↑y)

/-! ### The rigid-card criterion -/

/-- A vertex `v` of `G` is **rigid** if every card isomorphism onto a card of
a graph with the same degree data can be corrected by a card automorphism so
that it respects the deleted vertices' attachments. Rigidity says the
neighbour-marking of the card is canonical up to card automorphism — the
symmetry-breaking property of the deficit-marking programme
(`research/attacks/symmetry-breaking.md`). -/
def RigidVertex (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Prop :=
  ∀ (H : SimpleGraph V) [DecidableRel H.Adj] (w : V)
    (ψ : G.deleteVert v ≃g H.deleteVert w),
    G.degreeMultiset = H.degreeMultiset →
    G.degree v = H.degree w →
    ∃ α : G.deleteVert v ≃g G.deleteVert v,
      ∀ x : {y : V // y ≠ v}, G.Adj v ↑x ↔ H.Adj w ↑(ψ (α x))

omit [DecidableEq V] [DecidableRel H.Adj] in
/-- **The rigid-card criterion: one rigid vertex suffices.** If `G` has a
rigid vertex, then any graph with the same deck is isomorphic to `G`: the
deck supplies a card isomorphism with matching degree data (degree multisets
and the deleted degree are reconstructible), rigidity corrects it to respect
the attachments, and `isoOfDeleteVertIso` reassembles the global
isomorphism. -/
theorem nonempty_iso_of_rigidVertex {v : V}
    (hrig : G.RigidVertex v) (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) :
    Nonempty (G ≃g H) := by
  classical
  have hmul : G.degreeMultiset = H.degreeMultiset := h.degreeMultiset_eq hV
  have he : G.edgeFinset.card = H.edgeFinset.card := h.card_edgeFinset_eq hV
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨ψ⟩ := hσ v
  have hdeg : G.degree v = H.degree (σ v) :=
    degree_eq_of_card_edgeFinset_eq_of_deleteVert_iso he ψ
  obtain ⟨α, hα⟩ := hrig H (σ v) ψ hmul hdeg
  exact ⟨isoOfDeleteVertIso (α.trans ψ) hα⟩

omit [DecidableEq V] in
/-- **Every vertex of a regular graph is rigid**: the deficit stamp makes the
marking degree-forced, so no correcting automorphism is needed. -/
theorem IsRegularOfDegree.rigidVertex {d : ℕ} (hreg : G.IsRegularOfDegree d)
    (v : V) : G.RigidVertex v := by
  intro H hH w ψ hmul hdeg
  have hregH : H.IsRegularOfDegree d := by
    intro y
    have hy : H.degree y ∈ H.degreeMultiset :=
      Multiset.mem_map_of_mem _ (Finset.mem_val.mpr (Finset.mem_univ y))
    rw [← hmul] at hy
    obtain ⟨z, _, hz⟩ := Multiset.mem_map.mp hy
    rw [← hz]
    exact hreg z
  refine ⟨RelIso.refl _, fun x => ?_⟩
  simp only [RelIso.refl_apply]
  rw [G.adj_comm, H.adj_comm,
    hreg.adj_iff_degree_deleteVert_ne v x,
    hregH.adj_iff_degree_deleteVert_ne w (ψ x),
    iso_degree_eq ψ x]

omit [DecidableEq V] [DecidableRel H.Adj] in
/-- **Regular graphs are reconstructible** — the base case of the
deficit-marking mechanism, now derived from the rigid-card criterion: in a
regular graph every vertex is rigid (`IsRegularOfDegree.rigidVertex`). -/
theorem nonempty_iso_of_regular {d : ℕ} (hreg : G.IsRegularOfDegree d)
    (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) :
    Nonempty (G ≃g H) := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact nonempty_iso_of_rigidVertex
    (hreg.rigidVertex (Classical.arbitrary V)) h hV

end

end SimpleGraph
