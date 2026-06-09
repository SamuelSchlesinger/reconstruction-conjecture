import Reconstruction.Separator
import Reconstruction.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Clique Separators and Simplicial Vertices

This module adds the **clique-separator** vocabulary on top of the general
separator theory in `Reconstruction.Separator`. Clique separators are the
structural input for the higher rungs of the separator-decomposition programme:
in a chordal graph every minimal vertex separator induces a clique (Dirac), and
in the interval-graph reconstruction of Heinrich–Kiyomi–Otachi–Schweitzer (2025)
the "clean clique separations" are exactly separations whose separator is a
clique. Combined with the reassembly engine `isoOfSamePiece`, a clique separator
is precisely the situation the engine reassembles.

## Main definitions

* `SimpleGraph.IsSimplicial G v` — the neighbourhood of `v` is a clique.
* `SimpleGraph.IsCliqueSeparator G S` — `S` is a separator that induces a clique.

## Main results

* `SimpleGraph.IsSimplicial.map`, `SimpleGraph.IsCliqueSeparator.map` — both are
  isomorphism invariants (clique structure transports across `≃g`).
* `SimpleGraph.IsCliqueSeparator.adj_of_mem` — distinct separator vertices are
  adjacent. This is the extra ingredient (beyond `isoOfSamePiece`) needed to glue
  the two sides of a clean clique separation: within the separator, adjacency is
  forced, so a piece-matching that fixes the separator automatically matches the
  separator's internal edges.

## References

* Dirac, G. A. (1961). "On rigid circuit graphs." (Minimal separators of chordal
  graphs are cliques.)
* Heinrich, Kiyomi, Otachi, Schweitzer (2025). "Interval graphs are
  reconstructible." arXiv:2504.02353. (Clean clique separations.)
-/

namespace SimpleGraph

variable {V : Type*} {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
variable {S : Set V} {u w v : V}

/-- A graph isomorphism transports cliques: the image of a clique under `e` is a
clique in the target graph. (Mathlib's `IsClique.map` is stated for pushforwards
`SimpleGraph.map f G`; this is the cross-graph `≃g` version.) -/
theorem isClique_image_of_iso (e : G ≃g H) (h : G.IsClique S) :
    H.IsClique (e '' S) := by
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ hxy
  exact e.map_rel_iff.mpr (h ha hb fun heq => hxy (by rw [heq]))

/-- `v` is a **simplicial vertex** of `G`: its neighbourhood induces a clique.
Simplicial vertices drive the perfect-elimination view of chordal graphs. -/
def IsSimplicial (G : SimpleGraph V) (v : V) : Prop :=
  G.IsClique (G.neighborSet v)

/-- Simplicial vertices are isomorphism invariants. -/
theorem IsSimplicial.map (e : G ≃g H) (h : G.IsSimplicial v) :
    H.IsSimplicial (e v) := by
  intro x hx y hy hxy
  rw [SimpleGraph.mem_neighborSet] at hx hy
  have hax : G.Adj v (e.symm x) := by
    have h2 : H.Adj (e v) (e (e.symm x)) := by rw [e.apply_symm_apply]; exact hx
    exact e.map_rel_iff.mp h2
  have hay : G.Adj v (e.symm y) := by
    have h2 : H.Adj (e v) (e (e.symm y)) := by rw [e.apply_symm_apply]; exact hy
    exact e.map_rel_iff.mp h2
  have hne : e.symm x ≠ e.symm y := fun heq => hxy (e.symm.injective heq)
  have hadj : G.Adj (e.symm x) (e.symm y) := h hax hay hne
  have h3 : H.Adj (e (e.symm x)) (e (e.symm y)) := e.map_rel_iff.mpr hadj
  rwa [e.apply_symm_apply, e.apply_symm_apply] at h3

/-- `S` is a **clique separator** of `G`: it separates `G` and induces a clique.
This is the separation hypothesis of the reassembly engine specialized to the
case that arises for chordal and interval graphs. -/
def IsCliqueSeparator (G : SimpleGraph V) (S : Set V) : Prop :=
  G.IsClique S ∧ G.IsSeparator S

theorem IsCliqueSeparator.isClique (h : G.IsCliqueSeparator S) : G.IsClique S := h.1

theorem IsCliqueSeparator.isSeparator (h : G.IsCliqueSeparator S) :
    G.IsSeparator S := h.2

/-- Clique separators are isomorphism invariants (clique part via
`isClique_image_of_iso`, separator part via `IsSeparator.map`). -/
theorem IsCliqueSeparator.map (e : G ≃g H) (h : G.IsCliqueSeparator S) :
    H.IsCliqueSeparator (e '' S) :=
  ⟨isClique_image_of_iso e h.1, h.2.map e⟩

/-- Distinct vertices of a clique separator are adjacent. Within the separator,
adjacency is forced; this is what lets a piece-matching that fixes the separator
match the separator's internal edges for free, completing the clean-clique-
separation gluing on top of `isoOfSamePiece`. -/
theorem IsCliqueSeparator.adj_of_mem (h : G.IsCliqueSeparator S)
    (hu : u ∈ S) (hw : w ∈ S) (hne : u ≠ w) : G.Adj u w :=
  h.1 hu hw hne

end SimpleGraph
