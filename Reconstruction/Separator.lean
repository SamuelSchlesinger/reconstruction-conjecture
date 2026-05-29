import Reconstruction.Defs
import Reconstruction.Disconnected
import Reconstruction.DegreeSequence
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

/-!
# Reconstruction Conjecture — Separator Decomposition

This module begins the **separator-decomposition programme** (see
`research/attacks/separator-decomposition.md`): reconstruct graphs class by
class up a ladder of separator size, reusing the component-decomposition
machinery already proved in `Reconstruction.Disconnected`.

The bottom rung — decomposition along the **empty** separator (connected
components) — is the disconnected-graph theorem
`SimpleGraph.SameDeck.iso_of_not_connected`. This file provides the next layer
of vocabulary, missing entirely from Mathlib (v4.28.0): **vertex separators**,
**cut vertices**, and **2-connectivity**.

## Main definitions

* `SimpleGraph.IsSeparator G S` — deleting the vertex set `S` from the connected
  graph `G` leaves a nonempty, disconnected remainder.
* `SimpleGraph.IsCutVertex G v` — `v` is an articulation point: `IsSeparator G {v}`.
* `SimpleGraph.NoCutVertex`, `SimpleGraph.TwoConnected` — connected with no cut
  vertex.
* `SimpleGraph.MinDegreeTwo` — every vertex has two distinct neighbours (no
  pendant vertex); stated without `Fintype`/`degree` so it is instance-free.

## Isomorphism invariance (proved)

* `SimpleGraph.IsSeparator.map`, `IsCutVertex.map`, `MinDegreeTwo.map`,
  `TwoConnected.map` — all the programme's predicates are isomorphism
  invariants, via `Iso.induceImage` (an isomorphism restricts to the induced
  subgraphs on `s ↦ e '' s`). This is the first ingredient any reconstruction
  argument needs, since the deck only determines structure up to isomorphism.

## The separator reassembly engine (proved)

* `SimpleGraph.SamePiece` — `u`, `w` lie in a common piece of `G` over `S`.
* `SimpleGraph.adj_samePiece` — every edge lies within a single piece (the
  separator structural lemma: no edges run between distinct `G − S`
  components).
* `SimpleGraph.isoOfSamePiece` / `isoOfSamePiece'` — the engine: a vertex
  bijection that preserves adjacency within pieces and matches `G`'s pieces to
  `H`'s pieces is a global isomorphism `G ≃g H`. This is the amalgamation-over-
  `S` analogue of `isoOfComponentIsoEquiv` (the `S = ∅` case).
* `SimpleGraph.mem_iff_of_fixOn` — fixing `S` pointwise preserves `S`-membership
  (used when assembling the bijection from per-piece data).

## Staged targets (stated as `Prop`, not proved)

* `SimpleGraph.BondySeparableReconstructible` — Bondy's 1969 theorem: a graph
  with a cut vertex and no pendant vertex is reconstructible.
* `SimpleGraph.TwoConnectedReconstructible` — the class to which Bondy–Yongzhi
  reduces the whole conjecture.

The next Lean task is the *application* of the engine: assemble the bijection
`φ` for the cut-vertex case (`S = {v}`) from a bijection of `G − v` components
and per-component isomorphisms fixing `v`, discharging `isoOfSamePiece`'s two
hypotheses. The remaining deck-theoretic content — recovering those pieces and
their attachment to `v` from the deck — is the Bondy 1969 argument proper.

## References

* Bondy, J. A. (1969). "On Ulam's conjecture for separable graphs".
* Yongzhi, H. (1988). "On the Reconstruction Conjecture" (reduction to
  2-connected graphs).
-/

namespace SimpleGraph

variable {V : Type*} {W : Type*}

/-- `S` **separates** `G`: the graph is connected, its complement `Sᶜ` is
nonempty, and the induced subgraph on `Sᶜ` is not connected. Equivalently,
deleting the vertices of `S` leaves at least two nonempty pieces.

This is the general (multi-vertex) separator notion. The `|S| = 1` case is a
cut vertex; the `S = ∅` case never holds for a connected `G` (the complement is
all of `V`, whose induced graph is connected), which is exactly why the
empty-separator rung is the *connected* vs *disconnected* dichotomy handled in
`Reconstruction.Disconnected`. -/
def IsSeparator (G : SimpleGraph V) (S : Set V) : Prop :=
  G.Connected ∧ (Sᶜ : Set V).Nonempty ∧ ¬ (G.induce Sᶜ).Connected

/-- `v` is a **cut vertex** (articulation point) of `G`: deleting it from the
connected graph `G` disconnects the (nonempty) remainder. Defined as the
singleton-separator case so that all separator lemmas specialize to it. -/
def IsCutVertex (G : SimpleGraph V) (v : V) : Prop :=
  G.IsSeparator {v}

/-- `G` has no cut vertex. -/
def NoCutVertex (G : SimpleGraph V) : Prop :=
  ∀ v : V, ¬ G.IsCutVertex v

/-- `G` is **2-connected**: connected and free of cut vertices. (Some authors
additionally require `3 ≤ |V|`; we keep that side condition explicit at use
sites, e.g. in the reconstruction targets which already assume `3 ≤ |V|`.) -/
def TwoConnected (G : SimpleGraph V) : Prop :=
  G.Connected ∧ G.NoCutVertex

/-- `G` has **minimum degree at least 2** (no pendant or isolated vertex):
every vertex has two distinct neighbours. Stated combinatorially so it needs no
`Fintype`/`DecidableRel` instances. -/
def MinDegreeTwo (G : SimpleGraph V) : Prop :=
  ∀ v : V, ∃ a b : V, a ≠ b ∧ G.Adj v a ∧ G.Adj v b

/-! ### Basic projections -/

theorem IsSeparator.connected {G : SimpleGraph V} {S : Set V}
    (h : G.IsSeparator S) : G.Connected := h.1

theorem IsSeparator.compl_nonempty {G : SimpleGraph V} {S : Set V}
    (h : G.IsSeparator S) : (Sᶜ : Set V).Nonempty := h.2.1

theorem IsSeparator.not_connected_induce_compl {G : SimpleGraph V} {S : Set V}
    (h : G.IsSeparator S) : ¬ (G.induce Sᶜ).Connected := h.2.2

theorem IsCutVertex.connected {G : SimpleGraph V} {v : V}
    (h : G.IsCutVertex v) : G.Connected := h.1

theorem IsCutVertex.exists_ne {G : SimpleGraph V} {v : V}
    (h : G.IsCutVertex v) : ∃ w : V, w ≠ v := by
  obtain ⟨w, hw⟩ := h.compl_nonempty
  exact ⟨w, by simpa using hw⟩

theorem TwoConnected.connected {G : SimpleGraph V} (h : G.TwoConnected) :
    G.Connected := h.1

theorem TwoConnected.noCutVertex {G : SimpleGraph V} (h : G.TwoConnected) :
    G.NoCutVertex := h.2

/-! ### Separators are isomorphism invariants

The deck determines a graph only up to isomorphism, so every reconstruction
argument needs its structural predicates to be isomorphism invariants. We prove
this for separators (hence for cut vertices and 2-connectivity) by restricting
an isomorphism to the relevant induced subgraphs. -/

/-- An isomorphism `e : G ≃g H` restricts to an isomorphism between the subgraph
induced on a set `s` and the subgraph induced on its image `e '' s`. This is the
Set-based companion of `KellyLemma.induceMapIso` (which is Finset-based). -/
noncomputable def Iso.induceImage {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (s : Set V) : G.induce s ≃g H.induce (e '' s) where
  toEquiv := Equiv.Set.image (e : V → W) s (EquivLike.injective e)
  map_rel_iff' := by
    intro a b
    simp only [induce_adj, Equiv.Set.image_apply]
    exact e.map_rel_iff

theorem IsSeparator.map {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {S : Set V} (h : G.IsSeparator S) : H.IsSeparator (e '' S) := by
  refine ⟨e.connected_iff.mp h.connected, ?_, ?_⟩
  · -- the complement of the image is nonempty, witnessed by the image of a
    -- complement witness
    obtain ⟨x, hx⟩ := h.compl_nonempty
    refine ⟨e x, ?_⟩
    intro hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    exact hx (by simpa [EquivLike.injective e hyx] using hy)
  · -- the induced subgraph on the image complement is still disconnected,
    -- transported back along `induceImage`
    intro hconn
    apply h.not_connected_induce_compl
    have hcompl : (e '' S)ᶜ = e '' Sᶜ :=
      (Set.image_compl_eq (EquivLike.bijective e)).symm
    rw [hcompl] at hconn
    exact (Iso.induceImage e Sᶜ).connected_iff.mpr hconn

/-- Cut vertices are isomorphism invariants. -/
theorem IsCutVertex.map {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {v : V} (h : G.IsCutVertex v) : H.IsCutVertex (e v) := by
  have := IsSeparator.map e h
  rwa [Set.image_singleton] at this

/-- Minimum-degree-≥-2 is an isomorphism invariant. -/
theorem MinDegreeTwo.map {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (h : G.MinDegreeTwo) : H.MinDegreeTwo := by
  intro w
  obtain ⟨a, b, hab, hva, hvb⟩ := h (e.symm w)
  refine ⟨e a, e b, fun hcontra => hab (EquivLike.injective e hcontra), ?_, ?_⟩
  · have := e.map_rel_iff.mpr hva
    rwa [e.apply_symm_apply] at this
  · have := e.map_rel_iff.mpr hvb
    rwa [e.apply_symm_apply] at this

/-- 2-connectivity is an isomorphism invariant; this makes
`TwoConnectedReconstructible` a well-posed (isomorphism-stable) target. -/
theorem TwoConnected.map {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (h : G.TwoConnected) : H.TwoConnected := by
  refine ⟨e.connected_iff.mp h.connected, fun w hw => ?_⟩
  exact h.noCutVertex (e.symm w) (hw.map e.symm)

/-! ### The separator reassembly engine

This is the structural core of the programme: the generalization of
`isoOfComponentIsoEquiv` (the `S = ∅`, disjoint-union case) to amalgamation over
a shared separator `S`.

The key structural fact about a separator is that **every edge of `G` lies
inside a single "piece"** — a pair of endpoints is either incident to `S`, or
both endpoints avoid `S` and then (since deleting `S` cannot create edges) they
lie in the same connected component of `G − S`. There are *no* edges between
distinct `(G − S)`-components. Consequently a vertex bijection that preserves
adjacency *within* each piece, and that matches `G`'s pieces to `H`'s pieces
(so that cross-component non-edges map to cross-component non-edges), is already
a global isomorphism. -/

/-- `u` and `w` lie in a common **piece** of `G` relative to `S`: at least one
of them is in `S`, or both avoid `S` and lie in the same connected component of
the separator-deleted graph `G.induce Sᶜ`. Every edge lies within a piece
(`adj_samePiece`), and within a piece adjacency is "local". -/
def SamePiece (G : SimpleGraph V) (S : Set V) (u w : V) : Prop :=
  u ∈ S ∨ w ∈ S ∨ ∃ (hu : u ∉ S) (hw : w ∉ S),
    (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ =
      (G.induce Sᶜ).connectedComponentMk ⟨w, hw⟩

/-- Adjacent vertices avoiding `S` lie in the same component of `G − S`:
deleting a vertex set cannot turn a non-edge into an edge, so an edge between
two complement vertices is already an edge of `G.induce Sᶜ`. -/
theorem adj_connectedComponentMk_eq {G : SimpleGraph V} {S : Set V} {u w : V}
    (h : G.Adj u w) (hu : u ∉ S) (hw : w ∉ S) :
    (G.induce Sᶜ).connectedComponentMk ⟨u, hu⟩ =
      (G.induce Sᶜ).connectedComponentMk ⟨w, hw⟩ := by
  apply ConnectedComponent.connectedComponentMk_eq_of_adj
  rw [induce_adj]
  exact h

/-- **Every edge lies within a single piece.** This is the separator structural
lemma in the form the reassembly engine consumes. -/
theorem adj_samePiece {G : SimpleGraph V} {S : Set V} {u w : V}
    (h : G.Adj u w) : G.SamePiece S u w := by
  by_cases hu : u ∈ S
  · exact Or.inl hu
  · by_cases hw : w ∈ S
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr ⟨hu, hw, adj_connectedComponentMk_eq h hu hw⟩)

/-- **Separator reassembly engine.** A vertex bijection `φ` that (i) preserves
adjacency on every pair lying in a common piece of `G`, and (ii) reflects
`H`-pieces back to `G`-pieces, is a graph isomorphism `G ≃g H`.

This is the amalgamation-over-`S` analogue of `isoOfComponentIsoEquiv`: in the
`S = ∅` case a piece is just a connected component, hypothesis (i) is
"componentwise isomorphism", and (ii) holds because `φ` matches components. In
applications `φ` is assembled from a component bijection together with per-piece
isomorphisms that agree on `S`; this lemma is the structural step that turns
that local data into a global isomorphism. -/
def isoOfSamePiece {G H : SimpleGraph V} {S : Set V} (φ : V ≃ V)
    (hpiece : ∀ u w : V, G.SamePiece S u w → (G.Adj u w ↔ H.Adj (φ u) (φ w)))
    (hreflect : ∀ u w : V, H.SamePiece S (φ u) (φ w) → G.SamePiece S u w) :
    G ≃g H where
  toEquiv := φ
  map_rel_iff' := by
    intro u w
    constructor
    · intro h
      exact (hpiece u w (hreflect u w (adj_samePiece h))).mpr h
    · intro h
      exact (hpiece u w (adj_samePiece h)).mp h

/-- Convenience form of the reassembly engine with a single symmetric
piece-preservation hypothesis. -/
def isoOfSamePiece' {G H : SimpleGraph V} {S : Set V} (φ : V ≃ V)
    (hpres : ∀ u w : V, G.SamePiece S u w ↔ H.SamePiece S (φ u) (φ w))
    (hadj : ∀ u w : V, G.SamePiece S u w → (G.Adj u w ↔ H.Adj (φ u) (φ w))) :
    G ≃g H :=
  isoOfSamePiece φ hadj fun u w h => (hpres u w).mpr h

/-- If a bijection fixes `S` pointwise it preserves membership in `S` in both
directions. (When constructing the reassembly bijection from per-piece data,
this discharges the "preserves the separator" obligation from the single
assumption that the pieces agree on `S`.) -/
theorem mem_iff_of_fixOn {S : Set V} {φ : V ≃ V} (hfix : ∀ x ∈ S, φ x = x)
    (x : V) : x ∈ S ↔ φ x ∈ S := by
  constructor
  · intro hx; rw [hfix x hx]; exact hx
  · intro hx
    have hxx : φ x = x := φ.injective (hfix (φ x) hx)
    rwa [hxx] at hx

/-! ### Rung 1: the deleted-vertex reassembly constructor

The reassembly engine specialized to a single deleted vertex (`S = {v}`). A card
isomorphism `ψ : G − v ≃g H − w` that additionally matches the **link** of the
deleted vertex (its neighbourhood) extends to a global isomorphism `G ≃g H`.
This is the structural converse of vertex deletion: a graph is recovered from one
card together with the deleted vertex's attachment. (For `|S| = 1` the "no edge
crosses a piece" content is subsumed by `ψ` being a *card* isomorphism: any pair
of non-`v` vertices is adjacent in `G` iff adjacent in `G − v`.)

The deleted vertices `v` and `w` are allowed to differ, since a deck matching
matches `v` to some `σ v`. The remaining, deck-theoretic, work for Bondy's
theorem is to *produce* such a `ψ` from deck data — assembled from per-component
pieces that agree on the deleted vertex. -/

/-- Extend a bijection `ψ` from the vertices `≠ v` to the vertices `≠ w` to a
bijection of all of `V` sending `v` to `w`. -/
def extendMap [DecidableEq V] (v w : V)
    (ψ : {x : V // x ≠ v} ≃ {x : V // x ≠ w}) : V ≃ V where
  toFun x := if h : x = v then w else (ψ ⟨x, h⟩ : V)
  invFun y := if h : y = w then v else (ψ.symm ⟨y, h⟩ : V)
  left_inv x := by
    by_cases h : x = v
    · subst h; simp
    · have hx : ((ψ ⟨x, h⟩ : {y : V // y ≠ w}) : V) ≠ w := (ψ ⟨x, h⟩).2
      simp [dif_neg h, dif_neg hx, Equiv.symm_apply_apply]
  right_inv y := by
    by_cases h : y = w
    · subst h; simp
    · have hy : ((ψ.symm ⟨y, h⟩ : {x : V // x ≠ v}) : V) ≠ v := (ψ.symm ⟨y, h⟩).2
      simp [dif_neg h, dif_neg hy, Equiv.apply_symm_apply]

@[simp] theorem extendMap_apply_self [DecidableEq V] (v w : V)
    (ψ : {x : V // x ≠ v} ≃ {x : V // x ≠ w}) : extendMap v w ψ v = w :=
  dif_pos rfl

theorem extendMap_apply_of_ne [DecidableEq V] (v w : V)
    (ψ : {x : V // x ≠ v} ≃ {x : V // x ≠ w}) {x : V} (h : x ≠ v) :
    extendMap v w ψ x = (ψ ⟨x, h⟩ : V) :=
  dif_neg h

/-- **Deleted-vertex reassembly.** A card isomorphism `ψ : G − v ≃g H − w` that
preserves the link (for every `x ≠ v`, `v` is adjacent to `x` in `G` iff `w` is
adjacent to `ψ x` in `H`) extends to a global isomorphism `G ≃g H` sending `v`
to `w`. The deleted vertices `v`, `w` may differ — exactly what a deck matching
provides, since it matches `v` to some `σ v` rather than to `v` itself. -/
def isoOfDeleteVertIso [DecidableEq V] {G H : SimpleGraph V} {v w : V}
    (ψ : G.deleteVert v ≃g H.deleteVert w)
    (hlink : ∀ x : {x : V // x ≠ v}, G.Adj v (x : V) ↔ H.Adj w (ψ x : V)) :
    G ≃g H where
  toEquiv := extendMap v w ψ.toEquiv
  map_rel_iff' := by
    intro a b
    by_cases ha : a = v <;> by_cases hb : b = v
    · rw [ha, hb, extendMap_apply_self]
      simp
    · rw [ha, extendMap_apply_self, extendMap_apply_of_ne v w ψ.toEquiv hb]
      exact (hlink ⟨b, hb⟩).symm
    · rw [hb, extendMap_apply_self, extendMap_apply_of_ne v w ψ.toEquiv ha,
        G.adj_comm a v, H.adj_comm (ψ.toEquiv ⟨a, ha⟩ : V) w]
      exact (hlink ⟨a, ha⟩).symm
    · rw [extendMap_apply_of_ne v w ψ.toEquiv ha, extendMap_apply_of_ne v w ψ.toEquiv hb]
      calc H.Adj (ψ.toEquiv ⟨a, ha⟩ : V) (ψ.toEquiv ⟨b, hb⟩ : V)
          ↔ (H.deleteVert w).Adj (ψ.toEquiv ⟨a, ha⟩) (ψ.toEquiv ⟨b, hb⟩) := induce_adj.symm
        _ ↔ (G.deleteVert v).Adj ⟨a, ha⟩ ⟨b, hb⟩ := ψ.map_rel_iff
        _ ↔ G.Adj a b := induce_adj

/-- **Cut-vertex reassembly from pieces.** Given a bijection `e` between the
components of `G − v` and those of `H − v`, per-component isomorphisms `ι` of the
corresponding induced subgraphs, and the condition that each piece isomorphism
preserves adjacency to `v` (the link condition), the graphs `G` and `H` are
isomorphic.

This is the complete *structural* content of Bondy's cut-vertex reconstruction:
it reduces `G ≅ H` to a matching of the `(G − v)`-pieces that agrees on `v`'s
attachment. The remaining work is the deck-theoretic recovery of such a matching
from `SameDeck`. The card isomorphism is assembled with `componentIso` (whose
vertex action is `componentIso_apply`), and the global isomorphism is produced
by `isoOfDeleteVertIso`. -/
theorem nonempty_iso_of_cutVertex_pieces {G H : SimpleGraph V} {v : V}
    (e : (G.deleteVert v).ConnectedComponent ≃ (H.deleteVert v).ConnectedComponent)
    (ι : ∀ c : (G.deleteVert v).ConnectedComponent,
      (G.deleteVert v).induce c.supp ≃g (H.deleteVert v).induce (e c).supp)
    (hlink : ∀ (c : (G.deleteVert v).ConnectedComponent) (x : ↥c.supp),
      G.Adj v x.1.1 ↔ H.Adj v (ι c x).1.1) :
    Nonempty (G ≃g H) := by
  classical
  refine ⟨isoOfDeleteVertIso (componentIso e ι) ?_⟩
  intro x
  rw [componentIso_apply]
  exact hlink ((G.deleteVert v).connectedComponentMk x)
    ⟨x, ConnectedComponent.connectedComponentMk_mem⟩

/-! ### Application: dominating-vertex reconstruction

A first genuine deck-level reconstruction theorem from the reassembly machinery:
a graph with a **universal vertex** (one adjacent to every other vertex) is
reconstructible. This is the simplest case of Manvel's dominating-vertex method.
The link condition is automatic — a universal vertex is adjacent to everything —
and degree-preservation forces the matched card's vertex to be universal too, so
`isoOfDeleteVertIso` applies directly. -/

/-- `v` is a **universal vertex** of `G`: adjacent to every other vertex. -/
def IsUniversal (G : SimpleGraph V) (v : V) : Prop := ∀ x : V, x ≠ v → G.Adj v x

/-- A vertex is universal iff its degree is `|V| - 1`. -/
theorem isUniversal_iff_degree [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (v : V) : G.IsUniversal v ↔ G.degree v = Fintype.card V - 1 := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  constructor
  · intro hv
    have heq : G.neighborFinset v = Finset.univ.erase v := by
      ext y
      constructor
      · intro hy
        rw [SimpleGraph.mem_neighborFinset] at hy
        exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hy).symm, Finset.mem_univ y⟩
      · intro hy
        rw [SimpleGraph.mem_neighborFinset]
        exact hv y (Finset.mem_erase.mp hy).1
    rw [heq, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
  · intro hdeg x hxv
    have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
      intro y hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hy).symm, Finset.mem_univ y⟩
    have h1 : (Finset.univ.erase v).card = Fintype.card V - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    have hcard : (Finset.univ.erase v).card ≤ (G.neighborFinset v).card := by omega
    have heq : G.neighborFinset v = Finset.univ.erase v :=
      Finset.eq_of_subset_of_card_le hsub hcard
    have hxnb : x ∈ G.neighborFinset v := by
      rw [heq]; exact Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ x⟩
    rwa [SimpleGraph.mem_neighborFinset] at hxnb

/-- Two universal vertices with isomorphic cards give isomorphic graphs: the link
condition holds vacuously, since both vertices are adjacent to everything. -/
theorem nonempty_iso_of_universal_card_iso {G H : SimpleGraph V}
    {v w : V} (hv : G.IsUniversal v) (hw : H.IsUniversal w)
    (ψ : G.deleteVert v ≃g H.deleteVert w) : Nonempty (G ≃g H) := by
  classical
  exact ⟨isoOfDeleteVertIso ψ fun x => iff_of_true (hv x.1 x.2) (hw (ψ x).1 (ψ x).2)⟩

/-- **Graphs with a universal vertex are reconstructible.** If `G` has a vertex
adjacent to all others and `H` has the same deck (on `≥ 3` vertices), then
`G ≅ H`. The matched-card vertex `σ v` is forced to be universal in `H` because
degrees are deck-reconstructible, so `nonempty_iso_of_universal_card_iso`
applies. (Manvel's dominating-vertex method, simplest case.) -/
theorem nonempty_iso_of_universal_vertex [Fintype V]
    {G H : SimpleGraph V} {v : V}
    (hv : G.IsUniversal v) (hV : 3 ≤ Fintype.card V) (h : G.SameDeck H) :
    Nonempty (G ≃g H) := by
  classical
  have he := h.card_edgeFinset_eq hV
  obtain ⟨σ, hσ⟩ := h
  have ψ := (hσ v).some
  have hdeg : G.degree v = H.degree (σ v) :=
    degree_eq_of_card_edgeFinset_eq_of_deleteVert_iso he ψ
  have hwu : H.IsUniversal (σ v) :=
    (isUniversal_iff_degree (σ v)).mpr (hdeg ▸ (isUniversal_iff_degree v).mp hv)
  exact nonempty_iso_of_universal_card_iso hv hwu ψ

/-! ### Staged targets

These are the reconstruction theorems the programme aims at, stated as `Prop`s
(the project convention for open/under-construction goals; no `sorry`). -/

/-- **TARGET — Bondy 1969.** A graph with a cut vertex and no pendant vertex is
reconstructible: if `G` has a cut vertex, has minimum degree ≥ 2, and `H` has
the same deck, then `G ≅ H`. Together with `SameDeck.iso_of_not_connected` and
the pendant-vertex (tree) case, this yields the Bondy–Yongzhi reduction. -/
def BondySeparableReconstructible (G : SimpleGraph V) : Prop :=
  (∃ v : V, G.IsCutVertex v) → G.MinDegreeTwo →
    ∀ H : SimpleGraph V, G.SameDeck H → Nonempty (G ≃g H)

/-- **TARGET — the class Bondy–Yongzhi reduces to.** Every 2-connected graph is
reconstructible from its deck. By Bondy 1969 (separable case) + Kelly 1942
(disconnected case) + the tree case, the full Reconstruction Conjecture for
`n ≥ 3` follows from this restricted statement. -/
def TwoConnectedReconstructible (G : SimpleGraph V) : Prop :=
  G.TwoConnected → ∀ H : SimpleGraph V, G.SameDeck H → Nonempty (G ≃g H)

end SimpleGraph
