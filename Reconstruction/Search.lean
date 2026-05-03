import Reconstruction.Defs

/-!
# One-Card Extension Search Space

This module starts the finite-search API behind the optimization view of graph
reconstruction. Fix a card `C`. Every candidate reconstruction extending `C`
is obtained by adding one new vertex and choosing the set of old vertices
adjacent to it.

The new vertex is represented by `none`; old vertices are represented by
`some v`.

## Main definitions

* `SimpleGraph.addVertexWithNeighbors` — add one new vertex adjacent exactly to
  a prescribed set of old vertices.
* `SimpleGraph.deleteVert_addVertexWithNeighbors_none_iso` — deleting the new
  vertex recovers the original card.
* `SimpleGraph.addVertex_deleteVert_iso` — every graph is obtained from any
  one of its cards by adding the deleted vertex back with its attachment set.
* `SimpleGraph.addVertex_card_iso` — the same representation transported
  across an arbitrary card isomorphism.
-/

set_option autoImplicit false

namespace SimpleGraph

variable {V : Type*}

/-- Add one new vertex, represented by `none`, to `C`, adjacent exactly to the
old vertices in `S`. -/
def addVertexWithNeighbors (C : SimpleGraph V) (S : Set V) : SimpleGraph (Option V) where
  Adj x y :=
    match x, y with
    | some a, some b => C.Adj a b
    | none, some b => b ∈ S
    | some a, none => a ∈ S
    | none, none => False
  symm := by
    intro x y h
    cases x <;> cases y <;> simp_all [SimpleGraph.adj_comm]
  loopless := ⟨by
    intro x h
    cases x <;> simp_all⟩

@[simp] theorem addVertexWithNeighbors_adj_some_some
    (C : SimpleGraph V) (S : Set V) (a b : V) :
    (addVertexWithNeighbors C S).Adj (some a) (some b) ↔ C.Adj a b :=
  Iff.rfl

@[simp] theorem addVertexWithNeighbors_adj_none_some
    (C : SimpleGraph V) (S : Set V) (a : V) :
    (addVertexWithNeighbors C S).Adj none (some a) ↔ a ∈ S :=
  Iff.rfl

@[simp] theorem addVertexWithNeighbors_adj_some_none
    (C : SimpleGraph V) (S : Set V) (a : V) :
    (addVertexWithNeighbors C S).Adj (some a) none ↔ a ∈ S :=
  Iff.rfl

@[simp] theorem addVertexWithNeighbors_not_adj_none_none
    (C : SimpleGraph V) (S : Set V) :
    ¬(addVertexWithNeighbors C S).Adj none none := by
  simp [addVertexWithNeighbors]

/-- Vertices remaining after deleting the new `none` vertex are equivalent to
the old vertices. -/
def deleteNewVertexEquiv : {w : Option V // w ≠ none} ≃ V where
  toFun w := Option.get w.1 (Option.ne_none_iff_isSome.mp w.2)
  invFun v := ⟨some v, by simp⟩
  left_inv := by
    intro w
    cases w with
    | mk o ho =>
      cases o with
      | none => contradiction
      | some _ => rfl
  right_inv := by
    intro _
    rfl

/-- Deleting the newly added vertex recovers the original card. -/
def deleteVert_addVertexWithNeighbors_none_iso (C : SimpleGraph V) (S : Set V) :
    (addVertexWithNeighbors C S).deleteVert none ≃g C where
  toEquiv := deleteNewVertexEquiv
  map_rel_iff' := by
    intro a b
    cases a with
    | mk oa ha =>
      cases b with
      | mk ob hb =>
        cases oa with
        | none => contradiction
        | some _ =>
          cases ob with
          | none => contradiction
          | some _ => rfl

section Representation

variable [DecidableEq V]

/-- The neighbors of the deleted vertex, as a subset of the deleted card. -/
def deleteVertAttachment (G : SimpleGraph V) (v : V) : Set {w : V // w ≠ v} :=
  {w | G.Adj v w.1}

/-- Any graph is obtained from one of its vertex-deleted cards by adding the
deleted vertex back with the appropriate attachment set. -/
def addVertex_deleteVert_iso (G : SimpleGraph V) (v : V) :
    addVertexWithNeighbors (G.deleteVert v) (deleteVertAttachment G v) ≃g G where
  toEquiv := Equiv.optionSubtypeNe v
  map_rel_iff' := by
    intro x y
    cases x with
    | none =>
      cases y with
      | none => simp [addVertexWithNeighbors]
      | some _ => simp [deleteVertAttachment, addVertexWithNeighbors]
    | some _ =>
      cases y with
      | none => simp [deleteVertAttachment, addVertexWithNeighbors, SimpleGraph.adj_comm]
      | some _ => simp [deleteVertAttachment, addVertexWithNeighbors]

end Representation

section TransportedRepresentation

variable {W : Type*} [DecidableEq V]

/-- Transport the deleted-vertex attachment set across a card isomorphism. -/
def cardAttachment {G : SimpleGraph V} {C : SimpleGraph W} {v : V}
    (e : G.deleteVert v ≃g C) : Set W :=
  {w | G.Adj v ((e.symm.toEquiv w).1)}

/-- If `C` is isomorphic to a card `G - v`, then `G` is represented by adding
one vertex to `C` with the transported attachment set. -/
def addVertex_card_iso {G : SimpleGraph V} {C : SimpleGraph W} {v : V}
    (e : G.deleteVert v ≃g C) :
    addVertexWithNeighbors C (cardAttachment e) ≃g G where
  toEquiv := (Equiv.optionCongr e.symm.toEquiv).trans (Equiv.optionSubtypeNe v)
  map_rel_iff' := by
    intro x y
    cases x with
    | none =>
      cases y with
      | none => simp [addVertexWithNeighbors]
      | some _ => simp [cardAttachment, addVertexWithNeighbors]
    | some a =>
      cases y with
      | none => simp [cardAttachment, addVertexWithNeighbors, SimpleGraph.adj_comm]
      | some b =>
        change G.Adj (e.symm a).1 (e.symm b).1 ↔ C.Adj a b
        simpa using (e.symm.map_rel_iff (a := a) (b := b))

variable {G H : SimpleGraph V}

/-- A same-deck graph lies in the one-card extension search space of each
matched card. -/
theorem SameDeck.exists_addVertexWithNeighbors_iso
    (h : G.SameDeck H) (v : V) :
    ∃ S : Set {w : V // w ≠ v},
      Nonempty (addVertexWithNeighbors (G.deleteVert v) S ≃g H) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨cardAttachment (hσ v).some.symm, ?_⟩
  exact ⟨addVertex_card_iso (hσ v).some.symm⟩

end TransportedRepresentation

end SimpleGraph
