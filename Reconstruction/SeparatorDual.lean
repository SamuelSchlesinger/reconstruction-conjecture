import Reconstruction.Separator
import Reconstruction.Basic
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Separator Duality via Complementation

This module showcases the **complementation principle** (`Reconstruction.Basic`):
reconstructibility is closed under taking complements, so every positive result
dualizes. Here we dualize the **universal-vertex** reconstruction theorem
(`SimpleGraph.nonempty_iso_of_universal_vertex`) into an **isolated-vertex**
reconstruction theorem, and then *re-derive* the universal-vertex result through
the complement.

The bridge is the elementary observation that a vertex is universal in `G`
exactly when it is isolated in `Gᶜ` (`isUniversal_iff_compl_isIsolated`): the
non-edges at `v` in `G` are precisely the edges at `v` in `Gᶜ`, and `v` being
adjacent to *everything else* in `G` means it is adjacent to *nothing* in `Gᶜ`.

## Main definitions

* `SimpleGraph.IsIsolated G v` — `v` has no neighbours in `G`.

## Main results

* `SimpleGraph.isUniversal_iff_compl_isIsolated` — `v` is universal in `G` iff it
  is isolated in `Gᶜ`. This is the complementation dual at the vertex level.
* `SimpleGraph.IsIsolated.not_connected` — a graph with an isolated vertex and at
  least two vertices is disconnected.
* `SimpleGraph.nonempty_iso_of_isolated_vertex` — graphs with an isolated vertex
  are reconstructible (immediate from Kelly's disconnected-graph theorem).
* `SimpleGraph.nonempty_iso_of_universal_vertex_via_compl` — the universal-vertex
  reconstruction theorem re-derived through the complement, demonstrating the
  duality round-trip.

## References

* Bondy, J. A. (1991). "A graph reconstructor's manual" (complementation
  principle).
-/

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {v : V}

/-- `v` is an **isolated vertex** of `G`: it has no neighbours. This is the
complementation dual of a universal vertex (`IsUniversal`), via
`isUniversal_iff_compl_isIsolated`. -/
def IsIsolated (G : SimpleGraph V) (v : V) : Prop := ∀ x, ¬ G.Adj v x

/-- **Vertex-level complementation duality.** A vertex is universal in `G` iff it
is isolated in `Gᶜ`: the edges incident to `v` in `Gᶜ` are exactly the non-edges
incident to `v` in `G`, so `v` dominating `G` is the same as `v` having no
`Gᶜ`-neighbour. -/
theorem isUniversal_iff_compl_isIsolated (G : SimpleGraph V) (v : V) :
    G.IsUniversal v ↔ Gᶜ.IsIsolated v := by
  constructor
  · intro h x
    rw [SimpleGraph.compl_adj]
    rintro ⟨hne, hnadj⟩
    exact hnadj (h x (Ne.symm hne))
  · intro h x hxv
    by_contra hnadj
    exact h x ((SimpleGraph.compl_adj G v x).mpr ⟨(Ne.symm hxv), hnadj⟩)

/-- **An isolated vertex disconnects a graph with another vertex.** If `v` is
isolated and `2 ≤ |V|`, then `G` is not connected: there is some `w ≠ v`, and a
reachability `v ↝ w` would force a walk leaving `v` along an edge `G.Adj v _`,
which isolation forbids. -/
theorem IsIsolated.not_connected [Fintype V] (h : G.IsIsolated v)
    (hV : 2 ≤ Fintype.card V) : ¬ G.Connected := by
  classical
  intro hconn
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
  obtain ⟨p⟩ := (hconn.preconnected v w).symm.symm
  -- a reachability gives a walk; if `v ≠ w` it is nonempty and its first edge
  -- contradicts isolation of `v`
  cases p with
  | nil => exact hw rfl
  | cons hadj _ => exact h _ hadj

/-- **Graphs with an isolated vertex are reconstructible.** An isolated vertex
forces disconnectedness (`IsIsolated.not_connected`), so Kelly's 1942
disconnected-graph theorem `SameDeck.iso_of_not_connected` applies. This is the
complementation dual of `nonempty_iso_of_universal_vertex`. -/
theorem nonempty_iso_of_isolated_vertex [Fintype V] (h : G.IsIsolated v)
    (hV : 3 ≤ Fintype.card V) (hd : G.SameDeck H) : Nonempty (G ≃g H) :=
  hd.iso_of_not_connected hV (h.not_connected (by omega))

/-- **Universal-vertex reconstruction, re-derived through the complement.** A
round-trip through complementation: `Gᶜ` has `v` isolated
(`isUniversal_iff_compl_isIsolated`), and `Gᶜ` and `Hᶜ` share a deck
(`SameDeck.compl`), so the isolated-vertex theorem gives `Gᶜ ≃g Hᶜ`; mapping
back with `Iso.compl` and `compl_compl` recovers `G ≃g H`. This reproves
`nonempty_iso_of_universal_vertex` purely by duality. -/
theorem nonempty_iso_of_universal_vertex_via_compl [Fintype V]
    (h : G.IsUniversal v) (hV : 3 ≤ Fintype.card V) (hd : G.SameDeck H) :
    Nonempty (G ≃g H) := by
  have hiso : Gᶜ.IsIsolated v := (isUniversal_iff_compl_isIsolated G v).mp h
  obtain ⟨e⟩ := nonempty_iso_of_isolated_vertex hiso hV hd.compl
  have e' := e.compl
  rw [compl_compl, compl_compl] at e'
  exact ⟨e'⟩

/-- **Graphs with a disconnected complement are reconstructible.** If `Gᶜ` is not
connected (equivalently, `G` is a *join* `G₁ ∗ G₂` of two nonempty graphs — every
vertex of `G₁` adjacent to every vertex of `G₂`) and `H` has the same deck on
`≥ 3` vertices, then `G ≅ H`.

This is the exact complement-dual of Kelly's 1942 disconnected-graph theorem
(`SameDeck.iso_of_not_connected`): `Gᶜ` and `Hᶜ` share a deck (`SameDeck.compl`),
`Gᶜ` is disconnected, so Kelly reconstructs `Gᶜ ≃g Hᶜ`, and `Iso.compl` +
`compl_compl` map back to `G ≃g H`. It subsumes the universal-vertex case
(a universal vertex is an isolated vertex of `Gᶜ`, making `Gᶜ` disconnected),
and is itself the base case of cograph/modular-decomposition reconstruction. -/
theorem nonempty_iso_of_compl_not_connected [Fintype V] (hGc : ¬ Gᶜ.Connected)
    (hV : 3 ≤ Fintype.card V) (hd : G.SameDeck H) : Nonempty (G ≃g H) := by
  obtain ⟨e⟩ := hd.compl.iso_of_not_connected hV hGc
  have e' := e.compl
  rw [compl_compl, compl_compl] at e'
  exact ⟨e'⟩

end SimpleGraph
