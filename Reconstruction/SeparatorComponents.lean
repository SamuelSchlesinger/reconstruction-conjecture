import Reconstruction.Separator
import Reconstruction.Basic
import Reconstruction.ConnectedComponents
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Cut Vertices and Component Structure

This module connects the *cut-vertex* predicate from `Reconstruction.Separator`
to the **connected-component structure** of the vertex-deleted graph.

A cut vertex `v` of `G` is, by definition, a singleton separator: deleting `v`
leaves a nonempty, disconnected remainder `G.deleteVert v`. Here we record the
two consequences of this definition that downstream reconstruction arguments
actually consume — the deleted graph is disconnected and its vertex type is
nonempty — and then upgrade them into a quantitative statement about the number
of connected components.

## Main results

* `SimpleGraph.IsCutVertex.not_connected_deleteVert` — the vertex-deleted graph
  `G.deleteVert v` is disconnected. This is just the separator condition
  `h.2.2` read through the definitional equality
  `G.deleteVert v = G.induce {v}ᶜ`.
* `SimpleGraph.IsCutVertex.nonempty_deleteVert` — the vertex-deleted graph has
  at least one vertex (the separator complement `{v}ᶜ` is nonempty).
* `SimpleGraph.IsCutVertex.two_le_card_components` — over a finite vertex type,
  removing a cut vertex leaves **at least two** connected components. This is
  the quantitative form of "a cut vertex disconnects the graph": a nonempty
  graph whose connected-component quotient is a subsingleton is preconnected
  (hence connected), so a *disconnected* nonempty graph must have two or more
  components.
* `SimpleGraph.twoConnected_iff_forall_deleteVert_connected` — on more than one
  vertex, `G` is 2-connected iff `G` is connected and **every card is
  connected**. The cards are exactly the vertex-deleted subgraphs, so this
  characterizes 2-connectivity by card-level data alone.
* `SimpleGraph.SameDeck.twoConnected_iff` — **2-connectedness is
  deck-recognizable** (folklore; implicit in Bondy 1969): connectivity of `G`
  is reconstructible, and connectivity of each card is visible in the deck up
  to isomorphism, so same-deck graphs agree on 2-connectivity. This is the
  recognition half of rung 1 of the separator programme: it lets a deck
  argument split into the 2-connected case and the cut-vertex case.

## References

* Bondy, J. A. (1969). "On Ulam's conjecture for separable graphs".
-/

namespace SimpleGraph

variable {V : Type*}

/-- The vertex-deleted graph at a **cut vertex** is disconnected.

By definition a cut vertex is a singleton separator `IsSeparator G {v}`, whose
third component asserts `¬ (G.induce {v}ᶜ).Connected`. Since `G.deleteVert v` is
*definitionally* `G.induce {w | w ≠ v} = G.induce {v}ᶜ`, this is exactly the
statement we want, modulo bridging that definitional equality. -/
theorem IsCutVertex.not_connected_deleteVert {G : SimpleGraph V} {v : V}
    (h : G.IsCutVertex v) : ¬ (G.deleteVert v).Connected :=
  h.not_connected_induce_compl

/-- The vertex-deleted graph at a **cut vertex** has at least one vertex.

The separator condition requires the complement `{v}ᶜ` to be nonempty; the
vertex type of `G.deleteVert v` is `{w // w ≠ v}`, which is definitionally the
coercion of `{v}ᶜ`, so a complement witness supplies the required vertex. -/
theorem IsCutVertex.nonempty_deleteVert {G : SimpleGraph V} {v : V}
    (h : G.IsCutVertex v) : Nonempty {w : V // w ≠ v} := by
  obtain ⟨w, hw⟩ := h.compl_nonempty
  exact ⟨w, by simpa using hw⟩

open Classical in
/-- Removing a **cut vertex** from a finite graph leaves at least two connected
components.

This is the quantitative reading of the cut-vertex definition. We argue by
contradiction: if the component quotient had fewer than two elements, then —
being nonempty (the deleted graph has a vertex) — it would be a subsingleton.
A graph whose connected-component quotient is a subsingleton is preconnected
(any two vertices share a component, hence are reachable), and a preconnected
nonempty graph is connected. That contradicts
`IsCutVertex.not_connected_deleteVert`. -/
theorem IsCutVertex.two_le_card_components [Fintype V] {G : SimpleGraph V}
    {v : V} (h : G.IsCutVertex v) :
    2 ≤ Fintype.card (G.deleteVert v).ConnectedComponent := by
  -- The deleted graph is nonempty and disconnected.
  haveI hne : Nonempty {w : V // w ≠ v} := h.nonempty_deleteVert
  have hdisc : ¬ (G.deleteVert v).Connected := h.not_connected_deleteVert
  -- Suppose for contradiction there are fewer than two components.
  by_contra hlt
  push_neg at hlt
  -- Then the component quotient is a subsingleton (nonempty but ≤ 1 element).
  have hle : Fintype.card (G.deleteVert v).ConnectedComponent ≤ 1 := by omega
  have hsub : Subsingleton (G.deleteVert v).ConnectedComponent :=
    Fintype.card_le_one_iff_subsingleton.mp hle
  -- A subsingleton component quotient forces preconnectedness.
  have hpre : (G.deleteVert v).Preconnected := by
    intro a b
    have hab : (G.deleteVert v).connectedComponentMk a =
        (G.deleteVert v).connectedComponentMk b :=
      Subsingleton.elim _ _
    exact ConnectedComponent.eq.mp hab
  -- Preconnected + nonempty = connected, contradicting disconnectedness.
  exact hdisc ((connected_iff (G.deleteVert v)).mpr ⟨hpre, hne⟩)

/-! ### 2-connectedness is deck-recognizable

A vertex `v` of a connected graph (with at least one other vertex) is a cut
vertex exactly when the card `G - v` is disconnected. Quantifying over `v`
characterizes 2-connectivity by data visible in the deck: `G` itself is
connected (reconstructible, `SameDeck.connected`) and every card is connected
(an isomorphism invariant of each card). This is the *recognition* half of
rung 1 of the separator-decomposition programme. -/

/-- In a connected graph with a vertex other than `v`, `v` is a cut vertex iff
the card `G - v` is disconnected. Both directions are the definition of
`IsSeparator {v}` read through `G.deleteVert v = G.induce {v}ᶜ`. -/
theorem isCutVertex_iff_not_connected_deleteVert {G : SimpleGraph V} {v : V}
    (hconn : G.Connected) (hne : ∃ w : V, w ≠ v) :
    G.IsCutVertex v ↔ ¬ (G.deleteVert v).Connected := by
  refine ⟨IsCutVertex.not_connected_deleteVert, fun hnc => ?_⟩
  obtain ⟨w, hw⟩ := hne
  exact ⟨hconn, ⟨w, by simpa using hw⟩, hnc⟩

/-- On more than one vertex, `G` is 2-connected iff `G` is connected and
**every vertex-deleted card is connected**. -/
theorem twoConnected_iff_forall_deleteVert_connected [Fintype V]
    {G : SimpleGraph V} (hV : 1 < Fintype.card V) :
    G.TwoConnected ↔ G.Connected ∧ ∀ v : V, (G.deleteVert v).Connected := by
  constructor
  · rintro ⟨hconn, hnc⟩
    refine ⟨hconn, fun v => ?_⟩
    by_contra hdisc
    exact hnc v ((isCutVertex_iff_not_connected_deleteVert hconn
      (Fintype.exists_ne_of_one_lt_card hV v)).mpr hdisc)
  · rintro ⟨hconn, hcards⟩
    exact ⟨hconn, fun v hcut => hcut.not_connected_deleteVert (hcards v)⟩

/-- **2-connectedness is deck-recognizable** (one direction): if `G` and `H`
have the same deck on at least three vertices and `G` is 2-connected, so is
`H`. Connectivity of `H` comes from `SameDeck.connected`; connectivity of each
card of `H` comes from the matched isomorphic card of `G`. -/
theorem SameDeck.twoConnected [Fintype V] {G H : SimpleGraph V}
    (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) (hG : G.TwoConnected) :
    H.TwoConnected := by
  have hV1 : 1 < Fintype.card V := by omega
  rw [twoConnected_iff_forall_deleteVert_connected hV1] at hG ⊢
  refine ⟨h.connected hV hG.1, fun w => ?_⟩
  obtain ⟨σ, hσ⟩ := h
  obtain ⟨iso⟩ := hσ (σ.symm w)
  have hc := hG.2 (σ.symm w)
  rw [Equiv.apply_symm_apply] at iso
  exact iso.connected_iff.mp hc

/-- **2-connectedness is deck-recognizable**: same-deck graphs on at least
three vertices agree on 2-connectivity. -/
theorem SameDeck.twoConnected_iff [Fintype V] {G H : SimpleGraph V}
    (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) :
    G.TwoConnected ↔ H.TwoConnected :=
  ⟨fun hG => h.twoConnected hV hG, fun hH => h.symm.twoConnected hV hH⟩

end SimpleGraph
