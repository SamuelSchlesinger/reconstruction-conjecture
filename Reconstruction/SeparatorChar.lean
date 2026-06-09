import Reconstruction.Separator
import Reconstruction.Basic
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Reachability Characterization of Separators

This module gives a **vertex-pair characterization** of the separator and
cut-vertex predicates from `Reconstruction.Separator`. Rather than phrasing
disconnection of `G − S` through `¬ (G.induce Sᶜ).Connected`, we expose the
witnessing pair of vertices directly: `S` separates a *pair* `u, w` when both
avoid `S` and are unreachable from one another in `G − S`.

This is the standard textbook formulation of a separator (Menger-style): a set
`S` separates `u` from `w` if every `u`–`w` path passes through `S`. Here the
"path passes through `S`" condition is rendered as non-reachability in the
induced subgraph on the complement `Sᶜ`.

## Main definitions

* `SimpleGraph.Separates G S u w` — `u` and `w` both lie outside `S` and are
  mutually unreachable in the induced subgraph on `Sᶜ`.

## Main results

* `SimpleGraph.Separates.symm` — the relation is symmetric in `u, w`.
* `SimpleGraph.isSeparator_iff_separates` — `S` is a separator iff `G` is
  connected and some pair is separated by `S`.
* `SimpleGraph.isCutVertex_iff_separates` — `v` is a cut vertex iff `G` is
  connected and some pair is separated by `{v}` (the singleton specialization).

These restatements turn the abstract "induced subgraph is disconnected"
hypothesis into a concrete pair of vertices, which is convenient when one needs
to *exhibit* a separated pair (e.g. when locating a cut vertex from the deck).
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {S : Set V} {u w : V}

/-- `S` **separates** the pair `u, w` in `G`: both `u` and `w` avoid `S`
(equivalently lie in `Sᶜ`), and they are not reachable from one another in the
induced subgraph `G − S` (the subgraph on `Sᶜ`). The proofs `hu : u ∉ S` and
`hw : w ∉ S` simultaneously serve as the membership witnesses `u ∈ Sᶜ`,
`w ∈ Sᶜ` needed to form the subtype elements `⟨u, hu⟩`, `⟨w, hw⟩`. -/
def Separates (G : SimpleGraph V) (S : Set V) (u w : V) : Prop :=
  ∃ (hu : u ∉ S) (hw : w ∉ S),
    ¬ (G.induce Sᶜ).Reachable ⟨u, hu⟩ ⟨w, hw⟩

/-- Separation of a pair is symmetric: reachability in `G − S` is a symmetric
relation, so if `u` and `w` are unreachable in either order they are
unreachable in the other. -/
theorem Separates.symm (h : G.Separates S u w) : G.Separates S w u := by
  obtain ⟨hu, hw, hnr⟩ := h
  refine ⟨hw, hu, ?_⟩
  intro hr
  exact hnr hr.symm

/-- **Reachability characterization of separators.** A vertex set `S` separates
`G` exactly when `G` is connected and there is *some* pair `u, w` that `S`
separates. This converts the abstract disconnectivity condition
`¬ (G.induce Sᶜ).Connected` into the existence of a concrete unreachable pair.

The key step uses `connected_iff`: with `Sᶜ` nonempty (hence the subtype
`↥Sᶜ` nonempty), connectivity of `G.induce Sᶜ` is equivalent to its
preconnectivity, and the negation of `∀ a b, Reachable a b` unpacks to an
unreachable pair of subtype elements, which we repackage as `Separates`. -/
theorem isSeparator_iff_separates (G : SimpleGraph V) (S : Set V) :
    G.IsSeparator S ↔ G.Connected ∧ ∃ u w, G.Separates S u w := by
  classical
  constructor
  · rintro ⟨hconn, hne, hnc⟩
    refine ⟨hconn, ?_⟩
    -- `Sᶜ` nonempty gives a nonempty subtype, so disconnection reduces to
    -- failure of preconnectivity.
    have hnonempty : Nonempty (↥(Sᶜ : Set V)) := Set.nonempty_coe_sort.mpr hne
    rw [connected_iff] at hnc
    -- since the subtype is nonempty, the disconnect must come from
    -- non-preconnectivity.
    have hnp : ¬ (G.induce (Sᶜ : Set V)).Preconnected := by
      intro hp
      exact hnc ⟨hp, hnonempty⟩
    -- unfold preconnectivity and push the negation through.
    unfold Preconnected at hnp
    push_neg at hnp
    obtain ⟨a, b, hab⟩ := hnp
    exact ⟨a.1, b.1, a.2, b.2, hab⟩
  · rintro ⟨hconn, u, w, hu, hw, hnr⟩
    refine ⟨hconn, ⟨u, hu⟩, ?_⟩
    intro hc
    exact hnr (hc.preconnected ⟨u, hu⟩ ⟨w, hw⟩)

/-- **Reachability characterization of cut vertices.** A vertex `v` is a cut
vertex of `G` exactly when `G` is connected and some pair `u, w` is separated by
the singleton `{v}`. Immediate from `isSeparator_iff_separates` since
`IsCutVertex G v` is by definition `IsSeparator G {v}`. -/
theorem isCutVertex_iff_separates (G : SimpleGraph V) (v : V) :
    G.IsCutVertex v ↔ G.Connected ∧ ∃ u w, G.Separates {v} u w :=
  isSeparator_iff_separates G {v}

end SimpleGraph
