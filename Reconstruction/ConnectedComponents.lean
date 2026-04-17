import Reconstruction.Basic
import Reconstruction.KellyLemma
import Reconstruction.DegreeSequence
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Reconstruction Conjecture — Connected Components

The number of connected components and the property of being connected
are reconstructible graph invariants.

## Main results

* `SimpleGraph.SameDeck.connected` — connectivity is reconstructible
* `SimpleGraph.SameDeck.numComponents_eq` — number of components is reconstructible

## References

* Kelly, P. J. (1942). "On isometric transformations".
-/

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of connected components of a graph. -/
def numComponents (G : SimpleGraph V) : ℕ :=
  Nat.card G.ConnectedComponent

lemma numComponents_eq_fintype_card (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.numComponents = Fintype.card G.ConnectedComponent :=
  Nat.card_eq_fintype_card

variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

private theorem reachable_of_deleteVert {v : V}
    {a b : V} (ha : a ≠ v) (hb : b ≠ v)
    (h : (G.deleteVert v).Reachable ⟨a, ha⟩ ⟨b, hb⟩) : G.Reachable a b :=
  h.map ⟨Subtype.val, fun h => h⟩

omit [DecidableEq V] [DecidableRel G.Adj] [DecidableRel H.Adj] in
/-- **Connectivity is reconstructible.** If `G` is connected and has the same
deck as `H` (on ≥ 3 vertices), then `H` is connected.

The proof finds a non-cut vertex `v` in `G` (which exists in any connected
graph on ≥ 2 vertices). The deck isomorphism gives `G - v ≅ H - σ(v)`, so
`H - σ(v)` is connected. Since every vertex of `H` has positive degree
(degree sequence is reconstructible), `σ(v)` has a neighbor in `H`, and
we can extend connectivity of `H - σ(v)` to all of `H`. -/
theorem SameDeck.connected (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V)
    (hconn : G.Connected) : H.Connected := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hG_deg : ∀ u : V, 0 < G.degree u := by
    intro u; by_contra hc
    obtain ⟨w, hw⟩ := exists_ne u
    obtain ⟨p⟩ := hconn.preconnected u w
    cases p with
    | nil => exact hw rfl
    | cons hadj _ => exact hc ((G.degree_pos_iff_exists_adj u).mpr ⟨_, hadj⟩)
  have hH_deg : ∀ w : V, 0 < H.degree w := by
    obtain ⟨τ, hτ⟩ := h.degree_eq hV; intro w
    have h1 := hτ (τ.symm w); rw [τ.apply_symm_apply] at h1
    have h2 := hG_deg (τ.symm w); omega
  obtain ⟨v, hv_conn⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  obtain ⟨σ, hσ⟩ := h; obtain ⟨iso⟩ := hσ v
  have hH_del : (H.deleteVert (σ v)).Connected := iso.connected_iff.mp hv_conn
  obtain ⟨x, hx⟩ := (H.degree_pos_iff_exists_adj (σ v)).mp (hH_deg (σ v))
  have hxv : x ≠ σ v := Ne.symm hx.ne
  rw [connected_iff]; refine ⟨fun a b => ?_, ‹Nonempty V›⟩
  by_cases ha : a = σ v <;> by_cases hb : b = σ v
  · subst ha; subst hb; exact ⟨Walk.nil⟩
  · subst ha; exact (Adj.reachable hx).trans
      (reachable_of_deleteVert hxv hb (hH_del.preconnected ⟨x, hxv⟩ ⟨b, hb⟩))
  · subst hb; exact (reachable_of_deleteVert ha hxv
      (hH_del.preconnected ⟨a, ha⟩ ⟨x, hxv⟩)).trans (Adj.reachable hx).symm
  · exact reachable_of_deleteVert ha hb (hH_del.preconnected ⟨a, ha⟩ ⟨b, hb⟩)

/-- Isomorphic graphs have the same number of connected components. -/
private theorem numComponents_of_iso {V₁ V₂ : Type*} [Finite V₁] [Finite V₂]
    {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂} (e : G₁ ≃g G₂) :
    Nat.card G₁.ConnectedComponent = Nat.card G₂.ConnectedComponent :=
  Nat.card_congr e.connectedComponentEquiv

/-- Connected graphs (with nonempty vertex set) have exactly one component (via `Nat.card`). -/
private theorem natCard_connectedComponent_of_connected
    {W : Type*} [Nonempty W] {K : SimpleGraph W}
    (hK : K.Connected) :
    Nat.card K.ConnectedComponent = 1 := by
  haveI : Subsingleton K.ConnectedComponent :=
    hK.preconnected.subsingleton_connectedComponent
  haveI : Nonempty K.ConnectedComponent := Nonempty.map K.connectedComponentMk ‹_›
  exact Nat.card_unique

/-- Reachability in `K` between non-`v` vertices follows from reachability in `K - v`. -/
private theorem reachable_of_deleteVert' {W : Type*} {K : SimpleGraph W} {v : W}
    {a b : W} (ha : a ≠ v) (hb : b ≠ v)
    (h : (K.deleteVert v).Reachable ⟨a, ha⟩ ⟨b, hb⟩) : K.Reachable a b :=
  h.map ⟨Subtype.val, fun h => h⟩

/-- The natural map on connected components induced by the inclusion `K - v ↪ K`. -/
private noncomputable def deleteVertToComp {W : Type*} (K : SimpleGraph W) (v : W)
    (C : (K.deleteVert v).ConnectedComponent) : K.ConnectedComponent :=
  C.lift (fun w => K.connectedComponentMk w.val) (fun w₁ w₂ p _ =>
    ConnectedComponent.sound (reachable_of_deleteVert' w₁.2 w₂.2 ⟨p⟩))

@[simp]
private theorem deleteVertToComp_mk {W : Type*} (K : SimpleGraph W) (v : W)
    (w : W) (hw : w ≠ v) :
    deleteVertToComp K v ((K.deleteVert v).connectedComponentMk ⟨w, hw⟩) =
      K.connectedComponentMk w := rfl

/-- The Option-based surjection used for upper bound on `numComponents`. -/
private theorem surjective_optionLift_deleteVertToComp {W : Type*}
    (K : SimpleGraph W) (v : W) :
    Function.Surjective
      (fun o : Option (K.deleteVert v).ConnectedComponent =>
        o.elim (K.connectedComponentMk v) (deleteVertToComp K v)) := by
  intro C
  refine C.ind ?_
  intro w
  by_cases hw : w = v
  · exact ⟨none, by subst hw; rfl⟩
  · exact ⟨some ((K.deleteVert v).connectedComponentMk ⟨w, hw⟩), rfl⟩

/-- Removing any vertex increases the number of components by at most 1 (via `Nat.card`). -/
private theorem natCard_le_deleteVert_succ {W : Type*} [Finite W]
    (K : SimpleGraph W) (v : W) :
    Nat.card K.ConnectedComponent ≤
      Nat.card (K.deleteVert v).ConnectedComponent + 1 := by
  have hle : Nat.card K.ConnectedComponent ≤
      Nat.card (Option (K.deleteVert v).ConnectedComponent) :=
    Nat.card_le_card_of_surjective _ (surjective_optionLift_deleteVertToComp K v)
  simpa [Finite.card_option] using hle

/-- `deleteVertToComp K v` is surjective when `v` has a neighbour. -/
private theorem surjective_deleteVertToComp_of_exists_adj {W : Type*}
    (K : SimpleGraph W) {v : W} (hex : ∃ u, K.Adj v u) :
    Function.Surjective (deleteVertToComp K v) := by
  obtain ⟨u, hu⟩ := hex
  have huv : u ≠ v := hu.ne'
  intro C
  refine C.ind ?_
  intro w
  by_cases hw : w = v
  · refine ⟨(K.deleteVert v).connectedComponentMk ⟨u, huv⟩, ?_⟩
    subst hw
    exact ConnectedComponent.sound hu.symm.reachable
  · exact ⟨(K.deleteVert v).connectedComponentMk ⟨w, hw⟩, rfl⟩

/-- If `v` has positive degree (witnessed by a neighbor `u`), removing `v` does
not decrease the number of components. -/
private theorem natCard_le_deleteVert_of_exists_adj {W : Type*} [Finite W]
    (K : SimpleGraph W) {v : W} (hex : ∃ u, K.Adj v u) :
    Nat.card K.ConnectedComponent ≤ Nat.card (K.deleteVert v).ConnectedComponent :=
  Nat.card_le_card_of_surjective _ (surjective_deleteVertToComp_of_exists_adj K hex)

/-- If `v` has no neighbor, no walk starting away from `v` passes through `v`. -/
private theorem walk_support_avoids_isolated {W : Type*} {K : SimpleGraph W} {v : W}
    (hv : ∀ w, ¬ K.Adj v w) {u w : W} (huv : u ≠ v) (p : K.Walk u w) :
    ∀ x ∈ p.support, x ≠ v := by
  induction p with
  | nil => intro x hx hxv
           rw [Walk.support_nil, List.mem_singleton] at hx
           exact huv (hx ▸ hxv)
  | @cons a b c hadj q ih =>
    intro x hx hxv
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with (rfl | hx)
    · exact huv hxv
    · have hbv : b ≠ v := by
        rintro rfl
        exact hv a hadj.symm
      exact ih hbv x hx hxv

/-- If `v` has no neighbor, any walk between non-`v` vertices has support avoiding `v`. -/
private theorem walk_support_avoids_isolated' {W : Type*} (K : SimpleGraph W) {v : W}
    (hv : ∀ w, ¬ K.Adj v w) {u w : W} (huv : u ≠ v) (p : K.Walk u w) :
    ∀ x ∈ p.support, x ∈ {w : W | w ≠ v} :=
  walk_support_avoids_isolated hv huv p

/-- If `v` has no neighbor, reachability in `K` between non-`v` vertices lifts to `K - v`. -/
private theorem reach_lift_of_isolated {W : Type*} (K : SimpleGraph W) {v : W}
    (hv : ∀ w, ¬ K.Adj v w) {a b : W} (ha : a ≠ v) (hb : b ≠ v)
    (hr : K.Reachable a b) : (K.deleteVert v).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  obtain ⟨p⟩ := hr
  exact ⟨p.induce {w : W | w ≠ v} (walk_support_avoids_isolated' K hv ha p)⟩

/-- If `v` has no neighbor, no non-`v` vertex is reachable to `v`. -/
private theorem not_reach_isolated {W : Type*} (K : SimpleGraph W) {v : W}
    (hv : ∀ w, ¬ K.Adj v w) {w : W} (hwv : w ≠ v) : ¬ K.Reachable v w := by
  intro hr
  obtain ⟨p⟩ := hr.symm
  exact walk_support_avoids_isolated hv hwv p v (Walk.end_mem_support _) rfl

/-- The Option-lift map is injective on `some`, assuming `v` is isolated. -/
private theorem optionLift_inj_some {W : Type*} {K : SimpleGraph W} {v : W}
    (hv : ∀ w, ¬ K.Adj v w) :
    ∀ (C D : (K.deleteVert v).ConnectedComponent),
      deleteVertToComp K v C = deleteVertToComp K v D → C = D := by
  refine ConnectedComponent.ind₂ ?_
  intro wc wd hCD
  change K.connectedComponentMk wc.val = K.connectedComponentMk wd.val at hCD
  have hreach : K.Reachable wc.val wd.val := ConnectedComponent.exact hCD
  have hlift : (K.deleteVert v).Reachable ⟨wc.val, wc.2⟩ ⟨wd.val, wd.2⟩ :=
    reach_lift_of_isolated K hv wc.2 wd.2 hreach
  show (K.deleteVert v).connectedComponentMk wc = (K.deleteVert v).connectedComponentMk wd
  rw [show wc = (⟨wc.val, wc.2⟩ : {w // w ≠ v}) from Subtype.ext rfl,
      show wd = (⟨wd.val, wd.2⟩ : {w // w ≠ v}) from Subtype.ext rfl]
  exact ConnectedComponent.sound hlift

/-- The `none` component (mapped to `[v]`) is distinct from any `some` component. -/
private theorem optionLift_none_ne_some {W : Type*} {K : SimpleGraph W} {v : W}
    (hv : ∀ w, ¬ K.Adj v w) :
    ∀ (D : (K.deleteVert v).ConnectedComponent),
      K.connectedComponentMk v ≠ deleteVertToComp K v D := by
  refine ConnectedComponent.ind ?_
  intro w hD
  change K.connectedComponentMk v = K.connectedComponentMk w.val at hD
  exact not_reach_isolated K hv w.2 (ConnectedComponent.exact hD)

/-- The Option-lift map is injective when `v` is isolated. -/
private theorem optionLift_injective {W : Type*} {K : SimpleGraph W} {v : W}
    (hv : ∀ w, ¬ K.Adj v w) :
    Function.Injective
      (fun o : Option (K.deleteVert v).ConnectedComponent =>
        o.elim (K.connectedComponentMk v) (deleteVertToComp K v)) := by
  intro o₁ o₂ hfd
  match o₁, o₂ with
  | none, none => rfl
  | none, some D => exact absurd hfd (optionLift_none_ne_some hv D)
  | some C, none => exact absurd hfd.symm (optionLift_none_ne_some hv C)
  | some C, some D => exact congrArg some (optionLift_inj_some hv C D hfd)

/-- If `v` is isolated in `K`, removing `v` decreases the number of components by one
(formulated with `Nat.card`). -/
private theorem natCard_deleteVert_of_isolated {W : Type*} [Finite W]
    (K : SimpleGraph W) {v : W} (hv : ∀ w, ¬ K.Adj v w) :
    Nat.card (K.deleteVert v).ConnectedComponent + 1 =
      Nat.card K.ConnectedComponent := by
  have hcard : Nat.card (Option (K.deleteVert v).ConnectedComponent) =
      Nat.card K.ConnectedComponent :=
    Nat.card_eq_of_bijective _
      ⟨optionLift_injective hv, surjective_optionLift_deleteVertToComp K v⟩
  simpa [Finite.card_option] using hcard

/-- A vertex is "isolated" in a graph iff it has no neighbour. -/
private theorem isolated_iff_degree_zero {K : SimpleGraph V} [DecidableRel K.Adj] (v : V) :
    (∀ w, ¬ K.Adj v w) ↔ K.degree v = 0 := by
  rw [show K.degree v = 0 ↔ ¬ 0 < K.degree v from ⟨fun h => by omega, fun h => by omega⟩,
      K.degree_pos_iff_exists_adj v]
  push_neg
  rfl

/-- Injectivity of `deleteVertToComp K v` when `v` has the "non-cut" property within its
connected component: any two vertices `w₁, w₂ ≠ v` reachable in `K` are reachable in `K-v`. -/
private theorem deleteVertToComp_injective_of_nonCut
    {W : Type*} (K : SimpleGraph W) {v : W}
    (hnc : ∀ (w₁ : W) (hw₁ : w₁ ≠ v) (w₂ : W) (hw₂ : w₂ ≠ v),
      K.Reachable w₁ w₂ → (K.deleteVert v).Reachable ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩) :
    Function.Injective (deleteVertToComp K v) := by
  refine ConnectedComponent.ind₂ ?_
  intro wc wd hCD
  change K.connectedComponentMk wc.val = K.connectedComponentMk wd.val at hCD
  have hreach : K.Reachable wc.val wd.val := ConnectedComponent.exact hCD
  have hlift : (K.deleteVert v).Reachable ⟨wc.val, wc.2⟩ ⟨wd.val, wd.2⟩ :=
    hnc wc.val wc.2 wd.val wd.2 hreach
  show (K.deleteVert v).connectedComponentMk wc = (K.deleteVert v).connectedComponentMk wd
  rw [show wc = (⟨wc.val, wc.2⟩ : {w // w ≠ v}) from Subtype.ext rfl,
      show wd = (⟨wd.val, wd.2⟩ : {w // w ≠ v}) from Subtype.ext rfl]
  exact ConnectedComponent.sound hlift

/-- Key structural lemma: if every vertex of `K` has a neighbour in `K`, then there
is a vertex `v` such that removing `v` does not change the number of connected components.

Proof: pick any vertex `v₀` and its connected component `C`. Since `v₀` has a neighbour
in `C`, `C` has ≥ 2 elements, so `C.toSimpleGraph` is connected and nontrivial. By
`Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`, there is
`⟨v, hv⟩ : C` such that `C.toSimpleGraph.induce {⟨v, hv⟩}ᶜ` is connected. This `v` is
non-cut in its component: removing `v` from `K` leaves `C - v` connected, while all
other components are unchanged. Hence `(K - v).nc = K.nc`. -/
private theorem exists_nonCut_of_no_isolated {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) [DecidableRel K.Adj] [Nonempty W]
    (hno : ∀ w : W, ∃ u, K.Adj w u) :
    ∃ v : W, Nat.card (K.deleteVert v).ConnectedComponent = Nat.card K.ConnectedComponent := by
  -- Pick any vertex v₀ and its component C.
  obtain ⟨v₀⟩ := ‹Nonempty W›
  set C : K.ConnectedComponent := K.connectedComponentMk v₀ with hC
  have hv₀_in : v₀ ∈ C.supp := by
    rw [hC]; exact ConnectedComponent.connectedComponentMk_mem
  -- v₀ has a neighbour u; u is in C since K.Adj v₀ u.
  obtain ⟨u, hu⟩ := hno v₀
  have hu_in : u ∈ C.supp := C.mem_supp_of_adj_mem_supp hv₀_in hu
  have huv₀ : u ≠ v₀ := hu.ne'
  -- C.toSimpleGraph is nontrivial (has v₀ and u distinct).
  haveI : Nontrivial (↥C.supp : Type _) :=
    ⟨⟨⟨v₀, hv₀_in⟩, ⟨u, hu_in⟩, fun h => huv₀ (congrArg Subtype.val h.symm)⟩⟩
  haveI : Finite (↥C.supp : Type _) := Set.Finite.to_subtype (Set.toFinite _)
  have hCconn : C.toSimpleGraph.Connected := C.connected_toSimpleGraph
  -- Find a non-cut vertex within C.
  obtain ⟨⟨v, hv_in⟩, hvConn⟩ :=
    hCconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  refine ⟨v, ?_⟩
  -- Show (K - v).nc = K.nc via bijectivity of deleteVertToComp.
  -- Surjectivity: v has a neighbour (from hno), so use natCard_le_deleteVert_of_exists_adj.
  have hK_le : Nat.card K.ConnectedComponent ≤
      Nat.card (K.deleteVert v).ConnectedComponent :=
    natCard_le_deleteVert_of_exists_adj K (hno v)
  -- Injectivity: show that reachable pairs avoiding v in K remain reachable in K - v.
  have hinj : Function.Injective (deleteVertToComp K v) := by
    refine deleteVertToComp_injective_of_nonCut K ?_
    intro w₁ hw₁ w₂ hw₂ hreach
    -- Case: both in C.supp. Use hvConn.
    by_cases h1C : w₁ ∈ C.supp
    · -- If w₁ ∈ C, then w₂ must also be in C (same component).
      have h2C : w₂ ∈ C.supp := by
        rw [ConnectedComponent.mem_supp_iff] at h1C ⊢
        rw [← h1C]; exact (ConnectedComponent.eq).mpr hreach.symm
      -- v ∈ C.supp since hv_in is its membership witness.
      -- Build non-equality in subtype: w₁ ≠ v implies ⟨w₁, h1C⟩ ≠ ⟨v, hv_in⟩ under subtype.
      have hw1_ne : (⟨w₁, h1C⟩ : ↥C.supp) ≠ ⟨v, hv_in⟩ :=
        fun heq => hw₁ (congrArg Subtype.val heq)
      have hw2_ne : (⟨w₂, h2C⟩ : ↥C.supp) ≠ ⟨v, hv_in⟩ :=
        fun heq => hw₂ (congrArg Subtype.val heq)
      -- Use connectivity of C.toSimpleGraph.induce {⟨v,hv_in⟩}ᶜ.
      have hmem1 : (⟨w₁, h1C⟩ : ↥C.supp) ∈ ({⟨v, hv_in⟩}ᶜ : Set ↥C.supp) :=
        Set.mem_compl_singleton_iff.mpr hw1_ne
      have hmem2 : (⟨w₂, h2C⟩ : ↥C.supp) ∈ ({⟨v, hv_in⟩}ᶜ : Set ↥C.supp) :=
        Set.mem_compl_singleton_iff.mpr hw2_ne
      obtain ⟨p⟩ := hvConn.preconnected ⟨⟨w₁, h1C⟩, hmem1⟩ ⟨⟨w₂, h2C⟩, hmem2⟩
      -- Map the walk from C.toSimpleGraph.induce ... into K.deleteVert v.
      -- First: walk in C.toSimpleGraph.induce {⟨v,hv_in⟩}ᶜ ⟶ walk in C.toSimpleGraph
      --       ⟶ walk in K (via C.toSimpleGraph_hom) ⟶ walk avoiding v ⟶ walk in K-v.
      -- Simpler: lift support directly.
      -- Build a K-walk w₁ → w₂ with support avoiding v.
      -- The walk p in `(C.toSimpleGraph.induce {⟨v,hv_in⟩}ᶜ)` has support a list of
      -- vertices in {⟨v,hv_in⟩}ᶜ. Mapping through Subtype.val twice gives K-walk.
      -- Use `Walk.map` with composed hom.
      let f : (C.toSimpleGraph.induce ({⟨v, hv_in⟩}ᶜ : Set ↥C.supp)) →g K :=
        (C.toSimpleGraph_hom).comp (Embedding.induce _).toHom
      have hp_K : K.Walk w₁ w₂ := by
        have := p.map f
        exact this
      -- Map the induced walk into K.deleteVert v via support-avoidance.
      -- Support of walk `p.map f` in K avoids v.
      have hsupp : ∀ x ∈ (p.map f).support, x ∈ {w : W | w ≠ v} := by
        intro x hx
        rw [Walk.support_map] at hx
        -- x = f.toFun y for some y in p.support.
        obtain ⟨y, _, hy⟩ := List.mem_map.mp hx
        -- y ∈ C.toSimpleGraph.induce ({⟨v,hv_in⟩}ᶜ).Walk...so y.val : ↥C.supp, y.val.val : W
        -- y ∈ p.support means y ∈ ({⟨v,hv_in⟩}ᶜ) i.e. y.val ≠ ⟨v, hv_in⟩.
        have hy_ne : y.val ≠ ⟨v, hv_in⟩ := y.2
        -- So x = y.val.val ≠ v.
        intro hxv
        apply hy_ne
        apply Subtype.ext
        show y.val.val = v
        rw [← hy] at hxv
        exact hxv
      exact ⟨(p.map f).induce {w : W | w ≠ v} hsupp⟩
    · -- w₁ ∉ C.supp. Then w₂ ∉ C.supp either (same-component otherwise).
      have h2C : w₂ ∉ C.supp := by
        intro h2C
        apply h1C
        rw [ConnectedComponent.mem_supp_iff] at h2C ⊢
        rw [← h2C]; exact (ConnectedComponent.eq).mpr hreach
      -- v ∈ C.supp but w₁, w₂ ∉ C.supp, so w₁ and w₂ in "other components" of K.
      -- Reachability in K between w₁ and w₂ happens without passing through C,
      -- in particular without passing through v.
      -- Concretely: walk from w₁ to w₂; its support is in the component of w₁, which
      -- is disjoint from C (since w₁ ∉ C.supp). So it doesn't contain v.
      obtain ⟨p⟩ := hreach
      have hsupp : ∀ x ∈ p.support, x ∈ {w : W | w ≠ v} := by
        intro x hx hxv
        -- If x = v, then v is reachable from w₁ (via prefix of p), but v ∈ C while w₁ ∉ C.
        have hR_w1_x : K.Reachable w₁ x := by
          obtain ⟨q, _, _⟩ := Walk.mem_support_iff_exists_append.mp hx
          exact ⟨q⟩
        -- Reachable w₁ v. Since v ∈ C.supp, w₁ also in C.supp — contradiction with h1C.
        apply h1C
        have hv_eq : K.connectedComponentMk v = C := (ConnectedComponent.mem_supp_iff _ _).mp hv_in
        rw [ConnectedComponent.mem_supp_iff]
        calc K.connectedComponentMk w₁
            = K.connectedComponentMk x := ConnectedComponent.sound hR_w1_x
          _ = K.connectedComponentMk v := by rw [hxv]
          _ = C := hv_eq
      exact ⟨p.induce {w : W | w ≠ v} hsupp⟩
  have hcard : Nat.card (K.deleteVert v).ConnectedComponent =
      Nat.card K.ConnectedComponent :=
    Nat.card_eq_of_bijective _ ⟨hinj, surjective_deleteVertToComp_of_exists_adj K (hno v)⟩
  exact hcard

/-- **Number of connected components is reconstructible.**
If `G` and `H` on ≥ 3 vertices share the same deck, they have the same number of
connected components.

Proof strategy (three-way case split):
1. If `G` is connected, then `H` is connected (by `SameDeck.connected`), so both have 1 component.
2. If `G` has an isolated vertex `v`, the deck iso `G - v ≃g H - σ v` gives
   `(G-v).numComponents = (H - σ v).numComponents`. Since degrees match under `σ`,
   `σ v` is isolated in `H`. Thus `G.numComponents = (G-v).numComponents + 1 =
   (H - σ v).numComponents + 1 = H.numComponents`.
3. Otherwise every vertex has positive degree in both graphs. Pick any vertex `v`;
   then `G.numComponents ≤ (G-v).numComponents = (H - σ v).numComponents`, and
   symmetrically for the reverse. So both are equal to `(G-v).numComponents`. -/
theorem SameDeck.numComponents_eq (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) :
    G.numComponents = H.numComponents := by
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  haveI : Finite V := inferInstance
  -- Every vertex has positive degree in G iff in H (via σ), using SameDeck.degree_eq.
  obtain ⟨τ, hτ_deg⟩ := h.degree_eq hV
  have he : G.edgeFinset.card = H.edgeFinset.card := h.card_edgeFinset_eq hV
  have hsymm : H.SameDeck G := SameDeck.symm h
  -- Unfold the deck: obtain bijection σ and isos. (Keep h itself for later uses.)
  obtain ⟨σ, hσ⟩ := id h
  -- Case split: is G connected?
  by_cases hconn : G.Connected
  · -- Case 1: G connected ⇒ H connected ⇒ both have 1 component.
    have hH_conn : H.Connected := h.connected hV hconn
    unfold numComponents
    rw [natCard_connectedComponent_of_connected hconn,
        natCard_connectedComponent_of_connected hH_conn]
  · -- G is not connected.
    -- Case split: does G have an isolated vertex?
    by_cases hiso : ∃ v : V, ∀ w, ¬ G.Adj v w
    · -- Case 2: isolated vertex in G.
      obtain ⟨v, hv⟩ := hiso
      -- Get the deck iso at v.
      obtain ⟨iso⟩ := hσ v
      have hdeg_eq : G.degree v = H.degree (σ v) :=
        degree_eq_of_card_edgeFinset_eq_of_deleteVert_iso he iso
      have hdegG_v : G.degree v = 0 := (isolated_iff_degree_zero v).mp hv
      have hdegH_sv : H.degree (σ v) = 0 := by rw [← hdeg_eq]; exact hdegG_v
      have hv' : ∀ w, ¬ H.Adj (σ v) w := (isolated_iff_degree_zero (σ v)).mpr hdegH_sv
      -- Apply the isolated-vertex formula on both sides.
      have hG := natCard_deleteVert_of_isolated G hv
      have hH := natCard_deleteVert_of_isolated H hv'
      -- Apply iso on connected components of G-v and H-σv.
      have hIso_comps : Nat.card (G.deleteVert v).ConnectedComponent =
          Nat.card (H.deleteVert (σ v)).ConnectedComponent :=
        numComponents_of_iso iso
      -- Assemble.
      unfold numComponents
      omega
    · -- Case 3: every vertex has a neighbor in G.
      push_neg at hiso
      -- Transfer: every vertex also has a neighbor in H (via degree match through τ).
      have hiso_H : ∀ w : V, ∃ u, H.Adj w u := by
        intro w
        have hdegG : 0 < G.degree (τ.symm w) :=
          (G.degree_pos_iff_exists_adj (τ.symm w)).mpr (hiso (τ.symm w))
        have hdeg := hτ_deg (τ.symm w)
        rw [τ.apply_symm_apply] at hdeg
        have hdegH : 0 < H.degree w := by rw [← hdeg]; exact hdegG
        exact (H.degree_pos_iff_exists_adj w).mp hdegH
      -- Find a non-cut vertex v₀ in G such that (G - v₀).nc = G.nc.
      obtain ⟨v₀, hv₀_eq⟩ := exists_nonCut_of_no_isolated G hiso
      -- Via the deck iso at v₀, (G - v₀).nc = (H - σ v₀).nc.
      obtain ⟨iso₀⟩ := hσ v₀
      have hIso₀ : Nat.card (G.deleteVert v₀).ConnectedComponent =
          Nat.card (H.deleteVert (σ v₀)).ConnectedComponent :=
        numComponents_of_iso iso₀
      -- σ v₀ has a neighbor in H, so H.nc ≤ (H - σ v₀).nc = G.nc.
      have hH_le : Nat.card H.ConnectedComponent ≤
          Nat.card (H.deleteVert (σ v₀)).ConnectedComponent :=
        natCard_le_deleteVert_of_exists_adj H (hiso_H (σ v₀))
      have hH_le_G : Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent := by
        rw [← hv₀_eq, hIso₀]; exact hH_le
      -- Reverse direction: find non-cut vertex w₀ in H similarly.
      obtain ⟨w₀, hw₀_eq⟩ := exists_nonCut_of_no_isolated H hiso_H
      -- Use the SYMMETRIC deck: hsymm : H.SameDeck G. At vertex w₀, get iso H - w₀ ≃g G - σ.symm w₀.
      obtain ⟨σ_sym, hσ_sym⟩ := id hsymm
      obtain ⟨iso₁⟩ := hσ_sym w₀
      have hIso₁ : Nat.card (H.deleteVert w₀).ConnectedComponent =
          Nat.card (G.deleteVert (σ_sym w₀)).ConnectedComponent :=
        numComponents_of_iso iso₁
      -- σ_sym w₀ has a neighbor in G.
      have hG_le : Nat.card G.ConnectedComponent ≤
          Nat.card (G.deleteVert (σ_sym w₀)).ConnectedComponent :=
        natCard_le_deleteVert_of_exists_adj G (hiso (σ_sym w₀))
      have hG_le_H : Nat.card G.ConnectedComponent ≤ Nat.card H.ConnectedComponent := by
        rw [← hw₀_eq, hIso₁]; exact hG_le
      -- Combine.
      unfold numComponents; omega

end

end SimpleGraph
