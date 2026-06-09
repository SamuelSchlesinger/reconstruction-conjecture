import Reconstruction.MinimalSeparator
import Reconstruction.InducedCycle
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Minimal separators are cliques

The capstone of the chordal structure layer: in a chordal graph, an
inclusion-minimal separator is a clique. The proof contradicts chordality by
exhibiting an induced cycle of length `≥ 4`: take two non-adjacent vertices
`x, y` of the separator `S`; by minimality each has a neighbour in two distinct
components `A, B` of `G − S`; the two shortest `x`–`y` paths confined to
`A ∪ {x,y}` and `B ∪ {x,y}` are chordless arcs sharing only `x, y`, with no
cross-edges, so they glue (`inducedCycleEmbedding_of_paths`) into an induced
cycle — impossible in a chordal graph.

## Main results

* `SimpleGraph.exists_chordless_arc` — a chordless `x`–`y` arc through a
  prescribed component (a geodesic in the induced subgraph on that component
  plus `x, y`).
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

open Walk

/-- **A chordless arc through a component.** Given non-adjacent `x ≠ y`, a
component of `G − S` represented by `u₀ ∉ S`, and neighbours of `x` and of `y`
in that component, there is a chordless `x`–`y` path `P` of length `≥ 2` whose
interior lies entirely in that component. It is a shortest path in the induced
subgraph on the component together with `x, y`; being a geodesic makes it
chordless (`geodesic_not_adj_of_lt`), and the induced subgraph confines its
interior to the component. -/
theorem exists_chordless_arc {S : Set V} {x y : V} (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
    {u₀ : V} (hu₀ : u₀ ∉ S)
    (hax : ∃ a, ∃ (ha : a ∉ S), (G.induce Sᶜ).connectedComponentMk ⟨a, ha⟩
      = (G.induce Sᶜ).connectedComponentMk ⟨u₀, hu₀⟩ ∧ G.Adj x a)
    (hay : ∃ a, ∃ (ha : a ∉ S), (G.induce Sᶜ).connectedComponentMk ⟨a, ha⟩
      = (G.induce Sᶜ).connectedComponentMk ⟨u₀, hu₀⟩ ∧ G.Adj y a) :
    ∃ P : G.Walk x y, P.IsPath ∧ 2 ≤ P.length ∧
      (∀ i j, i + 1 < j → j ≤ P.length → ¬ G.Adj (P.getVert i) (P.getVert j)) ∧
      (∀ i, 0 < i → i < P.length → ∃ (h : P.getVert i ∉ S),
        (G.induce Sᶜ).connectedComponentMk ⟨P.getVert i, h⟩
          = (G.induce Sᶜ).connectedComponentMk ⟨u₀, hu₀⟩) := by
  classical
  obtain ⟨ax, hax_S, hax_c, hx_ax⟩ := hax
  obtain ⟨ay, hay_S, hay_c, hy_ay⟩ := hay
  set Cset : Set V :=
    insert x (insert y {v | ∃ (h : v ∉ S),
      (G.induce Sᶜ).connectedComponentMk ⟨v, h⟩
        = (G.induce Sᶜ).connectedComponentMk ⟨u₀, hu₀⟩}) with hCset
  have hxC : x ∈ Cset := Set.mem_insert x _
  have hyC : y ∈ Cset := Set.mem_insert_of_mem _ (Set.mem_insert y _)
  have hmemC : ∀ (v : V) (h : v ∉ S), (G.induce Sᶜ).connectedComponentMk ⟨v, h⟩
      = (G.induce Sᶜ).connectedComponentMk ⟨u₀, hu₀⟩ → v ∈ Cset :=
    fun v h hv => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨h, hv⟩)
  have haxC : ax ∈ Cset := hmemC ax hax_S hax_c
  have hayC : ay ∈ Cset := hmemC ay hay_S hay_c
  -- The middle walk `ax → ay` lives in `Sᶜ`, entirely in `u₀`'s component.
  obtain ⟨W₀⟩ : (G.induce Sᶜ).Reachable ⟨ax, hax_S⟩ ⟨ay, hay_S⟩ :=
    ConnectedComponent.eq.mp (hax_c.trans hay_c.symm)
  -- Its image in `G` is fully inside `Cset`.
  have hWsub : ∀ w ∈ (W₀.map (Embedding.induce Sᶜ).toHom).support, w ∈ Cset := by
    intro w hw
    rw [Walk.support_map, List.mem_map] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    refine hmemC z.1 z.2 ?_
    have hzr : (G.induce Sᶜ).Reachable ⟨ax, hax_S⟩ z := ⟨W₀.takeUntil z hz⟩
    rw [show (⟨z.1, z.2⟩ : ↥Sᶜ) = z from rfl, ← ConnectedComponent.eq.mpr hzr]
    exact hax_c
  -- Assemble the full `x → y` walk and lift it into `G[Cset]`.
  have hfull : ∀ w ∈ (cons hx_ax ((W₀.map (Embedding.induce Sᶜ).toHom).append
      (cons hy_ay.symm nil))).support, w ∈ Cset := by
    intro w hw
    rw [support_cons, support_append] at hw
    simp only [support_cons, support_nil, List.tail_cons, List.mem_cons,
      List.mem_append, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | hw | rfl
    · exact hxC
    · exact hWsub _ hw
    · exact hyC
  have hreach : (G.induce Cset).Reachable ⟨x, hxC⟩ ⟨y, hyC⟩ :=
    ⟨(cons hx_ax ((W₀.map (Embedding.induce Sᶜ).toHom).append
      (cons hy_ay.symm nil))).induce Cset hfull⟩
  -- A shortest such walk: a chordless geodesic.
  obtain ⟨P', hP'⟩ := hreach.exists_walk_length_eq_dist
  have hP'path : P'.IsPath := P'.isPath_of_length_eq_dist hP'
  refine ⟨P'.map (Embedding.induce Cset).toHom, ?_, ?_, ?_, ?_⟩
  · exact map_isPath_of_injective (Embedding.induce (G := G) Cset).injective hP'path
  · rw [length_map, hP']
    have hne : (⟨x, hxC⟩ : ↥Cset) ≠ ⟨y, hyC⟩ := fun h => hxy (congrArg Subtype.val h)
    have hnadj' : ¬ (G.induce Cset).Adj ⟨x, hxC⟩ ⟨y, hyC⟩ := fun h => hnadj h
    have := hreach.one_lt_dist_of_ne_of_not_adj hne hnadj'
    omega
  · intro i j hij hj
    rw [length_map] at hj
    intro hadj
    rw [getVert_map, getVert_map] at hadj
    simp only [Embedding.coe_toHom] at hadj
    rw [(Embedding.induce Cset).map_adj_iff] at hadj
    exact P'.geodesic_not_adj_of_lt hP' hij hj hadj
  · intro i hi hilt
    rw [length_map] at hilt
    rw [getVert_map]
    have hne_x : P'.getVert i ≠ ⟨x, hxC⟩ := by
      intro h
      have : i = 0 := hP'path.getVert_injOn hilt.le (Nat.zero_le _)
        (h.trans P'.getVert_zero.symm)
      omega
    have hne_y : P'.getVert i ≠ ⟨y, hyC⟩ := by
      intro h
      have : i = P'.length := hP'path.getVert_injOn hilt.le (le_refl P'.length)
        (h.trans P'.getVert_length.symm)
      omega
    have hival : (P'.getVert i).1 ∈ Cset := (P'.getVert i).2
    rw [Set.mem_insert_iff, Set.mem_insert_iff] at hival
    rcases hival with h | h | h
    · exact absurd (Subtype.ext h) hne_x
    · exact absurd (Subtype.ext h) hne_y
    · exact h

/-- **Minimal separators are cliques** (Dirac's lemma — the chordal-structure
crux). In a chordal graph, an inclusion-minimal separator induces a clique:
two non-adjacent separator vertices would, by minimality, have neighbours in two
distinct components of `G − S`, and the two shortest paths confined to those
components glue into an induced cycle of length `≥ 4`, impossible in a chordal
graph. -/
theorem minimalSeparatorClique : MinimalSeparatorClique V := by
  intro G S hchordal hsep hmin x hx y hy hxy
  by_contra hnadj
  obtain ⟨hconn, u₀, w₀, hu₀, hw₀, hsepuw⟩ := (isSeparator_iff_separates G S).mp hsep
  have hsepwu : ¬ (G.induce Sᶜ).Reachable ⟨w₀, hw₀⟩ ⟨u₀, hu₀⟩ := fun h => hsepuw h.symm
  have hAB : (G.induce Sᶜ).connectedComponentMk ⟨u₀, hu₀⟩
      ≠ (G.induce Sᶜ).connectedComponentMk ⟨w₀, hw₀⟩ :=
    fun h => hsepuw (ConnectedComponent.eq.mp h)
  -- Chordless arcs through the two components.
  obtain ⟨P, hPpath, hPlen, hPchord, hPint⟩ := exists_chordless_arc hxy hnadj hu₀
    (exists_adj_mem_component hconn hmin hx hu₀ hw₀ hsepuw)
    (exists_adj_mem_component hconn hmin hy hu₀ hw₀ hsepuw)
  obtain ⟨Q, hQpath, hQlen, hQchord, hQint⟩ := exists_chordless_arc hxy hnadj hw₀
    (exists_adj_mem_component hconn hmin hx hw₀ hu₀ hsepwu)
    (exists_adj_mem_component hconn hmin hy hw₀ hu₀ hsepwu)
  -- Support characterizations: a vertex of an arc is `x`, `y`, or in its component.
  have hPchar : ∀ a ∈ P.support, a = x ∨ a = y ∨ ∃ (h : a ∉ S),
      (G.induce Sᶜ).connectedComponentMk ⟨a, h⟩
        = (G.induce Sᶜ).connectedComponentMk ⟨u₀, hu₀⟩ := by
    intro a ha
    rw [Walk.mem_support_iff_exists_getVert] at ha
    obtain ⟨k, hk_eq, hk_le⟩ := ha
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · left; rw [← hk_eq, hk0, P.getVert_zero]
    · rcases eq_or_lt_of_le hk_le with hklen | hklt
      · right; left; rw [← hk_eq, hklen, P.getVert_length]
      · right; right; rw [← hk_eq]; exact hPint k hkpos hklt
  have hQchar : ∀ a ∈ Q.support, a = x ∨ a = y ∨ ∃ (h : a ∉ S),
      (G.induce Sᶜ).connectedComponentMk ⟨a, h⟩
        = (G.induce Sᶜ).connectedComponentMk ⟨w₀, hw₀⟩ := by
    intro a ha
    rw [Walk.mem_support_iff_exists_getVert] at ha
    obtain ⟨k, hk_eq, hk_le⟩ := ha
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · left; rw [← hk_eq, hk0, Q.getVert_zero]
    · rcases eq_or_lt_of_le hk_le with hklen | hklt
      · right; left; rw [← hk_eq, hklen, Q.getVert_length]
      · right; right; rw [← hk_eq]; exact hQint k hkpos hklt
  -- The arcs share only `x, y`.
  have hshare : ∀ a ∈ P.support, a ∈ Q.support → a = x ∨ a = y := by
    intro a haP haQ
    rcases hPchar a haP with h | h | ⟨hPaS, hPac⟩
    · exact Or.inl h
    · exact Or.inr h
    · rcases hQchar a haQ with h | h | ⟨_, hQac⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (hPac.symm.trans hQac) hAB
  -- No cross-edge between the two interiors (distinct components).
  have hcross : ∀ i j, 0 < i → i < P.length → 0 < j → j < Q.length →
      ¬ G.Adj (P.getVert i) (Q.getVert j) := by
    intro i j hi hil hj hjl hadj
    obtain ⟨hPi, hPic⟩ := hPint i hi hil
    obtain ⟨hQj, hQjc⟩ := hQint j hj hjl
    exact hAB (hPic.symm.trans ((adj_connectedComponentMk_eq hadj hPi hQj).trans hQjc))
  have hx_notin : x ∉ P.support.tail := by
    have h := hPpath.support_nodup
    rw [P.support_eq_cons] at h
    exact (List.nodup_cons.mp h).1
  have hy_notin : y ∉ Q.reverse.support.tail := by
    have h := hQpath.reverse.support_nodup
    rw [Q.reverse.support_eq_cons] at h
    exact (List.nodup_cons.mp h).1
  -- The arcs are edge-disjoint (a shared edge would join `x, y`).
  have hedj : List.Disjoint P.edges Q.edges := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      intro heP heQ
      have hab : G.Adj a b := P.adj_of_mem_edges heP
      rcases hshare a (P.fst_mem_support_of_mem_edges heP)
          (Q.fst_mem_support_of_mem_edges heQ) with rfl | rfl <;>
        rcases hshare b (P.snd_mem_support_of_mem_edges heP)
          (Q.snd_mem_support_of_mem_edges heQ) with rfl | rfl
      · exact hab.ne rfl
      · exact hnadj hab
      · exact hnadj hab.symm
      · exact hab.ne rfl
  -- Their interiors are disjoint.
  have hsupp : List.Disjoint P.support.tail Q.reverse.support.tail := by
    intro a haP haQ
    have haP' : a ∈ P.support := List.mem_of_mem_tail haP
    have haQ' : a ∈ Q.support := by
      have h : a ∈ Q.reverse.support := List.mem_of_mem_tail haQ
      rwa [support_reverse, List.mem_reverse] at h
    rcases hshare a haP' haQ' with rfl | rfl
    · exact hx_notin haP
    · exact hy_notin haQ
  -- Glue into an induced cycle of length `≥ 4`, contradicting chordality.
  have hemb := inducedCycleEmbedding_of_paths hxy P Q hPpath hQpath hPlen hQlen
    hPchord hQchord hcross hedj hsupp
  exact (hchordal (P.length + Q.length) (by omega)).false hemb.some

end SimpleGraph
