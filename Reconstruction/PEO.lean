import Reconstruction.Dirac
import Mathlib.Tactic.Abel
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Perfect elimination orderings

A **perfect elimination ordering** (PEO) of `G` lists the vertices so that for
every vertex `v`, the neighbours of `v` appearing later in the list form a
clique. Dirac's theorem (`diracSimplicial`) gives the main direction of the
classical characterization: every finite chordal graph has a PEO, obtained by
repeatedly peeling off a simplicial vertex.

## Main results

* `SimpleGraph.IsPEO` / `SimpleGraph.HasPEO` — the definition.
* `SimpleGraph.isClique_neighbors_of_isSimplicial_induce` — a vertex simplicial
  in `G[s]` has its `s`-neighbourhood a clique in `G`.
* `SimpleGraph.hasPEO_of_chordal` — every finite chordal graph has a PEO.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- `l` is a **perfect elimination ordering** of `G`: it lists every vertex once,
and for each suffix `v :: rest`, the later neighbours of `v` (those in `rest`)
form a clique. -/
def IsPEO (G : SimpleGraph V) (l : List V) : Prop :=
  l.Nodup ∧ (∀ v : V, v ∈ l) ∧
    ∀ v rest, v :: rest <:+ l → G.IsClique {w | w ∈ rest ∧ G.Adj v w}

/-- `G` has a perfect elimination ordering. -/
def HasPEO (G : SimpleGraph V) : Prop := ∃ l : List V, G.IsPEO l

/-- A vertex simplicial in the induced subgraph `G[s]` has its `s`-neighbourhood
a clique in `G` (induced adjacency is `G`-adjacency). -/
theorem isClique_neighbors_of_isSimplicial_induce {s : Set V} {v : V} (hv : v ∈ s)
    (h : (G.induce s).IsSimplicial ⟨v, hv⟩) : G.IsClique {w | w ∈ s ∧ G.Adj v w} := by
  rintro p ⟨hps, hpv⟩ q ⟨hqs, hqv⟩ hpq
  have hpm : (⟨p, hps⟩ : s) ∈ (G.induce s).neighborSet ⟨v, hv⟩ := hpv
  have hqm : (⟨q, hqs⟩ : s) ∈ (G.induce s).neighborSet ⟨v, hv⟩ := hqv
  exact h hpm hqm (fun heq => hpq (congrArg Subtype.val heq))

/-- The inductive core: on any `Finset s` of vertices, peeling off simplicial
vertices (Dirac) yields a list enumerating `s` whose every suffix `v :: rest` has
`v`'s later neighbours forming a clique. -/
theorem peo_aux (hchord : G.IsChordal) :
    ∀ (n : ℕ) (s : Finset V), s.card ≤ n →
      ∃ l : List V, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ s) ∧
        ∀ v rest, v :: rest <:+ l → G.IsClique {w | w ∈ rest ∧ G.Adj v w} := by
  classical
  intro n
  induction n with
  | zero =>
    intro s hs
    rw [Nat.le_zero, Finset.card_eq_zero] at hs
    subst hs
    exact ⟨[], List.nodup_nil, by simp, by simp⟩
  | succ n ih =>
    intro s hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · exact ⟨[], List.nodup_nil, by simp, by simp⟩
    · -- a simplicial vertex of `G[s]`, peeled off the front
      obtain ⟨⟨v, hv_s⟩, hvsimp⟩ := diracSimplicial (G.induce (↑s : Set V))
        (hchord.induce ↑s) (Finset.coe_nonempty.mpr hne).to_subtype
      have hvs : v ∈ s := hv_s
      have hclq : G.IsClique {w | w ∈ (↑s : Set V) ∧ G.Adj v w} :=
        isClique_neighbors_of_isSimplicial_induce hv_s hvsimp
      obtain ⟨l', hl'nd, hl'cov, hl'prop⟩ := ih (s.erase v)
        (by have := Finset.card_erase_of_mem hvs; omega)
      have hvl' : v ∉ l' := fun h => (Finset.mem_erase.mp ((hl'cov v).mp h)).1 rfl
      refine ⟨v :: l', List.nodup_cons.mpr ⟨hvl', hl'nd⟩, ?_, ?_⟩
      · intro x
        rw [List.mem_cons, hl'cov x, Finset.mem_erase]
        constructor
        · rintro (rfl | ⟨_, hx⟩)
          exacts [hvs, hx]
        · intro hx
          by_cases hxv : x = v
          exacts [Or.inl hxv, Or.inr ⟨hxv, hx⟩]
      · intro u rest hsuf
        rw [List.suffix_cons_iff] at hsuf
        rcases hsuf with heq | hsuf'
        · obtain ⟨rfl, rfl⟩ := List.cons.inj heq
          rintro p ⟨hpl', hpadj⟩ q ⟨hql', hqadj⟩ hpq
          exact hclq ⟨(Finset.mem_erase.mp ((hl'cov p).mp hpl')).2, hpadj⟩
            ⟨(Finset.mem_erase.mp ((hl'cov q).mp hql')).2, hqadj⟩ hpq
        · exact hl'prop u rest hsuf'

/-- **Every finite chordal graph has a perfect elimination ordering.** The main
direction of the Dirac/Fulkerson–Gross characterization of chordal graphs. -/
theorem hasPEO_of_chordal [Finite V] (hchord : G.IsChordal) : G.HasPEO := by
  haveI := Fintype.ofFinite V
  obtain ⟨l, hnd, hcov, hprop⟩ :=
    peo_aux hchord (Fintype.card V) Finset.univ Finset.card_univ.le
  exact ⟨l, hnd, fun v => (hcov v).mpr (Finset.mem_univ v), hprop⟩

/-! ### The converse: a perfect elimination ordering implies chordality -/

/-- In a `Nodup` list `l`, a nonempty set `S` of its elements has an earliest
member `v`: the suffix `v :: rest` of `l` starting at `v` contains every other
element of `S`. -/
theorem exists_earliest_suffix : ∀ (l : List V), l.Nodup → ∀ (S : Set V), S.Nonempty →
    (∀ a ∈ S, a ∈ l) →
    ∃ v rest, v ∈ S ∧ v :: rest <:+ l ∧ ∀ a ∈ S, a ≠ v → a ∈ rest := by
  intro l
  induction l with
  | nil =>
    intro _ S hSne hSsub
    obtain ⟨a, ha⟩ := hSne
    exact absurd (hSsub a ha) (by simp)
  | cons x l' ih =>
    intro hnd S hSne hSsub
    by_cases hxS : x ∈ S
    · refine ⟨x, l', hxS, List.suffix_rfl, ?_⟩
      intro a haS hax
      rcases List.mem_cons.mp (hSsub a haS) with rfl | h
      · exact absurd rfl hax
      · exact h
    · have hSsub' : ∀ a ∈ S, a ∈ l' := by
        intro a haS
        rcases List.mem_cons.mp (hSsub a haS) with rfl | h
        · exact absurd haS hxS
        · exact h
      obtain ⟨v, rest, hvS, hsuf, hrest⟩ := ih (List.nodup_cons.mp hnd).2 S hSne hSsub'
      exact ⟨v, rest, hvS, hsuf.trans (List.suffix_cons x l'), hrest⟩

/-- In `cycleGraph n` (`n ≥ 2`), each vertex is adjacent to its successor. -/
theorem cycleGraph_adj_succ {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (cycleGraph n).Adj i (i + 1) := by
  rw [cycleGraph_adj']; right; rw [add_sub_cancel_left]
  exact Fin.val_one' n ▸ Nat.mod_eq_of_lt (by omega)

/-- In `cycleGraph n` (`n ≥ 2`), each vertex is adjacent to its predecessor. -/
theorem cycleGraph_adj_pred {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (cycleGraph n).Adj i (i - 1) := by
  rw [cycleGraph_adj']; left; rw [sub_sub_cancel]
  exact Fin.val_one' n ▸ Nat.mod_eq_of_lt (by omega)

/-- In `cycleGraph n` (`n ≥ 4`), the two neighbours `i - 1` and `i + 1` of a
vertex are non-adjacent — the chordless property of a cycle of length `≥ 4`. -/
theorem cycleGraph_not_adj_pred_succ {n : ℕ} [NeZero n] (hn : 4 ≤ n) (i : Fin n) :
    ¬ (cycleGraph n).Adj (i - 1) (i + 1) := by
  have e1 : (i - 1) - (i + 1) = -(1 + 1 : Fin n) := by abel
  have e2 : (i + 1) - (i - 1) = (1 + 1 : Fin n) := by abel
  rw [cycleGraph_adj', e1, e2]
  simp only [Fin.val_neg', Fin.add_def, Fin.val_one']
  rw [Nat.mod_eq_of_lt (show 1 < n by omega), Nat.mod_eq_of_lt (show 1 + 1 < n by omega),
    Nat.mod_eq_of_lt (show n - (1 + 1) < n by omega)]
  omega

/-- **The converse: a graph with a perfect elimination ordering is chordal.**
In an induced `≥ 4`-cycle, the PEO-earliest vertex `v` has both its cycle
neighbours later in the order, so the PEO forces them adjacent — contradicting
the chordlessness of the cycle. -/
theorem isChordal_of_hasPEO (h : G.HasPEO) : G.IsChordal := by
  obtain ⟨l, hnd, hcov, hprop⟩ := h
  intro n hn
  haveI : NeZero n := ⟨by omega⟩
  rw [isEmpty_iff]
  intro f
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, rest, hvS, hsuf, hrest⟩ :=
    exists_earliest_suffix l hnd (Set.range f) (Set.range_nonempty f) (fun a _ => hcov a)
  obtain ⟨i₀, rfl⟩ := hvS
  have v1 : (1 : Fin n).val = 1 := Fin.val_one' n ▸ Nat.mod_eq_of_lt (by omega)
  have hone : (1 : Fin n) ≠ 0 := fun h0 => by
    have := congrArg Fin.val h0; rw [v1, Fin.val_zero] at this; omega
  have hone2 : (1 + 1 : Fin n) ≠ 0 := fun h0 => by
    have := congrArg Fin.val h0
    simp only [Fin.add_def, v1, Fin.val_zero] at this
    rw [Nat.mod_eq_of_lt (show 1 + 1 < n by omega)] at this
    omega
  have hne1 : i₀ - 1 ≠ i₀ := fun h => hone (sub_eq_self.mp h)
  have hne2 : i₀ + 1 ≠ i₀ := fun h => hone (add_left_cancel (h.trans (add_zero i₀).symm))
  have hne3 : i₀ - 1 ≠ i₀ + 1 := fun h => hone2 (neg_eq_zero.mp (by
    have e1 : (i₀ - 1) - (i₀ + 1) = -(1 + 1 : Fin n) := by abel
    rw [← e1, sub_eq_zero.mpr h]))
  have hr1 : f (i₀ - 1) ∈ rest :=
    hrest _ ⟨i₀ - 1, rfl⟩ (fun heq => hne1 (f.injective heq))
  have hr2 : f (i₀ + 1) ∈ rest :=
    hrest _ ⟨i₀ + 1, rfl⟩ (fun heq => hne2 (f.injective heq))
  have hadj1 : G.Adj (f i₀) (f (i₀ - 1)) :=
    f.map_adj_iff.mpr (cycleGraph_adj_pred (by omega) i₀)
  have hadj2 : G.Adj (f i₀) (f (i₀ + 1)) :=
    f.map_adj_iff.mpr (cycleGraph_adj_succ (by omega) i₀)
  have hadj3 : G.Adj (f (i₀ - 1)) (f (i₀ + 1)) :=
    hprop (f i₀) rest hsuf ⟨hr1, hadj1⟩ ⟨hr2, hadj2⟩ (fun heq => hne3 (f.injective heq))
  exact cycleGraph_not_adj_pred_succ hn i₀ (f.map_adj_iff.mp hadj3)

/-- **Chordal ⟺ has a perfect elimination ordering** (Dirac/Fulkerson–Gross). -/
theorem isChordal_iff_hasPEO [Finite V] : G.IsChordal ↔ G.HasPEO :=
  ⟨hasPEO_of_chordal, isChordal_of_hasPEO⟩

end SimpleGraph
