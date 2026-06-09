import Reconstruction.Chordal
import Reconstruction.Geodesic
import Reconstruction.CycleFromPaths
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Chordless cycle ⟶ `cycleGraph` embedding (the bridge)

Converts a chordless closed walk (a cycle whose only adjacencies among its
vertices are the cyclically-consecutive ones) into the embedding
`cycleGraph n ↪g G` that `IsChordal` forbids. This is the bridge between the
classical "induced cycle" produced by the separator argument and the
embedding-based definition of chordality.

## Main results

* `SimpleGraph.cycleGraph_adj_val` — a `.val`-level characterization of
  `cycleGraph n` adjacency (consecutive or wrap-around), the keystone.
* `SimpleGraph.inducedCycleEmbedding` — a chordless `IsCycle` walk of length
  `n ≥ 4` yields `cycleGraph n ↪g G`.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Value-level characterization of `cycleGraph n` adjacency for `n ≥ 4`: two
vertices are adjacent iff their indices are consecutive or wrap around the cycle.
This eliminates the opaque modular `Fin` subtraction once and for all. -/
theorem cycleGraph_adj_val {n : ℕ} (hn : 4 ≤ n) (i j : Fin n) :
    (cycleGraph n).Adj i j ↔
      i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
        (i.val = 0 ∧ j.val = n - 1) ∨ (j.val = 0 ∧ i.val = n - 1) := by
  rw [cycleGraph_adj']
  constructor
  · rintro (h | h) <;>
      · apply_fun (Nat.cast : ℕ → ℤ) at h
        rw [Fin.coe_int_sub_eq_ite] at h
        fin_omega
  · rintro (h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;>
      [right; left; left; right] <;>
      · rw [← @Nat.cast_inj ℤ, Fin.coe_int_sub_eq_ite]
        fin_omega

open Walk in
/-- **The bridge.** A chordless `IsCycle` walk of length `n ≥ 4` — chordless in
the sense that the only `G`-adjacencies among its `n` vertices `p.getVert 0, …,
p.getVert (n-1)` are the cyclically-consecutive ones (`hchord`) — yields a graph
embedding `cycleGraph n ↪g G`, i.e. an induced `n`-cycle. This is exactly the
object `IsChordal` forbids, so producing one for `n ≥ 4` contradicts chordality. -/
theorem inducedCycleEmbedding {u : V} {n : ℕ} (hn : 4 ≤ n) (p : G.Walk u u)
    (hp : p.IsCycle) (hlen : p.length = n)
    (hchord : ∀ a b : Fin n,
      G.Adj (p.getVert a.val) (p.getVert b.val) → (cycleGraph n).Adj a b) :
    Nonempty ((cycleGraph n) ↪g G) := by
  refine ⟨⟨⟨fun a => p.getVert a.val, ?_⟩, ?_⟩⟩
  · -- injectivity of `getVert` on `Fin n`
    intro a b hab
    have ha : a.val ≤ p.length - 1 := by have := a.isLt; omega
    have hb : b.val ≤ p.length - 1 := by have := b.isLt; omega
    exact Fin.ext (hp.getVert_injOn' ha hb hab)
  · -- the adjacency biconditional
    intro a b
    change G.Adj (p.getVert a.val) (p.getVert b.val) ↔ (cycleGraph n).Adj a b
    refine ⟨hchord a b, fun hcyc => ?_⟩
    rw [cycleGraph_adj_val hn] at hcyc
    have ha := a.isLt
    have hb := b.isLt
    have hu : p.getVert n = u := by rw [← hlen]; exact p.getVert_length
    rcases hcyc with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hadj := p.adj_getVert_succ (i := a.val) (by omega)
      rwa [h] at hadj
    · have hadj := p.adj_getVert_succ (i := b.val) (by omega)
      rw [h] at hadj
      exact hadj.symm
    · have hadj := p.adj_getVert_succ (i := n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega, hu] at hadj
      rw [h1, h2, getVert_zero]
      exact hadj.symm
    · have hadj := p.adj_getVert_succ (i := n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega, hu] at hadj
      rw [h1, h2, getVert_zero]
      exact hadj

open Walk in
/-- **Two-arc induced cycle.** Glue two internally-disjoint chordless arcs
`P, Q : x → y` (each a shortest path, hence chordless: no chord between
non-consecutive vertices; plus no edge between the two interiors) into an induced
cycle `cycleGraph (|P| + |Q|) ↪g G`. This is the form the separator argument
feeds: `P` runs through one component of `G − S`, `Q` through another, so they
share only `x, y`, have no cross-edges, and `x ≁ y`. -/
theorem inducedCycleEmbedding_of_paths {x y : V} (hxy : x ≠ y)
    (P Q : G.Walk x y) (hP : P.IsPath) (hQ : Q.IsPath)
    (hPlen : 2 ≤ P.length) (hQlen : 2 ≤ Q.length)
    (hPchord : ∀ i j, i + 1 < j → j ≤ P.length → ¬ G.Adj (P.getVert i) (P.getVert j))
    (hQchord : ∀ i j, i + 1 < j → j ≤ Q.length → ¬ G.Adj (Q.getVert i) (Q.getVert j))
    (hcross : ∀ i j, 0 < i → i < P.length → 0 < j → j < Q.length →
      ¬ G.Adj (P.getVert i) (Q.getVert j))
    (hedj : List.Disjoint P.edges Q.edges)
    (hsupp : List.Disjoint P.support.tail Q.reverse.support.tail) :
    Nonempty ((cycleGraph (P.length + Q.length)) ↪g G) := by
  have hC := isCycle_append_reverse hP hQ hxy hedj hsupp
  have hClen : (P.append Q.reverse).length = P.length + Q.length := by
    rw [length_append, length_reverse]
  have hcv : ∀ k, (P.append Q.reverse).getVert k
      = if k < P.length then P.getVert k else Q.getVert (Q.length - (k - P.length)) := by
    intro k; rw [getVert_append, getVert_reverse]
  refine inducedCycleEmbedding (by omega) (P.append Q.reverse) hC hClen ?_
  -- `key`: prove `hchord` for the ordered case `a ≤ b`, then close by symmetry.
  have key : ∀ a b : Fin (P.length + Q.length), a.val ≤ b.val →
      G.Adj ((P.append Q.reverse).getVert a.val) ((P.append Q.reverse).getVert b.val) →
      (cycleGraph (P.length + Q.length)).Adj a b := by
    intro a b hab hadj
    have ha := a.isLt
    have hb := b.isLt
    rw [hcv a.val, hcv b.val] at hadj
    rw [cycleGraph_adj_val (by omega)]
    by_cases hAa : a.val < P.length <;> by_cases hAb : b.val < P.length
    · -- both indices on `P`
      rw [if_pos hAa, if_pos hAb] at hadj
      have hne : a.val ≠ b.val := fun h => (G.ne_of_adj hadj) (by rw [h])
      rcases Nat.lt_or_ge (a.val + 1) b.val with hlt | hge
      · exact absurd hadj (hPchord a.val b.val hlt (by omega))
      · left; omega
    · -- `a` on `P`, `b` on `Q`-arc
      rw [if_pos hAa, if_neg hAb] at hadj
      by_cases ha0 : a.val = 0
      · -- `a = x = Q.getVert 0`
        rcases Nat.lt_or_ge (Q.length - (b.val - P.length)) 2 with hlt | hge
        · -- wrap edge `0 ↔ n-1`
          right; right; left
          exact ⟨ha0, by omega⟩
        · rw [ha0, P.getVert_zero] at hadj
          have h := hQchord 0 (Q.length - (b.val - P.length)) (by omega) (by omega)
          rw [Q.getVert_zero] at h
          exact absurd hadj h
      · -- `a` interior on `P`
        by_cases hjlen : Q.length - (b.val - P.length) = Q.length
        · -- `b`-arc vertex is `y = P.getVert |P|`
          have hyy : Q.getVert Q.length = P.getVert P.length := by
            rw [Q.getVert_length, P.getVert_length]
          rw [hjlen, hyy] at hadj
          rcases Nat.lt_or_ge (a.val + 1) P.length with hlt | hge
          · exact absurd hadj (hPchord a.val P.length hlt le_rfl)
          · left; omega
        · -- both interiors: no cross-edge
          exact absurd hadj
            (hcross a.val (Q.length - (b.val - P.length)) (by omega) hAa (by omega) (by omega))
    · -- impossible: `P.length ≤ a ≤ b < P.length`
      omega
    · -- both indices on the `Q`-arc
      rw [if_neg hAa, if_neg hAb] at hadj
      have hne : Q.length - (a.val - P.length) ≠ Q.length - (b.val - P.length) :=
        fun h => (G.ne_of_adj hadj) (by rw [h])
      rcases Nat.lt_or_ge (Q.length - (b.val - P.length) + 1)
          (Q.length - (a.val - P.length)) with hlt | hge
      · exact absurd hadj.symm
          (hQchord (Q.length - (b.val - P.length)) (Q.length - (a.val - P.length)) hlt (by omega))
      · left; omega
  intro a b hadj
  rcases le_total a.val b.val with h | h
  · exact key a b h hadj
  · exact (key b a h hadj.symm).symm

end SimpleGraph
