import Reconstruction.Chordal
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Geodesics are chordless

The linchpin of the induced-cycle-extraction machinery: a shortest path (a walk
whose length realizes the graph distance) has **no chord** — no edge joins two of
its vertices that are more than one step apart along the walk. Equivalently a
geodesic is an induced path. This is what forces the cycle glued from two
shortest paths (through two components of `G − S`) to be chordless, hence an
induced cycle.

## Main results

* `SimpleGraph.Walk.geodesic_not_adj_of_lt` — on a geodesic `p`, if `i + 1 < j`
  (and `j ≤ p.length`) then `p.getVert i` and `p.getVert j` are non-adjacent.
* `SimpleGraph.Walk.geodesic_not_adj_of_lt'` — the symmetric statement.
-/

namespace SimpleGraph
namespace Walk

variable {V : Type*} {G : SimpleGraph V}

/-- **A geodesic is chordless.** If `p` is a shortest `u`–`v` walk
(`p.length = G.dist u v`) and `i + 1 < j ≤ p.length`, then `p.getVert i` and
`p.getVert j` are not adjacent: a chord would shortcut `p` (take to `i`, the
chord edge, drop from `j`) into a strictly shorter `u`–`v` walk, impossible. -/
theorem geodesic_not_adj_of_lt {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i j : ℕ} (hij : i + 1 < j) (hj : j ≤ p.length) :
    ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  have h1 : hadj.toWalk.length = 1 := rfl
  have h2 : i ⊓ p.length = i := Nat.min_eq_left (by omega)
  have hqlen : (((p.take i).append hadj.toWalk).append (p.drop j)).length
      = i + 1 + (p.length - j) := by
    simp only [length_append, take_length, drop_length, h1, h2]
  have hd := dist_le (((p.take i).append hadj.toWalk).append (p.drop j))
  omega

/-- The symmetric form of `geodesic_not_adj_of_lt`. -/
theorem geodesic_not_adj_of_lt' {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) {i j : ℕ} (hij : i + 1 < j) (hj : j ≤ p.length) :
    ¬ G.Adj (p.getVert j) (p.getVert i) :=
  fun h => geodesic_not_adj_of_lt p hp hij hj h.symm

end Walk
end SimpleGraph
