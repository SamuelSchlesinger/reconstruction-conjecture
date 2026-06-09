import Reconstruction.CliqueSeparator
import Mathlib.Combinatorics.SimpleGraph.Circulant
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Chordal Graphs

This module begins the **chordal-graph structure layer** for rung 3 of the
separator-decomposition programme. Chordal graphs are entirely absent from
Mathlib (confirmed by source audit), so the definition and its basic closure
properties are built from scratch here.

A graph is **chordal** if it has no induced cycle of length `≥ 4`. The key
formalization observation: a `SimpleGraph.Embedding` (`↪g`) is a `RelEmbedding`,
so it not only preserves but *reflects* adjacency — therefore `cycleGraph n ↪g G`
is exactly an *induced* `n`-cycle in `G`, and "no induced `C_n` for `n ≥ 4`" is
the clean definition.

## Main definitions

* `SimpleGraph.IsChordal G` — no induced cycle of length `≥ 4`.

## Main results

* `SimpleGraph.IsChordal.map` — chordality is an isomorphism invariant.
* `SimpleGraph.IsChordal.induce` — chordality is hereditary (induced subgraphs
  of chordal graphs are chordal).

## Staged targets (stated as `Prop`, not proved)

* `SimpleGraph.DiracSimplicial` — Dirac's theorem: every finite chordal graph on
  a nonempty vertex set has a simplicial vertex. The inductive engine of perfect
  elimination orderings.
* `SimpleGraph.DiracCliqueSeparator` — Dirac's theorem: a non-complete chordal
  graph has a clique separator. This is what makes the clean-clique-separation
  hypothesis of `SeparatorAssembler.nonempty_iso_of_separator_pieces` always
  available for chordal graphs — the structural input for rung 3.

Both are classical (Dirac 1961) but genuinely hard to formalize (they need
cycle/chord analysis and a perfect-elimination induction), and are the real
Mathlib-gap content; they are recorded here as the precise next targets.

## References

* Dirac, G. A. (1961). "On rigid circuit graphs." *Abh. Math. Sem. Univ.
  Hamburg* 25, 71–76.
* Fulkerson, D. R., Gross, O. A. (1965). "Incidence matrices and interval
  graphs." (Perfect elimination orderings.)
-/

namespace SimpleGraph

variable {V : Type*} {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- A graph is **chordal** if it contains no induced cycle of length `≥ 4`.
An induced `n`-cycle is exactly an embedding `cycleGraph n ↪g G` (a graph
embedding is a `RelEmbedding`, hence reflects non-adjacency too). -/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ n : ℕ, 4 ≤ n → IsEmpty ((cycleGraph n) ↪g G)

/-- **Chordality is an isomorphism invariant.** An induced cycle in `H` would,
composed with `e⁻¹`, give an induced cycle in `G`. -/
theorem IsChordal.map (e : G ≃g H) (h : G.IsChordal) : H.IsChordal := by
  intro n hn
  refine ⟨fun f => (h n hn).false ?_⟩
  exact (e.symm.toEmbedding).comp f

/-- **Chordality is hereditary.** An induced cycle in `G.induce S` includes into
`G` as an induced cycle, so if `G` has none then neither does `G.induce S`. -/
theorem IsChordal.induce (S : Set V) (h : G.IsChordal) :
    (G.induce S).IsChordal := by
  intro n hn
  refine ⟨fun f => (h n hn).false ?_⟩
  exact (Embedding.induce S).comp f

/-- A graph on at most three vertices is chordal: an induced `n`-cycle for
`n ≥ 4` would embed `Fin n` into the vertex type, forcing `n ≤ |V| ≤ 3`. (A
sanity check that the definition behaves on small graphs.) -/
theorem isChordal_of_card_le_three [Fintype V] (h : Fintype.card V ≤ 3) :
    G.IsChordal := by
  intro n hn
  refine ⟨fun f => ?_⟩
  have hle : Fintype.card (Fin n) ≤ Fintype.card V :=
    Fintype.card_le_of_embedding f.toEmbedding
  rw [Fintype.card_fin] at hle
  omega

/-- The empty graph is chordal: it has no edges, so no cycle — in particular no
induced `≥ 4`-cycle — can embed (a `cycleGraph` edge would reflect to a
`⊥`-edge). A validation that the definition handles the edgeless case. -/
theorem isChordal_bot : (⊥ : SimpleGraph V).IsChordal := by
  intro m hm
  refine ⟨fun f => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hadj : (cycleGraph (k + 2)).Adj (0 : Fin (k + 2)) (1 : Fin (k + 2)) :=
    cycleGraph_adj.mpr (Or.inr (by simp))
  exact (f.map_rel_iff.mpr hadj).elim

/-- Deleting any vertex preserves chordality (`deleteVert` is `induce`). This is
the recursion step of a perfect elimination ordering: delete a simplicial vertex
and recurse on the still-chordal remainder. -/
theorem IsChordal.deleteVert (v : V) (h : G.IsChordal) :
    (G.deleteVert v).IsChordal :=
  h.induce _

/-! ### Simplicial vertices: the base cases

`IsSimplicial` lives in `Reconstruction.CliqueSeparator`. These are the cases
where a simplicial vertex is immediate — the base of the perfect-elimination
induction, and the complete-graph case of Dirac's theorem. -/

/-- A vertex whose neighbourhood has at most one element is **simplicial** (a
`≤ 1`-element set is vacuously a clique). In particular isolated vertices and
leaves are simplicial. -/
theorem isSimplicial_of_subsingleton_neighborSet {v : V}
    (h : (G.neighborSet v).Subsingleton) : G.IsSimplicial v :=
  h.pairwise G.Adj

/-- Every set of vertices is a clique in the complete graph. -/
theorem top_isClique (s : Set V) : (⊤ : SimpleGraph V).IsClique s := by
  intro a _ b _ hab
  exact (top_adj a b).mpr hab

/-- Every vertex of the complete graph is simplicial; so `DiracSimplicial` holds
for complete graphs, and the genuine content is the non-complete case. -/
theorem isSimplicial_top (v : V) : (⊤ : SimpleGraph V).IsSimplicial v :=
  top_isClique _

/-- **TARGET — Dirac 1961.** Every finite chordal graph on a nonempty vertex set
has a simplicial vertex. The inductive base of perfect elimination orderings;
hard to formalize (needs cycle/chord analysis). -/
def DiracSimplicial (V : Type*) [Fintype V] : Prop :=
  ∀ (G : SimpleGraph V), G.IsChordal → Nonempty V → ∃ v : V, G.IsSimplicial v

/-- **TARGET — Dirac 1961.** A non-complete chordal graph has a separator that
induces a clique. This guarantees the clean-clique-separation hypothesis of the
reassembly engine is always available for chordal graphs, and is the structural
input for rung 3. -/
def DiracCliqueSeparator (V : Type*) : Prop :=
  ∀ (G : SimpleGraph V), G.IsChordal → G ≠ ⊤ → G.Connected →
    ∃ S : Set V, G.IsCliqueSeparator S

/-- **The crux behind Dirac.** In a chordal graph an inclusion-minimal
separator induces a clique. (Two non-adjacent vertices of a minimal separator
would, via shortest paths through two different `G − S` components, yield an
induced `≥ 4`-cycle, contradicting chordality.) From this, both `DiracSimplicial`
and `DiracCliqueSeparator` follow by induction on the components of `G − S`.

**Proved** as `SimpleGraph.minimalSeparatorClique` in `MinimalSeparatorClique.lean`,
via the induced-cycle-extraction machinery (`Geodesic`, `InducedCycle`,
`CycleFromPaths`, `MinimalSeparator`). -/
def MinimalSeparatorClique (V : Type*) : Prop :=
  ∀ (G : SimpleGraph V) (S : Set V), G.IsChordal → G.IsSeparator S →
    (∀ T : Set V, T ⊂ S → ¬ G.IsSeparator T) → G.IsClique S

end SimpleGraph
