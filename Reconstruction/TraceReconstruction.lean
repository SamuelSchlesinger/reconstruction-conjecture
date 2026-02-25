import Reconstruction.KellyLemma
import Reconstruction.Spectral
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Reconstruction Conjecture — Trace Reconstructibility

The trace of powers of the adjacency matrix is a reconstructible invariant
for powers less than the number of vertices.

## Main results

* `SimpleGraph.SameDeck.trace_adjMatrix_pow_eq` — `tr(A_G^k) = tr(A_H^k)` for `k < |V|`

## Proof outline

The trace `tr(A^k) = ∑_v (A^k)_{vv}` counts the number of closed walks of
length `k` in `G`. A closed walk of length `k` visits at most `k` distinct
vertices. For `k < n`, express `tr(A^k)` as a sum over subgraph counts of
graphs on at most `k` vertices. By Kelly's Lemma, all these counts are
reconstructible since `k < n`.

More precisely, for each graph `F` on at most `k` vertices, the number of
closed walks of length `k` that visit exactly `V(F)` as their vertex set can
be expressed in terms of subgraph counts of `F`. Since `|V(F)| ≤ k < n`,
Kelly's Lemma applies.

## References

* Schwenk, A. J. (1979). "Spectral reconstruction problems".
* Tutte, W. T. (1979). "All the king's horses".
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Matrix

/-- The trace of the `k`-th power of the adjacency matrix counts closed walks
of length `k`. This is the diagonal sum `∑_v (A^k)_{vv}`. -/
noncomputable def closedWalkCount (k : ℕ) : ℤ :=
  trace ((G.adjMatrix ℤ) ^ k)

variable {G} {H : SimpleGraph V} [DecidableRel H.Adj]

/-- **Traces of adjacency matrix powers are reconstructible** for powers `< |V|`.

`tr(A_G^k) = tr(A_H^k)` for all `k < |V|`. The key insight is that `tr(A^k)`
counts closed walks of length `k`, which visit at most `k` vertices. These
walks can be decomposed according to which induced subgraph they inhabit,
and Kelly's Lemma reconstructs all subgraph counts for graphs on `< |V|`
vertices. -/
theorem SameDeck.trace_adjMatrix_pow_eq (h : G.SameDeck H)
    (hV : 3 ≤ Fintype.card V) {k : ℕ} (hk : k < Fintype.card V) :
    trace ((G.adjMatrix ℤ) ^ k) = trace ((H.adjMatrix ℤ) ^ k) := by
  sorry

end SimpleGraph
