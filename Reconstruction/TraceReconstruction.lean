import Reconstruction.KellyLemma
import Reconstruction.Spectral
import Reconstruction.Newton
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Reconstruction Conjecture — Trace Reconstructibility

The trace of powers of the adjacency matrix is a reconstructible invariant
for powers less than the number of vertices.

## Main results

* `SimpleGraph.SameDeck.trace_adjMatrix_pow_eq` — `tr(A_G^k) = tr(A_H^k)` for `k < |V|`

## Proof outline

By strong induction on `k`, using Newton's identity (`Newton.lean`):

  `tr(A^k) + ∑_{j=1}^{k-1} c_{N-j} · tr(A^{k-j}) + k · c_{N-k} = 0`

For `k = 0`: both traces equal `|V|` (trace of the identity matrix).

For `1 ≤ k < |V|`: the characteristic polynomial coefficients `c_1, ..., c_{N-1}`
are reconstructible (`charPoly_coeff_eq`), and the lower-order traces are
reconstructible by the induction hypothesis. Newton's identity then determines
`tr(A^k)` uniquely.

## References

* Schwenk, A. J. (1979). "Spectral reconstruction problems".
* Newton, I. (1707). *Arithmetica Universalis*.
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Matrix Finset

/-- The trace of the `k`-th power of the adjacency matrix counts closed walks
of length `k`. This is the diagonal sum `∑_v (A^k)_{vv}`. -/
noncomputable def closedWalkCount (k : ℕ) : ℤ :=
  trace ((G.adjMatrix ℤ) ^ k)

variable {G} {H : SimpleGraph V} [DecidableRel H.Adj]

/-- **Traces of adjacency matrix powers are reconstructible** for powers `< |V|`.

`tr(A_G^k) = tr(A_H^k)` for all `k < |V|`. The proof uses Newton's identity
to express `tr(A^k)` in terms of characteristic polynomial coefficients
(reconstructible by `charPoly_coeff_eq`) and lower-order traces (reconstructible
by the induction hypothesis). -/
theorem SameDeck.trace_adjMatrix_pow_eq (h : G.SameDeck H)
    (_hV : 3 ≤ Fintype.card V) {k : ℕ} (hk : k < Fintype.card V) :
    trace ((G.adjMatrix ℤ) ^ k) = trace ((H.adjMatrix ℤ) ^ k) := by
  -- Strong induction on k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  -- Base case: k = 0
  by_cases hk0 : k = 0
  · subst hk0; simp [pow_zero]
  -- Inductive case: 1 ≤ k < |V|
  · have hk1 : 1 ≤ k := by omega
    -- Newton's identity for G and H
    have newtonG := newton_trace_charpoly (G.adjMatrix ℤ) hk1 (le_of_lt hk)
    have newtonH := newton_trace_charpoly (H.adjMatrix ℤ) hk1 (le_of_lt hk)
    -- Characteristic polynomial coefficients agree
    -- (charPoly G ℤ = (G.adjMatrix ℤ).charpoly by definition)
    have hcoeff : ∀ i, 1 ≤ i →
        (G.adjMatrix ℤ).charpoly.coeff i = (H.adjMatrix ℤ).charpoly.coeff i :=
      fun i hi => h.charPoly_coeff_eq ℤ hi
    -- The middle sums in Newton's identity agree
    have hsum : ∑ j ∈ range (k - 1),
        (G.adjMatrix ℤ).charpoly.coeff (Fintype.card V - (j + 1)) *
          trace ((G.adjMatrix ℤ) ^ (k - (j + 1))) =
      ∑ j ∈ range (k - 1),
        (H.adjMatrix ℤ).charpoly.coeff (Fintype.card V - (j + 1)) *
          trace ((H.adjMatrix ℤ) ^ (k - (j + 1))) := by
      apply sum_congr rfl; intro j hj
      simp only [mem_range] at hj
      rw [hcoeff (Fintype.card V - (j + 1)) (by omega),
          ih (k - (j + 1)) (by omega) (by omega)]
    -- The constant terms agree
    have hc : (↑k : ℤ) * (G.adjMatrix ℤ).charpoly.coeff (Fintype.card V - k) =
              (↑k : ℤ) * (H.adjMatrix ℤ).charpoly.coeff (Fintype.card V - k) := by
      congr 1; exact hcoeff (Fintype.card V - k) (by omega)
    -- Conclude from the two Newton identities
    linarith

end SimpleGraph
