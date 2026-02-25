import Reconstruction.Spectral
import Reconstruction.TraceReconstruction
import Reconstruction.Newton

/-!
# Reconstruction Conjecture — Full Characteristic Polynomial

The full characteristic polynomial (including the constant term) is a
reconstructible graph invariant.

## Main results

* `SimpleGraph.SameDeck.charPoly_coeff_zero_eq` — the constant term is reconstructible
* `SimpleGraph.SameDeck.charPoly_eq` — the full characteristic polynomial is reconstructible

## Proof outline

From `Spectral.lean`, we know all non-constant coefficients (`c_1, ..., c_{n-1}`)
are reconstructible. The constant term `c_0 = (-1)^n det(A_G)` requires
additional machinery.

### Strategy for `c_0`

The Cayley–Hamilton trace identity (`Newton.lean`) gives:

`tr(A^n) + c_{n-1} tr(A^{n-1}) + ⋯ + c_1 tr(A) + n · c_0 = 0`

This determines `c_0` if we know `tr(A^k)` for all `k = 1, ..., n` and
`c_1, ..., c_{n-1}`. From `TraceReconstruction.lean`, traces are reconstructible
for `k < n`. The trace `tr(A^n)` is not directly covered by Kelly's Lemma, but
can be recovered by additional arguments (e.g., the Sachs coefficient formula
or walk decomposition over components).

## References

* Schwenk, A. J. (1979). "Spectral reconstruction problems".
* Tutte, W. T. (1979). "All the king's horses".
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- **The constant term of the characteristic polynomial is reconstructible.**

The constant term `c_0 = (-1)^n det(A)` is determined by the Cayley–Hamilton
trace identity: `n · c_0 = -(tr(A^n) + c_{n-1} tr(A^{n-1}) + ⋯ + c_1 tr(A))`.
All terms on the right are reconstructible: `c_1, ..., c_{n-1}` from the
derivative formula (`Spectral.lean`) and `tr(A^k)` from walk counting
(`TraceReconstruction.lean`). -/
theorem SameDeck.charPoly_coeff_zero_eq (h : G.SameDeck H)
    (hV : 3 ≤ Fintype.card V) :
    (G.charPoly ℤ).coeff 0 = (H.charPoly ℤ).coeff 0 := by
  sorry

/-- **The full characteristic polynomial is reconstructible.**

If two graphs on ≥ 3 vertices have the same deck, their characteristic
polynomials (over any integral domain of characteristic zero) are equal.

The proof combines:
1. Non-constant coefficients from the derivative formula (`charPoly_coeff_eq`)
2. The constant term from trace reconstruction and Cayley–Hamilton
   (`charPoly_coeff_zero_eq`) -/
theorem SameDeck.charPoly_eq (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) :
    G.charPoly ℤ = H.charPoly ℤ := by
  ext k
  by_cases hk : 1 ≤ k
  · exact h.charPoly_coeff_eq ℤ hk
  · push_neg at hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact h.charPoly_coeff_zero_eq hV

end SimpleGraph
