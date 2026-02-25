import Reconstruction.Spectral
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Newton's Identities for Matrices

Newton's identities (Faddeev–LeVerrier recurrence) relate the traces of powers
of a matrix to the coefficients of its characteristic polynomial.

## Main results

* `Matrix.newton_trace_charpoly` — the Newton identity at step `k`:
  `tr(A^k) + ∑_{j=1}^{k-1} c_{n-j} · tr(A^{k-j}) + k · c_{n-k} = 0`

* `Matrix.cayley_hamilton_trace` — the Cayley–Hamilton trace identity:
  `∑_{i=0}^{n} c_i · tr(A^i) = 0`, which is Newton at `k = n`

## Proof outline

### From Cayley–Hamilton

The Cayley–Hamilton theorem (`Matrix.aeval_self_charpoly`) gives `p(A) = 0` where
`p(x) = x^n + c_{n-1} x^{n-1} + ⋯ + c_1 x + c_0` is the characteristic polynomial.

Taking the trace of `p(A) = 0`:
`∑_{i=0}^{n} c_i · tr(A^i) = 0`

Since `c_n = 1` (monic) and `tr(A^0) = tr(I) = n`:
`tr(A^n) + c_{n-1} tr(A^{n-1}) + ⋯ + c_1 tr(A) + c_0 · n = 0`

This determines `c_0` from the traces and higher coefficients.

For `k < n`, Newton's identities follow from differentiating `det(xI - A)`
and applying the product rule to the Leibniz expansion.

## References

* Faddeev, D. K. & Faddeeva, V. N. (1963). *Computational Methods of Linear Algebra*.
* Newton, I. (1707). *Arithmetica Universalis*.
-/

namespace Matrix

open Polynomial Finset

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- **Newton's identity at step k.** For a matrix `A` over a commutative ring
and `1 ≤ k ≤ |n|`:

`tr(A^k) + ∑_{j=1}^{k-1} c_{|n|-j} · tr(A^{k-j}) + k · c_{|n|-k} = 0`

where `c_i` denotes `A.charpoly.coeff i`.

The full set of Newton identities for `k = 1, ..., |n|` determines all
coefficients of the characteristic polynomial from the traces of powers,
and vice versa. -/
theorem newton_trace_charpoly (A : Matrix n n R) {k : ℕ}
    (hk : 1 ≤ k) (hk' : k ≤ Fintype.card n) :
    trace (A ^ k) +
    ∑ j ∈ range (k - 1),
      A.charpoly.coeff (Fintype.card n - (j + 1)) *
      trace (A ^ (k - (j + 1))) +
    (k : R) * A.charpoly.coeff (Fintype.card n - k) = 0 := by
  sorry

/-- Helper: `trace(algebraMap r * M) = r * trace M` for scalar matrices. -/
private theorem trace_algebraMap_mul (r : R) (M : Matrix n n R) :
    trace (algebraMap R (Matrix n n R) r * M) = r * trace M := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact trace_smul r M

/-- **Cayley–Hamilton trace identity.** Taking the trace of `p(A) = 0`
(Cayley–Hamilton) yields a linear relation among `c_i · tr(A^i)`:

`∑_{i=0}^{n} charpoly.coeff(i) · tr(A^i) = 0`

Since `charpoly` is monic of degree `n`, the coefficient of `x^n` is `1`,
so this is equivalent to:

`tr(A^n) + ∑_{i=0}^{n-1} c_i · tr(A^i) = 0`

At `i = 0`: `tr(A^0) = tr(I) = n`, so the `c_0` term contributes `n · c_0`.
This determines `c_0` from `tr(A), ..., tr(A^n)` and `c_1, ..., c_{n-1}`. -/
theorem cayley_hamilton_trace (A : Matrix n n R) :
    ∑ i ∈ range (Fintype.card n + 1),
      A.charpoly.coeff i * trace (A ^ i) = 0 := by
  by_cases hR : Nontrivial R
  · haveI := hR
    -- trace(p(A)) = 0 from Cayley-Hamilton
    have htr : trace (aeval A A.charpoly) = 0 := by
      rw [aeval_self_charpoly]; simp
    -- Expand aeval as eval₂, then as sum over range
    rw [aeval_def,
        eval₂_eq_sum_range' (algebraMap R (Matrix n n R))
          (show A.charpoly.natDegree < Fintype.card n + 1 by
            rw [charpoly_natDegree_eq_dim]; omega) A] at htr
    -- Distribute trace over the sum
    rw [trace_sum] at htr
    -- Simplify each term: trace(algebraMap r * A^i) = r * trace(A^i)
    simp only [trace_algebraMap_mul] at htr
    exact htr
  · -- Trivial ring: all elements are 0
    rw [not_nontrivial_iff_subsingleton] at hR
    haveI := hR
    have h0 : ∀ r : R, r = 0 := fun r => Subsingleton.elim r 0
    simp [h0]

end Matrix
