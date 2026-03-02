import Reconstruction.Spectral
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Newton's Identities for Matrices

Newton's identities (Faddeev–LeVerrier recurrence) relate the traces of powers
of a matrix to the coefficients of its characteristic polynomial.

## Main results

* `Matrix.newton_trace_charpoly` — the Newton identity at step `k`:
  `tr(A^k) + ∑_{j=1}^{k-1} c_{|n|-j} · tr(A^{k-j}) + k · c_{|n|-k} = 0`

* `Matrix.cayley_hamilton_trace` — the Cayley–Hamilton trace identity:
  `∑_{i=0}^{n} c_i · tr(A^i) = 0`, which is Newton at `k = n`

## Proof strategy

The proof of Newton's identity combines two ingredients:

1. **Trace of adjugate = derivative.** The trace of `adjugate(charmatrix A)` equals
   `derivative(charpoly A)`. This follows from the fact that diagonal entries of the
   adjugate are principal subdeterminants, which sum to the derivative by the
   Jacobi/Leibniz formula (`derivative_det_charmatrix` from `Spectral.lean`).

2. **Adjugate coefficient recurrence.** From `mul_adjugate`, the polynomial-coefficient
   matrices of `adjugate(charmatrix A)` satisfy a Faddeev–LeVerrier recurrence:
   `B_{m-1} = A * B_m + c_m • I`, with `B_{N-1} = I`.
   By induction: `B_{N-1-k} = A^k + c_{N-1} A^{k-1} + ⋯ + c_{N-k} I`.

Combining: the coefficient of `x^{N-1-k}` in `derivative(charpoly)` is `(N-k) c_{N-k}`,
and the trace of `B_{N-1-k}` is `s_k + ∑ c_{N-j} s_{k-j} + N c_{N-k}`.
Equating gives Newton's identity.

## References

* Faddeev, D. K. & Faddeeva, V. N. (1963). *Computational Methods of Linear Algebra*.
* Newton, I. (1707). *Arithmetica Universalis*.
-/

namespace Matrix

open Polynomial Finset

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-! ### Adjugate diagonal = principal subdeterminant -/

/-- For `σ : Perm n` with `σ v = v`, restrict to a permutation of `{w // w ≠ v}`. -/
private def restrictPerm (σ : Equiv.Perm n) (v : n) (hσ : σ v = v) :
    Equiv.Perm {w : n // w ≠ v} :=
  σ.subtypePerm fun x => by
    constructor
    · intro hσx hc; exact absurd (hc ▸ hσ) hσx
    · intro hx hσx; exact hx (σ.injective (hσx.trans hσ.symm))

/-- The determinant of a matrix with row `v` replaced by the standard basis vector `e_v`
equals the determinant of the submatrix obtained by deleting row and column `v`.

This is the key fact connecting `adjugate M v v` (via `adjugate_apply`) to the
principal subdeterminant. -/
private theorem det_updateRow_Pi_single (M : Matrix n n R) (v : n) :
    (M.updateRow v (Pi.single v 1)).det =
    (M.submatrix (Subtype.val : {w : n // w ≠ v} → n) Subtype.val).det := by
  simp only [det_apply']
  -- For each σ, the product is nonzero only when σ v = v
  have term_eq : ∀ σ : Equiv.Perm n,
      ∏ i, (M.updateRow v (Pi.single v 1)) (σ i) i =
      if σ v = v then ∏ i ∈ univ.erase v, M (σ i) i else 0 := by
    intro σ
    split_ifs with h
    · -- σ v = v: factor out the v-term (which is 1)
      rw [← mul_prod_erase _ _ (mem_univ v)]
      have hfact_v : (M.updateRow v (Pi.single v 1)) (σ v) v = 1 := by
        rw [h, updateRow_self, Pi.single_eq_same]
      rw [hfact_v, one_mul]
      exact prod_congr rfl fun i hi => by
        have hne : i ≠ v := (mem_erase.mp hi).1
        have hσne : σ i ≠ v := fun hc => hne (σ.injective (hc.trans h.symm))
        rw [updateRow_apply, if_neg hσne]
    · -- σ v ≠ v: the factor at i = σ⁻¹ v is 0, killing the product
      have hσinv : σ⁻¹ v ≠ v := by
        intro hc; apply h
        have key : σ (σ⁻¹ v) = v := by simp
        rwa [hc] at key
      suffices hprod : ∏ i, (M.updateRow v (Pi.single v 1)) (σ i) i = 0 by
        exact hprod
      apply prod_eq_zero (mem_univ (σ⁻¹ v))
      simp only [show σ (σ⁻¹ v) = v from by simp, updateRow_self, Pi.single_apply,
        if_neg hσinv]
  simp_rw [term_eq, mul_ite, mul_zero]
  rw [sum_ite, sum_const_zero, add_zero]
  -- Biject: σ fixing v ↔ Perm {w // w ≠ v}
  symm
  apply sum_nbij' (fun τ => Equiv.Perm.ofSubtype τ)
    (fun σ => if hσ : σ v = v then restrictPerm σ v hσ else 1)
  · intro τ _; simp only [mem_filter, mem_univ, true_and]
    exact Equiv.Perm.ofSubtype_apply_of_not_mem τ (not_not.mpr rfl)
  · intro _ _; exact mem_univ _
  · intro τ _
    have hfix := Equiv.Perm.ofSubtype_apply_of_not_mem τ (not_not.mpr rfl)
    simp only [dif_pos hfix, restrictPerm]
    exact Equiv.Perm.subtypePerm_ofSubtype τ
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    simp only [dif_pos hσ, restrictPerm]
    exact Equiv.Perm.ofSubtype_subtypePerm _ fun x hx => by
      intro hc; subst hc; exact hx hσ
  · intro τ _
    congr 1
    · simp [Equiv.Perm.sign_ofSubtype]
    · symm
      rw [prod_subtype (p := (· ≠ v)) (univ.erase v)
        (fun x => by simp [mem_erase])]
      exact prod_congr rfl fun ⟨j, hj⟩ _ => by
        simp only [submatrix_apply]
        rw [Equiv.Perm.ofSubtype_apply_of_mem τ hj]

/-- Diagonal entry of the adjugate equals the principal subdeterminant. -/
private theorem adjugate_diag (M : Matrix n n R) (v : n) :
    M.adjugate v v =
    (M.submatrix (Subtype.val : {w : n // w ≠ v} → n) Subtype.val).det := by
  rw [adjugate_apply, det_updateRow_Pi_single]

/-! ### Trace of adjugate of charmatrix = characteristic polynomial derivative -/

/-- The polynomial `∑_v adjugate(charmatrix A)_{v,v}` equals `derivative(charpoly A)`.
This follows from `adjugate_diag` (each diagonal entry is a principal subdeterminant)
and `derivative_det_charmatrix` (the derivative of det equals the sum of such
subdeterminants). -/
private theorem trace_adjugate_charmatrix (A : Matrix n n R) :
    ∑ v : n, A.charmatrix.adjugate v v =
    Polynomial.derivative (A.charpoly) := by
  simp_rw [adjugate_diag]
  exact (SimpleGraph.derivative_det_charmatrix A).symm

/-! ### Coefficient extraction from `mul_adjugate` -/

/-- The matrix of degree-`k` polynomial coefficients from `adjugate(charmatrix A)`. -/
private noncomputable def adjCoeff (A : Matrix n n R) (k : ℕ) : Matrix n n R :=
  fun i j => (A.charmatrix.adjugate i j).coeff k

/-- The degree bound: `adjCoeff A k = 0` for `k ≥ Fintype.card n`.
Each entry of `adjugate(charmatrix A)` has degree ≤ `n - 1`, because the
adjugate entry `det(charmatrix.updateRow j (e_i))` is a determinant of a matrix
where one row has degree 0 (from `Pi.single`) and the rest have degree ≤ 1. -/
private theorem adjCoeff_eq_zero (A : Matrix n n R) {k : ℕ}
    (hk : Fintype.card n ≤ k) : adjCoeff A k = 0 := by
  ext i j
  simp only [adjCoeff, Matrix.zero_apply]
  rw [adjugate_apply, det_apply', Polynomial.finset_sum_coeff]
  apply sum_eq_zero; intro σ _
  -- Show the product (without sign) has coeff k = 0, then the signed term does too
  suffices hprod : (∏ l : n,
      (A.charmatrix.updateRow j (Pi.single i 1)) (σ l) l).coeff k = 0 by
    rw [Polynomial.coeff_intCast_mul, hprod, mul_zero]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  haveI : Nonempty n := ⟨i⟩
  -- Degree bound: the product has natDegree ≤ N-1 < k
  calc (∏ l, (A.charmatrix.updateRow j (Pi.single i 1)) (σ l) l).natDegree
      ≤ ∑ l, ((A.charmatrix.updateRow j (Pi.single i 1)) (σ l) l).natDegree :=
        natDegree_prod_le _ _
    _ ≤ Fintype.card n - 1 := by
        -- Split off the term at l = σ⁻¹ j (where the updateRow applies)
        rw [← add_sum_erase _ _ (mem_univ (σ⁻¹ j))]
        -- At l = σ⁻¹ j: σ l = j, so updateRow replaces the entry with Pi.single
        have h_upd : ((A.charmatrix.updateRow j (Pi.single i 1))
            (σ (σ⁻¹ j)) (σ⁻¹ j)).natDegree = 0 := by
          simp only [show σ (σ⁻¹ j) = j from by simp, updateRow_self, Pi.single_apply]
          split_ifs <;> simp
        rw [h_upd, zero_add]
        -- Remaining terms: each has degree ≤ 1
        calc ∑ l ∈ univ.erase (σ⁻¹ j),
              ((A.charmatrix.updateRow j (Pi.single i 1)) (σ l) l).natDegree
            ≤ (univ.erase (σ⁻¹ j)).card • 1 := by
              apply sum_le_card_nsmul; intro l hl
              have hne_inv : l ≠ σ⁻¹ j := (mem_erase.mp hl).1
              -- σ l ≠ j since l ≠ σ⁻¹ j
              have hσne : σ l ≠ j := by
                intro hc; exact hne_inv (by simp [← hc])
              rw [updateRow_apply, if_neg hσne]
              -- Now the entry is a charmatrix entry, degree ≤ 1
              rcases eq_or_ne (σ l) l with h | h
              · rw [h, charmatrix_apply_eq]
                exact (natDegree_sub_le _ _).trans (max_le
                  (Polynomial.natDegree_le_of_degree_le Polynomial.degree_X_le)
                  (le_trans (le_of_eq (natDegree_C _)) (by omega)))
              · rw [charmatrix_apply_ne A (σ l) l h, natDegree_neg, natDegree_C]; omega
          _ = Fintype.card n - 1 := by
              rw [smul_eq_mul, mul_one, card_erase_of_mem (mem_univ _), card_univ]
    _ < k := by
        have : 0 < Fintype.card n := Fintype.card_pos
        omega

/-- The Faddeev–LeVerrier recurrence for adjugate coefficient matrices.
From `charmatrix A * adjugate(charmatrix A) = charpoly A • I`, extracting the
degree-`m` polynomial coefficient gives:
`adjCoeff (m - 1) = A * adjCoeff m + charpoly.coeff m • I` for `m ≥ 1`. -/
private theorem adjCoeff_recurrence (A : Matrix n n R) {m : ℕ} (hm : 1 ≤ m) :
    adjCoeff A (m - 1) = A * adjCoeff A m + A.charpoly.coeff m • (1 : Matrix n n R) := by
  have hmul := mul_adjugate (charmatrix A)
  ext i l
  simp only [adjCoeff, add_apply, smul_apply, mul_apply, one_apply, smul_eq_mul]
  -- Entry (i,l) of mul_adjugate gives charmatrix * adj = charpoly * I
  have entry_eq : ∑ j : n, charmatrix A i j * adjugate (charmatrix A) j l =
      A.charpoly * (if i = l then 1 else 0) := by
    have h := congr_fun (congr_fun hmul i) l
    simp only [mul_apply, smul_apply, one_apply, smul_eq_mul] at h
    exact h
  -- Take coeff m of both sides
  have coeff_rhs : (A.charpoly * (if i = l then 1 else 0)).coeff m =
      (if i = l then A.charpoly.coeff m else 0) := by
    split_ifs <;> simp
  have coeff_eq : ∑ j : n, (charmatrix A i j * adjugate (charmatrix A) j l).coeff m =
      (if i = l then A.charpoly.coeff m else 0) := by
    rw [← Polynomial.finset_sum_coeff, entry_eq, coeff_rhs]
  -- For each j, decompose the charmatrix entry and expand the product coefficient
  have coeff_split : ∀ j : n,
      (charmatrix A i j * adjugate (charmatrix A) j l).coeff m =
      (if i = j then 1 else 0) * (adjugate (charmatrix A) j l).coeff (m - 1) +
      (-(A i j)) * (adjugate (charmatrix A) j l).coeff m := by
    intro j
    rcases eq_or_ne i j with rfl | h
    · -- diagonal: charmatrix A i i = X - C (A i i)
      rw [charmatrix_apply_eq, sub_mul, Polynomial.coeff_sub]
      have hX : (X * adjugate (charmatrix A) i l).coeff m =
          (adjugate (charmatrix A) i l).coeff (m - 1) := by
        conv_lhs => rw [show m = (m - 1) + 1 from by omega]
        exact Polynomial.coeff_X_mul _ _
      rw [hX, Polynomial.coeff_C_mul, if_pos rfl, one_mul, sub_eq_add_neg, neg_mul]
    · -- off-diagonal: charmatrix A i j = -C (A i j)
      rw [charmatrix_apply_ne A i j h, neg_mul, Polynomial.coeff_neg,
          Polynomial.coeff_C_mul]
      simp only [if_neg h, zero_mul, zero_add, neg_mul]
  -- Substitute and simplify
  simp_rw [coeff_split] at coeff_eq
  simp only [sum_add_distrib] at coeff_eq
  -- ∑_j δ_{ij} * adj(m-1)_{jl} = adj(m-1)_{il}
  have sum_delta : ∑ j : n, (if i = j then (1 : R) else 0) *
      (adjugate (charmatrix A) j l).coeff (m - 1) =
      (adjugate (charmatrix A) i l).coeff (m - 1) := by
    rw [sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), zero_mul])
      (fun h => absurd (mem_univ i) h)]
    simp
  rw [sum_delta] at coeff_eq
  -- ∑_j -(A_{ij}) * adj(m)_{jl} = -(∑_j A_{ij} * adj(m)_{jl})
  have sum_neg : ∑ j : n, -(A i j) * (adjugate (charmatrix A) j l).coeff m =
      -(∑ j : n, A i j * (adjugate (charmatrix A) j l).coeff m) := by
    simp [neg_mul, sum_neg_distrib]
  rw [sum_neg, ← sub_eq_add_neg] at coeff_eq
  -- Rearrange
  have ite_eq : (if i = l then A.charpoly.coeff m else (0 : R)) =
      A.charpoly.coeff m * (if i = l then 1 else 0) := by
    split_ifs <;> simp
  rw [ite_eq] at coeff_eq
  rw [sub_eq_iff_eq_add.mp coeff_eq, add_comm]

/-! ### Adjugate coefficient formula by induction -/

/-- The explicit formula for adjugate coefficient matrices:
`adjCoeff A (N-1-k) = ∑_{i=0}^{k} charpoly.coeff(N-i) • A^{k-i}`

In particular, `adjCoeff A (N-1-k) = A^k + c_{N-1} A^{k-1} + ⋯ + c_{N-k} I`. -/
private theorem adjCoeff_eq_sum (A : Matrix n n R) (k : ℕ)
    (hk : k + 1 ≤ Fintype.card n) :
    adjCoeff A (Fintype.card n - 1 - k) =
    ∑ i ∈ range (k + 1), A.charpoly.coeff (Fintype.card n - i) • A ^ (k - i) := by
  set N := Fintype.card n with hN_def
  induction k with
  | zero =>
    -- adjCoeff A (N-1) = c_N • 1
    -- From recurrence at m = N: adjCoeff(N-1) = A * adjCoeff(N) + c_N • 1
    -- adjCoeff(N) = 0 by degree bound
    have hrec := adjCoeff_recurrence A (m := N) (by omega)
    rw [show N - 1 = N - 1 from rfl, adjCoeff_eq_zero A (le_refl _),
        mul_zero, zero_add] at hrec
    -- Goal: adjCoeff A (N-1-0) = ∑ i ∈ range 1, c_{N-i} • A^{0-i}
    rw [show (0 : ℕ) + 1 = 1 from rfl, sum_range_one]
    simp only [Nat.sub_zero, pow_zero]
    exact hrec
  | succ k ih =>
    have hk_bound : k + 1 ≤ N := by omega
    have ih' := ih hk_bound
    -- Use recurrence at m = N - (k + 1)
    have hm : 1 ≤ N - (k + 1) := by omega
    have hrec := adjCoeff_recurrence A hm
    -- Align indices
    have hm_eq1 : N - (k + 1) - 1 = N - 1 - (k + 1) := by omega
    have hm_eq2 : N - (k + 1) = N - 1 - k := by omega
    rw [hm_eq1, hm_eq2] at hrec
    -- Substitute ih' into hrec
    rw [ih'] at hrec
    -- hrec: adjCoeff A (N-1-(k+1)) =
    --   A * (∑ i ∈ range(k+1), c_{N-i} • A^{k-i}) + c_{N-1-k} • 1
    rw [hrec]
    -- Distribute A over the sum and simplify
    rw [mul_sum]
    -- Rewrite each term: A * (c • A^m) = c • A^{k+1-i}
    have sum_eq : ∑ i ∈ range (k + 1), A * (A.charpoly.coeff (N - i) • A ^ (k - i)) =
        ∑ i ∈ range (k + 1), A.charpoly.coeff (N - i) • A ^ (k + 1 - i) := by
      apply sum_congr rfl; intro i hi
      simp only [mem_range] at hi
      rw [mul_smul_comm, ← pow_succ',
          show k - i + 1 = k + 1 - i from (Nat.succ_sub (by omega)).symm]
    rw [sum_eq]
    -- Now LHS = ∑ i ∈ range(k+1), c_{N-i} • A^{(k+1)-i} + c_{N-1-k} • 1
    -- RHS = ∑ i ∈ range(k+2), c_{N-i} • A^{(k+1)-i}
    conv_rhs => rw [show k + 1 + 1 = (k + 1) + 1 from rfl, sum_range_succ]
    congr 1
    -- c_{N-1-k} • 1 = c_{N-(k+1)} • A^{(k+1)-(k+1)}
    rw [show k + 1 - (k + 1) = 0 from Nat.sub_self _, pow_zero,
        show N - 1 - k = N - (k + 1) from by rw [Nat.sub_sub, add_comm]]

/-! ### Cayley–Hamilton trace identity -/

/-- Helper: `trace(algebraMap r * M) = r * trace M` for scalar matrices. -/
private theorem trace_algebraMap_mul (r : R) (M : Matrix n n R) :
    trace (algebraMap R (Matrix n n R) r * M) = r * trace M := by
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact trace_smul r M

/-- **Cayley–Hamilton trace identity.** Taking the trace of `p(A) = 0`
(Cayley–Hamilton) yields:

`∑_{i=0}^{n} charpoly.coeff(i) · tr(A^i) = 0` -/
theorem cayley_hamilton_trace (A : Matrix n n R) :
    ∑ i ∈ range (Fintype.card n + 1),
      A.charpoly.coeff i * trace (A ^ i) = 0 := by
  by_cases hR : Nontrivial R
  · haveI := hR
    have htr : trace (aeval A A.charpoly) = 0 := by
      rw [aeval_self_charpoly]; simp
    rw [aeval_def,
        eval₂_eq_sum_range' (algebraMap R (Matrix n n R))
          (show A.charpoly.natDegree < Fintype.card n + 1 by
            rw [charpoly_natDegree_eq_dim]; omega) A] at htr
    rw [trace_sum] at htr
    simp only [trace_algebraMap_mul] at htr
    exact htr
  · rw [not_nontrivial_iff_subsingleton] at hR
    haveI := hR
    have h0 : ∀ r : R, r = 0 := fun r => Subsingleton.elim r 0
    simp [h0]

/-! ### Newton's identity -/

/-- **Newton's identity at step k.** For a matrix `A` over a commutative ring
and `1 ≤ k ≤ |n|`:

`tr(A^k) + ∑_{j=1}^{k-1} c_{|n|-j} · tr(A^{k-j}) + k · c_{|n|-k} = 0`

where `c_i` denotes `A.charpoly.coeff i`. -/
theorem newton_trace_charpoly (A : Matrix n n R) {k : ℕ}
    (hk : 1 ≤ k) (hk' : k ≤ Fintype.card n) :
    trace (A ^ k) +
    ∑ j ∈ range (k - 1),
      A.charpoly.coeff (Fintype.card n - (j + 1)) *
      trace (A ^ (k - (j + 1))) +
    (k : R) * A.charpoly.coeff (Fintype.card n - k) = 0 := by
  set N := Fintype.card n with hN_def
  -- Handle k = N separately via Cayley-Hamilton
  by_cases hkN : k = N
  · -- k = N case: Newton at k = N is exactly Cayley-Hamilton trace
    subst hkN
    have hCH := cayley_hamilton_trace A
    -- Extract first term (i = 0): c_0 * s_0 = c_0 * ↑N
    rw [sum_range_succ'] at hCH
    simp only [pow_zero, trace_one] at hCH
    -- Extract last term (i = N): c_N * s_N
    have hsplit := sum_range_succ
      (fun i => A.charpoly.coeff (i + 1) * trace (A ^ (i + 1))) (N - 1)
    rw [show (N - 1) + 1 = N from by omega] at hsplit
    rw [hsplit] at hCH
    -- Handle trivial ring case
    by_cases hR : Nontrivial R
    swap
    · rw [not_nontrivial_iff_subsingleton] at hR; haveI := hR
      have h0 : ∀ r : R, r = 0 := fun r => Subsingleton.elim r 0
      simp [h0]
    haveI := hR
    -- c_N = 1 (charpoly is monic)
    have hc_top : A.charpoly.coeff N = 1 := by
      have := (charpoly_monic A).coeff_natDegree
      rwa [charpoly_natDegree_eq_dim] at this
    rw [hc_top, one_mul] at hCH
    -- Normalize ↑(Fintype.card n) to ↑N
    simp only [hN_def.symm] at hCH
    -- Reindex: ∑_{j<N-1} c_{N-(j+1)} s_{N-(j+1)} = ∑_{j<N-1} c_{j+1} s_{j+1}
    suffices sum_eq : ∑ j ∈ range (N - 1),
        A.charpoly.coeff (N - (j + 1)) * trace (A ^ (N - (j + 1))) =
        ∑ j ∈ range (N - 1),
        A.charpoly.coeff (j + 1) * trace (A ^ (j + 1)) by
      rw [sum_eq, Nat.sub_self]
      linear_combination hCH
    rw [← sum_range_reflect (fun j => A.charpoly.coeff (j + 1) * trace (A ^ (j + 1)))]
    apply sum_congr rfl; intro j hj
    simp only [mem_range] at hj
    have idx : N - 1 - 1 - j + 1 = N - (j + 1) := by omega
    simp only [idx]
  · -- k < N case: use adjugate approach
    have hk_lt : k < N := by omega
    have hk_bound : k + 1 ≤ N := by omega
    -- Step 1: adjCoeff formula
    have formula := adjCoeff_eq_sum A k hk_bound
    -- Step 2: From trace_adjugate_charmatrix, extract coeff (N-1-k)
    have htrace_adj := trace_adjugate_charmatrix A
    -- derivative coeff: coeff (N-1-k) of derivative = (N-k) * c_{N-k}
    have trace_via_deriv : ∑ v : n, (A.charmatrix.adjugate v v).coeff (N - 1 - k) =
        (↑(N - k) : R) * A.charpoly.coeff (N - k) := by
      have step1 : ∑ v : n, (A.charmatrix.adjugate v v).coeff (N - 1 - k) =
          (Polynomial.derivative A.charpoly).coeff (N - 1 - k) := by
        rw [← Polynomial.finset_sum_coeff]
        exact congr_arg (fun p => p.coeff (N - 1 - k)) htrace_adj
      rw [step1, Polynomial.coeff_derivative]
      have h : N - 1 - k + 1 = N - k := by omega
      rw [h, show (↑(N - 1 - k) : R) + 1 = ↑(N - k) from by
        rw [← Nat.cast_succ]; exact congr_arg Nat.cast h]
      exact mul_comm _ _
    -- Step 3: Trace of adjCoeff(N-1-k) via the explicit formula
    have trace_via_formula : ∑ v : n, (A.charmatrix.adjugate v v).coeff (N - 1 - k) =
        ∑ i ∈ range (k + 1), A.charpoly.coeff (N - i) * trace (A ^ (k - i)) := by
      -- Convert LHS to trace of adjCoeff
      have htrace : ∑ v : n, (A.charmatrix.adjugate v v).coeff (N - 1 - k) =
          trace (adjCoeff A (N - 1 - k)) := by
        simp only [adjCoeff, trace, diag_apply]
      rw [htrace, formula, trace_sum]
      apply sum_congr rfl; intro i _
      rw [trace_smul, smul_eq_mul]
    -- Equate: ∑_{i=0}^{k} c_{N-i} * s_{k-i} = (N-k) * c_{N-k}
    rw [trace_via_formula] at trace_via_deriv
    -- Split off the first term (i = 0): c_N * s_k
    rw [sum_range_succ'] at trace_via_deriv
    simp only [Nat.sub_zero] at trace_via_deriv
    -- Split off the last term from the inner sum: c_{N-k} * s_0
    have hsplit := sum_range_succ
      (fun i => A.charpoly.coeff (N - (i + 1)) * trace (A ^ (k - (i + 1)))) (k - 1)
    rw [show (k - 1) + 1 = k from by omega] at hsplit
    rw [hsplit, Nat.sub_self, pow_zero, trace_one] at trace_via_deriv
    -- Handle trivial ring case
    by_cases hR : Nontrivial R
    swap
    · rw [not_nontrivial_iff_subsingleton] at hR; haveI := hR
      have h0 : ∀ r : R, r = 0 := fun r => Subsingleton.elim r 0
      simp [h0]
    haveI := hR
    -- c_N = 1 (charpoly is monic)
    have hc_top : A.charpoly.coeff N = 1 := by
      have h := (charpoly_monic A).leadingCoeff
      rwa [Polynomial.leadingCoeff, charpoly_natDegree_eq_dim] at h
    rw [hc_top, one_mul] at trace_via_deriv
    -- Normalize ↑(Fintype.card n) to ↑N and replace ↑(N-k) with ↑N - ↑k
    simp only [hN_def.symm] at trace_via_deriv
    rw [Nat.cast_sub hk'] at trace_via_deriv
    -- trace_via_deriv: s_k + (middle + c_{N-k} * ↑N) = (↑N - ↑k) * c_{N-k}
    -- Newton's goal: s_k + middle + ↑k * c_{N-k} = 0
    linear_combination trace_via_deriv

end Matrix
