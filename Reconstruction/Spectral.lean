import Reconstruction.Defs
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Reconstruction Conjecture — Spectral Graph Theory

We develop spectral graph theory tools for the reconstruction conjecture.
The central result is the **derivative formula** for graph characteristic polynomials:

$$\varphi'(G, x) = \sum_v \varphi(G - v, x)$$

where $\varphi(G, x) = \det(xI - A_G)$ is the characteristic polynomial of the
adjacency matrix. This implies that if two graphs have the same deck, they share
the same characteristic polynomial derivative — and therefore agree on all
non-constant coefficients.

## Main definitions

* `SimpleGraph.charPoly` — characteristic polynomial of a graph

## Main results

* `SimpleGraph.adjMatrix_induce` — adjacency matrix of induced subgraph = principal submatrix
* `SimpleGraph.charPoly_deleteVert` — `charPoly(G - v)` = charpoly of principal submatrix
* `SimpleGraph.charPoly_eq_of_iso` — isomorphic graphs have equal characteristic polynomials
* `SimpleGraph.charPoly_derivative_eq_sum` — derivative formula
* `SimpleGraph.SameDeck.charPoly_derivative_eq` — same deck → same char. poly. derivative
* `SimpleGraph.SameDeck.charPoly_coeff_eq` — same deck → same non-constant coefficients

## References

* Kelly, P. J. (1942). "On isometric transformations".
* Tutte, W. T. (1979). "All the king's horses".
* Schwenk, A. J. (1979). "Spectral reconstruction problems".
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Phase 1: Foundation — Graph-Matrix Bridge -/

section Foundation

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The adjacency matrix of `G.induce s` equals the principal submatrix of `G.adjMatrix`
indexed by `s`. This bridges graph-theoretic vertex deletion and matrix-theoretic
principal submatrices. -/
theorem adjMatrix_induce (s : Set V) [DecidablePred (· ∈ s)]
    (α : Type*) [Zero α] [One α] :
    (G.induce s).adjMatrix α = (G.adjMatrix α).submatrix Subtype.val Subtype.val := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [adjMatrix_apply, comap_adj, Function.Embedding.subtype_apply,
    Matrix.submatrix_apply]

/-- The characteristic polynomial of a graph, defined as the characteristic polynomial
of its adjacency matrix: `charPoly G R = det(XI - A_G)`. -/
noncomputable def charPoly (R : Type*) [CommRing R] : Polynomial R :=
  (G.adjMatrix R).charpoly

/-- The characteristic polynomial of `G.deleteVert v` equals the characteristic polynomial
of the principal submatrix of `G.adjMatrix` obtained by deleting row and column `v`. -/
theorem charPoly_deleteVert (v : V) (R : Type*) [CommRing R] :
    (G.deleteVert v).charPoly R =
    ((G.adjMatrix R).submatrix
      (Subtype.val : {w : V // w ≠ v} → V)
      (Subtype.val : {w : V // w ≠ v} → V)).charpoly := by
  exact congr_arg Matrix.charpoly (G.adjMatrix_induce {w | w ≠ v} R)

/-- Isomorphic graphs have equal characteristic polynomials. The proof goes through
matrix reindexing: a graph isomorphism `φ : G ≃g H` yields a permutation of indices
that conjugates the adjacency matrix. -/
theorem charPoly_eq_of_iso {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (φ : G ≃g H) (R : Type*) [CommRing R] :
    G.charPoly R = H.charPoly R := by
  unfold charPoly
  have hadj : H.adjMatrix R = Matrix.reindex φ.toEquiv φ.toEquiv (G.adjMatrix R) := by
    ext i j
    simp only [adjMatrix_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    have key : H.Adj i j ↔ G.Adj (φ.toEquiv.symm i) (φ.toEquiv.symm j) :=
      φ.symm.map_rel_iff.symm
    split_ifs with h1 h2
    all_goals simp_all
  rw [hadj, Matrix.charpoly_reindex]

end Foundation

/-! ### Phase 2: The Derivative Formula -/

section DerivativeFormula

open Matrix Polynomial Equiv.Perm Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! #### Phase 2a: Charmatrix entry derivatives -/

theorem derivative_charmatrix_apply_eq {R : Type*} [CommRing R] (M : Matrix n n R) (i : n) :
    Polynomial.derivative (M.charmatrix i i) = 1 := by
  simp [Matrix.charmatrix_apply_eq]

theorem derivative_charmatrix_apply_ne {R : Type*} [CommRing R] (M : Matrix n n R) {i j : n}
    (h : i ≠ j) : Polynomial.derivative (M.charmatrix i j) = 0 := by
  unfold Matrix.charmatrix
  simp [sub_apply, scalar_apply, diagonal_apply, if_neg h]

/-! #### Phase 2b: Charmatrix-submatrix bridge -/

theorem charmatrix_submatrix {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (M : Matrix n n R) (f : l → n) (hf : Function.Injective f) :
    Matrix.charmatrix (M.submatrix f f) = M.charmatrix.submatrix f f := by
  ext i j
  simp only [Matrix.charmatrix, sub_apply, scalar_apply, diagonal_apply,
    RingHom.mapMatrix_apply, Matrix.map_apply, submatrix_apply]
  by_cases h : i = j
  · subst h; simp [hf.eq_iff]
  · simp [h, hf.ne h]

/-! #### Phase 2c: Derivative of determinant for charmatrices -/

/-- Helper: for `σ : Perm n` with `σ k = k`, construct the restriction to `{j // j ≠ k}`.
Note: `subtypePerm` takes `∀ x, p (f x) ↔ p x`. -/
private def restrictPerm (σ : Equiv.Perm n) (k : n) (hσ : σ k = k) :
    Equiv.Perm {j : n // j ≠ k} :=
  σ.subtypePerm fun x => by
    constructor
    · -- p (σ x) → p x, i.e., σ x ≠ k → x ≠ k
      intro hσx hc; exact absurd (hc ▸ hσ) hσx
    · -- p x → p (σ x), i.e., x ≠ k → σ x ≠ k
      intro hx hσx; exact hx (σ.injective (hσx.trans hσ.symm))

/-- The derivative of the determinant of a charmatrix equals the sum of determinants
of its principal submatrices. This is the core linear-algebra fact behind the
derivative formula for graph characteristic polynomials. -/
theorem derivative_det_charmatrix {R : Type*} [CommRing R] (M : Matrix n n R) :
    Polynomial.derivative M.charmatrix.det =
    ∑ k : n, (M.charmatrix.submatrix
      (Subtype.val : {j // j ≠ k} → n) (Subtype.val : {j // j ≠ k} → n)).det := by
  set B := M.charmatrix with hB_def
  -- Step 1: Leibniz formula + linearity of derivative
  rw [det_apply', map_sum]
  -- Step 2: derivative of ε(σ) * prod = ε(σ) * derivative(prod), using derivative_intCast_mul
  simp_rw [Polynomial.derivative_intCast_mul]
  -- Step 3: Product rule for polynomial derivative
  simp_rw [Polynomial.derivative_prod_finset (s := Finset.univ)]
  -- Step 4: Distribute ε(σ) into the inner sum, reassociate
  simp_rw [Finset.mul_sum, ← mul_assoc]
  -- Step 5: Swap sums ∑_σ ∑_k → ∑_k ∑_σ
  rw [Finset.sum_comm]
  -- Step 6: For each k, simplify derivative of charmatrix entries
  apply Finset.sum_congr rfl; intro k _
  have deriv_entry : ∀ σ : Equiv.Perm n,
      Polynomial.derivative (B (σ k) k) = if σ k = k then 1 else 0 := fun σ => by
    by_cases h : σ k = k
    · rw [if_pos h, h]; exact derivative_charmatrix_apply_eq M k
    · rw [if_neg h]; exact derivative_charmatrix_apply_ne M h
  simp_rw [deriv_entry, mul_ite, mul_one, mul_zero]
  -- Step 7: Convert if-then-else sum to filtered sum
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  -- Step 8: Relate filtered sum to det of submatrix via perm bijection
  rw [det_apply']
  symm
  apply Finset.sum_nbij' (fun τ => Equiv.Perm.ofSubtype τ)
    (fun σ => if hσ : σ k = k then restrictPerm σ k hσ else 1)
  -- ofSubtype maps into the filter
  · intro τ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Equiv.Perm.ofSubtype_apply_of_not_mem τ (not_not.mpr rfl)
  -- inverse maps into univ
  · intro _ _; exact Finset.mem_univ _
  -- left inverse: restrictPerm ∘ ofSubtype = id
  · intro τ _
    have hfix : (Equiv.Perm.ofSubtype τ) k = k :=
      Equiv.Perm.ofSubtype_apply_of_not_mem τ (not_not.mpr rfl)
    simp only [dif_pos hfix, restrictPerm]
    exact Equiv.Perm.subtypePerm_ofSubtype τ
  -- right inverse: ofSubtype ∘ restrictPerm = id (on filter)
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    simp only [dif_pos hσ, restrictPerm]
    exact Equiv.Perm.ofSubtype_subtypePerm _ fun x hx => by
      intro hc; subst hc; exact hx hσ
  -- values match
  · intro τ _
    congr 1
    · simp [Equiv.Perm.sign_ofSubtype]
    · symm
      rw [Finset.prod_subtype (p := (· ≠ k)) (Finset.univ.erase k)
        (fun x => by simp [Finset.mem_erase])]
      apply Finset.prod_congr rfl
      intro ⟨j, hj⟩ _
      simp only [submatrix_apply]
      rw [Equiv.Perm.ofSubtype_apply_of_mem τ hj]

/-! #### Phase 2d: Assembly — the graph-theoretic derivative formula -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The derivative formula for graph characteristic polynomials.**

The derivative of the characteristic polynomial of `G` equals the sum of characteristic
polynomials of all vertex-deleted subgraphs:

$$\varphi'(G, x) = \sum_{v \in V} \varphi(G - v, x)$$

This is a consequence of the Leibniz formula for the determinant and the product rule
for polynomial differentiation. The key insight is that differentiating `det(xI - A)`
via the Leibniz expansion yields, for each diagonal position `v`, the determinant of
the `(v,v)`-cofactor of the charmatrix, which equals `charPoly(G - v)`. -/
theorem charPoly_derivative_eq_sum (R : Type*) [CommRing R] :
    Polynomial.derivative (G.charPoly R) = ∑ v : V, (G.deleteVert v).charPoly R := by
  simp only [charPoly, Matrix.charpoly]
  rw [derivative_det_charmatrix]
  apply Finset.sum_congr rfl; intro v _
  rw [show (G.deleteVert v).adjMatrix R = (G.adjMatrix R).submatrix Subtype.val Subtype.val
    from G.adjMatrix_induce {w | w ≠ v} R]
  rw [charmatrix_submatrix _ _ Subtype.val_injective]

end DerivativeFormula

/-! ### Phase 3: Reconstructibility Corollaries -/

section Reconstructibility

variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- **The characteristic polynomial derivative is reconstructible.**

If two graphs have the same deck, they have the same characteristic polynomial derivative.
This follows from the derivative formula and the fact that isomorphic graphs have
equal characteristic polynomials. -/
theorem SameDeck.charPoly_derivative_eq (h : G.SameDeck H)
    (R : Type*) [CommRing R] :
    Polynomial.derivative (G.charPoly R) = Polynomial.derivative (H.charPoly R) := by
  rw [G.charPoly_derivative_eq_sum R, H.charPoly_derivative_eq_sum R]
  obtain ⟨σ, hσ⟩ := h
  calc ∑ v, (G.deleteVert v).charPoly R
      = ∑ v, (H.deleteVert (σ v)).charPoly R :=
        Finset.sum_congr rfl fun v _ =>
          (G.deleteVert v).charPoly_eq_of_iso (hσ v).some R
    _ = ∑ v, (H.deleteVert v).charPoly R :=
        σ.sum_comp (fun w => (H.deleteVert w).charPoly R)

/-- **Non-constant coefficients of the characteristic polynomial are reconstructible.**

If two graphs have the same deck, all coefficients of their characteristic polynomials
of degree ≥ 1 agree. Since `charPoly` is monic of degree `|V|`, the derivative
determines all coefficients of degree ≥ 1; only the constant term `(-1)^n det(A)` is
not immediately recovered.

(The constant term IS recoverable via Tutte's deeper theorem using Kelly's Lemma and
the Sachs coefficient theorem, but that requires significantly more machinery.) -/
theorem SameDeck.charPoly_coeff_eq (h : G.SameDeck H)
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    {k : ℕ} (hk : 1 ≤ k) :
    (G.charPoly R).coeff k = (H.charPoly R).coeff k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hderiv := h.charPoly_derivative_eq R
  have hcoeff := congr_arg (fun p => p.coeff n) hderiv
  simp only [Polynomial.coeff_derivative] at hcoeff
  have hne : (↑n + 1 : R) ≠ 0 := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (by omega)
  exact mul_right_cancel₀ hne hcoeff

end Reconstructibility

end SimpleGraph
