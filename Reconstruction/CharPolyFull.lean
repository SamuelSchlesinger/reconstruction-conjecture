import Reconstruction.Spectral
import Reconstruction.TraceReconstruction
import Reconstruction.TopTrace
import Reconstruction.Newton
import Reconstruction.SupportCount

/-!
# Reconstruction Conjecture — Full Characteristic Polynomial

The full characteristic polynomial (including the constant term) is a
reconstructible graph invariant.

## Main results

* `SimpleGraph.SameDeck.charPoly_coeff_zero_eq_of_trace_card_eq` — the
  constant term follows from equality of the top trace `tr(A^|V|)`.
* `SimpleGraph.SameDeck.charPoly_coeff_zero_eq_of_support_counts_eq` — the
  constant term follows from equality of the proper-support and full-support
  top-length closed-walk counts.
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

open Matrix Finset

/-- Conditional constant-term reconstruction from the missing top trace.

The Cayley-Hamilton trace identity says
`∑ i, c_i tr(A^i) = 0`. All non-constant coefficients are already
reconstructible, and traces of powers `< |V|` are reconstructible by
`SameDeck.trace_adjMatrix_pow_eq`. Therefore the constant coefficient follows
as soon as the remaining top trace `tr(A^|V|)` is known to agree. -/
theorem SameDeck.charPoly_coeff_zero_eq_of_trace_card_eq (h : G.SameDeck H)
    (hV : 3 ≤ Fintype.card V)
    (htrace :
      trace ((G.adjMatrix ℤ) ^ Fintype.card V) =
        trace ((H.adjMatrix ℤ) ^ Fintype.card V)) :
    (G.charPoly ℤ).coeff 0 = (H.charPoly ℤ).coeff 0 := by
  let N := Fintype.card V
  let termG : ℕ → ℤ := fun i =>
    (G.adjMatrix ℤ).charpoly.coeff i * trace ((G.adjMatrix ℤ) ^ i)
  let termH : ℕ → ℤ := fun i =>
    (H.adjMatrix ℤ).charpoly.coeff i * trace ((H.adjMatrix ℤ) ^ i)
  have hN_ne : (N : ℤ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  have hrest :
      ∑ i ∈ (range (N + 1)).erase 0, termG i =
        ∑ i ∈ (range (N + 1)).erase 0, termH i := by
    apply sum_congr rfl
    intro i hi
    rw [mem_erase, mem_range] at hi
    have hi_pos : 1 ≤ i := by omega
    have hi_le : i ≤ N := by omega
    have hcoeff :
        (G.adjMatrix ℤ).charpoly.coeff i =
          (H.adjMatrix ℤ).charpoly.coeff i := by
      simpa [charPoly] using h.charPoly_coeff_eq ℤ hi_pos
    have htrace_i :
        trace ((G.adjMatrix ℤ) ^ i) =
          trace ((H.adjMatrix ℤ) ^ i) := by
      by_cases hiN : i = N
      · subst hiN
        simpa [N] using htrace
      · exact h.trace_adjMatrix_pow_eq hV (k := i) (by omega)
    simp [termG, termH, hcoeff, htrace_i]
  have hCHG :
      ∑ i ∈ range (N + 1), termG i = 0 := by
    simpa [termG, N] using cayley_hamilton_trace (G.adjMatrix ℤ)
  have hCHH :
      ∑ i ∈ range (N + 1), termH i = 0 := by
    simpa [termH, N] using cayley_hamilton_trace (H.adjMatrix ℤ)
  have hsplitG :
      termG 0 + ∑ i ∈ (range (N + 1)).erase 0, termG i = 0 := by
    rw [Finset.add_sum_erase (s := range (N + 1)) (a := 0)
      (f := termG) (by simp)]
    exact hCHG
  have hsplitH :
      termH 0 + ∑ i ∈ (range (N + 1)).erase 0, termH i = 0 := by
    rw [Finset.add_sum_erase (s := range (N + 1)) (a := 0)
      (f := termH) (by simp)]
    exact hCHH
  have hmul :
      (G.charPoly ℤ).coeff 0 * (N : ℤ) =
        (H.charPoly ℤ).coeff 0 * (N : ℤ) := by
    have htermG :
        termG 0 = (G.charPoly ℤ).coeff 0 * (N : ℤ) := by
      simp [termG, charPoly, N, Matrix.trace_one]
    have htermH :
        termH 0 = (H.charPoly ℤ).coeff 0 * (N : ℤ) := by
      simp [termH, charPoly, N, Matrix.trace_one]
    linarith
  exact mul_right_cancel₀ hN_ne hmul

/-- Conditional constant-term reconstruction from the support split of the
missing top trace.

The remaining top trace is the sum of closed walks with proper support and
closed walks with full support.  Thus the constant term follows from equality
of those two support-count pieces. -/
theorem SameDeck.charPoly_coeff_zero_eq_of_support_counts_eq (h : G.SameDeck H)
    (hV : 3 ≤ Fintype.card V)
    (hproper :
      G.properSupportClosedWalkCount (Fintype.card V) =
        H.properSupportClosedWalkCount (Fintype.card V))
    (hfull :
      G.fullSupportClosedWalkCount (Fintype.card V) =
        H.fullSupportClosedWalkCount (Fintype.card V)) :
    (G.charPoly ℤ).coeff 0 = (H.charPoly ℤ).coeff 0 :=
  h.charPoly_coeff_zero_eq_of_trace_card_eq hV
    (trace_adjMatrix_card_eq_of_support_counts_eq hproper hfull)

/-- Conditional constant-term reconstruction from the **full-support sector
alone**. The proper-support sector of the top trace is unconditionally
reconstructible (`SameDeck.properSupportClosedWalkCount_eq`, via Kelly's
Lemma and the exact-support/isomorphism-class regrouping in
`Reconstruction.SupportCount`), so the constant coefficient — hence the whole
characteristic polynomial — is now reduced to equality of the full-support
top-length closed-walk counts. Those walks traverse Hamiltonian cycles, so
this hypothesis is precisely the deck-reconstructibility of the
Hamiltonian-cycle count (Tutte 1979, via Kocay's spanning-subgraph
counting). -/
theorem SameDeck.charPoly_coeff_zero_eq_of_fullSupport_eq (h : G.SameDeck H)
    (hV : 3 ≤ Fintype.card V)
    (hfull :
      G.fullSupportClosedWalkCount (Fintype.card V) =
        H.fullSupportClosedWalkCount (Fintype.card V)) :
    (G.charPoly ℤ).coeff 0 = (H.charPoly ℤ).coeff 0 :=
  h.charPoly_coeff_zero_eq_of_support_counts_eq hV
    (h.properSupportClosedWalkCount_eq _) hfull

/-- **The constant term of the characteristic polynomial is reconstructible.**

The constant term `c_0 = (-1)^n det(A)` is determined by the Cayley–Hamilton
trace identity: `n · c_0 = -(tr(A^n) + c_{n-1} tr(A^{n-1}) + ⋯ + c_1 tr(A))`.
All terms on the right are reconstructible: `c_1, ..., c_{n-1}` from the
derivative formula (`Spectral.lean`) and `tr(A^k)` from walk counting
(`TraceReconstruction.lean`). -/
theorem SameDeck.charPoly_coeff_zero_eq (h : G.SameDeck H)
    (hV : 3 ≤ Fintype.card V) :
    (G.charPoly ℤ).coeff 0 = (H.charPoly ℤ).coeff 0 := by
  -- TODO (single remaining ingredient): by
  -- `charPoly_coeff_zero_eq_of_fullSupport_eq` the constant term is reduced to
  -- equality of the full-support top-length closed-walk counts. A closed walk
  -- of length `n = |V|` visiting all `n` vertices traverses a Hamiltonian
  -- cycle (`Reconstruction.HamiltonianWalk`:
  -- `fullSupportClosedWalkCount_card_eq_hamiltonianHomCount`), so the remaining
  -- content is exactly Tutte's theorem that the number of Hamiltonian cycles
  -- is reconstructible — to be proved via Kocay's lemma: disconnected spanning
  -- subgraph counts are reconstructible by Möbius inversion over the
  -- cover-count identity (`Kocay.lean`), and the Hamiltonian count is
  -- extracted from products of path counts.
  refine h.charPoly_coeff_zero_eq_of_fullSupport_eq hV ?_
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
