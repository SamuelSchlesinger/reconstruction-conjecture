import Reconstruction.TraceReconstruction
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp

/-!
# Top-Trace Closed-Walk Support Split

This module isolates the missing `k = |V|` trace in the characteristic-polynomial
argument.  The trace of `A^k` is the number of rooted closed walks of length
`k`; for `k = |V|`, we split those walks into two sectors:

* walks whose support is a proper subset of the vertex set;
* walks whose support has full cardinality.

The proper-support sector is further expanded as a sum over exact vertex
supports.  This is the Lean-shaped version of the next campaign: regroup the
proper-support sum by induced-subgraph isomorphism type and use Kelly's Lemma,
then handle the full-support/Hamilton-cycle sector by Kocay-style counting.

## Main results

* `SimpleGraph.trace_adjMatrix_pow_eq_rootedClosedWalkCount`
* `SimpleGraph.rootedClosedWalkCount_eq_proper_add_full`
* `SimpleGraph.properSupportClosedWalkCount_eq_sum_exactSupport`
* `SimpleGraph.trace_adjMatrix_card_eq_of_support_counts_eq`

## References

* Kocay, W. L. (1981). "Some new methods in reconstruction theory".
* Tutte, W. T. (1979). "All the king's horses".
-/

set_option autoImplicit false

namespace SimpleGraph

noncomputable section

open Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A rooted closed walk of length `k`, packaged as a root together with the walk.

This is the finite type whose cardinality is the trace of the `k`th adjacency
matrix power.  The packaging keeps the root explicit, which is useful for
splitting the trace by vertex support. -/
abbrev RootedClosedWalk (k : ℕ) : Type _ :=
  Σ v : V, {p : G.Walk v v // p.length = k}

/-- The number of rooted closed walks of length `k`. -/
def rootedClosedWalkCount (k : ℕ) : ℕ :=
  Fintype.card (RootedClosedWalk G k)

/-- The number of rooted closed walks of length `k` whose support is not all of
`V`. -/
def properSupportClosedWalkCount (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (RootedClosedWalk G k)).filter fun wp =>
      wp.2.1.support.toFinset.card < Fintype.card V).card

/-- The number of rooted closed walks of length `k` whose support has full
cardinality. -/
def fullSupportClosedWalkCount (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (RootedClosedWalk G k)).filter fun wp =>
      wp.2.1.support.toFinset.card = Fintype.card V).card

/-- Rooted closed walks of length `k` with exactly the vertex support `U`. -/
def exactSupportClosedWalkCount (k : ℕ) (U : Finset V) : ℕ :=
  ((Finset.univ : Finset (RootedClosedWalk G k)).filter fun wp =>
      wp.2.1.support.toFinset = U).card

omit [DecidableRel G.Adj] in
/-- A support whose cardinality is `|V|` is the whole vertex set. -/
theorem support_toFinset_eq_univ_of_card_eq {k : ℕ} (wp : RootedClosedWalk G k)
    (hcard : wp.2.1.support.toFinset.card = Fintype.card V) :
    wp.2.1.support.toFinset = Finset.univ := by
  exact Finset.eq_univ_of_card wp.2.1.support.toFinset (by simpa using hcard)

/-- Every rooted closed walk has either proper support or full support. -/
theorem rootedClosedWalkCount_eq_proper_add_full (k : ℕ) :
    G.rootedClosedWalkCount k =
      G.properSupportClosedWalkCount k + G.fullSupportClosedWalkCount k := by
  classical
  unfold rootedClosedWalkCount properSupportClosedWalkCount fullSupportClosedWalkCount
  rw [← Finset.card_univ]
  rw [← Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (RootedClosedWalk G k)))
    (p := fun wp => wp.2.1.support.toFinset.card < Fintype.card V)]
  rw [add_left_cancel_iff]
  apply congrArg Finset.card
  ext wp
  simp only [mem_filter, mem_univ, true_and]
  have hle : wp.2.1.support.toFinset.card ≤ Fintype.card V := by
    simpa using wp.2.1.support.toFinset.card_le_univ
  omega

/-- The proper-support part of the trace is the sum over exact proper supports. -/
theorem properSupportClosedWalkCount_eq_sum_exactSupport (k : ℕ) :
    G.properSupportClosedWalkCount k =
      ∑ U ∈ (Finset.univ : Finset V).powerset with U.card < Fintype.card V,
        G.exactSupportClosedWalkCount k U := by
  classical
  unfold properSupportClosedWalkCount exactSupportClosedWalkCount
  let s := (Finset.univ : Finset (RootedClosedWalk G k)).filter fun wp =>
    wp.2.1.support.toFinset.card < Fintype.card V
  let t := (Finset.univ : Finset V).powerset.filter fun U =>
    U.card < Fintype.card V
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (f := fun wp : RootedClosedWalk G k => wp.2.1.support.toFinset)
    (s := s) (t := t) (by
      intro wp hwp
      have hproper : wp.2.1.support.toFinset.card < Fintype.card V := by
        simpa [s] using hwp
      simp [t, hproper])
  rw [hfiber]
  apply Finset.sum_congr rfl
  intro U hU
  rw [mem_filter, mem_powerset] at hU
  congr 1
  ext wp
  simp only [s, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨_, hsupp⟩
    exact hsupp
  · intro hsupp
    exact ⟨by rw [hsupp]; exact hU.2, hsupp⟩

/-- The full-support part is the exact-support count for `univ`. -/
theorem fullSupportClosedWalkCount_eq_exactSupport_univ (k : ℕ) :
    G.fullSupportClosedWalkCount k =
      G.exactSupportClosedWalkCount k (Finset.univ : Finset V) := by
  classical
  unfold fullSupportClosedWalkCount exactSupportClosedWalkCount
  congr 1
  ext wp
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · exact support_toFinset_eq_univ_of_card_eq G wp
  · intro h
    rw [h]
    simp

/-- The closed-walk count is the trace of the corresponding adjacency-matrix
power. -/
theorem trace_adjMatrix_pow_eq_rootedClosedWalkCount (k : ℕ) :
    trace ((G.adjMatrix ℤ) ^ k) = (G.rootedClosedWalkCount k : ℤ) := by
  classical
  simp [rootedClosedWalkCount, Matrix.trace, SimpleGraph.adjMatrix_pow_apply_eq_card_walk]

theorem trace_adjMatrix_pow_eq_proper_add_full (k : ℕ) :
    trace ((G.adjMatrix ℤ) ^ k) =
      (G.properSupportClosedWalkCount k + G.fullSupportClosedWalkCount k : ℤ) := by
  rw [trace_adjMatrix_pow_eq_rootedClosedWalkCount]
  exact congrArg Nat.cast (G.rootedClosedWalkCount_eq_proper_add_full k)

variable {G} {H : SimpleGraph V} [DecidableRel H.Adj]

/-- The top trace is reduced to the two support-count subgoals. -/
theorem trace_adjMatrix_card_eq_of_support_counts_eq
    (hproper : G.properSupportClosedWalkCount (Fintype.card V) =
      H.properSupportClosedWalkCount (Fintype.card V))
    (hfull : G.fullSupportClosedWalkCount (Fintype.card V) =
      H.fullSupportClosedWalkCount (Fintype.card V)) :
    trace ((G.adjMatrix ℤ) ^ Fintype.card V) =
      trace ((H.adjMatrix ℤ) ^ Fintype.card V) := by
  rw [trace_adjMatrix_pow_eq_proper_add_full,
    trace_adjMatrix_pow_eq_proper_add_full, hproper, hfull]

end

end SimpleGraph
