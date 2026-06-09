import Reconstruction.CharPolyFull
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# The Full-Support Walk Sector is the Hamiltonian Sector

`Reconstruction.SupportCount` reduced the constant coefficient of the
characteristic polynomial to the **full-support** closed-walk count at length
`n = |V|`. This module identifies that sector combinatorially: a rooted closed
walk of length `n` visiting all `n` vertices has no room to repeat a vertex,
so it traverses a Hamiltonian cycle, and conversely every injective
homomorphism `cycleGraph n →g G` unrolls to such a walk. Hence

* `fullSupportClosedWalkCount_card_eq_hamiltonianHomCount` —
  `G.fullSupportClosedWalkCount |V| = G.hamiltonianHomCount`, where
  `hamiltonianHomCount` counts the injective graph homomorphisms
  `cycleGraph |V| →g G` (each Hamiltonian cycle contributes exactly `2·|V|`
  of them: a starting vertex and a direction);
* `SameDeck.charPoly_coeff_zero_eq_of_hamiltonianHomCount_eq` — the constant
  coefficient of the characteristic polynomial follows from agreement of the
  Hamiltonian homomorphism counts.

Together with `SameDeck.properSupportClosedWalkCount_eq`, the remaining
content of Tutte's constant-term reconstruction (`charPoly_coeff_zero_eq`) is
**exactly** the deck-reconstructibility of the Hamiltonian-cycle count —
Tutte's 1979 theorem, classically proved via Kocay's disconnected-spanning-
subgraph counting, which is the project's next staged target.

## References

* Tutte, W. T. (1979). "All the king's horses".
* Kocay, W. L. (1981). "Some new methods in reconstruction theory".
* Bondy, J. A. (1991). "A graph reconstructor's manual" (§ Tutte's theorems).
-/

set_option autoImplicit false

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Walks from vertex sequences -/

section WalkOfFn

variable (G : SimpleGraph V)

/-- Build a walk from a vertex sequence whose consecutive values are
adjacent. -/
def walkOfFn : ∀ (k : ℕ) (g : ℕ → V), (∀ i, i < k → G.Adj (g i) (g (i + 1))) →
    G.Walk (g 0) (g k)
  | 0, _, _ => Walk.nil
  | k + 1, g, h =>
    Walk.cons (h 0 (Nat.succ_pos k))
      (walkOfFn k (fun i => g (i + 1)) fun i hi => h (i + 1) (Nat.succ_lt_succ hi))

omit [Fintype V] [DecidableEq V] in
@[simp] theorem walkOfFn_length : ∀ (k : ℕ) (g : ℕ → V) (h),
    (G.walkOfFn k g h).length = k
  | 0, _, _ => rfl
  | k + 1, g, h => by
    simpa [walkOfFn] using walkOfFn_length k (fun i => g (i + 1)) _

omit [Fintype V] [DecidableEq V] in
theorem walkOfFn_getVert : ∀ (k : ℕ) (g : ℕ → V) (h) (i : ℕ), i ≤ k →
    (G.walkOfFn k g h).getVert i = g i
  | 0, _, _, i, hi => by
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    rfl
  | k + 1, g, h, 0, _ => rfl
  | k + 1, g, h, i + 1, hi => by
    simpa [walkOfFn, Walk.getVert_cons_succ] using
      walkOfFn_getVert k (fun j => g (j + 1)) _ i (Nat.succ_le_succ_iff.mp hi)

end WalkOfFn

/-! ### Walks are determined by their vertex sequences -/

omit [Fintype V] [DecidableEq V] in
private theorem getVert_copy {G : SimpleGraph V} {u v u' v' : V} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') (i : ℕ) :
    (p.copy hu hv).getVert i = p.getVert i := by
  subst hu; subst hv; rfl

omit [Fintype V] [DecidableEq V] in
private theorem walk_ext_getVert {G : SimpleGraph V} :
    ∀ {u v : V} (p q : G.Walk u v), p.length = q.length →
      (∀ i, i ≤ p.length → p.getVert i = q.getVert i) → p = q := by
  intro u v p
  induction p with
  | nil =>
    intro q hlen _
    cases q with
    | nil => rfl
    | cons h q' => simp at hlen
  | cons hadj p' ih =>
    intro q hlen hvert
    cases q with
    | nil => simp at hlen
    | cons hadj' q' =>
      rename_i w'
      have hw : p'.getVert 0 = w' := by
        have h1 := hvert 1 (by simp)
        simpa [Walk.getVert_cons_succ] using h1
      rw [Walk.getVert_zero] at hw
      subst hw
      have htail : p' = q' := by
        refine ih q' (by simpa using hlen) fun i hi => ?_
        have := hvert (i + 1) (by simp; omega)
        simpa [Walk.getVert_cons_succ] using this
      subst htail
      rfl

omit [Fintype V] [DecidableEq V] in
/-- Two rooted closed walks of the same length with the same vertex sequence
are equal. The root is the sequence at `0`, so no separate root hypothesis is
needed. -/
private theorem rootedClosedWalk_ext {G : SimpleGraph V} {k : ℕ} (wp wq : G.RootedClosedWalk k)
    (h : ∀ i, wp.2.1.getVert i = wq.2.1.getVert i) : wp = wq := by
  obtain ⟨v, p, hp⟩ := wp
  obtain ⟨w, q, hq⟩ := wq
  have hroot : v = w := by simpa using h 0
  subst hroot
  have hpq : p = q := walk_ext_getVert p q (hp.trans hq.symm) fun i _ => h i
  subst hpq
  rfl

/-! ### Cycle-graph adjacency bookkeeping -/

private theorem fin_val_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    ((1 : Fin n) : ℕ) = 1 := by
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (by omega)

/-- Each vertex of `cycleGraph n` is adjacent to its successor (`n ≥ 2`).
Same proof as `cycleGraph_adj_succ` in `Reconstruction.PEO`; duplicated to
keep this module independent of the chordal stack. -/
private theorem cycle_adj_succ {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (cycleGraph n).Adj i (i + 1) := by
  rw [cycleGraph_adj']
  right
  rw [add_sub_cancel_left]
  exact fin_val_one hn

/-- Adjacency in `cycleGraph n` means the indices are cyclically
consecutive. -/
private theorem eq_add_one_of_cycle_adj {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    {a b : Fin n} (h : (cycleGraph n).Adj a b) : a = b + 1 ∨ b = a + 1 := by
  rw [cycleGraph_adj'] at h
  rcases h with h | h
  · left
    have hab : a - b = 1 := Fin.ext (by rw [fin_val_one hn]; exact h)
    rw [sub_eq_iff_eq_add] at hab
    exact hab.trans (add_comm 1 b)
  · right
    have hba : b - a = 1 := Fin.ext (by rw [fin_val_one hn]; exact h)
    rw [sub_eq_iff_eq_add] at hba
    exact hba.trans (add_comm 1 a)

/-! ### Unrolling an injective homomorphism to a rooted closed walk -/

section HomWalk

variable {G : SimpleGraph V} {n : ℕ} [NeZero n]

/-- The vertex sequence of a homomorphism from the `n`-cycle: position `i`
maps to the image of `i mod n`. -/
private def homSeq (f : cycleGraph n →g G) (i : ℕ) : V :=
  f ⟨i % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

omit [Fintype V] [DecidableEq V] in
private theorem homSeq_adj (hn : 2 ≤ n) (f : cycleGraph n →g G) :
    ∀ i, i < n → G.Adj (homSeq f i) (homSeq f (i + 1)) := by
  intro i _
  have hsucc : (⟨(i + 1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩ : Fin n) =
      ⟨i % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩ + 1 := by
    apply Fin.ext
    rw [Fin.val_add, fin_val_one hn, Nat.mod_add_mod]
  unfold homSeq
  rw [hsucc]
  exact f.map_adj (cycle_adj_succ hn _)

variable [DecidableRel G.Adj]

/-- The rooted closed walk obtained by unrolling a homomorphism from the
`n`-cycle: follow the images of `0, 1, …, n` and close up using
`n ≡ 0 (mod n)`. -/
private def homRCW (hn : 2 ≤ n) (f : cycleGraph n →g G) : G.RootedClosedWalk n :=
  ⟨homSeq f 0,
    ⟨(G.walkOfFn n (homSeq f) (homSeq_adj hn f)).copy rfl
        (congrArg f (Fin.ext (by simp))),
      by rw [Walk.length_copy, walkOfFn_length]⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem homRCW_getVert (hn : 2 ≤ n) (f : cycleGraph n →g G) {i : ℕ}
    (hi : i ≤ n) : (homRCW hn f).2.1.getVert i = homSeq f i := by
  unfold homRCW
  rw [getVert_copy, walkOfFn_getVert _ _ _ _ _ hi]

end HomWalk

/-! ### The Hamiltonian homomorphism count -/

variable (G : SimpleGraph V)

noncomputable instance {n : ℕ} : Fintype (cycleGraph n →g G) :=
  Fintype.ofInjective (fun f => ⇑f) DFunLike.coe_injective

/-- The number of injective graph homomorphisms `cycleGraph |V| →g G`. An
injective homomorphism from the `|V|`-cycle is precisely a Hamiltonian cycle
traversal: each Hamiltonian cycle of `G` contributes exactly `2·|V|` of them
(a choice of starting vertex and of direction). The deck-reconstructibility
of this count is Tutte's theorem and is the single remaining ingredient of
the constant-coefficient reconstruction. -/
def hamiltonianHomCount : ℕ :=
  Fintype.card {f : cycleGraph (Fintype.card V) →g G // Function.Injective f}

variable [DecidableRel G.Adj]

/-- **The full-support sector is the Hamiltonian sector.** A rooted closed
walk of length `|V|` with full support traverses a Hamiltonian cycle: its
`|V| + 1` vertex slots cover all `|V|` vertices with the single repetition
`getVert 0 = getVert |V|`, so the first `|V|` slots are pairwise distinct and
consecutive slots are adjacent. Conversely every injective homomorphism from
`cycleGraph |V|` unrolls to such a walk. -/
theorem fullSupportClosedWalkCount_card_eq_hamiltonianHomCount
    (hV : 3 ≤ Fintype.card V) :
    G.fullSupportClosedWalkCount (Fintype.card V) = G.hamiltonianHomCount := by
  classical
  have hn0 : 0 < Fintype.card V := by omega
  haveI : NeZero (Fintype.card V) := ⟨by omega⟩
  have hn2 : 2 ≤ Fintype.card V := by omega
  rw [hamiltonianHomCount, Fintype.card_subtype]
  unfold fullSupportClosedWalkCount
  refine le_antisymm
    (Finset.card_le_card_of_surjOn (homRCW hn2) ?_)
    (Finset.card_le_card_of_injOn (homRCW hn2) ?_ ?_)
  · -- surjectivity: a full-support closed walk of length `|V|` is Hamiltonian
    rintro ⟨v, p, hp⟩ hwp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hwp
    -- the first `|V|` vertex slots biject with `V`
    have himg : Finset.image (fun j : Fin (Fintype.card V) => p.getVert ↑j)
        Finset.univ = p.support.toFinset := by
      apply Finset.Subset.antisymm
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨j, rfl⟩ := hx
        refine List.mem_toFinset.mpr (p.mem_support_iff_exists_getVert.mpr ⟨↑j, rfl, ?_⟩)
        rw [hp]
        omega
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        obtain ⟨i, hxi, hile⟩ := p.mem_support_iff_exists_getVert.mp
          (List.mem_toFinset.mp hx)
        rw [hp] at hile
        rcases Nat.lt_or_ge i (Fintype.card V) with hilt | hige
        · exact ⟨⟨i, hilt⟩, hxi⟩
        · refine ⟨⟨0, hn0⟩, ?_⟩
          have hieq : i = Fintype.card V := by omega
          rw [← hxi, hieq, Walk.getVert_zero, ← hp, Walk.getVert_length]
    have hinj : Function.Injective fun j : Fin (Fintype.card V) => p.getVert ↑j := by
      rw [← Set.injOn_univ, ← Finset.coe_univ]
      rw [← Finset.card_image_iff, himg, hwp, Finset.card_univ, Fintype.card_fin]
    -- the traversal homomorphism
    have hmapadj : ∀ a b : Fin (Fintype.card V), (cycleGraph (Fintype.card V)).Adj a b →
        G.Adj (p.getVert ↑a) (p.getVert ↑b) := by
      have hstep : ∀ c : Fin (Fintype.card V),
          G.Adj (p.getVert ↑c) (p.getVert ↑(c + 1)) := by
        intro c
        rcases Nat.lt_or_ge (↑c + 1) (Fintype.card V) with hlt | hge
        · have hc1 : ((c + 1 : Fin (Fintype.card V)) : ℕ) = ↑c + 1 := by
            rw [Fin.val_add, fin_val_one hn2, Nat.mod_eq_of_lt hlt]
          rw [hc1]
          exact p.adj_getVert_succ (by omega)
        · have hceq : (c : ℕ) = Fintype.card V - 1 := by have := c.isLt; omega
          have hc1 : ((c + 1 : Fin (Fintype.card V)) : ℕ) = 0 := by
            rw [Fin.val_add, fin_val_one hn2, hceq,
              Nat.sub_add_cancel (by omega), Nat.mod_self]
          have hstep' := p.adj_getVert_succ (i := Fintype.card V - 1)
            (by rw [hp]; omega)
          rw [Nat.sub_add_cancel (by omega : 1 ≤ Fintype.card V)] at hstep'
          have hend : p.getVert (Fintype.card V) = v := by
            rw [← hp]; exact p.getVert_length
          rw [hend] at hstep'
          rw [hc1, hceq, Walk.getVert_zero]
          exact hstep'
      intro a b hab
      rcases eq_add_one_of_cycle_adj hn2 hab with hba | hab'
      · rw [hba]
        exact (hstep b).symm
      · rw [hab']
        exact hstep a
    refine ⟨⟨fun j => p.getVert ↑j, fun {a b} hab => hmapadj a b hab⟩, ?_, ?_⟩
    · simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
      exact hinj
    · -- the unrolled walk recovers the original
      refine rootedClosedWalk_ext _ _ fun i => ?_
      rcases Nat.lt_or_ge i (Fintype.card V + 1) with hile | higt
      · have hi : i ≤ Fintype.card V := by omega
        rw [homRCW_getVert hn2 _ hi]
        change p.getVert (i % Fintype.card V) = p.getVert i
        rcases Nat.lt_or_ge i (Fintype.card V) with hilt | hige
        · rw [Nat.mod_eq_of_lt hilt]
        · have hieq : i = Fintype.card V := by omega
          rw [hieq, Nat.mod_self, Walk.getVert_zero, ← hp, Walk.getVert_length]
      · -- beyond the length both walks sit at their endpoint
        have hlen1 : (homRCW hn2 ⟨fun j => p.getVert ↑j, fun {a b} hab =>
            hmapadj a b hab⟩).2.1.length = Fintype.card V :=
          (homRCW hn2 _).2.2
        rw [Walk.getVert_of_length_le _ (by rw [hlen1]; omega),
          Walk.getVert_of_length_le _ (by rw [hp]; omega)]
        have h0 := homRCW_getVert (G := G) hn2
          ⟨fun j => p.getVert ↑j, fun {a b} hab => hmapadj a b hab⟩
          (Nat.zero_le (Fintype.card V))
        change (homRCW hn2 _).1 = v
        have hroot : (homRCW hn2 ⟨fun j => p.getVert ↑j, fun {a b} hab =>
            hmapadj a b hab⟩).1 = p.getVert (0 % Fintype.card V) := rfl
        rw [hroot, Nat.zero_mod, Walk.getVert_zero]
  · -- the unrolled walk of an injective homomorphism has full support
    intro f hf
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hf ⊢
    have hsupp : (homRCW hn2 f).2.1.support.toFinset =
        Finset.image (fun j : Fin (Fintype.card V) => f j) Finset.univ := by
      apply Finset.Subset.antisymm
      · intro x hx
        obtain ⟨i, hxi, hile⟩ := (homRCW hn2 f).2.1.mem_support_iff_exists_getVert.mp
          (List.mem_toFinset.mp hx)
        rw [(homRCW hn2 f).2.2] at hile
        rw [homRCW_getVert hn2 f hile] at hxi
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨_, hxi⟩
      · intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨j, rfl⟩ := hx
        refine List.mem_toFinset.mpr
          ((homRCW hn2 f).2.1.mem_support_iff_exists_getVert.mpr ⟨↑j, ?_, ?_⟩)
        · rw [homRCW_getVert hn2 f (Nat.le_of_lt j.isLt)]
          change f ⟨↑j % Fintype.card V, _⟩ = f j
          congr 1
          exact Fin.ext (Nat.mod_eq_of_lt j.isLt)
        · rw [(homRCW hn2 f).2.2]
          omega
    rw [hsupp, Finset.card_image_of_injective _ hf, Finset.card_univ,
      Fintype.card_fin]
  · -- unrolling is injective on injective homomorphisms
    intro f hf f' hf' heq
    have hgv : ∀ i : ℕ, (homRCW hn2 f).2.1.getVert i = (homRCW hn2 f').2.1.getVert i :=
      fun i => congrArg (fun wp : G.RootedClosedWalk (Fintype.card V) =>
        wp.2.1.getVert i) heq
    apply DFunLike.ext
    intro a
    have h1 := hgv ↑a
    rw [homRCW_getVert hn2 f (Nat.le_of_lt a.isLt),
      homRCW_getVert hn2 f' (Nat.le_of_lt a.isLt)] at h1
    have hmod : (⟨↑a % Fintype.card V,
        Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne _))⟩ : Fin (Fintype.card V)) = a :=
      Fin.ext (Nat.mod_eq_of_lt a.isLt)
    unfold homSeq at h1
    rwa [hmod] at h1

variable {G} {H : SimpleGraph V} [DecidableRel H.Adj]

/-- Conditional constant-term reconstruction from the **Hamiltonian count
alone**: with the proper-support sector discharged by Kelly counting
(`SameDeck.properSupportClosedWalkCount_eq`) and the full-support sector
identified as the Hamiltonian sector
(`fullSupportClosedWalkCount_card_eq_hamiltonianHomCount`), the constant
coefficient of the characteristic polynomial follows from agreement of the
Hamiltonian homomorphism counts. The hypothesis `hham` is exactly Tutte's
theorem (1979) that the number of Hamiltonian cycles is reconstructible. -/
theorem SameDeck.charPoly_coeff_zero_eq_of_hamiltonianHomCount_eq
    (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V)
    (hham : G.hamiltonianHomCount = H.hamiltonianHomCount) :
    (G.charPoly ℤ).coeff 0 = (H.charPoly ℤ).coeff 0 := by
  refine h.charPoly_coeff_zero_eq_of_fullSupport_eq hV ?_
  rw [fullSupportClosedWalkCount_card_eq_hamiltonianHomCount G hV,
    fullSupportClosedWalkCount_card_eq_hamiltonianHomCount H hV, hham]

/-- **Staged target (Tutte 1979).** The number of Hamiltonian cycles — here,
of injective homomorphisms from the `|V|`-cycle — is reconstructible from the
deck. Proving this (via Kocay's disconnected-spanning-subgraph counting,
building on `Reconstruction.Kocay`) closes
`SameDeck.charPoly_coeff_zero_eq` and with it the full characteristic
polynomial. Stated as a `Prop`-valued definition per the project's staged-
target convention. -/
def HamiltonianHomCountReconstructible : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj],
    3 ≤ Fintype.card V → G.SameDeck H →
      G.hamiltonianHomCount = H.hamiltonianHomCount

/-- The **full characteristic polynomial** from the Hamiltonian count alone:
non-constant coefficients are unconditionally reconstructible
(`Spectral.lean`), and the constant term follows from the Hamiltonian
homomorphism counts. -/
theorem SameDeck.charPoly_eq_of_hamiltonianHomCount_eq
    (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V)
    (hham : G.hamiltonianHomCount = H.hamiltonianHomCount) :
    G.charPoly ℤ = H.charPoly ℤ := by
  ext k
  by_cases hk : 1 ≤ k
  · exact h.charPoly_coeff_eq ℤ hk
  · have hk0 : k = 0 := by omega
    subst hk0
    exact h.charPoly_coeff_zero_eq_of_hamiltonianHomCount_eq hV hham

end

/-- **The staged target suffices**: if the Hamiltonian homomorphism count is
deck-reconstructible (Tutte 1979), then same-deck graphs on at least three
vertices have equal characteristic polynomials. This makes the sufficiency
claim of `HamiltonianHomCountReconstructible` a theorem rather than prose:
closing the staged target closes `SameDeck.charPoly_coeff_zero_eq` and the
full Tutte characteristic-polynomial reconstruction. -/
theorem charPoly_eq_of_hamiltonianHomCountReconstructible
    (hrec : HamiltonianHomCountReconstructible)
    {V : Type} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) :
    G.charPoly ℤ = H.charPoly ℤ :=
  h.charPoly_eq_of_hamiltonianHomCount_eq hV (hrec G H hV h)

end SimpleGraph
