import Reconstruction.Dirac
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Chordal graphs are perfect (`χ ≤ ω`)

Greedy colouring along a simplicial elimination: a finite chordal graph with no
`(k+1)`-clique is `k`-colourable. Combined with the trivial `ω ≤ χ`
(`IsClique.card_le_of_colorable`), this is the perfect-graph identity `χ = ω` for
chordal graphs (Berge / Hajnal–Surányi / Dirac).

## Main result

* `SimpleGraph.chordal_colorable` — a finite chordal `G` with `G.CliqueFree (k+1)`
  is `G.Colorable k`.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

open Finset

universe u

/-- Inductive core: a finite chordal graph with no `(k+1)`-clique is
`k`-colourable. Strong induction on `|V|`, peeling a simplicial vertex `v`
(`diracSimplicial`): its neighbourhood is a clique of size `< k`, so after
colouring `G − v` it has a free colour. -/
theorem chordal_colorable_aux {k : ℕ} : ∀ (n : ℕ) (W : Type u) [Fintype W] (H : SimpleGraph W),
    Fintype.card W ≤ n → H.IsChordal → H.CliqueFree (k + 1) → H.Colorable k := by
  classical
  intro n
  induction n with
  | zero =>
    intro W _ H hcard _ _
    haveI : IsEmpty W := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
    exact Colorable.of_isEmpty k
  | succ n ih =>
    intro W _ H hcard hchord hcf
    rcases isEmpty_or_nonempty W with _ | hNE
    · exact Colorable.of_isEmpty k
    · -- a simplicial vertex `v`
      obtain ⟨v, hvsimp⟩ := diracSimplicial H hchord hNE
      -- recurse on `H − v`
      have hlt : Fintype.card ↥{w : W | w ≠ v} < Fintype.card W :=
        Fintype.card_subtype_lt (x := v) (by simp)
      obtain ⟨C'⟩ := ih ↥{w : W | w ≠ v} (H.induce {w | w ≠ v}) (by omega)
        (hchord.induce _) (hcf.comap (Embedding.induce _))
      -- `v`'s neighbourhood is a clique of size `< k`
      have hclq : H.IsClique (insert v (H.neighborFinset v) : Finset W) := by
        rw [coe_insert, coe_neighborFinset]
        exact hvsimp.insert fun b hb _ => hb
      have hbound : (H.neighborFinset v).card < k := by
        by_contra hge
        push_neg at hge
        have hcard' : k + 1 ≤ (insert v (H.neighborFinset v)).card := by
          rw [card_insert_of_notMem (by simp)]; omega
        obtain ⟨t, hts, ht⟩ := exists_subset_card_eq hcard'
        exact (⟨hclq.subset hts, ht⟩ : H.IsNClique (k + 1) t).not_cliqueFree hcf
      -- the colours used by `v`'s neighbours, and a free colour `c₀`
      set used : Finset (Fin k) :=
        (H.neighborFinset v).attach.image fun u => C' ⟨u.1, fun h => absurd (h ▸ u.2) (by simp)⟩
        with hused
      have hused_lt : used.card < (univ : Finset (Fin k)).card := by
        rw [card_univ, Fintype.card_fin]
        calc used.card ≤ (H.neighborFinset v).attach.card := card_image_le
          _ = (H.neighborFinset v).card := card_attach
          _ < k := hbound
      obtain ⟨c₀, hc₀⟩ : ∃ c, c ∉ used := by
        by_contra h
        push_neg at h
        rw [Finset.eq_univ_iff_forall.mpr h] at hused_lt
        exact lt_irrefl _ hused_lt
      -- extend the colouring
      refine ⟨Coloring.mk (fun w => if h : w = v then c₀ else C' ⟨w, h⟩) ?_⟩
      intro a b hab
      by_cases ha : a = v <;> by_cases hb : b = v
      · exact absurd (ha ▸ hb ▸ hab) (H.irrefl)
      · -- `a = v`, `b ≠ v`: `b` is a neighbour, its colour is in `used`, `c₀` isn't
        simp only [dif_pos ha, dif_neg hb]
        have hbmem : b ∈ H.neighborFinset v := by simp only [mem_neighborFinset]; exact ha ▸ hab
        refine fun hc => hc₀ ?_
        rw [hused, hc]
        exact mem_image.mpr ⟨⟨b, hbmem⟩, mem_attach _ _, rfl⟩
      · simp only [dif_neg ha, dif_pos hb]
        have hamem : a ∈ H.neighborFinset v := by
          simp only [mem_neighborFinset]; exact hb ▸ hab.symm
        refine fun hc => hc₀ ?_
        rw [hused, ← hc]
        exact mem_image.mpr ⟨⟨a, hamem⟩, mem_attach _ _, rfl⟩
      · simp only [dif_neg ha, dif_neg hb]
        exact C'.valid hab

/-- **Chordal graphs are perfect (`χ ≤ ω`).** A finite chordal graph with no
`(k+1)`-clique is `k`-colourable. With `IsClique.card_le_of_colorable` (the
trivial `ω ≤ χ`) this gives `χ = ω` for chordal graphs. -/
theorem chordal_colorable [Finite V] {k : ℕ} (hchord : G.IsChordal)
    (hcf : G.CliqueFree (k + 1)) : G.Colorable k := by
  haveI := Fintype.ofFinite V
  exact chordal_colorable_aux (Fintype.card V) V G le_rfl hchord hcf

end SimpleGraph
