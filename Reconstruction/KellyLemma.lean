import Reconstruction.Defs
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Kelly's Lemma (Subgraph Counting)

Kelly's Lemma is the central counting tool in reconstruction theory.
It states that for any graph F with fewer vertices than G, the number
of induced copies of F in G is reconstructible from the deck.

## Main definitions

* `SimpleGraph.copyFinset` — the set of k-element subsets S ⊆ V(G)
  whose induced subgraph G[S] is isomorphic to F
* `SimpleGraph.subgraphCount` — `|copyFinset F G|`, the number of
  such copies

## Main results

* `SimpleGraph.subgraphCount_sum` — the double-counting identity:
  `(n - k) * s(F, G) = ∑ v, s(F, G - v)`
* `SimpleGraph.SameDeck.subgraphCount_eq` — if `deck(G) = deck(H)`
  and `|V(F)| < |V(G)|`, then `s(F, G) = s(F, H)`

## References

* Kelly, P. J. (1942). "On isometric transformations".
-/

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical

variable {W : Type*} [Fintype W]
variable {V : Type*} [Fintype V]

/-- The set of `Fintype.card W`-element subsets `S ⊆ V` whose induced
subgraph `G[S]` is isomorphic to `F`. -/
def copyFinset (F : SimpleGraph W) (G : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ.powersetCard (Fintype.card W)).filter
    fun S => Nonempty (G.induce (↑S : Set V) ≃g F)

/-- The number of induced copies of `F` in `G`: how many `k`-element
subsets `S ⊆ V(G)` satisfy `G[S] ≅ F`. -/
def subgraphCount (F : SimpleGraph W) (G : SimpleGraph V) : ℕ :=
  (F.copyFinset G).card

theorem mem_copyFinset (F : SimpleGraph W) (G : SimpleGraph V) (S : Finset V) :
    S ∈ F.copyFinset G ↔
      S.card = Fintype.card W ∧ Nonempty (G.induce (↑S : Set V) ≃g F) := by
  simp [copyFinset, Finset.mem_filter, Finset.mem_powersetCard]

/-- Every set in `copyFinset F G` has cardinality `Fintype.card W`. -/
theorem copyFinset_card (F : SimpleGraph W) (G : SimpleGraph V)
    {S : Finset V} (hS : S ∈ F.copyFinset G) :
    S.card = Fintype.card W :=
  ((F.mem_copyFinset G S).mp hS).1

section IsoInvariance

variable {V₁ : Type*} [Fintype V₁]
variable {V₂ : Type*} [Fintype V₂]
variable {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}

/-- A graph isomorphism restricts to an isomorphism of induced subgraphs:
if `φ : G₁ ≃g G₂` and `S : Finset V₁`, then `G₁[S] ≃g G₂[φ(S)]`. -/
private def induceMapIso (φ : G₁ ≃g G₂) (S : Finset V₁) :
    G₁.induce (↑S : Set V₁) ≃g G₂.induce (↑(S.map φ.toEquiv.toEmbedding) : Set V₂) where
  toEquiv := Equiv.subtypeEquiv φ.toEquiv (fun v => by simp)
  map_rel_iff' {a b} := φ.map_rel_iff

/-- `subgraphCount` is invariant under graph isomorphism. -/
theorem subgraphCount_eq_of_iso (F : SimpleGraph W) (φ : G₁ ≃g G₂) :
    F.subgraphCount G₁ = F.subgraphCount G₂ := by
  unfold subgraphCount
  refine Finset.card_bij'
    (fun S _ => S.map φ.toEquiv.toEmbedding)
    (fun T _ => T.map φ.symm.toEquiv.toEmbedding)
    (fun S hS => ?_) (fun T hT => ?_) (fun S _ => ?_) (fun T _ => ?_)
  · -- Forward: copyFinset F G₁ → copyFinset F G₂
    have hS' := (mem_copyFinset F G₁ S).mp hS
    exact (mem_copyFinset F G₂ _).mpr
      ⟨by rw [Finset.card_map]; exact hS'.1,
       hS'.2.map ((induceMapIso φ S).symm.trans ·)⟩
  · -- Backward: copyFinset F G₂ → copyFinset F G₁
    have hT' := (mem_copyFinset F G₂ T).mp hT
    exact (mem_copyFinset F G₁ _).mpr
      ⟨by rw [Finset.card_map]; exact hT'.1,
       hT'.2.map ((induceMapIso φ.symm T).symm.trans ·)⟩
  · -- Left inverse
    simp only [Finset.map_map]
    convert Finset.map_refl (s := S) using 2
    ext v; simp
  · -- Right inverse
    simp only [Finset.map_map]
    convert Finset.map_refl (s := T) using 2
    ext v; simp

end IsoInvariance

section BridgeLemma

variable [DecidableEq V]
variable (F : SimpleGraph W) (G : SimpleGraph V)

/-- Bridge lemma: copies of `F` in `G - v` biject with copies of `F` in `G`
that avoid `v`. -/
theorem subgraphCount_deleteVert (v : V) :
    F.subgraphCount (G.deleteVert v) =
    ((F.copyFinset G).filter (fun S => v ∉ S)).card := by
  unfold subgraphCount
  refine Finset.card_bij'
    (fun T _ => T.map (Function.Embedding.subtype _))
    (fun S _ => S.subtype (· ≠ v))
    (fun T hT => ?fwd) (fun S hS => ?bwd) (fun T hT => ?linv) (fun S hS => ?rinv)
  case fwd =>
    have hT' := (mem_copyFinset F (G.deleteVert v) T).mp hT
    rw [Finset.mem_filter]
    refine ⟨(mem_copyFinset F G _).mpr ⟨by rw [Finset.card_map]; exact hT'.1, ?_⟩,
            Finset.notMem_map_subtype_of_not_property T (not_not.mpr rfl)⟩
    -- Need: G.induce ↑(T.map ...) ≃g F
    -- Have: (G.deleteVert v).induce ↑T ≃g F (from iso)
    exact hT'.2.map fun iso => by
      let fwd : (↑(T.map (Function.Embedding.subtype _)) : Set V) →
                (↑T : Set {w : V // w ≠ v}) :=
        fun x => ⟨⟨x.1, Finset.property_of_mem_map_subtype T (Finset.mem_coe.mp x.2)⟩,
          by have hmem := Finset.mem_coe.mp x.2
             rw [Finset.mem_map] at hmem
             obtain ⟨⟨w, hw⟩, ht, heq⟩ := hmem
             simp only [ne_eq] at heq
             subst heq
             exact ht⟩
      let bwd : (↑T : Set {w : V // w ≠ v}) →
                (↑(T.map (Function.Embedding.subtype _)) : Set V) :=
        fun y => ⟨y.1.1, Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨y.1, y.2, rfl⟩)⟩
      have hleft : Function.LeftInverse bwd fwd := fun x => by ext; rfl
      have hright : Function.RightInverse bwd fwd := fun y => by ext; rfl
      exact ({ toEquiv := ⟨fwd, bwd, hleft, hright⟩, map_rel_iff' := Iff.rfl } :
        G.induce (↑(T.map (Function.Embedding.subtype _))) ≃g
          (G.deleteVert v).induce (↑T)).trans iso
  case bwd =>
    rw [Finset.mem_filter] at hS
    obtain ⟨hS_mem, hv⟩ := hS
    have hS' := (mem_copyFinset F G S).mp hS_mem
    rw [mem_copyFinset]
    have hfilt : S.filter (· ≠ v) = S :=
      Finset.filter_true_of_mem (fun x hx h => hv (h ▸ hx))
    refine ⟨by rw [Finset.card_subtype, hfilt]; exact hS'.1, ?_⟩
    -- Need: (G.deleteVert v).induce ↑(S.subtype (· ≠ v)) ≃g F
    -- Have: G.induce ↑S ≃g F (from iso)
    exact hS'.2.map fun iso => by
      let fwd : (↑(S.subtype (· ≠ v)) : Set {w : V // w ≠ v}) → (↑S : Set V) :=
        fun x => ⟨x.1.1, Finset.mem_coe.mpr (Finset.mem_subtype.mp x.2)⟩
      let bwd : (↑S : Set V) → (↑(S.subtype (· ≠ v)) : Set {w : V // w ≠ v}) :=
        fun x => ⟨⟨x.1, fun h => hv (h ▸ Finset.mem_coe.mp x.2)⟩,
                   Finset.mem_coe.mpr (Finset.mem_subtype.mpr (Finset.mem_coe.mp x.2))⟩
      have hleft : Function.LeftInverse bwd fwd := fun x => by ext; rfl
      have hright : Function.RightInverse bwd fwd := fun x => by ext; rfl
      exact ({ toEquiv := ⟨fwd, bwd, hleft, hright⟩, map_rel_iff' := Iff.rfl } :
        (G.deleteVert v).induce (↑(S.subtype (· ≠ v))) ≃g G.induce (↑S)).trans iso
  case linv =>
    ext ⟨w, hw⟩
    simp only [Finset.mem_subtype, Finset.mem_map, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨⟨w', hw'⟩, ht, heq⟩
      cases heq
      exact ht
    · intro h
      exact ⟨⟨w, hw⟩, h, rfl⟩
  case rinv =>
    change (S.subtype (· ≠ v)).map (Function.Embedding.subtype _) = S
    rw [Finset.subtype_map]
    exact Finset.filter_true_of_mem (fun x hx h =>
      (Finset.mem_filter.mp hS).2 (h ▸ hx))

end BridgeLemma

section DoubleCounting

variable (F : SimpleGraph W) (G : SimpleGraph V)

/-- **Kelly's counting identity (double-counting).** For any graph `F` on `k`
vertices and `G` on `n ≥ k` vertices:
`(n - k) * s(F, G) = ∑ v, s(F, G - v)`. -/
theorem subgraphCount_sum [DecidableEq V]
    (_hcard : Fintype.card W ≤ Fintype.card V) :
    (Fintype.card V - Fintype.card W) * F.subgraphCount G =
    ∑ v : V, F.subgraphCount (G.deleteVert v) := by
  -- Step 1: Rewrite RHS using the bridge lemma
  simp_rw [subgraphCount_deleteVert]
  -- Step 2: Swap the sum (double-counting via bipartite graph)
  -- ∑ v, |{S ∈ copyFinset F G | v ∉ S}| = ∑ S ∈ copyFinset F G, |{v | v ∉ S}|
  have swap : ∑ v : V, ((F.copyFinset G).filter (fun S => v ∉ S)).card =
      ∑ S ∈ F.copyFinset G, (Finset.univ.filter (fun v : V => v ∉ S)).card :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun v S => v ∉ S)
  rw [swap]
  -- Step 3: Each S ∈ copyFinset has |{v | v ∉ S}| = n - k
  have each_eq : ∀ S ∈ F.copyFinset G,
      (Finset.univ.filter (fun v : V => v ∉ S)).card =
      Fintype.card V - Fintype.card W := by
    intro S hS
    have hScard := copyFinset_card F G hS
    have h1 : Finset.univ.filter (fun v : V => v ∉ S) = Finset.univ \ S := by
      ext v; simp
    rw [h1, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hScard]
  unfold subgraphCount
  rw [Finset.sum_congr rfl each_eq, Finset.sum_const, smul_eq_mul, mul_comm]

end DoubleCounting

section Reconstructibility

variable {G H : SimpleGraph V}

/-- **Kelly's Lemma (reconstructibility corollary).** If two graphs have
the same deck and `|V(F)| < |V(G)|`, then they have the same number
of induced copies of `F`. -/
theorem SameDeck.subgraphCount_eq
    (h : G.SameDeck H) (F : SimpleGraph W)
    (hcard : Fintype.card W < Fintype.card V) :
    F.subgraphCount G = F.subgraphCount H := by
  obtain ⟨σ, hσ⟩ := h
  have hiso : ∀ v, F.subgraphCount (G.deleteVert v) =
      F.subgraphCount (H.deleteVert (σ v)) :=
    fun v => subgraphCount_eq_of_iso F (hσ v).some
  have hsum : ∑ v : V, F.subgraphCount (G.deleteVert v) =
      ∑ v : V, F.subgraphCount (H.deleteVert v) := by
    calc ∑ v, F.subgraphCount (G.deleteVert v)
        = ∑ v, F.subgraphCount (H.deleteVert (σ v)) :=
          Finset.sum_congr rfl fun v _ => hiso v
      _ = ∑ v, F.subgraphCount (H.deleteVert v) :=
          σ.sum_comp (fun w => F.subgraphCount (H.deleteVert w))
  have hle : Fintype.card W ≤ Fintype.card V := Nat.le_of_lt hcard
  have hmulG := F.subgraphCount_sum G hle
  have hmulH := F.subgraphCount_sum H hle
  have hmul : (Fintype.card V - Fintype.card W) * F.subgraphCount G =
      (Fintype.card V - Fintype.card W) * F.subgraphCount H := by
    rw [hmulG, hsum, ← hmulH]
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < Fintype.card V - Fintype.card W) hmul

end Reconstructibility

end

end SimpleGraph
