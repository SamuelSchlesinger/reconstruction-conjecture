import Reconstruction.KellyLemma
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Edge Count via Kelly's Lemma

Edge count is a special case of Kelly's Lemma: the number of induced copies
of `K₂` (the complete graph on 2 vertices) in `G` equals `|E(G)|`.

This connects the ad-hoc edge count proof in `EdgeCount.lean` to the general
subgraph counting framework in `KellyLemma.lean`.

## Main results

* `SimpleGraph.subgraphCount_completeGraph_two` — `s(K₂, G) = |E(G)|`
* `SimpleGraph.SameDeck.card_edgeFinset_eq'` — edge count reconstructibility
  via Kelly's Lemma
-/

namespace SimpleGraph

noncomputable section

set_option linter.style.openClassical false
open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Sym2.toFinset` is injective: unordered pairs are determined by their
underlying set of elements. -/
private theorem sym2_toFinset_injective :
    Function.Injective (Sym2.toFinset : Sym2 V → Finset V) :=
  fun p q h => Sym2.ext fun x => by rw [← Sym2.mem_toFinset, h, Sym2.mem_toFinset]

/-- If `u ≠ v` and `G.Adj u v`, then the induced subgraph `G[{u,v}]` is
isomorphic to `K₂ = completeGraph (Fin 2)`. -/
private theorem induce_pair_iso (G : SimpleGraph V) {u v : V}
    (hne : u ≠ v) (hadj : G.Adj u v) :
    Nonempty (G.induce (↑({u, v} : Finset V) : Set V) ≃g completeGraph (Fin 2)) := by
  -- A 2-element set with all pairs adjacent is K₂.
  -- The induced subgraph has vertex type {w // w ∈ {u, v}} and adjacency G.Adj.
  -- Since u ≠ v and G.Adj u v, this is exactly K₂.
  have hu : u ∈ (↑({u, v} : Finset V) : Set V) := by simp
  have hv : v ∈ (↑({u, v} : Finset V) : Set V) := by simp
  -- Build the equivalence: {w // w ∈ {u,v}} ≃ Fin 2
  -- Map u ↦ 0, v ↦ 1
  let e : (↑({u, v} : Finset V) : Set V) ≃ Fin 2 := by
    refine (Fintype.equivOfCardEq ?_)
    simp [Finset.card_pair hne]
  refine ⟨⟨e, fun {a b} => ?_⟩⟩
  -- Show adjacency is preserved
  -- After unfolding, we need: G.Adj a.1 b.1 ↔ (completeGraph (Fin 2)).Adj (e a) (e b)
  -- i.e., G.Adj a.1 b.1 ↔ e a ≠ e b
  simp only [completeGraph, top_adj, ne_eq, comap_adj, Function.Embedding.subtype_apply]
  have ha := a.2; have hb := b.2
  simp only [Finset.coe_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  constructor
  · -- e a ≠ e b → G.Adj a.val b.val
    intro hdist
    have hab : a.val ≠ b.val := fun h => hdist (congr_arg e (Subtype.ext h))
    cases ha with
    | inl ha => cases hb with
      | inl hb => exact absurd (ha.trans hb.symm) hab
      | inr hb => rw [ha, hb]; exact hadj
    | inr ha => cases hb with
      | inl hb => rw [ha, hb]; exact hadj.symm
      | inr hb => exact absurd (ha.trans hb.symm) hab
  · -- G.Adj a.val b.val → e a ≠ e b
    intro hadj' heq
    exact G.ne_of_adj hadj' (congr_arg Subtype.val (e.injective heq))

/-- If `G[{u,v}] ≅ K₂` and `u ≠ v`, then `G.Adj u v`. -/
private theorem adj_of_induce_pair_iso (G : SimpleGraph V) {u v : V}
    (hne : u ≠ v)
    (hiso : Nonempty (G.induce (↑({u, v} : Finset V) : Set V) ≃g
      completeGraph (Fin 2))) :
    G.Adj u v := by
  obtain ⟨φ⟩ := hiso
  have hu : u ∈ (↑({u, v} : Finset V) : Set V) := by simp
  have hv : v ∈ (↑({u, v} : Finset V) : Set V) := by simp
  -- φ maps ⟨u, _⟩ and ⟨v, _⟩ to distinct elements of Fin 2
  have hdist : φ ⟨u, hu⟩ ≠ φ ⟨v, hv⟩ :=
    fun h => hne (congr_arg Subtype.val (φ.injective h))
  -- In completeGraph (Fin 2), distinct → adjacent, pull back through the iso
  have hadj_k2 : (completeGraph (Fin 2)).Adj (φ ⟨u, hu⟩) (φ ⟨v, hv⟩) :=
    (top_adj _ _).mpr hdist
  exact φ.map_rel_iff'.mp hadj_k2

/-- The number of induced copies of `K₂` in `G` equals the number of edges of `G`.

A 2-element subset `S ⊆ V` satisfies `G[S] ≅ K₂` if and only if the two
vertices in `S` are adjacent in `G`. -/
theorem subgraphCount_completeGraph_two (G : SimpleGraph V) :
    (completeGraph (Fin 2)).subgraphCount G = G.edgeFinset.card := by
  unfold subgraphCount
  -- Show copyFinset K₂ G = G.edgeFinset.image Sym2.toFinset, then use injectivity
  suffices h : (completeGraph (Fin 2)).copyFinset G = G.edgeFinset.image Sym2.toFinset by
    rw [h, Finset.card_image_of_injective _ sym2_toFinset_injective]
  ext S
  rw [mem_copyFinset, Finset.mem_image, Fintype.card_fin]
  constructor
  · -- S ∈ copyFinset → S = e.toFinset for some edge e
    rintro ⟨hcard, hiso⟩
    obtain ⟨u, v, hne, rfl⟩ := Finset.card_eq_two.mp hcard
    exact ⟨s(u, v), mem_edgeFinset.mpr (adj_of_induce_pair_iso G hne hiso),
           Sym2.toFinset_mk_eq⟩
  · -- S = e.toFinset for some edge e → S ∈ copyFinset
    rintro ⟨e, he, rfl⟩
    rw [mem_edgeFinset] at he
    -- Case-split on e = s(u, v)
    induction e with
    | h u v =>
      rw [Sym2.toFinset_mk_eq]
      exact ⟨Finset.card_pair (G.ne_of_adj he),
             induce_pair_iso G (G.ne_of_adj he) he⟩

/-- **Edge count is reconstructible (via Kelly's Lemma).** If `|V| ≥ 3` and two
graphs have the same deck, they have the same number of edges.

This is a direct corollary: `|E(G)| = s(K₂, G)`, and Kelly's Lemma gives
`s(K₂, G) = s(K₂, H)` since `|V(K₂)| = 2 < 3 ≤ |V|`. -/
theorem SameDeck.card_edgeFinset_eq' {G H : SimpleGraph V}
    (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V) :
    G.edgeFinset.card = H.edgeFinset.card := by
  rw [← subgraphCount_completeGraph_two G, ← subgraphCount_completeGraph_two H]
  exact h.subgraphCount_eq (completeGraph (Fin 2)) (by rw [Fintype.card_fin]; omega)

end

end SimpleGraph
