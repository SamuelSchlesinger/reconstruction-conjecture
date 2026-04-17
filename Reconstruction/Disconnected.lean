import Reconstruction.ConnectedComponents
import Reconstruction.KellyLemma

/-!
# Reconstruction Conjecture — Disconnected Graphs

Kelly (1942) proved that disconnected graphs are reconstructible: if `G` is
disconnected and has the same deck as `H`, then `G ≅ H`.

## Main results

* `SimpleGraph.isoSigmaComponents` — every graph is isomorphic to the disjoint
  union of its connected components (via a Sigma type).
* `SimpleGraph.SameDeck.iso_of_not_connected` — disconnected graphs are
  reconstructible (**currently a `sorry`**, see below).

## Proof outline for the main theorem

If `G` is disconnected with connected components of sizes `n₁ ≥ n₂ ≥ ⋯ ≥ nₖ`
where `k ≥ 2`:

1. Since `k ≥ 2`, every component has size `≤ n - 1 < n`, so Kelly's Lemma
   applies to **every** component of `G`.
2. One can therefore count, for each iso-class `[F]` of connected graphs on
   `< n` vertices, the number of induced copies of `F` in `G`.
3. The number of components of `G` isomorphic to each such `F` is then
   recoverable by induction on component size: the smallest components are
   counted directly (e.g. isolated vertices correspond to degree-0 vertices);
   larger component classes are obtained by subtracting contributions of
   induced `F`-copies lying inside larger components (processed in order).
4. Since `G` and `H` have matching component multisets, one constructs a
   bijection between `G.ConnectedComponent` and `H.ConnectedComponent`
   respecting iso-class, then assembles a global iso `G ≃g H` by combining
   per-component isos through the `Sigma` decomposition
   (`isoSigmaComponents` below).

## Current status

This file provides the `Sigma`-decomposition infrastructure
(`componentSigmaGraph`, `isoSigmaComponents`) which is the "assembly" piece of
Step 4. The multiset-reconstruction part of Steps 2–3 (which is the bulk of
Kelly's 1942 argument) remains a `sorry` in `SameDeck.iso_of_not_connected`.

## References

* Kelly, P. J. (1942). "On isometric transformations".
-/

namespace SimpleGraph

variable {V : Type*}

/-! ### Sigma decomposition of a graph by connected components

Given `G : SimpleGraph V`, we build an isomorphism `G ≃g componentSigmaGraph G`
where the right-hand side lives on `Σ c : G.ConnectedComponent, c.supp` and
places an edge between `⟨c, v⟩` and `⟨d, w⟩` iff `c = d` and `G.Adj v w`.

This is the natural "disjoint-union" description of `G` in terms of its
connected components; it is the structural step needed when assembling a global
isomorphism out of per-component isomorphisms. -/

/-- The disjoint-union of the connected components of `G`, as a graph on the
Sigma type `Σ c : G.ConnectedComponent, c.supp`. Two vertices are adjacent iff
they lie in the same component and are adjacent in `G`. -/
def componentSigmaGraph (G : SimpleGraph V) :
    SimpleGraph (Σ c : G.ConnectedComponent, (c : Set V)) where
  Adj p q := p.1 = q.1 ∧ G.Adj p.2.val q.2.val
  symm := by
    rintro ⟨c, v⟩ ⟨d, w⟩ ⟨hcd, hadj⟩
    exact ⟨hcd.symm, hadj.symm⟩
  loopless := ⟨by
    rintro ⟨c, v⟩ ⟨_, h⟩
    exact h.ne rfl⟩

@[simp] lemma componentSigmaGraph_adj (G : SimpleGraph V)
    (p q : Σ c : G.ConnectedComponent, (c : Set V)) :
    (componentSigmaGraph G).Adj p q ↔ p.1 = q.1 ∧ G.Adj p.2.val q.2.val :=
  Iff.rfl

/-- The forward map of the Sigma decomposition: project the second coordinate. -/
private def sigmaToV (G : SimpleGraph V) :
    (Σ c : G.ConnectedComponent, (c : Set V)) → V := fun p => p.2.val

/-- The backward map of the Sigma decomposition: pair a vertex with its
component. -/
private def vToSigma (G : SimpleGraph V) :
    V → Σ c : G.ConnectedComponent, (c : Set V) :=
  fun v => ⟨G.connectedComponentMk v,
           ⟨v, ConnectedComponent.connectedComponentMk_mem⟩⟩

private lemma sigmaToV_vToSigma (G : SimpleGraph V) (v : V) :
    sigmaToV G (vToSigma G v) = v := rfl

private lemma vToSigma_sigmaToV (G : SimpleGraph V)
    (p : Σ c : G.ConnectedComponent, (c : Set V)) :
    vToSigma G (sigmaToV G p) = p := by
  rcases p with ⟨c, v, hv⟩
  have hv' : G.connectedComponentMk v = c :=
    (ConnectedComponent.mem_supp_iff c v).mp hv
  -- Both sides are pairs; equate field by field.
  obtain rfl := hv'
  rfl

/-- The vertex equivalence underlying the Sigma decomposition. -/
def componentSigmaEquiv (G : SimpleGraph V) :
    V ≃ Σ c : G.ConnectedComponent, (c : Set V) where
  toFun := vToSigma G
  invFun := sigmaToV G
  left_inv := sigmaToV_vToSigma G
  right_inv := vToSigma_sigmaToV G

@[simp] lemma componentSigmaEquiv_apply (G : SimpleGraph V) (v : V) :
    componentSigmaEquiv G v =
      ⟨G.connectedComponentMk v,
        ⟨v, ConnectedComponent.connectedComponentMk_mem⟩⟩ := rfl

@[simp] lemma componentSigmaEquiv_symm_apply (G : SimpleGraph V)
    (p : Σ c : G.ConnectedComponent, (c : Set V)) :
    (componentSigmaEquiv G).symm p = p.2.val := rfl

/-- **Sigma decomposition of a graph.** Every graph is isomorphic to the
disjoint union of its connected components (presented as a Sigma-indexed
collection of vertex sets with the induced adjacency). -/
def isoSigmaComponents (G : SimpleGraph V) :
    G ≃g componentSigmaGraph G where
  toEquiv := componentSigmaEquiv G
  map_rel_iff' := by
    intro v w
    simp only [componentSigmaGraph_adj, componentSigmaEquiv_apply]
    refine ⟨fun h => h.2, fun hadj => ?_⟩
    refine ⟨?_, hadj⟩
    exact ConnectedComponent.connectedComponentMk_eq_of_adj hadj

/-! ### Main theorem (currently `sorry`) -/

variable [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- **Disconnected graphs are reconstructible** (Kelly 1942).

If `G` is disconnected (not connected) and has the same deck as `H` on ≥ 3
vertices, then `G ≅ H`.

**Status**: not yet proved. The proof requires a non-trivial induction to
recover the full component multiset from the subgraph counts given by
Kelly's Lemma (`SameDeck.subgraphCount_eq`), after which the assembly step
uses `isoSigmaComponents` above. -/
theorem SameDeck.iso_of_not_connected (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V)
    (hdisc : ¬G.Connected) : Nonempty (G ≃g H) := by
  -- See the module docstring for the full proof outline.
  -- The missing core: reconstruct, for every iso-class `[F]` of connected
  -- graphs on `< |V|` vertices, the number of components of `G` iso to `F`.
  -- Kelly's Lemma (`h.subgraphCount_eq`) gives equality of induced-subgraph
  -- counts between `G` and `H`; the induction on component size turns these
  -- into equal *component* counts. Having matched up components, the final
  -- step is the assembly: `G ≃g Σ c, c.toSimpleGraph ≃g Σ d, d.toSimpleGraph ≃g H`
  -- using `isoSigmaComponents`.
  sorry

end SimpleGraph
