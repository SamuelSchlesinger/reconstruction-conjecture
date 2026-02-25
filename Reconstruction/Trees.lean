import Reconstruction.ConnectedComponents
import Reconstruction.EdgeCount
import Reconstruction.DegreeSequence
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Reconstruction Conjecture — Trees

Being a tree is a reconstructible graph property: if `G` is a tree and has the
same deck as `H` (on ≥ 3 vertices), then `H` is also a tree.

## Main results

* `SimpleGraph.SameDeck.isTree` — tree property is reconstructible

## Proof outline

1. Trees have `|E| = |V| - 1` edges (`IsTree.card_edgeFinset`).
2. Edge count is reconstructible (`SameDeck.card_edgeFinset_eq`), so `|E(H)| = |V| - 1`.
3. Trees are connected; connectivity is reconstructible (`SameDeck.connected`).
4. A connected graph with `|V| - 1` edges is a tree
   (`isTree_iff_connected_and_card`).

## References

* Kelly, P. J. (1942). "On isometric transformations".
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- **The tree property is reconstructible.** If `G` is a tree and has the
same deck as `H` (on ≥ 3 vertices), then `H` is also a tree.

The proof combines three reconstructible invariants:
- **Edge count:** `|E(G)| = |E(H)|`, and trees have `|E| + 1 = |V|`
- **Connectivity:** trees are connected, and connectivity is reconstructible
- **Characterization:** a connected graph with `|V| - 1` edges is a tree -/
theorem SameDeck.isTree (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V)
    (htree : G.IsTree) : H.IsTree := by
  -- Step 1: H is connected (connectivity is reconstructible)
  have hconn : H.Connected := h.connected hV htree.isConnected
  -- Step 2: H has the same number of edges as G
  have hedge : H.edgeFinset.card = G.edgeFinset.card :=
    (h.card_edgeFinset_eq hV).symm
  -- Step 3: G has |V| - 1 edges (it's a tree)
  have hG_edges : G.edgeFinset.card + 1 = Fintype.card V :=
    htree.card_edgeFinset
  -- Step 4: So H has |V| - 1 edges
  have hH_edges : H.edgeFinset.card + 1 = Fintype.card V := by omega
  -- Step 5: Connected + |V| - 1 edges = tree
  rw [isTree_iff_connected_and_card]
  refine ⟨hconn, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← edgeFinset_card]
  exact hH_edges

end SimpleGraph
