import Reconstruction.ConnectedComponents
import Reconstruction.KellyLemma

/-!
# Reconstruction Conjecture — Disconnected Graphs

Kelly (1942) proved that disconnected graphs are reconstructible: if `G` is
disconnected and has the same deck as `H`, then `G ≅ H`.

## Main results

* `SimpleGraph.SameDeck.iso_of_not_connected` — disconnected graphs are reconstructible

## Proof outline

If `G` is disconnected with connected components of sizes `n₁ ≥ n₂ ≥ ⋯ ≥ nₖ`
where `k ≥ 2`:

1. Since `n₂ ≤ n/2 < n`, all components except possibly the largest have
   fewer than `n` vertices.
2. The number of copies of each "small" component can be counted via Kelly's
   Lemma, since these components have strictly fewer vertices than `G`.
3. The largest component is determined as the complement of the union of the
   smaller components in the vertex set.
4. This determines the full multiset of components, so `G ≅ H`.

## References

* Kelly, P. J. (1942). "On isometric transformations".
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- **Disconnected graphs are reconstructible** (Kelly 1942).

If `G` is disconnected (not connected) and has the same deck as `H` on ≥ 3
vertices, then `G ≅ H`. The proof proceeds by identifying all connected
components via Kelly's Lemma: components with fewer than `n` vertices are
counted directly, and the largest component is determined as the remainder. -/
theorem SameDeck.iso_of_not_connected (h : G.SameDeck H) (hV : 3 ≤ Fintype.card V)
    (hdisc : ¬G.Connected) : Nonempty (G ≃g H) := by
  -- TODO: Kelly's 1942 proof that disconnected graphs are reconstructible.
  -- If G has components of sizes n₁ ≥ n₂ ≥ ⋯ ≥ nₖ with k ≥ 2, then n₂ ≤ n/2 < n,
  -- so all components except possibly the largest have < n vertices and can be
  -- identified via Kelly's Lemma. The largest component is the remainder.
  -- This is a full reconstruction result (producing G ≃g H), not just an invariant
  -- equality, which makes it substantially harder to formalize than the other sorry's.
  sorry

end SimpleGraph
