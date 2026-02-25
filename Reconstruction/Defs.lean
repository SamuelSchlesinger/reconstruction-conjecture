import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Reconstruction Conjecture — Core Definitions

Definitions for the Reconstruction Conjecture (Kelly 1942, Ulam 1960):
every simple graph on ≥ 3 vertices is determined up to isomorphism by
its **deck** — the multiset of vertex-deleted subgraphs.

## Main definitions

* `SimpleGraph.deleteVert` — delete a single vertex from a graph
* `SimpleGraph.SameDeck` — two graphs have the same deck (via a
  bijection matching vertex-deleted subgraphs up to isomorphism)
-/

variable {V : Type*}

/-- Delete a single vertex from a graph, yielding an induced subgraph
on the remaining vertices. Made `reducible` so that typeclass instances
(e.g. `DecidableRel`, `Fintype edgeSet`) propagate through `induce`/`comap`. -/
abbrev SimpleGraph.deleteVert (G : SimpleGraph V) (v : V) : SimpleGraph {w : V // w ≠ v} :=
  G.induce {w | w ≠ v}

/-- Two graphs have the **same deck** if there is a bijection of vertices
matching corresponding vertex-deleted subgraphs up to isomorphism. -/
def SimpleGraph.SameDeck (G H : SimpleGraph V) : Prop :=
  ∃ σ : V ≃ V, ∀ v : V,
    Nonempty (G.deleteVert v ≃g H.deleteVert (σ v))
