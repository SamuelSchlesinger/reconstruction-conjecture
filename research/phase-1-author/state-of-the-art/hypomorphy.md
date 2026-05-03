# Hypomorphy and the Deck

This note disentangles three closely related but formally distinct
notions that all show up around the Reconstruction Conjecture:

1. **The deck** `D(G)` — the multiset of isomorphism classes of
   vertex-deleted subgraphs.
2. **Deck-isomorphism** (a.k.a. card-isomorphism) — `D(G) = D(H)` as
   multisets.
3. **Hypomorphy** — there is a specific bijection `f : V(G) → V(H)` with
   `G - v ≅ H - f(v)` for all `v`.

## Definitions

Let `G = (V, E)` be a finite simple graph with `|V| = n`.

**Cards.** For `v ∈ V`, the **card at `v`** is the isomorphism class
`[G - v]` of the subgraph induced on `V \ {v}`.

**Deck.** `D(G) := ⟦ [G - v] : v ∈ V ⟧` as a multiset (equivalently, a
function `Graphs/≅ → ℕ`).

**Deck-isomorphism.** Graphs `G` and `H` (on possibly different vertex
sets of the same size) are deck-isomorphic if `D(G) = D(H)`.

**Hypomorphism.** A bijection `f : V(G) → V(H)` is a *hypomorphism* if
for every `v ∈ V(G)` there is an isomorphism `G - v ≅ H - f(v)`. `G`
and `H` are **hypomorphic** iff such `f` exists.

## Equivalence for vertex reconstruction

**Proposition.** For finite simple graphs on the same number of
vertices, `G` and `H` are hypomorphic iff they are deck-isomorphic.

**Proof.** (⇒) A hypomorphism exhibits a bijection on vertex sets that
pairs cards, so the multisets of card-isomorphism-classes agree.
(⇐) If `D(G) = D(H)` as multisets, pick any bijection `f : V(G) →
V(H)` that matches vertex `v` to a vertex `w` with `[G - v] = [H - w]`
(such a matching exists because the multisets agree); this `f` is a
hypomorphism by construction.

So for vertex reconstruction the two notions **coincide**, and either
can be taken as "the hypothesis" of the Reconstruction Conjecture.

## The conjecture, restated

- **RC (deck version).** If `G, H` have `≥ 3` vertices and `D(G) =
  D(H)`, then `G ≅ H`.
- **RC (hypomorphy version).** If `G, H` have `≥ 3` vertices and are
  hypomorphic, then `G ≅ H`.

These are the same statement.

## Why the `n ≥ 3` lower bound?

- `n = 1`: both graphs are single-vertex graphs; the deck is empty;
  trivially determined, but conventions vary.
- `n = 2`: two graphs `K_2` and `\bar K_2` have the same two-card deck
  (both cards are a single isolated vertex, so deck = `{{ [K_1],
  [K_1] }}`). They are not isomorphic. Hence `n = 2` is a genuine
  counterexample and the conjecture is traditionally stated for
  `n ≥ 3`.

## Edge-deck analogue

The same formal setup works for the edge-reconstruction problem:

**Edge-card.** For `e ∈ E(G)`, the edge-card at `e` is `[G - e]`
(edge-deleted subgraph, vertex set preserved).

**Edge-deck.** `D_e(G) := ⟦ [G - e] : e ∈ E ⟧`.

**Edge-hypomorphy.** A bijection `f : E(G) → E(H)` with `G - e ≅
H - f(e)` for every `e`.

The analogue of the Proposition above holds with the same proof: on
finite graphs, edge-hypomorphy is equivalent to edge-deck-isomorphy.

## Connection to group actions / automorphisms

If `G` has non-trivial automorphism group `Aut(G)`, several vertices
of `G` can have the same card up to isomorphism. In the extreme,
`G = K_n` has all `n` cards equal to `[K_{n-1}]`. Reconstruction of
highly symmetric graphs is therefore harder: the deck provides
essentially a single piece of information rather than `n`.

This is why probabilistic results (Bollobás — see
[random-graphs.md](random-graphs.md)) rely on rigidity, and why
"difficult" reconstruction instances tend to be highly symmetric
graphs (Cayley graphs, strongly regular graphs, etc.).

## Lean 4 angle

In Mathlib:

- `SimpleGraph.induce (s : Set V)` gives the induced subgraph.
- `SimpleGraph.deleteVerts` gives vertex deletion.
- A good definition of the deck would be a `Multiset (Quotient
  SimpleGraph.Iso)`, but since isomorphism classes of finite
  `SimpleGraph`s do not have a canonical "quotient" in Mathlib, one
  usually works with `Multiset (SimpleGraph V')` and reasons up to
  isomorphism explicitly.
- Hypomorphy is the natural formulation for induction.

See [../formalization/index.md](../formalization/index.md).
