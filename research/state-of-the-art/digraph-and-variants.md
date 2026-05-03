# Digraph Reconstruction and Related Variants

## Digraph conjecture is FALSE (Stockmeyer 1977)

The **digraph reconstruction conjecture** is the analogue of the Kelly–Ulam
conjecture for directed graphs: a directed graph on `n ≥ 3` vertices is
determined up to isomorphism by its multiset of vertex-deleted sub-digraphs.
Stockmeyer [stockmeyer77][stockmeyer77] disproved this by exhibiting
infinite families of pairs of non-isomorphic tournaments with the same
vertex-deck.

**Counterexample orders.** Stockmeyer's construction produces
counterexample tournament pairs at every order `n = 2^s + 2^t` with
`0 ≤ s < t`, so the smallest tournament orders where counterexamples
arise are `n = 3, 5, 6, 9, 10, 12, 17, 18, ...`. (Non-tournament
digraph counterexamples also occur at small `n`.) In a follow-up
[stockmeyer81][stockmeyer81] he expanded the account into six related
families. A 2009 erratum appeared in *Journal of Graph Theory* **62**(2),
199–200.

**What the counterexamples use.**
- Asymmetric in-/out-neighbourhoods (the key extra structure a digraph
  has that an undirected graph does not).
- Score-sequence symmetries that leave individual vertex-deletions
  indistinguishable despite the global digraph being different.
- Cayley-style / Paley-like constructions on vertex sets of suitable
  binary-sum orders.

## Why Stockmeyer's counterexamples do NOT refute the undirected conjecture

This is a subtle but important point.

- **Different deck**. An undirected simple graph `G` has a deck of
  undirected `n - 1`-vertex graphs. A tournament `T` on the same
  underlying vertex set has a deck of `n - 1`-vertex *tournaments*.
  There is no natural map between these two decks.
- **The "undirected shadow" is not invariant.** If you take an
  undirected graph `G` and its orientation `T = (G, ori)`, the deck of
  `T` remembers orientations; the deck of `G` does not. Two
  non-isomorphic tournaments `T_1 ≇ T_2` with the same tournament-deck
  can have underlying undirected graphs `U(T_1), U(T_2)` that are
  isomorphic as undirected graphs, or non-isomorphic, or both-sharing
  an undirected deck but distinct — any combination is possible. So
  Stockmeyer's pair does not translate into an undirected counterexample
  of either direction.
- **No implication either way.** The undirected conjecture is neither
  implied by nor implies the digraph conjecture; they are independent
  statements about different decks.

**What Stockmeyer's result does tell us.** A proof of the undirected
Reconstruction Conjecture cannot be "orientation-agnostic" — it cannot
proceed purely by symbol-shuffling or edge-counting arguments that make
sense equally for directed and undirected graphs, because in the directed
setting the analogous argument is known to fail. The proof must use a
feature specific to the *unordered* edge relation.

## Set reconstruction

The **set reconstruction** problem asks whether a graph is determined
by the *set* (ignoring multiplicities) of its vertex-deleted subgraphs.
This is a formally stronger statement (less information given) than
multiset reconstruction.

- **Harary, Schwenk, and others** investigated set reconstruction; it
  is open in general, with similar positive results for trees,
  disconnected graphs, and regular graphs.
- Set reconstruction is *implied* by deck reconstruction (the multiset
  determines the set trivially), so any positive result for the
  standard conjecture implies the corresponding set version with
  possibly more book-keeping.

## `k`-deck reconstruction

Given `1 ≤ k ≤ n - 1`, the **`k`-deck** of `G` is the multiset

```
D_k(G) := { [G[S]] : S ⊆ V(G), |S| = k }
```

of isomorphism classes of induced subgraphs on `k`-vertex subsets. The
standard deck is `D_{n-1}(G)`.

- **Manvel (1970s)** showed that trees can be reconstructed from `D_k`
  for `k` around `n/2`.
- **Nýdl (1992)** and others gave counterexamples to `k`-deck
  reconstruction for small `k`: there are pairs of graphs with the same
  `k`-deck for `k = o(n)`. Exact threshold is unknown; verify primary
  source.
- **Kocay's Lemma** [kocay81][kocay81] generalizes Kelly's Lemma to
  induced subgraph counts of arbitrary fixed size.

The `k`-deck problem is interesting as an *interpolation* between the
trivial problem (`k = n`, which is just knowing `G`) and the
reconstruction conjecture (`k = n - 1`). A reconstruction from `k = 2`
would require recovering `G` from its adjacency information (trivial),
but `k`-deck reconstruction for intermediate `k` is substantive.

## Matrix / spectrum reconstruction

The **spectral reconstruction** question: is a graph determined by the
multiset of spectra of its vertex-deleted subgraphs? This is **false**:
Schwenk 1973 [schwenk73][schwenk73] showed that the fraction of unlabeled
trees on `n` vertices having a cospectral mate tends to 1 as `n → ∞`, so
almost every tree fails to be determined by its spectrum alone. The more
refined question of characteristic-polynomial reconstruction is more
subtle. Kelly's Lemma reconstructs the
characteristic polynomial of `G` from its deck (see
[../invariants/index.md](../invariants/index.md)).

## Hypergraph reconstruction

Hypergraph reconstruction is false in general (Kocay gave counterexamples
in the early 1980s). The combinatorial flexibility of hyperedges
dominates the deck constraint. See [laurisc16][laurisc16] for a summary.

## Infinite graphs

The analogue for countable infinite graphs is known to **fail** — there
are locally finite countable trees which share all `n - 1`-vertex
sub-multisets but are non-isomorphic. The conjecture is fundamentally a
finite-combinatorics statement.

[stockmeyer77]: ../sources.md#stockmeyer77
[stockmeyer81]: ../sources.md#stockmeyer81
[kocay81]: ../sources.md#kocay81
[laurisc16]: ../sources.md#laurisc16
[schwenk73]: ../sources.md#schwenk73
