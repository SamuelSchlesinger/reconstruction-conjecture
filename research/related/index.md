# Related Conjectures

This page surveys conjectures that sit in the orbit of the Kelly–Ulam
**Reconstruction Conjecture (RC)** — strengthenings, weakenings,
generalizations to other combinatorial objects, and refutations that
prompted new salvage formulations. Each variant is worth considering as a
Lean 4 formalization target, either because its statement is clean, or
because its proof machinery feeds back into the main conjecture. Cross-links:
[`../state-of-the-art/index.md`](../state-of-the-art/index.md),
[`../invariants/index.md`](../invariants/index.md),
[`../attacks/index.md`](../attacks/index.md).

## Summary table

| # | Conjecture | Statement (informal) | Status | Primary reference |
|---|------------|----------------------|--------|-------------------|
| 1 | **Reconstruction Conjecture (RC)** | Every graph on `n ≥ 3` vertices is determined by its vertex-deck (multiset of `(n−1)`-vertex induced subgraphs). | **Open**. Verified for `n ≤ 13`. | [kelly57][kelly57]; [ulam60][ulam60] |
| 2 | **Edge Reconstruction Conjecture (ERC)** | Every graph on `m ≥ 4` edges is determined by its edge-deck (multiset of edge-deleted subgraphs). | **Open in general**; true when `m ≥ n·log₂ n` ([muller77][muller77]) and in several graph classes. | [harary64][harary64] |
| 3 | **Set Reconstruction Conjecture (SRC)** | Every graph on `n ≥ 4` vertices is determined by the *set* (not multiset) of its `(n−1)`-cards. | **Open**; strictly stronger than RC; verified for `n ≤ 13` ([mckay22][mckay22]). | [hararyplantholt85][hararyplantholt85] |
| 4 | **k-Reconstruction** (`ℓ`-reconstructibility) | For fixed `k < n−1`, determine `G` from its k-deck (multiset of induced `k`-subgraphs). Equivalently: does there exist a threshold `M_ℓ` s.t. every `n`-vertex graph with `n ≥ M_ℓ` is `ℓ`-reconstructible? | Partial. `M_ℓ ≥ 2ℓ+1`; superlinear lower bounds by [nydl92][nydl92]. Many positive results by Kostochka–West and collaborators. | [kostochkawest21][kostochkawest21] |
| 5 | **Digraph Reconstruction Conjecture** | Every digraph is determined by its vertex-deck. | **Refuted** (tournaments of order `2^s + 2^t` for `0 ≤ s < t`). | [stockmeyer77][stockmeyer77] |
| 6 | **New Digraph Reconstruction Conjecture** | Digraph plus deck plus matched in-/out-degree pairs ⇒ isomorphism. | **Open**. | [ramachandran81][ramachandran81] |
| 7 | **Tournament Reconstruction** | Every tournament on `n ≥ n₀` vertices is deck-reconstructible. | **Refuted** for infinitely many `n` ([stockmeyer77][stockmeyer77]). | [stockmeyer77][stockmeyer77] |
| 8 | **Hypergraph Reconstruction** | Every hypergraph is vertex-deck reconstructible. | **Refuted** for uniform rank `≥ 3`. | [kocay87][kocay87] |
| 9 | **Switching Reconstruction Conjecture** (Stanley) | Every simple graph on `n ≥ 5` vertices is determined by its multiset of *switching-cards* (vertex-switches). | **Open** (undirected). | [stanley85][stanley85] |
| 10 | **Switching Reconstruction of Digraphs** | Digraph analogue (reverse incident arcs). | **Refuted on 8 vertices**; open for large `n`. | [mckayschweitzer18][mckayschweitzer18] |
| 11 | **Polynomial Reconstruction** | The characteristic / Tutte / chromatic / matching polynomial is deck-reconstructible. | Partial: these four are known reconstructible; full list open. | [tutte79][tutte79]; [farrellwahid87][farrellwahid87] |
| 12 | **Metric (Distance) Reconstruction** | Reconstruct `G` from the multiset of distance-matrices of vertex-deleted subgraphs (or from a related distance deck). | Largely **open**; used as a tool in RC reductions. | [bondy91][bondy91] (survey) |

## Implication diagram

The arrows below track what is known about logical dependency among the
variants. `A ⇒ B` means: a proof of `A` yields a proof of `B`. `A ⊬ B`
means there is a known counterexample showing no such implication. `?`
means open.

```
   Hypergraph Recon (FALSE)        Digraph Recon (FALSE)
                                          │
                                          │  (motivated salvage)
                                          ▼
                                   New Digraph Recon (open)
                                          │
                                          │  restricting to symmetric digraphs
                                          ▼
   Set Recon (SRC, open) ══(strictly stronger)══▶  Reconstruction Conjecture (RC)
                                                          │
                                                          │  Greenwell 1971
                                                          │  (on graphs w/o isolated vertices)
                                                          ▼
                                                    Edge Reconstruction (ERC, open)

   k-Reconstruction (k = n−1) ≡ RC
   k-Reconstruction (k small) ─── generally harder; decoupled from RC
```

Key verified implications:

- **RC ⇒ ERC** (on graphs without isolated vertices). Greenwell 1971
  [greenwell71][greenwell71] showed: if `G` has no isolated vertices
  (equivalently `δ(G) ≥ 1`) and `G` is vertex-reconstructible, then `G` is
  edge-reconstructible. The converse direction (ERC ⇒ RC) is **open**.
- **SRC ⇒ RC.** Trivially, since the deck-as-set is a coarsening of the
  deck-as-multiset (passing from multiset to set only loses information).
- **RC on `k = n−1`** is the classical conjecture. The `k`-reconstruction
  question for small `k` is not known to imply or be implied by RC in any
  direction.
- **ERC ⇒ RC?** Open. Some reductions exist in the triangle-free case and
  via Whitney-type arguments, but no full implication is known.
- **Digraph RC ⇏ RC** (trivially, since digraph RC is false).

## Per-variant detail pages

- [Edge Reconstruction](edge-reconstruction.md)
- [Set Reconstruction](set-reconstruction.md)
- [k-Reconstruction and k-decks](k-reconstruction.md)
- [Digraph and tournament variants](digraph-variants.md)

Polynomial, hypergraph, switching and metric reconstruction are covered
below in brief because they each fit on a single screen.

## Hypergraph Reconstruction

A hypergraph `H = (V, E)` has uniform rank `r` if every edge has exactly
`r` vertices. The natural vertex-deck is `{H − v : v ∈ V}`.

- **Kocay (1987)** [kocay87][kocay87] constructed infinite families of
  pairs of non-isomorphic 3-uniform hypergraphs with identical vertex-decks.
  Hence the reconstruction conjecture is **false for all uniformities
  `r ≥ 3`**.
- For `r = 2` the hypergraph case reduces to ordinary graph RC.
- Interest remains in which *hypergraph invariants* are reconstructible
  from the deck: e.g. the matching polynomial (see [polynomial-reconstruction
  notes below](#polynomial-reconstruction)).
- Kocay's constructions are also informative as test data for graph RC
  attacks: they show that invariants reconstructible for graphs (rank
  polynomial, cycle index) may fail for hypergraphs.

## Polynomial Reconstruction

Several families of graph polynomials are known to be deck-reconstructible
— i.e. computable from the vertex-deck alone — even though the underlying
graph is not known to be:

| Polynomial | Reconstructible? | Reference |
|------------|------------------|-----------|
| Characteristic polynomial | Yes | [tutte79][tutte79] (via Kelly) |
| Chromatic polynomial | Yes | [tutte79][tutte79] |
| Rank polynomial | Yes | [tutte79][tutte79] |
| Tutte polynomial | Yes | follows from rank polynomial reconstruction |
| Matching polynomial | Yes | [farrellwahid87][farrellwahid87] |
| Independence polynomial | Partial / class-restricted | survey in [bondy91][bondy91] |
| Permanental polynomial | Open (URL unknown — verify) | — |

Open direction: find a natural polynomial that is **provably not**
deck-reconstructible for graphs, or push reconstructibility to further
classes. For hypergraphs, Kocay's counterexamples achieve this for the
characteristic polynomial.

See also the companion notes in
[`../invariants/index.md`](../invariants/index.md) on Kelly's Lemma and
its polynomial applications.

## Switching Reconstruction

**Switching** a vertex `v` in a simple graph `G` means complementing its
neighborhood: edges `vw` become non-edges, and non-edges `vw` become edges
(for `w ≠ v`). The switching-deck is the multiset of all `n` single-vertex
switching results.

- **Stanley's Conjecture (1985)** [stanley85][stanley85]: every simple graph
  on `n ≥ 5` vertices is switching-reconstructible.
- Known: the vertex-deck and the switching-deck determine one another on
  sufficiently large `n` — so switching reconstruction is equivalent to RC
  at the asymptotic level, but behaves differently for small `n`.
- **Digraph version** (arc-reversal at a vertex): Bondy–Mercier
  [bondymercier11][bondymercier11] and later McKay–Schweitzer
  [mckayschweitzer18][mckayschweitzer18] produced non-reconstructible
  examples on 8 vertices; status above that threshold is open.

## Metric / Distance Reconstruction

Several "metric decks" appear in the literature; naming is not fully
standardized.

1. **Distance-deck of a vertex-deleted family.** Record for each `v`
   the multiset `{d_{G−v}(x,y)}`. Used in the classical RC reduction:
   **the diameter of `G` is reconstructible when `diam(G) ≥ 3`**
   (Bondy 1991 [bondy91][bondy91]), since distance profiles are
   recoverable from the ordinary deck via Kelly's Lemma. The
   **`diam = 2` case is open** and is known to be a reduction class for
   RC — i.e. RC reduces to the subclass of diameter-2 graphs.
2. **Distance-card deck.** Each card is the *distance matrix* of
   `G − v`. Conjecturally equivalent to the ordinary deck for graphs of
   diameter `≥ 2`, but no counterexample to `diameter = 2 ⇒` reconstructible
   is known; in fact, *diameter-2 graphs are recognizable* and the
   reconstruction conjecture on diameter-2 graphs is a well-known reduction
   of RC (see [bondy91][bondy91]).
3. **Metric-dimension-style variants**, e.g. reconstructing a graph from
   its "resolving set" distance information, are logically quite different
   problems and do not directly bear on RC, though they share motivation.

Status: no known counterexample to any sensible distance-deck
reconstruction conjecture, but also no proof; typically the techniques
mirror Kelly-style counting.

## Reconstruction number

A closely related invariant, frequently used to measure how "easy" a
given graph is to reconstruct:

- **Reconstruction number** `rn(G)`: the minimum number of cards from
  `deck(G)` that already determine `G` up to isomorphism. Formally, the
  smallest `k` such that every `k`-subset of the deck occurs in the
  deck of at most one graph (up to iso).
- **Adversary reconstruction number** `arn(G)`: the minimum `k` such
  that *every* choice of `k` cards determines `G` uniquely.

Clearly `rn(G) ≤ arn(G) ≤ n`, and `rn(G) = 1` iff some single card is
already unique to `G`.

- **Classical result.** `rn(K_n) = 3` for `n ≥ 4` — Molina 1995
  (verify); three edge-less `K_{n−1}` cards suffice, while two do not.
- **Bollobás 1990** [bollobas90][bollobas90]: for almost all graphs
  `rn(G) = 3`, i.e. three cards already suffice with probability
  tending to 1.
- Detailed tables of `rn(G)` for small graphs are maintained in the
  House of Graphs [coolsaet23][coolsaet23] and in McKay's 2022
  enumeration [mckay22][mckay22].

See the forthcoming [`../invariants/index.md`](../invariants/index.md)
entries for the Kelly-Lemma-based machinery used to extract lower
bounds on `rn(G)` from deck counts.

## Formal implications — open questions

- Is **ERC ⇒ RC**? Open in general. Proofs are known under hypotheses
  such as minimum degree, bipartiteness, triangle-freeness.
- Is **SRC ⇔ RC**? The set deck and multiset deck differ exactly when
  there are pairs of isomorphic cards. No counterexample separating SRC
  from RC is known.
- Is **k-Reconstructibility monotone in `k`**? I.e. `k`-reconstructibility
  for all graphs implies `(k+1)`-reconstructibility for all graphs with
  `n ≥ k+2`. Yes, follows from Kelly-style deck derivation — but the
  quantitative thresholds `M_ℓ` are not monotone in a clean way.
- Does **polynomial reconstructibility imply graph reconstructibility**
  for any known polynomial? Open — this is the motivation for many
  spectral attacks on RC (see [`../attacks/index.md`](../attacks/index.md)).

[kelly57]: ../sources.md#kelly57
[ulam60]: ../sources.md#ulam60
[harary64]: ../sources.md#harary64
[muller77]: ../sources.md#muller77
[stockmeyer77]: ../sources.md#stockmeyer77
[ramachandran81]: ../sources.md#ramachandran81
[kocay87]: ../sources.md#kocay87
[greenwell71]: ../sources.md#greenwell71
[hararyplantholt85]: ../sources.md#hararyplantholt85
[mckay22]: ../sources.md#mckay22
[nydl92]: ../sources.md#nydl92
[kostochkawest21]: ../sources.md#kostochkawest21
[tutte79]: ../sources.md#tutte79
[farrellwahid87]: ../sources.md#farrellwahid87
[bondy91]: ../sources.md#bondy91
[bondymercier11]: ../sources.md#bondymercier11
[stanley85]: ../sources.md#stanley85
[mckayschweitzer18]: ../sources.md#mckayschweitzer18
[bollobas90]: ../sources.md#bollobas90
[coolsaet23]: ../sources.md#coolsaet23
