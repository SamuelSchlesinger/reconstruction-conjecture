# k-Reconstruction and the k-Deck

## Definitions

Let `G` be a graph on `n` vertices, and let `k ≤ n` be a positive
integer.

- A **k-card** of `G` is an isomorphism class of a `k`-vertex *induced*
  subgraph of `G`.
- The **k-deck** of `G` is `D_k(G) :=` multiset of all `k`-cards,
  counted with multiplicity over `\binom{n}{k}` vertex subsets.

Equivalent, more common conventions:

- For `k = n − 1`, `D_{n−1}(G)` is the classical (vertex) deck; RC =
  `(n−1)`-reconstruction.
- A graph `G` is **ℓ-reconstructible** if `G` is determined up to
  isomorphism by `D_{n − ℓ}(G)`. So ℓ = 1 is standard RC.

**k-Reconstruction Conjecture (generic form)**. For each fixed `ℓ`
there exists `M_ℓ` such that every graph on `n ≥ M_ℓ` vertices is
`ℓ`-reconstructible (equivalently, determined by its `(n − ℓ)`-deck).

## Known bounds on `M_ℓ`

- `M_1 ≤ 14` follows from RC being open for `n ≥ 14` but believed true
  — note this is *assuming* RC, not a theorem.
- **Lower bound**: `M_ℓ ≥ 2ℓ + 1` always [kostochkawest21][kostochkawest21].
  Idea: any two graphs that differ only on a set of `2ℓ` "indistinguishable"
  vertices can have the same `(n − ℓ)`-deck.
- **Superlinear lower bound** (Nýdl). [nydl92][nydl92] constructed
  infinite families of pairs of non-isomorphic graphs with identical
  `(n − ℓ)`-decks, showing `M_ℓ` grows at least like `c · ℓ^{3/2}` and
  in fact superlinearly — definitely not `M_ℓ = 2ℓ + 1` in general.

## Solved cases for small `ℓ`

### ℓ = 1 (classical RC)

Open for `n ≥ 14`. See [`../state-of-the-art/index.md`](../state-of-the-art/index.md).

### ℓ = 2 (2-reconstruction from `(n − 2)`-deck)

- **Kostochka, Nahvi, West, Zirlin** [kostochkanahviwestzirlin21][kostochkanahviwestzirlin21]:
  every 3-regular graph on `n ≥ 8` vertices is 2-reconstructible.
- Strongly regular graphs and weakly distance-regular graphs have been
  handled by the same group of authors (papers 2021–2023, arXiv
  2210.11742, verify).
- General case: **open**.

### ℓ = 3 (3-reconstruction)

- **Kostochka, Nahvi, West, Zirlin** (arXiv:1904.11901):
  degree lists and connectedness are 3-reconstructible for graphs
  with `n ≥ 7` vertices — i.e. the *degree sequence* and connectivity
  status of `G` are determined by `D_{n−3}(G)` as long as `n ≥ 7`.
- Acyclic graphs on `n ≥ 2ℓ + 1` vertices are ℓ-recognizable
  [kostochka25][kostochka25] (i.e. the property "is a tree" is
  determined, even if the specific tree is not).

### Small `k` (fixed, small)

If `k` is a fixed small constant (like `k = 3, 4, 5`) and `n → ∞`,
the `k`-deck becomes very *weak* information; most graphs cannot be
reconstructed. The question there is different: which invariants
(edge count, triangle count, degree sequence) are determined by the
`k`-deck?

- The **3-deck determines the number of edges and triangles**
  (elementary counting).
- The **degree sequence is not in general determined by any bounded
  `k`-deck**; the threshold grows.
- [dudekwest14][dudekwest14] (verify) and related: small-`k`
  reconstruction of path length sequences, cycles, and other
  substructures.

## Recent positive results

### Reconstruction from smaller cards

[israelmath25][israelmath25] (Israel J. Math., *Reconstruction from
smaller cards*, 2025, verify URL):
new upper bounds on `M_ℓ` for certain graph classes, extending the
Kostochka–West line of work.

### k-Deck uniqueness for random graphs

Bollobás-style arguments show that for random `G(n, 1/2)`, the
`⌈log n⌉`-deck determines `G` w.h.p. So asymptotically `M_ℓ` is not
the obstruction for typical graphs; the hard cases are structured
ones.

## Formalization targets

For Lean 4:

1. **Define `k_deck`** as a `Multiset` of isomorphism classes of
   induced subgraphs. Prove basic lemmas: if `k = n` then
   `k_deck(G) = {[G]}`; if `k ≤ n`, `|k_deck(G)| = C(n, k)`.
2. **Kelly's Lemma at level `k`**: for `F` a graph on `f < k` vertices,
   `c(F, G)` is a linear combination of counts on `k_deck(G)`.
   Standard formula.
3. **3-regular + 2-reconstructible**: formalize the cubic graph theorem
   of Kostochka–Nahvi–West–Zirlin. Medium-length proof, case analysis
   on automorphism types of 3-regular components.
4. **Lower bound `M_ℓ ≥ 2ℓ + 1`**: straightforward construction once the
   API is in place. A good early exercise to check definitions.

[kostochkawest21]: ../sources.md#kostochkawest21
[nydl92]: ../sources.md#nydl92
[kostochkanahviwestzirlin21]: ../sources.md#kostochkanahviwestzirlin21
[kostochka25]: ../sources.md#kostochka25
[dudekwest14]: ../sources.md#dudekwest14
[israelmath25]: ../sources.md#israelmath25
