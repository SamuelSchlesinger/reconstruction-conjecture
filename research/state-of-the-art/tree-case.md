# Trees Are Reconstructible — Kelly 1957

Kelly's 1957 paper *A congruence theorem for trees* [kelly57][kelly57] is the
oldest non-trivial positive result for the Reconstruction Conjecture and was
in fact motivated by discussions with Ulam. It remains the paradigmatic
example of a reconstruction proof, and every subsequent tree-reconstruction
proof can be read as a streamlining of Kelly's argument.

## Statement

**Theorem (Kelly 1957).** Let `T` and `T'` be trees on `n ≥ 3` vertices
with `D(T) = D(T')`. Then `T ≅ T'`.

Equivalently: a tree on three or more vertices is determined up to
isomorphism by its vertex-deck.

## Kelly's Lemma

Kelly's argument rests on what is now known as **Kelly's Lemma** (sometimes
"Kelly's counting lemma"), which is useful far beyond trees. For graphs
`F`, `G` write `s(F, G)` for the number of subgraphs of `G` isomorphic to
`F`.

**Kelly's Lemma.** If `F` has strictly fewer vertices than `G` (so `|V(F)|
< |V(G)|`), then

```
s(F, G) = (1 / (n - |V(F)|)) · Σ_{v ∈ V(G)} s(F, G - v).
```

In particular, `s(F, G)` is reconstructible from `D(G)`. See
[../invariants/index.md](../invariants/index.md) for a derivation.

## Proof outline (Kelly 1957)

1. **The number `n` and the edge count are reconstructible.** Both are
   immediate from the deck (there are `n` cards, and `|E(G)| = (1/(n-2))
   · Σ_v |E(G-v)|` by a double count).
2. **The number of subtrees isomorphic to `T_0` is reconstructible** for
   every tree `T_0` with fewer than `n` vertices, by Kelly's Lemma.
3. **Identify the centre / bicentre.** Every tree has either a unique
   centre vertex (whose distance to the furthest leaf is minimal) or a
   pair of adjacent centre vertices. The "pruning" process — repeatedly
   deleting all leaves — strictly decreases the radius, and the number of
   times each pruning step occurs is a function of the *multiset of
   subtrees* of `T`. Kelly showed this centre-finding procedure can be run
   purely from the deck.
4. **Reconstruct outward from the centre.** Once the centre (or bicentre)
   is known, Kelly's Lemma gives the number of subtrees of each isomorphism
   type rooted at a given distance from the centre. A combinatorial
   matching argument pieces these together into a unique tree.

The key technical device is a "counting matrix" whose entries are the
multiplicities `s(T_0, T)` for a spanning family of small trees `T_0`;
Kelly's Lemma makes every entry reconstructible, and a Möbius-style
inversion recovers `T`.

## Modern streamlinings

- **Harary–Palmer (1966)** [hararypalmer66][hararypalmer66]. Introduced
  the "pruning sequence" viewpoint and reduced tree reconstruction to
  reconstructing the centre together with its subtree multiplicities.
  The proof fits on a page. Primary source: Harary, F., and Palmer, E. M.
  (1966). "The reconstruction of a tree from its maximal subtrees".
  *Canadian Journal of Mathematics* **18**, 803–810.
- **Bondy's survey.** [bondy91][bondy91] gives a crisp treatment with
  Kelly's Lemma up front.
- **Lauri–Scapellato.** [laurisc16][laurisc16] chapter on trees is the
  standard modern textbook reference; the proof is presented in three
  pages.

## Why trees are "easy"

- Trees have a canonical pruning from leaves inward, which means the deck
  essentially contains a recursive decomposition.
- Kelly's Lemma is at its most powerful on sparse graphs: the number of
  subgraphs isomorphic to any small tree grows slowly, so a few counts
  determine everything.
- Trees have a natural notion of centre, which gives a canonical
  "basepoint" for the reconstruction to anchor on.

None of these three features generalize cleanly to general graphs, which is
part of why the full conjecture is so much harder.

## Status of generalizations

- **Forests.** Immediately reconstructible by Harary's disconnected-graph
  result [harary64][harary64] applied to each component (which is a tree).
- **Unicyclic graphs (one cycle).** Reconstructible; see Manvel 1970s
  [manvel70][manvel70] (verify exact citation).
- **Graphs of tree-width `≤ 2` (series-parallel).** Partial results;
  believed reconstructible but primary-source coverage uncertain — verify.
- **Graphs with bounded tree-width.** Open in general.

## Lean 4 angle

Tree reconstruction is a strong candidate for a first non-trivial Lean 4
formalization within the sibling `graph-theory/reconstruction-conjecture`
project because:

1. Kelly's Lemma is a clean counting identity once `s(F, G)` is defined;
   it does not need the full reconstruction machinery.
2. Mathlib has trees and basic tree lemmas (`SimpleGraph.IsTree`), and the
   centre of a tree can be defined from `dist`.
3. The pruning / leaf-removal induction is amenable to well-founded
   recursion.
4. The outward-from-centre step is combinatorial and could piggy-back on
   Mathlib's `Multiset` infrastructure.

See [../formalization/index.md](../formalization/index.md) for a
breakdown of intermediate lemmas.

[kelly57]: ../sources.md#kelly57
[bondy91]: ../sources.md#bondy91
[harary64]: ../sources.md#harary64
[manvel70]: ../sources.md#manvel70
[laurisc16]: ../sources.md#laurisc16
[hararypalmer66]: ../sources.md#hararypalmer66
