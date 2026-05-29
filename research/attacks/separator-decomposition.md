# Reconstruction by Separator Decomposition

This note records the **separator-decomposition programme**, adopted after a
strategy review of the centered-extension / fixed-host campaign (see
[`fixed-host-t-empty.md`](fixed-host-t-empty.md) for the falsification that
prompted the review). It is the project's primary attack going forward.

## Why this direction

A literature-grounded hunt for a "new attack" produced three verdicts.

1. **Flag algebras / homomorphism-density / SDP-positivity: dead on arrival.**
   Two independent structural kills. *Orientation-agnosticism* — a pure
   density/positivity argument applies verbatim to tournaments, where
   reconstruction is **false** (Stockmeyer 1977 [stockmeyer77][stockmeyer77]);
   the positivity of homomorphism-density inequalities is in fact undecidable
   for tournaments (Chen–Lin–Ma–Wei 2025 [chenlinmawei25][chenlinmawei25])
   exactly as for graphs (Hatami–Norine 2011 [hataminorine11][hataminorine11]),
   so such an argument would "prove" the false directed version.
   *Truncation* — the deck gives densities only for patterns on `< n` vertices,
   and the missing top-level data is precisely what the conjecture is about, so
   pinning it down by PSD constraints is close to assuming the conclusion.
   Densities also vanish for sparse graphs, and there is no usable sparse-graphon
   analogue (Kunszenti-Kovács–Lovász–Szegedy 2020 refuted the natural one
   [kklovsz20][kklovsz20]).

2. **Weisfeiler–Leman / coherent configurations as *counting power*: collapses
   into Kelly.** Dell–Grohe–Rattan [dellgroherattan18][dellgroherattan18]:
   `k`-WL indistinguishability ⟺ equal homomorphism counts from all
   treewidth-`≤ k` graphs. Kelly's Lemma already reconstructs **all** hom-counts
   for **all** patterns on `< n` vertices, so WL reads a *strict subset* of the
   deck's counting information and cannot beat it. The one genuinely novel,
   self-contained WL question that survives (Arvind–Köbler–Verbitsky 2024
   [arvindkoblerverbitsky24][arvindkoblerverbitsky24]) is whether the global
   refinement colouring `WL(G)` is itself deck-reconstructible — a side target,
   not a route to the conjecture.

3. **Separator decomposition: the field's live frontier, and the right fit for
   this project.** Reconstruction has fallen, class by class, up a ladder of
   *separator size*, and the project already owns the bottom rung.

## The separator-size ladder

| Separator | Class | Status | Project status |
|---|---|---|---|
| `∅` (components) | disconnected | proven (Kelly 1942) | **formalized** (`Disconnected.lean`) |
| `1` vertex (cut vertex / blocks) | separable, `δ ≥ 2` | proven (Bondy 1969 [bondy69][bondy69]) | **target — rung 1** |
| reduces to | 2-connected | suffices for full conjecture (Yongzhi 1988 [yongzhi88][yongzhi88]) | corollary of rung 1 |
| `≥ 2` vertices | interval graphs | proven (Heinrich–Kiyomi–Otachi–Schweitzer 2025 [heinrich25][heinrich25]) | **target — rung 2** |
| clique separators | chordal graphs | **OPEN** | **target — rung 3 (new mathematics)** |
| small separators | bounded treewidth / genus | **OPEN** (but reconstruction is poly-time, Kratsch–Hemaspaandra 1994 [krahem94][krahem94]) | stretch target |

Adjacent open sparse classes that the same machinery may reach: planar (general),
bipartite, cubic (2-reconstructible known, Kostochka–Nahvi–West–Zirlin 2021
[kostochkanahviwestzirlin21][kostochkanahviwestzirlin21]).

The organizing thesis: **a graph is the amalgam of the pieces obtained by
deleting a separator `S`, glued along `S`.** If (i) the separator and the
attachment data are deck-reconstructible, and (ii) matched pieces reassemble
into a global isomorphism, the class is reconstructible. Our existing
component machinery is exactly case (i)+(ii) for `S = ∅`; each rung relaxes the
separator.

## How it clears the four barriers

- **Schwenk cospectrality (Wall 1):** structural, not a spectral function. ✓
- **Kelly counting ceiling (Wall 2):** uses card *iso-types* and the actual
  decomposition, not just counts; the reassembly step is where structure beyond
  counting enters. ✓
- **Stockmeyer (Wall 3):** *largely not applicable to class-restricted
  undirected theorems.* Stockmeyer's non-reconstructible tournaments are not
  members of these undirected classes, so the orientation barrier that blocks
  full-generality orientation-agnostic proofs is relaxed here. (Each reassembly
  proof should still be checked for an undirected-specific ingredient, but it is
  no longer a hard obstruction.) ✓
- **Sparse regime (Wall 4):** these *are* the sparse classes. This is the rare
  family of attacks with genuine sparse traction, and the only one the hunt
  found. ✓✓

## What Mathlib provides, and what is missing

Mathlib (v4.28.0) has the connectivity foundation but none of the separator
layer. Confirmed by source search:

**Present:** `SimpleGraph.Connected`, `Preconnected`, `Reachable`,
`ConnectedComponent` (+ `supp`), `induce`, `Subgraph.deleteVerts`,
`IsBridge` (edges only), `IsEdgeConnected k`, `Iso`/`≃g`,
`Iso.connectedComponentEquiv`.

**Missing — must be defined from scratch:**

- cut vertex / articulation point (`IsCutVertex`);
- vertex separator / vertex cut (set whose deletion disconnects);
- `k`-vertex-connectivity / 2-connectivity;
- blocks / biconnected components / block-cut tree;
- Menger's theorem (vertex form).

**Reusable project infrastructure:** `componentSigmaGraph`, `isoSigmaComponents`,
`componentSigmaGraphIsoOfComponentIso`, `isoOfComponentIsoEquiv`,
`isoOfComponentCountEq` (`Disconnected.lean`); Kelly's Lemma and subgraph counts
(`KellyLemma.lean`, `Kocay.lean`); the triangular component-count recovery
(`Disconnected/ComponentCount.lean`).

## Lean architecture

New module `Reconstruction/Separator.lean` (and later `Blocks.lean`):

1. **Primitives** (missing from Mathlib): `IsCutVertex`, `Separates S u v`
   (`S` separates `u` from `v`), `IsVertexCut`, `TwoConnected`. Basic
   characterizations and the `S = ∅ ↔ component` bridge to existing infra.
2. **Separator reassembly engine** — the generalization of `isoSigmaComponents`
   from disjoint union (`S = ∅`) to **amalgamation over a shared separator
   `S`**: given a separator `S` common to `G` and `H`, an isomorphism fixing `S`
   pointwise on each "piece" (component of `G − S` together with its attachment
   to `S`) assembles into `G ≃g H`. This is the structural heart of *every*
   rung and the main provable prize.
3. **Rung 1 — Bondy's reduction**: a connected graph with a cut vertex and
   `δ ≥ 2` is reconstructible; corollary (Yongzhi) that 2-connected suffices.
   Needs block decomposition + induction on the block-cut tree.
4. **Rung 2/3** — port the Heinrich et al. multi-vertex-separator method;
   attack chordal via clique separators.

Staged targets are stated as `def … : Prop` (the project's convention for
open/under-construction goals), **not** as `theorem … := sorry`. The only
permitted `sorry`s remain `reconstruction_conjecture` and
`charPoly_coeff_zero_eq`.

## Honest risks

- **Reassembly over a non-empty separator is genuinely harder than the
  disjoint-union case.** `G` is *not* the disjoint union of its `(component ∪ S)`
  pieces — `S` is shared — so the Sigma assembly must become an amalgamation
  (pushout over `S`), handling intra-`S` edges and each piece's attachment map.
  This is exactly why Bondy 1969 is harder than Kelly 1942.
- **Recovering the decomposition from the deck** (which separator, how pieces
  attach) is the deck-theoretic content and is class-specific; the reassembly
  engine is class-agnostic but does not by itself reconstruct anything.
- **This is "join the frontier," not "invent a new lever."** For an 80-year-old
  problem that is the higher-probability bet, but it means our novelty lives in
  the *formalization* (none of this is in Mathlib) and in possibly reaching an
  open class (chordal), not in a brand-new mathematical idea.

## References

See [`../sources.md`](../sources.md). New entries added for this programme:
Heinrich et al. 2025 (interval graphs), Kratsch–Hemachandra 1994 (complexity),
and the negative-result anchors (Dell–Grohe–Rattan 2018, Hatami–Norine 2011,
Chen–Lin–Ma–Wei 2025, Kunszenti-Kovács–Lovász–Szegedy 2020,
Arvind–Köbler–Verbitsky 2024, Oliveira–Thatte 2013).

[stockmeyer77]: ../sources.md#stockmeyer77
[bondy69]: ../sources.md#bondy69
[yongzhi88]: ../sources.md#yongzhi88
[heinrich25]: ../sources.md#heinrich25
[krahem94]: ../sources.md#krahem94
[kostochkanahviwestzirlin21]: ../sources.md#kostochkanahviwestzirlin21
[dellgroherattan18]: ../sources.md#dellgroherattan18
[hataminorine11]: ../sources.md#hataminorine11
[chenlinmawei25]: ../sources.md#chenlinmawei25
[kklovsz20]: ../sources.md#kklovsz20
[arvindkoblerverbitsky24]: ../sources.md#arvindkoblerverbitsky24
[oliveirathatte13]: ../sources.md#oliveirathatte13
