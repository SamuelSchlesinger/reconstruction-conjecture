# Rung 2/3 Formalization Plan — Interval and Chordal Reconstruction

Plan for the higher rungs of the [separator-decomposition programme](separator-decomposition.md),
grounded in Heinrich–Kiyomi–Otachi–Schweitzer 2025 (interval graphs,
[arXiv:2504.02353][heinrich25]), classical chordal clique-separator theory, the
existing `Reconstruction.Separator` engine (`isoOfSamePiece`), and a direct
audit of Mathlib v4.28.0.

## Executive summary

- The project's `isoOfSamePiece` is exactly the **structural reassembly half**
  of what rungs 2/3 need, and it is genuinely class-agnostic (already stated for
  an arbitrary separator set `S`). **It is reusable verbatim** for both interval
  and chordal graphs. The hard, unautomated content is everything *else*:
  recovering the separation from the deck.
- Heinrich et al. is **not** a "plug a clique separator into the engine" proof.
  It is a ~50-page bespoke interval-graph structure theory ("bulk", "flanks",
  "outsiders", linearly-ordered neighbourhoods) whose entire purpose is to
  *locate* a reconstructible clean clique separation in the deck. Porting it
  whole is a multi-person-year effort and is **not** the advisable next step.
- The **Mathlib gap is severe** (confirmed by source grep): Mathlib has
  `IsClique`/`IsNClique`/`cliqueNum` only. It has **none** of: chordal graphs,
  simplicial vertices, perfect elimination orderings, tree/clique-tree
  decompositions, treewidth, vertex separators, vertex connectivity, Menger
  (vertex form), or interval representations. Each must be built from scratch.
- Honest recommendation: full interval reconstruction (rung 2) and chordal
  reconstruction (rung 3) are **research-grade**. The tractable, high-value next
  work is a *multi-vertex* generalization of the piece-assembler plus the
  **clique-separator / chordal structure layer** as standalone, Mathlib-style
  contributions — reusable and citable even though they don't by themselves
  reconstruct anything.

## 1. Structure of the Heinrich et al. 2025 interval-graph proof

**Main result (Thm 1):** every interval graph on `≥ 3` vertices is
reconstructible (hence in polynomial time). Stated meta-contribution: a
technique to handle **separations of size `> 1`**, "a major roadblock to using
graph structure theory in reconstruction."

- **Separator used — clean clique separation.** A *separation* is an ordered
  partition `(A, C, B)` with no edges between `A` and `B`; `C` is the separator
  (exactly the project's "pieces over `S`" with `S = C`). It is *clean*
  (Def. 11) when an interval representation has the separator intervals
  overlapping the `A`/`B` gap. The separator `C` **induces a clique** (Lemma 12,
  from the linearly-ordered-neighbourhood property) — the bridge to chordal
  graphs.
- **Recovering the separation from the deck (the hard part).** Not a Kelly-style
  counting argument; a bespoke **resilient structure theory** producing
  combinatorially-definable anchors that survive single-vertex deletion:
  degree/neighbor-degree reconstructibility (Lemma 5; the project already has
  the kernel — `SameDeck.card_edgeFinset_eq`, `degree_eq_of_card_edgeFinset_eq_of_deleteVert_iso`);
  the **bulk** `span(V_Δ(G))` (Def. 20, reconstructible); **flanks/outsiders**
  with a resilience lemma (Lemma 23); and the **Distant Vertex Lemma**
  (Lemma 25), which picks one card `G − b` that reveals an entire annotated side
  of the separation. Class recognition is borrowed (interval is
  deck-recognizable, von Rimscha 1983).
- **Reassembly — Reconstruction-by-Separation (Lemma 24).** If `G`, `G'` have
  clean clique separations with isomorphic *annotated* sides (graph iso + each
  separator vertex's original degree), then `G ≅ G'`. Its **structural core is
  exactly `isoOfSamePiece`** (with `S = C`), plus (i) intra-`S` edges form a
  clique and (ii) the separator-vertex degree annotation.

## 2. Chordal graphs and why rung 3 is open

- **Clique-separator decomposition (classical).** Simplicial vertex = one whose
  neighbourhood is a clique. Chordal ⟺ has a perfect elimination ordering (PEO)
  (Fulkerson–Gross, Dirac). **Dirac:** every non-complete chordal graph has a
  *minimal vertex separator that is a clique* — this guarantees the
  clean-clique-separator hypothesis of the engine is always available. Chordal
  graphs decompose along clique separators into "atoms" (Tarjan–Whitesides;
  [Berry–Pogorelcnik–Simonet survey][berry]); their clique tree is a
  minimum-width tree decomposition (`treewidth = ω − 1`).
- **Why open.** Chordal graphs are deck-*recognizable* (von Rimscha 1983) and
  several proper subclasses are reconstructible (unit interval, threshold,
  split, and now interval 2025), but the full class is not. The interval proof
  does **not** generalize: its anchors (bulk, flanks, the *linear* order of
  maximal cliques, asteroidal-triple-freeness) are interval-specific. Chordal
  graphs have a clique **tree**, not a clique **path** — no canonical left–right
  order, no interval representation, branching maximal-clique structure. The
  "recover one annotated side from one card" move loses meaning without a linear
  backbone, and equal-degree simplicial vertices make the deck-recovery of
  *which* separator and *how atoms attach* unpinned. **Rung 3 is new
  mathematics, correctly labelled OPEN.**

## 3. Reuse vs. new infrastructure

**Reuses the existing engine essentially as-is:** `SamePiece` / `adj_samePiece`
/ `adj_connectedComponentMk_eq` (the "no edge crosses the separator" lemma,
`S = C`); `isoOfSamePiece` / `isoOfSamePiece'` (the reassembly core of Lemma 24
— never assumed `|S| = 1`); `IsSeparator` / `IsSeparator.map`; the new
`IsCliqueSeparator` / `IsSimplicial` vocabulary (`CliqueSeparator.lean`); the
degree-reconstructibility kernel.

**Key engine insight:** `isoOfSamePiece` is already general in `S`. Only the
*assembler* `nonempty_iso_of_cutVertex_pieces` is singleton-specific (it uses
`deleteVert v` / `extendMap`). So the first real rung-2 deliverable is a
**multi-vertex assembler** feeding the existing engine.

**New Mathlib-gap infrastructure (all confirmed absent):**
- *Tier A (chordal core):* `IsSimplicial` ✓ (done), `IsCliqueSeparator` ✓
  (done); `IsChordal` / PEO and the Fulkerson–Gross/Dirac equivalences (hard);
  Dirac's clique-minimal-separator existence (hard); clique tree / tree
  decomposition and `treewidth = ω − 1` (very hard — tree decompositions are
  entirely absent from Mathlib).
- *Tier B (separator/connectivity):* `Separates` ✓ (done, `SeparatorChar.lean`);
  `k`-vertex-connectivity, blocks, Menger (vertex form) — open gap.
- *Tier C (interval-specific):* interval representation, consecutive-ones,
  asteroidal triples / Lekkerkerker–Boland, bulk/flank/outsider resilient
  theory, annotated subgraphs, Distant Vertex Lemma. **The 50-page bespoke
  layer. Do not start here.**

## 4. Ordered list of tractable next lemmas

Items 1–4 are **done**. Remaining, by increasing difficulty:

4. **[DONE — `SeparatorAssembler.lean`]** **Multi-vertex piece assembler**
   `nonempty_iso_of_separator_pieces` (+ the card-iso form
   `nonempty_iso_of_induce_compl_iso` and the `extendFixingSet` combinator) — the
   generalization of `nonempty_iso_of_cutVertex_pieces` from `S = {v}` to
   general `S`: a bijection of `(G.induce Sᶜ)`-components to
   `(H.induce Sᶜ)`-components, per-piece isos agreeing on `S`, and the link
   condition, produce `G ≃g H` via `isoOfSamePiece`. **The single highest-value
   reusable deliverable** — makes the engine usable for every rung `≥ 2` and for
   chordal. Medium: replace `extendMap`/`deleteVert` (singleton) with an
   `induce Sᶜ`-based amalgamation and discharge `hreflect` from the component
   bijection.
5. **[STARTED — `Chordal.lean`]** **Chordal definition + Dirac statements.**
   `IsChordal` is defined as "no induced `≥ 4`-cycle" (`IsEmpty (cycleGraph n ↪g G)`
   for `n ≥ 4` — a graph embedding reflects adjacency, so this is exactly an
   induced `Cₙ`), with `IsChordal.map` (iso-invariance), `IsChordal.induce`
   (hereditary), and `isChordal_of_card_le_three` proved. Dirac's theorems are
   stated as `Prop` targets `DiracSimplicial` and `DiracCliqueSeparator`. **The
   full existence proofs are deferred** (hard; see item 6).
6. **[PARTIAL — `Chordal.lean`]** Vertex deletion stays chordal
   (`IsChordal.deleteVert`, the PEO recursion step) and the simplicial base
   cases (`isSimplicial_of_subsingleton_neighborSet`, `isSimplicial_top`) are
   **done**. The remaining content is Dirac's existence theorem, reduced to the
   crux `MinimalSeparatorClique` (a minimal separator of a chordal graph induces
   a clique) — proving it needs **induced-cycle extraction from glued shortest
   paths**, the genuine hard walk-combinatorics step with no Mathlib support.
   This is the current bottleneck for rung 3.
7. **`IsChordal ⟺ has-PEO`** (Fulkerson–Gross / Rose–Tarjan–Lueker). Hard,
   multi-file.
8. **Clique tree / chordal tree decomposition**, `treewidth = ω − 1`. Very hard.
9. **(Rung 2 proper)** interval representation + bulk/flank theory + Distant
   Vertex Lemma + Reconstruction-by-Separation as a deck theorem. Research-grade.

**Immediate target:** item 4 (the multi-vertex assembler) — the precise
structural prerequisite shared by rungs 2 and 3, low-risk, built on confirmed
project code. Stage deck-recovery pieces as `def … : Prop` per the no-`sorry`
convention.

## Honest difficulty assessment

Reassembly (structural side) is largely done; item 4 finishes the multi-vertex
structural layer. **Deck recovery is the wall**: for interval graphs a 50-page
resilient structure theory with no shortcut; for chordal graphs *no recovery
technique exists in the literature at all*. The Mathlib substrate beyond
`IsClique` is empty, so items 5–8 are real, sizable contributions worth landing
on their own merits. Realistic near-term win: item 4 + the clique-separator
vocabulary (done), giving a class-agnostic "clean clique separation ⟹
reassembly" engine matching Heinrich Lemma 24's structural core — without yet
claiming any new reconstruction theorem.

## Sources

- Heinrich, Kiyomi, Otachi, Schweitzer (2025). "Interval graphs are
  reconstructible." [arXiv:2504.02353][heinrich25].
- Berry, Pogorelcnik, Simonet (2010). "An Introduction to Clique Minimal
  Separator Decomposition." *Algorithms* 3(2), 197–215. [link][berry].
- Dirac (1961); Fulkerson–Gross (1965); Rose–Tarjan–Lueker (1976) — chordal /
  PEO / simplicial theory.
- von Rimscha (1983) — chordal deck-recognizability and reconstructible
  subclasses. See also Tan, *Graph Reconstruction and Structure* (Oxford thesis).

[heinrich25]: https://arxiv.org/abs/2504.02353
[berry]: https://www.mdpi.com/1999-4893/3/2/197
