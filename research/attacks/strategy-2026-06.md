# Strategy Review (2026-06): Where a Proof Could Come From

This note records a full review of the project's research corpus against the
current literature (verified by direct source checks, June 2026), the Lean
progress landed alongside it, and a ranked list of attack ideas. It corrects
two stale facts in earlier notes and adds two literature developments that
change the strategic picture.

## Corrections and new literature (verified)

1. **McKay's verification bound is `n ≤ 13`, not `n ≤ 11`.**
   [McKay 2022, "Reconstruction of small graphs and digraphs"](https://arxiv.org/abs/2102.01942)
   confirms RC (and the set-reconstruction variant) exhaustively for all
   graphs on ≤ 13 vertices, triangle-free to 14, square-free and bipartite
   to 15. Any counterexample has `n ≥ 14`.

2. **The reduction chain is sharper than Yongzhi.** The known chain is now:
   - [Yongzhi 1988](https://onlinelibrary.wiley.com/doi/10.1002/jgt.3190120214):
     RC ⟺ all **2-connected** graphs reconstructible.
   - Ramachandran–Monikandan 2009: RC ⟺ all 2-connected graphs with
     `diam(G) = 2` or `diam(G) = diam(Gᶜ) = 3` reconstructible.
   - [Aravind–Monikandan, Jan 2026](https://arxiv.org/abs/2601.00620):
     RC ⟺ all 2-connected graphs with **`γ(G) = 2` or
     `diam(G) = diam(Gᶜ) = 2`** reconstructible (γ = domination number).
     Their tools are pure counting: recognizability of `γ(G) = 2`, plus new
     reconstructible vertex-pair parameters — Kelly-flavored, very much in
     this project's wheelhouse.

   **Consequence:** the *hard core* of RC is dense, diameter-2, 2-connected
   graphs — exactly the regime where separators do not exist. The separator
   programme (rungs 1–3) is how the *literature frontier* advances class by
   class, but the residual class after all reductions is separator-free. A
   complete proof must eventually couple separator structure with a
   counting/domination argument for the diameter-2 core.

3. **Kocay's lemma is an active research vein again.**
   [Stark, Sept 2025](https://arxiv.org/abs/2509.02604) generalizes Kocay's
   lemma to 2-edge-refined graphs (tracking edges *and* non-edges), proves
   Hamiltonian **path** counts reconstructible with elementary machinery
   close to our `Kocay.lean`, and proves a trichotomy for tree subgraph
   counts. This is the modern elementary reference for finishing Tutte-style
   counting targets.

4. **Confirmed open/closed status** (matches our docs): Bondy 1969 covers
   separable graphs *without* end-vertices; the pendant-vertex class is
   open; interval graphs closed (Heinrich et al. 2025); chordal open.
   **No literature exists** on reconstruction via the Tutte/SPQR
   decomposition of 2-connected graphs — that direction is unexplored.

## What was just landed in Lean (this review's formal progress)

| Result | File |
|---|---|
| 2-connectedness is deck-recognizable (`SameDeck.twoConnected_iff`, via `twoConnected_iff_forall_deleteVert_connected`) | `SeparatorComponents.lean` |
| The multiset-Kelly regrouping engine: exact-support walk counts are full-support counts of induced subgraphs; full-support counts are iso-invariants; sums over `m`-subsets regroup into `∑_classes s(q,G)·fullCount(q)` (`GraphIsoClass`, `sum_fullSupport_induce_eq`) | `SupportCount.lean` |
| **The proper-support top-trace sector is reconstructible** (`SameDeck.properSupportClosedWalkCount_eq`) — discharges half of the staged constant-term obligation | `SupportCount.lean` |
| **The full-support sector is the Hamiltonian sector**: `fullSupportClosedWalkCount |V| = hamiltonianHomCount` (closed `n`-walks with full support are exactly Hamiltonian-cycle traversals = injective homs `cycleGraph n →g G`) | `HamiltonianWalk.lean` |
| Constant term of the charpoly now reduced to **one named hypothesis**: `SameDeck.charPoly_coeff_zero_eq_of_hamiltonianHomCount_eq`; staged target `HamiltonianHomCountReconstructible` (= Tutte 1979) | `CharPolyFull.lean`, `HamiltonianWalk.lean` |

The staged `sorry` in `charPoly_coeff_zero_eq` is now *exactly* "the number
of Hamiltonian cycles is deck-reconstructible" — the precise classical
content of Tutte's theorem, no more and no less.

## Ranked attack ideas

### R1 — Finish Tutte's theorem (known math; first-formalization prize)

> **Keystone landed (same review):** `SameDeck.coverTypeCount_eq`
> (`KocayHost.lean`) — **Kocay's lemma in deck form**: host cover counts are
> reconstructible for every pattern family on `< n` vertices. Kocay's
> identity has exactly one Kelly-invisible summand (the full vertex set), and
> the `GraphIsoClass` regrouping pins it. What remains is the extraction
> below.

Close `HamiltonianHomCountReconstructible` via Kocay's counting:

1. **Möbius/triangular induction over `Kocay.lean`'s cover identity** to
   prove: the number of *spanning disconnected* subgraphs of each
   isomorphism type is reconstructible. The identity
   `∏ s(Fᵢ,G) = ∑_X c(F,X)·s(X,G)` already exists
   (`coverTypeCount_sum_inducedIsoClass`); the induction is descending on
   the component partial order, exactly like
   `Disconnected/ComponentCount.lean` (the project has done this move once
   already, for components).
2. **Extract the Hamiltonian count** from products of path counts (Stark's
   elementary route, or Bondy's manual §Tutte). The `GraphIsoClass` engine
   from `SupportCount.lean` supplies the class-indexed sums.

Payoff: the full characteristic polynomial reconstructible in Lean — to our
knowledge the first formalization of Tutte's 1979 theorem — and the
spanning-count machinery is reusable for R6.

### R2 — Bondy rung 1 deck recovery, then the Yongzhi compiler

Recognition is now done (2-connectedness). The remaining content is
**attachment recovery for a cut vertex** (end-block analysis, Bondy 1969):
blocks, the block–cut tree, end-blocks, and the card that exhibits an
end-block with its attachment. This is the project's critical path: with it,
`BondySeparableReconstructible` closes, and formalizing Yongzhi 1988 turns
every future 2-connected class theorem into a global one. Sub-targets:

- vertex connectivity `κ` is deck-reconstructible (`κ(G) = 1 + min_v
  κ(G−v)` for connected `G` — folklore; quick once `κ` is defined);
- blocks and the block–cut tree (absent from Mathlib; sizable but
  self-contained Mathlib-grade contribution);
- the block-count and end-block-multiset reconstructibility lemmas
  (classical, Bondy/Bondy–Hemminger survey).

### R3 — The unexplored direction: SPQR / Tutte decomposition (new math)

A 2-connected, not 3-connected graph decomposes **canonically** (Tutte 1966;
SPQR tree) into a tree of triconnected components (3-connected nodes, cycle
nodes, bond nodes) glued over 2-cuts ("virtual edges"). Nobody has attempted
deck reconstruction guided by this decomposition — verified by literature
search; Heinrich et al. call size-≥2 separations "a major roadblock," and
their interval solution invents ad-hoc anchors precisely because general
tree decompositions are non-canonical. The SPQR tree **is** canonical: that
is a new lever the interval proof did not have.

- The project's multi-vertex assembler (`nonempty_iso_of_separator_pieces`)
  already handles `|S| = 2` reassembly: the structural side is done.
- First paper-sized question: **is the multiset of triconnected components
  deck-reconstructible?** (Analogue of Kelly's component-multiset result,
  one rung up; Kelly counting + the canonical decomposition makes this
  plausibly tractable.)
- Long goal: a Bondy-style end-node induction over the SPQR tree ⟹
  "RC for 3-connected ⟹ RC for 2-connected", which composed with Yongzhi
  would reduce RC to **3-connected** graphs — a reduction that does not
  exist in the literature.
- Tournament sanity check: SPQR/2-cuts are undirected-specific (Stockmeyer
  barrier respected).

### R4 — Chordal via clique trees (rung 3, new math)

The clique-separator decomposition of a chordal graph is canonical (atoms =
maximal cliques, Leimer); the clique tree is the branching analogue of the
interval clique *path*. Strategy: redo Kelly's tree induction at the level
of the clique tree. Stepping stones:

- **Maximal-clique counts are reconstructible** modulo the join case: the
  number of maximal `r`-cliques is an alternating sum of counts of
  `K_r ∗ (j-vertex graphs)` (join patterns), all on `< n` vertices *unless*
  some `K_r` dominates `G` — and graphs with dominating structure fall to
  the already-formalized join case (`nonempty_iso_of_compl_not_connected`).
  Concrete, provable now with `KellyLemma.lean` + `Kocay.lean`.
- **Block graphs** (every block a clique; clique tree = block–cut tree) as
  the warm-up class — shares the R2 block layer.
- The wall to watch: equal-degree simplicial vertices in symmetric
  positions; this is where the linear-order anchors of the interval proof
  have no analogue.

### R5 — Side theorem with publication value: the 1-WL deck question

Arvind–Köbler–Verbitsky (2024/2406.09351) study reconstruction up to color
refinement. The self-contained open-flavored question our machinery can
attack: **is the iterated degree sequence (the multiset of 1-WL colors)
deck-reconstructible?** Level-1 version: the multiset over `v` of
(neighbor-degree multisets). Moments of this distribution are counts of
degree-decorated stars; star patterns stay below `n` vertices unless a
vertex is universal — and universal-vertex graphs are already reconstructed
(`nonempty_iso_of_universal_vertex`). The degree decorations push patterns
above `n` in general, so this is genuinely open-ended — but any positive
level would be a new reconstructible invariant strictly refining the degree
sequence (our `DegreeSequence.lean` is level 0).

### R6 — Computational probe: the rank of the Kocay system

Kelly + Kocay give, for every family `F` of `< n`-vertex graphs, a linear
constraint `∑_{X spanning} c(F,X)·s(X,G) = deck-known`. The unknown vector
is `(s(X,G))_X` over spanning types `X`. Two concrete experiments for
`n = 7…10` (nauty-scale, scriptable in `research/computational/`):

1. Compute the rank of the constraint matrix `c(F,X)` over ℚ. If it pins
   all spanning counts, "counting + integrality" alone would prove RC at
   that size — strong evidence for a counting-complete strategy (and a
   precise conjecture: *the cover-count matrix has full column rank*). If
   not, the kernel basis **is** the wall, stated exactly.
2. Relatedly: which spanning *connected* counts become determined when all
   disconnected ones are known (the R1 machinery)? This quantifies how far
   Tutte/Kocay extraction can possibly reach (Thatte's and Stark's results
   are lower bounds on this rank).

This experiment has, as far as the search found, never been published, is
cheap, and directly informs whether R1's machinery has a ceiling.

## Honest bottom line

Nothing here is a royal road; RC has resisted 84 years and the McKay bound
means a counterexample, if any, is large. The project's framing — assembly
is done, **deck recovery is the wall** — survives this review intact. The
genuinely new opportunities found: the **SPQR programme (R3)**, which is
literature-empty and matches the project's machinery shape exactly; the
**reduction-chain target class** (2-connected, γ=2 / diameter-2), which is
counting-friendly and where any new reconstructible pair-parameter directly
shrinks the conjecture; and the **rank experiment (R6)**, which would put
the "counting ceiling" folklore on quantitative footing. The recommended
order of work: R1 (closes a staged sorry; reusable machinery), then R2
(critical path), with R3 opened in parallel as the research bet, and R6 as
a background computational task.

## Sources

- McKay (2022). Reconstruction of small graphs and digraphs. arXiv:2102.01942.
- Yang Yongzhi (1988). The reconstruction conjecture is true if all
  2-connected graphs are reconstructible. J. Graph Theory 12(2) 237–243.
- Ramachandran, Monikandan (2009). Graph reconstruction conjecture:
  reductions using complement, connectivity and distance. Bull. ICA 56.
- Aravind, Monikandan (2026). A reduction of the Reconstruction Conjecture
  using domination and vertex pair parameters. arXiv:2601.00620.
- Heinrich, Kiyomi, Otachi, Schweitzer (2025). Interval graphs are
  reconstructible. arXiv:2504.02353.
- Stark (2025). Generalization and power of Kocay's lemma in graph
  reconstruction. arXiv:2509.02604.
- Arvind, Köbler, Verbitsky (2024). On the expressibility of the
  reconstructional color refinement. arXiv:2406.09351.
- Bondy (1969). On Ulam's conjecture for separable graphs. Pacific J. Math.
- Tutte (1979). All the king's horses. Kocay (1981). Some new methods in
  reconstruction theory.
