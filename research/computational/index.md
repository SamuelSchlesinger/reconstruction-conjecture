# Computational Verification of the Reconstruction Conjecture

The Kelly–Ulam reconstruction conjecture has been verified by direct computer
search for every simple graph up through `n = 13` vertices. The extension
from `n = 11` (McKay 1997 [mckay97][mckay97]) to `n = 13`
(McKay 2022 [mckay22][mckay22]) required roughly a quarter-century of
algorithmic and hardware improvement; the size of the search space is the
sequence [OEIS A000088](https://oeis.org/A000088), which grows
super-exponentially, so pushing a single vertex further is a major undertaking.
This document collects the **state of verification**, the **software stack**
(McKay's `nauty`/`geng`, plus `showg` and `gtools`), the **databases** of
small and "interesting" graphs (House of Graphs [coolsaet23][coolsaet23]),
the **complexity-theoretic status** of the associated decision problems
(Kratsch–Hemaspaandra 1994 [krahem94][krahem94]; cf. Babai 2016
[babai16][babai16]), and the known **digraph / tournament counterexamples**
(Stockmeyer 1977 / 1981 [stockmeyer77][stockmeyer77][stockmeyer81][stockmeyer81]).

Cross-references: [../state-of-the-art/index.md](../state-of-the-art/index.md),
[../attacks/index.md](../attacks/index.md),
[../related/index.md](../related/index.md).

## State of verification

The table records what has been *directly* verified by computer enumeration,
i.e. every graph in the given class was generated and checked to have a unique
deck among isomorphism classes of graphs of the same order. "Verified" is
strong: it means no two non-isomorphic graphs with the same deck were found.

| n | verified undirected | by | year | reference |
|---|---------------------|----|----|-----------|
| ≤ 7 | yes (trivial; can redo on a laptop) | folklore | — | — |
| 8 | yes | implicit in Harary–Palmer era | pre-1970 | see Bondy survey |
| 9 | yes | McKay | ca. 1977 | [mckay97][mckay97] |
| 10 | yes | McKay | ca. 1977–1997 | [mckay97][mckay97] |
| 11 | **yes** | McKay | 1997 | [mckay97][mckay97] |
| 12 | yes | McKay | ca. 2021 | [mckay22][mckay22] |
| 13 | **yes** | McKay | 2022 | [mckay22][mckay22] |
| 14 | **open** | — | — | — |

In the same 2022 paper McKay also extends verification within particular
classes further (triangle-free graphs to 14 vertices, square-free graphs to
15, bipartite graphs to 15, connected digraphs to 9, posets to 13, tournaments
to 13). See [bounds.md](bounds.md) for the precise table.

### Why `n = 14` is out of reach

The raw count of non-isomorphic simple graphs on `n` vertices
(OEIS A000088) is:

| n | A000088(n) (number of unlabeled graphs) |
|---|----|
| 10 | 12,005,168 |
| 11 | 1,018,997,864 |
| 12 | 165,091,172,592 |
| 13 | 50,502,031,367,952 |
| 14 | 29,054,155,657,235,488 |
| 15 | 31,426,485,969,804,308,768 |

Going from `n = 13` to `n = 14` multiplies the graph count by roughly
575; even with canonical-deletion pruning the verification cost scales
super-linearly in this count because each graph's deck must be generated
and looked up. McKay's 2022 verification at `n = 13` relies on
parallelization and the *canonical-deletion* trick (see
[software.md](software.md)) that lets a candidate counterexample pair be
detected while building only *one* graph from each deck-equivalence
class — that is, the work is proportional to the number of deck
*classes* rather than to A000088(n) squared. Even so, the 2022 run at
`n = 13` was reported to use substantial CPU-months; a straight factor
of ~575 in the base count plus the cost of deck lookup at this scale
puts `n = 14` roughly two orders of magnitude beyond current practice.
Barring a structural shortcut (e.g. a proof that some easily-recognized
invariant already determines the graph in all but a tiny residue of
cases), brute-force verification of `n ≥ 14` is not feasible on
contemporary clusters.

See [bounds.md](bounds.md) for a more detailed accounting and
[software.md](software.md) for the algorithmic ingredients.

## Software stack

Every published verification run uses some version of **`nauty`**
(Brendan McKay, with Adolfo Piperno for `Traces`)
[nauty-manual][nauty-manual][mckayp14][mckayp14]. The relevant tools are:

- **`nauty`** — canonical labelling and automorphism group of a graph;
  used to decide isomorphism of cards.
- **`geng`** — generates one representative of each isomorphism class of
  graphs on `n` vertices (or matching a degree/edge constraint). The
  standard enumeration benchmark.
- **`directg`**, **`genbg`**, **`gentreeg`**, **`showg`** — generators
  and displayers for digraphs, bipartite graphs, trees, and textual
  output, all in the `gtools` suite.

Deck-equivalence is tested in practice by the following pipeline
(see [software.md](software.md) for details):

1. Enumerate graphs of order `n` with `geng` *in canonical form*.
2. For each graph `G`, compute `D(G) = { canonlab(G - v) : v ∈ V }`
   as a sorted multiset of nauty g6-strings (canonical labels).
3. Hash each such multiset; collisions within a hash bucket are
   checked for true deck-equivalence (multiset equality of canonical
   labels), and the associated `G` and `G'` are then checked for
   isomorphism. A hit where `G` and `G'` are non-isomorphic would be
   a counterexample.

Two engineering tricks make this tractable:

- **Canonical deletion.** Picking a canonical vertex of `G` (via
  `nauty`) to "re-attach" means the deck of `G` is obtained from
  exactly one canonical child of each card. This is the core of
  McKay's generation-tree approach and is what allows one to iterate
  over deck-classes rather than over pairs of graphs.
- **Invariant pre-filters.** Fast-to-compute reconstructible invariants
  (degree sequence, edge count, component structure, number of
  triangles) bucket the search so that deck-comparison is done only
  within small buckets.

A self-contained Python/Sage validation script for small `n ≤ 7` is
provided in [`data/deck_equiv.py`](data/deck_equiv.py); sample output
for `n = 5` is at [`data/deck_equiv.txt`](data/deck_equiv.txt).

## Databases and infrastructure

- **Brendan McKay's graph collections**
  ([https://users.cecs.anu.edu.au/~bdm/data/](https://users.cecs.anu.edu.au/~bdm/data/)).
  `graph6`/`sparse6` files for graphs on small vertex counts,
  regular graphs, trees, planar graphs, Cayley graphs,
  Ramsey candidates, and strongly regular graphs.
- **House of Graphs 2.0** (Coolsaet, D'hondt, Goedgebeur, et al.
  [coolsaet23][coolsaet23];
  [https://houseofgraphs.org](https://houseofgraphs.org)). Searchable
  database of *interesting* graphs with invariant queries and download
  in graph6/digraph6.
- **OEIS A000088** ([https://oeis.org/A000088](https://oeis.org/A000088)) —
  the enumeration counts above, the driver of the verification budget.
- **`nauty` / `Traces` distribution** (McKay and Piperno;
  [https://pallini.di.uniroma1.it/](https://pallini.di.uniroma1.it/) and
  [https://users.cecs.anu.edu.au/~bdm/nauty/](https://users.cecs.anu.edu.au/~bdm/nauty/)).
  Current stable 2.9.x (source-compatible with the 2.8.x series); see
  [`../sources.md#nauty-manual`](../sources.md#nauty-manual).

See [database.md](database.md) for a more detailed table of graph
databases with provenance and format notes.

## Complexity-theoretic status

Four natural decision / construction problems underlie the conjecture:

- **Deck Checking** — given `G`, `H`, decide whether `D(G) = D(H)` as
  multisets of isomorphism classes.
- **Legitimate Deck** — given a multiset `D` of graphs on `n - 1`
  vertices, decide whether there exists `G` on `n` vertices with
  `D(G) = D`.
- **Preimage Construction** — given a legitimate deck `D`, produce some
  `G` with `D(G) = D`.
- **Preimage Counting** — count the number of `G` with `D(G) = D`; the
  reconstruction conjecture asserts this is always `0` or `1` for
  `n ≥ 3`.

**Known relationships** (Kratsch and Hemaspaandra 1994
[krahem94][krahem94]; Hemaspaandra, Hemaspaandra, Radziszowski and
Tripathi 2007 [hhrt07][hhrt07]):

- Deck Checking is polynomial-time **equivalent** to Graph Isomorphism
  (both reductions are elementary).
- Graph Isomorphism reduces (many-one, polynomial-time) to Legitimate
  Deck.
- Legitimate Deck, Preimage Construction, and Preimage Counting are
  solvable in polynomial time for graphs of bounded degree, for
  partial `k`-trees for each fixed `k`, and for graphs of bounded
  genus (in particular, for planar graphs).

In the unrestricted setting these problems therefore inherit the
status of Graph Isomorphism, which Babai [babai16][babai16] placed in
quasi-polynomial time `exp((log n)^{O(1)})` at STOC 2016 (the
"minor error / repaired" saga of early 2017 was resolved; the
quasi-polynomial bound stands). No problem in this family is known
to be NP-complete, and doing so would collapse the polynomial
hierarchy (Boppana–Håstad–Zachos / Schöning-style consequences).

**Consequence for verification.** The per-graph work to detect a
counterexample is dominated by canonical labelling of the `n` cards
(`n` calls to `nauty` on graphs of order `n - 1`), which in practice
is linear in `n` with small constants for sparse graphs and
polynomial for dense graphs. Babai's theoretical improvement does
not yet change the constants in `nauty`, but it underpins the belief
that deck-comparison will never be the algorithmic bottleneck —
enumeration is.

## Algorithmic reconstruction from a legitimate deck

The decision version "is `D` legitimate?" is hard in general (at
least as hard as Graph Isomorphism), but *given* a legitimate deck,
Kelly-style algorithms construct a witness graph. A simple
polynomial-in-`|D|` procedure:

1. From `D`, read off the degree sequence `d_1, ..., d_n` of `G` (the
   edge-count recovers degrees, since `|E(G - v)| = |E(G)| - d(v)`).
2. From the degree sequence, determine the number of edges
   `|E(G)| = (1/(n-2)) · sum_v |E(G - v)|` (Kelly's Lemma in
   counting form).
3. Use **Kocay's Lemma** [kocay81][kocay81] — the counting identity
   for subgraph tuples — to determine, for each graph `F` on `≤ n-1`
   vertices, the number of ways `F` embeds in `G`. Specifically, for
   any sequence `(F_1, ..., F_r)` of subgraphs covering `G`, Kocay's
   Lemma expresses the number of ordered covers by `(F_1, ..., F_r)`
   in `G` as a deck-computable linear combination of cover-counts in
   the cards. Iterating on increasing `|V(F)|` recovers the
   subgraph-multiplicity profile of `G` up to `|V(G)| - 1`, from which
   `G` itself is determined under the usual reconstructibility
   hypotheses. This replaces the vague "fuse cards along a common
   `(n-2)`-vertex subgraph" step with the actual counting identity.

This naive algorithm is polynomial in `n` and the size of the deck,
but its precise running time is dominated by sub-isomorphism tests
between cards, hence by Graph Isomorphism. On the **restricted**
classes mentioned above (bounded degree, bounded genus, bounded
treewidth) every step is genuinely polynomial
[krahem94][krahem94][hhrt07][hhrt07].

For the full verification pipeline McKay does **not** run the above
reconstruction in forward mode; instead he enumerates `G` directly
via `geng` and asks whether two distinct canonical `G`, `G'` produce
the same deck. That is strictly easier than "given a deck, produce a
graph" because enumeration already builds a canonical candidate.

## Digraph counterexamples (Stockmeyer)

The digraph reconstruction conjecture is **false**. A census of the
smallest known counterexamples:

| Order `n` | # non-reconstructible pairs (tournaments) | # non-reconstructible pairs (general digraphs) | Reference |
|-----------|-------------------------------------------|-----------------------------------------------|-----------|
| 3 (= `2^0 + 2^1`) | **1** (the 3-cycle vs. the transitive tournament; each card is the unique 2-vertex tournament) | 1 | Stockmeyer 1977 [stockmeyer77][stockmeyer77]; cf. Harary–Palmer 1967 [hararypalmer67][hararypalmer67] |
| 4 | 0 new pairs (all 4 tournaments reconstructible) | 1 | Stockmeyer 1977 [stockmeyer77][stockmeyer77] |
| 5 (= `2^0 + 2^2`) | tournament pairs per Stockmeyer 1977 Table 1 (verify exact count) | (verify) | [stockmeyer77][stockmeyer77] |
| 6 (= `2^1 + 2^2`) | tournament pairs per Stockmeyer 1977 Table 1 (verify exact count) | (verify) | [stockmeyer77][stockmeyer77] |
| 8 | 2 tournament pairs | — | Stockmeyer 1975 (thesis); see [stockmeyer77][stockmeyer77] |
| all `n = 2^s + 2^t`, `0 ≤ s < t` | ≥ 1 tournament, plus five non-tournament | ≥ 6 pairs | Stockmeyer 1981 [stockmeyer81][stockmeyer81] |
| all `n = 2^t + 2^t = 2^{t+1}` | 0 tournament (construction gives non-tournaments only) | 3 pairs | Stockmeyer 1981 [stockmeyer81][stockmeyer81] |

The small-order counts come directly from Stockmeyer's 1977 Table 1
[stockmeyer77][stockmeyer77]; the smallest non-reconstructible
tournament pair sits at order `n = 3 = 2^0 + 2^1`, not at order 5, 6,
or 8 as sometimes misreported. For the broader enumeration of
tournaments and their invariants see Harary–Palmer 1967
[hararypalmer67][hararypalmer67] and Kocay 1985
[kocay85][kocay85]. Tan's Oxford thesis [tan23][tan23] (chapter 2)
consolidates the census; entries flagged "(verify exact count)" above
still need cross-check for the exact pair count at `n = 5, 6` because
conventions differ (labelled vs. unlabelled, symmetric pairs).

What the counterexamples *do not* imply: because the undirected deck
has no orientation, Stockmeyer's families do not produce undirected
counterexamples. They only restrict the class of arguments that could
settle the undirected conjecture (any "orientation-agnostic" deck
invariant argument would have to fail on tournaments too, and thus
could not succeed in general).

## Detail documents

- [bounds.md](bounds.md) — A000088 scaling, McKay 2022 class extensions,
  budget estimates for `n = 14`.
- [software.md](software.md) — `nauty`, `geng`, `gtools`, `graph6`
  format, canonical deletion, invariant pre-filters.
- [database.md](database.md) — McKay collections, House of Graphs,
  OEIS, provenance and formats.

[mckay97]: ../sources.md#mckay97
[mckay22]: ../sources.md#mckay22
[coolsaet23]: ../sources.md#coolsaet23
[krahem94]: ../sources.md#krahem94
[hhrt07]: ../sources.md#hhrt07
[babai16]: ../sources.md#babai16
[stockmeyer77]: ../sources.md#stockmeyer77
[stockmeyer81]: ../sources.md#stockmeyer81
[kocay81]: ../sources.md#kocay81
[kocay85]: ../sources.md#kocay85
[nauty-manual]: ../sources.md#nauty-manual
[mckayp14]: ../sources.md#mckayp14
[tan23]: ../sources.md#tan23
[hararypalmer67]: #hararypalmer67

[hararypalmer67]: ../sources.md#hararypalmer67
