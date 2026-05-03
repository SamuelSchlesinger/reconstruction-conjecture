# State of the Art — Graph Reconstruction Conjecture

The **Reconstruction Conjecture** (Kelly 1942, Ulam 1960) asserts that every
finite simple graph on at least three vertices is determined up to isomorphism
by the multiset of its one-vertex-deleted subgraphs (its **deck**). After
eighty-odd years the conjecture remains open in full generality, but an
extensive catalogue of graph classes is now known to be reconstructible, and
the **edge-reconstruction** variant (Harary 1964) is known to hold for almost
every graph and for every graph with more than roughly `(n-1) log_2 n` edges.
Computer verification now extends the conjecture through all graphs on at
most 11 vertices (McKay). In contrast, the **digraph reconstruction
conjecture** is *false*: Stockmeyer (1977) exhibited infinite families of
tournament counterexamples, though these say nothing about the undirected
problem. This document is the umbrella for the current status and links out
to detail files for each major class.

## Formal statement

Let `G = (V, E)` be a finite simple graph with `|V| = n`. For `v ∈ V`, write
`G - v` for the induced subgraph on `V \ {v}`. The **vertex-deck** of `G` is
the multiset

```
D(G) := { [G - v] : v ∈ V }
```

of isomorphism classes (cards). Two graphs `G`, `H` on at least three
vertices are **hypomorphic** if there is a bijection `f : V(G) → V(H)` such
that `G - v ≅ H - f(v)` for every `v`.

- **Reconstruction Conjecture (Kelly–Ulam).** If `G` and `H` are simple
  graphs on the same vertex set, `n(G) = n(H) ≥ 3`, and `D(G) = D(H)` as
  multisets, then `G ≅ H`. Equivalently, every hypomorphism between graphs
  on at least three vertices extends to an isomorphism.
- **Edge-Reconstruction Conjecture (Harary 1964).** The analogous statement
  with edge-deleted subgraphs in place of vertex-deleted ones, for graphs on
  at least four edges.

The vertex form implies the edge form for `n ≥ 4` (Greenwell 1971,
generalized by Harary), modulo small-case bookkeeping, but the edge form is
strictly easier and far more is known about it.

See [hypomorphy.md](hypomorphy.md) for the precise relationship between
hypomorphy, card-isomorphism, and the deck.

## Reconstructible classes

The table below collects the main classes known to be reconstructible.
"Reconstructible" always means: any graph in the class is determined up to
isomorphism by its vertex-deck among *all* graphs (not merely within the
class) unless otherwise noted. Entries are cross-checked against Bondy's
survey [bondy91][bondy91] and Lauri–Scapellato's book [laurisc16][laurisc16].

| Class | Year | Author(s) | Notes |
|-------|------|-----------|-------|
| Trees (`n ≥ 3`) | 1957 | Kelly [kelly57][kelly57] | Harary–Palmer later gave a count-based proof; see [tree-case.md](tree-case.md) |
| Disconnected graphs with `≥ 2` non-trivial components | 1964 | Harary; refined by Manvel [harary64][harary64][manvel70][manvel70] | See [graph-classes.md](graph-classes.md) |
| Regular graphs | folklore (attributed to Kelly) | — | Immediate from Kelly's Lemma; see [../invariants/index.md](../invariants/index.md) |
| Graphs with a cut-vertex and no pendant vertex (separable) | 1969 | Bondy [bondy69][bondy69] | "Separable graphs without endvertices" |
| Unit interval graphs | 1970s | von Rimscha / Hagard–Stockmeyer-era folklore (verify) | See [graph-classes.md](graph-classes.md); exact attribution uncertain |
| Maximal planar graphs | 1981 | Fiorini–Lauri [fiorinilauri81][fiorinilauri81] | Outer boundary plus triangulation |
| Outerplanar graphs | 1974 | Giles [giles74][giles74] | |
| Graphs with at least `n - 3` vertices of degree `n - 1` | 1975 | Manvel [manvel76][manvel76] | Dominating-vertex method |
| Squares of graphs | 1972 | Manvel | Using neighbourhood reconstruction |
| Digraphs that are *non-tournaments* in some special families (partial) | various | — | See caveats in [digraphs](#digraph-conjecture-false) |
| Almost all graphs | 1990 | Bollobás [bollobas90][bollobas90] | Three cards suffice for almost every graph; see [random-graphs.md](random-graphs.md) |
| Graphs with `> (n-1) log_2 n` edges (edge-reconstruction) | 1977 | Müller [muller77][muller77] | See [edge-reconstruction](#edge-reconstruction) |
| `k`-connected graphs for large `k` relative to diameter | various | — | Partial; see [../invariants/index.md](../invariants/index.md) |
| Graphs of bounded max degree vs. diameter (various) | 1970s–80s | Nash-Williams, Bondy | See [bondy91][bondy91] for consolidated table |

Dates and attributions in italics above are cross-referenced with
[bondy91][bondy91]; where no primary source is cited, the result is
"folklore" in the sense of Bondy's survey and the primary attribution should
be verified against MathSciNet/Zbl.

### Quick sketches

- **Trees (Kelly 1957).** Kelly showed the number of subtrees isomorphic to
  any tree `T` on at most `n - 1` vertices is reconstructible (Kelly's
  Lemma), and then used a counting argument on the number of
  pendant-bearing subtrees. Harary–Palmer later gave a cleaner reduction to
  reconstructing the centre. See [tree-case.md](tree-case.md).
- **Disconnected graphs.** Kelly's Lemma yields the number of copies of
  each connected graph as a component; a maximal component can be peeled
  off and the remainder reconstructed inductively.
- **Regular graphs.** The degree sequence is reconstructible, so we know
  regularity and the common degree. Kelly's Lemma reconstructs the number
  of subgraphs isomorphic to each small graph, which pins down the full
  structure via inductive amalgamation.
- **Maximal planar (Fiorini–Lauri 1981).** Uses 3-connectivity and
  Whitney's theorem that 3-connected planar embeddings are unique; the
  deck determines the edge set plus the combinatorial embedding.
- **Almost all graphs (Bollobás 1990).** A random graph on `n` vertices
  with edge probability `1/2` has, with probability `1 - o(1)`, the
  property that any three of its cards uniquely determine it.

More detail, including proof skeletons and the exact probabilistic
parameters, lives in:

- [tree-case.md](tree-case.md) — Kelly's tree result in depth.
- [random-graphs.md](random-graphs.md) — Bollobás and related density
  results.
- [graph-classes.md](graph-classes.md) — the remaining structural classes.

## Edge reconstruction

The edge-reconstruction conjecture (Harary 1964) posits that a graph with
at least four edges is determined by its multiset of edge-deleted subgraphs.
Key positive results:

- **Lovász (1972).** Every graph with more than `½ · C(n, 2)` edges is
  edge-reconstructible [lovasz72][lovasz72].
- **Nash-Williams (1978).** Generalized Lovász to `m > (1/2) · n(n-1)` via a
  counting / Möbius-style argument [nashwilliams78][nashwilliams78].
- **Müller (1977).** Every graph with more than `(n-1) · log_2 n` edges is
  edge-reconstructible [muller77][muller77]; this remains the standard
  "dense" threshold cited in Bondy's survey.
- **Bipartite graphs (Krasikov–Roditty 1987 and earlier).** Edge
  reconstructible; attribution should be double-checked against
  [bondy91][bondy91].

The edge-form implies the vertex-form is "easier near the top" in the sense
that dense graphs are comparatively well-controlled; sparse graphs remain
the hard case for both.

## Open for which classes

Despite the above, the following natural classes are **not** known to be
reconstructible in general:

- **Bipartite graphs** — even though many edge-reconstruction results are
  known, full vertex-reconstruction is open.
- **Planar graphs** — only the maximal and outerplanar subclasses are
  settled; general planar remains open.
- **3-regular (cubic) graphs** — regular graphs *in the abstract* are
  reconstructible in the "known small cases" sense, but it is *not* known
  that every cubic graph is reconstructible from its deck; the folklore
  "regular graphs are reconstructible" result actually requires extra
  hypotheses (see [../invariants/index.md](../invariants/index.md) and
  [bondy91][bondy91] for the precise statement — verify in primary source).
- **Line graphs** — partial results only.
- **Chordal / interval graphs beyond unit interval** — not fully settled.
- **Digraphs (in general)** — not merely open but *false* for tournaments;
  see below.

## Digraph conjecture: false

Stockmeyer (1977) [stockmeyer77][stockmeyer77] disproved the digraph
reconstruction conjecture by exhibiting infinite families of pairs of
non-isomorphic tournaments with the same deck. The smallest counterexample
pair has `n = 8` vertices; Stockmeyer gave counterexamples for every
`n = 2^k` for `k ≥ 3` (see [stockmeyer81][stockmeyer81] for the expanded
account).

**These are not counterexamples to the undirected conjecture.** The
undirected reconstruction problem is not implied by the digraph one in
either direction: the deck of an undirected graph `G` is genuinely different
from the deck of any orientation of `G`, and the counterexamples exploit
features (asymmetric in-/out-neighbourhoods, score sequences) that have no
direct undirected analogue. What Stockmeyer's result *does* tell us is
that any general proof of the undirected conjecture must use properties
specific to undirected simple graphs — it cannot be a purely combinatorial
deck-counting argument that is orientation-agnostic.

See [../related/index.md](../related/index.md) for more on variants,
including set reconstruction, `k`-deck reconstruction, and matrix/spectrum
reconstruction.

## Hypomorphy

Two graphs `G` and `H` are **hypomorphic** iff there is a bijection
`f : V(G) → V(H)` with `G - v ≅ H - f(v)` for all `v`. The reconstruction
conjecture is exactly the statement that hypomorphy implies isomorphism for
`n ≥ 3`. The difference is subtle but important: the deck as a *multiset of
unlabeled graphs* can be recovered from a hypomorphism, but two graphs with
the same deck are *a priori* only card-isomorphic, not hypomorphic-via-a-fixed
bijection. For vertex-deletion the two notions coincide (any bijection
matching cards works), so the multiset deck is the standard formulation.

For a careful proof of the equivalence, and for the edge-deck analogue, see
[hypomorphy.md](hypomorphy.md).

## Links to sibling research directories

- [../invariants/index.md](../invariants/index.md) — Kelly's Lemma,
  recoverable parameters (degree sequence, number of edges, components,
  characteristic polynomial, etc.).
- [../attacks/index.md](../attacks/index.md) — spectral approaches,
  Nash-Williams' lemma, probabilistic attacks.
- [../related/index.md](../related/index.md) — edge reconstruction, set
  reconstruction, `k`-deck reconstruction, matrix analogues, digraph
  results.
- [../formalization/index.md](../formalization/index.md) — Lean 4 /
  Mathlib angles and the sibling Lean project.

## Detail documents

- [tree-case.md](tree-case.md) — Kelly's 1957 proof for trees, modern
  simplifications, and the centre-of-a-tree viewpoint.
- [random-graphs.md](random-graphs.md) — Bollobás 1990 and later:
  reconstruction from three cards for almost all graphs.
- [graph-classes.md](graph-classes.md) — disconnected graphs, regular
  graphs, maximal planar, outerplanar, unit interval, squares, separable
  graphs without endvertices, dominating-vertex methods.
- [edge-reconstruction.md](edge-reconstruction.md) — Lovász, Nash-Williams,
  Müller, and the status of Harary's conjecture.
- [digraph-and-variants.md](digraph-and-variants.md) — Stockmeyer's
  counterexamples, what they do and do not imply, and the status of set
  and `k`-deck reconstruction.
- [hypomorphy.md](hypomorphy.md) — formal definition, equivalence to
  card-isomorphism, and the edge-deck analogue.
- [computational-verification.md](computational-verification.md) —
  McKay's verification up through `n = 11` and the tools used.

[bondy91]: ../sources.md#bondy91
[kelly57]: ../sources.md#kelly57
[harary64]: ../sources.md#harary64
[manvel70]: ../sources.md#manvel70
[manvel76]: ../sources.md#manvel76
[bondy69]: ../sources.md#bondy69
[fiorinilauri81]: ../sources.md#fiorinilauri81
[giles74]: ../sources.md#giles74
[bollobas90]: ../sources.md#bollobas90
[muller77]: ../sources.md#muller77
[lovasz72]: ../sources.md#lovasz72
[nashwilliams78]: ../sources.md#nashwilliams78
[stockmeyer77]: ../sources.md#stockmeyer77
[stockmeyer81]: ../sources.md#stockmeyer81
[laurisc16]: ../sources.md#laurisc16
[mckay97]: ../sources.md#mckay97
