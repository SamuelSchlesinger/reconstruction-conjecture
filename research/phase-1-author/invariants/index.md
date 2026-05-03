# Reconstructible Invariants

A graph parameter $\pi$ is **reconstructible** when $\pi(G)$ is determined by
the deck $\mathcal{D}(G) = \{\!\{G-v : v \in V(G)\}\!\}$ (a multiset of
unlabelled graphs). Equivalently, whenever $\mathcal{D}(G) = \mathcal{D}(H)$
we must have $\pi(G) = \pi(H)$. In symbols, $\pi$ is reconstructible iff
$\pi$ factors through the deck-equivalence relation on graphs of fixed order
$n \ge 2$ (or $\ge 3$, depending on convention).

The Kelly–Ulam **Reconstruction Conjecture** asserts that the isomorphism
class itself is reconstructible for all graphs with $n \ge 3$ vertices; a
major project of the field has been to show that more and more structural
invariants are reconstructible, chipping away at what a hypothetical
counterexample could look like.

This page tabulates the key invariants, their reconstructibility status,
and the technique used. Detail pages are linked where useful. For a higher
level overview see [../state-of-the-art/index.md](../state-of-the-art/index.md);
for attack strategies see [../attacks/index.md](../attacks/index.md); for
Lean 4 formalization status see [../formalization/index.md](../formalization/index.md).

## Summary table

| Invariant | Reconstructible? | Technique | Primary reference |
|-----------|------------------|-----------|-------------------|
| Vertex count $n = \|V(G)\|$ | yes | trivial (size of deck) | folklore |
| Edge count $m = \|E(G)\|$ | yes | $m = \tfrac{1}{n-2}\sum_v m(G-v)$ | Kelly 1957 [kelly57][kelly57] |
| Degree sequence | yes | $\deg_G(v) = m - m(G-v)$ | Kelly 1957 [kelly57][kelly57] |
| Induced-subgraph count $s(F,G)$ for $\|V(F)\| < n$ | yes | Kelly's Lemma (double counting) | Kelly 1957 [kelly57][kelly57] |
| Subgraph count (spanning not allowed) | yes | dual form via Möbius / Bondy | Bondy 1969/1991 [bondy91][bondy91] |
| Number of components | yes | disconnected-graph theorem | Kelly 1957; Harary 1964 [harary64][harary64] |
| Being disconnected | yes | same | Kelly 1957 [kelly57][kelly57] |
| Connectivity of $G$ when connected | yes (as a Yes/No) | follows from component count | Bondy–Hemminger 1977 [bondyhemminger77][bondyhemminger77] |
| Being a tree (and which tree, for $n \ge 3$) | yes | Kelly 1957 (trees reconstructible) | Kelly 1957 [kelly57][kelly57] |
| Number of spanning trees $\tau(G)$ | yes | from char. polynomial of Laplacian / Kelly counts | Tutte 1979 [tutte79][tutte79] |
| Characteristic polynomial $\phi(G,x)$ of adjacency matrix | yes | $\phi'(G,x) = \sum_v \phi(G-v,x)$ + Newton | Tutte 1979 [tutte79][tutte79]; Cvetković–Doob–Sachs [cds80][cds80] |
| Spectrum (as multiset of eigenvalues) | yes | determined by $\phi(G,x)$ | Tutte 1979 [tutte79][tutte79] |
| Laplacian characteristic polynomial | yes | analogous derivative identity | Tutte 1979 [tutte79][tutte79]; Kelmans [kelmans65][kelmans65] |
| Number of perfect matchings | yes | specialization of subgraph count / Tutte | Tutte 1979 [tutte79][tutte79] |
| Number of Hamiltonian cycles | yes (if $n$ large enough so $C_n$ not spanning-relevant) | subgraph-count, but $C_n$ is spanning so needs care | see [kellys-lemma.md](kellys-lemma.md) |
| Chromatic polynomial $P(G,k)$ | yes | coefficient-wise, via subgraph counts | Tutte 1979 [tutte79][tutte79] |
| Tutte polynomial $T(G;x,y)$ | claimed reconstructible | deletion–contraction + subgraph expansion | Tutte 1979 [tutte79][tutte79]; see [polynomial-invariants.md](polynomial-invariants.md) |
| Genus | unknown | — | open |
| Planarity | known for $n \ge 11$ (edge-reconstructible) | Lauri, others | [lauri82][lauri82] |
| Hamiltonicity | unknown in general | — | open |
| Girth | yes (when girth $\le n-1$) | subgraph count of shortest cycle | Manvel 1969 [manvel69][manvel69] |
| Diameter | partial results only | — | open in general |
| Automorphism group | unknown | — | open |

A note on convention: throughout, "reconstructible" means **deck-reconstructible**
from the vertex-deleted deck. *Edge reconstruction* is a separate, weaker
notion (decks of $G-e$). Results for edge reconstruction are not included
here unless explicitly noted.

## Detail pages

* [Kelly's Lemma](kellys-lemma.md) — the counting workhorse and its proof
* [Spectral invariants](spectral-invariants.md) — char. polynomial, Laplacian,
  eigenvalues, spanning trees
* [Polynomial invariants](polynomial-invariants.md) — chromatic polynomial,
  Tutte polynomial, matching polynomial

## Formalization difficulty (rough)

| Invariant | Ease in Lean/Mathlib | Why |
|-----------|----------------------|-----|
| Edge count, degree sequence | Easy | one-line identities over finite sums |
| Induced-subgraph count (Kelly) | Easy–medium | pure double counting; only needs `Finset`, `Sym2`, and `Iso` |
| Number of components | Medium | needs a reconstruction of "being disconnected" as a predicate on decks |
| Spanning trees $\tau(G)$ | Medium–hard | Matrix-Tree theorem is in Mathlib but plugging it into the deck argument is fiddly |
| Char. polynomial $\phi(G,x)$ | Hard | needs polynomial derivative identity **and** Newton's identities to recover low-degree coefficients |
| Chromatic polynomial | Medium | expressible as a finite sum of subgraph counts (Whitney) |
| Tutte polynomial | Hard | intertwines deletion–contraction with subgraph counts; proof in literature is non-trivial |

The "constructive counting" proofs — Kelly's Lemma and its direct corollaries
— are the most attractive Lean targets because they reduce to
`Finset.sum_bij`-style combinatorial identities. The spectral proofs require
running through Newton's identities (or Faddeev–LeVerrier) as a separate
algebraic layer.

## $k$-reconstructibility

For $k \ge 1$ the **$k$-deck** of $G$ is the multiset
$\mathcal{D}_k(G) = \{\!\{G[S] : S \in \binom{V(G)}{n-k}\}\!\}$ of all induced
subgraphs obtained by deleting $k$ vertices. The usual deck is $\mathcal{D}_1$.
A graph is **$k$-reconstructible** if $G$ is determined up to isomorphism by
$\mathcal{D}_k(G)$, and an invariant is $k$-reconstructible if it is
determined by $\mathcal{D}_k(G)$. Larger $k$ gives *less* information
(smaller subgraphs), so it is a genuinely stronger requirement.

Known facts:

* Manvel [manvel74][manvel74] showed that trees on $n$ vertices are
  $k$-reconstructible for $k \le \tfrac12(n-3)$ (roughly).
* Nýdl [nydl90][nydl90] showed that arbitrary graphs are **not**
  $k$-reconstructible for $k \ge c \sqrt{n}$.
* Kostochka and West and others have studied the threshold more precisely;
  the best general bounds are still far from tight. See
  [../state-of-the-art/index.md](../state-of-the-art/index.md).

Separately, **$n$-reconstructibility** (in Harary's sense) asks which
invariants are determined by the size of the deck alone; this is
essentially trivial. We do not discuss it further.

## Invariants NOT known to be reconstructible

These are the frontier parameters — proving any of them reconstructible
without using the full conjecture would be a genuine result.

* **Automorphism group** $\mathrm{Aut}(G)$. Its *order* is conjectured
  reconstructible (and would follow from the full conjecture), but no deck
  argument is known. See [../attacks/index.md](../attacks/index.md).
* **Hamiltonicity.** Counts of Hamiltonian cycles on $n$ vertices require a
  spanning-subgraph-count argument that Kelly's Lemma does **not** give.
* **Chromatic number** $\chi(G)$. The chromatic polynomial is reconstructible
  (Tutte), and $\chi(G) = \min\{k : P(G,k) > 0\}$, so this *is* in fact
  reconstructible. [tutte79][tutte79] The misconception that it is not is
  common; we flag it here.
* **Genus / embeddability on higher surfaces.** Even planarity is only
  known for large $n$.
* **Diameter** in general: partial results, not a full reconstruction proof.
* **Crossing number.**
* **Treewidth, pathwidth, rankwidth.**
* **Graph entropy.**
* **Cop number.**

A separate useful list: invariants that are **edge-reconstructible** (from
the edge deck) but whose vertex-deck reconstructibility is easier or
harder. See [polynomial-invariants.md](polynomial-invariants.md).

## Validation artifacts

See `data/`:

* [`data/kelly_small.py`](data/kelly_small.py) — brute-force verification of
  Kelly's Lemma on all graphs on 5 vertices for one choice of $F$.
* [`data/charpoly_deck.py`](data/charpoly_deck.py) — brute-force
  verification that $\phi'(G,x) = \sum_v \phi(G-v,x)$ on small graphs.
* [`data/kelly_small_output.txt`](data/kelly_small_output.txt) and
  [`data/charpoly_deck_output.txt`](data/charpoly_deck_output.txt) — sample
  runs.

[kelly57]: ../sources.md#kelly57
[bondy91]: ../sources.md#bondy91
[tutte79]: ../sources.md#tutte79
[harary64]: ../sources.md#harary64
[bondyhemminger77]: ../sources.md#bondyhemminger77
[cds80]: ../sources.md#cds80
[kelmans65]: ../sources.md#kelmans65
[manvel69]: ../sources.md#manvel69
[manvel74]: ../sources.md#manvel74
[nydl90]: ../sources.md#nydl90
[lauri82]: ../sources.md#lauri82
