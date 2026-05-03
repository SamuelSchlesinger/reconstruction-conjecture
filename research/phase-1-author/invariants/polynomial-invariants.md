# Polynomial Invariants

Several graph polynomials — the chromatic polynomial, the Tutte
polynomial, the matching polynomial, the characteristic polynomial —
encode global structural information. Many (but not all!) are
reconstructible. The landmark paper is Tutte's 1979 "All the king's
horses" [tutte79][tutte79].

Parent: [index.md](index.md). See also
[spectral-invariants.md](spectral-invariants.md) for the adjacency
characteristic polynomial.

## Chromatic polynomial $P(G, k)$

The chromatic polynomial $P(G, k)$ counts proper $k$-colourings of $G$.
By Whitney's theorem,
$$P(G, k) \;=\; \sum_{F \subseteq G} (-1)^{|E(F)|} k^{c(F)},$$
where the sum is over spanning subgraphs $F$ (same vertex set, subsets
of edges) and $c(F)$ is the number of connected components of $F$.

### Reconstructibility

> **Theorem (Tutte 1979).** $P(G, k)$ is reconstructible.

**Idea.** Write $P(G, k) = \sum_{i=0}^n a_i(G)\,k^i$. Each coefficient
$a_i(G)$ is a signed count of spanning subgraphs with a fixed number of
components. Using the **Broken Circuit Theorem** (Whitney) or the direct
expansion, $a_i(G)$ is expressible as a $\mathbb{Z}$-linear combination
of subgraph counts $N(F, G)$ for **non-spanning** $F$ — specifically,
$F$ running over all isomorphism classes of graphs on strictly fewer
than $n$ vertices, weighted by how they sit inside spanning subgraphs
(see Bondy [bondy91][bondy91, §4]).

Alternatively: the chromatic polynomial equals (up to substitution) a
specialization of the Tutte polynomial, $P(G, k) = (-1)^{r(G)} k^{c(G)} T(G; 1-k, 0)$,
so reconstructibility of $T$ implies reconstructibility of $P$. But the
direct argument via subgraph counts on $< n$ vertices is cleaner for
formalization purposes.

**Consequence: chromatic number.** Since $P(G, k)$ is reconstructible,
and $\chi(G) = \min \{k \in \mathbb{Z}_{\ge 1} : P(G, k) > 0\}$, the
chromatic number $\chi(G)$ is reconstructible.

## Tutte polynomial $T(G; x, y)$

The Tutte polynomial is the two-variable specialization
$$T(G; x, y) \;=\; \sum_{F \subseteq E(G)} (x - 1)^{r(E) - r(F)} (y - 1)^{|F| - r(F)},$$
where $r(F)$ is the rank (number of vertices minus number of components
of the spanning subgraph on edge set $F$). It unifies many enumerative
invariants: $T(G; 1, 1) = \tau(G)$ (# spanning trees) for a connected
graph, $T(G; 2, 1)$ counts spanning forests, $T(G; 1, 2)$ counts spanning
connected subgraphs, and specializations recover the chromatic and flow
polynomials.

### Status: reconstructible?

Tutte [tutte79][tutte79] claimed that the Tutte polynomial is
reconstructible. The claim has been re-examined by several authors.
The current state of the literature:

* **Proved reconstructible:** All coefficients of $T(G; x, y)$ that
  correspond to non-spanning subgraph configurations. In particular,
  *every specialization that can be written as a signed sum of subgraph
  counts on $< n$ vertices* is reconstructible by Kelly's Lemma.
* **Claimed reconstructible (Tutte 1979):** the entire polynomial.
* **Caveat:** There have been subsequent clarifications; the claim is
  widely accepted but the cleanest self-contained write-up is in Bondy
  [bondy91][bondy91] and the Tutte polynomial survey by Brylawski and
  Oxley [brylawskioxley92][brylawskioxley92]. Whether every step of
  Tutte's original argument has been fully verified in modern notation —
  and whether any edge case requires separate treatment — should be
  double-checked against primary sources before claiming "Tutte poly is
  reconstructible, QED." (Flag this as a **formalization subproject**:
  it would be valuable to either fully formalize or find a gap.)

### What follows from Tutte-polynomial reconstructibility

* Number of spanning trees $\tau(G) = T(G; 1, 1)$. (Also derivable
  spectrally — see [spectral-invariants.md](spectral-invariants.md).)
* Number of acyclic orientations (Stanley): $|a(G)| = (-1)^{|V|} T(G; -1, 0) \cdot \operatorname{sign}$.
* Reliability polynomial.
* Flow polynomial.

## Matching polynomial

$$\mu(G, x) \;=\; \sum_{k \ge 0} (-1)^k m_k(G)\,x^{n - 2k},$$
where $m_k(G)$ is the number of $k$-matchings of $G$ (sets of $k$
pairwise-disjoint edges).

* **Reconstructibility.** Each $m_k(G)$ for $k < n/2$ is a count of
  subgraphs on $2k < n$ vertices (namely, disjoint unions of $k$ edges),
  so is a subgraph count. Kelly's Lemma applies, and the entire matching
  polynomial is reconstructible **except possibly at** $k = n/2$ (perfect
  matchings when $n$ is even).
* **Perfect matching count.** The number of perfect matchings is a
  spanning-subgraph count; reconstructibility requires an additional
  argument. It is reconstructible via Tutte's char-polynomial argument
  for bipartite graphs (permanent ↔ determinant link) and by the
  matching-polynomial's relation to the char. polynomial for forests,
  but the general case uses spectral methods.

## Independence polynomial, clique polynomial

$$I(G, x) \;=\; \sum_k i_k(G)\,x^k, \qquad C(G, x) \;=\; \sum_k c_k(G)\,x^k,$$
where $i_k$ is the number of independent sets of size $k$ and $c_k$ the
number of cliques of size $k$. Since $i_k$ (resp. $c_k$) for $k < n$ is a
subgraph count in the obvious sense (independent set of size $k$ $\iff$
induced copy of $\overline{K_k}$), Kelly's Lemma makes these
reconstructible except at the top: $i_n(G) \in \{0, 1\}$ records whether
$G$ has no edges, and $c_n(G) \in \{0, 1\}$ records whether $G = K_n$.
Both top coefficients are trivially reconstructible (from $n$ and the
edge count).

## Characteristic polynomial

Reconstructible — see [spectral-invariants.md](spectral-invariants.md).

## Summary table

| Polynomial | Reconstructible? | Route |
|-----------|------------------|-------|
| $P(G, k)$ chromatic | yes | Whitney expansion → subgraph counts ($<n$) |
| $T(G; x, y)$ Tutte | claimed (Tutte 1979), standard | deletion–contraction + subgraph counts |
| $\mu(G, x)$ matching | yes modulo perfect matching term | $k$-matching counts |
| adjacency $\phi(G, x)$ | yes | Tutte 1979 derivative identity |
| Laplacian $\mu(G, x)$ | yes | Kelmans / Tutte |
| independence $I(G, x)$ | yes | trivial |
| clique $C(G, x)$ | yes | trivial |

## Polynomials NOT known to be reconstructible

No natural widely-studied graph polynomial is known to be
**non-reconstructible**. The open questions are more about **finer
invariants** that are not polynomials: genus, treewidth, cop number,
graph entropy, specific embedding counts on surfaces other than $S^2$.

## Formalization notes

The easiest polynomial-reconstruction target for Lean is:

1. **Chromatic polynomial.** Formalize Whitney's expansion
   $P(G, k) = \sum_F (-1)^{|E(F)|} k^{c(F)}$ and then notice that every
   $F$ is a spanning subgraph — but the coefficient $a_i(G)$, being a
   count of spanning forests with $i$ components, can be rewritten using
   inclusion-exclusion as a signed sum over **non-spanning** subgraph
   counts. This latter rewriting is the non-trivial step. Then Kelly's
   Lemma delivers.

2. **Matching polynomial up to $k < n/2$.** Trivial once Kelly's Lemma
   is in place; the matching count $m_k$ is literally a subgraph count.

3. **Tutte polynomial.** Harder. Requires either the full deletion–
   contraction recursion machinery (and careful handling of loops /
   multi-edges if moving outside simple graphs) or a conversion to
   subgraph-count sums.

[tutte79]: ../sources.md#tutte79
[bondy91]: ../sources.md#bondy91
[brylawskioxley92]: ../sources.md#brylawskioxley92
