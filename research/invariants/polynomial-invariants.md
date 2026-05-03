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

### Status: reconstructible

> **Theorem (Tutte 1979).** The Tutte polynomial $T(G; x, y)$ is
> reconstructible.

Concretely, the equivalent **rank polynomial**
$R(G; u, v) = \sum_{F \subseteq E(G)} u^{r(E) - r(F)} v^{|F| - r(F)}$
is reconstructible, and the Tutte polynomial is the affine change of
variables $T(G; x, y) = R(G; x - 1, y - 1)$. The reconstruction has two
ingredients:

1. **Non-spanning contribution.** Every rank-polynomial coefficient
   corresponding to a subgraph of strictly fewer than $n$ vertices is a
   signed sum of subgraph counts $N(F, G)$ for $|V(F)| < n$, hence
   reconstructible by Kelly counting.
2. **Spanning-term reduction.** The spanning contributions
   (coefficients involving subgraphs on all $n$ vertices) are recovered
   from the non-spanning ones via a deletion–contraction / generating-
   function identity — essentially, the full polynomial is determined by
   its non-spanning part together with the total number of edges, the
   number of spanning trees (reconstructible spectrally), and the
   connectivity pattern.

This is the classical argument of Tutte [tutte79][tutte79], presented
in modern notation in Bondy's survey [bondy91][bondy91, §5]. A
contemporary self-contained account appears in the Tutte-polynomial
chapter of Brylawski and Oxley [brylawskioxley92][brylawskioxley92].

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

* **Reconstructibility (coefficient-wise).** Each $m_k(G)$ for
  $k < n/2$ is a count of subgraphs on $2k < n$ vertices (namely,
  disjoint unions of $k$ edges), so is a subgraph count. Kelly's Lemma
  applies, and every coefficient of $\mu(G, x)$ below the perfect-
  matching coefficient is reconstructible.
* **Full matching polynomial (Farrell–Wahid 1987).** Farrell and Wahid
  [farrellwahid87][farrellwahid87] reconstruct $\mu(G, x)$ in full by a
  direct counting argument: they show that the perfect-matching
  coefficient $m_{n/2}(G)$ (when $n$ is even) is itself determined by
  the deck via a Kelly-style identity on pairs (matching, vertex)
  modified to account for spanning configurations. Their proof does
  **not** go through the adjacency characteristic polynomial.
* **Forest case, via Godsil.** Godsil [godsil81][godsil81] proved that
  for a **forest** $G$, the matching polynomial coincides with the
  adjacency characteristic polynomial: $\mu(G, x) = \phi(G, x)$. In the
  forest case therefore matching-polynomial reconstructibility follows
  immediately from charpoly reconstructibility (Tutte 1979); no
  separate argument is needed.
* **Perfect matching count.** In particular the number of perfect
  matchings, $m_{n/2}(G)$, is reconstructible: it is a coefficient of
  the matching polynomial.

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
| $T(G; x, y)$ Tutte | yes | Tutte 1979: non-spanning rank coefs via Kelly + spanning-term reduction |
| $\mu(G, x)$ matching | yes | Farrell–Wahid 1987 (direct counting); Godsil 1981 for forests via charpoly |
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
[farrellwahid87]: ../sources.md#farrellwahid87
[godsil81]: ../sources.md#godsil81
