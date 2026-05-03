# Kelly's Lemma

**Kelly's Lemma** is the workhorse of reconstruction theory. Every
"counting-type" invariant (edge count, degree sequence, triangle count,
4-cycles, …) is reconstructible as a consequence. The lemma appears in
Kelly's 1942 thesis and was published in 1957 [kelly57][kelly57]; the form
used in modern treatments is due to Bondy [bondy91][bondy91].

Parent page: [index.md](index.md).
See also [../attacks/counting-approach.md](../attacks/counting-approach.md)
for strategic use of Kelly counting in attacks on the full conjecture.

## Statement (induced form)

For a graph $F$, write $s(F, G)$ for the number of induced copies of $F$
in $G$, i.e., the number of $k$-element vertex subsets
$S \subseteq V(G)$ with $k = |V(F)|$ such that the induced subgraph
$G[S]$ is isomorphic to $F$.

> **Kelly's Lemma (1957).** Let $G$ and $H$ be graphs with $n \ge 2$
> vertices and equal deck. Then for every graph $F$ with $|V(F)| < n$,
>
> $$s(F, G) = s(F, H).$$

Equivalently, $s(F, \cdot)$ is a reconstructible invariant for every $F$
with $|V(F)| < n$.

## Proof sketch (constructive double counting)

Let $k = |V(F)| < n$. Count pairs
$(S, v)$ where $S \in \binom{V(G)}{k}$, $G[S] \cong F$, and $v \in V(G) \setminus S$.

* **Count by $S$ first.** Each good $S$ has exactly $n - k$ choices of
  $v \notin S$. So the number of pairs is $(n-k) \cdot s(F, G)$.
* **Count by $v$ first.** Fix $v$. The good pairs with this $v$ are exactly
  the induced copies of $F$ in $G - v$. So the count is $s(F, G-v)$.

Combining:
$$(n - k)\,s(F, G) \;=\; \sum_{v \in V(G)} s(F, G - v).$$

Since $k < n$, we have $n - k \ne 0$, so
$$s(F, G) \;=\; \frac{1}{n - k} \sum_{v \in V(G)} s(F, G - v).$$

The right-hand side depends only on the deck $\mathcal{D}(G)$
(the multiset of cards $G-v$, which is what "same deck" means): each
$s(F, G-v)$ is a graph invariant of $G-v$, summed over the cards. $\square$

This is a *constructive* argument: given the deck, you compute each
$s(F, G-v)$ from its card, sum, and divide by $n-k$. No existential or
algebraic machinery is invoked.

## Subgraph-count (spanning-subgraph) form due to Bondy

Let $N(F, G)$ be the number of subgraphs of $G$ isomorphic to $F$ (not
necessarily induced; *subgraph* meaning any $F' \subseteq G$ with
$F' \cong F$, where $V(F') \subseteq V(G)$ and $E(F') \subseteq E(G)$).
Kelly's Lemma implies the same identity for $N$:

$$(n - k)\,N(F, G) \;=\; \sum_{v \in V(G)} N(F, G - v),$$

provided $|V(F)| = k < n$. The relation between the induced count
$s(\cdot, G)$ and the not-necessarily-induced count $N(\cdot, G)$ is a
Möbius inversion on the subgraph poset: for each $F$ on $k$ vertices,

$$N(F, G) \;=\; \sum_{F' : V(F') = V(F),\; F' \supseteq F} s(F', G),$$

where the sum ranges over labelled supergraphs $F'$ on the same vertex
set as $F$ (i.e. $F'$ contains $F$ edge-wise), and conversely

$$s(F, G) \;=\; \sum_{F' : V(F') = V(F),\; F' \supseteq F} \mu(F, F')\, N(F', G),$$

where $\mu$ is the Möbius function of the subgraph lattice on $[k]$.
Both directions hold at the level of labelled subgraphs and then descend
to isomorphism classes by summing over automorphism orbits. In either
direction, when $|V(F)| < n$, the right-hand side is a finite
$\mathbb{Z}$-linear combination of reconstructible quantities, so the
left-hand side is reconstructible. Hence the two forms ($s$ and $N$) are
equivalent as reconstruction statements, both attributed in modern form
to Bondy [bondy91][bondy91, §3].

## Kocay's Lemma

Kocay [kocay81][kocay81] gave a substantial generalization of Kelly's
counting argument to *ordered tuples* of subgraphs. In its simplest
form: fix graphs $F_1, \ldots, F_r$ with $\sum_i |V(F_i)| < n$ and a
prescribed intersection pattern (specifying how the vertex sets of the
copies are allowed to overlap). Then the number of ordered tuples
$(H_1, \ldots, H_r)$ of induced subgraphs of $G$ with $H_i \cong F_i$
and the given overlap pattern is reconstructible. The proof again
proceeds by a double-counting identity over a vertex $v$ not in the
union $\bigcup_i V(H_i)$, which is nonempty precisely because the total
number of vertices covered is $< n$. Kocay's Lemma is the basis for
several reconstruction results that do not follow from Kelly's Lemma
alone — notably reductions involving counts of pairs of subgraphs with
controlled intersection. See [../attacks/counting-approach.md](../attacks/counting-approach.md).

Formalization status: `Reconstruction/Kocay.lean` now contains a typed
finite-index version of the product-count identity. The theorem
`SimpleGraph.coverTypeCount_sum_inducedIsoClass` groups vertex-set covers
by the quotient of induced subgraphs up to isomorphism, giving the Lean
form of
$$\prod_i s(F_i,G)=\sum_X c((F_i),X)\,s(X,G).$$

### Why the bound $|V(F)| < n$ is sharp

If $F$ is a *spanning* subgraph — e.g. $F = C_n$ (Hamilton cycle) or $F$
a Hamilton path — then $k = n$ and $n - k = 0$, so the double-counting
argument gives $0 = 0$ and carries no information. This is precisely why
Hamiltonicity is **not** known to be reconstructible: you cannot count
Hamilton cycles with Kelly's Lemma.

The same obstacle applies to spanning trees (which is why Tutte's
reconstructibility of $\tau(G)$ uses the characteristic polynomial of the
Laplacian, not Kelly's Lemma directly).

## Consequences — the "counting" invariants

### Edge count

Apply Kelly's Lemma with $F = K_2$ (so $k = 2$):
$$m(G) \;=\; s(K_2, G) \;=\; \frac{1}{n - 2} \sum_v s(K_2, G - v)
    \;=\; \frac{1}{n - 2} \sum_v m(G - v).$$

A slicker direct proof: every edge $uv \in E(G)$ appears in $G - w$ for
$w \notin \{u, v\}$, i.e., in $n - 2$ cards. So
$\sum_v m(G - v) = (n - 2)\,m(G)$.

### Degree sequence

Each card $G - v$ has $m(G) - \deg_G(v)$ edges. Once $m(G)$ is known,
$\deg_G(v) = m(G) - m(G - v)$. The multiset of degrees
$\{\!\{\deg_G(v)\}\!\}$ is then determined by the deck (identifying the
card $G - v$ with the pair $(G - v, \deg_G(v))$).

However the **labelled** degree function $v \mapsto \deg_G(v)$ is **not**
reconstructible — the deck forgets the labels. Only the multiset is.

### Triangle count

$F = K_3$: $s(K_3, G) = \frac{1}{n-3} \sum_v s(K_3, G - v)$, and
$s(K_3, G - v)$ is a graph invariant of each card. So the number of
triangles is reconstructible.

### Counts of any small fixed subgraph

$F = P_3$ (path), $F = C_4$, $F = K_{2,2}$, etc. — all are reconstructible
subgraph counts when $|V(F)| < n$.

## Consequence — disconnected graphs are reconstructible

> **Theorem (Kelly 1957).** If $G$ is disconnected and has $n \ge 2$
> vertices, then $G$ is reconstructible.

**Sketch.** By Kelly's Lemma the count $N(F, G)$ is reconstructible for
every $F$ with $|V(F)| < n$. If $G$ is disconnected, then every component
of $G$ has strictly fewer than $n$ vertices, and one shows (by induction
on the number of components, using the generating function of connected
subgraph counts) that the isomorphism class of $G$ is determined by the
multiset of component isomorphism classes, which in turn is determined by
the subgraph counts $N(C, G)$ for connected $C$. Since each such $C$ has
$< n$ vertices, Kelly's Lemma applies. $\square$

A clean modern rendition is in Bondy [bondy91][bondy91, §3].

## Consequences — trees

Kelly used the same counting technique to show that **every tree on
$n \ge 2$ vertices is reconstructible**. The argument is an induction on
$n$ combined with a count of pendant (leaf) subtrees. The details are
more intricate than the disconnected case and are typically presented
separately.

## What Kelly's Lemma does NOT give

* Spanning-subgraph counts: Hamilton cycles, Hamilton paths, spanning
  trees (except via the indirect spectral route — see
  [spectral-invariants.md](spectral-invariants.md)).
* Non-counting invariants such as automorphism group structure,
  embeddability, genus.
* Any invariant whose definition requires comparing $G$ to a spanning
  object.

## Formalization status

The Lean 4 project in `graph-theory/reconstruction-conjecture/` has:

* `Reconstruction.KellyLemma` — the induced-subgraph counting form, with
  the double-counting identity $(n-k)\,s(F,G) = \sum_v s(F, G-v)$ and the
  reconstructibility conclusion.
* `Reconstruction.KellyEdgeCount` — specialization to $F = K_2$, edge
  count reconstructibility.
* `Reconstruction.DegreeSequence` — degree multiset.
* `Reconstruction.Disconnected` — disconnected graphs are reconstructible.
* `Reconstruction.Trees` — tree reconstructibility (in progress).

See [../formalization/index.md](../formalization/index.md) for the live
status.

[kelly57]: ../sources.md#kelly57
[bondy91]: ../sources.md#bondy91
[tutte79]: ../sources.md#tutte79
[kocay81]: ../sources.md#kocay81
