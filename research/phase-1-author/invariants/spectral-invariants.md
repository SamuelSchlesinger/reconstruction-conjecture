# Spectral Invariants

Spectral invariants of a graph $G$ — those derived from the adjacency
matrix $A(G)$ or the Laplacian $L(G) = D(G) - A(G)$ — are among the most
delicate reconstructible invariants, because their definitions do not
obviously reduce to counts of small subgraphs. The central result is:

> **Theorem (Tutte 1979).** The characteristic polynomial
> $\phi(G, x) = \det(xI - A(G))$ of the adjacency matrix is
> reconstructible.

Hence the spectrum (multiset of eigenvalues of $A(G)$) is reconstructible.
The same technique reconstructs the Laplacian characteristic polynomial,
and with it the number of spanning trees $\tau(G)$.

Parent: [index.md](index.md).

## What "reconstructible polynomial" means precisely

$\phi(G, x) \in \mathbb{Z}[x]$ is a polynomial of degree $n = |V(G)|$.
Formally, the invariant $G \mapsto \phi(G, x)$ takes values in $\mathbb{Z}[x]$.
"Reconstructible" means: whenever $\mathcal{D}(G) = \mathcal{D}(H)$, the
polynomials $\phi(G, x)$ and $\phi(H, x)$ are equal as elements of
$\mathbb{Z}[x]$. Equivalently, each coefficient $c_i(G)$ of $\phi(G, x)$
is a reconstructible integer invariant.

## The derivative identity

The key identity, due independently to several authors but the earliest
proof attributed to [Schwenk][schwenk74] and used centrally by
[Tutte][tutte79]:

> **Derivative Lemma.** For every simple graph $G$ on $n$ vertices,
> $$\frac{\partial}{\partial x} \phi(G, x) \;=\; \sum_{v \in V(G)} \phi(G - v,\; x).$$

**Proof sketch.** Expand $\det(xI - A)$ using the cofactor expansion
along the "$x$ on the diagonal" structure:
$$\phi(G, x) \;=\; \det(xI - A) \;=\; \sum_{\sigma \in S_n} \operatorname{sgn}(\sigma) \prod_{i} (xI - A)_{i, \sigma(i)}.$$

Differentiate with respect to $x$: by the product rule, each term becomes
a sum over the index $j$ where we differentiate the $j$-th factor. This
turns out to equal $\sum_j \det((xI - A)^{(j)})$, where $(xI - A)^{(j)}$
is the matrix with the $j$-th row and $j$-th column deleted. But
$(xI - A)^{(j)} = xI' - A(G - j)$ where $I'$ is the identity of the
right size. So $\det((xI-A)^{(j)}) = \phi(G - j, x)$, and the claim
follows. $\square$

A cleaner, more modern phrasing is: differentiating the determinant of
$xI - A$ in $x$ is the same as summing the principal minors of $xI - A$
obtained by deleting one row/column, and each such principal minor is
the char. polynomial of the vertex-deleted graph.

## Reconstructing $\phi(G, x)$ from the deck

Given the deck $\mathcal{D}(G) = \{G - v_1, \ldots, G - v_n\}$, the sum
$\sum_v \phi(G - v, x)$ is determined by the deck (it does not depend on
the labelling of which card is which $v$ — it is a sum over cards). By
the derivative identity, this sum is $\phi'(G, x)$.

Integrating in $x$: $\phi(G, x) = \int_0^x \phi'(G, t)\,\mathrm{d}t + \phi(G, 0)$.

The coefficients of $\phi(G, x)$ of *positive* degree are recovered
directly from $\phi'(G, x)$. The only missing piece is the **constant
term** $\phi(G, 0) = \det(-A(G)) = (-1)^n \det(A(G))$. So it remains to
show $\det(A(G))$ is reconstructible.

### The constant term

There are two standard ways to recover the constant term $(-1)^n \det A(G)$:

1. **Trace via Newton's identities.** The power sums
   $p_k(G) = \sum_i \lambda_i^k = \operatorname{tr}(A(G)^k)$ for
   $1 \le k \le n$ determine the elementary symmetric polynomials in the
   eigenvalues, hence the coefficients of $\phi(G, x)$, including the
   constant term $e_n = \lambda_1 \cdots \lambda_n = \det A(G) \cdot (-1)^n / (-1)^n$
   — one needs to track signs carefully, but the point is that Newton's
   identities are invertible as long as we are working in characteristic
   $0$.

   The traces $\operatorname{tr}(A(G)^k)$ themselves are reconstructible:
   $\operatorname{tr}(A(G)^k)$ equals the number of closed walks of length
   $k$ in $G$, which is a sum over pairs $(v, W)$ of walks starting and
   ending at $v$. For $k < n$, one can reduce the count of closed
   $k$-walks to a subgraph count (walks land in at most $k < n$ vertices)
   and apply Kelly's Lemma. For $k = n$, closed walks may hit all
   vertices; this is the hard case.

2. **Direct from the derivative.** Actually, since we are working in
   $\mathbb{Z}[x]$ and $\phi(G, x)$ has degree $n$ with leading coefficient
   $1$, the derivative $\phi'(G, x)$ has degree $n - 1$ and
   **only the coefficients of $x^0, x^1, \ldots, x^{n-1}$ of $\phi(G,x)$
   are recoverable from $\phi'$**. Wait — $\phi(G, x)$'s coefficient of
   $x^k$ appears as $k \cdot [\text{coef of } x^{k-1}] \phi'$, so **every**
   coefficient of $\phi$ *except* the constant term is recovered. The
   leading term is always $1$ (monic), so we know it from $n$ alone. The
   constant term is the remaining unknown.

   Tutte's original approach is to combine the derivative identity with
   a separate reconstruction of $\det A(G)$ via a count of permanent-like
   expansions that do reduce to subgraph counts on $< n$ vertices. The
   cleanest modern write-up is in Cvetković–Doob–Sachs [cds80][cds80,
   Chapter 1].

Either way: **$\phi(G, x)$ is reconstructible**, and with it the spectrum.

## Newton's identities and Faddeev–LeVerrier

The algebraic link between traces $p_k = \operatorname{tr}(A^k)$ and
coefficients $e_k$ (elementary symmetric polynomials in the eigenvalues
= signed coefficients of $\phi$) is **Newton's identities**:

$$p_k - e_1 p_{k-1} + e_2 p_{k-2} - \cdots + (-1)^{k-1} e_{k-1} p_1 + (-1)^k k e_k = 0,
\qquad 1 \le k \le n.$$

Solving recursively: $e_k = \frac{1}{k}\bigl(p_k - e_1 p_{k-1} + \cdots \bigr)$.

The **Faddeev–LeVerrier algorithm** is the matrix form of this:
starting from $M_0 = I$, $c_n = 1$, it recursively sets
$c_{n-k} = -\tfrac{1}{k} \operatorname{tr}(A M_{k-1})$ and
$M_k = A M_{k-1} + c_{n-k} I$. This writes each coefficient of $\phi$ as
a polynomial in traces $\operatorname{tr}(A^j)$ for $j \le k$.

So **if** all traces $\operatorname{tr}(A^k)$ are reconstructible for
$1 \le k \le n$, then $\phi(G, x)$ is reconstructible, no derivative
identity needed. The subtlety is the $k = n$ trace, as noted above.

### Why Newton's identities are the right tool

Newton's identities are invertible over any ring containing $\mathbb{Q}$
(equivalently, in characteristic $0$ or characteristic $> n$). For
integer graphs they give integer coefficients because $\phi$ has integer
coefficients; the rationals appear only as an artifact of the recursion.

## Reconstructing the Laplacian characteristic polynomial

The Laplacian $L(G) = D(G) - A(G)$ (degree matrix minus adjacency) has
characteristic polynomial $\mu(G, x) = \det(xI - L(G))$. The same
derivative-plus-Newton argument, using
$\mu'(G, x) = \sum_v \mu(G - v, x) + \text{correction terms}$,
works — but with a correction because deleting a vertex from $G$ changes
the diagonal of $L(G)$ (the degrees of the remaining vertices drop for
each edge to the deleted vertex). The precise form of the derivative
identity for $\mu$ is slightly more complex and was worked out by
Kelmans [kelmans65][kelmans65] and Tutte [tutte79][tutte79].

## Reconstructibility of $\tau(G)$

By the **Matrix-Tree theorem** (Kirchhoff), the number of spanning trees
$\tau(G)$ equals any cofactor of $L(G)$, i.e., $\tau(G) = \tfrac{1}{n}\lambda_2 \cdots \lambda_n$
where $0 = \lambda_1 \le \lambda_2 \le \cdots \le \lambda_n$ are the
Laplacian eigenvalues. Since $\mu(G, x)$ is reconstructible, so is the
multiset of Laplacian eigenvalues, so is $\tau(G)$.

Hence: **the number of spanning trees is reconstructible**, despite
spanning trees being spanning subgraphs to which Kelly's Lemma does not
directly apply. The spectral detour is essential.

## Summary of techniques

| Invariant | Route | Ingredient |
|-----------|-------|-----------|
| Closed walk counts $\operatorname{tr}(A^k)$, $k < n$ | Kelly's Lemma applied to subgraphs on walk vertex support | pure combinatorics |
| $\operatorname{tr}(A^n)$ | separate argument (Tutte) | combinatorial + algebraic |
| Coefs $c_1, \ldots, c_{n-1}$ of $\phi$ | derivative identity | calculus + determinant expansion |
| Coef $c_0 = \phi(G, 0)$ | Newton / determinant count | linear algebra |
| Spectrum $\{\lambda_i\}$ | from $\phi$ | algebra |
| Laplacian spectrum | analogous derivative identity for $\mu$ | algebra |
| $\tau(G)$ | Matrix-Tree + Laplacian spectrum | Kirchhoff |
| # perfect matchings (for bipartite) | permanent / matching polynomial | algebra |
| # closed walks of length $k$ | $\operatorname{tr}(A^k)$ | linear algebra |

## Formalization difficulty

The derivative identity $\phi'(G, x) = \sum_v \phi(G - v, x)$ is clean —
it is an identity in $\mathbb{Z}[x]$ or $\mathrm{Polynomial}\,R$ for any
commutative ring $R$ — but formalizing it in Lean requires the
"differentiation of a determinant" lemma, which at the time of writing
is present in Mathlib but scattered. The Lean project has
`Reconstruction.CharPolyFull` and `Reconstruction.Spectral` pursuing this.

The Newton-identity / Faddeev–LeVerrier step is a separate algebraic
exercise and lives in `Reconstruction.Newton`.

The `Reconstruction.TraceReconstruction` module reconstructs low-degree
traces via Kelly's Lemma applied to closed-walk subgraph counts.

## Validation

See [`data/charpoly_deck.py`](data/charpoly_deck.py) for a sympy-based
verification that, for every simple graph on up to 6 vertices,
$\phi'(G, x) = \sum_v \phi(G - v, x)$.

[tutte79]: ../sources.md#tutte79
[cds80]: ../sources.md#cds80
[kelmans65]: ../sources.md#kelmans65
[schwenk74]: ../sources.md#schwenk74
