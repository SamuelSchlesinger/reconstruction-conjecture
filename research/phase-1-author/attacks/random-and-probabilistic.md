# Random and Probabilistic Approaches

## Bollobás 1990

Bollobás 1990 [bollobas90][bollobas90] proved that **almost every graph
is reconstructible from just three of its vertex-deleted cards**, chosen
uniformly at random from the deck. The precise statement: for
$G \sim \mathcal G(n, 1/2)$, with probability $1 - o(1)$ as $n \to \infty$,
any three cards suffice to determine $G$ up to isomorphism.

This is often summarized as the **reconstruction number** of a random
graph being at most $3$. In fact Bollobás's proof shows that, with high
probability, *every* triple of cards in the deck is enough: the graph is
reconstructible from any three cards.

The proof strategy:

1. In $\mathcal G(n, 1/2)$, with high probability every vertex is uniquely
   identified by its neighborhood pattern on a small set of "witness"
   vertices.
2. From three cards $G - u$, $G - v$, $G - w$ one can, with high
   probability, reconstruct the labels of all vertices (i.e. match up
   the copies of each vertex across cards).
3. Once vertex labels are aligned, the edges are determined by taking
   the "union" of the three cards minus the three missing vertices.

## Implications and limitations

- **Implication.** The conjecture holds for the measure-1 set of graphs
  in $\mathcal G(n, 1/2)$; the counterexamples, if any, live in a
  measure-0 family.
- **Limitation.** This does *not* prove the conjecture. Potential
  counterexamples are highly structured (regular, symmetric, cospectral,
  etc.) — exactly the graphs that $\mathcal G(n, 1/2)$ almost never
  produces. So probabilistic methods address the "easy" bulk but leave
  the hard cases untouched.
- **Reconstruction number.** For a specific $G$, the reconstruction
  number $\mathrm{rn}(G)$ is the minimum number of cards that determine
  $G$. Bollobás shows $\mathrm{rn}(G) \le 3$ a.s.; there exist graphs
  (e.g. $K_n$, $\overline{K_n}$, $C_n$, $P_n$) with $\mathrm{rn} = 3$,
  and some constructions reaching higher values, but known worst cases
  are bounded by small constants for each class.

## Refinements since Bollobás

- **Sparse random graphs.** For $\mathcal G(n, p)$ with $p = p(n) \to 0$,
  the analogous statements are known when $p$ is above the connectivity
  threshold $\log n / n$; below that, the deck inherits components
  whose multiplicity matters and the analysis is more delicate.
- **Random regular graphs.** Almost every $d$-regular graph is
  reconstructible; Kim–Sudakov, Krivelevich, and others have results
  along these lines (URLs/dates — verify).
- **Concentration of deck statistics.** McKay and others have shown
  that deck entropy concentrates; this is used to bound how much
  information is in the deck on average.

See [`../state-of-the-art/index.md`](../state-of-the-art/index.md) for
the current best quantitative bounds; the 3-card bound of Bollobás is
the headline, but tightenings exist in the constants and the
convergence rate.

## Limits of the probabilistic approach

The probabilistic method gives:

- Existence results: "most graphs have property X";
- Moments and concentration of deck-derived random variables;
- Lower bounds on the reconstruction number for adversarially chosen
  graph classes.

It does **not** give deterministic reconstruction for a named graph
class unless that class is itself "generic" in an appropriate measure.
In particular, it does not constrain any specific conjectural
counterexample.

## Lean formalization prospects

Mathlib's probability layer (`MeasureTheory`, `ProbabilityTheory`) can
formulate "almost every graph" as a statement about the uniform measure
on $\mathcal G(n, 1/2)$. However:

- The Bollobás argument uses a chain of high-probability events whose
  union bound requires careful bookkeeping;
- The payoff is a measure-1 statement rather than a deterministic
  reconstruction result;
- Formalization cost is high; mathematical impact on the conjecture is
  low (the result is already known and does not close any gap).

**Recommendation.** Not a near-term Lean target. If the sibling project
acquires a broader probabilistic toolbox later (for instance for
Erdős–Rényi threshold theorems), Bollobás's theorem becomes a natural
application.

[bollobas90]: ../sources.md#bollobas90
[bondy91]: ../sources.md#bondy91
