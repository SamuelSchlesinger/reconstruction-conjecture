# Computational bounds for verification

This document gives the detailed **scale** of verification runs and the
reason why pushing past `n = 13` is so expensive.

## A000088 at a glance

The base cost is the number of isomorphism classes of simple graphs on
`n` vertices (OEIS A000088, [https://oeis.org/A000088](https://oeis.org/A000088)).
Values in the relevant range:

| `n` | A000088(n) | approx. `log10` |
|-----|------------|-----------------|
| 1 | 1 | 0.0 |
| 2 | 2 | 0.3 |
| 3 | 4 | 0.6 |
| 4 | 11 | 1.0 |
| 5 | 34 | 1.5 |
| 6 | 156 | 2.2 |
| 7 | 1,044 | 3.0 |
| 8 | 12,346 | 4.1 |
| 9 | 274,668 | 5.4 |
| 10 | 12,005,168 | 7.1 |
| 11 | 1,018,997,864 | 9.0 |
| 12 | 165,091,172,592 | 11.2 |
| 13 | 50,502,031,367,952 | 13.7 |
| 14 | 29,054,155,657,235,488 | 16.5 |
| 15 | 31,426,485,969,804,308,768 | 19.5 |

(The offset in OEIS is 0; A000088(0) = 1. Values above use the
natural "n vertices" index starting at `n = 1`. OEIS offset is
verified against [oeis-a000088][oeis-a000088].)

Ratios of consecutive terms are the important quantity for extrapolation:

| step | A000088(n+1) / A000088(n) |
|------|---------------------------|
| 11 → 12 | ≈ 162 |
| 12 → 13 | ≈ 306 |
| 13 → 14 | ≈ 575 |
| 14 → 15 | ≈ 1080 |

Asymptotically the ratio is approximately `2^n / (n+1)` (each extra
vertex adds `n` potential edges and the automorphism group divides
out an `(n+1)`-order factor), which is consistent with the table.

## Reported runtime scaling

- **McKay 1997** (`n ≤ 11`). Machine-months on 1990s workstations.
  Exact CPU figures not tabulated in the paper itself
  ([mckay97][mckay97]).
- **McKay 2022** (`n ≤ 13`). Large parallel run on a university
  cluster; reported in [mckay22][mckay22] with
  per-class breakdowns (see Table 1 therein — verify exact totals).
  The 2022 paper also extends the following classes:

  | Class | Verified up to `n` | Source |
  |-------|--------------------|--------|
  | All simple graphs | 13 | [mckay22][mckay22] |
  | Triangle-free graphs | 14 | [mckay22][mckay22] (verify which: 1997 vs. 2022) |
  | Square-free graphs | 15 | [mckay22][mckay22] |
  | Bipartite graphs | 15 | [mckay22][mckay22] (verify which: 1997 vs. 2022) |
  | Regular graphs | (extended) — verify exact | [mckay22][mckay22] |
  | Tournaments (set-rec) | 13 | [mckay22][mckay22] |
  | General digraphs | 9 | [mckay22][mckay22] |
  | Posets | 13 | [mckay22][mckay22] |

  Note: the triangle-free `n ≤ 14` and bipartite `n ≤ 15` bounds are
  attributed here to McKay 2022 based on the summary table in that
  paper; some sources attribute earlier cutoffs of these classes to
  McKay 1997 [mckay97][mckay97]. The exact history per class should
  be traced back to the cited paper before quoting.

## Why brute force cannot confirm `n = 13 + 1`

Setting aside the cost of *comparison*, even just **generating** every
graph on 14 vertices once each is at the edge of what can be done on a
large cluster — A000088(14) ≈ 2.9 · 10^16, and `geng`'s throughput is
in the `10^5 – 10^7` canonical graphs per core-second range for small
`n` (and decreases with `n` as the per-graph canonical-labelling cost
grows). So even at an optimistic `10^7/sec/core` sustained, a single
core would take `10^9` seconds ≈ 31 core-years to *emit* the graphs.
10,000-core weeks are in principle feasible, but every graph then has
to have its **deck** computed (`n = 14` canonical labels of order-13
subgraphs each) and looked up in a large dictionary to check for a
hypomorphic twin. Memory becomes the binding constraint.

The practical way past this wall is **not** "more cores" but one of
the following structural reductions:

1. **Narrower enumeration via Kelly's Lemma.** The edge count, degree
   sequence, number of triangles, and more are recoverable from the
   deck [invariants][../invariants/index.md]. The space of decks
   consistent with each tuple of invariants is far smaller than
   A000088(n), and any counterexample pair would have to sit in a
   single such bucket. McKay already exploits this; a sharper set of
   invariants would let verification run at a constant factor of
   speedup.
2. **Class restriction.** McKay 2022 already pushes triangle-free and
   bipartite graphs to 14 – 15 vertices; these classes are sparse so
   the cost is dominated by a much smaller sub-sequence of A000088.
3. **A proof.** Any structural theorem that rules out a counterexample
   for `n ≥ some bound` replaces computation with mathematics. The
   most direct such theorem would be a proof of Harary's
   edge-reconstruction for `n = 14` graphs of some density, combined
   with Kelly-style recovery of the sparse case; but this is work on
   the conjecture itself, not a computational shortcut.

## Class-by-class tractability (2024 – 2026 viewpoint)

| Class | Practical ceiling | Obstruction |
|-------|-------------------|-------------|
| Arbitrary simple graphs | `n = 13` (verified); `n = 14` out of reach | A000088 super-exponential |
| Triangle-free | `n = 14` (verified); `n = 15` at edge | count growth slightly slower |
| Bipartite | `n = 15` (verified); `n = 16` conceivable | class much sparser than full A000088 |
| Trees | any `n` (proof, not computation) | — |
| Regular | polynomial in `n` per class, but class itself large | — |
| Cubic / `k`-regular small `k` | `n` in the hundreds (per-class enumeration tables exist at HoG) | asymmetry, not count |

References for the class extensions:
[mckay22][mckay22],
[mckay97][mckay97],
[oeis-a000088][oeis-a000088].

[mckay97]: ../sources.md#mckay97
[mckay22]: ../sources.md#mckay22
[oeis-a000088]: ../sources.md#oeis-a000088
