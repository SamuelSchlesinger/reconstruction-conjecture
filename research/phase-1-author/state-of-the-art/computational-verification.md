# Computational Verification

The Reconstruction Conjecture has been computer-verified for graphs up to
11 vertices. This document summarizes the verification milestones and the
tools used.

## Timeline

| Upper bound | Year | Author(s) | Tooling |
|-------------|------|-----------|---------|
| `n ≤ 7` | 1964 | (implicit in Harary / early surveys) | by hand / enumeration |
| `n ≤ 9` | ca. 1977 | various; see [bondy91][bondy91] | early graph-enumeration programs |
| `n ≤ 10` | 1988 | McKay (via `nauty`) | `nauty` isomorphism-canonization |
| `n ≤ 11` | 1997 | McKay [mckay97][mckay97] | `nauty` + custom deck check |

The "modern" reference is **McKay 1997** [mckay97][mckay97], which
verifies that no two non-isomorphic graphs on `n ≤ 11` vertices share a
deck.

## Method

The standard computational verification goes:

1. Enumerate all graphs on `n` vertices up to isomorphism using
   McKay's canonical-labeling algorithm (`nauty` / `gtools`). The
   counts are in OEIS A000088.
2. For each graph `G`, compute the canonical form of each card
   `G - v` and sort / hash to produce a canonical deck-signature.
3. Check that distinct graphs produce distinct deck-signatures.

At `n = 11`, there are `1018997864` graphs up to isomorphism — about
`10^9` — so the check is large but tractable with a few CPU-days on
modern hardware.

## Tools

- **`nauty`** (McKay, 1981–present). De facto standard for graph
  canonization; `dreadnaut` and `shortg` / `labelg` are the relevant
  front-ends.
- **`traces`** (Piperno). Alternative canonization algorithm; used
  for spot-checking `nauty` results.
- **`gtools`** (`geng`, `showg`, etc.). Graph-generation utilities
  bundled with `nauty`.
- **SageMath** wraps `nauty`; useful for scripting the deck check.
- **House-of-Graphs** (UGent). Online database of "interesting"
  graphs, including small graphs flagged as potential counterexample
  candidates in other conjectures.

## Status beyond `n = 11`

For `n = 12`, there are ≈ `1.6 · 10^{11}` graphs, and a brute-force
check is borderline. No full verification at `n = 12` has been
published as of the cutoff date. Partial checks (restricted to
certain classes — regular graphs, bipartite graphs, etc.) extend
much higher.

## Reconstruction number statistics

Beyond verification, computational work has measured the
**reconstruction number** `rn(G)` — the minimum size of a sub-deck
that still determines `G` — for small graphs:

- For almost every small graph `rn(G) = 3` (consistent with
  Bollobás, see [random-graphs.md](random-graphs.md)).
- The graphs with large `rn(G)` are highly symmetric: vertex-
  transitive graphs, strongly regular graphs, etc.
- Lauri, Mizzi, Scapellato have several papers enumerating graphs of
  high reconstruction number (exact citations uncertain — verify
  against MathSciNet).

## Lean 4 / Mathlib interplay

- Exact reconstruction up through a small `n` could be proved
  `by decide` after a suitable finite-graph encoding, but the
  combinatorial explosion (`n = 5` already has 34 graphs) means
  `native_decide` will be required for anything non-trivial — and
  per the repo's Lean conventions, `native_decide` should be used
  only for finite, small computations.
- A nice intermediate Lean target: verify the conjecture for
  `n ≤ 6` by enumeration, using Mathlib's `SimpleGraph` on
  `Fin n`. See [../formalization/index.md](../formalization/index.md).

[bondy91]: ../sources.md#bondy91
[mckay97]: ../sources.md#mckay97
