# Graph databases and infrastructure

Computational work on the reconstruction conjecture relies on a handful
of standing databases. Any future formalization effort that wants to
*replay* a computer verification (even at small `n`) should draw its
input from these sources rather than re-enumerate from scratch.

## Brendan McKay's graph collections

- URL: [https://users.cecs.anu.edu.au/~bdm/data/](https://users.cecs.anu.edu.au/~bdm/data/)
- Maintainer: Brendan D. McKay (Australian National University).
- Format: `graph6` / `sparse6` (documented in
  [https://users.cecs.anu.edu.au/~bdm/data/formats.txt](https://users.cecs.anu.edu.au/~bdm/data/formats.txt)).
- Contents (selection):
  - All non-isomorphic simple graphs on `n ≤ 10` (full lists);
    `n = 11` by class (connected, bi-regular, ...).
  - All trees on `n ≤ 22` vertices.
  - All cubic graphs on `n ≤ 32` (connected), including snarks.
  - Planar graphs to `n = 12` (via `plantri`).
  - Ramsey graph candidates for `R(3,k)`, `R(4,k)`.
  - Strongly regular graphs with various parameter sets.
  - Tournaments to `n ≤ 13`.

These are the canonical reference inputs for any reconstruction-related
computation; `nauty`-canonicalized so that two files differing in
content differ in some isomorphism class.

## House of Graphs

- URL: [https://houseofgraphs.org](https://houseofgraphs.org)
- Maintainers: Kris Coolsaet, Sven D'hondt, Jan Goedgebeur (Ghent
  University / KU Leuven) and collaborators
  [coolsaet23][coolsaet23].
- Database of "interesting" graphs with rich invariant queries
  (chromatic number, girth, independence, spectral, planarity,
  connectivity).
- Searchable and programmable via a REST API; downloads in `graph6`
  and several other formats.
- Includes `keywords` flagging reconstruction-relevant families
  (e.g. Stockmeyer tournaments, Kelly tree examples, hypomorphic
  pairs of digraphs).

For the reconstruction conjecture specifically, House of Graphs is the
primary reference for **small counterexamples in related problems**
(digraphs, hypergraphs, multigraphs) that are difficult to obtain
by re-enumeration, and for **extremal graphs** that inform invariant
conjectures.

## OEIS sequences of interest

| OEIS ID | What it counts | Used for |
|---------|-----------------|----------|
| [A000088](https://oeis.org/A000088) | unlabeled simple graphs on `n` vertices | verification budget |
| [A000664](https://oeis.org/A000664) | unlabeled connected graphs on `n` | restricted verification |
| [A000055](https://oeis.org/A000055) | unlabeled trees on `n` | Kelly-tree benchmarks |
| [A000568](https://oeis.org/A000568) | unlabeled tournaments on `n` | Stockmeyer context |
| [A052283](https://oeis.org/A052283) | unlabeled digraphs on `n` | digraph-counterexample context |
| [A000031](https://oeis.org/A000031) | unlabeled necklaces | cycle-like graph counts |

## Combinatorial Object Server

- URL: [https://combos.org/](https://combos.org/)
- Maintainers: Frank Ruskey et al. (University of Victoria).
- Serves on-demand enumeration of combinatorial objects including
  `geng`-wrapped non-isomorphic simple graphs up to size limits set by
  the server. Useful for small-`n` experimentation without local
  `nauty` installation.

## Nauty distribution

- URL: [https://users.cecs.anu.edu.au/~bdm/nauty/](https://users.cecs.anu.edu.au/~bdm/nauty/)
  and [https://pallini.di.uniroma1.it/](https://pallini.di.uniroma1.it/).
- Current version (as of 2024): 2.9.x.
- Language: portable C (C99). Builds via autoconf; binaries available
  for Linux, macOS, Windows (WSL).
- License: permissive (Apache-2-style); see the distribution's
  `COPYRIGHT` file.

## SageMath wrappers

SageMath exposes `nauty` through:

- `graphs.nauty_geng(n, e_min, e_max)` — Python generator of non-iso
  simple graphs.
- `G.canonical_label(algorithm='sage'|'bliss'|'nauty')` — canonical
  labelling.
- `G.is_isomorphic(H, certificate=False)` — isomorphism testing.

The demonstration script [`data/deck_equiv.py`](data/deck_equiv.py) uses
the pure-Python `networkx` stack for portability, but an analogous
Sage-native one-liner exists:

```
all(
    G.is_isomorphic(H)
    for G in graphs(n) for H in graphs(n)
    if deck_iso(G) == deck_iso(H)
)
```

## References

- [coolsaet23][coolsaet23] — House of Graphs 2.0.
- [nauty-manual][nauty-manual] — user's guide.
- [mckayp14][mckayp14] — current `nauty`/`Traces`
  algorithm.
- OEIS ([https://oeis.org/](https://oeis.org/)) — enumeration
  sequences.

[coolsaet23]: ../sources.md#coolsaet23
[nauty-manual]: ../sources.md#nauty-manual
[mckayp14]: ../sources.md#mckayp14
