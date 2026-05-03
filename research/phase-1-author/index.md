# Reconstruction Conjecture — Research Corpus

Topic: The Kelly–Ulam **Reconstruction Conjecture** in graph theory, together
with related conjectures (edge reconstruction, set reconstruction, etc.) and
known partial progress. Goal is to identify angles where **Lean 4**
formalization (in the sibling project `graph-theory/reconstruction-conjecture`)
could either make genuinely new progress or provide useful infrastructure for
an attack.

## Taxonomy

1. [State of the art](state-of-the-art/index.md)
   — what is proved, who proved it, which graph classes are known to be
   reconstructible, which aren't known.
2. [Reconstructible invariants](invariants/index.md)
   — Kelly's Lemma and its descendants; parameters recoverable from the deck.
3. [Attack strategies](attacks/index.md)
   — spectral/eigenvalue approaches, probabilistic and random-graph methods,
   structural reductions, counterexample hunts.
4. [Computational verification](computational/index.md)
   — up to what order has the conjecture been verified by computer, tools
   used (McKay et al.), databases, complexity.
5. [Related conjectures](related/index.md)
   — edge reconstruction, set reconstruction, digraph reconstruction,
   metric dimension-style variants.
6. [Formalization angles](formalization/index.md)
   — how the above maps to Lean 4 / Mathlib; what is already formalized in
   the sibling project; concrete next-step targets.

## Supplementary Code

Small scripts live alongside the research documents under each field's
`data/` subfolder. These scripts were used to brute-force sanity-check
identities at small orders; they are not part of the Lean formalization.

- [`computational/data/deck_equiv.py`](computational/data/deck_equiv.py) —
  Python/`networkx` implementation of the deck-equivalence test on all
  simple graphs of small order `n`, as a self-contained reference for the
  pipeline McKay's published verifications use.
- [`computational/data/deck_equiv.txt`](computational/data/deck_equiv.txt) —
  sample output of `deck_equiv.py` for small `n`.
- [`invariants/data/kelly_small.py`](invariants/data/kelly_small.py) —
  brute-force verification of Kelly's Lemma on all simple graphs on 5
  vertices for one choice of small subgraph `F`.
- [`invariants/data/kelly_small_output.txt`](invariants/data/kelly_small_output.txt) —
  sample run of `kelly_small.py`.
- [`invariants/data/charpoly_deck.py`](invariants/data/charpoly_deck.py) —
  `sympy`-based verification that the derivative identity
  `φ'(G, x) = Σ_v φ(G − v, x)` holds for every simple graph on up to 6
  vertices.
- [`invariants/data/charpoly_deck_output.txt`](invariants/data/charpoly_deck_output.txt) —
  sample run of `charpoly_deck.py`.

## Sources

See [`sources.md`](sources.md) for the master bibliography.
