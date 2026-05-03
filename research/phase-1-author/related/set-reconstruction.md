# Set Reconstruction Conjecture

## Statement

For a graph `G` on `n` vertices, define:

- `deck(G) := { G − v : v ∈ V(G) }` as a **multiset** of isomorphism
  classes — the usual (Kelly–Ulam) deck;
- `sdeck(G) := { G − v : v ∈ V(G) }` as a **set** of isomorphism
  classes — the set-deck, which forgets multiplicity.

**Set Reconstruction Conjecture (SRC)**
[hararyplantholt85][hararyplantholt85]. Every graph `G` on `n ≥ 4`
vertices is determined up to isomorphism by `sdeck(G)`.

## Logical position

Because `sdeck(G) = support(deck(G))` (the set underlying the multiset),
any two graphs with equal multiset-decks also have equal set-decks.
Hence:

> `SRC ⇒ RC.`

SRC is therefore at least as hard as RC, and strictly stronger in the
sense that it asks for reconstruction from less information.

The converse — `RC ⇒ SRC` — is **not known**. In principle there could
be a pair of non-isomorphic graphs `G ≠ H` with `sdeck(G) = sdeck(H)`
but `deck(G) ≠ deck(H)` (distinguishable by the multiplicities alone).
No such pair has been found for `n ≥ 4`.

## Why multiplicities might matter

From Kelly's Lemma the multiplicity of any proper subgraph `F` in `G`
is recoverable from the multiset deck:

```
c(F, G) = (1 / (n − |F|)) · Σ_{H ∈ deck(G)} c(F, H).
```

The *set-deck* loses this information: if `F` appears in `deck(G)` at
least once and in `deck(H)` at least once, with possibly different
multiplicities, the set-deck cannot distinguish them. So a priori, SRC
requires additional structural arguments to recover multiplicity-level
counts from the set alone.

A key observation (folklore): if any card in `deck(G)` appears with
multiplicity `1` (a "unique card"), then combined with the rest of the
set-deck one can often recover the full multiset by a counting argument
based on `|V(G)| = n` and the total number of cards. Many graph
classes — random graphs, graphs with many distinct degrees — have
unique cards almost surely, which is why SRC is *"morally no harder"*
on generic graphs.

## Status

- **Verified for all graphs on `n ≤ 13` vertices** by McKay's exhaustive
  computations [mckay97][mckay97].
- **Open** for all `n ≥ 14`, exactly as for RC.
- **Equivalent to RC on generic / random graphs**: almost all graphs
  have all distinct cards ([bollobas90][bollobas90] reconstruction
  number 3 result implies this).

## Is it equivalent to RC?

Explicit statement of the **equivalence question**:

> **Open.** Does `RC ⇔ SRC`? No counterexample is known; no proof is
> known either.

Partial reductions:

1. If every graph on `n` vertices has at least three cards of distinct
   isomorphism type, then the multiset deck can be recovered from the
   set deck (a counting argument, using only the vertex count and the
   known cards). [bondy91][bondy91] discusses this.
2. In the **asymptotic regime** (random graphs), set- and multiset-deck
   reconstruction are asymptotically equivalent.
3. The case that separates SRC from RC — if any — lies among graphs
   with **many repeated cards**, e.g. highly symmetric graphs
   (vertex-transitive, strongly regular). These are exactly the graphs
   most studied by reconstruction theorists on the RC side, because
   they are the hardest instances.

## Proved harder?

A common misconception is that SRC is "proved harder than RC". In fact
SRC **is** logically at least as strong as RC by inclusion; but no one
has exhibited a class where SRC fails while RC holds. The literature
generally proves SRC and RC in lockstep — i.e. techniques that give RC
for a class typically give SRC for the same class with at most minor
additional argument (unique-card analysis).

## Formalization targets

For Lean 4:

1. **Define `sdeck`** as a `Finset` (or `Set`) of isomorphism classes,
   mirroring an existing `deck` as `Multiset`.
2. **Prove `SRC n ⇒ RC n`** (immediate from definitions).
3. **Prove `RC n ∧ (no two cards are isomorphic) ⇒ SRC n`** — mechanical
   once the multiset/set API is in place.
4. **Formalize Bollobás's "reconstruction number 3" implication** that
   SRC holds for almost all graphs. Needs probabilistic-combinatorics
   scaffolding but gives a clean big theorem.

[hararyplantholt85]: ../sources.md#hararyplantholt85
[mckay97]: ../sources.md#mckay97
[bondy91]: ../sources.md#bondy91
[bollobas90]: ../sources.md#bollobas90
