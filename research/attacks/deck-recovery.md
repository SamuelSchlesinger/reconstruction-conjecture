# Deck Recovery — Where the Wall Is

The separator-decomposition programme has, in Lean, a **complete structural
reassembly layer**: given a separator `S` shared by `G` and `H` plus matched
pieces that agree on `S` and its attachment, `nonempty_iso_of_separator_pieces`
(general `S`) and `nonempty_iso_of_cutVertex_pieces` (`S = {v}`) deliver
`G ≃g H`. Everything structural reduces to producing that data.

**Deck recovery** is producing it *from `SameDeck` alone*. This is the genuine
hard content of every reconstruction theorem, and this note maps exactly which
cases are tractable, which are hard, and why — so future work targets the wall
rather than re-polishing the reassembly side.

## What `SameDeck` gives you for free (the reconstructible kernel)

From `G.SameDeck H` (a bijection `σ` with `G − x ≅ H − σ x` for all `x`), the
project already extracts:

- a card matching `σ`, and that `σ` **preserves degree** (`SameDeck.degree_eq`)
  and the **degree multiset** (`degreeMultiset_eq`);
- the **edge count** (`card_edgeFinset_eq`);
- **connectivity** and the **connected-component multiset**
  (`ConnectedComponents`, `Disconnected/ComponentCount`);
- all **subgraph counts** `s(F, G)` for `|F| < n` (Kelly's Lemma,
  `KellyLemma`), hence triangles, paths, small-cycle counts, and the Kocay
  product/cover counts;
- non-constant **characteristic-polynomial coefficients** (`Spectral`);
- by complementation (`SameDeck.compl`), every one of the above for `Gᶜ` too.

This is a lot — but it is all **unlabeled / counting** data plus a card matching
that need not respect any particular structure.

## The recovery-tractable cases (forced structure) — DONE

Recovery succeeds exactly when the decomposition is **forced by a deck-
reconstructible invariant**, so no labeling choices remain:

| Class | Why recovery is forced | Lean |
|---|---|---|
| Disconnected `G` | `S = ∅`; component multiset is reconstructible (Kelly), and components carry no cross-attachment | `SameDeck.iso_of_not_connected` |
| `Gᶜ` disconnected (join / decomposable) | the complement-dual of the above, via `SameDeck.compl` | `nonempty_iso_of_compl_not_connected` |
| Isolated vertex | `⇒ G` disconnected | `nonempty_iso_of_isolated_vertex` |
| Universal vertex | `⇒ Gᶜ` disconnected; equivalently degree `n−1` is recognizable and the attachment ("everything") is forced | `nonempty_iso_of_universal_vertex` |

The unifying principle: **`S = ∅` (in `G` or `Gᶜ`) needs no attachment data**,
and the component structure is reconstructible. The moment `S ≠ ∅`, attachment
must be recovered, and that is where it breaks.

## The recovery-hard cases — the wall

| Class | What recovery needs | Status |
|---|---|---|
| Cut vertex, `δ ≥ 2` (Bondy) | recognize the cut vertex's card, recover the `G − v` component matching **and the attachment (link) of `v`** | hard — needs block / block-cut-tree / end-block analysis (Bondy 1969); **not in Mathlib, not yet attempted here** |
| 2-connected (Yongzhi target) | the full conjecture for the residual class | open in general |
| Interval graphs | clean clique separation recovered via bulk/flank resilient structure theory | ~50-page proof (Heinrich et al. 2025); see [`rung-2-3-plan.md`](rung-2-3-plan.md) |
| Chordal graphs | recover *which* clique separator and *how atoms attach* | **OPEN mathematics** — no technique exists |

### Why the attachment is the wall

For a separator `S` (even a single vertex `v`), the deck gives the cards `G − x`
as **unlabeled** graphs. The link `N(v)` is, in principle, visible in a card:
`x ∈ N(v)` iff `deg_{G−v}(x) = deg_G(x) − 1`. But the card is unlabeled, so we do
not know which vertex of `G − v` is "`x`", and `SameDeck`'s card iso is free to
permute vertices of equal degree. Recovering the attachment therefore requires
**resilient, combinatorially-canonical anchors** that survive deletion and pin
the labeling — the bulk/flank theory for intervals, the end-block structure for
Bondy. There is no counting shortcut: this is exactly the content that the
cospectral/Kelly-ceiling barriers say cannot come from invariants alone.

This is also why Stockmeyer's tournament counterexamples matter here: the
reassembly engine is orientation-agnostic, so any *correct* attachment-recovery
step must use an undirected-specific fact. The forced-structure wins above do
(connectivity/complementation are undirected levers); a general recovery must
too.

## The precise obligation

For the cut-vertex case, deck recovery must establish, from `G.SameDeck H` and a
cut vertex `v`, the hypotheses of `nonempty_iso_of_cutVertex_pieces`:

```
∃ (e : (G−v).Components ≃ (H−σv).Components)
  (ι : ∀ c, (G−v).induce c.supp ≃g (H−σv).induce (e c).supp),
  (∀ c x, G.Adj v x ↔ H.Adj σv (ι c x))          -- attachment / link match
```

The reduction "this data ⇒ `G ≃g H`" is **done** (it is the assembler). The
existential is the open Bondy content. Stating and proving that existential — or
its interval/chordal analogues — is the entire remaining difficulty of the
programme.

## Honest bottom line

The forced-structure cases (disconnected, join, universal, isolated) are now
formalized and they exhaust what recovery gives "for free." Everything past them
— cut-vertex `δ ≥ 2`, 2-connected, interval, chordal — requires labeling-pinning
structure theory that is (a) absent from Mathlib and (b) for chordal, absent
from the literature. The reassembly side is complete; the deck-recovery side is
the genuine frontier, and none of it is a quick win.
