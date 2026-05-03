# Formalization Angles — Lean 4 / Mathlib

This document surveys the **Lean 4** formalization landscape for the
Reconstruction Conjecture, with an eye toward what an author of the sibling
Lean project
[`graph-theory/reconstruction-conjecture`](../../reconstruction-conjecture)
can realistically formalize in the next work cycle. It combines (a) a
survey of the relevant Mathlib API, (b) a precise inventory of the sibling
project's current state, and (c) a ranked list of next-step targets.

For the mathematical side of the conjecture see
[`../state-of-the-art/index.md`](../state-of-the-art/index.md); for the
invariant-by-invariant status see
[`../invariants/index.md`](../invariants/index.md); for attack strategies
see [`../attacks/index.md`](../attacks/index.md); for related variants see
[`../related/index.md`](../related/index.md); for computational
verification and small-`n` data see
[`../computational/index.md`](../computational/index.md).

Detail files:

- [`sibling-project.md`](sibling-project.md) — current Lean state, file-by-file.
- [`mathlib-api.md`](mathlib-api.md) — relevant Mathlib declarations and gaps.
- [`next-targets.md`](next-targets.md) — 1-page sketches of the top proposals.

## Ranked target table

Difficulty is **low / medium / high / open**. "Prereqs in Mathlib" refers
to *existing* declarations we can build on; "Sibling file" is where the
theorem lives (or should live) in
[`graph-theory/reconstruction-conjecture`](../../reconstruction-conjecture).

| # | Target | Difficulty | Prereqs in Mathlib | Sibling file | Sketch |
|---|--------|-----------|---------------------|--------------|--------|
| 1 | `Matrix.newton_trace_charpoly` — close existing `sorry` | **low** | `Matrix.aeval_self_charpoly`, `Matrix.mul_adjugate`, `Polynomial.coeff_derivative` | `Reconstruction/Newton.lean` | The infrastructure is already in place (`adjCoeff`, recurrence, degree bound, `trace_adjugate_charmatrix`, `cayley_hamilton_trace`); the `sorry` has been eliminated and only the final `linear_combination` assembly remains to harden (verify: the file reads as complete). |
| 2 | `SameDeck.trace_adjMatrix_pow_eq` — trace-of-powers reconstructibility | **low** | `Matrix.trace`, `Polynomial.coeff_derivative` | `Reconstruction/TraceReconstruction.lean` | Strong induction on `k`: Newton at step `k` expresses `tr(A^k)` in terms of `c_{N-j}` and `tr(A^{k-j})` for `j ≥ 1`. Non-constant `c_j` are reconstructible (`SameDeck.charPoly_coeff_eq`), lower traces by IH. The proof is written modulo Newton; closing #1 closes this. |
| 3 | `SameDeck.charPoly_coeff_zero_eq` — constant term of charpoly | **medium** | `Matrix.cayley_hamilton_trace`, trace reconstructibility (#2) | `Reconstruction/CharPolyFull.lean` | Cayley–Hamilton gives `n · c_0 = -∑_{i≥1} c_i · tr(A^i)`, and all right-hand terms are reconstructible *once `tr(A^n)` is*. The sharp obstruction: Kelly's Lemma only recovers `tr(A^k)` for `k < n`. Two routes: (a) Sachs coefficient formula expressing `c_0 = ∑ sign · product over elementary subgraphs`, all of which are counted by Kelly; (b) walk decomposition over cycle structure. See [`next-targets.md`](next-targets.md) #A. |
| 4 | `SameDeck.numComponents_eq` — component count is reconstructible | **medium** | `SimpleGraph.ConnectedComponent`, `Fintype.card_le_of_injective`, existing `SameDeck.connected` | `Reconstruction/ConnectedComponents.lean` | Three-way case split (connected / has isolated vertex / no isolated vertex). In-file TODO lists the decidability friction with `Fintype.card_le_of_surjective` under mixed Classical / concrete instances. Pure bookkeeping once decidability is handled. See [`next-targets.md`](next-targets.md) #B. |
| 5 | `SameDeck.iso_of_not_connected` — Kelly's disconnected-graph theorem | **medium–high** | `SimpleGraph.ConnectedComponent`, Kelly's Lemma (already proved) | `Reconstruction/Disconnected.lean` | Kelly 1942: if `G` has `k ≥ 2` components with sizes `n_1 ≥ … ≥ n_k`, then `n_2 ≤ n/2 < n`, so every component except possibly the largest is counted by Kelly's Lemma; the largest is the complement. This is a full *isomorphism* reconstruction, not just an invariant equality — formalization requires choosing representatives. See [`next-targets.md`](next-targets.md) #C. |
| 6 | Extend Kelly's Lemma to **rooted / coloured** subgraph counts | **medium** | `SimpleGraph.copyCount` (Mathlib), existing `subgraphCount` | new file | Carry additional structure (root vertex, labels) through Kelly's double-counting. Useful for the cut-vertex reduction (Bondy 1969). |
| 7 | **Edge-reconstruction** variant `EdgeDeck` / `SameEdgeDeck` | **medium** | `SimpleGraph.deleteEdges`, `DeleteEdges.lean` in Mathlib | new file | Parallel to the vertex-deck setup but with `G - e` for each edge. Unlocks Müller, Lovász, Nash-Williams. See [`next-targets.md`](next-targets.md) #D. |
| 8 | Deck-reconstructibility of the **Laplacian** characteristic polynomial | **medium–high** | `SimpleGraph.lapMatrix` (`Mathlib.Combinatorics.SimpleGraph.LapMatrix`), `Matrix.charpoly` | new file (`Reconstruction/Laplacian.lean`) | Same derivative-formula machinery; cofactors correspond to the Matrix-Tree theorem. Payoff: number of spanning trees is reconstructible. |
| 9 | `SameDeck.chromaticPolynomial_eq` — chromatic polynomial is reconstructible | **high** | Whitney's broken-circuit expansion (partial in Mathlib) | new file | Chromatic polynomial is a polynomial in induced-subgraph counts; Kelly's Lemma gives each term. |
| 10 | Full conjecture on `n ≤ 6` by `decide` / exhaustive enumeration | **medium (engineering)** | `Fintype.decidableForallFintype`, explicit deck decoder | new file | Computational witness: for each `n ≤ 6` enumerate all simple graphs (up to `Fin n`), bucket by deck, check each bucket is a single isomorphism class. Mathematical content is thin but the project would gain a reproducible, sorry-free small-`n` verification. **Constraint:** `native_decide` is disallowed on unbounded domains; a fixed-`n` `decide` over `Fin n` is in scope. See [`next-targets.md`](next-targets.md) #E. |
| 11 | Müller edge-reconstruction bound (`m > (n-1) log₂ n` implies reconstructible) | **high → research** | Entropy / Shannon lemmas (partial in `Mathlib.Information`), edge-deck #7 | new file | Probably the first mathematically *novel* contribution in scope: no Lean formalization of Müller's theorem exists (verify). Requires the edge-deck and a Möbius-inversion / inclusion–exclusion argument. |
| 12 | Bollobás "almost every graph is 3-reconstructible" | **research** | Probabilistic lemmas over finite graphs | new file | Very ambitious; formalization would likely require developing a random-graph API in Mathlib from scratch (currently absent — verify). See [`next-targets.md`](next-targets.md) #E (optional extension). |
| 13 | The full Reconstruction Conjecture | **open** | — | `Reconstruction/Basic.lean` | Open mathematical problem. |

Entries 1–3 are the natural immediate sequence: they close the remaining
spectral-side `sorry`s and produce a fully-proven *characteristic polynomial
is reconstructible* theorem. Entries 4–5 close the
connectivity / disconnected side and produce a fully-proven *disconnected
graphs are reconstructible* theorem. Beyond that, 7, 10, and 11 are the most
attractive directions for genuinely new Lean content.

## Design choices for a reconstruction library

The sibling project has already committed to several design decisions; they
are defensible, but any refactor or Mathlib upstreaming should revisit them.

### Same-vertex-set `SameDeck` vs. multiset deck

The current definition is
([`Reconstruction/Defs.lean`](../../reconstruction-conjecture/Reconstruction/Defs.lean#L28)):

```lean
def SimpleGraph.SameDeck (G H : SimpleGraph V) : Prop :=
  ∃ σ : V ≃ V, ∀ v : V,
    Nonempty (G.deleteVert v ≃g H.deleteVert (σ v))
```

This is a **bijection-based hypomorphism**, not a multiset equality. Two
things to note:

- Both graphs live on the *same* vertex type `V`. This is fine when we
  think of deck reconstruction as "can a hypomorphism be extended?", but
  the classical formulation is "as multisets of isomorphism classes of
  cards". The two formulations are interchangeable for vertex reconstruction
  (Bondy; see [`../state-of-the-art/hypomorphy.md`](../state-of-the-art/hypomorphy.md)
  if it exists), but they are genuinely *different* for the edge-deck.
- Using `Nonempty (... ≃g ...)` instead of `⟦...⟧ = ⟦...⟧` in
  `Quot (SimpleGraph V) Isomorphic` keeps everything at the level of
  `Prop` and avoids needing a quotient type. This matches the
  `Mathlib.Combinatorics.SimpleGraph.Copy` approach to subgraph counting
  (which uses `Nonempty (H ↪g G)`).

A *multiset deck* would be:

```lean
def deck (G : SimpleGraph V) [Fintype V] : Multiset (Σ' s : Set V, SimpleGraph s) := …
```

quotiented by graph isomorphism. Modelling this cleanly needs an
`IsomorphismClass` quotient that Mathlib does not yet supply (verify).
Bottom line: the current `SameDeck` is adequate for the reconstructible-
invariants layer. A multiset deck becomes necessary only for *stating* the
conjecture in its most classical form, which the sibling project does not
need.

### Computability

`subgraphCount` is defined `noncomputable` because it branches on
`Nonempty (G.induce S ≃g F)`. Alternatives:

- Use `Decidable (Nonempty (G.induce S ≃g F))`, available when both sides
  are finite and `DecidableEq` on edge sets (`Fintype (Iso G H)` is
  derivable via `Fintype (V ≃ W)`). This would make `subgraphCount`
  computable and enable small-`n` `decide` (target #10).
- Continue `noncomputable` and lift to classical reasoning. Simpler but
  precludes a computational witness.

The Mathlib idiom (see
[`SimpleGraph.copyCount`](../../reconstruction-conjecture/.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/Copy.lean))
is `noncomputable` with a TODO to make it computable.

### `abbrev deleteVert` vs. a named wrapper

`SimpleGraph.deleteVert G v := G.induce {w | w ≠ v}` is declared `abbrev`
so that typeclass search propagates `DecidableRel` and `Fintype
edgeFinset` automatically. This is the right call: a `def` would have
required forwarding ~10 instances manually. Downside: error messages
unfold `deleteVert`. Acceptable cost.

### Carrier types for card subgraphs

A `deleteVert`-card has vertex type `{w : V // w ≠ v}`, a subtype of `V`.
This is the right choice — it means `deleteVert` and `induce` share the
same vertex-type convention, and matrix operations via
`Matrix.submatrix Subtype.val Subtype.val` (see
[`Reconstruction/Spectral.lean`](../../reconstruction-conjecture/Reconstruction/Spectral.lean#L54))
compose cleanly.

## Cross-formalization check

- **Mathlib 4** — has `SimpleGraph.induce`, `.comap`, `.map`, `Iso`,
  `adjMatrix`, `lapMatrix`, `Matrix.charpoly`, `Matrix.aeval_self_charpoly`
  (Cayley–Hamilton), `SimpleGraph.copyCount`, `SimpleGraph.Subgraph.deleteVerts`,
  `SimpleGraph.ConnectedComponent`. It does **not** have: a formal "deck",
  `deleteVert` on the ambient `SimpleGraph` (only `Subgraph.deleteVerts`),
  Newton's identities, or the derivative formula `φ'(G) = Σ φ(G-v)`.
  Everything the sibling project's `Spectral.lean`, `Newton.lean`, and
  `KellyLemma.lean` contain is **new Lean content** and, per the author's
  review, is not duplicated elsewhere in Mathlib. See
  [`mathlib-api.md`](mathlib-api.md) for a per-declaration audit.
- **google-deepmind / formal-conjectures** — at time of writing (verify),
  the repository does not contain a formalization of the reconstruction
  conjecture; a reasonable contribution would be to port the sibling
  project's statement (`Reconstruction.Basic.reconstruction_conjecture`)
  there.
- **Isabelle / AFP** — no entry on graph reconstruction exists in the
  Archive of Formal Proofs (verify via https://www.isa-afp.org/).
  Combined with the above, **the sibling project appears to be the only
  ITP-level formalization of graph-reconstruction invariants**; pushing
  the derivative formula, Kelly's Lemma, or Newton's identity upstream
  into Mathlib would be a concrete contribution to the wider formal
  mathematics ecosystem.

## Opportunities for genuinely novel progress

Beyond finishing the open `sorry`s, the following would be *new* Lean content
whose mathematical content is known but whose formalization is (as best we
can tell) first-in-kind:

1. **Edge-reconstruction API.** Mathlib already has
   `SimpleGraph.deleteEdges`
   ([`Mathlib.Combinatorics.SimpleGraph.DeleteEdges`](../../reconstruction-conjecture/.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/DeleteEdges.lean)).
   Building `EdgeDeck` / `SameEdgeDeck` and proving Lovász's bound
   `m > ½ C(n,2) ⇒ G` is edge-reconstructible would be a clean ~500-line
   target that plugs directly into a Mathlib PR. See
   [`next-targets.md`](next-targets.md) #D.

2. **Computational verification up to `n ≤ 6`.** A `decide`-certified
   verification for small `n` (no `native_decide`, per project policy)
   closing the gap between the conjecture and McKay's computer search.
   Independently reproducible; substantially less ambitious than the
   full conjecture. See [`next-targets.md`](next-targets.md) #E.

3. **Port of Müller's edge-reconstruction bound.** The cleanest novel
   target at the research frontier: formalize that
   `m > (n-1) log₂ n ⇒ G` is edge-reconstructible. Requires a small
   entropy / information-theoretic argument (verify against
   `Mathlib.Information`).

4. **Kelly's Lemma with automated consequence transfer.** Write a
   tactic (or a Lean script) that, given a proof that some invariant is
   expressible as a fixed linear combination of `subgraphCount F G` over
   `F` on `< n` vertices, mechanically produces its deck-reconstructibility.
   This is a meta-level contribution and would be an interesting test of
   Lean's elaboration machinery.

[bondy91]: ../sources.md#bondy91
[kelly57]: ../sources.md#kelly57
[harary64]: ../sources.md#harary64
[tutte79]: ../sources.md#tutte79
[muller77]: ../sources.md#muller77
[lovasz72]: ../sources.md#lovasz72
[bollobas90]: ../sources.md#bollobas90
[schwenk79]: ../sources.md#schwenk79

Mathlib declarations cited in this file (verify against commit pinned by
`lakefile.toml` — `v4.28.0` at time of writing):

- `SimpleGraph.Iso` — `Mathlib.Combinatorics.SimpleGraph.Maps` (§`Iso`)
- `SimpleGraph.induce` — `Mathlib.Combinatorics.SimpleGraph.Maps`
- `SimpleGraph.Subgraph.deleteVerts` — `Mathlib.Combinatorics.SimpleGraph.Subgraph`
- `SimpleGraph.Subgraph.spanningCoe` — `Mathlib.Combinatorics.SimpleGraph.Subgraph`
- `SimpleGraph.adjMatrix` — `Mathlib.Combinatorics.SimpleGraph.AdjMatrix`
- `SimpleGraph.lapMatrix` — `Mathlib.Combinatorics.SimpleGraph.LapMatrix`
- `SimpleGraph.copyCount` — `Mathlib.Combinatorics.SimpleGraph.Copy`
- `SimpleGraph.ConnectedComponent` —
  `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`
- `SimpleGraph.Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial`
  — `Mathlib.Combinatorics.SimpleGraph.Acyclic`
- `Matrix.charpoly` / `Matrix.charmatrix` — `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`
- `Matrix.charpoly_reindex` — `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`
- `Matrix.aeval_self_charpoly` (Cayley–Hamilton) —
  `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`
- `Polynomial.coeff_derivative` —
  `Mathlib.Algebra.Polynomial.Derivative`
- `Matrix.adjugate`, `Matrix.mul_adjugate` —
  `Mathlib.LinearAlgebra.Matrix.Adjugate`
