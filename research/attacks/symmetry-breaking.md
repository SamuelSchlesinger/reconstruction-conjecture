# Canonical Symmetry-Breaking: Candidate Mechanisms

The strategy review identified the surviving corridor for a proof of the
Reconstruction Conjecture: **canonical symmetry-breaking in dense,
locally-symmetric graphs** — a deck-computable way to pin vertex labels
where cards look locally alike. This note develops candidate mechanisms,
with the first one's base case **proved in Lean today**
(`Reconstruction/RegularReconstruction.lean`).

## 0. A correction that sharpens the target

**Full symmetry is easy, not hard.** If `G` is `d`-regular, deleting `v`
stamps `N(v)` into the card as the vertices of degree `≠ d` — the
attachment is legible in the *unlabeled* card, and any same-deck `H` is
isomorphic to `G` (now formalized: `nonempty_iso_of_regular`, via
`degree_deleteVert` + `adj_iff_degree_deleteVert_ne` + the
`isoOfDeleteVertIso` assembler). In particular **vertex-transitive, strongly
regular, and cubic graphs are all reconstructible** — the attacks-index
row listing cubic graphs as open conflates the open *2-deck* problem
(Kostochka–Nahvi–West–Zirlin) with the closed 1-deck case.

Consequence: the wall is **not** at maximal symmetry. It is at
*near*-symmetry: **degree-irregular graphs whose vertices are locally
indistinguishable** — degree values clustered on adjacent integers
(`k`/`k+1` collisions), rich card automorphisms, no canonical extremes.
That is exactly the residual class of the reduction chain (2-connected,
`γ = 2` or `diam = diam(ᶜ) = 2`): dense enough that degrees concentrate,
irregular enough that the deficit stamp smears. Every mechanism below is
aimed at that refined target.

## M1. Deficit marking and marking rigidity (primary; partially formalized)

**The stamp.** Deleting `v` lowers the degree of exactly `N(v)` by one
(`degree_deleteVert`). Define a **marking** of an abstract card `C` (with
respect to the deck-known degree multiset `D` of `G` and degree `d_v` of the
deleted vertex): a 2-coloring `μ : V(C) → {in, out}` such that lifting
`in`-vertices' degrees by one yields `D − {d_v}`, and `|μ⁻¹(in)| = d_v`.
Every card has at least one marking (the true one); reconstruction fails
through a card only if it has *essentially different* markings.

**Rigid-card criterion — PROVED** (`nonempty_iso_of_rigidVertex`,
`RegularReconstruction.lean`). `RigidVertex G v` says every card
isomorphism onto a card with matching degree data (degree multiset and
deleted degree — both deck-reconstructible) can be corrected by a card
automorphism to respect the attachments. **One rigid vertex ⟹
reconstructible**: the deck supplies the degree-matched card iso, rigidity
corrects it, `isoOfDeleteVertIso` reassembles. *Graphs with a rigid vertex*
is now a formally verified reconstructible class; every vertex of a regular
graph is rigid (`IsRegularOfDegree.rigidVertex`), and regular
reconstruction is the corollary. The programme's remaining mathematics is
to push rigidity up the decoding ladder below.

**The decoding ladder** — sufficient conditions for rigidity. Two
discoveries (this review) restructure it:

**Discovery A — the shift multiset is always unique.** Fix the matched data
of a card: `D' :=` degree multiset of `G` minus the deleted degree, and
`C :=` card-degree multiset (both deck-determined for the matched pair).
Write `S(t)` for the number of the deleted vertex's neighbours with
*card*-degree `t`, and `C(t)`, `D'(t)` for value-counts. Counting vertices
of `G`-degree `t` among card vertices: non-neighbours contribute `C(t) −
S(t)`, neighbours contribute `S(t−1)` (their card-degree dropped by one),
so

`D'(t) = C(t) − S(t) + S(t−1)`,  i.e.  `S(t) = C(t) − D'(t) + S(t−1)`.

With `S(−1) = 0`, this **recurrence determines `S` completely** — there is
no Hall/chain ambiguity at the multiset level, contrary to what the first
draft of this note expected. Hence: *for every matched pair `(v, σv)`, the
multiset of neighbour degrees `M(v) = S(v) + 1` is deck-determined and
equals `M(σv)`.* (Classically adjacent to "neighbour-degree
reconstructibility", Heinrich et al. Lemma 5 vicinity; the per-matched-pair
recurrence form is the version the programme needs.) The only remaining
ambiguity is ever **within a value class**: which of the `C(t)` card
vertices of degree `t` are the `S(t)` neighbours.

**Discovery B — level 1 by telescoping.** Say `v` is **value-separated** if
each card-degree class is all-neighbours or all-non-neighbours
(equivalently: no `x ∉ N(v)`, `y ∈ N(v)` with `deg x = deg y − 1`). Then
`v` is rigid *with the identity correction*: for the `G`-side counts `n_t`
and `H`-side counts `m_t` of neighbours in the (shared) value class `t`,
both satisfy the same recurrence against the same `D'`, `C`, so
`n_t − m_t = n_{t−1} − m_{t−1} = ⋯ = 0`; value-separation says
`n_t ∈ {0, C(t)}`, hence `m_t = n_t` makes *every* vertex of the class
agree on both sides. **Value-separated vertices are rigid** — a strict
extension of the regular case (where every class is all-or-nothing
trivially), with a fully elementary proof ready to formalize.

The ladder above these:

3. **Refinement-forced**: run color refinement on the card seeded with the
   (now always-available) class-count constraints `S(t)`; rigidity of the
   refined coloring suffices. (The Arvind–Köbler–Verbitsky CR-deck question
   plugs in here.)
4. **Cross-card forced**: markings of `G−v` and `G−w` constrain each other
   through the shared `G−v−w`; global consistency over the deck can force
   rigidity no single card has. This is mechanism M2 in disguise — and
   Discovery A strengthens it: descent now starts from known per-card
   class counts, not from nothing.

**Honest novelty assessment.** The regular case is Kelly-era folklore. The
neighbouring literature is *degree-associated reconstruction* (`drn`,
Ramachandran, Monikandan et al.: one card plus the deleted degree); the
rigid-card criterion as a same-deck theorem, and the Hall-condition multiset
recovery, do not appear there in this form — candidate-novel, pending a
focused search. The mechanism is also exactly what the Heinrich et al.
interval proof does by hand (their "annotated sides" are markings; their
bulk/flank theory is a rigidity proof for interval cards).

**Formal next steps** (ordered):
(a) ~~define rigidity; prove the rigid-card criterion~~ **done**
(`RigidVertex`, `nonempty_iso_of_rigidVertex`);
(b) the shift-recurrence lemma (Discovery A): per-value identity
`D'(t) = C(t) − S(t) + S(t−1)` from `degree_deleteVert`, then uniqueness by
induction on `t` — gives `SameDeck → M_G(v) = M_H(σv)` for matched pairs;
(c) **value-separated ⟹ rigid** (Discovery B): the telescoping
`n_t − m_t = n_{t−1} − m_{t−1}` plus the all-or-nothing case split; corollary:
graphs with a value-separated vertex are reconstructible (strictly extends
`nonempty_iso_of_regular`);
(d) **experiment**: for `n ≤ 10`, compute the fraction of graphs with a
value-separated (resp. rigid) vertex — the complement *is* the wall,
enumerated; if empty up to some `n`, that is a theorem-shaped discovery.

## M2. Deck descent: transition cocycles (structural reframing)

Choosing card isomorphisms `φ_v : G−v ≅ H−σv` for all `v` gives, over each
double deletion `G−v−w`, comparison automorphisms (`φ_w⁻¹ ∘ φ_v`-style
"transition functions"). `G ≅ H` iff the choices can be corrected to agree
globally — i.e., iff a non-abelian 1-cocycle over the card-overlap complex
with coefficients in card-automorphism groups is a coboundary.
**Reconstruction = descent for the deck cover; the obstruction is an
`H¹`.** This is not yet a proof of anything, but it is the right organizing
frame, and the project has unknowingly built half of it: the FixedHost
campaign's *observer cycles* (3469 lines, retained) are precisely cocycle
loops, and its refuted low-slice conjecture says the *truncated* complex
has nonvanishing `H¹` — the live question is whether full overlaps kill it.
Interaction with M1 is the point: **rigidity shrinks the coefficient sheaf**
(from `Aut(card)` to `Aut(marked card)`); descent over smaller fibers
trivializes more often. Composite conjecture worth making precise: *the
obstruction vanishes whenever a spanning "rigidity skeleton" of cards
exists.*

## M3. Stability-then-exact (the dense-regime route)

Same deck ⟹ equal induced counts for **all** patterns below `n` — far
stronger than graphon-closeness; after an optimal alignment `σ`, the
adjacency symmetric difference `Δ` is a structure on which *every* Kelly
count vanishes. Two-step plan in the extremal-combinatorics style:
(i) *stability*: quantify how small `Δ` must be (counting lemmas at exact
scale, not asymptotic); (ii) *exact*: show no nonempty `Δ` below that size
is count-invisible — a finite classification for very small `Δ`
(`|Δ| ≤ 4` slots is a concrete, possibly machine-checkable first case).
Note the suggestive asymmetry: dense graphs are **edge**-reconstructible
(Lovász `m > ½C(n,2)`; Müller `m > n log n`) — the dense regime is where
the exact step has the most existing leverage. Speculative bridge, honestly
labeled: vertex-deck + small `Δ` ⟹ edge-deck-style constraints on the
aligned pair, importing Lovász–Müller machinery into the vertex problem.

## M4. Ruled out (for the record)

Spectral canonical forms (Schwenk cospectrality), lexicographic/extremal
canonization (needs labels — circular as proof, fine as algorithm), "exploit
transitivity" (already easy — see §0), pure counting at face value (Kelly
ceiling; see the rank experiment R6 in the strategy note).

## Where this leaves the programme

M1 is actionable now and partially landed; its experiment (d) converts the
vague wall into an enumerated set of hard instances. M2 gives the wall a
cohomological name and recycles the FixedHost corpus. M3 is the only
mechanism that *prefers* the dense residual class of the reduction chain.
The three interlock: rigidity (M1) shrinks descent fibers (M2); descent
failures localize to small invisible differences (M3). The recommended
sequence: formalize the rigid-card criterion, run the rigidity census,
and aim the first new-class theorem at *graphs with a rigid vertex* — a
class that provably contains all regular graphs and, conjecturally, almost
everything else.

## References

- Bondy (1991), "A graph reconstructor's manual" — regular folklore, manual
  of known reconstructible classes.
- Ramachandran; Monikandan et al. — degree-associated reconstruction
  (`drn`), the card+degree variant of marking.
- Heinrich, Kiyomi, Otachi, Schweitzer (2025), arXiv:2504.02353 — interval
  graphs; their annotated separations are marking-rigidity by hand.
- Arvind, Köbler, Verbitsky (2024), arXiv:2406.09351 — color refinement on
  decks (level 3 of the ladder).
- Kostochka, Nahvi, West, Zirlin (2021+) — cubic graphs from the **2-deck**
  (the genuinely open cubic problem).
- Lovász (1972), Müller (1977) — dense edge-reconstruction (M3's engine).
