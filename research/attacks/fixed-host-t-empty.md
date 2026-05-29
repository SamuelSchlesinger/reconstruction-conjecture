# Fixed-Host Singleton: the `T = empty` Full-Slice Target

This note records the corrected attack after the low-slice-only version was
falsified.

## Low slice is not enough

With `T = empty`, the low slice has one card:

```text
K - a  ~=_S  K - b.
```

The minimum deleted-star error of this one card need not be zero.  A concrete
uncolored example has vertices `0..8`, `a = 0`, `b = 1`, `S = empty`, and
edges

```text
01 02 03 04
14 15 17
23 38
45
67 68 78
```

There are two card isomorphisms `K - 0 -> K - 1`; the best one has star error
`2`, and `Aut(K)` is trivial.  Thus the low-slice minimum-error-zero statement
is false even when `S = empty`.

This example does not satisfy the full singleton-colored deck equality.  The
complementary cards are exactly the missing information.

## Full-slice normalization

For the full `T = empty` singleton switch, equality of the decks of
`(K,S,{a})` and `(K,S,{b})` splits by second-color cardinality.

1. The unique zero-second-color card gives a low card isomorphism
   `e0 : K - a ~=_S K - b`.
2. The remaining cards give a rooted complementary trade: every card deleting
   `x != a` on the left is matched to a card deleting `y != b` on the right,
   and the card isomorphism sends the unique second-colored root `a` to `b`.

The complementary trade is stronger than an arbitrary card matching.  If
`x != a` is matched to `y != b`, then the rooted card isomorphism gives

```text
deg_{K-x}(a) = deg_{K-y}(b).
```

The low card gives `deg_K(a) = deg_K(b)`.  Therefore

```text
K.Adj(a,x) <-> K.Adj(b,y).
```

So every complementary matched deleted vertex preserves root adjacency.  Any
positive low-card star error is therefore not an intrinsic degree defect; it is
an alignment defect between the low card isomorphism and the complementary
root-preserving trade.

## Transition-cycle formulation

Fix a low card isomorphism

```text
e0 : K - a -> K - b
```

and a complementary matching

```text
tau : V \\ {a} -> V \\ {b}
```

where each `x` is matched by a rooted card isomorphism
`K - x ~= K - tau(x)` sending `a` to `b`.  Define the transition permutation
on `V \\ {a}` by

```text
pi = e0^{-1} o tau.
```

Let

```text
A(x) = 1_{K.Adj(a,x)}
B0(x) = 1_{K.Adj(b,e0(x))}.
```

Root adjacency preservation along `tau` gives

```text
B0(x) = A(pi^{-1}(x)).
```

Hence the low star defect at `x` is

```text
A(x) - B0(x) = A(x) - A(pi^{-1}(x)).
```

Consequently every transition cycle has balanced positive and negative root
adjacency charge.  This recovers the parity phenomenon, but with more
structure: defects live on cycles of `pi`, and complementary rooted cards
constrain those cycles.

## Next proof obligation

The right target is not low-slice descent.  It is:

```text
No nontrivial transition cycle compatible with the full rooted complementary
card types can survive without a zero-star card.
```

The smallest nontrivial case is an exact two-error cycle: one lost root
neighbor and one gained root neighbor.  In the known-host language this is the
single-switch state `(C,S,p,q)` with `A = S union {p}` and `B = S union {q}`.
The existing rooted triangle and rooted two-step formulas are the right first
invariants:

```text
P_w(A) - P_w(B) =
  -1  if w is a lost witness,
  +1  if w is a gained witness,
   0  otherwise,
```

with endpoint charges at `p` and `q`.  Cycle balance forces these charges to
occur in zero-sum transition cycles.  A proof of the `T = empty` full-slice
case should first close this exact two-error edge-slide case, then induct on
`|N(a) triangle N(b)| / 2` by cutting or shortening a balanced transition
cycle.

## Practical next steps

1. Formalize the complementary root-adjacency lemma:
   rooted complementary card match plus low degree equality implies
   `Adj(a,x) <-> Adj(b,y)`.
2. Define the low/complementary transition permutation `pi`.
3. Prove balanced charge on every `pi`-cycle.
4. Close or computationally refute the exact two-error edge-slide case.
5. Only then return to the general all-inactive `T = empty` fork.

