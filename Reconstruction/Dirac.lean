import Reconstruction.MinimalSeparatorClique
set_option autoImplicit false

/-!
# Reconstruction Conjecture — Dirac's theorem (corollaries of the clique-separator lemma)

The two structural corollaries of `minimalSeparatorClique` (a minimal separator
of a chordal graph is a clique):

* `SimpleGraph.diracCliqueSeparator` — a finite chordal connected non-complete
  graph has a clique separator.  Proof: a non-complete connected graph has a
  separator (`{a,b}ᶜ` for a non-adjacent pair `a, b`); a `⊆`-minimal one exists
  (finite), and it is a clique by `minimalSeparatorClique`.
* `SimpleGraph.diracSimplicial` — a finite nonempty chordal graph has a
  simplicial vertex (Dirac 1961).  Proof by strong induction on `|V|`, peeling
  off a component across a clique separator.

`DiracCliqueSeparator V` (the target `Prop`) is stated without finiteness; it is
provable only for finite `V` (Dirac's theorem fails for infinite graphs), so the
theorem carries a `[Fintype V]` instance.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A finite connected non-complete graph has an inclusion-minimal separator. -/
theorem exists_minimal_separator [Finite V] (hconn : G.Connected) (hne : G ≠ ⊤) :
    ∃ S : Set V, G.IsSeparator S ∧ ∀ T : Set V, T ⊂ S → ¬ G.IsSeparator T := by
  classical
  -- a non-adjacent pair (the graph is not complete)
  obtain ⟨a, b, hab, hnadj⟩ : ∃ a b : V, a ≠ b ∧ ¬ G.Adj a b := by
    by_contra h
    push_neg at h
    exact hne (by ext u v; rw [top_adj]; exact ⟨fun hadj => hadj.ne, h u v⟩)
  have haS : a ∈ ({a, b} : Set V) := Set.mem_insert a _
  have hbS : b ∈ ({a, b} : Set V) := Set.mem_insert_of_mem a rfl
  -- `{a,b}` induces the empty graph (its only possible edge `a–b` is absent)
  have hbot : G.induce ({a, b} : Set V) = ⊥ := by
    ext u v
    obtain ⟨u, hu⟩ := u
    obtain ⟨v, hv⟩ := v
    simp only [induce_adj, bot_adj, iff_false]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact G.irrefl
    · exact hnadj
    · exact fun h => hnadj h.symm
    · exact G.irrefl
  -- hence `{a,b}ᶜ` separates `a` from `b`
  have hsep0 : G.IsSeparator ({a, b}ᶜ) := by
    refine ⟨hconn, ?_, ?_⟩
    · rw [compl_compl]; exact ⟨a, haS⟩
    · rw [compl_compl, hbot]
      intro hc
      exact hab (Subtype.ext_iff.mp (reachable_bot.mp (hc.preconnected ⟨a, haS⟩ ⟨b, hbS⟩)))
  -- pick a `⊆`-minimal separator
  obtain ⟨S, hSsep, hSmin⟩ :=
    (Set.toFinite {T : Set V | G.IsSeparator T}).exists_minimal ⟨_, hsep0⟩
  exact ⟨S, hSsep, fun T hTS hTsep => absurd (hSmin hTsep hTS.1) hTS.2⟩

/-- **Dirac's clique-separator theorem.** A finite chordal connected non-complete
graph has a separator that induces a clique. -/
theorem diracCliqueSeparator [Finite V] : DiracCliqueSeparator V := by
  intro G hchord hne hconn
  obtain ⟨S, hSsep, hSmin⟩ := exists_minimal_separator hconn hne
  exact ⟨S, minimalSeparatorClique G S hchord hSsep hSmin, hSsep⟩

/-- **Simplicial-vertex transfer.** If every `G`-neighbour of `v` lies in `T` and
`v` is simplicial in the induced subgraph `G[T]`, then `v` is simplicial in `G`.
This is the bridge that turns a simplicial vertex found by induction on a smaller
induced subgraph into a simplicial vertex of the whole graph. -/
theorem isSimplicial_of_induce {T : Set V} {v : V} (hv : v ∈ T)
    (hsub : G.neighborSet v ⊆ T) (h : (G.induce T).IsSimplicial ⟨v, hv⟩) :
    G.IsSimplicial v := by
  intro p hp q hq hpq
  have hpm : (⟨p, hsub hp⟩ : T) ∈ (G.induce T).neighborSet ⟨v, hv⟩ := hp
  have hqm : (⟨q, hsub hq⟩ : T) ∈ (G.induce T).neighborSet ⟨v, hv⟩ := hq
  exact h hpm hqm (fun heq => hpq (congrArg Subtype.val heq))

/-- **Extracting a simplicial vertex from the induction hypothesis.** Suppose
`G[T]` is complete or has two non-adjacent simplicial vertices (the inductive
dichotomy), `T' ⊆ T` is nonempty, every `T'`-vertex keeps its `G`-neighbours in
`T`, and `T \ T'` is a clique. Then some vertex of `T'` is simplicial in `G`.
(In the complete case any `T'`-vertex works; otherwise the two non-adjacent
simplicial vertices cannot both avoid `T'`, since `T \ T'` is a clique.) -/
theorem exists_simplicial_of_induce_disj {T T' : Set V} (hT'T : T' ⊆ T)
    (hT'ne : T'.Nonempty) (hnbhd : ∀ v ∈ T', G.neighborSet v ⊆ T)
    (hclique : ∀ p ∈ T, ∀ q ∈ T, p ∉ T' → q ∉ T' → p ≠ q → G.Adj p q)
    (hdisj : G.induce T = ⊤ ∨ ∃ a b : T, a ≠ b ∧ ¬ (G.induce T).Adj a b ∧
        (G.induce T).IsSimplicial a ∧ (G.induce T).IsSimplicial b) :
    ∃ v ∈ T', G.IsSimplicial v := by
  rcases hdisj with htop | ⟨a, b, hab, hnadj, hsa, hsb⟩
  · obtain ⟨t, ht⟩ := hT'ne
    exact ⟨t, ht, isSimplicial_of_induce (hT'T ht) (hnbhd t ht)
      (by rw [htop]; exact isSimplicial_top _)⟩
  · by_cases haT' : (a : V) ∈ T'
    · exact ⟨a, haT', isSimplicial_of_induce a.2 (hnbhd a haT') hsa⟩
    · by_cases hbT' : (b : V) ∈ T'
      · exact ⟨b, hbT', isSimplicial_of_induce b.2 (hnbhd b hbT') hsb⟩
      · exact absurd (hclique a a.2 b b.2 haT' hbT' (fun h => hab (Subtype.ext h))) hnadj

universe u

/-- The strong inductive form of Dirac's theorem, on a card-bounded family of
graphs (one universe, so the induced-subgraph recursion stays in type): a finite
chordal graph is complete or has two non-adjacent simplicial vertices. -/
theorem dirac_aux : ∀ (n : ℕ) (W : Type u) [Fintype W] (H : SimpleGraph W),
    Fintype.card W ≤ n → H.IsChordal →
    H = ⊤ ∨ ∃ a b : W, a ≠ b ∧ ¬ H.Adj a b ∧ H.IsSimplicial a ∧ H.IsSimplicial b := by
  classical
  intro n
  induction n with
  | zero =>
    intro W _ H hcard _
    left
    have hE : IsEmpty W := Fintype.card_eq_zero_iff.mp (Nat.le_zero.mp hcard)
    ext a b
    exact (hE.false a).elim
  | succ n ih =>
    intro W _ H hcard hchord'
    by_cases hcomplete : H = ⊤
    · exact Or.inl hcomplete
    · right
      -- recursion on a strictly smaller induced subgraph
      have hext : ∀ (T T' : Set W), T' ⊆ T → T'.Nonempty → (∃ w, w ∉ T) →
          (∀ v ∈ T', H.neighborSet v ⊆ T) →
          (∀ p ∈ T, ∀ q ∈ T, p ∉ T' → q ∉ T' → p ≠ q → H.Adj p q) →
          ∃ v ∈ T', H.IsSimplicial v := by
        intro T T' hT'T hT'ne hout hnbhd hclique
        obtain ⟨w, hw⟩ := hout
        have hlt : Fintype.card ↥T < Fintype.card W := Fintype.card_subtype_lt hw
        exact exists_simplicial_of_induce_disj hT'T hT'ne hnbhd hclique
          (ih ↥T (H.induce T) (by omega) (hchord'.induce T))
      by_cases hconn : H.Connected
      · -- connected, not complete: peel a component off a clique separator
        obtain ⟨S, hSclique, hSsep⟩ := diracCliqueSeparator H hchord' hcomplete hconn
        obtain ⟨x, y, hxy⟩ : ∃ x y : ↥Sᶜ, ¬ (H.induce Sᶜ).Reachable x y := by
          by_contra hc
          push_neg at hc
          haveI : Nonempty ↥Sᶜ := hSsep.2.1.to_subtype
          exact hSsep.2.2 ⟨hc⟩
        have hcompne : (H.induce Sᶜ).connectedComponentMk x
            ≠ (H.induce Sᶜ).connectedComponentMk y := fun h => hxy (ConnectedComponent.eq.mp h)
        -- a simplicial vertex of `H` in `x'`'s component, for any separated pair
        have hside : ∀ x' y' : ↥Sᶜ, (H.induce Sᶜ).connectedComponentMk x'
            ≠ (H.induce Sᶜ).connectedComponentMk y' → ∃ v, ∃ (hv : v ∉ S),
            (H.induce Sᶜ).connectedComponentMk ⟨v, hv⟩
              = (H.induce Sᶜ).connectedComponentMk x' ∧ H.IsSimplicial v := by
          intro x' y' hne'
          set Tu : Set W := {v | ∃ (h : v ∉ S), (H.induce Sᶜ).connectedComponentMk ⟨v, h⟩
            = (H.induce Sᶜ).connectedComponentMk x'} with hTu
          have hyne : y'.val ∉ S ∪ Tu := by
            rintro (hyS | ⟨h, hc⟩)
            · exact y'.2 hyS
            · exact hne' hc.symm
          have hnb : ∀ v ∈ Tu, H.neighborSet v ⊆ S ∪ Tu := by
            rintro v ⟨hv, hvc⟩ p hp
            by_cases hpS : p ∈ S
            · exact Or.inl hpS
            · exact Or.inr ⟨hpS, (adj_connectedComponentMk_eq hp hv hpS).symm.trans hvc⟩
          have hcl : ∀ p ∈ S ∪ Tu, ∀ q ∈ S ∪ Tu, p ∉ Tu → q ∉ Tu → p ≠ q → H.Adj p q := by
            rintro p (hpS | hpTu) q (hqS | hqTu) hpnTu hqnTu hpq
            · exact hSclique hpS hqS hpq
            · exact absurd hqTu hqnTu
            · exact absurd hpTu hpnTu
            · exact absurd hpTu hpnTu
          obtain ⟨v, ⟨hv, hvc⟩, hvsimp⟩ := hext (S ∪ Tu) Tu Set.subset_union_right
            ⟨x'.val, x'.2, rfl⟩ ⟨y'.val, hyne⟩ hnb hcl
          exact ⟨v, hv, hvc, hvsimp⟩
        obtain ⟨vu, hvu, hvuc, hvusimp⟩ := hside x y hcompne
        obtain ⟨vw, hvw, hvwc, hvwsimp⟩ := hside y x hcompne.symm
        refine ⟨vu, vw, ?_, ?_, hvusimp, hvwsimp⟩
        · intro h; subst h
          exact hcompne (hvuc.symm.trans hvwc)
        · intro hadj
          exact hcompne (hvuc.symm.trans
            ((adj_connectedComponentMk_eq hadj hvu hvw).trans hvwc))
      · -- disconnected: peel two whole components
        haveI hNE : Nonempty W := by
          rw [← not_isEmpty_iff]
          intro hE
          exact hcomplete (by ext a b; exact (hE.false a).elim)
        obtain ⟨u₀, w₀, hr⟩ : ∃ u₀ w₀ : W, ¬ H.Reachable u₀ w₀ := by
          by_contra hc
          push_neg at hc
          exact hconn ⟨hc⟩
        have hcompne : H.connectedComponentMk u₀ ≠ H.connectedComponentMk w₀ :=
          fun h => hr (ConnectedComponent.eq.mp h)
        have hsideD : ∀ z₀ w₀' : W, H.connectedComponentMk z₀ ≠ H.connectedComponentMk w₀' →
            ∃ v, H.connectedComponentMk v = H.connectedComponentMk z₀ ∧ H.IsSimplicial v := by
          intro z₀ w₀' hne'
          set Tz : Set W := {v | H.connectedComponentMk v = H.connectedComponentMk z₀} with hTz
          have hwout : w₀' ∉ Tz := fun hc => hne' hc.symm
          have hnb : ∀ v ∈ Tz, H.neighborSet v ⊆ Tz := by
            rintro v hv p hp
            exact (ConnectedComponent.connectedComponentMk_eq_of_adj hp).symm.trans hv
          have hcl : ∀ p ∈ Tz, ∀ q ∈ Tz, p ∉ Tz → q ∉ Tz → p ≠ q → H.Adj p q :=
            fun p hp _ _ hpn _ _ => absurd hp hpn
          obtain ⟨v, hvc, hvsimp⟩ := hext Tz Tz subset_rfl ⟨z₀, rfl⟩ ⟨w₀', hwout⟩ hnb hcl
          exact ⟨v, hvc, hvsimp⟩
        obtain ⟨vu, hvuc, hvusimp⟩ := hsideD u₀ w₀ hcompne
        obtain ⟨vw, hvwc, hvwsimp⟩ := hsideD w₀ u₀ hcompne.symm
        refine ⟨vu, vw, ?_, ?_, hvusimp, hvwsimp⟩
        · intro h; subst h
          exact hcompne (hvuc.symm.trans hvwc)
        · intro hadj
          exact hcompne (hvuc.symm.trans
            ((ConnectedComponent.connectedComponentMk_eq_of_adj hadj).trans hvwc))

/-- **Dirac's simplicial-vertex theorem (1961).** Every finite nonempty chordal
graph has a simplicial vertex. -/
theorem diracSimplicial [Fintype V] : DiracSimplicial V := by
  intro G hchord hne
  rcases dirac_aux (Fintype.card V) V G le_rfl hchord with htop | ⟨a, _, _, _, hsa, _⟩
  · obtain ⟨v⟩ := hne
    exact ⟨v, by rw [htop]; exact isSimplicial_top v⟩
  · exact ⟨a, hsa⟩

end SimpleGraph
