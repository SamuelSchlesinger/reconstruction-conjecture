import Reconstruction.Chordal
set_option autoImplicit false

/-!
# Reconstruction Conjecture — A cycle from two internally-disjoint paths

Gluing two paths `p, q : G.Walk u w` (with distinct endpoints, no shared edges,
and disjoint interiors) into a single cycle `p.append q.reverse : G.Walk u u`.
This is how the separator argument forms its cycle: `p` is a shortest path
through one component of `G − S`, `q` through another.

## Main result

* `SimpleGraph.Walk.isCycle_append_reverse` — under edge-disjointness and
  interior (`support.tail`) disjointness, `p.append q.reverse` is a cycle.
-/

namespace SimpleGraph
namespace Walk

variable {V : Type*} {G : SimpleGraph V}

/-- **A cycle from two internally-disjoint paths.** If `p q : G.Walk u w` are
paths with `u ≠ w`, no shared edges, and disjoint interiors (`support.tail`),
then `p.append q.reverse` is a cycle. -/
theorem isCycle_append_reverse {u w : V} {p q : G.Walk u w}
    (hp : p.IsPath) (hq : q.IsPath) (hne : u ≠ w)
    (hedj : List.Disjoint p.edges q.edges)
    (hsupp : List.Disjoint p.support.tail q.reverse.support.tail) :
    (p.append q.reverse).IsCycle := by
  rw [isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · -- edges nodup (IsTrail)
    rw [isTrail_def, edges_append, edges_reverse]
    refine List.Nodup.append hp.isTrail.edges_nodup
      (List.nodup_reverse.mpr hq.isTrail.edges_nodup) ?_
    rwa [List.disjoint_reverse_right]
  · -- nonempty
    intro hnil
    have hlen0 : (p.append q.reverse).length = 0 := by rw [hnil, length_nil]
    rw [length_append, length_reverse] at hlen0
    exact (not_nil_of_ne hne) (nil_iff_length_eq.mpr (show p.length = 0 by omega))
  · -- interior nodup
    rw [tail_support_append]
    exact List.Nodup.append (hp.support_nodup.sublist (List.tail_sublist _))
      (hq.reverse.support_nodup.sublist (List.tail_sublist _)) hsupp

end Walk
end SimpleGraph
