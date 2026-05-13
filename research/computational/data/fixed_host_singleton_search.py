"""fixed_host_singleton_search.py

Small-n probes for the fixed-host singleton campaign in proof_sketch.tex.

The search enumerates fixed hosts (K,S,T,a,b), compares the two-colored
fixed-host deletion decks of (K,S,T ∪ {a}) and (K,S,T ∪ {b}), checks orbit
success under Aut(K,S), and samples the local two-hole matches used in the
rectangular/named-deletion analysis.

This is deliberately a tiny brute-force script.  It is meant to falsify local
proof claims at n <= 5 or to produce candidate witnesses for more focused
inspection, not to compete with nauty-based reconstruction verification.

Usage:
    python fixed_host_singleton_search.py 5
    python fixed_host_singleton_search.py 6 --max-states 200000
    python fixed_host_singleton_search.py 6 --atlas --skip-local --max-states 200000
    python fixed_host_singleton_search.py 6 --labelled --max-hosts 200 --max-states 200000
    python fixed_host_singleton_search.py 6 --labelled --slice-probe --max-states 100000
    python fixed_host_singleton_search.py 6 --atlas --orbit-probe
    python fixed_host_singleton_search.py --c3-counterexample
    python fixed_host_singleton_search.py 6 --atlas --zero-star-pair-probe --max-states 100000
    python fixed_host_singleton_search.py 6 --atlas --min-error-probe --max-states 100000
    python fixed_host_singleton_search.py 8 --random-hosts 50 --zero-star-pair-probe --first-samples 8
    python fixed_host_singleton_search.py 8 --random-hosts 200 --nx-slice-orbit-probe --first-samples 20
    python fixed_host_singleton_search.py 7 --random-hosts 200 --skip-local --max-states 50000
"""

from __future__ import annotations

import argparse
import itertools
import random
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from typing import Iterable

EdgeSet = frozenset[tuple[int, int]]


def all_labelled_graphs(n: int) -> Iterable[EdgeSet]:
    pairs = list(itertools.combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        yield frozenset(pairs[i] for i in range(len(pairs)) if (mask >> i) & 1)


def random_labelled_graphs(n: int, count: int, seed: int) -> Iterable[EdgeSet]:
    rng = random.Random(seed)
    pairs = list(itertools.combinations(range(n), 2))
    max_mask = 1 << len(pairs)
    seen: set[int] = set()
    while len(seen) < count:
        mask = rng.randrange(max_mask)
        if mask in seen:
            continue
        seen.add(mask)
        yield frozenset(pairs[i] for i in range(len(pairs)) if (mask >> i) & 1)


def has_edge(edges: EdgeSet, u: int, v: int) -> bool:
    if u == v:
        return False
    a, b = (u, v) if u < v else (v, u)
    return (a, b) in edges


@lru_cache(maxsize=None)
def graph_label(vertices: tuple[int, ...], edges: EdgeSet) -> tuple[int, ...]:
    best: tuple[int, ...] | None = None
    for perm in itertools.permutations(vertices):
        row: list[int] = []
        for i in perm:
            for j in perm:
                row.append(1 if has_edge(edges, i, j) else 0)
        lab = tuple(row)
        if best is None or lab < best:
            best = lab
    assert best is not None
    return best


def graph_reps(n: int) -> list[EdgeSet]:
    reps: dict[tuple[int, ...], EdgeSet] = {}
    vertices = tuple(range(n))
    for edges in all_labelled_graphs(n):
        reps.setdefault(graph_label(vertices, edges), edges)
    return [reps[k] for k in sorted(reps)]


def atlas_graph_reps(n: int) -> list[EdgeSet]:
    import networkx as nx

    reps: list[EdgeSet] = []
    for graph in nx.graph_atlas_g():
        if graph.number_of_nodes() != n:
            continue
        mapping = {v: i for i, v in enumerate(sorted(graph.nodes()))}
        edges = frozenset(
            (min(mapping[u], mapping[v]), max(mapping[u], mapping[v]))
            for u, v in graph.edges()
        )
        reps.append(edges)
    return reps


@lru_cache(maxsize=None)
def colored_label(
    vertices: tuple[int, ...], edges: EdgeSet, first: frozenset[int], second: frozenset[int]
) -> tuple[int, ...]:
    best: tuple[int, ...] | None = None
    for perm in itertools.permutations(vertices):
        row: list[int] = []
        for v in perm:
            row.append(1 if v in first else 0)
            row.append(1 if v in second else 0)
        for i in perm:
            for j in perm:
                row.append(1 if has_edge(edges, i, j) else 0)
        lab = tuple(row)
        if best is None or lab < best:
            best = lab
    assert best is not None
    return best


@lru_cache(maxsize=None)
def fixed_host_deck(
    n: int, edges: EdgeSet, first: frozenset[int], second: frozenset[int]
) -> tuple[tuple[int, ...], ...]:
    cards: list[tuple[int, ...]] = []
    for z in range(n):
        vertices = tuple(v for v in range(n) if v != z)
        cards.append(colored_label(vertices, edges, first - {z}, second - {z}))
    return tuple(sorted(cards))


@lru_cache(maxsize=None)
def deleted_colored_label(
    n: int, edges: EdgeSet, delete: set[int] | frozenset[int], first: frozenset[int], second: frozenset[int]
) -> tuple[int, ...]:
    delete = frozenset(delete)
    vertices = tuple(v for v in range(n) if v not in delete)
    return colored_label(vertices, edges, first - delete, second - delete)


def powerset(n: int) -> Iterable[frozenset[int]]:
    verts = tuple(range(n))
    for mask in range(1 << n):
        yield frozenset(v for i, v in enumerate(verts) if (mask >> i) & 1)


def automorphisms_preserving_first(
    n: int, edges: EdgeSet, first: frozenset[int]
) -> Iterable[tuple[int, ...]]:
    verts = tuple(range(n))
    for perm in itertools.permutations(verts):
        ok = True
        for v in verts:
            if (v in first) != (perm[v] in first):
                ok = False
                break
        if not ok:
            continue
        for i in range(n):
            for j in range(i + 1, n):
                if has_edge(edges, i, j) != has_edge(edges, perm[i], perm[j]):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            yield perm


def orbit_success(
    n: int, edges: EdgeSet, first: frozenset[int], left: frozenset[int], right: frozenset[int]
) -> bool:
    for perm in automorphisms_preserving_first(n, edges, first):
        if frozenset(perm[v] for v in left) == right:
            return True
    return False


def solving_automorphisms(
    n: int,
    edges: EdgeSet,
    first: frozenset[int],
    source: frozenset[int],
    target: frozenset[int],
) -> Iterable[tuple[int, ...]]:
    for perm in automorphisms_preserving_first(n, edges, first):
        if frozenset(perm[v] for v in source) == target:
            yield perm


def low_internal_zero_star(
    n: int, edges: EdgeSet, first: frozenset[int], T: frozenset[int], a: int, b: int
) -> bool:
    """A solving automorphism fixing an internal low-slice deleted vertex.

    This is equivalent to a zero-star transport edge at some z in T, but it is
    intentionally only a sufficient local win condition for the proof sketch,
    not a conjectured replacement for one-slice orbit reconstruction.
    """
    left = T | {a}
    right = T | {b}
    return any(
        any(perm[z] == z for z in T)
        for perm in solving_automorphisms(n, edges, first, right, left)
    )


def direct_low(
    n: int, edges: EdgeSet, first: frozenset[int], T: frozenset[int], a: int, b: int
) -> bool:
    return deleted_colored_label(n, edges, frozenset({a}), first, T) == deleted_colored_label(
        n, edges, frozenset({b}), first, T
    )


def direct_complementary(
    n: int, edges: EdgeSet, first: frozenset[int], T: frozenset[int], a: int, b: int
) -> bool:
    return deleted_colored_label(n, edges, frozenset({b}), first, T | {a}) == deleted_colored_label(
        n, edges, frozenset({a}), first, T | {b}
    )


@lru_cache(maxsize=None)
def low_slice_deck(
    n: int, edges: EdgeSet, first: frozenset[int], T: frozenset[int], a: int
) -> tuple[tuple[int, ...], ...]:
    second = T | {a}
    return tuple(
        sorted(deleted_colored_label(n, edges, frozenset({z}), first, second) for z in (T | {a}))
    )


@lru_cache(maxsize=None)
def complementary_slice_deck(
    n: int, edges: EdgeSet, first: frozenset[int], T: frozenset[int], a: int, b: int
) -> tuple[tuple[int, ...], ...]:
    second = T | {a}
    outside = frozenset(v for v in range(n) if v not in T and v != a and v != b)
    return tuple(
        sorted(deleted_colored_label(n, edges, frozenset({z}), first, second) for z in (outside | {b}))
    )


@dataclass(frozen=True)
class MatchStats:
    total: int = 0
    name_coherent: int = 0
    pure_low: int = 0
    pure_low_nonzero_error: int = 0
    pure_comp: int = 0
    pure_comp_nonzero_error: int = 0
    mixed: int = 0
    mixed_nonzero_both: int = 0


@dataclass(frozen=True)
class PairMinError:
    error: int
    min_isomorphisms: int
    active_first_error: bool
    inactive_first_error: bool


def two_hole_isomorphisms(
    n: int,
    edges: EdgeSet,
    first: frozenset[int],
    T: frozenset[int],
    a: int,
    b: int,
    t: int,
    o: int,
    tp: int,
    op: int,
) -> Iterable[dict[int, int]]:
    domain = tuple(v for v in range(n) if v not in {t, o})
    codomain = tuple(v for v in range(n) if v not in {tp, op})
    left_second = T | {a}
    right_second = T | {b}
    for image_tuple in itertools.permutations(codomain):
        f = dict(zip(domain, image_tuple))
        ok = True
        for v in domain:
            if (v in first) != (f[v] in first):
                ok = False
                break
            if (v in left_second) != (f[v] in right_second):
                ok = False
                break
        if not ok:
            continue
        for i, u in enumerate(domain):
            for v in domain[i + 1 :]:
                if has_edge(edges, u, v) != has_edge(edges, f[u], f[v]):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            yield f


def extension_error_size(
    n: int, edges: EdgeSet, f: dict[int, int], hole_left: int, hole_right: int
) -> int:
    return sum(
        1
        for z in f
        if has_edge(edges, hole_left, z) != has_edge(edges, hole_right, f[z])
    )


def local_match_stats(
    n: int, edges: EdgeSet, first: frozenset[int], T: frozenset[int], a: int, b: int
) -> MatchStats:
    O = frozenset(v for v in range(n) if v not in T and v != a and v != b)
    counts = Counter()
    if not T or not O:
        return MatchStats()
    for t in T:
        for o in O:
            for tp in T:
                for op in O:
                    for f in two_hole_isomorphisms(n, edges, first, T, a, b, t, o, tp, op):
                        counts["total"] += 1
                        low_defect = f[a] != b
                        comp_defect = f[b] != a
                        err_o = extension_error_size(n, edges, f, o, op)
                        err_t = extension_error_size(n, edges, f, t, tp)
                        if not low_defect and not comp_defect:
                            counts["name_coherent"] += 1
                        elif low_defect and not comp_defect:
                            counts["pure_low"] += 1
                            if err_o != 0:
                                counts["pure_low_nonzero_error"] += 1
                        elif comp_defect and not low_defect:
                            counts["pure_comp"] += 1
                            if err_t != 0:
                                counts["pure_comp_nonzero_error"] += 1
                        else:
                            counts["mixed"] += 1
                            if err_o != 0 and err_t != 0:
                                counts["mixed_nonzero_both"] += 1
    return MatchStats(**{field: counts[field] for field in MatchStats.__dataclass_fields__})


def select_host_reps(
    n: int,
    labelled: bool,
    max_hosts: int | None,
    random_hosts: int | None,
    seed: int,
    atlas: bool,
) -> tuple[list[EdgeSet], str]:
    if random_hosts is not None:
        reps = list(random_labelled_graphs(n, random_hosts, seed))
        host_label = f"{len(reps)} random labelled host graphs (seed={seed})"
    elif atlas:
        reps = atlas_graph_reps(n)
        if max_hosts is not None:
            reps = reps[:max_hosts]
        host_label = f"{len(reps)} graph-atlas host representatives"
    elif labelled:
        reps_iter = all_labelled_graphs(n)
        if max_hosts is not None:
            reps = list(itertools.islice(reps_iter, max_hosts))
            host_label = f"{len(reps)} labelled host graphs"
        else:
            reps = list(reps_iter)
            host_label = f"{len(reps)} labelled host graphs"
    else:
        reps = graph_reps(n)
        if max_hosts is not None:
            reps = reps[:max_hosts]
        host_label = f"{len(reps)} host graph isomorphism representatives"
    return reps, host_label


def run(
    n: int,
    max_states: int | None,
    labelled: bool,
    max_hosts: int | None,
    random_hosts: int | None,
    seed: int,
    skip_local: bool,
    atlas: bool,
) -> None:
    reps, host_label = select_host_reps(n, labelled, max_hosts, random_hosts, seed, atlas)
    print(f"n={n}: {host_label}")
    examined = 0
    equal_deck = 0
    orbit_fail = 0
    no_direct = 0
    low_direct = 0
    comp_direct = 0
    both_direct = 0
    agg = Counter()
    example_one_sided: tuple[EdgeSet, frozenset[int], frozenset[int], int, int, MatchStats] | None = None

    for gi, edges in enumerate(reps, start=1):
        for first in powerset(n):
            for T in powerset(n):
                outside = [v for v in range(n) if v not in T]
                for a in outside:
                    for b in outside:
                        if a == b:
                            continue
                        examined += 1
                        if max_states is not None and examined > max_states:
                            print(f"stopped after --max-states={max_states}")
                            print_summary(
                                examined - 1,
                                equal_deck,
                                orbit_fail,
                                no_direct,
                                low_direct,
                                comp_direct,
                                both_direct,
                                agg,
                                example_one_sided,
                            )
                            return
                        left = T | {a}
                        right = T | {b}
                        if fixed_host_deck(n, edges, first, left) != fixed_host_deck(n, edges, first, right):
                            continue
                        equal_deck += 1
                        if not orbit_success(n, edges, first, left, right):
                            orbit_fail += 1
                            print("ORBIT FAILURE CANDIDATE")
                            print(f"edges={sorted(edges)} first={sorted(first)} T={sorted(T)} a={a} b={b}")
                        has_low_direct = direct_low(n, edges, first, T, a, b)
                        has_comp_direct = direct_complementary(n, edges, first, T, a, b)
                        if has_low_direct:
                            low_direct += 1
                        if has_comp_direct:
                            comp_direct += 1
                        if has_low_direct and has_comp_direct:
                            both_direct += 1
                        if not has_low_direct and not has_comp_direct:
                            no_direct += 1
                        if not skip_local:
                            stats = local_match_stats(n, edges, first, T, a, b)
                            for k, v in stats.__dict__.items():
                                agg[k] += v
                            if (
                                example_one_sided is None
                                and (stats.pure_low_nonzero_error or stats.pure_comp_nonzero_error)
                            ):
                                example_one_sided = (edges, first, T, a, b, stats)
        if gi % 10 == 0 or gi == len(reps):
            print(f"  host reps processed: {gi}/{len(reps)}; equal-deck states so far: {equal_deck}")

    print_summary(
        examined,
        equal_deck,
        orbit_fail,
        no_direct,
        low_direct,
        comp_direct,
        both_direct,
        agg,
        example_one_sided,
    )


def run_slice_probe(
    n: int,
    max_states: int | None,
    labelled: bool,
    max_hosts: int | None,
    random_hosts: int | None,
    seed: int,
    atlas: bool,
) -> None:
    reps, host_label = select_host_reps(n, labelled, max_hosts, random_hosts, seed, atlas)
    print(f"n={n}: {host_label}")
    print("slice probe: testing one-slice equality against endpoint direct cancellation")
    counts = Counter()
    examples: list[tuple[str, EdgeSet, frozenset[int], frozenset[int], int, int]] = []

    for gi, edges in enumerate(reps, start=1):
        for first in powerset(n):
            for T in powerset(n):
                outside = [v for v in range(n) if v not in T]
                for a in outside:
                    for b in outside:
                        if a == b:
                            continue
                        if max_states is not None and counts["states"] >= max_states:
                            print(f"stopped after --max-states={max_states}")
                            print_slice_probe_summary(counts, examples)
                            return
                        counts["states"] += 1

                        low_eq = low_slice_deck(n, edges, first, T, a) == low_slice_deck(
                            n, edges, first, T, b
                        )
                        comp_eq = complementary_slice_deck(
                            n, edges, first, T, a, b
                        ) == complementary_slice_deck(n, edges, first, T, b, a)
                        full_eq = fixed_host_deck(n, edges, first, T | {a}) == fixed_host_deck(
                            n, edges, first, T | {b}
                        )

                        if full_eq:
                            counts["full_eq"] += 1
                        if low_eq:
                            counts["low_eq"] += 1
                            if full_eq:
                                counts["low_eq_full_eq"] += 1
                            if direct_low(n, edges, first, T, a, b):
                                counts["low_eq_low_direct"] += 1
                            elif len(examples) < 5:
                                examples.append(("low-no-direct", edges, first, T, a, b))
                        if comp_eq:
                            counts["comp_eq"] += 1
                            if full_eq:
                                counts["comp_eq_full_eq"] += 1
                            if direct_complementary(n, edges, first, T, a, b):
                                counts["comp_eq_comp_direct"] += 1
                            elif len(examples) < 5:
                                examples.append(("comp-no-direct", edges, first, T, a, b))
                        if low_eq and comp_eq:
                            counts["both_slices_eq"] += 1
                        if low_eq and not full_eq and len(examples) < 5:
                            examples.append(("low-not-full", edges, first, T, a, b))
                        if comp_eq and not full_eq and len(examples) < 5:
                            examples.append(("comp-not-full", edges, first, T, a, b))
        if gi % 10 == 0 or gi == len(reps):
            print(f"  host reps processed: {gi}/{len(reps)}; low-slice equal states so far: {counts['low_eq']}")

    print_slice_probe_summary(counts, examples)


def run_orbit_probe(
    n: int,
    max_states: int | None,
    labelled: bool,
    max_hosts: int | None,
    random_hosts: int | None,
    seed: int,
    atlas: bool,
) -> None:
    reps, host_label = select_host_reps(n, labelled, max_hosts, random_hosts, seed, atlas)
    print(f"n={n}: {host_label}")
    print("orbit probe: testing orbit success against direct endpoint cancellation")
    counts = Counter()
    example: tuple[EdgeSet, frozenset[int], frozenset[int], int, int, bool, bool] | None = None

    for gi, edges in enumerate(reps, start=1):
        for first in powerset(n):
            autos = list(automorphisms_preserving_first(n, edges, first))
            if not autos:
                continue
            for T in powerset(n):
                outside = [v for v in range(n) if v not in T]
                for a in outside:
                    left = T | {a}
                    for b in outside:
                        if a == b:
                            continue
                        if max_states is not None and counts["states"] >= max_states:
                            print(f"stopped after --max-states={max_states}")
                            print_orbit_probe_summary(counts, example)
                            return
                        counts["states"] += 1
                        right = T | {b}
                        orbit_ok = any(frozenset(σ[v] for v in left) == right for σ in autos)
                        if not orbit_ok:
                            continue
                        counts["orbit"] += 1
                        low = direct_low(n, edges, first, T, a, b)
                        comp = direct_complementary(n, edges, first, T, a, b)
                        if low:
                            counts["low_direct"] += 1
                        if comp:
                            counts["comp_direct"] += 1
                        if low and comp:
                            counts["both_direct"] += 1
                        elif example is None:
                            example = (edges, first, T, a, b, low, comp)
        if gi % 20 == 0 or gi == len(reps):
            print(f"  host reps processed: {gi}/{len(reps)}; orbit states so far: {counts['orbit']}")

    print_orbit_probe_summary(counts, example)


def nx_graph(n: int, edges: EdgeSet):
    import networkx as nx

    graph = nx.Graph()
    graph.add_nodes_from(range(n))
    graph.add_edges_from(edges)
    return graph


def nx_card_graph(graph, first: frozenset[int], second: frozenset[int], delete: int):
    card = graph.copy()
    card.remove_node(delete)
    for v in card.nodes:
        card.nodes[v]["color"] = f"{int(v in first)}{int(v in second)}"
    return card


def nx_card_hash(graph, first: frozenset[int], second: frozenset[int], delete: int) -> str:
    import networkx as nx

    return nx.weisfeiler_lehman_graph_hash(
        nx_card_graph(graph, first, second, delete), node_attr="color"
    )


def nx_card_iso(graph, first: frozenset[int], second_left: frozenset[int], delete_left: int,
    second_right: frozenset[int], delete_right: int) -> bool:
    from networkx.algorithms import isomorphism as iso

    left = nx_card_graph(graph, first, second_left, delete_left)
    right = nx_card_graph(graph, first, second_right, delete_right)
    return iso.GraphMatcher(left, right,
        node_match=lambda x, y: x["color"] == y["color"]).is_isomorphic()


def nx_zero_star_card_iso(
    n: int,
    edges: EdgeSet,
    graph,
    first: frozenset[int],
    second_left: frozenset[int],
    delete_left: int,
    second_right: frozenset[int],
    delete_right: int,
) -> bool:
    """Whether some colored card isomorphism has zero deleted-star error."""
    from networkx.algorithms import isomorphism as iso

    if (delete_left in first) != (delete_right in first):
        return False
    left = nx_card_graph(graph, first, second_left, delete_left)
    right = nx_card_graph(graph, first, second_right, delete_right)
    matcher = iso.GraphMatcher(
        left, right, node_match=lambda x, y: x["color"] == y["color"]
    )
    for mapping in matcher.isomorphisms_iter():
        if all(
            has_edge(edges, delete_left, z) == has_edge(edges, delete_right, mapping[z])
            for z in left.nodes
        ):
            return True
    return False


def nx_card_isomorphisms(
    graph,
    first: frozenset[int],
    second_left: frozenset[int],
    delete_left: int,
    second_right: frozenset[int],
    delete_right: int,
) -> Iterable[dict[int, int]]:
    from networkx.algorithms import isomorphism as iso

    if (delete_left in first) != (delete_right in first):
        return
    left = nx_card_graph(graph, first, second_left, delete_left)
    right = nx_card_graph(graph, first, second_right, delete_right)
    matcher = iso.GraphMatcher(
        left, right, node_match=lambda x, y: x["color"] == y["color"]
    )
    yield from matcher.isomorphisms_iter()


def nx_pair_min_error(
    edges: EdgeSet,
    graph,
    first: frozenset[int],
    second_left: frozenset[int],
    delete_left: int,
    second_right: frozenset[int],
    delete_right: int,
) -> PairMinError | None:
    """Minimum deleted-star error over card isomorphisms for one active edge."""

    best_error: int | None = None
    min_isomorphisms = 0
    active_first_error = False
    inactive_first_error = False
    for mapping in nx_card_isomorphisms(
        graph, first, second_left, delete_left, second_right, delete_right
    ):
        mismatches = [
            z
            for z in mapping
            if has_edge(edges, delete_left, z)
            != has_edge(edges, delete_right, mapping[z])
        ]
        error = len(mismatches)
        if best_error is None or error < best_error:
            best_error = error
            min_isomorphisms = 0
            active_first_error = False
            inactive_first_error = False
        if error == best_error:
            min_isomorphisms += 1
            active_first_error = active_first_error or any(
                z in second_left for z in mismatches
            )
            inactive_first_error = inactive_first_error or any(
                z not in second_left for z in mismatches
            )
    if best_error is None:
        return None
    return PairMinError(
        best_error, min_isomorphisms, active_first_error, inactive_first_error
    )


def nx_minimum_error_matchings(
    left: frozenset[int],
    right: frozenset[int],
    pair_data: dict[tuple[int, int], PairMinError | None],
) -> tuple[int | None, list[tuple[tuple[int, int, PairMinError], ...]]]:
    left_vertices = tuple(sorted(left))
    best_total: int | None = None
    best_matchings: list[tuple[tuple[int, int, PairMinError], ...]] = []
    for right_perm in itertools.permutations(sorted(right)):
        matching: list[tuple[int, int, PairMinError]] = []
        total = 0
        ok = True
        for x, y in zip(left_vertices, right_perm):
            data = pair_data[(x, y)]
            if data is None:
                ok = False
                break
            matching.append((x, y, data))
            total += data.error
        if not ok:
            continue
        if best_total is None or total < best_total:
            best_total = total
            best_matchings = []
        if total == best_total:
            best_matchings.append(tuple(matching))
    return best_total, best_matchings


def nx_active_zero_star_pair(
    n: int,
    edges: EdgeSet,
    graph,
    first: frozenset[int],
    second_left: frozenset[int],
    second_right: frozenset[int],
) -> tuple[int, int] | None:
    for x in sorted(second_left):
        for y in sorted(second_right):
            if nx_zero_star_card_iso(n, edges, graph, first, second_left, x, second_right, y):
                return (x, y)
    return None


def nx_restricted_deck_equal(
    graph,
    first: frozenset[int],
    second_left: frozenset[int],
    deletes_left: frozenset[int],
    second_right: frozenset[int],
    deletes_right: frozenset[int],
) -> bool:
    left_hashes = sorted(nx_card_hash(graph, first, second_left, z) for z in deletes_left)
    right_hashes = sorted(nx_card_hash(graph, first, second_right, z) for z in deletes_right)
    if left_hashes != right_hashes:
        return False

    left = list(deletes_left)
    right = list(deletes_right)
    candidates = {
        z: [w for w in right if nx_card_hash(graph, first, second_left, z) ==
            nx_card_hash(graph, first, second_right, w) and
            nx_card_iso(graph, first, second_left, z, second_right, w)]
        for z in left
    }
    left.sort(key=lambda z: len(candidates[z]))
    used: set[int] = set()

    def search(i: int) -> bool:
        if i == len(left):
            return True
        z = left[i]
        for w in candidates[z]:
            if w in used:
                continue
            used.add(w)
            if search(i + 1):
                return True
            used.remove(w)
        return False

    return search(0)


def nx_automorphisms_preserving_first(graph, first: frozenset[int]) -> list[dict[int, int]]:
    from networkx.algorithms import isomorphism as iso

    colored = graph.copy()
    for v in colored.nodes:
        colored.nodes[v]["first"] = v in first
    matcher = iso.GraphMatcher(
        colored, colored, node_match=lambda x, y: x["first"] == y["first"]
    )
    return list(matcher.isomorphisms_iter())


def run_nx_slice_orbit_probe(
    n: int,
    max_states: int | None,
    labelled: bool,
    max_hosts: int | None,
    random_hosts: int | None,
    seed: int,
    atlas: bool,
    first_samples: int | None,
) -> None:
    reps, host_label = select_host_reps(n, labelled, max_hosts, random_hosts, seed, atlas)
    rng = random.Random(seed)
    print(f"n={n}: {host_label}")
    print("networkx slice/orbit probe: WL hash filter, exact colored-card isomorphism")
    counts = Counter()

    for gi, edges in enumerate(reps, start=1):
        graph = nx_graph(n, edges)
        if first_samples is None:
            firsts = list(powerset(n))
        else:
            firsts = [frozenset(v for v in range(n) if (mask >> v) & 1)
                for mask in rng.sample(range(1 << n), min(first_samples, 1 << n))]
        for first in firsts:
            autos = nx_automorphisms_preserving_first(graph, first)
            for T in powerset(n):
                outside = [v for v in range(n) if v not in T]
                for a in outside:
                    left = T | {a}
                    for b in outside:
                        if a == b:
                            continue
                        if max_states is not None and counts["states"] >= max_states:
                            print(f"stopped after --max-states={max_states}")
                            print_nx_slice_orbit_summary(counts)
                            return
                        counts["states"] += 1
                        right = T | {b}
                        if not nx_restricted_deck_equal(graph, first, left, left, right, right):
                            continue
                        counts["low_slice_equal"] += 1
                        orbit_ok = any(frozenset(σ[v] for v in left) == right for σ in autos)
                        if orbit_ok:
                            counts["orbit_success"] += 1
                        else:
                            counts["orbit_failures"] += 1
                            print("ONE-SLICE ORBIT FAILURE CANDIDATE")
                            print(f"  edges={sorted(edges)}")
                            print(f"  first={sorted(first)} T={sorted(T)} a={a} b={b}")
                            print_nx_slice_orbit_summary(counts)
                            return
        if gi % 20 == 0 or gi == len(reps):
            print(
                f"  host reps processed: {gi}/{len(reps)}; "
                f"low-slice equal states so far: {counts['low_slice_equal']}"
            )

    print_nx_slice_orbit_summary(counts)


def run_zero_star_pair_probe(
    n: int,
    max_states: int | None,
    labelled: bool,
    max_hosts: int | None,
    random_hosts: int | None,
    seed: int,
    atlas: bool,
    first_samples: int | None,
) -> None:
    reps, host_label = select_host_reps(n, labelled, max_hosts, random_hosts, seed, atlas)
    rng = random.Random(seed)
    print(f"n={n}: {host_label}")
    print("zero-star pair probe: low-slice equality versus an active zero-star card pair")
    counts = Counter()
    example: tuple[EdgeSet, frozenset[int], frozenset[int], int, int, tuple[int, int] | None] | None = None

    for gi, edges in enumerate(reps, start=1):
        graph = nx_graph(n, edges)
        if first_samples is None:
            firsts = list(powerset(n))
        else:
            firsts = [
                frozenset(v for v in range(n) if (mask >> v) & 1)
                for mask in rng.sample(range(1 << n), min(first_samples, 1 << n))
            ]
        for first in firsts:
            for T in powerset(n):
                outside = [v for v in range(n) if v not in T]
                for a in outside:
                    left = T | {a}
                    for b in outside:
                        if a == b:
                            continue
                        if max_states is not None and counts["states"] >= max_states:
                            print(f"stopped after --max-states={max_states}")
                            print_zero_star_pair_summary(counts, example)
                            return
                        counts["states"] += 1
                        right = T | {b}
                        if not nx_restricted_deck_equal(graph, first, left, left, right, right):
                            continue
                        counts["low_slice_equal"] += 1
                        pair = nx_active_zero_star_pair(n, edges, graph, first, left, right)
                        if pair is not None:
                            counts["zero_star_pair"] += 1
                            if pair == (a, b):
                                counts["endpoint_pair"] += 1
                            elif pair[0] == a:
                                counts["endpoint_to_internal"] += 1
                            elif pair[1] == b:
                                counts["internal_to_endpoint"] += 1
                            else:
                                counts["internal_pair"] += 1
                        else:
                            counts["zero_star_failures"] += 1
                            if example is None:
                                example = (edges, first, T, a, b, pair)
        if gi % 20 == 0 or gi == len(reps):
            print(
                f"  host reps processed: {gi}/{len(reps)}; "
                f"low-slice equal states so far: {counts['low_slice_equal']}"
            )

    print_zero_star_pair_summary(counts, example)


def run_min_error_probe(
    n: int,
    max_states: int | None,
    labelled: bool,
    max_hosts: int | None,
    random_hosts: int | None,
    seed: int,
    atlas: bool,
    first_samples: int | None,
) -> None:
    reps, host_label = select_host_reps(n, labelled, max_hosts, random_hosts, seed, atlas)
    rng = random.Random(seed)
    print(f"n={n}: {host_label}")
    print("minimum-error probe: classify first errors in minimum active matchings")
    counts = Counter()
    example: tuple[EdgeSet, frozenset[int], frozenset[int], int, int, int] | None = None

    for gi, edges in enumerate(reps, start=1):
        graph = nx_graph(n, edges)
        if first_samples is None:
            firsts = list(powerset(n))
        else:
            firsts = [
                frozenset(v for v in range(n) if (mask >> v) & 1)
                for mask in rng.sample(range(1 << n), min(first_samples, 1 << n))
            ]
        for first in firsts:
            for T in powerset(n):
                outside = [v for v in range(n) if v not in T]
                for a in outside:
                    left = T | {a}
                    for b in outside:
                        if a == b:
                            continue
                        if max_states is not None and counts["states"] >= max_states:
                            print(f"stopped after --max-states={max_states}")
                            print_min_error_probe_summary(counts, example)
                            return
                        counts["states"] += 1
                        right = T | {b}
                        if not nx_restricted_deck_equal(graph, first, left, left, right, right):
                            continue
                        counts["low_slice_equal"] += 1
                        pair_data = {
                            (x, y): nx_pair_min_error(edges, graph, first, left, x, right, y)
                            for x in left
                            for y in right
                        }
                        best_total, matchings = nx_minimum_error_matchings(
                            left, right, pair_data
                        )
                        if best_total is None:
                            counts["no_active_matching"] += 1
                            continue
                        counts["minimum_matchings"] += len(matchings)
                        if best_total == 0:
                            counts["min_total_zero"] += 1
                        else:
                            counts["min_total_positive"] += 1
                            if example is None:
                                example = (edges, first, T, a, b, best_total)
                        for matching in matchings:
                            for _x, _y, data in matching:
                                if data.error == 0:
                                    counts["min_zero_edges"] += 1
                                else:
                                    counts["min_positive_edges"] += 1
                                    if data.active_first_error:
                                        counts["active_first_error_edges"] += 1
                                    if data.inactive_first_error:
                                        counts["inactive_first_error_edges"] += 1
                                    if data.active_first_error and data.inactive_first_error:
                                        counts["both_branch_edges"] += 1
                                    elif data.active_first_error:
                                        counts["active_only_edges"] += 1
                                    elif data.inactive_first_error:
                                        counts["inactive_only_edges"] += 1
                                    else:
                                        counts["unclassified_positive_edges"] += 1
        if gi % 20 == 0 or gi == len(reps):
            print(
                f"  host reps processed: {gi}/{len(reps)}; "
                f"low-slice equal states so far: {counts['low_slice_equal']}"
            )

    print_min_error_probe_summary(counts, example)


def print_summary(
    examined: int,
    equal_deck: int,
    orbit_fail: int,
    no_direct: int,
    low_direct: int,
    comp_direct: int,
    both_direct: int,
    agg: Counter,
    example_one_sided: tuple[EdgeSet, frozenset[int], frozenset[int], int, int, MatchStats] | None,
) -> None:
    print("\nsummary")
    print(f"  singleton states examined: {examined}")
    print(f"  equal-deck singleton states: {equal_deck}")
    print(f"  orbit failures: {orbit_fail}")
    print(f"  equal-deck states with neither direct cancellation: {no_direct}")
    print(f"  equal-deck states with low direct cancellation: {low_direct}")
    print(f"  equal-deck states with complementary direct cancellation: {comp_direct}")
    print(f"  equal-deck states with both direct cancellations: {both_direct}")
    print("  local two-hole match totals over equal-deck states:")
    for key in [
        "total",
        "name_coherent",
        "pure_low",
        "pure_low_nonzero_error",
        "pure_comp",
        "pure_comp_nonzero_error",
        "mixed",
        "mixed_nonzero_both",
    ]:
        print(f"    {key}: {agg[key]}")
    if example_one_sided is not None:
        edges, first, T, a, b, stats = example_one_sided
        print("  example local one-sided nonzero extension artifact:")
        print(f"    edges={sorted(edges)}")
        print(f"    first={sorted(first)} T={sorted(T)} a={a} b={b}")
        print(f"    stats={stats}")


def print_slice_probe_summary(
    counts: Counter,
    examples: list[tuple[str, EdgeSet, frozenset[int], frozenset[int], int, int]],
) -> None:
    print("\nslice probe summary")
    for key in [
        "states",
        "full_eq",
        "low_eq",
        "low_eq_full_eq",
        "low_eq_low_direct",
        "comp_eq",
        "comp_eq_full_eq",
        "comp_eq_comp_direct",
        "both_slices_eq",
    ]:
        print(f"  {key}: {counts[key]}")
    if examples:
        print("  examples:")
        for kind, edges, first, T, a, b in examples:
            print(f"    {kind}: edges={sorted(edges)} first={sorted(first)} T={sorted(T)} a={a} b={b}")


def print_orbit_probe_summary(
    counts: Counter,
    example: tuple[EdgeSet, frozenset[int], frozenset[int], int, int, bool, bool] | None,
) -> None:
    print("\norbit probe summary")
    for key in ["states", "orbit", "low_direct", "comp_direct", "both_direct"]:
        print(f"  {key}: {counts[key]}")
    if example is not None:
        edges, first, T, a, b, low, comp = example
        print("  orbit-without-double-direct example:")
        print(f"    edges={sorted(edges)}")
        print(f"    first={sorted(first)} T={sorted(T)} a={a} b={b}")
        print(f"    low_direct={low} comp_direct={comp}")


def print_nx_slice_orbit_summary(counts: Counter) -> None:
    print("\nnetworkx slice/orbit summary")
    for key in ["states", "low_slice_equal", "orbit_success", "orbit_failures"]:
        print(f"  {key}: {counts[key]}")


def print_zero_star_pair_summary(
    counts: Counter,
    example: tuple[EdgeSet, frozenset[int], frozenset[int], int, int, tuple[int, int] | None] | None,
) -> None:
    print("\nzero-star pair summary")
    for key in ["states", "low_slice_equal", "zero_star_pair", "zero_star_failures"]:
        print(f"  {key}: {counts[key]}")
    for key in ["endpoint_pair", "endpoint_to_internal", "internal_to_endpoint", "internal_pair"]:
        if counts[key]:
            print(f"  {key}: {counts[key]}")
    if example is not None:
        edges, first, T, a, b, pair = example
        print("  zero-star failure candidate:")
        print(f"    edges={sorted(edges)}")
        print(f"    first={sorted(first)} T={sorted(T)} a={a} b={b}")
        print(f"    pair={pair}")


def print_min_error_probe_summary(
    counts: Counter,
    example: tuple[EdgeSet, frozenset[int], frozenset[int], int, int, int] | None,
) -> None:
    print("\nminimum-error summary")
    for key in [
        "states",
        "low_slice_equal",
        "no_active_matching",
        "minimum_matchings",
        "min_total_zero",
        "min_total_positive",
        "min_zero_edges",
        "min_positive_edges",
        "active_first_error_edges",
        "inactive_first_error_edges",
        "active_only_edges",
        "inactive_only_edges",
        "both_branch_edges",
        "unclassified_positive_edges",
    ]:
        print(f"  {key}: {counts[key]}")
    if example is not None:
        edges, first, T, a, b, best_total = example
        print("  positive minimum-error candidate:")
        print(f"    edges={sorted(edges)}")
        print(f"    first={sorted(first)} T={sorted(T)} a={a} b={b}")
        print(f"    best_total={best_total}")


def run_c3_counterexample() -> None:
    """Print the connected 9-vertex cyclic example where orbit success does
    not imply low direct endpoint cancellation."""
    n = 9
    edges: EdgeSet = frozenset(
        {
            (0, 5),
            (0, 6),
            (0, 8),
            (1, 3),
            (1, 6),
            (1, 7),
            (2, 4),
            (2, 7),
            (2, 8),
            (3, 7),
            (4, 8),
            (5, 6),
            (6, 7),
            (6, 8),
            (7, 8),
        }
    )
    first = frozenset()
    T = frozenset({1})
    a = 0
    b = 2
    left = T | {a}
    right = T | {b}
    print("c3 orbit/direct counterexample")
    print(f"  n: {n}")
    print(f"  edges: {sorted(edges)}")
    print(f"  first: {sorted(first)}")
    print(f"  T: {sorted(T)} a: {a} b: {b}")
    print(f"  low_slice_equal: {low_slice_deck(n, edges, first, T, a) == low_slice_deck(n, edges, first, T, b)}")
    print(f"  full_deck_equal: {fixed_host_deck(n, edges, first, left) == fixed_host_deck(n, edges, first, right)}")
    print(f"  orbit_success: {orbit_success(n, edges, first, left, right)}")
    print(f"  low_direct: {direct_low(n, edges, first, T, a, b)}")
    print(f"  complementary_direct: {direct_complementary(n, edges, first, T, a, b)}")
    print(f"  low_internal_zero_star: {low_internal_zero_star(n, edges, first, T, a, b)}")
    graph = nx_graph(n, edges)
    active_zero_pairs = [
        (x, y)
        for x in sorted(left)
        for y in sorted(right)
        if nx_zero_star_card_iso(n, edges, graph, first, left, x, right, y)
    ]
    print(f"  active_zero_star_pairs: {active_zero_pairs}")
    right_to_left = list(solving_automorphisms(n, edges, first, right, left))
    left_to_right = list(solving_automorphisms(n, edges, first, left, right))
    print(f"  automorphisms_right_to_left: {right_to_left}")
    print(f"  automorphisms_left_to_right: {left_to_right}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("n", type=int, nargs="?", default=5)
    parser.add_argument("--max-states", type=int, default=None)
    parser.add_argument("--labelled", action="store_true", help="scan labelled hosts instead of unlabeled reps")
    parser.add_argument("--max-hosts", type=int, default=None, help="stop after this many host graphs")
    parser.add_argument("--random-hosts", type=int, default=None, help="scan this many random labelled hosts")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--skip-local", action="store_true", help="skip two-hole local-match classification")
    parser.add_argument(
        "--slice-probe",
        action="store_true",
        help="test whether one color-size slice already forces the direct endpoint",
    )
    parser.add_argument(
        "--orbit-probe",
        action="store_true",
        help="test fixed-host orbit success against direct endpoint cancellation",
    )
    parser.add_argument(
        "--nx-slice-orbit-probe",
        action="store_true",
        help="fast NetworkX probe for one-slice equality versus fixed-host orbit success",
    )
    parser.add_argument(
        "--zero-star-pair-probe",
        action="store_true",
        help="test low-slice equality against existence of an active zero-star card pair",
    )
    parser.add_argument(
        "--min-error-probe",
        action="store_true",
        help="classify first errors in minimum-error active matchings",
    )
    parser.add_argument(
        "--first-samples",
        type=int,
        default=None,
        help="sample this many first-color sets per host in NetworkX probes",
    )
    parser.add_argument(
        "--c3-counterexample",
        action="store_true",
        help="print a 9-vertex orbit-success state where low direct cancellation fails",
    )
    parser.add_argument("--atlas", action="store_true", help="use NetworkX graph atlas host reps")
    args = parser.parse_args()
    if args.c3_counterexample:
        run_c3_counterexample()
        return
    if args.n < 1:
        raise SystemExit("Use n >= 1.")
    if args.n > 7 and not (
        args.nx_slice_orbit_probe or args.zero_star_pair_probe or args.min_error_probe
    ):
        raise SystemExit("Use n <= 7 for this brute-force script.")
    if args.n > 7 and args.random_hosts is None:
        raise SystemExit("Use --random-hosts for n > 7.")
    if args.n == 7 and args.random_hosts is None and not args.atlas:
        raise SystemExit("Use --random-hosts or --atlas for n = 7; exhaustive n = 7 is too slow here.")
    if args.slice_probe:
        run_slice_probe(
            args.n,
            args.max_states,
            args.labelled,
            args.max_hosts,
            args.random_hosts,
            args.seed,
            args.atlas,
        )
        return
    if args.zero_star_pair_probe:
        run_zero_star_pair_probe(
            args.n,
            args.max_states,
            args.labelled,
            args.max_hosts,
            args.random_hosts,
            args.seed,
            args.atlas,
            args.first_samples,
        )
        return
    if args.min_error_probe:
        run_min_error_probe(
            args.n,
            args.max_states,
            args.labelled,
            args.max_hosts,
            args.random_hosts,
            args.seed,
            args.atlas,
            args.first_samples,
        )
        return
    if args.nx_slice_orbit_probe:
        run_nx_slice_orbit_probe(
            args.n,
            args.max_states,
            args.labelled,
            args.max_hosts,
            args.random_hosts,
            args.seed,
            args.atlas,
            args.first_samples,
        )
        return
    if args.orbit_probe:
        run_orbit_probe(
            args.n,
            args.max_states,
            args.labelled,
            args.max_hosts,
            args.random_hosts,
            args.seed,
            args.atlas,
        )
        return
    run(
        args.n,
        args.max_states,
        args.labelled,
        args.max_hosts,
        args.random_hosts,
        args.seed,
        args.skip_local,
        args.atlas,
    )


if __name__ == "__main__":
    main()
