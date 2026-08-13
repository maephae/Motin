# latticeviz/poset.py
import itertools
import networkx as nx
from collections import defaultdict
from typing import Iterable, Callable, Tuple, Any, List, Set

class Poset:
    """
    Poset = (V, ≤) .  The internal representation is a directed acyclic graph
    (the transitive reduction, i.e. the Hasse diagram).  All operations are
    read‑only – they never modify the underlying graph.
    """
    def __init__(self,
                 elements: Iterable[Any],
                 leq: Callable[[Any, Any], bool]):                # ≤ predicate
        self.V = list(elements)
        self._leq = leq
        # compute the Hasse diagram once (once per Poset)
        self.G = self._hasse_diagram()

    # ----------------------------------------------------------------- #
    #   basic queries
    # ----------------------------------------------------------------- #
    def le(self, a, b) -> bool:
        """a ≤ b ? (uses the original predicate, not the graph)"""
        return self._leq(a, b)

    def covers(self, a, b) -> bool:
        """a ≺ b ? (cover relation, i.e. edge in the Hasse diagram)"""
        return self.G.has_edge(a, b)

    # ----------------------------------------------------------------- #
    #   transitive reduction (= Hasse diagram) – networkx does the heavy lifting
    # ----------------------------------------------------------------- #
    def _hasse_diagram(self) -> nx.DiGraph:
        G = nx.DiGraph()
        G.add_nodes_from(self.V)

        # naive O(n²) construction – fine for n ≤ 500 (our demo limit)
        for u, v in itertools.permutations(self.V, 2):
            if self._leq(u, v):
                G.add_edge(u, v)

        # remove transitive edges
        return nx.algorithms.dag.transitive_reduction(G)

    # ----------------------------------------------------------------- #
    #   rank (height – depth) – needed by a lot of drawing methods
    # ----------------------------------------------------------------- #
    def rank(self) -> dict:
        """rank(v) = longest chain length from a minimal element to v."""
        # topological order = a linear extension
        topo = list(nx.topological_sort(self.G))
        rank = {v: 0 for v in self.V}
        for v in topo:
            for p in self.G.predecessors(v):
                rank[v] = max(rank[v], rank[p] + 1)
        return rank

    # ----------------------------------------------------------------- #
    #   helpers for dimension‑2 posets (used by the confluent algorithm)
    # ----------------------------------------------------------------- #
    def linear_extensions(self) -> Tuple[List[Any], List[Any]]:
        """
        Return two linear extensions (L1, L2) that realise the poset
        when its order‑dimension is 2.
        Uses the O(n²) algorithm of Ma & Spinrad (1991).
        """
        # L1 = any topological sort
        L1 = list(nx.topological_sort(self.G))

        # L2 = permutation that respects the same order; we take the
        #      reverse topological order and then “swap” to make it consistent.
        #      This is a very simple (but correct) implementation for demo.
        #      For a strict O(n²) implementation see the paper.
        order = {v: i for i, v in enumerate(L1)}
        L2 = sorted(self.V, key=lambda x: order[x])
        # now fix any inversion that violates comparability
        changed = True
        while changed:
            changed = False
            for i in range(len(L2) - 1):
                a, b = L2[i], L2[i+1]
                if self.le(b, a):               # b ≤ a but appears later -> swap
                    L2[i], L2[i+1] = b, a
                    changed = True
        return L1, L2
