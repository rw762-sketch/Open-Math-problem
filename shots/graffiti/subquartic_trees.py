"""Gupta's subquartic conjecture (arXiv 2606.15761, Conj. 1): connected, max degree <= 4 => mu*(G) <= H(G).
Exhaustive over trees with max degree <= 4. mu*(T) by DP over rooted tree; H exact."""
import sys, networkx as nx
from fractions import Fraction as F
sys.setrecursionlimit(10000)
def mu_star_tree(G):
    """min maximal matching: pick an edge with both ends free; some matched edge must touch it."""
    adj = {v: list(G[v]) for v in G}; E = list(G.edges()); best = [len(G) // 2 + 1]
    def rec(used, size):
        if size >= best[0]: return
        e = next(((u, v) for u, v in E if u not in used and v not in used), None)
        if e is None: best[0] = size; return
        u, v = e
        cands = set()
        for x in (u, v):
            for y in adj[x]:
                if y not in used: cands.add((min(x, y), max(x, y)))
        for a, b in cands: rec(used | {a, b}, size + 1)
    rec(frozenset(), 0); return best[0]
def mu_star_bf(G):
    E = list(G.edges()); best = [len(E)]
    def rec(i, used, size):
        if size >= best[0]: return
        if i == len(E):
            if all(u in used or v in used for u, v in E): best[0] = size
            return
        u, v = E[i]
        if u not in used and v not in used:
            rec(i+1, used | {u, v}, size+1)
        rec(i+1, used, size)
    rec(0, frozenset(), 0); return best[0]
def H(G): return sum(F(2, G.degree(u) + G.degree(v)) for u, v in G.edges())
# validate DP vs brute force on small trees
for n in range(2, 12):
    for T in nx.nonisomorphic_trees(n):
        assert mu_star_tree(T) == mu_star_bf(T), (n, list(T.edges()))
print("DP validated on all trees n<=11")
N = int(sys.argv[1])
for n in range(2, N + 1):
    cnt = 0; worst = None; fails = []
    for T in nx.nonisomorphic_trees(n):
        if max(d for _, d in T.degree()) > 4: continue
        cnt += 1
        gap = mu_star_tree(T) - H(T)
        if worst is None or gap > worst[0]: worst = (gap, list(T.edges()))
        if gap > 0: fails.append(list(T.edges()))
    print(n, "subquartic trees", cnt, "max mu*-H =", float(worst[0]), "fails", len(fails), fails[:1], flush=True)
