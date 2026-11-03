"""TxGraffiti open conjectures (Davila-Brimkov-Pepper, arXiv 2507.17780), exhaustive on small graphs."""
import sys, pickle
from fractions import Fraction as F
from inv import G, pc
def annihilation(g):
    d = sorted(pc(x) for x in g.adj); m = sum(d) // 2; s = 0; j = 0
    for x in d:
        if s + x <= m: s += x; j += 1
        else: break
    return j
def maxdeg(g): return max(pc(x) for x in g.adj)
def zf_closure(g, S):
    n = g.n; B = S; changed = True
    while changed:
        changed = False
        m = B
        while m:
            u = (m & -m).bit_length()-1; m &= m-1
            W = g.adj[u] & ~B
            if W and W & (W-1) == 0: B |= W; changed = True
    return B
def Z(g):
    n = g.n; full = (1 << n)-1
    for k in range(n+1):
        # subsets of size k
        from itertools import combinations
        for c in combinations(range(n), k):
            S = 0
            for v in c: S |= 1 << v
            if zf_closure(g, S) == full: return k
def indep_dom(g):  # min maximal independent set
    n = g.n; full = (1 << n)-1; best = [n]
    def rec(I, cand, excl):
        if len(bin(I)) - 2 >= 0 and pc(I) >= best[0]: return
        if cand == 0:
            # maximal iff every excluded vertex has a neighbor in I
            ok = True; m = excl
            while m:
                v = (m & -m).bit_length()-1; m &= m-1
                if not g.adj[v] & I: ok = False; break
            if ok: best[0] = pc(I)
            return
        v = (cand & -cand).bit_length()-1
        rec(I | (1 << v), cand & ~(1 << v) & ~g.adj[v], excl | (g.adj[v] & cand))
        rec(I, cand & ~(1 << v), excl | (1 << v))
    rec(0, full, 0)
    return best[0]
def edges(g): return [(u, v) for u in range(g.n) for v in range(u+1, g.n) if g.adj[u] >> v & 1]
def min_maximal_matching(g):
    E = edges(g); best = [len(E)]
    def rec(i, used, size):
        if size >= best[0]: return
        if i == len(E):
            # maximal: every edge has an endpoint used
            if all(used >> u & 1 or used >> v & 1 for u, v in E): best[0] = size
            return
        u, v = E[i]
        if not (used >> u & 1) and not (used >> v & 1):
            rec(i+1, used | (1 << u) | (1 << v), size+1)
            # skip edge (u,v): then it must be covered later by another matched edge at u or v
            rec(i+1, used, size)
        else:
            rec(i+1, used, size)
    rec(0, 0, 0)
    return best[0]
def harmonic(g):
    return sum(F(2, pc(g.adj[u]) + pc(g.adj[v])) for u, v in edges(g))
res = {1: [], "2sub": [], "2cub": [], 3: [], 4: []}
for n in range(int(sys.argv[2]) if len(sys.argv) > 2 else 2, int(sys.argv[1]) + 1):
    for adj in pickle.load(open(f"g{n}.pkl", "rb")):
        g = G(adj); conn = all(d >= 0 for d in g.D[0])
        degs = [pc(x) for x in adj]; D = max(degs)
        if conn:
            al = g.alpha()
            if F(annihilation(g) + g.residue(), D) > al: res[1].append(adj)
            if D <= 3 and not (n == 4 and min(degs) == 3):
                z = Z(g)
                if z > al + 1:
                    res["2sub"].append(adj)
                    if min(degs) == 3: res["2cub"].append(adj)
            if min_maximal_matching(g) > harmonic(g): res[4].append(adj)
        if min(degs) == D and D > 0 and indep_dom(g) > min_maximal_matching(g): res[3].append(adj)
    print(n, {k: (len(v), v[:2]) for k, v in res.items()}, flush=True)
