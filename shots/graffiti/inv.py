"""Graph invariants exactly as in formal-conjectures (FormalConjecturesForMathlib/Combinatorics/SimpleGraph)."""
import math
from functools import lru_cache
def pc(x): return bin(x).count("1")
class G:
    def __init__(s, adj):
        s.n = n = len(adj); s.adj = adj
        s.D = [s.bfs(v) for v in range(n)]
    def bfs(s, v):
        d = [-1]*s.n; d[v] = 0; fr = [v]
        while fr:
            nf = []
            for u in fr:
                m = s.adj[u]
                while m:
                    w = (m & -m).bit_length()-1; m &= m-1
                    if d[w] < 0: d[w] = d[u]+1; nf.append(w)
            fr = nf
        return d
    def connected_sub(s, S):
        if S == 0: return False
        v = (S & -S).bit_length()-1; seen = 1 << v; fr = seen
        while fr:
            nb = 0; m = fr
            while m:
                u = (m & -m).bit_length()-1; m &= m-1; nb |= s.adj[u]
            nb &= S & ~seen; seen |= nb; fr = nb
        return seen == S
    def edges_in(s, S):
        t = 0; m = S
        while m:
            u = (m & -m).bit_length()-1; m &= m-1; t += pc(s.adj[u] & S)
        return t // 2
    def ecc(s, v): return max(s.D[v])
    def rad(s): return min(s.ecc(v) for v in range(s.n))
    def diam(s): return max(s.ecc(v) for v in range(s.n))
    def avg_ecc(s): return sum(s.ecc(v) for v in range(s.n)) / s.n
    def is_indep(s, S):
        m = S
        while m:
            u = (m & -m).bit_length()-1; m &= m-1
            if s.adj[u] & S: return False
        return True
    def alpha_of(s, S):
        # max independent subset of S
        if S == 0: return 0
        v = (S & -S).bit_length()-1
        a = s.alpha_of(S & ~(1 << v))
        b = 1 + s.alpha_of(S & ~(1 << v) & ~s.adj[v])
        return max(a, b)
    def alpha(s): return s.alpha_of((1 << s.n)-1)
    def lv(s, v): return s.alpha_of(s.adj[v])
    def l(s): return sum(s.lv(v) for v in range(s.n)) / s.n
    def maxL(s): return max(s.lv(v) for v in range(s.n))
    def subsets_max(s, pred):
        best = 0
        for S in range(1 << s.n):
            k = pc(S)
            if k > best and pred(S): best = k
        return best
    def tree(s):   # largest induced tree (nonempty connected acyclic)
        return s.subsets_max(lambda S: s.connected_sub(S) and s.edges_in(S) == pc(S)-1)
    def forest(s):  # acyclic: each component tree <=> edges = |S| - #components
        def acyc(S):
            comps = 0; R = S
            while R:
                v = (R & -R).bit_length()-1; seen = 1 << v; fr = seen
                while fr:
                    nb = 0; m = fr
                    while m:
                        u = (m & -m).bit_length()-1; m &= m-1; nb |= s.adj[u]
                    nb &= R & ~seen; seen |= nb; fr = nb
                R &= ~seen; comps += 1
            return s.edges_in(S) == pc(S) - comps
        return s.subsets_max(acyc)
    def bip(s):
        def isb(S):
            col = {}
            R = S
            while R:
                v = (R & -R).bit_length()-1; col[v] = 0; st = [v]; R &= ~(1 << v)
                while st:
                    u = st.pop(); m = s.adj[u] & S
                    while m:
                        w = (m & -m).bit_length()-1; m &= m-1
                        if w in col:
                            if col[w] == col[u]: return False
                        else: col[w] = 1-col[u]; st.append(w); R &= ~(1 << w)
            return True
        return s.subsets_max(isb)
    def path(s):   # largest induced path (vertex count)
        best = 0
        for S in range(1, 1 << s.n):
            k = pc(S)
            if k <= best: continue
            if not s.connected_sub(S) or s.edges_in(S) != k-1: continue
            # tree with max degree <= 2 => path
            m = S; ok = True
            while m:
                u = (m & -m).bit_length()-1; m &= m-1
                if pc(s.adj[u] & S) > 2: ok = False; break
            if ok: best = k
        return best
    def has_c4(s):
        n = s.n
        for a in range(n):
            for c in range(n):
                if c != a and pc(s.adj[a] & s.adj[c] & ~(1 << a) & ~(1 << c)) >= 2: return True
        return False
    def dist_even(s, v): return sum(1 for w in range(s.n) if s.D[v][w] % 2 == 0)
    def degs(s): return sorted(pc(x) for x in s.adj)
    def sigma2(s):
        d = s.degs(); return d[1] if len(d) > 1 else 0
    def mindeg(s): return min(pc(x) for x in s.adj)
    def ham_path(s):
        n = s.n; full = (1 << n)-1
        # DP over subsets
        dp = [0]*(1 << n)
        for v in range(n): dp[1 << v] = 1 << v
        for S in range(1, 1 << n):
            e = dp[S]
            if not e: continue
            m = e
            while m:
                v = (m & -m).bit_length()-1; m &= m-1
                nb = s.adj[v] & ~S
                while nb:
                    w = (nb & -nb).bit_length()-1; nb &= nb-1
                    dp[S | (1 << w)] |= 1 << w
        return dp[full] != 0
    def kappa(s):
        n = s.n
        if n <= 1: return 0
        best = n-1
        for S in range(1 << n):
            k = pc(S)
            if k < best and not s.connected_sub(((1 << n)-1) & ~S): best = k
        return best
    def path_cover(s):
        n = s.n; full = (1 << n)-1
        # P[S] = S is the vertex set of some path; then min partition into such sets
        dp = [0]*(1 << n)
        for v in range(n): dp[1 << v] = 1 << v
        for S in range(1, 1 << n):
            e = dp[S]
            if not e: continue
            m = e
            while m:
                v = (m & -m).bit_length()-1; m &= m-1
                nb = s.adj[v] & ~S
                while nb:
                    w = (nb & -nb).bit_length()-1; nb &= nb-1
                    dp[S | (1 << w)] |= 1 << w
        isP = [dp[S] != 0 for S in range(1 << n)]
        best = [10**9]*(1 << n); best[0] = 0
        for S in range(1, 1 << n):
            low = S & -S; T = S; b = 10**9
            sub = S
            while sub:
                if sub & low and isP[sub]:
                    b = min(b, 1 + best[S & ~sub])
                sub = (sub-1) & S
            best[S] = b
        return best[full]
    def residue(s):
        d = sorted((pc(x) for x in s.adj), reverse=True)
        while d:
            if d[0] == 0: return len(d)
            k = d[0]; rest = d[1:]
            d = sorted([x-1 for x in rest[:k]] + rest[k:], reverse=True)
        return 0
