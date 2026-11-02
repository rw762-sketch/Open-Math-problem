"""Hybrid certificate with moments up to order K (closed form).
P_i(C_i) <= min( M1, min_{k=2..K} c_k M_k / (delta^(k-1) (1-delta)) ),  c_k = (k-1)^(k-1)/k^k,
M_k = G_i^k * sum_{m_1..m_k | Q_{i-1}, all > 1} nu(lcm),
sum over all-(>1) tuples = sum_{s=0..k} (-1)^s C(k,s) Pi_{k-s},  Pi_r = prod_{l<i} (1 + c_l sum_{v>=1} ((v+1)^r - v^r) g_l(v)).
"""
import math
from itertools import permutations

def gvals(p, e):
    u = p**e - (p**e - 1)//(p - 1)
    return [min(p**(e - v), u)/u for v in range(e + 1)]

def eta_k(fo, deltas, K=4):
    gs = [gvals(p, e) for p, e in fo]
    Pi = [1.0]*(K + 1)  # Pi[r]
    tot = 0.0
    for g, d in zip(gs, deltas):
        G = sum(g[1:])
        S1 = Pi[1] - 1
        if S1 > 0:
            t = G*S1
            if d > 0:
                for k in range(2, K + 1):
                    Sk = sum((-1)**s*math.comb(k, s)*Pi[k - s] for s in range(k + 1))
                    ck = (k - 1)**(k - 1)/k**k
                    t = min(t, ck*G**k*Sk/(d**(k - 1)*(1 - d)))
            tot += t
        c = 1/(1 - d)
        for r in range(1, K + 1):
            Pi[r] *= 1 + c*sum(((v + 1)**r - v**r)*g[v] for v in range(1, len(g)))
    return tot

GRID = [k/100 for k in range(51)]
def best(fac, K=4, all_orders=True):
    b = math.inf
    for fo in (permutations(fac) if all_orders else [fac]):
        fo = list(fo); n = len(fo); d = [0.0]*n; v = eta_k(fo, d, K); imp = True
        while imp:
            imp = False
            for i in range(1, n):
                for gg in GRID:
                    c = d[:]; c[i] = gg; w = eta_k(fo, c, K)
                    if w < v - 1e-15: v, d, imp = w, c, True
        b = min(b, v)
    return b

if __name__ == "__main__":
    from hybrid_fast import factor
    for L in [12, 80, 53248, 11486475, 1527701175]:
        fac = factor(L)
        print(L, "K=2: %.4f" % best(fac, 2, len(fac) <= 6), " K=4: %.4f" % best(fac, 4, len(fac) <= 6))
