#!/usr/bin/env python3
r"""Independence-enhanced distorted tower certificate (floats; exact recheck in verify_enh.py).

Certificate data: an undistorted prefix set S of primes of L (processed first, delta = 0), a pivot r in S,
then the remaining primes in some order with caps delta_i.
    eta' = Mix(S) - gain_r(S) + sum over the remaining stages of min(M1, M2/(4 delta (1-delta))),
    Mix(S)    = prod_{p in S}(1+G_p) - 1 - sum_{p in S} G_p            (union bound for the mixed classes on S)
    gain_r(S) = kappa_r * sum_{q in S\{r}} G_q - Gamma_r(S\{r}),
    Gamma_r(Q) = max over vertices w of {w >= 0, sum w = 1, w_c <= kappa_r} and maps sigma: Q -> classes mod r
                 of sum_c w_c (1 - prod_{q: sigma(q)=c} (1 - G_q)),          kappa_r = c_r(1).
The gain is the exact product formula for the classes r*q^j (q in S\{r}) inside each residue class mod r.
"""
import sys, math
from itertools import permutations, product, combinations
sys.path.insert(0, '..')
from hybrid_fast import pdata, factor

def kappa(p, e):
    u = p ** e - (p ** e - 1) // (p - 1)
    return min(p ** (e - 1), u) / u

def gamma(k, Gs):
    m = int(1 / k + 1e-12)
    w = [k] * m + ([1 - m * k] if 1 - m * k > 1e-15 else [])
    n = len(Gs)
    if n <= m:
        return k * sum(Gs)
    best = 0.0
    for sig in product(range(len(w)), repeat=n):
        val = 0.0
        for c, wc in enumerate(w):
            pr = 1.0
            for q in range(n):
                if sig[q] == c: pr *= 1 - Gs[q]
            val += wc * (1 - pr)
        if val > best: best = val
    return best

def gain_set(S):
    """S: list of (p,e). best pivot among primes <= 7."""
    if len(S) < 3: return 0.0, None
    best, piv = 0.0, None
    for ri, (p, e) in enumerate(S):
        if p > 7: continue
        k = kappa(p, e)
        Gs = [pdata(q, f)[0] for i, (q, f) in enumerate(S) if i != ri]
        g = k * sum(Gs) - gamma(k, Gs)
        if g > best + 1e-15: best, piv = g, p
    return best, piv

def stages(P1, P2, data, deltas):
    tot = 0.0
    for (G, Gp), d in zip(data, deltas):
        S1 = P1 - 1
        if S1 > 0:
            M1 = G * S1
            t = M1 if d == 0 else min(M1, G * G * (P2 - 2 * P1 + 1) / (4 * d * (1 - d)))
            tot += t
        c = 1 / (1 - d)
        P1 *= 1 + c * G; P2 *= 1 + c * Gp
    return tot

GRID = [k / 40 for k in range(0, 21)]

def best_rest(P1, P2, rest, grid=GRID, last=None):
    best = (math.inf, None, None)
    if last is not None:
        base = [x for x in rest if x != last]
        orders = (list(o) + [last] for o in permutations(base))
    else:
        orders = permutations(rest)
    for o in orders:
        data = [pdata(p, e) for p, e in o]; n = len(o)
        for init in (0.0, 0.4):
            d = [init] * n
            b = stages(P1, P2, data, d); imp = True
            while imp:
                imp = False
                for i in range(n):
                    for g in grid:
                        c = d[:]; c[i] = g; v = stages(P1, P2, data, c)
                        if v < b - 1e-15: b, d, imp = v, c, True
            if b < best[0]: best = (b, list(o), d)
    return best

def eta_enh(fac, maxrest=5, grid=GRID, last=None):
    """returns (value, S, pivot, rest order, deltas).  last: a prime (p,e) forced to be the final stage."""
    fac = list(fac); n = len(fac)
    best = (math.inf, None, None, None, None)
    idx3 = [i for i, (p, e) in enumerate(fac) if p == 3]
    others = [i for i in range(n) if i not in idx3]
    for k in range(2, n):
        if n - 1 - k > maxrest: continue
        for comb in combinations(others, k):
            if last is not None and any(fac[i] == last for i in comb): continue
            S = [fac[i] for i in idx3] + [fac[i] for i in comb]
            rest = [fac[i] for i in others if i not in comb]
            g, piv = gain_set(S)
            if g <= 0: continue
            P1 = P2 = 1.0; s = 0.0
            for p, e in S:
                G, Gp = pdata(p, e); P1 *= 1 + G; P2 *= 1 + Gp; s += G
            mix = P1 - 1 - s
            if mix - g >= 1: continue
            r, o, d = best_rest(P1, P2, rest, grid, last) if rest else (0.0, [], [])
            v = mix - g + r
            if v < best[0]: best = (v, S, piv, o, d)
    return best

if __name__ == "__main__":
    for L in [int(a) for a in sys.argv[1:]]:
        fac = factor(L)
        print(L, fac, eta_enh(fac), flush=True)
