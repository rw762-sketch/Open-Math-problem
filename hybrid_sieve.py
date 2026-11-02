#!/usr/bin/env python3
"""
Hybrid "distorted tower" certificate (ours; validity argued in docs/PROGRESS.md, not yet formalised).

Expose primes p_1, ..., p_n of L in a chosen order.  At step i, on each fibre over Z/Q_{i-1}:
  (a) condition on the complement A_i of the pure-tower classes p_i^j (exact; |A_i| >= u_i),
  (b) then apply the BBMST distortion (cap delta_i) to the mixed classes m p_i^j, m > 1.
With g_k(v) = min(p_k^{e_k - v}, u_k)/u_k and nu(m) = prod_{p_k | m} g_k(v_k(m)) / (1 - delta_k):
  M1_i = sum_{m | Q_{i-1}, m > 1} sum_{j=1..e_i} g_i(j) nu(m)
  M2_i = sum_{m1, m2 | Q_{i-1}, > 1} sum_{j1, j2} g_i(j1) g_i(j2) nu(lcm(m1, m2))
  eta  = sum_i min(M1_i, M2_i / (4 delta_i (1 - delta_i)))
eta < 1  =>  no covering with lcm L.  With every delta = 0, eta = T(L) (the tower certificate).
"""
import sys
from fractions import Fraction
from math import gcd
from phi_certificate import factor


def setup(L, order=None):
    f = factor(L)
    primes = order or sorted(f)
    u = {p: p ** f[p] - (p ** f[p] - 1) // (p - 1) for p in primes}
    g = {p: [Fraction(min(p ** (f[p] - v), u[p]), u[p]) for v in range(f[p] + 1)] for p in primes}
    return f, primes, u, g


def vp(n, p):
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


def eta(L, deltas, order=None, ctx=None):
    f, primes, u, g = ctx or setup(L, order)
    nup = {p: Fraction(1) / (1 - deltas[i]) for i, p in enumerate(primes)}

    def nu(m):
        r = Fraction(1)
        for p in primes:
            v = vp(m, p)
            if v:
                r *= g[p][v] * nup[p]
        return r

    total = Fraction(0)
    ms = [1]
    for i, p in enumerate(primes):
        mm = [m for m in ms if m > 1]
        G = sum(g[p][j] for j in range(1, f[p] + 1))
        if mm:
            M1 = G * sum(nu(m) for m in mm)
            d = deltas[i]
            if d == 0:
                t = M1
            else:
                M2 = Fraction(0)
                for a in mm:
                    for b in mm:
                        M2 += nu(a * b // gcd(a, b))
                M2 *= G * G
                t = min(M1, M2 / (4 * d * (1 - d)))
            total += t
        ms = [m * p ** k for m in ms for k in range(f[p] + 1)]
    return total


def optimise(L, order=None, grid=None):
    ctx = setup(L, order)
    n = len(ctx[1])
    grid = grid or [Fraction(k, 20) for k in range(11)]
    deltas = [Fraction(0)] * n
    best = eta(L, deltas, ctx=ctx)
    imp = True
    while imp:
        imp = False
        for i in range(1, n):
            for gg in grid:
                c = deltas[:]
                c[i] = gg
                v = eta(L, c, ctx=ctx)
                if v < best:
                    best, deltas, imp = v, c, True
    return best, deltas


if __name__ == "__main__":
    Ls = [int(a) for a in sys.argv[1:]] or [12, 80, 945, 675675, 6891885, 11486475]
    for L in Ls:
        b, d = optimise(L)
        print(f"L={L} {factor(L)} eta_hybrid={float(b):.4f} deltas={[str(x) for x in d]}", flush=True)
