"""Distorted tower certificate with an exact base block.
Base: Q0 | L, u0 = u(Q0) (exact min uncovered count), weight uniform on the uncovered set U0,
class bound nu0(m) = min(Q0/m, u0)/u0 for m | Q0; covered mass 0. Later stages exactly as in
Hybrid/ (Lean), with Pi1, Pi2 seeded by B1 = sum_{m|Q0} nu0(m), B2 = sum_{m1,m2|Q0} nu0(lcm)."""
import sys, math, itertools
from math import gcd
sys.path.insert(0, '..')
import hybrid_fast as H

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

def base_sums(Q0, u0):
    D = divisors(Q0)
    nu0 = {m: min(Q0 // m, u0) / u0 for m in D}
    B1 = sum(nu0.values())
    B2 = sum(nu0[a * b // gcd(a, b)] for a in D for b in D)
    return B1, B2

def eta_from(B1, B2, data, deltas):
    P1, P2, tot = B1, B2, 0.0
    for (G, Gp), d in zip(data, deltas):
        S1 = P1 - 1
        M1 = G * S1
        t = M1 if d == 0 else min(M1, G * G * (P2 - 2 * P1 + 1) / (4 * d * (1 - d)))
        tot += t
        c = 1 / (1 - d); P1 *= 1 + c * G; P2 *= 1 + c * Gp
    return tot

def best(B1, B2, fac, grid=[k / 200 for k in range(101)]):
    bestv = math.inf
    for o in itertools.permutations(fac):
        data = [H.pdata(p, e) for p, e in o]; n = len(data)
        d = [0.0] * n; b = eta_from(B1, B2, data, d); imp = True
        while imp:
            imp = False
            for i in range(n):
                for g in grid:
                    c = d[:]; c[i] = g; v = eta_from(B1, B2, data, c)
                    if v < b - 1e-15: b, d, imp = v, c, True
        if b < bestv: bestv, bo, bd = b, o, d
    return bestv, bo, bd

if __name__ == "__main__":
    Q0, u0 = 675, 188
    B1, B2 = base_sums(Q0, u0)
    print("B1", B1, "B2", B2)
    rest = [(7, 2), (11, 1), (13, 1), (17, 1), (19, 1)]
    print("L* = 1527701175, exact {3,5} base:", best(B1, B2, rest))
    print("current hybrid eta (all orders):", H.eta_best([(3,3),(5,2),(7,2),(11,1),(13,1),(17,1),(19,1)], "all") if False else "1.014 (from scan)")
