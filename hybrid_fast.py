#!/usr/bin/env python3
"""
Fast closed forms (multiplicativity) for the tower certificate T(L) and the hybrid
distorted-tower certificate eta(L), from the prime factorisation alone.

For prime p with exponent e: u = p^e - (p^e - 1)/(p - 1), g(v) = min(p^(e-v), u)/u,
G = sum_{v=1..e} g(v).
  T(L) = prod_p (1 + G_p) - 1 - sum_p G_p                 (composite divisors, multiplicative)
Hybrid, primes in a chosen order, distortion c_k = 1/(1 - delta_k):
  H_k = c_k G_k,  K_k = 1 + c_k sum_{(a,b) != (0,0)} g(max(a,b))
  S1_i = prod_{k<i} (1 + H_k) - 1                         (sum over m | Q_{i-1}, m > 1 of nu(m))
  S2_i = prod_{k<i} K_k - 2 prod_{k<i} (1 + H_k) + 1      (sum over m1, m2 > 1 of nu(lcm))
  M1_i = G_i S1_i,  M2_i = G_i^2 S2_i
  eta = sum_i min(M1_i, M2_i / (4 delta_i (1 - delta_i)))
"""
import sys, math
from itertools import permutations


def pdata(p, e):
    u = p ** e - (p ** e - 1) // (p - 1)
    g = [min(p ** (e - v), u) / u for v in range(e + 1)]
    G = sum(g[1:])
    # sum over (a,b) in [0,e]^2 \ {(0,0)} of g(max(a,b)) = sum_v g(v) * (#pairs with max = v) = sum_v g(v)(2v+1)
    Gpair = sum(g[v] * (2 * v + 1) for v in range(1, e + 1))
    return G, Gpair


def tower(fac):
    pr, s = 1.0, 0.0
    for p, e in fac:
        G, _ = pdata(p, e)
        pr *= 1 + G
        s += G
    return pr - 1 - s


DGRID = [k / 40 for k in range(0, 21)]


def eta_order(data, deltas):
    P1, P2, tot = 1.0, 1.0, 0.0
    for (G, Gp), d in zip(data, deltas):
        S1 = P1 - 1
        if S1 > 0:
            M1 = G * S1
            if d == 0:
                t = M1
            else:
                S2 = P2 - 2 * P1 + 1
                t = min(M1, G * G * S2 / (4 * d * (1 - d)))
            tot += t
        c = 1 / (1 - d)
        P1 *= 1 + c * G
        P2 *= 1 + c * Gp
    return tot


def eta_best(fac, orders="increasing"):
    """minimise over deltas (coordinate descent on a grid) and, optionally, all prime orders."""
    best = math.inf
    facs = [fac] if orders == "increasing" else list(permutations(fac))
    for fo in facs:
        data = [pdata(p, e) for p, e in fo]
        n = len(data)
        deltas = [0.0] * n
        b = eta_order(data, deltas)
        imp = True
        while imp:
            imp = False
            for i in range(1, n):
                for gg in DGRID:
                    c = deltas[:]
                    c[i] = gg
                    v = eta_order(data, c)
                    if v < b - 1e-15:
                        b, deltas, imp = v, c, True
        best = min(best, b)
    return best


def factor(n):
    f, p = [], 2
    while p * p <= n:
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            f.append((p, e))
        p += 1 if p == 2 else 2
    if n > 1:
        f.append((n, 1))
    return f


if __name__ == "__main__":
    for L in [int(a) for a in sys.argv[1:]]:
        fac = factor(L)
        print(L, fac, "T=%.4f" % tower(fac), "eta=%.4f" % eta_best(fac), "eta_all_orders=%.4f" % eta_best(fac, "all"))
