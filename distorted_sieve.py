#!/usr/bin/env python3
"""
Distorted-sieve certificate for a specific L (Balister–Bollobás–Morris–Sahasrabudhe–Tiba,
arXiv 1811.03547, Theorem 3.1 with the moment bounds of Lemma 3.6, eq. (14)).

Primes p_1 < ... < p_n of L, Q_i = p_1^{e_1} ... p_i^{e_i}.  New moduli at step i:
N_i = { d | L : p_i | d, d | Q_i }, written d = m p_i^j with m | Q_{i-1}, j >= 1.
With nu(m) = prod_{p_k | m} 1/(1 - delta_k):
  M1_i = sum_{m p^j in N_i} p^{-j} nu(m)/m
  M2_i = sum_{(m1 p^j1, m2 p^j2) in N_i^2} p^{-(j1+j2)} nu(lcm(m1,m2))/lcm(m1,m2)
  eta  = sum_i min(M1_i, M2_i / (4 delta_i (1 - delta_i)))   (delta_i = 0 -> use M1_i)
If eta < 1 then no residue choice covers Z/L.  (Status: the inequality is BBMST's theorem;
this script only evaluates it; nothing here is proved by us.)
"""
import sys
from fractions import Fraction
from math import gcd
from itertools import product
from phi_certificate import factor


def eta_for(L, deltas, f=None):
    f = f or factor(L)
    primes = sorted(f)
    n = len(primes)
    assert len(deltas) == n
    nu_p = {p: Fraction(1) / (1 - deltas[i]) for i, p in enumerate(primes)}

    def nu(m):
        r = Fraction(1)
        for p in primes:
            if m % p == 0:
                r *= nu_p[p]
        return r

    # divisors of Q_{i-1}
    def divisors_of(ps):
        ds = [1]
        for p in ps:
            ds = [d * p ** k for d in ds for k in range(f[p] + 1)]
        return ds

    total = Fraction(0)
    terms = []
    for i, p in enumerate(primes):
        ms = divisors_of(primes[:i])
        e = f[p]
        # list of (m, weight) with weight = sum_{j=1..e} p^{-j} for each m (all m p^j are divisors of L)
        w = sum(Fraction(1, p ** j) for j in range(1, e + 1))
        M1 = sum(w * nu(m) / m for m in ms)
        M2 = Fraction(0)
        for m1 in ms:
            for m2 in ms:
                l = m1 * m2 // gcd(m1, m2)
                M2 += w * w * nu(l) / l
        d = deltas[i]
        if d == 0:
            t = M1
        else:
            t = min(M1, M2 / (4 * d * (1 - d)))
        terms.append((p, float(M1), float(M2), float(t)))
        total += t
    return total, terms


def optimise(L, grid=None):
    f = factor(L)
    n = len(f)
    grid = grid or [Fraction(k, 40) for k in range(0, 21)]  # 0 .. 1/2
    deltas = [Fraction(0)] * n
    best, _ = eta_for(L, deltas, f)
    improved = True
    while improved:
        improved = False
        for i in range(n):
            for g in grid:
                cand = deltas[:]
                cand[i] = g
                v, _ = eta_for(L, cand, f)
                if v < best:
                    best, deltas, improved = v, cand, True
    return best, deltas


if __name__ == "__main__":
    Ls = [int(a) for a in sys.argv[1:]] or [12, 80, 945, 10395, 675675, 6891885, 11486475]
    for L in Ls:
        best, deltas = optimise(L)
        _, terms = eta_for(L, deltas)
        print(f"L={L} {factor(L)}  eta={float(best):.4f}  deltas={[str(d) for d in deltas]}")
        for p, m1, m2, t in terms:
            print(f"    p={p:3d} M1={m1:.4f} M2={m2:.4f} term={t:.4f}")
