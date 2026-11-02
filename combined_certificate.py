#!/usr/bin/env python3
"""
Numerical exploration of a combined certificate: tower sieve + inclusion-exclusion over
pairwise-coprime subsets of the remaining (omega >= 2) moduli.

Part A: brute-force test of the McNew-Setty Lemma 4.10 bound
    covered proportion <= sum_{S nonempty, pairwise coprime} (-1)^{|S|+1} / lcm(S)
  against the exact maximum over all residue choices, for small modulus sets.

Part B: candidate combined bound.  After sieving the prime-power classes, each remaining class
  C_i (modulus d_i, omega >= 2) meets U in at most  t(d_i) = prod_p min(p^{e-v_p(d_i)}, u_p)
  residues (normalised by |U| -> prod min/u).  For a pairwise-coprime set S the intersection is a
  class mod prod S and meets U in at most t(prod S).  Candidate:
    T2(L) = sum_{S pairwise coprime, |S| odd} t(prod S) - sum_{S pairwise coprime, |S| even} t(prod S)
  (Bonferroni-style, truncated to |S| <= 3).  Validity is tested empirically in Part C by
  comparing to exact maximum coverage for small L.
"""
import itertools, sys
from fractions import Fraction
from math import gcd, lcm
from functools import reduce
from phi_certificate import factor, divisors


def max_coverage_exact(L, moduli):
    """exact max # residues mod L covered by one class per modulus (brute force)."""
    best = 0
    for res in itertools.product(*[range(m) for m in moduli]):
        cov = 0
        for n in range(L):
            if any(n % m == r for m, r in zip(moduli, res)):
                cov += 1
        best = max(best, cov)
    return best


def ms_bound(moduli):
    tot = Fraction(0)
    for k in range(1, len(moduli) + 1):
        for S in itertools.combinations(moduli, k):
            if all(gcd(a, b) == 1 for a, b in itertools.combinations(S, 2)):
                tot += Fraction((-1) ** (k + 1), reduce(lcm, S))
    return tot


def t_factor(L, d):
    f = factor(L)
    fd = factor(d) if d > 1 else {}
    u = {p: p**e - (p**e - 1) // (p - 1) for p, e in f.items()}
    t = Fraction(1)
    for p, e in f.items():
        v = fd.get(p, 0)
        t *= Fraction(min(p ** (e - v), u[p]), u[p])
    return t


def T2(L, maxk=3):
    comps = [d for d in divisors(L) if len(factor(d)) >= 2]
    tot = Fraction(0)
    for k in range(1, maxk + 1):
        sign = (-1) ** (k + 1)
        for S in itertools.combinations(comps, k):
            if all(gcd(a, b) == 1 for a, b in itertools.combinations(S, 2)):
                tot += sign * t_factor(L, reduce(lambda a, b: a * b, S))
    return tot


if __name__ == "__main__":
    # Part A
    import random
    random.seed(1)
    bad = 0
    for trial in range(300):
        L = random.choice([12, 24, 30, 36, 60, 72, 90, 120])
        ds = [d for d in divisors(L) if d > 1]
        k = random.randint(2, min(5, len(ds)))
        M = random.sample(ds, k)
        exact = Fraction(max_coverage_exact(L, M), L)
        b = ms_bound(M)
        if exact > b:
            bad += 1; print("MS bound VIOLATED", L, M, exact, b)
    print("Part A: MS lemma violations:", bad, "/ 300")
    # Part C: T2 on covering numbers must be >= 1
    cov = [12, 24, 36, 48, 60, 72, 80, 84, 90, 96, 108, 120, 132, 144, 156]
    print("Part C: T2 on covering numbers:", [(L, round(float(T2(L)), 3)) for L in cov])
    print("T2 on odd stragglers:", [(L, round(float(T2(L)), 4)) for L in [6891885, 11486475]])
