#!/usr/bin/env python3
"""
Adversarial test of McNew-Setty Lemma 4.10 (arXiv 2507.23041):
  max covered proportion by one class per m in M  <=  Phi'(M) := sum_{S pwc, S nonempty} (-1)^{|S|+1} / lcm S.
Equivalently  min uncovered proportion >= Phi(M) := sum_{S pwc, incl. empty} (-1)^{|S|}/lcm S.

Phi(M) is the independence polynomial Z(G_M, -1/m) of the share-a-prime graph G_M.
Shearer's theorem guarantees  P(uncovered) >= Phi(M)  only when every induced subgraph has Z >= 0
("Shearer region").  We search for M OUTSIDE the region (some subset W with Phi(W) < 0, but Phi(M) > 0)
and test the lemma there by exact minimisation of the uncovered count over all residue choices.
"""
import itertools, sys
from fractions import Fraction
from math import gcd, lcm
from functools import reduce


def phi(M):
    M = list(M)
    tot = Fraction(0)
    for k in range(len(M) + 1):
        for S in itertools.combinations(M, k):
            if all(gcd(a, b) == 1 for a, b in itertools.combinations(S, 2)):
                tot += Fraction((-1) ** k, reduce(lcm, S, 1))
    return tot


def min_uncovered(L, M):
    """exact min #uncovered residues mod L over all residue choices (DFS with symmetry: first class = 0)."""
    best = [L]
    masks = []
    for m in M:
        masks.append([sum(1 << n for n in range(L) if n % m == r) for r in range(m)])
    full = (1 << L) - 1
    order = sorted(range(len(M)), key=lambda i: M[i])  # small moduli first

    def rec(idx, cov):
        if idx == len(order):
            u = bin(full & ~cov).count("1")
            if u < best[0]:
                best[0] = u
            return
        i = order[idx]
        rs = range(1) if idx == 0 else range(M[i])
        for r in rs:
            rec(idx + 1, cov | masks[i][r])
    rec(0, 0)
    return best[0]


def outside_region(M):
    for k in range(1, len(M) + 1):
        for W in itertools.combinations(M, k):
            if phi(W) < 0:
                return W
    return None


if __name__ == "__main__":
    Ls = [12, 24, 36, 60, 72, 90, 120, 180, 240, 360]
    maxk = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    tested = outside = viol = 0
    for L in Ls:
        D = [d for d in range(2, L + 1) if L % d == 0]
        for k in range(2, min(maxk, len(D)) + 1):
            for M in itertools.combinations(D, k):
                p = phi(M)
                if p <= 0:
                    continue  # bound trivial
                W = outside_region(M)
                if W is None:
                    continue
                outside += 1
                # exact test only if cheap
                prod = 1
                for m in M[1:]:
                    prod *= m
                if prod > 2_000_000:
                    continue
                tested += 1
                u = Fraction(min_uncovered(L, list(M)), L)
                if u < p:
                    viol += 1
                    print(f"VIOLATION L={L} M={M} uncovered={u} Phi={p} bad subset={W}")
    print(f"outside-region configs: {outside}, exactly tested: {tested}, violations: {viol}")
