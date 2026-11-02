#!/usr/bin/env python3
"""
The phi-certificate for non-existence of covering systems with distinct moduli > 1
all dividing L.

Claim.  If  S(L) := sum_{d | L, d > 1, d not prime} 1/phi(d)  <  1,  then no covering
system of Z has distinct moduli > 1 all dividing L.

Proof sketch.  Let P' be the set of primes dividing L that occur as moduli, with classes
a_p (mod p).  The residues mod L avoiding all a_p form the CRT product set U of size
L * prod_{p in P'} (1 - 1/p).  A class c (mod d), d composite, meets U in at most
(L/d) * prod_{p in P', p does not divide d} (1 - 1/p) points.  Covering U needs
sum_d (L/d) prod_{p in P', p ∤ d}(1-1/p) >= |U|, i.e. sum_d (1/d) prod_{p in P', p | d} p/(p-1) >= 1,
and the left side is at most sum_d 1/phi(d) = S(L) (with equality when P' is all primes of L).

Compare: Mian–Siddique's capacity certificate is  sum_{d ∉ P} 1/d < prod_{p in P}(1 - 1/p),
which is weaker since 1/phi(d) <= (1/d) prod_{p|L} p/(p-1).
"""
from fractions import Fraction
from math import gcd
import sys


def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def divisors(n):
    ds = [1]
    for p, e in factor(n).items():
        ds = [d * p**k for d in ds for k in range(e + 1)]
    return sorted(ds)


def phi(n):
    r = n
    for p in factor(n):
        r = r // p * (p - 1)
    return r


def sigma(n):
    return sum(divisors(n))


def S(L):
    ps = set(factor(L))
    return sum(Fraction(1, phi(d)) for d in divisors(L) if d > 1 and d not in ps)


def excluded(L):
    return S(L) < 1


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
    # odd abundant (or perfect) numbers are the only candidates (density lemma)
    stragglers = []
    cnt = 0
    for L in range(3, N + 1, 2):
        if sigma(L) < 2 * L:
            continue
        cnt += 1
        if not excluded(L):
            stragglers.append((L, float(S(L))))
    print(f"odd non-deficient L <= {N}: {cnt}")
    print(f"NOT excluded by phi-certificate: {len(stragglers)}")
    for L, s in stragglers[:20]:
        print(f"  L={L} = {factor(L)}  S(L)={s:.4f}")
    if stragglers:
        print(f"=> certified bound: lcm > {stragglers[0][0] - 1}  (first straggler {stragglers[0][0]})")
    else:
        print(f"=> every odd non-deficient L <= {N} is excluded: lcm > {N}")
