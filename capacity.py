#!/usr/bin/env python3
"""
CRT capacity exclusion (Mian–Siddique 2026, Thm 4.4, adapted to a repeat budget).

For a pairwise-coprime family P of moduli dividing L (we take the distinct primes of L),
classes with moduli in P leave at least  U = (L / prod P) * prod (p - 1)  residues uncovered.
Every other usable modulus d covers at most L/d residues.  With modulus K allowed T times,
the total mop-up budget is  sum_{d | L, d odd, d>1, d not in P} L/d  +  (T-1) * L/K  (if K ∉ P).
If budget < U, no covering exists for this L.

The monotone-relaxation point of the paper: using a subfamily of P only raises U, so the
certificate is adversary-free.
"""
from math import prod


def factor_primes(L):
    ps, n, p = [], L, 3
    while p * p <= n:
        if n % p == 0:
            ps.append(p)
            while n % p == 0:
                n //= p
        p += 2
    if n > 1:
        ps.append(n)
    return ps


def excluded(L, K=9, T=2):
    """True if the capacity certificate proves no covering with lcm L."""
    P = factor_primes(L)
    U = (L // prod(P)) * prod(p - 1 for p in P)
    budget = sum(L // d for d in range(3, L + 1, 2) if L % d == 0 and d not in P)
    if K not in P and L % K == 0:
        budget += (T - 1) * (L // K)
    return budget < U, U, budget


if __name__ == "__main__":
    import sys
    L = int(sys.argv[1])
    ex, U, b = excluded(L)
    print(f"L={L}: uncovered>={U}, budget={b}, {'EXCLUDED' if ex else 'not excluded'}")
