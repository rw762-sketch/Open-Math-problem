"""Certificates for Erdős #273 (moduli d | L with d >= 4, d+1 prime).
Pure prime-power moduli: only 2^j with 2^j+1 prime (4, 16, 256, 65536); odd primes have none.
Tower T (union bound after the 2-adic tower sieve) and the distorted version eta, both summing
only over allowed moduli (valid: the proofs bound sums over used moduli by sums over a superset)."""
import sys, itertools
from fractions import Fraction
from sympy import isprime, factorint
from math import gcd

def stats(L, order=None, deltas=None):
    f = factorint(L); primes = order or sorted(f)
    u = {}
    for p in primes:
        e = f[p]
        pure = [j for j in range(1, e+1) if p == 2 and isprime(2**j + 1) and 2**j >= 4]
        u[p] = p**e - sum(p**(e-j) for j in pure)
    g = lambda p, v: min(p**(f[p]-v), u[p]) / u[p]
    def vp(n, p):
        k = 0
        while n % p == 0: n //= p; k += 1
        return k
    divs = [1]
    for p in primes: divs = [d*p**k for d in divs for k in range(f[p]+1)]
    allowed = [d for d in divs if d >= 4 and isprime(d+1)]
    dens = sum(1/d for d in allowed)
    # stage of d = last prime in order dividing d; mixed iff d not a prime power
    deltas = deltas or [0.0]*len(primes)
    c = {p: 1/(1-deltas[i]) for i, p in enumerate(primes)}
    def nu(m):
        r = 1.0
        for p in primes:
            v = vp(m, p)
            if v: r *= g(p, v) * c[p]
        return r
    eta = 0.0; T = 0.0
    for i, p in enumerate(primes):
        Qprev = 1
        for q in primes[:i]: Qprev *= q**f[q]
        mixed = [(d // p**vp(d, p), vp(d, p)) for d in allowed if vp(d, p) >= 1 and all(vp(d, q) == 0 for q in primes[i+1:])]
        mixed = [(m, j) for m, j in mixed if m > 1]
        M1 = sum(g(p, j) * nu(m) for m, j in mixed)
        T += sum(g(p, j) * (1.0 if True else 0) * __import__('math').prod(g(q, vp(m, q)) for q in primes[:i] if vp(m, q)) for m, j in mixed)
        d = deltas[i]
        if d == 0: t = M1
        else:
            M2 = 0.0
            for (m1, j1) in mixed:
                for (m2, j2) in mixed:
                    M2 += g(p, j1) * g(p, j2) * nu(m1 * m2 // gcd(m1, m2))
            t = min(M1, M2 / (4*d*(1-d)))
        eta += t
    return dens, T, eta, len(allowed)

def best_eta(L, grid=(0, .1, .2, .25, .3, .35, .4, .45, .5)):
    f = factorint(L); primes = sorted(f)
    best = (9, None, None)
    for order in ([primes] if len(primes) > 6 else itertools.permutations(primes)):
        order = list(order); d = [0.0]*len(order); cur = stats(L, order, d)[2]; imp = True
        while imp:
            imp = False
            for i in range(1, len(order)):
                for x in grid:
                    dd = d[:]; dd[i] = x; v = stats(L, order, dd)[2]
                    if v < cur - 1e-12: cur, d, imp = v, dd, True
        if cur < best[0]: best = (cur, order, d)
    return best

if __name__ == "__main__":
    for L in map(int, sys.argv[1:]):
        dens, T, eta0, n = stats(L)
        b = best_eta(L)
        print(f"L={L} {factorint(L)} allowed={n} dens={dens:.4f} T_tower={T:.4f} eta_best={b[0]:.4f} order={b[1]} deltas={b[2]}", flush=True)
