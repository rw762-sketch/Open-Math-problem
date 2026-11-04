"""Check the Harrington-Sun-Wong Theorem 3.2 construction (arXiv 2104.00602) by brute force.

Input C0: a covering of Z whose moduli are distinct except that p appears exactly twice
(as 0 mod p and 1 mod p) and no modulus is divisible by p^2.  Output C: the covering
built in the proof, with distinct moduli.  Odd/square-free hypotheses play no role in
the covering/distinctness argument, so toy C0 with even moduli test the mechanics.
"""
import math
import numpy as np
from sympy import divisors, isprime, nextprime

def lcm(xs):
    return math.lcm(*xs)

def covers(C):
    L = lcm([m for _, m in C])
    hit = np.zeros(L, dtype=bool)
    for r, m in C:
        hit[r % m::m] = True
    return hit.all(), L

def crt(a, m, b, n):
    # x = a mod m, x = b mod n, gcd(m,n)=1
    return (a + m * ((b - a) * pow(m, -1, n) % n)) % (m * n)

def greedy_C0(p, L):
    """Greedy covering of Z/L: 0,1 mod p, then distinct divisors d|L, d not in {1,p}, p^2 not | d."""
    C = [(0, p), (1, p)]
    unc = np.ones(L, dtype=bool)
    unc[0::p] = False; unc[1::p] = False
    ds = [d for d in divisors(L) if d not in (1, p) and d % (p * p)]
    while unc.any() and ds:
        best = None
        for d in ds:
            cnt = unc.reshape(-1, d).sum(axis=0)
            r = int(cnt.argmax())
            if best is None or cnt[r] > best[0]:
                best = (cnt[r], r, d)
        c, r, d = best
        if c == 0:
            break
        C.append((r, d)); ds.remove(d); unc[r::d] = False
    return C if not unc.any() else None

def hsw(C0, p, q):
    plain = [(r, m) for r, m in C0 if m % p]                     # r_j mod m_j
    lifted = [(r, m // p) for r, m in C0 if m % p == 0 and m != p]  # r_{xi,j} mod p m_{xi,j}
    C = [(p**i, p**(i + 1)) for i in range(q - 1)]               # p^i mod p^{i+1}
    C += [(crt(0, p**i, i, q), p**i * q) for i in range(q)]      # s_i mod p^i q
    C += plain
    for r, mm in lifted:
        xi = r % p
        assert 2 <= xi <= p - 1
        for i in range(q - 1):
            C.append((crt(xi * p**i, p**(i + 1), r % mm, mm), p**(i + 1) * mm))
    return C

if __name__ == "__main__":
    for p, L0 in [(3, 3 * 4 * 5), (5, 5 * 8 * 9), (5, 5 * 8 * 9 * 7), (7, 7 * 8 * 9 * 5)]:
        C0 = greedy_C0(p, L0)
        if C0 is None:
            print(p, L0, "greedy C0 failed"); continue
        ok0, _ = covers(C0)
        ms = [m for _, m in C0]
        assert ok0 and ms.count(p) == 2 and len(set(ms)) == len(ms) - 1
        q = nextprime(3)
        while lcm(ms) % q == 0 or q == p:
            q = nextprime(q)
        C = hsw(C0, p, q)
        mods = [mm for _, mm in C]
        ok, L = covers(C)
        print(f"p={p} |C0|={len(C0)} q={q}: |C|={len(C)} lcm={L} covers={ok} distinct={len(set(mods)) == len(mods)}")
