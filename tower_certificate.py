#!/usr/bin/env python3
"""
Tower certificate.  For odd L = prod p^e:
  u_p = p^e - (p^{e-1} + ... + 1)          # worst-case uncovered residues mod p^e after sieving
                                            # by one class each mod p, p^2, ..., p^e
  T(L) = sum_{d | L, omega(d) >= 2}  prod_p  p^{e_p - v_p(d)} / u_p
Claim: T(L) < 1  =>  no covering system with distinct moduli > 1 has lcm L.
Reduces to the phi-certificate when L is squarefree.
"""
from fractions import Fraction
import sys
from phi_certificate import factor, divisors, sigma, S


def T(L):
    f = factor(L)
    u = {p: p**e - (p**e - 1) // (p - 1) for p, e in f.items()}
    tot = Fraction(0)
    for d in divisors(L):
        fd = factor(d) if d > 1 else {}
        if len(fd) < 2:
            continue
        t = Fraction(1)
        for p, e in f.items():
            v = fd.get(p, 0)
            t *= Fraction(min(p ** (e - v), u[p]), u[p])
        tot += t
    return tot


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 3_000_000
    first = None; cnt = 0; worst = (0, 0)
    for L in range(3, N + 1, 2):
        if sigma(L) < 2 * L:
            continue
        cnt += 1
        t = T(L)
        if t > worst[0]: worst = (t, L)
        if t >= 1:
            first = L
            print(f"first straggler {L} = {factor(L)}  T={float(t):.4f}  S={float(S(L)):.4f}")
            break
    print(f"checked {cnt} odd non-deficient L up to {first or N}; max T below = {float(worst[0]):.4f} at {worst[1]}")
