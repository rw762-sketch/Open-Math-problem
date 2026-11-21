#!/usr/bin/env python3
"""Exact rational verification of the five-prime theorem (support {3,5,7,11,13}, all exponents).

(1) Limit constants: total = 28/45 + tau_11 + tau_13 = 4099375/4234032 < 1  (delta_11 = 2/5, delta_13 = 1/2).
(2) Sanity: for every exponent vector with entries in 1..EMAX the finite-exponent bound is below the limit value
    (the proof shows this by monotonicity; here it is recomputed directly).
"""
from fractions import Fraction as F
from itertools import product
import sys

def consts(p, e):
    """g(1..e), G, Gpair for the tower of p^e."""
    u = p**e - (p**e - 1)//(p - 1)
    g = [F(min(p**(e - v), u), u) for v in range(1, e + 1)]
    return g, sum(g), sum((2*v + 1)*g[v - 1] for v in range(1, e + 1))

def lim(p):
    return F(p - 1, p*(p - 2)), F(1, p - 2), F(3*p - 1, (p - 1)*(p - 2))   # g(1), G, Gpair in the limit

def total(c3, c5, c7, c11, c13, d11=F(2, 5)):
    """c_p = (g1, G, Gpair). Block {3,5,7} with the independence gain, then 11 (delta d11) and 13 (delta 1/2)."""
    (k, G3, H3), (_, a, H5), (_, b, H7), (_, G11, H11), (_, G13, H13) = c3, c5, c7, c11, c13
    mix = (1 + G3)*(1 + a)*(1 + b) - 1 - G3 - a - b
    gamma = max(k*(a + b - a*b), k*max(a, b) + (1 - k)*min(a, b))
    beta = mix - k*(a + b) + gamma
    C1 = (1 + G3)*(1 + a)*(1 + b); C3 = (1 + H3)*(1 + H5)*(1 + H7)
    t11 = G11**2*(C3 - 2*C1 + 1)/(4*d11*(1 - d11))
    C1 *= 1 + G11/(1 - d11); C3 *= 1 + H11/(1 - d11)
    t13 = G13**2*(C3 - 2*C1 + 1)
    return beta, t11, t13

L = [lim(p) for p in (3, 5, 7, 11, 13)]
beta, t11, t13 = total(*L)
tot = beta + t11 + t13
print("limit: beta =", beta, " tau11 =", t11, " tau13 =", t13)
print("limit total =", tot, "=", float(tot), " < 1:", tot < 1)
assert beta == F(28, 45) and tot == F(4099375, 4234032) and tot < 1

EMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
worst = 0
for es in product(range(1, EMAX + 1), repeat=5):
    cs = []
    for p, e in zip((3, 5, 7, 11, 13), es):
        g, G, H = consts(p, e); cs.append((g[0], G, H))
    v = sum(total(*cs))
    assert v < tot, (es, v)
    worst = max(worst, v)
print(f"all {EMAX**5} exponent vectors in [1,{EMAX}]^5: finite bound < limit; largest = {float(worst):.6f}")
