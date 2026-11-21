#!/usr/bin/env python3
r"""Benchmark engine (floats).  Stage bounds for the distortion method on covering systems.

Comparison model of Dai-Li-Li-Yi (arXiv 2611.15110, Thm 2.6): for a stage at the prime p with cap delta_p,
c_p = 1/(1-delta_p), and X = tau(R), R = prod_{q before p} q^{T_q}, T_q independent, P(T_q >= e) = gamma_q/q^e:
        L_p <= c_p/(p-1) * E (X - a_p)^+ ,      a_p = delta_p (p-1).
X is a product of independent D_q = T_q + 1:  P(D=1) = 1 - gamma/q,  P(D=d) = gamma (q-1)/q^d (d >= 2),
E D = 1 + gamma/(q-1),  E D^3 = 1 + gamma (7q^2 - 2q + 1)/(q-1)^3.
E(X-a)^+ = EX - a + sum_{t<a} (a-t) P(X=t)  needs only the distribution below a.
Large multipliers (D > dstar) are replaced by 1 in the table, which can only increase the bound.
"""
import math
import numpy as np

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]: s[i * i::i] = False
    return np.nonzero(s)[0]

class Model:
    def __init__(self, H, dstar=10):
        self.H, self.dstar = H, dstar
        self.P = np.zeros(H + 1); self.P[1] = 1.0
        self.M1 = 1.0; self.M3 = 1.0
    def copy(self):
        m = Model.__new__(Model); m.H, m.dstar = self.H, self.dstar
        m.P = self.P.copy(); m.M1, m.M3 = self.M1, self.M3
        return m
    def mult(self, q, gamma):
        H, ds, P = self.H, self.dstar, self.P
        new = P * (1 - gamma / q + gamma / q ** ds)
        for d in range(2, ds + 1):
            n = H // d
            if n == 0: break
            w = gamma * (q - 1) / q ** d
            if w < 1e-22: break
            new[d:n * d + 1:d] += P[1:n + 1] * w
        self.P = new
        self.M1 *= 1 + gamma / (q - 1)
        self.M3 *= 1 + gamma * (7 * q * q - 2 * q + 1) / (q - 1) ** 3
    def mult_dist(self, pd):
        """multiply by an independent positive integer variable with distribution pd = {d: prob}"""
        H, P = self.H, self.P
        new = np.zeros_like(P)
        for d, w in pd.items():
            n = H // d
            if n: new[d:n * d + 1:d] += P[1:n + 1] * w
        self.P = new
        self.M1 *= sum(d * w for d, w in pd.items())
        self.M3 *= sum(d ** 3 * w for d, w in pd.items())
    def pos(self, a):
        """upper bound for E(X - a)^+ ; exact up to the dstar truncation when a <= H"""
        if a <= 0: return self.M1
        assert a <= self.H + 1e-9, (a, self.H)
        k = int(math.ceil(a - 1e-12))            # t = 1..k-1 are < a
        t = np.arange(1, k)
        return self.M1 - a + float(((a - t) * self.P[1:k]).sum())

def tail_third_moment(model, primes, start_idx, delta, C=None, upto=10 ** 7):
    """sum over primes[start_idx:] (<= upto) of C*M3/(p-1)^3 with constant cap delta, then Lemma 2.10 beyond.
    C defaults to c*4/(27 delta^2).  Returns (middle, far)."""
    c = 1 / (1 - delta)
    if C is None: C = c * 4 / (27 * delta * delta)
    ps = primes[start_idx:]; ps = ps[ps <= upto].astype(float)
    fac = 1 + c * (7 * ps * ps - 2 * ps + 1) / (ps - 1) ** 3
    cum = np.concatenate([[1.0], np.cumprod(fac)])
    M3_before = model.M3 * cum[:-1]
    middle = float((C * M3_before / (ps - 1) ** 3).sum())
    M3_after = model.M3 * cum[-1]
    return middle, C, M3_after

def far_tail(C, M3, J, ell=13.0, beta=15.0):
    b = J - 1
    assert math.log(b) >= ell > (beta - 3) / 2
    return C * M3 / (b * b * ell * ell * (2 * ell - beta + 3))
