#!/usr/bin/env python3
"""Cap schedules for the comparison bound: coordinate descent on a_p = delta_p (p-1) for the first primes,
piecewise-constant delta on dyadic ranges after that.  Floats; exploratory."""
import math, sys, time
import numpy as np
from engine import *

PR = primes_upto(10 ** 7)
J7 = len(PR)

class Problem:
    """start: list of (q, gamma) multipliers applied before the first stage (conditioned coordinates);
    first: first stage prime; last: last stage prime (None = all primes); pre: cost already paid."""
    def __init__(self, start, first, last=None, pre=0.0, P_exact=1000, dmax=0.5, sqfree=False):
        self.start, self.first, self.last, self.pre, self.dmax = start, first, last, pre, dmax
        self.sqfree = sqfree
        self.set_exact(P_exact)
    def set_exact(self, P_exact):
        self.P_exact = P_exact if self.last is None else min(P_exact, self.last)
        hi = self.P_exact
        self.ps = [int(p) for p in PR[(PR >= self.first) & (PR <= hi)]]
        self.H = int(self.dmax * hi) + 2
    def bands(self):
        b = []; lo = 128
        while lo < 10 ** 7: b.append((lo, 2 * lo)); lo *= 2
        return b
    def delta_of(self, p, head, band):
        if p in head: return head[p] / (p - 1)
        for (lo, hi), d in band.items():
            if lo < p <= hi: return d
        return 0.5
    def total(self, head, band, detail=False):
        m = Model(self.H, 12)
        for it in self.start:
            if isinstance(it, dict): m.mult_dist(it)
            else: m.mult(*it)
        tot = self.pre; det = []
        for p in self.ps:
            n = p if self.sqfree else p - 1          # stage weight 1/n: classes m*p (square-free) or m*p^e
            d = self.delta_of(p, head, band); a = d * n
            L = m.pos(a) / (n - a)
            L = min(L, m.M1 / n)                   # delta = 0 is always allowed as a bound for the stage cost
            tot += L; det.append((p, d, L))
            if self.sqfree: m.mult_dist({1: 1 - 1 / ((1 - d) * p), 2: 1 / ((1 - d) * p)})
            else: m.mult(p, 1 / (1 - d))
        if self.last is None:
            # third-moment range: per-band constant delta, then far tail with delta = 1/2
            idx = int(np.searchsorted(PR, self.P_exact, side='right'))
            ps = PR[idx:].astype(float)
            dl = np.array([self.delta_of(p, head, band) for p in [self.P_exact * 2 ** k + 1 for k in range(0, 15)]])
            dvec = np.full(len(ps), 0.5)
            for (lo, hi), d in band.items():
                dvec[(ps > lo) & (ps <= hi)] = d
            c = 1 / (1 - dvec)
            fac = (1 + 7 * c / ps) if self.sqfree else (1 + c * (7 * ps * ps - 2 * ps + 1) / (ps - 1) ** 3)
            cum = np.concatenate([[1.0], np.cumprod(fac)])
            mid = float((c * 4 / (27 * dvec ** 2) * m.M3 * cum[:-1] / (ps - 1) ** 3).sum())
            far = far_tail(32 / 27, m.M3 * cum[-1], J7)
            tot += mid + far; det.append(('mid', mid)); det.append(('far', far))
        return (tot, det) if detail else tot

def optimise(prob, head_primes, rounds=4, verbose=False, head=None, band=None):
    head = dict(head or {}); band = dict(band or {})
    for p in head_primes: head.setdefault(p, round(0.3 * (p - 1)))
    if prob.last is None:
        for b in prob.bands(): band.setdefault(b, 0.4)
    best = prob.total(head, band)
    for r in range(rounds):
        imp = False
        for p in head_primes:
            cur = head[p]
            step = 0.5 if p < 60 else max(1.0, round((p - 1) / 40))
            cands = sorted(set([max(0.0, min((p - 1) * prob.dmax, cur + k * step)) for k in range(-4, 5)]))
            for a in cands:
                if a == cur: continue
                h = dict(head); h[p] = a; v = prob.total(h, band)
                if v < best - 1e-12: best, head, imp = v, h, True
        for b in list(band):
            for d in [0.25, 0.3, 0.35, 0.4, 0.45, 0.5]:
                if d == band[b]: continue
                bb = dict(band); bb[b] = d; v = prob.total(head, bb)
                if v < best - 1e-12: best, band, imp = v, bb, True
        if verbose: print('  round', r, round(best, 6), flush=True)
        if not imp: break
    return best, head, band

if __name__ == '__main__':
    t = time.time()
    head_primes = [int(p) for p in PR[(PR >= 5) & (PR <= 127)]]
    # open case: 3-powers conditioned away (gamma_3 = 2), all primes >= 5
    prob = Problem([(3, 2.0)], 5, None, P_exact=1000)
    best, head, band = optimise(prob, head_primes, verbose=True)
    print('open case (P_exact=1000):', best, round(time.time() - t)); print(head); print(band)
    prob.set_exact(20000)
    tot, det = prob.total(head, band, detail=True)
    print('open case, exact table to 20000:', tot, det[-2:], round(time.time() - t))
    print([(p, round(d, 3), round(L, 4)) for p, d, L in det[:14]])
