#!/usr/bin/env python3
"""Scores for 'first k odd primes, all exponents' under each method (floats)."""
import sys, time, math
from schedule import *

def lim(p):   # limit constants G, H (sum of (2j+1) g) for the tower measure on U_p
    return 1 / (p - 2), (3 * p - 1) / ((p - 1) * (p - 2))

def union(ps):
    P1 = 1.0; s = 0.0
    for p in ps: G, _ = lim(p); P1 *= 1 + G; s += G
    return P1 - 1 - s

GRID = [k / 40 for k in range(0, 21)]
def second_moment(ps, P1=1.0, P2=1.0, pre=0.0):
    def run(d):
        a, b, tot = P1, P2, pre
        for p, dl in zip(ps, d):
            G, H = lim(p); S1 = a - 1
            if S1 > 1e-15:
                M1 = G * S1
                tot += M1 if dl == 0 else min(M1, G * G * (b - 2 * a + 1) / (4 * dl * (1 - dl)))
            a *= 1 + G / (1 - dl); b *= 1 + H / (1 - dl)
        return tot
    best = math.inf
    for init in (0.0, 0.4):
        d = [init] * len(ps); v = run(d); imp = True
        while imp:
            imp = False
            for i in range(len(ps)):
                for g in GRID:
                    c = d[:]; c[i] = g; w = run(c)
                    if w < v - 1e-15: v, d, imp = w, c, True
        best = min(best, v)
    return best

def comparison(ps, start, pre=0.0):
    prob = Problem(start, ps[0], ps[-1], pre=pre, P_exact=ps[-1])
    best = math.inf
    for f in (0.0, 0.25, 0.4):
        init = {p: round(f * (p - 1) * 2) / 2 for p in ps}
        v, head, band = optimise(prob, ps, head=init, rounds=6)
        best = min(best, v)
    return best

if __name__ == '__main__':
    odd = [int(p) for p in PR[(PR >= 3) & (PR <= 60)]]
    print('k  largest  union  2nd-moment  block+2nd  comparison  block+comparison')
    for k in range(4, 13):
        ps = odd[:k]; t = time.time()
        u = union(ps)
        s = second_moment(ps)
        row = [u, s]
        if k >= 4:
            bl = second_moment(ps[3:], P1=2 * (4 / 3) * (6 / 5), P2=5 * (13 / 6) * (5 / 3), pre=28 / 45)
            cm = comparison(ps[1:], [(3, 2.0)])
            bc = comparison(ps[3:], [(3, 2.0), (5, 4 / 3), (7, 6 / 5)], pre=28 / 45)
            row += [bl, cm, bc]
        print(k, ps[-1], ' '.join(f'{x:.4f}' for x in row), round(time.time() - t, 1), flush=True)
