#!/usr/bin/env python3
"""Finer cap schedules for the all-primes cases: one cap per prime up to 127, then delta constant on narrow
geometric ranges.  Coordinate descent, floats.  Usage: tune.py open|no9|no5"""
import sys, json, time, math
import numpy as np
from schedule import *

def run(name, start, first, P_opt=4000, P_final=100000, rounds=4):
    t = time.time()
    prob = Problem(start, first, None, P_exact=P_opt)
    head_primes = [int(p) for p in PR[(PR >= first) & (PR <= 127)]]
    edges = [127]
    while edges[-1] < 10 ** 5: edges.append(int(edges[-1] * 2 ** (1 / 3)) + 1)
    bands = [(edges[i], edges[i + 1]) for i in range(len(edges) - 1)]
    prob.bands = lambda: bands
    head = {p: float(round(0.25 * (p - 1))) for p in head_primes}
    band = {b: (0.3 if b[0] < 1000 else 0.36) for b in bands}
    best = prob.total(head, band)
    for r in range(rounds):
        imp = False
        for p in head_primes:
            step = 0.5 if p <= 13 else 1.0
            for k in (-3, -2, -1, 1, 2, 3):
                a = head[p] + k * step
                if a < 0 or a > (p - 1) / 2: continue
                h = dict(head); h[p] = a; v = prob.total(h, band)
                if v < best - 1e-12: best, head, imp = v, h, True
        for b in bands:
            if b[0] > P_opt: continue
            for dd in (-0.05, -0.025, -0.0125, 0.0125, 0.025, 0.05):
                d = band[b] + dd
                if d < 0.05 or d > 0.5: continue
                bb = dict(band); bb[b] = d; v = prob.total(head, bb)
                if v < best - 1e-12: best, band, imp = v, bb, True
        print(name, 'round', r, round(best, 5), round(time.time() - t), flush=True)
        if not imp: break
    prob.set_exact(P_final)
    tot, det = prob.total(head, band, detail=True)
    print(name, 'final (table to %d):' % P_final, tot, det[-2:], round(time.time() - t), flush=True)
    for b in bands:
        if b[0] <= P_opt: continue
        for d in (0.3, 0.33, 0.39, 0.42, 0.45, 0.5):
            bb = dict(band); bb[b] = d; v = prob.total(head, bb)
            if v < tot - 1e-12: tot, band = v, bb
    print(name, 'after tuning the upper ranges:', tot, round(time.time() - t), flush=True)
    json.dump({'total': float(tot), 'head': head, 'band': {f'{a}-{b}': d for (a, b), d in band.items()}}, open(f'schedule_{name}.json', 'w'), indent=1)
    return tot

if __name__ == '__main__':
    half = {1: 0.5, 2: 0.5}
    cases = {'open': ([(3, 2.0)], 5), 'no9': ([half], 5), 'no5': ([(3, 2.0)], 7)}
    for name in sys.argv[1:]:
        run(name, *cases[name])
