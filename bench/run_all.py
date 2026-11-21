#!/usr/bin/env python3
"""Scoreboard: every case scored by every method.  Writes results.json.  Floats; see README.md."""
import json, sys, time
from schedule import *
from finite import union, second_moment, comparison
from reproduce import case_no5, case_no9

def all_primes(start, first, sqfree=False, head_to=127, exact=20000):
    prob = Problem(start, first, None, P_exact=1000, sqfree=sqfree)
    hp = [int(p) for p in PR[(PR >= first) & (PR <= head_to)]]
    best = None
    for f in (0.0, 0.3):
        v, head, band = optimise(prob, hp, head={p: round(f * (p - 1) * 2) / 2 for p in hp}, rounds=5)
        if best is None or v < best[0]: best = (v, head, band)
    v, head, band = best
    prob.set_exact(exact)
    return prob.total(head, band)

if __name__ == '__main__':
    t = time.time(); R = {}
    a = case_no5(PR); b = case_no9(PR)
    R['paper'] = {'no5': sum(a), 'no9': float(sum(b)), 'paper_no5': 0.836491555924628, 'paper_no9': 0.999442814397167}
    print(R['paper'], flush=True)
    odd = [int(p) for p in PR[(PR >= 3) & (PR <= 60)]]
    R['first_k'] = {}
    for k in range(4, 11):
        ps = odd[:k]
        row = {'largest': ps[-1], 'union': union(ps), 'second_moment': second_moment(ps),
               'block_second_moment': second_moment(ps[3:], P1=2 * (4 / 3) * (6 / 5), P2=5 * (13 / 6) * (5 / 3), pre=28 / 45),
               'comparison': comparison(ps[1:], [(3, 2.0)]),
               'block_comparison': comparison(ps[3:], [(3, 2.0), (5, 4 / 3), (7, 6 / 5)], pre=28 / 45)}
        R['first_k'][k] = row; print(k, {x: round(float(y), 4) for x, y in row.items()}, round(time.time() - t), flush=True)
    half = {1: 0.5, 2: 0.5}       # 3 to the first power only: after removing the class mod 3, D_3 is 1 or 2
    R['all_primes'] = {}
    for name, args in [('open', dict(start=[(3, 2.0)], first=5)),
                       ('open_block', None),
                       ('no5', dict(start=[(3, 2.0)], first=7)),
                       ('no9_direct', dict(start=[half], first=5)),
                       ('squarefree_direct', dict(start=[half], first=5, sqfree=True))]:
        if name == 'open_block':
            prob = Problem([(3, 2.0), (5, 4 / 3), (7, 6 / 5)], 11, None, pre=28 / 45, P_exact=1000)
            hp = [int(p) for p in PR[(PR >= 11) & (PR <= 127)]]
            v, head, band = optimise(prob, hp, rounds=5); prob.set_exact(20000); val = prob.total(head, band)
        else:
            val = all_primes(**args)
        R['all_primes'][name] = float(val); print(name, round(float(val), 4), round(time.time() - t), flush=True)
    json.dump(R, open('results.json', 'w'), indent=1)
