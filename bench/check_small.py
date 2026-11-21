"""Independent check of the comparison bound for small supports: exact fractions, direct enumeration of the
divisor-count multipliers (no table code shared with engine.py)."""
from fractions import Fraction as F
import itertools, sys
sys.setrecursionlimit(10000)
def dist(q, gamma, dmax):
    """P(D = d), d = 1..dmax, with the tail mass put on dmax+... handled as lower truncation: returns list and tail prob"""
    pr = {1: 1 - gamma / q}
    for d in range(2, dmax + 1): pr[d] = gamma * (q - 1) / F(q) ** d
    tail = gamma / F(q) ** dmax          # P(D > dmax) = P(T >= dmax)
    return pr, tail
def EposX(mults, a, dmax=60):
    """exact E(X - a)^+ = EX - a + sum_{t<a}(a-t)P(X=t), X = prod D_q; P(X = t) for t < a by enumeration."""
    EX = F(1)
    for q, g in mults: EX *= 1 + g / F(q - 1)
    # distribution below a
    cur = {1: F(1)}
    for q, g in mults:
        pr, _ = dist(q, g, int(a) + 2)
        new = {}
        for t, pt in cur.items():
            for d, pd in pr.items():
                if t * d < a: new[t * d] = new.get(t * d, 0) + pt * pd
        cur = new
    return EX - a + sum((a - t) * p for t, p in cur.items())
def total(stages, start):
    """stages: list of (p, a_p); start: list of (q, gamma)."""
    mults = list(start); tot = F(0); det = []
    for p, a in stages:
        a = F(a); L = EposX(mults, a) / (p - 1 - a)
        L0 = EposX(mults, F(0)) / (p - 1)
        L = min(L, L0); tot += L; det.append((p, a, float(L)))
        mults.append((p, F(p - 1) / (p - 1 - a)))
    return tot, det
if __name__ == '__main__':
    from schedule import *
    for k, last in ((5, 13), (6, 17), (7, 19)):
        ps = [int(p) for p in PR[(PR >= 5) & (PR <= last)]]
        prob = Problem([(3, 2.0)], 5, last, P_exact=last)
        best = None
        for f in (0.0, 0.25, 0.4):
            v, head, band = optimise(prob, ps, head={p: round(f * (p - 1) * 2) / 2 for p in ps}, rounds=6)
            if best is None or v < best[0]: best = (v, head)
        v, head = best
        st = [(p, F(head[p]).limit_denominator(2)) for p in ps]
        tot, det = total(st, [(3, F(2))])
        print(k, 'engine', round(v, 6), ' exact', tot, '=', float(tot), det)
