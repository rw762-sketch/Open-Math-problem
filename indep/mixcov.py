#!/usr/bin/env python3
"""Exact maximum coverage of the pure-survivor set U by mixed classes (one class per mixed divisor),
for L = prod p^e and a given pure configuration.  CP-SAT.  Usage: mixcov.py "3:2,5:1,7:1" [timelimit]"""
import sys, itertools, time
from ortools.sat.python import cp_model

def crt(res, mods):
    M = 1
    for m in mods: M *= m
    n = 0
    for r, m in zip(res, mods):
        Mi = M // m; n += r * Mi * pow(Mi, -1, m)
    return n % M

def run(fac, pure, tl=300, workers=2):
    """fac: list of (p,e); pure: dict (p,j) -> residue mod p^j of the pure class."""
    mods = [p**e for p, e in fac]; L = 1
    for m in mods: L *= m
    alive = []
    for (p, e), m in zip(fac, mods):
        alive.append([y for y in range(m) if all(y % p**j != pure[(p, j)] % p**j for j in range(1, e + 1))])
    pts = [crt(t, mods) for t in itertools.product(*alive)]
    divs = [d for d in range(2, L + 1) if L % d == 0 and sum(1 for p, _ in fac if d % p == 0) >= 2]
    m = cp_model.CpModel()
    x = {(d, r): m.NewBoolVar("") for d in divs for r in range(d)}
    for d in divs: m.AddExactlyOne(x[d, r] for r in range(d))
    cov = []
    for n in pts:
        c = m.NewBoolVar(""); m.AddBoolOr([x[d, n % d] for d in divs] + [c.Not()]); cov.append(c)
    m.Maximize(sum(cov))
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = workers
    st = s.Solve(m)
    return len(pts), int(round(s.ObjectiveValue())), s.BestObjectiveBound(), s.StatusName(st)

if __name__ == "__main__":
    fac = [tuple(map(int, t.split(":"))) for t in sys.argv[1].split(",")]
    tl = float(sys.argv[2]) if len(sys.argv) > 2 else 300
    # canonical pure configuration: p^j class = p^(j-1) mod p^j  (class 1 mod p, p mod p^2, ...)
    pure = {(p, j): p**(j - 1) for p, e in fac for j in range(1, e + 1)}
    t = time.time(); U, cov, ub, st = run(fac, pure, tl)
    print(fac, "|U| =", U, "max covered =", cov, "(ub %.1f, %s, %.0fs)" % (ub, st, time.time() - t), "=> u =", U - cov, flush=True)
