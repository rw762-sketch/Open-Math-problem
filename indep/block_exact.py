#!/usr/bin/env python3
"""Exact u(L) (CP-SAT) for L = 3^a 5^b 7^c versus the union bound and the independence-gain bound."""
import sys, time
from fractions import Fraction as F
from ortools.sat.python import cp_model

def umin(Q, tl=45):
    divs = [d for d in range(2, Q + 1) if Q % d == 0]
    m = cp_model.CpModel()
    x = {(d, r): m.NewBoolVar("") for d in divs for r in range(d)}
    for d in divs: m.AddExactlyOne(x[d, r] for r in range(d))
    m.Add(x[divs[0], 0] == 1)
    y = [m.NewBoolVar("") for n in range(Q)]
    for n in range(Q): m.AddBoolOr([x[d, n % d] for d in divs] + [y[n]])
    m.Minimize(sum(y))
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = 2
    st = s.Solve(m)
    return int(round(s.ObjectiveValue())), s.BestObjectiveBound(), s.StatusName(st)

def consts(p, e):
    u = p**e - (p**e - 1)//(p - 1)
    c = [F(1)] + [F(min(p**(e - j), u), u) for j in range(1, e + 1)]
    return u, c, sum(c[1:])

def bounds(a, b, c):
    u3, c3, G3 = consts(3, a); u5, c5, G5 = consts(5, b); u7, c7, G7 = consts(7, c)
    mix = (1 + G3)*(1 + G5)*(1 + G7) - 1 - G3 - G5 - G7
    k = c3[1]
    gamma = max(k*(G5 + G7 - G5*G7), k*max(G5, G7) + (1 - k)*min(G5, G7))
    gain = k*(G5 + G7) - gamma
    U = u3*u5*u7
    return U, mix, gain

for arg in sys.argv[1:]:
    a, b, c = map(int, arg.split(","))
    L = 3**a * 5**b * 7**c
    U, mix, gain = bounds(a, b, c)
    t = time.time(); u, lb, st = umin(L)
    print(f"L={L}=3^{a}5^{b}7^{c}: exact u={u} (lb {lb:.1f}, {st}, {time.time()-t:.0f}s) | |U|={U} "
          f"union: u >= {float(U*(1-mix)):.2f}  new: u >= {float(U*(1-mix+gain)):.2f}  "
          f"(mix={float(mix):.4f}, gain={float(gain):.4f}, exact covered frac of U = {1-u/U:.4f})", flush=True)
