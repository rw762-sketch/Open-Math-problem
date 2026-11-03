"""Worst-case covered fraction of A3 x A5 x A7 (canonical minimal towers) by mixed classes
mod divisors of 3^3 5^2 7^2 with >= 2 primes. Quick feasibility test (minimal sizes only)."""
import sys, itertools
from ortools.sat.python import cp_model
tow = [(3,3),(5,2),(7,2)]
def Aset(p, e):
    P = p**e
    return [y for y in range(P) if all(y % p**j != (j - 1) for j in range(1, e + 1))]
As = [Aset(p, e) for p, e in tow]
print("sizes", [len(a) for a in As])
mods = [3**i * 5**j * 7**k for i in range(4) for j in range(3) for k in range(3)]
mixed = sorted(d for d in mods if sum(1 for p in (3,5,7) if d % p == 0) >= 2)
N = 27 * 25 * 49
from math import prod
pts = []
for y, z, w in itertools.product(*As):
    # CRT to n mod N
    for n in [None]:
        pass
    pts.append((y, z, w))
def crt(y, z, w):
    # n ≡ y mod 27, z mod 25, w mod 49
    M = N; n = 0
    for r, m in ((y,27),(z,25),(w,49)):
        Mi = M // m; n += r * Mi * pow(Mi, -1, m)
    return n % M
m = cp_model.CpModel()
x = {(d, r): m.NewBoolVar("") for d in mixed for r in range(d)}
for d in mixed: m.AddExactlyOne(x[d, r] for r in range(d))
cov = []
for y, z, w in pts:
    n = crt(y, z, w); c = m.NewBoolVar("")
    m.AddBoolOr([x[d, n % d] for d in mixed] + [c.Not()]); cov.append(c)
m.Maximize(sum(cov))
s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = float(sys.argv[1]) if len(sys.argv) > 1 else 300
s.parameters.num_workers = 8; s.parameters.log_search_progress = False
st = s.Solve(m)
tot = len(pts)
print(s.StatusName(st), "found", s.ObjectiveValue(), "bound", s.BestObjectiveBound(), "of", tot,
      "-> fraction in [%.4f, %.4f]" % (s.ObjectiveValue()/tot, s.BestObjectiveBound()/tot), "union bound 0.5933, need < 0.5732")
