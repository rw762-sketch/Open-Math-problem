"""u(Q): minimum number of residues mod Q left uncovered when one class is chosen for every
divisor d | Q, d > 1 (distinct moduli). CP-SAT, exact."""
import sys
from ortools.sat.python import cp_model
def umin(Q, tl=600):
    divs = [d for d in range(2, Q + 1) if Q % d == 0]
    m = cp_model.CpModel()
    x = {(d, r): m.NewBoolVar(f"x{d}_{r}") for d in divs for r in range(d)}
    for d in divs: m.AddExactlyOne(x[d, r] for r in range(d))
    m.Add(x[divs[0], 0] == 1)          # translate so the smallest modulus uses residue 0
    y = [m.NewBoolVar(f"y{n}") for n in range(Q)]
    for n in range(Q): m.AddBoolOr([x[d, n % d] for d in divs] + [y[n]])   # y[n]=1 allowed if uncovered
    m.Minimize(sum(y))
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = 8
    st = s.Solve(m)
    return s.ObjectiveValue(), s.BestObjectiveBound(), s.StatusName(st)
for Q in map(int, sys.argv[1:]): print(Q, umin(Q))
