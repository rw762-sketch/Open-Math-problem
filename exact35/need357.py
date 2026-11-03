import sys, itertools, math
sys.path.insert(0, '..'); import hybrid_fast as H
from eta_base import eta_from
base = [(3,3),(5,2),(7,2)]
P1 = P2 = 1.0; T = 0.0
for p, e in base:
    G, Gp = H.pdata(p, e); T += G * (P1 - 1); P1 *= 1 + G; P2 *= 1 + Gp
print("union bound for mixed {3,5,7} classes (delta=0):", T, " seeds", P1, P2)
rest = [(11,1),(13,1),(17,1),(19,1)]
best = math.inf
grid = [k/200 for k in range(101)]
for o in itertools.permutations(rest):
    data = [H.pdata(p, e) for p, e in o]; d = [0.0]*4; b = eta_from(P1, P2, data, d); imp = True
    while imp:
        imp = False
        for i in range(4):
            for g in grid:
                c = d[:]; c[i] = g; v = eta_from(P1, P2, data, c)
                if v < b - 1e-15: b, d, imp = v, c, True
    best = min(best, b)
print("later stages contribute", best, "-> eta = T357 +", best, "; need T357 <", 1 - best)
