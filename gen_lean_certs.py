"""Certificates (exposure order, deltas on the grid k/200) for every shaped odd L <= N,
verified in exact arithmetic; emitted as JSON for the Lean generator."""
import json, sys, math
from fractions import Fraction as F
from itertools import permutations
import hybrid_fast as H
from verify_hybrid_exact import eta as eta_exact

N = int(sys.argv[1]) if len(sys.argv) > 1 else 1527701174
OP = [3,5,7,11,13,17,19,23,29,31,37,41,43,47]
shaped = []
def gen(i, acc, fac):
    if acc > 1: shaped.append((acc, list(fac)))
    if i >= len(OP): return
    a, e = acc*OP[i], 1
    while a <= N:
        gen(i+1, a, fac + [(OP[i], e)]); a *= OP[i]; e += 1
gen(0, 1, [])

def search(fo, grid):
    data = [H.pdata(p, e) for p, e in fo]; n = len(data)
    d = [0.0]*n; b = H.eta_order(data, d); imp = True
    while imp:
        imp = False
        for i in range(1, n):
            for g in grid:
                c = d[:]; c[i] = g; v = H.eta_order(data, c)
                if v < b - 1e-15: b, d, imp = v, c, True
    return b, d

G40 = [k/40 for k in range(21)]; G200 = [k/200 for k in range(101)]
out = []; worst = F(0)
for L, fac in shaped:
    b, d = search(fac, G40); fo = fac
    if b >= 0.995:
        orders = list(permutations(fac)) if len(fac) <= 7 else [list(o) + fac[6:] for o in permutations(fac[:6])]
        cands = sorted((search(list(o), G40) + (list(o),) for o in orders), key=lambda t: t[0])[:6]
        b, d, fo = min((search(o, G200) + (o,) for _, _, o in cands), key=lambda t: t[0])
    dq = [F(round(x*200), 200) for x in d]
    v = eta_exact(fo, dq)
    if v >= 1:
        print("NO CERTIFICATE", L, fac, float(v)); continue
    worst = max(worst, v)
    out.append([L, [[p, e, round(x*200)] for (p, e), x in zip(fo, d)]])
print(f"{len(shaped)} shaped L <= {N}; certified {len(out)}; worst exact eta {float(worst):.6f}")
json.dump(out, open(f"lean_certs_{N}.json", "w"))
