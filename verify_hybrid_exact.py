"""Exact (Fraction) re-check of every hybrid certificate: eta(order, deltas) < 1.
Deltas are snapped to the rational grid k/200 they came from."""
import json, sys
from fractions import Fraction as F

def pdata(p, e):
    u = p**e - (p**e - 1)//(p - 1)
    g = [F(min(p**(e - v), u), u) for v in range(e + 1)]
    return sum(g[1:]), sum(g[v]*(2*v + 1) for v in range(1, e + 1))

def eta(order, deltas):
    P1 = P2 = F(1); tot = F(0)
    for (p, e), d in zip(order, deltas):
        G, Gp = pdata(p, e); S1 = P1 - 1
        if S1 > 0:
            M1 = G*S1
            t = M1 if d == 0 else min(M1, G*G*(P2 - 2*P1 + 1)/(4*d*(1 - d)))
            tot += t
        c = 1/(1 - d); P1 *= 1 + c*G; P2 *= 1 + c*Gp
    return tot

certs = json.load(open(sys.argv[1]))
worst = F(0); bad = 0
for order, ds in certs:
    dq = [F(round(x*200), 200) for x in ds]
    assert all(abs(float(a) - b) < 1e-12 for a, b in zip(dq, ds))
    v = eta([tuple(pe) for pe in order], dq)
    if v >= 1:
        bad += 1; print("FAILS EXACTLY", order, ds, float(v))
    worst = max(worst, v)
print(f"{len(certs)} certificates, exact failures: {bad}, max eta = {float(worst):.6f}")

if len(sys.argv) > 2:
    near = json.load(open(sys.argv[2]))
    nb = 0
    for fac, kind in near:
        fac = [tuple(pe) for pe in fac]
        if kind == "tower":
            pr = F(1); sm = F(0)
            for p, e in fac:
                G, _ = pdata(p, e); pr *= 1 + G; sm += G
            ok = pr - 1 - sm < 1
        else:
            ab = F(1)
            for p, e in fac:
                ab *= F(p**(e + 1) - 1, p**e*(p - 1))
            ok = ab < 2
        if not ok:
            nb += 1; print("NEAR-BOUNDARY DECISION WRONG", kind, fac)
    print(f"{len(near)} near-boundary float decisions rechecked exactly, wrong: {nb}")
