#!/usr/bin/env python3
"""
SAT search for near-odd covering systems.

Target: a covering system of Z whose moduli are odd, > 1, distinct, except
that one designated modulus K may be used up to T times (T = 1 is the open
Erdős–Selfridge odd covering problem; T = 2, K = 9 is the open bound t_9 <= 2).

Encoding (over Z/LZ for a chosen odd L):
  variable x[d][r]  <=>  the class  r (mod d)  is in the system,  d | L, d odd, d > 1
  (C1) coverage: for every n in [0, L):  OR_{d} x[d][n mod d]
  (C2) distinctness: for d != K, at most one r has x[d][r]
  (C3) repeat budget: for d = K, at most T classes
  (C4) symmetry breaking: class 0 (mod 3) is present if 3 | L  (translation invariance)

Usage:
  python3 search.py L [--K 9] [--T 2] [--out witness.json] [--forbid d1,d2,...]
"""
import argparse, json, sys, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType


def odd_divisors(L):
    return [d for d in range(3, L + 1, 2) if L % d == 0]


def build(L, K, T, forbid):
    divs = [d for d in odd_divisors(L) if d not in forbid]
    var = {}
    nv = 0
    for d in divs:
        for r in range(d):
            nv += 1
            var[(d, r)] = nv
    clauses = []
    # (C1) coverage
    for n in range(L):
        clauses.append([var[(d, n % d)] for d in divs])
    # (C2)/(C3) cardinality on each modulus
    top = nv
    for d in divs:
        lits = [var[(d, r)] for r in range(d)]
        bound = T if d == K else 1
        enc = CardEnc.atmost(lits=lits, bound=bound, top_id=top, encoding=EncType.seqcounter)
        clauses.extend(enc.clauses)
        top = max(top, enc.nv)
    # (C4) symmetry: translate so that 0 mod 3 is used, if 3 | L and 3 allowed
    if 3 in divs:
        clauses.append([var[(3, 0)]])
    return divs, var, clauses, top


def density(L, K, T, forbid=()):
    """sum of 1/d over usable moduli, counting K with multiplicity T.
    A covering needs this >= 1 (necessary, not sufficient)."""
    from fractions import Fraction
    s = Fraction(0)
    for d in odd_divisors(L):
        if d in forbid:
            continue
        s += Fraction(T if d == K else 1, d)
    return s


def solve(L, K=9, T=2, forbid=(), verbose=True, conf_budget=None):
    """Returns witness dict, None for UNSAT, or 'UNKNOWN' if the conflict budget ran out."""
    t0 = time.time()
    if density(L, K, T, forbid) < 1:
        if verbose:
            print(f"L={L}: density {float(density(L,K,T,forbid)):.3f} < 1, UNSAT a priori", file=sys.stderr)
        return None
    divs, var, clauses, top = build(L, K, T, set(forbid))
    if verbose:
        print(f"L={L} |divs|={len(divs)} vars={top} clauses={len(clauses)} density={float(density(L,K,T,forbid)):.3f}", file=sys.stderr)
    inv = {v: k for k, v in var.items()}
    with Cadical153(bootstrap_with=clauses) as s:
        if conf_budget is None:
            ok = s.solve()
        else:
            s.conf_budget(conf_budget)
            ok = s.solve_limited()
        if ok is None:
            if verbose:
                print(f"UNKNOWN (budget) in {time.time()-t0:.1f}s", file=sys.stderr)
            return "UNKNOWN"
        if not ok:
            if verbose:
                print(f"UNSAT in {time.time()-t0:.1f}s", file=sys.stderr)
            return None
        model = s.get_model()
    classes = sorted(inv[v] for v in model if v > 0 and v in inv)
    if verbose:
        print(f"SAT in {time.time()-t0:.1f}s, {len(classes)} classes", file=sys.stderr)
    return {"L": L, "K": K, "T": T, "classes": [[r, d] for (d, r) in classes]}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("L", type=int)
    ap.add_argument("--K", type=int, default=9)
    ap.add_argument("--T", type=int, default=2)
    ap.add_argument("--out", default=None)
    ap.add_argument("--forbid", default="")
    ap.add_argument("--budget", type=int, default=None, help="conflict budget")
    a = ap.parse_args()
    forbid = [int(x) for x in a.forbid.split(",") if x]
    w = solve(a.L, a.K, a.T, forbid, conf_budget=a.budget)
    if w is None or w == "UNKNOWN":
        print(json.dumps({"L": a.L, "K": a.K, "T": a.T, "result": "UNSAT" if w is None else "UNKNOWN"}))
        sys.exit(1)
    if a.out:
        json.dump(w, open(a.out, "w"), indent=1)
    print(json.dumps(w))
