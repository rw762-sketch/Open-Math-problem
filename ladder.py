#!/usr/bin/env python3
"""Run search.py over every odd L (built from primes <= 23) that passes the density
precheck, with a per-L conflict budget. Results appended to results/ladder.jsonl."""
import json, os, sys, time
import search

K, T = 9, 2
BUDGET = int(sys.argv[1]) if len(sys.argv) > 1 else 300_000
LMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 3_000_000
os.makedirs("results", exist_ok=True)
out = open("results/ladder.jsonl", "a")

cands = set()
primes = [3, 5, 7, 11, 13, 17, 19, 23]
def rec(i, L):
    if L > LMAX: return
    if i == len(primes):
        cands.add(L); return
    p = primes[i]
    e = 0
    while L * p**e <= LMAX:
        rec(i + 1, L * p**e); e += 1
rec(0, 1)
cands = sorted(L for L in cands if L > 1 and search.density(L, K, T) >= 1)
print(f"{len(cands)} candidates", file=sys.stderr)

for L in cands:
    t0 = time.time()
    w = search.solve(L, K, T, verbose=False, conf_budget=BUDGET)
    rec_ = {"L": L, "K": K, "T": T, "budget": BUDGET, "secs": round(time.time() - t0, 1),
            "result": "SAT" if isinstance(w, dict) else ("UNKNOWN" if w == "UNKNOWN" else "UNSAT")}
    if isinstance(w, dict):
        path = f"results/witness_L{L}_K{K}_T{T}.json"
        json.dump(w, open(path, "w"), indent=1)
        rec_["witness"] = path
        print(f"*** SAT at L={L}: {path}", file=sys.stderr)
    out.write(json.dumps(rec_) + "\n"); out.flush()
    print(json.dumps(rec_), file=sys.stderr)
