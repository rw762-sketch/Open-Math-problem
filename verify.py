#!/usr/bin/env python3
"""
Independent verifier for a witness produced by search.py.

Checks, with no shared code:
  1. every modulus d is odd and > 1;
  2. every modulus other than K appears at most once; K appears at most T times;
  3. every residue n in [0, L) satisfies some class r (mod d), where L = lcm(moduli);
     by periodicity this is equivalent to the classes covering all of Z.
Exit status 0 iff all checks pass.
"""
import json, sys
from math import gcd


def lcm(a, b):
    return a * b // gcd(a, b)


def verify(w):
    K, T = w["K"], w["T"]
    classes = [(int(r), int(d)) for r, d in w["classes"]]
    L = 1
    counts = {}
    for r, d in classes:
        assert d > 1 and d % 2 == 1, f"bad modulus {d}"
        assert 0 <= r < d, f"bad residue {r} mod {d}"
        counts[d] = counts.get(d, 0) + 1
        L = lcm(L, d)
    for d, c in counts.items():
        lim = T if d == K else 1
        assert c <= lim, f"modulus {d} used {c} times (limit {lim})"
    covered = bytearray(L)
    for r, d in classes:
        for n in range(r, L, d):
            covered[n] = 1
    missing = [n for n in range(L) if not covered[n]]
    assert not missing, f"{len(missing)} residues uncovered, e.g. {missing[:5]}"
    return L, len(classes), counts.get(K, 0)


if __name__ == "__main__":
    w = json.load(open(sys.argv[1]))
    L, n, kuses = verify(w)
    print(f"OK: {n} classes, lcm {L}, modulus {w['K']} used {kuses} times, all other moduli distinct odd > 1")
