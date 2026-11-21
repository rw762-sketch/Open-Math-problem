#!/usr/bin/env python3
"""Exhaustive maximum coverage of U (pure survivors) by the mixed classes for L = 315 = 9*5*7.
All non-nested pure configurations are equivalent to the canonical one under x -> ux + t (CRT), so one suffices;
a nested pure 9-class is dominated.  Mixed moduli: 15, 45, 21, 63, 35, 105, 315."""
import itertools
L = 315
pure = {3: 1, 9: 3, 5: 1, 7: 1}
U = [n for n in range(L) if all(n % m != r for m, r in pure.items())]
idx = {n: i for i, n in enumerate(U)}
def masks(d):
    out = {}
    for r in range(d):
        mk = 0
        for n in U:
            if n % d == r: mk |= 1 << idx[n]
        if mk: out[r] = mk
    return sorted(set(out.values()), key=lambda m: -bin(m).count("1"))
M = {d: masks(d) for d in (15, 45, 21, 63, 35, 105, 315)}
print("|U| =", len(U), {d: (len(v), bin(v[0]).count("1")) for d, v in M.items()})
best = 0; cnt = 0
pc = lambda m: bin(m).count("1")
for a in M[15]:
    for b in M[45]:
        ab = a | b
        for c in M[21]:
            abc = ab | c
            for d_ in M[63]:
                abcd = abc | d_
                for e in M[35]:
                    cov = abcd | e
                    # 105: best single class; 315: one more point if any left
                    g = max(pc(f & ~cov) for f in M[105])
                    tot = pc(cov) + g
                    if tot < len(U): tot += 1
                    cnt += 1
                    if tot > best: best = tot
print("configs", cnt, "max covered =", best, "=> u(315) =", len(U) - best)
