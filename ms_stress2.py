import itertools, sys
from fractions import Fraction
from ms_lemma_stress import phi, min_uncovered
# seeds with Phi < 0
seeds = {12: (2,3,4,6,12), 24: (2,3,4,6,8,12,24), 20: (2,4,5,10,20), 18: (2,3,6,9,18)}
found = tested = viol = 0
for L in [60, 84, 120, 180, 420, 36, 72, 90, 126, 140]:
    D = [d for d in range(2, L + 1) if L % d == 0]
    for s, W in seeds.items():
        if L % s: continue
        rest = [d for d in D if d not in W]
        for k in range(1, 4):
            for E in itertools.combinations(rest, k):
                M = list(W) + list(E)
                p = phi(M)
                if p <= 0: continue
                found += 1
                prod = 1
                for m in M[1:]: prod *= m
                if prod > 3_000_000: continue
                tested += 1
                u = Fraction(min_uncovered(L, M), L)
                print(f"L={L} M={M} Phi={p} uncovered={u} {'VIOLATION' if u < p else 'ok'}", flush=True)
                if u < p: viol += 1
print("found", found, "tested", tested, "violations", viol)
