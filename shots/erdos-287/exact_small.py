"""Exhaustive: all A ⊆ [2, N] with max(A) = N, consecutive gaps <= 2, sum 1/a = 1 (exact)."""
import sys
from fractions import Fraction as F
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 40
sols = []
def search(N):
    # build downward from N: next element below a is a-1 or a-2; stop when sum hits 1
    tail = [F(0)] * (N + 2)   # tail[a] = sum_{b=2..a} 1/b (max achievable below and incl. a)
    for a in range(2, N + 1): tail[a] = tail[a - 1] + F(1, a)
    def go(a, s, chosen):
        if s == 1: sols.append(sorted(chosen)); return
        if s > 1 or a < 2: return
        # choose a; remaining elements are among [2, a-1]
        for b in (a - 1, a - 2):
            if b >= 2 and s + tail[b] >= 1:   # prune: even taking everything below cannot reach 1
                go2(b, s, chosen)
    def go2(a, s, chosen):
        s2 = s + F(1, a)
        chosen.append(a)
        if s2 == 1: sols.append(sorted(chosen))
        elif s2 < 1:
            for b in (a - 1, a - 2):
                if b >= 2 and s2 + tail[b] >= 1: go2(b, s2, chosen)
        chosen.pop()
    go2(N, F(0), [])
for N in range(2, NMAX + 1): search(N)
print("solutions with max <= %d:" % NMAX, sols)
