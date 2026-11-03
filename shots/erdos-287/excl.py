"""Erdős #287 probe. A = {n_1 < ... < n_k}, sum 1/a = 1, all gaps <= 2, N = n_k.
Exclusion: x in A with prime p | x, p^2 > N, K = N // p, j0 = x // p, requires some J ⊆ [1,K], j0 ∈ J,
with sum_{j in J} j^{-1} ≡ 0 (mod p).  If none, x ∉ A.  Two adjacent excluded x, x+1 with
N/e + 1 <= x and x + 1 <= N - 1 (n_1 < N/e + 1 since sum_{n1..N} 1/n < log(N/(n1-1))) is impossible."""
import sys, math
from functools import lru_cache
X = int(sys.argv[1]) if len(sys.argv) > 1 else 10**5
# largest prime factor sieve
lp = list(range(X + 1))
for i in range(2, int(X**0.5) + 1):
    if lp[i] == i:
        for j in range(i * i, X + 1, i):
            if lp[j] == j or True: pass
P = [0] * (X + 1)
for i in range(2, X + 1):
    if P[i] == 0:
        for j in range(i, X + 1, i): P[j] = i   # ends as largest prime factor
@lru_cache(None)
def ok(p, K, j0):
    """is there J ⊆ [1,K], j0 ∈ J, sum inverses ≡ 0 mod p ? (K < p)"""
    inv = [pow(j, -1, p) for j in range(1, K + 1)]
    reach = {inv[j0 - 1] % p}
    for j in range(1, K + 1):
        if j == j0: continue
        reach |= {(r + inv[j - 1]) % p for r in reach}
        if len(reach) == p: return True
    return 0 in reach
def excluded(x, N):
    p = P[x]
    if p * p <= N: return False
    return not ok(p, N // p, x // p)
bad = []
for N in range(3, X + 1):
    if excluded(N, N): continue
    lo = math.ceil(N / math.e + 1)
    prev = False; found = False
    for x in range(N - 1, lo - 1, -1):
        e = excluded(x, N)
        if e and prev: found = True; break
        prev = e
    if not found: bad.append(N)
print("N <= %d not ruled out:" % X, len(bad), bad[:60], bad[-10:])
