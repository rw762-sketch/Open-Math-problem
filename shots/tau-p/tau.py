"""Distorted tower certificate for squarefree odd supports 3,5,7,...,p_k, optionally with one prime p used
twice as a modulus (its pure stage removes 2 residues: u = p-2, g(1) = 1/(p-2)).
Stage data for squarefree prime q (e=1): G = g(1), Gpair = 3 g(1). Exposure order: increasing primes.
eta = sum_i min(M1_i, M2_i / (4 d_i (1-d_i))), M1 = G S1, M2 = G^2 S2, S1 = P1 - 1, S2 = P2 - 2 P1 + 1."""
import sys, math
from sympy import primerange
def run(N, twice=None, dsched=None, opt_first=25, verbose=False):
    ps = list(primerange(3, N + 1))
    G = [1/(q-2) if q == twice else 1/(q-1) for q in ps]
    def eta(ds, upto=None):
        P1 = P2 = 1.0; tot = 0.0
        for i, (g, d) in enumerate(zip(G, ds)):
            S1 = P1 - 1
            if S1 > 0:
                M1 = g * S1
                t = M1 if d == 0 else min(M1, g*g*(P2 - 2*P1 + 1)/(4*d*(1-d)))
                tot += t
            c = 1/(1-d); P1 *= 1 + c*g; P2 *= 1 + 3*c*g
        return tot
    ds = [0.5] * len(ps); ds[0] = 0.0
    grid = [k/100 for k in range(51)]
    best = eta(ds); imp = True
    while imp:
        imp = False
        for i in range(1, min(opt_first, len(ps))):
            for g in grid:
                c = ds[:]; c[i] = g; v = eta(c)
                if v < best - 1e-12: best, ds, imp = v, c, True
    return best, ds[:opt_first], len(ps)
if __name__ == "__main__":
    for N in (100, 1000, 10000, 100000):
        print("squarefree, primes <=", N, ":", round(run(N)[0], 4), flush=True)
