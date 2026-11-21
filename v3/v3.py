#!/usr/bin/env python3
r"""Certificate v3 (floats, exploratory): distorted tower with a sharper stage bound.

Stage for prime p with cap delta over a base measure P on Z/Q (Q = product of the earlier prime powers).
Stage classes k = (n, j): n | Q, n > 1, weight c_k = g_p(j), base event E_k = class mod n, P(E_k) <= nu(n),
and P(E_k & E_l) <= nu(lcm).  S = sum_k c_k 1[E_k] >= alpha = covered fraction of the fibre, alpha <= 1.
BBMST distortion with cap delta:  new covered mass = E[(alpha - delta)^+]/(1 - delta).
With h = 1[alpha > delta], theta = P(h):
    E[(alpha - delta)^+] = E[h alpha] - delta*theta,   E[h alpha] <= theta,
    E[h S_g] <= sum_{k in g} c_k min(nu(n_k), theta)          (comonotone / "Lemma C")
    E[h S_g] <= sqrt(theta * E[S_g^2])                         (Cauchy-Schwarz; = BBMST second moment after max over theta)
so   cost <= max_{theta in [0,1]} [ min(theta, sum_g T_g(theta)) - delta*theta ] / (1 - delta).
"""
import math, itertools, sys
import numpy as np

def gvals(p, e):
    u = p ** e - (p ** e - 1) // (p - 1)
    return [min(p ** (e - v), u) / u for v in range(1, e + 1)]

THETA = np.concatenate([np.linspace(0, 1, 801)[1:], 10.0 ** np.linspace(-6, -1, 200)])
THETA.sort()

def stage_cost(nu, pair, G, delta, mode):
    """nu: array over n>1 of nu(n); pair: matrix nu(lcm(n1,n2)) over n>1; G = G_p (unnormalised by 1-delta).
    mode: ('thr', tau) -> classes with nu >= tau comonotone, the rest min(M1, CS);  returns cost."""
    M1 = G * nu.sum()
    if delta == 0:
        return min(1.0, M1)
    kind, tau = mode
    big = nu >= tau
    nb = nu[big]; sm = ~big
    M1s = G * nu[sm].sum()
    M2s = G * G * pair[np.ix_(sm, sm)].sum() if sm.any() else 0.0
    th = THETA
    if nb.size:
        A = G * np.minimum(nb[None, :], th[:, None]).sum(axis=1)
    else:
        A = np.zeros_like(th)
    T = A + np.minimum(M1s, np.sqrt(th * M2s))
    f = np.minimum(th, T) - delta * th
    return max(0.0, f.max()) / (1 - delta)

class Tower:
    def __init__(self, order):
        self.order = order
        self.g = [gvals(p, e) for p, e in order]
    def run(self, deltas, modes, block=None, detail=False):
        """block: None or (k, value): the first k primes are undistorted and cost `value` in total (independence block)."""
        # divisor table: exponent tuples -> handled as arrays nu and pair
        nu = np.array([1.0]); pair = np.array([[1.0]])
        tot = 0.0; det = []
        start = 0
        for i, (p, e) in enumerate(self.order):
            g = np.array(self.g[i]); G = g.sum(); d = deltas[i]
            if block is not None and i < block[0]:
                d = 0.0; c = 0.0 if i < block[0] - 1 else block[1]
            elif i == 0:
                c = 0.0
            else:
                c = stage_cost(nu[1:], pair[1:, 1:], G, d, modes[i])
            tot += c; det.append(c)
            # extend the divisor table by prime p with inflation 1/(1-d)
            col = np.concatenate([[1.0], g / (1 - d)])          # nu_p(v), v = 0..e
            mx = np.maximum.outer(np.arange(e + 1), np.arange(e + 1))
            pm = col[mx]                                        # nu_p(max(v1,v2))
            nu = np.kron(nu, col)
            pair = np.kron(pair, pm)
        return (tot, det) if detail else tot

GRID = [k / 40 for k in range(0, 31)]
MODES = [('thr', t) for t in (0.0, 0.01, 0.03, 0.06, 0.1, 0.15, 0.25, 0.4, 2.0)]

def optimise(order, block=None, grid=GRID, modes=MODES, rounds=6, init=0.3, verbose=False):
    T = Tower(order); n = len(order)
    k0 = block[0] if block else 1
    d = [0.0] * n; m = [modes[-1]] * n
    for i in range(k0, n): d[i] = init
    best = T.run(d, m, block)
    for r in range(rounds):
        imp = False
        for i in range(k0, n):
            for gdel in grid:
                for mo in (modes if gdel > 0 else modes[:1]):
                    dd = d[:]; mm = m[:]; dd[i] = gdel; mm[i] = mo
                    v = T.run(dd, mm, block)
                    if v < best - 1e-12:
                        best, d, m, imp = v, dd, mm, True
        if verbose: print('round', r, best, d, [x[1] for x in m], flush=True)
        if not imp: break
    return best, d, m

if __name__ == '__main__':
    sys.path.insert(0, '..')
    from hybrid_fast import factor
    for L in [int(a) for a in sys.argv[1:]]:
        fac = factor(L)
        b, d, m = optimise(fac, verbose=True)
        print(L, fac, b)
        print(Tower(fac).run(d, m, None, detail=True))
