import math
from sympy import primerange
ps = list(primerange(3, 200001))
def eta_sched(f, twice=None):
    P1 = P2 = 1.0; tot = 0.0
    for q in ps:
        g = 1/(q-2) if q == twice else 1/(q-1)
        d = 0.0 if q == 3 else f(q)
        S1 = P1 - 1
        if S1 > 0:
            M1 = g*S1; t = M1 if d == 0 else min(M1, g*g*(P2-2*P1+1)/(4*d*(1-d)))
            tot += t
        c = 1/(1-d); P1 *= 1+c*g; P2 *= 1+3*c*g
    return tot, P1, P2
best = None
for a in [0.05, 0.1, 0.2, 0.3, 0.5, 1, 2]:
    for b in [0, 0.25, 0.5, 0.75, 1.0]:
        f = lambda q, a=a, b=b: min(0.5, a / (math.log(q) ** b) if b else a)
        v = eta_sched(f)[0]
        if best is None or v < best[0]: best = (v, a, b)
        print(f"a={a} b={b}: eta={v:.4f}")
print("best", best)
