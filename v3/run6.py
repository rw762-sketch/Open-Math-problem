import sys, time
sys.path.insert(0, '..'); sys.path.insert(0, '../indep')
from v3 import *
from enh import gain_set
from hybrid_fast import pdata

def block_value(S):
    P1 = 1.0; s = 0.0
    for p, e in S:
        G, _ = pdata(p, e); P1 *= 1 + G; s += G
    g, piv = gain_set(S)
    return P1 - 1 - s - g

if __name__ == '__main__':
    orders = {
      '5 primes': [(3,6),(5,4),(7,3),(11,3),(13,3)],
      '6 primes': [(3,6),(5,3),(7,3),(11,2),(13,2),(17,2)],
    }
    grid = [k/20 for k in range(0, 19)]
    modes = [('thr', t) for t in (0.0, 0.03, 0.1, 0.25, 2.0)]
    for name, order in orders.items():
        t = time.time()
        b, d, m = optimise(order, grid=grid, modes=modes)
        print(name, 'no block', round(b, 5), d, [x[1] for x in m], Tower(order).run(d, m, None, detail=True)[1], round(time.time()-t), flush=True)
        bv = block_value(order[:3])
        b, d, m = optimise(order, block=(3, bv), grid=grid, modes=modes)
        print(name, 'block', round(bv, 5), round(b, 5), d, [x[1] for x in m], Tower(order).run(d, m, (3, bv), detail=True)[1], round(time.time()-t), flush=True)
