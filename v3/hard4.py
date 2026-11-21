import sys, time
sys.path.insert(0, '..'); sys.path.insert(0, '../indep')
from v3 import *
from run6 import block_value
from hybrid_fast import factor
Ls = [5547967425, 9820936125, 7638505875, 4583103525]
grid = [k/20 for k in range(0, 19)]
modes = [('thr', t) for t in (0.0, 0.03, 0.1, 0.25, 2.0)]
for L in (int(a) for a in sys.argv[1:]) if len(sys.argv) > 1 else Ls:
    fac = factor(L); t = time.time()
    b, d, m = optimise(fac, grid=grid, modes=modes)
    print(L, fac, 'no block', round(b, 5), d, [x[1] for x in m], [round(float(x), 4) for x in Tower(fac).run(d, m, None, detail=True)[1]], round(time.time()-t), flush=True)
    bv = block_value(fac[:3])
    b, d, m = optimise(fac, block=(3, bv), grid=grid, modes=modes)
    print(L, 'block', round(bv, 5), round(b, 5), d, [x[1] for x in m], [round(float(x), 4) for x in Tower(fac).run(d, m, (3, bv), detail=True)[1]], round(time.time()-t), flush=True)
