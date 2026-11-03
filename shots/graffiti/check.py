import sys, pickle, math
from inv import G, pc
CONJ = {
 "19":  lambda g: math.floor(g.avg_ecc() + g.maxL() + 1e-12) <= g.bip(),
 "40":  lambda g: math.ceil((g.path_cover() + g.bip() + 1) / 2 - 1e-12) <= g.forest(),
 "61":  lambda g: g.residue() + math.ceil(g.diam() / 3 - 1e-12) <= g.forest(),
 "72":  lambda g: math.ceil(g.avg_ecc() + g.maxL() / 3 - 1e-12) <= g.tree(),
 "84":  lambda g: 2 * g.rad() / g.mindeg() <= g.tree() + 1e-12,
 "96":  lambda g: g.alpha() <= 1 + min(g.dist_even(v) for v in range(g.n)) * (g.maxL() - 1),
 "133": lambda g: g.rad() + (1 if g.has_c4() else g.l()) <= g.path() + 1e-12,
 "189": lambda g: (not max(g.dist_even(v) for v in range(g.n)) <= 1 + g.sigma2()) or g.ham_path(),
 "199": lambda g: (not max(g.tree() - 2, 0) <= g.kappa()) or g.ham_path(),
}
which = sys.argv[2].split(",") if len(sys.argv) > 2 else list(CONJ)
for n in range(2, int(sys.argv[1]) + 1):
    gs = pickle.load(open(f"g{n}.pkl", "rb"))
    cnt = 0; fails = {k: [] for k in which}
    for adj in gs:
        g = G(adj)
        if any(d < 0 for d in g.D[0]): continue
        cnt += 1
        for k in which:
            if not fails[k] or len(fails[k]) < 3:
                if not CONJ[k](g): fails[k].append(adj)
    print(n, "connected", cnt, {k: (len(v), v[:1]) for k, v in fails.items() if v}, flush=True)
