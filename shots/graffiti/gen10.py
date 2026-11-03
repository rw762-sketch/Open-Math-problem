"""Stream all connected graphs on 10 vertices (up to isomorphism) to stdout, one per line, from g9.pkl."""
import pickle, pynauty, sys
g9 = pickle.load(open("g9.pkl", "rb"))
n = 10; seen = set(); out = sys.stdout; full = (1 << n) - 1
def connected(a):
    seen_v = 1; fr = 1
    while fr:
        nb = 0; m = fr
        while m:
            u = (m & -m).bit_length() - 1; m &= m - 1; nb |= a[u]
        nb &= ~seen_v; seen_v |= nb; fr = nb
    return seen_v == full
START = int(sys.argv[1]) if len(sys.argv) > 1 else 0
for idx, adj in enumerate(g9):
    if idx < START: continue
    for S in range(1, 1 << 9):          # S = 0 gives a disconnected graph
        a = [adj[i] | ((S >> i & 1) << 9) for i in range(9)] + [S]
        if not connected(a): continue
        c = pynauty.certificate(pynauty.Graph(n, adjacency_dict={i: [j for j in range(n) if a[i] >> j & 1] for i in range(n)}))
        h = hash(c)
        if h in seen: continue
        seen.add(h)
        out.write("10 " + " ".join(map(str, a)) + "\n")
    if idx % 20000 == 0: sys.stderr.write(f"{idx}/{len(g9)} base graphs, {len(seen)} connected so far\n")
sys.stderr.write(f"done: {len(seen)} connected graphs on 10 vertices (A001349 says 11716571)\n")
