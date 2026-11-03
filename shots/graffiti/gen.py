"""All graphs on n vertices up to isomorphism (by vertex extension + pynauty certificates).
Writes graphs as adjacency bitmask lists, one graph per line, to g{n}.txt; connected flag computed later."""
import sys, pynauty, pickle
def cert(n, adj):
    g = pynauty.Graph(n, adjacency_dict={i: [j for j in range(n) if adj[i] >> j & 1] for i in range(n)})
    return pynauty.certificate(g)
N = int(sys.argv[1])
cur = [[0]]  # n=1
for n in range(2, N + 1):
    seen = {}; nxt = []
    for adj in cur:
        for S in range(1 << (n - 1)):
            a = adj[:] + [S]
            a = [a[i] | ((S >> i & 1) << (n - 1)) if i < n - 1 else S for i in range(n)]
            c = cert(n, a)
            if c not in seen:
                seen[c] = 1; nxt.append(a)
    cur = nxt
    print(n, len(cur), flush=True)
    pickle.dump(cur, open(f"g{n}.pkl", "wb"))
