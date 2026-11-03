import networkx as nx, itertools
from fractions import Fraction as F
exec(open('subquartic_trees.py').read().split('# validate DP')[0])
best = None
for T in nx.nonisomorphic_trees(16):
    if max(d for _, d in T.degree()) > 4: continue
    g = mu_star_tree(T) - H(T)
    if best is None or g > best[0]: best = (g, T)
g, T = best
print("n=16 gap", g, "degrees", sorted((d for _, d in T.degree()), reverse=True))
print("edges", list(T.edges()))
# describe: hubs of degree 4 and their legs
for v in T:
    if T.degree(v) >= 3: print(v, "deg", T.degree(v), "nbr degs", [T.degree(w) for w in T[v]])
