"""Conjecture 133 on structured C4-free graphs: path(G) >= rad(G) + l(G) (C4-free case)."""
import networkx as nx, itertools, sys, time


def incidence_pg2(q):
    """Point-line incidence graph of PG(2, q), q prime."""
    pts = []
    for v in itertools.product(range(q), repeat=3):
        if v == (0, 0, 0):
            continue
        f = next(x for x in v if x)
        inv = pow(f, -1, q)
        w = tuple(x * inv % q for x in v)
        if w not in pts:
            pts.append(w)
    G = nx.Graph()
    for i, p in enumerate(pts):
        for j, l in enumerate(pts):
            if sum(a * b for a, b in zip(p, l)) % q == 0:
                G.add_edge(("p", i), ("l", j))
    return nx.convert_node_labels_to_integers(G)


def has_c4(G):
    nodes = list(G)
    for i, u in enumerate(nodes):
        for w in nodes[i + 1:]:
            if len((set(G[u]) & set(G[w])) - {u, w}) >= 2:
                return True
    return False


def alpha(G, S):
    H = G.subgraph(S)
    return max((len(c) for c in nx.find_cliques(nx.complement(H))), default=0)


def longest_induced_path(G, limit=None, tl=900):
    nodes = list(G)
    idx = {v: i for i, v in enumerate(nodes)}
    adj = [0] * len(nodes)
    for u, v in G.edges():
        adj[idx[u]] |= 1 << idx[v]
        adj[idx[v]] |= 1 << idx[u]
    best = [1]
    t0 = time.time()

    def rec(end, S, length):
        if length > best[0]:
            best[0] = length
        if (limit and best[0] >= limit) or time.time() - t0 > tl:
            return True
        m = adj[end] & ~S
        while m:
            w = (m & -m).bit_length() - 1
            m &= m - 1
            if adj[w] & S == 1 << end:
                if rec(w, S | (1 << w), length + 1):
                    return True
        return False

    for s in range(len(nodes)):
        if rec(s, 1 << s, 1):
            break
    return best[0], time.time() - t0 > tl


graphs = [("Petersen", nx.petersen_graph()), ("Hoffman-Singleton", nx.hoffman_singleton_graph())]
graphs += [(f"PG(2,{q}) incidence", incidence_pg2(q)) for q in (2, 3, 5, 7)]
for name, G in graphs:
    rad = nx.radius(G)
    c4 = has_c4(G)
    l = sum(alpha(G, list(G[v])) for v in G) / G.number_of_nodes()
    need = rad + (1 if c4 else l)
    p, timed_out = longest_induced_path(G, limit=int(need) + 3)
    print(f"{name}: n={G.number_of_nodes()} rad={rad} C4={c4} l={l:.3f} need path>={need:.3f}; "
          f"longest induced path found {p}{' (search capped)' if timed_out else ''}", flush=True)
