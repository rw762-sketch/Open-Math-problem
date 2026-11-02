#!/usr/bin/env python3
"""
Scan all odd L <= N with sigma(L) >= 2L (the only possible covering numbers, by the density
bound) and report every L that the hybrid certificate does NOT exclude.

Enumeration: DFS over odd primes in increasing order.  Bulk step: when the next prime q exceeds
sqrt(N/m), every child m*q is a leaf with q the largest prime, exponent 1; the certificate value
is non-increasing in q for fixed deltas (G_q = 1/(q-1) decreases and q is exposed last), so one
evaluation at the smallest q (plus a binary search if it fails) settles the whole range.
"""
import sys, math, time
from hybrid_fast import pdata, eta_order, tower, DGRID

N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**9
LIM = int(sys.argv[2]) if len(sys.argv) > 2 else min(N // 945 + 10, 3 * 10**7)

# odd primes up to LIM
sieve = bytearray([1]) * (LIM + 1)
sieve[0:2] = b"\x00\x00"
for i in range(2, int(LIM ** 0.5) + 1):
    if sieve[i]:
        sieve[i * i :: i] = bytearray(len(range(i * i, LIM + 1, i)))
PR = [i for i in range(3, LIM + 1) if sieve[i]]
del sieve


def sigma_ratio(p, e):
    return (p ** (e + 1) - 1) / (p ** e * (p - 1))


def eta_with_deltas(fac):
    data = [pdata(p, e) for p, e in fac]
    n = len(data)
    deltas = [0.0] * n
    b = eta_order(data, deltas)
    imp = True
    while imp:
        imp = False
        for i in range(1, n):
            for gg in DGRID:
                c = deltas[:]
                c[i] = gg
                v = eta_order(data, c)
                if v < b - 1e-15:
                    b, deltas, imp = v, c, True
    return b, deltas


WATCH = {6891885, 11486475}
NEAR = []  # (fac, kind) near-boundary float decisions to recheck exactly
CERTS = []  # (factorisation in exposure order, deltas) with eta < 1
def refine(fac):
    """all prime orders on the coarse grid, then a fine grid on the best 6 orders."""
    import hybrid_fast as H
    from itertools import permutations
    fac = list(fac)
    def eb(o):
        data = [H.pdata(p, e) for p, e in o]
        n = len(data); d = [0.0] * n; b = H.eta_order(data, d); imp = True
        while imp:
            imp = False
            for i in range(1, n):
                for gg in H.DGRID:
                    c = d[:]; c[i] = gg; v = H.eta_order(data, c)
                    if v < b - 1e-15:
                        b, d, imp = v, c, True
        return b, d
    if len(fac) <= 7:
        orders = list(permutations(fac))
    else:
        head, tail = fac[:6], fac[6:]
        orders = [list(o) + tail for o in permutations(head)]
    saved = H.DGRID
    scored = sorted((eb(list(o)) + (list(o),) for o in orders), key=lambda t: t[0])
    H.DGRID = [k / 200 for k in range(101)]
    cands = [eb(o) + (o,) for _, _, o in scored[:6]] + [scored[0]]
    H.DGRID = saved
    b, d, o = min(cands, key=lambda t: t[0])
    if b < 1:
        CERTS.append((o, d))
    return b


stats = {"abundant": 0, "tower_fail": 0, "bulk": 0}
fails = []


def check(m, fac):
    stats["abundant"] += 1
    t = tower(fac)
    if t < 1:
        if t > 0.99:
            NEAR.append((list(fac), "tower"))
        return
    stats["tower_fail"] += 1
    if m in WATCH:
        print("watch", m, "evaluated", flush=True)
    e, dd = eta_with_deltas(fac)
    if e < 1:
        CERTS.append((list(fac), dd))
    else:
        e = refine(fac)
    if e >= 1:
        fails.append((m, list(fac), e))
        print("NOT EXCLUDED", m, fac, round(e, 4), flush=True)


def maxgain(idx, budget):
    g, prod = 1.0, 1
    j = idx
    while j < len(PR) and prod * PR[j] <= budget:
        prod *= PR[j]
        g *= PR[j] / (PR[j] - 1)
        j += 1
    return g


def bulk(m, fac, ab, lo_idx, qmax):
    """children m*q, q prime in [PR[lo_idx], qmax], each a leaf with q largest, exponent 1."""
    hi_idx = lo_idx
    # restrict to abundant children: ab * (1 + 1/q) >= 2
    if ab < 2:
        qa = 1.0 / (2.0 / ab - 1.0)
        qmax = min(qmax, int(qa))
    import bisect
    hi_idx = bisect.bisect_right(PR, qmax)
    if hi_idx <= lo_idx:
        return
    stats["bulk"] += 1
    q0 = PR[lo_idx]
    fac0 = fac + [(q0, 1)]
    stats["abundant"] += hi_idx - lo_idx
    t0_ = tower(fac0)
    if t0_ < 1:
        if t0_ > 0.99:
            NEAR.append((fac0, "tower"))
        return
    stats["tower_fail"] += 1
    if m * q0 in WATCH:
        print("watch", m * q0, "evaluated in bulk", flush=True)
    e0, d0 = eta_with_deltas(fac0)
    if e0 < 1:
        CERTS.append((fac0, d0))  # covers all larger q in the range (monotone)
        return
    if qmax > PR[-1]:
        print("WARNING: bulk failure may extend past prime table", m, fac, qmax, flush=True)
    # binary search smallest index where eta (with re-optimised deltas) < 1
    lo, hi = lo_idx, hi_idx
    hcert = None
    while lo < hi:
        mid = (lo + hi) // 2
        e, dm = eta_with_deltas(fac + [(PR[mid], 1)])
        if e < 1:
            hi = mid
            hcert = (fac + [(PR[mid], 1)], dm)
        else:
            lo = mid + 1
    if hcert:
        CERTS.append(hcert)
    for k in range(lo_idx, lo):
        q = PR[k]
        e, dk = eta_with_deltas(fac + [(q, 1)])
        if e < 1:
            CERTS.append((fac + [(q, 1)], dk))
        else:
            e = refine(fac + [(q, 1)])
        if e < 1:
            continue
        fails.append((m * q, fac + [(q, 1)], e))
        print("NOT EXCLUDED", m * q, fac + [(q, 1)], round(e, 4), flush=True)


def dfs(m, fac, ab, idx):
    if ab >= 2 and fac:
        check(m, fac)
    elif fac and ab > 2 - 1e-9:
        NEAR.append((list(fac), "abundance"))
    j = idx
    while True:
        if j >= len(PR):
            if m * (PR[-1] + 2) <= N:
                print("WARNING: prime table exhausted at", m, fac, flush=True)
            break
        q = PR[j]
        if m * q > N:
            break
        if ab * maxgain(j, N // m) < 2:
            break
        if q * q > N // m:
            bulk(m, fac, ab, j, N // m)
            break
        mm, e = m * q, 1
        while mm <= N:
            dfs(mm, fac + [(q, e)], ab * sigma_ratio(q, e), j + 1)
            mm *= q
            e += 1
        j += 1


t0 = time.time()
dfs(1, [], 1.0, 0)
print(f"N={N:.3g}: odd abundant L counted={stats['abundant']}, tower fails evaluated={stats['tower_fail']}, "
      f"bulk ranges={stats['bulk']}, NOT excluded by hybrid: {len(fails)}, time {time.time()-t0:.0f}s")
if fails:
    fails.sort()
    print("smallest not excluded:", fails[0])

import json
with open(f"hybrid_certs_{N:.0e}.json", "w") as fh:
    json.dump([[[list(pe) for pe in o], d] for o, d in CERTS], fh)
print("certificates written:", len(CERTS))
with open(f"hybrid_near_{N:.0e}.json", "w") as fh:
    json.dump([[[list(pe) for pe in f], k] for f, k in NEAR], fh)
print("near-boundary float decisions logged:", len(NEAR))
