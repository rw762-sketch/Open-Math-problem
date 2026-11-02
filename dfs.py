#!/usr/bin/env python3
"""
Exact branch-and-bound search for coverings of Z/LZ with distinct odd moduli > 1
(modulus K allowed T times).

Branch: take the least uncovered residue n; for each modulus d with uses left, add the
class (n mod d) and recurse.  Bound: if the number of uncovered residues exceeds the
total coverage still available from unused moduli, prune.  Bitsets as Python ints.

Returns a witness (list of (r, d)) or None (exhaustive: no covering exists for this L).
"""
import sys, json, time


def odd_divisors(L):
    return [d for d in range(3, L + 1, 2) if L % d == 0]


def class_mask(L, r, d):
    m = 0
    for n in range(r, L, d):
        m |= 1 << n
    return m


def search(L, K=9, T=2, forbid=(), verbose=False):
    divs = [d for d in odd_divisors(L) if d not in forbid]
    masks = {d: [class_mask(L, r, d) for r in range(d)] for d in divs}
    uses = {d: (T if d == K else 1) for d in divs}
    full = (1 << L) - 1
    # coverage capacity of each modulus = L/d per remaining use
    cap = sum(uses[d] * (L // d) for d in divs)
    chosen = []
    nodes = [0]
    t0 = time.time()
    # order moduli by size descending (large classes first tends to find solutions faster)
    divs_sorted = sorted(divs)

    def rec(covered, cap):
        nodes[0] += 1
        if covered == full:
            return True
        missing = L - bin(covered).count("1")
        if missing > cap:
            return False
        # least uncovered residue
        n = (~covered & full).bit_length()
        n = (((~covered) & full) & -((~covered) & full)).bit_length() - 1
        for d in divs_sorted:
            if uses[d] == 0:
                continue
            r = n % d
            m = masks[d][r]
            uses[d] -= 1
            chosen.append((r, d))
            if rec(covered | m, cap - L // d):
                return True
            chosen.pop()
            uses[d] += 1
        return False

    # symmetry breaking: translate so that residue 0 is covered by the smallest modulus 3? No:
    # we only fix that residue 0 is covered by *some* class, which the branching already does.
    ok = rec(0, cap)
    if verbose:
        print(f"L={L}: {'SAT' if ok else 'UNSAT'} nodes={nodes[0]} {time.time()-t0:.1f}s", file=sys.stderr)
    return list(chosen) if ok else None


if __name__ == "__main__":
    L = int(sys.argv[1]); K = int(sys.argv[2]) if len(sys.argv) > 2 else 9
    T = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    w = search(L, K, T, verbose=True)
    if w:
        out = {"L": L, "K": K, "T": T, "classes": [[r, d] for r, d in w]}
        print(json.dumps(out))
    else:
        print(json.dumps({"L": L, "K": K, "T": T, "result": "UNSAT"}))
