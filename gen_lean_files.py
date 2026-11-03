#!/usr/bin/env python3
"""Regenerate the machine-written Lean certificate files from their data.

    python3 gen_lean_files.py            # rewrite lean/Covering/ShapedK6/L*.lean and HybridScan/C*.lean
    python3 gen_lean_files.py --check    # exit 1 if any committed file differs from what this writes

Inputs:
  * ShapedK6 (lcm > 6891884, tower/density certificate): the shaped odd moduli L <= 6891884
    (L = 3^a 5^b 7^c ... with an initial run of odd primes), sorted, cut greedily into chunks
    whose total divisor count stays <= BUDGET, so each `decide +kernel` fits in memory.
  * HybridScan (lcm > 1527701174, distorted tower certificate): lean_certs_1527701174.json,
    written by gen_lean_certs.py. Each entry is [L, [[p, e, k], ...]] in exposure order with
    caps delta = k/200; the Lean `Stage` list is that order reversed (Qs (s :: rs) = Qs rs * p^e).
    Entries are bucketed by L % 17.

The hand-written files (ShapedK6/All.lean, HybridScan/All.lean) are not generated. Nothing here
is trusted: the Lean kernel re-checks every certificate.
"""
import json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
COV = ROOT / "lean" / "Covering"
OP = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def shaped(N):
    out = []
    def gen(i, acc, exps):
        if acc > 1:
            out.append((acc, exps))
        if i >= len(OP):
            return
        a, e = acc * OP[i], 1
        while a <= N:
            gen(i + 1, a, exps + [e])
            a *= OP[i]
            e += 1
    gen(0, 1, [])
    return sorted(out)


# ---------- ShapedK6 ----------
K6_N, BUDGET = 6891884, 1120


def k6_files():
    chunks, cur, tot = [], [], 0
    for L, exps in shaped(K6_N):
        nd = 1
        for e in exps:
            nd *= e + 1
        if cur and tot + nd > BUDGET:
            chunks.append(cur)
            cur, tot = [], 0
        cur.append(L)
        tot += nd
    chunks.append(cur)
    files = {}
    for k, c in enumerate(chunks):
        files[COV / "ShapedK6" / f"L{k}.lean"] = (
            "import Covering.ShapedBound\nnamespace Covering.ShapedK6\n"
            f"def l{k} : List ℕ := [{', '.join(map(str, c))}]\n"
            f"theorem l{k}_ok : l{k}.all check2 = true := by decide +kernel\n"
            "end Covering.ShapedK6\n")
    return files


# ---------- HybridScan ----------
HY_N, NB = 1527701174, 17


def stage(p, e, k):
    return f"⟨{p}, {e}, {'0' if k == 0 else f'{k}/200'}⟩"


def hybrid_files():
    certs = json.load(open(ROOT / f"lean_certs_{HY_N}.json"))
    buckets = [[] for _ in range(NB)]
    for L, st in certs:
        buckets[L % NB].append((L, st))
    files = {}
    for i, b in enumerate(buckets):
        rows = ",\n".join(f"  ({L}, [{', '.join(stage(*s) for s in reversed(st))}])" for L, st in b)
        files[COV / "HybridScan" / f"C{i}.lean"] = (
            "import Covering.Hybrid.Check\nnamespace Covering.HybridScan\nopen Covering.Hybrid\n"
            f"/-- Certificates for the shaped moduli `L ≤ {HY_N}` with `L % {NB} = {i}`. -/\n"
            f"def c{i} : List (ℕ × List Stage) := [\n{rows}]\n"
            f"def l{i} : List ℕ := [{', '.join(str(L) for L, _ in b)}]\n"
            f"theorem l{i}_eq : c{i}.map Prod.fst = l{i} := by decide +kernel\n"
            f"theorem c{i}_ok : c{i}.all (fun t => hyb t.1 t.2) = true := by decide +kernel\n"
            f"theorem l{i}_sound : ∀ L ∈ l{i}, ∀ S, ¬ IsCovering L S := by\n"
            "  intro L hL S hS\n"
            f"  rw [← l{i}_eq] at hL\n"
            "  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hL\n"
            f"  exact no_covering_of_hyb (List.all_eq_true.mp c{i}_ok t ht) S hS\n"
            "end Covering.HybridScan\n")
    return files


def main():
    check = "--check" in sys.argv
    files = {**k6_files(), **hybrid_files()}
    bad = 0
    for path, text in files.items():
        if check:
            if not path.exists() or path.read_text() != text:
                bad += 1
                print("DIFFERS:", path.relative_to(ROOT))
        else:
            path.write_text(text)
    print(f"{len(files)} files {'checked' if check else 'written'}; differing: {bad}")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
