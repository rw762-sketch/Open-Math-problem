# Odd covering systems — search + kernel-checked verification

Target problem: the Erdős–Selfridge **odd covering problem** (Erdős #7). Does a covering
system of ℤ exist whose moduli are odd, distinct and > 1? Open. The full problem is out of
reach; this repo attacks the clean sub-target

> **t₉ ≤ 2**: a covering system in which every modulus is odd, > 1 and distinct, *except*
> that 9 may be used twice.

Known: t₉ ≤ 3 (Bispels–Cohen–Harrington–Lowrance–Pontes–Schaumann–Wong, 2025), who name
t₉ ≤ 2 as the next step. An odd covering system would give t_k ≤ 1 for every k.

## Pipeline

```
search.py / dfs.py   -> witness.json          (SAT / branch-and-bound over Z/LZ)
verify.py            -> independent re-check   (no shared code with the search)
lean/                -> kernel-checked proof   (core Lean 4, no mathlib, no native_decide)
```

* `search.py L --K 9 --T 2` — CaDiCaL encoding: coverage clauses for every residue mod L,
  at-most-one class per modulus (at-most-T for K), density precheck.
* `dfs.py L K T` — exact branch-and-bound on the least uncovered residue with a capacity bound.
* `capacity.py L` — the CRT capacity certificate (Mian–Siddique 2026) adapted to a repeat
  budget; proves non-existence for many L by a one-line inequality.
* `ladder.py BUDGET LMAX` — runs the search over every candidate L passing the density test.
* `lean/Covering/Basic.lean` — `coversInt_of_check`: if the finite checker `checkBelow cs L`
  returns `true` and every modulus divides `L`, then the classes cover all of ℤ. The checker is
  structural recursion on `L` so the kernel evaluates it with `decide`.
* `lean/Covering/Smoke.lean` — the classic period-12 covering, kernel-checked; a broken one
  rejected; a timing probe.

## Status (2026-11-02)

* Pipeline verified end to end on the classic covering {0 (2), 0 (3), 1 (4), 5 (6), 7 (12)}.
* Density + capacity prefilters: of 1368 candidate odd L ≤ 3·10⁶ built from primes ≤ 23,
  755 survive. Smallest survivor L = 945.
* **L = 945 is UNSAT** for (K, T) = (9, 2): CaDiCaL proof in 557 s. Branch-and-bound is slower.
* Bottleneck: proving UNSAT is slow (minutes per L at L ≈ 10³, hours beyond). All published
  near-odd coverings use enormous lcms (prime-power tails like 3², 3³, …, 3^{q−1}), so a small-lcm
  witness for t₉ ≤ 2 may well not exist; the search cannot currently say either way.

## Honest assessment

A kernel-checked *existence* proof is possible the moment a witness is found: it is one
`decide` call. A kernel-checked *non-existence* result needs a proof the kernel can replay;
the capacity certificate is one (it is a closed inequality), the SAT solver's UNSAT is not
(it would need DRAT replay inside Lean, which is not set up here).

## Reproduce

```
pip install python-sat
python3 search.py 945 --K 9 --T 2            # UNSAT, ~10 min
python3 verify.py results/witness.json       # when a witness exists
cd lean && lake build                        # needs elan; core Lean 4.22, no mathlib
```
