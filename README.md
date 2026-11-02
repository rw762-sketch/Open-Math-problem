# The φ-certificate for odd covering systems — Lean-verified exclusion bounds

**Problem.** Erdős–Selfridge (Erdős #7): does there exist a covering system of ℤ whose moduli
are odd, distinct and > 1? Open. This repo proves, with the Lean 4 kernel checking every step
of the mathematics, that any such system must have a *large* lcm of moduli.

## Results

| Theorem (in `lean/Covering/`) | Statement | Trusted base |
|---|---|---|
| `one_le_phiSum` (Phi.lean) | For any covering of `[0,L)` by classes with distinct moduli `> 1` dividing `L`, and any set `P` of primes dividing `L`: `1 ≤ ∑_{c, c.d ∉ P} (1/c.d) ∏_{p ∈ P, p ∣ c.d} p/(p−1)` | kernel; axioms `propext, Classical.choice, Quot.sound` |
| `no_covering_of_check` (Check.lean) | If the decidable certificate `check L` holds, no covering system with distinct moduli `> 1` has lcm `L` | same |
| `odd_covering_lcm_gt_100000` (ScanK/All.lean) | Every covering of ℤ by finitely many classes with distinct odd moduli `> 1` has lcm `> 100000` | **kernel only**, no `native_decide` (200 chunk theorems by `decide +kernel`) |
| `odd_covering_lcm_gt_675674` (ScanN.lean) | Same with lcm `> 675674` | mathematics kernel-checked; the scan of odd `L ≤ 675674` uses `native_decide` (adds axiom `Lean.ofReduceBool`, i.e. trusts the Lean compiler) |

Previous certified bound (Mian–Siddique, July 2026, arXiv 2607.25628): lcm `> 10000`, whose
prime-only CRT certificate explicitly stalls at `10395, 12285, 17325`. The φ-certificate excludes
those three in milliseconds and everything up to `675674`. The first odd abundant number it does
*not* exclude is `675675 = 3³·5²·7·11·13` (`S = 1.0127`). McNew–Setty's uncertified Gurobi
classification (arXiv 2507.23041) reaches `10⁶`.

## The certificate

Write `φ` for Euler's totient. For `L > 0`:

> **Theorem.** If `∑_{d ∣ L, d composite} 1/φ(d) < 1` then there is no covering system of ℤ with
> distinct moduli `> 1` all dividing `L`.

*Proof.* Let `P` be the primes dividing `L`. A covering uses each `p ∈ P` as a modulus at most
once, say with residue `a_p`. The residues mod `L` avoiding every `a_p (mod p)` form a CRT
product set `U` of size `L ∏_{p∈P}(1 − 1/p)`. A class `c (mod d)` with `d` composite meets `U`
in at most `(L/d) ∏_{p ∤ d}(1 − 1/p)` residues (zero unless `c` avoids every `a_p` with `p ∣ d`).
Since the composite classes must cover `U`, dividing by `|U|` gives
`1 ≤ ∑_d (1/d) ∏_{p ∣ d} p/(p−1) = ∑_d 1/φ(d)`. ∎

Taking `P = ∅` in the same argument recovers the classical density bound `∑_{d∣L, d>1} 1/d ≥ 1`
(i.e. `L` is non-deficient); `check L` is the disjunction of the two tests.

Lean proof structure: `Count.lean` (exact CRT count by induction over the prime set),
`Phi.lean` (union bound and the rational inequality), `Fast.lean` (verified √L divisor
enumeration and trial-division primality so the kernel can evaluate the certificate),
`Check.lean` (decidable certificates, bridge from coverings of ℤ to `IsCovering` at the lcm,
oddness of the lcm, chunked scanning), `ScanK/`, `ScanN.lean` (the scans).

## Reproduce

```
cd lean
lake build            # mathlib from cache (≈1 GB); ScanK takes ~1 CPU-hour, ScanN ~3 min
lake env lean Covering/Axioms.lean   # prints the axioms of each headline theorem
```

Python cross-checks: `phi_certificate.py N` scans odd non-deficient `L ≤ N`;
the empirical soundness test (certificate never fires on an `L` that has a covering,
checked against brute force for `L ≤ 240` with all moduli allowed) is in the commit history.

## Also in the repo (earlier, exploratory)

`search.py`, `dfs.py`, `ladder.py`, `capacity.py`, `verify.py`: SAT and branch-and-bound
search for a covering with `9` used twice and all other moduli distinct odd (`t₉ ≤ 2`, open);
`L = 945` shown UNSAT (CaDiCaL, 557 s). `lean/Covering/Basic.lean` has the kernel-checkable
*existence* verifier for any future witness.
