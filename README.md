# The φ-certificate for odd covering systems — Lean-verified exclusion bounds

**Problem.** Erdős–Selfridge (Erdős #7): does there exist a covering system of ℤ whose moduli
are odd, distinct and > 1? Open. This repo proves, with the Lean 4 kernel checking every step
of the mathematics, that any such system must have a *large* lcm of moduli.

## Results

| Theorem (`lean/Covering/`) | Statement | Trusted base |
|---|---|---|
| `one_le_phiSum` (Phi.lean) | φ-certificate inequality (below) | kernel; axioms `propext, Classical.choice, Quot.sound` |
| `one_le_towerSum` (Tower.lean) | tower-certificate inequality (below) | same |
| `no_covering_of_check`, `no_covering_of_towerCheck` | decidable certificates exclude `L` | same |
| `odd_covering_lcm_gt_100000` (ScanK/) | odd covering ⇒ lcm `> 10⁵` | **kernel only** (`decide +kernel`) |
| `odd_covering_lcm_gt_675674` (ScanN.lean) | odd covering ⇒ lcm `> 675674` | scan by `native_decide` (`Lean.ofReduceBool`) |
| `odd_covering_lcm_gt_1000000` (ScanT/All1M.lean) | odd covering ⇒ lcm `> 10⁶` | scan by `native_decide` |
| `odd_covering_lcm_gt_6891884` (ScanT/AllFull.lean) | odd covering ⇒ lcm `> 6 891 884` | scan by `native_decide` |

Context. Previous *certified* bound: lcm `> 10⁴` (Mian–Siddique, arXiv 2607.25628, July 2026),
whose prime-only CRT certificate stalls at `10395, 12285, 17325`; they name "charging prime-power
towers" as the needed fix, which is what the tower certificate does. McNew–Setty (arXiv 2507.23041)
classify covering numbers to `10⁶` with a MIP solver; their inclusion–exclusion inequality (their
eq. (10)) is, numerically, a stronger necessary condition than the tower certificate on odd numbers:
evaluated on odd non-deficient numbers it first fails at `11486475 = 3³·5²·7·11·13·17` (our
`tower_certificate.py` comparison), so it would informally give lcm `> 11486474`, but no odd bound is
stated there and nothing is machine-checked. So the contribution here is (i) a clean elementary sieve
certificate that is cheap for a proof kernel to evaluate, (ii) the first formally verified exclusion
bound past `10⁶`, and (iii) a 10× improvement of the kernel-only bound.

## The certificates

Let `L = ∏ p^{e_p}`, `φ` Euler's totient, `u_p = p^{e_p} − (1 + p + ⋯ + p^{e_p−1})`.

> **φ-certificate.** If `∑_{d ∣ L, d composite} 1/φ(d) < 1`, no covering system with distinct
> moduli `> 1` has lcm `L`.
>
> **Tower certificate.** If `∑_{d ∣ L, ω(d) ≥ 2} ∏_{p ∣ L} min(p^{e_p − v_p(d)}, u_p) / u_p < 1`,
> no covering system with distinct moduli `> 1` has lcm `L`. (Equal to the φ-certificate when `L`
> is squarefree; sharp at `L = 12` and `L = 80`, which are covering numbers.)

*Proof idea.* The moduli `p, p², …, p^{e_p}` are each used at most once. Sieving out their classes
leaves, modulo `p^{e_p}`, at least `u_p` residues; the CRT product `U` of these sets has size
`∏ |A_p|`. A class `c (mod d)` meets `U` in at most `∏_p min(p^{e_p − v_p(d)}, |A_p|)` residues
(by CRT, the count factors over primes). The classes with `ω(d) ≥ 2` must cover `U`; divide the
union bound by `|U|` and use `min(a,s)/s ≤ min(a,u)/u` for `u ≤ s`.

First odd non-deficient `L` not excluded: φ: `675675 = 3³·5²·7·11·13`; tower:
`6891885 = 3⁴·5·7·11·13·17` (`T = 1.0098`).

Lean files: `Count.lean` (CRT count over a prime set), `Product.lean` (general CRT product count
with arbitrary allowed residues), `Phi.lean`, `Tower.lean` (the two inequalities), `Fast.lean`
(verified √L divisor enumeration, trial-division primality), `Check.lean`, `TowerCheck.lean`
(verified p-adic valuation, decidable certificates, bridge from coverings of ℤ to the lcm, odd lcm,
tail-recursive chunked scanning), `ScanK/`, `ScanN.lean`, `ScanT/` (the scans).

## Beyond: what the next certificate would need

Running the sieve and then McNew–Setty's pairwise-coprime inclusion–exclusion on the remaining
classes (`combined_certificate.py`, not formalized, validity not yet proved) excludes
`6891885` (`0.940`) but fails at `11486475 = 3³·5²·7·11·13·17` (`1.011`), exactly where
McNew–Setty's own inequality fails. First-order sieve bounds of this kind appear to end there; going
further needs the prime-by-prime distorted sieve of Hough / Balister–Bollobás–Morris–
Sahasrabudhe–Tiba, which is a research-level formalization.

## Reproduce

```
cd lean
lake build            # mathlib from cache (≈1 GB); ScanK ≈1 CPU-hour, ScanN ≈3 min, ScanT ≈7 CPU-hours
lake env lean Covering/Axioms.lean   # prints the axioms of each headline theorem
```

Python cross-checks: `phi_certificate.py N`, `tower_certificate.py N` scan odd non-deficient `L ≤ N`;
the empirical soundness test (certificate never fires on an `L` that has a covering,
checked against brute force for `L ≤ 240` with all moduli allowed) is in the commit history.

## Also in the repo (earlier, exploratory)

`search.py`, `dfs.py`, `ladder.py`, `capacity.py`, `verify.py`: SAT and branch-and-bound
search for a covering with `9` used twice and all other moduli distinct odd (`t₉ ≤ 2`, open);
`L = 945` shown UNSAT (CaDiCaL, 557 s). `lean/Covering/Basic.lean` has the kernel-checkable
*existence* verifier for any future witness.
