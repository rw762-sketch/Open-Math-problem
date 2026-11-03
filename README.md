# Odd covering systems: a distorted tower sieve, checked in Lean

[![Lean proofs](https://github.com/rw762-sketch/Open-Math-problem/actions/workflows/lean.yml/badge.svg)](https://github.com/rw762-sketch/Open-Math-problem/actions/workflows/lean.yml)


*Ryan Wu and Claude Fable 5.1 · November 2026 · Status: problem **open**; results below as stated.*
*Pages: [problem statement](docs/PROBLEM.md) · [progress report with prose proofs and claims ledger](docs/PROGRESS.md) · [references](docs/references/) · [milestones](MILESTONES.md).*

**Problem.** Erdős–Selfridge (Erdős #7): does there exist a covering system of ℤ whose moduli
are odd, distinct and > 1? Open. This repo proves, with the Lean 4 kernel checking every step
of the mathematics, that any such system must have a *large* lcm of moduli.

**Headline (2 Nov 2026).** `odd_covering_lcm_gt_1527701174`: **every covering system of ℤ with
odd, distinct moduli `> 1` has lcm of moduli `≥ 1 527 701 175`.** Checked by the Lean kernel alone
(axioms `propext, Classical.choice, Quot.sound`; no `native_decide`, no `sorry`); the full library
builds from scratch in about 7 minutes. The proof combines three pieces, all formalized here:
(1) **prime replacement** for arbitrary exponents, which reduces any odd covering to one whose
lcm is `3^a 5^b 7^c ⋯` with an initial run of odd primes; (2) the **distorted tower certificate**,
which at each prime conditions on the complement of the prime-power classes and then applies
the Balister–Bollobás–Morris–Sahasrabudhe–Tiba distortion to the mixed classes; (3) an explicit
certificate for each of the 1638 initial-run moduli below the bound. See
[docs/PROGRESS.md §1b](docs/PROGRESS.md).

**Literature caveat (2 Nov 2026).** The tower-sieve idea appears independently in Hackmon
(Zenodo, Apr 2026, per prime support, not formalized), and Schroeder (Zenodo, Sep 2026) *claims*
lcm ≥ 9 704 539 845 with a Lean package that we have not yet rebuilt. See
[docs/PROGRESS.md §3](docs/PROGRESS.md) for exactly what this changes.

## Results

| Theorem (`lean/Covering/`) | Statement | Trusted base |
|---|---|---|
| `odd_covering_lcm_gt_1527701174` (HybridScan/All.lean) | odd covering ⇒ lcm `> 1 527 701 174` | **kernel only**, standard axioms |
| `Hybrid.one_le_eta` (Hybrid/Main.lean) | distorted tower certificate: a covering forces `η ≥ 1` | kernel, standard axioms |
| `replace_one`, `reduce_to_shaped` (Replace.lean, Shaped.lean) | prime replacement, any exponents; reduction to initial-run lcm | kernel, standard axioms |
| `five_primes_of_odd_covering` (FourPrimes.lean) | odd covering ⇒ at least 5 distinct primes divide the lcm | kernel, standard axioms |
| `towerSum_le_bff`, `no_covering_3_5_7_11` (BFF.lean) | tower certificate ⇒ Berger–Felzenbaum–Fraenkel; four-prime theorem | kernel, standard axioms |
| `odd_covering_lcm_gt_6891884_kernel` (ShapedK6/All.lean) | odd covering ⇒ lcm `> 6 891 884` (tower certificate only) | kernel, standard axioms |
| `one_le_towerSum`, `one_le_phiSum` (Tower.lean, Phi.lean) | tower and φ-certificate inequalities | kernel, standard axioms |
| `odd_covering_lcm_gt_675674` (ScanN.lean) | earlier brute-force scan, superseded | `native_decide` |

The brute-force scans `ScanK/`, `ScanT/` are in `attic/` (superseded). Axiom report:
`cd lean && lake env lean Covering/Axioms.lean`.

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

Lean files (`lean/Covering/`):
- `Count.lean`, `Product.lean`: CRT counts over a prime set, with arbitrary allowed residues.
- `Phi.lean`, `Tower.lean`: the φ- and tower-certificate inequalities.
- `Fast.lean`, `Check.lean`, `TowerCheck.lean`: verified divisor enumeration, trial-division
  primality and p-adic valuation; decidable certificates; bridge from coverings of ℤ to the lcm.
- `BFF.lean`, `FourPrimes.lean`: tower ⇒ BFF, the four-prime theorem, `ω(lcm) ≥ 5`.
- `Replace.lean`, `Shaped.lean`, `ShapedBound.lean`: prime replacement and the reduction to
  initial-run (shaped) moduli.
- `Hybrid/`: the distorted tower certificate (`Fibre`, `Nu`, `Main`: `one_le_eta`; `Check`: `hyb`).
- `ShapedK6/`, `HybridScan/`: the certificate lists behind the two kernel-only bounds. The `L*.lean`
  and `C*.lean` files are machine-written by `gen_lean_files.py`.
- `ScanN.lean`: the old `native_decide` scan. `Test/`: control values (the classic covering of 12,
  the first `L` each certificate cannot exclude).

## Beyond: what the next certificate would need

First-order sieve bounds (the tower certificate; the sieve followed by McNew–Setty's pairwise-coprime
inclusion–exclusion in `combined_certificate.py`) stop at `11486475 = 3³·5²·7·11·13·17`. The
distorted tower certificate gets past that wall, and is what the headline uses. It in turn fails on
20 odd non-deficient `L ≤ 10¹⁰`, the smallest being `1527701175 = 3³5²7²·11·13·17·19`
(`η = 1.014`). It also cannot give `ω(lcm) ≥ 6`: at `{3,5,7,11,13}` it fails for large exponents.
Going further needs an exact (non-union-bound) treatment of the first mixed stage `{3,5}`, or a
prime-by-prime distorted sieve in the style of Hough / BBMST. See [MILESTONES.md](MILESTONES.md).

## Reproduce

```
cd lean
lake exe cache get    # Mathlib from cache (≈1 GB)
lake build            # whole library, about 7 minutes from scratch
lake env lean Covering/Axioms.lean   # prints the axioms of each headline theorem
python3 ../gen_lean_files.py --check # the generated certificate files match their data
```

CI (`.github/workflows/lean.yml`) runs the same steps on every push. The certificate data come from
`gen_lean_certs.py` (hybrid) and the shaped-moduli enumeration in `gen_lean_files.py`.

Python cross-checks: `phi_certificate.py N`, `tower_certificate.py N` scan odd non-deficient `L ≤ N`;
the empirical soundness test (certificate never fires on an `L` that has a covering,
checked against brute force for `L ≤ 240` with all moduli allowed) is in the commit history.

## Also in the repo (earlier, exploratory)

`search.py`, `dfs.py`, `ladder.py`, `capacity.py`, `verify.py`: SAT and branch-and-bound
search for a covering with `9` used twice and all other moduli distinct odd (`t₉ ≤ 2`, open);
`L = 945` shown UNSAT (CaDiCaL, 557 s). `lean/Covering/Basic.lean` has the kernel-checkable
*existence* verifier for any future witness.
