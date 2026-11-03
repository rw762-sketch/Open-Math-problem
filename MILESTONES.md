# Milestones — odd covering problem (Erdős #7)

Status key: ✅ done · 🔄 running · ⬜ next · 🧪 exploratory

## What the literature check changed (SciSpace, 2026-11-02)

Three items found that bear directly on how our results should be stated:

| Paper | What it does | Relation to this repo |
|---|---|---|
| Zeraoulia Rafik, Zenodo 10.5281/zenodo.18360978 (Jan 2026) | Only the density condition `Σ_{d∣L,d>1} 1/d ≥ 1` ⇒ `L ≥ 945` for odd `L`. | Strictly weaker than our φ-certificate (which starts from the same lemma and sieves). |
| Idan Hackmon, Zenodo 10.5281/zenodo.19495463 (Apr 2026) | "Weight-function method": sieve out the prime-power towers, bound composite coverage of the weight region `W` by a union bound, `R = 41/45` for `{3,5,7,11}`; excludes any odd `L` with ≤ 4 prime factors, any exponents. Not formalized. | **Same idea as our tower certificate.** His bound uses the limit `(p−2)/(p−1)` per prime; ours is the exact finite-`L` version with `min(p^{e−v}, u_p)/u_p`, evaluated per `L`, and is Lean-verified. So: the method is prior art (independently found, 7 months earlier); the sharp per-`L` form, the formalization and the numerical scans are ours. |
| Michael Schroeder, Zenodo 10.5281/zenodo.22759614 (Sep 2026) | Claims `ω(lcm) ≥ 9` for every odd distinct covering, hence **lcm ≥ 9 704 539 845**, with a Lean 4 package (no `sorry`, no `native_decide` found; toolchain v4.32.0-rc1, 28 001-inequality certificate). Also cites the Berger–Felzenbaum–Fraenkel condition `∏(p−1)/(p−2) − Σ 1/(p−2) > 2`. | If it checks, it supersedes our numerical bound by a factor ≈ 1400. Not peer-reviewed; third in a self-published series (ranks 7, 8, 9). **Must be independently rebuilt before we cite it as fact.** |

Honest position after the check: the φ/tower certificate is a clean, elementary, cheaply
kernel-checkable condition and ours is the first kernel-only formalization of a sieve certificate
for this problem, but it is no longer the strongest *claimed* bound. The write-up should say so.

## Milestone 1 — close out the current Lean results ✅ (superseded by the kernel-only shaped route)
- ✅ `one_le_phiSum`, `one_le_towerSum`, decidable certificates (kernel, standard axioms).
- ✅ `odd_covering_lcm_gt_675674`, `odd_covering_lcm_gt_1000000` (`native_decide`).
- 🔄 `odd_covering_lcm_gt_100000` kernel-only (ScanK, 79/165 chunks; ~1.5 min/chunk).
- 🔄 `odd_covering_lcm_gt_6891884` (ScanT, 90/173 chunks; ~2.5 min/chunk).
- ⬜ Commit, regenerate `Axioms.lean` output, tag `v0.1`.

## Milestone 2 — reproduce Schroeder's Lean package ⬜
- Build `lean_proof.tar.xz` (Lean v4.32.0-rc1 + pinned mathlib) in a clean directory.
- `#print axioms` on `LcmCorollary` (`9704539845 ≤ S.commonModulus`) and the rank theorem.
- Read the definition `OddDistinctCoveringSystem` (checked: residues/moduli indexed by `Fin L`, covers ℕ, moduli > 1, odd, injective — this is the standard statement).
- Outcome decides the framing of everything below. If it builds: our bound is a corollary of theirs and we cite it; if it does not: report exactly what fails.

## Milestone 3 — write-up (short note, ~6 pages) ⬜
Outline:
1. Problem and statement of the two certificates.
2. Proof (one page): tower sieve + CRT product count + union bound.
3. Comparison: density (945), BFF condition, Hackmon's weight region, McNew–Setty inclusion–exclusion (wall at 11 486 475), Mian–Siddique (10⁴, Lean), Schroeder (9.7·10⁹, Lean, if reproduced).
4. Formalization: architecture, trust levels (kernel vs `native_decide`), cost per chunk.
5. Tables: first odd failures (675675 / 6891885), sharp cases (12, 80).
6. Where first-order sieve certificates end (11 486 475) and what is needed beyond.

## Milestone 4 — combined sieve + inclusion–exclusion certificate ⬜
- Prove the truncated Bonferroni bound inside the weight region (currently only tested numerically, 0 violations).
- Formalize; it should exclude `6 891 885` and fail first at `11 486 475`.
- Value: closes the gap between our certificate and McNew–Setty's inequality with a proof.

## Milestone 5 — prime-support version of the tower certificate ✅ (2 Nov)
- Our certificate is per-`L`; Hackmon/BFF/Schroeder are per prime support with arbitrary exponents.
- ✅ `towerSum_le_bff`: `T(L) ≤ ∏(p−1)/(p−2) − 1 − Σ 1/(p−2)` (kernel, standard axioms). ✅ `no_covering_3_5_7_11`: no covering with lcm `3^a5^b7^c11^d`, any exponents (Hackmon's four-prime theorem at that prime set, now in Lean).
- ✅ `five_primes_of_odd_covering`: every odd distinct covering has ≥ 5 distinct primes in its lcm (induction on primes in increasing order; standard axioms). This is the ceiling of first-order sieves: BFF value exceeds 1 at `{3,5,7,11,13}`.

## Milestone 6 — beyond first-order sieves 🔄 (first step done, 2 Nov)
- ✅ **Distorted tower certificate** (ours): condition on the tower complement at each prime, then BBMST-distort the mixed classes. Proof in prose (`docs/PROGRESS.md` §1b). Reduces to T(L) at δ = 0. Sound on all 94 known primitive covering numbers < 10⁶ (min η exactly 1).
- ✅ Scan: every odd L ≤ 10¹⁰ with σ(L) ≥ 2L excluded except 20; first survivor **1 527 701 175 = 3³5²7²·11·13·17·19**. 1704 certificates + 220 near-boundary float decisions rechecked in exact arithmetic, 0 failures. ⇒ odd covering ⇒ lcm ≥ 1 527 701 175 (numerical, rests on the prose theorem).
- ✅ Higher moments (k ≤ 4) give no gain; BBMST distortion alone stops at 11 486 475 too.
- ✅ Prime replacement in Lean (any exponents) + shaped enumeration ⇒ `odd_covering_lcm_gt_6891884_kernel`, kernel only (supersedes the 7 CPU-hour native scan).
- ✅ Distorted tower certificate in Lean (`Hybrid/`, `one_le_eta`): weighted counting on ℤ/Q, stage by stage.
- ✅ **`odd_covering_lcm_gt_1527701174`: odd covering ⇒ lcm ≥ 1 527 701 175, kernel only** (1638 certificates, `HybridScan/`).
- ⬜ Push past 1.53·10⁹: exact (non-union-bound) treatment of the first mixed stage {3,5}.
- Only route to new numerical bounds past 11 486 475: prime-by-prime distorted sieve (Hough / BBMST) or Schroeder-style conditional reweighting. Research-level formalization; decide after Milestone 2.

## Side track (parked) 🧪
- `t₉ ≤ 2` search (`9` used twice): `L = 945` UNSAT; nothing promising at small lcm.
