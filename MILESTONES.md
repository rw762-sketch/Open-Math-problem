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

## Milestone 1 — close out the current Lean results ✅/🔄
- ✅ `one_le_phiSum`, `one_le_towerSum`, decidable certificates (kernel, standard axioms).
- ✅ `odd_covering_lcm_gt_675674`, `odd_covering_lcm_gt_1000000` (`native_decide`).
- 🔄 `odd_covering_lcm_gt_100000` kernel-only (ScanK, 150/165 chunks).
- 🔄 `odd_covering_lcm_gt_6891884` (ScanT, 100/173 chunks).
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

## Milestone 5 — prime-support version of the tower certificate ⬜
- Our certificate is per-`L`; Hackmon/BFF/Schroeder are per prime support with arbitrary exponents.
- Take `e_p → ∞` in `u_p` (`u_p/p^{e_p} → (p−2)/(p−1)`) and prove the monotonicity needed to get a statement "no odd covering supported on `{3,5,7,11}` for any exponents" from one finite check. Formalize. This recovers Hackmon's Four-Prime Theorem in Lean (he has none).

## Milestone 6 — beyond first-order sieves 🧪
- Only route to new numerical bounds past 11 486 475: prime-by-prime distorted sieve (Hough / BBMST) or Schroeder-style conditional reweighting. Research-level formalization; decide after Milestone 2.

## Side track (parked) 🧪
- `t₉ ≤ 2` search (`9` used twice): `L = 945` UNSAT; nothing promising at small lcm.
