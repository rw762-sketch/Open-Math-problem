# Route: uniform-in-exponents contradiction for a fixed prime support (bounded attempt, 4 Nov 2026)

**Target.** For P = {3,5,7,11,13}, prove no odd covering has lcm supported on P (any exponents), i.e. omega(lcm) >= 6, by making the distorted tower certificate eta < 1 uniformly in exponents.

**Success criterion.** A stage-wise bound with eta_inf(P) < 1. **No-go criterion.** Every lossy step shown tight or inherent.

**Done.**
1. Exact worst case (CP-SAT, `exact35/mix35.py`) of the first mixed stage {3,5} under the tower measure equals the union bound at (3^3,5^2), (3^4,5^2), (3^3,5^3): 78/266, ratio 0.3081 = G_5 G_3 (40/41 * 6/19), 0.3062 = (13/14)(31/94). Numerical, optimal.
2. Stage decomposition at large exponents (3^14, 5^9, 7^7, 11^6, 13^6; best order 3,7,5,11,13; deltas on a 1/200 grid): eta = 1.0119; G_p = 1, 0.2, 1/3, 1/9, 1/11 = 1/(p-2) (the exponent-infinity limit); stage terms 0, 0.125, 0.5, 0.182, 0.205.

**Obstruction (precise).** As e_3 -> infinity, G_3 = sum_v min(3^{e-v}, u)/u -> 1/(3-2) = 1: under the tower measure a mixed class m*3^v costs the full nu(m), summed over v. The first mixed stage is exactly tight (step 1), so the loss is not in the union bound there; it is the tower measure itself giving the 3-adic tree too much room. This mirrors the "power branch" construction of Harrington–Sun–Wong (arXiv 2104.00602, Fig. 5–7): with powers 3^2, 3^3, ..., 3^{q-1} one residue class mod 3 can be absorbed with distinct moduli.

**Outcome.** Inconclusive for the target; route (i) "exact first mixed stage" is **obstructed with evidence**. Strongest surviving statement: within this certificate family (tower measure + BBMST distortion), eta_inf({3,...,13}) ~ 1.012 and the first-stage union bound is not the slack.

**Continuations.**
- Untried: a non-uniform (distorted) measure on the 3-tower itself, i.e. down-weighting deep 3-adic residues, so that G_3 < 1 in the limit. Concrete next action: replace uniform weight on A_3 by weights decaying in v_3-depth and re-derive g(v).
- Untried: use the HSW power-branch structure as an extremal configuration to test any proposed measure (a measure that fails on it cannot work).
