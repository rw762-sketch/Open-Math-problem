# Route: lower bounds on tau_p (HSW square-free repeated-prime variant), 4 Nov 2026

**Target.** tau_p >= 3 (HSW arXiv 2104.00602, Question 1.5), predicted by the Erdős–Selfridge conjecture via HSW Thm 3.2.

**Attempt 1 (own certificate), obstructed.** The distorted tower certificate on square-free supports, with the repeated prime's pure stage removing 2 residues, fails calibration: eta = 0.671 / 1.020 / 1.179 / 1.232 for primes <= 1e2 / 1e3 / 1e4 / 1e5. The best delta schedule gives 1.197. It cannot reproduce BBMST's square-free theorem without their LP small-prime measure and the large-prime termination theorem (arXiv 1811.03547). Scripts: `shots/tau-p/tau.py`, `sched.py`.

**Attempt 2 (reduction), succeeded.** Combine the two papers:
- HSW Thm 3.2 construction: from p used twice, with p^2 not dividing any modulus, build an odd covering. The new moduli are p^{i+1}, p^i q, and p^{i+1} times old moduli.
- BBMST square-free paper, end of §5: square-freeness is needed only on the 73-smooth part.

For p >= 79 and q > 73, the combination gives a contradiction. **Proposition (proved, conditional only on the two cited results as stated by their authors):** tau_p >= 3 for all primes p >= 79. More strongly, no odd covering exists with p used exactly twice, p^2 dividing no modulus, and every modulus square-free at primes <= 73.

**Check.** `shots/tau-p/hsw_construct.py` brute-forces the construction on greedy toy C0 (p = 3, 5, 7). The output covers and has distinct moduli. It also confirms the corrected index ranges (HSW's proof has a typo).

**Non-claims and limits.**
- p <= 73 is not covered.
- tau_p >= 4 is not covered.
- t_p (non-square-free) is not covered.
- BBMST's numerics were not re-derived.
- Novelty is checked only within HSW, Bispels et al. 2025, BBMST, one web search and one alphaXiv discovery query (see README).

**Continuations.**
- Lower the 73 in BBMST's remark; that lowers our 79 directly. This needs BBMST's LP for 3, 5, 7, 11 with prime powers: hard.
- Check papers citing HSW for a prior statement.
