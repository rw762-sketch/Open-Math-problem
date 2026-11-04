# A lower bound for $\tau_p$: $\tau_p \ge 3$ for every prime $p \ge 79$

*Ryan Wu and Claude · 4 November 2026 · short proof assembled from two published results; novelty only checked within a limited search (see below).*

## The quantity

Harrington–Sun–Wong (HSW, arXiv 2104.00602, *Discrete Math.* 345 (2022), Question 1.5) define $\tau_p$ as the smallest $t \ge 0$ such that there is a covering system of $\mathbb Z$ in which $p$ appears as a modulus exactly $t$ times and all other moduli are odd, distinct, square-free and $> 1$.

The known bounds are:
- $\tau_p \ge 2$ for every odd prime $p$. If $p$ is used 0 or 1 times, the system is a square-free odd covering, and Balister–Bollobás–Morris–Sahasrabudhe–Tiba (BBMST, arXiv 1901.11465, Thm 1.1) rule that out.
- $\tau_7 \le 6$, and $\tau_p \le p-1$ for all $p \ge 7$ (HSW Thm 3.4 and Cor. 5.2).

HSW Theorem 3.2 says that $\tau_p \le 2$ for some $p$ implies an odd covering exists. So the Erdős–Selfridge conjecture predicts $\tau_p \ge 3$ for all $p$. As far as we found, no lower bound beyond $\tau_p \ge 2$ appears in HSW or in the 2025 follow-up (Bispels et al., arXiv 2507.16135), which proves only upper bounds.

## Result

**Proposition.** Let $p \ge 79$ be prime. Suppose a finite system of congruences satisfies all of the following:
- it covers $\mathbb Z$;
- every modulus is odd and $> 1$;
- the moduli are distinct, except that $p$ is used exactly twice;
- no modulus is divisible by $p^2$;
- no modulus is divisible by $\ell^2$ for any prime $\ell \le 73$.

No such system exists. In particular, $\tau_p \ge 3$ for every prime $p \ge 79$.

**Proof.**
1. *Normalise the two classes mod $p$.* By HSW Lemma 3.1 we may assume the two congruences with modulus $p$ are $0 \bmod p$ and $1 \bmod p$.
2. *Build an odd covering.* Run the construction in the proof of HSW Theorem 3.2, with an auxiliary prime $q$ satisfying $q > 73$ and $q \nmid p\,m$, where $m$ is the lcm of the other moduli. The construction produces an odd covering with distinct moduli. Its moduli are of four kinds:
   - $p^{i+1}$, for $0 \le i \le q-2$;
   - $p^i q$, for $0 \le i \le q-1$;
   - the moduli $m_j$ of the original system that are coprime to $p$;
   - $p^{i+1} m_{\xi,j}$, where $p\,m_{\xi,j}$ runs over the original moduli that are multiples of $p$ other than $p$ itself.

   The construction needs only "no modulus divisible by $p^2$". It does not use square-freeness at any other prime.
3. *Check the small primes.* A prime $\ell \le 73$ can only enter through $m_j$ or $m_{\xi,j}$, because $p, q > 73$. By hypothesis it divides those to the first power at most.
4. *Apply BBMST.* At the end of §5, BBMST note that their proof uses square-freeness only on the 73-smooth part. Precisely: if the moduli are distinct and every prime $\ell \le 73$ occurs in each modulus to power at most 1, then some modulus is even. The covering from step 2 meets these conditions and has no even modulus, a contradiction. ∎

The only new step is matching the two papers: the moduli $p^{i}$ that HSW's power branch introduces are harmless for BBMST exactly when $p > 73$. HSW (2021/22) do not cite BBMST.

**Dependencies, as stated by their authors:**
- HSW Lemma 3.1 and Theorem 3.2.
- BBMST's strengthened statement, given as a remark at the end of §5. It rests on their Lemmas 5.3–5.4 together with the large-prime analysis of their Inventiones paper (arXiv 1811.03547), which does not assume square-free moduli.

We have not re-derived the BBMST numerics. Their final margin is thin: $f_{21} \le 138.874$ against a threshold of $138.877$.

**Machine check of the construction's mechanics.** `hsw_construct.py` builds toy systems $C_0$ by greedy search. Each covers $\mathbb Z$, uses $p$ twice and has no modulus divisible by $p^2$. The script then applies the Theorem 3.2 construction and brute-forces the result over its lcm.
- Cases: $p = 3, 5, 7$, with lcm up to $2.6 \cdot 10^6$.
- Outcome: the output always covers and always has distinct moduli.

This checks our reading of the index ranges. HSW's proof has a typo, "$1 \le i \le q-2,\ 2 \le \xi \le p-2$"; the correct ranges are $0 \le i \le q-2$ and $2 \le \xi \le p-1$.

## What does not extend

- **$p \le 73$.** The power branch creates moduli $p^2, p^3, \dots$, and BBMST say nothing about non-square-free 73-smooth parts. So $\tau_3, \dots, \tau_{73} \ge 3$ stays open. Lowering BBMST's 73 would lower our 79 to the next prime after the new cutoff.
- **Three or more uses.** The power-branch trick absorbs exactly one extra class mod $p$ at each depth, so it says nothing about $\tau_p \ge 4$.
- **$t_p$ (non-square-free version).** The same argument gives an odd covering, but one that is not square-free at small primes, so BBMST do not apply.
- **Our own certificate (negative calibration, `tau.py`, `sched.py`).** We first tried to prove $\tau_p \ge 3$ with our distorted tower certificate, adapting BBMST's sieve with the repeated prime's pure stage removing 2 residues. On plain square-free supports $3..N$ the certificate gives:

  | $N$ | $\eta$ |
  |---|---|
  | 100 | 0.671 |
  | 1000 | 1.020 |
  | $10^4$ | 1.179 |
  | $10^5$ | 1.232 |

  A schedule $\delta(q) = \min(0.5,\ a/(\log q)^b)$ gives at best 1.197. So without BBMST's LP-optimised small-prime measure and the large-prime termination theorem from 1811.03547, the certificate cannot even reproduce the square-free theorem. That route was abandoned for the reduction above.

## Literature search (4 Nov 2026, bounded)

- Read in full: HSW, Bispels et al. 2025 and BBMST square-free (alphaXiv full text).
- Searched:
  - web search for the repeated-prime square-free lower-bound question;
  - alphaXiv discovery for "odd covering / square-free / covering system".

  Hits included 2603.26043, 2610.34541, 2605.18644 and 2607.25628. None states a lower bound on $\tau_p$.
- Not checked: the papers that cite HSW, and the erdosproblems.com forum (comments suspended). This is not a global novelty claim.
