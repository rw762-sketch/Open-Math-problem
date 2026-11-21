# Dai–Li–Li–Yi: On the moduli of distinct covering systems

*Summary [DLLY26] · arXiv 2611.15110, 11 Nov 2026 · read 21 Nov 2026: introduction, §2.2, §2.5 and §4 in full text; §3, §5, §6 by headings only. Nothing here was re-derived or machine-checked by us.*

**TL;DR.** For every distinct covering with odd moduli and lcm $Q$: $45 \mid Q$ (Thm 1.1) and some modulus is $\le 9$ (Thm 1.2). For arbitrary distinct moduli the minimum modulus is $< 14000$; for square-free moduli it is $\le 7$ (Thm 1.3). All of these hold for every set of primes.

**Method.** BBMST distortion plus:
- *Convex comparison* (Lemma 2.5, Thm 2.6). For increasing convex $\Phi$ and $b_j \ge 0$: $E_\mu \Phi(\sum_j b_j 1[x \in C_j]) \le E\,\Phi(\sum_j b_j 1[m_j \mid R])$, where $R = \prod_q q^{T_q}$ with independent exponents, $P(T_q \ge e) = \gamma_q/q^e$. Lemma 2.5 is the Bernoulli case of the Lorentz–Tchen rearrangement inequality (nested events are the worst case). The theorem holds for the distorted measure $\mu$.
- *Reduction modulo 3 and averaging* (§4.1, Lemma 2.7), used when $9 \nmid Q$: on the two residue classes not covered by the modulus 3, the classes with 3-free moduli are shared, and each modulus $3m$ gives an extra class of modulus $m$ on one branch only.
- *Conditioning on the complement of the classes with moduli $3^e$* (Lemma 2.12): a class modulo $3^e$ then has probability at most $2/3^e$.

**Numbers.** Case $9 \nmid Q$: averaged distortion sum $\le 0.99944$. Case $5 \nmid Q$: $\le 0.83649$.

**Relation to this repo.**
- Their Lemma 2.5 is the general form of the nested ("comonotone") bound in our [21 Nov record](../../research/records/2026-11-21-sharper-stage-bound.md), and Thm 2.6 already extends it to the distorted measure, which that record listed as untried. The stage bound there is superseded.
- §4.1 is the restriction "prime powers act as repeated moduli", one level deep.
- Not found in the parts read: the exact product formula for two families inside one residue class (Lemmas 1–2 of [FIVE_PRIMES.md](../FIVE_PRIMES.md)), which is not a convexity argument. Their Remark 1.4 mentions tracking intersections of residue classes at small primes as a refinement.
- Neither result implies the other. Theirs holds for all supports ($45 \mid Q$, a modulus $\le 9$); ours excludes supports with at most five primes.
- The case left open for the conjecture is $45 \mid Q$. A rough extrapolation of their §4.3 computation with the prime 5 added gives about $1.5$ (our estimate, not computed).
