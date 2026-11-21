# Benchmark of methods on fixed cases, 21 Nov 2026

**What.** One code base ([bench/](../../bench/README.md)) that scores the union bound, the BBMST second moment, our block lemma, and the comparison bound of Dai–Li–Li–Yi on the same cases: first $k$ odd primes with all exponents, the two cases proved in that paper, and the open case.

**Outcome (floats).**
- The paper's totals $0.83649$ ($5 \nmid Q$) and $0.99944$ ($9 \nmid Q$) are reproduced to nine digits with the paper's parameters.
- Open case ($45 \mid Q$, all primes, all exponents): about $2.07$ with the comparison bound and our caps. No method is below 1.
- First $k$ odd primes with the comparison bound: $0.785$ ($k=5$), $0.895$ ($k=6$), $1.003$ ($k=7$). The values for $k = 5, 6, 7$ are confirmed as exact fractions by independent code.
- Square-free odd moduli: $0.512$.

**Consequences.**
- Given Theorem 2.6 of the paper, no odd covering has an lcm with at most six prime factors. This supersedes Theorem A of [FIVE_PRIMES.md](../../docs/FIVE_PRIMES.md) as a result, though Theorem A's proof is independent of the paper.
- The method misses the conjecture by a factor of about two, so the gap is not a matter of tuning.

**Non-claims.** No directed rounding. Caps are not optimal (2% worse than the paper's in the case where both exist). Theorem 2.6 was read, not re-derived or formalised.
