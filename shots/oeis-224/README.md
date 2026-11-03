# OEIS A000224: a primality test via the number of squares mod n (partial result)

*Ryan Wu and Claude · November 2026 · Conjecture **open**; the cases below are proved.*

**Conjecture** (T. Ordowski, 2017; `FormalConjectures/OEIS/224.lean`). Let $a(n)$ be the number of squares mod $n$. For $n > 1$,
$$n \text{ is an odd prime} \iff n^2 \equiv 1 \pmod{a(n)\,(a(n)-1)}.$$

| # | Claim | Disposition |
|---|---|---|
| 1 | ($\Rightarrow$) For an odd prime $p$, $a(p) = \tfrac{p+1}{2}$ and $a(p)(a(p)-1) = \tfrac{p^2-1}{4} \mid p^2 - 1$. | proved |
| 2 | $n$ even: $a(n) \ge 2$, so $a(n)(a(n)-1)$ is even and nonzero, while $n^2-1$ is odd. | proved |
| 3 | $n = p^e$, $e \ge 2$ even: $a(p^e) = 1 + \tfrac{p-1}{2}\sum_{j < e/2} p^{e-2j-1} \equiv 1 \pmod p$, so $p \mid a - 1$ but $p \nmid n^2 - 1$. | proved |
| 4 | $n = p^e$, $e \ge 3$ odd: $a = 1 + t$ with $t = \tfrac{p^{e+1}-1}{2(p+1)}$. If $n^2 - 1 = k\,t(t+1)$ then reducing mod $p$ gives $t \equiv -\tfrac12$, $t+1 \equiv \tfrac12$, hence $k \equiv 4 \pmod p$; size gives $5 \le k \le 7$ for $p = 3$ and $k = 5$ for $p \ge 5$. Only $p = 3$, $k = 7$ survives, i.e. $9^e - 126\cdot 3^e - 15 = 0$, which has no solution ($x^2 - 126x - 15$ has discriminant $15936$, not a square). | proved |
| 5 | $n = pq$, $3 \le p < q$ primes: $A = \tfrac{(p+1)(q+1)}{4}$, $n^2 - 1 = k A(A-1)$ forces $k \le 15$ and then $(1+\tfrac1p)^4 > \tfrac{16}{15} - \tfrac{16}{15\cdot 225}$, so $p \le 61$; for each $(p, k)$ the equation is a quadratic in $q$ with no prime root (`pq_case.py`, exact integer arithmetic, plus a brute-force cross-check for $p < 400$, $q < 4000$). | proved (finite computation) |
| 6 | The conjecture holds for all $n \le 3\cdot 10^8$ (`scan.c`, exact square-count formula validated against brute force for $n < 3000$). | numerical |

**What remains.** Composite odd $n$ with at least two distinct prime factors other than the squarefree $pq$ case (e.g. $p^2 q$, $pqr$). With $\omega(n)$ primes the quotient $k$ is roughly $4^{\omega}$, so the size argument no longer bounds anything; the condition resembles Lehmer's totient problem, and a full proof would need a new idea.
