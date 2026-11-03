# Erdős #273: coverings with moduli p − 1

*Progress note · Ryan Wu and Claude · November 2026 · Problem remains **open**. Every claim carries a disposition: proved / numerical / unchecked.*

**Problem** ([erdosproblems.com/273](https://www.erdosproblems.com/273)). Is there a covering system with distinct moduli, all of the form $p-1$ for primes $p \ge 5$? Selfridge found one using divisors of 360 when $p = 3$ is allowed (so modulus 2 is available); with $p \ge 5$ nothing is known.

## Results

| # | Claim | Disposition |
|---|---|---|
| 1 | Density: a covering with moduli $d \mid L$ needs $\sum_{d \mid L,\ d \ge 4,\ d+1 \text{ prime}} 1/d \ge 1$. The smallest such $L$ is $55\,440$; there are $10\,136$ such $L \le 10^8$. | proved (trivial) / numerical count (`dens273d.c`, double precision) |
| 2 | The distorted tower certificate of `docs/PROGRESS.md` §1b remains valid when every sum is restricted to the allowed moduli (the proof bounds sums over *used* moduli by sums over a superset). The only pure prime-power moduli are $4, 16, 256, 65536$ (Fermat primes), so only the prime 2 has a nontrivial tower. | proved in prose; Lean pending |
| 3 | Sanity: with modulus 2 allowed ($p \ge 3$), the certificate does **not** exclude the known covering numbers 360, 720, 1080, 2520, 5040 ($\eta = 1.21$–$1.56$). | numerical |
| 4 | Every $L \le 10^8$ passing the density test is excluded by the certificate except $12$; the smallest survivor is $21\,621\,600 = 2^5 3^3 5^2 \cdot 7 \cdot 11 \cdot 13$ ($\eta = 1.0012$, all prime orders, δ grid $1/2000$). | numerical (`eta273.c`, `eta273p.c`); the 50 certificates with $\eta \ge 0.98$ rechecked in exact arithmetic (`exact273.py`), worst $0.999728$ |
| 5 | **Consequence: any covering for #273 has lcm of moduli $\ge 21\,621\,600$.** | numerical, rests on 2 |
| 6 | Greedy construction at $L = 43\,243\,200$ (219 allowed moduli, $\sum 1/d = 1.187$) leaves 8% uncovered. | numerical (`greedy.py`) |

## What remains open
- Formalize claim 2 in Lean (the closed forms of the main development are multiplicative; with restricted moduli the sums must be computed directly) and turn claim 5 into a kernel-checked theorem.
- Push past $21\,621\,600$ (the same certificate barrier phenomenon as for #7), or construct a covering: the density sum grows only like $\log\log L$ (about $1.27$ at $L \approx 8\cdot10^9$), so a construction, if one exists, needs a large structured $L$.
