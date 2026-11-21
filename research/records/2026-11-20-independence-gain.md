# Route: independence gain for the first three primes (five-prime wall), 20 Nov 2026

**Target.** Uniform in exponents: no odd covering with lcm $3^a5^b7^c11^d13^f$. Obstructed on 4 Nov 2026: the distorted tower certificate gives $\eta \to 1.0126$ at large exponents.

**New input.** The tower measure on the first three primes is a product measure. For the moduli $3\cdot5^j$ and $3\cdot7^k$ this gives an exact formula inside each residue class mod 3: coverage $1-(1-x)(1-y)$, not $x+y$. There are only two usable classes mod 3, of mass at most $\kappa = g_3(1) < 2/3$ and $1-\kappa$, so the overlap cannot be avoided. Saving over the union bound: $\min\{\kappa G_5G_7,\ (2\kappa-1)\min(G_5,G_7)\}$, which is $2/45$ in the limit.

**Outcome.**
- **Theorem A (proved in prose, [docs/FIVE_PRIMES.md](../../docs/FIVE_PRIMES.md)).** Block $\{3,5,7\} \le 28/45$, then distortion on 11 ($\delta = 2/5$) and 13 ($\delta = 1/2$): total $4099375/4234032 \approx 0.9682 < 1$ for all exponents. With prime replacement (`Replace.lean`): every odd covering has at least six primes in its lcm.
- **Finite scan (numerical, floats).** The same lemma inside the scan (`indep/enh_scan.py`, `indep/enh.py`) excludes 16 of the 20 odd $L \le 10^{10}$ left by the distorted certificate, including $1\,527\,701\,175$. Not excluded: $4\,583\,103\,525$, $5\,547\,967\,425$, $7\,638\,505\,875$, $9\,820\,936\,125$ (values 1.0415, 1.0043, 1.0194, 1.0161). So the scan would give lcm $\ge 4\,583\,103\,525$ once the 19 new certificates (`indep/enh_certs_1e+10.json`) are rechecked exactly.

**Evidence.**
- `indep/verify5.py`: exact fractions; finite-exponent bound below the limit for all exponent vectors in $[1,6]^5$.
- `indep/brute315.py`: exhaustive optimum for $L=315$ is 74 uncovered residues; Lemma 2 gives 74, the union bound 71. CP-SAT on the unrestricted problem also finds 74 (not proved optimal there). For $L = 945$: best found 191, Lemma 2 gives $\ge 188$, union bound 179.

**Status and non-claims.**
- Independent audit: started, cut off by a usage limit, **not completed**. Literature check on "six primes": likewise not completed.
- Not formalised in Lean. `Hybrid/Main.lean` is modular enough (`Pw_cons_cov` takes the bound on the earlier stages as a hypothesis), so the plan is: generalise that lemma to an arbitrary bound, prove the three-prime block lemma for the product weight, then a limit bound in the style of `BFF.lean`.
- Not new relative to Schroeder's unchecked claims ($\omega \ge 7, 8, 9$); it is an independent, short argument.
- Six primes: the same bookkeeping gives about 1.13 for $\{3,\dots,17\}$.

**Continuations (untried or partial).**
1. Full-depth version of the gain for two families: in the limit the forced loss is $\min\{G_5G_7,\ \min(G_5,G_7)/3\} = 1/15$, giving block $\le 3/5$ (needs a proof that no arrangement of the deeper moduli $3^i5^j$, $3^i7^k$ does better).
2. Leafwise reduction at the prime 3: each surviving residue $\ell$ mod $3^a$ sees a system on the other primes in which a modulus $m$ occurs once plus once for every $3^im$ whose class contains $\ell$ (on average at most once more). Pure prime powers among these are removed multiplicatively. In the equalised arrangement this gives values well below 1 for five and six primes, but the worst case over arrangements is not controlled yet.
3. Lean formalisation as above.
