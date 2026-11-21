# Route: sharper bound for one distorted stage (exploratory, numerical), 21 Nov 2026

**Target.** Lower the certificate value for six primes and for the four odd $L \le 10^{10}$ left by the independence-gain scan.

**Idea.** For a stage with cap $\delta$, let $S = \sum_k c_k 1[E_k] \ge \alpha$ be the usual upper bound for the covered fraction $\alpha \le 1$ of a fibre, with $P(E_k) \le \nu(n_k)$ and $P(E_k \cap E_l) \le \nu(\operatorname{lcm})$. Put $h = 1[\alpha > \delta]$ and $\theta = P(h)$. Then
$$E[(\alpha-\delta)^+] = E[h\alpha] - \delta\theta, \qquad E[h\alpha] \le \theta, \qquad E[hS_g] \le \sum_{k \in g} c_k \min(\nu(n_k), \theta), \qquad E[hS_g] \le \sqrt{\theta\,E[S_g^2]}$$
for any group $g$ of stage classes. So the stage costs at most
$$\frac{1}{1-\delta}\max_{0 \le \theta \le 1}\Bigl[\min\bigl(\theta, \textstyle\sum_g T_g(\theta)\bigr) - \delta\theta\Bigr],$$
with $T_g$ the better of the two bounds. Taking one group and Cauchy–Schwarz gives back the second-moment bound $M_2/(4\delta(1-\delta))$; the first bound is exact for nested classes (chains $3^i p^j$), and the cap $E[h\alpha] \le \theta$ makes large $\delta$ usable on the last stage.

**Outcome (floats, $\theta$ maximised on a grid, not rechecked exactly — not a certificate).** `v3/v3.py`, `v3/run6.py`, `v3/hard4.py`.

| case | before | with this bound |
|---|---|---|
| five primes, exponents $(6,4,3,3,3)$ | 0.968 (limit, with block lemma) | 0.953 |
| six primes, exponents $(6,3,3,2,2,2)$ | about 1.13 | 1.087 |
| $5\,547\,967\,425$ | 1.0043 | 0.9965 |
| $9\,820\,936\,125$ | 1.0161 | 1.0103 |
| $7\,638\,505\,875$ | 1.0194 | 1.0147 |
| $4\,583\,103\,525$ | 1.0415 | 1.0378 |

Six primes and three of the four $L$ are still not excluded. Only the increasing prime order was tried.

**Untried continuations.**
1. Product base measure: for convex cost the worst arrangement is nested in every coordinate, so the stage cost is at most $E[(G_p(\prod_q(1+d_q)-1)-\delta)^+]/(1-\delta)$ with independent depths $d_q$, $P(d_q \ge v) = g_q(v)$. Applies to the first distorted stage only.
2. Higher moments (Hölder with exponent 3 or 4) for the non-chain classes.
3. Leafwise scheme at the prime 3 (see the 20 Nov record).

**Assessment.** Each of these moves the count of primes by one at best. None of them is a route to the conjecture, which needs an argument uniform in the number of primes; the only known one (BBMST) covers square-free moduli, and what blocks it otherwise is the powers of the small primes.
