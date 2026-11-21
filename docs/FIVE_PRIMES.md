# No odd covering has only the primes 3, 5, 7, 11, 13 in its lcm

*Ryan Wu and Claude · 20 November 2026 · Disposition: **proved in prose** (this file), exact arithmetic checked by `indep/verify5.py`; **not yet formalised in Lean**. Independent of Schroeder's unchecked rank papers, which claim more ($\omega \ge 9$).*

> **Theorem A.** For all exponents $a,b,c,d,f \ge 0$ there is no covering system with distinct moduli $> 1$ whose lcm is $3^a5^b7^c11^d13^f$.
>
> **Corollary.** The lcm of every covering system with distinct odd moduli $>1$ has at least six distinct prime factors.

The corollary follows from Theorem A by prime replacement (`Replace.lean`, kernel-checked: a covering with lcm $\prod q_i^{e_i}$, $q_1 < q_2 < \dots$ odd primes, gives one with lcm $\prod p_i^{e_i}$ for the first odd primes $p_i \le q_i$) together with `five_primes_of_odd_covering` ($\omega \ge 5$).

The proof is the distorted tower certificate of [PROGRESS.md §1b](PROGRESS.md) with one new ingredient, Lemma 2 below. On its own that certificate gives $1.0126 > 1$ for this support at large exponents (the wall recorded on 4 Nov 2026). Lemma 2 lowers the bound for the first three primes from $2/3$ to $28/45$, and the total becomes $4099375/4234032 \approx 0.9682$.

## 0. Setup

Let $L = 3^a5^b7^c11^d13^f$. If a covering with distinct moduli has lcm $L$ and $L \mid L'$, its classes are classes modulo divisors of $L'$. So we may assume every exponent is $\ge 1$, and it suffices to prove:

> for every choice of one residue class $A_m$ for each divisor $m > 1$ of $L$, the classes do not cover $\mathbb{Z}/L$.

Fix such a choice. For $p \mid L$ with exponent $e$ write $T_p = \mathbb{Z}/p^{e}$, so $\mathbb{Z}/L = \prod_p T_p$ by CRT, and every class $A_m$ is a box $\prod_p N_p(m)$, where $N_p(m)$ is a class modulo $p^{v_p(m)}$ in $T_p$ (all of $T_p$ if $p \nmid m$).

**Tower constants.** Let $U_p \subseteq T_p$ be the complement of the classes of the *pure* moduli $p, p^2, \dots, p^e$. Then $|U_p| \ge u_p := p^e - (1 + p + \dots + p^{e-1}) \ge 1$. For $1 \le j \le e$ put
$$g_p(j) = \frac{\min(p^{e-j}, u_p)}{u_p}, \qquad G_p = \sum_{j=1}^{e} g_p(j), \qquad H_p = \sum_{j=1}^{e} (2j+1)\,g_p(j).$$
Let $\pi_p$ be the uniform probability measure on $U_p$. For every class $N$ modulo $p^j$,
$$\pi_p(N) = \frac{|N \cap U_p|}{|U_p|} \le \frac{\min(p^{e-j}, |U_p|)}{|U_p|} \le g_p(j), \tag{1}$$
because $s \mapsto \min(t,s)/s$ is non-increasing. Since $u_p > p^e\frac{p-2}{p-1}$,
$$g_p(j) < \hat g_p(j) := \frac{p-1}{p-2}\,p^{-j}, \qquad G_p < \hat G_p := \frac{1}{p-2}, \qquad H_p < \hat H_p := \frac{3p-1}{(p-1)(p-2)}. \tag{2}$$
(The last two are the sums of $\hat g_p(j)$ and $(2j+1)\hat g_p(j)$ over all $j \ge 1$.) Also $g_3(1) = 3^{a-1}/u_3 = \frac{2\cdot 3^{a-1}}{3^a+1} \in [\tfrac12, \tfrac23)$.

A modulus is **mixed** if it has at least two prime factors. A point of $\mathbb{Z}/L$ outside $U := \prod_p U_p$ is covered by a pure class, and a point of $U$ can only be covered by a mixed class.

## 1. The measure

Order the primes $3, 5, 7, 11, 13$ and write $Q_i$ for the product of the first $i$ prime powers. A mixed modulus belongs to *stage* $i$ if its largest prime is the $i$-th one. Let $C_i$ be the union of the classes of the mixed moduli of stage $i$ ($i = 2,\dots,5$).

Take caps $\delta_2 = \delta_3 = 0$, $\delta_4 = \tfrac25$, $\delta_5 = \tfrac12$, and let $P_0, \dots, P_5$ be the measures of PROGRESS.md §1b: $P_i$ is a probability measure on $\mathbb{Z}/Q_i$, obtained from $P_{i-1}$ by (a) spreading each point mass uniformly over $U_{p_i}$ in the new coordinate, then (b) applying the Balister–Bollobás–Morris–Sahasrabudhe–Tiba distortion with cap $\delta_i$ on the fibres, with respect to the mixed classes of stage $i$. We use four facts proved there (and kernel-checked in `Hybrid/Main.lean`):

- **(F1)** $P_j(S) = P_i(S)$ for $j \ge i$ whenever $S$ depends only on the first $i$ coordinates.
- **(F2)** $P_5$ gives measure $0$ to every pure class.
- **(F3)** For $m \mid Q_i$ and any class $b + m\mathbb{Z}$: $P_i(b + m\mathbb{Z}) \le \nu(m)$, where $\nu$ is multiplicative with $\nu(p_k^v) = g_{p_k}(v)/(1-\delta_k)$.
- **(F4)** $P_i(C_i) \le M^{(2)}_i / (4\delta_i(1-\delta_i))$ when $\delta_i > 0$, with
$$M^{(2)}_i = G_{p_i}^2 \sum_{\substack{m_1, m_2 \mid Q_{i-1}\\ m_1, m_2 > 1}} \nu(\operatorname{lcm}(m_1, m_2)).$$

With $\delta_i = 0$ step (b) changes nothing. Hence $P_3$ is the **product measure** $\pi_3 \otimes \pi_5 \otimes \pi_7$ on $U_3 \times U_5 \times U_7$. By (F1), (F2),
$$P_5(\text{covered}) \le P_3(C_2 \cup C_3) + P_4(C_4) + P_5(C_5). \tag{3}$$
We bound the three terms and show the sum is $< 1$.

## 2. The first three primes

$C_2 \cup C_3$ is the union of the classes $A_m$ over the mixed $m \mid 3^a5^b7^c$. By (1) and the product structure, $P_3(A_m) \le c(m) := \prod_{p} g_p(v_p(m))$ (empty factors are $1$).

> **Lemma 1 (two events in one cell).** Let $w_\rho \ge 0$ ($\rho$ in a finite set) with $\sum_\rho w_\rho = 1$ and $w_\rho \le \kappa$. Let $x_\rho, y_\rho \in [0,1]$ with $\sum_\rho x_\rho \le \alpha \le 1$ and $\sum_\rho y_\rho \le \beta \le 1$. Then
> $$\sum_\rho w_\rho\,(x_\rho + y_\rho - x_\rho y_\rho) \ \le\ \Gamma(\kappa,\alpha,\beta) := \max\bigl\{\kappa(\alpha+\beta-\alpha\beta),\ \kappa\max(\alpha,\beta) + (1-\kappa)\min(\alpha,\beta)\bigr\}.$$

*Proof.* Write the left side as $\sum_\rho x_\rho\, w_\rho(1-y_\rho) + \sum_\rho w_\rho y_\rho$. The coefficients $w_\rho(1-y_\rho)$ are $\ge 0$ and $\sum x_\rho \le \alpha$, so the first sum is at most $\alpha\, w_{\sigma}(1-y_{\sigma})$ for an index $\sigma$ maximising $w_\rho(1-y_\rho)$. The left side is therefore at most
$$\alpha w_\sigma + \sum_\rho y_\rho\, w_\rho\,(1 - \alpha[\rho=\sigma]) \ \le\ \alpha w_\sigma + \beta \max\bigl(w_\sigma(1-\alpha),\ \max_{\rho\ne\sigma} w_\rho\bigr).$$
If the maximum is $w_\sigma(1-\alpha)$ we get $w_\sigma(\alpha+\beta-\alpha\beta) \le \kappa(\alpha+\beta-\alpha\beta)$. Otherwise we get $\alpha w_\sigma + \beta w_\tau$ with $\tau \ne \sigma$, $w_\sigma + w_\tau \le 1$ and both $\le \kappa$; if $\alpha \ge \beta$ this is $\le \beta + (\alpha-\beta)w_\sigma \le \kappa\alpha + (1-\kappa)\beta$, and symmetrically if $\alpha < \beta$. $\square$

> **Lemma 2 (block bound).** With $\kappa = g_3(1)$, $\alpha = G_5$, $\beta = G_7$,
> $$P_3(C_2 \cup C_3) \ \le\ \Bigl[(1+G_3)(1+G_5)(1+G_7) - 1 - G_3 - G_5 - G_7 - \kappa(\alpha+\beta)\Bigr] + \Gamma(\kappa,\alpha,\beta).$$

*Proof.* Let $\mathcal F = \{3\cdot 5^j : 1 \le j \le b\} \cup \{3\cdot 7^k : 1 \le k \le c\}$. For a residue $\rho$ modulo 3 let $X_\rho \subseteq U_5$ be the union of the sets $N_5(3\cdot5^j) \cap U_5$ over those $j$ with $N_3(3\cdot 5^j) = \rho$, and define $Y_\rho \subseteq U_7$ in the same way from the moduli $3\cdot7^k$. A point $(\ell, y, z) \in U_3\times U_5\times U_7$ lies in $\bigcup_{m\in\mathcal F} A_m$ exactly when $y \in X_{\rho}$ or $z \in Y_{\rho}$ for $\rho = \ell \bmod 3$. Since $P_3$ is a product measure,
$$P_3\Bigl(\bigcup_{m \in \mathcal F} A_m\Bigr) = \sum_{\rho} w_\rho\,\bigl(1 - (1-x_\rho)(1-y_\rho)\bigr), \qquad w_\rho = \pi_3(\rho),\ x_\rho = \pi_5(X_\rho),\ y_\rho = \pi_7(Y_\rho).$$
Here $w_\rho \le g_3(1) = \kappa$ by (1). Each $j$ contributes to exactly one $X_\rho$, so $\sum_\rho x_\rho \le \sum_j g_5(j) = G_5$, and likewise $\sum_\rho y_\rho \le G_7$; both are $< 1$ by (2). Lemma 1 gives $P_3(\bigcup_{\mathcal F} A_m) \le \Gamma(\kappa, G_5, G_7)$. For the remaining mixed $m \mid 3^a5^b7^c$ use the union bound $\sum_{m \notin \mathcal F} c(m)$. The sum of $c(m)$ over all mixed $m$ is $(1+G_3)(1+G_5)(1+G_7) - 1 - G_3 - G_5 - G_7$, and over $\mathcal F$ it is $g_3(1)(G_5 + G_7)$. $\square$

*Remark.* Without Lemma 1 the bracket plus $\kappa(\alpha+\beta)$ is the plain union bound. The saving $\kappa(\alpha+\beta) - \Gamma = \min\{\kappa\alpha\beta,\ (2\kappa-1)\min(\alpha,\beta)\}$ is forced: the two moduli $3\cdot5^j$ and $3\cdot7^k$ either sit in the same class mod 3, where their classes mod $5^j$ and mod $7^k$ are independent and overlap, or one of them sits in the lighter class. Exact search confirms it is sharp: for $L = 315$ the true minimum number of uncovered residues is $74$, the bound of Lemma 2 gives $74$, and the union bound gives only $71$ (`indep/brute315.py`).

**Passing to the limit constants.** The bracket in Lemma 2 equals $\sum_{m \text{ mixed},\, m\notin\mathcal F} c(m)$, a sum of products of the $g_p(j)$ with non-negative coefficients, so by (2) it is at most its value with $\hat g$ and all $j \ge 1$, namely $2\cdot\tfrac43\cdot\tfrac65 - 1 - 1 - \tfrac13 - \tfrac15 - \tfrac23\bigl(\tfrac13+\tfrac15\bigr) = \tfrac{14}{45}$. $\Gamma$ is non-decreasing in each argument on $[0,1]^3$, so $\Gamma(\kappa, G_5, G_7) \le \Gamma(\tfrac23, \tfrac13, \tfrac15) = \max\{\tfrac{14}{45}, \tfrac{13}{45}\} = \tfrac{14}{45}$. Hence
$$P_3(C_2 \cup C_3) \le \tfrac{28}{45}. \tag{4}$$

## 3. The primes 11 and 13

By (F4) with $\delta_4 = \tfrac25$ and $\delta_5 = \tfrac12$,
$$P_4(C_4) \le \frac{G_{11}^2\,\Sigma_3}{4\cdot\frac25\cdot\frac35}, \qquad P_5(C_5) \le G_{13}^2\,\Sigma_4, \qquad \Sigma_i := \sum_{\substack{m_1,m_2 \mid Q_i\\ m_1,m_2>1}} \nu(\operatorname{lcm}(m_1,m_2)).$$
$\Sigma_i$ is a sum of products of the numbers $\nu(p^v) = g_p(v)/(1-\delta_p)$ with non-negative coefficients, so by (2) it is at most the same sum with $\hat g$ and all exponents allowed. The pairs $(v_1, v_2)$ with $\max = v$ number $2v+1$, so that enlarged sum over **all** pairs $(m_1,m_2)$ is $\prod_p\bigl(1 + \hat H_p/(1-\delta_p)\bigr)$; removing the pairs with $m_1 = 1$ or $m_2 = 1$ gives
$$\Sigma_i \le \hat\Pi_2 - 2\hat\Pi_1 + 1, \qquad \hat\Pi_1 = \prod_{k \le i}\Bigl(1 + \frac{\hat G_{p_k}}{1-\delta_k}\Bigr),\quad \hat\Pi_2 = \prod_{k\le i}\Bigl(1 + \frac{\hat H_{p_k}}{1-\delta_k}\Bigr).$$
With $\hat G = 1, \tfrac13, \tfrac15, \tfrac19, \tfrac1{11}$ and $\hat H = 4, \tfrac76, \tfrac23, \tfrac{16}{45}, \tfrac{19}{66}$ for $p = 3,5,7,11,13$:

- $i = 3$: $\hat\Pi_1 = \tfrac{16}{5}$, $\hat\Pi_2 = \tfrac{325}{18}$, so $P_4(C_4) \le \tfrac1{81}\cdot\tfrac{1139}{90}\cdot\tfrac{25}{24} = \tfrac{5695}{34992} \approx 0.16275$.
- $i = 4$: $\hat\Pi_1 = \tfrac{16}{5}\cdot\tfrac{32}{27}$, $\hat\Pi_2 = \tfrac{325}{18}\cdot\tfrac{43}{27}$, so $P_5(C_5) \le \tfrac{1}{121}\bigl(\hat\Pi_2 - 2\hat\Pi_1 + 1\bigr) = \tfrac{53873}{294030} \approx 0.18322$.

## 4. Conclusion

By (3), (4) and §3,
$$P_5(\text{covered}) \le \frac{28}{45} + \frac{5695}{34992} + \frac{53873}{294030} = \frac{4099375}{4234032} < 1 .$$
$P_5$ is a probability measure on $\mathbb{Z}/L$, so some residue is uncovered. $\blacksquare$

## Checks

- `indep/verify5.py`: the fractions above, in exact arithmetic; and, as a sanity check of the monotonicity step, the finite-exponent bound for all $6^5$ exponent vectors in $[1,6]^5$ (largest value $0.96412$).
- `indep/brute315.py`: exhaustive optimum for $L = 315$ (Lemma 2 is sharp there).
- `indep/enh_scan.py`: the same lemma inside the finite scan excludes 16 of the 20 odd $L \le 10^{10}$ that the distorted certificate could not, including $1\,527\,701\,175$. The smallest remaining is $4\,583\,103\,525 = 3^4 5^2 7^2\cdot 11\cdot 13\cdot 17\cdot 19$. (Numerical; see `research/records/2026-11-20-independence-gain.md`.)

## What this does not do

- It does not reach six primes. The same bookkeeping for $\{3,5,7,11,13,17\}$ gives about $1.13$.
- It is not the conjecture. Supports with many primes need the large-prime machinery of BBMST, which misses the non-squarefree case by a wide margin.
