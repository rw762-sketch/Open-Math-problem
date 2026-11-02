# Progress report for the odd covering problem

*Ryan Wu and Claude Fable 5.1 · November 2026 · Problem remains **open**. Every claim below carries a disposition: **proved** (prose proof here, kernel-checked in Lean), **native** (Lean with `native_decide`), **numerical** (computed, not proved), or **unchecked**.*

## 1. The two certificates, with proofs

Fix $L = \prod_p p^{e_p}$ and write $u_p = p^{e_p} - (1 + p + \dots + p^{e_p - 1})$, the number of residues mod $p^{e_p}$ that survive after one class is removed for each of the moduli $p, p^2, \dots, p^{e_p}$. Note $u_p / p^{e_p} \ge (p-2)/(p-1)$.

> **Tower certificate** (proved). If
> $$T(L) := \sum_{\substack{d \mid L\\ \omega(d) \ge 2}} \ \prod_{p \mid L} \frac{\min\bigl(p^{\,e_p - v_p(d)},\, u_p\bigr)}{u_p} \ < 1,$$
> then no covering system with distinct moduli $> 1$ has lcm $L$.
>
> **φ-certificate** (proved). If $\sum_{d \mid L,\ d \text{ composite}} 1/\varphi(d) < 1$, the same conclusion holds. (For squarefree $L$ the two coincide; in general the tower certificate is at least as strong.)

**Proof of the tower certificate.** Let $\mathcal{C}$ be a covering with distinct moduli dividing $L$; reduce everything mod $L$, so $\mathcal{C}$ covers $\mathbb{Z}/L$.

*Step 1, sieve the towers.* For each prime $p \mid L$ the moduli $p, p^2, \dots, p^{e_p}$ each occur at most once. Their classes, read mod $p^{e_p}$, remove at most $p^{e_p - 1} + p^{e_p - 2} + \dots + 1$ residues, so a set $A_p \subseteq \mathbb{Z}/p^{e_p}$ of size $|A_p| \ge u_p$ is untouched by them. Let
$$U = \{\, n \in \mathbb{Z}/L : n \bmod p^{e_p} \in A_p \text{ for all } p \,\}.$$
By the Chinese remainder theorem $|U| = \prod_p |A_p|$, and every $n \in U$ must be covered by a class whose modulus $d$ has $\omega(d) \ge 2$.

*Step 2, count how much one composite class can take.* Fix a class $c \pmod d$ with $d \mid L$. An element $n \in U$ lies in it iff for every $p$, $n \bmod p^{e_p} \in A_p$ and $n \equiv c \pmod{p^{v_p(d)}}$. By CRT the count factors over primes:
$$|\{c \bmod d\} \cap U| = \prod_p \bigl|\{ x \in A_p : x \equiv c \pmod{p^{v_p(d)}} \}\bigr| \le \prod_p \min\bigl(p^{\,e_p - v_p(d)},\ |A_p|\bigr).$$
(The $p$-factor is a class mod $p^{v_p(d)}$ inside $\mathbb{Z}/p^{e_p}$, which has $p^{e_p - v_p(d)}$ elements, intersected with $A_p$.)

*Step 3, union bound and normalise.* Since the composite classes cover $U$,
$$1 \le \sum_{\omega(d)\ge 2} \frac{|\{c_d\} \cap U|}{|U|} \le \sum_{\omega(d)\ge 2} \prod_p \frac{\min(p^{e_p - v_p(d)}, |A_p|)}{|A_p|} \le \sum_{\omega(d)\ge 2} \prod_p \frac{\min(p^{e_p - v_p(d)}, u_p)}{u_p} = T(L),$$
the last step because $s \mapsto \min(a, s)/s$ is non-increasing and $|A_p| \ge u_p$. So $T(L) \ge 1$ for every covering number $L$; contrapositively $T(L) < 1$ excludes $L$. $\square$

**Proof of the φ-certificate.** Same argument, sieving only the prime moduli: take $A_p$ to be the complement of the class mod $p$ used by the modulus $p$ (or any class if $p$ is unused), so $|A_p| = p^{e_p} - p^{e_p - 1} = \varphi(p^{e_p})$. For $p \mid d$ the $p$-factor in Step 2 is at most $p^{e_p - v_p(d)}$; for $p \nmid d$ it is $|A_p|$. Dividing by $|U| = \prod_p \varphi(p^{e_p})$ gives
$$\frac{|\{c\}\cap U|}{|U|} \le \prod_{p \mid d} \frac{p^{e_p - v_p(d)}}{p^{e_p-1}(p-1)} = \prod_{p \mid d} \frac{1}{p^{v_p(d)-1}(p-1)} = \frac{1}{\varphi(d)},$$
and the union bound over the composite $d$ gives $\sum_{d \text{ composite}} 1/\varphi(d) \ge 1$. $\square$

*Sharpness.* $T(12) = 1$ and $T(80) = 1$, and both are covering numbers, so the inequality cannot be improved by a constant.

**The tower certificate sharpens Berger–Felzenbaum–Fraenkel.** Let $P$ be the set of primes dividing $L$. Then

$$T(L) \ \le\ \prod_{p \in P}\frac{p-1}{p-2} \;-\; 1 \;-\; \sum_{p\in P}\frac{1}{p-2},$$

so the classical BFF condition "$\prod_{p \mid L}\frac{p-1}{p-2} - \sum_{p \mid L}\frac1{p-2} \ge 2$ for every covering number $L$" is the exponent‑free limit of the tower certificate, and Hackmon's four‑prime theorem (his $R = 41/45$ for $\{3,5,7,11\}$) is this inequality evaluated at that prime set. (Status: **proved**, Lean kernel `towerSum_le_bff` in `BFF.lean`, standard axioms; corollary `no_covering_3_5_7_11`: no covering with lcm $3^a5^b7^c11^d$ for any exponents, i.e. Hackmon's four-prime theorem at $\{3,5,7,11\}$.)

*Proof.* Since $u_p = p^{e_p} - \frac{p^{e_p}-1}{p-1} \ge p^{e_p}\frac{p-2}{p-1}$, for $p \mid d$ the factor satisfies $\frac{\min(p^{e_p - v}, u_p)}{u_p} \le \frac{p^{e_p-v}}{u_p} \le \frac{p-1}{p-2}\,p^{-v}$, and for $p \nmid d$ it equals $1$. Group the divisors $d$ by their support $S \subseteq P$, $|S| \ge 2$, and sum the geometric series over each exponent $v \in [1, e_p]$:
$$T(L) \le \sum_{|S|\ge 2}\ \prod_{p\in S}\frac{p-1}{p-2}\sum_{v=1}^{e_p} p^{-v} \ \le\ \sum_{|S| \ge 2}\ \prod_{p \in S}\frac{p-1}{p-2}\cdot\frac{1}{p-1} \ =\ \sum_{|S| \ge 2}\ \prod_{p\in S}\frac{1}{p-2},$$
and $\sum_{S \subseteq P} \prod_{p \in S} \frac1{p-2} = \prod_{p \in P}\bigl(1 + \frac1{p-2}\bigr)$; removing the terms $|S| \le 1$ gives the claim. $\square$

Consequences: the per‑$L$ certificate is strictly stronger than BFF (e.g. BFF cannot exclude $L = 3^a 5^b 7^c 11^d 13^e$ for any exponents since $\prod - \sum = 2.14$, while $T(L) < 1$ for all such $L$ below $6\,891\,885$), and BFF alone gives only $\omega(L) \ge 5$ for odd coverings.

## 1b. The distorted tower sieve (Milestone 6, first step)

Every first-order method stops at $11\,486\,475$: the tower certificate ($T = 1.09$), the sieve plus McNew–Setty inclusion–exclusion ($1.011$), and, as we checked, the Balister–Bollobás–Morris–Sahasrabudhe–Tiba distorted sieve evaluated as written ($\eta = 1.0024$, optimised $\delta$). Combining two of them does better than either.

**Setting.** List the primes of $L$ in any order $p_1, \dots, p_n$, put $Q_i = p_1^{e_1}\cdots p_i^{e_i}$, and pick caps $\delta_i \in [0, \tfrac12]$. With $u_k$ as before, let $g_k(v) = \min(p_k^{e_k - v}, u_k)/u_k$, $G_k = \sum_{v=1}^{e_k} g_k(v)$, and let $\nu$ be the multiplicative function with $\nu(p_k^v) = g_k(v)/(1-\delta_k)$ for $v \ge 1$. Define
$$M^{(1)}_i = G_i\!\!\sum_{\substack{m \mid Q_{i-1}\\ m>1}}\!\! \nu(m),\qquad M^{(2)}_i = G_i^2\!\!\!\sum_{\substack{m_1, m_2 \mid Q_{i-1}\\ m_1, m_2 > 1}}\!\!\!\nu(\operatorname{lcm}(m_1,m_2)),\qquad \eta = \sum_{i} \min\Bigl(M^{(1)}_i,\ \frac{M^{(2)}_i}{4\delta_i(1-\delta_i)}\Bigr),$$
with the second option dropped when $\delta_i = 0$.

> **Distorted tower certificate** (proof below, **proved in prose**, not yet formalised). If $\eta < 1$ for some order and some caps, then no covering system with distinct moduli $> 1$ has lcm $L$. With every $\delta_i = 0$, $\eta = T(L)$, so this extends the tower certificate.

**Proof.** Fix a covering $\{a_d \bmod d\}$ with distinct moduli dividing $L$. Each modulus $d$ belongs to exactly one stage $i$, the largest $i$ with $p_i \mid d$; write $d = m p_i^{j}$ with $m \mid Q_{i-1}$, $j \ge 1$. Call it **pure** if $m = 1$ and **mixed** otherwise; let $T_i, C_i \subseteq \mathbb{Z}/L$ be the unions of the pure and mixed classes of stage $i$. We build probability measures $P_0, \dots, P_n$, where $P_i$ is a measure on $\mathbb{Z}/Q_i$ extended uniformly to $\mathbb{Z}/L$, and $P_0$ is uniform. By CRT, write $\mathbb{Z}/Q_i = \mathbb{Z}/Q_{i-1} \times \mathbb{Z}/p_i^{e_i}$ and call $F(x) = \{x\}\times \mathbb{Z}/p_i^{e_i}$ a fibre.

*(a) Condition on the tower.* The pure classes of stage $i$ remove a fixed set $Y_i \subseteq \mathbb{Z}/p_i^{e_i}$, the same in every fibre, with $|Y_i| \le \sum_{j=1}^{e_i} p_i^{e_i - j}$. So $A_i = \mathbb{Z}/p_i^{e_i}\setminus Y_i$ has $|A_i| \ge u_i \ge 1$. Put $P'_i(x,y) = P_{i-1}(x)\,\mathbf 1[y \in A_i]/|A_i|$.

*(b) Distort on the mixed classes.* Let $\alpha_i(x) = |\{y \in A_i : (x,y) \in C_i\}|/|A_i|$ be the $P'_i$-fraction of the fibre removed by mixed classes, and define $P_i$ from $P'_i$ by BBMST's rule (their (5)): on $C_i$, multiply by $\max\{0, \frac{\alpha_i - \delta_i}{\alpha_i(1-\delta_i)}\}$; off $C_i$, multiply by $\min\{\frac{1}{1-\alpha_i}, \frac{1}{1-\delta_i}\}$.

Four facts, each a one-line check.
1. *Fibre masses are preserved* in both (a) and (b), so $P_i(S) = P_{i-1}(S)$ for every $Q_{i-1}$-measurable $S$ (BBMST Lemma 2.1). In particular $P_n(T_i \cup C_i) = P_i(T_i \cup C_i)$.
2. *$P_i(T_i) = 0$*, since $T_i$ is the set of $(x,y)$ with $y \in Y_i$, and $P'_i$ vanishes there; step (b) only rescales.
3. *$P_i(C_i) \le \min\{E_{i-1}\alpha_i,\ E_{i-1}\alpha_i^2/(4\delta_i(1-\delta_i))\}$*, by BBMST Lemma 3.3 applied to $P'_i$ (their proof is fibre by fibre and only uses that $\alpha_i$ is the $P'_i$-fraction removed).
4. *Class bound:* for $m \mid Q_i$ and any $b$, $P_i(b + m\mathbb{Z}) \le \nu(m)$. By induction: if $p_i \nmid m$ then $b+m\mathbb{Z}$ is $Q_{i-1}$-measurable and fact 1 applies. If $p_i^j \parallel m$, $m = m' p_i^j$, then in each fibre over $x \equiv b \pmod{m'}$ the class picks the $y \in A_i$ with $y \equiv b \pmod{p_i^j}$. There are at most $\min(p_i^{e_i-j}, |A_i|)$ of them, so step (a) gives mass at most $g_i(j)P_{i-1}(x)$ (as $s \mapsto \min(a,s)/s$ is non-increasing and $|A_i| \ge u_i$), and step (b) multiplies by at most $1/(1-\delta_i)$. Summing over $x$ gives $\nu(p_i^j)P_{i-1}(b + m'\mathbb{Z}) \le \nu(m)$.

*Moments.* A point $(x,y)$ lies in the mixed class $a_d \bmod m p_i^j$ iff $x \equiv a_d \pmod m$ and $y \equiv a_d \pmod{p_i^j}$, so by the count in fact 4, $\alpha_i(x) \le \sum_{d = m p_i^j \text{ mixed}} g_i(j)\,\mathbf 1[x \equiv a_d \bmod m]$. Taking $E_{i-1}$ and using fact 4 gives $E_{i-1}\alpha_i \le M^{(1)}_i$. Squaring, a pair of conditions $x \equiv a \pmod{m_1}$, $x \equiv a' \pmod{m_2}$ is empty or one class modulo $\operatorname{lcm}(m_1,m_2)$, so $E_{i-1}\alpha_i^2 \le M^{(2)}_i$. Distinctness enters only here: each modulus contributes at most one class, so the sums over used moduli are bounded by sums over all divisors.

*Conclusion.* The covered set is $\bigcup_i (T_i \cup C_i)$, so by facts 1–3 and the moment bounds, $P_n(\text{covered}) \le \sum_i P_i(C_i) \le \eta < 1$. Some residue is uncovered. $\square$

*Closed form.* $\nu$ is multiplicative, so $\sum_{m \mid Q_{i-1}}\nu(m) = \prod_{k<i}(1 + c_kG_k)$ with $c_k = 1/(1-\delta_k)$. The pairs $(a,b) \in [0,e]^2$ with $\max(a,b) = v$ number $2v+1$, so $\sum_{m_1,m_2 \mid Q_{i-1}}\nu(\operatorname{lcm}) = \prod_{k<i}\bigl(1 + c_k\sum_{v\ge1}(2v+1)g_k(v)\bigr)$. Removing the terms with $m_1 = 1$ or $m_2 = 1$ gives $S_2 = \Pi_2 - 2\Pi_1 + 1$. Each $L$ therefore costs $O(\omega^2)$ (`hybrid_fast.py`, cross-checked against the divisor-sum implementation `hybrid_sieve.py`).

*What it gives* (`hybrid_scan.py`, all **numerical** until formalised):
- **Soundness check:** $\eta \ge 1$ on all 94 primitive covering numbers below $10^6$ in McNew–Setty's Table 2, minimised over every prime order and the $\delta$-grid, with minimum exactly $1$ (at $12$, $80$, $53248$, …). A sound certificate must pass this; a sharp one hits $1$.
- **Scan:** every odd $L \le 10^{10}$ with $\sigma(L) \ge 2L$ (about $2\times10^7$ numbers) is excluded, except $20$ values, the smallest being $L_{**} = 1\,527\,701\,175 = 3^3 5^2 7^2\cdot 11\cdot 13\cdot 17\cdot 19$ ($\eta = 1.014$). So **every odd covering would have lcm $\ge 1\,527\,701\,175$**, given the theorem above.
- **Exact check:** each of the $1704$ exclusions that needed the hybrid is emitted as an explicit certificate (order, $\delta$'s on the grid $k/200$) and rechecked in exact rational arithmetic (`verify_hybrid_exact.py`): $0$ failures, worst $\eta = 0.999002$. Float decisions near the boundary (tower values in $(0.99, 1)$, abundance within $10^{-9}$ of $2$) are logged and rechecked exactly.
- **Comparison:** this is $220\times$ the tower wall and $130\times$ the wall shared by the first-order methods, and about $6\times$ below Schroeder's claimed $9.7\times10^9$. His method ("completion … with conditional reweighting") sounds related and should be compared once his package is rebuilt. The tower conditioning in step (a) is Hackmon's weight region; the distortion is BBMST's. As far as our search shows, the combination is not in either paper.

## 2. Claims ledger

| # | Claim | Disposition | Where |
|---|---|---|---|
| 1 | Tower certificate inequality | **proved** (prose above; Lean kernel `one_le_towerSum`) | `lean/Covering/Tower.lean` |
| 2 | φ-certificate inequality | **proved** (Lean kernel `one_le_phiSum`) | `lean/Covering/Phi.lean` |
| 3 | Decidable checks `check`, `check2` are sound (divisor enumeration, trial division, valuations verified) | **proved** (kernel) | `Fast.lean`, `Check.lean`, `TowerCheck.lean` |
| 4 | Odd covering ⇒ lcm $> 10^5$ | **proved, kernel only** (build 79/165 chunks at time of writing; earlier counts in this log double-counted files) | `ScanK/` |
| 5 | Odd covering ⇒ lcm $> 675\,674$ and $> 10^6$ | **native** | `ScanN.lean`, `ScanT/All1M.lean` |
| 6 | Odd covering ⇒ lcm $> 6\,891\,884$ | **proved, kernel only** (`odd_covering_lcm_gt_6891884_kernel`; standard axioms) via prime replacement + 363 shaped moduli; supersedes the native scan | `Replace.lean`, `Shaped.lean`, `ShapedK6/` |
| 7 | First odd non-deficient $L$ with $S_\varphi(L) \ge 1$ is $675675 = 3^3 5^2 7\cdot 11\cdot 13$; with $T(L) \ge 1$ is $6891885 = 3^4 5\cdot 7\cdot 11\cdot 13\cdot 17$ | **numerical** (Python), and implied by 5–6 for the lower side | `phi_certificate.py`, `tower_certificate.py` |
| 8 | Certificate never fires on an actual covering number (soundness cross-check, $L \le 240$, all moduli) | **numerical** | commit history |
| 9 | Sieve + McNew–Setty pairwise-coprime inclusion–exclusion excludes 6891885 and first fails at 11486475 | **numerical**; validity of the combined bound **unproved** | `combined_certificate.py` |
| 11 | Tower ⇒ BFF, and the four-prime theorem for $\{3,5,7,11\}$ | **proved** (kernel, standard axioms) | `BFF.lean` |
| 12 | Every odd distinct covering has $\ge 5$ distinct primes in its lcm (`five_primes_of_odd_covering`) | **proved** (kernel, standard axioms) | `FourPrimes.lean` |
| 15 | Prime replacement for arbitrary exponents (`replace_one`, `reduce_to_shaped`) | **proved** (kernel, standard axioms) | `Replace.lean`, `Shaped.lean` |
| 13 | Distorted tower certificate ($\eta < 1$ ⇒ no covering with lcm $L$) | **proved in prose** (§1b); Lean pending | `hybrid_fast.py` |
| 14 | Odd covering ⇒ lcm $\ge 1\,527\,701\,175$ | **numerical**, certificates rechecked exactly (rests on 13); Lean pending | `hybrid_scan.py`, `verify_hybrid_exact.py` |
| 10 | $t_9 \le 2$ (modulus 9 used twice) has no covering with $L = 945$ | **numerical** (CaDiCaL UNSAT, 557 s; not independently certified) | `search.py`, `verify.py` |

## 3. Literature check (SciSpace, 2 Nov 2026) and what it changes

- The weight-region idea of Step 1 appears in Hackmon (Apr 2026) with the limiting factor $(p-2)/(p-1)$ and a prime-support (any exponents) conclusion for $\le 4$ primes; see [references/H26.md](references/H26.md). Our certificate is the exact finite-$L$ form, and the formalization is ours. The method should be credited as independently found there first.
- Schroeder (Sep 2026) claims $\omega(L) \ge 9$ and $L \ge 9\,704\,539\,845$ with a Lean package; see [references/S26.md](references/S26.md). **Unchecked**: the package (no `sorry`, no `native_decide` found by grep; toolchain v4.32.0-rc1) could not be built in this environment, because executing downloaded code is blocked here. Until rebuilt, it is a claim, not a result we rely on. If it holds, claims 4–6 are superseded numerically; the elementary certificate and kernel-only check remain of independent interest.
- The Zenodo note of Rafik (Jan 2026) states only the density condition ($L \ge 945$); see [references/R26.md](references/R26.md).
- Mian–Siddique (Jul 2026): $L > 10^4$, Lean; McNew–Setty (2025): covering numbers to $10^6$, inclusion–exclusion inequality; see [references/MS26.md](references/MS26.md), [references/MS25.md](references/MS25.md).

## 3b. Status of McNew–Setty's Lemma 4.10 (the basis of Milestone 4)

The lemma (covered proportion $\le \sum_{S \text{ pairwise coprime}} (-1)^{|S|+1}/\operatorname{lcm} S$) is stated in [MS25] with "follows likewise by inclusion–exclusion" and no written proof. Observations (ours):

- It is **not** a pointwise inclusion–exclusion inequality: for moduli $\{2,4,3,9\}$ with nested classes, an integer in all four classes contributes $1 - 4 + 4 = 1$ to the alternating count of covered points, i.e. $0$ to the uncovered side where $1$ is needed. Any proof must average.
- It is a **Shearer-type bound**: pairwise-coprime subsets are the independent sets of the "share a prime" graph $G_M$, so the right side is the independence polynomial $Z(G_M, -1/m)$, and $G_M$ is a valid dependency graph for the events "$n \in C_m$" by CRT. Shearer's theorem (1985) therefore proves the lemma whenever $(1/m)_{m\in M}$ lies in the Shearer region of $G_M$ (every induced subgraph has $Z > 0$). Outside that region the lemma is unproved.
- Exact search (`ms_lemma_stress.py`, `ms_stress2.py`): 0 violations in 446 exactly-solved instances, but every instance with $\Phi(M) > 0$ that we could solve exactly was inside the Shearer region; an instance outside it with $\Phi > 0$ needs two coprime "negative blocks", which forces moduli far beyond exact range. Many equality cases $\Phi(M) = $ min uncovered proportion were found (the bound is tight).
- For the application ($L = 6\,891\,885$, 160 divisors, $\Phi(D(L)) \approx 0.06$) membership in the Shearer region is **unverified**, and the LLL sufficient condition appears to fail there.

Disposition: Milestone 4 is **deprioritised** — it rests on an unproved lemma whose natural proof route (Shearer) does not obviously cover the cases needed. Milestone 5 (BFF in Lean) is fully proved in prose and comes first.

## 4. What remains open (next steps, in order)

1. Rebuild Schroeder's Lean package outside this sandbox and print its axioms (decides the framing of everything).
2. Prove the combined sieve + inclusion–exclusion bound (claim 9), then formalize; expected wall 11486475.
3. ~~Prime-support version of the tower certificate~~ done (`BFF.lean`); remaining: the general prime-replacement form (any four odd primes, via monotonicity of $1/(p-2)$).
4. Write-up (outline in [MILESTONES.md](../MILESTONES.md)).

*Related: [PROBLEM.md](PROBLEM.md) (statement and conventions) · [references/](references/) (one page per cited work).*
