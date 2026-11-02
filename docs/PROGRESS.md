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

## 2. Claims ledger

| # | Claim | Disposition | Where |
|---|---|---|---|
| 1 | Tower certificate inequality | **proved** (prose above; Lean kernel `one_le_towerSum`) | `lean/Covering/Tower.lean` |
| 2 | φ-certificate inequality | **proved** (Lean kernel `one_le_phiSum`) | `lean/Covering/Phi.lean` |
| 3 | Decidable checks `check`, `check2` are sound (divisor enumeration, trial division, valuations verified) | **proved** (kernel) | `Fast.lean`, `Check.lean`, `TowerCheck.lean` |
| 4 | Odd covering ⇒ lcm $> 10^5$ | **proved, kernel only** (build 150/165 chunks at time of writing) | `ScanK/` |
| 5 | Odd covering ⇒ lcm $> 675\,674$ and $> 10^6$ | **native** | `ScanN.lean`, `ScanT/All1M.lean` |
| 6 | Odd covering ⇒ lcm $> 6\,891\,884$ | **native** (build 100/173 chunks) | `ScanT/AllFull.lean` |
| 7 | First odd non-deficient $L$ with $S_\varphi(L) \ge 1$ is $675675 = 3^3 5^2 7\cdot 11\cdot 13$; with $T(L) \ge 1$ is $6891885 = 3^4 5\cdot 7\cdot 11\cdot 13\cdot 17$ | **numerical** (Python), and implied by 5–6 for the lower side | `phi_certificate.py`, `tower_certificate.py` |
| 8 | Certificate never fires on an actual covering number (soundness cross-check, $L \le 240$, all moduli) | **numerical** | commit history |
| 9 | Sieve + McNew–Setty pairwise-coprime inclusion–exclusion excludes 6891885 and first fails at 11486475 | **numerical**; validity of the combined bound **unproved** | `combined_certificate.py` |
| 10 | $t_9 \le 2$ (modulus 9 used twice) has no covering with $L = 945$ | **numerical** (CaDiCaL UNSAT, 557 s; not independently certified) | `search.py`, `verify.py` |

## 3. Literature check (SciSpace, 2 Nov 2026) and what it changes

- The weight-region idea of Step 1 appears in Hackmon (Apr 2026) with the limiting factor $(p-2)/(p-1)$ and a prime-support (any exponents) conclusion for $\le 4$ primes; see [references/H26.md](references/H26.md). Our certificate is the exact finite-$L$ form, and the formalization is ours. The method should be credited as independently found there first.
- Schroeder (Sep 2026) claims $\omega(L) \ge 9$ and $L \ge 9\,704\,539\,845$ with a Lean package; see [references/S26.md](references/S26.md). **Unchecked**: the package (no `sorry`, no `native_decide` found by grep; toolchain v4.32.0-rc1) could not be built in this environment, because executing downloaded code is blocked here. Until rebuilt, it is a claim, not a result we rely on. If it holds, claims 4–6 are superseded numerically; the elementary certificate and kernel-only check remain of independent interest.
- The Zenodo note of Rafik (Jan 2026) states only the density condition ($L \ge 945$); see [references/R26.md](references/R26.md).
- Mian–Siddique (Jul 2026): $L > 10^4$, Lean; McNew–Setty (2025): covering numbers to $10^6$, inclusion–exclusion inequality; see [references/MS26.md](references/MS26.md), [references/MS25.md](references/MS25.md).

## 4. What remains open (next steps, in order)

1. Rebuild Schroeder's Lean package outside this sandbox and print its axioms (decides the framing of everything).
2. Prove the combined sieve + inclusion–exclusion bound (claim 9), then formalize; expected wall 11486475.
3. Prime-support version of the tower certificate (take $e_p \to \infty$), recovering Hackmon's four-prime theorem in Lean.
4. Write-up (outline in [MILESTONES.md](../MILESTONES.md)).

*Related: [PROBLEM.md](PROBLEM.md) (statement and conventions) · [references/](references/) (one page per cited work).*
