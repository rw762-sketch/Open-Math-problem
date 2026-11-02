# The odd covering problem (Erdős #7)

*Problem page · Erdős–Selfridge, c. 1970 · Status: **open**. Verbatim statements below; everything this repo proves is on the [progress page](PROGRESS.md).*

*Tags: covering systems · sieve · Chinese remainder theorem · formal verification (Lean 4). Difficulty: ★★★ for the problem; ★★ for the exclusion bounds pursued here.*

A **covering system** is a finite family of residue classes $a_i \pmod{m_i}$ whose union is $\mathbb{Z}$. It is **distinct** if the moduli are pairwise different, and **odd** if every modulus is odd. Throughout, moduli are $> 1$.

**Problem (Erdős–Selfridge).** Does there exist a distinct covering system all of whose moduli are odd?

**Quantitative form pursued here.** Write $L = \operatorname{lcm}(m_1,\dots,m_k)$. Find an explicit $N$ such that every odd distinct covering system has $L > N$, with a machine-checked proof.

Prior certified bound before this repo: $L > 10^4$ (Mian–Siddique, Lean; see [references](references/MS26.md)). What is known in general: Hough–Nielsen (every distinct covering has a modulus divisible by 2 or 3, so $3 \mid L$); Balister–Bollobás–Morris–Sahasrabudhe–Tiba (no odd distinct covering with squarefree moduli); Berger–Felzenbaum–Fraenkel's condition $\prod_{p\mid L}\frac{p-1}{p-2} - \sum_{p \mid L}\frac{1}{p-2} > 2$, which already forces $\omega(L) \ge 5$.

## Conventions used in the Lean development

- A covering of $\mathbb{Z}$ is a list of classes `Cls r d` with `CoversInt`; `IsCovering L` packages: all moduli positive, all moduli divide `L`, all `> 1`, moduli injective, union covers `range L`.
- `odd_covering_lcm_gt_N : CoversZ cs → (∀ c ∈ cs, Odd c.d) → (∀ c, 1 < c.d) → injective moduli → N < lcm of the moduli`.
- Trust levels: **kernel** means `decide +kernel` only (axioms `propext, Classical.choice, Quot.sound`); **native** means the scan uses `native_decide` (adds `Lean.ofReduceBool`, i.e. trusts the Lean compiler).
