# Benchmark: how far is each method from the odd covering conjecture?

*Ryan Wu and Claude · 21 Nov 2026 · floats unless marked exact.*

Every method in this area ends in the same way: a total that must be **below 1**. If it is, no covering exists in that case. This directory scores every method on one fixed list of cases with one code base, so a new idea can be measured against the rest in a few minutes.

The conjecture is the last row of the first table. No method is below 1 there.

## Scoreboard

**All odd primes at once, every exponent allowed unless stated.** Method: the comparison bound of Dai–Li–Li–Yi ([summary](../docs/references/DLLY26.md)).

| Case | Total | Status |
|---|---|---|
| Square-free moduli | 0.512 | theorem (BBMST 2021); our number |
| $5 \nmid Q$ (powers of 3 and of every prime $\ge 7$) | 0.836 with the paper's caps, 0.800 with ours | theorem (DLLY 2026) |
| $9 \nmid Q$ (3 once, powers of every prime $\ge 5$) | 0.9994 with the paper's caps, 1.019 with ours | theorem (DLLY 2026) |
| **Open case: $45 \mid Q$, nothing assumed** | **2.07** | open |
| Open case, block lemma on $\{3,5,7\}$ first | 2.18 | open |

**First $k$ odd primes, every exponent.** A total below 1 rules out every covering whose lcm has $k$ odd prime factors (prime replacement, `Replace.lean`).

| $k$ | largest prime | union bound | second moment (BBMST) | block lemma + second moment | comparison (DLLY) | block lemma + comparison |
|---|---|---|---|---|---|---|
| 4 | 11 | 0.911 | 0.811 | 0.779 | 0.606 | 0.720 |
| 5 | 13 | 1.143 | 1.013 | 0.968 | 0.785 | 0.833 |
| 6 | 17 | 1.335 | 1.172 | 1.127 | 0.895 | 0.918 |
| 7 | 19 | 1.520 | 1.340 | 1.296 | 1.003 | 1.015 |
| 8 | 23 | 1.681 | 1.470 | 1.426 | 1.091 | 1.097 |
| 9 | 29 | 1.814 | 1.567 | 1.522 | 1.155 | 1.154 |
| 10 | 31 | 1.944 | 1.662 | 1.617 | 1.218 | 1.211 |

## What the numbers say

- The open case is at about 2.07, so the best published method is short by a factor of two. (An earlier guess of 1.5 in our notes was too optimistic.)
- Adding the prime 5 to the case $5 \nmid Q$ takes the total from 0.80 to 2.07. Allowing 9 in the case $9 \nmid Q$ takes it from 1.0 to 2.07. The difficulty is the towers of 3 and 5 together.
- The comparison bound is much stronger than the second moment: it passes the square-free case at 0.51, where BBMST's own proof has a margin of about $2 \cdot 10^{-5}$.
- By-product: with the comparison bound, six primes come out at $0.8947 < 1$ (exact fraction in `results.json`, caps $a_p = 1, 2, 4, 6, 8$ for $p = 5, \dots, 17$). Given DLLY's Theorem 2.6, every odd covering then has at least seven primes in its lcm. Seven primes miss at 1.0026. Our own block lemma reaches five.
- The block lemma helps the second moment at every $k$, but next to the comparison bound it only helps from $k = 9$ on, and not in the open case.

## Methods

- **union bound**: $\prod(1+G_p) - 1 - \sum G_p$ with $G_p = 1/(p-2)$ (tower measure, [PROGRESS.md](../docs/PROGRESS.md)).
- **second moment**: BBMST distortion, stage cost $\min(M_1, M_2/(4\delta(1-\delta)))$, caps on a grid.
- **block lemma**: the first three primes cost $28/45$ ([FIVE_PRIMES.md](../docs/FIVE_PRIMES.md)), then the stated method from 11 on.
- **comparison**: classes with moduli $3^e$ conditioned away (a class mod $3^e$ then has probability $\le 2/3^e$), then for each prime $p \ge 5$ the stage cost is at most $c_p\,E(\tau(R)/(p-1) - \delta_p)^+$, where $R = \prod q^{T_q}$ with independent exponents, $P(T_q \ge e) = \gamma_q/q^e$, $\gamma_3 = 2$, $\gamma_q = c_q = 1/(1-\delta_q)$, and $\delta_q \le 1/2$.

## Files

| File | Purpose |
|---|---|
| `engine.py` | distribution of $\tau(R)$, stage costs, tail bounds |
| `reproduce.py` | the paper's two totals with the paper's parameters |
| `schedule.py`, `tune.py` | search for the caps $\delta_p$ (coordinate descent) |
| `finite.py` | the first-$k$ table |
| `run_all.py` | everything; writes `results.json` |
| `check_small.py`, `exact_small.py` | independent exact-fraction check for $k = 5, 6, 7$ |

Run: `python3 reproduce.py` (2 s), `python3 exact_small.py` (5 s), `python3 run_all.py` (6 min), `python3 tune.py open no9` (5 min).

## Validation

- `reproduce.py` gives 0.8364915559 and 0.9994428113; the paper states 0.8364915559 and 0.9994428144.
- Row $k = 5$ returns our earlier numbers: 1.0126 (the five-prime wall of 4 Nov) and 0.9682 (Theorem A).
- `exact_small.py` (fractions, no shared table code) agrees with the float engine to five digits for $k = 5, 6, 7$.

## Adding a method

A method is a function from a list of primes to a total (see `union`, `second_moment`, `comparison` in `finite.py`), or a new stage bound inside `Problem.total` in `schedule.py`. Add it to `run_all.py` and rerun. A valid method must be an upper bound for the covered measure in every arrangement, so it should never score below 1 on a support where coverings exist (any support containing 2 and 3).

## Caveats

- Floats, not directed rounding. Only the three exact fractions are exact.
- The caps come from coordinate descent and are not optimal. In the one case where the paper prints its caps ($9 \nmid Q$), ours are worse by 2%. Expect the open-case total to be high by a similar amount, not by a factor.
- The comparison rows rest on Theorem 2.6 of the paper, which we have read but not re-derived or formalised.
- A total above 1 is a score, not a probability.
