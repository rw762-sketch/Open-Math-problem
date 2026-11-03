# Graffiti-type graph conjectures: exhaustive and local search (no counterexample)

*Ryan Wu and Claude · November 2026 · All conjectures below remain **open**; results are numerical.*

**Targets.**
- The 9 conjectures of DeLaViña's *Written on the Wall II* (Graffiti.pc) marked open in google-deepmind/formal-conjectures (`FormalConjectures/WrittenOnTheWallII/`): numbers 19, 40, 61, 72, 84, 96, 133, 189, 199.
- The four TxGraffiti conjectures of Davila–Brimkov–Pepper (arXiv 2507.17780).

**Invariants.** Every invariant is implemented to match the Lean definitions in `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/`:
- path number (largest induced path), largest induced tree, largest induced forest, largest induced bipartite subgraph;
- path cover number, vertex connectivity (complete-graph convention), Havel–Hakimi residue;
- `distEven` (distance 0 counts), second-smallest degree, local independence $l(v) = \alpha(N(v))$;
- Hamiltonian path.

The C engine `ls.c` agrees with the Python reference `inv.py` on all 12,112 connected graphs with at most 8 vertices (11 invariants compared).

## Results

| # | Search | Outcome |
|---|---|---|
| 1 | All connected graphs on $\le 9$ vertices (261,080 at $n=9$; counts match OEIS A001349), all 9 WOWII conjectures (`gen.py`, `ls.c -DEXH`) | no counterexample |
| 2 | All connected graphs on 10 vertices: every 10-vertex graph is a 9-vertex graph plus a vertex, so extending all 274,668 graphs on 9 vertices covers them. This ran in two overlapping passes (base graphs 0 to about 140,000, then 135,000 to the end), checking 8,341,214 and 10,178,070 graphs (64-bit hash deduplication within each pass, so duplicates across passes); all 9 WOWII conjectures (`gen10.py`) | no counterexample |
| 3 | Simulated annealing over connected graphs with 10–20 vertices, conjectures 19, 61, 72, 84, 96 (`ls.c`), roughly 10^6 evaluations each | best slack exactly 0 (equality), never negative |
| 4 | Conjecture 133 on large $C_4$-free graphs (Petersen, Hoffman–Singleton, incidence graphs of PG(2,q) for q = 2, 3, 5, 7; `special.py`) | holds with margin $\ge 0$ (Petersen tight; Hoffman–Singleton has an induced path on 12 vertices vs 9 needed) |
| 5 | TxGraffiti Conjectures 1–4 on all connected graphs with $\le 9$ vertices (`txg.py`) | Conjecture 1 fails only on $K_2$ ($\alpha = 1$, $a = R = \Delta = 1$, bound $2$): a literal counterexample to "every nontrivial connected graph", presumably an unintended edge case. Conjecture 4 ($\mu^* \le H$) fails on exactly 8 graphs with 9 vertices, e.g. the friendship graph $F_4$; this reproduces Gupta (arXiv 2606.15761), who found the same 8, so it is a check of our code, not a new result. Conjectures 2 and 3: no failure up to 9 vertices |
| 6 | Gupta's new conjecture (arXiv 2606.15761, Conj. 1): $\mu^*(G) \le H(G)$ whenever $\Delta(G) \le 4$; he checked all graphs up to 11 vertices. We checked all trees with $\Delta \le 4$ up to 19 vertices (148,284 trees at $n = 19$; `subquartic_trees.py`) | no counterexample; closest $\mu^* - H = -1/14$ at $n = 16$ (two degree-4 hubs with three legs each, joined through a degree-3 vertex); equality only at $S_4$ ($n = 9$) |

**Why Gupta's subquartic conjecture looks true (heuristic, not a proof).** With $\Delta \le 4$, a pendant leg hub–mid–leaf costs $\tfrac{2}{2 + d(\text{hub})} + \tfrac23 \ge 1$ in $H$ and forces exactly one matching edge; pendant triangles ($\tfrac76$), leaves on a hub ($\tfrac25$ each, but one matching edge covers all of them) and degree-3 connectors ($\approx 1.07$ per forced edge) all cost at least 1 per forced matching edge. A counterexample needs a gadget forcing a matching edge at harmonic cost below 1; a proof could try a charging argument along these lines.

**Literature (checked 3 Nov 2026).** All four TxGraffiti conjectures were attacked in 2026:
- Conjecture 2 is refuted by a 24-vertex subcubic graph (arXiv 2607.23664).
- Conjecture 4 is treated in arXiv 2606.15761.
- Conjecture 1 in arXiv 2606.29553 and 2607.01438.
- The domination versus edge-domination conjecture, which is related to Conjecture 3, has a 50-vertex cubic counterexample (arXiv 2609.10783).

The WOWII conjectures in formal-conjectures record their known counterexamples at 12 to 18 vertices, beyond exhaustive reach. The surviving open ones are robust against both exhaustive and local search at these sizes.
