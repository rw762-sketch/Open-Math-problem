# Exact low-prime blocks for the distorted tower certificate (negative results, 3 Nov 2026)

Goal: push `odd_covering_lcm_gt_1527701174` past the barrier
$L_* = 1\,527\,701\,175 = 3^3 5^2 7^2\cdot 11\cdot 13\cdot 17\cdot 19$ ($\eta = 1.014$) by treating the
smallest primes exactly instead of by the union bound. All numerical (CP-SAT, `ortools`).

| Attempt | Result | Disposition |
|---|---|---|
| `umin.py`: exact minimum uncovered count $u(Q)$ with one class per divisor $d \mid Q$, $d>1$ | $u(45)=16$, $u(135)=43$, $u(225)=71$, $u(675)=188$ (tower bound for the pure classes alone: $14\cdot 19 = 266$) | numerical, optimal |
| `eta_base.py`: base weight uniform on the exact uncovered set mod $675$, class bound $\min(675/m, u)/u$ | $\eta(L_*) = 1.218$, **worse** than $1.014$: the uncovered set is not a product set, so its class bounds are much cruder | numerical |
| `mix35.py`: keep the tower measure (uniform on $A_3\times A_5$), replace the union bound for the mixed $\{3,5\}$ classes by their exact worst case | worst case $78/266 = 0.2932$, **exactly** the union bound $G_5(\Pi_1 - 1)$: the mixed classes can be placed disjointly. No gain | numerical, optimal |
| `need357.py`, `mix357.py`: same for the block $\{3,5,7\}$ | an exact block helps only if the worst-case covered fraction is $< 0.5732$ (union bound $0.5933$). CP-SAT does not close the gap in 10 min (bound $0.976$); `mix357.py` also fixes one pure configuration, which is not WLOG | inconclusive |

Conclusion: the slack in $\eta(L_*)$ is not in the first mixed stage. The union bound is tight
there because the adversary can arrange the mixed classes disjointly on the product set. Any further
gain has to come from the large-prime stages (second moment / distortion), or from a different
certificate.
