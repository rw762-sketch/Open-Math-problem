"""Exact worst-case covered fraction of the product set A_p x A_q by the mixed classes.
A_p = residues mod p^a missed by the pure classes p, p^2, .., p^a (one class each), likewise A_q.
Mixed moduli: p^i q^j, i, j >= 1. Weight uniform on A_p x A_q (the tower measure, no distortion).
c(p^a, q^b) = max over all choices of  |covered ∩ (A_p x A_q)| / (|A_p| |A_q|)."""
import sys
from ortools.sat.python import cp_model
def cmix(p, a, q, b, tl=120):
    P, Qq = p**a, q**b; N = P * Qq
    pure_p = [p**i for i in range(1, a + 1)]; pure_q = [q**j for j in range(1, b + 1)]
    mixed = [p**i * q**j for i in range(1, a + 1) for j in range(1, b + 1)]
    best = 0; arg = None
    # possible sizes
    for s3 in range(P - sum(P // d for d in pure_p), P + 1):
        for s5 in range(Qq - sum(Qq // d for d in pure_q), Qq + 1):
            m = cp_model.CpModel()
            x = {(d, r): m.NewBoolVar("") for d in pure_p + pure_q + mixed for r in range(d)}
            for d in pure_p + pure_q + mixed: m.AddExactlyOne(x[d, r] for r in range(d))
            m.Add(x[p, 0] == 1); m.Add(x[q, 0] == 1)
            A = [m.NewBoolVar("") for y in range(P)]; B = [m.NewBoolVar("") for z in range(Qq)]
            for y in range(P):   # A[y] == not covered by pure p classes
                cs = [x[d, y % d] for d in pure_p]
                m.AddBoolOr(cs + [A[y]]); [m.AddImplication(c, A[y].Not()) for c in cs]
            for z in range(Qq):
                cs = [x[d, z % d] for d in pure_q]
                m.AddBoolOr(cs + [B[z]]); [m.AddImplication(c, B[z].Not()) for c in cs]
            m.Add(sum(A) == s3); m.Add(sum(B) == s5)
            cov = []
            for n in range(N):
                y, z = n % P, n % Qq
                c = m.NewBoolVar("")
                m.AddImplication(c, A[y]); m.AddImplication(c, B[z])
                m.AddBoolOr([x[d, n % d] for d in mixed] + [c.Not()])
                cov.append(c)
            m.Maximize(sum(cov))
            s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = 8
            st = s.Solve(m)
            if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE): continue
            ub = s.BestObjectiveBound()
            r = ub / (s3 * s5)
            print(f"  |A|=({s3},{s5}) cover<= {ub:.0f} (found {s.ObjectiveValue():.0f}, {s.StatusName(st)}) ratio<= {r:.4f}", flush=True)
            if r > best: best, arg = r, (s3, s5)
    return best, arg
if __name__ == "__main__":
    p, a, q, b = map(int, sys.argv[1:5])
    print(cmix(p, a, q, b))
