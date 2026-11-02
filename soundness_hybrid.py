"""Soundness test: eta must be >= 1 on every known covering number (McNew-Setty Table 2, primitive,
< 10^6, excluding 773500 whose status is unknown). Minimised over all prime orders and delta grid."""
from hybrid_fast import eta_best, tower, factor
COV = [12,80,90,210,280,378,448,1386,1650,2200,2464,5346,9750,11264,11466,13000,14994,18954,20384,
23166,26656,27846,30294,31122,33150,33858,36608,37050,37674,44200,44850,49400,49504,53248,53900,
55328,59800,63750,66976,71250,72930,85000,95000,95744,97240,100100,107008,107406,112112,117306,
120042,131274,142002,145314,192500,208544,223074,242250,252448,272272,293250,311168,318500,323000,
369750,385434,391000,395250,423500,431250,450846,452608,485982,493000,505856,519498,527000,568458,
575000,612352,617526,654500,660114,685216,731500,735150,747954,785850,863968,885500,896610,909568,
923552,980200]
bad = 0
worst = (9, None)
for L in COV:
    fac = factor(L)
    e = eta_best(fac, "all")
    if e < worst[0]: worst = (e, L)
    if e < 1 - 1e-12:
        bad += 1; print("UNSOUND?", L, fac, e)
print(f"{len(COV)} covering numbers tested, violations: {bad}, min eta = {worst[0]:.6f} at L={worst[1]}")
