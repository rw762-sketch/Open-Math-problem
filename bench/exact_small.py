#!/usr/bin/env python3
"""Exact rational totals of the comparison bound for the first k odd primes (k = 5, 6, 7), with fixed caps.
Independent of engine.py (no tables, no floats): uses check_small.total."""
from fractions import Fraction as F
from check_small import total
CAPS = {5: 1, 7: 2, 11: 4, 13: 6, 17: 8, 19: 9}     # a_p = delta_p (p-1); delta_p <= 1/2
if __name__ == '__main__':
    for last in (13, 17, 19):
        st = [(p, F(a)) for p, a in CAPS.items() if p <= last]
        if last == 13: st = [(5, F(2)), (7, F(2)), (11, F(4)), (13, F(6))]
        tot, det = total(st, [(3, F(2))])
        print(f'primes 3..{last}: caps {[(p, int(a)) for p, a in st]}')
        print(f'   total = {tot} = {float(tot):.10f}  ->', 'below 1' if tot < 1 else 'NOT below 1')
