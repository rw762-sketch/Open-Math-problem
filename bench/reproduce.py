#!/usr/bin/env python3
"""Reproduce the two totals of Dai-Li-Li-Yi (arXiv 2611.15110): 5 does not divide Q (0.83649...) and
9 does not divide Q (0.99944...), with their parameters."""
import sys, time
from engine import *

TABLE2 = [(5,5,1),(7,11,2),(13,19,4),(23,23,6),(29,31,8),(37,37,9),(41,43,12),(47,61,16),(67,67,18),(71,83,24),
 (89,113,32),(127,127,40),(131,157,48),(163,223,64),(227,233,72),(239,239,80),(241,293,96),(307,307,120),
 (311,419,128),(421,449,144),(457,457,160),(461,577,192),(587,587,216),(593,787,256),(797,859,288),(863,863,320),
 (877,1103,384),(1109,1117,432),(1123,1123,480),(1129,1493,512),(1499,1637,576),(1657,1667,640),(1669,2131,768),
 (2137,2153,864),(2161,2161,960),(2179,2843,1024),(2851,3163,1152),(3167,3209,1280),(3217,3217,1296),
 (3221,4099,1536),(4111,4153,1728),(4157,4157,1792),(4159,4177,1920),(4201,5443,2048),(5449,6053,2304),
 (6067,6151,2560),(6163,6163,2592),(6173,6173,2880),(6197,7879,3072),(7883,7993,3456)]
def A_of(p):
    for lo, hi, A in TABLE2:
        if lo <= p <= hi: return A
    raise KeyError(p)

def case_no5(PR):
    """5 does not divide Q: gamma_3 = 2, primes >= 7, delta = 3/10."""
    m = Model(1600, 10); m.mult(3, 2.0)
    d = 0.3; c = 1 / (1 - d); tot = 0.0; i = 0
    ps = PR[PR >= 7]
    while ps[i] <= 5000:
        p = int(ps[i]); tot += c / (p - 1) * m.pos(d * (p - 1)); m.mult(p, c); i += 1
    # keep the third moment exact from here on; engine continues with M3 only
    mid, C, M3 = tail_third_moment(m, ps, i, d)
    J = len(PR[PR <= 10 ** 7])
    far = far_tail(C, M3, J)
    return tot, mid, far

def case_no9(PR):
    """9 does not divide Q: branches mod 3 averaged; primes >= 5."""
    m = Model(36000, 10); tot = 0.0; i = 0
    ps = PR[PR >= 5]
    while ps[i] <= 10 ** 5:
        p = int(ps[i]); a = A_of(p) if p <= 7993 else 71 / 200 * (p - 1)
        c = 1 / (1 - a / (p - 1))
        tot += c / (2 * (p - 1)) * (m.pos(a) + 2 * m.pos(a / 2)); m.mult(p, c); i += 1
    mid, C, M3 = tail_third_moment(m, ps, i, 0.5, C=128 / 27)
    J = len(PR[PR <= 10 ** 7])
    return tot, mid, far_tail(C, M3, J)

if __name__ == '__main__':
    t = time.time(); PR = primes_upto(10 ** 7)
    a = case_no5(PR); print('5 !| Q :', a, sum(a), ' paper: 0.771326775551 0.065156698062 0.000008082310  sum 0.836491555924', round(time.time() - t, 1), flush=True)
    b = case_no9(PR); print('9 !| Q :', b, sum(b), ' paper: 0.995566393703 0.003831404539 0.000045016154  sum 0.999442814397', round(time.time() - t, 1), flush=True)
