import sys, numpy as np
from sympy import isprime, divisors
L=int(sys.argv[1])
A=sorted(d for d in divisors(L) if d>=4 and isprime(d+1))
print("L",L,"moduli",len(A),"sum",sum(1/d for d in A))
unc=np.arange(L,dtype=np.int64)
chosen=[]
for d in A:
    if unc.size==0: break
    cnt=np.bincount(unc % d, minlength=d)
    r=int(cnt.argmax())
    chosen.append((r,d))
    unc=unc[unc % d != r]
print("uncovered after greedy:", unc.size, f"fraction {unc.size/L:.5f}")
