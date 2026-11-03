"""Exact (Fraction) recheck of #273 certificates: lines 'L eta p:k p:k ...' (order, delta=k/200)."""
import sys
from fractions import Fraction as F
from math import gcd
from sympy import isprime, factorint
def vp(n,p):
    v=0
    while n%p==0: n//=p; v+=1
    return v
def eta_exact(L, order, ks):
    f=factorint(L); E={p:f[p] for p in order}
    U={}
    for p in order:
        rem=sum(2**(E[p]-j) for j in range(1,E[p]+1) if p==2 and 2**j>=4 and isprime(2**j+1))
        U[p]=p**E[p]-rem
    g=lambda p,v: F(min(p**(E[p]-v),U[p]),U[p])
    c={p:1/(1-F(k,200)) for p,k in zip(order,ks)}
    divs=[1]
    for p in order: divs=[d*p**k for d in divs for k in range(E[p]+1)]
    allowed=[d for d in divs if d>=4 and isprime(d+1)]
    nu=lambda m: __import__('math').prod([g(q,vp(m,q))*c[q] for q in order if m%q==0], start=F(1))
    tot=F(0)
    for i,p in enumerate(order):
        later=order[i+1:]
        mixed=[]
        for d in allowed:
            if d%p or any(d%q==0 for q in later): continue
            j=vp(d,p); m=d//p**j
            if m>1: mixed.append((m,j))
        M1=sum((g(p,j)*nu(m) for m,j in mixed), F(0))
        dl=F(ks[i],200)
        if dl==0: t=M1
        else:
            M2=sum((g(p,j1)*g(p,j2)*nu(m1*m2//gcd(m1,m2)) for m1,j1 in mixed for m2,j2 in mixed), F(0))
            t=min(M1, M2/(4*dl*(1-dl)))
        tot+=t
    return tot
bad=0; n=0; worst=F(0)
for line in open(sys.argv[1]):
    a=line.split(); L=int(a[0]); eta=float(a[1])
    if eta>=1 or eta<float(sys.argv[2]): continue
    pk=[x.split(':') for x in a[2:]]; order=[int(p) for p,k in pk]; ks=[int(k) for p,k in pk]
    v=eta_exact(L,order,ks); n+=1; worst=max(worst,v)
    if v>=1: bad+=1; print("EXACT FAIL",L,float(v))
print(f"rechecked {n} certificates exactly (float eta >= {sys.argv[2]}): failures {bad}, worst {float(worst):.6f}")
