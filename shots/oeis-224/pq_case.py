"""A000224 conjecture, case n = p q (distinct odd primes p < q): no solution of
   A (A - 1) | n^2 - 1,  A = (p+1)(q+1)/4.
Write n^2 - 1 = k A (A - 1). Then 1 <= k <= 15 (since X(X-4) > p^2 q^2 - 1 for X = (p+1)(q+1)),
and k X (X - 4) = 16 (p^2 q^2 - 1). For k <= 15 this forces (1+1/p)^2 (1+1/q)^2 > 16/15 - 16/(15 p^2 q^2),
hence p <= 61 (checked below). For each such p and k the equation is quadratic in q: solve exactly."""
from sympy import isprime, primerange
from math import isqrt
sols = []
# step 1: p bound. (1+1/p)^4 >= (1+1/p)^2 (1+1/q)^2 > 16/15 - 16/(15*9*25) gives p <= 61
lhs = lambda p: (1 + 1/p) ** 4
thr = 16/15 - 16/(15*9*25)
pmax = max(p for p in primerange(3, 10**4) if lhs(p) > thr)
print("p bound:", pmax)
for p in primerange(3, pmax + 1):
    c = p + 1
    for k in range(1, 16):
        # k c^2 (q+1)^2 - 4 k c (q+1) - 16 p^2 q^2 + 16 = 0  ->  a q^2 + b q + d = 0
        a = k * c * c - 16 * p * p
        b = 2 * k * c * c - 4 * k * c
        d = k * c * c - 4 * k * c + 16
        if a == 0:
            if b != 0 and (-d) % b == 0:
                q = -d // b
                if q > p and isprime(q): sols.append((p, q, k))
            continue
        disc = b * b - 4 * a * d
        if disc < 0: continue
        r = isqrt(disc)
        if r * r != disc: continue
        for num in (-b + r, -b - r):
            if num % (2 * a) == 0:
                q = num // (2 * a)
                if q > p and isprime(q):
                    A = c * (q + 1) // 4
                    if (p*p*q*q - 1) % (A * (A - 1)) == 0: sols.append((p, q, k))
print("solutions (p, q, k):", sols)
# brute-force cross-check for small q
bad = [(p, q) for p in primerange(3, 400) for q in primerange(p + 1, 4000)
       if (p*p*q*q - 1) % (((p+1)*(q+1)//4) * ((p+1)*(q+1)//4 - 1)) == 0]
print("brute force p<400, q<4000:", bad)
