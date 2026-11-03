// a(n) = number of squares mod n, multiplicative; check n^2 ≡ 1 mod a(a-1) only for odd primes.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64; typedef __uint128_t u128;
static int sq_pe_cache[64];
u64 sqcount_pe(u64 p, int e) {  // brute force for small p^e, formula otherwise
    // formula (odd p): s(p^e) = floor(p^(e+1)/(2(p+1))) + 1 ; p=2: s(2^e) = floor(2^e/6)+2 for e>=... use brute for small
    u64 q = 1; for (int i = 0; i < e; i++) q *= p;
    if (1) {  // exact formula: 1 + sum_{2j<e} #(unit squares mod p^(e-2j))
        u64 c = 1;
        for (int j = 0; 2 * j < e; j++) {
            int k = e - 2 * j; u64 pk = 1; for (int i = 0; i < k; i++) pk *= p;
            if (p == 2) c += (k <= 2) ? 1 : (pk >> 3);
            else c += (pk / p) * (p - 1) / 2;
        }
        return c;
    }
    if (q <= 2000000) {
        char *seen = calloc(q, 1); u64 c = 0;
        for (u64 x = 0; x <= q / 2; x++) { u64 r = (u128)x * x % q; if (!seen[r]) { seen[r] = 1; c++; } }
        free(seen); return c;
    }
    fprintf(stderr, "too big %llu^%d\n", p, e); exit(1);
}
int main(int argc, char **argv) {
    u64 N = strtoull(argv[1], 0, 10);
    unsigned *spf = calloc(N + 1, sizeof(unsigned));
    for (u64 i = 2; i <= N; i++) if (!spf[i]) for (u64 j = i; j <= N; j += i) if (!spf[j]) spf[j] = i;
    // cache s(p^e) lazily via small table keyed by q
    unsigned *sv = calloc(N + 1, sizeof(unsigned));  // sv[q] for prime powers q
    u64 bad = 0;
    for (u64 n = 2; n <= N; n++) {
        u64 m = n, a = 1;
        while (m > 1) {
            u64 p = spf[m]; int e = 0; u64 q = 1;
            while (m % p == 0) { m /= p; e++; q *= p; }
            if (!sv[q]) sv[q] = sqcount_pe(p, e);
            a *= sv[q];
        }
        u64 M = a * (a - 1);
        int prime = (spf[n] == n);
        int cond = (M == 0) ? 0 : (((u128)n * n - 1) % M == 0);
        if (cond != (prime && n != 2)) { printf("MISMATCH n=%llu a=%llu prime=%d\n", n, a, prime); if (++bad > 20) break; }
    }
    printf("checked n <= %llu, mismatches %llu\n", N, bad);
}
