/* xcheck helper. `vec N`: prints N random lines "key;plain;cipher;F(key);F^-1(F(key));" (seed 99).
   `vec -`: reads lines "key;plain" (52 comma-separated ids each) from stdin, prints the cipher. */
#include <stdio.h>
#include <stdlib.h>
#include "dd.h"
static void pr(const int *d) { for (int i = 0; i < 52; i++) printf("%d%c", d[i], i == 51 ? ';' : ','); }
int main(int argc, char **argv) { int k[52], p[52], c[52], f[52], g[52];
    if (argc > 1 && argv[1][0] == '-') {
        for (;;) { for (int i = 0; i < 52; i++) if (scanf(" %d%*[,;]", &k[i]) != 1) return 0;
            for (int i = 0; i < 52; i++) if (scanf(" %d%*[,;]", &p[i]) != 1) return 0;
            encrypt(p, k, c); pr(c); printf("\n"); } }
    long N = argc > 1 ? atol(argv[1]) : 200; uint64_t s = 99;
    for (long n = 0; n < N; n++) { shuffle_(k, &s); shuffle_(p, &s); encrypt(p, k, c); passkey(k, f); passkey_inv(f, g);
        pr(k); pr(p); pr(c); pr(f); pr(g); printf("\n"); } }
