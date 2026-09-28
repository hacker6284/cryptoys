/* One unkeyed v10 round (lay_cm, SumRanks v10, ShiftRows, scoop_cm, GridCycle variant) and
   per-value-pair survival P_d[round(tau d) == tau round(d)]. Compose commutes with every
   relabelling, so this equals the keyed-round survival for any key.
   Only same-suit pairs are run by default: v10 SumRanks lets only same-suit pairs through
   (analysis/v10-sumranks: same-rank / other pairs 0 hits in 200k decks per pair).
   usage: round V N seed [all]   (V as in variants.c; 0 = v10) */
#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#define main variants_main
#include "variants.c"
#undef main
#include "stem.h"   /* same stem as cand.c */
int main(int argc, char **argv) {
    V = atoi(argv[1]); long N = atol(argv[2]); rs ^= strtoull(argv[3],0,10)*0x9E3779B97F4A7C15ULL;
    int all = argc > 4;
    int d[52], e[52], x[52], y[52], s0[52], s1[52]; static long hs[52][52], hr[52][52];
    for (long n = 0; n < N; n++) {
        shuffle(d); stem(d, x); walkv(x, s0, 0);
        for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) {
            if (!all && a / 13 != b / 13) continue;
            for (int i = 0; i < 52; i++) e[i] = d[i] == a ? b : d[i] == b ? a : d[i];
            stem(e, y); int ok = 1;
            for (int i = 0; i < 52; i++) { int t = x[i] == a ? b : x[i] == b ? a : x[i]; if (y[i] != t) { ok = 0; break; } }
            if (!ok) continue;
            hs[a][b]++;
            walkv(y, s1, 0); if (!memcmp(s0, s1, sizeof s0)) hr[a][b]++;
        }
    }
    for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) if (all || a / 13 == b / 13)
        printf("%d %d %ld %ld %ld\n", a, b, hs[a][b], hr[a][b], N);
}
