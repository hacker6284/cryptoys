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
static const int LABEL[4] = {0, 2, 3, 1}, TW[4] = {0, 2, 3, 1};
static void stem(const int *m, int *out) {
    int g[4][13];
    for (int k = 0; k < 52; k++) g[k % 4][k / 4] = m[k];
    for (int a = 1; a <= 4; a++) { int i = a % 4, p = (i + 3) % 4, tot = 0, tmp[13];
        for (int j = 0; j < 13; j++) tot += (13 - j) * (g[p][j] % 13 + 1);
        int k = tot % 13; for (int j = 0; j < 13; j++) tmp[j] = g[i][(j + k) % 13]; memcpy(g[i], tmp, sizeof tmp); }
    for (int a = 1; a <= 13; a++) { int j = a % 13, p = (j + 12) % 13;
        int v = LABEL[g[1][p] / 13] ^ TW[LABEL[g[2][p] / 13]] ^ TW[TW[LABEL[g[3][p] / 13]]];
        int su = LABEL[g[0][j] / 13] ^ LABEL[g[1][j] / 13] ^ LABEL[g[2][j] / 13] ^ LABEL[g[3][j] / 13];
        int s = v ^ su, col[4]; for (int i = 0; i < 4; i++) col[i] = g[i][j];
        for (int i = 0; i < 4; i++) g[i][j] = col[((i - s) % 4 + 4) % 4]; }
    for (int i = 0; i < 4; i++) { int tmp[13]; for (int j = 0; j < 13; j++) tmp[j] = g[i][(j + i) % 13]; memcpy(g[i], tmp, sizeof tmp); }
    for (int c = 0, k = 0; c < 13; c++) for (int r = 0; r < 4; r++) out[k++] = g[r][c];
}
int main(int argc, char **argv) {
    V = atoi(argv[1]); long N = atol(argv[2]); rs ^= strtoull(argv[3],0,10)*0x9E3779B97F4A7C15ULL;
    int all = argc > 4;
    int d[52], e[52], x[52], y[52], s0[52], s1[52]; static long hs[52][52], hr[52][52];
    for (long n = 0; n < N; n++) {
        shuffle(d); int st = 0; stem(d, x); walkv(x, s0, 0); (void)st;
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
