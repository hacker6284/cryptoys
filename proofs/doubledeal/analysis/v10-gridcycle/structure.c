/* Structural statistics of v10 GridCycle alone over random decks.
   [1] where input walk index p lands: P(output seat s <- input index p); largest entries.
   [2] overflow profile: P(overflow at walk index i), first-overflow index distribution.
   [3] positional swap diffusion: mean output weight and P(weight<=k) by first swapped index.
   usage: structure N seed */
#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
static long M[52][52], ovf[52], firstov[53], wsum[52], wcnt[52], wle[52][4];
int main(int argc, char **argv) {
    long N = atol(argv[1]); rs ^= strtoull(argv[2],0,10)*0x9E3779B97F4A7C15ULL;
    int d[52], e[52], s0[52], o0[52], o1[52];
    for (long n = 0; n < N; n++) {
        shuffle(d);
        uint8_t occ[52]; memset(occ, 0, 52);
        gc_walk(d, s0, 52);
        for (int i = 0; i < 52; i++) M[i][s0[i]]++;
        int fo = 52;
        for (int i = 1; i < 52; i++) {            /* overflow at i <=> seat_i != step target */
            int pc = d[i-1], pr = s0[i-1] / 13, pcc = s0[i-1] % 13;
            int tgt = ((pr + pc / 13) & 3) * 13 + (pcc + pc % 13 + 1) % 13;
            if (s0[i] != tgt) { ovf[i]++; if (fo == 52) fo = i; }
        }
        firstov[fo]++;
        gc_mix(d, o0);
        for (int k = 0; k < 20; k++) {            /* 20 random positional swaps per deck */
            int i = rnd() % 52, j = rnd() % 52; if (i == j) { k--; continue; }
            if (i > j) { int x = i; i = j; j = x; }
            memcpy(e, d, sizeof d); e[i] = d[j]; e[j] = d[i]; gc_mix(e, o1);
            int w = 0; for (int q = 0; q < 52; q++) w += o0[q] != o1[q];
            wsum[i] += w; wcnt[i]++;
            wle[i][0] += w <= 2; wle[i][1] += w <= 4; wle[i][2] += w <= 8; wle[i][3] += w <= 16;
        }
    }
    printf("[1] input walk index -> output seat: largest P(seat | index) per index (uniform would be 1/52 = 0.019)\n");
    for (int i = 0; i < 52; i++) { int best = 0; for (int s = 0; s < 52; s++) if (M[i][s] > M[i][best]) best = s;
        printf("  index %2d: max P = %.4f at seat %2d (r%d c%d)\n", i, (double)M[i][best] / N, best, best / 13, best % 13); }
    printf("[2] P(overflow at walk index i):\n ");
    long tot = 0; for (int i = 1; i < 52; i++) { printf(" %d:%.2f", i, (double)ovf[i] / N); tot += ovf[i]; }
    printf("\n  mean overflows per deck %.2f of 51 placements\n  first overflow index: ", (double)tot / N);
    long cum = 0; for (int i = 1; i <= 52; i++) { cum += firstov[i]; if (i <= 12 || i == 52) printf(" P(<=%d)=%.3f", i, (double)cum / N); }
    printf("\n[3] positional swap (i<j): by first index i: mean output weight, P(w<=2), P(w<=4), P(w<=8), P(w<=16)\n");
    for (int i = 0; i < 51; i++) printf("  i=%2d mean %.1f  %.3f %.3f %.3f %.3f\n", i, (double)wsum[i] / wcnt[i],
        (double)wle[i][0] / wcnt[i], (double)wle[i][1] / wcnt[i], (double)wle[i][2] / wcnt[i], (double)wle[i][3] / wcnt[i]);
    long W = 0, C = 0, L[4] = {0}; for (int i = 0; i < 51; i++) { W += wsum[i]; C += wcnt[i]; for (int k = 0; k < 4; k++) L[k] += wle[i][k]; }
    printf("  all uniform swaps: mean %.2f  P(w<=2) %.4f P(w<=4) %.4f P(w<=8) %.4f P(w<=16) %.4f  (random deck pair: mean 51)\n",
        (double)W / C, (double)L[0] / C, (double)L[1] / C, (double)L[2] / C, (double)L[3] / C);
}
