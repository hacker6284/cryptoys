/* Exact count of labelled fleets (5,4,3a,3b,2) on a 10x10 grid: (1) no overlap (touching allowed),
   (2) no ship touching another, even diagonally.  128-bit masks. */
#include <stdio.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static u128 P[6][200], H[6][200]; static int NP[6];
static const int L[5] = {5, 4, 3, 3, 2};
static u128 bit(int c) { return ((u128)1) << c; }
static void gen(int len) {
  int k = 0;
  for (int h = 0; h < 2; h++)
    for (int r = 0; r < (h ? 10 : 11 - len); r++)
      for (int c = 0; c < (h ? 11 - len : 10); c++) {
        u128 m = 0, halo = 0;
        for (int i = 0; i < len; i++) {
          int rr = h ? r : r + i, cc = h ? c + i : c; m |= bit(rr * 10 + cc);
          for (int dr = -1; dr <= 1; dr++) for (int dc = -1; dc <= 1; dc++) {
            int a = rr + dr, b = cc + dc; if (a >= 0 && a < 10 && b >= 0 && b < 10) halo |= bit(a * 10 + b); }
        }
        P[len][k] = m; H[len][k] = halo; k++;
      }
  NP[len] = k;
}
int main(void) {
  for (int l = 2; l <= 5; l++) gen(l);
  unsigned long long tot[2] = {0, 0};
  for (int mode = 0; mode < 2; mode++) {
    unsigned long long cnt = 0;
    for (int a = 0; a < NP[5]; a++) { u128 o1 = P[5][a], f1 = mode ? H[5][a] : P[5][a];
     for (int b = 0; b < NP[4]; b++) { if (P[4][b] & f1) continue; u128 f2 = f1 | (mode ? H[4][b] : P[4][b]);
      for (int c = 0; c < NP[3]; c++) { if (P[3][c] & f2) continue; u128 f3 = f2 | (mode ? H[3][c] : P[3][c]);
       for (int d = 0; d < NP[3]; d++) { if (P[3][d] & f3) continue; u128 f4 = f3 | (mode ? H[3][d] : P[3][d]);
        for (int e = 0; e < NP[2]; e++) if (!(P[2][e] & f4)) cnt++; }}}}
    (void)0; tot[mode] = cnt;
  }
  unsigned long long all = (unsigned long long)NP[5] * NP[4] * NP[3] * NP[3] * NP[2];
  printf("placements per ship: 5:%d 4:%d 3:%d 2:%d  (independent tuples %llu)\n", NP[5], NP[4], NP[3], NP[2], all);
  printf("labelled fleets, no overlap (touching allowed): %llu  acceptance %.6f\n", tot[0], (double)tot[0] / all);
  printf("labelled fleets, no touching even diagonally:   %llu\n", tot[1]);
  return 0;
}
