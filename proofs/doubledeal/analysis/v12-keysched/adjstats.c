/* Adjacency preservation (MEASUREMENT): for uniform K0 and s = 1..6, the mean number of the 51
   top-to-bottom neighbour pairs (K0[i], K0[i+1]) that are neighbours (either order) in K_s = F^s(K0),
   and the mean number whose ordered offset pos_{K_s}(K0[i+1]) - pos_{K_s}(K0[i]) is +1 or -1 separately.
   Random-deck expectation: 51 * 2/52 = 1.9615 (either order). usage: adjstats N SEED */
#include <stdio.h>
#include <stdlib.h>
#include "dd12.h"
int main(int argc, char **argv) { long n = atol(argv[1]); uint64_t st = seed_for(atol(argv[2]), 5, 5);
  double adj[7] = {0}, fw[7] = {0}, bw[7] = {0}; long offc[7][103] = {{0}};
  int k[7][52], pos[52];
  for (long t = 0; t < n; t++) { shuffle_(k[0], &st);
    for (int s = 1; s <= 6; s++) { passkey12(k[s-1], k[s]); for (int j = 0; j < 52; j++) pos[k[s][j]] = j;
      for (int i = 0; i < 51; i++) { int d = pos[k[0][i+1]] - pos[k[0][i]]; offc[s][d + 51]++;
        if (d == 1) fw[s]++; if (d == -1) bw[s]++; if (d == 1 || d == -1) adj[s]++; } } }
  for (int s = 1; s <= 6; s++) { int best = 0; for (int d = 0; d < 103; d++) if (offc[s][d] > offc[s][best]) best = d;
    printf("s=%d mean adjacent %.4f (fwd %.4f, bwd %.4f); most common offset %+d with P=%.4f (uniform over the 102 nonzero offsets would be ~%.4f at small |d|)\n",
      s, adj[s] / n, fw[s] / n, bw[s] / n, best - 51, offc[s][best] / (51.0 * n), 1.0 / 51 * 51.0 / 52 * 1); }
  return 0; }
