/* Key-schedule statistics (MEASUREMENT). K0 uniform (xorshift64 Fisher-Yates, seed from argv);
   K_s = F^s(K0), F = v12 PassKey. Prints raw counts for merging by keystats.py:
   T s i j   : #{K0 : the card at seat i of K0 is at seat j of K_s}   (s = 1,2,3)
   C s c i j : the same, split by card identity c, s = 1 only
   FX s f    : #{K0 : exactly f seats j with K_s[j] = K0[j]}           (s = 1,2,3)
   CY s k    : #{K0 : relative permutation i -> pos_{K_s}(K0[i]) has k cycles}
   H s h     : 64-bit hash of K_s's relative permutation, first 200000 samples (collision test) */
#include <stdio.h>
#include <stdlib.h>
#include "dd12.h"
static long T[4][52][52], CC[52][52][52], FX[4][53], CY[4][53];
int main(int argc, char **argv) { long n = atol(argv[1]); uint64_t st = seed_for(atol(argv[2]), 7, 11);
  int k[4][52], pos[52];
  FILE *hf = fopen(argv[3], "w");
  for (long t = 0; t < n; t++) { shuffle_(k[0], &st);
    for (int s = 1; s <= 3; s++) passkey12(k[s-1], k[s]);
    for (int s = 1; s <= 3; s++) { for (int j = 0; j < 52; j++) pos[k[s][j]] = j;
      int fx = 0, pi[52]; for (int i = 0; i < 52; i++) { int j = pos[k[0][i]]; pi[i] = j; T[s][i][j]++; if (s == 1) CC[k[0][i]][i][j]++; fx += (j == i); }
      FX[s][fx]++;
      int seen[52] = {0}, cyc = 0; for (int i = 0; i < 52; i++) if (!seen[i]) { cyc++; for (int x = i; !seen[x]; x = pi[x]) seen[x] = 1; }
      CY[s][cyc]++;
      if (t < 200000) { uint64_t h = 1469598103934665603ull; for (int i = 0; i < 52; i++) { h ^= pi[i]; h *= 1099511628211ull; } fprintf(hf, "%d %016llx\n", s, (unsigned long long)h); } } }
  fclose(hf);
  for (int s = 1; s <= 3; s++) { for (int i = 0; i < 52; i++) for (int j = 0; j < 52; j++) printf("T %d %d %d %ld\n", s, i, j, T[s][i][j]);
    for (int f = 0; f <= 52; f++) if (FX[s][f]) printf("FX %d %d %ld\n", s, f, FX[s][f]);
    for (int c = 0; c <= 52; c++) if (CY[s][c]) printf("CY %d %d %ld\n", s, c, CY[s][c]); }
  for (int c = 0; c < 52; c++) for (int i = 0; i < 52; i++) for (int j = 0; j < 52; j++) if (CC[c][i][j]) printf("C 1 %d %d %d %ld\n", c, i, j, CC[c][i][j]);
  return 0; }
