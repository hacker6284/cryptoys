/* DP_2(alpha -> beta) under independent uniform keys (MEASUREMENT, empirical only):
   DP_2 = sum_gamma T[alpha][gamma] T[gamma][beta]. F = forward keys of gamma ~ T[alpha][.],
   B = backward keys of gamma ~ T[.][beta] (diff1 ... b). Estimate = (#equal pairs) / (N_F N_B).
   usage: mitm F B KEYA KEYB   (KEYA/KEYB: keys of alpha and beta, hex, to split the terms) */
#include "ddiff.h"
static uint64_t *load(const char *p, long *n) { FILE *f = fopen(p, "rb"); fseek(f, 0, SEEK_END); *n = ftell(f) / 8; rewind(f);
  uint64_t *k = malloc(*n * 8); if (fread(k, 8, *n, f) != (size_t)*n) exit(1); fclose(f); qsort(k, *n, 8, cmpu); return k; }
int main(int argc, char **argv) { long nf, nb; uint64_t *F = load(argv[1], &nf), *B = load(argv[2], &nb);
  uint64_t ka = strtoull(argv[3], 0, 16), kb = strtoull(argv[4], 0, 16);
  double tot = 0, ta = 0, tb = 0; long ncommon = 0, pairs_other = 0; long hsupp[53] = {0};
  long i = 0, j = 0;
  while (i < nf && j < nb) { if (F[i] < B[j]) { i++; continue; } if (F[i] > B[j]) { j++; continue; }
    uint64_t k = F[i]; long ci = 0, cj = 0; while (i < nf && F[i] == k) { i++; ci++; } while (j < nb && B[j] == k) { j++; cj++; }
    double m = (double)ci * cj; tot += m; ncommon++;
    if (k == ka) ta += m; else if (k == kb) tb += m; else { pairs_other += ci * cj; hsupp[k & 63] += ci * cj; } }
  double nn = (double)nf * nb;
  printf("NF %ld NB %ld common-keys %ld pairs %.0f est %.3e | gamma=alpha pairs %.0f (%.3e) | gamma=beta pairs %.0f (%.3e) | other pairs %ld (%.3e)\n",
    nf, nb, ncommon, tot, tot / nn, ta, ta / nn, tb, tb / nn, pairs_other, pairs_other / nn);
  printf("other pairs by support of gamma:"); for (int s = 0; s <= 52; s++) if (hsupp[s]) printf(" %d:%ld", s, hsupp[s]); printf("\n");
  return 0; }
