/* M7 (EMPIRICAL ONLY; no theorem uses this): the final no-mix round without its keys
   (stem = lay, SumRanks, ShiftRows, scoop = Lean `unkeyedNoMix`) on input difference alpha,
   uniform deck x. Prints P[stem(alpha.x) = alpha.stem(x)], the number of distinct output
   differences (by 64-bit hash), the largest count of a single output difference, and the
   histogram of output-difference support sizes.
   usage: final1 SPEC N SEED */
#include "../v12-differential/ddiff.h"
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: final1 SPEC N SEED\n"); return 2; }
  int s[52]; parse_rel(argv[1], s); long n = atol(argv[2]); uint64_t st = seed_for(atol(argv[3]), 3, 17);
  uint64_t *h = malloc(n * 8); long same_ = 0, hist[53] = {0}; int x[52], xs[52], p[52], q[52], d[52];
  for (long t = 0; t < n; t++) { shuffle_(x, &st); rel(s, x, xs); stem(x, p); stem(xs, q); diff(p, q, d);
    int sm = 1; for (int c = 0; c < 52; c++) if (d[c] != s[c]) { sm = 0; break; }
    same_ += sm; hist[support(d)]++; h[t] = hsh(d); }
  qsort(h, n, 8, cmpu); long distinct = 0, best = 0, run = 0;
  for (long t = 0; t < n; t++) { if (t == 0 || h[t] != h[t-1]) { distinct++; run = 0; } run++; if (run > best) best = run; }
  printf("%s N=%ld P[gamma=alpha]=%.4e (%ld) distinct=%ld maxfreq=%ld supp:", argv[1], n, (double)same_/n, same_, distinct, best);
  for (int k = 0; k <= 52; k++) if (hist[k]) printf(" %d:%ld", k, hist[k]);
  printf("\n"); return 0; }
