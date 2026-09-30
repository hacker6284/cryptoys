/* One unkeyed v12 round, relabelling differences (MEASUREMENT, empirical only).
   usage: diff1 SPEC N SEED OUTFILE|-  [b]
   forward (default): x uniform, pair (x, s.x):
     dS = diff after stem (lay, SumRanks, ShiftRows, scoop: only SumRanks can change it),
     dM = diff after GridCycle ALONE applied to (x, s.x),
     dU = diff after the whole unkeyed round (stem then GridCycle).
   backward ("b"): z uniform, gamma = diff(U^-1 z, U^-1 (s.z)); P[gamma] = T[gamma][s] (DP of the round from gamma to s).
   Writes one uint64 key per sample for dU (forward) / gamma (backward): (hash & ~63) | support. */
#include "ddiff.h"
static void top(uint64_t *k, long n, const char *name, uint64_t selfkey) {
  qsort(k, n, 8, cmpu); long best[8] = {0}; uint64_t bk[8] = {0}; long distinct = 0, selfc = 0;
  for (long i = 0; i < n; ) { long j = i; while (j < n && k[j] == k[i]) j++; long c = j - i; distinct++;
    if (k[i] == selfkey) selfc = c;
    for (int t = 0; t < 8; t++) if (c > best[t]) { for (int u = 7; u > t; u--) { best[u] = best[u-1]; bk[u] = bk[u-1]; } best[t] = c; bk[t] = k[i]; break; }
    i = j; }
  printf("%s: distinct %ld of %ld; count(beta = input) %ld; top counts:", name, distinct, n, selfc);
  for (int t = 0; t < 8 && best[t]; t++) printf(" %ld(supp %d%s)", best[t], (int)(bk[t] & 63), bk[t] == selfkey ? ",=input" : "");
  printf("\n"); }
int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: diff1 SPEC N SEED OUTFILE|-  [b]\n"); return 2; }
  int s[52]; parse_rel(argv[1], s); long n = atol(argv[2]);
  uint64_t st = seed_for(atol(argv[3]), 7, 11); int back = argc > 5 && argv[5][0] == 'b';
  uint64_t selfkey = (hsh(s) & ~63ull) | support(s);
  uint64_t *kU = malloc(n * 8), *kS = back ? 0 : malloc(n * 8), *kM = back ? 0 : malloc(n * 8);
  long hS[53] = {0}, hM[53] = {0}, hU[53] = {0}, eqS = 0, eqM = 0, eqU = 0, rc = 0, eqUnotS = 0;
  int x[52], xs[52], a[52], b[52], u[52], v[52], d[52], dS[52];
  for (long t = 0; t < n; t++) { shuffle_(x, &st);
    if (back) { rel(s, x, xs); inv_unkeyed(x, a); inv_unkeyed(xs, b); diff(a, b, d); int sp = support(d); hU[sp]++;
      kU[t] = (hsh(d) & ~63ull) | sp; if (kU[t] == selfkey && same(d, s)) eqU++; continue; }
    rel(s, x, xs);
    stem(x, a); stem(xs, b); diff(a, b, dS); int sS = support(dS); hS[sS]++; int isS = same(dS, s); eqS += isS;
    kS[t] = (hsh(dS) & ~63ull) | sS;
    mix_v11(a, u); mix_v11(b, v); diff(u, v, d); int sU = support(d); hU[sU]++; int isU = same(d, s); eqU += isU;
    rc += isS && isU; eqUnotS += isU && !isS; kU[t] = (hsh(d) & ~63ull) | sU;
    mix_v11(x, u); mix_v11(xs, v); diff(u, v, d); int sM = support(d); hM[sM]++; eqM += same(d, s);
    kM[t] = (hsh(d) & ~63ull) | sM; }
  printf("spec %s N %ld seed %s mode %s\n", argv[1], n, argv[3], back ? "backward" : "forward");
  if (!back) {
    printf("P[dS = s] %ld  P[dM = s] (GridCycle alone) %ld  P[dU = s] %ld  RoundChar %ld  dU = s with dS != s %ld\n", eqS, eqM, eqU, rc, eqUnotS);
    printf("support hist dS:"); for (int i = 0; i <= 52; i++) if (hS[i]) printf(" %d:%ld", i, hS[i]); printf("\n");
    printf("support hist dM:"); for (int i = 0; i <= 52; i++) if (hM[i]) printf(" %d:%ld", i, hM[i]); printf("\n"); }
  else printf("P[gamma = s] %ld\n", eqU);
  printf("support hist %s:", back ? "gamma" : "dU"); for (int i = 0; i <= 52; i++) if (hU[i]) printf(" %d:%ld", i, hU[i]); printf("\n");
  if (strcmp(argv[4], "-")) { FILE *f = fopen(argv[4], "wb"); fwrite(kU, 8, n, f); fclose(f); }
  if (!back) { top(kS, n, "dS", selfkey); top(kM, n, "dM", selfkey); }
  top(kU, n, back ? "gamma" : "dU", selfkey);
  return 0; }
