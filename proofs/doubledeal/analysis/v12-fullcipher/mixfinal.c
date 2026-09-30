/* M7 (EMPIRICAL ONLY; no theorem uses this): independent uniform keys, one mix round then
   the final no-mix round. Markov sampling, valid under independent uniform keys by
   `fullDiffCount_eq` (M7) and `diffCount_succ` (M6): x uniform, beta = difference after the
   unkeyed mix round, fresh uniform w, test stem(beta.w) == alpha.stem(w).
   usage: mixfinal SPEC N SEED ; prints N, hits, hits with beta == alpha, count(beta == alpha) */
#include "../v12-differential/ddiff.h"
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: mixfinal SPEC N SEED\n"); return 2; }
  int s[52]; parse_rel(argv[1], s); long n = atol(argv[2]); uint64_t st = seed_for(atol(argv[3]), 13, 29);
  long hit = 0, hitA = 0, nA = 0; int x[52], xs[52], u[52], v[52], b[52], w[52], bw[52], p[52], q[52], sp[52];
  for (long t = 0; t < n; t++) { shuffle_(x, &st); rel(s, x, xs); unkeyed(x, u); unkeyed(xs, v); diff(u, v, b);
    int isA = 1; for (int c = 0; c < 52; c++) if (b[c] != s[c]) { isA = 0; break; } nA += isA;
    shuffle_(w, &st); rel(b, w, bw); stem(w, p); stem(bw, q); rel(s, p, sp);
    if (same(q, sp)) { hit++; hitA += isA; } }
  printf("%s N=%ld hits=%ld hits_via_beta_eq_alpha=%ld beta_eq_alpha=%ld\n", argv[1], n, hit, hitA, nA); return 0; }
