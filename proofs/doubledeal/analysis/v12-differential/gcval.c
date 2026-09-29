/* Validation of the MITM estimator on a toy with large DP: GridCycle alone, uniform key, GridCycle alone.
   usage: gcval f|b|d SPEC_A SPEC_B N SEED OUT  (f: forward keys from A; b: backward keys to B; d: direct count A->B) */
#include "ddiff.h"
int main(int argc, char **argv) { int A[52], Bt[52]; parse_rel(argv[2], A); parse_rel(argv[3], Bt); long n = atol(argv[4]);
  uint64_t st = seed_for(atol(argv[5]), 5, 9); char m = argv[1][0]; uint64_t *k = m == 'd' ? 0 : malloc(n * 8); long hit = 0;
  int x[52], xs[52], u[52], v[52], d[52], kk[52], p[52], q[52];
  for (long t = 0; t < n; t++) { shuffle_(x, &st);
    if (m == 'f') { rel(A, x, xs); mix_v11(x, u); mix_v11(xs, v); diff(u, v, d); k[t] = (hsh(d) & ~63ull) | support(d); }
    else if (m == 'b') { rel(Bt, x, xs); inv_mix_v11(x, u); inv_mix_v11(xs, v); diff(u, v, d); k[t] = (hsh(d) & ~63ull) | support(d); }
    else { rel(A, x, xs); mix_v11(x, u); mix_v11(xs, v); shuffle_(kk, &st); compose(u, kk, p); compose(v, kk, q);
      mix_v11(p, u); mix_v11(q, v); diff(u, v, d); hit += same(d, Bt); } }
  if (m == 'd') printf("direct %s -> %s: %ld of %ld = %.3e\n", argv[2], argv[3], hit, n, (double)hit / n);
  else { FILE *f = fopen(argv[6], "wb"); fwrite(k, 8, n, f); fclose(f); }
  return 0; }
