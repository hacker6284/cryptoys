/* One-round DP(alpha -> alpha) for the 312 same-suit swaps (MEASUREMENT, empirical only).
   usage: scan1 PART NPARTS N SEED ; prints: a b N count(dU = alpha) count(RoundChar) */
#include "ddiff.h"
int main(int argc, char **argv) { int part = atoi(argv[1]), np = atoi(argv[2]); long n = atol(argv[3]); int idx = 0;
  for (int su = 0; su < 4; su++) for (int r1 = 0; r1 < 13; r1++) for (int r2 = r1 + 1; r2 < 13; r2++, idx++) {
    if (idx % np != part) continue;
    int a = 13 * su + r1, b = 13 * su + r2, s[52];
    for (int i = 0; i < 52; i++) s[i] = i;
    s[a] = b; s[b] = a;
    uint64_t st = seed_for(atol(argv[4]), a, b); long cu = 0, crc = 0; int x[52], xs[52], p[52], q[52], u[52], v[52], d[52];
    for (long t = 0; t < n; t++) { shuffle_(x, &st); rel(s, x, xs); stem(x, p); stem(xs, q); mix_v11(p, u); mix_v11(q, v); diff(u, v, d);
      int iu = same(d, s); cu += iu; if (iu) { diff(p, q, d); crc += same(d, s); } }
    printf("%d %d %ld %ld %ld\n", a, b, n, cu, crc); fflush(stdout); }
  return 0; }
