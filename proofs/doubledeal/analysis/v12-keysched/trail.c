/* Constant-sigma characteristic under the REAL PassKey schedule vs independent keys (MEASUREMENT).
   Round i (i = 0, 1, 2) as in TrailBound.lean `rounds`/`Trail`: x_i = Compose(s_i, K_i), s_0 = y,
   s_{i+1} = GridCycle(stem(x_i)); RC_i = RoundChar(sigma, x_i).
   Real schedule: K_i = F^i(K0). K0 uniform is sampled as x_0 uniform (K0 <-> x_0 is a bijection for
   fixed y: K0[i] = pos_{x_0}(y[i])).  Independent control: K_1, K_2 fresh uniform.
   usage: trail SIGMA Y N SEED MARG
     SIGMA: "a,b" (value transposition) or "v10:a,x";  Y: "id" or a seed number (random fixed y)
     MARG=1: also count RC_1 on every sample (the marginal of round 1's event, not conditioned on RC_0).
   prints: N H0 H01real H012real H01ind M1real (M1real = #RC_1 real over all N, only if MARG) */
#include <stdio.h>
#include <stdlib.h>
#include "dd12.h"
static const int LAB[4] = {0, 2, 3, 1}, SOL[4] = {0, 3, 1, 2};
int main(int argc, char **argv) { int s[52], y[52]; for (int i = 0; i < 52; i++) s[i] = i;
  if (!strncmp(argv[1], "v10:", 4)) { int a, x; sscanf(argv[1] + 4, "%d,%d", &a, &x);
    for (int c = 0; c < 52; c++) s[c] = 13 * SOL[LAB[c / 13] ^ x] + (c % 13 + a) % 13; }
  else { int a, b; sscanf(argv[1], "%d,%d", &a, &b); s[a] = b; s[b] = a; }
  if (!strcmp(argv[2], "id")) { for (int i = 0; i < 52; i++) y[i] = i; }
  else { uint64_t ys = seed_for(atol(argv[2]), 99, 99); shuffle_(y, &ys); }
  long n = atol(argv[3]); uint64_t st = seed_for(atol(argv[4]), 1, 2), st2 = seed_for(atol(argv[4]), 3, 4);
  int marg = atoi(argv[5]);
  long H0 = 0, H01 = 0, H012 = 0, H01i = 0, M1 = 0;
  int x0[52], k0[52], k1[52], k2[52], s1[52], x1[52], s2[52], x2[52], pos[52], kr[52];
  for (long t = 0; t < n; t++) { shuffle_(x0, &st);
    int rc0 = roundchar(s, x0);
    if (!rc0 && !marg) continue;
    for (int j = 0; j < 52; j++) pos[x0[j]] = j;
    for (int i = 0; i < 52; i++) k0[i] = pos[y[i]];
    passkey12(k0, k1); unkeyed(x0, s1); compose(s1, k1, x1);
    int rc1 = roundchar(s, x1); M1 += rc1;
    if (!rc0) continue;
    H0++;
    if (rc1) { H01++; passkey12(k1, k2); unkeyed(x1, s2); compose(s2, k2, x2); H012 += roundchar(s, x2); }
    shuffle_(kr, &st2); compose(s1, kr, x1); H01i += roundchar(s, x1); }
  printf("%ld %ld %ld %ld %ld %ld\n", n, H0, H01, H012, H01i, marg ? M1 : -1L);
  return 0; }
