/* Counterexample search for the covariant round conjecture (EMPIRICAL; no theorem uses it).
   Covariant sigma: exists tau with F(sigma.m) = tau.F(m) on every deck (F = unkeyed round body).
   tau is forced by one deck m1 (tau[F(m1)[k]] = F(sigma.m1)[k]); sigma is refuted if a further
   deck breaks F(sigma.m) = tau.F(m).  usage: covsearch FAMILY N SEED
   FAMILY: norm   = the 3744 maps (rank, label) -> (u*rank + a, A*label + b) (the normalizer of
                    v10Sym; true by the holomorph count, not a Lean theorem)
           prod   = N random (pi(rank), rho(label)), pi in S13, rho in S4 (labels)
           fiber  = N random maps with rank -> pi_label(rank), label -> rho(label) (per-suit rank perms)
           rand   = N uniform random sigma
           prime  = N random sigma of prime order p <= 47 that are not a transposition: p uniform
                    among the 15 primes, then c disjoint p-cycles, c uniform in 1..52/p (c >= 2
                    if p = 2), on a uniform random support (the cases of PrimeNonSwapCase)
           dbl    = ALL 812175 products (a b)(c d) of two disjoint transpositions (N ignored)
           cyc3   = ALL 44200 3-cycles (a b c) (N ignored) */
#include "../v12-differential/ddiff.h"
static int card_of(int rank, int lab) { return 13 * SOL_[lab] + rank; }
static int F_cov_refuted(const int *s, uint64_t *st, int ndecks, int *firstfail) {
  int m[52], sm[52], fm[52], fsm[52], tau[52];
  shuffle_(m, st); rel(s, m, sm); unkeyed(m, fm); unkeyed(sm, fsm); diff(fm, fsm, tau);
  for (int t = 1; t < ndecks; t++) { shuffle_(m, st); rel(s, m, sm); unkeyed(m, fm); unkeyed(sm, fsm);
    for (int k = 0; k < 52; k++) if (fsm[k] != tau[fm[k]]) { *firstfail = t; return 1; } }
  return 0; }
static int is_id(const int *s) { for (int i = 0; i < 52; i++) if (s[i] != i) return 0; return 1; }
static int is_v10(const int *s) { char sp[16]; int v[52];
  for (int a = 0; a < 13; a++) for (int x = 0; x < 4; x++) { snprintf(sp, sizeof sp, "v10:%d,%d", a, x); parse_rel(sp, v);
    if (same(s, v)) return 1; } return 0; }
int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: covsearch norm|dbl|cyc3|prime|prod|fiber|rand N SEED\n"); return 2; }
  const char *fam = argv[1]; long n = atol(argv[2]); uint64_t st = seed_for(atol(argv[3]), 5, 23);
  long tested = 0, refuted = 0, skipped = 0, hist[8] = {0}; int s[52];
  if (!strcmp(fam, "norm")) {
    static const int GL[6][4] = {{1,0,0,1},{0,1,1,0},{1,1,0,1},{1,0,1,1},{0,1,1,1},{1,1,1,0}};
    for (int u = 1; u < 13; u++) for (int g = 0; g < 6; g++) for (int a = 0; a < 13; a++) for (int b = 0; b < 4; b++) {
      for (int c = 0; c < 52; c++) { int r = c % 13, l = LAB_[c / 13], l0 = l & 1, l1 = l >> 1;
        int n0 = (GL[g][0] * l0 + GL[g][1] * l1) & 1, n1 = (GL[g][2] * l0 + GL[g][3] * l1) & 1;
        s[c] = card_of((u * r + a) % 13, (n0 | (n1 << 1)) ^ b); }
      if (is_id(s) || is_v10(s)) { skipped++; continue; }
      int ff = 0; tested++; if (F_cov_refuted(s, &st, 6, &ff)) { refuted++; hist[ff < 7 ? ff : 7]++; }
      else printf("NOT REFUTED: u=%d g=%d a=%d b=%d\n", u, g, a, b); } }
  else if (!strcmp(fam, "dbl") || !strcmp(fam, "cyc3")) { int three = !strcmp(fam, "cyc3");
    /* dbl: a < b, a < c < d, {c, d} disjoint from {a, b}; cyc3: a < b < c, orientation o */
    for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) for (int c = a + 1; c < 52; c++)
      for (int d = three ? 0 : c + 1; d < (three ? 2 : 52); d++) {
        if (c == b || (!three && d == b) || (three && c < b)) continue;
        for (int i = 0; i < 52; i++) s[i] = i;
        if (!three) { s[a] = b; s[b] = a; s[c] = d; s[d] = c; }
        else if (d == 0) { s[a] = b; s[b] = c; s[c] = a; }
        else { s[a] = c; s[c] = b; s[b] = a; }
        int ff = 0; tested++; if (F_cov_refuted(s, &st, 6, &ff)) { refuted++; hist[ff < 7 ? ff : 7]++; }
        else { printf("NOT REFUTED:"); for (int i = 0; i < 52; i++) printf(" %d", s[i]); printf("\n"); } } }
  else for (long t = 0; t < n; t++) {
    if (!strcmp(fam, "rand")) shuffle_(s, &st);
    else if (!strcmp(fam, "prime")) { static const int PR[15] = {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47};
      int p = PR[rnd_(&st) % 15], cmax = 52 / p, cmin = p == 2 ? 2 : 1;
      int c = cmin + (int)(rnd_(&st) % (uint64_t)(cmax - cmin + 1)), sh[52];
      shuffle_(sh, &st); for (int i = 0; i < 52; i++) s[i] = i;
      for (int q = 0; q < c; q++) for (int i = 0; i < p; i++) s[sh[q * p + i]] = sh[q * p + (i + 1) % p]; }
    else { int pi[4][13], rho[4]; for (int i = 0; i < 4; i++) rho[i] = i;
      for (int i = 3; i > 0; i--) { int j = (int)(rnd_(&st) % (uint64_t)(i + 1)), x = rho[i]; rho[i] = rho[j]; rho[j] = x; }
      for (int l = 0; l < 4; l++) { for (int i = 0; i < 13; i++) pi[l][i] = i;
        for (int i = 12; i > 0; i--) { int j = (int)(rnd_(&st) % (uint64_t)(i + 1)), x = pi[l][i]; pi[l][i] = pi[l][j]; pi[l][j] = x; }
        if (!strcmp(fam, "prod") && l > 0) memcpy(pi[l], pi[0], sizeof pi[0]); }
      for (int c = 0; c < 52; c++) { int r = c % 13, l = LAB_[c / 13]; s[c] = card_of(pi[l][r], rho[l]); } }
    if (is_id(s) || is_v10(s)) { skipped++; continue; }
    int ff = 0; tested++; if (F_cov_refuted(s, &st, 6, &ff)) { refuted++; hist[ff < 7 ? ff : 7]++; }
    else { printf("NOT REFUTED:"); for (int c = 0; c < 52; c++) printf(" %d", s[c]); printf("\n"); } }
  printf("family %s N %ld seed %s: tested %ld refuted %ld skipped(id/v10Sym) %ld; refuted at deck #:", fam, n, argv[3], tested, refuted, skipped);
  for (int i = 1; i < 8; i++) if (hist[i]) printf(" %d:%ld", i, hist[i]);
  printf("\n"); return 0; }
