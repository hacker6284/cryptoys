/* One unkeyed v12 round, relabelling differences (MEASUREMENT, empirical only).
   usage: diff1 SPEC N SEED OUTFILE|-  [b]
   forward (default): x uniform, pair (x, s.x):
     dS = diff after stem (lay, SumRanks, ShiftRows, scoop: only SumRanks can change it),
     dM = diff after GridCycle ALONE applied to (x, s.x),
     dU = diff after the whole unkeyed round (stem then GridCycle).
   backward ("b"): z uniform, gamma = diff(U^-1 z, U^-1 (s.z)); P[gamma] = T[gamma][s] (DP of the round from gamma to s).
   Writes one uint64 key per sample for dU (forward) / gamma (backward): (hash & ~63) | support.
   usage: diff1 SPEC N SEED - r|k|c   (repeat statistics for one row or column; v12-dp1)
     r: row    alpha = SPEC; x uniform; beta = diff(U x, U(alpha.x)); P[beta] = T[alpha][beta].
        Also checks stem(alpha.x) = alpha.stem(x) on every sample (for SPEC in v10Sym this is
        proved: unkeyedNoMix_rel_v10Sym).
     k: row alpha = SPEC restricted to the decks x whose stem output starts with K-clubs or
        K-spades (stem(x)[0] in {12, 38}; rejection sampling; N accepted decks). These are the
        first cards for which the two-read argument of OneRoundDP gives no factor.
     c: column beta = SPEC; y uniform; gamma = diff(U^-1 y, U^-1(beta.y)); P[gamma] = T[gamma][beta].
   Each sampled difference is reduced to a 64-bit hash (ddiff.h hsh). Equal hashes are counted
   as equal differences (a hash collision can only add a spurious repeat). If no hash repeats,
   then with 95% confidence (per run) every difference has probability < 4.744/N: a difference
   of probability p >= 4.744/N is drawn at most once with probability
   (1-p)^N + Np(1-p)^(N-1) <= (1+4.744) e^-4.744 = 0.05. Prints distinct / repeat pairs / max
   multiplicity, and the support and agreement-with-SPEC histograms. The seed stream of these
   modes is its own (seed_for(SEED, hash(SPEC) [+100 for c], 17)), independent of the default modes. */
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
static int is_v10(const int *g, int *pa, int *px) {   /* v10Sym a x is fixed by its image of card 0 (A-clubs) */
  int a = g[0] % 13, x = LAB_[g[0] / 13]; char sp[16]; int s[52];
  snprintf(sp, sizeof sp, "v10:%d,%d", a, x); parse_rel(sp, s);
  if (same(s, g)) { *pa = a; *px = x; return 1; }
  return 0; }
static int dp1stats(int argc, char **argv) {   /* argv: prog r|k|c SPEC N SEED */
  (void)argc;
  int kmode = argv[1][0] == 'k', row = argv[1][0] == 'r' || kmode; const char *sp = argv[2]; long n = atol(argv[3]); int s[52]; parse_rel(sp, s);
  uint64_t sh = 0; for (const char *q = sp; *q; q++) sh = sh * 131 + (unsigned char)*q;
  uint64_t st = seed_for(atol(argv[4]), sh + (row ? 0 : 100), 17);
  uint64_t *k = malloc(n * 8); long hsup[53] = {0}, hagree[53] = {0}, stemfail = 0, diag = 0, inv10 = 0;
  int x[52], xs[52], a[52], b[52], u[52], v[52], d[52], sa[52];
  long tries = 0;
  for (long t = 0; t < n; t++) { shuffle_(x, &st); rel(s, x, xs); tries++;
    if (kmode) { stem(x, a); if (a[0] != 12 && a[0] != 38) { t--; continue; } }
    if (row) { stem(x, a); stem(xs, b); rel(s, a, sa); if (!same(sa, b)) stemfail++;
      mix_v11(a, u); mix_v11(b, v); diff(u, v, d); }
    else { inv_unkeyed(x, a); inv_unkeyed(xs, b); diff(a, b, d); }
    int sp_ = support(d); hsup[sp_]++; int ag = 0; for (int c = 0; c < 52; c++) ag += d[c] == s[c]; hagree[ag]++;
    if (same(d, s)) diag++;
    if (!row) { int pa, px; if (sp_ >= 40 && is_v10(d, &pa, &px)) inv10++; }
    k[t] = hsh(d); }
  qsort(k, n, 8, cmpu); long distinct = 0, pairs = 0, maxm = 0;
  for (long i = 0; i < n; ) { long j = i; while (j < n && k[j] == k[i]) j++; long m = j - i; distinct++;
    pairs += m * (m - 1) / 2; if (m > maxm) maxm = m; i = j; }
  int minsup = 52; for (int i = 0; i <= 52; i++) if (hsup[i]) { minsup = i; break; }
  int maxag = 0; for (int i = 0; i <= 52; i++) if (hagree[i]) maxag = i;
  printf("%s %s N %ld (tries %ld): distinct %ld repeats(pairs) %ld max-multiplicity %ld min-support %d "
         "max-agree-with-SPEC %d diff=SPEC %ld", kmode ? "row|first in {KC,KS}" : row ? "row" : "col", sp, n, tries, distinct, pairs, maxm,
         minsup, maxag, diag);
  if (row) printf(" stem-check-failures %ld", stemfail); else printf(" gamma-in-v10Sym %ld", inv10);
  printf("\n  support hist:"); for (int i = 0; i <= 52; i++) if (hsup[i]) printf(" %d:%ld", i, hsup[i]);
  printf("\n  agree hist:"); for (int i = 0; i <= 52; i++) if (hagree[i]) printf(" %d:%ld", i, hagree[i]);
  printf("\n"); return 0; }
int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: diff1 SPEC N SEED OUTFILE|-  [b|r|k|c]\n"); return 2; }
  if (argc > 5 && argv[5][1] == 0 && (argv[5][0] == 'r' || argv[5][0] == 'k' || argv[5][0] == 'c')) {
    char *av[5] = {argv[0], argv[5], argv[1], argv[2], argv[3]}; return dp1stats(5, av); }
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
