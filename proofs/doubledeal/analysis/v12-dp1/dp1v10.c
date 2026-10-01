/* One unkeyed v12 mix round U = GridCycle o stem: the v10Sym rows and columns of the
   one-round difference table T[alpha][beta] = #{x : U(alpha.x) = beta.U(x)} / 52!.
   MEASUREMENT, EMPIRICAL ONLY; no theorem uses these numbers.
   usage: dp1v10 r|k|c SPEC N SEED   (SPEC as ddiff.h parse_rel: "v10:A,X", "a,b" swap, ...)
     r: row    alpha = SPEC (here v10Sym A X); x uniform; beta = diff(U x, U(alpha.x)); P[beta] = T[alpha][beta].
        Also checks stem(alpha.x) = alpha.stem(x) on every sample (proved: unkeyedNoMix_rel_v10Sym).
     k: row alpha = SPEC restricted to the decks x whose stem output starts with K-clubs or
        K-spades (stem(x)[0] in {12, 38}; rejection sampling; N accepted decks). These are the
        first cards for which the proof's two-read argument (Lean, OneRoundDP) gives no factor.
     c: column beta = SPEC;  y uniform; gamma = diff(U^-1 y, U^-1(beta.y)); P[gamma] = T[gamma][beta].
   Each sampled difference is reduced to a 64-bit FNV-style hash (ddiff.h hsh). Equal hashes are
   counted as equal differences (a hash collision can only add a spurious repeat).
   If no hash repeats, then with 95% confidence (per run) every difference has
   probability < 4.744/N: a difference of probability p >= 4.744/N is drawn at most once
   with probability (1-p)^N + Np(1-p)^(N-1) <= (1+4.744) e^-4.744 = 0.05. */
#include "../v12-differential/ddiff.h"
static int is_v10(const int *g, int *pa, int *px) {   /* v10Sym a x is fixed by its image of card 0 (A-clubs) */
  int a = g[0] % 13, x = LAB_[g[0] / 13]; char sp[16]; int s[52];
  snprintf(sp, sizeof sp, "v10:%d,%d", a, x); parse_rel(sp, s);
  if (same(s, g)) { *pa = a; *px = x; return 1; }
  return 0; }
int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: dp1v10 r|k|c SPEC N SEED\n"); return 2; }
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
