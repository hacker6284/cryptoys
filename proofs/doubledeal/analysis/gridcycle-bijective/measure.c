/* Measurements for the GridCycle-replacement sketches (analysis only).
   usage:
     measure check  L N seed         round-trip + bijectivity on N random decks
     measure surv   L N seed         value-pair swap survival through layer L alone, all 1326 pairs, N decks/pair
     measure round  L N seed         same through one unkeyed full round: L(stem(d)) (stem = v10 SumRanks+ShiftRows)
     measure pair   L N seed a b R   one pair (R=0 layer, R=1 round), N decks
     measure spread L N seed         all 1326 position swaps x N decks: spread = #output seats that differ
     measure sym    L N seed         structured relabellings (suit perm x rank affine map) commuting on N decks
     measure vec    L N seed         print N (input, output) pairs for the Python cross-check
   Every deck stream is seeded from (seed, pair index), so output does not depend on thread count. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "layers.h"
static const char *CN = "A23456789TJQK", *SN = "CHSD";
static void cname(int c, char *b) { b[0] = CN[c % 13]; b[1] = SN[c / 13]; b[2] = 0; }
static void wilson(long h, long n, double *lo, double *hi) { double z = 1.96, p = (double)h / n, d = 1 + z*z/n,
    c = (p + z*z/(2*n)) / d, w = z * sqrt(p*(1-p)/n + z*z/(4.0*n*n)) / d; *lo = c - w; *hi = c + w; }
static uint64_t mkseed(uint64_t seed, uint64_t k) { uint64_t s = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ (k + 1) * 0xD1B54A32D192ED03ULL; for (int i = 0; i < 8; i++) rnd_(&s); return s ? s : 1; }
static void relab(const int *d, int *e, int a, int b) { for (int i = 0; i < 52; i++) e[i] = d[i] == a ? b : d[i] == b ? a : d[i]; }
static long pair_hits(LayerFn f, int R, int a, int b, long N, uint64_t s) {
    int d[52], e[52], x[52], y[52], o0[52], o1[52]; long h = 0;
    for (long n = 0; n < N; n++) { shuffle_(d, &s); relab(d, e, a, b);
        if (R) { stem(d, x); stem(e, y); f(x, o0); f(y, o1); } else { f(d, o0); f(e, o1); }
        int ok = 1; for (int i = 0; i < 52 && ok; i++) { int t = o0[i] == a ? b : o0[i] == b ? a : o0[i]; ok = t == o1[i]; }
        h += ok; }
    return h;
}
typedef struct { int a, b; long h; } PR;
static int cmppr(const void *x, const void *y) { long a = ((PR*)x)->h, b = ((PR*)y)->h; return (b > a) - (b < a); }
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: see header\n"); return 1; }
    const char *mode = argv[1]; int L = atoi(argv[2]); long N = atol(argv[3]); uint64_t seed = strtoull(argv[4], 0, 10);
    LayerFn f = LFWD[L], g = LINV[L];
    if (!strcmp(mode, "check")) {
        long bad = 0, notperm = 0; uint64_t s = mkseed(seed, 0); int d[52], o[52], b[52];
        for (long n = 0; n < N; n++) { shuffle_(d, &s); f(d, o); g(o, b); bad += memcmp(b, d, sizeof d) != 0;
            int seen[52] = {0}; for (int i = 0; i < 52; i++) { if (o[i] < 0 || o[i] > 51 || seen[o[i]]) { notperm++; break; } seen[o[i]] = 1; } }
        printf("%s check N=%ld seed=%llu: inverse failures %ld, non-permutation outputs %ld\n", LNAME[L], N, (unsigned long long)seed, bad, notperm);
    } else if (!strcmp(mode, "surv") || !strcmp(mode, "round")) {
        int R = mode[0] == 'r'; PR *pr = malloc(1326 * sizeof(PR)); int k = 0;
        for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) { pr[k].a = a; pr[k].b = b; k++; }
        #pragma omp parallel for schedule(dynamic)
        for (int q = 0; q < 1326; q++) pr[q].h = pair_hits(f, R, pr[q].a, pr[q].b, N, mkseed(seed, q));
        double sum = 0, cls[3] = {0}; int ncls[3] = {0}, over = 0;
        for (int q = 0; q < 1326; q++) { double p = (double)pr[q].h / N; sum += p; if (p > 1.0/64) over++;
            int c = pr[q].a % 13 == pr[q].b % 13 ? 0 : pr[q].a / 13 == pr[q].b / 13 ? 1 : 2; cls[c] += p; ncls[c]++; }
        qsort(pr, 1326, sizeof(PR), cmppr);
        printf("%s %s N=%ld/pair seed=%llu: mean %.3g (1/%.0f); pairs>1/64 %d; class means same-rank %.3g same-suit %.3g other %.3g\n",
            LNAME[L], R ? "one-round(L o stem)" : "layer-alone", N, (unsigned long long)seed, sum / 1326, 1326 / sum, over,
            cls[0]/ncls[0], cls[1]/ncls[1], cls[2]/ncls[2]);
        for (int q = 0; q < 8; q++) { char x[3], y[3]; double lo, hi; cname(pr[q].a, x); cname(pr[q].b, y); wilson(pr[q].h, N, &lo, &hi);
            printf("  #%d %s<->%s %ld/%ld = %.3g [%.3g, %.3g]%s\n", q + 1, x, y, pr[q].h, N, (double)pr[q].h / N, lo, hi,
                pr[q].h ? "" : ""); }
    } else if (!strcmp(mode, "pair")) {
        int a = atoi(argv[5]), b = atoi(argv[6]), R = atoi(argv[7]); int T = 8; long hs[8];
        #pragma omp parallel for
        for (int t = 0; t < T; t++) hs[t] = pair_hits(f, R, a, b, N / T, mkseed(seed, 100000 + t));
        long h = 0; for (int t = 0; t < T; t++) h += hs[t]; long NN = N / T * T; double lo, hi; wilson(h, NN, &lo, &hi); char x[3], y[3]; cname(a, x); cname(b, y);
        printf("%s %s %s<->%s N=%ld seed=%llu: %ld hits = %.3g [%.3g, %.3g]%s\n", LNAME[L], R ? "one-round" : "layer", x, y, NN,
            (unsigned long long)seed, h, (double)h / NN, lo, hi, h ? "" : " (0 hits: 95% upper bound ~3/N)");
    } else if (!strcmp(mode, "spread")) {
        long hist[53] = {0}; double byi[52] = {0}; long nbyi[52] = {0};
        #pragma omp parallel
        { long lh[53] = {0}; double lbyi[52] = {0}; long lnb[52] = {0};
          #pragma omp for schedule(dynamic)
          for (long n = 0; n < N; n++) { uint64_t s = mkseed(seed, n); int d[52], e[52], o0[52], o1[52]; shuffle_(d, &s); f(d, o0);
            for (int i = 0; i < 52; i++) for (int j = i + 1; j < 52; j++) { memcpy(e, d, sizeof d); e[i] = d[j]; e[j] = d[i]; f(e, o1);
                int sp = 0; for (int k = 0; k < 52; k++) sp += o0[k] != o1[k]; lh[sp]++; lbyi[i] += sp; lnb[i]++; } }
          #pragma omp critical
          { for (int k = 0; k < 53; k++) hist[k] += lh[k]; for (int i = 0; i < 52; i++) { byi[i] += lbyi[i]; nbyi[i] += lnb[i]; } } }
        long tot = 0; double m = 0; for (int k = 0; k < 53; k++) { tot += hist[k]; m += (double)k * hist[k]; }
        long c2 = hist[2], c4 = 0, c8 = 0, c16 = 0; for (int k = 0; k <= 16; k++) { if (k <= 4) c4 += hist[k]; if (k <= 8) c8 += hist[k]; c16 += hist[k]; }
        int mn = 0; while (!hist[mn]) mn++; long acc = 0; int med = 0, p1 = -1; for (int k = 0; k < 53; k++) { acc += hist[k]; if (p1 < 0 && acc >= tot / 100) p1 = k; if (acc >= tot / 2) { med = k; break; } }
        printf("%s spread N=%ld decks x 1326 swaps seed=%llu: mean %.2f median %d p1 %d min %d; share =2 %.5f <=4 %.5f <=8 %.5f <=16 %.5f\n",
            LNAME[L], N, (unsigned long long)seed, m / tot, med, p1, mn, (double)c2 / tot, (double)c4 / tot, (double)c8 / tot, (double)c16 / tot);
        printf("  mean by first position i:"); for (int i = 0; i <= 50; i += 5) printf(" i=%d:%.1f", i, byi[i] / nbyi[i]);
        printf("\n");
    } else if (!strcmp(mode, "sym")) {
        /* sigma(c) = suit' = P[suit], rank0' = (u*rank0 + a) mod 13; all 24*12*13 maps, identity excluded */
        int perms[24][4], np = 0; for (int p = 0; p < 256; p++) { int x[4] = {p & 3, (p >> 2) & 3, (p >> 4) & 3, (p >> 6) & 3};
            if (x[0] != x[1] && x[0] != x[2] && x[0] != x[3] && x[1] != x[2] && x[1] != x[3] && x[2] != x[3]) memcpy(perms[np++], x, sizeof x); }
        int tested = 0, commuting = 0, v10sym_comm = 0, v10sym_n = 0;
        for (int pi = 0; pi < 24; pi++) for (int u = 1; u < 13; u++) for (int a = 0; a < 13; a++) {
            int sg[52], isid = 1; for (int c = 0; c < 52; c++) { sg[c] = perms[pi][c / 13] * 13 + (u * (c % 13) + a) % 13; isid &= sg[c] == c; }
            if (isid) continue;
            tested++;
            /* v10Sym: GF(4)-label XOR x (a suit perm) with u = 1 */
            int isv10 = 0; if (u == 1) for (int x = 0; x < 4; x++) { int ok = 1; for (int s = 0; s < 4; s++) { int l = LABEL[s] ^ x, s2 = 0; while (LABEL[s2] != l) s2++; ok &= perms[pi][s] == s2; } isv10 |= ok; }
            uint64_t s = mkseed(seed, tested); int okall = 1;
            for (long n = 0; n < N && okall; n++) { int d[52], e[52], o0[52], o1[52]; shuffle_(d, &s); for (int i = 0; i < 52; i++) e[i] = sg[d[i]];
                f(d, o0); f(e, o1); for (int i = 0; i < 52; i++) if (sg[o0[i]] != o1[i]) { okall = 0; break; } }
            commuting += okall; if (isv10) { v10sym_n++; v10sym_comm += okall; } }
        printf("%s sym N=%ld seed=%llu: %d of %d structured relabellings commute on all N decks (v10Sym non-identity: %d of %d)\n",
            LNAME[L], N, (unsigned long long)seed, commuting, tested, v10sym_comm, v10sym_n);
    } else if (!strcmp(mode, "vec")) {
        uint64_t s = mkseed(seed, 0); int d[52], o[52];
        for (long n = 0; n < N; n++) { shuffle_(d, &s); f(d, o); for (int i = 0; i < 52; i++) printf("%d%c", d[i], i < 51 ? ',' : ' '); for (int i = 0; i < 52; i++) printf("%d%c", o[i], i < 51 ? ',' : '\n'); }
    }
    return 0;
}
