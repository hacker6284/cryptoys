/* Phase 5: diffusion ("branch-number-style spread") of GridCycle alone (analysis only).
   Rules: 0 = v10, 33 = rule 1 (ghost + blocker sends you), 30 = rule 2 (ghost + row by blocker suit,
   start at target column). Reuses the Phase-2 walk from cand.c (v10 there is checked against gc.h).
   Output layout: out[seat] = card, seat = row*13+col (row-major, == gc.h / spec output index).
   spread(d,i,j) = #{k : GC(d)[k] != GC(d with positions i,j swapped)[k]}   (always >= 2: permutation)
   excess(d,i,j) = #{k : GC(d')[k] != tau(GC(d))[k]}, tau = swap the two card values; 0 <=> survival.
   Modes:
     dist  V N seed            all 1326 swaps of N random decks: histograms, per-i and per-(i,j) stats
     climb V kmax iters restarts seed [mingap]   hill-climb decks to minimise spread over swaps with i < kmax (and j-i >= mingap)
     cyc3  V N seed            random 3-cycles of positions (i<j<k, d[i]->j, d[j]->k, d[k]->i)
     merge V N seed            after the second swapped position, fraction of steps landing on the same seat
     x V < decks               cross-check dump (used by p5check.py)
     ideal N seed              reference: ideal one-pass layer (prefix 0..i-1 fixed, rest re-randomised)
                               and a fully random layer */
#define main cand_main
#include "cand.c"
#undef main
static void gcout(const int *d, int *out) { int s[52]; walk(d, s); for (int i = 0; i < 52; i++) out[s[i]] = d[i]; }
static int spread(const int *o0, const int *o1) { int n = 0; for (int k = 0; k < 52; k++) n += o0[k] != o1[k]; return n; }
static int excess(const int *o0, const int *o1, int a, int b) { int n = 0;
    for (int k = 0; k < 52; k++) { int t = o0[k] == a ? b : o0[k] == b ? a : o0[k]; n += o1[k] != t; } return n; }
static void pct(const long *h, int H, long tot, const char *tag) {
    long acc = 0; int p1 = -1, p10 = -1, p50 = -1, mn = -1, mx = 0; double s = 0;
    for (int v = 0; v < H; v++) { if (h[v] && mn < 0) mn = v; if (h[v]) mx = v; acc += h[v]; s += (double)v * h[v];
        if (p1 < 0 && acc >= tot * 0.01) p1 = v;
        if (p10 < 0 && acc >= tot * 0.10) p10 = v;
        if (p50 < 0 && acc >= tot * 0.5) p50 = v; }
    long le2 = h[2], le4 = h[2] + h[3] + h[4], le8 = 0; for (int v = 0; v <= 8; v++) le8 += h[v];
    printf("%s: cases %ld  min %d  p1 %d  p10 %d  median %d  mean %.2f  max %d  | spread=2 %.5f  <=4 %.5f  <=8 %.5f\n",
           tag, tot, mn, p1, p10, p50, s / tot, mx, (double)le2 / tot, (double)le4 / tot, (double)le8 / tot);
}
int main(int argc, char **argv) {
    counting = 0; char m = argv[1][0];
    int d[52], e[52], o0[52], o1[52];
    if (m == 'd') {
        V = atoi(argv[2]); long N = atol(argv[3]); rs ^= strtoull(argv[4],0,10)*0x9E3779B97F4A7C15ULL;
        static long H[53], H40[53], H20[53], HF[53], HN[53], E[53], Hi[52][53], ij2[52][52]; static double sij[52][52]; static int mij[52][52];
        for (int i = 0; i < 52; i++) for (int j = 0; j < 52; j++) mij[i][j] = 99;
        for (long n = 0; n < N; n++) { shuffle(d); gcout(d, o0);
            for (int i = 0; i < 52; i++) for (int j = i + 1; j < 52; j++) {
                memcpy(e, d, sizeof d); e[i] = d[j]; e[j] = d[i]; gcout(e, o1);
                int s = spread(o0, o1), x = excess(o0, o1, d[i], d[j]);
                if (s < 2 || (s == 2) != (x == 0)) { printf("INVARIANT FAILED\n"); return 1; }
                H[s]++; E[x]++; Hi[i][s]++; if (i < 40) H40[s]++; if (i < 20) H20[s]++; if (i < 20 && j - i > 16) HF[s]++; if (i < 40 && j - i <= 4) HN[s]++;
                sij[i][j] += s; if (s < mij[i][j]) mij[i][j] = s; ij2[i][j] += s == 2; } }
        printf("rule %d, %ld decks x 1326 swaps\n", V, N);
        pct(H, 53, N * 1326, "spread all swaps      ");
        long t40 = 0, t20 = 0; for (int v = 0; v < 53; v++) { t40 += H40[v]; t20 += H20[v]; }
        pct(H40, 53, t40, "spread swaps with i<40");
        pct(H20, 53, t20, "spread swaps with i<20");
        { long tf = 0, tn = 0; for (int v = 0; v < 53; v++) { tf += HF[v]; tn += HN[v]; }
          pct(HF, 53, tf, "spread i<20, gap j-i>16");
          pct(HN, 53, tn, "spread i<40, gap j-i<=4"); }
        { double s = 0; long z = E[0]; int mn = -1; for (int v = 0; v < 53; v++) { s += (double)v * E[v]; if (E[v] && mn < 0) mn = v; }
          printf("excess (vs survival prediction): zero (=survival) %.5f  mean %.2f\n", (double)z / (N * 1326), s / (N * 1326)); }
        printf("histogram spread: "); for (int v = 0; v < 53; v++) if (H[v]) printf("%d:%ld ", v, H[v]); printf("\n");
        printf("per i (over all j>i): i  min  mean  frac(spread=2)  ideal-one-pass mean ~ (52-i)-1\n");
        for (int i = 0; i < 51; i++) { long t = 0; double s = 0; int mn = -1; for (int v = 0; v < 53; v++) { t += Hi[i][v]; s += (double)v * Hi[i][v]; if (Hi[i][v] && mn < 0) mn = v; }
            printf("  i=%2d  min %2d  mean %5.2f  spread2 %.5f\n", i, mn, s / t, (double)Hi[i][2] / t); }
        printf("per (i,j) buckets of 4 positions: min spread / mean spread\n      ");
        for (int b = 0; b < 13; b++) printf("   j%2d-%2d  ", 4*b, 4*b+3);
        printf("\n");
        for (int a = 0; a < 13; a++) { printf("i%2d-%2d", 4*a, 4*a+3);
            for (int b = 0; b < 13; b++) { int mn = 99; double s = 0; long c = 0;
                for (int i = 4*a; i < 4*a+4; i++) for (int j = 4*b; j < 4*b+4; j++) if (j > i) { if (mij[i][j] < mn) mn = mij[i][j]; s += sij[i][j]; c += N; }
                if (c) printf("  %2d/%5.1f  ", mn, s / c); else printf("     -     "); } printf("\n"); }
        int bi = 0, bj = 0; long bc = -1; for (int i = 0; i < 40; i++) for (int j = i+1; j < 52; j++) if (ij2[i][j] > bc) { bc = ij2[i][j]; bi = i; bj = j; }
        printf("position pair with i<40 most often at spread 2: (%d,%d) %.5f; pair (50,51): %.5f\n", bi, bj, (double)bc / N, (double)ij2[50][51] / N);
        return 0;
    }
    if (m == 'c' && argv[1][1] == 'l') {
        V = atoi(argv[2]); int kmax = atoi(argv[3]); long iters = atol(argv[4]); int R = atoi(argv[5]); rs ^= strtoull(argv[6],0,10)*0x9E3779B97F4A7C15ULL;
        int best = 99, bd[52], bi = 0, bj = 0, mingap = argc > 7 ? atoi(argv[7]) : 1;
        for (int r = 0; r < R; r++) { shuffle(d);
            int cur = 99, cnt = 0, ci = 0, cj = 0;
            #define EVAL(D, MN, CT, I, J) { int oo[52], ee[52], o2[52]; gcout(D, oo); MN = 99; CT = 0; \
                for (int i = 0; i < kmax; i++) for (int j = i + mingap; j < 52; j++) { memcpy(ee, D, sizeof ee); ee[i] = D[j]; ee[j] = D[i]; gcout(ee, o2); \
                    int s = spread(oo, o2); if (s < MN) { MN = s; CT = 1; I = i; J = j; } else if (s == MN) CT++; } }
            EVAL(d, cur, cnt, ci, cj);
            for (long it = 0; it < iters && cur > 2; it++) { memcpy(e, d, sizeof d); int a = rnd() % 52, b = rnd() % 52; int x = e[a]; e[a] = e[b]; e[b] = x;
                int mn, ct, ii = 0, jj = 0; EVAL(e, mn, ct, ii, jj);
                if (mn < cur || (mn == cur && ct >= cnt)) { memcpy(d, e, sizeof d); cur = mn; cnt = ct; ci = ii; cj = jj; } }
            if (cur < best) { best = cur; memcpy(bd, d, sizeof d); bi = ci; bj = cj; }
            printf("rule %d kmax %d restart %d: min spread %d (swap %d,%d)\n", V, kmax, r, cur, ci, cj); fflush(stdout); }
        printf("RESULT rule %d, swaps with i<%d, gap>=%d: lowest spread found %d at swap (%d,%d) [upper bound on the true minimum]; deck:", V, kmax, mingap, best, bi, bj);
        for (int k = 0; k < 52; k++) printf(" %d", bd[k]);
        printf("\n");
        return 0;
    }
    if (m == 'c') {
        V = atoi(argv[2]); long N = atol(argv[3]); rs ^= strtoull(argv[4],0,10)*0x9E3779B97F4A7C15ULL;
        static long H[53], H40[53]; long t40 = 0;
        for (long n = 0; n < N; n++) { shuffle(d); gcout(d, o0);
            int p[3]; do { p[0] = rnd() % 52; p[1] = rnd() % 52; p[2] = rnd() % 52; } while (p[0] == p[1] || p[1] == p[2] || p[0] == p[2]);
            for (int a = 0; a < 3; a++) for (int b = a + 1; b < 3; b++) if (p[b] < p[a]) { int x = p[a]; p[a] = p[b]; p[b] = x; }
            memcpy(e, d, sizeof d); e[p[1]] = d[p[0]]; e[p[2]] = d[p[1]]; e[p[0]] = d[p[2]]; gcout(e, o1);
            int s = spread(o0, o1); H[s]++; if (p[0] < 40) { H40[s]++; t40++; } }
        printf("rule %d, %ld random (deck, position 3-cycle)\n", V, N);
        pct(H, 53, N, "3-cycle spread all     "); pct(H40, 53, t40, "3-cycle spread, i<40   ");
        printf("  spread=3 fraction (includes every case where the walk is unchanged): %.6f\n", (double)H[3] / N);
        return 0;
    }
    if (m == 'm') {   /* merge: after the second swapped position j, how often do the two walks use the same target / seat? */
        V = atoi(argv[2]); long N = atol(argv[3]); rs ^= strtoull(argv[4],0,10)*0x9E3779B97F4A7C15ULL;
        double sameS[4] = {0}, cnt[4] = {0}; int s0[52], s1[52];
        for (long n = 0; n < N; n++) { shuffle(d); walk(d, s0);
            for (int i = 0; i < 40; i++) for (int j = i + 1; j < 50; j++) { int g = j - i == 1 ? 0 : j - i <= 4 ? 1 : j - i <= 16 ? 2 : 3;
                memcpy(e, d, sizeof d); e[i] = d[j]; e[j] = d[i]; walk(e, s1);
                /* targets: recompute from the chooser state is intrusive; use seats of the walk and compare, and
                   for ghost rules the target after j is provably equal (sum of steps), so only seats are measured */
                for (int k = j + 1; k < 52; k++) { sameS[g] += s0[k] == s1[k]; cnt[g]++; } } }
        const char *nm[4] = {"gap 1", "gap 2-4", "gap 5-16", "gap >16"};
        printf("rule %d, %ld decks, swaps i<40, j<50: fraction of later steps (k>j) placed on the same seat in both walks\n", V, N);
        for (int g = 0; g < 4; g++) printf("  %-9s %.4f\n", nm[g], sameS[g] / cnt[g]);
        return 0;
    }
    if (m == 'x') {   /* cross-check: read decks from stdin, print the 1326 spreads (i<j order) per deck */
        V = atoi(argv[2]);
        while (1) { for (int k = 0; k < 52; k++) if (scanf("%d", &d[k]) != 1) return 0;
            gcout(d, o0);
            for (int i = 0; i < 52; i++) for (int j = i + 1; j < 52; j++) { memcpy(e, d, sizeof d); e[i] = d[j]; e[j] = d[i]; gcout(e, o1); printf("%d ", spread(o0, o1)); }
            printf("\n"); }
    }
    if (m == 'i') {
        long N = atol(argv[2]); rs ^= strtoull(argv[3],0,10)*0x9E3779B97F4A7C15ULL;
        /* fully random layer: out0, out1 independent uniform arrangements of the same 52 cards */
        static long H[53], Hi[52][53];
        for (long n = 0; n < N; n++) { shuffle(o0); shuffle(o1); H[spread(o0, o1)]++; }
        pct(H, 53, N, "ideal random layer, one swap");
        /* ideal one-pass layer: steps 0..i keep their seats (card at seat[i] changes), all later cards
           get independent uniform seats among the rest */
        for (long n = 0; n < N; n++) { int i = rnd() % 51, m2 = 51 - i, a[52], b[52];
            for (int k = 0; k < m2; k++) a[k] = b[k] = k;   /* cards of steps i+1..51 labelled 0..m2-1; label 0 = the moved card */
            /* deck 1 has card b_swapped in place of card a at label 0: treat label 0 as a different card */
            for (int k = m2 - 1; k > 0; k--) { int r = rnd() % (k+1), x = a[k]; a[k] = a[r]; a[r] = x; r = rnd() % (k+1); x = b[k]; b[k] = b[r]; b[r] = x; }
            int s = 1; for (int k = 0; k < m2; k++) s += a[k] != b[k] || a[k] == 0; Hi[i][s]++; }
        printf("ideal one-pass layer: mean spread by first swapped position i (min possible 2)\n");
        for (int i = 0; i < 51; i++) { long t = 0; double s = 0; for (int v = 0; v < 53; v++) { t += Hi[i][v]; s += (double)v * Hi[i][v]; } printf("  i=%2d mean %5.2f\n", i, s / t); }
        return 0;
    }
    return 1;
}
