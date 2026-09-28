/* Phase 2: GridCycle candidate rules (analysis only; nothing here is the spec).
   A candidate is a "chooser": given the occupancy, a small state and the card just placed, it
   picks the seat of the next card. The chooser sees only things the inverse also knows (placed
   cards, their seats, the state), so the inverse is the same replay with visited marks; the
   stats mode checks invMix(Mix(d)) == d.

   State: finger (fr,fc) = where the next step starts; t = marker chip (0..3); aux = extra.
   Variants:
     0  v10: step from the card's seat; overflow = marker row t, first free from blocked column,
        marker +1 (row full -> marker +1, next row).
     7  Phase-1 option C (row t+suit, count rank free seats) for reference.
    20  GHOST: the finger always moves to the TARGET seat, even when the card is bumped
        (next step starts from the target). Overflow as v10.
    21  GHOST + overflow scans the target's own row (then next rows), no marker.
    22  GHOST + overflow row = marker + suit, marker +1.
   (more variants are added below with their own comments)
   usage: cand V value N seed | cand V stats N seed | cand V cyc3 N seed N2 | cand V round N seed */
#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
typedef struct { int fr, fc, t, aux; } St;
static int V;
static long scanN, scanMax, scanHist[64]; static int counting = 1;
/* scan helper: rows starting at `row`, each from column c0 rightward with wrap, taking the k-th
   free seat (k>=1); rows advance by +1; if mark!=0 the marker advances once per row tried
   (v10 semantics: advance after use, and past full rows). Returns seat. */
static int scan_rows(const uint8_t *occ, int row, int c0, int k, int *t, int mark, int *steps) {
    int cnt = 0;
    for (;;) {
        for (int a = 0; a < 4; a++) {
            int rr = (row + a) & 3;
            for (int q = 0; q < 13; q++) { int cc = (c0 + q) % 13; (*steps)++;
                if (!occ[rr*13+cc] && ++cnt == k) { if (mark) *t = (*t + a + 1) & 3; return rr*13+cc; } }
        }
    }
}
static int choose(const uint8_t *occ, const int *g, St *S, int pc) {
    int s = pc / 13, rk = pc % 13 + 1;
    int tr = (S->fr + s) & 3, tc = (S->fc + rk) % 13, tgt = tr*13+tc, seat, steps = 0;
    int ghost = V >= 20 && V != 24 && V != 35;
    if (!occ[tgt]) seat = tgt;
    else switch (V) {
        case 0: case 20: seat = scan_rows(occ, S->t, tc, 1, &S->t, 1, &steps); break;
        case 7: { int t0 = S->t; seat = scan_rows(occ, (t0 + s) & 3, tc, rk, &S->t, 0, &steps); S->t = (t0 + 1) & 3; } break;
        case 21: seat = scan_rows(occ, tr, tc, 1, &S->t, 0, &steps); break;
        case 22: { int t0 = S->t; seat = scan_rows(occ, (t0 + s) & 3, tc, 1, &S->t, 0, &steps); S->t = (t0 + 1) & 3; } break;
        case 23: case 24: case 25: case 26: {
            /* hop: from the blocked target, step by the OCCUPANT's (suit, rank); up to H hops
               (23/24: H=1, 25: H=2); if still blocked, scan as named. 23,25 = ghost + v10 scan
               from the last hop's column; 24 = no ghost, v10 scan; 26 = ghost + row (marker+suit). */
            int H = V == 25 ? 2 : 1, hr = tr, hc = tc, got = -1;
            for (int h = 0; h < H && got < 0; h++) { int o = g[hr*13+hc]; hr = (hr + o / 13) & 3; hc = (hc + o % 13 + 1) % 13;
                steps++; if (!occ[hr*13+hc]) got = hr*13+hc; }
            if (got >= 0) seat = got;
            else if (V == 26) { int t0 = S->t; seat = scan_rows(occ, (t0 + s) & 3, hc, 1, &S->t, 0, &steps); S->t = (t0 + 1) & 3; }
            else seat = scan_rows(occ, S->t, hc, 1, &S->t, 1, &steps);
        } break;
        case 27: case 28: case 29: case 30: {
            /* 27: ghost + hop once by the occupant's step; if blocked, scan the HOP seat's own row
                   from the hop column (then next rows); no marker.
               28: as 27 but the scan row is marker + suit(occupant of the hop seat), marker +1.
               29: as 27 with up to two hops.
               30: no hop: scan row = marker + suit(occupant of the blocked target), from the
                   target column; marker +1. (ghost) */
            int hr = tr, hc = tc, got = -1, H = V == 29 ? 2 : V == 30 ? 0 : 1;
            for (int h = 0; h < H && got < 0; h++) { int o = g[hr*13+hc]; hr = (hr + o / 13) & 3; hc = (hc + o % 13 + 1) % 13;
                steps++; if (!occ[hr*13+hc]) got = hr*13+hc; }
            if (got >= 0) seat = got;
            else if (V == 27 || V == 29) seat = scan_rows(occ, hr, hc, 1, &S->t, 0, &steps);
            else { int t0 = S->t, o = g[hr*13+hc]; seat = scan_rows(occ, (t0 + o / 13) & 3, hc, 1, &S->t, 0, &steps); S->t = (t0 + 1) & 3; }
        } break;
        case 31: case 33: case 35: {
            /* 31: ghost + hop once; if blocked, scan row marker + suit(occupant of the TARGET)
                   from the hop column; marker +1.
               33: ghost, no separate hop check: scan row marker + suit(o) starting at column
                   target column + rank(o), o = occupant of the target; marker +1.
               35: as 33 without the ghost (finger moves to where the card landed). */
            int o = g[tgt], hr = (tr + o / 13) & 3, hc = (tc + o % 13 + 1) % 13, t0 = S->t;
            if (V == 31) { steps++; if (!occ[hr*13+hc]) { seat = hr*13+hc; break; } }
            seat = scan_rows(occ, (t0 + o / 13) & 3, hc, 1, &S->t, 0, &steps); S->t = (t0 + 1) & 3;
        } break;
        default: fprintf(stderr, "unknown variant\n"); exit(1);
    }
    if (steps && counting) { scanHist[steps < 63 ? steps : 63]++; scanN += steps; if (steps > scanMax) scanMax = steps; }
    if (ghost) { S->fr = tr; S->fc = tc; } else { S->fr = seat / 13; S->fc = seat % 13; }
    return seat;
}
static int walk(const int *d, int *seat) {
    uint8_t occ[52]; memset(occ, 0, 52); St S = {2, 0, 0, 0}; int nov = 0, g[52];
    for (int i = 0; i < 52; i++) {
        int cur;
        if (i == 0) cur = 26;
        else { int pc = d[i-1]; int tgt = ((S.fr + pc / 13) & 3) * 13 + (S.fc + pc % 13 + 1) % 13;
               cur = choose(occ, g, &S, pc); nov += cur != tgt; }
        occ[cur] = 1; seat[i] = cur; g[cur] = d[i];
    }
    return nov;
}
static void inv_mix(const int *out, int *hand) {
    uint8_t vis[52]; memset(vis, 0, 52); St S = {2, 0, 0, 0};
    for (int i = 0; i < 52; i++) { int cur = i == 0 ? 26 : choose(vis, out, &S, hand[i-1]); vis[cur] = 1; hand[i] = out[cur]; }
}
/* ---- v10 stem (lay_cm, SumRanks v10, ShiftRows, scoop_cm), checked against ddport by candcheck.py ---- */
static const int LABEL[4] = {0, 2, 3, 1}, TW[4] = {0, 2, 3, 1};
static void stem(const int *m, int *out) {
    int g[4][13];
    for (int k = 0; k < 52; k++) g[k % 4][k / 4] = m[k];
    for (int a = 1; a <= 4; a++) { int i = a % 4, p = (i + 3) % 4, tot = 0, tmp[13];
        for (int j = 0; j < 13; j++) tot += (13 - j) * (g[p][j] % 13 + 1);
        int k = tot % 13; for (int j = 0; j < 13; j++) tmp[j] = g[i][(j + k) % 13]; memcpy(g[i], tmp, sizeof tmp); }
    for (int a = 1; a <= 13; a++) { int j = a % 13, p = (j + 12) % 13;
        int v = LABEL[g[1][p] / 13] ^ TW[LABEL[g[2][p] / 13]] ^ TW[TW[LABEL[g[3][p] / 13]]];
        int su = LABEL[g[0][j] / 13] ^ LABEL[g[1][j] / 13] ^ LABEL[g[2][j] / 13] ^ LABEL[g[3][j] / 13];
        int sh = v ^ su, col[4]; for (int i = 0; i < 4; i++) col[i] = g[i][j];
        for (int i = 0; i < 4; i++) g[i][j] = col[((i - sh) % 4 + 4) % 4]; }
    for (int i = 0; i < 4; i++) { int tmp[13]; for (int j = 0; j < 13; j++) tmp[j] = g[i][(j + i) % 13]; memcpy(g[i], tmp, sizeof tmp); }
    for (int c = 0, k = 0; c < 13; c++) for (int r = 0; r < 4; r++) out[k++] = g[r][c];
}
static void swapv(const int *d, int *e, int a, int b) { for (int i = 0; i < 52; i++) e[i] = d[i] == a ? b : d[i] == b ? a : d[i]; }
static long cyc_run(int a, int b, int c, long N) {
    int d[52], e[52], s0[52], s1[52]; long h = 0;
    for (long n = 0; n < N; n++) { shuffle(d); walk(d, s0);
        for (int i = 0; i < 52; i++) e[i] = d[i] == a ? b : d[i] == b ? c : d[i] == c ? a : d[i];
        walk(e, s1); h += !memcmp(s0, s1, sizeof s0); }
    return h;
}
typedef struct { int a, b, c; long h; } Cy;
static int cmpcy(const void *x, const void *y) { long a = ((Cy*)x)->h, b = ((Cy*)y)->h; return (b > a) - (b < a); }
int main(int argc, char **argv) {
    V = atoi(argv[1]); char mode = argv[2][0]; char mode2 = argv[2][1]; long N = atol(argv[3]);
    rs ^= strtoull(argv[4],0,10)*0x9E3779B97F4A7C15ULL;
    int d[52], e[52], s0[52], s1[52], x[52], y[52];
    if (mode == 's' && mode2 == 't') {           /* stats */
        long nov = 0, invbad = 0, bad = 0;
        for (long n = 0; n < N; n++) { shuffle(d); nov += walk(d, s0);
            uint8_t seen[52] = {0}; for (int i = 0; i < 52; i++) { bad += seen[s0[i]]; seen[s0[i]] = 1; }
            int out[52], back[52]; for (int i = 0; i < 52; i++) out[s0[i]] = d[i];
            counting = 0; inv_mix(out, back); counting = 1; invbad += memcmp(back, d, sizeof d) != 0; }
        long tot = 0, acc = 0; int p50 = 0, p90 = 0, p99 = 0; for (int i = 0; i < 64; i++) tot += scanHist[i];
        for (int i = 0; i < 64; i++) { acc += scanHist[i]; if (!p50 && acc >= tot / 2) p50 = i; if (!p90 && acc >= tot * 0.9) p90 = i; if (!p99 && acc >= tot * 0.99) p99 = i; }
        printf("variant %d: seats inspected per overflow p50 %d p90 %d p99 %d; ", V, p50, p90, p99); fflush(stdout);
        printf("overflows/deck %.2f; seats inspected per overflow mean %.2f max %ld; per GridCycle %.0f; "
               "non-bijective %ld; inverse failures %ld/%ld\n", (double)nov / N, (double)scanN / nov, scanMax,
               (double)scanN / N, bad, invbad, N);
        return 0;
    }
    if (mode == 'v') {                            /* value-pair survival */
        static long h[52][52]; int where[52];
        for (long n = 0; n < N; n++) { shuffle(d); walk(d, s0); for (int i = 0; i < 52; i++) where[d[i]] = i;
            for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) {
                memcpy(e, d, sizeof d); e[where[a]] = b; e[where[b]] = a;
                walk(e, s1); h[a][b] += !memcmp(s0, s1, sizeof s0); } }
        for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) printf("%d %d %ld %ld\n", a, b, h[a][b], N);
        return 0;
    }
    if (mode == 'c') {                            /* all 3-cycles: screen, refine top 10 */
        long N2 = atol(argv[5]); static Cy cy[44200]; int n = 0;
        for (int a = 0; a < 52; a++) for (int b = a+1; b < 52; b++) for (int c = a+1; c < 52; c++) if (c != b)
            { cy[n] = (Cy){a, b, c, cyc_run(a, b, c, N)}; n++; }
        qsort(cy, n, sizeof(Cy), cmpcy);
        const char *R = "A23456789TJQK", *SU = "CHSD"; long tot = 0; for (int i = 0; i < n; i++) tot += cy[i].h;
        printf("variant %d: %d 3-cycles, screen N=%ld: mean %.4f, max screen %.4f\n", V, n, N, (double)tot / n / N, (double)cy[0].h / N);
        for (int i = 0; i < 10; i++) { long h2 = cyc_run(cy[i].a, cy[i].b, cy[i].c, N2);
            printf("(%c%c %c%c %c%c) screen %.4f refined %ld/%ld = %.4f\n", R[cy[i].a%13], SU[cy[i].a/13], R[cy[i].b%13], SU[cy[i].b/13],
                   R[cy[i].c%13], SU[cy[i].c/13], (double)cy[i].h / N, h2, N2, (double)h2 / N2); }
        return 0;
    }
    if (mode == 'r') {                            /* one v10 round, same-suit pairs */
        static long hs[52][52], hr[52][52];
        for (long n = 0; n < N; n++) { shuffle(d); stem(d, x); walk(x, s0);
            for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) { if (a / 13 != b / 13) continue;
                swapv(d, e, a, b); stem(e, y); int ok = 1;
                for (int i = 0; i < 52; i++) { int t = x[i] == a ? b : x[i] == b ? a : x[i]; if (y[i] != t) { ok = 0; break; } }
                if (!ok) continue;
                hs[a][b]++; walk(y, s1); hr[a][b] += !memcmp(s0, s1, sizeof s0); } }
        for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) if (a / 13 == b / 13)
            printf("%d %d %ld %ld %ld\n", a, b, hs[a][b], hr[a][b], N);
        return 0;
    }
    if (mode == 'g') {                            /* position-pair survival by gap j-i (where the floor comes from) */
        static long hg[52], ng[52], tail = 0, tot = 0;
        for (long n = 0; n < N; n++) { shuffle(d); walk(d, s0);
            for (int i = 0; i < 52; i++) for (int j = i + 1; j < 52; j++) {
                memcpy(e, d, sizeof d); e[i] = d[j]; e[j] = d[i]; walk(e, s1);
                int sv = !memcmp(s0, s1, sizeof s0); hg[j - i] += sv; ng[j - i]++; tot += sv; if (j >= 48) tail += sv; } }
        printf("variant %d: mean position-pair survival %.5f; share of survivals with j >= 48: %.3f\n", V, (double)tot / (N * 1326.0), (double)tail / tot);
        for (int g2 = 1; g2 <= 8; g2++) printf("  gap %d: survival %.4f, share of all survivals %.3f\n", g2, (double)hg[g2] / ng[g2], (double)hg[g2] / tot);
        return 0;
    }
    if (mode == 'x') {                            /* dump for cross-checks: stem and GC of stdin decks */
        while (1) { for (int i = 0; i < 52; i++) if (scanf("%d", &d[i]) != 1) return 0;
            stem(d, x); walk(d, s0); int o[52]; for (int i = 0; i < 52; i++) o[s0[i]] = d[i];
            for (int i = 0; i < 52; i++) printf("%d ", x[i]);
            printf("| ");
            for (int i = 0; i < 52; i++) printf("%d ", o[i]);
            printf("\n"); }
    }
    return 1;
}
