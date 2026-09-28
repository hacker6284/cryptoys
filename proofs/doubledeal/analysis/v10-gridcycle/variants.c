/* GridCycle overflow-rule variants (analysis only; v10 = variant 0).
   All variants keep the step rule and differ only in how a blocked target is resolved.
   The overflow choice depends only on (prev card, prev seat, occupancy, marker), so every variant
   is invertible by the same walk-with-visited-marks inverse (checked in this program).
   0: v10         marker row t (then t+1..), scan from blocked column c*, marker advances
   1: rowTarget   scan the blocked seat's own row r* from c* (then r*+1, ...); no marker
   2: markerSuit  marker row (t + suit(prev)) mod 4, then as v10; marker advances
   3: countRank   from the blocked seat, count rank(prev) empty seats forward in reading order
                  (row-major, wrapping 51 -> 0); take the last one counted
   4: countRankRow like 3 but reading column-major from the blocked seat (down the column first)
   5: row (t+suit), then later rows; take the k-th free seat from c*, k = ((rank-1) mod 4) + 1
   6: marker row t, k = suit + 1
   7: row (t+suit), k = rank (1..13)                         [fix option C, "count the rank"]
   8: row (t+suit), k = ((rank-1) mod 5) + 1                 [fix option B, "count on one hand"]
   9: re-step: repeat step(prev card) from the blocked seat until free, else fall back to v10
  10: row (t+suit): list that row's free seats from c*, take entry (rank-1) mod (#free)
  11: row (t+suit), k = ((rank-1) mod 7) + 1                 [fix option B', "count to seven"]
  Variant 2 is fix option A ("suit picks the overflow row"). In 5-8 and 11 the marker still
  advances by one per overflow, and counting wraps round the grid if fewer than k seats are free.
   usage: variants V value N seed   -> per-pair survival lines (a b hits N)
          variants V stats N seed   -> overflow count and scan-length stats, inverse check */
#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
static int V;
/* Seat for walk card i+1, given the card just placed (pc) at (r,c), occupancy and marker t.
   Depends on nothing else, so the inverse (lay row-major, replay with visited marks) is the same
   replay; stats mode checks invMix(Mix(d)) == d for every variant. */
static int choose(const uint8_t *occ, int *tp, int pc, int r, int c, long *scan) {
    int t = *tp, s = pc / 13, rk = pc % 13 + 1;
    int tr = (r + s) & 3, tc = (c + rk) % 13;
    if (!occ[tr*13+tc]) return tr*13+tc;
    int found = 0, steps = 0;
        if (V == 0 || V == 1 || V == 2) {
            int row = V == 0 ? t : V == 1 ? tr : (t + s) & 3;
            for (int a = 0; a < 4 && !found; a++) {
                for (int k = 0; k < 13; k++) { steps++;
                    int cc = (tc + k) % 13;
                    if (!occ[row*13+cc]) { r = row; c = cc; found = 1; break; } }
                row = (row + 1) & 3; if (V != 1) t = (t + 1) & 3;
            }
        } else if (V == 10) {
            /* 10: row (t+suit) (first non-full row from there); list its free seats from c*
               rightward with wrap; take entry number (rank-1) mod (#free in that row). */
            int row = (t + s) & 3, fr[13], nf = 0;
            for (int a = 0; a < 4; a++) { nf = 0;
                for (int q = 0; q < 13; q++) { int cc = (tc + q) % 13; steps++; if (!occ[row*13+cc]) fr[nf++] = cc; }
                if (nf) break;
                row = (row + 1) & 3; }
            r = row; c = fr[(rk - 1) % nf]; found = 1;
            t = (t + 1) & 3;
        } else if (V == 9) {
            /* 9: re-step: keep applying step(prev card) from the blocked seat until a free
               seat; if the step's orbit returns to the blocked seat, fall back to the v10 scan. */
            int rr = tr, cc = tc;
            for (;;) { rr = (rr + s) & 3; cc = (cc + rk) % 13; steps++;
                if (rr == tr && cc == tc) break;
                if (!occ[rr*13+cc]) { r = rr; c = cc; found = 1; break; } }
            int row = t;
            for (int a = 0; a < 4 && !found; a++) {
                for (int k = 0; k < 13; k++) { steps++;
                    int c2 = (tc + k) % 13;
                    if (!occ[row*13+c2]) { r = row; c = c2; found = 1; break; } }
                row = (row + 1) & 3; t = (t + 1) & 3;
            }
        } else if (V == 5 || V == 7 || V == 6 || V == 8 || V == 11) {
            /* 5: row (t+suit), count k=((rank-1)%4)+1 free seats; 7: row (t+suit), k=rank;
               6: row t, k = suit+1; 8: row (t+suit), k=((rank-1)%5)+1 (A..5 = 1..5, 6..T = 1..5, J Q K = 1 2 3);
               11: row (t+suit), k=((rank-1)%7)+1. Seat order: row from c* wrapping, then next row, ... */
            int row = V == 6 ? t : (t + s) & 3;
            int k = V == 11 ? (rk - 1) % 7 + 1 : V == 8 ? (rk - 1) % 5 + 1 : V == 5 ? (rk - 1) % 4 + 1 : V == 7 ? rk : s + 1, cnt = 0;
            while (!found) {
                for (int a = 0; a < 4 && !found; a++) {
                    for (int q = 0; q < 13; q++) { steps++;
                        int cc = (tc + q) % 13;
                        if (!occ[((row + a) & 3)*13+cc] && ++cnt == k) { r = (row + a) & 3; c = cc; found = 1; break; } }
                }
            }
            t = (t + 1) & 3;
        } else {
            int cnt = 0, p = V == 3 ? tr*13+tc : tc*4+tr;  /* index in reading order */
            while (cnt < rk) { p = (p + 1) % 52; steps++;
                int rr = V == 3 ? p / 13 : p % 4, cc = V == 3 ? p % 13 : p / 4;
                if (!occ[rr*13+cc]) { cnt++; if (cnt == rk) { r = rr; c = cc; } } }
        }
    if (scan) *scan += steps;
    *tp = t; return r*13+c;
}
static int walkv(const int *d, int *seat, long *scan) {
    uint8_t occ[52]; memset(occ, 0, 52);
    int t = 0, nov = 0, cur = 2*13+0;
    for (int i = 0; i < 52; i++) {
        if (i > 0) { int pc = d[i-1], r = cur / 13, c = cur % 13;
            int tgt = ((r + pc / 13) & 3) * 13 + (c + pc % 13 + 1) % 13;
            cur = choose(occ, &t, pc, r, c, scan); nov += cur != tgt; }
        occ[cur] = 1; seat[i] = cur;
    }
    return nov;
}
/* inverse: out is the row-major grid; replay the walk with visited marks, reading the cards */
static void inv_mix(const int *out, int *hand) {
    uint8_t vis[52]; memset(vis, 0, 52); int t = 0, cur = 26;
    for (int i = 0; i < 52; i++) {
        if (i > 0) cur = choose(vis, &t, hand[i-1], cur / 13, cur % 13, 0);
        vis[cur] = 1; hand[i] = out[cur];
    }
}
int main(int argc, char **argv) {
    (void)argc;
    V = atoi(argv[1]); int stats = argv[2][0] == 's'; long N = atol(argv[3]);
    rs ^= strtoull(argv[4],0,10)*0x9E3779B97F4A7C15ULL;
    int d[52], e[52], s0[52], s1[52], where[52];
    if (stats) {
        long nov = 0, scan = 0, bad = 0, invbad = 0;
        for (long n = 0; n < N; n++) { shuffle(d); nov += walkv(d, s0, &scan);
            uint8_t seen[52] = {0}; for (int i = 0; i < 52; i++) { if (seen[s0[i]]) bad++; seen[s0[i]] = 1; }
            int out[52], back[52]; for (int i = 0; i < 52; i++) out[s0[i]] = d[i];
            inv_mix(out, back); invbad += memcmp(back, d, sizeof d) != 0; }
        printf("variant %d: mean overflows %.2f, mean scan steps per overflow %.2f, non-bijective walks %ld, inverse failures %ld / %ld\n",
               V, (double)nov / N, (double)scan / nov, bad, invbad, N);
        return 0;
    }
    static long hits[52][52];
    for (long n = 0; n < N; n++) {
        shuffle(d); walkv(d, s0, 0);
        for (int i = 0; i < 52; i++) where[d[i]] = i;
        for (int a = 0; a < 52; a++) for (int b = a+1; b < 52; b++) {
            int i = where[a], j = where[b];
            memcpy(e, d, sizeof d); e[i] = d[j]; e[j] = d[i];
            walkv(e, s1, 0);
            if (!memcmp(s0, s1, sizeof s0)) hits[a][b]++;
        }
    }
    for (int a = 0; a < 52; a++) for (int b = a+1; b < 52; b++) printf("%d %d %ld %ld\n", a, b, hits[a][b], N);
    return 0;
}
