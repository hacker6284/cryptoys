/* Phase 4: "C sends itself" (analysis only).
   50: rule-1 walk (ghost finger: next step from the target T by the card just placed, C), but a
       blocked C goes to the first free seat of row (marker + suit(C)) scanning right from column
       (T.col + rank(C)), dropping a row if full; marker +1.
   51: as 50 without the ghost finger (next step from where C landed).
   52: row marker + suit(C), column T.col + rank(blocker).   53: row marker + suit(blocker), column T.col + rank(C).
   Modes:
     collide V decks seed      single-swap collisions (bump-style search as p3collide.c)
     decrypt V decks seed      best decryptor: depth-first search over candidates. At a visited target
                               the candidates are the unvisited seats s whose card c would itself scan
                               to s; each is tried. Counts solutions (cap 2), candidates per blocked step.
     value/stats/cyc3/round    only meaningful if invertible (not used: it is not) */
#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
static int V;
static int scan4(const uint8_t *occ, int row, int c0) {
    for (int a = 0; a < 4; a++) { int rr = (row + a) & 3;
        for (int q = 0; q < 13; q++) { int cc = (c0 + q) % 13; if (!occ[rr*13+cc]) return rr*13+cc; } }
    return -1;
}
static int land(const uint8_t *occ, const int *g, int T, int t, int c) {   /* where a blocked c lands */
    int o = g[T], rsuit = V == 53 ? o / 13 : c / 13, crank = V == 52 ? o % 13 + 1 : c % 13 + 1;
    return scan4(occ, (t + rsuit) & 3, (T % 13 + crank) % 13);
}
static void mix4(const int *d, int *out, int *seat) {
    uint8_t occ[52] = {0}; int g[52], t = 0, fr = 2, fc = 0; occ[26] = 1; g[26] = d[0]; seat[0] = 26;
    for (int i = 1; i < 52; i++) { int p = d[i-1], x = d[i], tr = (fr + p / 13) & 3, tc = (fc + p % 13 + 1) % 13, T = tr*13+tc, s;
        if (!occ[T]) s = T; else { s = land(occ, g, T, t, x); t = (t + 1) & 3; }
        occ[s] = 1; g[s] = x; seat[i] = s;
        if (V == 51) { fr = s / 13; fc = s % 13; } else { fr = tr; fc = tc; } }
    memcpy(out, g, sizeof g);
}
/* ---- DFS decryptor ---- */
static const int *G; static long sols, cap = 2; static long nodes, nodecap = 2000000;
static int hand[52], first[52]; static long candSum, candSteps; static const int *truth;
static void dfs(int i, uint8_t *vis, int t, int fr, int fc, int drv, int prefixTrue) {
    if (sols >= cap || nodes > nodecap) return;
    nodes++;
    if (i == 52) { if (sols == 0) memcpy(first, hand, sizeof hand); sols++; return; }
    int tr = (fr + drv / 13) & 3, tc = (fc + drv % 13 + 1) % 13, T = tr*13+tc;
    if (!vis[T]) { vis[T] = 1; hand[i] = G[T];
        int nfr = tr, nfc = tc; dfs(i + 1, vis, t, nfr, nfc, G[T], prefixTrue && G[T] == truth[i]); vis[T] = 0; return; }
    int cands[52], nc = 0;
    for (int s = 0; s < 52; s++) if (!vis[s] && land(vis, G, T, t, G[s]) == s) cands[nc++] = s;
    if (prefixTrue) { candSum += nc; candSteps++; }
    for (int k = 0; k < nc; k++) { int s = cands[k]; vis[s] = 1; hand[i] = G[s];
        int nfr = V == 51 ? s / 13 : tr, nfc = V == 51 ? s % 13 : tc;
        dfs(i + 1, vis, (t + 1) & 3, nfr, nfc, G[s], prefixTrue && G[s] == truth[i]); vis[s] = 0; if (sols >= cap) return; }
}
int main(int argc, char **argv) {
    V = atoi(argv[1]); char m = argv[2][0]; long N = atol(argv[3]); rs ^= strtoull(argv[4],0,10)*0x9E3779B97F4A7C15ULL;
    if (argc > 5) { cap = atol(argv[5]); nodecap = 200000000L; }
    int d[52], e[52], o0[52], o1[52], sd[52];
    if (m == 'c') {
        long hits = 0, decksHit = 0, adj = 0, kc = 0, mid = 0, decksMid = 0; int shown = 0, shownMid = 0;
        for (long n = 0; n < N; n++) { shuffle(d); mix4(d, o0, sd); int any = 0, anyMid = 0;
            for (int i = 0; i < 52; i++) for (int j = i + 1; j < 52; j++) { memcpy(e, d, sizeof d); e[i] = d[j]; e[j] = d[i]; mix4(e, o1, sd);
                if (!memcmp(o0, o1, sizeof o0)) { hits++; any = 1; adj += j == i + 1; kc += d[i] == 12 || d[j] == 12;
                    if (j < 48) { mid++; anyMid = 1; }
                    if (shown < 2 || (j < 48 && shownMid < 2)) { shown++; shownMid += j < 48; printf("collision V%d: swap walk positions %d,%d (cards %d,%d) deck:", V, i, j, d[i], d[j]);
                        for (int k = 0; k < 52; k++) printf(" %d", d[k]);
                        printf("\n"); } } }
            decksHit += any; decksMid += anyMid; }
        printf("V%d: %ld decks x 1326 swaps: %ld collisions (%ld adjacent, %ld involve K♣); %ld decks (%.1f%%) have a colliding one-swap neighbour\n",
               V, N, hits, adj, kc, decksHit, 100.0 * decksHit / N);
        printf("V%d: mid-deck (both swapped walk positions < 48): %ld collisions; %ld decks (%.1f%%)\n", V, mid, decksMid, 100.0 * decksMid / N);
        return 0;
    }
    if (m == 'd') {
        long ok = 0, unique = 0, ambiguous = 0, capped = 0; long nodeSum = 0;
        for (long n = 0; n < N; n++) { shuffle(d); mix4(d, o0, sd); G = o0; truth = d; sols = 0; nodes = 0;
            uint8_t vis[52] = {0}; vis[26] = 1; hand[0] = G[26];
            dfs(1, vis, 0, 2, 0, G[26], G[26] == d[0]);
            nodeSum += nodes;
            if (nodes > nodecap) capped++;
            if (argc > 5) printf("deck %ld preimages %ld%s\n", n, sols, nodes > nodecap ? " (capped)" : "");
            if (sols == 1) { unique++; ok += !memcmp(first, d, sizeof d); } else if (sols >= 2) ambiguous++; }
        printf("V%d: %ld decks: unique preimage %ld (%.2f%%; of these recovered %ld), >= 2 preimages %ld (%.2f%%), search capped %ld; "
               "candidates per blocked step on the true path %.2f; DFS nodes per deck %.0f\n",
               V, N, unique, 100.0 * unique / N, ok, ambiguous, 100.0 * ambiguous / N, capped, (double)candSum / candSteps, (double)nodeSum / N);
        return 0;
    }
    return 1;
}
