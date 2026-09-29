/* One-pass swap pass-through and reversibility for readings of "rotate x cards one by one, then cut by rank".
   x = suit(C) (clubs 0, hearts 1, spades 2, diamonds 3). Every reading keeps the current rank cut with its
   fallback (hand if rank < hand size, else key pile if rank < key size, else skip) and puts C on top of the key pile.
     0 CUR   current SPEC 3.7 F (dd.h passkey)
     1 SAME  x one-card moves top -> bottom of the SAME hand, done literally one card at a time (should equal CUR)
     2 DEAL  deal x cards one at a time from the top of the hand onto the key pile (each lands on top, so their
             order reverses); those cards never become controllers; x is capped at the hand size
     3 KEYP  x one-card moves top -> bottom of the KEY pile (= cut the key pile by suit), then the rank cut
     4 DEALB deal x cards one at a time off the top of the hand (so they reverse), put that small packet under the
             hand ("rotate the hand by x" with the moved packet reversed); x capped at the hand size.
             Zachary's stated intent (2026-09-28): the x cards change order.
             DEALK=k (env) deals x = suit + k instead (k = 0..4); the count is capped at the hand size (min), see README 8.
     6 DEALKF deal suit + k (k from env DEALK) under the hand if it is smaller than the hand, else under the key pile
     5 REVT  reverse the top x cards of the hand in place (deal them off and put them back on top), then the rank cut
   usage: readings N seed      (all 1326 swaps, N uniform decks each; round-trip test on 200k decks each way) */
#include <stdio.h>
#include <stdlib.h>
#include <omp.h>
#include "dd.h"
static const char *nm(int c) { static char b[64][3]; static int i; char *s = b[i++ & 63]; s[0] = "A23456789TJQK"[c % 13]; s[1] = "CHSD"[c / 13]; s[2] = 0; return s; }
static void top_to_bottom(int *a, int n) { if (n <= 1) return; int t = a[0]; memmove(a, a + 1, (n - 1) * sizeof(int)); a[n-1] = t; }
static void bottom_to_top(int *a, int n) { if (n <= 1) return; int t = a[n-1]; memmove(a + 1, a, (n - 1) * sizeof(int)); a[0] = t; }
static void push(int *a, int *n, int c) { memmove(a + 1, a, *n * sizeof(int)); a[0] = c; (*n)++; }
static int pop(int *a, int *n) { int c = a[0]; memmove(a, a + 1, (*n - 1) * sizeof(int)); (*n)--; return c; }
static void rank_cut(int *hand, int hn, int *key, int kn, int r, int dir) {
    if (hn && r < hn) rotl(hand, hn, dir * r); else if (kn && r < kn) rotl(key, kn, dir * r); }
static int KDEAL = 0;    /* DEALB: deal suit + KDEAL cards (env DEALK) */
static int DMOD = 0;     /* DEALB: env DEALMOD=1 caps the count as x mod hand size instead of min(x, hand size) */
/* deal m cards one at a time off the top of pile a (size n), reversed, under the pile (dir 1); dir -1 undoes it */
static void deal_under(int *a, int n, int m, int dir) { int t[8];
    if (dir < 0) rotl(a, n, -m);
    for (int i = 0; i < m; i++) t[i] = a[m - 1 - i];
    memcpy(a, t, m * sizeof(int));
    if (dir > 0) rotl(a, n, m); }
/* 6 DEALKF: x = suit + KDEAL; if x < hand size deal x under the hand; else if x < key size deal x under the key pile;
   else skip (never happens in a 52-card pass: x >= hand means hand <= 5, so key >= 46). Then the rank cut. */
static void dealkf(int *hand, int hn, int *key, int kn, int x, int dir) {
    if (x < hn) deal_under(hand, hn, x, dir); else if (x < kn) deal_under(key, kn, x, dir); }
static void fwd(int v, const int *d, int *o) {
    if (v == 0) { passkey(d, o); return; }
    int hand[52], key[52], hn = 52, kn = 0; memcpy(hand, d, sizeof hand);
    while (hn) { int C = pop(hand, &hn), x = SUIT(C) + (v == 4 || v == 6 ? KDEAL : 0);
        if (v == 6) dealkf(hand, hn, key, kn, x, 1);
        if (v == 1) for (int i = 0; i < x && hn; i++) top_to_bottom(hand, hn);
        if (v == 2) for (int i = 0; i < x && hn; i++) push(key, &kn, pop(hand, &hn));
        if (v == 3) for (int i = 0; i < x && kn; i++) top_to_bottom(key, kn);
        if (v == 4 || v == 5) { int m = (v == 4 && DMOD) ? (hn ? x % hn : 0) : (x < hn ? x : hn), t[8]; for (int i = 0; i < m; i++) t[i] = hand[m - 1 - i];
            memcpy(hand, t, m * sizeof(int)); if (v == 4) rotl(hand, hn, m); }
        rank_cut(hand, hn, key, kn, RANK(C), 1);
        push(key, &kn, C); }
    memcpy(o, key, sizeof key); }
static int MLAST = -1;   /* DEAL only: how many cards the last controller dealt (-1: take min(x, key size)) */
static void inv(int v, const int *o, int *d) {
    if (v == 0) { passkey_inv(o, d); return; }
    int hand[52], key[52], hn = 0, kn = 52; memcpy(key, o, sizeof key);
    while (kn) { int C = pop(key, &kn), x = SUIT(C) + (v == 4 || v == 6 ? KDEAL : 0);
        rank_cut(hand, hn, key, kn, RANK(C), -1);             /* same pile sizes as at the forward cut */
        if (v == 6) dealkf(hand, hn, key, kn, x, -1);
        if (v == 1) for (int i = 0; i < x && hn; i++) bottom_to_top(hand, hn);
        if (v == 2) { /* a non-last controller always dealt exactly x (cards remained after it); the last one dealt
                         h0 <= x cards, h0 = the hand it saw, which the inverse cannot read: MLAST picks it */
            int m = (hn == 0 && MLAST >= 0) ? MLAST : x; if (m > x) m = x; if (m > kn) m = kn;
            for (int i = 0; i < m; i++) push(hand, &hn, pop(key, &kn)); }
        if (v == 3) for (int i = 0; i < x && kn; i++) bottom_to_top(key, kn);
        if (v == 4 || v == 5) { int m = (v == 4 && DMOD) ? (hn ? x % hn : 0) : (x < hn ? x : hn), t[8]; if (v == 4) rotl(hand, hn, -m);
            for (int i = 0; i < m; i++) t[i] = hand[m - 1 - i];
            memcpy(hand, t, m * sizeof(int)); }
        push(hand, &hn, C); }
    memcpy(d, hand, sizeof hand); }
static const char *VN[] = {"CUR", "SAME", "DEAL", "KEYP", "DEALB", "REVT", "DEALKF"};
int main(int argc, char **argv) {
    if (getenv("DEALK")) KDEAL = atoi(getenv("DEALK"));
    if (getenv("DEALMOD")) DMOD = atoi(getenv("DEALMOD"));
    long N = argc > 1 ? atol(argv[1]) : 50000; uint64_t seed = argc > 2 ? strtoull(argv[2], 0, 10) : 21;
    printf("readings N=%ld seed=%llu  (x = suit; one pass; swap tau passes if F(tau K) = tau F(K))\n", N, (unsigned long long)seed);
    for (int v = (getenv("ONLYV") ? atoi(getenv("ONLYV")) : 0); v < (getenv("ONLYV") ? atoi(getenv("ONLYV")) + 1 : 6); v++) {
        long rt1 = 0, rt2 = 0, eqcur = 0; uint64_t s = seed_for(seed, v, 999);
        for (int n = 0; n < 200000; n++) { int a[52], b[52], c[52], z[52]; shuffle_(a, &s); fwd(v, a, b); inv(v, b, c); rt1 += !same(a, c);
            inv(v, a, b); fwd(v, b, c); rt2 += !same(a, c); fwd(0, a, z); fwd(v, a, b); eqcur += same(z, b); }
        if (v == 2) { /* count distinct valid preimages over the choices of MLAST */
            long hist[5] = {0}; uint64_t s3 = seed_for(seed, 7, 7);
            for (int n = 0; n < 200000; n++) { int a[52], y[52], pre[4][52], np = 0; shuffle_(a, &s3); fwd(2, a, y);
                for (int m = 0; m <= 3; m++) { int c[52], z[52]; MLAST = m; inv(2, y, c); fwd(2, c, z); if (!same(z, y)) continue;
                    int dup = 0; for (int q = 0; q < np; q++) dup |= same(pre[q], c); if (!dup) memcpy(pre[np++], c, sizeof c); }
                hist[np]++; }
            MLAST = -1;
            printf("DEAL  preimages found per output (200000 random decks, trying every last-deal count): 1:%ld 2:%ld 3:%ld 4:%ld  -> not injective if any >1\n",
                   hist[1], hist[2], hist[3], hist[4]); }
        static double p[52][52];
        #pragma omp parallel for schedule(dynamic)
        for (int ab = 0; ab < 52 * 52; ab++) { int a = ab / 52, b = ab % 52; if (a >= b) continue;
            uint64_t s2 = seed_for(seed, a, b); long hit = 0; int k[52], kt[52], f[52], ft[52], tf[52];
            for (long n = 0; n < N; n++) { shuffle_(k, &s2); relabel(k, a, b, kt); fwd(v, k, f); fwd(v, kt, ft); relabel(f, a, b, tf); hit += same(ft, tf); }
            p[a][b] = (double)hit / N; }
        int over = 0, wa = 0, wb = 0; double w = 0, sum = 0;
        for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) { over += p[a][b] > 1.0 / 64; sum += p[a][b]; if (p[a][b] > w) { w = p[a][b]; wa = a; wb = b; } }
        printf("%-4s  F^-1(F(x)) != x: %ld/200000  F(F^-1(y)) != y: %ld/200000  equals CUR on %ld/200000 decks\n", VN[v], rt1, rt2, eqcur);
        if (v == 6) printf("      (DEALKF with k = %d: deal suit + %d under the hand if it is smaller than the hand, else under the key pile)\n", KDEAL, KDEAL);
        if (v == 4) printf("      (DEALB with k = %d: deal suit + %d cards, %s)\n", KDEAL, KDEAL, DMOD ? "count mod hand size" : "count capped at the hand size (min)");
        printf("      worst %s<->%s %.4f   2H<->AS %.4f   pairs > 1/64: %d   mean over 1326: %.5f\n", nm(wa), nm(wb), w, p[14][26], over, sum / 1326);
        printf("      top 5:"); for (int t = 0; t < 5; t++) { double m = -1; int ma = 0, mb = 0;
            for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) if (p[a][b] > m) { m = p[a][b]; ma = a; mb = b; }
            printf(" %s<->%s %.4f", nm(ma), nm(mb), m); p[ma][mb] = -2; } printf("\n");
        if (v != 2 && v != 1) { long all6 = 0, M = 200000; uint64_t s4 = seed_for(seed, wa * 64 + wb, 55 + v);
            for (long n = 0; n < M; n++) { int k[52], kt[52], t[52], ok = 1; shuffle_(k, &s4); relabel(k, wa, wb, kt);
                for (int r = 0; r < 6 && ok; r++) { int f[52], ft[52]; fwd(v, k, f); fwd(v, kt, ft); relabel(f, wa, wb, t); ok = same(ft, t); memcpy(k, f, sizeof f); memcpy(kt, ft, sizeof ft); }
                all6 += ok; }
            printf("      six chained passes, worst pair %s<->%s: K'_r = tau K_r for all r=1..6 in %ld/%ld keys = %.5f\n", nm(wa), nm(wb), all6, M, (double)all6 / M); }
        fflush(stdout); }
    return 0; }
