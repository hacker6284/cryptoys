/* Exhaustive injectivity check of GridCycle variants on small R x C analogues (R rows, C columns,
   n = R*C cards; card c has suit c / C (row step) and rank c % C + 1 (column step), start seat
   (min(2,R-1), 0), marker scan as in v10). A map on n! decks is invertible iff it is injective.
   Variants:
     0  v10 (no bump)                         33 rule 1 (ghost + blocker sends you)
    40  (a) bump: new card takes the target; occupant goes to the v10 scan seat (marker row, from
        the target's column), marker +1; next step from the target by the new card.
        (With bump the new card always sits on the target, so "ghost finger" (b) is the same map.)
    41  (c) bump, the occupant sends itself: row marker + suit(occupant), start column target +
        rank(occupant); marker +1; next step from the target by the new card.
    42  (d) bump, follow the occupant: as 40 but the next step starts at the occupant's new seat,
        driven by the occupant.
    43  (d) bump, follow the occupant, as 41 (occupant sends itself) with next step from its new
        seat driven by it.
    45  tweak: bump (v10 scan for the occupant); next step from the TARGET driven by the OCCUPANT.
    46  tweak: bump (v10 scan); next step from the occupant's new seat driven by the NEW card.
    50  Phase 4 "C sends itself": no bump; when the target is taken the new card C goes to the first
        free seat in row marker + suit(C), from column target + rank(C); marker +1; ghost finger
        (next step from the target by C).   51: same without ghost (next step from where C landed).
    52  row marker + suit(C), column target + rank(blocker); ghost.
    53  row marker + suit(blocker), column target + rank(C); ghost.
    47  side pile: a bumped occupant leaves the table onto a pile; the new card takes the target;
        next step from the target by the new card; at the end the pile is dealt into the empty
        seats in reading order, first-bumped card first. 48: same, last-bumped card first.
    60-64 Phase 6 anti-resync variants (A, A', B, C, A+B; definitions in cand.c).
   usage: p3small R C V   -> prints #distinct outputs of n! decks, and one collision if any */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
static int R, C, n, V;
static int scan(const unsigned char *occ, int row, int c0, int *t, int mark) {
    for (int a = 0; a < R; a++) { int rr = (row + a) % R;
        for (int q = 0; q < C; q++) { int cc = (c0 + q) % C; if (!occ[rr*C+cc]) { if (mark) *t = (*t + a + 1) % R; return rr*C+cc; } } }
    return -1;
}
static void mix(const int *d, int *out) {
    unsigned char occ[64] = {0}; int g[64], pile[64], np = 0; int t = 0, fr = R > 2 ? 2 : R - 1, fc = 0, drv = -1;
    for (int i = 0; i < n; i++) {
        int x = d[i];
        if (i == 0) { int s = fr*C+fc; occ[s] = 1; g[s] = x; drv = x; continue; }
        if (V >= 60) {   /* Phase 6 anti-resync variants, ghost finger + rule-1 scan (see cand.c) */
            int tr = (fr + drv / C + (V == 63 ? t : 0)) % R, rk = drv % C + 1;
            int tc = V == 60 || V == 64 ? (fc + rk + fr) % C : V == 61 ? (fc + rk * (fr + 1)) % C : (fc + rk) % C, T = tr*C+tc;
            if (!occ[T]) { occ[T] = 1; g[T] = x; fr = tr; fc = tc; drv = x; continue; }
            int o = g[T], t0 = t, s = scan(occ, (t0 + o / C) % R, (tc + o % C + 1) % C, &t, 0); t = (t0 + 1) % R;
            occ[s] = 1; g[s] = x; drv = x;
            if (V == 62 || V == 64) { fr = (tr + o / C) % R; fc = (tc + o % C + 1) % C; } else { fr = tr; fc = tc; }
            continue;
        }
        int tr = (fr + drv / C) % R, tc = (fc + drv % C + 1) % C, T = tr*C+tc;
        if (!occ[T]) { occ[T] = 1; g[T] = x; fr = tr; fc = tc; drv = x; continue; }
        if (V >= 50 && V <= 53) {
            int o = g[T], t0 = t, rs_ = (V == 53) ? o / C : x / C, cs_ = (V == 52) ? o % C : x % C;
            int s = scan(occ, (t0 + rs_) % R, (tc + cs_ + 1) % C, &t, 0); t = (t0 + 1) % R;
            occ[s] = 1; g[s] = x;
            if (V == 51) { fr = s / C; fc = s % C; } else { fr = tr; fc = tc; }
            drv = x; continue;
        }
        if (V == 0 || V == 33) {
            int s;
            if (V == 0) s = scan(occ, t, tc, &t, 1);
            else { int o = g[T], t0 = t; s = scan(occ, (t0 + o / C) % R, (tc + o % C + 1) % C, &t, 0); t = (t0 + 1) % R; }
            assert(s >= 0);   /* scan finds a free seat: fewer than R*C cards placed */
            occ[s] = 1; g[s] = x;
            if (V == 0) { fr = s / C; fc = s % C; } else { fr = tr; fc = tc; }
            drv = x; continue;
        }
        if (V == 47 || V == 48) { pile[np++] = g[T]; g[T] = x; fr = tr; fc = tc; drv = x; continue; }
        int o = g[T], s;
        if (V == 40 || V == 42 || V == 45 || V == 46) s = scan(occ, t, tc, &t, 1);
        else { int t0 = t; s = scan(occ, (t0 + o / C) % R, (tc + o % C + 1) % C, &t, 0); t = (t0 + 1) % R; }
        occ[s] = 1; g[s] = o; g[T] = x;
        if (V == 40 || V == 41) { fr = tr; fc = tc; drv = x; } else if (V == 45) { fr = tr; fc = tc; drv = o; }
        else if (V == 46) { fr = s / C; fc = s % C; drv = x; } else { fr = s / C; fc = s % C; drv = o; }
    }
    if (V == 47 || V == 48) { int k = 0; for (int s = 0; s < n; s++) if (!occ[s]) { g[s] = V == 47 ? pile[k] : pile[np - 1 - k]; k++; } }
    for (int s = 0; s < n; s++) out[s] = g[s];
}
static unsigned long long code(const int *p) { unsigned long long v = 0; for (int i = 0; i < n; i++) v = v * n + p[i]; return v; }
typedef struct { unsigned long long key, deck; } E;
static int cmp(const void *a, const void *b) { unsigned long long x = ((E*)a)->key, y = ((E*)b)->key; return (x > y) - (x < y); }
int main(int argc, char **argv) {
    (void)argc;
    R = atoi(argv[1]); C = atoi(argv[2]); V = atoi(argv[3]); n = R * C;
    long long N = 1; for (int i = 2; i <= n; i++) N *= i;
    E *e = malloc(sizeof(E) * N); int p[16], out[16];
    for (int i = 0; i < n; i++) p[i] = i;
    for (long long k = 0; k < N; k++) {
        mix(p, out); e[k].key = code(out); e[k].deck = code(p);
        int i = n - 2; while (i >= 0 && p[i] > p[i+1]) i--;          /* next permutation */
        if (i < 0) break;
        int j = n - 1; while (p[j] < p[i]) j--;
        int x = p[i]; p[i] = p[j]; p[j] = x;
        for (int a = i + 1, b = n - 1; a < b; a++, b--) { x = p[a]; p[a] = p[b]; p[b] = x; }
    }
    qsort(e, N, sizeof(E), cmp);
    long long distinct = 0, firstc = -1;
    for (long long k = 0; k < N; k++) if (k == 0 || e[k].key != e[k-1].key) distinct++; else if (firstc < 0) firstc = k;
    printf("R=%d C=%d n=%d variant %d: %lld decks -> %lld distinct outputs (%s)", R, C, n, V, N, distinct, distinct == N ? "injective" : "NOT injective");
    if (firstc >= 0) {
        printf("; collision:");
        for (int w = 0; w < 2; w++) { unsigned long long v = e[firstc - w].deck; int q[16];
            for (int i = n - 1; i >= 0; i--) { q[i] = v % n; v /= n; } printf(" ["); for (int i = 0; i < n; i++) printf("%d%s", q[i], i < n-1 ? " " : ""); printf("]"); }
        unsigned long long v = e[firstc].key; int q[16]; for (int i = n - 1; i >= 0; i--) { q[i] = v % n; v /= n; }
        printf(" -> ["); for (int i = 0; i < n; i++) printf("%d%s", q[i], i < n-1 ? " " : ""); printf("]");
    }
    printf("\n"); return 0;
}
