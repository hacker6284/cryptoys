/* 52-card bump variants of GridCycle (analysis only). Same card encoding as gc.h: suit = c/13
   (clubs 0, hearts 1, spades 2, diamonds 3), rank = c%13+1; seats r*13+c; start (2,0).
   40 (a) bump: new card takes the target; occupant goes to the v10 scan seat (marker row t, from
          the target column, first free, marker +1 / past full rows); next step from the target by
          the new card. ("(b) bump + ghost finger" is the same map: the new card sits on the target.)
   41 (c) bump, occupant sends itself: row marker + suit(occupant), start column target column +
          rank(occupant), first free to the right (full row -> next row), marker +1; next step from
          the target by the new card.
   42 (d) as 40, but the next step starts at the occupant's new seat, driven by the occupant.
   43 (d) as 41, but the next step starts at the occupant's new seat, driven by the occupant.
   44 (d) as 40 with a zero-step guard: K♣'s column step counts 13 (still 0 mod 13) -- identical map,
          kept only as a reminder; not used. */
#pragma once
#include <string.h>
#include <stdint.h>
static long bump_moves;   /* number of bumps (lift, place, move) */
static long bump_scan;    /* seats inspected by the occupant's scan */
static int bscan(const uint8_t *occ, int row, int c0, int *t, int mark) {
    for (int a = 0; a < 4; a++) { int rr = (row + a) & 3;
        for (int q = 0; q < 13; q++) { int cc = (c0 + q) % 13; bump_scan++;
            if (!occ[rr*13+cc]) { if (mark) *t = (*t + a + 1) & 3; return rr*13+cc; } } }
    return -1;
}
static void bump_mix(int V, const int *d, int *out) {
    uint8_t occ[52] = {0}; int g[52]; int t = 0, fr = 2, fc = 0, drv = d[0];
    occ[26] = 1; g[26] = d[0];
    for (int i = 1; i < 52; i++) {
        int x = d[i], tr = (fr + drv / 13) & 3, tc = (fc + drv % 13 + 1) % 13, T = tr*13+tc;
        if (!occ[T]) { occ[T] = 1; g[T] = x; fr = tr; fc = tc; drv = x; continue; }
        int o = g[T], s; bump_moves++;
        if (V == 40 || V == 42) s = bscan(occ, t, tc, &t, 1);
        else { int t0 = t; s = bscan(occ, (t0 + o / 13) & 3, (tc + o % 13 + 1) % 13, &t, 0); t = (t0 + 1) & 3; }
        occ[s] = 1; g[s] = o; g[T] = x;
        if (V == 40 || V == 41) { fr = tr; fc = tc; drv = x; } else { fr = s / 13; fc = s % 13; drv = o; }
    }
    memcpy(out, g, sizeof g);
}
