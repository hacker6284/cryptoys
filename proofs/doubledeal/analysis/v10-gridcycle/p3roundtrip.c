/* 100k-deck round trip for the bump variants with the natural table decryptor:
   lay the output row-major, replay the walk with visited marks; the card of step i is read from
   the target seat T_i (the new card sits on the target in every bump variant); if T_i was already
   visited, the occupant's destination seat is computed with the same rule (the occupant being the
   card read at T_i's earlier visit) and marked visited. This is the only decryptor that reads the
   table in walk order; the collisions (p3collide.c, p3trace.py) show that NO decryptor can work.
   For 42/43 the next step is driven by the occupant from its new seat, read at that seat.
   usage: p3roundtrip V N seed */
#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include "p3bump.h"
static void decrypt(int V, const int *G, int *hand) {
    uint8_t vis[52] = {0}; int cur[52]; int t = 0, fr = 2, fc = 0;
    /* cur[s] = the card the decryptor believes is at seat s now */
    vis[26] = 1; cur[26] = G[26]; hand[0] = G[26]; int drv = G[26];
    for (int i = 1; i < 52; i++) {
        int tr = (fr + drv / 13) & 3, tc = (fc + drv % 13 + 1) % 13, T = tr*13+tc;
        if (!vis[T]) { vis[T] = 1; cur[T] = G[T]; hand[i] = G[T]; fr = tr; fc = tc; drv = G[T]; continue; }
        int o = cur[T], s;
        if (V == 40 || V == 42) s = bscan(vis, t, tc, &t, 1);
        else { int t0 = t; s = bscan(vis, (t0 + o / 13) & 3, (tc + o % 13 + 1) % 13, &t, 0); t = (t0 + 1) & 3; }
        vis[s] = 1; cur[s] = o; hand[i] = G[T]; cur[T] = G[T];
        if (V == 40 || V == 41) { fr = tr; fc = tc; drv = G[T]; } else { fr = s / 13; fc = s % 13; drv = o; }
    }
}
int main(int argc, char **argv) {
    (void)argc;
    int V = atoi(argv[1]); long N = atol(argv[2]); rs ^= strtoull(argv[3],0,10)*0x9E3779B97F4A7C15ULL;
    int d[52], G[52], h[52]; long ok = 0; long moves0 = 0, scan0 = 0;
    for (long n = 0; n < N; n++) { shuffle(d); bump_mix(V, d, G); moves0 = bump_moves; scan0 = bump_scan;
        decrypt(V, G, h); bump_moves = moves0; bump_scan = scan0; ok += !memcmp(d, h, sizeof d); }
    printf("V%d: natural decryptor recovers %ld / %ld decks (%.2f%%); bumps per deck %.2f; occupant-scan seats per bump %.2f\n",
           V, ok, N, 100.0 * ok / N, (double)bump_moves / N, (double)bump_scan / bump_moves);
}
