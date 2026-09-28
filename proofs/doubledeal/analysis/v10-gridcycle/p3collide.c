/* Look for explicit collisions of the 52-card bump maps: decks d != e with bump(d) == bump(e).
   For random decks d, try every transposition of walk positions (i, j) with j - i <= W.
   usage: p3collide V decks W seed   -> prints the first few collisions found and the rate */
#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#include "p3bump.h"
int main(int argc, char **argv) {
    (void)argc;
    int V = atoi(argv[1]); long N = atol(argv[2]); int W = atoi(argv[3]); rs ^= strtoull(argv[4],0,10)*0x9E3779B97F4A7C15ULL;
    int d[52], e[52], o0[52], o1[52]; long tries = 0, hits = 0, decksHit = 0, withKC = 0, adjacent = 0; int shown = 0;
    for (long n = 0; n < N; n++) { shuffle(d); bump_mix(V, d, o0); int any = 0;
        for (int i = 0; i < 52; i++) for (int j = i + 1; j < 52 && j - i <= W; j++) {
            memcpy(e, d, sizeof d); e[i] = d[j]; e[j] = d[i]; bump_mix(V, e, o1); tries++;
            if (!memcmp(o0, o1, sizeof o0)) { hits++; any = 1; withKC += d[i] == 12 || d[j] == 12; adjacent += j == i + 1;
                if (shown < 3) { shown++; printf("collision (V%d): swap walk positions %d,%d (cards %d,%d) in deck:", V, i, j, d[i], d[j]);
                    for (int k = 0; k < 52; k++) printf(" %d", d[k]);
                    printf("\n"); } } }   /* one newline per shown collision, after the deck */
        decksHit += any; }
    printf("V%d: %ld swaps tried (|i-j|<=%d) on %ld decks: %ld collisions (%ld involve K♣, %ld adjacent walk positions); %ld of %ld decks have one\n", V, tries, W, N, hits, withKC, adjacent, decksHit, N);
}
