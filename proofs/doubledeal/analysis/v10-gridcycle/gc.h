#pragma once
/* DoubleDeal v10 GridCycle (mix_columns), SPEC 3.5 / doubledeal.sudo. Unchanged since v9.
   Cards 0..51: suit = c/13 (GridCycle order: clubs 0, hearts 1, spades 2, diamonds 3), rank = c%13+1.
   Seats are r*13+c; output is row-major, so output index == seat id. */
#include <stdint.h>
#include <string.h>
static inline int gc_walk(const int *d, int *seat /*52*/, int upto) {
    /* Fills seat[0..upto-1]; returns number of overflows. */
    uint8_t occ[52]; memset(occ, 0, 52);
    int t = 0, nov = 0, r = 2, c = 0;
    for (int i = 0; i < upto; i++) {
        if (i > 0) {
            int pc = d[i-1];
            int tr = (r + pc / 13) & 3, tc = (c + pc % 13 + 1) % 13;
            if (!occ[tr*13+tc]) { r = tr; c = tc; }
            else {
                nov++;
                int found = 0;
                for (int a = 0; a < 4 && !found; a++) {
                    for (int k = 0; k < 13; k++) {
                        int cc = (tc + k) % 13;
                        if (!occ[t*13+cc]) { r = t; c = cc; found = 1; break; }
                    }
                    t = (t + 1) & 3;   /* advance marker after use, or when the row is full */
                }
            }
        } else { r = 2; c = 0; }
        occ[r*13+c] = 1; seat[i] = r*13+c;
    }
    return nov;
}
static inline void gc_mix(const int *d, int *out) {
    int seat[52]; gc_walk(d, seat, 52);
    for (int i = 0; i < 52; i++) out[seat[i]] = d[i];
}
/* xorshift rng + Fisher-Yates */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline void shuffle(int *d) { for (int i = 0; i < 52; i++) d[i] = i;
    for (int i = 51; i > 0; i--) { int j = rnd() % (i+1); int x = d[i]; d[i] = d[j]; d[j] = x; } }
