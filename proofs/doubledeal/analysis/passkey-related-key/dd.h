#pragma once
/* DoubleDeal v11 (SPEC on main) in C, for the PassKey related-key analysis. Analysis only.
   Cards 0..51: suit = c/13 (C,H,S,D = 0..3), rank = c%13 + 1. Decks are top-first arrays.
   Cross-checked against proofs/doubledeal/security/checks/ddport.py and the committed vectors (xcheck.py). */
#include <stdint.h>
#include <string.h>
#define SUIT(c) ((c) / 13)
#define RANK(c) ((c) % 13 + 1)
static inline uint64_t rnd_(uint64_t *s) { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; return *s; }
static inline void shuffle_(int *d, uint64_t *s) { for (int i = 0; i < 52; i++) d[i] = i;
    for (int i = 51; i > 0; i--) { int j = rnd_(s) % (i + 1); int x = d[i]; d[i] = d[j]; d[j] = x; } }
static inline uint64_t seed_for(uint64_t base, uint64_t a, uint64_t b) { /* splitmix of (base,a,b) */
    uint64_t z = base * 0x9E3779B97F4A7C15ull ^ (a << 32) ^ (b << 8) ^ 0x1234567ull;
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull; z = (z ^ (z >> 27)) * 0x94D049BB133111EBull; z ^= z >> 31;
    return z ? z : 1; }
static inline void rotl(int *a, int n, int k) { if (n <= 1) return; k %= n; if (k < 0) k += n; if (!k) return;
    int t[52]; for (int i = 0; i < n; i++) t[i] = a[(i + k) % n]; memcpy(a, t, n * sizeof(int)); }
static inline void relabel(const int *d, int a, int b, int *o) { for (int i = 0; i < 52; i++) o[i] = d[i] == a ? b : d[i] == b ? a : d[i]; }
static inline int same(const int *x, const int *y) { return !memcmp(x, y, 52 * sizeof(int)); }
static inline int hamming(const int *x, const int *y) { int h = 0; for (int i = 0; i < 52; i++) h += x[i] != y[i]; return h; }

/* ---- PassKey F (SPEC 3.7) and F^-1 ---- */
static inline void passkey(const int *d, int *o) { int hand[52], key[52], hn = 51, kn = 0; memcpy(hand, d + 1, 51 * sizeof(int)); int C = d[0];
    for (;;) {
        if (hn) rotl(hand, hn, SUIT(C) % hn);
        if (hn && RANK(C) < hn) rotl(hand, hn, RANK(C));
        else if (kn && RANK(C) < kn) rotl(key, kn, RANK(C));
        memmove(key + 1, key, kn * sizeof(int)); key[0] = C; kn++;
        if (!hn) break;
        C = hand[0]; memmove(hand, hand + 1, (hn - 1) * sizeof(int)); hn--; }
    memcpy(o, key, 52 * sizeof(int)); }
static inline void passkey_inv(const int *o, int *d) { int hand[52], key[52], hn = 0, kn = 52; memcpy(key, o, 52 * sizeof(int));
    while (kn) { int C = key[0]; memmove(key, key + 1, (kn - 1) * sizeof(int)); kn--;
        int n = hn;
        if (n > 0 && RANK(C) < n) rotl(hand, hn, -RANK(C));
        else if (kn && RANK(C) < kn) rotl(key, kn, -RANK(C));
        if (n > 0) rotl(hand, hn, -(SUIT(C) % n));
        memmove(hand + 1, hand, hn * sizeof(int)); hand[0] = C; hn++; }
    memcpy(d, hand, 52 * sizeof(int)); }
/* Analysis-only alternative (NOT the spec): deal suit + k cards off the top of the hand (reversed) under the hand,
   count capped at the hand size, then the unchanged rank cut. expand_keys uses it when DD_DEALK >= 0 (rk.c: env DEALK). */
static int DD_DEALK = -1, DD_DEALMOD = 0;   /* DD_DEALMOD: count = (suit + k) mod hand size instead of min */
static inline void passkey_dealb(const int *d, int *o, int k) { int hand[52], key[52], hn = 51, kn = 0; memcpy(hand, d + 1, 51 * sizeof(int)); int C = d[0];
    for (;;) {
        int m = SUIT(C) + k; if (DD_DEALMOD) m = hn ? m % hn : 0; else if (m > hn) m = hn;
        for (int i = 0; i < m / 2; i++) { int t = hand[i]; hand[i] = hand[m-1-i]; hand[m-1-i] = t; }
        rotl(hand, hn, m);
        if (hn && RANK(C) < hn) rotl(hand, hn, RANK(C));
        else if (kn && RANK(C) < kn) rotl(key, kn, RANK(C));
        memmove(key + 1, key, kn * sizeof(int)); key[0] = C; kn++;
        if (!hn) break;
        C = hand[0]; memmove(hand, hand + 1, (hn - 1) * sizeof(int)); hn--; }
    memcpy(o, key, 52 * sizeof(int)); }
static inline void expand_keys(const int *k0, int keys[7][52]) { memcpy(keys[0], k0, 52 * sizeof(int));
    for (int r = 1; r <= 6; r++) { if (DD_DEALK >= 0) passkey_dealb(keys[r-1], keys[r], DD_DEALK); else passkey(keys[r-1], keys[r]); } }

/* ---- grid layers ---- */
static inline void lay_cm(const int *d, int g[4][13]) { for (int k = 0; k < 52; k++) g[k%4][k/4] = d[k]; }
static inline void scoop_cm(int g[4][13], int *d) { for (int k = 0; k < 52; k++) d[k] = g[k%4][k/4]; }
static inline void rot_col_down(int g[4][13], int j, int s) { int col[4]; for (int i = 0; i < 4; i++) col[i] = g[i][j];
    for (int i = 0; i < 4; i++) g[i][j] = col[(((i - s) % 4) + 4) % 4]; }
static const int LABEL[4] = {0, 2, 3, 1}, TW[4] = {0, 2, 3, 1};
static inline int sr_row_turn(const int *x) { int tot = 0; for (int j = 0; j < 13; j++) tot += (13 - j) * RANK(x[j]); return tot % 13; }
static inline int sr_col_turn(int g[4][13], int j) { int p = (j + 12) % 13;
    int v = LABEL[SUIT(g[1][p])] ^ TW[LABEL[SUIT(g[2][p])]] ^ TW[TW[LABEL[SUIT(g[3][p])]]];
    int su = LABEL[SUIT(g[0][j])] ^ LABEL[SUIT(g[1][j])] ^ LABEL[SUIT(g[2][j])] ^ LABEL[SUIT(g[3][j])];
    return v ^ su; }
static inline void stem(const int *m, int *o) { int g[4][13]; lay_cm(m, g);
    for (int a = 1; a <= 4; a++) { int i = a % 4; rotl(g[i], 13, sr_row_turn(g[(i + 3) % 4])); }
    for (int a = 1; a <= 13; a++) { int j = a % 13; rot_col_down(g, j, sr_col_turn(g, j)); }
    for (int i = 0; i < 4; i++) rotl(g[i], 13, i);           /* ShiftRows (0,1,2,3) */
    scoop_cm(g, o); }
static inline void mix_v11(const int *d, int *o) { uint8_t occ[52] = {0}; int grid[52]; int t = 0, fr = 2, fc = 0, prev = -1;
    for (int i = 0; i < 52; i++) { int r = 0, c = 0;
        if (i == 0) { r = 2; c = 0; }
        else { int tr = (fr + SUIT(prev)) & 3, tc = (fc + RANK(prev)) % 13;
            if (!occ[tr*13+tc]) { r = tr; c = tc; fr = tr; fc = tc; }
            else { int b = grid[tr*13+tc], row = (t + SUIT(b)) & 3, st = (tc + RANK(b)) % 13, found = 0;
                for (int a = 0; a < 4 && !found; a++, row = (row + 1) & 3)
                    for (int k = 0; k < 13; k++) { int cc = (st + k) % 13; if (!occ[row*13+cc]) { r = row; c = cc; found = 1; break; } }
                t = (t + 1) & 3; fr = (tr + SUIT(b)) & 3; fc = st; } }
        occ[r*13+c] = 1; grid[r*13+c] = d[i]; prev = d[i]; }
    memcpy(o, grid, 52 * sizeof(int)); }                     /* grid index r*13+c = row-major scoop */
static inline void compose(const int *m, const int *k, int *o) { for (int i = 0; i < 52; i++) o[k[i]] = m[i]; } /* o[j] = m[pos_K(j)] */

/* encrypt with explicit round keys; if st != NULL, st[r] = state after round r (r = 0 whitening .. 6) */
static inline void encrypt_keys(const int *p, int keys[7][52], int *c, int st[7][52]) { int m[52], x[52], y[52];
    compose(p, keys[0], m); if (st) memcpy(st[0], m, sizeof m);
    for (int r = 1; r <= 5; r++) { stem(m, x); mix_v11(x, y); compose(y, keys[r], m); if (st) memcpy(st[r], m, sizeof m); }
    stem(m, x); compose(x, keys[6], c); if (st) memcpy(st[6], c, 52 * sizeof(int)); }
static inline void encrypt(const int *p, const int *k0, int *c) { int keys[7][52]; expand_keys(k0, keys); encrypt_keys(p, keys, c, 0); }
