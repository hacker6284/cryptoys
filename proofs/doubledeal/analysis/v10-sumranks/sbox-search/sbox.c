/* v10 SumRanks (SPEC 3.3, W5c) as a stand-alone S-box on 4x13 grids, plus a differential survey.
   Grid cell index = 13*row + col. Card c: suit c/13 (0 clubs,1 hearts,2 spades,3 diamonds), rank c%13.
   GF(4) labels by suit: clubs 0, hearts w=2, spades w^2=3, diamonds 1. Multiply by w: 0->0,1->2,2->3,3->1. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
typedef uint8_t u8;
static const int LABEL[4] = {0, 2, 3, 1};
static const int TW[4] = {0, 2, 3, 1};
static inline int lab(int c) { return LABEL[c / 13]; }
static inline int rk(int c) { return c % 13; }
static int row_turn(const u8 *g, int i) { int s = 0; for (int j = 0; j < 13; j++) s += (13 - j) * rk(g[13*i+j]); return s % 13; }
static int col_value(const u8 *g, int j) { return lab(g[13+j]) ^ TW[lab(g[26+j])] ^ TW[TW[lab(g[39+j])]]; }
static int col_suits(const u8 *g, int j) { return lab(g[j]) ^ lab(g[13+j]) ^ lab(g[26+j]) ^ lab(g[39+j]); }
static void rotl13(u8 *row, int k) { u8 t[13]; for (int j = 0; j < 13; j++) t[j] = row[(j + k) % 13]; memcpy(row, t, 13); }
/* amounts[0..3] = row turns in order 1,2,3,0 ; amounts[4..16] = column turns in order 1..12,0 */
void sr_amt(const u8 *in, u8 *out, u8 *amt) {
    u8 g[52]; memcpy(g, in, 52);
    static const int RO[4] = {1, 2, 3, 0};
    for (int a = 0; a < 4; a++) { int i = RO[a]; int t = row_turn(g, (i + 3) % 4); if (amt) amt[a] = t; rotl13(g + 13*i, t); }
    for (int a = 0; a < 13; a++) { int j = (a + 1) % 13; int s = col_value(g, (j + 12) % 13) ^ col_suits(g, j);
        if (amt) amt[4 + a] = s;
        u8 c[4]; for (int i = 0; i < 4; i++) c[i] = g[13*i+j];
        for (int i = 0; i < 4; i++) g[13*i+j] = c[(i - s + 4) % 4]; }
    memcpy(out, g, 52);
}
void sr(const u8 *in, u8 *out) { sr_amt(in, out, 0); }
void sr_batch(int n, const u8 *in, u8 *out) { for (int i = 0; i < n; i++) sr(in + 52*i, out + 52*i); }

static uint64_t S[4];
static inline uint64_t rotl64(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static uint64_t nxt(void) { uint64_t r = rotl64(S[1] * 5, 7) * 9, t = S[1] << 17; S[2] ^= S[0]; S[3] ^= S[1]; S[1] ^= S[2]; S[0] ^= S[3]; S[2] ^= t; S[3] = rotl64(S[3], 45); return r; }
void seed(uint64_t s) { for (int i = 0; i < 4; i++) { s += 0x9E3779B97F4A7C15ULL; uint64_t z = s; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; S[i] = z ^ (z >> 31); } }
static void shuffle(u8 *d) { for (int i = 0; i < 52; i++) d[i] = i; for (int i = 51; i > 0; i--) { int j = nxt() % (i + 1); u8 t = d[i]; d[i] = d[j]; d[j] = t; } }
void rand_decks(int n, u8 *out) { for (int i = 0; i < n; i++) shuffle(out + 52*i); }
static uint64_t h52(const u8 *x) { uint64_t h = 1469598103934665603ULL; for (int i = 0; i < 52; i++) { h ^= x[i]; h *= 1099511628211ULL; } h ^= h >> 29; h *= 0xBF58476D1CE4E5B9ULL; return h ^ (h >> 32); }
static int cmpu(const void *a, const void *b) { uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y; }

/* mode 0: value difference tau (card relabelling): g' = tau o g; output diff tau_out with SR(g') = tau_out o SR(g).
   mode 1: position difference pi: g'[cell] = g[pi[cell]]; output diff pi_out with SR(g')[cell] = SR(g)[pi_out[cell]].
   res[0] = #decks with output diff == input diff (same-difference survival)
   res[1] = count of the most common output difference; res[2] = 1 if that most common one is the input diff
   res[3] = number of distinct output differences; top (52 bytes) = the most common output difference */
/* one random deck: draw g, apply the difference d (mode 0 value, mode 1 position), run SumRanks on both and
   write the output difference to od */
static void one_diff(int mode, const u8 *d, u8 *od) {
    u8 g[52], g2[52], y[52], y2[52], pos[52];
    shuffle(g);
    if (mode == 0) for (int c = 0; c < 52; c++) g2[c] = d[g[c]]; else for (int c = 0; c < 52; c++) g2[c] = g[d[c]];
    sr(g, y); sr(g2, y2);
    if (mode == 0) for (int c = 0; c < 52; c++) od[y[c]] = y2[c];
    else { for (int c = 0; c < 52; c++) pos[y[c]] = c; for (int c = 0; c < 52; c++) od[c] = pos[y2[c]]; }
}
void survey(int mode, const u8 *d, int n, uint64_t sd, long *res, u8 *top) {
    seed(sd); uint64_t *H = malloc(sizeof(uint64_t) * n); u8 od[52];
    uint64_t hin = h52(d); long same = 0;
    for (int t = 0; t < n; t++) { one_diff(mode, d, od); H[t] = h52(od); if (H[t] == hin) same++; }
    qsort(H, n, sizeof(uint64_t), cmpu);
    long best = 0, run = 0, distinct = 0; uint64_t bh = 0;
    for (int t = 0; t < n; t++) { if (t == 0 || H[t] != H[t-1]) { run = 0; distinct++; } run++; if (run > best) { best = run; bh = H[t]; } }
    res[0] = same; res[1] = best; res[2] = (bh == hin); res[3] = distinct;
    /* second pass over the same decks to recover the top output difference */
    seed(sd); memset(top, 255, 52);
    for (int t = 0; t < n; t++) { one_diff(mode, d, od); if (h52(od) == bh) { memcpy(top, od, 52); break; } }
    free(H);
}
/* fast same-difference survival only (value diff): counts decks where SR(tau o g) == tau o SR(g) */
long same_only(const u8 *tau, int n, uint64_t sd) {
    seed(sd); u8 g[52], g2[52], y[52], y2[52]; long same = 0;
    for (int t = 0; t < n; t++) { shuffle(g); for (int c = 0; c < 52; c++) g2[c] = tau[g[c]]; sr(g, y); sr(g2, y2);
        int ok = 1; for (int c = 0; c < 52; c++) if (y2[c] != tau[y[c]]) { ok = 0; break; } same += ok; }
    return same;
}
