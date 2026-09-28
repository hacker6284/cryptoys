#pragma once
/* Candidate GridCycle replacements (analysis only; nothing here is the spec).
   Cards 0..51: suit s = c/13 (clubs 0, hearts 1, spades 2, diamonds 3 -- the GridCycle order),
   rank r = c%13 + 1 (A=1..K=13). A layer maps a 52-card packet to a packet; each has an inverse.
   Layer ids:
     0  V11   v11 GridCycle (SPEC v11 3.5: ghost finger, blocker scan, blocker nudge). Reference.
     1  SR    v10 SumRanks alone, as a packet map (lay col-major, SumRanks, scoop col-major). Reference.
     2  PIVOT PivotRoll: lay row-major; rows 1,2,3,0: rotate row i left by rank of the card now at
              (i-1, col 0); columns 1..12,0: rotate column j down by suit of the card now at (row 0, j-1).
              Scoop row-major.
     3  TWIN  TwinSum: lay row-major; rows 1,2,3,0: rotate row i left by
                (sum_j (13-j) rank(x_j) + rank(x_0)) mod 13 over the row above x (as it is now);
              columns 1..12,0: rotate column j down by
                (s(y0) + s(y1) + 2 s(y2) + 3 s(y3) [left column, as it is now] + sum of own suits) mod 4.
              Scoop row-major.
     4  SRDUP verbatim SumRanks v10 on a row-major lay (to show the shared-symmetry pitfall).
     5  PASSK PassKey F itself used as the mixer (SPEC 3.7).
     6  PASSM PassMix: hand = packet, key pile empty. Repeat: pop controller C off the hand;
              rotate the hand left by rank(C) (mod hand size); rotate the key pile left by suit(C)
              (mod key size); put C on top of the key pile. Output = key pile.
     7  PASSM2 PassMix, then the same pass again (two passes).
     8  PASSMR PassMix with roles swapped: hand by suit, key pile by rank.
     9  PASSF  PassMix with a proper-cut fallback (rank cut goes to the key pile when rank >= hand size).
    10  PASSF2 PassMix-F (the proposed sketch): if rank < hand size, cut the hand by rank and the key pile by
              suit; otherwise cut the key pile by rank and the hand by suit. (Rules at the definition below.)
    11  TWINGF TwinSum with GF(4) columns (weights w^2,1,w,w^2 on the left column; sum is non-zero).
    12  PASSF2x2 two PassMix-F passes.
    13  PASSF3 PassMix-F plus an edge rule for the first/last 4 controllers (rank + 13*suit on one pile).
*/
#include <stdint.h>
#include <string.h>
#define SUIT(c) ((c) / 13)
#define RANK(c) ((c) % 13 + 1)
static inline uint64_t rnd_(uint64_t *s) { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; return *s; }
static inline void shuffle_(int *d, uint64_t *s) { for (int i = 0; i < 52; i++) d[i] = i;
    for (int i = 51; i > 0; i--) { int j = rnd_(s) % (i + 1); int x = d[i]; d[i] = d[j]; d[j] = x; } }
static inline void rotl(int *a, int n, int k) { if (n <= 1) return; k %= n; if (k < 0) k += n; if (!k) return;
    int t[52]; for (int i = 0; i < n; i++) t[i] = a[(i + k) % n]; memcpy(a, t, n * sizeof(int)); }

/* ---------- 0: v11 GridCycle ---------- */
static void v11_seats(const int *d, const int *table, int *seat, int *hand_out) {
    uint8_t occ[52] = {0}; int grid[52]; int t = 0, fr = 2, fc = 0, prev = -1;
    for (int i = 0; i < 52; i++) { int r, c;
        if (i == 0) { r = 2; c = 0; }
        else { int tr = (fr + SUIT(prev)) & 3, tc = (fc + RANK(prev)) % 13;
            if (!occ[tr*13+tc]) { r = tr; c = tc; fr = tr; fc = tc; }
            else { int b = table ? table[tr*13+tc] : grid[tr*13+tc];
                int row = (t + SUIT(b)) & 3, st = (tc + RANK(b)) % 13, found = 0;
                for (int a = 0; a < 4 && !found; a++, row = (row + 1) & 3)
                    for (int k = 0; k < 13; k++) { int cc = (st + k) % 13; if (!occ[row*13+cc]) { r = row; c = cc; found = 1; break; } }
                t = (t + 1) & 3; fr = (tr + SUIT(b)) & 3; fc = st; } }
        occ[r*13+c] = 1; seat[i] = r*13+c; prev = table ? table[r*13+c] : d[i]; grid[r*13+c] = prev;
        if (hand_out) hand_out[i] = prev; }
}
static void L_v11(const int *d, int *o) { int s[52]; v11_seats(d, 0, s, 0); for (int i = 0; i < 52; i++) o[s[i]] = d[i]; }
static void I_v11(const int *o, int *d) { int s[52]; v11_seats(0, o, s, d); }

/* ---------- grid helpers ---------- */
static void lay_rm(const int *d, int g[4][13]) { for (int k = 0; k < 52; k++) g[k/13][k%13] = d[k]; }
static void scoop_rm(int g[4][13], int *d) { for (int k = 0; k < 52; k++) d[k] = g[k/13][k%13]; }
static void lay_cm(const int *d, int g[4][13]) { for (int k = 0; k < 52; k++) g[k%4][k/4] = d[k]; }
static void scoop_cm(int g[4][13], int *d) { for (int k = 0; k < 52; k++) d[k] = g[k%4][k/4]; }
static void rot_row(int g[4][13], int i, int k) { rotl(g[i], 13, k); }
static void rot_col_down(int g[4][13], int j, int s) { int col[4]; for (int i = 0; i < 4; i++) col[i] = g[i][j];
    for (int i = 0; i < 4; i++) g[i][j] = col[(((i - s) % 4) + 4) % 4]; }

/* ---------- 1/4: SumRanks v10 ---------- */
static const int LABEL[4] = {0, 2, 3, 1}, TW[4] = {0, 2, 3, 1};
static int sr_row_turn(const int *x) { int tot = 0; for (int j = 0; j < 13; j++) tot += (13 - j) * RANK(x[j]); return tot % 13; }
static int sr_col_turn(int g[4][13], int j) { int p = (j + 12) % 13;
    int v = LABEL[SUIT(g[1][p])] ^ TW[LABEL[SUIT(g[2][p])]] ^ TW[TW[LABEL[SUIT(g[3][p])]]];
    int su = LABEL[SUIT(g[0][j])] ^ LABEL[SUIT(g[1][j])] ^ LABEL[SUIT(g[2][j])] ^ LABEL[SUIT(g[3][j])];
    return v ^ su; }
static void sr_fwd(int g[4][13]) {
    for (int a = 1; a <= 4; a++) { int i = a % 4; rot_row(g, i, sr_row_turn(g[(i + 3) % 4])); }
    for (int a = 1; a <= 13; a++) { int j = a % 13; rot_col_down(g, j, sr_col_turn(g, j)); } }
static void sr_inv(int g[4][13]) {
    for (int a = 13; a >= 1; a--) { int j = a % 13; rot_col_down(g, j, -sr_col_turn(g, j)); }
    for (int a = 4; a >= 1; a--) { int i = a % 4; rot_row(g, i, -sr_row_turn(g[(i + 3) % 4])); } }
static void L_sr(const int *d, int *o) { int g[4][13]; lay_cm(d, g); sr_fwd(g); scoop_cm(g, o); }
static void I_sr(const int *o, int *d) { int g[4][13]; lay_cm(o, g); sr_inv(g); scoop_cm(g, d); }
static void L_srdup(const int *d, int *o) { int g[4][13]; lay_rm(d, g); sr_fwd(g); scoop_rm(g, o); }
static void I_srdup(const int *o, int *d) { int g[4][13]; lay_rm(o, g); sr_inv(g); scoop_rm(g, d); }

/* ---------- 2: PivotRoll ---------- */
static void L_pivot(const int *d, int *o) { int g[4][13]; lay_rm(d, g);
    for (int a = 1; a <= 4; a++) { int i = a % 4; rot_row(g, i, RANK(g[(i + 3) % 4][0])); }
    for (int a = 1; a <= 13; a++) { int j = a % 13; rot_col_down(g, j, SUIT(g[0][(j + 12) % 13])); }
    scoop_rm(g, o); }
static void I_pivot(const int *o, int *d) { int g[4][13]; lay_rm(o, g);
    for (int a = 13; a >= 1; a--) { int j = a % 13; rot_col_down(g, j, -SUIT(g[0][(j + 12) % 13])); }
    for (int a = 4; a >= 1; a--) { int i = a % 4; rot_row(g, i, -RANK(g[(i + 3) % 4][0])); }
    scoop_rm(g, d); }

/* ---------- 3: TwinSum ---------- */
static int tw_row_turn(const int *x) { int tot = RANK(x[0]); for (int j = 0; j < 13; j++) tot += (13 - j) * RANK(x[j]); return tot % 13; }
static int tw_col_turn(int g[4][13], int j) { int p = (j + 12) % 13;
    int v = SUIT(g[0][p]) + SUIT(g[1][p]) + 2 * SUIT(g[2][p]) + 3 * SUIT(g[3][p]);
    int su = SUIT(g[0][j]) + SUIT(g[1][j]) + SUIT(g[2][j]) + SUIT(g[3][j]);
    return (v + su) & 3; }
static void L_twin(const int *d, int *o) { int g[4][13]; lay_rm(d, g);
    for (int a = 1; a <= 4; a++) { int i = a % 4; rot_row(g, i, tw_row_turn(g[(i + 3) % 4])); }
    for (int a = 1; a <= 13; a++) { int j = a % 13; rot_col_down(g, j, tw_col_turn(g, j)); }
    scoop_rm(g, o); }
static void I_twin(const int *o, int *d) { int g[4][13]; lay_rm(o, g);
    for (int a = 13; a >= 1; a--) { int j = a % 13; rot_col_down(g, j, -tw_col_turn(g, j)); }
    for (int a = 4; a >= 1; a--) { int i = a % 4; rot_row(g, i, -tw_row_turn(g[(i + 3) % 4])); }
    scoop_rm(g, d); }

/* ---------- 5: PassKey F (SPEC 3.7) ---------- */
/* piles stored top-first: hand[0..hn), key[0..kn) */
static void L_passk(const int *d, int *o) { int hand[52], key[52], hn = 51, kn = 0; memcpy(hand, d + 1, 51 * sizeof(int)); int C = d[0];
    for (;;) {
        if (hn) { int k = SUIT(C) % hn; rotl(hand, hn, k); }
        if (hn && RANK(C) < hn) rotl(hand, hn, RANK(C));
        else if (kn && RANK(C) < kn) rotl(key, kn, RANK(C));
        memmove(key + 1, key, kn * sizeof(int)); key[0] = C; kn++;
        if (!hn) break;
        C = hand[0]; memmove(hand, hand + 1, (hn - 1) * sizeof(int)); hn--; }
    memcpy(o, key, 52 * sizeof(int)); }
static void I_passk(const int *o, int *d) { int hand[52], key[52], hn = 0, kn = 52; memcpy(key, o, 52 * sizeof(int));
    while (kn) { int C = key[0]; memmove(key, key + 1, (kn - 1) * sizeof(int)); kn--;
        int n = hn;
        if (n > 0 && RANK(C) < n) rotl(hand, hn, -RANK(C));
        else if (kn && RANK(C) < kn) rotl(key, kn, -RANK(C));
        if (n > 0) { int k = SUIT(C) % n; rotl(hand, hn, -k); }
        memmove(hand + 1, hand, hn * sizeof(int)); hand[0] = C; hn++; }
    memcpy(d, hand, 52 * sizeof(int)); }

/* ---------- 6/8: PassMix ---------- */
static _Thread_local int PM_ROLES = 0; /* 0: hand by rank, key by suit; 1: hand by suit, key by rank */
static inline int pm_h(int C) { return PM_ROLES ? SUIT(C) : RANK(C); }
static inline int pm_k(int C) { return PM_ROLES ? RANK(C) : SUIT(C); }
static void L_passm(const int *d, int *o) { int hand[52], key[52], hn = 52, kn = 0; memcpy(hand, d, 52 * sizeof(int));
    while (hn) { int C = hand[0]; memmove(hand, hand + 1, (hn - 1) * sizeof(int)); hn--;
        rotl(hand, hn, pm_h(C)); rotl(key, kn, pm_k(C));
        memmove(key + 1, key, kn * sizeof(int)); key[0] = C; kn++; }
    memcpy(o, key, 52 * sizeof(int)); }
static void I_passm(const int *o, int *d) { int hand[52], key[52], hn = 0, kn = 52; memcpy(key, o, 52 * sizeof(int));
    while (kn) { int C = key[0]; memmove(key, key + 1, (kn - 1) * sizeof(int)); kn--;
        rotl(key, kn, -pm_k(C)); rotl(hand, hn, -pm_h(C));
        memmove(hand + 1, hand, hn * sizeof(int)); hand[0] = C; hn++; }
    memcpy(d, hand, 52 * sizeof(int)); }
static void L_passm2(const int *d, int *o) { int t[52]; L_passm(d, t); L_passm(t, o); }
static void I_passm2(const int *o, int *d) { int t[52]; I_passm(o, t); I_passm(t, d); }
static void L_passmr(const int *d, int *o) { PM_ROLES = 1; L_passm(d, o); PM_ROLES = 0; }
static void I_passmr(const int *o, int *d) { PM_ROLES = 1; I_passm(o, d); PM_ROLES = 0; }

/* ---------- 9/10: PassMix with a proper-cut fallback ----------
   9  PASSF  pop C (n = hand size, m = key size after the pop). If rank(C) < n: cut the hand by rank(C);
             else cut the key pile by rank(C) (mod m). Then cut the key pile by suit(C) (mod m).
             Put C on top of the key pile.
  10  PASSF2 as 9, but in the fallback case the suit cut goes to the hand instead (mod n). */
static _Thread_local int PF_VAR = 0;
static void L_passf(const int *d, int *o) { int hand[52], key[52], hn = 52, kn = 0; memcpy(hand, d, 52 * sizeof(int));
    while (hn) { int C = hand[0]; memmove(hand, hand + 1, (hn - 1) * sizeof(int)); hn--;
        if (RANK(C) < hn) { rotl(hand, hn, RANK(C)); rotl(key, kn, SUIT(C)); }
        else { rotl(key, kn, RANK(C)); if (PF_VAR) rotl(hand, hn, SUIT(C)); else rotl(key, kn, SUIT(C)); }
        memmove(key + 1, key, kn * sizeof(int)); key[0] = C; kn++; }
    memcpy(o, key, 52 * sizeof(int)); }
static void I_passf(const int *o, int *d) { int hand[52], key[52], hn = 0, kn = 52; memcpy(key, o, 52 * sizeof(int));
    while (kn) { int C = key[0]; memmove(key, key + 1, (kn - 1) * sizeof(int)); kn--;
        if (RANK(C) < hn) { rotl(key, kn, -SUIT(C)); rotl(hand, hn, -RANK(C)); }
        else { if (PF_VAR) rotl(hand, hn, -SUIT(C)); else rotl(key, kn, -SUIT(C)); rotl(key, kn, -RANK(C)); }
        memmove(hand + 1, hand, hn * sizeof(int)); hand[0] = C; hn++; }
    memcpy(d, hand, 52 * sizeof(int)); }
static void L_passf2(const int *d, int *o) { PF_VAR = 1; L_passf(d, o); PF_VAR = 0; }
static void I_passf2(const int *o, int *d) { PF_VAR = 1; I_passf(o, d); PF_VAR = 0; }

/* ---------- 11: TwinSum-GF: TWIN with SumRanks-style GF(4) columns whose weights sum to non-zero ----------
   rows as TWIN; column j turns by  V'(left) xor S(own),  V'(y) = w^2 l(y0) + l(y1) + w l(y2) + w^2 l(y3)
   (GF(4) labels as SumRanks: clubs 0, diamonds 1, hearts w, spades w^2). */
static int tg_col_turn(int g[4][13], int j) { int p = (j + 12) % 13;
    int v = TW[TW[LABEL[SUIT(g[0][p])]]] ^ LABEL[SUIT(g[1][p])] ^ TW[LABEL[SUIT(g[2][p])]] ^ TW[TW[LABEL[SUIT(g[3][p])]]];
    int su = LABEL[SUIT(g[0][j])] ^ LABEL[SUIT(g[1][j])] ^ LABEL[SUIT(g[2][j])] ^ LABEL[SUIT(g[3][j])];
    return v ^ su; }
static void L_twgf(const int *d, int *o) { int g[4][13]; lay_rm(d, g);
    for (int a = 1; a <= 4; a++) { int i = a % 4; rot_row(g, i, tw_row_turn(g[(i + 3) % 4])); }
    for (int a = 1; a <= 13; a++) { int j = a % 13; rot_col_down(g, j, tg_col_turn(g, j)); }
    scoop_rm(g, o); }
static void I_twgf(const int *o, int *d) { int g[4][13]; lay_rm(o, g);
    for (int a = 13; a >= 1; a--) { int j = a % 13; rot_col_down(g, j, -tg_col_turn(g, j)); }
    for (int a = 4; a >= 1; a--) { int i = a % 4; rot_row(g, i, -tw_row_turn(g[(i + 3) % 4])); }
    scoop_rm(g, d); }

/* ---------- 13: PASSF3 = PassMix-F with an edge rule ----------
   As PASSF2, except while the key pile has fewer than 4 cards (first 4 controllers) the suit cannot be told
   apart on the key pile, so the hand is cut by rank + 13*suit instead (and the key pile is not cut); and while
   the hand has fewer than 4 cards in a fallback step, the key pile is cut by rank + 13*suit (hand not cut). */
static void pf3_act(int C, int hn, int kn, int *h, int *g) { int r = RANK(C), s = SUIT(C);
    if (r < hn) { if (kn >= 4) { *h = r; *g = s; } else { *h = r + 13 * s; *g = 0; } }
    else { if (hn >= 4) { *h = s; *g = r; } else { *h = 0; *g = r + 13 * s; } } }
static void L_passf3(const int *d, int *o) { int hand[52], key[52], hn = 52, kn = 0; memcpy(hand, d, 52 * sizeof(int));
    while (hn) { int C = hand[0], h, g; memmove(hand, hand + 1, (hn - 1) * sizeof(int)); hn--;
        pf3_act(C, hn, kn, &h, &g); rotl(hand, hn, h); rotl(key, kn, g);
        memmove(key + 1, key, kn * sizeof(int)); key[0] = C; kn++; }
    memcpy(o, key, 52 * sizeof(int)); }
static void I_passf3(const int *o, int *d) { int hand[52], key[52], hn = 0, kn = 52; memcpy(key, o, 52 * sizeof(int));
    while (kn) { int C = key[0], h, g; memmove(key, key + 1, (kn - 1) * sizeof(int)); kn--;
        pf3_act(C, hn, kn, &h, &g); rotl(key, kn, -g); rotl(hand, hn, -h);
        memmove(hand + 1, hand, hn * sizeof(int)); hand[0] = C; hn++; }
    memcpy(d, hand, 52 * sizeof(int)); }

/* ---------- 12: PASSF2 twice ---------- */
static void L_pf2x2(const int *d, int *o) { int t[52]; L_passf2(d, t); L_passf2(t, o); }
static void I_pf2x2(const int *o, int *d) { int t[52]; I_passf2(o, t); I_passf2(t, d); }

typedef void (*LayerFn)(const int *, int *);
__attribute__((unused)) static const char *LNAME[] = {"V11", "SR", "PIVOT", "TWIN", "SRDUP", "PASSK", "PASSM", "PASSM2", "PASSMR", "PASSF", "PASSF2", "TWINGF", "PASSF2x2", "PASSF3"};
__attribute__((unused)) static LayerFn LFWD[] = {L_v11, L_sr, L_pivot, L_twin, L_srdup, L_passk, L_passm, L_passm2, L_passmr, L_passf, L_passf2, L_twgf, L_pf2x2, L_passf3};
__attribute__((unused)) static LayerFn LINV[] = {I_v11, I_sr, I_pivot, I_twin, I_srdup, I_passk, I_passm, I_passm2, I_passmr, I_passf, I_passf2, I_twgf, I_pf2x2, I_passf3};
#define NLAYERS 14

/* v10 unkeyed stem: lay_cm, SumRanks v10, ShiftRows, scoop_cm */
__attribute__((unused)) static void stem(const int *m, int *out) { int g[4][13]; lay_cm(m, g); sr_fwd(g);
    for (int i = 0; i < 4; i++) rot_row(g, i, i);
    scoop_cm(g, out); }
