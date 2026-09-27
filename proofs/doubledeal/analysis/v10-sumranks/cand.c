/* C port of DoubleDeal v9 with candidate patches (analysis only; NOT a spec).
   var bits: 1 = B4 "slide along" (overflow scans the blocked target row from the blocked
   column, next row down if full; no marker counter), 2 = R2 (SumRanks rows, columns, rows
   again), 4 = G "step again" (a blocked card repeats its step from the blocked seat until a
   free seat; if it comes back to its own seat, the v9 marker-row scan), 8 = A3 (SumRanks column
   weight rank - suit, i.e. rank + 3 suit mod 4), 16 = SP (v10 experiment: SumRanks columns use
   rank only, then SuitProduct: each column rotates by prod(suit+1) mod 5, taken mod 4), 32 = PW
   (v10 experiment: chained position-weighted SumRanks, see sum_ranks_pw), 64 = PW2 (rows as PW
   but weighing rank+suit; columns: v9-style own-column rotation by sum(suit) mod 4), 128 = PW3 (PW2, then a chained column pass: columns in order 1..12,0,
   column j rotates down by (sum_r (r+1)(rank + 4 suit)(column j-1 [r]) mod 13) mod 4), 256 = SR2 (v9 SumRanks twice: rows, cols, rows, cols),
   512 = SR3 (three times). W family (index-weighted, see sum_ranks_w): 1024 W1, 2048 W2, 4096 W3,
   8192 W4, 32768 W5, 65536 W5b, 131072 W5c; 16384 = two passes of the chosen W. var 0 = v9. Checked against candidates.py by check_cand.py. */
#include <string.h>
#define N 52
static int VAR = 0;
void set_var(int v) { VAR = v; }
static inline int suit(int c) { return c / 13; }
static inline int rnk(int c) { return c % 13 + 1; }
static void rotl(int *xs, int n, int k) {
    k %= n; if (k < 0) k += n; if (!k) return;
    int t[N]; for (int i = 0; i < n; i++) t[i] = xs[(i + k) % n]; memcpy(xs, t, sizeof(int) * n);
}
static void lay_cm(const int *d, int g[4][13]) { for (int k = 0; k < N; k++) g[k % 4][k / 4] = d[k]; }
static void scoop_cm(int g[4][13], int *d) { for (int c = 0; c < 13; c++) for (int r = 0; r < 4; r++) d[4 * c + r] = g[r][c]; }
static void scoop_rm(int g[4][13], int *d) { for (int r = 0; r < 4; r++) for (int c = 0; c < 13; c++) d[13 * r + c] = g[r][c]; }
static void sum_ranks(int g[4][13]);
static void rows(int g[4][13]) { for (int i = 0; i < 4; i++) { int s = 0; for (int j = 0; j < 13; j++) s += rnk(g[i][j]); rotl(g[i], 13, s % 13); } }
static void cols(int g[4][13]) {
    for (int j = 0; j < 13; j++) {
        int col[4], s = 0;
        for (int i = 0; i < 4; i++) { col[i] = g[i][j]; s += (VAR & 8) ? rnk(col[i]) + 3 * suit(col[i]) : rnk(col[i]) + suit(col[i]); }
        s %= 4; for (int i = 0; i < 4; i++) g[i][j] = col[((i - s) % 4 + 4) % 4];
    }
}
static void cols_rank(int g[4][13]) {   /* SP: column step with rank-only weights */
    for (int j = 0; j < 13; j++) {
        int col[4], s = 0;
        for (int i = 0; i < 4; i++) { col[i] = g[i][j]; s += rnk(col[i]); }
        s %= 4; for (int i = 0; i < 4; i++) g[i][j] = col[((i - s) % 4 + 4) % 4];
    }
}
static void suit_product(int g[4][13]) { /* SP: rotate each column by prod(suit+1) mod 5 (1..4), mod 4 */
    for (int j = 0; j < 13; j++) {
        int col[4], p = 1;
        for (int i = 0; i < 4; i++) { col[i] = g[i][j]; p = p * (suit(col[i]) + 1) % 5; }
        int s = p % 4; for (int i = 0; i < 4; i++) g[i][j] = col[((i - s) % 4 + 4) % 4];
    }
}
/* PW: rows in order 1,2,3,0: row i rotates left by sum_c (c+1) rank(row i-1 [c]) mod 13 (row i-1 as it
   is at that moment); then columns in order 1..12,0: column j rotates down by
   sum_r (r+1) (rank+suit)(column j-1 [r]) mod 4. Invertible: undo in reverse order. */
static int roww(int g[4][13], int i) { int s = 0; for (int c = 0; c < 13; c++) s += (c + 1) * rnk(g[i][c]); return s % 13; }
static int colwt(int g[4][13], int j) { int s = 0; for (int r = 0; r < 4; r++) s += (r + 1) * (rnk(g[r][j]) + suit(g[r][j])); return s % 4; }
static void sum_ranks_pw(int g[4][13]) {
    for (int a = 1; a <= 4; a++) { int i = a % 4; rotl(g[i], 13, roww(g, (i + 3) % 4)); }
    for (int a = 1; a <= 13; a++) {
        int j = a % 13, s = colwt(g, (j + 12) % 13), col[4];
        for (int i = 0; i < 4; i++) col[i] = g[i][j];
        for (int i = 0; i < 4; i++) g[i][j] = col[((i - s) % 4 + 4) % 4];
    }
}
static int roww2(int g[4][13], int i) { int s = 0; for (int c = 0; c < 13; c++) s += (c + 1) * (rnk(g[i][c]) + suit(g[i][c])); return s % 13; }
static void sum_ranks_pw2(int g[4][13]) {
    for (int a = 1; a <= 4; a++) { int i = a % 4; rotl(g[i], 13, roww2(g, (i + 3) % 4)); }
    for (int j = 0; j < 13; j++) {
        int col[4], s = 0;
        for (int i = 0; i < 4; i++) { col[i] = g[i][j]; s += suit(col[i]); }
        s %= 4; for (int i = 0; i < 4; i++) g[i][j] = col[((i - s) % 4 + 4) % 4];
    }
}
static int colw3(int g[4][13], int j) { int s = 0; for (int r = 0; r < 4; r++) s += (r + 1) * (rnk(g[r][j]) + 4 * suit(g[r][j])); return (s % 13) % 4; }
/* W family. Rows (chained, order 1,2,3,0): row i rotates left by U mod 13 of row i-1, where
   U = sum_c (13 - c) v(card at c) (running total of running totals; weights 13..1, so the leftmost
   card has weight 13 = 0 mod 13); v = rank (W1, W3, W4) or rank + suit (W2).
   Columns: W1/W2 = v9 column step (own column, sum(rank+suit) mod 4).
   W3 = chained (order 1..12,0): column j rotates down by (sum_r (4 - r)(suit+1) of column j-1 mod 5) mod 4.
   W4 = as W3 plus the column's own sum(suit): (own sum(suit) + chained mod-5 value) mod 4. */
static int wrow(int g[4][13], int i, int ws) { int U = 0; for (int c = 0; c < 13; c++) U += (13 - c) * (rnk(g[i][c]) + (ws ? suit(g[i][c]) : 0)); return U % 13; }
static void w_rows(int g[4][13], int ws) { for (int a = 1; a <= 4; a++) { int i = a % 4; rotl(g[i], 13, wrow(g, (i + 3) % 4, ws)); } }
static int wcol5(int g[4][13], int j) { int U = 0; for (int r = 0; r < 4; r++) U += (4 - r) * (suit(g[r][j]) + 1); return U % 5; }
static void w_cols_chain(int g[4][13], int own) {
    for (int a = 1; a <= 13; a++) {
        int j = a % 13, s = wcol5(g, (j + 12) % 13), col[4];
        if (own) for (int i = 0; i < 4; i++) s += suit(g[i][j]);
        s %= 4;
        for (int i = 0; i < 4; i++) col[i] = g[i][j];
        for (int i = 0; i < 4; i++) g[i][j] = col[((i - s) % 4 + 4) % 4];
    }
}
/* W5: columns = chained GF(4)-weighted suit sum. GF(4) labels 0=00, 1=01, w=10, w^2=11 (w^2 = w + 1,
   addition = XOR). Suits: clubs 0, diamonds 1, hearts w, spades w^2. Column value of column j-1 =
   0*s(row0) + 1*s(row1) + w*s(row2) + w^2*s(row3); column j (order 1..12,0) rotates down by the 2-bit label.
   W5b: the same with s replaced by s XOR (rank mod 4) as a 2-bit label.
   W5c: W5 label XOR the column's own unweighted GF(4) suit sum (XOR of its 4 suit labels; rotation-invariant,
   so still invertible) -- the W4 trick, to cover the weight-0 top row. */
static const int GFMUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static const int SUITGF[4] = {0, 2, 3, 1};   /* our suits: 0 clubs, 1 hearts, 2 spades, 3 diamonds */
static int gfv(int card, int b) { int v = SUITGF[suit(card)]; return b ? v ^ (rnk(card) % 4) : v; }
static int gfcol(int g[4][13], int j, int b) { int v = 0; for (int r = 0; r < 4; r++) v ^= GFMUL[r][gfv(g[r][j], b)]; return v; }
static void gf_cols_chain(int g[4][13], int b) {
    for (int a = 1; a <= 13; a++) {
        int j = a % 13, s = gfcol(g, (j + 12) % 13, b & 1), col[4];
        if (b & 2) for (int i = 0; i < 4; i++) s ^= gfv(g[i][j], 0);
        for (int i = 0; i < 4; i++) col[i] = g[i][j];
        for (int i = 0; i < 4; i++) g[i][j] = col[((i - s) % 4 + 4) % 4];
    }
}
static void sum_ranks_w(int g[4][13]) {
    int passes = (VAR & 16384) ? 2 : 1;
    for (int p = 0; p < passes; p++) {
        if (VAR & 1024) { w_rows(g, 0); cols(g); }
        else if (VAR & 2048) { w_rows(g, 1); cols(g); }
        else if (VAR & 32768) { w_rows(g, 0); gf_cols_chain(g, 0); }
        else if (VAR & 65536) { w_rows(g, 0); gf_cols_chain(g, 1); }
        else if (VAR & 131072) { w_rows(g, 0); gf_cols_chain(g, 2); }
        else if (VAR & 4096) { w_rows(g, 0); w_cols_chain(g, 0); }
        else { w_rows(g, 0); w_cols_chain(g, 1); }
    }
}
/* SumRanks-only commute counts for the current VAR: out[0] += 1 per deck where it commutes */
void sr_only_var(int n, const int *ds, const int *sig, long *out) {
    for (int s = 0; s < n; s++) {
        const int *d = ds + N * s; int d2[N], g[4][13], h[4][13], ok = 1;
        for (int i = 0; i < N; i++) d2[i] = sig[d[i]];
        lay_cm(d, g); lay_cm(d2, h); sum_ranks(g); sum_ranks(h);
        for (int r = 0; r < 4 && ok; r++) for (int c = 0; c < 13; c++) if (h[r][c] != sig[g[r][c]]) { ok = 0; break; }
        out[0] += ok;
    }
}
static void sum_ranks(int g[4][13]) {
    if (VAR & (1024 | 2048 | 4096 | 8192 | 32768 | 65536 | 131072)) { sum_ranks_w(g); return; }
    if (VAR & 128) {
        sum_ranks_pw2(g);
        for (int a = 1; a <= 13; a++) {
            int j = a % 13, s = colw3(g, (j + 12) % 13), col[4];
            for (int i = 0; i < 4; i++) col[i] = g[i][j];
            for (int i = 0; i < 4; i++) g[i][j] = col[((i - s) % 4 + 4) % 4];
        }
        return;
    }
    if (VAR & 64) { sum_ranks_pw2(g); return; }
    if (VAR & (256 | 512)) { int k = (VAR & 512) ? 3 : 2; for (int a = 0; a < k; a++) { rows(g); cols(g); } return; }
    if (VAR & 32) { sum_ranks_pw(g); return; }
    rows(g);
    if (VAR & 16) { cols_rank(g); suit_product(g); return; }
    cols(g); if (VAR & 2) rows(g);
}
static void shift_rows(int g[4][13]) { for (int i = 0; i < 4; i++) rotl(g[i], 13, i); }
void stem(const int *m, int *out) { int g[4][13]; lay_cm(m, g); sum_ranks(g); shift_rows(g); scoop_cm(g, out); }
void mix_columns(const int *d, int *out) {
    int grid[4][13], occ[4][13]; memset(occ, 0, sizeof occ);
    int t = 0, pr = 0, pc = 0;
    for (int i = 0; i < N; i++) {
        int r = 2, c = 0;
        if (i > 0) {
            int card = d[i - 1];
            int tr = (pr + suit(card)) % 4, tc = (pc + rnk(card)) % 13;
            int hop = 0;
            if (!occ[tr][tc]) { r = tr; c = tc; }
            else if (VAR & 4) {  /* G "step again": repeat the card's step until a free seat or back at the start */
                int hr = tr, hc = tc;
                for (;;) {
                    hr = (hr + suit(card)) % 4; hc = (hc + rnk(card)) % 13;
                    if (hr == pr && hc == pc) break;
                    if (!occ[hr][hc]) { r = hr; c = hc; hop = 1; break; }
                }
            }
            if (occ[tr][tc] && !hop) {
                int row0 = (VAR & 1) ? tr : t, found = 0;
                for (int a = 0; a < 4 && !found; a++) {
                    int row = (row0 + a) % 4;
                    for (int k = 0; k < 13; k++) { int col = (tc + k) % 13; if (!occ[row][col]) { r = row; c = col; found = 1; break; } }
                }
                if (!(VAR & 1)) t = (r + 1) % 4;   /* v9: marker moves to the row after the seat used */
            }
        }
        occ[r][c] = 1; grid[r][c] = d[i]; pr = r; pc = c;
    }
    scoop_rm(grid, out);
}
void compose(const int *m, const int *k, int *out) { int pos[N]; for (int i = 0; i < N; i++) pos[k[i]] = i; for (int j = 0; j < N; j++) out[j] = m[pos[j]]; }
void passkey(const int *deck, int *out) {
    int hand[N], key[N], nh = N, nk = 0; memcpy(hand, deck, sizeof hand);
    for (int it = 0; it < N; it++) {
        int c = hand[0]; memmove(hand, hand + 1, sizeof(int) * (nh - 1)); nh--;
        if (nh) { int k = suit(c) % nh; if (k > 0) rotl(hand, nh, k); }
        if (nh && rnk(c) < nh) rotl(hand, nh, rnk(c));
        else if (nk && rnk(c) < nk) rotl(key, nk, rnk(c));
        memmove(key + 1, key, sizeof(int) * nk); key[0] = c; nk++;
    }
    memcpy(out, key, sizeof key);
}
void enc(const int *m, const int *keys, int nfull, int fin, int *out) {
    int s[N], u[N], v[N]; compose(m, keys, s);
    for (int r = 1; r <= nfull; r++) { stem(s, u); mix_columns(u, v); compose(v, keys + 52 * r, s); }
    if (fin) { stem(s, u); compose(u, keys + 52 * (nfull + 1), s); }
    memcpy(out, s, sizeof s);
}
void expand(const int *k0, int *keys) { memcpy(keys, k0, sizeof(int) * N); for (int r = 1; r < 7; r++) passkey(keys + 52 * (r - 1), keys + 52 * r); }
void enc_batch(int n, const int *ms, const int *keys, int nfull, int fin, int *out) { for (int i = 0; i < n; i++) enc(ms + 52 * i, keys + 364 * i, nfull, fin, out + 52 * i); }
void expand_batch(int n, const int *k0s, int *keys) { for (int i = 0; i < n; i++) expand(k0s + 52 * i, keys + 364 * i); }
/* per-layer commute counts for relabelling sig (52 ints) on n random decks ds:
   out[0] += stem commutes, out[1] += mix commutes (fresh deck), out[2] += round (stem+mix) commutes */
void layer_counts(int n, const int *ds, const int *sig, long *out) {
    for (int s = 0; s < n; s++) {
        const int *d = ds + N * s; int d2[N], u[N], u2[N], v[N], v2[N], ok = 1;
        for (int i = 0; i < N; i++) d2[i] = sig[d[i]];
        stem(d, u); stem(d2, u2); for (int i = 0; i < N; i++) if (u2[i] != sig[u[i]]) { ok = 0; break; }
        out[0] += ok;
        int okm = 1; mix_columns(d, v); mix_columns(d2, v2); for (int i = 0; i < N; i++) if (v2[i] != sig[v[i]]) { okm = 0; break; }
        out[1] += okm;
        if (ok) { int w[N], w2[N], okr = 1; mix_columns(u, w); mix_columns(u2, w2); for (int i = 0; i < N; i++) if (w2[i] != sig[w[i]]) { okr = 0; break; } out[2] += okr; }
    }
}
