/* Fast C port of DoubleDeal v9 (analysis only). Must match dd_v9.py;
   checked by check_port.py against the port and the committed vectors. */
#include <string.h>
#define N 52
static inline int suit(int c) { return c / 13; }
static inline int rnk(int c) { return c % 13 + 1; }

static void rotl(int *xs, int n, int k) {
    if (n == 0) return;
    k %= n; if (k < 0) k += n;
    if (!k) return;
    int t[N]; for (int i = 0; i < n; i++) t[i] = xs[(i + k) % n];
    memcpy(xs, t, sizeof(int) * n);
}
static void lay_cm(const int *d, int g[4][13]) { for (int k = 0; k < N; k++) g[k % 4][k / 4] = d[k]; }
static void scoop_cm(int g[4][13], int *d) { for (int c = 0; c < 13; c++) for (int r = 0; r < 4; r++) d[4 * c + r] = g[r][c]; }
static void scoop_rm(int g[4][13], int *d) { for (int r = 0; r < 4; r++) for (int c = 0; c < 13; c++) d[13 * r + c] = g[r][c]; }

static void sum_ranks(int g[4][13]) {
    for (int i = 0; i < 4; i++) { int s = 0; for (int j = 0; j < 13; j++) s += rnk(g[i][j]); rotl(g[i], 13, s % 13); }
    for (int j = 0; j < 13; j++) {
        int col[4], s = 0;
        for (int i = 0; i < 4; i++) { col[i] = g[i][j]; s += rnk(col[i]) + suit(col[i]); }
        s %= 4;
        for (int i = 0; i < 4; i++) g[i][j] = col[((i - s) % 4 + 4) % 4];
    }
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
            if (!occ[tr][tc]) { r = tr; c = tc; }
            else {
                int found = 0;
                for (int a = 0; a < 4 && !found; a++) {
                    int row = t;
                    for (int k = 0; k < 13; k++) { int col = (tc + k) % 13; if (!occ[row][col]) { r = row; c = col; found = 1; break; } }
                    if (found) t = (t + 1) % 4; else t = (t + 1) % 4;
                    if (found) break;
                }
            }
        }
        occ[r][c] = 1; grid[r][c] = d[i]; pr = r; pc = c;
    }
    scoop_rm(grid, out);
}
void compose(const int *m, const int *k, int *out) { int pos[N]; for (int i = 0; i < N; i++) pos[k[i]] = i; for (int j = 0; j < N; j++) out[j] = m[pos[j]]; }

void passkey(const int *deck, int *out) {
    int hand[N], key[N], nh = N, nk = 0;
    memcpy(hand, deck, sizeof hand);
    for (int it = 0; it < N; it++) {
        int c = hand[0]; memmove(hand, hand + 1, sizeof(int) * (nh - 1)); nh--;
        if (nh) { int k = suit(c) % nh; if (k > 0) rotl(hand, nh, k); }
        if (nh && rnk(c) < nh) rotl(hand, nh, rnk(c));
        else if (nk && rnk(c) < nk) rotl(key, nk, rnk(c));
        memmove(key + 1, key, sizeof(int) * nk); key[0] = c; nk++;
    }
    memcpy(out, key, sizeof key);
}
/* keys: 7*52 ints. s = compose(m,K0); nfull full rounds with K1..; final round with K_{nfull+1} if fin. */
void enc(const int *m, const int *keys, int nfull, int fin, int *out) {
    int s[N], u[N], v[N];
    compose(m, keys, s);
    for (int r = 1; r <= nfull; r++) { stem(s, u); mix_columns(u, v); compose(v, keys + 52 * r, s); }
    if (fin) { stem(s, u); compose(u, keys + 52 * (nfull + 1), s); }
    memcpy(out, s, sizeof s);
}
void expand(const int *k0, int *keys) { memcpy(keys, k0, sizeof(int) * N); for (int r = 1; r < 7; r++) passkey(keys + 52 * (r - 1), keys + 52 * r); }
/* batch: n messages (n*52) and n key schedules (n*7*52) */
void enc_batch(int n, const int *ms, const int *keys, int nfull, int fin, int *out) {
    for (int i = 0; i < n; i++) enc(ms + 52 * i, keys + 364 * i, nfull, fin, out + 52 * i);
}
void expand_batch(int n, const int *k0s, int *keys) { for (int i = 0; i < n; i++) expand(k0s + 52 * i, keys + 364 * i); }
