/* Per-layer instrumentation for the v9 swap analysis (analysis only).
   Built together with dd9.c (the checked C port). */
#include "dd9.c"

static void swapc(const int *a, int *b, int x, int y) {
    for (int i = 0; i < N; i++) b[i] = a[i] == x ? y : a[i] == y ? x : a[i];
}
static int eqarr(const int *a, const int *b) { for (int i = 0; i < N; i++) if (a[i] != b[i]) return 0; return 1; }

/* GridCycle walk that also records the seat sequence, the overflow counter
   after each step, and for every step whether the target was occupied. */
static void walk_rec(const int *d, int *seat, int *tt, int *blocked) {
    int occ[4][13]; memset(occ, 0, sizeof occ);
    int t = 0, pr = 0, pc = 0;
    for (int i = 0; i < N; i++) {
        int r = 2, c = 0, b = 0;
        if (i > 0) {
            int card = d[i - 1];
            int tr = (pr + suit(card)) % 4, tc = (pc + rnk(card)) % 13;
            if (!occ[tr][tc]) { r = tr; c = tc; }
            else {
                b = 1;
                int found = 0;
                for (int a = 0; a < 4 && !found; a++) {
                    for (int k = 0; k < 13; k++) { int col = (tc + k) % 13; if (!occ[t][col]) { r = t; c = col; found = 1; break; } }
                    t = (t + 1) % 4;
                }
            }
        }
        occ[r][c] = 1; pr = r; pc = c; seat[i] = 13 * r + c; tt[i] = t; blocked[i] = b;
    }
}

/* For n random decks ms (states entering a round) and swap (x,y):
   out[8*i + ...] = { S: stem commutes, G: mix commutes on u = stem(m) (valid if S),
                      px, py: positions of x,y in u, bxA, byA: target blocked at the step after
                      x / y in run A (u), bxB, byB: same in run B (sigma u) } */
void layer_batch(int n, const int *ms, int x, int y, int *out) {
    for (int s = 0; s < n; s++) {
        const int *m = ms + N * s;
        int m2[N], u[N], u2[N], su[N], v[N], v2[N], sv[N];
        swapc(m, m2, x, y);
        stem(m, u); stem(m2, u2); swapc(u, su, x, y);
        int S = eqarr(u2, su), G = 0, px = -1, py = -1, bxA = -1, byA = -1, bxB = -1, byB = -1;
        if (S) {
            mix_columns(u, v); mix_columns(u2, v2); swapc(v, sv, x, y); G = eqarr(v2, sv);
            int seatA[N], tA[N], blA[N], seatB[N], tB[N], blB[N];
            walk_rec(u, seatA, tA, blA); walk_rec(u2, seatB, tB, blB);
            for (int i = 0; i < N; i++) { if (u[i] == x) px = i; if (u[i] == y) py = i; }
            if (px < N - 1) { bxA = blA[px + 1]; bxB = blB[px + 1]; }
            if (py < N - 1) { byA = blA[py + 1]; byB = blB[py + 1]; }
        }
        int *o = out + 8 * s;
        o[0] = S; o[1] = G; o[2] = px; o[3] = py; o[4] = bxA; o[5] = byA; o[6] = bxB; o[7] = byB;
    }
}

/* mix-only commute on arbitrary decks (no stem): out[i] = mix(sigma d) == sigma mix(d) */
void mix_batch(int n, const int *ds, int x, int y, int *out) {
    for (int s = 0; s < n; s++) {
        const int *d = ds + N * s; int d2[N], v[N], v2[N], sv[N];
        swapc(d, d2, x, y); mix_columns(d, v); mix_columns(d2, v2); swapc(v, sv, x, y);
        out[s] = eqarr(v2, sv);
    }
}
/* stem-only commute */
void stem_batch(int n, const int *ds, int x, int y, int *out) {
    for (int s = 0; s < n; s++) {
        const int *d = ds + N * s; int d2[N], v[N], v2[N], sv[N];
        swapc(d, d2, x, y); stem(d, v); stem(d2, v2); swapc(v, sv, x, y);
        out[s] = eqarr(v2, sv);
    }
}
/* seat-level diagnostics for the step after position p of deck d (runs d and sigma d share
   the walk up to that step). out: {blockedA, blockedB, tA_before, rowA(prev seat), seat equal} */
void step_diag(int n, const int *ds, int x, int y, int *out) {
    for (int s = 0; s < n; s++) {
        const int *d = ds + N * s; int d2[N];
        swapc(d, d2, x, y);
        int seatA[N], tA[N], blA[N], seatB[N], tB[N], blB[N];
        walk_rec(d, seatA, tA, blA); walk_rec(d2, seatB, tB, blB);
        int px = 0; for (int i = 0; i < N; i++) if (d[i] == x) px = i;
        int *o = out + 6 * s;
        o[0] = px;
        if (px == N - 1) { o[1] = o[2] = o[3] = o[4] = -1; o[5] = 1; continue; }
        o[1] = blA[px + 1]; o[2] = blB[px + 1];
        o[3] = tA[px];                 /* overflow row counter before the step */
        o[4] = seatA[px] / 13;         /* row of x's seat */
        o[5] = seatA[px + 1] == seatB[px + 1] && tA[px + 1] == tB[px + 1];
    }
}
