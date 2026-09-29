#pragma once
/* M6 measurements: relabelling differences through the v12 unkeyed round. EMPIRICAL ONLY; no theorem uses these. */
#include <stdio.h>
#include <stdlib.h>
#include "../v12-keysched/dd12.h"
/* inverse GridCycle: replay the walk reading the output grid */
static inline void inv_mix_v11(const int *o, int *d) { uint8_t occ[52] = {0}; int t = 0, fr = 2, fc = 0, prev = -1;
    for (int i = 0; i < 52; i++) { int r = 0, c = 0;
        if (i == 0) { r = 2; c = 0; }
        else { int tr = (fr + SUIT(prev)) & 3, tc = (fc + RANK(prev)) % 13;
            if (!occ[tr*13+tc]) { r = tr; c = tc; fr = tr; fc = tc; }
            else { int b = o[tr*13+tc], row = (t + SUIT(b)) & 3, st = (tc + RANK(b)) % 13, found = 0;
                for (int a = 0; a < 4 && !found; a++, row = (row + 1) & 3)
                    for (int k = 0; k < 13; k++) { int cc = (st + k) % 13; if (!occ[row*13+cc]) { r = row; c = cc; found = 1; break; } }
                t = (t + 1) & 3; fr = (tr + SUIT(b)) & 3; fc = st; } }
        occ[r*13+c] = 1; d[i] = o[r*13+c]; prev = d[i]; } }
static inline void inv_stem(const int *o, int *m) { int g[4][13]; lay_cm(o, g);
    for (int i = 0; i < 4; i++) rotl(g[i], 13, -i);
    for (int a = 13; a >= 1; a--) { int j = a % 13; rot_col_down(g, j, -sr_col_turn(g, j)); }
    for (int a = 4; a >= 1; a--) { int i = a % 4; rotl(g[i], 13, -sr_row_turn(g[(i + 3) % 4])); }
    scoop_cm(g, m); }
static inline void inv_unkeyed(const int *o, int *m) { int t[52]; inv_mix_v11(o, t); inv_stem(t, m); }
/* relabelling difference: b = beta . a  (beta[a[i]] = b[i]) */
static inline void diff(const int *a, const int *b, int *beta) { for (int i = 0; i < 52; i++) beta[a[i]] = b[i]; }
static inline int support(const int *beta) { int s = 0; for (int c = 0; c < 52; c++) s += beta[c] != c; return s; }
static inline uint64_t hsh(const int *beta) { uint64_t h = 1469598103934665603ull;
    for (int c = 0; c < 52; c++) { h ^= (uint64_t)beta[c] + 1; h *= 1099511628211ull; h ^= h >> 29; } return h; }
static const int LAB_[4] = {0, 2, 3, 1}, SOL_[4] = {0, 3, 1, 2};
/* spec: "a,b" swap; "a,b,c" 3-cycle a->b->c->a; "a,b;c,d" double swap; "v10:a,x" */
static inline void parse_rel(const char *sp, int *s) { for (int i = 0; i < 52; i++) s[i] = i;
    int a, b, c, d;
    if (!strncmp(sp, "v10:", 4)) { sscanf(sp + 4, "%d,%d", &a, &b);
        for (int k = 0; k < 52; k++) s[k] = 13 * SOL_[LAB_[k / 13] ^ b] + (k % 13 + a) % 13; }
    else if (sscanf(sp, "%d,%d;%d,%d", &a, &b, &c, &d) == 4) { s[a] = b; s[b] = a; s[c] = d; s[d] = c; }
    else if (sscanf(sp, "%d,%d,%d", &a, &b, &c) == 3) { s[a] = b; s[b] = c; s[c] = a; }
    else { sscanf(sp, "%d,%d", &a, &b); s[a] = b; s[b] = a; } }
static inline int cmpu(const void *x, const void *y) { uint64_t a = *(const uint64_t *)x, b = *(const uint64_t *)y; return a < b ? -1 : a > b; }
