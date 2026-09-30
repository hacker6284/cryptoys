#pragma once
/* v10 unkeyed stem: lay_cm, SumRanks v10, ShiftRows, scoop_cm (analysis only; nothing here is the spec).
   Shared by cand.c (and p5.c, which includes cand.c) and round.c. Checked against ddport.stem by candcheck.py. */
#include <string.h>
static const int LABEL[4] = {0, 2, 3, 1}, TW[4] = {0, 2, 3, 1};
static void stem(const int *m, int *out) {
    int g[4][13];
    for (int k = 0; k < 52; k++) g[k % 4][k / 4] = m[k];
    for (int a = 1; a <= 4; a++) { int i = a % 4, p = (i + 3) % 4, tot = 0, tmp[13];
        for (int j = 0; j < 13; j++) tot += (13 - j) * (g[p][j] % 13 + 1);
        int k = tot % 13; for (int j = 0; j < 13; j++) tmp[j] = g[i][(j + k) % 13]; memcpy(g[i], tmp, sizeof tmp); }
    for (int a = 1; a <= 13; a++) { int j = a % 13, p = (j + 12) % 13;
        int v = LABEL[g[1][p] / 13] ^ TW[LABEL[g[2][p] / 13]] ^ TW[TW[LABEL[g[3][p] / 13]]];
        int su = LABEL[g[0][j] / 13] ^ LABEL[g[1][j] / 13] ^ LABEL[g[2][j] / 13] ^ LABEL[g[3][j] / 13];
        int sh = v ^ su, col[4]; for (int i = 0; i < 4; i++) col[i] = g[i][j];
        for (int i = 0; i < 4; i++) g[i][j] = col[((i - sh) % 4 + 4) % 4]; }
    for (int i = 0; i < 4; i++) { int tmp[13]; for (int j = 0; j < 13; j++) tmp[j] = g[i][(j + i) % 13]; memcpy(g[i], tmp, sizeof tmp); }
    for (int c = 0, k = 0; c < 13; c++) for (int r = 0; r < 4; r++) out[k++] = g[r][c];
}
