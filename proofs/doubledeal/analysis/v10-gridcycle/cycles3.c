/* Screen all 3-cycles (a b c) of card values through GridCycle alone:
   survival = P_d[GC(tau d) == tau GC(d)] <=> seat walk unchanged (T2-style, relabelling moves only values).
   usage: cycles3 N seed [refineTop N2]  prints top cycles */
#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
typedef struct { int a, b, c; long h; } Cy;
static int cmp(const void *x, const void *y) { long a = ((Cy*)x)->h, b = ((Cy*)y)->h; return (b > a) - (b < a); }
static long run(int a, int b, int c, long N) {
    int d[52], e[52], s0[52], s1[52]; long h = 0;
    for (long n = 0; n < N; n++) { shuffle(d); gc_walk(d, s0, 52);
        for (int i = 0; i < 52; i++) e[i] = d[i] == a ? b : d[i] == b ? c : d[i] == c ? a : d[i];
        gc_walk(e, s1, 52); h += !memcmp(s0, s1, sizeof s0); }
    return h;
}
int main(int argc, char **argv) {
    long N = atol(argv[1]); rs ^= strtoull(argv[2],0,10)*0x9E3779B97F4A7C15ULL; long N2 = argc > 3 ? atol(argv[3]) : 0;
    static Cy cy[44200]; int n = 0;
    for (int a = 0; a < 52; a++) for (int b = a+1; b < 52; b++) for (int c = a+1; c < 52; c++) if (c != b)
        { cy[n].a = a; cy[n].b = b; cy[n].c = c; cy[n].h = run(a, b, c, N); n++; }
    qsort(cy, n, sizeof(Cy), cmp);
    const char *R = "A23456789TJQK", *S = "CHSD";
    long tot = 0; for (int i = 0; i < n; i++) tot += cy[i].h;
    printf("%d 3-cycles, screen N=%ld: mean survival %.4f\n", n, N, (double)tot / n / N);
    for (int i = 0; i < 10; i++) {
        long h2 = N2 ? run(cy[i].a, cy[i].b, cy[i].c, N2) : 0;
        printf("(%c%c %c%c %c%c) screen %.4f", R[cy[i].a%13], S[cy[i].a/13], R[cy[i].b%13], S[cy[i].b/13], R[cy[i].c%13], S[cy[i].c/13], (double)cy[i].h / N);
        if (N2) printf("  refined %ld/%ld = %.4f", h2, N2, (double)h2 / N2);
        printf("\n");
    }
}
