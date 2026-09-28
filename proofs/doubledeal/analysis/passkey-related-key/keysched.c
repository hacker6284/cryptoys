/* PassKey related-key measurements on the real v11 key schedule (K_r = F(K_{r-1}), K_0 = master key).
   usage:
     keysched pass  N seed            every one of the 1326 swaps: P[F(tau K) = tau F(K)], K uniform
     keysched sched N seed a,b ...    for each listed swap: K uniform, K' = tau K; how often K'_r = tau K_r
                                      pass by pass (r = 1..6), all six at once, and whether a broken relation
                                      ever comes back at a later pass
   Seeds are per swap (seed_for(seed, a, b)), so every line is reproducible on its own. */
#include <stdio.h>
#include <stdlib.h>
#include <omp.h>
#include "dd.h"
static const char *nm(int c) { static char b[64][3]; static int i; char *s = b[i++ & 63]; s[0] = "A23456789TJQK"[c % 13]; s[1] = "CHSD"[c / 13]; s[2] = 0; return s; }
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: keysched pass|sched N seed [a,b ...]\n"); return 1; }
    long N = atol(argv[2]); uint64_t seed = strtoull(argv[3], 0, 10);
    if (argv[1][0] == 'p') {
        static double p[52][52];
        #pragma omp parallel for schedule(dynamic)
        for (int ab = 0; ab < 52 * 52; ab++) { int a = ab / 52, b = ab % 52; if (a >= b) continue;
            uint64_t s = seed_for(seed, a, b); long hit = 0; int k[52], kt[52], f[52], ft[52], tf[52];
            for (long n = 0; n < N; n++) { shuffle_(k, &s); relabel(k, a, b, kt); passkey(k, f); passkey(kt, ft); relabel(f, a, b, tf); hit += same(ft, tf); }
            p[a][b] = (double)hit / N; }
        int over = 0; double worst = 0; int wa = 0, wb = 0, ov2 = 0;
        for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) { over += p[a][b] > 1.0 / 64; if (p[a][b] > worst) { worst = p[a][b]; wa = a; wb = b; }
            if (p[a][b] > 1.0 / 64 && (SUIT(a) + RANK(a) != SUIT(b) + RANK(b))) ov2++; }
        printf("keysched pass N=%ld seed=%llu: swaps with P[F(tK)=tF(K)] > 1/64: %d (of which suit+rank differs: %d); worst %s<->%s %.5f\n",
               N, (unsigned long long)seed, over, ov2, nm(wa), nm(wb), worst);
        double mx = 0; int ma = 0, mb = 0;
        for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) if (SUIT(a) + RANK(a) != SUIT(b) + RANK(b) && p[a][b] > mx) { mx = p[a][b]; ma = a; mb = b; }
        printf("  worst swap with suit+rank different: %s<->%s %.5f\n", nm(ma), nm(mb), mx);
        printf("  suit+rank-equal swaps (measured):");
        for (int a = 0; a < 52; a++) for (int b = a + 1; b < 52; b++) if (SUIT(a) + RANK(a) == SUIT(b) + RANK(b)) printf(" %s%s=%.4f", nm(a), nm(b), p[a][b]);
        printf("\n");
        return 0; }
    printf("keysched sched N=%ld seed=%llu (K uniform, K' = tau K, K_r = F^r(K))\n", N, (unsigned long long)seed);
    printf("%-8s %-9s %-9s %-9s %-9s %-9s %-9s %-10s %-10s %-9s %-8s\n", "swap", "r=1", "r=2|r=1", "r=3|..2", "r=4|..3", "r=5|..4", "r=6|..5", "all 1..6", "p1^6", "comeback", "95%CI+-");
    for (int ai = 4; ai < argc; ai++) { int a, b; if (sscanf(argv[ai], "%d,%d", &a, &b) != 2) return 1;
        long cond[7] = {0}, hold[7] = {0}, all6 = 0, back = 0;
        #pragma omp parallel
        { uint64_t s = seed_for(seed, a * 64 + b, omp_get_thread_num()); long c_[7] = {0}, h_[7] = {0}, a6 = 0, bk = 0; int nt = omp_get_num_threads();
          long lo = N * omp_get_thread_num() / nt, hi = N * (omp_get_thread_num() + 1) / nt;
          for (long n = lo; n < hi; n++) { int K[7][52], Kp[7][52], t[52]; shuffle_(K[0], &s); relabel(K[0], a, b, Kp[0]);
              int ok = 1, broke = 0;
              for (int r = 1; r <= 6; r++) { passkey(K[r-1], K[r]); passkey(Kp[r-1], Kp[r]); relabel(K[r], a, b, t); int h = same(Kp[r], t);
                  if (ok) { c_[r]++; h_[r] += h; } if (!h) { ok = 0; broke = 1; } else if (broke) bk++; }
              a6 += ok; }
          #pragma omp critical
          { for (int r = 0; r < 7; r++) { cond[r] += c_[r]; hold[r] += h_[r]; } all6 += a6; back += bk; } }
        double p1 = (double)hold[1] / cond[1], pa = (double)all6 / N, p16 = p1 * p1 * p1 * p1 * p1 * p1;
        printf("%s<->%s ", nm(a), nm(b));
        for (int r = 1; r <= 6; r++) printf("%-9.5f ", (double)hold[r] / cond[r]);
        printf("%-10.5f %-10.5f %-9ld %.5f\n", pa, p16, back, 1.96 * __builtin_sqrt(pa * (1 - pa) / N));
    }
    return 0; }
