/* Related-key tests of the full v11 cipher (6 PassKey passes, whitening + 5 full rounds + final round).
   usage: rk N seed a,b ...     (tau = swap of cards a and b; K, P uniform; K' = tau K)
   Per sample, with sigma = swap of SEATS a and b (Compose turns a key swap into this seat swap):
     V1 same plaintext      C = E_K(P),        C1 = E_K'(P)      tests C1 = C, C1 = C o sigma
     V2 label-related       C2 = E_K'(tau P)                     tests C2 = tau C  (card relabelling)
     V3 aligned (oracle)    P' = P with the cards at positions pos_K(a), pos_K(b) swapped, so the two
                            whitened states are EQUAL; C3 = E_K'(P').  Needs K, so it is the most favourable
                            case for the attacker (a real attacker would have to guess 1 of 1326 position pairs).
                            tests C3 = C, C3 = C o sigma; per-round internal state distance.
   "eq seats" = number of seats where the two decks hold the same card (1 on average for unrelated decks).
   Stats are given over all samples and over the samples where all six round keys kept K'_r = tau K_r. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <omp.h>
#include "dd.h"
static const char *nm(int c) { static char b[64][3]; static int i; char *s = b[i++ & 63]; s[0] = "A23456789TJQK"[c % 13]; s[1] = "CHSD"[c / 13]; s[2] = 0; return s; }
enum { V1EQ, V1SIG, V2EQ, V3EQ, V3SIG, NEV };
typedef struct { long n, ev[NEV]; double eq1, eq1s, eq2, eq2s, eq3, eq3s; long st_eq[7], st_h2[7]; double st_ham[7]; } Acc;
static void add(Acc *A, const Acc *B) { A->n += B->n; for (int i = 0; i < NEV; i++) A->ev[i] += B->ev[i];
    A->eq1 += B->eq1; A->eq1s += B->eq1s; A->eq2 += B->eq2; A->eq2s += B->eq2s; A->eq3 += B->eq3; A->eq3s += B->eq3s;
    for (int r = 0; r < 7; r++) { A->st_eq[r] += B->st_eq[r]; A->st_h2[r] += B->st_h2[r]; A->st_ham[r] += B->st_ham[r]; } }
static void report(const char *tag, const Acc *A) {
    double n = A->n; if (!n) return;
    #define CI(s, ss) (1.96 * sqrt(((ss) / n - ((s) / n) * ((s) / n)) / n))
    printf("  [%s] n=%ld\n", tag, A->n);
    printf("    V1 E_K'(P) = E_K(P): %ld   = E_K(P) o sigma: %ld   eq seats %.4f +- %.4f\n", A->ev[V1EQ], A->ev[V1SIG], A->eq1 / n, CI(A->eq1, A->eq1s));
    printf("    V2 E_K'(tau P) = tau E_K(P): %ld   eq seats vs tau E_K(P) %.4f +- %.4f\n", A->ev[V2EQ], A->eq2 / n, CI(A->eq2, A->eq2s));
    printf("    V3 aligned: E_K'(P') = E_K(P): %ld   = E_K(P) o sigma: %ld   eq seats %.4f +- %.4f\n", A->ev[V3EQ], A->ev[V3SIG], A->eq3 / n, CI(A->eq3, A->eq3s));
    printf("    V3 internal state after round r (0 = whitening, 6 = ciphertext): #equal / #differ in exactly 2 seats / mean seats differing (unrelated decks: 0 / ~0 / 51)\n     ");
    for (int r = 0; r < 7; r++) printf(" r%d %ld/%ld/%.3f", r, A->st_eq[r], A->st_h2[r], A->st_ham[r] / n);
    printf("\n"); }
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: rk N seed a,b ...\n"); return 1; }
    long N = atol(argv[1]); uint64_t seed = strtoull(argv[2], 0, 10);
    printf("rk N=%ld seed=%llu (full v11, K and P uniform, K' = tau K); 0 hits in n samples => 95%% upper bound 3/n\n", N, (unsigned long long)seed);
    for (int ai = 3; ai < argc; ai++) { int a, b; if (sscanf(argv[ai], "%d,%d", &a, &b) != 2) return 1;
        Acc all = {0}, kept = {0};
        #pragma omp parallel
        { Acc A = {0}, Kp = {0}; uint64_t s = seed_for(seed, a * 64 + b, omp_get_thread_num()); int nt = omp_get_num_threads();
          long lo = N * omp_get_thread_num() / nt, hi = N * (omp_get_thread_num() + 1) / nt;
          for (long n = lo; n < hi; n++) {
              int K[52], Kt[52], keys[7][52], keyt[7][52], P[52], Pt[52], P3[52], C[52], C1[52], C2[52], C3[52], tC[52], Cs[52], t[52];
              int st[7][52], st3[7][52];
              shuffle_(K, &s); shuffle_(P, &s); relabel(K, a, b, Kt); expand_keys(K, keys); expand_keys(Kt, keyt);
              int ok = 1; for (int r = 1; r <= 6; r++) { relabel(keys[r], a, b, t); ok &= same(keyt[r], t); }
              encrypt_keys(P, keys, C, st); encrypt_keys(P, keyt, C1, 0);
              relabel(P, a, b, Pt); encrypt_keys(Pt, keyt, C2, 0); relabel(C, a, b, tC);
              int pa = -1, pb = -1; for (int i = 0; i < 52; i++) { if (K[i] == a) pa = i; if (K[i] == b) pb = i; }
              memcpy(P3, P, sizeof P3); P3[pa] = P[pb]; P3[pb] = P[pa]; encrypt_keys(P3, keyt, C3, st3);
              memcpy(Cs, C, sizeof Cs); Cs[a] = C[b]; Cs[b] = C[a];
              Acc *T[2] = {&A, ok ? &Kp : 0};
              for (int w = 0; w < 2; w++) { Acc *X = T[w]; if (!X) continue; X->n++;
                  X->ev[V1EQ] += same(C1, C); X->ev[V1SIG] += same(C1, Cs); X->ev[V2EQ] += same(C2, tC);
                  X->ev[V3EQ] += same(C3, C); X->ev[V3SIG] += same(C3, Cs);
                  double e1 = 52 - hamming(C1, C), e2 = 52 - hamming(C2, tC), e3 = 52 - hamming(C3, C);
                  X->eq1 += e1; X->eq1s += e1 * e1; X->eq2 += e2; X->eq2s += e2 * e2; X->eq3 += e3; X->eq3s += e3 * e3;
                  for (int r = 0; r < 7; r++) { int h = hamming(st[r], st3[r]); X->st_eq[r] += h == 0; X->st_h2[r] += h == 2; X->st_ham[r] += h; } } }
          #pragma omp critical
          { add(&all, &A); add(&kept, &Kp); } }
        printf("swap %s<->%s (suit+rank %d vs %d)\n", nm(a), nm(b), SUIT(a) + RANK(a), SUIT(b) + RANK(b));
        report("all samples", &all); report("all six round keys kept K'_r = tau K_r", &kept); fflush(stdout); }
    return 0; }
