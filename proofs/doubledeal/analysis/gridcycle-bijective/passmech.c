/* PassMix mechanism check (analysis only).
   For a pass layer, output = the input positions placed by an action sequence A (one (hand cut, key cut) pair per
   controller step), so a swap tau survives iff the induced position permutation is unchanged. This program tests
   the stronger statement  survive  <=>  A(tau d) == A(d)  (equal actions at every step) on random decks, and prints
   the closed-form collision probability e(e-1)/(52*51), e = #{steps k : act_k(a) == act_k(b)}, which is exact for
   the right-hand event because the controller sequence of a uniform deck is a uniform ordering (the map
   deck -> controller order is a bijection).
   usage: passmech V N seed      V: 6 = PASSM (hand rank, key suit), 10 = PASSF2 (fallback swaps the piles), 13 = PASSF3 (edge rule)
   Checks all 1326 pairs at N decks each; reports exceptions (survive with A' != A, or A' == A without survival).
   All counts are deterministic (per-pair seeded streams); WHICH exception witnesses are printed (first 3 found)
   depends on thread timing. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "layers.h"
static int V;
/* action at step k (hand size n = 51-k after the pop, key size m = k) for card c, as (hand cut mod n, key cut mod m) */
static void act(int c, int k, int *h, int *g) { int n = 51 - k, m = k, r = RANK(c), s = SUIT(c);
    if (V == 6) { *h = n ? r % n : 0; *g = m ? s % m : 0; return; }
    if (V == 13) { int hh, gg; pf3_act(c, n, m, &hh, &gg); *h = n ? hh % n : 0; *g = m ? gg % m : 0; return; }
    if (r < n) { *h = r % n; *g = m ? s % m : 0; } else { *g = m ? r % m : 0; *h = n ? s % n : 0; } }
static void run(const int *d, int *out, int *A) { int hand[52], key[52], hn = 52, kn = 0; memcpy(hand, d, sizeof hand);
    for (int k = 0; k < 52; k++) { int C = hand[0], h, g; memmove(hand, hand + 1, (hn - 1) * sizeof(int)); hn--;
        act(C, k, &h, &g); rotl(hand, hn, h); rotl(key, kn, g); A[2*k] = h; A[2*k+1] = g;
        memmove(key + 1, key, kn * sizeof(int)); key[0] = C; kn++; }
    memcpy(out, key, sizeof key); }
static uint64_t mk(uint64_t seed, uint64_t k) { uint64_t s = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ (k + 1) * 0xD1B54A32D192ED03ULL; for (int i = 0; i < 8; i++) rnd_(&s); return s ? s : 1; }
static int nwit = 0;
int main(int argc, char **argv) { (void)argc; V = atoi(argv[1]); long N = atol(argv[2]); uint64_t seed = strtoull(argv[3], 0, 10);
    /* self-check against layers.h */
    { uint64_t s = 99; int d[52], o1[52], o2[52], A[104]; for (int n = 0; n < 2000; n++) { shuffle_(d, &s); run(d, o1, A); (V == 6 ? L_passm : V == 13 ? L_passf3 : L_passf2)(d, o2);
        if (memcmp(o1, o2, sizeof o1)) { printf("model mismatch\n"); return 1; } } }
    long exc1 = 0, exc2 = 0, surv = 0, tot = 0; double worstF = 0, worstM = 0; int wa = 0, wb = 0, ma = 0, mb = 0; double maxdev = 0;
    #pragma omp parallel for schedule(dynamic) reduction(+:exc1,exc2,surv,tot)
    for (int q = 0; q < 1326; q++) { int a = 0, b, qq = q; while (qq >= 51 - a) { qq -= 51 - a; a++; } b = a + 1 + qq;
        int e = 0; for (int k = 0; k < 52; k++) { int h1, g1, h2, g2; act(a, k, &h1, &g1); act(b, k, &h2, &g2); e += h1 == h2 && g1 == g2; }
        double F = e * (e - 1) / 2652.0; uint64_t s = mk(seed, q); long hs = 0;
        for (long n = 0; n < N; n++) { int d[52], x[52], o0[52], o1[52], A0[104], A1[104]; shuffle_(d, &s);
            for (int i = 0; i < 52; i++) x[i] = d[i] == a ? b : d[i] == b ? a : d[i];
            run(d, o0, A0); run(x, o1, A1); int ok = 1;
            for (int i = 0; i < 52 && ok; i++) { int t = o0[i] == a ? b : o0[i] == b ? a : o0[i]; ok = t == o1[i]; }
            int same = !memcmp(A0, A1, sizeof A0); hs += ok; exc1 += ok && !same; exc2 += same && !ok; tot++;
            if (ok && !same) {
                #pragma omp critical
                { if (nwit < 3) { nwit++; int k0 = 0, k1 = 51; while (A0[2*k0] == A1[2*k0] && A0[2*k0+1] == A1[2*k0+1]) k0++;
                    while (A0[2*k1] == A1[2*k1] && A0[2*k1+1] == A1[2*k1+1]) k1--;
                    int nd = 0; for (int k = 0; k < 52; k++) nd += A0[2*k] != A1[2*k] || A0[2*k+1] != A1[2*k+1];
                    printf("  witness (survive, actions differ): pair %d<->%d, first differing step %d, last %d, %d differing steps; deck", a, b, k0, k1, nd);
                    for (int i = 0; i < 52; i++) printf("%c%d", i ? ',' : ' ', d[i]);
                    printf("\n"); } } } }
        surv += hs; double M = (double)hs / N;
        #pragma omp critical
        { if (F > worstF) { worstF = F; wa = a; wb = b; } if (M > worstM) { worstM = M; ma = a; mb = b; }
          double dev = fabs(M - F) / sqrt(F * (1 - F) / N + 1e-12); if (F > 0 && dev > maxdev) maxdev = dev; } }
    const char *CN = "A23456789TJQK", *SN = "CHSD";
    printf("%s mechanism N=%ld/pair seed=%llu: %ld survivals in %ld pair-decks; survive-but-actions-differ %ld; actions-equal-but-no-survival %ld\n",
        V == 6 ? "PASSM" : V == 13 ? "PASSF3" : "PASSF2", N, (unsigned long long)seed, surv, tot, exc1, exc2);
    printf("  closed form e(e-1)/2652: worst pair %c%c<->%c%c = %.5f (1/%.0f); measured worst %c%c<->%c%c = %.5f; max |measured-formula|/sd over pairs %.2f\n",
        CN[wa%13], SN[wa/13], CN[wb%13], SN[wb/13], worstF, 1 / worstF, CN[ma%13], SN[ma/13], CN[mb%13], SN[mb/13], worstM, maxdev);
    return 0; }
