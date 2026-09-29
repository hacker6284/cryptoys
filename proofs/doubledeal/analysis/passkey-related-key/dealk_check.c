/* checks dd.h passkey_dealb (used by rk.c with env DEALK) against readings.c DEALB. usage: ./dealk_check */
#define main readings_main
#include "readings.c"
#undef main
int refine_main(int argc, char **argv);
int main(int argc, char **argv) { if (argc > 1) return refine_main(argc, argv); uint64_t s = 5; long bad = 0; for (int md = 0; md <= 1; md++) for (int k = 0; k <= 4; k++) { KDEAL = k; DMOD = md; DD_DEALMOD = md;
    for (int n = 0; n < 20000; n++) { int a[52], b[52], c[52]; shuffle_(a, &s); fwd(4, a, b); passkey_dealb(a, c, k); bad += !same(b, c); } }
  printf("passkey_dealb vs readings DEALB, k=0..4, min and mod, 200000 decks: %ld mismatches\n", bad); return 0; }
/* `dealk_check N k mod a,b ...` (mod: 0 = min, 1 = mod, 2 = key-pile fallback reading 6): one-pass pass-through of the listed swaps at N decks (refines readings.c top pairs) */
int refine_main(int argc, char **argv) { long N = atol(argv[1]); KDEAL = atoi(argv[2]); DMOD = atoi(argv[3]); int V = DMOD == 2 ? 6 : 4; if (V == 6) DMOD = 0;
    printf("k=%d %s, N=%ld per swap:", KDEAL, V == 6 ? "key-pile fallback" : DMOD ? "mod" : "min", N);
    for (int ai = 4; ai < argc; ai++) { int a, b; sscanf(argv[ai], "%d,%d", &a, &b); long hit = 0;
        #pragma omp parallel reduction(+:hit)
        { uint64_t s = seed_for(77, a * 64 + b, omp_get_thread_num()); int nt = omp_get_num_threads();
          for (long n = N * omp_get_thread_num() / nt; n < N * (omp_get_thread_num() + 1) / nt; n++) {
              int k[52], kt[52], f[52], ft[52], tf[52]; shuffle_(k, &s); relabel(k, a, b, kt); fwd(V, k, f); fwd(V, kt, ft); relabel(f, a, b, tf); hit += same(ft, tf); } }
        printf("  %s<->%s %.5f (1/%.0f)", nm(a), nm(b), (double)hit / N, hit ? (double)N / hit : 0.0); }
    printf("\n"); return 0; }
