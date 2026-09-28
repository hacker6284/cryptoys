/* Swap survival through GridCycle alone.
   value mode: for every card pair {a,b} (1326), P_d[ GC(tau d) == tau GC(d) ], tau = (a b) on card values.
   pos mode:   for every position pair {i,j}, P_d[ GC(d o (i j)) differs from GC(d) in exactly 2 seats ].
   Both events are equivalent to "the seat walk is unchanged" (T2 characterisation; checked here too).
   usage: survival value|pos N seed */
#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
static long hits[52][52];
int main(int argc, char **argv) {
    (void)argc;
    int mode_pos = argv[1][0] == 'p'; long N = atol(argv[2]); rs ^= strtoull(argv[3],0,10)*0x9E3779B97F4A7C15ULL;
    int d[52], e[52], s0[52], s1[52], where[52], o0[52], o1[52];
    long checked = 0, mism = 0;
    for (long n = 0; n < N; n++) {
        shuffle(d); gc_walk(d, s0, 52);
        for (int i = 0; i < 52; i++) where[d[i]] = i;
        for (int a = 0; a < 52; a++) for (int b = a+1; b < 52; b++) {
            int i = mode_pos ? a : where[a], j = mode_pos ? b : where[b];
            if (i > j) { int x = i; i = j; j = x; }
            memcpy(e, d, sizeof d); e[i] = d[j]; e[j] = d[i];
            /* walk identical up to index i; only recompute from i on */
            gc_walk(e, s1, 52);
            int same = memcmp(s0, s1, sizeof s0) == 0;
            if (same) hits[a][b]++;
            if ((n & 1023) == 0) { /* spot-check equivalence walk-unchanged <=> weight 2 */
                gc_mix(d, o0); gc_mix(e, o1); int w = 0; for (int k = 0; k < 52; k++) w += o0[k] != o1[k];
                checked++; if ((w == 2) != same) mism++;
            }
        }
    }
    fprintf(stderr, "equivalence spot checks %ld, mismatches %ld\n", checked, mism);
    for (int a = 0; a < 52; a++) for (int b = a+1; b < 52; b++) printf("%d %d %ld %ld\n", a, b, hits[a][b], N);
    return 0;
}
