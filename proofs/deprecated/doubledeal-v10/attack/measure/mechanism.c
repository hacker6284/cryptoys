/* Mechanism check for the worst GridCycle pair K♣<->K♦ (cards 12 and 51).
   K♣ steps by (0, 13 = 0 mod 13): its target is its own seat, so it always overflows, and the
   overflow seat depends only on (marker t, blocked column = K♣'s column, occupancy).
   K♦ steps by (3, 0): target is the seat one row up in the same column. If that seat is
   occupied, K♦ overflows from the same column with the same t, i.e. exactly where K♣ would go.
   Claim (sufficient condition): the walk is unchanged under (K♣ K♦) if at each of the two walk positions holding K♣/K♦ that is
   not index 51, the seat one row up from the current seat (same column) is occupied at that moment.
   (The remaining survivals: K♣'s overflow lands exactly on K♦'s free target and the marker
   desync happens not to matter later.)
   usage: mechanism N seed */
#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
int main(int argc, char **argv) {
    long N = atol(argv[1]); rs ^= strtoull(argv[2],0,10)*0x9E3779B97F4A7C15ULL;
    int d[52], e[52], s0[52], s1[52]; long surv = 0, pred = 0, agree = 0, predNotSurv = 0;
    for (long n = 0; n < N; n++) {
        shuffle(d); gc_walk(d, s0, 52);
        for (int i = 0; i < 52; i++) e[i] = d[i] == 12 ? 51 : d[i] == 51 ? 12 : d[i];
        gc_walk(e, s1, 52); int sv = !memcmp(s0, s1, sizeof s0);
        /* predicate from d's walk: occupancy before placing card i+1 = seats s0[0..i] */
        int ok = 1;
        for (int i = 0; i < 51; i++) if (d[i] == 12 || d[i] == 51) {
            int r = s0[i] / 13, c = s0[i] % 13, up = ((r + 3) & 3) * 13 + c, occ = 0;
            for (int k = 0; k <= i; k++) occ |= s0[k] == up;
            if (!occ) ok = 0;
        }
        surv += sv; pred += ok; agree += sv == ok; predNotSurv += ok && !sv;
    }
    printf("K♣<->K♦: survival %ld/%ld = %.4f; predicate true %ld (%.4f); predicate but not survival %ld; survival without predicate %ld\n", surv, N, (double)surv / N, pred, (double)pred / N, predNotSurv, surv - (pred - predNotSurv));
}
