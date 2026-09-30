/* Dump for candcheck.py: for each deck on stdin, the output of variants.c walkv with the chosen V
   (row-major scoop of the walk) and of gc.h gc_mix, separated by '|'. round.c walks with walkv, so
   this pins walkv(V=0) to the v10 model that xcheck.py checks against ddport.
   usage: walkvdump V < decks */
#include <stdio.h>
#include <stdlib.h>
#include "gc.h"
#define main variants_main
#include "variants.c"
#undef main
int main(int argc, char **argv) {
    V = argc > 1 ? atoi(argv[1]) : 0;
    int d[52], s[52], o[52], g[52];
    while (1) {
        for (int i = 0; i < 52; i++) if (scanf("%d", &d[i]) != 1) return 0;
        walkv(d, s, 0); for (int i = 0; i < 52; i++) o[s[i]] = d[i];
        gc_mix(d, g);
        for (int i = 0; i < 52; i++) printf("%d ", o[i]);
        printf("| ");
        for (int i = 0; i < 52; i++) printf("%d ", g[i]);
        printf("\n");
    }
}
