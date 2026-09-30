/* Round-trip check of the inverse unkeyed round (inv_stem, inv_mix_v11) on 200000 decks. */
#include "ddiff.h"
int main(void) { uint64_t st = 12345; int x[52], y[52], z[52], w[52];
  for (int t = 0; t < 200000; t++) { shuffle_(x, &st);
    stem(x, y); inv_stem(y, z); if (!same(x, z)) { puts("inv_stem FAIL"); return 1; }
    mix_v11(x, y); inv_mix_v11(y, z); if (!same(x, z)) { puts("inv_mix FAIL"); return 1; }
    unkeyed(x, y); inv_unkeyed(y, w); if (!same(x, w)) { puts("inv_unkeyed FAIL"); return 1; } }
  puts("OK inverse round on 200000 decks"); return 0; }
