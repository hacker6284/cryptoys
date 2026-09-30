/* M8b CHECK of the model used by stem_sign_dp.py, deck by deck (sampled; EMPIRICAL ONLY, not
   a proof). For N uniform decks (seed (7,7,8)), runs the v12 stem of dd12.h and prints one
   line per deck: the 52 suits of the grid after the row step (row-major, g[r][c]), then the
   13 column turns sr_col_turn actually applied (indexed by column 0..12). The Python model is
   compared with these turns by stem_turn_model_check.py. Usage: stem_turn_dump N > file */
#include "../../v12-differential/ddiff.h"
int main(int argc, char **argv) { long N = atol(argv[1]); uint64_t st = seed_for(7, 7, 8);
  int x[52], g[4][13], tr[13];
  for (long n = 0; n < N; n++) { shuffle_(x, &st); lay_cm(x, g);
    for (int a = 1; a <= 4; a++) { int i = a % 4; rotl(g[i], 13, sr_row_turn(g[(i + 3) % 4])); }
    for (int r = 0; r < 4; r++) for (int c = 0; c < 13; c++) printf("%d ", SUIT(g[r][c]));
    for (int a = 1; a <= 13; a++) { int j = a % 13; tr[j] = sr_col_turn(g, j); rot_col_down(g, j, tr[j]); }
    for (int j = 0; j < 13; j++) printf(j < 12 ? "%d " : "%d\n", tr[j]); }
  return 0; }
