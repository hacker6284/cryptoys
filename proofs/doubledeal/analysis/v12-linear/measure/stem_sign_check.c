/* M8b CHECK of the model used by stem_sign_dp.py (sampled; EMPIRICAL ONLY, not a proof).
   (1) On N uniform decks: the turn-recording copy stem_t of the stem gives the same output as
   dd12.h's stem, and sgn(x) sgn(stem x) = (-1)^(sum of the 13 column turns), the identity the
   DP relies on. (2) The sampled joint distribution of (turn of column 1, turn of column 2),
   to compare with the exact values of stem_turn_dp_check.py. Seed fixed (7,7,7).
   Usage: stem_sign_check N */
#include "../../v12-differential/ddiff.h"
/* stem with turn recording (copy of dd.h stem) */
static void stem_t(const int *m, int *o, int *turns){ int g[4][13]; lay_cm(m, g);
    for (int a = 1; a <= 4; a++) { int i = a % 4; rotl(g[i], 13, sr_row_turn(g[(i + 3) % 4])); }
    for (int a = 1; a <= 13; a++) { int j = a % 13; int t=sr_col_turn(g, j); turns[j]=t;
        rot_col_down(g, j, t); }
    for (int i = 0; i < 4; i++) rotl(g[i], 13, i); scoop_cm(g, o); }
int main(int argc,char**argv){ long N=atol(argv[1]); uint64_t st=seed_for(7,7,7);
  int x[52],a[52],b[52],tr[13]; long bad=0, hist[16]={0};
  for(long n=0;n<N;n++){ shuffle_(x,&st); stem_t(x,a,tr); stem(x,b); if(!same(a,b)) bad++;
    int par=0; for(int j=0;j<13;j++) par^=tr[j]&1; if(sgn(x)*sgn(a) != (par?-1:1)) bad++;
    hist[tr[1]*4+tr[2]]++; }
  printf("identity failures: %ld of %ld\n",bad,N);
  for(int k=0;k<16;k++) printf("P(turn1=%d,turn2=%d) = %.5f\n",k/4,k%4,(double)hist[k]/N);
  return 0; }
