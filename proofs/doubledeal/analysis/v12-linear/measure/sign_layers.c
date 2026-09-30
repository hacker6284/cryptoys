/* M8b MEASUREMENT (sampled; EMPIRICAL ONLY, not a proof; no theorem uses it).
   Sign-character correlation per layer, E_x[sgn(x) sgn(U x)] for uniform decks x, with
   U = the v12 stem, U = GridCycle alone (input: the stem's output), U = one unkeyed round,
   and a control (a fresh uniform deck y instead of U x). With one keyed layer the keys only
   flip this sign (LinearMasks.corr_keyedLayer_sign, proved), so |E| is the key-free
   one-layer value. Usage: sign_layers N seed */
#include "../../v12-differential/ddiff.h"
#include <math.h>
static int sgn(const int *p){ int seen[52]={0}, s=1; for(int i=0;i<52;i++) if(!seen[i]){ int j=i,l=0; while(!seen[j]){seen[j]=1;j=p[j];l++;} if(!(l&1)) s=-s; } return s; }
int main(int argc,char**argv){ long N=atol(argv[1]); uint64_t st=seed_for(atol(argv[2]),9,3);
  int x[52],a[52],b[52],y[52]; long S[4]={0};
  for(long n=0;n<N;n++){ shuffle_(x,&st); stem(x,a); mix_v11(a,b); shuffle_(y,&st);
    int sx=sgn(x), sa=sgn(a), sb=sgn(b), sy=sgn(y);
    S[0]+=sx*sa; S[1]+=sa*sb; S[2]+=sx*sb; S[3]+=sx*sy; }
  const char*nm[4]={"stem","GridCycle","unkeyed round","control"};
  for(int u=0;u<4;u++) printf("%-14s E[sgn(in)sgn(out)] = %+.5f  (+-%.5f 1sd)\n",nm[u],(double)S[u]/N,1/sqrt((double)N));
  return 0; }
