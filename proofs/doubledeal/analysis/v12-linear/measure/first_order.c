/* M8b MEASUREMENT (sampled; EMPIRICAL ONLY, not a proof; no theorem uses it).
   First-order (single-card) position tables P_U(card c at output seat t | c at input seat s)
   for U = the v12 stem, U = one unkeyed round (GridCycle after the stem), and a control
   (a fresh uniform deck, independent of the input: pure sampling noise).
   Printed per U: max |P(t|s) - 1/52| over (c, s, t); q_c - 1/52 with
   q_c = mean_s sum_t P(t|s)^2 (unbiased estimate from pair counts), its mean, max and min
   over c; and (52/51^2)(max q_c - 1/52), the normalised single-card squared correlation of
   one keyed layer that q_c would give (L1 with f = cardMask; not proved here).
   Usage: first_order N seed */
#include <math.h>
#include "../../v12-differential/ddiff.h"
static unsigned cnt[3][52][52][52]; /* [U][c][s][t] */
int main(int argc,char**argv){ long N=atol(argv[1]); uint64_t st=seed_for(atol(argv[2]),8,1);
  int x[52],a[52],b[52],y[52],inv[52];
  for(long n=0;n<N;n++){ shuffle_(x,&st); stem(x,a); mix_v11(a,b); shuffle_(y,&st);
    int *outs[3]={a,b,y};
    for(int u=0;u<3;u++){ for(int t=0;t<52;t++) inv[outs[u][t]]=t;
      for(int s=0;s<52;s++) cnt[u][x[s]][s][inv[x[s]]]++; } }
  const char*nm[3]={"stem","unkeyed","control"};
  for(int u=0;u<3;u++){ double maxdev=0, mean_q=0, maxq=-1, minq=1; int argc_=-1;
    for(int c=0;c<52;c++){ double qc=0;
      for(int s=0;s<52;s++){ double n_=0; for(int t=0;t<52;t++) n_+=cnt[u][c][s][t];
        double ss=0; for(int t=0;t<52;t++){ double k=cnt[u][c][s][t]; ss+=k*(k-1); double d=fabs(k/n_-1.0/52); if(d>maxdev) maxdev=d; }
        qc+= ss/(n_*(n_-1)) - 1.0/52; }
      qc/=52; mean_q+=qc/52; if(qc>maxq){maxq=qc;argc_=c;} if(qc<minq)minq=qc; }
    printf("%s: N=%ld  max|P(t|s)-1/52|=%.2e  (q_cc-1/52): mean %.2e max %.2e (card %d) min %.2e ; ELP=(52/51^2)(q-1/52): max %.2e\n",
      nm[u],N,maxdev,mean_q,maxq,argc_,minq,maxq*52.0/(51*51)); }
  return 0; }
