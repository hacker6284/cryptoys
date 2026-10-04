/* EMPIRICAL / ENUMERATION ONLY (no theorem uses it; see NOTES.md, section 5).
   Exact per-row maximum F1 (enumeration, integer counts; not a proof in Lean).
   A row's free content: 12 cards; only their ranks mod 13 matter (a residue multiset M,
   each residue at most 4 times).  After translating weights (shifts the target only),
   the 12 free positions carry the weights 1..12 (mod 13).  For each M, count the distinct
   arrangements a : {1..12} -> M by S = sum_w w * a(w) mod 13; f(M, tau) = cnt[tau] / total.
   Prints max over M, tau of f, the arg max, and a histogram of max_tau f over M. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
static int k, res[13], mult[13], radix[13];
int main(void){
  long nms=0; double best=0; int bestM[13]; uint64_t bestc=0,bestt=0; int besttau=0;
  long hist[64]={0};
  int idx[13]; memset(idx,0,sizeof idx);
  /* enumerate multiplicity vectors m[0..12] in {0..4}, sum 12 */
  for(;;){
    int s=0; for(int i=0;i<13;i++) s+=idx[i];
    if(s==12){
      nms++;
      k=0; for(int i=0;i<13;i++) if(idx[i]){res[k]=i;mult[k]=idx[i];k++;}
      int nst=1; for(int i=0;i<k;i++){radix[i]=nst; nst*=mult[i]+1;}
      /* state = remaining multiplicities in mixed radix; start full */
      uint64_t *cur=calloc((size_t)nst*13,8), *nxt=calloc((size_t)nst*13,8);
      int full=0; for(int i=0;i<k;i++) full+=mult[i]*radix[i];
      cur[full*13+0]=1;
      for(int w=1;w<=12;w++){
        memset(nxt,0,(size_t)nst*13*8);
        for(int st=0;st<nst;st++) for(int sm=0;sm<13;sm++){ uint64_t v=cur[st*13+sm]; if(!v) continue;
          for(int i=0;i<k;i++){ int rem=(st/radix[i])%(mult[i]+1); if(!rem) continue;
            nxt[(st-radix[i])*13+(sm+w*res[i])%13]+=v; } }
        uint64_t *t=cur; cur=nxt; nxt=t;
      }
      uint64_t tot=0,mx=0; int mt=0; for(int sm=0;sm<13;sm++){tot+=cur[sm]; if(cur[sm]>mx){mx=cur[sm];mt=sm;}}
      double f=(double)mx/tot; int b=(int)(f*200); if(b>63)b=63; hist[b]++;
      if(f>best){best=f;memcpy(bestM,idx,sizeof idx);bestc=mx;bestt=tot;besttau=mt;}
      free(cur); free(nxt);
    }
    int i=0; while(i<13 && idx[i]==4){idx[i]=0;i++;} if(i==13) break; idx[i]++;
  }
  printf("multisets %ld\nF1 = %llu / %llu = %.6f (tau %d)\nargmax multiplicities by residue 0..12:",
    nms,(unsigned long long)bestc,(unsigned long long)bestt,best,besttau);
  for(int i=0;i<13;i++) printf(" %d",bestM[i]);
  printf("\nhistogram of max_tau f (bins of 0.005):\n");
  for(int b=0;b<64;b++) if(hist[b]) printf("  [%.3f,%.3f): %ld\n",b/200.0,(b+1)/200.0,hist[b]);
  return 0;
}
