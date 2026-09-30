// Case B (rank-constant tau): exact survival  F(n) = E[ prod_c phi(M_c, S(M_{c+1})) ]  over a uniform
// partition of 52 cards (eps-multiset counts n[0..3]) into 13 ordered columns of 4.
// phi(Z,S=0)=1, phi(Z,S!=0)=0; phi(P,S!=0)=1/3, phi(P,S=0)=0; phi(F,S=0)=1/2, phi(F,S!=0)=1/6; phi(U,*)=1/4.
// F depends only on the sorted count vector (type and S!=0 are invariant under any bijection of the 4 values).
// Usage: ./caseB_tm            -> scan all partitions of 52 into <=4 parts (nonconstant), print max and table
//        ./caseB_tm a b c d    -> print F for that count vector
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
enum {Z=0,P=1,Fu=2,U=3};
static int ms[35][4], mtype[35], nms=0;
static double phi(int t,int snz){ switch(t){case Z: return snz?0:1; case P: return snz?1.0/3:0; case Fu: return snz?1.0/6:0.5; default: return 0.25;} }
static double lchoose(int n,int k){ if(k<0||k>n) return -INFINITY; return lgamma(n+1.0)-lgamma(k+1.0)-lgamma(n-k+1.0); }
static double ch(int n,int k){ if(k<0||k>n) return 0; double r=1; for(int i=0;i<k;i++) r=r*(n-i)/(i+1); return r; }
static void init(void){
  for(int a=0;a<=4;a++)for(int b=0;a+b<=4;b++)for(int c=0;a+b+c<=4;c++){int d=4-a-b-c; int *m=ms[nms]; m[0]=a;m[1]=b;m[2]=c;m[3]=d;
    int nz=0,mx=0; for(int v=0;v<4;v++){if(m[v])nz++; if(m[v]>mx)mx=m[v];}
    int s=0; for(int v=0;v<4;v++) if(m[v]&1) s^=v;
    int t; if(nz==1)t=Z; else if(nz==2&&mx==2)t=P; else if(nz==4)t=Fu; else t=U;
    if((t==U)!=(s!=0)){fprintf(stderr,"type/S mismatch\n");exit(1);}
    mtype[nms++]=t; }
}
// DP state: remaining counts r1,r2,r3 (r0 implied), prev type (4), first S!=0 flag (2)
double F(const int n[4]){
  int N1=n[1]+1,N2=n[2]+1,N3=n[3]+1; long sz=(long)N1*N2*N3*8;
  double *cur=calloc(sz,sizeof(double)),*nxt=calloc(sz,sizeof(double));
  #define IDX(r1,r2,r3,t,f) ((((long)(r1)*N2+(r2))*N3+(r3))*8+(t)*2+(f))
  // first column
  for(int k=0;k<nms;k++){int *m=ms[k]; if(m[0]>n[0]||m[1]>n[1]||m[2]>n[2]||m[3]>n[3])continue;
    double w=ch(n[0],m[0])*ch(n[1],m[1])*ch(n[2],m[2])*ch(n[3],m[3])/ch(52,4);
    cur[IDX(n[1]-m[1],n[2]-m[2],n[3]-m[3],mtype[k],mtype[k]==U)]+=w; }
  for(int layer=1;layer<13;layer++){
    memset(nxt,0,sz*sizeof(double)); int rem=52-4*layer; // cards remaining before drawing this column
    for(int r1=0;r1<N1;r1++)for(int r2=0;r2<N2;r2++)for(int r3=0;r3<N3;r3++){
      int r0=rem-r1-r2-r3; if(r0<0||r0>n[0])continue;
      for(int t=0;t<4;t++)for(int f=0;f<2;f++){ double v=cur[IDX(r1,r2,r3,t,f)]; if(v==0)continue;
        for(int k=0;k<nms;k++){int *m=ms[k]; if(m[0]>r0||m[1]>r1||m[2]>r2||m[3]>r3)continue;
          double w=ch(r0,m[0])*ch(r1,m[1])*ch(r2,m[2])*ch(r3,m[3])/ch(rem,4);
          double p=phi(t,mtype[k]==U); if(p==0)continue;
          nxt[IDX(r1-m[1],r2-m[2],r3-m[3],mtype[k],f)]+=v*w*p; } } }
    double *tmp=cur;cur=nxt;nxt=tmp; }
  double tot=0; for(int t=0;t<4;t++)for(int f=0;f<2;f++) tot+=cur[IDX(0,0,0,t,f)]*phi(t,f);
  free(cur);free(nxt); return tot;
}
int main(int argc,char**argv){
  init();
  if(argc==5){int n[4]; for(int i=0;i<4;i++)n[i]=atoi(argv[i+1]); double f=F(n); printf("F(%d,%d,%d,%d) = %.12g = 1/%.4f\n",n[0],n[1],n[2],n[3],f,1/f); return 0;}
  // all partitions n0>=n1>=n2>=n3, sum 52, not constant (n1>0)
  int cnt=0; double best=0; int bn[4]={0}; static double bym[53]; static int bymn[53][4];
  int list[3000][4]; int L=0;
  for(int a=52;a>=13;a--)for(int b=a<52-a?a:52-a;b>=0;b--)for(int c=b<52-a-b?b:52-a-b;c>=0;c--){int d=52-a-b-c; if(d>c||d<0)continue; if(b==0)continue; list[L][0]=a;list[L][1]=b;list[L][2]=c;list[L][3]=d;L++;}
  double *res=malloc(sizeof(double)*L);
  #pragma omp parallel for schedule(dynamic)
  for(int i=0;i<L;i++) res[i]=F(list[i]);
  for(int i=0;i<L;i++){ int m=52-list[i][0]; if(res[i]>bym[m]){bym[m]=res[i]; memcpy(bymn[m],list[i],sizeof(int)*4);} if(res[i]>best){best=res[i];memcpy(bn,list[i],sizeof bn);} }
  printf("partitions scanned: %d\nmax F = %.10g = 1/%.3f at (%d,%d,%d,%d)\n",L,best,1/best,bn[0],bn[1],bn[2],bn[3]);
  // realisable count vectors: XOR of all 52 eps values is 0 <=> the values with odd count XOR to 0.
  // Counts sum to 52, so the number of odd counts is even; 0 or 4 odd counts can always be placed ({0,1,w,w^2} XORs to 0),
  // 2 odd counts never can (a xor b != 0 for a != b). So realisable <=> number of odd counts != 2.
  { double rb=0; int rn[4]={0}; int nreal=0;
    for(int i=0;i<L;i++){ int odd=0; for(int v=0;v<4;v++) odd+=list[i][v]&1; if(odd==2) continue; nreal++;
      if(res[i]>rb){rb=res[i]; memcpy(rn,list[i],sizeof rn);} }
    printf("restricted to realisable vectors (sum eps = 0, i.e. #odd counts != 2): %d vectors, max F = %.10g = 1/%.3f at (%d,%d,%d,%d)\n",nreal,rb,1/rb,rn[0],rn[1],rn[2],rn[3]); }
  printf("max by m' = 52 - n0:\n");
  for(int m=1;m<=39;m++) if(bym[m]>0) printf("  m'=%2d  max F=%.6g = 1/%.1f  at (%d,%d,%d,%d)\n",m,bym[m],1/bym[m],bymn[m][0],bymn[m][1],bymn[m][2],bymn[m][3]);
  return 0;
}
