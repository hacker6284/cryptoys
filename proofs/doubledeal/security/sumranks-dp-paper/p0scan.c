// For every 13-multiset of Z13 (counts n[0..12], sum 13), canonical under v->m*v+t,
// compute #arrangements (labelled: multiply by prod n_v!) with S=sum_j j*v_j = c (mod 13).
// Report: max over nonconstant multisets with D=0 of P[S=0]; check D!=0 gives exactly 1/13 for all c;
// also max P[S=c] for c!=0 when D=0; and table of max p0 by z (max multiplicity).
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
typedef long double LD;
int n[13];
static long long dp[1<<14][13]; // index by mixed radix
int rad[13], stride[13], tot;
int main(){
  int total=0; double best=0; int bestn[13]; double bestz[14]; memset(bestz,0,sizeof bestz);
  double maxnz=0; int bad13=0; long cls=0; long bad2b=0, checks2b=0; long bad2c=0;
  // enumerate compositions
  int c[13]; 
  // recursive enumeration via stack
  int idx=0; for(int i=0;i<13;i++)c[i]=0;
  // simple nested generation using stars and bars iteration
  int bars[12]; for(int i=0;i<12;i++)bars[i]=i; // positions among 25 slots
  while(1){
    // counts from bars
    int prev=-1; for(int i=0;i<12;i++){c[i]=bars[i]-prev-1; prev=bars[i];} c[12]=24-prev;
    // canonical check: counts vector under all affine maps; keep if lexicographically max
    int canon=1;
    for(int m=1;m<13&&canon;m++)for(int t=0;t<13&&canon;t++){
      if(m==1&&t==0)continue;
      int d[13]; for(int v=0;v<13;v++) d[(m*v+t)%13]=c[v];
      for(int v=0;v<13;v++){ if(d[v]>c[v]){canon=0;break;} if(d[v]<c[v])break; }
    }
    if(canon){
      cls++;
      int D=0,z=0; for(int v=0;v<13;v++){D+=v*c[v]; if(c[v]>z)z=c[v];} D%=13;
      if(z<13){
        tot=1; for(int v=0;v<13;v++){rad[v]=c[v]+1; stride[v]=tot; tot*=rad[v];}
        // dp over states = used counts; pos = number used
        memset(dp,0,sizeof(long long)*13*tot);
        dp[0][0]=1;
        for(int s=0;s<tot;s++){
          int used[13],pos=0,r=s; for(int v=0;v<13;v++){used[v]=r%rad[v]; r/=rad[v]; pos+=used[v];}
          for(int v=0;v<13;v++) if(used[v]<c[v]){
            int s2=s+stride[v]; int sh=(pos*v)%13;
            for(int x=0;x<13;x++) if(dp[s][x]) dp[s2][(x+sh)%13]+=dp[s][x];
          }
        }
        long long *res=dp[tot-1]; long long sum=0; for(int x=0;x<13;x++)sum+=res[x];
        { long long mx=0; for(int x=0;x<13;x++) if(res[x]>mx) mx=res[x];
          for(int v=0;v<13;v++) if(c[v]>0){ checks2b++; if(mx*(long long)(c[v]+1) > sum) bad2b++; } }
        { int nz=0,a=-1,b=-1,zz=-1; for(int v=0;v<13;v++){ if(c[v]==11) zz=v; }
          if(zz>=0){ for(int v=0;v<13;v++) if(v!=zz && c[v]) { if(a<0)a=v; else b=v; if(c[v]!=1) a=-2; }
            if(a>=0 && b>=0 && ((a-zz+13)%13 + (b-zz+13)%13)%13==0 && res[0]!=0) bad2c++; } }
        if(D!=0){ for(int x=0;x<13;x++) if(res[x]*13!=sum) bad13++; }
        else {
          double p0=(double)res[0]/sum; if(p0>best){best=p0; memcpy(bestn,c,sizeof c);} if(p0>bestz[z])bestz[z]=p0;
          for(int x=1;x<13;x++){double q=(double)res[x]/sum; if(q>maxnz)maxnz=q;}
        }
      }
    }
    // next combination of 12 bars in 25 slots
    int i=11; while(i>=0 && bars[i]==25-12+i) i--; if(i<0)break; bars[i]++; for(int j=i+1;j<12;j++)bars[j]=bars[j-1]+1;
  }
  printf("classes=%ld  D!=0 non-uniform count=%d\n",cls,bad13);
  printf("Lemma 2(b) exhaustive: %ld (class, value) checks of max_c P[S=c] <= 1/(z_v+1), violations=%ld\n",checks2b,bad2b);
  printf("Lemma 2(c) exhaustive: cancelling-pair classes with P[S=0]>0: %ld\n",bad2c);
  printf("max p0 (D=0, nonconstant) = %.6f = 1/%.3f  at counts:",best,1/best); for(int v=0;v<13;v++)printf(" %d",bestn[v]); printf("\n");
  printf("max P[S=c], c!=0, D=0 = %.6f = 1/%.3f\n",maxnz,1/maxnz);
  for(int z=1;z<13;z++) if(bestz[z]>0) printf("z=%2d  max p0=%.6f = 1/%.3f   one-card bound 1/(z+1)=%.4f\n",z,bestz[z],1/bestz[z],1.0/(z+1));
}
