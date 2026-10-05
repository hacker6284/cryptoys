/* mr_fleets.c -- Mathematician review, independent of kx-specs/ecbs code.
   Exhaustive enumeration of all labelled fleets (5,4,3a,3b,2) on a 10x10 grid, no overlap
   (touching allowed).  Computes, exactly:
   (1) NLAB = number of labelled fleets;
   (2) for every translation class (fleet with bounding box touching row 0 and column 0) the
       multiplicity M(T) = number of labelled fleets whose union is T (exact-cover recursion),
       the global max of M(T) over all 17-cell unions, and a pattern attaining it;
   (3) S1[h][w] = #normalised fleets with bbox h x w, S2[h][w] = sum of M(T) over them.
       => for a box of H x W, sum_{T fits} M(T)^2 = sum_{F fits} M(T(F)) = sum_{h,w} S2[h][w](H-h+1)(W-w+1)
          and N_fit = sum S1[h][w](H-h+1)(W-w+1).
   (4) Toy (n=23, one grid, cell p on residue (99-p) mod 23): for each r0, the exact value
          P_r0 = (1/NLAB) sum_F  prod_{r != r0} [m_r even] C(m_r,m_r/2)/2^m_r  *  [m_r0 odd] C(m_r0,(m_r0+1)/2)/2^m_r0
       = Pr[ residue sign-sum vector c equals e_r0 ]  (a rigorous LOWER bound on Pr[k = lambda^r0]).
   Build: gcc -O3 -march=native -fopenmp mr_fleets.c -o mr_fleets */
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>
typedef unsigned __int128 u128;
static const int LEN[5] = {5, 4, 3, 3, 2};
static u128 PM[6][200]; static int NPL[6];
static int PR0[6][200], PR1[6][200], PC0[6][200], PC1[6][200];
static uint32_t PPAR[6][200];            /* Toy residue parity mask */
static unsigned char PRES[6][200][5];     /* Toy residues of the cells */
static u128 HM[6][100], VM[6][100];       /* ship of length L starting at cell c, horizontal / vertical (0 = invalid) */
static u128 bit(int c) { return ((u128)1) << c; }
static void gen(int L) {
  int k = 0;
  for (int h = 0; h < 2; h++)
    for (int r = 0; r < (h ? 10 : 11 - L); r++)
      for (int c = 0; c < (h ? 11 - L : 10); c++) {
        u128 m = 0; uint32_t par = 0;
        for (int i = 0; i < L; i++) {
          int rr = h ? r : r + i, cc = h ? c + i : c, p = rr * 10 + cc;
          m |= bit(p); int res = (99 - p) % 23; par ^= 1u << res; PRES[L][k][i] = (unsigned char)res;
        }
        PM[L][k] = m; PPAR[L][k] = par;
        PR0[L][k] = r; PC0[L][k] = c; PR1[L][k] = h ? r : r + L - 1; PC1[L][k] = h ? c + L - 1 : c;
        k++;
      }
  NPL[L] = k;
  for (int c = 0; c < 100; c++) {
    int r = c / 10, cc = c % 10; HM[L][c] = 0; VM[L][c] = 0;
    if (cc + L <= 10) { u128 m = 0; for (int i = 0; i < L; i++) m |= bit(c + i); HM[L][c] = m; }
    if (r + L <= 10) { u128 m = 0; for (int i = 0; i < L; i++) m |= bit(c + 10 * i); VM[L][c] = m; }
  }
}
static int ctz128(u128 x) { uint64_t lo = (uint64_t)x; if (lo) return __builtin_ctzll(lo); return 64 + __builtin_ctzll((uint64_t)(x >> 64)); }
static long mult(u128 rem, int used) {           /* labelled tilings of rem by the unused ships */
  if (!rem) return used == 31 ? 1 : 0;
  int c = ctz128(rem); long tot = 0;
  for (int i = 0; i < 5; i++) {
    if (used >> i & 1) continue;
    int L = LEN[i];
    u128 m = HM[L][c]; if (m && (m & rem) == m) tot += mult(rem & ~m, used | 1 << i);
    m = VM[L][c]; if (L > 1 && m && (m & rem) == m) tot += mult(rem & ~m, used | 1 << i);
  }
  return tot;
}
static double PZ[8], PO[8];
int main(void) {
  for (int L = 2; L <= 5; L++) gen(L);
  /* C(m, m/2)/2^m for even m ; C(m,(m+1)/2)/2^m for odd m */
  double Cb[8][8]; for (int a = 0; a < 8; a++) for (int b = 0; b < 8; b++) Cb[a][b] = 0;
  for (int a = 0; a < 8; a++) { Cb[a][0] = 1; for (int b = 1; b <= a; b++) Cb[a][b] = Cb[a-1][b-1] + (b <= a-1 ? Cb[a-1][b] : 0); }
  for (int m = 0; m < 8; m++) { double p2 = 1; for (int i = 0; i < m; i++) p2 *= 2; PZ[m] = (m % 2 == 0) ? Cb[m][m/2] / p2 : 0; PO[m] = (m % 2) ? Cb[m][(m+1)/2] / p2 : 0; }
  unsigned long long NL = 0; long maxM = 0; u128 argT = 0;
  unsigned long long S1[11][11]; double S2[11][11]; unsigned long long Mhist[1024];
  memset(S1, 0, sizeof S1); memset(S2, 0, sizeof S2); memset(Mhist, 0, sizeof Mhist);
  double toy[23]; memset(toy, 0, sizeof toy);
  #pragma omp parallel
  {
    unsigned long long nl = 0, s1[11][11], mh[1024]; double s2[11][11], ty[23]; long mx = 0; u128 at = 0;
    memset(s1, 0, sizeof s1); memset(s2, 0, sizeof s2); memset(mh, 0, sizeof mh); memset(ty, 0, sizeof ty);
    #pragma omp for schedule(dynamic, 1)
    for (int a = 0; a < NPL[5]; a++) {
      u128 o1 = PM[5][a];
      for (int b = 0; b < NPL[4]; b++) { if (PM[4][b] & o1) continue; u128 o2 = o1 | PM[4][b];
       for (int c = 0; c < NPL[3]; c++) { if (PM[3][c] & o2) continue; u128 o3 = o2 | PM[3][c];
        for (int d = 0; d < NPL[3]; d++) { if (PM[3][d] & o3) continue; u128 o4 = o3 | PM[3][d];
         for (int e = 0; e < NPL[2]; e++) { if (PM[2][e] & o4) continue;
          nl++;
          int ids[5] = {a, b, c, d, e}, Ls[5] = {5, 4, 3, 3, 2};
          int r0 = 99, c0 = 99, r1 = -1, c1 = -1; uint32_t par = 0;
          for (int s = 0; s < 5; s++) { int L = Ls[s], k = ids[s];
            if (PR0[L][k] < r0) r0 = PR0[L][k]; if (PC0[L][k] < c0) c0 = PC0[L][k];
            if (PR1[L][k] > r1) r1 = PR1[L][k]; if (PC1[L][k] > c1) c1 = PC1[L][k]; par ^= PPAR[L][k]; }
          if (__builtin_popcount(par) == 1) {           /* Toy: exactly one residue with odd load */
            unsigned char ld[23]; memset(ld, 0, 23);
            for (int s = 0; s < 5; s++) { int L = Ls[s], k = ids[s]; for (int i = 0; i < L; i++) ld[PRES[L][k][i]]++; }
            int rr0 = __builtin_ctz(par); double pr = 1;
            for (int r = 0; r < 23; r++) pr *= (r == rr0) ? PO[ld[r]] : PZ[ld[r]];
            ty[rr0] += pr;
          }
          if (r0 == 0 && c0 == 0) {
            u128 T = o4 | PM[2][e]; long M = mult(T, 0);
            int h = r1 + 1, w = c1 + 1; s1[h][w]++; s2[h][w] += (double)M; mh[M < 1023 ? M : 1023]++;
            if (M > mx) { mx = M; at = T; }
          }
         }}}}
    }
    #pragma omp critical
    {
      NL += nl; for (int i = 0; i < 11; i++) for (int j = 0; j < 11; j++) { S1[i][j] += s1[i][j]; S2[i][j] += s2[i][j]; }
      for (int i = 0; i < 1024; i++) Mhist[i] += mh[i];
      for (int r = 0; r < 23; r++) toy[r] += ty[r];
      if (mx > maxM) { maxM = mx; argT = at; }
    }
  }
  printf("NLAB %llu\n", NL);
  printf("maxM %ld\n", maxM);
  printf("argT");
  for (int r = 0; r < 10; r++) { printf(" "); for (int c = 0; c < 10; c++) putchar((argT >> (10 * r + c)) & 1 ? '#' : '.'); }
  printf("\n");
  for (int i = 1; i <= 10; i++) for (int j = 1; j <= 10; j++) if (S1[i][j]) printf("S %d %d %llu %.1f\n", i, j, S1[i][j], S2[i][j]);
  for (int i = 0; i < 1024; i++) if (Mhist[i]) printf("MH %d %llu\n", i, Mhist[i]);
  for (int r = 0; r < 23; r++) printf("TOY %d %.17g\n", r, toy[r] / (double)NL);
  return 0;
}
