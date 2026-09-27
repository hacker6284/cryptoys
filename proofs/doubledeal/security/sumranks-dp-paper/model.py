"""Pure-Python SumRanks v10 model in the same conventions as
../../analysis/v10-sumranks/sbox-search/sbox.c
(grid cell = 13*row+col, card = 13*suit+rank0, suits 0C 1H 2S 3D, GF(4) labels C0 H=w(2) S=w^2(3) D=1)."""
import random
LABEL=[0,2,3,1]
def mulw(x): return [0,2,3,1][x]
def lab(c): return LABEL[c//13]
def rk(c): return c%13
def U(row): return sum((13-j)*rk(row[j]) for j in range(13))%13
def V(col): return lab(col[1])^mulw(lab(col[2]))^mulw(mulw(lab(col[3])))
def S(col): return lab(col[0])^lab(col[1])^lab(col[2])^lab(col[3])
def sr_trace(g):
    g=list(g); amts=[]
    for i in (1,2,3,0):
        p=(i+3)%4; t=U(g[13*p:13*p+13]); amts.append(t)
        r=g[13*i:13*i+13]; g[13*i:13*i+13]=r[t:]+r[:t]
    for j in list(range(1,13))+[0]:
        pc=[g[13*i+(j-1)%13] for i in range(4)]; cc=[g[13*i+j] for i in range(4)]
        s=V(pc)^S(cc); amts.append(s)
        for i in range(4): g[13*i+j]=cc[(i-s)%4]
    return g,amts
