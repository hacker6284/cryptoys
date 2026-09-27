import sys, pathlib; sys.path.insert(0, str(pathlib.Path(__file__).parent)); from emp import *
keys={'identity':list(range(52)),'reverse':list(range(51,-1,-1))}
for r in range(1,52): keys[f'rot{r}']=list(range(r,52))+list(range(r))
keys['rank-major']=[13*s+r for r in range(13) for s in range(4)]
for ab,s in SYMS[:8]: keys[f'v9Sym{ab}-deck']=s
msgs=[list(range(52)),firstDeck(51)]+[firstDeck(c) for c in (0,12,25,38)]
hold=0;tot=0
for kn,k in keys.items():
    for m in msgs:
        for ab,s in SYMS:
            tot+=1; hold+=commutes_on(m,k,s)
print(f'structured keys ({len(keys)}) x structured msgs ({len(msgs)}) x 51 v9Sym: commuting {hold}/{tot}')
