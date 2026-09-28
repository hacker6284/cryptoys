import sys, random
sys.path.insert(0,str(__import__('pathlib').Path(__file__).resolve().parents[1]))
import ddport as P
E=lambda m,k: P.encrypt(m,k,9)
v9sym = P.v9sym
SYMS=[((a,b),v9sym(a,b)) for a in range(13) for b in range(4) if (a,b)!=(0,0)]
assert all(sorted(s)==list(range(52)) for _,s in SYMS)
def rel(s,m): return [s[x] for x in m]
def commutes_on(m,k,s): return E(rel(s,m),k)==rel(s,E(m,k))
def firstDeck(c): return [c]+[x for x in range(52) if x!=c]
idK=list(range(52))
if __name__ == '__main__':
    # (a) identity key: single message for all 51?
    for name,m0 in [('identity deck',list(range(52))),('firstDeck 51 (K♦,A♣,2♣,…)',firstDeck(51))]:
        bad=[ab for ab,s in SYMS if commutes_on(m0,idK,s)]
        print(f'(a) identity key, message {name}: breaks {51-len(bad)}/51 v9Sym', bad[:5])
    rng=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 0)
    NK=int(sys.argv[2]) if len(sys.argv)>2 else 200
    # (c) random real master keys, one random message each, all 51 v9Sym
    hold=0; tot=0; agree=0
    for _ in range(NK):
        k=list(range(52)); rng.shuffle(k); m=list(range(52)); rng.shuffle(m); c=E(m,k)
        for ab,s in SYMS:
            a=E(rel(s,m),k); b=rel(s,c); tot+=1
            hold+= a==b; agree+=sum(x==y for x,y in zip(a,b))
    print(f'(c) v9Sym: {NK} random keys x 51 sigma x 1 random msg: commuting instances {hold}/{tot}; mean agreeing positions {agree/tot:.3f}/52 (random: 1)')
    # random sigma in Perm52: transpositions and uniform
    hold=0; tot=0
    for _ in range(NK):
        k=list(range(52)); rng.shuffle(k); m=list(range(52)); rng.shuffle(m); c=E(m,k)
        for kind in range(10):
            if kind<5:
                i,j=rng.sample(range(52),2); s=list(range(52)); s[i],s[j]=j,i
            else:
                s=list(range(52)); rng.shuffle(s)
            tot+=1; hold+= E(rel(s,m),k)==rel(s,c)
    print(f'(b/c) random sigma (5 transpositions + 5 uniform per key), {NK} keys: commuting instances {hold}/{tot}')
