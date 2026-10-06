"""ENUMERATION ONLY (no theorem uses it; NOTES.md section 5). Premises of a
5-swap coupling (not formalised; StemSupportFour does not need it): the largest number of disjoint
different-rank pairs among 12 or 13 cards with each rank at most 4 times, what an arbitrary greedy
choice (as in StemCoupling.exists_good) can be left with, and L(5) over all nonzero residues
(no WLOG)."""
import itertools
from collections import Counter
# max number of disjoint different-rank pairs in a multiset with multiplicities m (greedy from the two largest classes is optimal)
def maxpairs(m):
    m=sorted([x for x in m if x>0],reverse=True); n=0
    while len(m)>=2:
        m[0]-=1; m[1]-=1; n+=1
        m=sorted([x for x in m if x>0],reverse=True)
    return n
def parts(n, maxp, maxlen):
    if n==0: yield []; return
    if maxlen==0: return
    for p in range(min(n,maxp),0,-1):
        for r in parts(n-p,p,maxlen-1): yield [p]+r
worst=min((maxpairs(p),p) for p in parts(12,4,13))
print("12 cards, ranks<=4: min over rank-multiplicity patterns of max disjoint diff-rank pairs:",worst)
worst13=min((maxpairs(p),p) for p in parts(13,4,13))
print("13 cards: ",worst13)
# greedy as in exists_good (any pair of different ranks, repeated): can it get stuck below 5?
def greedy_worst(m, k):
    # adversarial greedy: returns min number of pairs a greedy that picks ANY different-rank pair may reach
    m=tuple(sorted([x for x in m if x>0],reverse=True))
    best=None
    if len(m)<2: return 0
    res=10**9
    for i in range(len(m)):
        for j in range(i+1,len(m)):
            mm=list(m); mm[i]-=1; mm[j]-=1
            res=min(res,1+greedy_worst(mm,k))
    return res
print("adversarial greedy, 12 cards:",min((greedy_worst(p,5),p) for p in parts(12,4,13)))
cnt=[0]
best=0
for D in itertools.product(range(1,13),repeat=5):
    c=[0]*13
    for e in itertools.product((0,1),repeat=5):
        c[sum(a*b for a,b in zip(e,D))%13]+=1
    best=max(best,max(c))
print("L(5) without WLOG over all 12^5 nonzero tuples:",best,"/ 32")
