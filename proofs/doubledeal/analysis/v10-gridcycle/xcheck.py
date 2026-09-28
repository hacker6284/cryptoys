"""Cross-check gc.h (C) against the repo's Python port (ddport, v10 GridCycle == v9) and the
sudocode test vector. Run: python3 xcheck.py"""
import sys, random, subprocess, os
here = os.path.dirname(os.path.abspath(__file__))
# in the repo this folder is proofs/doubledeal/analysis/v10-gridcycle/
sys.path.insert(0, os.environ.get('DDPORT_DIR', os.path.join(here, '../../security/checks')))
import ddport
src = r'''#include <stdio.h>
#include "gc.h"
int main(){int d[52],o[52];while(1){for(int i=0;i<52;i++) if(scanf("%d",&d[i])!=1) return 0;
gc_mix(d,o);for(int i=0;i<52;i++) printf("%d ",o[i]);printf("\n");fflush(stdout);}}'''
open('/tmp/gcx.c','w').write(src)
subprocess.check_call(['cc','-O2','-I',here,'/tmp/gcx.c','-o','/tmp/gcx'])
rng = random.Random(1); decks = []
for _ in range(2000):
    d = list(range(52)); rng.shuffle(d); decks.append(d)
inp = '\n'.join(' '.join(map(str, d)) for d in decks) + '\n'
out = subprocess.run(['/tmp/gcx'], input=inp, capture_output=True, text=True).stdout.split('\n')
bad = sum(1 for d, line in zip(decks, out) if list(map(int, line.split())) != ddport.mix_columns(d, 10))
print('C vs ddport mix_columns on 2000 random decks: mismatches =', bad)
assert bad == 0
