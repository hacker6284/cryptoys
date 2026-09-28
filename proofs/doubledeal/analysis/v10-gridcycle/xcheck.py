"""Cross-check gc.h gc_mix (C) against the repo's Python port ddport.mix_columns (v10 GridCycle ==
v9) on 2000 seeded random decks. ddport itself is checked against the sudocode vectors in CI; this
script compares only against ddport. Run: python3 xcheck.py"""
import sys, random, subprocess, os, tempfile
here = os.path.dirname(os.path.abspath(__file__))
# in the repo this folder is proofs/doubledeal/analysis/v10-gridcycle/
sys.path.insert(0, os.environ.get('DDPORT_DIR', os.path.join(here, '../../security/checks')))
import ddport
src = r'''#include <stdio.h>
#include "gc.h"
int main(){int d[52],o[52];while(1){for(int i=0;i<52;i++) if(scanf("%d",&d[i])!=1) return 0;
gc_mix(d,o);for(int i=0;i<52;i++) printf("%d ",o[i]);printf("\n");fflush(stdout);}}'''
tmp = tempfile.mkdtemp(prefix='gcx')
csrc, exe = os.path.join(tmp, 'gcx.c'), os.path.join(tmp, 'gcx')
open(csrc, 'w').write(src)
subprocess.check_call([os.environ.get('CC', 'cc'), '-O2', '-I', here, csrc, '-o', exe])
rng = random.Random(1); decks = []
for _ in range(2000):
    d = list(range(52)); rng.shuffle(d); decks.append(d)
inp = '\n'.join(' '.join(map(str, d)) for d in decks) + '\n'
out = subprocess.run([exe], input=inp, capture_output=True, text=True).stdout.split('\n')
bad = sum(1 for d, line in zip(decks, out) if list(map(int, line.split())) != ddport.mix_columns(d, 10))
print('C vs ddport mix_columns on 2000 random decks: mismatches =', bad)
assert bad == 0, f"gc.h gc_mix disagrees with ddport v10 on {bad} decks"
import shutil; shutil.rmtree(tmp)
