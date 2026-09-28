"""Cross-check the analysis C model of v10 GridCycle (proofs/doubledeal/analysis/v10-gridcycle/gc.h,
gc_mix) against the repo Python port ddport.mix_columns(d, 10) on 2000 seeded random decks. It compares
only against ddport (which CI checks against the frozen v10 vectors). Run: python3 xcheck.py"""
import sys, random, subprocess, os, tempfile, shutil
here = os.path.dirname(os.path.abspath(__file__))
# in the repo this folder is proofs/deprecated/doubledeal-v10/attack/measure/
repo = os.path.normpath(os.path.join(here, '../../../../..'))
gc_dir = os.path.join(repo, 'proofs/doubledeal/analysis/v10-gridcycle')
sys.path.insert(0, os.environ.get('DDPORT_DIR', os.path.join(repo, 'proofs/doubledeal/security/checks')))
import ddport
src = r'''#include <stdio.h>
#include "gc.h"
int main(){int d[52],o[52];while(1){for(int i=0;i<52;i++) if(scanf("%d",&d[i])!=1) return 0;
gc_mix(d,o);for(int i=0;i<52;i++) printf("%d ",o[i]);printf("\n");fflush(stdout);}}'''
tmp = tempfile.mkdtemp(prefix='gcx')
csrc, exe = os.path.join(tmp, 'gcx.c'), os.path.join(tmp, 'gcx')
open(csrc, 'w').write(src)
subprocess.check_call(['cc', '-O2', '-I', gc_dir, csrc, '-o', exe])
rng = random.Random(1); decks = []
for _ in range(2000):
    d = list(range(52)); rng.shuffle(d); decks.append(d)
inp = '\n'.join(' '.join(map(str, d)) for d in decks) + '\n'
out = subprocess.run([exe], input=inp, capture_output=True, text=True).stdout.split('\n')
shutil.rmtree(tmp)
bad = sum(1 for d, line in zip(decks, out) if list(map(int, line.split())) != ddport.mix_columns(d, 10))
print('C (analysis gc.h) vs ddport mix_columns(d, 10) on 2000 random decks: mismatches =', bad)
assert bad == 0
