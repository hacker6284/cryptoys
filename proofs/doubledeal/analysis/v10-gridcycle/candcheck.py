"""Cross-check the C models against the repo Python port ddport (checked in CI against the v10 vectors),
on 2000 seeded decks (random.Random(7)):
  1. cand.c: variant 0 GridCycle and the v10 stem (stem.h: lay_cm, SumRanks, ShiftRows, scoop_cm);
  2. variants.c walkv with V=0 (the walk round.c uses for README section 5) == gc.h gc_mix == ddport.mix_columns.
Run: python3 candcheck.py"""
import os, sys, random, subprocess
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.environ.get('DDPORT_DIR', os.path.join(here, '../../security/checks')))
import ddport
subprocess.check_call(['cc', '-O2', '-o', os.path.join(here, 'cand_check'), os.path.join(here, 'cand.c')])
rng = random.Random(7); decks = []
for _ in range(2000):
    d = list(range(52)); rng.shuffle(d); decks.append(d)
out = subprocess.run([os.path.join(here, 'cand_check'), '0', 'x', '0', '0'], input='\n'.join(' '.join(map(str, d)) for d in decks) + '\n',
                     capture_output=True, text=True).stdout.strip().split('\n')
bs = bg = 0
for d, line in zip(decks, out):
    a, b = line.split('|')
    bs += list(map(int, a.split())) != ddport.stem(d, 10)
    bg += list(map(int, b.split())) != ddport.mix_columns(d, 10)
print(f'cand.c vs ddport on 2000 decks: stem mismatches {bs}, GridCycle(v10) mismatches {bg}')
assert bs == 0 and bg == 0, f"cand.c vs ddport: stem mismatches {bs}, GridCycle(v10) mismatches {bg}"
subprocess.check_call(['cc', '-O2', '-o', os.path.join(here, 'walkv_check'), os.path.join(here, 'walkvdump.c')])
out = subprocess.run([os.path.join(here, 'walkv_check'), '0'], input='\n'.join(' '.join(map(str, d)) for d in decks) + '\n',
                     capture_output=True, text=True).stdout.strip().split('\n')
assert len(out) == len(decks), f"walkv_check printed {len(out)} lines for {len(decks)} decks"
bw = bm = 0
for d, line in zip(decks, out):
    a, b = line.split('|')
    ref = ddport.mix_columns(d, 10)
    bw += list(map(int, a.split())) != ref
    bm += list(map(int, b.split())) != ref
print(f'variants.c walkv(V=0) vs ddport on 2000 decks: mismatches {bw}; gc.h gc_mix vs ddport: mismatches {bm}')
assert bw == 0 and bm == 0, f"walkv(V=0) vs ddport: {bw} mismatches; gc_mix vs ddport: {bm}"
