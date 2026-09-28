"""Cross-check cand.c: variant 0 GridCycle and the v10 stem (lay_cm, SumRanks, ShiftRows, scoop_cm)
against the repo Python port ddport (checked in CI against the v10 vectors). Run: python3 candcheck.py"""
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
assert bs == 0 and bg == 0
