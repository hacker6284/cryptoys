"""Recorded outputs of the attack scripts in this directory (write-or-check).

Every script here is seeded and deterministic.  This runner executes each one with the
arguments below, and writes its stdout to logs/<name>.log (default) or, with --check,
fails if a committed log differs from a fresh run (tools/gencheck.py convention).
The numbers in REPORT.md are taken from these logs.

    python3 logs.py                  # regenerate all logs (about 2.5 min)
    python3 logs.py --check          # CI: fail on any stale log or non-zero exit
    python3 logs.py --only NAME ...  # a subset

suit_blind_collision.py has its own --log / --check (quick) and --log --full /
--check --full (report-size runs) modes; see that script.
"""
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / 'tools'))
from gencheck import parser, emit  # noqa: E402

RUNS = {
    'md': ['md.py'],                                  # 8 KATs, IV digest, |G|
    'exp_corner_driven': ['exp_corner_driven.py'],    # F1
    'pseudo_collision': ['pseudo_collision.py'],      # F2
    'exp_related_blocks': ['exp_related_blocks.py'],
    'exp_local_collisions': ['exp_local_collisions.py'],
    'exp_corner_local': ['exp_corner_local.py'],
    'exp_square_classes': ['exp_square_classes.py'],
    'exp_square_fraction': ['exp_square_fraction.py'],
    'exp_edge_tree': ['exp_edge_tree.py'],
    'exp_edge_first_merge': ['exp_edge_first_merge.py'],
    'toy_attacks_coll': ['toy_attacks.py', 'coll'],
    'toy_attacks_pre': ['toy_attacks.py', 'pre'],     # about 1 min
}


def main():
    cli = parser(__doc__)
    cli.add_argument('--only', nargs='+', choices=sorted(RUNS), help='run only these')
    args = cli.parse_args()
    rc = 0
    for name in args.only or RUNS:
        argv = RUNS[name]
        p = subprocess.run([sys.executable, *argv], cwd=HERE, capture_output=True, text=True)
        if p.returncode != 0:
            print(f"FAIL {name}: exit {p.returncode}\n{p.stderr}", file=sys.stderr)
            rc = 1
            continue
        text = f"$ python3 {' '.join(argv)}\n{p.stdout}"
        rc |= emit(HERE / 'logs' / f'{name}.log', text, args.check,
                   fix=f'python3 proofs/megadreifach/security/logs.py --only {name}')
    return rc


if __name__ == '__main__':
    sys.exit(main())
