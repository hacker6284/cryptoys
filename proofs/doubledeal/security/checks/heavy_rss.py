#!/usr/bin/env python3
"""Build the heavy library DoubleDealSecurityHeavy ONE MODULE AT A TIME and log the
wall time and peak RSS of each step (CI job doubledeal-security-heavy).

Why one at a time: several heavy modules each need 4.5-5 GB of kernel memory; built by
one `lake build DoubleDealSecurityHeavy`, Lake may run them in parallel on a ~16 GB
runner. Sequential steps both bound the peak by the largest single module and measure it.

Each step is `lake build <module>` in proofs/doubledeal/security, in the import order
of DoubleDealSecurityHeavy.lean, after the default library is built (the CI job builds
`DoubleDealSecurity AuditAll` first). Peak RSS is ru_maxrss from os.wait4 on the `lake`
process: the largest resident set of lake or any Lean process it waited for in that
step (a step also builds any heavy dependency not built yet, so its figure is the
maximum over those). A final step builds the root `DoubleDealSecurityHeavy`.

Prints a table, appends it to $GITHUB_STEP_SUMMARY when set, and exits 1 if any build
fails. usage: heavy_rss.py   (run from anywhere)
"""
import os
import re
import subprocess
import sys
import time
from pathlib import Path

SEC = Path(__file__).resolve().parents[1]
ROOT = SEC / 'DoubleDealSecurityHeavy.lean'


def modules():
    mods = re.findall(r'^import\s+(DoubleDealSecurityHeavy\.\S+)\s*$', ROOT.read_text(), re.M)
    if not mods:
        raise SystemExit(f'no heavy imports found in {ROOT}')
    return mods + ['DoubleDealSecurityHeavy']


def build(mod):
    t = time.time()
    p = subprocess.Popen(['lake', 'build', mod], cwd=SEC, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True)
    out = p.stdout.read()
    _, status, ru = os.wait4(p.pid, 0)
    p.stdout.close()
    p.returncode = os.waitstatus_to_exitcode(status)
    return p.returncode, time.time() - t, ru.ru_maxrss / 1024 / 1024, out  # KiB -> GiB


def main():
    rows, rc = [], 0
    for mod in modules():
        code, dt, gib, out = build(mod)
        status = 'ok' if code == 0 else f'FAILED ({code})'
        print(f'{mod}: {status}, {dt:.0f} s, peak RSS {gib:.2f} GiB', flush=True)
        if code != 0:
            print(out)
            rc = 1
        rows.append(f'| `{mod}` | {status} | {dt:.0f} | {gib:.2f} |')
    table = '\n'.join(['| module (lake build step) | result | wall s | peak RSS GiB |',
                       '|---|---|---|---|'] + rows)
    print(table)
    summary = os.environ.get('GITHUB_STEP_SUMMARY')
    if summary:
        with open(summary, 'a') as f:
            f.write('### DoubleDealSecurityHeavy: one module at a time\n\n' + table + '\n')
    return rc


if __name__ == '__main__':
    sys.exit(main())
