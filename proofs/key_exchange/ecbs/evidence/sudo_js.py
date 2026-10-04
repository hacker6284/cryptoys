"""Run the code sudoc generates from primitives/key_exchange/ecbs/ecbs.sudo, from Python.

build() compiles ecbs.sudo with the pinned sudoc (proofs/sudocode.sh) to the JS target
and runs its sudo tests (TAP) once; Sudo() starts `node serve.mjs` on that build and
call(fn, *args) runs one exported function. Tiers are passed as tier('Toy'). Numbers
are lists of trits (hole 0 first; 0 empty, 1 white, 2 red); records come back as
dicts, Option None as None, enums as {'$': 'Name'}; an Err result or a trap comes back
as SudoError. Nothing here computes ECBS: it only moves JSON.
"""
import json, os, subprocess, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", "..", "..", ".."))
SUDO = os.path.join(ROOT, "primitives", "key_exchange", "ecbs", "ecbs.sudo")
_built = {}


class SudoError(Exception):
    pass


def tier(name):
    return {"tier": name}


def build():
    """sudoc build --target js --tests at the pin; returns (outdir, sudocode commit, sudo sha256)."""
    if "dir" in _built:
        return _built["dir"], _built["commit"], _built["sha"]
    out = tempfile.mkdtemp(prefix="ecbs-js-")
    script = (f'set -euo pipefail; ROOT="{ROOT}"; source "$ROOT/proofs/sudocode.sh"; '
              f'"$SUDOC" build --target js --tests -o "{out}" "{SUDO}" >/dev/null; '
              f'node "{out}/_ecbs_impl.mjs" > "{out}/tap.txt"; echo "$SUDOCODE_COMMIT"')
    commit = subprocess.run(["bash", "-c", script], check=True, capture_output=True, text=True).stdout.split()[-1]
    sha = subprocess.run(["sha256sum", SUDO], check=True, capture_output=True, text=True).stdout.split()[0]
    _built.update(dir=out, commit=commit, sha=sha)
    return out, commit, sha


def provenance():
    out, commit, sha = build()
    tap = open(os.path.join(out, "tap.txt")).read().strip().splitlines()[-1]
    return {"source": "primitives/key_exchange/ecbs/ecbs.sudo", "sudo_sha256": sha,
            "sudocode_commit": commit, "target": "sudoc js", "sudo_tests": tap}


class Sudo:
    def __init__(self):
        out, _, _ = build()
        self.p = subprocess.Popen(["node", os.path.join(HERE, "serve.mjs"), out], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, text=True, bufsize=1)

    def call(self, fn, *args):
        self.p.stdin.write(json.dumps({"fn": fn, "args": list(args)}) + "\n")
        self.p.stdin.flush()
        r = json.loads(self.p.stdout.readline())
        if "err" in r:
            raise SudoError(r["err"])
        return r["r"]

    def close(self):
        self.p.stdin.close(); self.p.wait()
