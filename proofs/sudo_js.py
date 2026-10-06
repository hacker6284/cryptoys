"""Run sudoc's JS output (`sudoc build --target js --tests`) of a repo .sudo from Python, at the pin.

The JS twin of sudo_py.py, for drivers that need speed (the ECBS evidence calls whole board
exchanges). build(path) compiles the .sudo (path relative to the repo root) with the sudoc that
proofs/sudocode.sh selects, runs its sudo tests (TAP) once, and caches the build per process in a
temporary directory removed at exit. Sudo(path) starts `node sudo_js_serve.mjs` on that build;
call(fn, *args) runs one exported function. Records come back as dicts, Option None as None,
enums as {'$': 'Name'}; an Err result or a trap raises SudoError. call_arg(fn, *args) makes an
argument that the server replaces by the result of that exported call (for example
tier('Toy') = call_arg('tier', 'Toy')). This file and the server only move JSON; the algorithms
are sudoc's.

    sys.path.insert(0, str(REPO / 'proofs')); import sudo_js as SJ
    s = SJ.Sudo('primitives/key_exchange/ecbs/ecbs.sudo')
    s.call('base_point_of', SJ.tier('Toy'))
"""
import atexit, json, os, shutil, subprocess, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, ".."))
_built = {}


class SudoError(Exception):
    pass


def call_arg(fn, *args):
    return {"$call": fn, "args": list(args)}


def tier(name):
    return call_arg("tier", name)


def build(path):
    """sudoc build --target js --tests at the pin; returns (outdir, sudocode commit, sudo sha256)."""
    if path in _built:
        b = _built[path]
        return b["dir"], b["commit"], b["sha"]
    src = os.path.join(ROOT, path)
    out = tempfile.mkdtemp(prefix="sudo_js-")
    atexit.register(shutil.rmtree, out, True)
    stem = os.path.splitext(os.path.basename(path))[0]
    script = (f'set -euo pipefail; ROOT="{ROOT}"; source "$ROOT/proofs/sudocode.sh" >&2; '
              f'"$SUDOC" build --target js --tests -o "{out}" "{src}" >/dev/null; '
              f'node "{out}/_{stem}_impl.mjs" > "{out}/tap.txt"; echo "$SUDOCODE_COMMIT"')
    commit = subprocess.run(["bash", "-c", script], check=True, capture_output=True, text=True).stdout.split()[-1]
    sha = subprocess.run(["sha256sum", src], check=True, capture_output=True, text=True).stdout.split()[0]
    _built[path] = dict(dir=out, commit=commit, sha=sha, stem=stem)
    return out, commit, sha


def provenance(path):
    out, commit, sha = build(path)
    tap = open(os.path.join(out, "tap.txt")).read().strip().splitlines()[-1]
    return {"source": path, "sudo_sha256": sha, "sudocode_commit": commit, "target": "sudoc js",
            "sudo_tests": tap}


class Sudo:
    def __init__(self, path):
        out, _, _ = build(path)
        self.p = subprocess.Popen(["node", os.path.join(HERE, "sudo_js_serve.mjs"), out, _built[path]["stem"]],
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True, bufsize=1)

    def call(self, fn, *args):
        self.p.stdin.write(json.dumps({"fn": fn, "args": list(args)}) + "\n")
        self.p.stdin.flush()
        r = json.loads(self.p.stdout.readline())
        if "err" in r:
            raise SudoError(r["err"])
        return r["r"]

    def close(self):
        self.p.stdin.close(); self.p.wait()
