"""Import sudoc's Python output (`sudoc build --target py`) of a repo .sudo, at the sudocode pin.

The generated Python is not committed. Each process builds what it loads into a temporary
directory (removed at exit), with the sudoc that proofs/sudocode.sh selects: $SUDOC if set (as in
the generated-fresh CI job, which builds it at proofs/SUDOCODE_PIN), otherwise built at the pin in
$SUDOCODE_DIR (default /tmp/sudocode).

    sys.path.insert(0, str(REPO / 'proofs')); import sudo_py
    dd = sudo_py.doubledeal(9)         # DoubleDeal v8..v12 (DOUBLEDEAL table)
    dd.encrypt(msg, key)               # any sudo func, exported or not: plain lists in, plain lists out

Builds are isolated per load: each build directory is imported as its own package, registered
under its unique temporary directory name (not via sys.path), and sudoc's package-relative imports
keep its modules and runtime inside it. So builds whose modules share names load side by side,
each with its own runtime. Only the generated implementation module is used; sudoc's host API
module is not. This file is a loader only; the algorithms are sudoc's.

usage: python3 proofs/sudo_py.py --selftest
"""
import atexit, dataclasses, functools, json, shutil, subprocess, sys, tempfile, types
import importlib, importlib.machinery, importlib.util
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
DOUBLEDEAL = {v: f'primitives/cipher/doubledeal/v{v}/doubledeal_v{v}.sudo' for v in (8, 9, 10, 11)}
DOUBLEDEAL[12] = 'primitives/cipher/doubledeal/doubledeal.sudo'


@functools.cache
def sudoc():
    """Path of the sudoc binary, via proofs/sudocode.sh (reads the pin; builds at it unless $SUDOC)."""
    sh = 'set -euo pipefail; ROOT="$1"; source "$ROOT/proofs/sudocode.sh" >&2; printf %s "$SUDOC"'
    return subprocess.run(['bash', '-c', sh, 'sudo_py', str(REPO)],
                          check=True, stdout=subprocess.PIPE, text=True).stdout


@functools.cache
def _outdir():
    d = tempfile.mkdtemp(prefix='sudo_py-')
    atexit.register(shutil.rmtree, d, True)
    return Path(d)


def to_rt(x, rt):
    """Host value -> value of the build's runtime rt: list -> CowList (recursively), anything else
    (int, bool, float) unchanged."""
    if isinstance(x, list):
        return rt.lst([to_rt(e, rt) for e in x])
    return x


def host(v, rt):
    """Value of the build's runtime rt -> plain Python: CowList -> list, record -> SimpleNamespace,
    tuple -> tuple (recursively). Text is a list of code points in sudo; compare it with text(s)."""
    if isinstance(v, rt.CowList):
        return [host(e, rt) for e in v]
    if isinstance(v, rt.CowRec):
        v = v._box.d
    if dataclasses.is_dataclass(v) and not isinstance(v, type):
        return types.SimpleNamespace(**{f.name: host(getattr(v, f.name), rt) for f in dataclasses.fields(v)})
    if isinstance(v, tuple):
        return tuple(host(e, rt) for e in v)
    return v


def text(s):
    """A host str as sudo text (as host() returns it)."""
    return [ord(c) for c in s]


class Sudo:
    """One generated build. Attribute access gives impl funcs wrapped with to_rt / host."""
    def __init__(self, impl):
        self.impl, self.rt = impl, impl._rt     # _rt: the generated header's name for the build's runtime

    def __getattr__(self, name):
        f, rt = getattr(self.impl, name), self.rt
        if not callable(f) or isinstance(f, type):
            return host(f, rt)
        return functools.wraps(f)(lambda *args: host(f(*(to_rt(a, rt) for a in args)), rt))


@functools.cache
def load(sudo):
    """Build REPO/sudo with sudoc --target py and import it as its own package (cached per sudo
    path)."""
    out = Path(tempfile.mkdtemp(prefix='sudo_', dir=_outdir()))
    subprocess.run([sudoc(), 'build', '--target', 'py', '-o', str(out), str(REPO / sudo)],
                   check=True, stdout=subprocess.DEVNULL)
    pkg = out.name
    assert pkg.isidentifier(), pkg
    spec = importlib.machinery.ModuleSpec(pkg, None, is_package=True)
    spec.submodule_search_locations = [str(out)]
    sys.modules[pkg] = importlib.util.module_from_spec(spec)
    return Sudo(importlib.import_module(f'{pkg}._{Path(sudo).stem}_impl'))


def doubledeal(v):
    """DoubleDeal v (8..12), from DOUBLEDEAL."""
    return load(DOUBLEDEAL[v])


def _selftest():
    """Each DOUBLEDEAL entry is the sudo its committed vectors were built from (JSON `source`) and
    reproduces their encrypt vectors. MegaDreifach v1 and v2, whose modules share names, load side by
    side, each with its own runtime, and pass their committed KATs."""
    vec = {v: f'proofs/deprecated/doubledeal-v{v}/vectors/doubledeal_v{v}_vectors.json' for v in (8, 9, 10, 11)}
    vec[12] = 'proofs/doubledeal/vectors/doubledeal_vectors.json'
    for v, path in vec.items():
        doc = json.loads((REPO / path).read_text())
        assert doc['source'] == DOUBLEDEAL[v], (v, doc['source'], DOUBLEDEAL[v])
        dd, n = doubledeal(v), 0
        for x in doc['vectors']:
            if x['kind'] == 'encrypt':
                assert dd.encrypt(x['message'], x['key']) == x['cipher'], (v, x['name'])
                n += 1
        assert n, path
        print(f'DoubleDeal v{v}: {DOUBLEDEAL[v]} agrees on {n} encrypt vectors')
    md = {1: 'primitives/hash/megadreifach/v1/megadreifach.sudo', 2: 'primitives/hash/megadreifach/megadreifach.sudo'}
    for v, sudo in md.items():                  # both builds' modules are named _megadreifach_impl
        h = load(sudo)
        kats = json.loads((REPO / f'primitives/hash/megadreifach/kats/megaminx_hash_kats_v{v}.json').read_text())
        for x in kats['vectors']:
            assert bytes(h.Hash(list(bytes.fromhex(x['msg_hex'])))).hex() == x['digest_hex'], (v, x['name'])
        print(f'MegaDreifach v{v}: {sudo} agrees on {len(kats["vectors"])} KATs')
    assert load(md[1]).rt is not load(md[2]).rt and '_sudo_rt' not in sys.modules, 'builds share a runtime'


if __name__ == '__main__':
    if sys.argv[1:] != ['--selftest']:
        sys.exit(__doc__)
    _selftest()
