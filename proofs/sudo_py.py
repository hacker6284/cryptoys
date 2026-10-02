"""Import sudoc's Python output (`sudoc build --target py`) of a repo .sudo, at the sudocode pin.

The generated Python is not committed. Each process builds what it loads into a temporary
directory (removed at exit), with the sudoc that proofs/sudocode.sh selects: $SUDOC if set (as in
the generated-fresh CI job, which builds it at proofs/SUDOCODE_PIN), otherwise built at the pin in
$SUDOCODE_DIR (default /tmp/sudocode). A py build takes a fraction of a second per .sudo.
A local run without $SUDOC clones and builds sudoc into $SUDOCODE_DIR (default /tmp/sudocode).

    sys.path.insert(0, str(REPO / 'proofs')); import sudo_py
    dd = sudo_py.doubledeal(9)         # DoubleDeal v8..v12 (DOUBLEDEAL table)
    dd.encrypt(msg, key)               # any sudo func, exported or not: plain lists in, plain lists out

Only the generated implementation module is loaded (with its runtime), under the name sudoc gives
it (_doubledeal_v9_impl, ...; distinct for DoubleDeal v8..v12); sudoc's host API module is not
used. If the name is already loaded, load() raises rather than alias it: sudoc's py output for
MegaDreifach v1 and v2 collides on module names, a fix that belongs in sudoc, not here. This file
is a loader only; the algorithms are sudoc's.

usage: python3 proofs/sudo_py.py --selftest
"""
import atexit, dataclasses, functools, importlib.util, json, shutil, subprocess, sys, tempfile, types
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


def _exec(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def to_rt(x):
    """Host value -> sudoc runtime value: list -> CowList (recursively), anything else (int, bool,
    float) unchanged."""
    if isinstance(x, list):
        return sys.modules['_sudo_rt'].lst([to_rt(e) for e in x])
    return x


def host(v):
    """sudoc runtime value -> plain Python: CowList -> list, record -> SimpleNamespace, tuple ->
    tuple (recursively). Text is a list of code points in sudo; compare it with text(s)."""
    rt = sys.modules['_sudo_rt']
    if isinstance(v, rt.CowList):
        return [host(e) for e in v]
    if isinstance(v, rt.CowRec):
        v = v._box.d
    if dataclasses.is_dataclass(v) and not isinstance(v, type):
        return types.SimpleNamespace(**{f.name: host(getattr(v, f.name)) for f in dataclasses.fields(v)})
    if isinstance(v, tuple):
        return tuple(host(e) for e in v)
    return v


def text(s):
    """A host str as sudo text (as host() returns it)."""
    return [ord(c) for c in s]


class Sudo:
    """One generated build. Attribute access gives impl funcs wrapped with to_rt / host."""
    def __init__(self, impl):
        self.impl = impl

    def __getattr__(self, name):
        f = getattr(self.impl, name)
        if not callable(f) or isinstance(f, type):
            return host(f)
        return functools.wraps(f)(lambda *args: host(f(*map(to_rt, args))))


@functools.cache
def load(sudo):
    """Build REPO/sudo with sudoc --target py and import it (cached per sudo path)."""
    out = Path(tempfile.mkdtemp(dir=_outdir()))
    subprocess.run([sudoc(), 'build', '--target', 'py', '-o', str(out), str(REPO / sudo)],
                   check=True, stdout=subprocess.DEVNULL)
    rt_path = out / '_sudo_rt.py'
    if '_sudo_rt' not in sys.modules:          # one runtime per process: identical across builds of one sudoc
        _exec('_sudo_rt', rt_path)
    elif Path(sys.modules['_sudo_rt'].__file__).read_bytes() != rt_path.read_bytes():
        raise RuntimeError(f'{sudo}: _sudo_rt.py differs from the runtime already loaded')
    impl_path, = out.glob('_*_impl.py')        # one impl per build (no sudo imports yet)
    name = impl_path.stem
    if name in sys.modules:
        raise RuntimeError(f'{sudo}: module {name} is already loaded '
                           f'(from {getattr(sys.modules[name], "__file__", "?")})')
    return Sudo(_exec(name, impl_path))


def doubledeal(v):
    """DoubleDeal v (8..12), from DOUBLEDEAL."""
    return load(DOUBLEDEAL[v])


def _selftest():
    """Each DOUBLEDEAL entry is the sudo its committed vectors were built from (JSON `source`) and
    reproduces their encrypt vectors."""
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


if __name__ == '__main__':
    if sys.argv[1:] != ['--selftest']:
        sys.exit(__doc__)
    _selftest()
