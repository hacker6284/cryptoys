"""Import sudoc's Python output (`sudoc build --target py`) of a repo .sudo, at the sudocode pin.

The generated Python is not committed. Each process builds what it loads into a temporary
directory (removed at exit), with the sudoc that proofs/sudocode.sh selects: $SUDOC if set (as in
the generated-fresh CI job, which builds it at proofs/SUDOCODE_PIN), otherwise built at the pin in
$SUDOCODE_DIR (default /tmp/sudocode). A py build takes a fraction of a second per .sudo.

    sys.path.insert(0, str(REPO / 'proofs')); import sudo_py
    dd = sudo_py.doubledeal(9)         # DoubleDeal v8..v12 (DOUBLEDEAL table)
    dd.encrypt(msg, key)               # any sudo func, exported or not: plain lists in, plain lists out
    dd.api, dd.impl, dd.rt             # the generated modules (api = exports with host checks)
    v1, v2 = sudo_py.megadreifach(1), sudo_py.megadreifach(2)   # coexist in one process

Each .sudo is imported under its own alias (module `<alias>` for the API, `<alias>_impl` for the
implementation), because builds can emit colliding module names (v1 and v2 MegaDreifach both emit
megadreifach.py / _megadreifach_impl.py). This file is a loader only; the algorithms are sudoc's.

usage: python3 proofs/sudo_py.py --selftest
"""
import atexit, dataclasses, functools, importlib.util, json, re, shutil, subprocess, sys, tempfile, types
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
DOUBLEDEAL = {v: f'primitives/cipher/doubledeal/v{v}/doubledeal_v{v}.sudo' for v in (8, 9, 10, 11)}
DOUBLEDEAL[12] = 'primitives/cipher/doubledeal/doubledeal.sudo'
MEGADREIFACH = {1: 'primitives/hash/megadreifach/v1/megadreifach.sudo',
                2: 'primitives/hash/megadreifach/megadreifach.sudo'}


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
    """Host value -> sudoc runtime value: list/bytes/bytearray -> CowList (recursively), tuple
    -> tuple, anything else (int, bool, float) unchanged."""
    rt = sys.modules['_sudo_rt']
    if isinstance(x, (bytes, bytearray)):
        return rt.lst(list(x))
    if isinstance(x, list):
        return rt.lst([to_rt(e) for e in x])
    if isinstance(x, tuple):
        return tuple(to_rt(e) for e in x)
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
    def __init__(self, api, impl, rt):
        self.api, self.impl, self.rt = api, impl, rt

    def __getattr__(self, name):
        f = getattr(self.impl, name)
        if not callable(f) or isinstance(f, type):
            return f
        return functools.wraps(f)(lambda *args: host(f(*map(to_rt, args))))


_LOADED = {}


def load(sudo, alias):
    """Build REPO/sudo with sudoc --target py and import it as `alias` (cached per process)."""
    if alias in _LOADED:
        if _LOADED[alias][0] != sudo:
            raise ValueError(f'alias {alias} already loaded from {_LOADED[alias][0]}')
        return _LOADED[alias][1]
    out = _outdir() / alias
    subprocess.run([sudoc(), 'build', '--target', 'py', '-o', str(out), str(REPO / sudo)],
                   check=True, stdout=subprocess.DEVNULL)
    rt_path = out / '_sudo_rt.py'
    if '_sudo_rt' not in sys.modules:          # one runtime per process: identical across builds of one sudoc
        _exec('_sudo_rt', rt_path)
    elif Path(sys.modules['_sudo_rt'].__file__).read_bytes() != rt_path.read_bytes():
        raise RuntimeError(f'{sudo}: _sudo_rt.py differs from the runtime already loaded')
    impl_path, = out.glob('_*_impl.py')        # one impl per build (no sudo imports yet)
    api_path = out / (impl_path.stem[1:-len('_impl')] + '.py')
    name = impl_path.stem                      # e.g. _megadreifach_impl, emitted by v1 and v2 alike
    saved = sys.modules.pop(name, None)
    try:
        impl = _exec(name, impl_path)
        api = _exec(alias, api_path)           # its `import <name> as _impl` binds the impl just loaded
    finally:
        sys.modules.pop(name, None)
        if saved is not None:
            sys.modules[name] = saved
    sys.modules[alias + '_impl'] = impl
    s = Sudo(api, impl, sys.modules['_sudo_rt'])
    _LOADED[alias] = (sudo, s)
    return s


def doubledeal(v):
    """DoubleDeal v (8..12) from DOUBLEDEAL, as module sudo_doubledeal_v<v>."""
    return load(DOUBLEDEAL[v], f'sudo_doubledeal_v{v}')


def megadreifach(v):
    """MegaDreifach v (1 or 2) from MEGADREIFACH, as module sudo_megadreifach_v<v>."""
    return load(MEGADREIFACH[v], f'sudo_megadreifach_v{v}')


def _selftest():
    """Each DOUBLEDEAL entry is the sudo its committed vectors were built from (JSON `source`) and
    reproduces their encrypt vectors; MegaDreifach v1 and v2, both loaded before either is used,
    reproduce their own KATs through the generated API (fails if the aliases collide)."""
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
    md = {v: megadreifach(v) for v in MEGADREIFACH}
    assert md[1].impl is not md[2].impl and md[1].api._impl is md[1].impl and md[2].api._impl is md[2].impl
    for v, m in md.items():
        kats = json.loads((REPO / f'primitives/hash/megadreifach/kats/megaminx_hash_kats_v{v}.json').read_text())
        for x in kats['vectors']:
            assert bytes(m.api.Hash(list(bytes.fromhex(x['msg_hex'])))).hex() == x['digest_hex'], (v, x['name'])
        print(f'MegaDreifach v{v}: {MEGADREIFACH[v]} agrees on {len(kats["vectors"])} KATs')


if __name__ == '__main__':
    if sys.argv[1:] != ['--selftest']:
        sys.exit(__doc__)
    _selftest()
