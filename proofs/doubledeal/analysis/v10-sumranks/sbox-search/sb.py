"""ctypes wrapper for sbox.c (v10 SumRanks S-box + differential survey)."""
import ctypes, subprocess, pathlib, numpy as np
HERE = pathlib.Path(__file__).resolve().parent
LIB = HERE / "build" / "libsbox.so"   # gitignored (../.gitignore: build/)
if not LIB.exists() or LIB.stat().st_mtime < (HERE / "sbox.c").stat().st_mtime:
    LIB.parent.mkdir(exist_ok=True)
    subprocess.check_call(["gcc", "-O3", "-march=native", "-shared", "-fPIC", "-o", str(LIB), str(HERE / "sbox.c")])
L = ctypes.CDLL(str(LIB))
U8 = np.ctypeslib.ndpointer(dtype=np.uint8, flags="C_CONTIGUOUS")
L.sr_amt.argtypes = [U8, U8, U8]
L.sr_batch.argtypes = [ctypes.c_int, U8, U8]
L.survey.argtypes = [ctypes.c_int, U8, ctypes.c_int, ctypes.c_uint64, np.ctypeslib.ndpointer(dtype=np.int64), U8]
L.same_only.argtypes = [U8, ctypes.c_int, ctypes.c_uint64]; L.same_only.restype = ctypes.c_long
def u8(x): return np.ascontiguousarray(np.array(x, dtype=np.uint8))
def sr(grid52):
    out = np.zeros(52, np.uint8); amt = np.zeros(17, np.uint8); L.sr_amt(u8(grid52), out, amt); return out.tolist(), amt.tolist()
def survey(mode, diff, n, seed=1):
    res = np.zeros(4, np.int64); top = np.zeros(52, np.uint8)
    L.survey(mode, u8(diff), n, seed, res, top)
    return dict(same=int(res[0]), top=int(res[1]), top_is_same=bool(res[2]), distinct=int(res[3]), top_diff=top.tolist(), n=n)
def same_only(tau, n, seed=1): return L.same_only(u8(tau), n, seed)
# card helpers: card = 13*suit + rank ; suits 0 C, 1 H, 2 S, 3 D ; GF(4) label C0 H2 S3 D1
SUITS = "CHSD"; RANKS = "A23456789TJQK"
def card(s, r): return 13 * SUITS.index(s) + RANKS.index(r) if isinstance(r, str) else 13 * SUITS.index(s) + r
def name(c): return RANKS[c % 13] + SUITS[c // 13]
def cyc(*cycles):
    """permutation of 0..51 from cycles (lists of ints)."""
    p = list(range(52))
    for c in cycles:
        for i, x in enumerate(c): p[x] = c[(i + 1) % len(c)]
    return p
def wilson(k, n, z=1.96):
    if n == 0: return (0, 1)
    p = k / n; d = 1 + z*z/n; c = p + z*z/(2*n); h = z * ((p*(1-p) + z*z/(4*n)) / n) ** 0.5
    return (max(0, (c - h) / d), min(1, (c + h) / d))
