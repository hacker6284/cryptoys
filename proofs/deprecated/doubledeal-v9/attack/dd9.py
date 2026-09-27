"""numpy wrapper for the C port dd9.c (compiled on first import)."""
import ctypes, subprocess, pathlib, numpy as np
HERE = pathlib.Path(__file__).resolve().parent
LIB = HERE / "build" / "libdd9.so"
if not LIB.exists() or LIB.stat().st_mtime < (HERE / "dd9.c").stat().st_mtime:
    LIB.parent.mkdir(exist_ok=True)
    subprocess.check_call(["gcc", "-O2", "-shared", "-fPIC", "-o", str(LIB), str(HERE / "dd9.c")])
_L = ctypes.CDLL(str(LIB))
_P = np.ctypeslib.ndpointer(dtype=np.int32, flags="C_CONTIGUOUS")
_L.enc_batch.argtypes = [ctypes.c_int, _P, _P, ctypes.c_int, ctypes.c_int, _P]
_L.expand_batch.argtypes = [ctypes.c_int, _P, _P]

def rand_perms(rng, n):
    return np.argsort(rng.random((n, 52)), axis=1).astype(np.int32)

def real_keys(k0):
    """(n,52) master keys -> (n,7,52) PassKey schedules."""
    k0 = np.ascontiguousarray(k0, dtype=np.int32); out = np.empty((len(k0), 7, 52), np.int32)
    _L.expand_batch(len(k0), k0, out); return out

def indep_keys(rng, n):
    return np.ascontiguousarray(rand_perms(rng, n * 7).reshape(n, 7, 52))

# target name -> (full rounds, final round?)
TARGETS = {**{f"E{r}": (r, 0) for r in range(1, 7)}, **{f"F{r}": (r - 1, 1) for r in range(1, 7)}}

def enc(ms, keys, target):
    nfull, fin = TARGETS[target]
    ms = np.ascontiguousarray(ms, dtype=np.int32); keys = np.ascontiguousarray(keys, dtype=np.int32)
    out = np.empty_like(ms); _L.enc_batch(len(ms), ms, keys, nfull, fin, out); return out
