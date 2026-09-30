"""numpy wrapper for cand.c (compiled on first import)."""
import ctypes, subprocess, pathlib, numpy as np
HERE = pathlib.Path(__file__).resolve().parent
LIB = HERE / "build" / "libcand.so"
if not LIB.exists() or LIB.stat().st_mtime < (HERE / "cand.c").stat().st_mtime:
    LIB.parent.mkdir(exist_ok=True)
    subprocess.check_call(["gcc", "-O2", "-shared", "-fPIC", "-o", str(LIB), str(HERE / "cand.c")])
_L = ctypes.CDLL(str(LIB))
_P = np.ctypeslib.ndpointer(dtype=np.int32, flags="C_CONTIGUOUS")
_PL = np.ctypeslib.ndpointer(dtype=np.int64, flags="C_CONTIGUOUS")
_L.enc_batch.argtypes = [ctypes.c_int, _P, _P, ctypes.c_int, ctypes.c_int, _P]
_L.expand_batch.argtypes = [ctypes.c_int, _P, _P]
_L.layer_counts.argtypes = [ctypes.c_int, _P, _P, _PL]
_L.set_var.argtypes = [ctypes.c_int]
TARGETS = {**{f"E{r}": (r, 0) for r in range(1, 7)}, **{f"F{r}": (r - 1, 1) for r in range(1, 7)}}
def rand_perms(rng, n): return np.ascontiguousarray(np.argsort(rng.random((n, 52)), axis=1).astype(np.int32))
def real_keys(k0):
    k0 = np.ascontiguousarray(k0, dtype=np.int32); out = np.empty((len(k0), 7, 52), np.int32)
    _L.expand_batch(len(k0), k0, out); return out
def enc(ms, keys, target, var):
    _L.set_var(var); nfull, fin = TARGETS[target]
    ms = np.ascontiguousarray(ms, dtype=np.int32); keys = np.ascontiguousarray(keys, dtype=np.int32)
    out = np.empty_like(ms); _L.enc_batch(len(ms), ms, keys, nfull, fin, out); return out
def layer_counts(ds, sig, var):
    _L.set_var(var); out = np.zeros(3, np.int64)
    _L.layer_counts(len(ds), np.ascontiguousarray(ds, dtype=np.int32), np.ascontiguousarray(sig, dtype=np.int32), out)
    return out
