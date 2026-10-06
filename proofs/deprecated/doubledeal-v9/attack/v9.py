"""The frozen v9 sudo as sudoc's Python output (proofs/sudo_py.py), and the helpers the v9 witness
scripts share. encrypt_stages: the Compose steps of trace_encrypt (whitening, rounds 1-5, final)."""
import pathlib, sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[3]))
import sudo_py
V = sudo_py.doubledeal(9)
def swap(x, y): return lambda c: y if c == x else x if c == y else c
def encrypt_stages(m, k): return [s.hand for s in V.trace_encrypt(m, k) if s.kind == sudo_py.text("compose")]
