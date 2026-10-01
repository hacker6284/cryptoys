"""Two-grid combined keys (page order: grid1 ships, grid1 pegs, grid2 ships, grid2 pegs),
one start marker: decode 3000 random keys back to both grids."""
import random, collections
from combined import build_combined, encode_combined, exponent, digits_after_marker
from read_rule import decode

def decode_pages(ds, G):
    out = []; pos = 0
    for _ in range(G):
        # the ship pass is self-delimiting: find the shortest prefix that decodes to 100 holes
        for L in range(100, 134):
            try:
                sh = decode(ds[pos:pos + L]); break
            except Exception:
                continue
        # verify prefix choice by re-encoding
        from read_rule import encode
        assert encode(sh) == ds[pos:pos + L]
        pos += L; pg = ds[pos:pos + 100]; pos += 100
        out.append((sh, pg))
    assert pos == len(ds)
    return out

if __name__ == "__main__":
    rng = random.Random(7); ok = 0
    for _ in range(3000):
        gs = [build_combined(rng, letgo_prob=0.0) for _ in range(2)]
        t = sum((encode_combined(s, p) for s, p in gs), [])
        dec = decode_pages(digits_after_marker(exponent(t)), 2)
        assert all(sorted(s) == s2 and p == p2 for (s, p), (s2, p2) in zip(gs, dec))
        ok += 1
    print(f"{ok} two-grid combined keys decode to both grids")
