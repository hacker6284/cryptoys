"""The ship pass of the ships+pegs key: encoder, decoder, checks.  The rule ("the fleet walk",
including the Sub/Cruiser extra cell and the start marker) is BS SPEC §4.3; the exponent
e = 3^M + sum t_j 3^(M-1-j) is §4.4.  Cells are trits 0/1/2 = plain/white/red.
The peg pass and whole pages are in combined.py; the ECBS Lemma A check that used to sit here
is ../key-selection/ecbs_lemma_a.py."""
import sys, random, math, itertools, json
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))

KL = {"D": 2, "S": 3, "C": 3, "B": 4, "A": 5}

def encode(ships, n=10, m=10):
    """ships: list of (K, orient 'H'/'V', (r,c) of first hole, bow 0=at first hole,1=at last)."""
    role = {}
    for K, o, (r, c), bow in ships:
        L = KL[K]
        cells = [(r, c + t) if o == "H" else (r + t, c) for t in range(L)]
        for t, cell in enumerate(cells):
            assert cell not in role and 0 <= cell[0] < n and 0 <= cell[1] < m
            if t == 0: role[cell] = [1 if o == "H" else 2]
            elif t < L - 1: role[cell] = [0]
            else:
                role[cell] = [2 if bow == 1 else 1] + ([0 if K == "S" else 1] if L == 3 else [])
    trits = []
    for r in range(n):
        for c in range(m):
            trits += role.get((r, c), [0])
    return trits

def decode(trits, n=10, m=10):
    """Inverse of encode (raises on invalid input)."""
    pos = 0
    cover = {}          # cell -> [ship record, index]
    ships = []
    for r in range(n):
        for c in range(m):
            t = trits[pos]; pos += 1
            if (r, c) in cover:
                rec, k = cover.pop((r, c))
                K_o, o, start = rec
                L_so_far = k + 1
                if t == 0:                       # ship continues
                    nxt = (r, c + 1) if o == "H" else (r + 1, c)
                    if L_so_far >= 5 or nxt[0] >= n or nxt[1] >= m or nxt in cover:
                        raise ValueError("bad continue")
                    cover[nxt] = [rec, k + 1]
                else:
                    bow = 1 if t == 2 else 0
                    if L_so_far == 2: K = "D"
                    elif L_so_far == 3:
                        K = "S" if trits[pos] == 0 else ("C" if trits[pos] == 1 else None); pos += 1
                        if K is None: raise ValueError("bad kind cell")
                    elif L_so_far == 4: K = "B"
                    else: K = "A"
                    ships.append((K, o, start, bow))
            else:
                if t == 0: continue
                o = "H" if t == 1 else "V"
                nxt = (r, c + 1) if o == "H" else (r + 1, c)
                if nxt[0] >= n or nxt[1] >= m or nxt in cover: raise ValueError("bad head")
                cover[nxt] = [(None, o, (r, c)), 1]
    if cover or pos != len(trits): raise ValueError("unfinished")
    return sorted(ships)

def bs_exponent(trits):
    e = 1                                 # leading marker cell (white)
    for t in trits: e = 3 * e + t
    return e

def bs_decode_exponent(e, n=10, m=10):
    ds = []
    while e > 0: ds.append(e % 3); e //= 3
    ds.reverse()
    assert ds[0] == 1
    return decode(ds[1:], n, m)

def all_layouts(n, m):
    """every placement with bows, as ship lists"""
    out = []
    grid = [[False] * m for _ in range(n)]
    def rec(pos, ships):
        while pos < n * m and grid[pos // m][pos % m]: pos += 1
        if pos == n * m: out.append(list(ships)); return
        r, c = divmod(pos, m)
        grid[r][c] = True; rec(pos + 1, ships); grid[r][c] = False
        for K, L in KL.items():
            for o in "HV":
                cells = [(r, c + t) if o == "H" else (r + t, c) for t in range(L)]
                if all(a < n and b < m and not grid[a][b] for a, b in cells):
                    for a, b in cells: grid[a][b] = True
                    for bow in (0, 1): rec(pos + 1, ships + [(K, o, (r, c), bow)])
                    for a, b in cells: grid[a][b] = False
    rec(0, [])
    return out

if __name__ == "__main__":
    print("== injectivity, exhaustive on small grids ==")
    for g in [(1, 2), (2, 2), (1, 5), (2, 3), (3, 3), (2, 5), (3, 4), (4, 4)]:
        L = all_layouts(*g)
        es = {}
        for s in L:
            t = encode(s, *g)
            assert decode(t, *g) == sorted(s)
            e = bs_exponent(t)
            assert e not in es, ("collision", s, es[e])
            es[e] = s
        print(f"  {g[0]}x{g[1]}: {len(L)} layouts (count A), {len(es)} distinct exponents, decode(encode)=id")
    # random 10x10 layouts from the exact uniform sampler
    import free_fleet_count as f
    rng = random.Random(3)
    p = f.pieces_for("A"); S, base = f.forward_store(10, 10, p, True)
    cells = []; hits = []; seen = set()
    for _ in range(20000):
        sh = f.sample_layout(S, base, 10, 10, p, True, rng)
        ships = []
        for Lg, o, r, c in sh:
            K = rng.choice([k for k, l in KL.items() if l == Lg]); ships.append((K, o, (r, c), rng.randrange(2)))
        t = encode(ships)
        assert bs_decode_exponent(bs_exponent(t)) == sorted(ships)
        cells.append(len(t)); hits.append(sum(t))
    print(f"== 10x10 uniform layouts: 20000 round trips OK; cells walked mean {sum(cells)/len(cells):.3f} "
          f"(min {min(cells)}, max {max(cells)}), hit units mean {sum(hits)/len(hits):.3f}")
    print("   max possible cells = 100 + 33 (33 three-hole ships tile 99 holes) = 133")

def decode_multi(trits, G, n=10, m=10):
    """Decode G grids walked like pages (one leading marker for the whole key)."""
    out = []; pos = 0
    for g in range(G):
        # find how many trits grid g uses by decoding greedily
        for end in range(pos + n * m, min(len(trits), pos + n * m + 34) + 1):
            try:
                out.append(decode(trits[pos:end], n, m)); pos = end; break
            except (ValueError, IndexError):
                continue
        else:
            raise ValueError("grid %d" % g)
    if pos != len(trits): raise ValueError("trailing")
    return out

def test_multi(N=3000, seed=9):
    import random
    from sim_bump import build_bump
    rng = random.Random(seed)
    for _ in range(N):
        a, b = build_bump(rng), build_bump(rng)
        t = encode(a) + encode(b)
        e = bs_exponent(t)
        ds = []
        x = e
        while x: ds.append(x % 3); x //= 3
        ds.reverse(); assert ds[0] == 1
        assert decode_multi(ds[1:], 2) == [sorted(a), sorted(b)]
    return N
