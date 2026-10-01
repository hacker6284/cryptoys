"""BS (Battleship Diffie-Hellman): peg-recipe simulation of arithmetic mod p = 3^n - c.
Evidence harness, cross-checked against bs.sudo by check_oracle.py; not a reference.  The
normative description is primitives/key_exchange/bs/SPEC.md with bs.sudo beside it.
Everything here acts on COLOURS only: '.' empty, 'W' white, 'R' red.  No colour is ever turned into a
number; the only operations are the recipes of BS SPEC section 3:
  CLICK  : spin a hole one click on the wheel  empty -> white -> red -> empty
  DROP   : a white peg = one click, a red peg = two clicks; whenever a hole clicks from red over to
           empty, flick a white into the next hole up (the ODOMETER carry)
  LAY    : lay a copy of register A into a strip starting at some hole (drop each of A's pegs)
  MULTIPLY A x B: for every pegged hole i of B, lay A starting at hole i (twice if B's peg is red)
  FOLD   : while any peg sits at/after hole n: lift the highest one and lay the TOLL register starting
           n holes lower (twice if the lifted peg was red)
  TIDY   : copy, pour the toll into the copy; if a peg spills into hole n the copy (minus the spill)
           is the tidy answer and slides back into X, otherwise the original is kept
A move = one peg placed, lifted, or swapped for another colour in one hole (so a drop costs one move
for its own hole plus one move per carry it causes)."""

WHEEL = {'.': 'W', 'W': 'R', 'R': '.'}

class Counter:
    def __init__(s): s.reset()
    def reset(s): s.moves = 0; s.ops = {}
    def op(s, k, v=1): s.ops[k] = s.ops.get(k, 0) + v
C = Counter()

class Field:
    """n = register length (trits); toll = colour list of c = 3^n - p (hole 0 first)."""
    def __init__(s, n, toll):
        s.n = n; s.toll = toll
        s.toll_pegs = [(j, t) for j, t in enumerate(toll) if t != '.']
    def empty(s, m=None): return ['.'] * (s.n if m is None else m)

def drop(strip, i, colour):
    """drop a peg of `colour` into hole i: white = 1 click, red = 2 clicks; red->empty click => carry"""
    clicks = 1 if colour == 'W' else 2
    while True:
        carry = False
        for _ in range(clicks):
            if strip[i] == 'R': carry = True
            strip[i] = WHEEL[strip[i]]
        C.moves += 1
        if not carry: return
        C.op('carry'); i += 1; clicks = 1          # flick a white into the next hole up

def lay(strip, A, offset, times=1):
    for _ in range(times):
        for j, a in enumerate(A):
            if a != '.': drop(strip, offset + j, a)

def fold(F, strip):
    """always lift the highest peg at/after hole n and lay the toll n holes lower (twice if red)"""
    n = F.n
    h = len(strip) - 1
    while h >= n:
        c = strip[h]
        if c == '.': h -= 1; continue
        strip[h] = '.'; C.moves += 1; C.op('fold_lift')
        for _ in range(1 if c == 'W' else 2):
            for j, t in F.toll_pegs: drop(strip, h - n + j, t)
        # a carry can only re-peg holes <= h (value went down), so keep scanning from h
    return strip

def slide_out(F, strip):
    """move the answer (holes 0..n-1 of the strip) into a register: lift + place each peg"""
    r = strip[:F.n]; C.moves += 2 * sum(x != '.' for x in r); return r

def clear(reg): C.moves += sum(x != '.' for x in reg)

def multiply(F, A, B, nudge=0, dest=None):
    """A x B mod p.  nudge = 1 or 2 lays every copy one/two holes higher (= also multiply by 3 or 9).
       The strip has 2n holes; a nudged product runs up to `nudge` holes further (BS SPEC B3 step 1).
       dest = the register the answer slides into: its old pegs are lifted first (B3 step 3)."""
    C.op('mul')
    strip = F.empty(2 * F.n + nudge)
    try:
        for i, b in enumerate(B):
            if b != '.': lay(strip, A, i + nudge, 1 if b == 'W' else 2)
    except IndexError:
        raise AssertionError("strip overflow: the product ran past hole 2n + nudge - 1")
    fold(F, strip)
    if dest is not None: clear(dest)
    return slide_out(F, strip)

def tidy(F, X):
    """canonical form: if X >= p return X - p.  Copy X, pour the toll in; spill into hole n => the copy slides back into X."""
    C.op('tidy')
    cp = X[:] + ['.']; C.moves += sum(x != '.' for x in X)        # one spare hole: X + c < 2 * 3^n
    lay(cp, F.toll, 0)
    if cp[F.n] != '.':
        assert cp[F.n] == 'W'
        C.moves += 1                                     # lift the spilled white; the copy is the answer
        clear(X); return slide_out(F, cp)                # lift X's pegs, slide the copy back into X
    clear(cp); return X

def one(F): r = F.empty(); r[0] = 'W'; return r
def is_one(X): return X[0] == 'W' and all(x == '.' for x in X[1:])
def is_empty(X): return all(x == '.' for x in X)

def check_and_square(F, B):
    """received-value check (Wong 5.4): square it, tidy; reject if the square is empty (0) or a lone
       white in hole 0 (1).  Otherwise the square is the base for the shared walk."""
    if len(B) != F.n: raise ValueError("wrong length")
    S = tidy(F, multiply(F, B, B))
    if is_empty(S) or is_one(S): raise ValueError("REJECT: received value squares to 0 or 1")
    return S

def walk(F, fleets, base=None):
    """The key walk B7 (left-to-right cube-and-multiply).  fleets = list of cell strings with
       '.', 'W', 'R' (plain / white / red), walked in order; for the ships+pegs key this is one
       string: the start marker 'W', the ship pass, the peg pass (../ships-pegs/keygrid.py).
       base None  -> public phase, base g = 3: a hit is a NUDGE of the second cube product
                     (white: lay one hole higher, red: two holes higher);
       base = reg -> shared phase: after cubing, white -> multiply by base once, red -> twice."""
    X = Y = None
    for board in fleets:
        for cell in board:
            if X is None:
                if cell == '.': continue                         # accumulator is still 1: skip
                if base is None:
                    X = F.empty(); X[1 if cell == 'W' else 2] = 'W'; C.moves += 1   # 3 or 9
                else:
                    X = base[:] if cell == 'W' else multiply(F, base, base)
                    if cell == 'W': C.moves += sum(x != '.' for x in base)
                continue
            C.op('cube')
            Y = multiply(F, X, X, dest=Y)                        # square; lifts Y's old pegs first
            nud = 0 if (base is not None or cell == '.') else (1 if cell == 'W' else 2)
            X = multiply(F, Y, X, nud, dest=X)                   # cube (and nudge on a hit); Y keeps X x X
            if base is not None and cell != '.':
                for _ in range(1 if cell == 'W' else 2):
                    X = multiply(F, X, base, dest=X)
    assert X is not None, "the walk never started: the key must begin with the start marker (B7)"
    return tidy(F, X)
