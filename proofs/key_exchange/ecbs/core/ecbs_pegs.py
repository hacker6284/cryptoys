"""ECBS peg recipes, acting on COLOURS only ('.', 'W', 'R'), with a move counter.
Written from the recipe text in ECBS_SPEC.md §4 (independent of kx-report/peg).

Move convention (ECBS_SPEC.md §4.0): every single peg action is one move --
placing a peg, lifting a peg, or changing a hole's colour by dropping a peg into it.
A 'jump' (lift from one hole, place in another) is 2 moves. Clearing a register or strip
counts one move per peg lifted.  Reading/comparing costs nothing.
"""
NEXT = {'.': 'W', 'W': 'R', 'R': '.'}      # colour wheel: empty -> white -> red -> empty
PREV = {'.': 'R', 'W': '.', 'R': 'W'}
MIRROR = {'.': '.', 'W': 'R', 'R': 'W'}

class Board:
    def __init__(self, n, k):
        self.n, self.k = n, k                # field GF(3^n), fold rule x^n = x^k + 1
        self.moves = 0; self.ops = {}
    def op(self, name): self.ops[name] = self.ops.get(name, 0) + 1
    # ---- R1 drop ------------------------------------------------------------
    def drop(self, reg, i, colour, mirror=False):
        if colour == '.': return
        if mirror: colour = MIRROR[colour]
        reg[i] = NEXT[reg[i]] if colour == 'W' else PREV[reg[i]]
        self.moves += 1
    # ---- helpers --------------------------------------------------------------
    def empty(self, length=None): return ['.'] * (self.n if length is None else length)
    def single(self, colour): r = self.empty(); r[0] = colour; self.moves += colour != '.'; return r
    def copy(self, reg):
        self.moves += sum(c != '.' for c in reg); return reg[:]
    def clear(self, reg):
        self.moves += sum(c != '.' for c in reg)
    def mirror_in_place(self, reg):
        for i, c in enumerate(reg):
            if c != '.': reg[i] = MIRROR[c]; self.moves += 1
    # ---- R2 add ---------------------------------------------------------------
    def add_into(self, dst, src, offset=0, mirror=False):
        for i, c in enumerate(src):
            if c != '.': self.drop(dst, i + offset, c, mirror)
    def add(self, a, b):  r = self.copy(a); self.add_into(r, b); return r
    def sub(self, a, b):  r = self.copy(a); self.add_into(r, b, mirror=True); return r
    # ---- R3 fold ----------------------------------------------------------------
    def fold(self, strip):
        n, k = self.n, self.k
        for j in range(len(strip) - 1, n - 1, -1):
            c = strip[j]
            if c != '.':
                strip[j] = '.'; self.moves += 1                  # lift
                self.drop(strip, j - n, c); self.drop(strip, j - n + k, c)
        return strip[:n]
    # ---- R4 multiply ----------------------------------------------------------------
    def mul(self, a, b):
        self.op('mul'); strip = self.empty(2 * self.n - 1)
        for i, c in enumerate(b):
            if c != '.': self.add_into(strip, a, offset=i, mirror=(c == 'R'))
        return self.fold(strip)
    # ---- R5 cube (consumes its input: pegs jump) ----------------------------------
    def cube(self, a):
        self.op('cube'); strip = self.empty(3 * self.n - 2)
        for i, c in enumerate(a):
            if c != '.': strip[3 * i] = c; self.moves += 2          # lift + place
        for i in range(len(a)): a[i] = '.'
        return self.fold(strip)
    def cube_keep(self, a):                                           # cube a copy, keep the original
        return self.cube(self.copy(a))
    def is_empty(self, a): return all(c == '.' for c in a)
    # ---- R6 invert (Itoh-Tsujii) -------------------------------------------------
    def invert(self, x):
        self.op('inv'); n = self.n
        bits = bin(n - 1)[2:]
        e = self.copy(x); m = 1
        for b in bits[1:]:
            t = self.copy(e)
            for _ in range(m): t = self.cube(t)
            new = self.mul(t, e); self.clear(t); self.clear(e); e = new; m *= 2
            if b == '1':
                t = self.cube(e); new = self.mul(t, x); self.clear(t); e = new; m += 1
        inv = self.cube(e)                                            # e is consumed
        norm = self.mul(inv, x)
        assert all(c == '.' for c in norm[1:]) and norm[0] != '.', "norm not in GF(3)*"
        if norm[0] == 'R': self.mirror_in_place(inv)
        self.clear(norm)
        return inv
    # ---- R7 points ----------------------------------------------------------------
    def frobenius(self, Q):                                           # cube X, Y, Z (consumes Q)
        return tuple(self.cube(c) for c in Q)
    def mixed_add(self, Q, x2, y2, mirror=False):
        """Q = (X, Y, Z) projective; (x2, +-y2) affine. Returns Q + (x2, y2) or raises on v = 0.
           Consumes Q.  Script (a = 2, char 3):
           v = x2 Z - X; u = y2 Z - Y; w = v - X - Z; A = u u Z - v v w;
           X' = v A; Y' = u (v v X - A) - v v v Y; Z' = v v v Z."""
        self.op('ptadd'); X, Y, Z = Q
        if mirror: y2 = self.copy(y2); self.mirror_in_place(y2)
        t = self.mul(x2, Z); v = self.sub(t, X); self.clear(t)
        t = self.mul(y2, Z); u = self.sub(t, Y); self.clear(t)
        if mirror: self.clear(y2)
        if self.is_empty(v):
            raise ArithmeticError("exceptional case: v is empty (doubling or inverse)")
        w = self.sub(v, X); w2 = self.sub(w, Z); self.clear(w); w = w2
        uu = self.mul(u, u); uuZ = self.mul(uu, Z); self.clear(uu)
        vv = self.mul(v, v); vvv = self.mul(vv, v)
        t = self.mul(vv, w); A = self.sub(uuZ, t); self.clear(t); self.clear(uuZ); self.clear(w)
        X3 = self.mul(v, A)
        t = self.mul(vv, X); s = self.sub(t, A); self.clear(t)
        t1 = self.mul(u, s); t2 = self.mul(vvv, Y); Y3 = self.sub(t1, t2)
        for r in (s, t1, t2): self.clear(r)
        Z3 = self.mul(vvv, Z)
        for r in (u, v, vv, vvv, A, X, Y, Z): self.clear(r)
        return (X3, Y3, Z3)
    def to_affine(self, Q):
        X, Y, Z = Q; zi = self.invert(Z)
        x = self.mul(X, zi); y = self.mul(Y, zi)
        for r in (X, Y, Z, zi): self.clear(r)
        return (x, y)
    # ---- R8 walks -----------------------------------------------------------------------
    def walk(self, digits, x, y):
        """digits: sequence of steps; each step is 'F' (Frobenius) or ('A', colour, base) where base
           is (x, y) affine and colour 'W' adds base, 'R' adds its mirror.  Q starts at 'nothing';
           Frobenius on 'nothing' is skipped; the first addition sets Q = +-base with Z = white."""
        Q = None
        for d in digits:
            if d == 'F':
                if Q is not None: Q = self.frobenius(Q)
            else:
                _, colour, (bx, by) = d
                if Q is None:
                    yy = self.copy(by)
                    if colour == 'R': self.mirror_in_place(yy)
                    Q = (self.copy(bx), yy, self.single('W'))
                else:
                    Q = self.mixed_add(Q, bx, by, mirror=(colour == 'R'))
        return Q
    # ---- R9 checks ------------------------------------------------------------------------
    def on_curve(self, x, y):
        """y*y  versus  cube(x) + (x*x mirrored, i.e. + 2 x^2) + one white peg in hole 0."""
        lhs = self.mul(y, y)
        rhs = self.cube_keep(x); x2 = self.mul(x, x); self.add_into(rhs, x2, mirror=True); self.clear(x2)
        self.drop(rhs, 0, 'W')
        ok = lhs == rhs; self.clear(lhs); self.clear(rhs); return ok
    def in_F3(self, x, y):
        return all(c == '.' for c in x[1:]) and all(c == '.' for c in y[1:])
