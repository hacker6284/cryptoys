"""Independent integer reference for BS (never looks at pegs except to encode/decode)."""
def enc(x, n):
    out = []
    for _ in range(n): out.append('.WR'[x % 3]); x //= 3
    assert x == 0; return out
def dec(reg): return sum('.WR'.index(c) * 3**i for i, c in enumerate(reg))
def exponent(boards):
    """e = the key's cell strings read as one ternary numeral, most significant cell first:
       cell j is the digit of 3^(M-1-j); plain '.' = 0, white 'W' = 1, red 'R' = 2"""
    e = 0
    for b in boards:
        for c in b: e = 3 * e + '.WR'.index(c)
    return e
