"""Candidate BUILD rules (all: at each uncovered hole in reading order, roll; if the
result does not fit, roll again for that hole)."""
from build_dp import Rule

def shipmix(pD, p3, pB, pA):
    return {"D": pD, "S": p3 / 2, "C": p3 / 2, "B": pB, "A": pA}

def make_rules():
    R = {}
    # R_len: "roll the length": 1 or 6 water, 2 D, 3 Sub/Cruiser (coin die), 4 B, 5 A
    R["len"] = Rule("roll-the-length d6 (1,6 water; 2 D; 3 S/C; 4 B; 5 A)", 2 / 6,
                    shipmix(1 / 6, 1 / 6, 1 / 6, 1 / 6))
    R["len"].dattempt = 1 + (4 / 6) * 2 + (1 / 6)          # kind die; ship: direction+bow dice; 3: S/C die
    # R_grow: water 1-2; ship 3-6; grow dice: D->3 on 4-6 (1/2), 3->4 on 6 (1/6), 4->5 on 6 (1/6)
    s = 4 / 6
    R["grow"] = Rule("grow d6 (1-2 water; grow on 4-6, then on 6, then on 6)", 2 / 6,
                     shipmix(s * 1 / 2, s * 1 / 2 * 5 / 6, s * 1 / 2 * 1 / 6 * 5 / 6, s * 1 / 2 * 1 / 6 * 1 / 6))
    R["grow"].dattempt = 1 + s * (2 + 1 + 1 / 2 * (1 + 5 / 6 + 1 / 6))  # dir, bow, grow dice, S/C die
    # R_grow2: water 1-2; grow on 5-6 (1/3) past 2, then on 6, then on 6
    R["grow2"] = Rule("grow d6 (1-2 water; grow on 5-6, then 6, then 6)", 2 / 6,
                      shipmix(s * 2 / 3, s * 1 / 3 * 5 / 6, s * 1 / 3 * 1 / 6 * 5 / 6, s * 1 / 3 / 36))
    R["grow2"].dattempt = 1 + s * (2 + 1 + 1 / 3 * (1 + 5 / 6 + 1 / 6))
    # R_pow: exact x^L weights, x = root of x+4x^2+8x^3+4x^4+4x^5 = 1 (uniform before fit)
    x = 0.3128
    for _ in range(60):
        f = x + 4 * x**2 + 8 * x**3 + 4 * x**4 + 4 * x**5 - 1
        fp = 1 + 8 * x + 24 * x**2 + 16 * x**3 + 20 * x**4
        x -= f / fp
    R["pow"] = Rule(f"x^L weights, x={x:.5f} (not a dice rule; reference)", x,
                    shipmix(4 * x**2, 8 * x**3, 4 * x**4, 4 * x**5))
    R["pow"].dattempt = 0
    R["pow"].x = x
    import copy
    for k in ["grow", "pow", "grow2"]:
        R[k + "_w"] = copy.copy(R[k]); R[k + "_w"].misfit = "water"
        R[k + "_w"].name = R[k].name + " / misfit -> water"
    return R

class FuncRule:
    """A BUILD rule given directly by its local option distribution f(r, rl)."""
    def __init__(self, name, f, dattempt=0):
        self.name, self.f, self.dattempt = name, f, dattempt
        self.dice_cost = None
    def local(self, r, rl):
        return self.f(r, rl), 1.0

GROW = [None, None, 1 / 2, 1 / 6, 1 / 6]     # P(grow past length L) for L=2,3,4

def _ship_lengths(space, grow=GROW):
    """distribution of final length when growth stops at obstacles (space = holes available
    along the heading incl. this one, >= 2)."""
    out = {}; p = 1.0; L = 2
    while True:
        if L == 5 or space <= L:
            out[L] = out.get(L, 0) + p; break
        g = grow[L]
        out[L] = out.get(L, 0) + p * (1 - g); p *= g; L += 1
    return out

def _to_opts(pairs):
    opts = []
    for p, L, o in pairs:
        if L == 3: opts += [(p / 2, "S", o), (p / 2, "C", o)]
        else: opts.append((p, {2: "D", 4: "B", 5: "A"}[L], o))
    return opts

def bump_turn(r, rl, sea=1 / 3):
    """sea on 1-2; else a ship: heading die; if that heading has no room even for 2 holes,
    turn it; if neither has room it is sea.  The ship grows (1/2, 1/6, 1/6) and simply
    stops when it bumps into the edge or a ship."""
    fitH, fitV = r >= 2, rl >= 2
    if not (fitH or fitV): return [(1.0, None, None)]
    heads = [("H", 0.5), ("V", 0.5)] if (fitH and fitV) else ([("H", 1.0)] if fitH else [("V", 1.0)])
    pairs = []
    for o, ph in heads:
        space = r if o == "H" else rl
        for L, pl in _ship_lengths(space).items():
            pairs.append(((1 - sea) * ph * pl, L, o))
    return [(sea, None, None)] + _to_opts(pairs)

def bump_reroll(r, rl, sea=1 / 3):
    """as bump_turn, but if the rolled heading has no room for 2 holes, roll again."""
    fitH, fitV = r >= 2, rl >= 2
    pairs = []
    for o, ok in (("H", fitH), ("V", fitV)):
        if not ok: continue
        space = r if o == "H" else rl
        for L, pl in _ship_lengths(space).items():
            pairs.append(((1 - sea) * 0.5 * pl, L, o))
    Z = sea + sum(p for p, _, _ in pairs)
    return [(sea / Z, None, None)] + _to_opts([(p / Z, L, o) for p, L, o in pairs])

def grow_turn(r, rl, sea=1 / 3):
    """grow rule with re-roll on bump, but a heading with no room for 2 holes is turned."""
    fitH, fitV = r >= 2, rl >= 2
    if not (fitH or fitV): return [(1.0, None, None)]
    heads = [("H", 0.5), ("V", 0.5)] if (fitH and fitV) else ([("H", 1.0)] if fitH else [("V", 1.0)])
    full = _ship_lengths(99)
    pairs = []
    for o, ph in heads:
        space = r if o == "H" else rl
        for L, pl in full.items():
            if L <= space: pairs.append(((1 - sea) * ph * pl, L, o))
    Z = sea + sum(p for p, _, _ in pairs)
    return [(sea / Z, None, None)] + _to_opts([(p / Z, L, o) for p, L, o in pairs])

def extra_rules():
    return {"bump_turn": FuncRule("grow until it bumps; turn if no room", bump_turn),
            "bump_reroll": FuncRule("grow until it bumps; re-roll if no room for 2", bump_reroll),
            "grow_turn": FuncRule("grow, re-roll on bump; turn if no room for 2", grow_turn)}

def bump_reroll_g(grow, sea=1 / 3):
    def f(r, rl):
        fitH, fitV = r >= 2, rl >= 2
        pairs = []
        for o, ok in (("H", fitH), ("V", fitV)):
            if not ok: continue
            space = r if o == "H" else rl
            for L, pl in _ship_lengths(space, grow).items():
                pairs.append(((1 - sea) * 0.5 * pl, L, o))
        Z = sea + sum(p for p, _, _ in pairs)
        return [(sea / Z, None, None)] + _to_opts([(p / Z, L, o) for p, L, o in pairs])
    return f

def variant_rules():
    V = {}
    for name, g in {"br_2_6_3": (1/2, 1/6, 1/3), "br_2_3_6": (1/2, 1/3, 1/6), "br_3_6_6": (1/3, 1/6, 1/6),
                    "br_2_6_2": (1/2, 1/6, 1/2)}.items():
        V[name] = FuncRule(f"bump_reroll grow={g}", bump_reroll_g([None, None] + list(g)))
    V["br_sea2"] = FuncRule("bump_reroll sea=1/2", bump_reroll_g(GROW, sea=1/2))
    return V
