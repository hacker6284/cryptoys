"""Tests for mdw4_lib (per-card scrambles, memory-free registers).  Reuses mdw3_tests' parts unchanged
(d2scan, d2, d3, merge, big, diag) with the mdw4 rules patched in for kind strings starting with 'Z'."""
import sys

import mdw_lib as W
import mdw_tests as TT
import mdw_d1big as B
import mdw3_lib as T3
import mdw3_tests as X
import mdw4_lib as Z

_em, _mk = W.em, TT.mk          # (already the mdw3-patched versions)


def em_any(kind, t, h, deal, rec=None, stop=52, rounds=True):
    if kind.startswith('Z'):
        return Z.em4(kind, t, h, deal, rec=rec, stop=stop, rounds=rounds)
    return _em(kind, t, h, deal, rec, stop, rounds)


def mk_any(kind, t):
    return Z.make_dm(kind, t) if kind.startswith('Z') else _mk(kind, t)


W.em = em_any
TT.mk = mk_any
B.mk = mk_any
TT.cards_only = lambda kind, h, d: em_any(kind, 0, h, d, rounds=False)


class Shim:
    TURNS = T3.TURNS

    @staticmethod
    def em3(kind, m, h, d, **kw):
        return Z.em4(kind, m, h, d, **kw) if kind.startswith('Z') else T3.em3(kind, m, h, d, **kw)

    @staticmethod
    def make_dm(kind, m):
        return Z.make_dm(kind, m) if kind.startswith('Z') else T3.make_dm(kind, m)

    @staticmethod
    def cost(kind, m):
        return Z.cost(kind, m) if kind.startswith('Z') else T3.cost(kind, m)

    @staticmethod
    def selftest(kinds):
        return T3.selftest([('SBR', 26)]) + Z.selftest([('ZB0F1N', 0), ('ZB0F2N', 0), ('ZB3F2N', 0), ('ZB3F3N', 0),
                                                        ('ZB3R3N', 0), ('ZB3F2E', 9), ('ZH3F0E', 9), ('ZH0F0E', 5), ('ZE3F0E', 9), ('ZP3F0E', 9), ('ZP3F0E', 13), ('ZP0F0E', 9), ('ZP0F0E', 26), ('ZB3F1S', 9), ('ZB0R2S', 8)])


X.T = Shim

if __name__ == '__main__':
    X.main()
