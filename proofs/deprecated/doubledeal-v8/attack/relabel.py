"""Relabellings of card values, shared by the v8 attack scripts.

A relabelling tau is a list with tau[c] = new card id for card c; it renames card
faces and leaves seats alone.
"""


def tau_swap(pairs):
    """The relabelling that swaps each (x, y) in `pairs` (applied in order)."""
    t = list(range(52))
    for x, y in pairs:
        t[x], t[y] = t[y], t[x]
    return t


def swap(x, y):
    """The transposition x <-> y."""
    return tau_swap([(x, y)])


def app(t, deck):
    """Apply relabelling t to every card of `deck`."""
    return [t[c] for c in deck]
