"""
Megaminx group model for toy-hash research.

Piece model (fixed centres):
  - 12 faces / centres (identity labels 0..11)
  - 20 corners, each with orientation in {0,1,2}
  - 30 edges, each with orientation in {0,1}

A position is a pair of arrays:
  cp[20], co[20]  — corner permutation and orientation
  ep[30], eo[30]  — edge permutation and orientation

Convention for orientations:
  Corner: 0 = "primary" colour (lowest face index of the three) on the
           lowest-index face among the three slot faces; +1 = CW twist
           of the cubie as viewed from outside the three faces' vertex.
  Edge:   0 = lower face-index colour on the lower face-index slot face.

Composition (group law): g * h means "apply h first, then g"
  (left action on cubies: pieces follow the permutation of the second factor
   first). This matches function composition (g∘h)(x) = g(h(x)).

Face turns are 72° CW as viewed looking at the face centre from outside.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import List, Tuple, Optional
import copy

# ---------------------------------------------------------------------------
# Dodecahedron face adjacency
# Faces 0..11. Neighbours listed in CLOCKWISE order looking from outside.
# Opposite pairs: (0,11), (1,9), (2,10), (3,6), (4,7), (5,8)
# ---------------------------------------------------------------------------

FACE_NEIGHBORS: List[List[int]] = [
    [1, 2, 3, 4, 5],       # 0
    [0, 5, 6, 7, 2],       # 1
    [0, 1, 7, 8, 3],       # 2
    [0, 2, 8, 9, 4],       # 3
    [0, 3, 9, 10, 5],      # 4
    [0, 4, 10, 6, 1],      # 5
    [1, 5, 10, 11, 7],     # 6
    [1, 6, 11, 8, 2],      # 7
    [2, 7, 11, 9, 3],      # 8
    [3, 8, 11, 10, 4],     # 9
    [4, 9, 11, 6, 5],      # 10
    [6, 10, 9, 8, 7],      # 11
]

OPPOSITES = [11, 9, 10, 6, 7, 8, 3, 4, 5, 1, 2, 0]


def verify_geometry() -> None:
    """Sanity-check the face adjacency graph."""
    assert len(FACE_NEIGHBORS) == 12
    for f, nbrs in enumerate(FACE_NEIGHBORS):
        assert len(nbrs) == 5, f
        assert len(set(nbrs)) == 5, f
        assert f not in nbrs
        for n in nbrs:
            assert f in FACE_NEIGHBORS[n], (f, n)
        # neighbours listed CW: consecutive neighbours must be adjacent
        for i in range(5):
            a, b = nbrs[i], nbrs[(i + 1) % 5]
            assert a in FACE_NEIGHBORS[b], (f, a, b)
    for f in range(12):
        assert OPPOSITES[OPPOSITES[f]] == f
        assert OPPOSITES[f] not in FACE_NEIGHBORS[f]
        # opposite shares no neighbours
        assert not (set(FACE_NEIGHBORS[f]) & set(FACE_NEIGHBORS[OPPOSITES[f]]))
    # each face: 5 adj, 1 opp, 5 share-no-pieces (= opp's neighbours)
    for f in range(12):
        share_none = {OPPOSITES[f]} | set(FACE_NEIGHBORS[OPPOSITES[f]])
        assert len(share_none) == 6
        assert share_none.isdisjoint(set(FACE_NEIGHBORS[f]) | {f})


# ---------------------------------------------------------------------------
# Derive corner and edge slots from face adjacency
# ---------------------------------------------------------------------------

def _canonical_corner(a: int, b: int, c: int) -> Tuple[int, int, int]:
    """Rotate so smallest face index is first; keep cyclic order."""
    t = (a, b, c)
    i = t.index(min(t))
    return (t[i], t[(i + 1) % 3], t[(i + 2) % 3])


def _build_corners() -> List[Tuple[int, int, int]]:
    """20 corners: triples of mutually adjacent faces, CW from outside."""
    seen = set()
    corners = []
    for f in range(12):
        nbrs = FACE_NEIGHBORS[f]
        for i in range(5):
            a, b = nbrs[i], nbrs[(i + 1) % 5]
            # faces f,a,b meet at a vertex; order from outside at that vertex
            # Looking from outside along the vertex: need CW order of the three faces.
            # The three faces around the vertex, viewed from outside the solid:
            # For face f with CW neighbours (...,a,b...), the vertex f-a-b
            # as seen from outside has faces in order f -> a -> b (CW) or opposite
            # depending on chirality. We fix: (f, a, b) as stored when f is not
            # necessarily smallest; then canonicalize.
            trip = _canonical_corner(f, a, b)
            if trip not in seen:
                # verify a,b adjacent
                assert a in FACE_NEIGHBORS[b]
                seen.add(trip)
                corners.append(trip)
    assert len(corners) == 20, len(corners)
    return corners


def _build_edges() -> List[Tuple[int, int]]:
    """30 edges: pairs of adjacent faces, ordered with smaller index first."""
    edges = []
    for f in range(12):
        for n in FACE_NEIGHBORS[f]:
            if f < n:
                edges.append((f, n))
    assert len(edges) == 30, len(edges)
    return edges


CORNERS: List[Tuple[int, int, int]] = _build_corners()
EDGES: List[Tuple[int, int]] = _build_edges()

# Index helpers
CORNER_INDEX = {c: i for i, c in enumerate(CORNERS)}
EDGE_INDEX = {e: i for i, e in enumerate(EDGES)}


def corner_at_faces(a: int, b: int, c: int) -> int:
    return CORNER_INDEX[_canonical_corner(a, b, c)]


def edge_at_faces(a: int, b: int) -> int:
    return EDGE_INDEX[(min(a, b), max(a, b))]


# ---------------------------------------------------------------------------
# Face-turn action on slots
# ---------------------------------------------------------------------------

def _face_corner_cycle(face: int) -> List[int]:
    """5 corner-slot indices around `face`, in CW order (looking at face)."""
    nbrs = FACE_NEIGHBORS[face]
    slots = []
    for i in range(5):
        a, b = nbrs[i], nbrs[(i + 1) % 5]
        slots.append(corner_at_faces(face, a, b))
    return slots


def _face_edge_cycle(face: int) -> List[int]:
    """5 edge-slot indices around `face`, in CW order."""
    nbrs = FACE_NEIGHBORS[face]
    return [edge_at_faces(face, n) for n in nbrs]


def _corner_ori_delta(face: int, corner_slot: int) -> int:
    """
    Orientation change when the cubie in `corner_slot` is moved by a CW
    turn of `face`.

    Orientation of a corner cubie = index of the face-colour that sits on
    the lowest-index face of the slot, measured in the cubie's colour-cycle
    (which matches the canonical slot triple cycle).

    Simpler operational definition used here (standard twisty-puzzle):
    a CW face turn twists each moved corner by +1 if the face being turned
    is NOT the lowest-index face of the destination? — actually the usual
    convention for megaminx/cube is:

      Turning a face changes corner orientation by +1 or -1 depending on
      whether the moved cubie's 'U-colour' axis is the turning face.

    We use: after a CW turn of face F, each corner that was on F moves to
    the next slot on F. The orientation change is +1 if F is not the
    primary (lowest) face of the *destination* slot's face-triple when
    the triple is ordered to start at F... 

    Practical rule matching total-twist invariant (sum co ≡ 0 mod 3):
    For each moved corner, δ = 0 if the turning face equals the lowest
    face index among the three faces of the SOURCE slot; else δ = 1 or 2
    so that the colour that was on the turning face stays on the turning
    face (since the face turns in place relative to its centre).

    Colour on face F stays on face F. So orientation is determined by
    which cubie-colour sits on the lowest-index slot face.
    """
    # Source slot faces
    src = CORNERS[corner_slot]
    # After CW turn of `face`, cubie goes to next slot in the face cycle.
    # Colour that was on `face` remains on `face`.
    # We define orientation as: which of the cubie's three colours (indexed
    # 0,1,2 in the solved cubie's canonical colour order) sits on the
    # lowest-index face of the current slot.
    #
    # For the MOVE definition we just need the delta applied to co[] when
    # permuting. Standard: δ ∈ {0,1,2} with sum of deltas over the 5-cycle
    # ≡ 0 (mod 3) for a single face turn (since a 5-cycle of corners with
    # each twisted the same way: 5δ ≡ 0 mod 3 ⇒ δ ≡ 0 mod 3 — wait that
    # forces δ=0!). That's wrong for cubes too...
    #
    # On Rubik's cube a U turn does NOT change corner orientation numbers
    # under the "U/D colour on U/D face" convention. On megaminx the
    # analogous convention: orientation 0 means the colour of the
    # "reference" face among the three sits on a designated reference.
    #
    # Use sticker-based definition via face indices:
    # Cubie colours = the three faces it belongs to when solved (= its id).
    # Slot faces = CORNERS[slot].
    # Orientation = how many CW steps to rotate cubie colours to match
    # slot faces, matching colour of cubie to lowest slot face.
    #
    # When face F turns CW: stickers on F cycle; stickers not on F leave.
    # Implementation via stickers is cleaner — see FaceTurn below.
    raise NotImplementedError


# ---------------------------------------------------------------------------
# Sticker-based representation for correct orientation tracking
# ---------------------------------------------------------------------------
# Corner stickers: 20 corners × 3 faces = 60. Index = 3*corner + local
# where local 0,1,2 correspond to the three faces of CORNERS[corner] in order.
# Edge stickers: 30 edges × 2 = 60. Index = 2*edge + local
# where local 0 = EDGES[edge][0], local 1 = EDGES[edge][1].
#
# A face turn permutes stickers. Piece permutation/orientation is recovered
# from which stickers sit in which slots.

N_CORNER_STICKERS = 60
N_EDGE_STICKERS = 60


def corner_sticker(corner: int, local: int) -> int:
    return 3 * corner + local


def edge_sticker(edge: int, local: int) -> int:
    return 2 * edge + local


def _build_face_turn_sticker_perm(face: int) -> Tuple[List[int], List[int]]:
    """
    Return (corner_sticker_perm, edge_sticker_perm) for one CW 72° turn of
    `face`. Each is a list p with p[i] = image of sticker i (where the
    sticker moves TO).
    """
    cperm = list(range(N_CORNER_STICKERS))
    eperm = list(range(N_EDGE_STICKERS))

    # --- corners ---
    # Slots around face in CW order
    cyc = _face_corner_cycle(face)
    # For each corner slot on this face, find which local index is the
    # sticker on `face`.
    locals_on_face = []
    for slot in cyc:
        faces = CORNERS[slot]
        locals_on_face.append(faces.index(face))

    # A CW turn cycles slots: cubie in cyc[i] moves to cyc[(i+1)%5].
    # The sticker that was on `face` stays on `face`.
    # The other two stickers move to the neighbouring faces.
    #
    # At slot s=cyc[i], faces = (a0,a1,a2) in canonical order.
    # Stickers: local k sits on face ak.
    # After move to slot t=cyc[(i+1)%5], faces' = CORNERS[t].
    # The sticker that was on `face` goes to the local of t that is on face.
    # The sticker that was on nbrs[i] (the CW-previous neighbour? ) ...
    #
    # Neighbours of face: nbrs[0..4] CW. Corner cyc[i] sits between
    # nbrs[i] and nbrs[(i+1)%5], i.e. CORNERS[cyc[i]] = canon(face, nbrs[i], nbrs[i+1]).
    #
    # After CW turn of face: that corner cubie moves into the slot that was
    # between nbrs[i+1] and nbrs[i+2], i.e. cyc[(i+1)%5].
    # Stickers:
    #   - on `face` stays on `face`
    #   - on nbrs[i] moves to on nbrs[i+1]  (the face that was "behind" CW)
    #   - on nbrs[i+1] moves to on nbrs[i+2]
    #
    # Wait: physically, when you turn face F CW, the corner piece slides
    # along F. The sticker on F rotates with F. The two side stickers:
    # the one that was on the "trailing" neighbour moves to where the
    # "leading" neighbour sticker was relative to F... 
    #
    # Corner between nbrs[i] and nbrs[i+1]:
    #   side stickers on nbrs[i] and nbrs[i+1]
    # After CW move to between nbrs[i+1] and nbrs[i+2]:
    #   sticker that was on nbrs[i] is now on nbrs[i+1]
    #   sticker that was on nbrs[i+1] is now on nbrs[i+2]
    #   sticker on face stays on face
    nbrs = FACE_NEIGHBORS[face]
    for i in range(5):
        src_slot = cyc[i]
        dst_slot = cyc[(i + 1) % 5]
        src_faces = CORNERS[src_slot]  # 3 faces
        dst_faces = CORNERS[dst_slot]

        # map each source face -> destination face for that sticker
        face_map = {
            face: face,
            nbrs[i]: nbrs[(i + 1) % 5],
            nbrs[(i + 1) % 5]: nbrs[(i + 2) % 5],
        }
        for loc_src, f_src in enumerate(src_faces):
            f_dst = face_map[f_src]
            loc_dst = dst_faces.index(f_dst)
            cperm[corner_sticker(src_slot, loc_src)] = corner_sticker(dst_slot, loc_dst)

    # --- edges ---
    ecyc = _face_edge_cycle(face)
    # Edge between face and nbrs[i] moves to edge between face and nbrs[(i+1)%5]
    # Sticker on `face` stays on `face`; sticker on nbrs[i] moves to nbrs[(i+1)%5]
    for i in range(5):
        src_e = ecyc[i]
        dst_e = ecyc[(i + 1) % 5]
        src_faces = EDGES[src_e]  # (lo, hi) sorted
        dst_faces = EDGES[dst_e]
        face_map = {
            face: face,
            nbrs[i]: nbrs[(i + 1) % 5],
        }
        for loc_src, f_src in enumerate(src_faces):
            f_dst = face_map[f_src]
            loc_dst = list(dst_faces).index(f_dst)
            eperm[edge_sticker(src_e, loc_src)] = edge_sticker(dst_e, loc_dst)

    return cperm, eperm


# Precompute face-turn sticker perms (1× CW)
_FACE_CPERMS = []
_FACE_EPERMS = []
for _f in range(12):
    _cp, _ep = _build_face_turn_sticker_perm(_f)
    _FACE_CPERMS.append(_cp)
    _FACE_EPERMS.append(_ep)


def _compose_perm(p: List[int], q: List[int]) -> List[int]:
    """(p ∘ q)(i) = p[q[i]]; apply q first, then p."""
    return [p[q[i]] for i in range(len(q))]


def _invert_perm(p: List[int]) -> List[int]:
    inv = [0] * len(p)
    for i, j in enumerate(p):
        inv[j] = i
    return inv


def _perm_power(p: List[int], k: int) -> List[int]:
    """p^k for k in 0..4 (and negative via inverse)."""
    if k < 0:
        return _perm_power(_invert_perm(p), -k)
    out = list(range(len(p)))
    for _ in range(k):
        out = _compose_perm(p, out)
    return out


# ---------------------------------------------------------------------------
# Position class
# ---------------------------------------------------------------------------

@dataclass
class Position:
    """
    Megaminx position via corner/edge permutation + orientation.

    cp[i] = which cubie is in corner slot i
    co[i] = orientation of the cubie in slot i
    ep, eo similarly.

    Identity: cp=ep=range, co=eo=0.
    """
    cp: List[int]
    co: List[int]
    ep: List[int]
    eo: List[int]

    @staticmethod
    def identity() -> "Position":
        return Position(
            list(range(20)), [0] * 20,
            list(range(30)), [0] * 30,
        )

    def copy(self) -> "Position":
        return Position(self.cp[:], self.co[:], self.ep[:], self.eo[:])

    def is_identity(self) -> bool:
        return (
            self.cp == list(range(20)) and self.co == [0] * 20
            and self.ep == list(range(30)) and self.eo == [0] * 30
        )

    def corner_parity(self) -> int:
        """0 even, 1 odd."""
        seen = [False] * 20
        cycles = 0
        for i in range(20):
            if not seen[i]:
                cycles += 1
                j = i
                while not seen[j]:
                    seen[j] = True
                    j = self.cp[j]
        return (20 - cycles) & 1

    def edge_parity(self) -> int:
        seen = [False] * 30
        cycles = 0
        for i in range(30):
            if not seen[i]:
                cycles += 1
                j = i
                while not seen[j]:
                    seen[j] = True
                    j = self.ep[j]
        return (30 - cycles) & 1

    def corner_orientation_sum(self) -> int:
        return sum(self.co) % 3

    def edge_orientation_sum(self) -> int:
        return sum(self.eo) % 2

    def is_valid(self) -> bool:
        """Check megaminx reachability invariants."""
        if sorted(self.cp) != list(range(20)):
            return False
        if sorted(self.ep) != list(range(30)):
            return False
        if any(o not in (0, 1, 2) for o in self.co):
            return False
        if any(o not in (0, 1) for o in self.eo):
            return False
        return (
            self.corner_parity() == 0
            and self.edge_parity() == 0
            and self.corner_orientation_sum() == 0
            and self.edge_orientation_sum() == 0
        )


def _stickers_from_position(pos: Position) -> Tuple[List[int], List[int]]:
    """
    Convert position to sticker arrays.
    cstick[slot_sticker] = cubie_sticker that sits there.
    For cubie c with orientation o in slot s:
      cubie's local colour k sits on slot face (k+o) mod 3
      (i.e. sticker corner_sticker(c, k) is at corner_sticker(s, (k+o)%3)).
    """
    cstick = [0] * 60
    for s in range(20):
        c = pos.cp[s]
        o = pos.co[s]
        for k in range(3):
            cstick[corner_sticker(s, (k + o) % 3)] = corner_sticker(c, k)
    estick = [0] * 60
    for s in range(30):
        e = pos.ep[s]
        o = pos.eo[s]
        for k in range(2):
            estick[edge_sticker(s, (k + o) % 2)] = edge_sticker(e, k)
    return cstick, estick


def _position_from_stickers(cstick: List[int], estick: List[int]) -> Position:
    cp = [0] * 20
    co = [0] * 20
    for s in range(20):
        # Which cubie? Look at any sticker in the slot.
        cubie_st = cstick[corner_sticker(s, 0)]
        c = cubie_st // 3
        k0 = cubie_st % 3  # cubie local colour at slot local 0
        # cubie local k sits at slot local (k+o)%3, so at slot local 0 we have k with (k+o)%3=0
        # ⇒ o = (-k0) % 3, and k0 is the cubie-local at slot 0.
        # From: cstick[s, (k+o)%3] = cubie(c,k)
        # At (k+o)%3 = 0: k = (-o)%3 = k0 ⇒ o = (-k0)%3
        cp[s] = c
        co[s] = (-k0) % 3
    ep = [0] * 30
    eo = [0] * 30
    for s in range(30):
        edge_st = estick[edge_sticker(s, 0)]
        e = edge_st // 2
        k0 = edge_st % 2
        ep[s] = e
        eo[s] = (-k0) % 2
    return Position(cp, co, ep, eo)


def apply_sticker_perm(pos: Position, cperm: List[int], eperm: List[int]) -> Position:
    """
    Apply a sticker permutation to a position.
    cperm[i] = new location of the sticker that was at i
    (i.e. sticker moves from i to cperm[i]).
    """
    cstick, estick = _stickers_from_position(pos)
    # After move: new_cstick[cperm[i]] = cstick[i]
    new_c = [0] * 60
    new_e = [0] * 60
    for i in range(60):
        new_c[cperm[i]] = cstick[i]
        new_e[eperm[i]] = estick[i]
    return _position_from_stickers(new_c, new_e)


def face_turn(pos: Position, face: int, amount: int = 1) -> Position:
    """Apply `amount` CW 72° turns of `face` (amount in {1,2,3,4})."""
    amount %= 5
    if amount == 0:
        return pos.copy()
    cperm = _perm_power(_FACE_CPERMS[face], amount)
    eperm = _perm_power(_FACE_EPERMS[face], amount)
    return apply_sticker_perm(pos, cperm, eperm)


# 48-move alphabet: 12 faces × amounts {1,2,3,4}
MOVES_48: List[Tuple[int, int]] = [(f, a) for f in range(12) for a in (1, 2, 3, 4)]


def apply_move(pos: Position, move: Tuple[int, int]) -> Position:
    return face_turn(pos, move[0], move[1])


# ---------------------------------------------------------------------------
# Group law on positions
# ---------------------------------------------------------------------------

def compose(g: Position, h: Position) -> Position:
    """
    g * h : apply h first, then g. (left action / function composition)

    Cubie that ends in slot s: first h places cubie h.cp[s] with ori h.co[s];
    then g moves that cubie. Equivalently, working in sticker space:
    stickers_of(g*h) = stickers_of(g) after applying the placement of h...

    Standard cubie composition (same as cube):
      (g*h).cp[s] = g.cp[h.cp[s]]  -- wait, that's apply g first if cp is
      "cubie in slot". Careful.

    If state is "which cubie in each slot":
      After move m (as a position relative to solved), new_cp[s] = old_cp[m.cp[s]]
      means: look at where m sends slot s from (m.cp[s] is cubie id = source
      slot under the move when applied to solved)... 

    Representing a move as the position you get by applying it to solved:
      move.cp[s] = cubie now in slot s = the cubie that came FROM somewhere.
      Actually after move on solved: cubie c is in slot m.cp^{-1}[c], or
      slot s contains cubie m.cp[s].

    Applying move m to position p (p then m):
      The cubie now in slot s came from slot m^{-1}(s) in the previous
      position, so (p*m).cp[s] = p.cp[m.cp[s]] if m.cp means "source slot
      whose contents go to s"? 

    Our face_turn on identity: after turn, slot s contains the cubie that
    was previously in the slot that maps TO s. So id.cp was identity;
    after move, new.cp[s] = old cubie in source = source_slot(s).
    So move.cp[s] = source slot of the cubie now in s = which cubie (by id,
    since solved) is in s.

    Applying m to p: (p then m). Slot s gets what was in source_m(s) under p.
    source_m(s) = m.cp[s] (since on solved, cubie id = source slot).
    So (p*m).cp[s] = p.cp[m.cp[s]].
    Orientation: (p*m).co[s] = (p.co[m.cp[s]] + m.co[s]) mod 3.

    compose(g,h) = g*h = apply h first then g = (h then g):
      (g*h).cp[s] = h.cp[g.cp[s]]? No — "h then g" means
      (h then g).cp[s] = h.cp[g.cp[s]] if we use the formula (p then m)
      with p=h, m=g: (h then g).cp[s] = h.cp[g.cp[s]].

    So compose(g,h) with "g*h = h then g" would be confusing.
    We DEFINE: compose(g,h) = g after h = (h then g):
      cp[s] = h.cp[g.cp[s]]
      co[s] = (h.co[g.cp[s]] + g.co[s]) % 3
    And we say compose(g,h) means "g ∘ h" (g after h).
    """
    cp = [0] * 20
    co = [0] * 20
    for s in range(20):
        # h then g: (h then g).cp[s] = h.cp[g.cp[s]]
        cp[s] = h.cp[g.cp[s]]
        co[s] = (h.co[g.cp[s]] + g.co[s]) % 3
    ep = [0] * 30
    eo = [0] * 30
    for s in range(30):
        ep[s] = h.ep[g.ep[s]]
        eo[s] = (h.eo[g.ep[s]] + g.eo[s]) % 2
    return Position(cp, co, ep, eo)


def inverse(g: Position) -> Position:
    """g^{-1} such that compose(g, inverse(g)) = identity = compose(inverse(g), g)."""
    cp = [0] * 20
    co = [0] * 20
    for s in range(20):
        cp[g.cp[s]] = s
        # (g then g^{-1}): co_id[s] = 0 = (g.co[g^{-1}.cp[s]] + g^{-1}.co[s]) % 3
        # g^{-1}.cp[s] = cp[s] above... use: for slot t=g.cp[s] (cubie s in slot t? )
        # Let t be slot: cubie g.cp[t] is in slot t. Inverse puts cubie t into slot g.cp[t]?
        # cp_inv[g.cp[s]] = s.
        # Orientation: (inv then g).co[s] = 0 = (inv.co[g.cp[s]] + g.co[s]) % 3
        # ⇒ inv.co[g.cp[s]] = -g.co[s] (mod 3)
    for s in range(20):
        co[g.cp[s]] = (-g.co[s]) % 3
    # Wait that's inv.co[g.cp[s]] = -g.co[s], so for slot u=g.cp[s], inv.co[u]=-g.co[s]=-g.co[cp_inv[u]]
    # Redo cleanly:
    cp_inv = [0] * 20
    co_inv = [0] * 20
    for s in range(20):
        cp_inv[g.cp[s]] = s
    for s in range(20):
        # inv.co[s] = -g.co[cp_inv[s]] from: inv.co[g.cp[t]] = -g.co[t]
        # with s = g.cp[t], t = cp_inv[s]: inv.co[s] = -g.co[cp_inv[s]]
        co_inv[s] = (-g.co[cp_inv[s]]) % 3
    ep_inv = [0] * 30
    eo_inv = [0] * 30
    for s in range(30):
        ep_inv[g.ep[s]] = s
    for s in range(30):
        eo_inv[s] = (-g.eo[ep_inv[s]]) % 2
    return Position(cp_inv, co_inv, ep_inv, eo_inv)


def face_turn_position(face: int, amount: int = 1) -> Position:
    """Position resulting from applying the turn to the solved puzzle."""
    return face_turn(Position.identity(), face, amount)


# Precompute the 48 move-positions and 12 single CW generators
GEN_CW: List[Position] = [face_turn_position(f, 1) for f in range(12)]
MOVES_48_POS: List[Position] = [face_turn_position(f, a) for f, a in MOVES_48]


def apply_position(p: Position, move_pos: Position) -> Position:
    """Apply move (as a position) to p: p then move. Equals compose(move_pos, p)? 
    (p then m).cp[s] = p.cp[m.cp[s]]; compose(m,p).cp[s] = p.cp[m.cp[s]]. Yes.
    So apply_position(p, m) = compose(m, p).
    """
    return compose(move_pos, p)


# ---------------------------------------------------------------------------
# Sympy permutation representation (for group-order checks)
# ---------------------------------------------------------------------------

def position_to_sympy_perm(pos: Position):
    """
    Map a position to a permutation of 120 stickers (60 corner + 60 edge)
    as a sympy Permutation. Sticker i moves to image[i].
    """
    from sympy.combinatorics import Permutation
    cstick, estick = _stickers_from_position(pos)
    # cstick[slot] = which cubie-sticker is at slot.
    # For the permutation of "where each solved sticker goes":
    # At identity, sticker i is at location i.
    # After pos (applied to solved), location s contains sticker cstick[s]
    # meaning sticker cstick[s] moved to s, so image[cstick[s]] = s.
    image = [0] * 120
    for s in range(60):
        image[cstick[s]] = s
        image[60 + estick[s]] = 60 + s
    return Permutation(image)


def generators_as_sympy():
    from sympy.combinatorics import Permutation, PermutationGroup
    gens = []
    for f in range(12):
        gens.append(position_to_sympy_perm(GEN_CW[f]))
    return PermutationGroup(gens)


# ---------------------------------------------------------------------------
# Rank / unrank (factoradic over the reachable set)
# ---------------------------------------------------------------------------

GROUP_ORDER = (
    (math.factorial(20) // 2)
    * (3 ** 19)
    * (math.factorial(30) // 2)
    * (2 ** 29)
)


def _perm_rank(perm: List[int]) -> int:
    """Lehmer code / factoradic rank of a permutation of 0..n-1."""
    n = len(perm)
    avail = list(range(n))
    rank = 0
    for i, v in enumerate(perm):
        idx = avail.index(v)
        rank = rank * (n - i) + idx
        avail.pop(idx)
    return rank


def perm_unrank(rank: int, n: int) -> List[int]:
    avail = list(range(n))
    out = []
    # extract factoradic digits most-significant first
    facts = [1] * n
    for i in range(1, n):
        facts[i] = facts[i - 1] * i
    # facts[k] = k!
    rem = rank
    for i in range(n):
        f = facts[n - 1 - i]
        d = rem // f
        rem %= f
        out.append(avail.pop(d))
    return out


def perm_parity(perm: List[int]) -> int:
    seen = [False] * len(perm)
    cycles = 0
    for i in range(len(perm)):
        if not seen[i]:
            cycles += 1
            j = i
            while not seen[j]:
                seen[j] = True
                j = perm[j]
    return (len(perm) - cycles) & 1


def even_perm_rank(perm: List[int]) -> int:
    """Rank among even permutations only (0 .. n!/2 - 1), lex/factoradic order."""
    if perm_parity(perm) != 0:
        raise ValueError("odd permutation")
    r = _perm_rank(perm)
    # Count how many even perms have factoradic rank < r.
    # Among {0,...,r-1} exactly ceil(r/2) or similar? Not uniform in pairs.
    # Binary search unrank: find k such that even_perm_unrank(k)==perm.
    # Direct: walk factoradic — for each even perm the k-th is the unique
    # index whose perm is even and exactly k even perms precede it.
    # Count even perms before this one in factoradic order:
    n = len(perm)
    count = 0
    # Brute for small? Too slow for n=30.
    # Better: for each prefix, count even completions.
    # Actually: pair each odd with an even by swapping last two entries
    # when they differ. Standard trick:
    #   rank_even(p) = factoradic(p) // 2   IF we use a code where
    #   swapping n-2 and n-1 flips parity and changes rank by 1.
    #
    # Factoradic does NOT guarantee adjacent ranks are parity-flips.
    # Use: encode even perm by ranking freely on first n-2 choices of the
    # lehmer code, then set the last two to make parity even.
    avail = list(range(n))
    rank = 0
    # Choose first n-2 elements freely (as in lehmer); last 2 determined
    # up to order, and we pick the order that makes overall parity even.
    chosen = []
    for i in range(n - 2):
        idx = avail.index(perm[i])
        rank = rank * (n - i) + idx
        avail.pop(idx)
        chosen.append(perm[i])
    # avail has 2 elements left; perm[n-2], perm[n-1] is one ordering.
    # Number of free choices so far: n*(n-1)*...*(3) = n!/2, perfect.
    # rank is already in 0 .. n!/2 - 1.
    # Verify that the forced even completion matches perm.
    # Build the even completion for this prefix:
    a, b = avail[0], avail[1]
    # parity of chosen prefix as a partial perm: count inversions involving
    # chosen positions plus whether (a,b) or (b,a) is needed.
    trial = chosen + [a, b]
    if perm_parity(trial) == 0:
        even_completion = trial
    else:
        even_completion = chosen + [b, a]
    if even_completion != perm:
        raise ValueError("internal even-perm encoding mismatch")
    return rank


def even_perm_unrank(rank: int, n: int) -> List[int]:
    """Unrank among the n!/2 even permutations (matches even_perm_rank)."""
    if not (0 <= rank < math.factorial(n) // 2):
        raise ValueError("rank out of range")
    avail = list(range(n))
    out = []
    # Digits for first n-2 positions: multipliers (n-1), (n-2), ..., 3
    # Total = n!/2.
    # Extract MS digit first with weight (n-1)!/2 ? 
    # Our rank encoding: sequentially rank = rank*(n-i)+idx for i=0..n-3
    # so least work: peel from the end.
    weights = []
    for i in range(n - 2):
        weights.append(n - i)  # branching at step i
    # After all steps rank in [0, n!/2). Product of weights = n!/2.
    # Peel LS:
    digits = [0] * (n - 2)
    rem = rank
    for i in range(n - 3, -1, -1):
        digits[i] = rem % weights[i]
        rem //= weights[i]
    # rem should be 0; weights[0] is the MS
    # Actually peeling LS means digits[i] corresponds to step i.
    # Wait product: if we did rank = ((d0*w0+d1)*w1+...) the MS is d0.
    # Building: start rank=0; for i in 0..n-3: rank = rank*(n-i)+idx
    # So d0 is MS. To extract: 
    rem = rank
    facts_branch = [1] * (n - 2)
    # branch_mul[i] = product of weights[i+1] * ... 
    for i in range(n - 4, -1, -1):
        facts_branch[i] = facts_branch[i + 1] * weights[i + 1]
    for i in range(n - 2):
        d = rem // facts_branch[i]
        rem %= facts_branch[i]
        out.append(avail.pop(d))
    a, b = avail[0], avail[1]
    trial = out + [a, b]
    if perm_parity(trial) == 0:
        return trial
    return out + [b, a]


def rank_position(pos: Position) -> int:
    """
    Bijective rank in [0, GROUP_ORDER).
    Layout (most significant first):
      even corner perm (20!/2) |
      corner ori[0..18] (3^19); ori[19] determined |
      even edge perm (30!/2) |
      edge ori[0..28] (2^29); ori[29] determined
    """
    if not pos.is_valid():
        raise ValueError("position not in reachable group")
    r = even_perm_rank(pos.cp)
    for i in range(19):
        r = r * 3 + pos.co[i]
    r = r * (math.factorial(30) // 2) + even_perm_rank(pos.ep)
    for i in range(29):
        r = r * 2 + pos.eo[i]
    return r


def unrank_position(rank: int) -> Position:
    if not (0 <= rank < GROUP_ORDER):
        raise ValueError("rank out of range")
    # unpack least-significant first
    eo = [0] * 30
    for i in range(28, -1, -1):
        eo[i] = rank & 1
        rank >>= 1
    eo[29] = (-sum(eo[:29])) % 2
    ep_rank = rank % (math.factorial(30) // 2)
    rank //= math.factorial(30) // 2
    ep = even_perm_unrank(ep_rank, 30)
    co = [0] * 20
    for i in range(18, -1, -1):
        co[i] = rank % 3
        rank //= 3
    co[19] = (-sum(co[:19])) % 3
    cp = even_perm_unrank(rank, 20)
    pos = Position(cp, co, ep, eo)
    assert pos.is_valid()
    return pos


def position_to_bytes(pos: Position) -> bytes:
    """29-byte big-endian encoding of rank."""
    r = rank_position(pos)
    return r.to_bytes(29, "big")


def position_from_bytes(b: bytes) -> Position:
    if len(b) != 29:
        raise ValueError("need 29 bytes")
    return unrank_position(int.from_bytes(b, "big"))


# ---------------------------------------------------------------------------
# Whole-puzzle rotations (icosahedral rotation group, order 60)
# ---------------------------------------------------------------------------

def _face_perm_from_rotation(face_image: List[int]) -> bool:
    """Check face_image is an automorphism of the adjacency graph."""
    for f in range(12):
        nbrs = FACE_NEIGHBORS[f]
        img_nbrs = [face_image[n] for n in nbrs]
        target = FACE_NEIGHBORS[face_image[f]]
        # must be a rotation of target (CW or — rotations preserve orientation)
        if sorted(img_nbrs) != sorted(target):
            return False
        # find rotation offset
        try:
            k = target.index(img_nbrs[0])
        except ValueError:
            return False
        rotated = target[k:] + target[:k]
        if img_nbrs != rotated:
            return False
    return True


def enumerate_face_rotations() -> List[List[int]]:
    """
    The 60 orientation-preserving automorphisms of the dodecahedron face
    graph (= icosahedral rotation group ≅ A5).
    A rotation is determined by where face 0 goes (12 choices) and how its
    neighbour cycle is rotated (5 choices): 12×5=60.
    """
    rots = []
    for f0 in range(12):
        target_nbrs = FACE_NEIGHBORS[f0]
        src_nbrs = FACE_NEIGHBORS[0]
        for k in range(5):
            face_image = [-1] * 12
            face_image[0] = f0
            for i in range(5):
                face_image[src_nbrs[i]] = target_nbrs[(k + i) % 5]
            # propagate using adjacency BFS
            changed = True
            while changed:
                changed = False
                for f in range(12):
                    if face_image[f] < 0:
                        continue
                    sn = FACE_NEIGHBORS[f]
                    tn = FACE_NEIGHBORS[face_image[f]]
                    # find alignment
                    mapped = [(i, face_image[sn[i]]) for i in range(5) if face_image[sn[i]] >= 0]
                    if not mapped:
                        continue
                    i0, t0 = mapped[0]
                    try:
                        j0 = tn.index(t0)
                    except ValueError:
                        face_image = None
                        break
                    for i in range(5):
                        want = tn[(j0 - i0 + i) % 5]
                        if face_image[sn[i]] < 0:
                            face_image[sn[i]] = want
                            changed = True
                        elif face_image[sn[i]] != want:
                            face_image = None
                            break
                    if face_image is None:
                        break
                if face_image is None:
                    break
            if face_image is None or any(x < 0 for x in face_image):
                continue
            if len(set(face_image)) != 12:
                continue
            if _face_perm_from_rotation(face_image):
                # also require opposite preserved (rotation, not reflection)
                ok = all(face_image[OPPOSITES[f]] == OPPOSITES[face_image[f]] for f in range(12))
                if ok and face_image not in rots:
                    rots.append(face_image)
    return rots


def rotation_to_position(face_image: List[int]) -> Position:
    """
    Whole-puzzle rotation as a Position: reassigns pieces according to where
    their home faces go. Centres are fixed in our model (colours stay with
    centres), so a "rotation" here is really: conjugate the puzzle so that
    piece colours move as if the whole puzzle were rotated while colours
    stayed fixed — i.e. the standard "reorientation" used in Rule B.

    Cubie that lived at corner with faces (a,b,c) moves to corner
    (face_image[a], face_image[b], face_image[c]), with orientation matching
    the face map.
    """
    # Build sticker perm from face map
    cperm = [0] * 60
    for slot, faces in enumerate(CORNERS):
        new_faces = (face_image[faces[0]], face_image[faces[1]], face_image[faces[2]])
        # destination slot
        dst = corner_at_faces(*new_faces)
        dst_faces = CORNERS[dst]
        # canonical order of new_faces may differ by rotation from dst_faces
        # Map: sticker on faces[k] goes to sticker on face_image[faces[k]] at dst
        for k in range(3):
            src_st = corner_sticker(slot, k)
            dst_face = face_image[faces[k]]
            dst_local = dst_faces.index(dst_face)
            cperm[src_st] = corner_sticker(dst, dst_local)
    eperm = [0] * 60
    for slot, faces in enumerate(EDGES):
        new_faces = (face_image[faces[0]], face_image[faces[1]])
        dst = edge_at_faces(*new_faces)
        dst_faces = EDGES[dst]
        for k in range(2):
            src_st = edge_sticker(slot, k)
            dst_face = face_image[faces[k]]
            dst_local = list(dst_faces).index(dst_face)
            eperm[src_st] = edge_sticker(dst, dst_local)
    return apply_sticker_perm(Position.identity(), cperm, eperm)


def rule_b_reorientation(pos: Position, corner_slot: int = 0) -> Position:
    """
    Rule-B-like step: read the three colours at a fixed corner slot; choose
    the unique whole-puzzle rotation that sends that cubie's colours to a
    canonical home (the identity corner 0 with orientation 0), and apply it.

    Returns the reoriented position. There are 20×3=60 colourings of a fixed
    corner slot (any of 20 cubies in any of 3 oris), matching |Rot|=60, so
    the colours at one fixed corner determine a unique rotation — IF every
    (cubie, ori) pair appears, which they do (any cubie can reach any slot
    with any orientation, subject to global constraints; for a single corner
    the 60 possibilities are all achievable in some full position).
    """
    # Cubie in corner_slot and its orientation determine which solved corner
    # colours sit on which slot faces.
    cubie = pos.cp[corner_slot]
    ori = pos.co[corner_slot]
    # Colour on slot face CORNERS[corner_slot][j] is cubie's colour
    # CORNERS[cubie][(j - ori) % 3]
    slot_faces = CORNERS[corner_slot]
    cubie_faces = CORNERS[cubie]
    # We want a rotation R such that the colours currently at corner_slot
    # end up matching identity corner 0 with ori 0.
    # After reorientation by R (acting on positions), ...
    #
    # Simpler: find face_image sending cubie_faces (as a triple) to
    # CORNERS[0], matching orientations so ori becomes 0 at slot 0.
    # Current colours on slot_faces[j] = cubie_faces[(j-ori)%3].
    # We want after rotation to have corner 0 solved: colour CORNERS[0][j]
    # on face CORNERS[0][j].
    #
    # The reorientation rotates the puzzle so that the physical cubie at
    # corner_slot moves to slot 0 with ori 0. That means face_image maps
    # slot_faces to CORNERS[0] (with a cyclic shift clearing ori).
    target = CORNERS[0]
    # Map slot_faces[j] -> target[(j - ori) % 3]? Let's think...
    # After moving cubie to slot 0 with ori 0: colour cubie_faces[k] sits on
    # target[k]. Currently colour cubie_faces[k] sits on slot_faces[(k+ori)%3].
    # So we need face_image[slot_faces[(k+ori)%3]] = target[k],
    # i.e. face_image[slot_faces[j]] = target[(j-ori)%3].
    face_image = [-1] * 12
    for j in range(3):
        face_image[slot_faces[j]] = target[(j - ori) % 3]
    # Extend to a full rotation using our enumeration: find the unique rot
    # agreeing on these three faces (they determine it — three faces around
    # a vertex fix a rotation).
    rots = getattr(rule_b_reorientation, "_rots", None)
    if rots is None:
        rots = enumerate_face_rotations()
        rule_b_reorientation._rots = rots
    matches = []
    for rot in rots:
        if all(face_image[f] < 0 or rot[f] == face_image[f] for f in range(12)):
            matches.append(rot)
    if len(matches) != 1:
        raise RuntimeError(f"expected 1 rotation, got {len(matches)}")
    rot_pos = rotation_to_position(matches[0])
    # Apply rotation to the position: compose(rot, pos)? 
    # Reorienting the puzzle: new_pos = rot * pos * rot^{-1} (conjugation)
    # keeps the "relative scramble" but changes which colours are where.
    # For Rule B as "reorient so corner looks solved-like", we conjugate:
    return compose(compose(rot_pos, pos), inverse(rot_pos))


# ---------------------------------------------------------------------------
# Self-test helpers
# ---------------------------------------------------------------------------

def _parity(n_cycles_missing, n):
    return (n - n_cycles_missing) & 1


if __name__ == "__main__":
    verify_geometry()
    print("geometry OK")
    print("corners", len(CORNERS), "edges", len(EDGES))
    print("GROUP_ORDER", GROUP_ORDER)
    print("log2", math.log2(GROUP_ORDER))
    print("bytes", math.ceil(math.log2(GROUP_ORDER) / 8))

    # Each generator order 5
    for f in range(12):
        p = Position.identity()
        for k in range(5):
            p = face_turn(p, f, 1)
            if k < 4:
                assert not p.is_identity(), (f, k)
        assert p.is_identity(), f
    print("all face turns order 5 OK")

    # Validity preserved
    p = Position.identity()
    import random
    rng = random.Random(0)
    for _ in range(200):
        f, a = rng.choice(MOVES_48)
        p = face_turn(p, f, a)
        assert p.is_valid(), p
    print("random walk stays valid OK")

    # Opposite faces commute
    for f in range(6):
        g = OPPOSITES[f]
        # only check f < g to do each pair once — opposites are 6 pairs
    pairs = []
    for f in range(12):
        g = OPPOSITES[f]
        if f < g:
            pairs.append((f, g))
    for f, g in pairs:
        a = face_turn(face_turn(Position.identity(), f, 1), g, 1)
        b = face_turn(face_turn(Position.identity(), g, 1), f, 1)
        assert a == b, (f, g)
    print("opposite faces commute OK", pairs)

    # Composition associativity / inverse
    rng = random.Random(1)
    def rand_pos():
        q = Position.identity()
        for _ in range(30):
            q = face_turn(q, *rng.choice(MOVES_48))
        return q
    for _ in range(20):
        a, b, c = rand_pos(), rand_pos(), rand_pos()
        assert compose(compose(a, b), c) == compose(a, compose(b, c))
        assert compose(a, inverse(a)).is_identity()
        assert compose(inverse(a), a).is_identity()
        assert compose(a, Position.identity()) == a
        assert compose(Position.identity(), a) == a
    print("group law OK")

    # Rank/unrank
    for _ in range(10):
        q = rand_pos()
        r = rank_position(q)
        assert 0 <= r < GROUP_ORDER
        assert unrank_position(r) == q
        b = position_to_bytes(q)
        assert len(b) == 29
        assert position_from_bytes(b) == q
    print("rank/unrank OK")

    rots = enumerate_face_rotations()
    print("rotations found", len(rots))
    assert len(rots) == 60
