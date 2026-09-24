"""
MegaDreifach front end: pad, φ, HashDeckBody domain, IV-COOK12, digest rank.

This is the landable reference without the abs-G2 runner (`em_spike_r4`).
`hash_bytes` / `E_m` are follow-up — see SPEC.md.

Product name: MegaDreifach. Puzzle/group library: megaminx.
"""
from __future__ import annotations

import math
from typing import List, Sequence, Tuple

from megaminx import (  # noqa: E402
    GROUP_ORDER,
    Position,
    compose,
    face_turn,
    inverse,
    position_to_bytes,
)

Card = Tuple[int, int]

PAD_BLOCK = 28
BODY_LEN = 52
LEN_FIELD = 8
DIGEST_LEN = 29
FACT_52 = math.factorial(52)
PHI_MAX = 1 << 224


def id_to_card(cid: int) -> Card:
    if not 0 <= cid < 52:
        raise ValueError(f"card id {cid} out of 0..51")
    return (cid // 4, cid % 4)


def card_to_id(card: Card) -> int:
    rank, suit = card
    if not (0 <= rank <= 12 and 0 <= suit <= 3):
        raise ValueError(f"bad card {card}")
    return rank * 4 + suit


def pad_bytes(msg: bytes, block: int = PAD_BLOCK, len_field: int = LEN_FIELD) -> bytes:
    """SHA-2-style pad: M || 0x80 || 0x00*z || bitlen as 8-byte BE."""
    if block <= 0:
        raise ValueError("block must be positive")
    bitlen = 8 * len(msg)
    z = (block - (len(msg) + 1 + len_field) % block) % block
    return bytes(msg) + b"\x80" + (b"\x00" * z) + bitlen.to_bytes(len_field, "big")


def unpad_bytes(padded: bytes, block: int = PAD_BLOCK, len_field: int = LEN_FIELD) -> bytes:
    if len(padded) == 0 or len(padded) % block != 0 or len(padded) < 1 + len_field:
        raise ValueError("padded length is not a positive multiple of the block")
    bitlen = int.from_bytes(padded[-len_field:], "big")
    if bitlen % 8 != 0:
        raise ValueError("bit length is not a multiple of 8")
    n = bitlen // 8
    if len(padded) < n + 1 + len_field:
        raise ValueError("padded buffer shorter than recovered message")
    if padded[n] != 0x80:
        raise ValueError("missing 0x80 marker")
    fill = padded[n + 1 : len(padded) - len_field]
    if any(b != 0 for b in fill):
        raise ValueError("nonzero pad filler")
    z = (block - (n + 1 + len_field) % block) % block
    if len(fill) != z:
        raise ValueError("pad filler length mismatch")
    return padded[:n]


def pad_message(msg: bytes) -> bytes:
    return pad_bytes(msg, PAD_BLOCK, LEN_FIELD)


def chunks28(padded: bytes) -> List[bytes]:
    if len(padded) == 0 or len(padded) % PAD_BLOCK != 0:
        raise ValueError("padded length must be a positive multiple of 28")
    return [padded[i : i + PAD_BLOCK] for i in range(0, len(padded), PAD_BLOCK)]


def unrank_perm(items: List[int], rank: int) -> List[int]:
    """Lehmer / factoradic unrank of `rank` against `items`."""
    avail = list(items)
    n = len(avail)
    out: List[int] = []
    for i in range(n):
        f = math.factorial(n - 1 - i)
        idx = rank // f
        rank = rank % f
        if idx >= len(avail):
            raise ValueError("rank out of range for remaining items")
        out.append(avail.pop(idx))
    return out


def lehmer_rank(ids: Sequence[int]) -> int:
    avail = list(range(len(ids)))
    rank = 0
    for i, v in enumerate(ids):
        idx = avail.index(v)
        rank = rank * (len(ids) - i) + idx
        avail.pop(idx)
    return rank


def phi_chunk(chunk28: bytes) -> List[Card]:
    if len(chunk28) != PAD_BLOCK:
        raise ValueError("φ expects 28 bytes")
    n = int.from_bytes(chunk28, "big")
    if n >= FACT_52:
        raise ValueError("chunk integer ≥ 52!")
    perm = unrank_perm(list(range(52)), n)
    return [id_to_card(x) for x in perm]


def phi_inv_deal(deal: Sequence[Card]) -> bytes:
    if len(deal) != BODY_LEN:
        raise ValueError("deal must be 52 cards")
    ids = []
    seen = set()
    for card in deal:
        cid = card_to_id(card)
        if cid in seen:
            raise ValueError("deal is not a permutation (duplicate card)")
        seen.add(cid)
        ids.append(cid)
    if seen != set(range(52)):
        raise ValueError("deal is not a full 52-card permutation")
    rank = lehmer_rank(ids)
    if rank >= PHI_MAX:
        raise ValueError("deal rank ≥ 2^224; not in image of φ")
    return rank.to_bytes(PAD_BLOCK, "big")


def require_permutation(deal: Sequence[Card]) -> List[Card]:
    """HashDeckBody domain: a full 52-card permutation."""
    if len(deal) != BODY_LEN:
        raise ValueError("deal must be 52 cards")
    cards: List[Card] = []
    seen = set()
    for rank, suit in deal:
        if not (0 <= int(rank) <= 12 and 0 <= int(suit) <= 3):
            raise ValueError(f"bad card {(rank, suit)}")
        cid = int(rank) * 4 + int(suit)
        if cid in seen:
            raise ValueError("deal is not a permutation (duplicate card)")
        seen.add(cid)
        cards.append((int(rank), int(suit)))
    if seen != set(range(52)):
        raise ValueError("deal is not a full 52-card permutation")
    return cards


def iv_cook12() -> Position:
    """IV-COOK12 (LOCKED): from solved, faces 0..11 each +1 CW."""
    g = Position.identity()
    for face in range(12):
        g = face_turn(g, face, 1)
    return g


def iv_cook12_inverse() -> Position:
    """Hand inverse for puzzle B: faces 11..0 each −1 (≡ +4 mod 5)."""
    g = Position.identity()
    for face in range(11, -1, -1):
        g = face_turn(g, face, 4)
    return g


def digest_encode(g: Position) -> bytes:
    return position_to_bytes(g)


__all__ = [
    "PAD_BLOCK",
    "BODY_LEN",
    "DIGEST_LEN",
    "GROUP_ORDER",
    "PHI_MAX",
    "pad_message",
    "pad_bytes",
    "unpad_bytes",
    "chunks28",
    "phi_chunk",
    "phi_inv_deal",
    "require_permutation",
    "iv_cook12",
    "iv_cook12_inverse",
    "digest_encode",
    "id_to_card",
    "card_to_id",
    "compose",
    "inverse",
]
