#!/usr/bin/env python3
"""Front-end self-check for MegaDreifach (pad / φ / domain / IV). No E_m."""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from front import (  # noqa: E402
    DIGEST_LEN,
    GROUP_ORDER,
    PAD_BLOCK,
    compose,
    digest_encode,
    id_to_card,
    inverse,
    iv_cook12,
    iv_cook12_inverse,
    pad_message,
    phi_chunk,
    phi_inv_deal,
    require_permutation,
    unpad_bytes,
)
from megaminx import Position  # noqa: E402

def _find_kat() -> Path:
    for parent in [ROOT, *ROOT.parents]:
        cand = parent / "proofs" / "megadreifach" / "vectors" / "megaminx_hash_kats.json"
        if cand.is_file():
            return cand
    raise FileNotFoundError("megaminx_hash_kats.json not found above " + str(ROOT))


KAT = _find_kat()


def main() -> None:
    for n in (0, 1, 19, 20, 27, 28, 29, 55, 56, 100):
        m = bytes((i * 3) & 0xFF for i in range(n))
        p = pad_message(m)
        assert len(p) % PAD_BLOCK == 0 and len(p) > 0
        assert unpad_bytes(p) == m

    iv = iv_cook12()
    assert iv.is_valid()
    assert compose(iv, iv_cook12_inverse()).is_identity()
    assert compose(iv_cook12_inverse(), iv).is_identity()
    assert inverse(iv) == iv_cook12_inverse()
    d_iv = digest_encode(iv)
    assert len(d_iv) == DIGEST_LEN

    for raw in (b"\x00" * 28, b"\xff" * 28, bytes(range(28))):
        deal = phi_chunk(raw)
        assert len(deal) == 52 and len(set(deal)) == 52
        assert phi_inv_deal(deal) == raw
        require_permutation(deal)

    try:
        require_permutation([(0, 0)] * 52)
    except ValueError:
        pass
    else:
        raise AssertionError("duplicate deal must be rejected")

    data = json.loads(KAT.read_text())
    assert data["spec"] == "MegaDreifach"
    assert data["digest_len"] == DIGEST_LEN
    assert data["pad_block"] == PAD_BLOCK
    assert int(data["group_order_hex"], 16) == GROUP_ORDER
    assert data["iv_cook12_digest_hex"] == d_iv.hex()
    for v in data["vectors"]:
        msg = bytes.fromhex(v["msg_hex"])
        p = pad_message(msg)
        assert len(p) == v["padded_len"]
        assert len(p) // PAD_BLOCK == v["n_blocks"]
        assert len(v["digest_hex"]) == 58
    hd = data["hash_deck"]
    deal0 = [id_to_card(i) for i in hd["deal_ids"]]
    assert phi_inv_deal(deal0) == bytes.fromhex(hd["phi_inv_hex"])
    assert Position.identity().is_valid()
    print("MegaDreifach front-end selfcheck OK")
    print(f"  |G| = {GROUP_ORDER}")
    print(f"  IV-COOK12 digest: {d_iv.hex()}")
    print(f"  KAT metadata: {len(data['vectors'])} vectors @ {KAT}")


if __name__ == "__main__":
    main()
