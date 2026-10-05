#!/usr/bin/env python3
"""Structural KAT checks for DoubleDeal-CBC-Sandwich v2. Does not reimplement anything."""

from __future__ import annotations

import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
KATS = json.loads((HERE / "doubledeal_cbc_hmac_kats.json").read_text())


def unhex(value: str) -> bytes:
    raw = value[2:] if value.startswith("0x") else value
    return bytes.fromhex(raw)


def is_deck(d) -> bool:
    return sorted(d) == list(range(52))


def main() -> None:
    assert KATS["product"] == "DoubleDeal-CBC-Sandwich"
    assert KATS["version"] == "v2"
    assert len(unhex(KATS["master"])) > 0
    for name in ("k_enc", "k_mac", "iv"):
        assert is_deck(KATS[name]), name
    assert KATS["k_enc"] != KATS["k_mac"]
    assert len(unhex(KATS["mac_version_only"])) == 29
    by_name = {row["name"]: row for row in KATS["vectors"]}
    abc = unhex(by_name["abc"]["blob"])
    abc_aad = unhex(by_name["abc_aad"]["blob"])
    assert abc[:-29] == abc_aad[:-29]
    assert abc[-29:] != abc_aad[-29:]
    for row in KATS["vectors"]:
        blob = unhex(row["blob"])
        assert len(blob) >= 87 and len(blob) % 29 == 0
        for i in range(0, len(blob) - 29, 29):
            assert int.from_bytes(blob[i:i + 29], "big") < math.factorial(52)
    print("doubledeal-cbc-sandwich v2 kat structure ok")


if __name__ == "__main__":
    main()
