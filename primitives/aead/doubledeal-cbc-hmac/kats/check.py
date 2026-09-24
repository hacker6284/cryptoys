#!/usr/bin/env python3
"""Structural KAT checks for DoubleDeal-CBC-HMAC. Does not reimplement Hash."""

from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
KATS = json.loads((HERE / "doubledeal_cbc_hmac_kats.json").read_text())


def unhex(value: str) -> bytes:
    raw = value[2:] if value.startswith("0x") else value
    return bytes.fromhex(raw)


def main() -> None:
    assert KATS["product"] == "DoubleDeal-CBC-HMAC"
    assert KATS["version"] == "v1"
    assert len(unhex(KATS["iv"])) == 28
    assert len(unhex(KATS["master"])) > 0
    by_name = {row["name"]: row for row in KATS["vectors"]}
    abc = unhex(by_name["abc"]["blob"])
    abc_aad = unhex(by_name["abc_aad"]["blob"])
    assert abc[:-29] == abc_aad[:-29]
    assert abc[-29:] != abc_aad[-29:]
    for row in KATS["vectors"]:
        blob = unhex(row["blob"])
        assert len(blob) >= 58
        assert (len(blob) - 29) % 29 == 0
    print("doubledeal-cbc-hmac kat structure ok")


if __name__ == "__main__":
    main()
