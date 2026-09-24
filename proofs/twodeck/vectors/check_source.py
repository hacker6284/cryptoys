#!/usr/bin/env python3
"""Fail if twodeck_vectors.json is stale relative to twodeck.sudo.

Does not re-run sudoc. CI uses this so editing the sudo without regen is red.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
SUDO = ROOT / "primitives" / "cipher" / "twodeck" / "twodeck.sudo"
JSON_PATH = ROOT / "proofs" / "twodeck" / "vectors" / "twodeck_vectors.json"


def main() -> int:
    h = hashlib.sha256(SUDO.read_bytes()).hexdigest()
    doc = json.loads(JSON_PATH.read_text())
    got = doc.get("sudo_sha256")
    commit = doc.get("sudocode_commit")
    if got != h:
        print(
            f"sudo_sha256 mismatch: json={got} file={h}\n"
            "regenerate: proofs/twodeck/vectors/regen.sh",
            file=sys.stderr,
        )
        return 1
    if not isinstance(commit, str) or len(commit) < 7:
        print("json missing sudocode_commit", file=sys.stderr)
        return 1
    print(f"ok sudo_sha256={h} sudocode_commit={commit}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
