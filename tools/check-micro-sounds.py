#!/usr/bin/env python3
"""Headless check: every library and microdemo sound file decodes, in both formats.

Reads demos/anim/sounds/index.json and demos/micro/sounds/index.json and decodes each <file>.ogg and
<file>.mp3 with ffmpeg (`-f null`), failing on any decode error or an
empty result. Run after tools/sync-micro-sounds.py:

    python3 tools/check-micro-sounds.py
"""
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOUNDS = [ROOT / "demos" / "anim" / "sounds", ROOT / "demos" / "micro" / "sounds"]


def decode(path):
    """Return (ok, detail). ok needs a clean decode with >0 samples."""
    if not path.exists():
        return False, "missing"
    proc = subprocess.run(
        ["ffmpeg", "-nostdin", "-v", "error", "-xerror", "-i", str(path), "-f", "null", "-"],
        capture_output=True, text=True,
    )
    if proc.returncode != 0 or proc.stderr.strip():
        return False, (proc.stderr.strip().splitlines() or ["exit %d" % proc.returncode])[-1]
    probe = subprocess.run(
        ["ffprobe", "-v", "error", "-show_entries", "format=duration", "-of", "csv=p=0", str(path)],
        capture_output=True, text=True,
    )
    try:
        duration = float(probe.stdout.strip())
    except ValueError:
        return False, "no duration"
    return duration > 0, "%.3f s" % duration


def main():
    total = 0
    bad = []
    for sounds in SOUNDS:
        index = json.loads((sounds / "index.json").read_text())
        for file in sorted(index["files"]):
            for ext in ("ogg", "mp3"):
                total += 1
                ok, detail = decode(sounds / f"{file}.{ext}")
                if not ok:
                    bad.append(f"{sounds.relative_to(ROOT)}/{file}.{ext}: {detail}")
    print(f"{total - len(bad)}/{total} sound files decode")
    for line in bad:
        print("  FAIL", line)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
