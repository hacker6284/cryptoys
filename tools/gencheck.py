"""One write-or-check convention for the repo's generators.

    from gencheck import parser, emit
    args = parser(__doc__).parse_args()        # --check; unknown flags are an error
    sys.exit(emit(path, text, args.check))     # 0 = written or OK, 1 = STALE

Write mode writes `path` and prints "wrote <path>". Check mode never writes: it
prints "OK <path>" if the committed file equals `text`, else "STALE <path>" with
the command that regenerates it (on stderr) and returns 1.
"""
from __future__ import annotations

import argparse
import shlex
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent


def _rel(p: Path) -> str:
    p = Path(p).resolve()
    try:
        return str(p.relative_to(REPO))
    except ValueError:
        return str(p)


def parser(description: str | None = None) -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=description,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true",
                    help="do not write; fail (exit 1) if the committed file differs")
    return ap


def emit(path, text: str, check: bool, fix: str | None = None) -> int:
    """Write `text` to `path`, or with check=True compare it. Returns an exit code."""
    path = Path(path)
    if check:
        have = path.read_text() if path.exists() else None
        if have == text:
            print(f"OK {_rel(path)}")
            return 0
        fix = fix or "python3 " + shlex.quote(_rel(Path(sys.argv[0])))
        why = "missing" if have is None else "differs from a fresh run"
        print(f"STALE {_rel(path)} {why} (fix: {fix})", file=sys.stderr)
        return 1
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    print(f"wrote {_rel(path)}")
    return 0
