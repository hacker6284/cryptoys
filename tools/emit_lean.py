#!/usr/bin/env python3
"""Emit cryptoys .sudo through the sudocode protocol-4 Lean backend.

Reproduces the spike path that was green on DoubleDeal / MegaDreifach:

    sudoc emit-ir -I stdlib FILE
      → wrap {protocol:4, cmd:emit, entry, with_tests, modules}
      → python3 backends/lean/emit.py
      → unpack files/

Full-peer emit (no --require terminates). Cryptoys publics have unmeasured
whiles; the totality gate RefusedExport-s them. See proofs/ANTI_DRIFT.md.

This is not a claim of sudo↔Lean semantic equivalence.
"""
from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path


def run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    print("+", " ".join(cmd), flush=True)
    return subprocess.run(cmd, **kw)


def emit_one(
    sudoc: Path,
    emit_py: Path,
    stdlib: Path,
    sudo_file: Path,
    dest: Path,
    with_tests: bool,
) -> int:
    dest.mkdir(parents=True, exist_ok=True)
    stem = sudo_file.stem
    ir_path = dest / "modules.json"
    req_path = dest / "request.json"
    resp_path = dest / "response.json"
    files_dir = dest / "files"
    if files_dir.exists():
        shutil.rmtree(files_dir)
    files_dir.mkdir()

    cmd = [str(sudoc), "emit-ir", "-I", str(stdlib), "-o", str(ir_path), str(sudo_file)]
    r = run(cmd)
    if r.returncode != 0:
        print(f"emit-ir failed rc={r.returncode}", file=sys.stderr)
        return r.returncode

    modules_text = ir_path.read_text()
    header = json.dumps(
        {
            "protocol": 4,
            "cmd": "emit",
            "entry": stem,
            "with_tests": with_tests,
        },
        separators=(",", ":"),
    )
    envelope = header[:-1] + ',"modules":' + modules_text + "}"
    req_path.write_text(envelope)
    json.loads(envelope)

    r = run(
        [sys.executable, str(emit_py)],
        cwd=str(emit_py.parent),
        input=envelope.encode(),
        stdout=open(resp_path, "wb"),
    )
    if r.returncode != 0:
        print(f"emit.py failed rc={r.returncode}", file=sys.stderr)
        return r.returncode

    resp = json.loads(resp_path.read_text())
    if "error" in resp:
        print("EMITTER ERROR:", resp["error"], file=sys.stderr)
        (dest / "EMIT_ERROR.txt").write_text(resp["error"] + "\n")
        return 2
    if "files" not in resp:
        print("malformed emit response keys:", list(resp), file=sys.stderr)
        return 2

    banner = (
        "-- DO NOT EDIT. Generated from "
        f"{sudo_file.name} by tools/emit_lean.py.\n"
        "-- Algorithm source of truth is the .sudo file. Regenerate with\n"
        "--   proofs/emit_lean.sh\n"
        "-- This is not a sudo↔Lean semantic-equivalence theorem.\n"
    )
    manifest = []
    for item in resp["files"]:
        rel = item["path"]
        dest_file = files_dir / rel
        dest_file.parent.mkdir(parents=True, exist_ok=True)
        contents = item["contents"]
        if rel.endswith(".lean") and not contents.startswith("-- DO NOT EDIT"):
            contents = banner + contents
        dest_file.write_text(contents)
        manifest.append({"path": rel, "bytes": len(contents)})
        print(f"  wrote {dest_file} ({len(contents)} bytes)")
    (dest / "files_manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"OK {stem} → {files_dir} ({len(manifest)} files)")
    return 0


def install_into(files_dir: Path, generated: Path) -> None:
    """Replace generated/ with the unpacked emit files (keep README if present)."""
    generated.mkdir(parents=True, exist_ok=True)
    keep = {"README.md", ".gitignore", "lake-manifest.json"}
    for child in generated.iterdir():
        if child.name in keep:
            continue
        if child.is_dir():
            shutil.rmtree(child)
        else:
            child.unlink()
    for src in files_dir.iterdir():
        dest = generated / src.name
        if src.is_dir():
            shutil.copytree(src, dest)
        else:
            shutil.copy2(src, dest)
    write_lake_manifest(generated)


def write_lake_manifest(generated: Path) -> None:
    """Lake 5 / lean-action require a committed lake-manifest.json (no deps)."""
    path = generated / "lake-manifest.json"
    path.write_text(
        '{\n'
        ' "version": "1.1.0",\n'
        ' "packagesDir": ".lake/packages",\n'
        ' "packages": [],\n'
        ' "name": "sudo",\n'
        ' "lakeDir": ".lake"}\n'
    )


# Committed sidecar files that emit.py does not produce.
IGNORE_NAMES = {
    "README.md",
    ".gitignore",
    "EMITTED_FROM.json",
    "lake-manifest.json",
}


def same_tree(committed: Path, emitted: Path) -> list[str]:
    """Return human-readable diffs if file sets or contents differ."""
    def collect(root: Path) -> dict[str, Path]:
        out = {}
        for p in sorted(root.rglob("*")):
            if not p.is_file():
                continue
            rel = p.relative_to(root).as_posix()
            if p.name in IGNORE_NAMES or rel in IGNORE_NAMES:
                continue
            if ".lake" in p.parts:
                continue
            out[rel] = p
        return out

    left = collect(committed)
    right = collect(emitted)
    diffs = []
    for k in sorted(set(left) | set(right)):
        if k not in left:
            diffs.append(f"emit produced a file not in Generated/: {k}")
        elif k not in right:
            diffs.append(f"Generated/ has a file emit did not produce: {k}")
        elif left[k].read_bytes() != right[k].read_bytes():
            diffs.append(f"content differs: {k}")
    return diffs


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("sudo_file", help="path to a .sudo file")
    ap.add_argument(
        "--out",
        required=True,
        help="scratch directory (modules.json, request.json, files/)",
    )
    ap.add_argument(
        "--install",
        help="copy unpacked files into this Generated/ directory",
    )
    ap.add_argument(
        "--check",
        help="compare emit output to this Generated/ directory (no write)",
    )
    ap.add_argument("--no-tests", action="store_true", help="set with_tests=false")
    ap.add_argument(
        "--sudoc",
        default="",
        help="path to sudoc binary (or set SUDOC)",
    )
    ap.add_argument(
        "--sudocode-dir",
        default="",
        help="sudocode checkout containing backends/lean and stdlib (or SUDOCODE_DIR)",
    )
    args = ap.parse_args()

    import os

    sudocode_dir = Path(
        args.sudocode_dir or os.environ.get("SUDOCODE_DIR", "/tmp/sudocode")
    ).resolve()
    sudoc = Path(args.sudoc or os.environ.get("SUDOC", sudocode_dir / "sudoc/target/release/sudoc"))
    emit_py = sudocode_dir / "backends" / "lean" / "emit.py"
    stdlib = sudocode_dir / "stdlib"

    if not sudoc.is_file():
        print(f"sudoc not found: {sudoc}", file=sys.stderr)
        return 1
    if not emit_py.is_file():
        print(
            f"Lean emitter not found at {emit_py}.\n"
            "Main sudocode does not ship backends/lean/. Pin the Lean backend "
            "branch (see proofs/ANTI_DRIFT.md).",
            file=sys.stderr,
        )
        return 1
    if not stdlib.is_dir():
        print(f"stdlib not found: {stdlib}", file=sys.stderr)
        return 1

    src = Path(args.sudo_file).resolve()
    out = Path(args.out).resolve()
    rc = emit_one(sudoc, emit_py, stdlib, src, out, with_tests=not args.no_tests)
    if rc != 0:
        return rc

    files_dir = out / "files"
    if args.check:
        got = same_tree(Path(args.check).resolve(), files_dir)
        if got:
            print("Generated Lean is stale vs emit from current .sudo:", file=sys.stderr)
            for line in got:
                print(f"  {line}", file=sys.stderr)
            print("Re-run: proofs/emit_lean.sh", file=sys.stderr)
            return 1
        print(f"OK {src.name} matches {args.check}")
    if args.install:
        install_into(files_dir, Path(args.install).resolve())
        print(f"installed → {args.install}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
