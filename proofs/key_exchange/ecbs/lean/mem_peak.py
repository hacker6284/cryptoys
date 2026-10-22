#!/usr/bin/env python3
"""Cache-free `lake build EcbsLink2` with a per-module VmHWM table.

Deletes this package's EcbsLink2 oleans first (no Mathlib cache and no restored
olean cache for those modules), then builds under `ulimit -v 7000000`. Each
`lean` process is wrapped so its peak resident set (Linux `ru_maxrss`, the
VmHWM in kB) is recorded. The run fails if any module exceeds 2097152 kB.

Not part of push CI or ordinary pull requests. The workflow
`.github/workflows/ecbs-link2-mem.yml` runs this script.
"""
import fcntl
import os
import shutil
import subprocess
import sys
from pathlib import Path

LIMIT_KB = 2_097_152
VIRT_KB = 7_000_000
PKG = Path(__file__).resolve().parent


def toolchain_lean() -> Path:
    # elan walks up from its cwd for lean-toolchain. The file is in this
    # package; the checkout root has none, and lean-action sets no default.
    lean = subprocess.check_output(
        ["elan", "which", "lean"], cwd=PKG, text=True
    ).strip()
    path = Path(lean)
    if not path.is_file():
        sys.exit(f"mem_peak: elan which lean returned {lean}, which is not a file")
    return path


def install_wrapper(lean: Path, log: Path) -> None:
    real = Path(str(lean) + ".real")
    if real.exists():
        sys.exit(f"mem_peak: {real} already exists; refusing to wrap twice")
    lean.rename(real)
    # The wrapper is the lean binary lake execs. It measures that one process.
    lean.write_text(
        "#!/usr/bin/env python3\n"
        "import fcntl, os, sys\n"
        f"real = {str(real)!r}\n"
        "args = sys.argv[1:]\n"
        "lean_file = next((a for a in args if a.endswith('.lean')), '')\n"
        "pid = os.fork()\n"
        "if pid == 0:\n"
        "    os.execv(real, [real, *args])\n"
        "_, status, ru = os.wait4(pid, 0)\n"
        "code = os.waitstatus_to_exitcode(status)\n"
        f"log = {str(log)!r}\n"
        "if lean_file:\n"
        "    with open(log, 'a') as fh:\n"
        "        fcntl.flock(fh, fcntl.LOCK_EX)\n"
        "        fh.write(f'{ru.ru_maxrss}\\t{lean_file}\\n')\n"
        "sys.exit(code)\n"
    )
    lean.chmod(0o755)


def restore_lean(lean: Path) -> None:
    real = Path(str(lean) + ".real")
    if real.is_file():
        if lean.exists() or lean.is_symlink():
            lean.unlink()
        real.rename(lean)


def drop_ecbs_oleans() -> None:
    """Drop this package's EcbsLink2 build products so the build is cache-free
    for those modules. Dependency packages (Generated, audit) keep their own
    directories; a fresh CI checkout has neither."""
    build = PKG / ".lake" / "build"
    if not build.exists():
        return
    for path in build.rglob("*"):
        if "EcbsLink2" not in path.name and "EcbsLink2" not in str(path.relative_to(build)):
            continue
        if path.is_file() or path.is_symlink():
            path.unlink()
    # Remove emptied EcbsLink2 directories bottom-up.
    for path in sorted(build.rglob("*"), key=lambda p: len(p.parts), reverse=True):
        if path.is_dir() and "EcbsLink2" in path.name:
            shutil.rmtree(path, ignore_errors=True)


def read_peaks(log: Path) -> dict:
    peaks = {}
    if not log.exists():
        return peaks
    for line in log.read_text().splitlines():
        if not line.strip():
            continue
        kb, path = line.split("\t", 1)
        name = path
        for marker in ("EcbsLink2/", "proofs/key_exchange/ecbs/lean/"):
            at = path.find(marker)
            if at >= 0:
                name = path[at:]
                break
        else:
            name = Path(path).name
        peaks[name] = max(peaks.get(name, 0), int(kb))
    return peaks


def main() -> int:
    log = Path(os.environ.get("ECBS_MEM_LOG", f"/tmp/ecbs-mem-{os.getpid()}.log"))
    log.write_text("")
    lean = toolchain_lean()
    drop_ecbs_oleans()
    install_wrapper(lean, log)
    try:
        def limit():
            bytes_ = VIRT_KB * 1024
            import resource
            resource.setrlimit(resource.RLIMIT_AS, (bytes_, bytes_))

        proc = subprocess.run(
            ["lake", "--no-cache", "build", "EcbsLink2"],
            cwd=PKG,
            env={**os.environ, "ECBS_MEM_LOG": str(log)},
            preexec_fn=limit,
        )
    finally:
        restore_lean(lean)
    peaks = read_peaks(log)
    print(f"{'module':<56} {'VmHWM_kB':>10}  cap")
    over = []
    for name, kb in sorted(peaks.items(), key=lambda kv: -kv[1]):
        flag = "OVER" if kb > LIMIT_KB else "ok"
        if kb > LIMIT_KB:
            over.append(name)
        print(f"{name:<56} {kb:10d}  {flag}")
    if not peaks:
        print("mem_peak: no per-module VmHWM records; the lean wrapper did not run",
              file=sys.stderr)
        return 1
    if proc.returncode != 0:
        print(f"mem_peak: lake build EcbsLink2 failed ({proc.returncode})", file=sys.stderr)
        return proc.returncode
    if over:
        print(f"mem_peak: {len(over)} module(s) exceeded {LIMIT_KB} kB", file=sys.stderr)
        return 1
    print(f"mem_peak: {len(peaks)} modules, all at most {LIMIT_KB} kB, "
          f"virtual limit {VIRT_KB} kB")
    return 0


if __name__ == "__main__":
    sys.exit(main())
