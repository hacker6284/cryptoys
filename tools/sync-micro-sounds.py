#!/usr/bin/env python3
"""Copy Scrounger's microdemo sound candidates into demos/micro/sounds/.

    python3 tools/sync-micro-sounds.py [--scrounger /workspace/scrounger]

Re-run whenever Scrounger adds candidates. Sources, in order:

1. /workspace/scrounger/micro/<primitive>/candidates.json (Scrounger's
   per-primitive picks: file, group, peak_ms, loudness, licence, source).
2. FALLBACK below: primitives Scrounger has not cut yet, taken from the
   megadreifach / demos-sfx / bs-ecbs scrounges. Peak and loudness are
   measured here with ffmpeg (loudest sample; ebur128 momentary max).
   A Scrounger folder of the same name replaces its fallback.

Only CC0 is copied. Anything else is listed under "Rejected" in
demos/micro/sounds/LICENSE.md and printed, and never reaches the pages.

Writes demos/micro/sounds/<primitive>/<file>.{ogg,mp3}, index.json
(what the pages read) and LICENSE.md. Needs ffmpeg for the fallbacks
and for any missing .mp3/.ogg twin.
"""
import argparse
import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "demos" / "micro" / "sounds"

MD = "megadreifach/sounds"
SFX = "demos-sfx/sounds"
BS = "bs-ecbs"

# primitive -> list of (group or None, scrounge-relative path without extension)
FALLBACK = {
    "scramble-lift": [
        ("lift", f"{MD}/regrip/regrip-1_01kamii05-428594"),
        ("lift", f"{MD}/regrip/regrip-2_bwarpus99-452535-slice"),
    ],
    "playroom-fly": [
        ("lift", f"{SFX}/box-lift/lift-1_kenney-card-slide-3"),
        ("lift", f"{SFX}/box-lift/lift-2_kenney-rpg-bookflip1"),
    ],
    "peg": [
        ("push", f"{BS}/sounds/peg_in/peg_in_lego_click_670000"),
        ("push", f"{BS}/sounds/peg_in/peg_in_lego_press_203939"),
        ("push", f"{BS}/sounds/peg_in/peg_in_floss_click_167829_a"),
        ("push", f"{BS}/sounds/peg_in/peg_in_floss_click_167829_b"),
        ("push", f"{BS}/sounds/peg_in/peg_in_toy_click_441349"),
        ("pull", f"{BS}/sounds/peg_out/peg_out_pill_pop_536417"),
        ("pull", f"{BS}/sounds/peg_out/peg_out_punch_pulled_431447"),
        ("pull", f"{BS}/sounds/peg_out/peg_out_slide_686165"),
    ],
    "dice-cup": [
        ("shake", f"{BS}/yahtzee/sounds/cup_shake/cup_shake_6dice_185985_a"),
        ("shake", f"{BS}/yahtzee/sounds/cup_shake/cup_shake_6dice_185985_b"),
        ("shake", f"{BS}/yahtzee/sounds/cup_shake/cup_shake_466141"),
        ("shake", f"{BS}/yahtzee/sounds/cup_shake/cup_shake_kenney_2"),
        ("shake", f"{BS}/yahtzee/sounds/cup_shake/cup_shake_plastic_529816"),
        ("land", f"{BS}/yahtzee/sounds/cup_pour_felt/cup_pour_6dice_felt_185982_a"),
        ("land", f"{BS}/yahtzee/sounds/cup_pour_felt/cup_pour_6dice_felt_185982_b"),
        ("land", f"{BS}/yahtzee/sounds/cup_pour_felt/cup_pour_6dice_felt_185982_c"),
        ("land", f"{BS}/yahtzee/sounds/cup_pour_felt/cup_slam_3dice_felt_185977_a"),
        ("land", f"{BS}/polyhedral/sounds/d20_roll/d20_cup_felt_854519"),
    ],
}

CC0 = re.compile(r"\bCC0\b|Creative Commons 0|Creative Commons Zero|publicdomain/zero", re.I)
LINK = re.compile(r"\[([^\]]*)\]\((https?://[^)]+)\)")


def run(cmd):
    return subprocess.run(cmd, check=True, capture_output=True, text=True)


def measure(path):
    """(peak_ms, momentary-max LUFS, duration_s) of an audio file."""
    import array
    raw = subprocess.run(
        ["ffmpeg", "-v", "error", "-i", str(path), "-ac", "1", "-ar", "48000", "-f", "f32le", "-"],
        check=True, capture_output=True,
    ).stdout
    samples = array.array("f")
    samples.frombytes(raw[: len(raw) // 4 * 4])
    peak_i = max(range(len(samples)), key=lambda i: abs(samples[i])) if samples else 0
    err = subprocess.run(
        ["ffmpeg", "-nostats", "-i", str(path), "-af", "apad=pad_dur=0.5,ebur128", "-f", "null", "-"],
        capture_output=True, text=True,
    ).stderr
    moments = [float(m) for m in re.findall(r"\bM:\s*(-?[\d.]+)", err) if float(m) > -120]
    return round(peak_i / 48.0), (max(moments) if moments else None), round(len(samples) / 48000, 3)


def manifest_row(scrounge_root, rel):
    """Author / licence / source for a fallback file, from its scrounge MANIFEST row."""
    parts = Path(rel).parts
    base = Path(rel).name
    for n in range(len(parts) - 1, 0, -1):
        man = scrounge_root / Path(*parts[:n]) / "MANIFEST.md"
        if not man.exists():
            continue
        for line in man.read_text(encoding="utf8").splitlines():
            if base in line and line.lstrip().startswith("|"):
                cells = [c.strip() for c in line.strip().strip("|").split("|")]
                lic = next((c for c in cells if re.search(r"Creative Commons|CC0|CC-BY|licen", c, re.I)), "")
                link = LINK.search(line)
                author = ""
                if link:
                    idx = next((i for i, c in enumerate(cells) if link.group(2) in c), -1)
                    if 0 <= idx < len(cells) - 1:
                        author = cells[idx + 1]
                return {"license": lic, "source_url": link.group(2) if link else "", "source_title": link.group(1) if link else "", "author": author}
        # also accept a bs-ecbs style manifest that names the file in any line
    return {"license": "", "source_url": "", "source_title": "", "author": ""}


def twin(src_dir, rel_noext, dest_noext):
    """Copy .ogg and .mp3 (encoding the missing twin with ffmpeg)."""
    have = {}
    for ext in ("ogg", "mp3"):
        p = src_dir / f"{rel_noext}.{ext}"
        if p.exists():
            have[ext] = p
    if not have:
        return False
    dest_noext.parent.mkdir(parents=True, exist_ok=True)
    for ext, p in have.items():
        shutil.copy2(p, dest_noext.with_name(dest_noext.name + f".{ext}"))
    src = next(iter(have.values()))
    if "ogg" not in have:
        run(["ffmpeg", "-y", "-v", "error", "-i", str(src), "-ac", "1", "-c:a", "libvorbis", "-q:a", "4", "-map_metadata", "-1", str(dest_noext) + ".ogg"])
    if "mp3" not in have:
        run(["ffmpeg", "-y", "-v", "error", "-i", str(src), "-ac", "1", "-c:a", "libmp3lame", "-b:a", "96k", "-map_metadata", "-1", str(dest_noext) + ".mp3"])
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scrounger", default="/workspace/scrounger")
    args = ap.parse_args()
    root = Path(args.scrounger)
    micro = root / "micro"

    if OUT.exists():
        for child in OUT.iterdir():
            if child.is_dir():
                shutil.rmtree(child)
    OUT.mkdir(parents=True, exist_ok=True)

    index = {"note": "Generated by tools/sync-micro-sounds.py; do not edit.", "primitives": {}}
    licence_rows = []
    rejected = []
    missing = []

    scrounged = sorted(p.parent.name for p in micro.glob("*/candidates.json")) if micro.exists() else []
    for prim in scrounged:
        folder = micro / prim
        data = json.loads((folder / "candidates.json").read_text(encoding="utf8"))
        kept = []
        for c in data.get("candidates", []):
            lic = c.get("license", "")
            if not CC0.search(lic):
                rejected.append((prim, c.get("file"), lic))
                continue
            if not twin(folder, c["file"], OUT / prim / c["file"]):
                missing.append((prim, c["file"]))
                continue
            kept.append({
                "file": f"{prim}/{c['file']}",
                "group": c.get("group"),
                "peakMs": c.get("peak_ms"),
                "clicksMs": c.get("clicks_ms"),
                "lufs": c.get("loudness_lufs"),
                "gainTo16": c.get("gain_to_minus16_db"),
                "durationS": c.get("duration_s"),
                "author": c.get("author", ""),
                "license": lic,
                "source": c.get("source_url", ""),
                "description": c.get("description", ""),
            })
            licence_rows.append((f"{prim}/{c['file']}", c.get("author", ""), lic, c.get("source_url", "")))
        if (folder / "MANIFEST.md").exists():
            shutil.copy2(folder / "MANIFEST.md", OUT / prim / "MANIFEST.md")
        index["primitives"][prim] = {"from": f"scrounger/micro/{prim}", "candidates": kept}

    for prim, rows in FALLBACK.items():
        if prim in index["primitives"]:
            continue
        kept = []
        for group, rel in rows:
            meta = manifest_row(root, rel)
            lic = meta["license"] or ("CC0 (bs-ecbs MANIFEST: all files CC0)" if rel.startswith(BS) else "")
            if not CC0.search(lic):
                rejected.append((prim, rel, lic or "no licence found"))
                continue
            name = Path(rel).name
            dest = OUT / prim / (group or "") / name
            if not twin(root, rel, dest):
                missing.append((prim, rel))
                continue
            peak, lufs, dur = measure(str(dest) + ".ogg")
            relout = dest.relative_to(OUT).as_posix()
            kept.append({
                "file": relout,
                "group": group,
                "peakMs": peak,
                "lufs": round(lufs, 1) if lufs is not None else None,
                "gainTo16": round(-16 - lufs, 1) if lufs is not None else None,
                "durationS": dur,
                "author": meta["author"],
                "license": lic,
                "source": meta["source_url"],
                "description": f"from {rel}",
            })
            licence_rows.append((relout, meta["author"], lic, meta["source_url"] or rel))
        index["primitives"][prim] = {"from": "fallback (tools/sync-micro-sounds.py)", "candidates": kept}

    (OUT / "index.json").write_text(json.dumps(index, indent=1, ensure_ascii=False) + "\n", encoding="utf8")
    lines = [
        "# Microdemo sounds: licences",
        "",
        "Generated by `tools/sync-micro-sounds.py` from Scrounger's scrounges (`/workspace/scrounger/micro/*`, with fallbacks from `megadreifach/`, `demos-sfx/` and `bs-ecbs/`). Every file below is **CC0**; per-primitive `MANIFEST.md` files (where Scrounger wrote one) have processing notes and descriptions. Each sound ships as `.ogg` and `.mp3`.",
        "",
        "| File | Author | Licence | Source |",
        "|---|---|---|---|",
    ]
    for f, a, l, s in sorted(licence_rows):
        lines.append(f"| `{f}` | {a} | {l} | {s} |")
    lines += ["", "## Rejected (not CC0, not copied)", ""]
    lines += [f"- `{p}/{f}`: {l}" for p, f, l in rejected] or ["None."]
    (OUT / "LICENSE.md").write_text("\n".join(lines) + "\n", encoding="utf8")

    total = sum(len(v["candidates"]) for v in index["primitives"].values())
    print(f"{total} candidates in {len(index['primitives'])} primitives -> {OUT.relative_to(ROOT)}")
    for p, f, l in rejected:
        print(f"REJECTED (not CC0): {p}/{f}: {l}", file=sys.stderr)
    for p, f in missing:
        print(f"MISSING audio: {p}/{f}", file=sys.stderr)


if __name__ == "__main__":
    main()
