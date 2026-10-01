#!/usr/bin/env python3
"""Copy the sounds the microdemo pages use into demos/micro/sounds/.

    python3 tools/sync-micro-sounds.py [--scrounger /workspace/scrounger]
    python3 tools/sync-micro-sounds.py --list [primitive]   # what can be swapped in

Each page's demos/micro/<page>/settings.js names one file per sound slot
(`file: "<primitive>/<group>/<name>"`). Only those files are copied, so
after swapping a file in a settings.js, re-run this. Candidates come from:

1. /workspace/scrounger/micro/<primitive>/candidates.json (Scrounger's
   per-primitive picks: file, group, peak_ms, loudness, licence, source).
2. FALLBACK below: primitives Scrounger has not cut yet, taken from the
   megadreifach / demos-sfx / bs-ecbs scrounges. Peak and loudness are
   measured here with ffmpeg (loudest sample; ebur128 momentary max).
   A Scrounger folder of the same name replaces its fallback.
3. CUTS below: our own cuts from raw CC0 packs in Scrounger's downloads
   (trim, fades, mono, peak-normalised to -1.5 dBFS, OGG q4 + MP3 96k),
   for sounds no scrounge has cut yet. These are added to any primitive.

Only CC0 candidates can be chosen; anything else is printed as rejected.

Writes demos/micro/sounds/<primitive>/<file>.{ogg,mp3}, index.json
(metadata of the copied files, read by tools/check-micro-sounds.py) and
LICENSE.md (credits). Needs ffmpeg for the fallbacks and for any missing
.mp3/.ogg twin.
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

# primitive -> list of (group, scrounge-relative raw file, cut name, cut spec, credit)
# cut spec: start / dur / fade_out in seconds (3 ms fade-in).
KENNEY_RPG = {"author": "Kenney Vleugels (Kenney.nl)", "license": "Creative Commons Zero, CC0 (License.txt in the pack)", "source": "https://kenney.nl/assets/rpg-audio"}
CUTS = {
    "scramble-turn": [
        ("settle", "_dl/kenney_rpg-audio/Audio/bookClose.ogg", "settle_kenney-rpg-bookclose-cut",
         {"start": 0.058, "dur": 0.15, "fade_out": 0.09}, KENNEY_RPG,
         "Kenney RPG Audio bookClose, cut to the single thump: a hardcover closing, soft and dull (no paper tail)."),
        ("settle", "_dl/kenney_rpg-audio/Audio/bookOpen.ogg", "settle_kenney-rpg-bookopen-cut",
         {"start": 0.0, "dur": 0.15, "fade_out": 0.07}, KENNEY_RPG,
         "Kenney RPG Audio bookOpen, cut: a darker, softer cover flop that swells into its thump."),
        ("settle", "_dl/kenney_rpg-audio/Audio/bookPlace1.ogg", "settle_kenney-rpg-bookplace1-cut",
         {"start": 0.045, "dur": 0.16, "fade_out": 0.09}, KENNEY_RPG,
         "Kenney RPG Audio bookPlace1, cut past its pre-tick: a book set down on wood, a little firmer and brighter."),
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


def cut(src, dest_noext, spec):
    """Trim, fade, mono 44.1 kHz, peak-normalise to -1.5 dBFS, encode OGG and MP3."""
    import array
    start, dur, fade = spec["start"], spec["dur"], spec["fade_out"]
    shape = f"atrim=start={start}:duration={dur},asetpts=N/SR/TB,afade=t=in:d=0.003,afade=t=out:st={dur - fade:.4f}:d={fade}"
    raw = subprocess.run(["ffmpeg", "-v", "error", "-i", str(src), "-af", shape, "-ac", "1", "-ar", "44100", "-f", "f32le", "-"],
                         check=True, capture_output=True).stdout
    samples = array.array("f")
    samples.frombytes(raw[: len(raw) // 4 * 4])
    peak = max((abs(v) for v in samples), default=0) or 1.0
    gain = 10 ** (-1.5 / 20) / peak
    dest_noext.parent.mkdir(parents=True, exist_ok=True)
    af = f"{shape},volume={gain:.6f}"
    run(["ffmpeg", "-y", "-v", "error", "-i", str(src), "-af", af, "-ac", "1", "-ar", "44100", "-c:a", "libvorbis", "-q:a", "4", "-map_metadata", "-1", "-fflags", "+bitexact", "-flags:a", "+bitexact", str(dest_noext) + ".ogg"])
    run(["ffmpeg", "-y", "-v", "error", "-i", str(src), "-af", af, "-ac", "1", "-ar", "44100", "-c:a", "libmp3lame", "-b:a", "96k", "-map_metadata", "-1", "-fflags", "+bitexact", "-flags:a", "+bitexact", str(dest_noext) + ".mp3"])
    return True


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


SETTINGS_FILE = re.compile(r"""\bfile:\s*["']([^"']+)["']""")


def catalogue(root):
    """Every CC0 candidate Scrounger offers: relout -> source + metadata."""
    micro = root / "micro"
    cat, rejected = {}, []
    scrounged = sorted(p.parent.name for p in micro.glob("*/candidates.json")) if micro.exists() else []
    for prim in scrounged:
        folder = micro / prim
        data = json.loads((folder / "candidates.json").read_text(encoding="utf8"))
        for c in data.get("candidates", []):
            lic = c.get("license", "")
            if not CC0.search(lic):
                rejected.append((prim, c.get("file"), lic))
                continue
            cat[f"{prim}/{c['file']}"] = {
                "src": (folder, c["file"]),
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
            }
    for prim, rows in FALLBACK.items():
        if prim in scrounged:
            continue
        for group, rel in rows:
            meta = manifest_row(root, rel)
            lic = meta["license"] or ("CC0 (bs-ecbs MANIFEST: all files CC0)" if rel.startswith(BS) else "")
            if not CC0.search(lic):
                rejected.append((prim, rel, lic or "no licence found"))
                continue
            relout = f"{prim}/{group}/{Path(rel).name}" if group else f"{prim}/{Path(rel).name}"
            cat[relout] = {
                "src": (root, rel),
                "group": group,
                "author": meta["author"],
                "license": lic,
                "source": meta["source_url"] or rel,
                "description": f"from {rel}",
                "measure": True,
            }
    for prim, rows in CUTS.items():
        for group, rel, name, spec, credit, description in rows:
            if not CC0.search(credit["license"]) or not (root / rel).exists():
                rejected.append((prim, rel, credit["license"] if (root / rel).exists() else "raw file not found"))
                continue
            cat[f"{prim}/{group}/{name}"] = {
                "cut": (root / rel, spec),
                "group": group,
                "author": credit["author"],
                "license": credit["license"],
                "source": credit["source"],
                "description": description,
                "measure": True,
            }
    return cat, rejected


def chosen_files():
    """Sound files named in demos/micro/*/settings.js: page -> [file]."""
    out = {}
    for path in sorted((ROOT / "demos" / "micro").glob("*/settings.js")):
        out[path.parent.name] = SETTINGS_FILE.findall(path.read_text(encoding="utf8"))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scrounger", default="/workspace/scrounger")
    ap.add_argument("--list", nargs="?", const="", metavar="PRIMITIVE", help="print the available candidates (optionally for one primitive) and exit")
    args = ap.parse_args()
    root = Path(args.scrounger)
    cat, rejected = catalogue(root)

    if args.list is not None:
        for relout, c in sorted(cat.items()):
            if args.list and not relout.startswith(args.list + "/"):
                continue
            print(f"{relout}  peak {c.get('peakMs', '?')} ms  To-16 {c.get('gainTo16', '?')} dB  {c.get('description', '')}")
        return

    pages = chosen_files()
    wanted = sorted({f for files in pages.values() for f in files})
    unknown = [f for f in wanted if f not in cat]

    if OUT.exists():
        for child in OUT.iterdir():
            if child.is_dir():
                shutil.rmtree(child)
    OUT.mkdir(parents=True, exist_ok=True)

    index = {"note": "Generated by tools/sync-micro-sounds.py from demos/micro/*/settings.js; do not edit.", "files": {}}
    licence_rows = []
    missing = []
    for relout in wanted:
        c = cat.get(relout)
        if not c:
            continue
        if "cut" in c:
            ok = cut(c["cut"][0], OUT / relout, c["cut"][1])
        else:
            src_dir, src_rel = c["src"]
            ok = twin(src_dir, src_rel, OUT / relout)
        if not ok:
            missing.append(relout)
            continue
        meta = {k: v for k, v in c.items() if k not in ("src", "cut", "measure")}
        if c.get("measure"):
            peak, lufs, dur = measure(str(OUT / relout) + ".ogg")
            meta.update(peakMs=peak, lufs=round(lufs, 1) if lufs is not None else None,
                        gainTo16=round(-16 - lufs, 1) if lufs is not None else None, durationS=dur)
        meta["pages"] = sorted(p for p, files in pages.items() if relout in files)
        index["files"][relout] = meta
        licence_rows.append((relout, c.get("author", ""), c.get("license", ""), c.get("source", "")))

    (OUT / "index.json").write_text(json.dumps(index, indent=1, ensure_ascii=False) + "\n", encoding="utf8")
    lines = [
        "# Microdemo sounds: credits",
        "",
        "The sounds the microdemo pages play (chosen in `demos/micro/*/settings.js`), copied by `tools/sync-micro-sounds.py` from Scrounger's scrounges (`/workspace/scrounger/micro/*`, with fallbacks from `megadreifach/`, `demos-sfx/` and `bs-ecbs/`, and a few of our own cuts from raw CC0 packs in Scrounger's downloads, named `*-cut`). Every file is **CC0**. Each sound ships as `.ogg` and `.mp3`.",
        "",
        "| File | Author | Licence | Source |",
        "|---|---|---|---|",
    ]
    for f, a, l, s in sorted(licence_rows):
        lines.append(f"| `{f}` | {a} | {l} | {s} |")
    (OUT / "LICENSE.md").write_text("\n".join(lines) + "\n", encoding="utf8")

    print(f"{len(index['files'])} sound files for {len(pages)} pages -> {OUT.relative_to(ROOT)} ({len(cat)} candidates available)")
    for p, f, l in rejected:
        print(f"REJECTED (not CC0): {p}/{f}: {l}", file=sys.stderr)
    for f in unknown:
        print(f"UNKNOWN (not a CC0 candidate): {f}", file=sys.stderr)
    for f in missing:
        print(f"MISSING audio: {f}", file=sys.stderr)
    if unknown or missing:
        sys.exit(1)


if __name__ == "__main__":
    main()
