#!/usr/bin/env python3
"""Build the BS demo's two retail boxes into demos/bs/assets/models/ (CC0).

- proc_naval_game_box_400x265x52.glb: Scrounger's Battleship box (own work,
  CC0; MANIFEST "proc_naval_game_box_400x265x52", MEASURED by Zachary on his
  Hasbro 2015 set), unchanged geometry, with its own box art (CC0, MANIFEST
  §3 box-art plan) embedded in the material slots it was built for.
- proc_dice_game_box_120x114x89.glb: the dice game box, DESIGNED TO FIT
  what it holds (own work, CC0; after Scrounger's Yahtzee-style box,
  proc_dice_game_box_245x160x70, whose materials and lid-top art it keeps):
  the dice cup lying on its side (Ø 82.6 × 101.6 mm, real size) in one well
  and the BS key dice (five d10s, the d12, the d6) in two layers in a strip
  beside it, behind a card divider; 2 mm clearance round everything, 2 mm
  chipboard base and lid top, 1.5 mm lid walls and divider, a lid that
  telescopes over the base down to 3 mm off the table. Every size below is
  worked out from the contents (DICE BOX DESIGN); the art is recomposed for
  the lid's own proportions.

  python3 tools/bs_boxes.py [scrounger_dir]   (default /workspace/scrounger)
"""
import json, os, struct, sys

SCR = sys.argv[1] if len(sys.argv) > 1 else "/workspace/scrounger"
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "demos", "bs", "assets", "models")
NAVAL = os.path.join(SCR, "battleship-assets", "models", "box", "proc_naval_game_box_400x265x52.glb")
NAVAL_ART = os.path.join(SCR, "battleship-assets", "models", "box", "art")
DICE_ART = os.path.join(SCR, "bs-ecbs", "boxart", "mock_dice_lid_top_1024x668.jpg")


def read_glb(path):
    b = open(path, "rb").read()
    n = struct.unpack("<I", b[12:16])[0]
    j = json.loads(b[20:20 + n])
    off = 20 + n
    bl = struct.unpack("<I", b[off:off + 4])[0]
    return j, bytearray(b[off + 8:off + 8 + bl])


def write_glb(path, j, bin_):
    while len(bin_) % 4:
        bin_.append(0)
    j["buffers"] = [{"byteLength": len(bin_)}]
    js = json.dumps(j, separators=(",", ":")).encode()
    js += b" " * ((4 - len(js) % 4) % 4)
    out = struct.pack("<III", 0x46546C67, 2, 12 + 8 + len(js) + 8 + len(bin_))
    out += struct.pack("<II", len(js), 0x4E4F534A) + js + struct.pack("<II", len(bin_), 0x004E4942) + bytes(bin_)
    open(path, "wb").write(out)


def embed_art(j, bin_, art):
    """art: {material name: jpg path} -> baseColorTexture on that material (white factor)."""
    j.setdefault("images", []); j.setdefault("textures", []); j.setdefault("samplers", [])
    if not j["samplers"]:
        j["samplers"].append({"magFilter": 9729, "minFilter": 9987, "wrapS": 33071, "wrapT": 33071})
    for mat in j["materials"]:
        path = art.get(mat["name"])
        if not path:
            continue
        data = open(path, "rb").read()
        while len(bin_) % 4:
            bin_.append(0)
        j["bufferViews"].append({"buffer": 0, "byteOffset": len(bin_), "byteLength": len(data)})
        bin_ += data
        j["images"].append({"bufferView": len(j["bufferViews"]) - 1, "mimeType": "image/jpeg", "name": os.path.basename(path)})
        j["textures"].append({"sampler": 0, "source": len(j["images"]) - 1})
        pbr = mat.setdefault("pbrMetallicRoughness", {})
        pbr["baseColorTexture"] = {"index": len(j["textures"]) - 1}
        pbr["baseColorFactor"] = [1, 1, 1, 1]


def naval():
    j, bin_ = read_glb(NAVAL)
    embed_art(j, bin_, {
        "navalbox_lid_top": os.path.join(NAVAL_ART, "mock_naval_lid_top_400x265_1024x678.jpg"),
        "navalbox_lid_side_long": os.path.join(NAVAL_ART, "mock_naval_lid_side_long_400x52_1024x134.jpg"),
        "navalbox_lid_side_short": os.path.join(NAVAL_ART, "mock_naval_lid_side_short_265x52_1024x203.jpg"),
        "navalbox_insert_divider_art": os.path.join(NAVAL_ART, "mock_insert_divider_top_229x45_1024x201.jpg"),
        "navalbox_insert_fleet_art": os.path.join(NAVAL_ART, "mock_insert_fleet_strip_top_393x27_1024x70.jpg"),
    })
    write_glb(os.path.join(OUT, "proc_naval_game_box_400x265x52.glb"), j, bin_)


# ---- the dice box: DESIGNED TO FIT ------------------------------------------------
# Box frame: origin under the middle of the base's floor, +y up, the long
# side along x. The cup lies along z (its mouth to +z) in the well at +x;
# the dice strip runs along the −x wall, behind a card divider.
CUP_R, CUP_H = 0.0413, 0.1016  # the dice cup (anim/shared/cup.js), Ø 82.6 × 101.6 mm
DIE_W = 0.0202                 # the widest die across the strip: a d10's 20.2 mm (anim/dice SHAPES)
CLEAR = 0.002                  # play round the cup and the dice, every side and above
WALL, FLOOR = 0.002, 0.002     # base card (2 mm chipboard)
DIV = 0.0015                   # the divider card
LWALL, LTOP = 0.0015, 0.002    # lid walls (wrapped card), lid top
PLAY = 0.0005                  # lid over base, each side
LGAP = 0.003                   # the lid stops 3 mm off the table (a finger's grip on the base)
CUP_WELL_X = 2 * CUP_R + 2 * CLEAR          # 86.6 mm across the lying cup
STRIP_X = DIE_W + 2 * CLEAR                 # 24.2 mm: one die wide
IN_X = STRIP_X + DIV + CUP_WELL_X           # 112.3 mm
IN_Z = CUP_H + 2 * CLEAR                    # 105.6 mm: the cup's length (the dice strip is as long)
IN_H = 2 * CUP_R + CLEAR                    # 84.6 mm: the lying cup, 2 mm under the lid
W, D = IN_X + 2 * WALL, IN_Z + 2 * WALL     # base outer 116.3 × 109.6 mm
HB = FLOOR + IN_H                           # base rim 86.6 mm; the lid's top rests on it
HT = HB + LTOP                              # 88.6 mm closed
LW, LD = W + 2 * (PLAY + LWALL), D + 2 * (PLAY + LWALL)  # lid outer 120.3 × 113.6 mm
DIV_X0 = -IN_X / 2 + STRIP_X                # the divider, x DIV_X0 … DIV_X0 + DIV
DICE_FILE = "proc_dice_game_box_%dx%dx%d.glb" % (round(LW * 1000), round(LD * 1000), round(HT * 1000))


class Mesh:
    def __init__(self):
        self.prims = {}

    def quad(self, mat, a, b, c, d, n, uv=((0, 1), (1, 1), (1, 0), (0, 0))):
        p = self.prims.setdefault(mat, {"pos": [], "nor": [], "uv": [], "idx": []})
        base = len(p["pos"])
        p["pos"] += [a, b, c, d]; p["nor"] += [n] * 4; p["uv"] += list(uv)
        # counter-clockwise seen from the normal side
        e1 = [b[k] - a[k] for k in range(3)]; e2 = [c[k] - a[k] for k in range(3)]
        cr = [e1[1] * e2[2] - e1[2] * e2[1], e1[2] * e2[0] - e1[0] * e2[2], e1[0] * e2[1] - e1[1] * e2[0]]
        if sum(cr[k] * n[k] for k in range(3)) >= 0:
            p["idx"] += [base, base + 1, base + 2, base, base + 2, base + 3]
        else:
            p["idx"] += [base, base + 2, base + 1, base, base + 3, base + 2]


def box_faces(m, x0, x1, y0, y1, z0, z1, mats, inward=False, skip=(), uvs=None):
    """Faces of an axis box; mats: {face: material}; inward flips normals (an inside surface); uvs: {face: uv} overrides."""
    s = -1 if inward else 1
    F = {
        "top": ([(x0, y1, z1), (x1, y1, z1), (x1, y1, z0), (x0, y1, z0)], (0, s, 0)),
        "bottom": ([(x0, y0, z0), (x1, y0, z0), (x1, y0, z1), (x0, y0, z1)], (0, -s, 0)),
        "front": ([(x0, y0, z1), (x1, y0, z1), (x1, y1, z1), (x0, y1, z1)], (0, 0, s)),
        "back": ([(x1, y0, z0), (x0, y0, z0), (x0, y1, z0), (x1, y1, z0)], (0, 0, -s)),
        "left": ([(x0, y0, z0), (x0, y0, z1), (x0, y1, z1), (x0, y1, z0)], (-s, 0, 0)),
        "right": ([(x1, y0, z1), (x1, y0, z0), (x1, y1, z0), (x1, y1, z1)], (s, 0, 0)),
    }
    for name, (q, n) in F.items():
        if name in skip or name not in mats:
            continue
        # one uv for every face unless overridden: on the top, the art reads upright from the front (+z)
        uv = (uvs or {}).get(name, ((0, 1), (1, 1), (1, 0), (0, 0)))
        m.quad(mats[name], *q, n, uv)


def rim(m, mat, ox, oz, ix, iz, y, n):
    """The ring between an outer and an inner rectangle at height y (normal n)."""
    O = [(-ox, y, -oz), (ox, y, -oz), (ox, y, oz), (-ox, y, oz)]
    I = [(-ix, y, -iz), (ix, y, -iz), (ix, y, iz), (-ix, y, iz)]
    for k in range(4):
        a, b = O[k], O[(k + 1) % 4]
        c, d = I[(k + 1) % 4], I[k]
        m.quad(mat, a, b, c, d, n)


def dice_box():
    mats = ["dicebox_lid_top", "dicebox_lid_side_long", "dicebox_lid_side_short", "dicebox_inside", "dicebox_base"]
    colour = {"dicebox_lid_top": [1, 1, 1, 1], "dicebox_lid_side_long": [0.30, 0.35, 0.50, 1],
              "dicebox_lid_side_short": [0.30, 0.35, 0.50, 1], "dicebox_inside": [0.85, 0.82, 0.75, 1],
              "dicebox_base": [0.85, 0.82, 0.75, 1]}
    base, lid = Mesh(), Mesh()
    hx, hz = W / 2, D / 2
    box_faces(base, -hx, hx, 0, HB, -hz, hz, {k: "dicebox_base" for k in ("bottom", "front", "back", "left", "right")})
    ix, iz = hx - WALL, hz - WALL
    box_faces(base, -ix, ix, FLOOR, HB, -iz, iz, {k: "dicebox_inside" for k in ("bottom", "front", "back", "left", "right")}, inward=True)
    rim(base, "dicebox_inside", hx, hz, ix, iz, HB, (0, 1, 0))
    box_faces(base, DIV_X0, DIV_X0 + DIV, FLOOR, HB, -iz, iz, {k: "dicebox_inside" for k in ("top", "left", "right")})
    lx, lz = LW / 2, LD / 2
    y0 = LGAP
    # The art reads upright from the strip side (−x), as the box lies on the table and in the chest (turned a quarter).
    box_faces(lid, -lx, lx, y0, HT, -lz, lz, {"top": "dicebox_lid_top", "front": "dicebox_lid_side_long", "back": "dicebox_lid_side_long",
                                             "left": "dicebox_lid_side_short", "right": "dicebox_lid_side_short"},
              uvs={"top": ((1, 1), (1, 0), (0, 0), (0, 1))})
    jx, jz = lx - LWALL, lz - LWALL
    box_faces(lid, -jx, jx, y0, HT - LTOP, -jz, jz, {k: "dicebox_inside" for k in ("top", "front", "back", "left", "right")}, inward=True)
    rim(lid, "dicebox_inside", lx, lz, jx, jz, y0, (0, -1, 0))

    j = {"asset": {"version": "2.0", "generator": "cryptoys tools/bs_boxes.py"}, "scene": 0,
         "scenes": [{"nodes": [0, 1]}], "nodes": [{"name": "dicebox_lid", "mesh": 0}, {"name": "dicebox_base", "mesh": 1}],
         "materials": [{"name": n, "pbrMetallicRoughness": {"baseColorFactor": colour[n], "metallicFactor": 0, "roughnessFactor": 0.6}} for n in mats],
         "meshes": [], "accessors": [], "bufferViews": []}
    bin_ = bytearray()

    def view(data, target):
        while len(bin_) % 4:
            bin_.append(0)
        j["bufferViews"].append({"buffer": 0, "byteOffset": len(bin_), "byteLength": len(data), "target": target})
        bin_.extend(data)
        return len(j["bufferViews"]) - 1

    for name, mesh in (("dicebox_lid", lid), ("dicebox_base", base)):
        prims = []
        for mat, p in mesh.prims.items():
            pos = b"".join(struct.pack("<fff", *v) for v in p["pos"])
            nor = b"".join(struct.pack("<fff", *v) for v in p["nor"])
            uv = b"".join(struct.pack("<ff", *v) for v in p["uv"])
            idx = b"".join(struct.pack("<H", i) for i in p["idx"])
            acc = []
            for data, comp, typ, cnt, tgt, extra in (
                (pos, 5126, "VEC3", len(p["pos"]), 34962, {"min": [min(v[k] for v in p["pos"]) for k in range(3)], "max": [max(v[k] for v in p["pos"]) for k in range(3)]}),
                (nor, 5126, "VEC3", len(p["nor"]), 34962, {}),
                (uv, 5126, "VEC2", len(p["uv"]), 34962, {}),
                (idx, 5123, "SCALAR", len(p["idx"]), 34963, {}),
            ):
                j["accessors"].append({"bufferView": view(data, tgt), "componentType": comp, "count": cnt, "type": typ, **extra})
                acc.append(len(j["accessors"]) - 1)
            prims.append({"attributes": {"POSITION": acc[0], "NORMAL": acc[1], "TEXCOORD_0": acc[2]}, "indices": acc[3], "material": mats.index(mat)})
        j["meshes"].append({"name": name, "primitives": prims})
    embed_art(j, bin_, {"dicebox_lid_top": lid_art()})
    write_glb(os.path.join(OUT, DICE_FILE), j, bin_)


def lid_art():
    """Scrounger's lid-top art (1024 × 668, CC0) recomposed for this lid's proportions, read from −x:
    LD wide, LW tall. Its own pieces (title, line, five dice) on its own paper; returns a jpg path."""
    from PIL import Image, ImageDraw
    src = Image.open(DICE_ART).convert("RGB")
    w = 1024
    h = round(w * LW / LD)
    paper = src.crop((60, 336, 980, 398))  # plain paper between the line and the dice
    out = Image.new("RGB", (w, h))
    for k, y in enumerate(range(0, h, paper.height)):
        tile = paper.transpose(Image.FLIP_TOP_BOTTOM) if k % 2 else paper
        for x in (0, paper.width):
            out.paste(tile if x == 0 else tile.transpose(Image.FLIP_LEFT_RIGHT), (x, y))
    ink = src.getpixel((32, 300))
    ImageDraw.Draw(out).rectangle((30, 30, w - 31, h - 31), outline=ink, width=7)
    title = src.crop((62, 92, 906, 242))
    line = src.crop((66, 266, 786, 326))
    out.paste(title, ((w - title.width) // 2, 140))
    out.paste(line, ((w - line.width) // 2, 330))
    dice = [src.crop((x, 408, x + 154, 566)) for x in (68, 252, 436, 620, 804)]
    size = 200
    dice = [d.resize((size, round(d.height * size / d.width)), Image.LANCZOS) for d in dice]
    for row, (y, idx) in enumerate(((500, (0, 1, 2)), (500 + dice[0].height + 50, (3, 4)))):
        n = len(idx)
        x0 = (w - (n * size + (n - 1) * 60)) // 2
        for i, k in enumerate(idx):
            out.paste(dice[k], (x0 + i * (size + 60), y))
    path = "/tmp/dicebox_lid_top_%dx%d.jpg" % (w, h)
    out.save(path, quality=90)
    return path


if __name__ == "__main__":
    naval()
    dice_box()
    print("wrote", OUT)
