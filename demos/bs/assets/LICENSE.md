# BS demo assets

Every file here is CC0 1.0 or public domain (Zachary's rule for demo
assets: CC0 or public domain only, no CC-BY). Assembled by Scrounger for
cryptoys; the playroom loads each one by path (`playroom/bs-stage.js`
`BS_MODELS`), so an updated GLB can be dropped in under the same name.

| File | What | Real size | Source / author | Licence |
|---|---|---|---|---|
| `models/bs_unit_red.glb` | Battleship travel unit (Hasbro 2015 edition #B7447/E6445, modelled from Zachary's tape and caliper measurements, 2026-10-07), red, lid open 90° | 230 × 177 × 173.6 mm open (230 × 170 × 35 mm closed) | own work, Scrounger for cryptoys (Blender 4.2, procedural), 2026-10-07 | CC0 1.0 |
| `models/bs_unit_blue.glb` | the same unit, blue | same | own work, Scrounger | CC0 1.0 |
| `models/bs_pegs.glb` | `peg_white`, `peg_red` (+ 8-sided LODs) | Ø 5 × 18 mm (head 12 mm, shank Ø 3 × 6 mm) | own work, Scrounger | CC0 1.0 |
| `models/bs_ships.glb` | carrier, battleship, cruiser, submarine, destroyer | 65 / 52 / 41 / 41 / 27 × 10 mm | own work, Scrounger | CC0 1.0 |
| `models/facehunter_d10_22mm.glb` | d10 numbered 0–9 (rescaled by Scrounger to 22 mm) | 22.0 mm pole to pole | Facehunter2003, "Low Poly 3D Dice", https://opengameart.org/content/low-poly-3d-dice (licence re-read 2026-10-10); numerals in Tuffy (public domain, http://tulrich.com/fonts/) | CC0 |
| `models/facehunter_d12_19mm_box.glb` | d12 | 19 mm bounding box (20.3 mm vertex to vertex) | Facehunter2003, same page | CC0 |
| `models/facehunter_d6_16mm.glb` | d6 with numerals | 16.0 mm face to face | Facehunter2003, same page | CC0 |
| `models/proc_dice_cup_83x102mm.glb` | leather-look dice cup (lathe, rolled rim), rebuilt at the sourced 3 1/4" × 4" | Ø 82.6 × 101.6 mm (Scrounger's Ø 82 × 99.5 mm `proc_dice_cup_95mm.glb`, scaled per axis, normals redone) | own work, Scrounger (procedural, `bs-ecbs/yahtzee/models/`, MANIFEST §2c "procedural (mine)") | CC0 1.0 (own work, released like the rest of his own models) |
| `models/proc_naval_game_box_400x265x52.glb` | Battleship retail box (Hasbro 2015 set), lid and base in 1.5 mm card with the card divider and fleet strip; holds both closed units; mock box art embedded as textures (`tools/bs_boxes.py`) | 400 × 265 × 52.5 mm (MEASURED by Zachary, 2026-10-07) | own work, Scrounger (procedural, `bs-ecbs/models/procedural/`, MANIFEST §2b); art: Scrounger's own mock-ups (`bs-ecbs/boxart/mock_naval_*`, `mock_insert_*`: PD U.S. Navy photo of the USS Iowa, Paper006 CC0, set in Black Ops One and Oswald, SIL OFL 1.1, used only to render; no font file ships) | CC0 1.0 |
| `models/proc_dice_game_box_245x160x108.glb` | dice game retail box, lid and hollow base in card; holds the dice cup standing with the key dice inside it; the lid's top carries the mock box art (`tools/bs_boxes.py`) | 248 × 163 × 108 mm with its lid (base 245 × 160 × 102.5 mm). The footprint is Scrounger's 245 × 160 mm design (not sourced); the height is ours, so the Ø 82.6 × 101.6 mm cup stands in it (his 70 mm box has a solid base) | own work (procedural, `tools/bs_boxes.py`, after Scrounger's `proc_dice_game_box_245x160x70.glb`, MANIFEST §2c); art: Scrounger's `bs-ecbs/boxart/mock_dice_lid_top_1024x668.jpg` (Paper001 CC0, Alfa Slab One and Oswald, SIL OFL 1.1, used only to render; dice drawn by hand) | CC0 1.0 |

The grid-plate textures embedded in the unit GLBs are Scrounger's own art
(cell outlines and A–J / 1–10 set in Oswald, SIL OFL 1.1, used only to
render the image; no font file ships). No Hasbro or Milton Bradley logos,
stickers or moulded text, with one exception: the box art's titles
"BATTLESHIP" and "YAHTZEE" are Hasbro trademarks, used knowingly with
Zachary's approval for the retail boxes; check them again before any public
release.
