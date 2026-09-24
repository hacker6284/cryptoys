# Third-party assets — cryptoys playroom

All materials below were verified CC0 / Public Domain on download day (2026-09-23).
No invented license claims. These files ship with the demo-layer playroom under `demos/playroom/assets/`.

## Ship scene (hub)

Loaded by `demos/playroom/world.js`:

- Textures: wood floor, furniture wood, plaster, fabric normal/roughness (felt albedo stays tinted green)
- HDRI: Solitude Interior 1K as `scene.environment` only (windowless room; warm solid background)
- Models: Kenney chest (separable lid), Kenney shelf plants, Quaternius houseplant

**Not loaded in the shipped room** (kept here as spares; do not drop a rug under the table — that was rejected):

- `models/kenney_rugRound.glb`
- `models/round_rug.glb`
- `models/kenney_bookcaseOpen.glb`
- `models/shelf_large.glb`
- `models/light_ceiling.glb` (pendant stays procedural so the light stays colocated)

The chest is scaled in-scene to about 0.95 m on its longest edge (kid-openable toy chest against the empty side wall).

## Models

| File | Source | Author | License | Notes |
|------|--------|--------|---------|-------|
| `models/chest.glb` | [Poly Pizza — Chest](https://poly.pizza/m/g54i2tEIEs) (Kenney Furniture / objects) | Kenney (www.kenney.nl) | **CC0** | Separate `chest_1` + `lid_1` meshes |
| `models/kenney_bookcaseOpen.glb` | [Kenney Furniture Kit](https://kenney.nl/assets/furniture-kit) OBJ → GLB via obj2gltf | Kenney | **CC0** | Spare |
| `models/kenney_pottedPlant.glb` | Kenney Furniture Kit OBJ → GLB | Kenney | **CC0** | Shelf plant |
| `models/kenney_plantSmall2.glb` | Kenney Furniture Kit OBJ → GLB | Kenney | **CC0** | Shelf plant variant |
| `models/kenney_rugRound.glb` | Kenney Furniture Kit OBJ → GLB | Kenney | **CC0** | **Unused in ship scene** |
| `models/houseplant.glb` | [Poly Pizza — Houseplant](https://poly.pizza/m/bfLOqIV5uP) | Quaternius | **CC0** | Floor / corner plant |
| `models/shelf_large.glb` | [Poly Pizza — Shelf Large](https://poly.pizza/m/3FmjkLClVE) | Quaternius | **CC0** | Spare (too tall/narrow for the 4.4 m bay) |
| `models/light_ceiling.glb` | [Poly Pizza — Light Ceiling](https://poly.pizza/m/S3HkX8iTl2) | Quaternius | **CC0** | Spare |
| `models/round_rug.glb` | [Poly Pizza — Round Rug](https://poly.pizza/m/ZYBzMHnSbM) | Quaternius | **CC0** | **Unused in ship scene** |

**Kenney Furniture Kit** downloaded from  
`https://kenney.nl/media/pages/assets/furniture-kit/440e0608a4-1677580847/kenney_furniture-kit.zip`  
License.txt: Creative Commons Zero (CC0).

**Not used:** 3Darknight itch chest (`https://3darknight.itch.io/3d-low-poly-chest`) — Kenney CC0 chest with separable lid substituted.

## Textures (ambientCG — CC0)

| Folder | Material | URL | Maps kept |
|--------|----------|-----|-----------|
| `textures/woodfloor/` | WoodFloor042 1K JPG | https://ambientcg.com/view?id=WoodFloor042 | Color, NormalGL, Roughness |
| `textures/wood/` | Wood051 1K JPG | https://ambientcg.com/view?id=Wood051 | Color, NormalGL, Roughness |
| `textures/plaster/` | Plaster001 1K JPG | https://ambientcg.com/view?id=Plaster001 | Color, NormalGL, Roughness |
| `textures/fabric/` | Fabric030 1K JPG | https://ambientcg.com/view?id=Fabric030 | Color, NormalGL, Roughness (felt uses Normal + Roughness; albedo stays tinted green) |

## HDRI

| File | Source | License |
|------|--------|---------|
| `hdri/solitude_interior_1k.hdr` | [Poly Haven — Solitude Interior](https://polyhaven.com/a/solitude_interior) 1K HDR | **CC0** |

## Attribution note

CC0 does not require attribution; Kenney / Quaternius / ambientCG / Poly Haven credited here for clarity.
