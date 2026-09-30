/-
  PROOF-ONLY. The hand-written model of `scramble_v2`'s digest, written from
  primitives/hash/scramble/SPEC.md ("The cube", "Moves", "Rule B", "Closer and seat",
  "Digest", "API", "scramble_v2"). Sudo does not emit this file.

  Cubies sit on integer coordinates; a cubie is its position plus a list of stickers,
  each a color facing a direction. A face turn applies the SPEC's map to the position
  and to every sticker direction; Rule B and the seat apply the matrix with rows
  `n = e × t`, `e`, `t`. The digest reads the seated cube by the SPEC's slot tables.

  v2 only. No trace (the trace text is not modelled; see README). Not a hash-security
  claim. Where the SPEC leaves a case undefined (no cubie at a spot, a sticker missing,
  a set of colors that is no piece, a color with no center), the model answers `none`;
  `Link2/Reach.lean` proves that never happens on the walk.

  The list order of the cubies (x outer, then y, then z) is an enumeration convention
  of the model and of the sudo's `solved_cube`; nothing in the digest depends on it,
  because every read looks a cubie up by its position.
-/
namespace ScrambleV2

/-! ## The cube (SPEC "The cube") -/

/-- A lattice point or a direction: `+X` right, `+Y` up, `+Z` front. -/
structure V3 where
  x : Int
  y : Int
  z : Int
  deriving DecidableEq, Repr

namespace V3
def dot (a b : V3) : Int := a.x * b.x + a.y * b.y + a.z * b.z
def cross (a b : V3) : V3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩
end V3

/-- The six solved colors. -/
inductive Color where
  | W | Y | R | O | B | G
  deriving DecidableEq, Repr

/-- The six axes, in the order of the SPEC's solved-color table:
    `+Y`, `-Y`, `+X`, `-X`, `+Z`, `-Z`. -/
def axes : List V3 := [⟨0, 1, 0⟩, ⟨0, -1, 0⟩, ⟨1, 0, 0⟩, ⟨-1, 0, 0⟩, ⟨0, 0, 1⟩, ⟨0, 0, -1⟩]

/-- SPEC solved colors: `+Y` W, `-Y` Y, `+X` R, `-X` O, `+Z` G, `-Z` B. -/
def homeColor (a : V3) : Option Color :=
  if a = ⟨0, 1, 0⟩ then some .W
  else if a = ⟨0, -1, 0⟩ then some .Y
  else if a = ⟨1, 0, 0⟩ then some .R
  else if a = ⟨-1, 0, 0⟩ then some .O
  else if a = ⟨0, 0, 1⟩ then some .G
  else if a = ⟨0, 0, -1⟩ then some .B
  else none

/-- A cubie: where it sits, and its stickers (a color facing a direction). -/
structure Cubie where
  pos : V3
  stickers : List (V3 × Color)
  deriving DecidableEq, Repr

abbrev Cube := List Cubie

def trits : List Int := [-1, 0, 1]

/-- The 26 lattice points `x, y, z ∈ {-1, 0, 1}` without the core, `x` outer, then
    `y`, then `z`. -/
def lattice : List V3 :=
  trits.flatMap fun x => trits.flatMap fun y => trits.filterMap fun z =>
    if x = 0 ∧ y = 0 ∧ z = 0 then none else some ⟨x, y, z⟩

/-- A solved cubie at `p`: one sticker on every axis `a` with `a · p = 1` (the faces the
    cubie is on), in that face's solved color. -/
def solvedCubie (p : V3) : Cubie :=
  ⟨p, axes.filterMap fun a => if V3.dot a p = 1 then (homeColor a).map (a, ·) else none⟩

def solvedCube : Cube := lattice.map solvedCubie

/-! ## Moves (SPEC "Moves") -/

inductive Face where
  | U | D | R | L | F | B
  deriving DecidableEq, Repr

/-- SPEC "Moves", column "Cubies". -/
def Face.onFace : Face → V3 → Bool
  | .U, p => p.y = 1
  | .D, p => p.y = -1
  | .R, p => p.x = 1
  | .L, p => p.x = -1
  | .F, p => p.z = 1
  | .B, p => p.z = -1

/-- SPEC "Moves", column "Map". `U` and `D` use the same map. -/
def Face.map : Face → V3 → V3
  | .U, ⟨x, y, z⟩ => ⟨z, y, -x⟩
  | .D, ⟨x, y, z⟩ => ⟨z, y, -x⟩
  | .R, ⟨x, y, z⟩ => ⟨x, z, -y⟩
  | .L, ⟨x, y, z⟩ => ⟨x, -z, y⟩
  | .F, ⟨x, y, z⟩ => ⟨y, -x, z⟩
  | .B, ⟨x, y, z⟩ => ⟨-y, x, z⟩

/-- Move a cubie by `g`: its position and each of its sticker directions. -/
def moveCubie (g : V3 → V3) (c : Cubie) : Cubie :=
  ⟨g c.pos, c.stickers.map fun s => (g s.1, s.2)⟩

/-- One quarter turn: the map, applied to every cubie on that face. -/
def quarter (f : Face) (cube : Cube) : Cube :=
  cube.map fun c => if f.onFace c.pos then moveCubie f.map c else c

/-! ## Rule B, closer and seat -/

/-- The color on `c` facing `d`. -/
def colorFacing (c : Cubie) (d : V3) : Option Color :=
  (c.stickers.find? fun s => s.1 = d).map (·.2)

/-- The cubie in slot `p`. -/
def cubieAt (cube : Cube) (p : V3) : Option Cubie :=
  cube.find? fun c => c.pos = p

/-- A face center: exactly two coordinates are zero. -/
def isCenter (p : V3) : Bool :=
  ([p.x, p.y, p.z].filter (· = 0)).length = 2

/-- Where the center of color `col` sits. -/
def centerOf (cube : Cube) (col : Color) : Option V3 :=
  (cube.find? fun c => isCenter c.pos && c.stickers.any (·.2 = col)).map (·.pos)

/-- A 3×3 integer matrix by rows, acting on column vectors. -/
structure Mat where
  r0 : V3
  r1 : V3
  r2 : V3
  deriving DecidableEq, Repr

def Mat.app (m : Mat) (v : V3) : V3 := ⟨m.r0.dot v, m.r1.dot v, m.r2.dot v⟩

/-- SPEC "Rule B": rotate the whole cube so the center of `up` goes to `+Y` and the
    center of `front` to `+Z`, by the matrix with rows `n = e × t`, `e`, `t`. If `e` is
    already `+Y` and `t` already `+Z`, the cube does not move. -/
def rotateTo (cube : Cube) (up front : Color) : Option Cube := do
  let e ← centerOf cube up
  let t ← centerOf cube front
  if e = ⟨0, 1, 0⟩ ∧ t = ⟨0, 0, 1⟩ then pure cube
  else pure (cube.map (moveCubie (Mat.app ⟨V3.cross e t, e, t⟩)))

/-- SPEC "Rule B": `up` and `front` are the colors on the cubie in `(1, 1, 1)` facing
    `+Y` and `+Z`. -/
def ruleB (cube : Cube) : Option Cube := do
  let c ← cubieAt cube ⟨1, 1, 1⟩
  let up ← colorFacing c ⟨0, 1, 0⟩
  let front ← colorFacing c ⟨0, 0, 1⟩
  rotateTo cube up front

/-- SPEC "Closer and seat": `F2`, `B2`, then the Rule B rotation with `up = W`,
    `front = G`. -/
def seat (cube : Cube) : Option Cube :=
  rotateTo (quarter .B (quarter .B (quarter .F (quarter .F cube)))) .W .G

/-! ## scramble_v2 walk (SPEC "API", "scramble_v2") -/

/-- SPEC `scramble_v2` turn table: each nybble is two clockwise quarter turns. -/
def v2Turns : Nat → Face × Face
  | 0 => (.U, .R) | 1 => (.U, .F) | 2 => (.U, .L) | 3 => (.U, .B)
  | 4 => (.D, .R) | 5 => (.D, .F) | 6 => (.R, .U) | 7 => (.R, .D)
  | 8 => (.F, .U) | 9 => (.F, .D) | 10 => (.B, .U) | 11 => (.F, .R)
  | 12 => (.L, .U) | 13 => (.F, .L) | 14 => (.R, .F) | _ => (.R, .B)

/-- One v2 symbol: its two quarter turns, then Rule B. -/
def symbolV2 (cube : Cube) (n : Nat) : Option Cube :=
  ruleB (quarter (v2Turns n).2 (quarter (v2Turns n).1 cube))

/-- SPEC "API": each byte is two nybbles, high nybble first. -/
def nybbles (msg : List Nat) : List Nat :=
  msg.flatMap fun b => [b / 16, b % 16]

/-- SPEC `scramble_v2` padding: append the marker `8`; while the tape is shorter than
    12 nybbles, append the cycle `6 0 7 1`. -/
def padV2 (ny : List Nat) : List Nat :=
  let t := ny ++ [8]
  t ++ (List.range (12 - t.length)).map fun k => [6, 0, 7, 1].getD (k % 4) 0

def walkV2 (cube : Cube) (tape : List Nat) : Option Cube :=
  tape.foldlM symbolV2 cube

/-! ## Digest (SPEC "Digest") -/

/-- Corner slots and their sticker axes, in orientation order. -/
def cornerSlots : List (V3 × List V3) :=
  [(⟨1, 1, 1⟩, [⟨0, 1, 0⟩, ⟨1, 0, 0⟩, ⟨0, 0, 1⟩]),
   (⟨-1, 1, 1⟩, [⟨0, 1, 0⟩, ⟨0, 0, 1⟩, ⟨-1, 0, 0⟩]),
   (⟨-1, 1, -1⟩, [⟨0, 1, 0⟩, ⟨-1, 0, 0⟩, ⟨0, 0, -1⟩]),
   (⟨1, 1, -1⟩, [⟨0, 1, 0⟩, ⟨0, 0, -1⟩, ⟨1, 0, 0⟩]),
   (⟨1, -1, 1⟩, [⟨0, -1, 0⟩, ⟨0, 0, 1⟩, ⟨1, 0, 0⟩]),
   (⟨-1, -1, 1⟩, [⟨0, -1, 0⟩, ⟨-1, 0, 0⟩, ⟨0, 0, 1⟩]),
   (⟨-1, -1, -1⟩, [⟨0, -1, 0⟩, ⟨0, 0, -1⟩, ⟨-1, 0, 0⟩]),
   (⟨1, -1, -1⟩, [⟨0, -1, 0⟩, ⟨1, 0, 0⟩, ⟨0, 0, -1⟩])]

/-- Edge slots and their two sticker axes; orientation reads the first. -/
def edgeSlots : List (V3 × List V3) :=
  [(⟨1, 1, 0⟩, [⟨0, 1, 0⟩, ⟨1, 0, 0⟩]), (⟨0, 1, 1⟩, [⟨0, 1, 0⟩, ⟨0, 0, 1⟩]),
   (⟨-1, 1, 0⟩, [⟨0, 1, 0⟩, ⟨-1, 0, 0⟩]), (⟨0, 1, -1⟩, [⟨0, 1, 0⟩, ⟨0, 0, -1⟩]),
   (⟨1, -1, 0⟩, [⟨0, -1, 0⟩, ⟨1, 0, 0⟩]), (⟨0, -1, 1⟩, [⟨0, -1, 0⟩, ⟨0, 0, 1⟩]),
   (⟨-1, -1, 0⟩, [⟨0, -1, 0⟩, ⟨-1, 0, 0⟩]), (⟨0, -1, -1⟩, [⟨0, -1, 0⟩, ⟨0, 0, -1⟩]),
   (⟨1, 0, 1⟩, [⟨0, 0, 1⟩, ⟨1, 0, 0⟩]), (⟨-1, 0, 1⟩, [⟨0, 0, 1⟩, ⟨-1, 0, 0⟩]),
   (⟨-1, 0, -1⟩, [⟨0, 0, -1⟩, ⟨-1, 0, 0⟩]), (⟨1, 0, -1⟩, [⟨0, 0, -1⟩, ⟨1, 0, 0⟩])]

/-- Corner piece ids `0 … 7`, by the three colors on the piece. -/
def cornerTable : List (List Color) :=
  [[.W, .G, .R], [.W, .G, .O], [.W, .B, .O], [.W, .B, .R],
   [.Y, .G, .R], [.Y, .G, .O], [.Y, .B, .O], [.Y, .B, .R]]

/-- Edge piece ids `RW GW OW BW RY GY OY BY GR GO BO BR` = `0 … 11`. -/
def edgeTable : List (List Color) :=
  [[.R, .W], [.G, .W], [.O, .W], [.B, .W], [.R, .Y], [.G, .Y], [.O, .Y], [.B, .Y],
   [.G, .R], [.G, .O], [.B, .O], [.B, .R]]

/-- The id of the piece whose colors are `cols`, in any order. -/
def pieceId (table : List (List Color)) (cols : List Color) : Option Nat :=
  table.findIdx? fun s => decide (s.Perm cols)

def isUD (c : Color) : Bool := c = .W || c = .Y

/-- Corner orientation: which of the three axes, in slot order, carries W or Y. -/
def cornerOri (cols : List Color) : Option Nat := cols.findIdx? isUD

/-- Edge orientation bit of the first-axis sticker: `0` for W, Y, R, O, else `1`. -/
def edgeBit (c : Color) : Nat := if c = .W ∨ c = .Y ∨ c = .R ∨ c = .O then 0 else 1

def firstBit : List Color → Nat
  | c :: _ => edgeBit c
  | [] => 0

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- SPEC permutation rank, `Σ inv(n) · (len(p) - 1 - n)!`, where `inv(n)` counts the
    entries after index `n` smaller than `p[n]` (here peeled from the front). -/
def rank : List Nat → Nat
  | [] => 0
  | a :: t => t.countP (· < a) * fact t.length + rank t

/-- Little-endian digits in `base`: `Σ d[i] · base^i`. -/
def packLE (base : Nat) : List Nat → Nat
  | [] => 0
  | d :: ds => d + base * packLE base ds

/-- The last `w` base-256 digits of `n`, most significant first. -/
def beBytes (w n : Nat) : List Nat := (List.range w).reverse.map fun i => n / 256 ^ i % 256

/-- The colors of the cubie in slot `p`, read on `ax` in order. -/
def readSlot (cube : Cube) (slot : V3 × List V3) : Option (List Color) := do
  let c ← cubieAt cube slot.1
  slot.2.mapM (colorFacing c)

/-- SPEC "Digest": `cp`, `co` (first seven corner orientations, little-endian base 3),
    `ep`, `eo` (first eleven edge bits, little-endian base 2), then
    `s = ((rank cp · 2187 + co) · 239500800 + ⌊rank ep / 2⌋) · 2048 + eo` as 9 bytes,
    big-endian. -/
def digestOf (cube : Cube) : Option (List Nat) := do
  let cs ← cornerSlots.mapM (readSlot cube)
  let cp ← cs.mapM (pieceId cornerTable)
  let co ← (cs.take 7).mapM cornerOri
  let es ← edgeSlots.mapM (readSlot cube)
  let ep ← es.mapM (pieceId edgeTable)
  let eo := (es.take 11).map firstBit
  pure (beBytes 9 (((rank cp * 2187 + packLE 3 co) * 239500800 + rank ep / 2) * 2048 +
    packLE 2 eo))

/-- The v2 digest of a message: walk the padded tape from the solved cube, seat, read. -/
def digestV2? (msg : List Nat) : Option (List Nat) := do
  let c ← walkV2 solvedCube (padV2 (nybbles msg))
  let c ← seat c
  digestOf c

/-- `digestV2?` as a total function (`Link2` proves the `none` branch never fires). -/
def digestV2 (msg : List Nat) : List Nat := (digestV2? msg).getD []

end ScrambleV2
