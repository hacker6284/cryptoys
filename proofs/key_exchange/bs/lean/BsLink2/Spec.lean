/-
  BS: a hand-written model of the arithmetic of `primitives/key_exchange/bs/SPEC.md`
  (§2.3 parameters, §3 registers, B3 multiply, B5 tidy), written from the SPEC and not
  from `bs.sudo`. Numbers are `Nat`; a register is a `List Nat` of trits, hole 0 first,
  hole `i` worth `3^i` (§3). Nothing here is a security claim.
-/

namespace BsLink2.Spec

/-- §3. The value of a register: hole `i` is worth `3^i` (0 empty, 1 white, 2 red). -/
def value : List Nat → Nat
  | [] => 0
  | t :: ts => t + 3 * value ts

/-- §3. A register of `n` holes: `n` trits. -/
def IsReg (n : Nat) (x : List Nat) : Prop := x.length = n ∧ ∀ t ∈ x, t ≤ 2

/-- The register of `n` holes holding `v` (its `n` low base-3 digits, hole 0 first). -/
def toReg : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => v % 3 :: toReg n (v / 3)

/-- §2.3. A field `p = 3^n − c`; the toll `c` is given as a register, hole 0 first. -/
structure Field where
  n : Nat
  toll : List Nat

/-- §2.3. The toll `c`. -/
def Field.c (F : Field) : Nat := value F.toll

/-- §2.3. The modulus `p = 3^n − c`. -/
def Field.p (F : Field) : Nat := 3 ^ F.n - F.c

/-- §2.3 / B4. The domain the recipes are stated for: the toll is a non-empty trit
    register of fewer than `n` trits (so `c < 3^(n−1)`; SPEC §2.3 "Every toll has fewer
    than n trits"). Primality of `p` is not assumed anywhere below. -/
structure Field.Wf (F : Field) : Prop where
  toll_trits : ∀ t ∈ F.toll, t ≤ 2
  toll_pos : 0 < F.toll.length
  toll_lt : F.toll.length < F.n

/-- B5. The tidy answer (canonical form) of a register: its value reduced mod `p`, as a
    register of `n` holes. -/
def tidy (F : Field) (x : List Nat) : List Nat := toReg F.n (value x % F.p)

/-- B3. What a product must be. The SPEC's fold (B4) fixes one representative below
    `3^n` of `A · B · 3^nudge` mod `p`, but not by a closed formula, so the model of
    `multiply` is this relation: a register of `n` trits, below `3^n`, congruent to
    `A · B · 3^nudge` mod `p`. -/
def MulResult (F : Field) (a b : List Nat) (nudge : Nat) (out : List Nat) : Prop :=
  IsReg F.n out ∧ value out < 3 ^ F.n ∧ value out % F.p = value a * value b * 3 ^ nudge % F.p

/-- §2.3 tier T1 (skiff): `p = 3^18 − 3^2 − 1`, toll white at holes 0 and 2. -/
def T1 : Field := ⟨18, [1, 0, 1]⟩

/-- §2.3 tier T2 (frigate): `p = 3^35 − 3^29 − 1`, toll white at holes 0 and 29. -/
def T2 : Field := ⟨35, [1] ++ List.replicate 28 0 ++ [1]⟩

/-- §2.3 tier T6 (demo): `n = 100` and a 50-trit toll (`p = 3^100 − (π₅₀ + 4383)`). The
    digits are copied from `bs.sudo`. `BsLink2.TollPi` checks them against a rational
    bracket of π (Machin's formula, cited, not proved): see that file for exactly what is
    checked. -/
def T6 : Field := ⟨100, [1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 1, 1, 0, 2, 2, 2, 2, 2, 1, 2,
                        2, 0, 1, 1, 1, 1, 1, 2, 0, 0, 1, 1, 2, 0, 1, 0, 2, 2, 2, 2,
                        1, 0, 1, 1, 2, 0, 1, 0, 0, 1]⟩

/-- The SPEC §2.3 table's values of `p` for T1 and T2. -/
theorem T1_p : T1.p = 387420479 := by decide
theorem T2_p : T2.p = 49962914721634823 := by decide
theorem T1_p_formula : T1.p = 3 ^ 18 - 3 ^ 2 - 1 := by decide
theorem T2_p_formula : T2.p = 3 ^ 35 - 3 ^ 29 - 1 := by decide
theorem T1_wf : T1.Wf := ⟨by decide, by decide, by decide⟩
theorem T2_wf : T2.Wf := ⟨by decide, by decide, by decide⟩
theorem T6_wf : T6.Wf := ⟨by decide, by decide, by decide⟩

end BsLink2.Spec

namespace BsLink2.Spec

/-- §3.1. The sender's answer to a called hole. -/
inductive Shot where
  | hit
  | miss
  | misfire
  deriving DecidableEq, Repr

/-- §3.1: red "Hit!", white "Miss!", empty "Misfire!". -/
def answer : Nat → Shot
  | 2 => .hit
  | 1 => .miss
  | _ => .misfire

/-- §3.1. Sending a public value `x`: the receiver calls every hole from 0 to `n − 1`
    (a fixed `n` calls) and copies each answer into the same hole of a cleared Y, so the
    answers are `x`'s holes read as shots and Y ends up holding `x`. -/
def sendPublicValue (x : List Nat) : List Shot × List Nat := (x.map answer, x)

end BsLink2.Spec

namespace BsLink2.Spec

/-- B7. The exponent a cell string encodes: the cells read as a base-3 number, first
    cell most significant (cells before the first white or red one contribute nothing). -/
def expOf (cells : List Nat) : Nat := cells.foldl (fun e c => 3 * e + c) 0

/-- B7, public phase: the tidy answer of the walk with `g = 3` over `cells`, i.e. the
    register holding `3^e mod p`. -/
def publicValue (F : Field) (cells : List Nat) : List Nat := toReg F.n (3 ^ expOf cells % F.p)

/-- B7, shared phase: the tidy answer of the walk with base `C` over `cells`, i.e. the
    register holding `C^e mod p`. -/
def sharedSecret (F : Field) (base cells : List Nat) : List Nat :=
  toReg F.n (value base ^ expOf cells % F.p)

end BsLink2.Spec

namespace BsLink2.Spec

/-- B8. Checking a received number: it must have exactly `n` trits; square it and tidy
    (C = R·R mod p); reject (`none`) if C is empty (0) or a lone white in hole 0 (1);
    otherwise C is the base. -/
def checkReceived (F : Field) (r : List Nat) : Option (List Nat) :=
  if r.length = F.n ∧ ∀ t ∈ r, t ≤ 2 then
    if value r * value r % F.p = 0 ∨ value r * value r % F.p = 1 then none
    else some (toReg F.n (value r * value r % F.p))
  else none

end BsLink2.Spec

namespace BsLink2.Spec

/-- B9. The key both players should end with: `K = 3^(2·a·b) mod p`, as a register, where
    `a` and `b` are the exponents of Alice's and Bob's cell strings. -/
def exchangeKey (F : Field) (cellsA cellsB : List Nat) : List Nat :=
  toReg F.n (3 ^ (2 * expOf cellsA * expOf cellsB) % F.p)

end BsLink2.Spec

namespace BsLink2.Spec

/-! ### §4.1 and §4.3: the key grid and READ ("ships, then pegs")

A key grid is 10 × 10 holes in reading order (row A to J = 0 to 9, holes 1 to 10 = columns
0 to 9); hole `(row, col)` is index `10 · row + col`. -/

/-- §4.1. Every kind has its own piece: Destroyer (2 holes), Sub (3), Cruiser (3),
    Battleship (4), Carrier (5). -/
inductive Kind where
  | destroyer
  | sub
  | cruiser
  | battleship
  | carrier
  deriving DecidableEq, Repr

/-- §4.1. How many holes a piece plugs into. -/
def Kind.len : Kind → Nat
  | .destroyer => 2
  | .sub => 3
  | .cruiser => 3
  | .battleship => 4
  | .carrier => 5

/-- §4.1. A ship: its kind, whether it lies down (else across), the row and column of its
    first hole (the one reached first in reading order), and whether its bow is at its
    last hole ("points on") rather than its first ("points back"). -/
structure Ship where
  kind : Kind
  down : Bool
  row : Nat
  col : Nat
  bowLast : Bool
  deriving DecidableEq, Repr

/-- Reading-order distance between neighbouring holes of the ship. -/
def Ship.step (s : Ship) : Nat := if s.down then 10 else 1

/-- §4.1. The ship's first hole. -/
def Ship.first (s : Ship) : Nat := 10 * s.row + s.col

/-- The holes the ship covers, first hole first. -/
def Ship.holes (s : Ship) : List Nat := (List.range s.kind.len).map (fun t => s.first + t * s.step)

/-- §4.1. The ship's last hole. -/
def Ship.last (s : Ship) : Nat := s.first + (s.kind.len - 1) * s.step

/-- The ship lies on the 10 × 10 grid. -/
def Ship.OnGrid (s : Ship) : Prop :=
  if s.down then s.col < 10 ∧ s.row + s.kind.len ≤ 10 else s.row < 10 ∧ s.col + s.kind.len ≤ 10

/-- §4.1. A key grid (one page): its fleet and the peg in each of its 100 holes, in
    reading order (0 no peg, 1 white, 2 red). -/
structure Grid where
  ships : List Ship
  pegs : List Nat

/-- §4.1 / §4.2. A key grid as the SPEC describes it: every ship lies on the grid, no two
    ships share a hole ("they never overlap"), and every one of the 100 holes has one
    3-state peg. -/
structure Grid.Wf (g : Grid) : Prop where
  onGrid : ∀ s ∈ g.ships, s.OnGrid
  disjoint : g.ships.Pairwise (fun a b => ∀ h ∈ a.holes, h ∉ b.holes)
  pegs_len : g.pegs.length = 100
  pegs_trits : ∀ t ∈ g.pegs, t ≤ 2

/-- §4.3, the ship pass at hole `h`: no ship, or a ship's middle hole, is a plain cell;
    a ship's first hole is white if it lies across, red if down; its last hole is white
    if it points back, red if it points on, and then one more cell for a Sub (plain) or a
    Cruiser (white). -/
def holeCells (ships : List Ship) (h : Nat) : List Nat :=
  match ships.find? (fun s => decide (h ∈ s.holes)) with
  | none => [0]
  | some s =>
    if h = s.first then [if s.down then 2 else 1]
    else if h = s.last then
      [if s.bowLast then 2 else 1] ++
        (match s.kind with
         | .sub => [0]
         | .cruiser => [1]
         | _ => [])
    else [0]

/-- §4.3, the ship pass of one page, one hole at a time in reading order (the start
    marker is not part of a page). -/
def shipPass (g : Grid) : List Nat := (List.range 100).flatMap (holeCells g.ships)

/-- §4.3, the peg pass: one cell per hole in reading order, the peg's colour. -/
def pegPass (g : Grid) : List Nat := g.pegs

/-- §4.3 READ: the start marker (a white cell, once for the whole key), then every page's
    ship pass and peg pass. Read as a base-3 numeral, first cell most significant, this
    is the exponent of §4.4 (`expOf`). -/
def readKey (pages : List Grid) : List Nat :=
  1 :: pages.flatMap (fun g => shipPass g ++ pegPass g)

end BsLink2.Spec

namespace BsLink2.Spec

/-! ### B9: the exchange, with its two reject branches -/

/-- B9. What a completed exchange records: both public values, the shots each sender
    answered and what each receiver's Y ended up holding, both bases and both secrets. -/
structure ExchangeRecord where
  publicA : List Nat
  publicB : List Nat
  shotsA : List Shot
  receivedA : List Nat
  shotsB : List Shot
  receivedB : List Nat
  baseA : List Nat
  baseB : List Nat
  secretA : List Nat
  secretB : List Nat

/-- B8 reject text when Alice's check of Bob's value fails (as `bs.sudo` spells it). -/
def aliceRejects : String := "B8: Alice rejects Bob's value"

/-- B8 reject text when Bob's check of Alice's value fails (as `bs.sudo` spells it). -/
def bobRejects : String := "B8: Bob rejects Alice's value"

/-- B9 over the two cell strings. Each player publishes `3^e mod p` (B7) and sends it to
    the other (§3.1); each checks what it received (B8). Alice's check of Bob's value is
    looked at first, so if both checks fail the result is Alice's rejection. If both pass,
    each walks over the base it got (B7, shared phase). -/
def exchangeCells (F : Field) (ca cb : List Nat) : Except String ExchangeRecord :=
  let pa := publicValue F ca
  let pb := publicValue F cb
  match checkReceived F pb, checkReceived F pa with
  | none, _ => .error aliceRejects
  | some _, none => .error bobRejects
  | some ba, some bb =>
    .ok { publicA := pa, publicB := pb,
          shotsA := (sendPublicValue pa).1, receivedA := (sendPublicValue pa).2,
          shotsB := (sendPublicValue pb).1, receivedB := (sendPublicValue pb).2,
          baseA := ba, baseB := bb,
          secretA := sharedSecret F ba ca, secretB := sharedSecret F bb cb }

/-- B9 from the two keys: each key is read by §4.3 first. -/
def exchange (F : Field) (keyA keyB : List Grid) : Except String ExchangeRecord :=
  exchangeCells F (readKey keyA) (readKey keyB)

end BsLink2.Spec

namespace BsLink2.Spec

/-! ### §4.2: the dice a build reads -/

/-- §4.2. The dice a build reads: the faces of the hole die (d12), the d6 and the row-cup
    d10s, each stream in the order thrown, and how many faces of each have been read. The
    faces are arbitrary integers here; the build checks each face it reads. -/
structure Dice where
  d12 : List Int
  d6 : List Int
  d10 : List Int
  next12 : Nat
  next6 : Nat
  next10 : Nat

/-- §4.2. Fresh dice: nothing read yet. -/
def dice (d12 d6 d10 : List Int) : Dice := ⟨d12, d6, d10, 0, 0, 0⟩

end BsLink2.Spec
