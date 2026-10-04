/-
  BS: a hand-written model of `primitives/key_exchange/bs/SPEC.md` (§2.3 parameters, §3
  registers, §3.1 sending, B3 multiply, B5 tidy, B7 to B9 the walk, the received-value
  check and the exchange, §4.1 / §4.3 the key grid and READ, §4.2 the dice and BUILD), written from
  the SPEC and not from `bs.sudo` (where `bs.sudo` fixes something the SPEC leaves open,
  the docstring says so). Numbers are `Nat`; a register is a `List Nat` of trits, hole 0 first,
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

/-! ### §3.1: sending a public value -/

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

/-! ### B7: the walk's exponent, public value and shared secret -/

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

/-! ### B8: checking a received value -/

/-- B8. Checking a received number: it must have exactly `n` trits; square it and tidy
    (C = R·R mod p); reject (`none`) if C is empty (0) or a lone white in hole 0 (1);
    otherwise C is the base. -/
def checkReceived (F : Field) (r : List Nat) : Option (List Nat) :=
  if r.length = F.n ∧ ∀ t ∈ r, t ≤ 2 then
    if value r * value r % F.p = 0 ∨ value r * value r % F.p = 1 then none
    else some (toReg F.n (value r * value r % F.p))
  else none

/-! ### B9: the exchange key -/

/-- B9. The key both players should end with: `K = 3^(2·a·b) mod p`, as a register, where
    `a` and `b` are the exponents of Alice's and Bob's cell strings. -/
def exchangeKey (F : Field) (cellsA cellsB : List Nat) : List Nat :=
  toReg F.n (3 ^ (2 * expOf cellsA * expOf cellsB) % F.p)

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

/-- The ship (among `ships`) covering hole `h`, if any. -/
def shipAt (ships : List Ship) (h : Nat) : Option Ship := ships.find? (fun s => decide (h ∈ s.holes))

/-- §4.3, the ship pass at hole `h`: no ship, or a ship's middle hole, is a plain cell;
    a ship's first hole is white if it lies across, red if down; its last hole is white
    if it points back, red if it points on, and then one more cell for a Sub (plain) or a
    Cruiser (white). -/
def holeCells (ships : List Ship) (h : Nat) : List Nat :=
  match shipAt ships h with
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

theorem Kind.two_le_len (k : Kind) : 2 ≤ k.len := by cases k <;> decide

theorem Kind.len_le_five (k : Kind) : k.len ≤ 5 := by cases k <;> decide

/-- §4.1 / §4.2: a key is one or more well-formed pages. -/
def KeyWf (pages : List Grid) : Prop := pages ≠ [] ∧ ∀ g ∈ pages, g.Wf

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
    looked at first, so if both checks fail the result is Alice's rejection: that order is
    `bs.sudo`'s, not something SPEC B9 fixes. If both pass,
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

/-! ### §4.2 BUILD, "one hole at a time: ship, then peg"

The build reads three face streams (`Dice`). A key grid is built in one sitting, without
letting go (SPEC §4.2), so there is no let-go input. The theorems about it hold for each
dice separately. It is partial (`Option`): it fails when a stream runs out or shows a face
off its die, or when a tray has no unread die. No probability is modelled. -/

/-- §4.2 step 1: roll the hole die (d12), faces 1–12. Fails if the stream has run out or
    the face is off the die. -/
def rollHole (d : Dice) : Option (Nat × Dice) :=
  match d.d12[d.next12]? with
  | none => none
  | some f => if 1 ≤ f ∧ f ≤ 12 then some (f.toNat, { d with next12 := d.next12 + 1 }) else none

/-- §4.2 step 1: roll the d6, faces 1–6. -/
def rollD6 (d : Dice) : Option (Nat × Dice) :=
  match d.d6[d.next6]? with
  | none => none
  | some f => if 1 ≤ f ∧ f ≤ 6 then some (f.toNat, { d with next6 := d.next6 + 1 }) else none

/-- One row-cup d10 from the faces `fs` (starting at stream position `t`): a zero face is
    thrown again; the first face 1–9 is the die's. Fails on a face off the die (0–9) or when
    the stream runs out first. Returns the face and the next stream position. -/
def d10Scan : List Int → Nat → Option (Nat × Nat)
  | [], _ => none
  | f :: fs, t =>
    if 0 ≤ f ∧ f ≤ 9 then (if f = 0 then d10Scan fs (t + 1) else some (f.toNat, t + 1))
    else none

/-- §4.2 step 0: throw one row-cup d10 until it shows 1–9. -/
def throwD10 (d : Dice) : Option (Nat × Dice) :=
  (d10Scan (d.d10.drop d.next10) d.next10).map (fun p => (p.1, { d with next10 := p.2 }))

/-- §4.2 step 0: throw the row cup, five d10s in rainbow order; the tray holds their faces. -/
def throwRowCup (d : Dice) : Option (List Nat × Dice) :=
  (List.range 5).foldlM (fun (acc : List Nat × Dice) _ =>
    (throwD10 acc.2).map (fun p => (acc.1 ++ [p.1], p.2))) ([], d)

/-- §4.2 step 2, the keypad (1 2 3 / 4 5 6 / 7 8 9): the row of the face is the peg of the
    pair's first hole (0 none, 1 white, 2 red). For faces 1–9. -/
def keypadFirst (f : Nat) : Nat := (f - 1) / 3

/-- §4.2 step 2: the column of the face is the peg of the pair's second hole,
    `(f − 1) mod 3`, written `(f + 2) mod 3` (the same for faces 1–9). -/
def keypadSecond (f : Nat) : Nat := (f + 2) % 3

/-- §4.2 step 1: a heading "has room for a Destroyer" when the next hole that way is on the
    grid and not under a ship (`cov`: the holes ships cover). -/
def hasRoom (cov : Nat → Bool) (row col : Nat) : Bool :=
  decide (row < 10) && decide (col < 10) && !cov (row * 10 + col)

/-- §4.2 step 1, growing: from `len` holes, while there is room for one more hole roll the
    d6: from 2 holes it grows on 4–6, from 3 and 4 only on a 6. At most three growths
    (`fuel`): Destroyer → 3-holer → Battleship → Carrier. Returns the dice and the length. -/
def growLoop (cov : Nat → Bool) (row col : Nat) (down : Bool) :
    Nat → Dice → Nat → Option (Dice × Nat)
  | 0, d, len => some (d, len)
  | fuel + 1, d, len =>
    if hasRoom cov (if down then row + len else row) (if down then col else col + len) then
      match rollD6 d with
      | none => none
      | some (f, d') =>
        if (if len = 2 then 4 else 6) ≤ f then growLoop cov row col down fuel d' (len + 1)
        else some (d', len)
    else some (d, len)

/-- §4.2 step 1, the piece of a grown length; a 3-holer rolls the d6: 1–3 Sub, 4–6
    Cruiser. -/
def pieceOf (len : Nat) (d : Dice) : Option (Kind × Dice) :=
  if len = 3 then (rollD6 d).map (fun p => (if p.1 ≤ 3 then .sub else .cruiser, p.2))
  else if len = 4 then some (.battleship, d)
  else if len = 5 then some (.carrier, d)
  else some (.destroyer, d)

/-- §4.2 step 1 once the heading is chosen: the bow from the hole die's parity (even: bow
    at the far end), a Destroyer grown until it bumps, then its piece. -/
def layShip (cov : Nat → Bool) (row col : Nat) (d : Dice) (face : Nat) (down : Bool) :
    Option (Option Ship × Dice) :=
  match growLoop cov row col down 3 d 2 with
  | none => none
  | some (d, len) =>
    (pieceOf len d).map (fun p =>
      (some { kind := p.1, down := down, row := row, col := col, bowLast := face % 2 = 0 },
       p.2))

/-- §4.2 step 1, "grow until it bumps", at an uncovered hole: neither heading has room, sea
    with no roll; both, the hole die 1–4 sea, 5–8 across, 9–12 down; only one, 1–6 sea,
    7–12 a ship in the open heading. Returns the ship laid (`none`: sea) and the dice. -/
def growUntilItBumps (d : Dice) (cov : Nat → Bool) (row col : Nat) :
    Option (Option Ship × Dice) :=
  let across := hasRoom cov row (col + 1)
  let down := hasRoom cov (row + 1) col
  if !across && !down then some (none, d)
  else
    match rollHole d with
    | none => none
    | some (face, d) =>
      if across && down then
        (if face ≤ 4 then some (none, d) else layShip cov row col d face (decide (9 ≤ face)))
      else
        (if face ≤ 6 then some (none, d) else layShip cov row col d face down)

/-- Covering the holes of a ship. -/
def cover (cov : Nat → Bool) (s : Ship) : Nat → Bool := fun h => cov h || decide (h ∈ s.holes)

/-- Setting one hole's peg. -/
def setPeg (pegs : Nat → Nat) (h v : Nat) : Nat → Nat := fun x => if x = h then v else pegs x

/-- BUILD's state as the cursor walks: the dice, the tray and how many of its dice are
    read, the covered holes, the ships laid, the face of the current pair, the pegs. -/
structure BuildSt where
  dice : Dice
  tray : List Nat
  read : Nat
  covered : Nat → Bool
  ships : List Ship
  face : Nat
  pegs : Nat → Nat

/-- §4.2 step 0: at the start of a row (`col = 0`) throw the row cup; nothing read yet. -/
def rowCupAt (col : Nat) (st : BuildSt) : Option BuildSt :=
  if col = 0 then
    (throwRowCup st.dice).map (fun p => { st with dice := p.2, tray := p.1, read := 0 })
  else some st

/-- §4.2 step 1: if no ship covers the hole, grow until it bumps; a ship laid covers its
    holes and joins the fleet. -/
def growAt (row col : Nat) (st : BuildSt) : Option BuildSt :=
  if !st.covered (row * 10 + col) then
    (growUntilItBumps st.dice st.covered row col).map (fun p =>
      match p.1 with
      | some s => { st with dice := p.2, covered := cover st.covered s, ships := st.ships ++ [s] }
      | none => { st with dice := p.2 })
  else some st

/-- §4.2 step 2: peg hole `h` from its pair's die. The first hole of a pair (`col` even)
    reads the next tray die and takes the keypad row; the second takes the column. Fails
    when the tray has no unread die. -/
def pegAt (h col : Nat) (st : BuildSt) : Option BuildSt :=
  if col % 2 = 0 then
    st.tray[st.read]?.map (fun f =>
      { st with face := f, read := st.read + 1, pegs := setPeg st.pegs h (keypadFirst f) })
  else some { st with pegs := setPeg st.pegs h (keypadSecond st.face) }

/-- §4.2, one hole (`row`, `col`), `h = 10·row + col`: the row cup, grow, peg. -/
def holeStep (row col : Nat) (st : BuildSt) : Option BuildSt :=
  (rowCupAt col st).bind fun st =>
  (growAt row col st).bind (pegAt (row * 10 + col) col)

/-- One row: its ten holes in order, the pair face starting at 0. -/
def rowStep (row : Nat) (st : BuildSt) : Option BuildSt :=
  (List.range 10).foldlM (fun st col => holeStep row col st) { st with face := 0 }

/-- §4.2 BUILD, in one sitting: from an empty grid and an empty tray, the ten rows in
    order. Returns the key grid and the dice left. -/
def build (d : Dice) : Option (Grid × Dice) :=
  ((List.range 10).foldlM (fun st row => rowStep row st)
    ({ dice := d, tray := [], read := 0, covered := fun _ => false, ships := [], face := 0,
       pegs := fun _ => 0 } : BuildSt)).map
    (fun st => (⟨st.ships, (List.range 100).map st.pegs⟩, st.dice))

/-- A built key grid and how many faces of each die it read (the read counts of the dice
    after the build). -/
structure Built where
  grid : Grid
  used12 : Nat
  used6 : Nat
  used10 : Nat

/-- §4.2 BUILD from the given dice, with the read counts. -/
def buildKeyGrid (d : Dice) : Option Built :=
  (build d).map (fun p => ⟨p.1, p.2.next12, p.2.next6, p.2.next10⟩)

end BsLink2.Spec
