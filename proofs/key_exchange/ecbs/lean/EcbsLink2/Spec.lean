/-
  ECBS: a hand-written model of `primitives/key_exchange/ecbs/SPEC.md` for the
  refinement in `EcbsLink2.Link2`. Written from the SPEC (tiers §1, the control-row
  ladder §2 / R6, calling coordinates §5.2, the d10 keypad §4, the fold §6). Numbers
  are `Nat`. A register is a `List Nat` of trits, hole 0 first. Nothing here is a
  security claim, and nothing here is the peg recipe for the curve walk.
-/

namespace EcbsLink2.Spec

/-- i64 upper bound as a `Nat`, the same literal as `MegaDreifach.Link2.i64MaxNat`. -/
def i64Bound : Nat := 9223372036854775807

/-- `n` fits in an i64. An `abbrev`, so `Decidable` for `≤` applies. -/
abbrev Fits (n : Nat) : Prop := n ≤ i64Bound

/-! ### §1 Tiers -/

/-- §1. One published tier. The numeric fields are the SPEC table; `name` is the
    ASCII bytes of the tier's name (what `tier` compares). -/
structure Tier where
  name : List Nat
  n : Nat
  k : Nat
  w : Nat
  h : Nat
  r : Nat
  benchlen : Nat
  combgap : Nat
  control : Nat
  script : Nat
  demo : Bool
  cells : Nat
  foldsrc : List Nat
  folddst : List Nat
  keeprows : Nat
  georows : Nat
  geoper : Nat
  geofirst : Nat
  geodouble : Bool
  geowork : Nat
  geokey : List Nat

def demoName : List Nat := [68, 101, 109, 111]
def toyName : List Nat := [84, 111, 121]
def hobbyName : List Nat := [72, 111, 98, 98, 121]
def seriousName : List Nat := [83, 101, 114, 105, 111, 117, 115]

/-- §1 Demo. -/
def demo : Tier :=
  { name := demoName, n := 7, k := 5, w := 2, h := 4, r := 1, benchlen := 20, combgap := 0,
    control := 16, script := 5, demo := true, cells := 2, foldsrc := [2, 3], folddst := [0, 1],
    keeprows := 2, georows := 4, geoper := 1, geofirst := 1, geodouble := false, geowork := 1,
    geokey := [2] }

/-- §1 Toy. -/
def toy : Tier :=
  { name := toyName, n := 23, k := 15, w := 8, h := 3, r := 1, benchlen := 72, combgap := 2,
    control := 40, script := 15, demo := false, cells := 16, foldsrc := [2], folddst := [0],
    keeprows := 2, georows := 3, geoper := 3, geofirst := 2, geodouble := false, geowork := 4,
    geokey := [5] }

/-- §1 Hobby. -/
def hobby : Tier :=
  { name := hobbyName, n := 59, k := 39, w := 20, h := 3, r := 1, benchlen := 180, combgap := 2,
    control := 80, script := 15, demo := false, cells := 51, foldsrc := [2], folddst := [0],
    keeprows := 2, georows := 3, geoper := 3, geofirst := 3, geodouble := true, geowork := 8,
    geokey := [9] }

/-- §1 Serious. -/
def serious : Tier :=
  { name := seriousName, n := 179, k := 59, w := 20, h := 9, r := 6, benchlen := 540,
    combgap := 2, control := 200, script := 15, demo := false, cells := 162,
    foldsrc := [5, 6, 7, 8], folddst := [0, 1, 2, 3], keeprows := 5, georows := 9, geoper := 1,
    geofirst := 7, geodouble := true, geowork := 20, geokey := [21, 22] }

def Tier.withScript (t : Tier) (script : Nat) : Tier := { t with script := script }

/-! ### §2 / R6 The halving ladder

`n − 1` pegs, paired off: a leftover (odd count) is a red rung (`2`), none is a white
rung (`1`); one peg of each pair is kept. Build order, first rung first. -/

def rungColour (c : Nat) : Nat := if c % 2 = 1 then 2 else 1

def rungList (c : Nat) : List Nat :=
  if c ≤ 1 then [] else rungColour c :: rungList (c / 2)
termination_by c
decreasing_by
  simp_wf
  exact Nat.div_lt_self (by omega) (by decide)

theorem rungList_le {c : Nat} (h : c ≤ 1) : rungList c = [] := by
  conv =>
    lhs
    unfold rungList
    rw [if_pos h]

theorem rungList_gt {c : Nat} (h : 1 < c) :
    rungList c = rungColour c :: rungList (c / 2) := by
  conv =>
    lhs
    unfold rungList
    rw [if_neg (show ¬ c ≤ 1 by omega)]

theorem rungList_length_le (c : Nat) : (rungList c).length ≤ c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    by_cases h : c ≤ 1
    · simp [rungList_le h]
    · rw [rungList_gt (by omega)]
      have hlt : c / 2 < c := Nat.div_lt_self (by omega) (by decide)
      have := ih (c / 2) hlt
      simp
      omega

/-- Moves added on one rung: the leftover peg plus one peg from each pair (`c / 2`). -/
def rungMoves (c : Nat) : Nat := c % 2 + c / 2

/-- Moves added by the halving itself, not the putting and clearing of the spare. -/
def halveMoves (c : Nat) : Nat :=
  if c ≤ 1 then 0 else rungMoves c + halveMoves (c / 2)
termination_by c
decreasing_by
  simp_wf
  exact Nat.div_lt_self (by omega) (by decide)

theorem halveMoves_le {c : Nat} (h : c ≤ 1) : halveMoves c = 0 := by
  conv =>
    lhs
    unfold halveMoves
    rw [if_pos h]

theorem halveMoves_gt {c : Nat} (h : 1 < c) :
    halveMoves c = rungMoves c + halveMoves (c / 2) := by
  conv =>
    lhs
    unfold halveMoves
    rw [if_neg (show ¬ c ≤ 1 by omega)]

theorem halveMoves_le_self (c : Nat) : halveMoves c ≤ c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    by_cases h : c ≤ 1
    · simp [halveMoves_le h]
    · rw [halveMoves_gt (by omega)]
      have hlt : c / 2 < c := Nat.div_lt_self (by omega) (by decide)
      have := ih (c / 2) hlt
      unfold rungMoves
      omega

/-- Pegs laid in the spare at the start of `new_board`: `n − 1` whites, then a zero.
    Length `n` for `n > 0`. -/
def sparePegs (n : Nat) : List Nat := List.replicate (n - 1) 1 ++ [0]

theorem sparePegs_length {n : Nat} (hn : 0 < n) : (sparePegs n).length = n := by
  unfold sparePegs
  simp
  omega

theorem nnz_sparePegs (n : Nat) :
    ((sparePegs n).filter (· ≠ 0)).length = n - 1 := by
  unfold sparePegs
  have h1 : (List.replicate (n - 1) 1).filter (· ≠ 0) = List.replicate (n - 1) 1 := by
    induction n - 1 with
    | zero => simp
    | succ k ih => simp [List.replicate_succ, ih]
  simp [h1]

/-- Ladder-section moves: put the spare, halve, clear the spare. Both the put and the
    clear count the `n − 1` whites. -/
def ladderMoves (n : Nat) : Nat := 2 * (n - 1) + halveMoves (n - 1)

/-! ### §5.2 Coordinates -/

/-- §5.2. A called hole: grid, row (`A = 0`), column (`1` is the first column). -/
structure Hole where
  grid : Nat
  row : Nat
  col : Nat

/-- Demo's lane of each home, then the homes that wrap to the lower half of the target. -/
def demoLanes : List Nat := [2, 3, 4, 5, 2, 3, 4]
def demoHalf : List Nat := [0, 0, 0, 0, 1, 1, 1]

/-- §5.2 `coordinate`. `home < 7` and `i < n`. Demo uses the fixed lane table; the other
    tiers use `geoper` bands per grid (per double grid when `geodouble`). -/
def coordinate (t : Tier) (home i : Nat) : Hole :=
  if t.demo then
    { grid := 1
      row := 4 * demoHalf.getD home 0 + i / 2
      col := 2 * demoLanes.getD home 0 - 1 + i % 2 }
  else
    let unit := home / t.geoper
    let band := home % t.geoper
    let r := i / t.w
    let c := i % t.w
    let row := band * t.georows + r
    if t.geodouble then
      let g := t.geofirst + 2 * unit + (if c ≥ 10 then 1 else 0)
      { grid := g, row := row, col := c % 10 + 1 }
    else
      { grid := t.geofirst + unit, row := row, col := c + 1 }

/-! ### §4 The d10 keypad -/

/-- §4. Keypad row of a face `1 .. 9` (top empty, middle white, bottom red). -/
def keypadFirst (face : Nat) : Nat := (face - 1) / 3

/-- §4. Keypad column of a face `1 .. 9` (left empty, middle white, right red). -/
def keypadSecond (face : Nat) : Nat := (face - 1) % 3

/-- The first face at or after index `i` that is not `0`, with the index just past it.
    `none` when every remaining face is `0` or the stream has run out. -/
def readFace (faces : List Nat) (i : Nat) : Option (Nat × Nat) :=
  if h : i < faces.length then
    if faces[i] = 0 then readFace faces (i + 1) else some (faces[i], i + 1)
  else none
termination_by faces.length - i
decreasing_by
  simp_wf
  omega

theorem readFace_ge {faces : List Nat} {i : Nat} (h : faces.length ≤ i) :
    readFace faces i = none := by
  conv =>
    lhs
    unfold readFace
    rw [dif_neg (show ¬ i < faces.length by omega)]

theorem readFace_zero {faces : List Nat} {i : Nat} (h : i < faces.length) (hz : faces[i] = 0) :
    readFace faces i = readFace faces (i + 1) := by
  conv =>
    lhs
    unfold readFace
    rw [dif_pos h, if_pos hz]

theorem readFace_pos {faces : List Nat} {i : Nat} (h : i < faces.length) (hz : faces[i] ≠ 0) :
    readFace faces i = some (faces[i], i + 1) := by
  conv =>
    lhs
    unfold readFace
    rw [dif_pos h, if_neg hz]

def writePair (cells : Nat) (acc : List Nat) (pair face : Nat) : List Nat :=
  let acc := acc.set (2 * pair) (keypadFirst face)
  if 2 * pair + 1 < cells then acc.set (2 * pair + 1) (keypadSecond face) else acc

/-- Fill `cells` holes, two per die, starting at face-index `next`. `none` if a die is
    required and the stream has run out (or every remaining face is `0`). -/
def fill (cells : Nat) (faces : List Nat) (next pair : Nat) (acc : List Nat) :
    Option (List Nat × Nat) :=
  if pair ≥ (cells + 1) / 2 then some (acc, next)
  else
    match readFace faces next with
    | none => none
    | some (f, next') => fill cells faces next' (pair + 1) (writePair cells acc pair f)
termination_by (cells + 1) / 2 - pair
decreasing_by
  simp_wf
  omega

def allZero (xs : List Nat) : Bool := xs.all (· = 0)

/-- One attempt, then the next if the cells came out empty. `attempt` starts at 1.
    `none` if a read runs out, or every attempt up to `faces.length + 1` was empty. -/
def rollGo (cells : Nat) (faces : List Nat) (attempt next : Nat) :
    Option (List Nat × Nat × Nat) :=
  if attempt > faces.length + 1 then none
  else
    match fill cells faces next 0 (List.replicate cells 0) with
    | none => none
    | some (cs, next') =>
      if allZero cs then rollGo cells faces (attempt + 1) next'
      else some (cs, next', attempt)
termination_by faces.length + 2 - attempt
decreasing_by
  simp_wf
  omega

/-- §4 `roll_key`. `cells` holes from the face stream. -/
def rollKey (cells : Nat) (faces : List Nat) : Option (List Nat × Nat × Nat) :=
  rollGo cells faces 1 0

/-! ### §6 The fold

Drop each source row onto the matching destination row, same column, in GF(3), reading
the original across. Then keep the first `keeprows` rows. -/

def add3 (a b : Nat) : Nat := (a + b) % 3

def dropCol (w : Nat) (x : List Nat) (src dst c : Nat) (out : List Nat) : List Nat :=
  let i := src * w + c
  let j := dst * w + c
  if h : i < x.length then
    if x[i] = 0 then out else out.set j (add3 (out.getD j 0) x[i])
  else out

def dropRow (w : Nat) (x : List Nat) (src dst : Nat) (out : List Nat) : List Nat :=
  (List.range w).foldl (fun out c => dropCol w x src dst c out) out

/-- §6. Drop each `(source row, destination row)` onto `out`, reading coefficients from
    the original `x` (not from `out`). -/
def foldRows (w : Nat) (x : List Nat) (pairs : List (Nat × Nat)) : List Nat :=
  pairs.foldl (fun out p => dropRow w x p.1 p.2 out) x

def foldKey (t : Tier) (x : List Nat) : List Nat :=
  (foldRows t.w x (t.foldsrc.zip t.folddst)).take (t.keeprows * t.w)

/-! ### Field arithmetic (SPEC §§3 R3–R5)

Schoolbook multiplication and the lane fold, as list operations. `fieldMul` / `fieldCube`
are what `multiply` and `cube_number` return when the emitted board procedure agrees
with these lists. They are not a hardness or extractor claim. -/

/-- Colour flip on a trit: empty stays empty, white ↔ red. -/
def flipTrit (c : Nat) : Nat := if c = 0 then 0 else 3 - c

def tritAdd (a b : Nat) : Nat := (a + b) % 3

def coeff (xs : List Nat) (i : Nat) : Nat := xs.getD i 0

/-- Lay one trit `d` (already flipped when the peg is red) onto hole `idx`. -/
def layCell (strip : List Nat) (idx d : Nat) : List Nat :=
  strip.set idx (tritAdd (coeff strip idx) d)

/-- One column of "lay this number from hole `i`": `j` runs through `0 .. n`. -/
def schoolStep (a : List Nat) (i : Nat) (mir : Bool) (strip : List Nat) (j : Nat) : List Nat :=
  let d := coeff a j
  if d = 0 then strip
  else layCell strip (i + j) (if mir then flipTrit d else d)

def schoolRow (n : Nat) (a : List Nat) (i : Nat) (mir : Bool) (strip : List Nat) : List Nat :=
  (List.range n).foldl (fun s j => schoolStep a i mir s j) strip

/-- Lift `second` from the high end. A red peg (`2`) mirrors `first` unless `mirror`
    already asked for a mirror, in which case the two agree and the peg is laid as is. -/
def school (n : Nat) (first second strip : List Nat) (mirror : Bool) : List Nat :=
  (List.range n).foldr (fun i st =>
      let c := coeff second i
      if c = 0 then st else schoolRow n first i (decide (c = 2) != mirror) st)
    strip

/-- One high peg of the lane fold: `x^e = x^{e-n} + x^{e-(n-k)}` in this basis.
    `gap = n - k`. A zero peg, or a peg still inside the number, is left alone. -/
def foldHigh (n gap e : Nat) (strip : List Nat) : List Nat :=
  let c := coeff strip e
  if c = 0 ∨ e < n then strip
  else
    let cleared := strip.set e 0
    let once := cleared.set (e - n) (tritAdd (coeff cleared (e - n)) c)
    once.set (e - gap) (tritAdd (coeff once (e - gap)) c)

/-- Fold every hole from the far end down through hole `n`. -/
def reduceStrip (n gap : Nat) (strip : List Nat) : List Nat :=
  (List.range (strip.length - n)).foldr (fun d st => foldHigh n gap (n + d) st) strip

/-- SPEC §3 R3, the lane fold: `reduceStrip` under `gap = n - k`. -/
def laneFold (n gap : Nat) (strip : List Nat) : List Nat :=
  reduceStrip n gap strip

/-- Highest nonzero hole, or `0` when the strip is empty or all zeros. The scan in `lane_fold`. -/
def topIdx (strip : List Nat) : Nat :=
  (List.range strip.length).foldl (fun t i => if coeff strip i = 0 then t else i) 0

/-- R4, `onto = false` and `mirror = false`: the product in the first `n` holes. -/
def fieldMul (n k bench : Nat) (x y : List Nat) : List Nat :=
  (reduceStrip n (n - k) (school n x y (List.replicate bench 0) false)).take n

/-- R5: `(∑ a_i X^i)^3 = ∑ a_i X^{3i}` before the same fold. -/
def combStrip (n bench : Nat) (x : List Nat) : List Nat :=
  (List.range n).foldl (fun s i =>
      let c := coeff x i
      if c = 0 then s else s.set (3 * i) c)
    (List.replicate bench 0)

def fieldCube (n k bench : Nat) (x : List Nat) : List Nat :=
  (reduceStrip n (n - k) (combStrip n bench x)).take n

/-! ### Lists -/

def nnz : List Int → Nat
  | [] => 0
  | x :: xs => (if x = 0 then 0 else 1) + nnz xs

def allEqZero (a : List Int) : Prop := ∀ x ∈ a, x = 0

def allTrits (a : List Int) : Prop := ∀ x ∈ a, 0 ≤ x ∧ x ≤ 2

/-! ### Phase and operation names (ASCII) -/

def phaseNames : List (List Nat) := [
  [98, 97, 115, 101, 32, 112, 111, 105, 110, 116],
  [111, 119, 110, 32, 119, 97, 108, 107],
  [115, 119, 97, 112],
  [99, 117, 114, 118, 101, 32, 116, 101, 115, 116],
  [109, 97, 107, 101, 32, 99, 101, 114, 116, 105, 102, 105, 99, 97, 116, 101],
  [114, 101, 98, 117, 105, 108, 100, 32, 116, 104, 101, 105, 114, 115],
  [115, 104, 97, 114, 101, 100, 32, 119, 97, 108, 107],
  [102, 111, 108, 100]]

def opNames : List (List Nat) := [
  [109, 117, 108],
  [99, 117, 98, 101],
  [105, 110, 118],
  [99, 104, 111, 114, 100],
  [102, 97, 100, 100]]

end EcbsLink2.Spec
