/-
  The v3 card phase E_m (SPEC v3 §5) as a typed Lean model: a transliteration of the v3 sudo
  (primitives/hash/megadreifach/v3/megadreifach.sudo, `lowest_nbr_index` .. `dm_step`), on the
  v2 position algebra (`MegaDreifach.Em`: `faceTurn`, `nbr`, `opp`, `cornerSlot`, `colourOn`,
  `edgeSlot`, `edgeFace`, `edgeColoursAt`, `cornerFace`, `compose`), which v3 keeps.

  The sudo's two piece searches (`edge_face_of`, `corner_face_of`) can trap (`assert slot >= 0`,
  `assert c1 == x`, `assert found >= 0`). The model keeps them as `Option` (`edgeFaceOf?`,
  `cornerFaceOf?`, `none` = the trap) and the card step reads them with `getD 0`; the Link 2
  theorems carry the side conditions under which they are `some` (bijective positions, and the
  finite check on the (c, k) ↦ (c, n, n2) triples in Link2/CardFacts.lean).

  A model of the sudo, not of the hand procedure. No claim about E_m beyond equality with the
  emitted code. No sorry. No native_decide.
-/
import MegaDreifach.Em

namespace MegaDreifachV3.Em

open MegaDreifach MegaDreifach.Em

/-- `echo_count` (SPEC v3 §5.4). -/
def echoCount : Nat := 26

/-- `lowest_nbr_index f`: index in `face_nbrs f` of its lowest neighbour (first on ties). -/
def lowestNbrIndex (f : Fin 12) : Nat :=
  [1, 2, 3, 4].foldl (fun best i => if (nbr f i).val < (nbr f best).val then i else best) 0

/-- `suit_nbrs c k`: the neighbour `k - 1` places clockwise of `c`'s lowest neighbour, and the
    next one clockwise. -/
def suitNbrs (c : Fin 12) (k : Nat) : Fin 12 × Fin 12 :=
  let i := lowestNbrIndex c
  (nbr c ((i + k - 1) % 5), nbr c ((i + k) % 5))

/-- Last index `s < n` with `p s` (the sudo's `for s: if ..: slot = s` scan); `none` if none. -/
def lastIdx (n : Nat) (p : Nat → Bool) : Option Nat :=
  (List.range n).foldl (fun acc s => if p s then some s else acc) none

/-- `edge_face_of g a b x`: the face carrying the `x`-coloured sticker of edge piece `(a, b)`.
    `none` is a trap of the emitted code. -/
def edgeFaceOf? (g : Position) (a b x : Fin 12) : Option (Fin 12) :=
  let piece := edgeSlot a b
  match lastIdx 30 (fun s => decide ((g.ep ⟨s % 30, Nat.mod_lt _ (by decide)⟩) = piece)) with
  | none => none
  | some slot =>
    let f0 := edgeFace slot 0
    let f1 := edgeFace slot 1
    let cs := edgeColoursAt g f0 f1
    if cs.1 = x then some f0 else if cs.2 = x then some f1 else none

/-- `corner_face_of g a b c x`: the face carrying the `x`-coloured sticker of corner piece
    `(a, b, c)`. `none` is a trap of the emitted code. -/
def cornerFaceOf? (g : Position) (a b c x : Fin 12) : Option (Fin 12) :=
  let piece := cornerSlot a b c
  match lastIdx 20 (fun s => decide ((g.cp ⟨s % 20, Nat.mod_lt _ (by decide)⟩) = piece)) with
  | none => none
  | some slot =>
    let f0 := cornerFace slot 0
    let f1 := cornerFace slot 1
    let f2 := cornerFace slot 2
    let p0 := cornerFace piece.val 0
    let p1 := cornerFace piece.val 1
    let p2 := cornerFace piece.val 2
    let ori := g.co ⟨slot % 20, Nat.mod_lt _ (by decide)⟩
    let r0 : Option (Fin 12) := if colourOn f0 f1 f2 p0 p1 p2 ori = x then some f0 else none
    let r1 : Option (Fin 12) := if colourOn f1 f1 f2 p0 p1 p2 ori = x then some f1 else r0
    if colourOn f2 f1 f2 p0 p1 p2 ori = x then some f2 else r1

def edgeFaceOf (g : Position) (a b x : Fin 12) : Fin 12 := (edgeFaceOf? g a b x).getD 0

def cornerFaceOf (g : Position) (a b c x : Fin 12) : Fin 12 := (cornerFaceOf? g a b c x).getD 0

/-- An E_m run: the position, the last face turned, and the SPEC v3 §5.6 cost counters. -/
structure Run where
  g : Position
  last : Fin 12
  turns : Nat
  clicks : Nat
  finds : Nat
  relooks : Nat
  registerLooks : Nat

def startRun (h : Position) : Run := ⟨h, 0, 0, 0, 0, 0, 0⟩

def turnRun (r : Run) (face : Fin 12) (amount : Nat) : Run :=
  ⟨faceTurn r.g face amount, face, r.turns + 1, r.clicks + amount, r.finds, r.relooks,
    r.registerLooks⟩

def countFind (r : Run) : Run := { r with finds := r.finds + 1 }

def countRelook (r : Run) : Run := { r with relooks := r.relooks + 1 }

def countRegisterLooks (r : Run) : Run := { r with registerLooks := r.registerLooks + 2 }

/-- The face a card step turns first: `base` counted up by `rank`, or `base`'s opposite for a
    King (`rank = 12`). -/
def turnedFace (base : Fin 12) (rank : Nat) : Fin 12 :=
  if rank < 12 then ⟨(base.val + rank) % 12, Nat.mod_lt _ (by decide)⟩ else opp base

/-- `card_step r base rank k c` (SPEC v3 §5.3). -/
def cardStep (r : Run) (base : Fin 12) (rank k : Nat) (c : Fin 12) : Run :=
  let r := turnRun r (turnedFace base rank) k
  let n := (suitNbrs c k).1
  let n2 := (suitNbrs c k).2
  let r := countFind r
  let r := turnRun r (edgeFaceOf r.g c n c) 1
  let r := turnRun r (edgeFaceOf r.g c n n) 1
  let r := countFind r
  let r := turnRun r (cornerFaceOf r.g c n n2 c) 1
  let r := turnRun r (cornerFaceOf r.g c n n2 n) 1
  let r := countRelook r
  turnRun r (edgeFaceOf r.g c n n) 1

/-- `card_colour card`: the rank's colour, Ace (0) for a King. -/
def cardColour (card : Nat) : Fin 12 :=
  if h : card / 4 < 12 then ⟨card / 4, h⟩ else 0

/-- `echo_colour g held` (SPEC v3 §5.4). -/
def echoColour (g : Position) (held : Nat) : Fin 12 :=
  let c := cardColour held
  let n := (suitNbrs c (held % 4 + 1)).1
  let n2 := (suitNbrs c (held % 4 + 1)).2
  let x := edgeFaceOf g c n n
  let y := cornerFaceOf g c n n2 n
  ⟨(x.val + y.val) % 12, Nat.mod_lt _ (by decide)⟩

/-- One card step of the 52-card phase: count up from the last face. -/
def dealStep (r : Run) (card : Nat) : Run :=
  cardStep r r.last (card / 4) (card % 4 + 1) (cardColour card)

/-- One echo of the held card: count up from the echo colour `P`. -/
def echoStep (held : Nat) (r : Run) : Run :=
  let p := echoColour r.g held
  cardStep (countRegisterLooks r) p (held / 4) (held % 4 + 1) p

/-- `n` echoes of `held`. -/
def echoRun (held : Nat) : Nat → Run → Run
  | 0, r => r
  | n + 1, r => echoRun held n (echoStep held r)

/-- `em_run h deal`: 52 card steps from `startRun h`, then `echoCount` echoes of `deal[51]`. -/
def emRun (h : Position) (deal : List Nat) : Run :=
  echoRun (deal.getD 51 0) echoCount ((deal.take 52).foldl dealStep (startRun h))

/-- `em_block h deal = em_run(h, deal).g` (E_m = W·h). -/
def emBlock (h : Position) (deal : List Nat) : Position := (emRun h deal).g

/-- `dm_step h deal`, the sudo's one Davies–Meyer step (used by `Hash`, `HashDeckBody` and
    `HashDeckBodyFrom`): `h' = compose h (E_m h deal)`. -/
def dmStep (h : Position) (deal : List Nat) : Position := compose h (emBlock h deal)

end MegaDreifachV3.Em
