/-
  SECURITY. Two-turn read-word injectivity for MegaDreifach v3.

  Plan item C of A(b) → A(a) → C → B. A(b) is the same-`h` cancellation and A(a) is the
  constructive MD extractor; both are on main. This file does not start B (full
  `card_step` injectivity).

  What is proved: the Lean form of the sudo test "read words" (SPEC v3 §5.8). For every
  edge piece and every ordered pair of its colours, the 60 placements (30 slots × 2
  orientations) give 60 distinct two-turn words, and the same for every corner piece and
  every ordered pair of distinct colours among its three faces (20 slots × 3 orientations).
  The placement is the sudo's: on the identity, swap the piece's home slot with the target
  slot and set the target orientation. The word is
  `faceTurn (faceTurn identity f1 1) f2 1`, where `f1` is the face carrying the first
  colour and `f2` is the face carrying the second colour after that one turn.

  The distinctness check is one kernel `decide!` per piece and colour order
  (`edgeGroup_ok`, `cornerGroup_ok`), assembled into `edgeAll_ok` and `cornerAll_ok`.
  `posCode` is injective, so distinct codes are distinct positions.

  Link 2 already has `edge_face_of_refines`, `corner_face_of_refines` and
  `face_turn_refines`. On these placements the searches return `some`
  (`edgeFaceOf_found`, `cornerFaceOf_found`, using `InjPos` of the swap, kept by
  `faceTurn`), so the emitted `edge_face_of` / `corner_face_of` / `face_turn` / `identity`
  return the embedding of the model word. Injectivity transfers along `embedPos`.

  This is not ANALYSIS P2 (every input difference changes the turn sequence). It is not
  collision resistance and not a PRF claim. SPEC and ANALYSIS tags are unchanged.
  Zero sorry. Kernel `decide!`, not `native_decide`.
-/
import MegaDreifachV3.Link2.FaceOfFound
import MegaDreifachV3.Link2.Shared

namespace MegaDreifachV3.Security

open MegaDreifach MegaDreifach.Em MegaDreifachV3.Em MegaDreifach.Link2 MegaDreifachV3.Link2

-- Per-group `decide!` proofs are one kernel reduction each. Later folds must not
-- re-reduce them under the default heartbeat cap.
set_option maxHeartbeats 0

/-! ## The sudo's placement and the two-turn word -/

/-- Swap edge piece `p` into slot `s` at orientation `o` on the identity, as the sudo
    test does: `ep[p] := ep[s]`, `eo[p] := 0`, `ep[s] := p`, `eo[s] := o`. -/
def placeEdge (p s : Fin 30) (o : Fin 2) : Position where
  cp := identity.cp
  co := identity.co
  ep := fun i => if i = s then p else if i = p then s else i
  eo := fun i => if i = s then o else 0

/-- Swap corner piece `p` into slot `s` at twist `o` on the identity. -/
def placeCorner (p s : Fin 20) (o : Fin 3) : Position where
  cp := fun i => if i = s then p else if i = p then s else i
  co := fun i => if i = s then o else 0
  ep := identity.ep
  eo := identity.eo

/-- `face_turn (face_turn identity f1 1) f2 1`, the sudo's two-turn read word. -/
def twoTurnWord (f1 f2 : Fin 12) : Position :=
  faceTurn (faceTurn identity f1 1) f2 1

/-- Edge read word for piece `p`. `order = 0` reads colours
    `(edgeFace p 0, edgeFace p 1)`; `order = 1` reads them swapped. -/
def edgeReadWord (p : Fin 30) (order : Fin 2) (s : Fin 30) (o : Fin 2) : Position :=
  let a := edgeFace p.val 0
  let b := edgeFace p.val 1
  let x := if order = 0 then a else b
  let y := if order = 0 then b else a
  let g := placeEdge p s o
  let f1 := edgeFaceOf g a b x
  let f2 := edgeFaceOf (faceTurn g f1 1) a b y
  twoTurnWord f1 f2

/-- Corner read word for piece `p` and colour indices `i1` then `i2` into
    `cornerFace p`. -/
def cornerReadWord (p : Fin 20) (i1 i2 : Fin 3) (s : Fin 20) (o : Fin 3) : Position :=
  let a := cornerFace p.val 0
  let b := cornerFace p.val 1
  let c := cornerFace p.val 2
  let col (j : Fin 3) : Fin 12 := cornerFace p.val j.val
  let g := placeCorner p s o
  let f1 := cornerFaceOf g a b c (col i1)
  let f2 := cornerFaceOf (faceTurn g f1 1) a b c (col i2)
  twoTurnWord f1 f2

/-! ## Codes of positions, and the finite distinctness check -/

/-- The four cubie tables, in order. Equal codes are equal positions. -/
def posCode (g : Position) : List Nat :=
  listOf g.cp ++ listOfOri g.co ++ listOf g.ep ++ listOfOri g.eo

def codesDistinct : List (List Nat) → Bool
  | [] => true
  | c :: cs => !(cs.any (· == c)) && codesDistinct cs

def edgeCodes (p : Fin 30) (order : Fin 2) : List (List Nat) :=
  (List.range 60).map fun i =>
    if hi : i < 60 then
      posCode (edgeReadWord p order ⟨i / 2, by omega⟩ ⟨i % 2, Nat.mod_lt _ (by decide)⟩)
    else []

def cornerCodes (p : Fin 20) (i1 i2 : Fin 3) : List (List Nat) :=
  (List.range 60).map fun i =>
    if hi : i < 60 then
      posCode (cornerReadWord p i1 i2 ⟨i / 3, by omega⟩ ⟨i % 3, Nat.mod_lt _ (by decide)⟩)
    else []

def edgeGroup (p : Fin 30) (order : Fin 2) : Bool :=
  codesDistinct (edgeCodes p order)

def cornerGroup (p : Fin 20) (i1 i2 : Fin 3) : Bool :=
  if i1 = i2 then true else codesDistinct (cornerCodes p i1 i2)

def edgeAll : Bool :=
  (List.range 30).all fun p =>
    if hp : p < 30 then
      (List.range 2).all fun o =>
        if ho : o < 2 then edgeGroup ⟨p, hp⟩ ⟨o, ho⟩ else true
    else true

def cornerAll : Bool :=
  (List.range 20).all fun p =>
    if hp : p < 20 then
      (List.range 3).all fun i1 =>
        if h1 : i1 < 3 then
          (List.range 3).all fun i2 =>
            if h2 : i2 < 3 then cornerGroup ⟨p, hp⟩ ⟨i1, h1⟩ ⟨i2, h2⟩ else true
        else true
    else true

set_option maxHeartbeats 0 in
/-- One piece and one ordered colour pair: the 60 edge states have distinct read-word codes.
    Each `decide!` is a single group, so the kernel does not reduce every piece at once. -/
theorem edgeGroup_ok (p : Fin 30) (order : Fin 2) : edgeGroup p order = true := by
  have hp : p.val = 0 ∨ p.val = 1 ∨ p.val = 2 ∨ p.val = 3 ∨ p.val = 4 ∨ p.val = 5 ∨ p.val = 6 ∨ p.val = 7 ∨ p.val = 8 ∨ p.val = 9 ∨ p.val = 10 ∨ p.val = 11 ∨ p.val = 12 ∨ p.val = 13 ∨ p.val = 14 ∨ p.val = 15 ∨ p.val = 16 ∨ p.val = 17 ∨ p.val = 18 ∨ p.val = 19 ∨ p.val = 20 ∨ p.val = 21 ∨ p.val = 22 ∨ p.val = 23 ∨ p.val = 24 ∨ p.val = 25 ∨ p.val = 26 ∨ p.val = 27 ∨ p.val = 28 ∨ p.val = 29 := by have := p.isLt; omega
  have ho : order.val = 0 ∨ order.val = 1 := by have := order.isLt; omega
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp <;> rcases ho with ho | ho
  · rw [show p = 0 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 0 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 1 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 1 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 2 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 2 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 3 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 3 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 4 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 4 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 5 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 5 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 6 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 6 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 7 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 7 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 8 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 8 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 9 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 9 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 10 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 10 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 11 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 11 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 12 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 12 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 13 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 13 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 14 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 14 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 15 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 15 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 16 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 16 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 17 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 17 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 18 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 18 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 19 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 19 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 20 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 20 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 21 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 21 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 22 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 22 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 23 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 23 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 24 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 24 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 25 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 25 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 26 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 26 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 27 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 27 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 28 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 28 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!
  · rw [show p = 29 from Fin.ext hp, show order = 0 from Fin.ext ho]
    decide!
  · rw [show p = 29 from Fin.ext hp, show order = 1 from Fin.ext ho]
    decide!

set_option maxHeartbeats 0 in
/-- One corner and one ordered pair of distinct colours: the 60 states have distinct
    read-word codes. Equal colour indices are the sudo's skipped pairs (`i1 ≠ i2`). -/
theorem cornerGroup_ok (p : Fin 20) (i1 i2 : Fin 3) (hne : i1 ≠ i2) :
    cornerGroup p i1 i2 = true := by
  have hp : p.val = 0 ∨ p.val = 1 ∨ p.val = 2 ∨ p.val = 3 ∨ p.val = 4 ∨ p.val = 5 ∨ p.val = 6 ∨ p.val = 7 ∨ p.val = 8 ∨ p.val = 9 ∨ p.val = 10 ∨ p.val = 11 ∨ p.val = 12 ∨ p.val = 13 ∨ p.val = 14 ∨ p.val = 15 ∨ p.val = 16 ∨ p.val = 17 ∨ p.val = 18 ∨ p.val = 19 := by have := p.isLt; omega
  have ha : i1.val = 0 ∨ i1.val = 1 ∨ i1.val = 2 := by have := i1.isLt; omega
  have hb : i2.val = 0 ∨ i2.val = 1 ∨ i2.val = 2 := by have := i2.isLt; omega
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp <;> rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 0 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 0 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 0 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 0 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 0 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 0 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 1 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 1 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 1 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 1 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 1 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 1 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 2 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 2 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 2 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 2 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 2 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 2 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 3 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 3 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 3 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 3 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 3 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 3 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 4 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 4 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 4 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 4 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 4 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 4 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 5 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 5 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 5 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 5 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 5 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 5 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 6 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 6 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 6 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 6 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 6 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 6 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 7 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 7 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 7 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 7 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 7 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 7 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 8 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 8 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 8 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 8 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 8 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 8 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 9 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 9 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 9 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 9 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 9 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 9 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 10 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 10 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 10 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 10 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 10 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 10 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 11 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 11 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 11 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 11 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 11 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 11 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 12 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 12 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 12 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 12 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 12 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 12 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 13 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 13 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 13 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 13 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 13 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 13 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 14 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 14 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 14 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 14 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 14 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 14 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 15 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 15 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 15 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 15 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 15 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 15 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 16 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 16 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 16 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 16 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 16 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 16 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 17 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 17 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 17 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 17 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 17 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 17 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 18 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 18 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 18 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 18 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 18 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 18 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 19 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · rw [show p = 19 from Fin.ext hp, show i1 = 0 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 19 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  · rw [show p = 19 from Fin.ext hp, show i1 = 1 from Fin.ext ha, show i2 = 2 from Fin.ext hb]
    decide!
  · rw [show p = 19 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 0 from Fin.ext hb]
    decide!
  · rw [show p = 19 from Fin.ext hp, show i1 = 2 from Fin.ext ha, show i2 = 1 from Fin.ext hb]
    decide!
  · exact absurd (Fin.ext (ha.trans hb.symm)) hne

attribute [irreducible] edgeGroup cornerGroup

private theorem edgeAll_ok : edgeAll = true := by
  unfold edgeAll
  rw [List.all_eq_true]
  intro n hn
  have hn30 : n < 30 := List.mem_range.mp hn
  rw [dif_pos hn30, List.all_eq_true]
  intro o ho
  have ho2 : o < 2 := List.mem_range.mp ho
  rw [dif_pos ho2]
  exact edgeGroup_ok ⟨n, hn30⟩ ⟨o, ho2⟩

private theorem cornerAll_ok : cornerAll = true := by
  unfold cornerAll
  rw [List.all_eq_true]
  intro n hn
  have hn20 : n < 20 := List.mem_range.mp hn
  rw [dif_pos hn20, List.all_eq_true]
  intro a ha
  have ha3 : a < 3 := List.mem_range.mp ha
  rw [dif_pos ha3, List.all_eq_true]
  intro b hb
  have hb3 : b < 3 := List.mem_range.mp hb
  rw [dif_pos hb3]
  by_cases h : (⟨a, ha3⟩ : Fin 3) = ⟨b, hb3⟩
  · rw [cornerGroup, if_pos h]
  · exact cornerGroup_ok ⟨n, hn20⟩ ⟨a, ha3⟩ ⟨b, hb3⟩ h

/-! ## From the Bool check to unequal codes -/

private theorem codesDistinct_get {cs : List (List Nat)} (h : codesDistinct cs = true)
    {i j : Nat} (hi : i < cs.length) (hj : j < cs.length) (hne : i ≠ j) :
    cs[i] ≠ cs[j] := by
  induction cs generalizing i j with
  | nil => simp at hi
  | cons c cs ih =>
    have h' : (!cs.any (fun x => x == c) && codesDistinct cs) = true := by
      simpa only [codesDistinct] using h
    rw [Bool.and_eq_true] at h'
    obtain ⟨hnot, hcs⟩ := h'
    have hfalse : cs.any (fun x => x == c) = false := by
      cases hb : cs.any (fun x => x == c) with
      | false => rfl
      | true => simp [hb] at hnot
    have tail_ne : ∀ k (hk : k < cs.length), cs[k] ≠ c := by
      intro k hk heq
      have ht : cs.any (fun x => x == c) = true := by
        rw [List.any_eq_true]
        exact ⟨cs[k], List.getElem_mem hk, by rw [heq]; exact beq_iff_eq.mpr rfl⟩
      exact Bool.noConfusion (hfalse.symm.trans ht)
    cases i with
    | zero =>
      cases j with
      | zero => exact (hne rfl).elim
      | succ j =>
        have hj' : j < cs.length := by simpa [List.length_cons] using hj
        rw [List.getElem_cons_zero (h := by simp), List.getElem_cons_succ]
        exact (tail_ne j hj').symm
    | succ i =>
      cases j with
      | zero =>
        have hi' : i < cs.length := by simpa [List.length_cons] using hi
        rw [List.getElem_cons_succ, List.getElem_cons_zero (h := by simp)]
        exact tail_ne i hi'
      | succ j =>
        have hi' : i < cs.length := by simpa [List.length_cons] using hi
        have hj' : j < cs.length := by simpa [List.length_cons] using hj
        rw [List.getElem_cons_succ, List.getElem_cons_succ]
        exact ih hcs hi' hj' (fun h => hne (congrArg Nat.succ h))

private theorem posCode_inj {a b : Position} (h : posCode a = posCode b) : a = b := by
  unfold posCode at h
  have hlenL :
      (listOf a.cp ++ listOfOri a.co ++ listOf a.ep).length =
        (listOf b.cp ++ listOfOri b.co ++ listOf b.ep).length := by
    simp [listOf_length, listOfOri_length, List.length_append]
  obtain ⟨hL, heo⟩ := List.append_inj h hlenL
  have hlenM :
      (listOf a.cp ++ listOfOri a.co).length = (listOf b.cp ++ listOfOri b.co).length := by
    simp [listOf_length, listOfOri_length, List.length_append]
  obtain ⟨hcpco, hep⟩ := List.append_inj hL hlenM
  have hlenC : (listOf a.cp).length = (listOf b.cp).length := by simp [listOf_length]
  obtain ⟨hcp, hco⟩ := List.append_inj hcpco hlenC
  apply Position.ext
  · exact listOf_inj _ _ hcp
  · exact listOfOri_inj _ _ hco
  · exact listOf_inj _ _ hep
  · exact listOfOri_inj _ _ heo

private theorem edgeAll_group (p : Fin 30) (order : Fin 2) : edgeGroup p order = true :=
  edgeGroup_ok p order

private theorem cornerAll_group (p : Fin 20) (i1 i2 : Fin 3) : cornerGroup p i1 i2 = true := by
  by_cases h : i1 = i2
  · rw [cornerGroup, if_pos h]
  · exact cornerGroup_ok p i1 i2 h

private theorem edgeIx (s : Fin 30) (o : Fin 2) :
    s.val * 2 + o.val < 60 ∧ (s.val * 2 + o.val) / 2 = s.val ∧
      (s.val * 2 + o.val) % 2 = o.val := by
  have := s.isLt
  have := o.isLt
  omega

private theorem cornerIx (s : Fin 20) (o : Fin 3) :
    s.val * 3 + o.val < 60 ∧ (s.val * 3 + o.val) / 3 = s.val ∧
      (s.val * 3 + o.val) % 3 = o.val := by
  have := s.isLt
  have := o.isLt
  omega

private theorem edgeCodes_length (p : Fin 30) (order : Fin 2) :
    (edgeCodes p order).length = 60 := by
  simp [edgeCodes]

private theorem cornerCodes_length (p : Fin 20) (i1 i2 : Fin 3) :
    (cornerCodes p i1 i2).length = 60 := by
  simp [cornerCodes]

private theorem edgeCodes_get (p : Fin 30) (order : Fin 2) (s : Fin 30) (o : Fin 2) :
    (edgeCodes p order)[s.val * 2 + o.val]'(by
      rw [edgeCodes_length]; exact (edgeIx s o).1) =
    posCode (edgeReadWord p order s o) := by
  unfold edgeCodes
  rw [List.getElem_map]
  rw [List.getElem_range]
  rw [dif_pos (by simpa [List.getElem_range] using (edgeIx s o).1)]
  apply congrArg posCode
  refine congr ?_ ?_
  · apply congrArg (edgeReadWord p order)
    apply Fin.ext
    simpa [List.getElem_range] using (edgeIx s o).2.1
  · apply Fin.ext
    simpa [List.getElem_range] using (edgeIx s o).2.2

private theorem cornerCodes_get (p : Fin 20) (i1 i2 : Fin 3) (s : Fin 20) (o : Fin 3) :
    (cornerCodes p i1 i2)[s.val * 3 + o.val]'(by
      rw [cornerCodes_length]; exact (cornerIx s o).1) =
    posCode (cornerReadWord p i1 i2 s o) := by
  unfold cornerCodes
  rw [List.getElem_map]
  rw [List.getElem_range]
  rw [dif_pos (by simpa [List.getElem_range] using (cornerIx s o).1)]
  apply congrArg posCode
  refine congr ?_ ?_
  · apply congrArg (cornerReadWord p i1 i2)
    apply Fin.ext
    simpa [List.getElem_range] using (cornerIx s o).2.1
  · apply Fin.ext
    simpa [List.getElem_range] using (cornerIx s o).2.2

private theorem edgeIx_inj {s1 s2 : Fin 30} {o1 o2 : Fin 2}
    (h : s1.val * 2 + o1.val = s2.val * 2 + o2.val) : s1 = s2 ∧ o1 = o2 := by
  have h1 := edgeIx s1 o1
  have h2 := edgeIx s2 o2
  have hs : s1.val = s2.val := by omega
  have ho : o1.val = o2.val := by omega
  exact ⟨Fin.ext hs, Fin.ext ho⟩

private theorem cornerIx_inj {s1 s2 : Fin 20} {o1 o2 : Fin 3}
    (h : s1.val * 3 + o1.val = s2.val * 3 + o2.val) : s1 = s2 ∧ o1 = o2 := by
  have h1 := cornerIx s1 o1
  have h2 := cornerIx s2 o2
  have hs : s1.val = s2.val := by omega
  have ho : o1.val = o2.val := by omega
  exact ⟨Fin.ext hs, Fin.ext ho⟩

/-! ## Model injectivity -/

/-- For every edge piece and every ordered pair of its colours, the 60 states give
    60 distinct two-turn read words. -/
theorem edge_read_words_injective (p : Fin 30) (order : Fin 2) :
    ∀ s1 s2 : Fin 30, ∀ o1 o2 : Fin 2,
      edgeReadWord p order s1 o1 = edgeReadWord p order s2 o2 → s1 = s2 ∧ o1 = o2 := by
  intro s1 s2 o1 o2 hEq
  by_cases hst : s1 = s2 ∧ o1 = o2
  · exact hst
  · apply False.elim
    have hix : s1.val * 2 + o1.val ≠ s2.val * 2 + o2.val := by
      intro h
      exact hst (edgeIx_inj h)
    have hi1 : s1.val * 2 + o1.val < (edgeCodes p order).length := by
      rw [edgeCodes_length]; exact (edgeIx s1 o1).1
    have hi2 : s2.val * 2 + o2.val < (edgeCodes p order).length := by
      rw [edgeCodes_length]; exact (edgeIx s2 o2).1
    have hdis : (edgeCodes p order)[s1.val * 2 + o1.val] ≠
        (edgeCodes p order)[s2.val * 2 + o2.val] :=
      codesDistinct_get (by
        have h := edgeAll_group p order
        rwa [edgeGroup] at h) hi1 hi2 hix
    have hcode : posCode (edgeReadWord p order s1 o1) =
        posCode (edgeReadWord p order s2 o2) := congrArg posCode hEq
    rw [← edgeCodes_get p order s1 o1, ← edgeCodes_get p order s2 o2] at hcode
    exact hdis hcode

/-- For every corner piece and every ordered pair of distinct colours among its three
    faces, the 60 states give 60 distinct two-turn read words. -/
theorem corner_read_words_injective (p : Fin 20) (i1 i2 : Fin 3) (hne : i1 ≠ i2) :
    ∀ s1 s2 : Fin 20, ∀ o1 o2 : Fin 3,
      cornerReadWord p i1 i2 s1 o1 = cornerReadWord p i1 i2 s2 o2 → s1 = s2 ∧ o1 = o2 := by
  intro s1 s2 o1 o2 hEq
  by_cases hst : s1 = s2 ∧ o1 = o2
  · exact hst
  · apply False.elim
    have hix : s1.val * 3 + o1.val ≠ s2.val * 3 + o2.val := by
      intro h
      exact hst (cornerIx_inj h)
    have hcd : codesDistinct (cornerCodes p i1 i2) = true := by
      have h := cornerAll_group p i1 i2
      rwa [cornerGroup, if_neg hne] at h
    have hi1 : s1.val * 3 + o1.val < (cornerCodes p i1 i2).length := by
      rw [cornerCodes_length]; exact (cornerIx s1 o1).1
    have hi2 : s2.val * 3 + o2.val < (cornerCodes p i1 i2).length := by
      rw [cornerCodes_length]; exact (cornerIx s2 o2).1
    have hdis : (cornerCodes p i1 i2)[s1.val * 3 + o1.val] ≠
        (cornerCodes p i1 i2)[s2.val * 3 + o2.val] :=
      codesDistinct_get hcd hi1 hi2 hix
    have hcode : posCode (cornerReadWord p i1 i2 s1 o1) =
        posCode (cornerReadWord p i1 i2 s2 o2) := congrArg posCode hEq
    rw [← cornerCodes_get p i1 i2 s1 o1, ← cornerCodes_get p i1 i2 s2 o2] at hcode
    exact hdis hcode

/-! ## The swap is `InjPos`, so the searches succeed and Link 2 applies -/

private theorem swapFun_invol {n : Nat} (p s i : Fin n) :
    (fun i => if i = s then p else if i = p then s else i)
      ((fun i => if i = s then p else if i = p then s else i) i) = i := by
  by_cases hs : i = s
  · by_cases hp : p = s
    · simp [hs, hp]
    · simp [hs, hp]
  · by_cases hp : i = p
    · have hps : p ≠ s := by intro e; exact hs (e ▸ hp)
      simp [hs, hp, hps]
    · simp [hs, hp]

private theorem swapFun_inj {n : Nat} (p s : Fin n) :
    Injective (fun i : Fin n => if i = s then p else if i = p then s else i) := by
  intro i j h
  have hi := swapFun_invol p s i
  have hj := swapFun_invol p s j
  have h' := congrArg (fun k => if k = s then p else if k = p then s else k) h
  rwa [hi, hj] at h'

private theorem placeEdge_injPos (p s : Fin 30) (o : Fin 2) : InjPos (placeEdge p s o) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    simpa [placeEdge] using h
  · dsimp [placeEdge]
    exact swapFun_inj p s

private theorem placeCorner_injPos (p s : Fin 20) (o : Fin 3) : InjPos (placeCorner p s o) := by
  refine ⟨?_, ?_⟩
  · dsimp [placeCorner]
    exact swapFun_inj p s
  · intro a b h
    simpa [placeCorner] using h

private theorem edgeFaceOf_eq_some {g : Position} {a b x y : Fin 12}
    (h : edgeFaceOf? g a b x = some y) : edgeFaceOf g a b x = y := by
  simp [edgeFaceOf, h]

private theorem cornerFaceOf_eq_some {g : Position} {a b c x y : Fin 12}
    (h : cornerFaceOf? g a b c x = some y) : cornerFaceOf g a b c x = y := by
  simp [cornerFaceOf, h]

private theorem edge_asked (p : Fin 30) (order : Fin 2) :
    let a := edgeFace p.val 0
    let b := edgeFace p.val 1
    let x := if order = 0 then a else b
    let y := if order = 0 then b else a
    (x = a ∨ x = b) ∧ (y = a ∨ y = b) := by
  by_cases h : order = 0 <;> simp [h]

private theorem corner_asked (p : Fin 20) (j : Fin 3) :
    cornerFace p.val j.val = cornerFace p.val 0 ∨ cornerFace p.val j.val = cornerFace p.val 1 ∨
      cornerFace p.val j.val = cornerFace p.val 2 := by
  have h : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by have := j.isLt; omega
  rcases h with h | h | h <;> simp [h]

/-! ## Emitted read words -/

/-- Emitted two-turn edge read on the embedded placement, in the sudo test's order:
    `edge_face_of`, `face_turn` by 1, `edge_face_of` of the other colour, then
    `face_turn (face_turn identity f1 1) f2 1`. -/
def emittedEdgeReadWord (p : Fin 30) (order : Fin 2) (s : Fin 30) (o : Fin 2) :
    Except SudoRt.Trap Megadreifach.Position :=
  let a := edgeFace p.val 0
  let b := edgeFace p.val 1
  let x := if order = 0 then a else b
  let y := if order = 0 then b else a
  do
    let g := embedPos (placeEdge p s o)
    let f1 ← Megadreifach.edge_face_of g (Int.ofNat a.val) (Int.ofNat b.val) (Int.ofNat x.val)
    let g1 ← Megadreifach.face_turn g f1 (Int.ofNat 1)
    let f2 ← Megadreifach.edge_face_of g1 (Int.ofNat a.val) (Int.ofNat b.val) (Int.ofNat y.val)
    let idp ← Megadreifach.identity
    let w ← Megadreifach.face_turn idp f1 (Int.ofNat 1)
    Megadreifach.face_turn w f2 (Int.ofNat 1)

/-- Emitted two-turn corner read, same shape as the sudo test. -/
def emittedCornerReadWord (p : Fin 20) (i1 i2 : Fin 3) (s : Fin 20) (o : Fin 3) :
    Except SudoRt.Trap Megadreifach.Position :=
  let a := Int.ofNat (cornerFace p.val 0).val
  let b := Int.ofNat (cornerFace p.val 1).val
  let c := Int.ofNat (cornerFace p.val 2).val
  let x := Int.ofNat (cornerFace p.val i1.val).val
  let y := Int.ofNat (cornerFace p.val i2.val).val
  do
    let g := embedPos (placeCorner p s o)
    let f1 ← Megadreifach.corner_face_of g a b c x
    let g1 ← Megadreifach.face_turn g f1 (Int.ofNat 1)
    let f2 ← Megadreifach.corner_face_of g1 a b c y
    let idp ← Megadreifach.identity
    let w ← Megadreifach.face_turn idp f1 (Int.ofNat 1)
    Megadreifach.face_turn w f2 (Int.ofNat 1)

/-- The emitted edge read word is the embedding of the model word. -/
theorem emitted_edge_read_word_eq (p : Fin 30) (order : Fin 2) (s : Fin 30) (o : Fin 2) :
    emittedEdgeReadWord p order s o = .ok (embedPos (edgeReadWord p order s o)) := by
  let aF := edgeFace p.val 0
  let bF := edgeFace p.val 1
  let xF := if order = 0 then aF else bF
  let yF := if order = 0 then bF else aF
  let g := placeEdge p s o
  have hg : InjPos g := placeEdge_injPos p s o
  have hs : edgeSlot? aF bF = some p := by
    simpa [aF, bF] using edgeSlot?_faces p
  have hx : xF = edgeFace p.val 0 ∨ xF = edgeFace p.val 1 := (edge_asked p order).1
  have hy : yF = edgeFace p.val 0 ∨ yF = edgeFace p.val 1 := (edge_asked p order).2
  obtain ⟨f1, hf1⟩ := edgeFaceOf_found g hg.2 aF bF xF p hs hx
  have hf1e : edgeFaceOf g aF bF xF = f1 := edgeFaceOf_eq_some hf1
  have hturn : InjPos (faceTurn g f1 1) := by
    simpa [hf1e] using injPos_faceTurn g (edgeFaceOf g aF bF xF) 1 hg
  obtain ⟨f2, hf2⟩ := edgeFaceOf_found (faceTurn g f1 1) hturn.2 aF bF yF p hs hy
  have hf2e : edgeFaceOf (faceTurn g f1 1) aF bF yF = f2 := edgeFaceOf_eq_some hf2
  have hword : edgeReadWord p order s o = twoTurnWord f1 f2 := by
    show twoTurnWord (edgeFaceOf g aF bF xF)
        (edgeFaceOf (faceTurn g (edgeFaceOf g aF bF xF) 1) aF bF yF) = twoTurnWord f1 f2
    rw [hf1e, hf2e]
  show (Megadreifach.edge_face_of (embedPos g) (Int.ofNat aF.val) (Int.ofNat bF.val)
        (Int.ofNat xF.val) >>= fun f1i =>
      Megadreifach.face_turn (embedPos g) f1i (Int.ofNat 1) >>= fun g1 =>
      Megadreifach.edge_face_of g1 (Int.ofNat aF.val) (Int.ofNat bF.val) (Int.ofNat yF.val) >>=
        fun f2i =>
      Megadreifach.identity >>= fun idp =>
      Megadreifach.face_turn idp f1i (Int.ofNat 1) >>= fun w =>
      Megadreifach.face_turn w f2i (Int.ofNat 1)) =
    .ok (embedPos (edgeReadWord p order s o))
  rw [edge_face_of_refines g aF bF xF p hs f1 hf1, ok_bind]
  rw [MegaDreifachV3.Link2.face_turn_refines g f1 1, ok_bind]
  rw [edge_face_of_refines (faceTurn g f1 1) aF bF yF p hs f2 hf2, ok_bind]
  rw [identity_refines, ok_bind]
  rw [MegaDreifachV3.Link2.face_turn_refines identity f1 1, ok_bind]
  rw [MegaDreifachV3.Link2.face_turn_refines (faceTurn identity f1 1) f2 1, hword, twoTurnWord]

/-- The emitted corner read word is the embedding of the model word. -/
theorem emitted_corner_read_word_eq (p : Fin 20) (i1 i2 : Fin 3) (s : Fin 20) (o : Fin 3) :
    emittedCornerReadWord p i1 i2 s o =
      .ok (embedPos (cornerReadWord p i1 i2 s o)) := by
  let aF := cornerFace p.val 0
  let bF := cornerFace p.val 1
  let cF := cornerFace p.val 2
  let xF := cornerFace p.val i1.val
  let yF := cornerFace p.val i2.val
  let g := placeCorner p s o
  have hg : InjPos g := placeCorner_injPos p s o
  have ht : cornerSlot? aF bF cF = some p := by
    simpa [aF, bF, cF] using cornerSlot?_faces p
  have hx : xF = cornerFace p.val 0 ∨ xF = cornerFace p.val 1 ∨ xF = cornerFace p.val 2 :=
    corner_asked p i1
  have hy : yF = cornerFace p.val 0 ∨ yF = cornerFace p.val 1 ∨ yF = cornerFace p.val 2 :=
    corner_asked p i2
  obtain ⟨f1, hf1⟩ := cornerFaceOf_found g hg.1 aF bF cF xF p ht hx
  have hf1e : cornerFaceOf g aF bF cF xF = f1 := cornerFaceOf_eq_some hf1
  have hturn : InjPos (faceTurn g f1 1) := by
    simpa [hf1e] using injPos_faceTurn g (cornerFaceOf g aF bF cF xF) 1 hg
  obtain ⟨f2, hf2⟩ := cornerFaceOf_found (faceTurn g f1 1) hturn.1 aF bF cF yF p ht hy
  have hf2e : cornerFaceOf (faceTurn g f1 1) aF bF cF yF = f2 := cornerFaceOf_eq_some hf2
  have hword : cornerReadWord p i1 i2 s o = twoTurnWord f1 f2 := by
    show twoTurnWord (cornerFaceOf g aF bF cF xF)
        (cornerFaceOf (faceTurn g (cornerFaceOf g aF bF cF xF) 1) aF bF cF yF) =
      twoTurnWord f1 f2
    rw [hf1e, hf2e]
  show (Megadreifach.corner_face_of (embedPos g) (Int.ofNat aF.val) (Int.ofNat bF.val)
        (Int.ofNat cF.val) (Int.ofNat xF.val) >>= fun f1i =>
      Megadreifach.face_turn (embedPos g) f1i (Int.ofNat 1) >>= fun g1 =>
      Megadreifach.corner_face_of g1 (Int.ofNat aF.val) (Int.ofNat bF.val) (Int.ofNat cF.val)
          (Int.ofNat yF.val) >>= fun f2i =>
      Megadreifach.identity >>= fun idp =>
      Megadreifach.face_turn idp f1i (Int.ofNat 1) >>= fun w =>
      Megadreifach.face_turn w f2i (Int.ofNat 1)) =
    .ok (embedPos (cornerReadWord p i1 i2 s o))
  rw [corner_face_of_refines g aF bF cF xF p ht f1 hf1, ok_bind]
  rw [MegaDreifachV3.Link2.face_turn_refines g f1 1, ok_bind]
  rw [corner_face_of_refines (faceTurn g f1 1) aF bF cF yF p ht f2 hf2, ok_bind]
  rw [identity_refines, ok_bind]
  rw [MegaDreifachV3.Link2.face_turn_refines identity f1 1, ok_bind]
  rw [MegaDreifachV3.Link2.face_turn_refines (faceTurn identity f1 1) f2 1, hword, twoTurnWord]

/-- Injectivity of the model edge words transfers to the emitted words. -/
theorem emitted_edge_read_words_injective (p : Fin 30) (order : Fin 2) :
    ∀ s1 s2 : Fin 30, ∀ o1 o2 : Fin 2,
      emittedEdgeReadWord p order s1 o1 = emittedEdgeReadWord p order s2 o2 →
        s1 = s2 ∧ o1 = o2 := by
  intro s1 s2 o1 o2 h
  rw [emitted_edge_read_word_eq, emitted_edge_read_word_eq] at h
  exact edge_read_words_injective p order s1 s2 o1 o2 (embedPos_inj (Except.ok.inj h))

/-- Injectivity of the model corner words transfers to the emitted words. -/
theorem emitted_corner_read_words_injective (p : Fin 20) (i1 i2 : Fin 3) (hne : i1 ≠ i2) :
    ∀ s1 s2 : Fin 20, ∀ o1 o2 : Fin 3,
      emittedCornerReadWord p i1 i2 s1 o1 = emittedCornerReadWord p i1 i2 s2 o2 →
        s1 = s2 ∧ o1 = o2 := by
  intro s1 s2 o1 o2 h
  rw [emitted_corner_read_word_eq, emitted_corner_read_word_eq] at h
  exact corner_read_words_injective p i1 i2 hne s1 s2 o1 o2 (embedPos_inj (Except.ok.inj h))

end MegaDreifachV3.Security
