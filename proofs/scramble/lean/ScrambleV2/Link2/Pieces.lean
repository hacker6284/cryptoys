/-
  LINK 2. The emitted sticker and piece readers against the model: `sticker_on`,
  `color_char`, `is_ud`, `edge_bit`, `corner_piece`, `edge_piece`. The piece readers are
  checked on every triple / pair of the six colors (`decide`); on a set of colors that
  is a piece they return the model's `pieceId`. Proof-only.
-/
import ScrambleV2.Link2.Reach

namespace ScrambleV2.Link2
open MegaDreifach.Link2

/-- The sudo's axis codes (`0 xp, 1 xn, 2 yp, 3 yn, 4 zp, 5 zn`). -/
def axisCode : List (Int × V3) :=
  [(0, ax_xp), (1, ax_xn), (2, ax_yp), (3, ax_yn), (4, ax_zp), (5, ax_zn)]

theorem sticker_on_refines (c : Cubie) :
    ∀ ka ∈ axisCode, Scramble.sticker_on (embedC c) ka.1 = .ok (slot c ka.2) := by
  intro ka hka
  simp only [axisCode, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hka
  rcases hka with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The SPEC's color letters. -/
def _root_.ScrambleV2.Color.letter : Color → Int
  | .W => 87 | .Y => 89 | .R => 82 | .O => 79 | .B => 66 | .G => 71

theorem color_char_refines (col : Color) :
    Scramble.color_char col.code = .ok col.letter := by
  cases col <;> rfl

theorem is_ud_refines (col : Color) : Scramble.is_ud col.code = .ok (isUD col) := by
  cases col <;> rfl

theorem edge_bit_refines (col : Color) :
    Scramble.edge_bit col.code = .ok (Int.ofNat (edgeBit col)) := by
  cases col <;> rfl

def cornerOK3 (u v w : Color) : Bool :=
  match pieceId cornerTable [u, v, w] with
  | some n => decide (Scramble.corner_piece u.code v.code w.code = .ok (Int.ofNat n))
  | none => true

def edgeOK2 (u v : Color) : Bool :=
  match pieceId edgeTable [u, v] with
  | some n => decide (Scramble.edge_piece u.code v.code = .ok (Int.ofNat n))
  | none => true

theorem cornerOK3_all : ∀ u ∈ allColors, ∀ v ∈ allColors, ∀ w ∈ allColors,
    cornerOK3 u v w = true := by decide

theorem edgeOK2_all : ∀ u ∈ allColors, ∀ v ∈ allColors, edgeOK2 u v = true := by decide

/-- On three colors that form a corner piece, the emitted `corner_piece` is its id. -/
theorem corner_piece_refines (u v w : Color) (n : Nat)
    (h : pieceId cornerTable [u, v, w] = some n) :
    Scramble.corner_piece u.code v.code w.code = .ok (Int.ofNat n) := by
  have hk := cornerOK3_all u (mem_allColors u) v (mem_allColors v) w (mem_allColors w)
  unfold cornerOK3 at hk
  rw [h] at hk
  exact of_decide_eq_true hk

/-- On two colors that form an edge piece, the emitted `edge_piece` is its id. -/
theorem edge_piece_refines (u v : Color) (n : Nat) (h : pieceId edgeTable [u, v] = some n) :
    Scramble.edge_piece u.code v.code = .ok (Int.ofNat n) := by
  have hk := edgeOK2_all u (mem_allColors u) v (mem_allColors v)
  unfold edgeOK2 at hk
  rw [h] at hk
  exact of_decide_eq_true hk

end ScrambleV2.Link2

namespace ScrambleV2.Link2

/-- The emitted `fact` on the arguments `rank_perm` passes for lists of length at most
    12 (the digest ranks 8 corners and 12 edges). -/
theorem fact_small_all : ∀ n ∈ List.range 12,
    Scramble.fact (Int.ofNat n) = .ok (Int.ofNat (fact n)) := by decide

theorem fact_refines (n : Nat) (h : n < 12) :
    Scramble.fact (Int.ofNat n) = .ok (Int.ofNat (fact n)) :=
  fact_small_all n (List.mem_range.mpr h)

end ScrambleV2.Link2
