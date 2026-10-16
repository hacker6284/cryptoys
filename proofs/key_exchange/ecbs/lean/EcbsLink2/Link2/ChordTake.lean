/-
  Take the settled bottom away from the across, then mirror the up.
  SPEC.md §3 R7 line 156. The last multiply is still open.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Add
import EcbsLink2.Link2.Mirror
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- `add` of the bottom onto the across with the mirror on, then `mirror` of
    the up. The across becomes `fieldSub` of the old across and the bottom,
    and the up becomes `mirrorTrits`. SPEC.md §3 R7 line 156: take the bottom
    away from its across, and mirror its up. One `FitsLen (moves + 2 * n)`
    covers both. -/
theorem chord_take_mirror (b : Ecbs.Board) (xs x3 ys : List Nat) (n moves : Nat)
    (h0H : 0 < b.sudo_5Board_4home.size) (h0D : 0 < b.sudo_5Board_4held.size)
    (h0t : b.sudo_5Board_4held[0] = true)
    (h0a : b.sudo_5Board_4home[0] = embed xs)
    (h2H : 2 < b.sudo_5Board_4home.size) (h2D : 2 < b.sudo_5Board_4held.size)
    (h2t : b.sudo_5Board_4held[2] = true)
    (h2a : b.sudo_5Board_4home[2] = embed x3)
    (h1H : 1 < b.sudo_5Board_4home.size) (h1D : 1 < b.sudo_5Board_4held.size)
    (h1t : b.sudo_5Board_4held[1] = true)
    (h1a : b.sudo_5Board_4home[1] = embed ys)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx : xs.length = n) (hx3 : x3.length = n) (hy : ys.length = n)
    (hpos : 0 < n)
    (htriX : allTritList xs) (htri3 : allTritList x3) (htriY : allTritList ys)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + 2 * n)) :
    ∃ (b' : Ecbs.Board) (h0 : 0 < b'.sudo_5Board_4home.size) (h1 : 1 < b'.sudo_5Board_4home.size),
      (do
          let b ← Ecbs.add b Ecbs.across Ecbs.bottom true
          Ecbs.mirror b Ecbs.up) = .ok b' ∧
      b'.sudo_5Board_4home[0] = embed (fieldSub n xs x3) ∧
      b'.sudo_5Board_4home[1] = embed (mirrorTrits ys) ∧
      b'.sudo_5Board_4held = b.sudo_5Board_4held ∧
      b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      b'.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      b'.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      b'.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      b'.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      b'.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak =
        b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (moves + pegCount x3 + pegCount ys) ∧
      (∀ i, i ≠ 0 → i ≠ 1 → ∀ hi : i < b.sudo_5Board_4home.size,
        ∀ hi' : i < b'.sudo_5Board_4home.size,
          b'.sudo_5Board_4home[i] = b.sudo_5Board_4home[i]) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest ∧
      b'.sudo_5Board_3row = b.sudo_5Board_3row := by
  have hfit1 : FitsLen (moves + n) := FitsLen.of_le hfit (by omega)
  have hp3 : pegCount x3 ≤ n := by rw [← hx3]; exact pegCount_le x3
  have hadd := add_refines b 0 2 xs x3 n moves h0H h0D h2H h2D h0t h0a h2t h2a hn hx3 hx
    hpos htriX htri3 hm hfit1
  rw [show Ecbs.across = ((0 : Nat) : Int) from rfl, show Ecbs.bottom = ((2 : Nat) : Int) from rfl,
    hadd, ok_bind]
  let mv1 := moves + pegCount x3
  let bA := addBoard b 0 h0H (embed (fieldAdd n xs (mirrorTrits x3))) mv1
  have h1Hb : 1 < bA.sudo_5Board_4home.size := by
    simpa [bA, addBoard, withMoves, Array.size_set] using h1H
  have h1Db : 1 < bA.sudo_5Board_4held.size := by
    simpa [bA, addBoard, withMoves] using h1D
  have h1tb : bA.sudo_5Board_4held[1] = true := by simpa [bA, addBoard, withMoves] using h1t
  have h1ab : bA.sudo_5Board_4home[1] = embed ys := by
    simpa [bA, addBoard, withMoves, Array.getElem_set_ne] using h1a
  have hnA : bA.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simpa [bA, addBoard, withMoves] using hn
  have hmA : bA.sudo_5Board_4cost.sudo_5Costs_5moves = (mv1 : Int) := by
    simp [bA, addBoard, withMoves, mv1, ofNat_eq_natCast]
  have hfit2 : FitsLen (mv1 + n) := FitsLen.of_le hfit (by omega)
  have hmirr := mirror_refines bA 1 ys n mv1 h1Hb h1Db h1tb h1ab hnA hy hpos htriY hmA hfit2
  rw [show Ecbs.up = ((1 : Nat) : Int) from rfl, hmirr]
  let bM := mirrorHome bA 1 h1Hb (embed (mirrorTrits ys)) (mv1 + pegCount ys)
  have h0s : 0 < bM.sudo_5Board_4home.size := by
    simpa [bM, mirrorHome, bA, addBoard, withMoves, Array.size_set] using h0H
  have h1s : 1 < bM.sudo_5Board_4home.size := by
    simpa [bM, mirrorHome, Array.size_set] using h1Hb
  refine ⟨bM, h0s, h1s, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hsub : fieldAdd n xs (mirrorTrits x3) = fieldSub n xs x3 := by
      simp [fieldSub]
    simp [bM, mirrorHome, Array.getElem_set_ne, bA, addBoard, withMoves, Array.getElem_set_eq, hsub]
  · simp [bM, mirrorHome, Array.get_set_eq]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, Array.size_set, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome, withMoves, mv1, Nat.add_assoc]
  · intro i hne0 hne1 hi hi'
    have hne0' : (0 : Nat) ≠ i := hne0.symm
    have hne1' : (1 : Nat) ≠ i := hne1.symm
    simp [bM, mirrorHome, Array.getElem_set_ne, hne1', bA, addBoard, withMoves,
      Array.getElem_set_ne, hne0']
  · simp [bM, mirrorHome, bA, addBoard, withMoves]
  · simp [bM, mirrorHome_row, bA, addBoard_row]

end EcbsLink2.Link2
