/-
  The tail of `curve_side`: the destination already holds `x³` and the spare
  holds `x²`. `add` with the mirror flag, `clear` of the spare, and `white0`
  on the held home write `x³ − x² + 1`. That is `curveSide`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Add
import EcbsLink2.Link2.FieldNeg
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem field_len (n : Nat) (xs ys : List Nat) :
    (fieldAdd n xs ys).length = n := by
  unfold fieldAdd
  simp [List.length_map, List.length_range]

private theorem spare_home (b : Ecbs.Board) (dst spare : Nat)
    (hH : dst < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat)
    (hne : spare ≠ dst) (hs : spare < b.sudo_5Board_4home.size) :
    (addBoard b dst hH arr mv).sudo_5Board_4home[spare]'(by
      simp [addBoard, withMoves, Array.size_set]; exact hs) =
      b.sudo_5Board_4home[spare] := by
  simp [addBoard, withMoves, Array.getElem_set_ne, hne.symm]

private theorem spare_held (b : Ecbs.Board) (dst spare : Nat)
    (hH : dst < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat)
    (hs : spare < b.sudo_5Board_4held.size) :
    (addBoard b dst hH arr mv).sudo_5Board_4held[spare]'(by
      simp [addBoard, withMoves]; exact hs) =
      b.sudo_5Board_4held[spare] := by
  simp [addBoard, withMoves]

private theorem dst_held_add (b : Ecbs.Board) (dst : Nat)
    (hH : dst < b.sudo_5Board_4home.size) (hD : dst < b.sudo_5Board_4held.size)
    (arr : Array Int) (mv : Nat) (hheld : b.sudo_5Board_4held[dst] = true) :
    (addBoard b dst hH arr mv).sudo_5Board_4held[dst]'(by
      simp [addBoard, withMoves]; exact hD) = true := by
  simpa [addBoard, withMoves] using hheld

private theorem dst_home_clear (b : Ecbs.Board) (dst spare : Nat)
    (hHs : spare < b.sudo_5Board_4home.size) (hDs : spare < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves : Nat) (hne : dst ≠ spare)
    (hHd : dst < b.sudo_5Board_4home.size)
    (harr : b.sudo_5Board_4home[dst] = embed xs) :
    ({ b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨spare, hHs⟩ #[]
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨spare, hDs⟩ false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat moves } }).sudo_5Board_4home[dst]'(by
      simp [Array.size_set]; exact hHd) = embed xs := by
  simp [Array.getElem_set_ne, hne.symm, harr]

private theorem dst_held_clear (b : Ecbs.Board) (dst spare : Nat)
    (hHs : spare < b.sudo_5Board_4home.size) (hDs : spare < b.sudo_5Board_4held.size)
    (moves : Nat) (hne : dst ≠ spare)
    (hDd : dst < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[dst] = true) :
    ({ b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨spare, hHs⟩ #[]
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨spare, hDs⟩ false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat moves } }).sudo_5Board_4held[dst]'(by
      simp [Array.size_set]; exact hDd) = true := by
  simp [Array.getElem_set_ne, hne.symm, hheld]

private theorem moves_clear (b : Ecbs.Board) (spare : Nat)
    (hHs : spare < b.sudo_5Board_4home.size) (hDs : spare < b.sudo_5Board_4held.size)
    (moves : Nat) :
    ({ b with
        sudo_5Board_4home := b.sudo_5Board_4home.set ⟨spare, hHs⟩ #[]
        sudo_5Board_4held := b.sudo_5Board_4held.set ⟨spare, hDs⟩ false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat moves } }).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat moves := rfl

/-- One digit of the root power. `2` multiplies by the squared side, `1` by
    the side, and `0` only cubes. -/
theorem powStep_branch (n k bench : Nat) (rhs acc : List Nat) (d : Nat) :
    powStep n k bench rhs acc d =
      let cubed := fieldCube n k bench acc
      if d = 2 then fieldMul n k bench cubed (fieldMul n k bench rhs rhs)
      else if d = 1 then fieldMul n k bench cubed rhs
      else cubed := by
  unfold powStep
  rfl

/-- The root up is that power on `rootDigits`, starting from the white peg. -/
theorem rootY_digits (n k bench : Nat) (x : List Nat) :
    rootY n k bench x =
      (rootDigits n).foldl (powStep n k bench (curveSide n k bench x)) (whiteHole0 n) := by
  unfold rootY fieldPowDigits
  rfl

/-- A hit is the squared root up agreeing with the curve side. -/
theorem rootHit_beq (n k bench : Nat) (x : List Nat) :
    rootHit n k bench x =
      ((fieldMul n k bench (rootY n k bench x) (rootY n k bench x)) ==
        curveSide n k bench x) := by
  unfold rootHit
  rfl

/-- Fields the close does not write, besides the destination home and the spare. -/
structure CloseKeep (b bW : Ecbs.Board) (dst spare : Nat) : Prop where
  markerOn : bW.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on
  marker : bW.sudo_5Board_6marker = b.sudo_5Board_6marker
  bench : bW.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on
  ctrl : bW.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl
  mx : bW.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
    b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max
  ops : bW.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops
  tier : bW.sudo_5Board_1t = b.sudo_5Board_1t
  szH : bW.sudo_5Board_4home.size = b.sudo_5Board_4home.size
  szD : bW.sudo_5Board_4held.size = b.sudo_5Board_4held.size
  home : ∀ i, i ≠ dst → i ≠ spare →
    ∀ (hi : i < b.sudo_5Board_4home.size) (hi' : i < bW.sudo_5Board_4home.size),
      bW.sudo_5Board_4home[i] = b.sudo_5Board_4home[i]
  held : ∀ i, i ≠ spare →
    ∀ (hi : i < b.sudo_5Board_4held.size) (hi' : i < bW.sudo_5Board_4held.size),
      bW.sudo_5Board_4held[i] = b.sudo_5Board_4held[i]
  spareHeld : ∀ h : spare < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[spare] = false
  dstHeld : ∀ h : dst < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[dst] = true
  slides : bW.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides
  peak : bW.sudo_5Board_4cost.sudo_5Costs_4peak = b.sudo_5Board_4cost.sudo_5Costs_4peak
  strict : bW.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
    b.sudo_5Board_4cost.sudo_5Costs_11peak_strict
  hole : bW.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
    b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole
  moves : ∃ mv, bW.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int)

/-- Mirror-add, clear the spare, then add one in hole 0. -/
theorem curve_side_close (b : Ecbs.Board) (dst spare : Nat)
    (x3 x2 : List Nat) (n moves : Nat)
    (hHd : dst < b.sudo_5Board_4home.size) (hDd : dst < b.sudo_5Board_4held.size)
    (hHs : spare < b.sudo_5Board_4home.size) (hDs : spare < b.sudo_5Board_4held.size)
    (hne : spare ≠ dst) (hne' : dst ≠ spare)
    (hheldD : b.sudo_5Board_4held[dst] = true)
    (harrD : b.sudo_5Board_4home[dst] = embed x3)
    (hheldS : b.sudo_5Board_4held[spare] = true)
    (harrS : b.sudo_5Board_4home[spare] = embed x2)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx3 : x3.length = n) (hx2 : x2.length = n) (hpos : 0 < n)
    (ht3 : allTritList x3) (ht2 : allTritList x2)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + 2 * n + 1))
    (_hbench : b.sudo_5Board_8bench_on = false) :
    ∃ bW,
      (do
          let b ← add b (dst : Int) (spare : Int) true
          let b ← clear b (spare : Int)
          white0 b (dst : Int)) = .ok bW ∧
        (∀ h : dst < bW.sudo_5Board_4home.size,
          bW.sudo_5Board_4home[dst] =
            embed (fieldAdd n (fieldAdd n x3 (mirrorTrits x2)) (whiteHole0 n))) ∧
        CloseKeep b bW dst spare ∧
        bW.sudo_5Board_4cost.sudo_5Costs_5moves =
          Int.ofNat (moves + 2 * pegCount x2 + 1) := by
  have hlenS : (fieldAdd n x3 (mirrorTrits x2)).length = n := field_len _ _ _
  have htS : allTritList (fieldAdd n x3 (mirrorTrits x2)) := fieldAdd_trits _ _ _
  have hfitA : FitsLen (moves + n) := FitsLen.of_le hfit (by omega)
  have hadd := add_refines b dst spare x3 x2 n moves hHd hDd hHs hDs
    hheldD harrD hheldS harrS hn hx2 hx3 hpos ht3 ht2 hm hfitA
  let sum := fieldAdd n x3 (mirrorTrits x2)
  let mv1 := moves + pegCount x2
  let b1 := addBoard b dst hHd (embed sum) mv1
  have hmv1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves = (mv1 : Int) := by
    simp [b1, addBoard, withMoves, ofNat_eq_natCast]
  have harr1 : b1.sudo_5Board_4home[spare]'(by
      simp [b1, addBoard, withMoves, Array.size_set]; exact hHs) = embed x2 := by
    simpa [b1, harrS] using spare_home b dst spare hHd (embed sum) mv1 hne hHs
  have hheld1 : b1.sudo_5Board_4held[spare]'(by simp [b1, addBoard, withMoves]; exact hDs) =
      true := by
    simpa [b1, hheldS] using spare_held b dst spare hHd (embed sum) mv1 hDs
  have hfitC : FitsLen (mv1 + pegCount x2) := by
    have hle : pegCount x2 ≤ n := by rw [← hx2]; exact pegCount_le x2
    exact FitsLen.of_le hfit (by omega)
  have hf2 : FitsLen x2.length := by rw [hx2]; exact FitsLen.of_le hfit (by omega)
  have hclear := clear_held_refines b1 spare x2 mv1
    (by simp [b1, addBoard, withMoves, Array.size_set]; exact hHs)
    (by simp [b1, addBoard, withMoves]; exact hDs)
    hheld1 harr1 hmv1 hf2 hfitC
  let mv2 := mv1 + pegCount x2
  let b2 := { b1 with
    sudo_5Board_4home := b1.sudo_5Board_4home.set
      ⟨spare, by simp [b1, addBoard, withMoves, Array.size_set]; exact hHs⟩ #[]
    sudo_5Board_4held := b1.sudo_5Board_4held.set
      ⟨spare, by simp [b1, addBoard, withMoves]; exact hDs⟩ false
    sudo_5Board_4cost := { b1.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat mv2 } }
  have hdstH : dst < b2.sudo_5Board_4home.size := by
    simp [b2, b1, addBoard, withMoves, Array.size_set]; exact hHd
  have hdstD : dst < b2.sudo_5Board_4held.size := by
    simp [b2, b1, addBoard, withMoves, Array.size_set]; exact hDd
  have hhome2 : b2.sudo_5Board_4home[dst] = embed sum := by
    have hbase : b1.sudo_5Board_4home[dst]'(by simp [b1, addBoard, withMoves, Array.size_set]; exact hHd) =
        embed sum := by simp [b1, addBoard, withMoves, Array.getElem_set]
    simpa [b2, hbase] using dst_home_clear b1 dst spare
      (by simp [b1, addBoard, withMoves, Array.size_set]; exact hHs)
      (by simp [b1, addBoard, withMoves]; exact hDs) sum mv2 hne'
      (by simp [b1, addBoard, withMoves, Array.size_set]; exact hHd) hbase
  have hheld2 : b2.sudo_5Board_4held[dst] = true := by
    have hkeep := dst_held_add b dst hHd hDd (embed sum) mv1 hheldD
    simpa [b2, b1] using dst_held_clear b1 dst spare
      (by simp [b1, addBoard, withMoves, Array.size_set]; exact hHs)
      (by simp [b1, addBoard, withMoves]; exact hDs) mv2 hne' hDd hkeep
  have hmv2 : b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv2 := moves_clear _ _ _ _ _
  have h0 : 0 < sum.length := by rw [hlenS]; exact hpos
  have hc0 : sum[0]'(h0) ≤ 2 := by
    exact htS _ (List.getElem_mem h0)
  have hfitW : FitsLen (mv2 + 1) := by
    have hle : pegCount x2 ≤ n := by rw [← hx2]; exact pegCount_le x2
    exact FitsLen.of_le hfit (by omega)
  have hwhite := white0_held b2 dst sum mv2 hdstH hdstD hheld2 hhome2 h0 hc0 hmv2 hfitW
  let bW := addBoard b2 dst hdstH (embed (sum.set 0 (tritAdd (sum[0]'h0) 1))) (mv2 + 1)
  refine ⟨bW, ?_, ?_, ?_, ?_⟩
  · rw [hadd, ok_bind]
    have hclear' : clear b1 (spare : Int) = .ok b2 := by
      simpa [b2, mv2, b1] using hclear
    rw [hclear', ok_bind, hwhite]
  · intro _
    have hpoly : fieldAdd n sum (whiteHole0 n) =
        sum.set 0 (tritAdd (sum[0]'h0) 1) := by
      have hw : whiteHole0 n = 1 :: List.replicate (n - 1) 0 := rfl
      rw [hw]
      exact fieldAdd_white n sum hlenS hpos htS
    simp [bW, addBoard, withMoves, Array.getElem_set, hpoly]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [bW, b2, b1, addBoard, withMoves]
    · simp [bW, b2, b1, addBoard, withMoves]
    · simp [bW, b2, b1, addBoard, withMoves]
    · simp [bW, b2, b1, addBoard, withMoves]
    · simp [bW, b2, b1, addBoard, withMoves]
    · simp [bW, b2, b1, addBoard, withMoves]
    · simp [bW, b2, b1, addBoard, withMoves]
    · simp [bW, b2, b1, addBoard, withMoves, Array.size_set]
    · simp [bW, b2, b1, addBoard, withMoves, Array.size_set]
    · intro i hd hs hi hi'
      have hneD : dst ≠ i := Ne.symm hd
      have hneS : spare ≠ i := Ne.symm hs
      simp [bW, b2, b1, addBoard, withMoves, Array.getElem_set, hneD, hneS]
    · intro i hs hi hi'
      have hneS : spare ≠ i := Ne.symm hs
      simp [bW, b2, b1, addBoard, withMoves, Array.getElem_set, hneS]
    · intro _
      have hneS : spare ≠ dst := hne
      simp [bW, b2, b1, addBoard, withMoves, Array.getElem_set, hneS]
    · intro _
      have hneS : spare ≠ dst := hne
      simp [bW, b2, b1, addBoard, withMoves, Array.getElem_set, hneS, hheldD]
    · simp [bW, b2, b1, addBoard, withMoves]
    · simp [bW, b2, b1, addBoard, withMoves]
    · simp [bW, b2, b1, addBoard, withMoves]
    · simp [bW, b2, b1, addBoard, withMoves]
    · exact ⟨mv2 + 1, by simp [bW, addBoard, withMoves, ofNat_eq_natCast]⟩
  · have hmvEq : mv2 + 1 = moves + 2 * pegCount x2 + 1 := by
      dsimp [mv2, mv1]
      omega
    simp [bW, addBoard, withMoves, ofNat_eq_natCast, hmvEq]

/-- Seated `x³` and `x²` close to the curve side. -/
theorem curve_side_of_cube (b : Ecbs.Board) (dst spare : Nat)
    (x : List Nat) (n k bench moves : Nat)
    (hHd : dst < b.sudo_5Board_4home.size) (hDd : dst < b.sudo_5Board_4held.size)
    (hHs : spare < b.sudo_5Board_4home.size) (hDs : spare < b.sudo_5Board_4held.size)
    (hne : spare ≠ dst) (hne' : dst ≠ spare)
    (hheldD : b.sudo_5Board_4held[dst] = true)
    (harrD : b.sudo_5Board_4home[dst] =
      embed (fieldCube n k bench x))
    (hheldS : b.sudo_5Board_4held[spare] = true)
    (harrS : b.sudo_5Board_4home[spare] =
      embed (fieldMul n k bench x x))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx : x.length = n) (hpos : 0 < n)
    (htx : allTritList x)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + 2 * n + 1))
    (hbench : b.sudo_5Board_8bench_on = false)
    (hcube : (fieldCube n k bench x).length = n)
    (hmul : (fieldMul n k bench x x).length = n)
    (htC : allTritList (fieldCube n k bench x))
    (htM : allTritList (fieldMul n k bench x x)) :
    ∃ bW,
      (do
          let b ← add b (dst : Int) (spare : Int) true
          let b ← clear b (spare : Int)
          white0 b (dst : Int)) = .ok bW ∧
        (∀ h : dst < bW.sudo_5Board_4home.size,
          bW.sudo_5Board_4home[dst] = embed (curveSide n k bench x)) ∧
        CloseKeep b bW dst spare ∧
        bW.sudo_5Board_4cost.sudo_5Costs_5moves =
          Int.ofNat (moves + 2 * pegCount (fieldMul n k bench x x) + 1) := by
  obtain ⟨bW, hrun, hhome, hkeep, hmv⟩ := curve_side_close b dst spare
    (fieldCube n k bench x) (fieldMul n k bench x x) n moves
    hHd hDd hHs hDs hne hne' hheldD harrD hheldS harrS hn hcube hmul hpos
    htC htM hm hfit hbench
  refine ⟨bW, hrun, ?_, hkeep, hmv⟩
  rw [curveSide]
  exact hhome

end EcbsLink2.Link2
