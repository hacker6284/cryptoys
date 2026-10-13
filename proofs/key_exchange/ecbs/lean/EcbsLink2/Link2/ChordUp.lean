/-
  Clear the gap, settle the bench into the up, and move the bottom into the
  across. This is the suffix of `chord_tail` after the onto multiply: the bench
  is on and aimed at the up, the up and the across are empty, the gap still
  holds the slope, and the bottom holds the new x. SPEC.md §3 R7 line 156.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Settle
import Lean.Elab.Tactic.Conv.Basic

open Lean Meta Elab Tactic Conv in
elab "zeta1" : conv => do
  let lhs ← getLhs
  match lhs with
  | .letE _ _ val body _ => changeLhs (body.instantiate1 val)
  | _ => throwError "zeta1: not a let"

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem set_fin {α : Type} (a : Array α) (i : Nat) (h₁ h₂ : i < a.size) (v : α) :
    a.set ⟨i, h₁⟩ v = a.set ⟨i, h₂⟩ v := by
  have : (⟨i, h₁⟩ : Fin a.size) = ⟨i, h₂⟩ := Fin.ext rfl
  rw [this]

private theorem set_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) (v : α) :
    a.set ⟨i, ha⟩ v = b.set ⟨i, h ▸ ha⟩ v := by
  cases h
  rfl

private theorem atL_cast {α : Type} (a : Array α) (i : Nat) (h : i < a.size) :
    SudoRt.atL a (i : Int) = .ok a[i] := by
  rw [← ofNat_eq_natCast i]
  exact atL_ofNat a i h

private theorem putL_cast {α : Type} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    SudoRt.putL a (i : Int) v = .ok (a.set ⟨i, h⟩ v) := by
  rw [← ofNat_eq_natCast i]
  exact putL_ofNat a i v h

private theorem pegCount_embed (xs : List Nat) :
    nnz (embed xs).toList = pegCount xs := by
  rw [toList_embed, nnz_embed]
  rfl

private theorem decide_gt_ofNat (a b : Nat) :
    decide (Int.ofNat a > (b : Int)) = decide (b < a) := by
  rw [decide_eq_decide, show (b : Int) = Int.ofNat b from ofNat_eq_natCast b]
  exact ofNat_lt_iff b a

private theorem idx_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

/-- `j` stays in range after `set` replaces a different index. One term, so the
    board the proof builds matches `moveBandCore`. -/
def idxSet {α : Type} (a : Array α) (i : Nat) (hi : i < a.size) (v : α)
    (j : Nat) (hj : j < a.size) : j < (a.set ⟨i, hi⟩ v).size := by
  rw [Array.size_set]
  exact hj

private theorem addI_let {β : Type} (a n : Int) (k : Int → Except SudoRt.Trap β) :
    (let m := n; SudoRt.addI a m >>= k) = (SudoRt.addI a n >>= k) := rfl

private theorem putL_ix {α β : Type} (a : Array α) (i : Nat) (v : α)
    (k : Array α → Except SudoRt.Trap β) :
    (let ix := (i : Int); SudoRt.putL a ix v >>= k) =
      (SudoRt.putL a (i : Int) v >>= k) := rfl

private theorem settle_skip {β : Type} (b : Ecbs.Board)
    (hoff : b.sudo_5Board_8bench_on = false)
    (k : Ecbs.Board → Except SudoRt.Trap β) :
    (Ecbs.settle b >>= fun io => let b := io; k b) = k b := by
  rw [settle_off b hoff, ok_bind]

private theorem need_empty_off (b : Ecbs.Board) (home : Nat)
    (hD : home < b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[home] = false) :
    Ecbs.need_empty b (home : Int) = .ok () := by
  unfold Ecbs.need_empty
  rw [atL_cast _ _ hD, hempty]
  simp only [Bool.not_false, sudoAssert_true, ok_bind, pure_eq_ok]

/-- The board `move_band` leaves before `note_peak`, bench already off. -/
def moveBandCore (b : Ecbs.Board) (dst src : Nat)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (mv sl : Nat) : Ecbs.Board :=
  let b1 := { b with
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨src, hSrcD⟩ false }
  let b2 := { b1 with
    sudo_5Board_4home := b1.sudo_5Board_4home.set ⟨src, hSrcH⟩ (#[] : Array Int) }
  let b3 := { b2 with
    sudo_5Board_4cost := { b2.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat mv } }
  let b4 := { b3 with
    sudo_5Board_4cost := { b3.sudo_5Board_4cost with
      sudo_5Costs_6slides := Int.ofNat sl } }
  let b5 := { b4 with
    sudo_5Board_4home := b4.sudo_5Board_4home.set
      ⟨dst, idxSet b.sudo_5Board_4home src hSrcH (#[] : Array Int) dst hDstH⟩ (embed xs) }
  { b5 with
    sudo_5Board_4held := b5.sudo_5Board_4held.set
      ⟨dst, idxSet b.sudo_5Board_4held src hSrcD false dst hDstD⟩ true }

/-- `move_band` with the bench off. `note_peak` may raise the peak. -/
def moveBandBoard (b : Ecbs.Board) (dst src : Nat)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves slides peak : Nat) : Ecbs.Board :=
  let core := moveBandCore b dst src hSrcH hSrcD hDstH hDstD xs
    (moves + 2 * pegCount xs) (slides + 2 * pegCount xs)
  let occ := countHeld core.sudo_5Board_4held 7
  if peak < occ then
    { core with sudo_5Board_4cost := { core.sudo_5Board_4cost with
      sudo_5Costs_4peak := Int.ofNat occ } }
  else
    core

theorem moveBand_home (b : Ecbs.Board) (dst src : Nat)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves slides peak : Nat) :
    (moveBandBoard b dst src hSrcH hSrcD hDstH hDstD xs moves slides peak).sudo_5Board_4home =
      (b.sudo_5Board_4home.set ⟨src, hSrcH⟩ (#[] : Array Int)).set
        ⟨dst, idxSet b.sudo_5Board_4home src hSrcH (#[] : Array Int) dst hDstH⟩ (embed xs) := by
  unfold moveBandBoard moveBandCore
  dsimp only
  split <;> rfl

theorem moveBand_held (b : Ecbs.Board) (dst src : Nat)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves slides peak : Nat) :
    (moveBandBoard b dst src hSrcH hSrcD hDstH hDstD xs moves slides peak).sudo_5Board_4held =
      (b.sudo_5Board_4held.set ⟨src, hSrcD⟩ false).set
        ⟨dst, idxSet b.sudo_5Board_4held src hSrcD false dst hDstD⟩ true := by
  unfold moveBandBoard moveBandCore
  dsimp only
  split <;> rfl

theorem moveBand_on (b : Ecbs.Board) (dst src : Nat)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves slides peak : Nat) :
    (moveBandBoard b dst src hSrcH hSrcD hDstH hDstD xs moves slides peak).sudo_5Board_8bench_on =
      b.sudo_5Board_8bench_on := by
  unfold moveBandBoard moveBandCore
  dsimp only
  split <;> rfl

theorem moveBand_marker (b : Ecbs.Board) (dst src : Nat)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves slides peak : Nat) :
    (moveBandBoard b dst src hSrcH hSrcD hDstH hDstD xs moves slides peak).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on := by
  unfold moveBandBoard moveBandCore
  dsimp only
  split <;> rfl

theorem moveBand_tier (b : Ecbs.Board) (dst src : Nat)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves slides peak : Nat) :
    (moveBandBoard b dst src hSrcH hSrcD hDstH hDstD xs moves slides peak).sudo_5Board_1t =
      b.sudo_5Board_1t := by
  unfold moveBandBoard moveBandCore
  dsimp only
  split <;> rfl

theorem moveBand_moves (b : Ecbs.Board) (dst src : Nat)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves slides peak : Nat) :
    (moveBandBoard b dst src hSrcH hSrcD hDstH hDstD xs moves slides peak).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + 2 * pegCount xs) := by
  unfold moveBandBoard moveBandCore
  dsimp only
  split <;> rfl

theorem moveBand_slides (b : Ecbs.Board) (dst src : Nat)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves slides peak : Nat) :
    (moveBandBoard b dst src hSrcH hSrcD hDstH hDstD xs moves slides peak).sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (slides + 2 * pegCount xs) := by
  unfold moveBandBoard moveBandCore
  dsimp only
  split <;> rfl

/-- Bench off, `dst` empty, `src` held. `move_band` settles as the identity,
    charges `2 * pegCount` moves and the same number of slides, and writes
    `src` into `dst`. -/
theorem move_band_off (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (moves slides peak : Nat)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hDstH : dst < b.sudo_5Board_4home.size)
    (hDstD : dst < b.sudo_5Board_4held.size)
    (hSrcH : src < b.sudo_5Board_4home.size)
    (hSrcD : src < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[dst] = false)
    (hheld : b.sudo_5Board_4held[src] = true)
    (harr : b.sudo_5Board_4home[src] = embed xs)
    (hf : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hfit2 : FitsLen (2 * pegCount xs))
    (hfitM : FitsLen (moves + 2 * pegCount xs))
    (hfitS : FitsLen (slides + 2 * pegCount xs)) :
    Ecbs.move_band b (dst : Int) (src : Int) =
      .ok (moveBandBoard b dst src hSrcH hSrcD hDstH hDstD xs moves slides peak) := by
  unfold Ecbs.move_band
  rw [settle_skip b hoff]
  rw [need_empty_off b dst hDstD hempty, ok_bind]
  rw [atL_cast _ _ hSrcD, hheld, ok_bind, sudoAssert_true, ok_bind]
  rw [atL_cast _ _ hSrcH, harr, ok_bind]
  rw [putL_ix b.sudo_5Board_4held src false, putL_cast _ _ false hSrcD, ok_bind]
  generalize hb1 :
    ({ b with sudo_5Board_4held := b.sudo_5Board_4held.set ⟨src, hSrcD⟩ false } : Ecbs.Board) = b1
  have hSrcH1 : src < b1.sudo_5Board_4home.size := by
    simpa [← hb1] using hSrcH
  rw [putL_ix _ src (#[] : Array Int)]
  rw [putL_cast b1.sudo_5Board_4home src (#[] : Array Int) hSrcH1, ok_bind]
  generalize hb2 :
    ({ b1 with sudo_5Board_4home := b1.sudo_5Board_4home.set ⟨src, hSrcH1⟩ (#[] : Array Int) } :
      Ecbs.Board) = b2
  have hfs : FitsLen (embed xs).size := by rw [size_embed]; exact hf
  rw [npeg_refines (embed xs) hfs, pegCount_embed, ok_bind]
  rw [show (2 : Int) = Int.ofNat 2 from rfl, mulI_ofNat 2 (pegCount xs) hfit2, ok_bind]
  have hm2 : b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    simp [← hb2, ← hb1, hmoves]
  rw [hm2, addI_let, addI_ofNat moves (2 * pegCount xs) hfitM, ok_bind]
  conv =>
    lhs
    zeta1
    zeta1
    zeta1
  generalize hb3 :
    ({ b2 with sudo_5Board_4cost := { b2.sudo_5Board_4cost with
        sudo_5Costs_5moves := Int.ofNat (moves + 2 * pegCount xs) } } : Ecbs.Board) = b3
  have hs3 : b3.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simp [← hb3, ← hb2, ← hb1, hslides]
  rw [hs3, addI_ofNat slides (2 * pegCount xs) hfitS, ok_bind]
  conv =>
    lhs
    zeta1
    zeta1
    zeta1
  generalize hb4 :
    ({ b3 with sudo_5Board_4cost := { b3.sudo_5Board_4cost with
        sudo_5Costs_6slides := Int.ofNat (slides + 2 * pegCount xs) } } : Ecbs.Board) = b4
  have hDstH4 : dst < b4.sudo_5Board_4home.size := by
    simpa [← hb4, ← hb3, ← hb2, ← hb1] using
      (idxSet b.sudo_5Board_4home src hSrcH (#[] : Array Int) dst hDstH)
  rw [putL_ix b4.sudo_5Board_4home dst (embed xs),
    putL_cast b4.sudo_5Board_4home dst (embed xs) hDstH4, ok_bind]
  conv =>
    lhs
    zeta1
    zeta1
    zeta1
  generalize hb5 :
    ({ b4 with sudo_5Board_4home := b4.sudo_5Board_4home.set ⟨dst, hDstH4⟩ (embed xs) } :
      Ecbs.Board) = b5
  have hDstD5 : dst < b5.sudo_5Board_4held.size := by
    simpa [← hb5, ← hb4, ← hb3, ← hb2, ← hb1] using
      (idxSet b.sudo_5Board_4held src hSrcD false dst hDstD)
  rw [putL_ix b5.sudo_5Board_4held dst true,
    putL_cast b5.sudo_5Board_4held dst true hDstD5, ok_bind]
  conv =>
    lhs
    zeta1
    zeta1
  generalize hb6 :
    ({ b5 with sudo_5Board_4held := b5.sudo_5Board_4held.set ⟨dst, hDstD5⟩ true } : Ecbs.Board) = b6
  have h7c : 7 ≤ b6.sudo_5Board_4held.size := by
    simpa [← hb6, ← hb5, ← hb4, ← hb3, ← hb2, ← hb1, Array.size_set] using h7
  have hpk : b6.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simp [← hb6, ← hb5, ← hb4, ← hb3, ← hb2, ← hb1, hpeak]
  have hcore : b6 = moveBandCore b dst src hSrcH hSrcD hDstH hDstD xs
      (moves + 2 * pegCount xs) (slides + 2 * pegCount xs) := by
    apply board_ext
    case hhome =>
      have hh : b4.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨src, hSrcH⟩ (#[] : Array Int) := by
        have h4 : b4.sudo_5Board_4home = b2.sudo_5Board_4home := by
          simp [← hb4, ← hb3]
        have h2 : b2.sudo_5Board_4home =
            b1.sudo_5Board_4home.set ⟨src, hSrcH1⟩ (#[] : Array Int) := by
          simp [← hb2]
        have h1 : b1.sudo_5Board_4home = b.sudo_5Board_4home := by
          simp [← hb1]
        rw [h4, h2, set_eq h1 src hSrcH1 (#[] : Array Int)]
      simp [moveBandCore, ← hb6, ← hb5]
      refine (set_eq hh dst hDstH4 (embed xs)).trans ?_
      exact set_fin _ _ (hh ▸ hDstH4) _ _
    case hheld =>
      have hh : b5.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨src, hSrcD⟩ false := by
        have h5 : b5.sudo_5Board_4held = b1.sudo_5Board_4held := by
          simp [← hb5, ← hb4, ← hb3, ← hb2]
        have h1 : b1.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨src, hSrcD⟩ false := by
          simp [← hb1]
        rw [h5, h1]
      simp [moveBandCore, ← hb6]
      refine (set_eq hh dst hDstD5 true).trans ?_
      exact set_fin _ _ (hh ▸ hDstD5) _ _
    all_goals
      simp [moveBandCore, ← hb6, ← hb5, ← hb4, ← hb3, ← hb2, ← hb1]
  unfold Ecbs.note_peak
  rw [occupied_refines b6 h7c, ok_bind, hpk]
  rw [ofNat_eq_natCast peak]
  conv =>
    lhs
    arg 1
    zeta1
  rw [decide_gt_ofNat]
  by_cases hlt : peak < countHeld b6.sudo_5Board_4held 7
  · have hcI : decide (peak < countHeld b6.sudo_5Board_4held 7) = true := by
      rw [decide_eq_true_eq]; exact hlt
    rw [hcI]
    simp only [if_true]
    rw [except_bind_pure, pure_eq_ok]
    unfold moveBandBoard
    rw [if_pos (by simpa [hcore] using hlt)]
    simp [hcore]
  · have hcI : decide (peak < countHeld b6.sudo_5Board_4held 7) = false := by
      rw [decide_eq_false_iff_not]; exact hlt
    rw [hcI]
    simp only [Bool.false_eq_true, if_false]
    rw [except_bind_pure, pure_eq_ok]
    unfold moveBandBoard
    rw [if_neg (by simpa [hcore] using hlt)]
    simp [hcore]

/-- Clear the gap, slide the bench into the up, then move the bottom into the
    across. The up becomes the length-`n` bench prefix and the across becomes
    what the bottom held. The gap and the bottom end empty. The bench ends off.
    The marker flag stays. SPEC.md §3 R7 line 156. The settle charges and the
    move's `FitsLen`s stay hypotheses. -/
theorem chord_up_slide (b : Ecbs.Board) (up across bottom gap : Nat)
    (slope x3 benchL : List Nat) (n moves slides peak : Nat)
    (hUpH : up < b.sudo_5Board_4home.size) (hUpD : up < b.sudo_5Board_4held.size)
    (hAcH : across < b.sudo_5Board_4home.size) (hAcD : across < b.sudo_5Board_4held.size)
    (hBotH : bottom < b.sudo_5Board_4home.size) (hBotD : bottom < b.sudo_5Board_4held.size)
    (hGapH : gap < b.sudo_5Board_4home.size) (hGapD : gap < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hneUG : up ≠ gap) (hneUA : up ≠ across) (hneUB : up ≠ bottom)
    (hneAG : across ≠ gap) (hneBG : bottom ≠ gap) (hneAB : across ≠ bottom)
    (hGapT : b.sudo_5Board_4held[gap] = true)
    (hGapA : b.sudo_5Board_4home[gap] = embed slope)
    (hUpE : b.sudo_5Board_4held[up] = false)
    (hAcE : b.sudo_5Board_4held[across] = false)
    (hBotT : b.sudo_5Board_4held[bottom] = true)
    (hBotA : b.sudo_5Board_4home[bottom] = embed x3)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (up : Int))
    (hbench : b.sudo_5Board_5bench = embed benchL)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenS : slope.length = n) (hlenX : x3.length = n)
    (hpos : 0 < benchL.length) (hnle : n ≤ benchL.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < benchL.length, benchL[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen benchL.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfitClear : FitsLen (moves + pegCount slope))
    (hpeg : FitsLen (2 * pegCount (benchL.take n)))
    (hfitSM : FitsLen (moves + pegCount slope + 2 * pegCount (benchL.take n)))
    (hfitSS : FitsLen (slides + 2 * pegCount (benchL.take n)))
    (hfit2 : FitsLen (2 * pegCount x3))
    (hfitMM : FitsLen (moves + pegCount slope + 2 * pegCount (benchL.take n) +
        2 * pegCount x3))
    (hfitMS : FitsLen (slides + 2 * pegCount (benchL.take n) + 2 * pegCount x3)) :
    ∃ b',
      (do
          let b ← Ecbs.clear b (gap : Int)
          let b ← Ecbs.settle b
          Ecbs.move_band b (across : Int) (bottom : Int)) = .ok b' ∧
      (∀ h : up < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[up] = embed (benchL.take n)) ∧
      (∀ h : up < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[up] = true) ∧
      (∀ h : across < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[across] = embed x3) ∧
      (∀ h : across < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[across] = true) ∧
      (∀ h : bottom < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[bottom] = (#[] : Array Int)) ∧
      (∀ h : bottom < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[bottom] = false) ∧
      (∀ h : gap < b'.sudo_5Board_4home.size,
        b'.sudo_5Board_4home[gap] = (#[] : Array Int)) ∧
      (∀ h : gap < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[gap] = false) ∧
      b'.sudo_5Board_8bench_on = false ∧
      b'.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (moves + pegCount slope + 2 * pegCount (benchL.take n) + 2 * pegCount x3) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + 2 * pegCount (benchL.take n) + 2 * pegCount x3) := by
  have hfS : FitsLen slope.length := by rw [hlenS]; exact hf
  have hfX : FitsLen x3.length := by rw [hlenX]; exact hf
  have hclear := clear_held_refines b gap slope moves hGapH hGapD hGapT hGapA hmoves hfS hfitClear
  rw [hclear, ok_bind]
  let mvC := moves + pegCount slope
  let bC := { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨gap, hGapH⟩ (#[] : Array Int)
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨gap, hGapD⟩ false
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat mvC } }
  have hUpHc : up < bC.sudo_5Board_4home.size := by
    simpa [bC, Array.size_set] using hUpH
  have hUpDc : up < bC.sudo_5Board_4held.size := by
    simpa [bC, Array.size_set] using hUpD
  have h7c : 7 ≤ bC.sudo_5Board_4held.size := by
    simpa [bC, Array.size_set] using h7
  have hUpEc : bC.sudo_5Board_4held[up]'(hUpDc) = false := by
    have hne : gap ≠ up := hneUG.symm
    simpa [bC, Array.getElem_set_ne, hne] using hUpE
  have honC : bC.sudo_5Board_8bench_on = true := by simpa [bC] using hon
  have htoC : bC.sudo_5Board_8bench_to = (up : Int) := by simpa [bC] using hto
  have hbenchC : bC.sudo_5Board_5bench = embed benchL := by simpa [bC] using hbench
  have hnC : bC.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by simpa [bC] using hn
  have hmC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by simp [bC]
  have hsC : bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simpa [bC, ofNat_eq_natCast] using hslides
  have hpC : bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simpa [bC, ofNat_eq_natCast] using hpeak
  have hset := settle_refines bC up benchL n mvC slides peak hUpHc hUpDc h7c honC htoC
    hUpEc hbenchC hnC hpos hnle hzero hf hfitL hmC hsC hpC hpeg hfitSM hfitSS
  rw [hset, ok_bind]
  let bS := settleBoard bC up hUpHc hUpDc benchL n mvC slides peak
  let pegY := pegCount (benchL.take n)
  let mvS := mvC + 2 * pegY
  let slS := slides + 2 * pegY
  let pk := if peak < countHeld (bC.sudo_5Board_4held.set ⟨up, hUpDc⟩ true) 7 then
      countHeld (bC.sudo_5Board_4held.set ⟨up, hUpDc⟩ true) 7 else peak
  have hAcHs : across < bS.sudo_5Board_4home.size := by
    simpa [bS, settle_home_eq, Array.size_set, bC] using hAcH
  have hAcDs : across < bS.sudo_5Board_4held.size := by
    simpa [bS, settle_held_eq, Array.size_set, bC] using hAcD
  have hBotHs : bottom < bS.sudo_5Board_4home.size := by
    simpa [bS, settle_home_eq, Array.size_set, bC] using hBotH
  have hBotDs : bottom < bS.sudo_5Board_4held.size := by
    simpa [bS, settle_held_eq, Array.size_set, bC] using hBotD
  have h7s : 7 ≤ bS.sudo_5Board_4held.size := by
    simpa [bS, settle_held_eq, Array.size_set] using h7c
  have hoffS : bS.sudo_5Board_8bench_on = false := by
    simpa [bS] using settle_bench_off bC up hUpHc hUpDc benchL n mvC slides peak
  have hAcEs : bS.sudo_5Board_4held[across]'(hAcDs) = false := by
    have heq := settle_held_eq bC up hUpHc hUpDc benchL n mvC slides peak
    have hget := idx_eq (by simpa [bS] using heq) across
      (by simpa [bS, heq, Array.size_set] using hAcDs)
    have hne : up ≠ across := hneUA
    simpa [Array.getElem_set_ne, hne, bC, Array.getElem_set_ne, hneAG.symm, hAcE] using hget
  have hBotTs : bS.sudo_5Board_4held[bottom]'(hBotDs) = true := by
    have heq := settle_held_eq bC up hUpHc hUpDc benchL n mvC slides peak
    have hget := idx_eq (by simpa [bS] using heq) bottom
      (by simpa [bS, heq, Array.size_set] using hBotDs)
    simpa [Array.getElem_set_ne, hneUB, bC, Array.getElem_set_ne, hneBG.symm, hBotT] using hget
  have hBotAs : bS.sudo_5Board_4home[bottom]'(hBotHs) = embed x3 := by
    have heq := settle_home_eq bC up hUpHc hUpDc benchL n mvC slides peak
    have hget := idx_eq (by simpa [bS] using heq) bottom
      (by simpa [bS, heq, Array.size_set] using hBotHs)
    simpa [Array.getElem_set_ne, hneUB, bC, Array.getElem_set_ne, hneBG.symm, hBotA] using hget
  have hmS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvS := by
    simpa [bS, mvS, mvC, pegY, Nat.add_assoc] using
      settle_moves_eq bC up hUpHc hUpDc benchL n mvC slides peak
  have hsS : bS.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slS := by
    simpa [bS, slS, pegY] using
      settle_slides_eq bC up hUpHc hUpDc benchL n mvC slides peak
  have hpS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk := by
    simpa [bS, pk] using
      settle_peak_eq bC up hUpHc hUpDc benchL n mvC slides peak hpC
  have hmove := move_band_off bS across bottom x3 mvS slS pk hoffS hAcHs hAcDs
    hBotHs hBotDs h7s hAcEs hBotTs hBotAs hfX hmS hsS hpS hfit2
    (by simpa [mvS, mvC, pegY, Nat.add_assoc] using hfitMM)
    (by simpa [slS, pegY] using hfitMS)
  rw [hmove]
  let b' := moveBandBoard bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
  refine ⟨b', rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have hh := moveBand_home bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
    have hget := idx_eq (by simpa [b'] using hh) up (by simpa [b', hh] using h)
    have hUpS : up < bS.sudo_5Board_4home.size := by
      simpa [bS, settle_home_eq, Array.size_set, bC] using hUpH
    have heq := settle_home_eq bC up hUpHc hUpDc benchL n mvC slides peak
    have hpre := idx_eq (by simpa [bS] using heq) up (by simpa [bS, heq] using hUpS)
    simpa [Array.getElem_set_ne, hneUA.symm, Array.getElem_set_ne, hneUB.symm,
      Array.getElem_set_eq, bS, hpre] using hget
  · intro h
    have hh := moveBand_held bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
    have hget := idx_eq (by simpa [b'] using hh) up (by simpa [b', hh] using h)
    have hUpS : up < bS.sudo_5Board_4held.size := by
      simpa [bS, settle_held_eq, Array.size_set, bC] using hUpD
    have heq := settle_held_eq bC up hUpHc hUpDc benchL n mvC slides peak
    have hpre := idx_eq (by simpa [bS] using heq) up (by simpa [bS, heq] using hUpS)
    simpa [Array.getElem_set_ne, hneUA.symm, Array.getElem_set_ne, hneUB.symm,
      Array.getElem_set_eq, hpre] using hget
  · intro h
    have hh := moveBand_home bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
    have hget := idx_eq (by simpa [b'] using hh) across (by simpa [b', hh] using h)
    simpa [Array.getElem_set_eq] using hget
  · intro h
    have hh := moveBand_held bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
    have hget := idx_eq (by simpa [b'] using hh) across (by simpa [b', hh] using h)
    simpa [Array.getElem_set_eq] using hget
  · intro h
    have hh := moveBand_home bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
    have hget := idx_eq (by simpa [b'] using hh) bottom (by simpa [b', hh] using h)
    simpa [Array.getElem_set_ne, hneAB, Array.getElem_set_eq] using hget
  · intro h
    have hh := moveBand_held bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
    have hget := idx_eq (by simpa [b'] using hh) bottom (by simpa [b', hh] using h)
    simpa [Array.getElem_set_ne, hneAB, Array.getElem_set_eq] using hget
  · intro h
    have hh := moveBand_home bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
    have hget := idx_eq (by simpa [b'] using hh) gap h
    rw [Array.getElem_set_ne (h := hneAG), Array.getElem_set_ne (h := hneBG)] at hget
    rw [hget]
    have hGapS : gap < bS.sudo_5Board_4home.size := by
      simpa [bS, settle_home_eq, Array.size_set, bC] using hGapH
    have heq := settle_home_eq bC up hUpHc hUpDc benchL n mvC slides peak
    have hpre := idx_eq (by simpa [bS] using heq) gap hGapS
    simpa [Array.getElem_set_ne, hneUG, bC, Array.getElem_set_eq] using hpre
  · intro h
    have hh := moveBand_held bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
    have hget := idx_eq (by simpa [b'] using hh) gap h
    rw [Array.getElem_set_ne (h := hneAG), Array.getElem_set_ne (h := hneBG)] at hget
    rw [hget]
    have hGapDs : gap < bS.sudo_5Board_4held.size := by
      simpa [bS, settle_held_eq, Array.size_set, bC] using hGapD
    have heq := settle_held_eq bC up hUpHc hUpDc benchL n mvC slides peak
    have hpre := idx_eq (by simpa [bS] using heq) gap hGapDs
    simpa [Array.getElem_set_ne, hneUG, bC, Array.getElem_set_eq] using hpre
  · simpa [b'] using
      (moveBand_on bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk).trans hoffS
  · have hflagS : bS.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := by
      simpa [bS, bC] using settle_marker_eq bC up hUpHc hUpDc benchL n mvC slides peak
    simpa [b', hflagS] using
      moveBand_marker bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
  · have htS : bS.sudo_5Board_1t = b.sudo_5Board_1t := by
      simpa [bS, bC] using settle_tier_eq bC up hUpHc hUpDc benchL n mvC slides peak
    simpa [b', htS] using
      moveBand_tier bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
  · have hszS : bS.sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
      simp [bS, settle_home_eq, Array.size_set, bC]
    simp [b', hszS, moveBand_home, Array.size_set]
  · have hszS : bS.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
      simp [bS, settle_held_eq, Array.size_set, bC]
    simp [b', hszS, moveBand_held, Array.size_set]
  · simpa [b', mvS, mvC, pegY, Nat.add_assoc] using
      moveBand_moves bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk
  · simpa [b', slS, pegY] using
      moveBand_slides bS across bottom hBotHs hBotDs hAcHs hAcDs x3 mvS slS pk

end EcbsLink2.Link2
