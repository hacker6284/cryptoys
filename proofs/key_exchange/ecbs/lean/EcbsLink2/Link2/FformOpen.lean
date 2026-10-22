/-
  An empty home's `white0` plants `whiteHole0`. That is the peg `start_walk`
  writes into the bottom after the opening copy. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Mul
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem white_arr (n : Nat) (hn : 0 < n) :
    (Array.mkArray n (Int.ofNat 0)).set ⟨0, by rw [Array.size_mkArray]; exact hn⟩ (1 : Int) =
      embed (whiteHole0 n) := by
  cases n with
  | zero => omega
  | succ n =>
    simp [Array.mkArray, List.replicate_succ, whiteHole0, embed, Array.set]

private theorem white_len (n : Nat) (hn : 0 < n) : (whiteHole0 n).length = n := by
  rw [whiteHole0, List.length_cons, List.length_replicate]
  omega

private theorem white_nnz (n : Nat) :
    nnz ((embed (whiteHole0 n)).toList) = 1 := by
  rw [toList_embed, nnz_embed]
  simp [whiteHole0]

private theorem need_empty_off (b : Ecbs.Board) (home : Nat)
    (hD : home < b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[home] = false) :
    Ecbs.need_empty b (Int.ofNat home) = .ok () := by
  unfold Ecbs.need_empty
  rw [atL_ofNat _ home hD, hempty]
  simp only [Bool.not_false, sudoAssert_true, ok_bind, pure_eq_ok]

/-- The board `put` leaves before `note_peak`: the home is `whiteHole0`,
    it is held, and the move counter grew by the one peg. -/
def whitePut (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (n moves : Nat) : Ecbs.Board :=
  let bH := { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (whiteHole0 n)) }
  let bD := { bH with
    sudo_5Board_4held := bH.sudo_5Board_4held.set ⟨home, hD⟩ true }
  { bD with
    sudo_5Board_4cost := { bD.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (moves + 1) } }

/-- An empty home, bench off. `white0` plants a white peg in hole 0. -/
theorem white0_fresh (b : Ecbs.Board) (home n moves peak : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[home] = false)
    (hbench : b.sudo_5Board_8bench_on = false)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < n)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hfitN : FitsLen n) (hfitM : FitsLen (moves + 1)) :
    Ecbs.white0 b (home : Int) =
      .ok (peakBoard (whitePut b home hH hD n moves) peak) := by
  unfold Ecbs.white0
  rw [show (home : Int) = Int.ofNat home from rfl]
  rw [atL_ofNat _ home hD, hempty]
  simp only [ok_bind, Bool.not_false, Bool.true_eq_false, if_false]
  rw [hbench]
  simp only [Bool.false_eq_true, if_false, pure_eq_ok, Bool.not_false, ok_bind]
  rw [hn]
  rw [show ((n : Int)) = Int.ofNat n from rfl, filledL_ofNat, ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl]
  rw [putL_ofNat _ 0 1 (by rw [Array.size_mkArray]; exact hpos), ok_bind]
  have harr := white_arr n hpos
  rw [harr]
  unfold Ecbs.put
  rw [hn]
  have hlen : SudoRt.listLen (embed (whiteHole0 n)) = (n : Int) := by
    rw [listLen_eq, size_embed, white_len n hpos]
    rfl
  rw [sudoAssertEq_int hlen 427, ok_bind]
  rw [need_empty_off b home hD hempty, ok_bind]
  conv => zeta
  rw [putL_ofNat _ home (embed (whiteHole0 n)) hH, ok_bind]
  rw [putL_ofNat _ home true hD, ok_bind]
  have hpeg : Ecbs.npeg (embed (whiteHole0 n)) = .ok (1 : Int) := by
    rw [npeg_refines _ (by rw [size_embed, white_len n hpos]; exact hfitN)]
    rw [white_nnz n]
    rfl
  rw [hpeg, ok_bind]
  rw [hm, addI_ofNat_one moves hfitM, ok_bind]
  simp only [← pure_eq_ok]
  rw [except_bind_pure]
  have hpeak : ({ b with
      sudo_5Board_4home := (b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (whiteHole0 n)))
      sudo_5Board_4held := (b.sudo_5Board_4held.set ⟨home, hD⟩ true)
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_5moves := Int.ofNat (moves + 1) } }).sudo_5Board_4cost.sudo_5Costs_4peak =
      (peak : Int) := by
    simpa using hp
  have h7' : 7 ≤ ({ b with
      sudo_5Board_4home := (b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (whiteHole0 n)))
      sudo_5Board_4held := (b.sudo_5Board_4held.set ⟨home, hD⟩ true)
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_5moves := Int.ofNat (moves + 1) } }).sudo_5Board_4held.size := by
    simpa using h7
  have hnote := note_peak_eq _ peak h7' hpeak
  -- identify that board with whitePut, whose peak field is the incoming peak
  simpa [whitePut, peakBoard] using hnote

end EcbsLink2.Link2
