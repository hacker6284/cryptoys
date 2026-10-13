/-
  The `onto` arm copies the destination home onto a zero strip before the
  schoolbook. The copy is `pref`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MulKeep
import EcbsLink2.Link2.Lists

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem band_copy (xs : List Nat) (m n : Nat)
    (hpos : 0 < n) (hn : n ≤ m) (hx : n ≤ xs.length) (hf : FitsLen n) :
    SudoRt.runLoopOn (ρ := Ecbs.Board) ((0 : Int), embed (List.replicate m 0))
      (fuelRange 0 (Int.ofNat (n - 1)))
      (Ecbs.bandCopyStep (embed xs) (Int.ofNat (n - 1)))
      (fun σ => pure σ.2) (fun _ => pure (embed (pref xs m n))) =
      .ok (embed (pref xs m n)) := by
  have hfuel : fuelRange (0 : Int) (Int.ofNat (n - 1)) =
      fuelRange (Int.ofNat 0) (Int.ofNat (n - 1)) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
  rw [hfuel]
  refine asc_goal (fromN := 0) (toN := n - 1)
    (fun i (st : Array Int) => st = embed (pref xs m i))
    (Nat.zero_le _) ?_ ?_ ?_
  · change embed (List.replicate m 0) = embed (pref xs m 0)
    rw [pref_zero, embed_replicate_zero]
  · intro i st _ hi hI
    have hin : i < n := by omega
    have hix : i < xs.length := by omega
    have hii : i < m := by omega
    have hfi : FitsLen (i + 1) := FitsLen.of_le hf (by omega)
    have hsz : i < (embed (pref xs m i)).size := by
      rw [size_embed, pref_length (Nat.le_of_lt hii) (Nat.le_of_lt hix)]
      exact hii
    refine ⟨embed (pref xs m (i + 1)), ?_, ?_⟩
    · rfl
    · rw [hI]
      have hng : ¬ Int.ofNat i > Int.ofNat (n - 1) := not_gt_cast hi
      simp only [Ecbs.bandCopyStep, hng, if_false]
      rw [atL_embed xs i hix]
      simp only [bind, Except.bind, pure, Except.pure]
      rw [putL_ofNat _ i (Int.ofNat xs[i]) hsz, pref_set (by omega) hix]
      simp only [bind, Except.bind, pure, Except.pure]
      exact asc_tail (n - 1) i hfi _
  · intro st hs
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)] at hs
    rw [hs, pure_eq_ok]

end EcbsLink2.Link2
