/-
  One coefficient of `Ecbs.add` with `mirror = true`: flip the source trit
  and add it to the destination in GF(3). A zero source is skipped, which
  is the same as adding zero.
-/
import EcbsLink2.Link2.Mirror

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The mirror arm of one `add` step. `mirror = true` is inlined. -/
def addMirrorCell (s d : Array Int) (i : Int) (b : Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int × Ecbs.Board) Ecbs.Board) :=
  do
    let c ← SudoRt.atL s i
    if !(SudoRt.SEq.beq c (0 : Int)) then
      do
        let f ← Ecbs.flip c
        let cur ← SudoRt.atL d i
        let sum ← SudoRt.addI cur f
        let m ← SudoRt.modI sum (3 : Int)
        let d ← SudoRt.putL d i m
        let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int)
        let b := ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_5moves := mv } } : Ecbs.Board)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (d, b))
    else
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (d, b))

private theorem embed_put (xs : List Nat) (j v : Nat) (hj : j < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat j) (Int.ofNat v) = .ok (embed (xs.set j v)) := by
  have hsz : j < (embed xs).size := by rw [size_embed]; exact hj
  rw [putL_ofNat (embed xs) j (Int.ofNat v) hsz]
  apply congrArg Except.ok
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro k hk hk'
    simp [embed, Array.getElem_set, List.getElem_set]

theorem addMirrorCell_zero (src dst : List Nat) (i : Nat) (b : Ecbs.Board)
    (hi : i < src.length) (hz : src[i] = 0) :
    addMirrorCell (embed src) (embed dst) (Int.ofNat i) b =
      .ok (SudoRt.Flow.cont (embed dst, b)) := by
  unfold addMirrorCell
  rw [atL_embed src i hi, ok_bind, sEq_ofNat_zero, hz]
  simp only [decide_True, Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok]

theorem addMirrorCell_nz (src dst : List Nat) (i moves : Nat) (b : Ecbs.Board)
    (hiS : i < src.length) (hiD : i < dst.length) (hnz : src[i] ≠ 0) (hc : src[i] ≤ 2)
    (hd : dst[i] ≤ 2)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfm : FitsLen (moves + 1)) :
    addMirrorCell (embed src) (embed dst) (Int.ofNat i) b =
      .ok (SudoRt.Flow.cont
        (embed (dst.set i (tritAdd dst[i] (flipTrit src[i]))),
          withMoves b (Int.ofNat (moves + 1)))) := by
  unfold addMirrorCell
  rw [atL_embed src i hiS, ok_bind, sEq_ofNat_zero]
  simp only [hnz, decide_False, Bool.not_false, if_true, ok_bind]
  rw [flip_refines _ hc, ok_bind, atL_embed dst i hiD, ok_bind]
  have hsum : FitsLen (dst[i] + flipTrit src[i]) := by
    have hle : dst[i] + flipTrit src[i] ≤ 4 := by
      have hf : flipTrit src[i] ≤ 2 := by
        unfold flipTrit
        split <;> omega
      omega
    exact fits_small (by omega)
  rw [addI_ofNat _ _ hsum, ok_bind, show (3 : Int) = Int.ofNat 3 from rfl,
    modI_ofNat _ (by decide), ok_bind]
  rw [embed_put dst i ((dst[i] + flipTrit src[i]) % 3) hiD, ok_bind]
  rw [hm, addI_ofNat_one moves hfm, ok_bind, pure_eq_ok]
  simp [withMoves, tritAdd]

/-- `for i = 0 to n - 1` around `addMirrorCell`. Breaks on the last index. -/
def addMirrorStep (src : Array Int) (toV : Int) (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) Ecbs.Board) :=
  let i := σ.1
  let d := σ.2.1
  let b := σ.2.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, (d, b)))
    else
      match ← addMirrorCell src d i b with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs))

end EcbsLink2.Link2
