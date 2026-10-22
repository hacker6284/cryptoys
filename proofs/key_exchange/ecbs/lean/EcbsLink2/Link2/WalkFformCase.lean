/-
  One live white or red cell, in three branches.
  `zero` is an empty affine run: `walkStep` is `none` and `fform_add`
  returns `(false, _)`. `success` is `walkStep = some (true, _)`: the run
  inverts, and `fform_add` takes the live arm. `RunNonUnit` is the remaining
  branch, a nonzero run whose `fieldInv` is `none`. No field hypothesis is
  assumed. A later one slots in by emptying `RunNonUnit`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformAddCell
import EcbsLink2.Link2.FformHframe
import EcbsLink2.Link2.FformCellWalk

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The affine run `baseX − x³`. -/
def affineRun (n k bench : Nat) (baseX px : List Nat) : List Nat :=
  fieldSub n baseX (fieldCube n k bench px)

/-- A nonzero run that `fieldInv` refuses. The success and zero-run proofs
    do not assume this is empty. -/
def RunNonUnit (n k bench : Nat) (baseX px : List Nat) : Prop :=
  affineRun n k bench baseX px ≠ List.replicate n 0 ∧
    fieldInv n k bench (affineRun n k bench baseX px) = none

/-- Every run is zero, invertible, or `RunNonUnit`. -/
theorem cell_run_split (n k bench : Nat) (baseX px : List Nat) :
    affineRun n k bench baseX px = List.replicate n 0 ∨
    (∃ g, fieldInv n k bench (affineRun n k bench baseX px) = some g) ∨
    RunNonUnit n k bench baseX px := by
  by_cases h0 : affineRun n k bench baseX px = List.replicate n 0
  · exact Or.inl h0
  · by_cases hnone : fieldInv n k bench (affineRun n k bench baseX px) = none
    · exact Or.inr (Or.inr ⟨h0, hnone⟩)
    · right; left
      revert hnone
      generalize hfi : fieldInv n k bench (affineRun n k bench baseX px) = o
      clear hfi
      intro hne
      cases o with
      | none => exact absurd rfl hne
      | some g => exact ⟨g, rfl⟩

private theorem bind_ok {ε α β} (m : Except ε α) (a : α) (f : α → Except ε β)
    (h : m = .ok a) : m >>= f = f a := by
  rw [h]
  exact ok_bind a f

private theorem z_arm {ε α} (b : Bool) (t e : Except ε α) (h : b = true) :
    (if b then t else e) = t := by
  subst h
  rfl

private theorem nz_arm {ε α} (b : Bool) (t e : Except ε α) (h : b = false) :
    (if b then t else e) = e := by
  subst h
  rfl

/-- The arm `fform_add` takes once `is_zero` is false. -/
def fformAddLive (b : Board) (red : Bool) : Except SudoRt.Trap (Bool × Board) :=
  mirror b up >>= fun b4 =>
    mul b4 up base_up bottom true true red >>= fun b5 =>
      mul b5 gap up up true false false >>= fun b6 =>
        mul b6 gap bottom gap false false false >>= fun b7 =>
          mul b7 spare across across true false false >>= fun b8 =>
            mul b8 bottom spare bottom false false false >>= fun b9 =>
              mul b9 gap across spare false true false >>= fun b10 =>
                add b10 gap bottom false >>= fun b11 =>
                  fformAddTail b11 red

/-- `fieldInv = some` is not the zero home. -/
theorem field_inv_ne_zero (n k bench : Nat) (x g : List Nat)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (h : fieldInv n k bench x = some g) :
    x ≠ List.replicate n 0 := by
  intro hx
  have hnone : fieldInv n k bench (List.replicate n 0) = none := by
    rw [← specInv_fieldInv]
    exact specInv_zero n k bench hn0 hnb
  rw [hx] at h
  rw [hnone] at h
  cases h

/-- A right-invertible factor keeps a nonzero run nonzero. -/
theorem prod_ne_of_right (n k bench : Nat) (a z w : List Nat)
    (hn : 0 < n) (hk : k < n) (hb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench)
    (ha : allTritList a) (hz : allTritList z) (hw : allTritList w)
    (haL : a.length = n)
    (hne : a ≠ zeroPeg n)
    (hzw : fieldMul n k bench z w = onePeg n) :
    fieldMul n k bench a z ≠ zeroPeg n := by
  intro h0
  exact hne (mul_right_inv_zero n k bench a z w hn hk hb h2 ha hz hw haL hzw h0)

/-- `is_zero` true returns `(false, b3)` and does not enter the live arm. -/
theorem fform_add_zero_flag (b : Board) (red : Bool)
    (t0 t1 : Int) (ops : Array Int) (b2 b3 : Board)
    (hAt : SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd = .ok t0)
    (hInc : SudoRt.addI t0 (1 : Int) = .ok t1)
    (hPut : SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd t1 = .ok ops)
    (hMir : mirror ({ b with sudo_5Board_4cost :=
        { b.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Board) across = .ok b2)
    (hRun : mul b2 across base_across bottom true true false = .ok b3)
    (hZ : is_zero b3 across = .ok true) :
    fform_add b red = .ok (false, b3) := by
  rw [fform_add_binds]
  rw [bind_ok _ _ _ hAt, bind_ok _ _ _ hInc, bind_ok _ _ _ hPut, bind_ok _ _ _ hMir,
    bind_ok _ _ _ hRun, bind_ok _ _ _ hZ]
  rw [z_arm true _ _ rfl, pure_eq_ok]

/-- `is_zero` false is the live arm. -/
theorem fform_add_live_arm (b : Board) (red : Bool)
    (t0 t1 : Int) (ops : Array Int) (b2 b3 : Board)
    (hAt : SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd = .ok t0)
    (hInc : SudoRt.addI t0 (1 : Int) = .ok t1)
    (hPut : SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd t1 = .ok ops)
    (hMir : mirror ({ b with sudo_5Board_4cost :=
        { b.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Board) across = .ok b2)
    (hRun : mul b2 across base_across bottom true true false = .ok b3)
    (hZ : is_zero b3 across = .ok false) :
    fform_add b red = fformAddLive b3 red := by
  rw [fform_add_binds]
  rw [bind_ok _ _ _ hAt, bind_ok _ _ _ hInc, bind_ok _ _ _ hPut, bind_ok _ _ _ hMir,
    bind_ok _ _ _ hRun, bind_ok _ _ _ hZ]
  rw [nz_arm false _ _ rfl]
  rfl

/-- Spec refuses an inverse of `none`, zero or not. -/
theorem walk_step_inv_none (n k bench : Nat) (base acc : List Nat × List Nat)
    (c : Nat) (hc : c = 1 ∨ c = 2)
    (hinv : specInv n k bench (fieldSub n base.1 (fieldCube n k bench acc.1)) = none) :
    walkStep n k bench base true acc c = none := by
  unfold walkStep
  have hc0 : ¬ c = 0 := by
    cases hc with
    | inl h => simp [h]
    | inr h => simp [h]
  have hbad : ¬ (c ≠ 1 ∧ c ≠ 2) := by
    cases hc with
    | inl h => simp [h]
    | inr h => simp [h]
  simp only [pointCube, hc0, if_false, hbad, if_false, if_true]
  unfold chordAdd
  dsimp only
  rw [hinv]

/-- Zero run. The spec returns `none` and the emitted add returns `(false, _)`. -/
theorem walk_fform_zero_run (n k bench : Nat) (baseX baseY px py : List Nat)
    (c : Nat) (b : Board) (red : Bool) (t0 t1 : Int) (ops : Array Int)
    (b2 b3 : Board) (v : List Nat)
    (hc : c = 1 ∨ c = 2) (hn0 : 0 < n) (hnb : n ≤ bench)
    (hrun : affineRun n k bench baseX px = List.replicate n 0)
    (hv : v = List.replicate n 0)
    (hAt : SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd = .ok t0)
    (hInc : SudoRt.addI t0 (1 : Int) = .ok t1)
    (hPut : SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd t1 = .ok ops)
    (hMir : mirror ({ b with sudo_5Board_4cost :=
        { b.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Board) across = .ok b2)
    (hRun : mul b2 across base_across bottom true true false = .ok b3)
    (hZ : is_zero b3 across = .ok (decide (v = List.replicate n 0))) :
    walkStep n k bench (baseX, baseY) true (px, py) c = none ∧
      fform_add b red = .ok (false, b3) ∧
      ¬ RunNonUnit n k bench baseX px := by
  have hsub : fieldSub n baseX (fieldCube n k bench px) = List.replicate n 0 := by
    simpa [affineRun] using hrun
  have hstep := walkStep_empty_run n k bench (baseX, baseY) (px, py) c hc hsub hn0 hnb
  have hZt : is_zero b3 across = .ok true := by
    rw [hZ, hv]
    exact congrArg Except.ok (decide_eq_true rfl)
  have hadd := fform_add_zero_flag b red t0 t1 ops b2 b3 hAt hInc hPut hMir hRun hZt
  refine ⟨hstep, hadd, ?_⟩
  intro hbad
  exact hbad.1 hrun

/-- Success. `walkStep` returns a point, so the run inverts, and `fform_add`
    takes the live arm. This is not `RunNonUnit`. -/
theorem walk_fform_success (n k bench : Nat) (baseX baseY px py ax' ay' : List Nat)
    (c : Nat) (b : Board) (red : Bool) (t0 t1 : Int) (ops : Array Int)
    (b2 b3 : Board) (v z w : List Nat)
    (hc : c = 1 ∨ c = 2) (hn0 : 0 < n) (hk : k < n) (hnb : n ≤ bench)
    (h2 : 2 * (n - 1) < bench)
    (ha : allTritList (affineRun n k bench baseX px))
    (hz : allTritList z) (hw : allTritList w)
    (haL : (affineRun n k bench baseX px).length = n)
    (hzw : fieldMul n k bench z w = onePeg n)
    (hv : v = fieldMul n k bench (affineRun n k bench baseX px) z)
    (hwalk : walkStep n k bench (baseX, baseY) true (px, py) c =
      some (true, (ax', ay')))
    (hAt : SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd = .ok t0)
    (hInc : SudoRt.addI t0 (1 : Int) = .ok t1)
    (hPut : SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd t1 = .ok ops)
    (hMir : mirror ({ b with sudo_5Board_4cost :=
        { b.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Board) across = .ok b2)
    (hRun : mul b2 across base_across bottom true true false = .ok b3)
    (hZ : is_zero b3 across = .ok (decide (v = List.replicate n 0))) :
    (∃ g, fieldInv n k bench (affineRun n k bench baseX px) = some g) ∧
      ¬ RunNonUnit n k bench baseX px ∧
      fform_add b red = fformAddLive b3 red := by
  obtain ⟨g, hspec⟩ :=
    walk_run_inv n k bench baseX baseY px py ax' ay' c hc hwalk
  have hinv : fieldInv n k bench (affineRun n k bench baseX px) = some g := by
    rw [affineRun]
    rw [specInv_fieldInv] at hspec
    exact hspec
  have hne0 : affineRun n k bench baseX px ≠ List.replicate n 0 :=
    field_inv_ne_zero n k bench _ g hn0 hnb hinv
  have hneZ : zeroPeg n = List.replicate n 0 := rfl
  have hprod : fieldMul n k bench (affineRun n k bench baseX px) z ≠
      List.replicate n 0 := by
    intro h0
    have hbad := prod_ne_of_right n k bench (affineRun n k bench baseX px) z w
      hn0 hk hnb h2 ha hz hw haL (by simpa [hneZ] using hne0) hzw
    exact hbad (by simpa [hneZ] using h0)
  have hZf : is_zero b3 across = .ok false := by
    have hvn : v ≠ List.replicate n 0 := by
      intro heq
      exact hprod (heq ▸ hv).symm
    exact run_nz b3 n v hZ hvn
  have hadd := fform_add_live_arm b red t0 t1 ops b2 b3 hAt hInc hPut hMir hRun hZf
  refine ⟨⟨g, hinv⟩, ?_, hadd⟩
  intro hbad
  have hnone : fieldInv n k bench (affineRun n k bench baseX px) = none := hbad.2
  rw [hnone] at hinv
  cases hinv

end EcbsLink2.Link2
