/-
  `fform_add` on a nonzero run. The split binds the prefix into the tail.
  `is_zero` false is the `v ≠ 0` branch. The tail is `cell_on_add`, and the
  board it reads is the one `add_at_of_room` leaves.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformAddSplit
import EcbsLink2.Link2.FformCellStep
import EcbsLink2.Link2.Loop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

attribute [local irreducible] Ecbs.mul Ecbs.add

private theorem bind_ok {ε α β} (m : Except ε α) (a : α) (f : α → Except ε β)
    (h : m = .ok a) : m >>= f = f a := by
  rw [h]
  exact ok_bind a f

private theorem nz_branch {ε α} (b : Bool) (t e : Except ε α) (h : b = false) :
    (if b then t else e) = e := by
  subst h
  rfl

/-- `v ≠ 0` makes the emitted zero-run check false. -/
theorem run_nz (b : Board) (n : Nat) (v : List Nat)
    (h : is_zero b across = .ok (decide (v = List.replicate n 0)))
    (hv : v ≠ List.replicate n 0) :
    is_zero b across = .ok false := by
  rw [h, decide_eq_false hv]

theorem fformAddTail_chain (b : Board) (red : Bool) :
    fformAddTail b red =
      (mul b bottom across bottom false false false >>= fun b =>
        mul b across gap across false false false >>= fun b =>
        mul b across base_across bottom true true false >>= fun b =>
        mul b up gap up false false true >>= fun b =>
        mul b up base_up bottom true true (! red) >>= fun b =>
        clear b gap >>= fun b =>
        pure (true, b)) := by
  unfold fformAddTail
  rfl

/-- The same binds as `fform_add_split`, written so each step can be replaced. -/
theorem fform_add_binds (b : Board) (red : Bool) :
    fform_add b red =
      (SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd >>= fun t0 =>
        SudoRt.addI t0 (1 : Int) >>= fun t1 =>
          SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd t1 >>= fun ops =>
            let b1 : Board :=
              { b with sudo_5Board_4cost :=
                  { b.sudo_5Board_4cost with sudo_5Costs_3ops := ops } }
            mirror b1 across >>= fun b2 =>
              mul b2 across base_across bottom true true false >>= fun b3 =>
                is_zero b3 across >>= fun z =>
                  if z then
                    pure (false, b3)
                  else
                    mirror b3 up >>= fun b4 =>
                      mul b4 up base_up bottom true true red >>= fun b5 =>
                        mul b5 gap up up true false false >>= fun b6 =>
                          mul b6 gap bottom gap false false false >>= fun b7 =>
                            mul b7 spare across across true false false >>= fun b8 =>
                              mul b8 bottom spare bottom false false false >>= fun b9 =>
                                mul b9 gap across spare false true false >>= fun b10 =>
                                  add b10 gap bottom false >>= fun b11 =>
                                    fformAddTail b11 red) := by
  rw [fform_add_split]

/-- Nonzero run: the prefix's `.ok` steps and the tail give `fform_add`. -/
theorem fform_add_nz (b : Board) (red : Bool)
    (t0 t1 : Int) (ops : Array Int)
    (b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 bA : Board)
    (hAt : SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd = .ok t0)
    (hInc : SudoRt.addI t0 (1 : Int) = .ok t1)
    (hPut : SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd t1 = .ok ops)
    (hMir : mirror ({ b with sudo_5Board_4cost :=
        { b.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Board) across = .ok b2)
    (hRun : mul b2 across base_across bottom true true false = .ok b3)
    (hZ : is_zero b3 across = .ok false)
    (hMirU : mirror b3 up = .ok b4)
    (hRise : mul b4 up base_up bottom true true red = .ok b5)
    (hU : mul b5 gap up up true false false = .ok b6)
    (hUZ : mul b6 gap bottom gap false false false = .ok b7)
    (hV : mul b7 spare across across true false false = .ok b8)
    (hVZ : mul b8 bottom spare bottom false false false = .ok b9)
    (hSum : mul b9 gap across spare false true false = .ok b10)
    (hAdd : add b10 gap bottom false = .ok b11)
    (hTail : fformAddTail b11 red = .ok (true, bA)) :
    fform_add b red = .ok (true, bA) := by
  rw [fform_add_binds]
  rw [bind_ok _ _ _ hAt, bind_ok _ _ _ hInc, bind_ok _ _ _ hPut, bind_ok _ _ _ hMir,
    bind_ok _ _ _ hRun, bind_ok _ _ _ hZ]
  rw [nz_branch false _ _ rfl]
  rw [bind_ok _ _ _ hMirU, bind_ok _ _ _ hRise, bind_ok _ _ _ hU, bind_ok _ _ _ hUZ,
    bind_ok _ _ _ hV, bind_ok _ _ _ hVZ, bind_ok _ _ _ hSum, bind_ok _ _ _ hAdd]
  exact hTail

/-- The tail on the board `add_at_of_room` leaves is `CellAt`. -/
theorem cell_at_of_add (b : Board) (lane : List Nat) (n k bench : Nat)
    (u v z x2 y2 : List Nat) (script w h r : Nat)
    (m ctrl mx cOps moves slides hole peak peakS : Nat) (red : Bool)
    (x3 yUp : List Nat)
    (s : AddAt b lane n k bench u v z x2 y2 script w h r
      m ctrl mx cOps moves slides hole peak peakS)
    (hbound : m + 5 < script)
    (hfitM6 : FitsLen (m + 6)) (hfitC6 : FitsLen (ctrl + 12)) (hfops6 : FitsLen (cOps + 6))
    (hf : FitsLen n)
    (hBig : FitsLen (moves + 8 * stepBudget n bench))
    (hSlide : FitsLen (slides + 8 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgapN : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench)
    (hx : fformAcross n k bench x2 u v z =
      fieldMul n k bench x3 (fformBottom n k bench v z))
    (hy : addUp n k bench red y2 u v z =
      fieldMul n k bench yUp (fformBottom n k bench v z)) :
    ∃ b' lane',
      fformAddTail b red = .ok (true, b') ∧
      CellAt b' lane' n k bench v z x2 y2 x3 yUp b.sudo_5Board_1t
        b.sudo_5Board_4home.size b.sudo_5Board_4held.size ∧
      b'.sudo_5Board_9marker_on = true ∧
      (∀ h0 : 0 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[0] = true) ∧
      (∃ moves' slides' ctrl' mark' mx' pk' peakS' hole' cOps',
        TailCharge b' moves' slides' ctrl' mark' mx' pk' peakS' hole' cOps' ∧
        cOps' = cOps + 5 ∧
        ctrl' = ctrl + 10 ∧
        moves' ≤ moves + 24 * stepBudget n bench ∧
        slides' ≤ slides + 16 * n) ∧
      ((1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) →
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
          b.sudo_5Board_4cost.sudo_5Costs_3ops[1]?) ∧
      (∀ h6 : 6 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[6] = false) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  obtain ⟨b', lane', hdo, hC, hslot, hmon, hH0, hcount, h6, hopsSz⟩ :=
    cell_on_add b lane n k bench u v z x2 y2 script w h r
      m ctrl mx cOps moves slides hole peak peakS red x3 yUp s
      hbound hfitM6 hfitC6 hfops6 hf hBig hSlide
      hw0 hh0 hrR hrP hnE hkLe hgapN hsm hnsm hfitB hx hy
  refine ⟨b', lane', ?_, hC, hmon, hH0, hcount, hslot, h6, hopsSz⟩
  rw [fformAddTail_chain]
  exact hdo

/-- A nonzero cell. The add is the one `add_at_of_room` returns, the tail is
    `cell_on_add`, and `is_zero` has taken the `v ≠ 0` branch. -/
theorem fform_add_cell (b : Board) (red : Bool)
    (t0 t1 : Int) (ops : Array Int)
    (b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Board)
    (hAt : SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd = .ok t0)
    (hInc : SudoRt.addI t0 (1 : Int) = .ok t1)
    (hPut : SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops op_fadd t1 = .ok ops)
    (hMir : mirror ({ b with sudo_5Board_4cost :=
        { b.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Board) across = .ok b2)
    (hRun : mul b2 across base_across bottom true true false = .ok b3)
    (hZ : is_zero b3 across = .ok false)
    (hMirU : mirror b3 up = .ok b4)
    (hRise : mul b4 up base_up bottom true true red = .ok b5)
    (hU : mul b5 gap up up true false false = .ok b6)
    (hUZ : mul b6 gap bottom gap false false false = .ok b7)
    (hV : mul b7 spare across across true false false = .ok b8)
    (hVZ : mul b8 bottom spare bottom false false false = .ok b9)
    (hSum : mul b9 gap across spare false true false = .ok b10)
    (hAdd : add b10 gap bottom false = .ok b11)
    (lane : List Nat) (n k bench : Nat)
    (u v z x2 y2 : List Nat) (script w h r : Nat)
    (m ctrl mx cOps moves slides hole peak peakS : Nat)
    (x3 yUp : List Nat)
    (s : AddAt b11 lane n k bench u v z x2 y2 script w h r
      m ctrl mx cOps moves slides hole peak peakS)
    (hbound : m + 5 < script)
    (hfitM6 : FitsLen (m + 6)) (hfitC6 : FitsLen (ctrl + 12)) (hfops6 : FitsLen (cOps + 6))
    (hf : FitsLen n)
    (hBig : FitsLen (moves + 8 * stepBudget n bench))
    (hSlide : FitsLen (slides + 8 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgapN : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench)
    (hx : fformAcross n k bench x2 u v z =
      fieldMul n k bench x3 (fformBottom n k bench v z))
    (hy : addUp n k bench red y2 u v z =
      fieldMul n k bench yUp (fformBottom n k bench v z)) :
    ∃ b' lane',
      fform_add b red = .ok (true, b') ∧
      CellAt b' lane' n k bench v z x2 y2 x3 yUp b11.sudo_5Board_1t
        b11.sudo_5Board_4home.size b11.sudo_5Board_4held.size ∧
      b'.sudo_5Board_9marker_on = true ∧
      (∀ h0 : 0 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[0] = true) ∧
      (∃ moves' slides' ctrl' mark' mx' pk' peakS' hole' cOps',
        TailCharge b' moves' slides' ctrl' mark' mx' pk' peakS' hole' cOps' ∧
        cOps' = cOps + 5 ∧
        ctrl' = ctrl + 10 ∧
        moves' ≤ moves + 24 * stepBudget n bench ∧
        slides' ≤ slides + 16 * n) ∧
      ((1 < b11.sudo_5Board_4cost.sudo_5Costs_3ops.size) →
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
          b11.sudo_5Board_4cost.sudo_5Costs_3ops[1]?) ∧
      (∀ h6 : 6 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[6] = false) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
        b11.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
  obtain ⟨b', lane', hTail, hC, hmon, hH0, hcount, hslot, h6, hopsSz⟩ :=
    cell_at_of_add b11 lane n k bench u v z x2 y2 script w h r
      m ctrl mx cOps moves slides hole peak peakS red x3 yUp s
      hbound hfitM6 hfitC6 hfops6 hf hBig hSlide
      hw0 hh0 hrR hrP hnE hkLe hgapN hsm hnsm hfitB hx hy
  refine ⟨b', lane', ?_, hC, hmon, hH0, hcount, hslot, h6, hopsSz⟩
  exact fform_add_nz b red t0 t1 ops b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b'
    hAt hInc hPut hMir hRun hZ hMirU hRise hU hUZ hV hVZ hSum hAdd hTail

end EcbsLink2.Link2
