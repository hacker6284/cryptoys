/-
  `Ecbs.mirror` and `Ecbs.add` leave the ops array where they found it.
  One pass of the F-form prefix — the `op_fadd` bump, both mirrors, the seven
  multiplies, and the gap add — therefore keeps slot 1 and writes slot 4 once.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Add
import EcbsLink2.Link2.FformOpsMul

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- `set_number` writes a home or the bench. The ops array is neither. -/
theorem set_number_ops (b : Ecbs.Board) (home : Int) (v : Array Int) (b' : Ecbs.Board)
    (h : Ecbs.set_number b home v = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.set_number at h
  dsimp only at h
  cases hw : Ecbs.where_bench b home with
  | error _ =>
    rw [hw] at h
    simp only [error_bind] at h
    cases h
  | ok wb =>
    rw [hw] at h
    simp only [ok_bind] at h
    by_cases hwb : wb = true
    · rw [if_pos hwb, pure_eq_ok] at h
      cases h
      rfl
    · rw [if_neg hwb] at h
      cases hp : SudoRt.putL b.sudo_5Board_4home home v with
      | error _ =>
        rw [hp] at h
        simp only [error_bind] at h
        cases h
      | ok _ =>
        rw [hp] at h
        simp only [ok_bind, pure_eq_ok] at h
        cases h
        rfl

private theorem mirrorCell_ops (v : Array Int) (i : Int) (b : Ecbs.Board)
    (fl : SudoRt.Flow (Array Int × Ecbs.Board) Ecbs.Board)
    (h : mirrorCell v i b = .ok fl) :
    match fl with
    | .cont fs => fs.2.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops
    | .brk fs => fs.2.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops
    | .ret r => r.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold mirrorCell at h
  dsimp only at h
  cases hc : SudoRt.atL v i with
  | error _ =>
    rw [hc] at h
    simp only [error_bind] at h
    cases h
  | ok c =>
    rw [hc] at h
    simp only [ok_bind] at h
    by_cases hz : SudoRt.SEq.beq c (0 : Int) = true
    · rw [hz] at h
      simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok] at h
      cases h
      rfl
    · have hzf : SudoRt.SEq.beq c (0 : Int) = false := eq_false_of_ne_true hz
      rw [hzf] at h
      simp only [Bool.not_false, if_true] at h
      cases hf : Ecbs.flip c with
      | error _ =>
        rw [hf] at h
        simp only [error_bind] at h
        cases h
      | ok f =>
        rw [hf] at h
        simp only [ok_bind] at h
        cases hp : SudoRt.putL v i f with
        | error _ =>
          rw [hp] at h
          simp only [error_bind] at h
          cases h
        | ok _ =>
          rw [hp] at h
          simp only [ok_bind] at h
          cases hm : SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int) with
          | error _ =>
            rw [hm] at h
            simp only [error_bind] at h
            cases h
          | ok _ =>
            rw [hm] at h
            simp only [ok_bind, pure_eq_ok] at h
            cases h
            rfl

private theorem mirrorStep_ops (toV : Int)
    (σ : Int × (Array Int × Ecbs.Board))
    (fl : SudoRt.Flow (Int × (Array Int × Ecbs.Board)) Ecbs.Board)
    (hst : mirrorStep toV σ = .ok fl) :
    match fl with
    | .cont st => st.2.2.sudo_5Board_4cost.sudo_5Costs_3ops =
        σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops
    | .brk st => st.2.2.sudo_5Board_4cost.sudo_5Costs_3ops =
        σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops
    | .ret r => r.sudo_5Board_4cost.sudo_5Costs_3ops =
        σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold mirrorStep at hst
  dsimp only at hst
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at hst
    cases hst
    rfl
  · rw [if_neg hgt] at hst
    cases hb : mirrorCell σ.2.1 σ.1 σ.2.2 with
    | error _ =>
      rw [hb] at hst
      simp only [error_bind] at hst
      cases hst
    | ok flb =>
      rw [hb] at hst
      simp only [ok_bind] at hst
      have hcell := mirrorCell_ops σ.2.1 σ.1 σ.2.2 flb hb
      cases flb with
      | ret r =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hcell
      | brk fs =>
        simp only [pure_eq_ok] at hst
        cases hst
        exact hcell
      | cont fs =>
        dsimp only at hst
        by_cases hlast : (σ.1 == toV) = true
        · simp only [if_pos hlast, pure_eq_ok] at hst
          cases hst
          exact hcell
        · rw [if_neg hlast] at hst
          cases hi : SudoRt.addI σ.1 (1 : Int) with
          | error _ =>
            rw [hi] at hst
            simp only [error_bind] at hst
            cases hst
          | ok _ =>
            rw [hi] at hst
            simp only [ok_bind, pure_eq_ok] at hst
            cases hst
            exact hcell

/-- `Ecbs.mirror` flips coefficients and may add to the move counter. Every ops
    slot stays. -/
theorem mirror_ops (b : Ecbs.Board) (home : Int) (b' : Ecbs.Board)
    (h : Ecbs.mirror b home = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.mirror at h
  dsimp only at h
  cases hg : Ecbs.get_number b home with
  | error _ =>
    rw [hg] at h
    simp only [error_bind] at h
    cases h
  | ok v =>
    rw [hg] at h
    simp only [ok_bind] at h
    cases hsub : SudoRt.subI b.sudo_5Board_1t.sudo_4Tier_1n (1 : Int) with
    | error _ =>
      rw [hsub] at h
      simp only [error_bind] at h
      cases h
    | ok toV =>
      rw [hsub] at h
      simp only [ok_bind] at h
      rw [except_bind_pure] at h
      conv at h =>
        pattern (fun σ : Int × (Array Int × Ecbs.Board) => _)
        change mirrorStep toV
      apply runLoopOn_ok_inv
          (P := fun σ : Int × (Array Int × Ecbs.Board) =>
            σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops =
              b.sudo_5Board_4cost.sudo_5Costs_3ops)
          (Q := fun q : Ecbs.Board =>
            q.sudo_5Board_4cost.sudo_5Costs_3ops =
              b.sudo_5Board_4cost.sudo_5Costs_3ops)
          (h0 := rfl)
          (h := h)
      · intro st st' hs hstep
        exact (mirrorStep_ops toV st (.cont st') hstep).trans hs
      · intro st st' hs hstep
        exact (mirrorStep_ops toV st (.brk st') hstep).trans hs
      · intro st r q hs hstep hr
        simp only [pure_eq_ok] at hr
        cases hr
        exact (mirrorStep_ops toV st (.ret r) hstep).trans hs
      · intro st q hs hq
        cases hsn : Ecbs.set_number st.2.2 home st.2.1 with
        | error _ =>
          rw [hsn] at hq
          simp only [error_bind] at hq
          cases hq
        | ok b1 =>
          rw [hsn] at hq
          simp only [ok_bind, pure_eq_ok] at hq
          cases hq
          exact (set_number_ops st.2.2 home st.2.1 q hsn).trans hs

private theorem addStep_ops (s : Array Int) (toV : Int) (mirror : Bool)
    (σ : Int × (Array Int × Ecbs.Board))
    (fl : SudoRt.Flow (Int × (Array Int × Ecbs.Board)) Ecbs.Board)
    (hst : addStep s toV mirror σ = .ok fl) :
    match fl with
    | .cont st => st.2.2.sudo_5Board_4cost.sudo_5Costs_3ops =
        σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops
    | .brk st => st.2.2.sudo_5Board_4cost.sudo_5Costs_3ops =
        σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops
    | .ret r => r.sudo_5Board_4cost.sudo_5Costs_3ops =
        σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold addStep at hst
  dsimp only at hst
  by_cases hgt : σ.1 > toV
  · rw [if_pos hgt, pure_eq_ok] at hst
    cases hst
    rfl
  · rw [if_neg hgt] at hst
    cases hc : SudoRt.atL s σ.1 with
    | error _ =>
      rw [hc] at hst
      simp only [error_bind] at hst
      cases hst
    | ok c =>
      rw [hc] at hst
      simp only [ok_bind] at hst
      by_cases hz : SudoRt.SEq.beq c (0 : Int) = true
      · rw [hz] at hst
        simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind] at hst
        by_cases hlast : (σ.1 == toV) = true
        · simp only [if_pos hlast, pure_eq_ok] at hst
          cases hst
          rfl
        · rw [if_neg hlast] at hst
          cases hi : SudoRt.addI σ.1 (1 : Int) with
          | error _ =>
            rw [hi] at hst
            simp only [error_bind] at hst
            cases hst
          | ok _ =>
            rw [hi] at hst
            simp only [ok_bind, pure_eq_ok] at hst
            cases hst
            rfl
      · have hzf : SudoRt.SEq.beq c (0 : Int) = false := eq_false_of_ne_true hz
        rw [hzf] at hst
        simp only [Bool.not_false, if_true] at hst
        by_cases hm : mirror = true
        · rw [if_pos hm] at hst
          cases hf : Ecbs.flip c with
          | error _ =>
            rw [hf] at hst
            simp only [error_bind] at hst
            cases hst
          | ok f =>
            rw [hf] at hst
            simp only [ok_bind] at hst
            cases hd : SudoRt.atL σ.2.1 σ.1 with
            | error _ =>
              rw [hd] at hst
              simp only [error_bind] at hst
              cases hst
            | ok cur =>
              rw [hd] at hst
              simp only [ok_bind] at hst
              cases hs : SudoRt.addI cur f with
              | error _ =>
                rw [hs] at hst
                simp only [error_bind] at hst
                cases hst
              | ok sum =>
                rw [hs] at hst
                simp only [ok_bind] at hst
                cases hmod : SudoRt.modI sum (3 : Int) with
                | error _ =>
                  rw [hmod] at hst
                  simp only [error_bind] at hst
                  cases hst
                | ok m =>
                  rw [hmod] at hst
                  simp only [ok_bind] at hst
                  cases hp : SudoRt.putL σ.2.1 σ.1 m with
                  | error _ =>
                    rw [hp] at hst
                    simp only [error_bind] at hst
                    cases hst
                  | ok _ =>
                    rw [hp] at hst
                    simp only [ok_bind] at hst
                    cases hmv : SudoRt.addI σ.2.2.sudo_5Board_4cost.sudo_5Costs_5moves
                        (1 : Int) with
                    | error _ =>
                      rw [hmv] at hst
                      simp only [error_bind] at hst
                      cases hst
                    | ok _ =>
                      rw [hmv] at hst
                      simp only [ok_bind, pure_eq_ok] at hst
                      by_cases hlast : (σ.1 == toV) = true
                      · simp only [if_pos hlast, pure_eq_ok] at hst
                        cases hst
                        rfl
                      · rw [if_neg hlast] at hst
                        cases hi : SudoRt.addI σ.1 (1 : Int) with
                        | error _ =>
                          rw [hi] at hst
                          simp only [error_bind] at hst
                          cases hst
                        | ok _ =>
                          rw [hi] at hst
                          simp only [ok_bind, pure_eq_ok] at hst
                          cases hst
                          rfl
        · rw [if_neg hm] at hst
          cases hd : SudoRt.atL σ.2.1 σ.1 with
          | error _ =>
            rw [hd] at hst
            simp only [error_bind] at hst
            cases hst
          | ok cur =>
            rw [hd] at hst
            simp only [ok_bind] at hst
            cases hs : SudoRt.addI cur c with
            | error _ =>
              rw [hs] at hst
              simp only [error_bind] at hst
              cases hst
            | ok sum =>
              rw [hs] at hst
              simp only [ok_bind] at hst
              cases hmod : SudoRt.modI sum (3 : Int) with
              | error _ =>
                rw [hmod] at hst
                simp only [error_bind] at hst
                cases hst
              | ok m =>
                rw [hmod] at hst
                simp only [ok_bind] at hst
                cases hp : SudoRt.putL σ.2.1 σ.1 m with
                | error _ =>
                  rw [hp] at hst
                  simp only [error_bind] at hst
                  cases hst
                | ok _ =>
                  rw [hp] at hst
                  simp only [ok_bind] at hst
                  cases hmv : SudoRt.addI σ.2.2.sudo_5Board_4cost.sudo_5Costs_5moves
                      (1 : Int) with
                  | error _ =>
                    rw [hmv] at hst
                    simp only [error_bind] at hst
                    cases hst
                  | ok _ =>
                    rw [hmv] at hst
                    simp only [ok_bind, pure_eq_ok] at hst
                    by_cases hlast : (σ.1 == toV) = true
                    · simp only [if_pos hlast, pure_eq_ok] at hst
                      cases hst
                      rfl
                    · rw [if_neg hlast] at hst
                      cases hi : SudoRt.addI σ.1 (1 : Int) with
                      | error _ =>
                        rw [hi] at hst
                        simp only [error_bind] at hst
                        cases hst
                      | ok _ =>
                        rw [hi] at hst
                        simp only [ok_bind, pure_eq_ok] at hst
                        cases hst
                        rfl

/-- `Ecbs.add` writes the destination lane and the move counter. Slot 4, the
    `op_fadd` cell, and every other ops slot stay. -/
theorem add_ops_other (b : Ecbs.Board) (dst src : Int) (mirror : Bool) (b' : Ecbs.Board)
    (h : Ecbs.add b dst src mirror = .ok b') :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold Ecbs.add at h
  dsimp only at h
  cases hv : Ecbs.value b src with
  | error _ =>
    rw [hv] at h
    simp only [error_bind] at h
    cases h
  | ok s =>
    rw [hv] at h
    simp only [ok_bind] at h
    cases hg : Ecbs.get_number b dst with
    | error _ =>
      rw [hg] at h
      simp only [error_bind] at h
      cases h
    | ok d =>
      rw [hg] at h
      simp only [ok_bind] at h
      cases hsub : SudoRt.subI b.sudo_5Board_1t.sudo_4Tier_1n (1 : Int) with
      | error _ =>
        rw [hsub] at h
        simp only [error_bind] at h
        cases h
      | ok toV =>
        rw [hsub] at h
        simp only [ok_bind] at h
        rw [except_bind_pure] at h
        conv at h =>
          pattern (fun σ : Int × (Array Int × Ecbs.Board) => _)
          change addStep s toV mirror
        apply runLoopOn_ok_inv
            (P := fun σ : Int × (Array Int × Ecbs.Board) =>
              σ.2.2.sudo_5Board_4cost.sudo_5Costs_3ops =
                b.sudo_5Board_4cost.sudo_5Costs_3ops)
            (Q := fun q : Ecbs.Board =>
              q.sudo_5Board_4cost.sudo_5Costs_3ops =
                b.sudo_5Board_4cost.sudo_5Costs_3ops)
            (h0 := rfl)
            (h := h)
        · intro st st' hs hstep
          exact (addStep_ops s toV mirror st (.cont st') hstep).trans hs
        · intro st st' hs hstep
          exact (addStep_ops s toV mirror st (.brk st') hstep).trans hs
        · intro st r q hs hstep hr
          simp only [pure_eq_ok] at hr
          cases hr
          exact (addStep_ops s toV mirror st (.ret r) hstep).trans hs
        · intro st q hs hq
          cases hsn : Ecbs.set_number st.2.2 dst st.2.1 with
          | error _ =>
            rw [hsn] at hq
            simp only [error_bind] at hq
            cases hq
          | ok b1 =>
            rw [hsn] at hq
            simp only [ok_bind, pure_eq_ok] at hq
            cases hq
            exact (set_number_ops st.2.2 dst st.2.1 q hsn).trans hs

private theorem putL_fadd_slots (ops : Array Int) (c1 c4 : Nat) (ops' : Array Int)
    (hopsN : ops.size = 5)
    (hop1 : ops[1]? = some ((c1 + 3 : Nat) : Int))
    (hPut : SudoRt.putL ops Ecbs.op_fadd (Int.ofNat (c4 + 1)) = .ok ops') :
    ops'.size = 5 ∧
      ops'[1]? = some ((c1 + 3 : Nat) : Int) ∧
      ops'[4]? = some (Int.ofNat (c4 + 1)) := by
  have hopF : Ecbs.op_fadd = Int.ofNat 4 := rfl
  have h4 : 4 < ops.size := by rw [hopsN]; decide
  rw [hopF, putL_ofNat ops 4 (Int.ofNat (c4 + 1)) h4] at hPut
  cases hPut
  refine ⟨?_, ?_, ?_⟩
  · rw [Array.size_set, hopsN]
  · rw [Array.getElem?_set_ne _ _ _ (by decide : (4 : Nat) ≠ 1), hop1]
  · rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact h4)]
    simp [Array.getElem_set]

private theorem eq_ops_slots {s1 s4 : Option Int}
    (b b' : Ecbs.Board)
    (h : b'.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops)
    (hsz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5)
    (h1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = s1)
    (h4 : b.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = s4) :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = s1 ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = s4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h, hsz]
  · rw [h, h1]
  · rw [h, h4]

private theorem mul_ops_slots
    (b b' : Ecbs.Board) (dst first second : Int) (copySecond onto mirror : Bool)
    {s1 s4 : Option Int}
    (h : Ecbs.mul b dst first second copySecond onto mirror = .ok b')
    (hsz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5)
    (h1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = s1)
    (h4 : b.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = s4) :
    b'.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = s1 ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = s4 := by
  rcases mul_ops_other b dst first second copySecond onto mirror b' h with ⟨hs, ho⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hs, hsz]
  · rw [ho 1 (by decide), h1]
  · rw [ho 4 (by decide), h4]

/-- The F-form prefix bumps slot 4 once and leaves slot 1. Size stays 5. -/
theorem oncomb_prefix_ops
    (bZ b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Ecbs.Board)
    (c1 c4 : Nat) (ops : Array Int) (red : Bool)
    (hopsN : bZ.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5)
    (hop1 : bZ.sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
      some ((c1 + 3 : Nat) : Int))
    (hPut : SudoRt.putL bZ.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_fadd
      (Int.ofNat (c4 + 1)) = .ok ops)
    (hMir : Ecbs.mirror ({ bZ with sudo_5Board_4cost :=
        { bZ.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Ecbs.Board)
        Ecbs.across = .ok b2)
    (hRun : Ecbs.mul b2 Ecbs.across Ecbs.base_across Ecbs.bottom true true false = .ok b3)
    (hMirU : Ecbs.mirror b3 Ecbs.up = .ok b4)
    (hRise : Ecbs.mul b4 Ecbs.up Ecbs.base_up Ecbs.bottom true true red = .ok b5)
    (hU : Ecbs.mul b5 Ecbs.gap Ecbs.up Ecbs.up true false false = .ok b6)
    (hUZ : Ecbs.mul b6 Ecbs.gap Ecbs.bottom Ecbs.gap false false false = .ok b7)
    (hV : Ecbs.mul b7 Ecbs.spare Ecbs.across Ecbs.across true false false = .ok b8)
    (hVZ : Ecbs.mul b8 Ecbs.bottom Ecbs.spare Ecbs.bottom false false false = .ok b9)
    (hSum : Ecbs.mul b9 Ecbs.gap Ecbs.across Ecbs.spare false true false = .ok b10)
    (hAdd : Ecbs.add b10 Ecbs.gap Ecbs.bottom false = .ok b11) :
    b11.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 ∧
      b11.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some ((c1 + 3 : Nat) : Int) ∧
      b11.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = some (Int.ofNat (c4 + 1)) := by
  rcases putL_fadd_slots _ c1 c4 ops hopsN hop1 hPut with ⟨hsz, h1, h4⟩
  have hBump :
      ({ bZ with sudo_5Board_4cost :=
          { bZ.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_3ops =
        ops := rfl
  have hszB : ({ bZ with sudo_5Board_4cost :=
      { bZ.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_3ops.size =
        5 := by rw [hBump, hsz]
  have h1B : ({ bZ with sudo_5Board_4cost :=
      { bZ.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_3ops[1]? =
        some ((c1 + 3 : Nat) : Int) := by rw [hBump, h1]
  have h4B : ({ bZ with sudo_5Board_4cost :=
      { bZ.sudo_5Board_4cost with sudo_5Costs_3ops := ops } } : Ecbs.Board).sudo_5Board_4cost.sudo_5Costs_3ops[4]? =
        some (Int.ofNat (c4 + 1)) := by rw [hBump, h4]
  rcases eq_ops_slots _ b2 (mirror_ops _ Ecbs.across b2 hMir) hszB h1B h4B
    with ⟨hsz2, h12, h42⟩
  rcases mul_ops_slots b2 b3 Ecbs.across Ecbs.base_across Ecbs.bottom true true false
      hRun hsz2 h12 h42 with ⟨hsz3, h13, h43⟩
  rcases eq_ops_slots b3 b4 (mirror_ops b3 Ecbs.up b4 hMirU) hsz3 h13 h43
    with ⟨hsz4, h14, h44⟩
  rcases mul_ops_slots b4 b5 Ecbs.up Ecbs.base_up Ecbs.bottom true true red
      hRise hsz4 h14 h44 with ⟨hsz5, h15, h45⟩
  rcases mul_ops_slots b5 b6 Ecbs.gap Ecbs.up Ecbs.up true false false
      hU hsz5 h15 h45 with ⟨hsz6, h16, h46⟩
  rcases mul_ops_slots b6 b7 Ecbs.gap Ecbs.bottom Ecbs.gap false false false
      hUZ hsz6 h16 h46 with ⟨hsz7, h17, h47⟩
  rcases mul_ops_slots b7 b8 Ecbs.spare Ecbs.across Ecbs.across true false false
      hV hsz7 h17 h47 with ⟨hsz8, h18, h48⟩
  rcases mul_ops_slots b8 b9 Ecbs.bottom Ecbs.spare Ecbs.bottom false false false
      hVZ hsz8 h18 h48 with ⟨hsz9, h19, h49⟩
  rcases mul_ops_slots b9 b10 Ecbs.gap Ecbs.across Ecbs.spare false true false
      hSum hsz9 h19 h49 with ⟨hsz10, h110, h410⟩
  exact eq_ops_slots b10 b11 (add_ops_other b10 Ecbs.gap Ecbs.bottom false b11 hAdd)
    hsz10 h110 h410

end EcbsLink2.Link2
