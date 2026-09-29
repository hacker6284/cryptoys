/-
  LINK 2. Two-limb `big_factorial`.

  `13!` through `19!` sit in two base-10^9 limbs (`19! < 10^18`, `20!` does not).
  Each step multiplies that accumulator by `i ≤ 19`. The schoolbook product stays
  below `10^18`, so the third scratch limb is zero and trims away.

  The same bound extends `peel_leading` of the zero bigint through `d ≤ 19`.
  The digit is `0 / d!`. The closing multiply is a zero coefficient, so a
  two-limb factorial is never multiplied by a positive digit.

  Not `20!`. Not `51!`. Not a positive two-limb peel. Not `phi_chunk`. Not `v_Hash`.
-/
import MegaDreifach.Link2.Factorial
import MegaDreifach.Link2.Helpers

namespace MegaDreifach.Link2

def mulKStep (toK : Int) (σk : Int × (Array Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Int)) Megadreifach.BigInt) :=
  if σk.fst > toK then
    pure (SudoRt.Flow.brk (σk.fst, σk.snd.fst, σk.snd.snd))
  else do
    let liftK ←
      (if decide (σk.snd.snd > 0) = true then do
        let cur0 ← SudoRt.atL σk.snd.fst σk.fst
        let cur ← SudoRt.addI cur0 σk.snd.snd
        let digit ← SudoRt.modI cur Megadreifach.limb_base
        let out ← SudoRt.putL σk.snd.fst σk.fst digit
        let carry ← SudoRt.divI cur Megadreifach.limb_base
        pure (SudoRt.Flow.cont (out, carry))
      else
        pure (SudoRt.Flow.cont (σk.snd.fst, σk.snd.snd)))
    match liftK with
    | .ret r => pure (SudoRt.Flow.ret r)
    | .brk fs => pure (SudoRt.Flow.brk (σk.fst, fs))
    | .cont fs =>
      if (σk.fst == toK) = true then
        pure (SudoRt.Flow.brk (σk.fst, fs))
      else do
        let i' ← SudoRt.addI σk.fst 1
        pure (SudoRt.Flow.cont (i', fs))

def mulIStep (a b : Megadreifach.BigInt) (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) Megadreifach.BigInt) :=
  if σ.fst > toV then
    pure (SudoRt.Flow.brk (σ.fst, σ.snd))
  else do
    let lift ←
      (do
        let toJ ← SudoRt.subI (SudoRt.listLen b.sudo_6BigInt_5limbs) 1
        let inner ←
          SudoRt.runLoopOn ((0 : Int), σ.snd, (0 : Int))
            (if (0 : Int) > toJ then 1 else (toJ - 0).natAbs + 1)
            (fun σ1 =>
              if σ1.fst > toJ then
                pure (SudoRt.Flow.brk (σ1.fst, σ1.snd.fst, σ1.snd.snd))
              else do
                let liftJ ←
                  (do
                    let ij ← SudoRt.addI σ.fst σ1.fst
                    let cur0 ← SudoRt.atL σ1.snd.fst ij
                    let ai ← SudoRt.atL a.sudo_6BigInt_5limbs σ.fst
                    let bj ← SudoRt.atL b.sudo_6BigInt_5limbs σ1.fst
                    let prod ← SudoRt.mulI ai bj
                    let s1 ← SudoRt.addI cur0 prod
                    let cur ← SudoRt.addI s1 σ1.snd.snd
                    let ij2 ← SudoRt.addI σ.fst σ1.fst
                    let digit ← SudoRt.modI cur Megadreifach.limb_base
                    let out ← SudoRt.putL σ1.snd.fst ij2 digit
                    let carry ← SudoRt.divI cur Megadreifach.limb_base
                    pure (SudoRt.Flow.cont (out, carry)))
                match liftJ with
                | .ret r => pure (SudoRt.Flow.ret r)
                | .brk fs => pure (SudoRt.Flow.brk (σ1.fst, fs))
                | .cont fs =>
                  if (σ1.fst == toJ) = true then
                    pure (SudoRt.Flow.brk (σ1.fst, fs))
                  else do
                    let i' ← SudoRt.addI σ1.fst 1
                    pure (SudoRt.Flow.cont (i', fs)))
            (fun σ1 => do
              let k0 ← SudoRt.addI σ.fst (SudoRt.listLen b.sudo_6BigInt_5limbs)
              let toK ← SudoRt.subI (SudoRt.listLen σ1.snd.fst) 1
              let kLoop ←
                SudoRt.runLoopOn (k0, σ1.snd.fst, σ1.snd.snd)
                  (if k0 > toK then 1 else (toK - k0).natAbs + 1)
                  (mulKStep toK)
                  (fun σk => pure (SudoRt.Flow.cont σk.snd.fst))
                  (fun r => pure (SudoRt.Flow.ret r))
              pure kLoop)
            (fun r => pure (SudoRt.Flow.ret r))
        pure inner :
        Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt))
    match lift with
    | .ret r => pure (SudoRt.Flow.ret r)
    | .brk fs => pure (SudoRt.Flow.brk (σ.fst, fs))
    | .cont fs =>
      if (σ.fst == toV) = true then
        pure (SudoRt.Flow.brk (σ.fst, fs))
      else do
        let i' ← SudoRt.addI σ.fst 1
        pure (SudoRt.Flow.cont (i', fs))

private theorem flowCont_brk (x : Array Int × Int) :
    (match SudoRt.Flow.cont (σ := Array Int × Int) (ρ := Megadreifach.BigInt) x with
      | SudoRt.Flow.ret r =>
        pure (SudoRt.Flow.ret (σ := Int × (Array Int × Int)) (ρ := Megadreifach.BigInt) r)
      | SudoRt.Flow.brk fs =>
        pure (SudoRt.Flow.brk (σ := Int × (Array Int × Int)) (ρ := Megadreifach.BigInt)
          ((0 : Int), fs))
      | SudoRt.Flow.cont fs =>
        pure (SudoRt.Flow.brk (σ := Int × (Array Int × Int)) (ρ := Megadreifach.BigInt)
          ((0 : Int), fs))) =
      (pure (SudoRt.Flow.brk (σ := Int × (Array Int × Int)) (ρ := Megadreifach.BigInt)
          ((0 : Int), x)) :
        Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Int)) Megadreifach.BigInt)) := by
  rfl

private theorem repr_mul (lo hi r : Nat) :
    (lo + limbBase * hi) * r =
      (lo * r) % limbBase +
        limbBase * ((lo * r) / limbBase + hi * r) := by
  have hlow : lo * r = (lo * r) % limbBase + limbBase * ((lo * r) / limbBase) :=
    (Nat.mod_add_div (lo * r) limbBase).symm
  have hL := congrArg (fun n => n + limbBase * (hi * r)) hlow
  have hA :
      ((lo * r) % limbBase + limbBase * ((lo * r) / limbBase)) + limbBase * (hi * r) =
        (lo * r) % limbBase +
          (limbBase * ((lo * r) / limbBase) + limbBase * (hi * r)) := by
    rw [Nat.add_assoc]
  have hM :
      (lo * r) % limbBase +
          (limbBase * ((lo * r) / limbBase) + limbBase * (hi * r)) =
        (lo * r) % limbBase + limbBase * ((lo * r) / limbBase + hi * r) := by
    rw [← Nat.mul_add]
  rw [Nat.add_mul, Nat.mul_assoc]
  exact (hL.trans hA).trans hM

private theorem prod_div_eq (lo hi r : Nat) :
    ((lo + limbBase * hi) * r) / limbBase =
      (lo * r) / limbBase + hi * r := by
  have hq : (lo * r) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hdiv := limb_div_add_mul ((lo * r) % limbBase)
    ((lo * r) / limbBase + hi * r) hq
  have hrepr := repr_mul lo hi r
  rw [← hrepr] at hdiv
  exact hdiv

private theorem prod_mod_eq (lo hi r : Nat) :
    ((lo + limbBase * hi) * r) % limbBase = (lo * r) % limbBase := by
  have hq : (lo * r) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hmod := limb_mod_add_mul ((lo * r) % limbBase)
    ((lo * r) / limbBase + hi * r) hq
  rw [← repr_mul lo hi r] at hmod
  exact hmod

private theorem mid_lt_base (lo hi r : Nat)
    (hp : (lo + limbBase * hi) * r < limbBase ^ 2) :
    (lo * r) / limbBase + hi * r < limbBase := by
  rw [← prod_div_eq lo hi r]
  rw [limbBase_pow2] at hp
  exact div_lt_of_lt_mul limbBase_pos hp

private theorem lo_div_lt (lo r : Nat) (hlo : lo < limbBase) (hr : r < limbBase) :
    (lo * r) / limbBase < limbBase := by
  have hsq := limb_prod_lt_sq hlo hr
  rw [limbBase_pow2] at hsq
  exact div_lt_of_lt_mul limbBase_pos hsq

private theorem hi_mul_lt (lo hi r : Nat)
    (hp : (lo + limbBase * hi) * r < limbBase ^ 2) :
    hi * r < limbBase :=
  Nat.lt_of_le_of_lt (Nat.le_add_left (hi * r) ((lo * r) / limbBase))
    (mid_lt_base lo hi r hp)

private theorem dropTrail_pad0 (a b : Nat) (hb : b ≠ 0) :
    dropTrail [a, b, 0] = [a, b] := by
  simp [dropTrail, hb]

private theorem mulKStep_idle_break (out : Array Int) (k : Nat) :
    mulKStep (Int.ofNat k) (Int.ofNat k, out, (0 : Int)) =
      .ok (SudoRt.Flow.brk (Int.ofNat k, out, (0 : Int))) := by
  unfold mulKStep
  dsimp
  have hngt : ¬ (k : Int) > (k : Int) := Int.lt_irrefl _
  rw [if_neg hngt]
  simp only [show decide ((0 : Int) > 0) = false from by decide, decide_False,
    Bool.false_eq_true, ite_false, bind_pure_flow]
  have hbeq : ((k : Int) == (k : Int)) = true := by simp [beq_int_iff]
  rw [if_pos hbeq]
  exact pure_eq_ok _

private theorem mulKStep_idle_cont (out : Array Int) (k toK : Nat)
    (hk : k < toK) (hfit : FitsLen (k + 1)) :
    mulKStep (Int.ofNat toK) (Int.ofNat k, out, (0 : Int)) =
      .ok (SudoRt.Flow.cont (Int.ofNat (k + 1), out, (0 : Int))) := by
  unfold mulKStep
  dsimp
  have hngt : ¬ (k : Int) > (toK : Int) := ofNat_not_gt (Nat.le_of_lt hk)
  rw [if_neg hngt]
  simp only [show decide ((0 : Int) > 0) = false from by decide, decide_False,
    Bool.false_eq_true, ite_false, bind_pure_flow]
  have hneI : (k : Int) ≠ (toK : Int) := fun h => (Nat.ne_of_lt hk) (Int.ofNat.inj h)
  have hbeq : ((k : Int) == (toK : Int)) = false := by
    simpa [beq_int_iff] using hneI
  have hneB : ¬ (((k : Int) == (toK : Int)) = true) := by
    rw [hbeq]; decide
  rw [if_neg hneB]
  erw [addI_ofNat_one k hfit]
  rw [ok_bind, pure_eq_ok]
  rfl

private theorem mulKStep_place (d0 c : Nat) (hc0 : 0 < c) (hc : c < limbBase) :
    mulKStep (2 : Int) ((1 : Int), embed [d0, 0, 0], Int.ofNat c) =
      .ok (SudoRt.Flow.cont ((2 : Int), embed [d0, c, 0], (0 : Int))) := by
  unfold mulKStep
  dsimp
  have hdec : decide ((c : Int) > (0 : Int)) = true := by
    rw [show (c : Int) = Int.ofNat c from rfl, decide_ofNat_pos, decide_eq_true_eq]
    exact hc0
  rw [hdec]
  simp only [ite_true]
  have hsz : 1 < (embed [d0, 0, 0]).size := by simp [size_embed]
  have hat : SudoRt.atL (embed [d0, 0, 0]) (1 : Int) = .ok (0 : Int) := by
    erw [atL_embed [d0, 0, 0] 1 (by simp)]
    simp
  rw [hat, ok_bind]
  have hcur : FitsLen c := fits_of_lt_limb hc
  erw [addI_zero_nat c hcur]
  rw [ok_bind]
  erw [modI_nat_base c]
  rw [ok_bind]
  have hmod : c % limbBase = c := Nat.mod_eq_of_lt hc
  have hdiv : c / limbBase = 0 := Nat.div_eq_of_lt hc
  rw [hmod]
  erw [putL_ofNat (embed [d0, 0, 0]) 1 (Int.ofNat c) hsz]
  rw [ok_bind]
  erw [divI_nat_base c]
  rw [ok_bind, hdiv, embed3_set1 d0 0 0 c, addI_one_one]
  simp [pure_eq_ok]

/-- Carry propagation across the two high scratch slots. `c` is one limb. -/
private theorem kLoop_low (d0 c : Nat) (hc : c < limbBase) :
    (SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
        ((1 : Int), embed [d0, 0, 0], Int.ofNat c) 2
        (mulKStep (2 : Int))
        (fun σk =>
          pure (SudoRt.Flow.cont (σ := Array Int) (ρ := Megadreifach.BigInt) σk.snd.fst))
        (fun r => pure (SudoRt.Flow.ret (σ := Array Int) r)) :
      Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt)) =
      pure (SudoRt.Flow.cont (embed [d0, c, 0])) := by
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
  by_cases hc0 : c = 0
  · subst hc0
    erw [mulKStep_idle_cont (embed [d0, 0, 0]) 1 2 (by decide) fits2]
    simp only [match_ok_cont]
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    erw [mulKStep_idle_break (embed [d0, 0, 0]) 2]
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
    erw [mulKStep_place d0 c hcpos hc]
    simp only [match_ok_cont]
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    erw [mulKStep_idle_break (embed [d0, c, 0]) 2]

set_option maxHeartbeats 2000000 in
private theorem big_mul_two_limbs_rfl (lo hi r : Nat) (_hr0 : 0 < r) :
    Megadreifach.big_mul (bigOf [lo, hi]) (bigOf [r]) =
      SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
        ((0 : Int), Array.mkArray 3 (0 : Int)) 2
        (mulIStep (bigOf [lo, hi]) (bigOf [r]) (1 : Int))
        (fun σ => do
          let t ← Megadreifach.make_big false σ.2
          pure t)
        (fun r => pure r) := by
  unfold Megadreifach.big_mul
  dsimp [bigOf]
  have hlena : SudoRt.listLen (embed [lo, hi]) = (2 : Int) := by
    rw [listLen_embed]; rfl
  have hlenb : SudoRt.listLen (embed [r]) = (1 : Int) := by
    rw [listLen_embed]; rfl
  rw [hlena]
  have hbeq2 : SudoRt.SEq.beq (2 : Int) (0 : Int) = false := by simp [sEq_int]
  have hbeq1 : SudoRt.SEq.beq (1 : Int) (0 : Int) = false := by simp [sEq_int]
  rw [hbeq2]
  dsimp
  rw [hlenb, hbeq1]
  have hnz : ¬ ((false : Bool) = true) := by decide
  rw [show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind, if_neg hnz]
  rw [addI_two_one, ok_bind, filledL_three, ok_bind, subI_two_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := mulIStep (bigOf [lo, hi]) (bigOf [r]) (1 : Int))
    intro σ
    unfold mulIStep mulKStep
    dsimp [bigOf]
    rfl
  rfl

/-- Low limb of a two-limb × one-limb product. The carry stays below `10^9`. -/
theorem mulIStep_low (lo hi r : Nat) (hlo : lo < limbBase) (hr : r < limbBase) :
    mulIStep (bigOf [lo, hi]) (bigOf [r]) (1 : Int)
        ((0 : Int), Array.mkArray 3 (0 : Int)) =
      .ok (SudoRt.Flow.cont
        ((1 : Int), embed [lo * r % limbBase, lo * r / limbBase, 0])) := by
  have hfit : FitsLen (lo * r) := limb_prod_fits hlo hr
  have hlenb : SudoRt.listLen (embed [r]) = (1 : Int) := by rw [listLen_embed]; rfl
  unfold mulIStep
  dsimp [bigOf]
  rw [hlenb, subI_one_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  have hat0 : SudoRt.atL (Array.mkArray 3 (0 : Int)) (0 : Int) = .ok (0 : Int) := by
    erw [atL_ofNat (Array.mkArray 3 (0 : Int)) 0 (by simp [Array.size_mkArray])]
    simp [Array.getElem_mkArray]
  rw [addI_zero_zero, ok_bind, hat0, ok_bind]
  erw [atL_embed [lo, hi] 0 (by simp)]
  rw [ok_bind]
  erw [atL_embed [r] 0 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_zero]
  erw [mulI_ofNat lo r hfit]
  rw [ok_bind]
  erw [addI_zero_nat (lo * r) hfit]
  rw [ok_bind]
  erw [addI_nat_zero (lo * r) hfit]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base (lo * r)]
  rw [ok_bind]
  erw [putL_ofNat (Array.mkArray 3 (0 : Int)) 0
    (Int.ofNat ((lo * r) % limbBase)) zeros3_size0]
  rw [ok_bind]
  erw [divI_nat_base (lo * r)]
  rw [ok_bind, zeros3_set0 ((lo * r) % limbBase), bind_pure_flow, flowCont_brk]
  simp only [toPure_eq_ok, match_ok_brk]
  have hlenOut : SudoRt.listLen (embed [lo * r % limbBase, 0, 0]) = (3 : Int) := by
    rw [listLen_embed]; rfl
  rw [addI_zero_one, ok_bind, hlenOut, subI_three_one, ok_bind]
  dsimp
  erw [(Int.ofNat_ediv (lo * r) limbBase).symm]
  erw [kLoop_low (lo * r % limbBase) (lo * r / limbBase) (lo_div_lt lo r hlo hr)]
  simp [pure_eq_ok]

private theorem mulIStep_high (lo hi r : Nat)
    (_hlo : lo < limbBase) (hhi : hi < limbBase) (hr : r < limbBase)
    (hp : (lo + limbBase * hi) * r < limbBase ^ 2) :
    mulIStep (bigOf [lo, hi]) (bigOf [r]) (1 : Int)
        ((1 : Int), embed [lo * r % limbBase, lo * r / limbBase, 0]) =
      .ok (SudoRt.Flow.brk
        ((1 : Int),
          embed [((lo + limbBase * hi) * r) % limbBase,
            ((lo + limbBase * hi) * r) / limbBase, 0])) := by
  have hfitR : FitsLen (hi * r) := limb_prod_fits hhi hr
  have hmid := mid_lt_base lo hi r hp
  have hfitM : FitsLen ((lo * r) / limbBase + hi * r) := fits_of_lt_limb hmid
  have hlenb : SudoRt.listLen (embed [r]) = (1 : Int) := by rw [listLen_embed]; rfl
  unfold mulIStep
  dsimp [bigOf]
  rw [hlenb, subI_one_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  erw [addI_nat_zero 1 FitsLen.one]
  rw [ok_bind]
  erw [atL_embed [lo * r % limbBase, lo * r / limbBase, 0] 1 (by simp)]
  rw [ok_bind]
  erw [atL_embed [lo, hi] 1 (by simp)]
  rw [ok_bind]
  erw [atL_embed [r] 0 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [mulI_ofNat hi r hfitR]
  rw [ok_bind]
  erw [addI_ofNat ((lo * r) / limbBase) (hi * r) hfitM]
  rw [ok_bind]
  erw [addI_nat_zero ((lo * r) / limbBase + hi * r) hfitM]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base ((lo * r) / limbBase + hi * r)]
  rw [ok_bind]
  have hmod : ((lo * r) / limbBase + hi * r) % limbBase =
      (lo * r) / limbBase + hi * r := Nat.mod_eq_of_lt hmid
  have hdiv0 : ((lo * r) / limbBase + hi * r) / limbBase = 0 := Nat.div_eq_of_lt hmid
  rw [hmod]
  erw [putL_ofNat (embed [lo * r % limbBase, lo * r / limbBase, 0]) 1
    (Int.ofNat ((lo * r) / limbBase + hi * r)) (by simp [size_embed])]
  rw [ok_bind]
  erw [divI_nat_base ((lo * r) / limbBase + hi * r)]
  rw [ok_bind, hdiv0, embed3_set1 (lo * r % limbBase) (lo * r / limbBase) 0
    ((lo * r) / limbBase + hi * r), bind_pure_flow, flowCont_brk]
  simp only [toPure_eq_ok, match_ok_brk]
  have hlenOut : SudoRt.listLen
      (embed [lo * r % limbBase, (lo * r) / limbBase + hi * r, 0]) = (3 : Int) := by
    rw [listLen_embed]; rfl
  rw [addI_one_one, ok_bind, hlenOut, subI_three_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  erw [mulKStep_idle_break
    (embed [lo * r % limbBase, (lo * r) / limbBase + hi * r, 0]) 2]
  simp [pure_eq_ok, ← prod_mod_eq lo hi r, ← prod_div_eq lo hi r]

/-- Two-limb × one-limb schoolbook product, still below `10^18`. -/
theorem big_mul_two_limbs (lo hi r : Nat)
    (hlo : lo < limbBase) (hhi0 : 0 < hi) (hhi : hi < limbBase)
    (hr0 : 0 < r) (hr : r < limbBase)
    (hp : (lo + limbBase * hi) * r < limbBase ^ 2) :
    Megadreifach.big_mul (bigOf [lo, hi]) (bigOf [r]) =
      .ok (bigNat ((lo + limbBase * hi) * r)) := by
  rw [big_mul_two_limbs_rfl lo hi r hr0]
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ, mulIStep_low lo hi r hlo hr]
  simp only [match_ok_cont]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ,
    mulIStep_high lo hi r hlo hhi hr hp]
  simp only [match_ok_brk, except_bind_pure]
  let p := (lo + limbBase * hi) * r
  have hpge : limbBase ≤ p := by
    have hmul : limbBase * 1 ≤ limbBase * hi :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hhi0)
    have hb : limbBase ≤ limbBase * hi := by simpa using hmul
    exact Nat.le_trans (Nat.le_trans hb (Nat.le_add_left _ _))
      (Nat.le_mul_of_pos_right (lo + limbBase * hi) hr0)
  have hdivNe : p / limbBase ≠ 0 := Nat.ne_of_gt (div_pos_of_le limbBase_pos hpge)
  rw [make_big_false [p % limbBase, p / limbBase, 0] (by simp [fits_le3]),
    dropTrail_pad0 (p % limbBase) (p / limbBase) hdivNe]
  exact congrArg Except.ok (bigNat_two p hpge hp).symm

/-- Multiply a two-limb value by a one-limb factor. The product stays below `10^18`. -/
theorem big_mul_two (a r : Nat) (hr0 : 0 < r) (hr : r < limbBase)
    (hge : limbBase ≤ a) (hlt : a < limbBase ^ 2) (hp : a * r < limbBase ^ 2) :
    Megadreifach.big_mul (bigNat a) (bigNat r) = .ok (bigNat (a * r)) := by
  have ha0 : a % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have ha1lt : a / limbBase < limbBase := by
    rw [limbBase_pow2] at hlt
    exact div_lt_of_lt_mul limbBase_pos hlt
  have ha1 : 0 < a / limbBase := div_pos_of_le limbBase_pos hge
  have hrepr : a % limbBase + limbBase * (a / limbBase) = a :=
    Nat.mod_add_div a limbBase
  rw [bigNat_two a hge hlt, bigNat_limb r hr (Nat.ne_of_gt hr0)]
  have hp' : (a % limbBase + limbBase * (a / limbBase)) * r < limbBase ^ 2 := by
    simpa [hrepr] using hp
  have hmul :=
    big_mul_two_limbs (a % limbBase) (a / limbBase) r ha0 ha1 ha1lt hr0 hr hp'
  simpa [hrepr] using hmul

private theorem big_mul_fact (acc k : Nat) (hk0 : 0 < k) (hk : k < limbBase)
    (hacc : acc < limbBase ^ 2) (hp : acc * k < limbBase ^ 2) :
    Megadreifach.big_mul (bigNat acc) (bigNat k) = .ok (bigNat (acc * k)) := by
  by_cases hlt : acc < limbBase
  · exact big_mul_acc acc k hk0 hk hlt
  · exact big_mul_two acc k hk0 hk (Nat.le_of_not_lt hlt) hacc hp

private theorem nineteen_lt_limb : 19 < limbBase := by
  unfold limbBase
  decide

private theorem fits19 : FitsLen 19 := by
  unfold FitsLen i64MaxNat
  decide

private theorem factStep_wide (n i : Nat) (hlo : 2 ≤ i) (hhi : i ≤ n) (hn : n ≤ 19) :
    factStep (Int.ofNat n) (Int.ofNat i, bigNat (factorial (i - 1))) =
      if i = n then
        .ok (SudoRt.Flow.brk (Int.ofNat i, bigNat (factorial i)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), bigNat (factorial i))) := by
  unfold factStep
  dsimp
  have hngt : ¬ (i : Int) > (n : Int) := ofNat_not_gt hhi
  rw [if_neg hngt]
  have hi0 : i ≠ 0 := by omega
  have hiPos : 0 < i := by omega
  have hilt : i < limbBase :=
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hn) nineteen_lt_limb
  have hfits : FitsLen i := FitsLen.of_le fits19 (Nat.le_trans hhi hn)
  have hacc : factorial (i - 1) < limbBase ^ 2 := factorial_lt_sq (i - 1) (by omega)
  have hp : factorial (i - 1) * i < limbBase ^ 2 := by
    rw [factorial_pred_mul i hiPos]
    exact factorial_lt_sq i (Nat.le_trans hhi hn)
  rw [show (i : Int) = Int.ofNat i from rfl, big_from_int_refines i hfits, ok_bind]
  have hlimbs : limbsOfNat i = [i] := by
    have hq : i / limbBase = 0 := Nat.div_eq_of_lt hilt
    simp [limbsOfNat, hi0, hq, Nat.mod_eq_of_lt hilt]
  rw [hlimbs, ← bigNat_limb i hilt hi0]
  rw [big_mul_fact (factorial (i - 1)) i hiPos hilt hacc hp]
  rw [factorial_pred_mul i hiPos, ok_bind, pure_eq_ok, ok_bind]
  dsimp
  by_cases heq : i = n
  · have hbeq : ((i : Int) == (n : Int)) = true := by simp [beq_int_iff, heq]
    rw [if_pos hbeq, if_pos heq]
    exact pure_eq_ok _
  · have hneI : (i : Int) ≠ (n : Int) := fun h => heq (Int.ofNat.inj h)
    have hbeq : ((i : Int) == (n : Int)) = false := by
      simpa [beq_int_iff] using hneI
    have hneB : ¬ ((i : Int) == (n : Int)) = true := by
      rw [hbeq]; decide
    have hadd := addI_ofNat_one i (FitsLen.of_le fits19 (by omega))
    rw [ofNat_eq_natCast i] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

private theorem factStep_gt (toV i : Int) (r : Megadreifach.BigInt) (h : i > toV) :
    factStep toV (i, r) = .ok (SudoRt.Flow.brk (i, r)) := by
  unfold factStep
  rw [if_pos h]
  rfl

/-- `big_factorial n = n!` for `n ≤ 19`. `13!` through `19!` are two limbs; `20!` is not. -/
theorem big_factorial_two (n : Nat) (hn : n ≤ 19) :
    Megadreifach.big_factorial (n : Int) = .ok (bigNat (factorial n)) := by
  unfold Megadreifach.big_factorial
  rw [show (1 : Int) = Int.ofNat 1 from rfl, big_from_int_refines 1 FitsLen.one, ok_bind]
  have h1lt : (1 : Nat) < limbBase := by unfold limbBase; decide
  have hlimbs1 : limbsOfNat 1 = [1] := by
    have hq : 1 / limbBase = 0 := Nat.div_eq_of_lt h1lt
    have hm : 1 % limbBase = 1 := Nat.mod_eq_of_lt h1lt
    simp [limbsOfNat, hq, hm]
  rw [hlimbs1, ← bigNat_limb 1 (by unfold limbBase; decide) (by decide)]
  dsimp
  by_cases hn1 : n ≤ 1
  · have hgt : (2 : Int) > (n : Int) := by
      have hle : (n : Int) ≤ 1 := Int.ofNat_le.mpr hn1
      omega
    have hf : factorial n = 1 := by
      cases n with
      | zero => rfl
      | succ n =>
        have : n = 0 := by omega
        subst this
        simp [factorial]
    rw [hf, fuelRange_eq, except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise (step' := factStep (n : Int))
      intro σ
      unfold factStep
      dsimp
      rfl
    rw [asc_break (2 : Int) (n : Int) (bigNat 1) _ _ _ hgt
        (factStep_gt (n : Int) 2 (bigNat 1) hgt), pure_eq_ok]
  · have hn2 : 2 ≤ n := by omega
    rw [fuelRange_eq, except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise (step' := factStep (n : Int))
      intro σ
      unfold factStep
      dsimp
      rfl
    rw [show (2 : Int) = Int.ofNat 2 from rfl]
    have hf2 : factorial (2 - 1) = 1 := by simp [factorial]
    rw [← hf2]
    apply chain_loop
      (f := fun i => bigNat (factorial (i - 1)))
      (fromN := 2) (toN := n)
      (hle := hn2)
      (goal := .ok (bigNat (factorial n)))
    · intro i hlo hhi
      have hs := factStep_wide n i hlo hhi hn
      have hsub : (i + 1) - 1 = i := by omega
      simpa [hsub] using hs
    · have hsub : (n + 1) - 1 = n := by omega
      rw [hsub, pure_eq_ok]

private theorem peelDivStep_wide (d f : Nat) (hlo : 2 ≤ f) (hhi : f ≤ d) (hd : d ≤ 19) :
    peelDivStep (Int.ofNat d) (Int.ofNat f, bigOf []) =
      if f = d then
        .ok (SudoRt.Flow.brk (Int.ofNat f, bigOf []))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (f + 1), bigOf [])) := by
  unfold peelDivStep
  dsimp
  have hngt : ¬ (f : Int) > (d : Int) := ofNat_not_gt hhi
  rw [if_neg hngt]
  have hf0 : 0 < f := by omega
  have hflt : f < limbBase :=
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hd) nineteen_lt_limb
  rw [show (f : Int) = Int.ofNat f from rfl, divmod_zero f hf0 hflt, ok_bind]
  rw [show ((bigOf [], (0 : Int)).1) = bigOf [] from rfl, pure_eq_ok, ok_bind]
  dsimp
  by_cases heq : f = d
  · have hbeq : ((f : Int) == (d : Int)) = true := by simp [beq_int_iff, heq]
    rw [if_pos hbeq, if_pos heq]
    exact pure_eq_ok _
  · have hneI : (f : Int) ≠ (d : Int) := fun h => heq (Int.ofNat.inj h)
    have hbeq : ((f : Int) == (d : Int)) = false := by
      simpa [beq_int_iff] using hneI
    have hneB : ¬ ((f : Int) == (d : Int)) = true := by
      rw [hbeq]; decide
    have hadd := addI_ofNat_one f (FitsLen.of_le fits19 (by omega))
    rw [ofNat_eq_natCast f] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

private theorem peel_after_wide (d : Nat) (hd : d ≤ 19) :
    (do
      let idx ← Megadreifach.limb_to_small (bigOf [])
      let fact ← Megadreifach.big_factorial (d : Int)
      let coeff ← Megadreifach.big_from_int idx
      let prod ← Megadreifach.big_mul coeff fact
      let diff ← Megadreifach.mag_sub
        (bigOf []).sudo_6BigInt_5limbs prod.sudo_6BigInt_5limbs
      let rest ← Megadreifach.make_big false diff
      pure (rest, idx)) =
      .ok (bigNat 0, (0 : Int)) := by
  rw [limb_to_small_zero, ok_bind, big_factorial_two d hd, ok_bind,
    show (0 : Int) = Int.ofNat 0 from rfl, big_from_int_refines 0 FitsLen.zero, ok_bind]
  have hlimbs : limbsOfNat 0 = [] := by simp [limbsOfNat]
  rw [hlimbs, big_mul_zero_left, ok_bind]
  dsimp [bigOf]
  rw [mag_sub_zeros, ok_bind, make_big_false [] FitsLen.zero, ok_bind, pure_eq_ok]
  simp [dropTrail, bigNat_zero]

/-- `peel_leading 0 d = (0, 0)` for `d ≤ 19`. The digit is `0 / d!`. -/
theorem peel_leading_zero_two (d : Nat) (hd : d ≤ 19) :
    Megadreifach.peel_leading (bigNat 0) (d : Int) =
      .ok (bigNat 0, (0 : Int)) := by
  rw [bigNat_zero]
  unfold Megadreifach.peel_leading
  dsimp
  rw [fuelRange_eq, except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := peelDivStep (d : Int))
    intro σ
    unfold peelDivStep
    dsimp
    rfl
  by_cases hd2 : 2 ≤ d
  · rw [show (2 : Int) = Int.ofNat 2 from rfl]
    apply chain_loop
      (f := fun _ : Nat => bigOf [])
      (fromN := 2) (toN := d)
      (hle := hd2)
      (goal := .ok (bigNat 0, (0 : Int)))
    · intro i hlo hhi
      exact peelDivStep_wide d i hlo hhi hd
    · exact peel_after_wide d hd
  · have hlt : d < 2 := by omega
    have hgt : (2 : Int) > (d : Int) := by
      have : (d : Int) < 2 := (ofNat_lt_iff d 2).mpr hlt
      omega
    rw [asc_break (2 : Int) (d : Int) (bigOf []) _ _ _ hgt
        (peelDivStep_gt (d : Int) 2 (bigOf []) hgt)]
    exact peel_after_wide d hd

/-- Same zero peel, as the factoradic digit `0 / d!` and remainder `0`. -/
theorem peel_leading_zero_digit_two (d : Nat) (hd : d ≤ 19) :
    Megadreifach.peel_leading (bigNat 0) (d : Int) =
      .ok (bigNat (0 % factorial d), ((0 / factorial d : Nat) : Int)) := by
  have hdiv : 0 / factorial d = 0 := Nat.div_eq_of_lt (factorial_pos d)
  have hmod : 0 % factorial d = 0 := Nat.mod_eq_of_lt (factorial_pos d)
  rw [hdiv, hmod]
  exact peel_leading_zero_two d hd

end MegaDreifach.Link2
