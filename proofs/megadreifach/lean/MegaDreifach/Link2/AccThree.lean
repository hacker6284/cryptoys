/-
  LINK 2. Three-limb accumulator × one-limb factor.

  `20!` is three limbs. `21!` through `26!` multiply that accumulator by
  `i ≤ 26`. The product stays below `10^27`, so the fourth scratch limb is
  zero and trims away. `27!` is four limbs.

  Not `27!`. Not `51!`. Not an arbitrary positive two-limb `peel_leading`.
  Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.FactThree

namespace MegaDreifach.Link2

set_option maxHeartbeats 8000000

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem toPure_eq_ok {α} (a : α) :
    (Applicative.toPure.1 a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem bind_pure_flow {σ ρ β} (fl : SudoRt.Flow σ ρ)
    (f : SudoRt.Flow σ ρ → Except SudoRt.Trap β) :
    (pure fl >>= f) = f fl := rfl

private theorem match_ok_brk {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.brk s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onBrk s := by
  rfl

private theorem match_ok_cont {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.cont s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onCont s := by
  rfl

private theorem addI_three_one : SudoRt.addI (3 : Int) (1 : Int) = .ok (4 : Int) := by
  have h : FitsLen (3 + 1) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 3 1 h]
  rfl

private theorem addI_two_one : SudoRt.addI (2 : Int) (1 : Int) = .ok (3 : Int) := by
  have h : FitsLen (2 + 1) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 2 1 h]
  rfl

private theorem addI_one_one : SudoRt.addI (1 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen (1 + 1) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 1 1 h]
  rfl

private theorem addI_zero_one : SudoRt.addI (0 : Int) (1 : Int) = .ok (1 : Int) := by
  erw [addI_ofNat 0 1 FitsLen.one]
  simp [Nat.zero_add]

private theorem addI_zero_zero : SudoRt.addI (0 : Int) (0 : Int) = .ok (0 : Int) := by
  erw [addI_ofNat 0 0 FitsLen.zero]
  simp

private theorem addI_nat_zero (n : Nat) (h : FitsLen n) :
    SudoRt.addI (Int.ofNat n) (0 : Int) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (n + 0) := by simpa [Nat.add_zero] using h
  erw [addI_ofNat n 0 h0]
  simp [Nat.add_zero]

private theorem addI_zero_nat (n : Nat) (h : FitsLen n) :
    SudoRt.addI (0 : Int) (Int.ofNat n) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (0 + n) := by simpa [Nat.zero_add] using h
  erw [addI_ofNat 0 n h0]
  simp [Nat.zero_add]

private theorem subI_one_one : SudoRt.subI (1 : Int) (1 : Int) = .ok (0 : Int) := by
  erw [subI_ofNat_one 1 (by decide) FitsLen.one]
  rfl

private theorem subI_three_one : SudoRt.subI (3 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen 3 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 3 1 h (by decide)]
  rfl

private theorem subI_four_one : SudoRt.subI (4 : Int) (1 : Int) = .ok (3 : Int) := by
  have h : FitsLen 4 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 4 1 h (by decide)]
  rfl

private theorem filledL_four :
    SudoRt.filledL (4 : Int) (0 : Int) = .ok (Array.mkArray 4 (0 : Int)) := by
  erw [filledL_ofNat 4 (0 : Int)]

private theorem modI_nat_base (n : Nat) :
    SudoRt.modI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n % limbBase)) := by
  erw [limb_base_eq, modI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem divI_nat_base (n : Nat) :
    SudoRt.divI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n / limbBase)) := by
  erw [limb_base_eq, divI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem fits2 : FitsLen 2 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits3 : FitsLen 3 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits4 : FitsLen 4 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits26 : FitsLen 26 := by
  unfold FitsLen i64MaxNat
  decide

private theorem zeros4_size0 : 0 < (Array.mkArray 4 (0 : Int)).size := by
  simp [Array.size_mkArray]

private theorem zeros4_set0 (x : Nat) :
    (Array.mkArray 4 (0 : Int)).set ⟨0, zeros4_size0⟩ (Int.ofNat x) =
      embed [x, 0, 0, 0] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate, List.set_cons_zero]

private theorem embed4_set1 (w x y z v : Nat) :
    (embed [w, x, y, z]).set ⟨1, by simp [size_embed]⟩ (Int.ofNat v) =
      embed [w, v, y, z] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

private theorem embed4_set2 (w x y z v : Nat) :
    (embed [w, x, y, z]).set ⟨2, by simp [size_embed]⟩ (Int.ofNat v) =
      embed [w, x, v, z] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

private theorem prod_lt_sq {a b : Nat} (ha : a < limbBase) (hb : b < limbBase) :
    a * b < limbBase ^ 2 := by
  have ha' : a ≤ limbBase - 1 := by omega
  have hb' : b ≤ limbBase - 1 := by omega
  have hmul : a * b ≤ (limbBase - 1) * (limbBase - 1) := Nat.mul_le_mul ha' hb'
  have hconst : (limbBase - 1) * (limbBase - 1) < limbBase ^ 2 := by
    unfold limbBase
    decide
  exact Nat.lt_of_le_of_lt hmul hconst

private theorem prod_fits {a b : Nat} (ha : a < limbBase) (hb : b < limbBase) :
    FitsLen (a * b) :=
  Nat.le_trans (Nat.le_of_lt (prod_lt_sq ha hb)) limb_sq_fits

private theorem div_le_div_right {a b n : Nat} (hn : 0 < n) (h : a ≤ b) : a / n ≤ b / n := by
  rw [Nat.le_div_iff_mul_le hn]
  exact Nat.le_trans (Nat.div_mul_le_self a n) h

private theorem lo_div_lt (lo r : Nat) (hlo : lo < limbBase) (hr : r < limbBase) :
    (lo * r) / limbBase < limbBase := by
  have hsq := prod_lt_sq hlo hr
  rw [limbBase_pow2] at hsq
  exact div_lt_of_lt_mul limbBase_pos hsq

/-- Middle scratch sum of a three-limb × one-limb product stays below `10^18`. -/
private theorem mid_lt_sq (a0 a1 r : Nat) (ha0 : a0 < limbBase) (ha1 : a1 < limbBase)
    (hr : r < limbBase) :
    (a0 * r) / limbBase + a1 * r < limbBase ^ 2 := by
  have ha0' : a0 ≤ limbBase - 1 := by omega
  have ha1' : a1 ≤ limbBase - 1 := by omega
  have hr' : r ≤ limbBase - 1 := by omega
  have h0 : a0 * r ≤ (limbBase - 1) * (limbBase - 1) := Nat.mul_le_mul ha0' hr'
  have h1 : a1 * r ≤ (limbBase - 1) * (limbBase - 1) := Nat.mul_le_mul ha1' hr'
  have hc : (a0 * r) / limbBase ≤ ((limbBase - 1) * (limbBase - 1)) / limbBase :=
    div_le_div_right limbBase_pos h0
  have hdiv : ((limbBase - 1) * (limbBase - 1)) / limbBase = limbBase - 2 := by
    unfold limbBase
    decide
  rw [hdiv] at hc
  have hsum : (a0 * r) / limbBase + a1 * r ≤
      (limbBase - 2) + (limbBase - 1) * (limbBase - 1) :=
    Nat.add_le_add hc h1
  have hlt : (limbBase - 2) + (limbBase - 1) * (limbBase - 1) < limbBase ^ 2 := by
    unfold limbBase
    decide
  exact Nat.lt_of_le_of_lt hsum hlt

private theorem lt_of_mul_lt {a b c : Nat} (_ha : 0 < a) (h : a * b < a * c) : b < c := by
  by_cases hlt : b < c
  · exact hlt
  · have hge : c ≤ b := Nat.le_of_not_lt hlt
    exact absurd h (Nat.not_lt_of_le (Nat.mul_le_mul_left a hge))

/-- Schoolbook expansion of a three-limb × one-limb product. -/
private theorem expand3 (a0 a1 a2 r : Nat) :
    (a0 + limbBase * a1 + limbBase ^ 2 * a2) * r =
      (a0 * r) % limbBase +
        limbBase * (((a0 * r) / limbBase + a1 * r) % limbBase) +
        limbBase ^ 2 *
          (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r) := by
  have hx : a0 * r = (a0 * r) % limbBase + limbBase * ((a0 * r) / limbBase) :=
    (Nat.mod_add_div (a0 * r) limbBase).symm
  have hy : (a0 * r) / limbBase + a1 * r =
      (((a0 * r) / limbBase + a1 * r) % limbBase) +
        limbBase * (((a0 * r) / limbBase + a1 * r) / limbBase) :=
    (Nat.mod_add_div ((a0 * r) / limbBase + a1 * r) limbBase).symm
  let A := (a0 * r) % limbBase
  let C := limbBase * ((a0 * r) / limbBase)
  let D := limbBase * (a1 * r)
  let E := limbBase ^ 2 * (a2 * r)
  let sum := (a0 * r) / limbBase + a1 * r
  let d1 := sum % limbBase
  let c1 := sum / limbBase
  have h1 : (a0 + limbBase * a1 + limbBase ^ 2 * a2) * r =
      (a0 + limbBase * a1) * r + (limbBase ^ 2 * a2) * r :=
    Nat.add_mul (a0 + limbBase * a1) (limbBase ^ 2 * a2) r
  have h2 : (a0 + limbBase * a1) * r + (limbBase ^ 2 * a2) * r =
      a0 * r + (limbBase * a1) * r + (limbBase ^ 2 * a2) * r :=
    congrArg (fun n => n + (limbBase ^ 2 * a2) * r) (Nat.add_mul a0 (limbBase * a1) r)
  have h3 : a0 * r + (limbBase * a1) * r + (limbBase ^ 2 * a2) * r =
      a0 * r + limbBase * (a1 * r) + (limbBase ^ 2 * a2) * r :=
    congrArg (fun n => a0 * r + n + (limbBase ^ 2 * a2) * r) (Nat.mul_assoc limbBase a1 r)
  have h4 : a0 * r + limbBase * (a1 * r) + (limbBase ^ 2 * a2) * r =
      a0 * r + D + E :=
    congrArg (fun n => a0 * r + limbBase * (a1 * r) + n) (Nat.mul_assoc (limbBase ^ 2) a2 r)
  have h5 : a0 * r + D + E = (A + C) + D + E :=
    congrArg (fun n => n + D + E) hx
  have h6 : (A + C) + D + E = A + (C + D) + E :=
    congrArg (fun n => n + E) (Nat.add_assoc A C D)
  have h7 : A + (C + D) + E = A + limbBase * sum + E :=
    congrArg (fun n => A + n + E) (Eq.symm (Nat.mul_add limbBase ((a0 * r) / limbBase) (a1 * r)))
  have h8 : A + limbBase * sum + E = A + limbBase * (d1 + limbBase * c1) + E :=
    congrArg (fun n => A + limbBase * n + E) hy
  have h9 : A + limbBase * (d1 + limbBase * c1) + E =
      A + (limbBase * d1 + limbBase * (limbBase * c1)) + E :=
    congrArg (fun n => A + n + E) (Nat.mul_add limbBase d1 (limbBase * c1))
  have h10 : A + (limbBase * d1 + limbBase * (limbBase * c1)) + E =
      (A + limbBase * d1) + limbBase * (limbBase * c1) + E :=
    congrArg (fun n => n + E) (Eq.symm (Nat.add_assoc A (limbBase * d1) (limbBase * (limbBase * c1))))
  have h11 : (A + limbBase * d1) + limbBase * (limbBase * c1) + E =
      (A + limbBase * d1) + limbBase ^ 2 * c1 + E :=
    congrArg (fun n => (A + limbBase * d1) + n + E)
      (Eq.trans (Eq.symm (Nat.mul_assoc limbBase limbBase c1))
        (congrArg (fun n => n * c1) (Eq.symm limbBase_pow2)))
  have h12 : (A + limbBase * d1) + limbBase ^ 2 * c1 + E =
      A + limbBase * d1 + (limbBase ^ 2 * c1 + E) :=
    Nat.add_assoc (A + limbBase * d1) (limbBase ^ 2 * c1) E
  have h13 : A + limbBase * d1 + (limbBase ^ 2 * c1 + E) =
      A + limbBase * d1 + limbBase ^ 2 * (c1 + a2 * r) :=
    congrArg (fun n => A + limbBase * d1 + n)
      (Eq.symm (Nat.mul_add (limbBase ^ 2) c1 (a2 * r)))
  exact (h1.trans h2).trans (h3.trans (h4.trans (h5.trans (h6.trans (h7.trans
    (h8.trans (h9.trans (h10.trans (h11.trans (h12.trans h13))))))))))

private theorem top_lt (a0 a1 a2 r : Nat)
    (hp : (a0 + limbBase * a1 + limbBase ^ 2 * a2) * r < limbBase ^ 3) :
    ((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r < limbBase := by
  have hexpand := expand3 a0 a1 a2 r
  have hle : limbBase ^ 2 * (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r) ≤
      (a0 + limbBase * a1 + limbBase ^ 2 * a2) * r := by
    rw [hexpand]
    exact Nat.le_add_left _ _
  have hmul : limbBase ^ 2 * (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r) <
      limbBase ^ 2 * limbBase := by
    have hlt : limbBase ^ 2 * (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r) <
        limbBase ^ 3 := Nat.lt_of_le_of_lt hle hp
    simpa [Nat.pow_succ] using hlt
  exact lt_of_mul_lt (Nat.pow_pos limbBase_pos) hmul

private theorem dropTrail_pad0 (a b c : Nat) (hc : c ≠ 0) :
    dropTrail [a, b, c, 0] = [a, b, c] := by
  simp [dropTrail, hc]

private theorem mod_low (q rest : Nat) (hq : q < limbBase) :
    (q + limbBase * rest) % limbBase = q := by
  rw [Nat.add_comm q (limbBase * rest), Nat.mul_add_mod, Nat.mod_eq_of_lt hq]

private theorem div_low (q rest : Nat) (hq : q < limbBase) :
    (q + limbBase * rest) / limbBase = rest := by
  have h := Nat.add_mul_div_right q rest limbBase_pos
  rw [Nat.mul_comm rest limbBase] at h
  rw [h, Nat.div_eq_of_lt hq, Nat.zero_add]

private theorem pack3 (d0 d1 top : Nat) :
    d0 + limbBase * d1 + limbBase ^ 2 * top =
      d0 + limbBase * (d1 + limbBase * top) := by
  calc
    d0 + limbBase * d1 + limbBase ^ 2 * top
        = d0 + limbBase * d1 + limbBase * (limbBase * top) := by
          rw [← Nat.mul_assoc, ← limbBase_pow2]
    _ = d0 + (limbBase * d1 + limbBase * (limbBase * top)) := by rw [Nat.add_assoc]
    _ = d0 + limbBase * (d1 + limbBase * top) := by rw [← Nat.mul_add]

private theorem repr3 (a : Nat) (_hlt : a < limbBase ^ 3) :
    a % limbBase + limbBase * ((a / limbBase) % limbBase) +
        limbBase ^ 2 * ((a / limbBase) / limbBase) = a := by
  have hmid : (a / limbBase) % limbBase + limbBase * ((a / limbBase) / limbBase) =
      a / limbBase := Nat.mod_add_div (a / limbBase) limbBase
  calc
    a % limbBase + limbBase * ((a / limbBase) % limbBase) +
        limbBase ^ 2 * ((a / limbBase) / limbBase)
      = a % limbBase + (limbBase * ((a / limbBase) % limbBase) +
          limbBase * (limbBase * ((a / limbBase) / limbBase))) := by
        rw [← Nat.mul_assoc, ← limbBase_pow2, Nat.add_assoc]
    _ = a % limbBase + limbBase * ((a / limbBase) % limbBase +
          limbBase * ((a / limbBase) / limbBase)) := by rw [← Nat.mul_add]
    _ = a % limbBase + limbBase * (a / limbBase) := by rw [hmid]
    _ = a := Nat.mod_add_div a limbBase

/-! ## Carry across a four-limb scratch buffer -/

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

private theorem mulKStep_place1 (d0 c : Nat) (hc0 : 0 < c) (hc : c < limbBase) :
    mulKStep (3 : Int) ((1 : Int), embed [d0, 0, 0, 0], Int.ofNat c) =
      .ok (SudoRt.Flow.cont ((2 : Int), embed [d0, c, 0, 0], (0 : Int))) := by
  unfold mulKStep
  dsimp
  have hdec : decide ((c : Int) > (0 : Int)) = true := by
    rw [show (c : Int) = Int.ofNat c from rfl, decide_ofNat_pos, decide_eq_true_eq]
    exact hc0
  rw [hdec]
  simp only [ite_true]
  have hsz : 1 < (embed [d0, 0, 0, 0]).size := by simp [size_embed]
  have hat : SudoRt.atL (embed [d0, 0, 0, 0]) (1 : Int) = .ok (0 : Int) := by
    erw [atL_embed [d0, 0, 0, 0] 1 (by simp)]
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
  erw [putL_ofNat (embed [d0, 0, 0, 0]) 1 (Int.ofNat c) hsz]
  rw [ok_bind]
  erw [divI_nat_base c]
  rw [ok_bind, hdiv, embed4_set1 d0 0 0 0 c, addI_one_one]
  simp [pure_eq_ok]

private theorem mulKStep_place2 (d0 d1 c : Nat) (hc0 : 0 < c) (hc : c < limbBase) :
    mulKStep (3 : Int) ((2 : Int), embed [d0, d1, 0, 0], Int.ofNat c) =
      .ok (SudoRt.Flow.cont ((3 : Int), embed [d0, d1, c, 0], (0 : Int))) := by
  unfold mulKStep
  dsimp
  have hdec : decide ((c : Int) > (0 : Int)) = true := by
    rw [show (c : Int) = Int.ofNat c from rfl, decide_ofNat_pos, decide_eq_true_eq]
    exact hc0
  rw [hdec]
  simp only [ite_true]
  have hsz : 2 < (embed [d0, d1, 0, 0]).size := by simp [size_embed]
  have hat : SudoRt.atL (embed [d0, d1, 0, 0]) (2 : Int) = .ok (0 : Int) := by
    erw [atL_embed [d0, d1, 0, 0] 2 (by simp)]
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
  erw [putL_ofNat (embed [d0, d1, 0, 0]) 2 (Int.ofNat c) hsz]
  rw [ok_bind]
  erw [divI_nat_base c]
  rw [ok_bind, hdiv, embed4_set2 d0 d1 0 0 c, addI_two_one]
  simp [pure_eq_ok]

private theorem kLoop0 (d0 c : Nat) (hc : c < limbBase) :
    (SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
        ((1 : Int), embed [d0, 0, 0, 0], Int.ofNat c) 3
        (mulKStep (3 : Int))
        (fun σk =>
          pure (SudoRt.Flow.cont (σ := Array Int) (ρ := Megadreifach.BigInt) σk.snd.fst))
        (fun r => pure (SudoRt.Flow.ret (σ := Array Int) r)) :
      Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt)) =
      pure (SudoRt.Flow.cont (embed [d0, c, 0, 0])) := by
  rw [show (3 : Nat) = 2 + 1 from rfl, runLoopOn_succ]
  by_cases hc0 : c = 0
  · subst hc0
    erw [mulKStep_idle_cont (embed [d0, 0, 0, 0]) 1 3 (by decide) fits2]
    simp only [match_ok_cont]
    rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
    erw [mulKStep_idle_cont (embed [d0, 0, 0, 0]) 2 3 (by decide) fits3]
    simp only [match_ok_cont]
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    erw [mulKStep_idle_break (embed [d0, 0, 0, 0]) 3]
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
    erw [mulKStep_place1 d0 c hcpos hc]
    simp only [match_ok_cont]
    rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
    erw [mulKStep_idle_cont (embed [d0, c, 0, 0]) 2 3 (by decide) fits3]
    simp only [match_ok_cont]
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    erw [mulKStep_idle_break (embed [d0, c, 0, 0]) 3]

private theorem kLoop1 (d0 d1 c : Nat) (hc : c < limbBase) :
    (SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
        ((2 : Int), embed [d0, d1, 0, 0], Int.ofNat c) 2
        (mulKStep (3 : Int))
        (fun σk =>
          pure (SudoRt.Flow.cont (σ := Array Int) (ρ := Megadreifach.BigInt) σk.snd.fst))
        (fun r => pure (SudoRt.Flow.ret (σ := Array Int) r)) :
      Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt)) =
      pure (SudoRt.Flow.cont (embed [d0, d1, c, 0])) := by
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
  by_cases hc0 : c = 0
  · subst hc0
    erw [mulKStep_idle_cont (embed [d0, d1, 0, 0]) 2 3 (by decide) fits3]
    simp only [match_ok_cont]
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    erw [mulKStep_idle_break (embed [d0, d1, 0, 0]) 3]
  · have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
    erw [mulKStep_place2 d0 d1 c hcpos hc]
    simp only [match_ok_cont]
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    erw [mulKStep_idle_break (embed [d0, d1, c, 0]) 3]

/-! ## Three outer digits -/

private theorem big_mul_open3 (a0 a1 a2 r : Nat) :
    Megadreifach.big_mul (bigOf [a0, a1, a2]) (bigOf [r]) =
      SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
        ((0 : Int), Array.mkArray 4 (0 : Int)) 3
        (mulIStep (bigOf [a0, a1, a2]) (bigOf [r]) (2 : Int))
        (fun σ => do
          let t ← Megadreifach.make_big false σ.2
          pure t)
        (fun r => pure r) := by
  unfold Megadreifach.big_mul
  dsimp [bigOf]
  have hlena : SudoRt.listLen (embed [a0, a1, a2]) = (3 : Int) := by
    rw [listLen_embed]; rfl
  have hlenb : SudoRt.listLen (embed [r]) = (1 : Int) := by
    rw [listLen_embed]; rfl
  rw [hlena]
  have hbeq3 : SudoRt.SEq.beq (3 : Int) (0 : Int) = false := by simp [sEq_int]
  have hbeq1 : SudoRt.SEq.beq (1 : Int) (0 : Int) = false := by simp [sEq_int]
  rw [hbeq3]
  dsimp
  rw [hlenb, hbeq1]
  have hnz : ¬ ((false : Bool) = true) := by decide
  rw [show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind, if_neg hnz]
  rw [addI_three_one, ok_bind, filledL_four, ok_bind, subI_three_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := mulIStep (bigOf [a0, a1, a2]) (bigOf [r]) (2 : Int))
    intro σ
    unfold mulIStep mulKStep
    dsimp [bigOf]
    rfl
  rfl

private theorem mulIStep_i0 (a0 a1 a2 r : Nat) (ha0 : a0 < limbBase) (hr : r < limbBase) :
    mulIStep (bigOf [a0, a1, a2]) (bigOf [r]) (2 : Int)
        ((0 : Int), Array.mkArray 4 (0 : Int)) =
      .ok (SudoRt.Flow.cont
        ((1 : Int), embed [(a0 * r) % limbBase, (a0 * r) / limbBase, 0, 0])) := by
  have hfit : FitsLen (a0 * r) := prod_fits ha0 hr
  have hlenb : SudoRt.listLen (embed [r]) = (1 : Int) := by rw [listLen_embed]; rfl
  unfold mulIStep
  dsimp [bigOf]
  rw [hlenb, subI_one_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  have hat0 : SudoRt.atL (Array.mkArray 4 (0 : Int)) (0 : Int) = .ok (0 : Int) := by
    erw [atL_ofNat (Array.mkArray 4 (0 : Int)) 0 (by simp [Array.size_mkArray])]
    simp [Array.getElem_mkArray]
  rw [addI_zero_zero, ok_bind, hat0, ok_bind]
  erw [atL_embed [a0, a1, a2] 0 (by simp)]
  rw [ok_bind]
  erw [atL_embed [r] 0 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_zero]
  erw [mulI_ofNat a0 r hfit]
  rw [ok_bind]
  erw [addI_zero_nat (a0 * r) hfit]
  rw [ok_bind]
  erw [addI_nat_zero (a0 * r) hfit]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base (a0 * r)]
  rw [ok_bind]
  erw [putL_ofNat (Array.mkArray 4 (0 : Int)) 0
    (Int.ofNat ((a0 * r) % limbBase)) zeros4_size0]
  rw [ok_bind]
  erw [divI_nat_base (a0 * r)]
  rw [ok_bind, zeros4_set0 ((a0 * r) % limbBase), bind_pure_flow]
  dsimp [SudoRt.Flow.casesOn]
  simp only [toPure_eq_ok, match_ok_brk]
  have hlenOut : SudoRt.listLen (embed [(a0 * r) % limbBase, 0, 0, 0]) = (4 : Int) := by
    rw [listLen_embed]; rfl
  rw [addI_zero_one, ok_bind, hlenOut, subI_four_one, ok_bind]
  dsimp
  erw [(Int.ofNat_ediv (a0 * r) limbBase).symm]
  erw [kLoop0 ((a0 * r) % limbBase) ((a0 * r) / limbBase) (lo_div_lt a0 r ha0 hr)]
  simp [pure_eq_ok]

private theorem mulIStep_i1 (a0 a1 a2 r : Nat)
    (ha0 : a0 < limbBase) (ha1 : a1 < limbBase) (hr : r < limbBase) :
    mulIStep (bigOf [a0, a1, a2]) (bigOf [r]) (2 : Int)
        ((1 : Int), embed [(a0 * r) % limbBase, (a0 * r) / limbBase, 0, 0]) =
      .ok (SudoRt.Flow.cont
        ((2 : Int),
          embed [(a0 * r) % limbBase,
            ((a0 * r) / limbBase + a1 * r) % limbBase,
            ((a0 * r) / limbBase + a1 * r) / limbBase, 0])) := by
  have hfitR : FitsLen (a1 * r) := prod_fits ha1 hr
  have hmid := mid_lt_sq a0 a1 r ha0 ha1 hr
  have hfitM : FitsLen ((a0 * r) / limbBase + a1 * r) :=
    Nat.le_trans (Nat.le_of_lt hmid) limb_sq_fits
  have hcarry : ((a0 * r) / limbBase + a1 * r) / limbBase < limbBase := by
    rw [limbBase_pow2] at hmid
    exact div_lt_of_lt_mul limbBase_pos hmid
  have hlenb : SudoRt.listLen (embed [r]) = (1 : Int) := by rw [listLen_embed]; rfl
  unfold mulIStep
  dsimp [bigOf]
  rw [hlenb, subI_one_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  erw [addI_nat_zero 1 FitsLen.one]
  rw [ok_bind]
  erw [atL_embed [(a0 * r) % limbBase, (a0 * r) / limbBase, 0, 0] 1 (by simp)]
  rw [ok_bind]
  erw [atL_embed [a0, a1, a2] 1 (by simp)]
  rw [ok_bind]
  erw [atL_embed [r] 0 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [mulI_ofNat a1 r hfitR]
  rw [ok_bind]
  erw [addI_ofNat ((a0 * r) / limbBase) (a1 * r) hfitM]
  rw [ok_bind]
  erw [addI_nat_zero ((a0 * r) / limbBase + a1 * r) hfitM]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base ((a0 * r) / limbBase + a1 * r)]
  rw [ok_bind]
  erw [putL_ofNat (embed [(a0 * r) % limbBase, (a0 * r) / limbBase, 0, 0]) 1
    (Int.ofNat ((((a0 * r) / limbBase + a1 * r) % limbBase))) (by simp [size_embed])]
  rw [ok_bind]
  erw [divI_nat_base ((a0 * r) / limbBase + a1 * r)]
  rw [ok_bind,
    embed4_set1 ((a0 * r) % limbBase) ((a0 * r) / limbBase) 0 0
      (((a0 * r) / limbBase + a1 * r) % limbBase),
    bind_pure_flow]
  dsimp [SudoRt.Flow.casesOn]
  simp only [toPure_eq_ok, match_ok_brk]
  have hlenOut : SudoRt.listLen
      (embed [(a0 * r) % limbBase, ((a0 * r) / limbBase + a1 * r) % limbBase, 0, 0]) =
      (4 : Int) := by rw [listLen_embed]; rfl
  rw [addI_one_one, ok_bind, hlenOut, subI_four_one, ok_bind]
  dsimp
  erw [(Int.ofNat_ediv ((a0 * r) / limbBase + a1 * r) limbBase).symm]
  erw [kLoop1 ((a0 * r) % limbBase) (((a0 * r) / limbBase + a1 * r) % limbBase)
    (((a0 * r) / limbBase + a1 * r) / limbBase) hcarry]
  simp [pure_eq_ok]

private theorem mulIStep_i2 (a0 a1 a2 r : Nat)
    (ha2 : a2 < limbBase) (hr : r < limbBase)
    (hp : (a0 + limbBase * a1 + limbBase ^ 2 * a2) * r < limbBase ^ 3) :
    mulIStep (bigOf [a0, a1, a2]) (bigOf [r]) (2 : Int)
        ((2 : Int),
          embed [(a0 * r) % limbBase,
            ((a0 * r) / limbBase + a1 * r) % limbBase,
            ((a0 * r) / limbBase + a1 * r) / limbBase, 0]) =
      .ok (SudoRt.Flow.brk
        ((2 : Int),
          embed [(a0 * r) % limbBase,
            ((a0 * r) / limbBase + a1 * r) % limbBase,
            ((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r, 0])) := by
  have hfitR : FitsLen (a2 * r) := prod_fits ha2 hr
  have htop := top_lt a0 a1 a2 r hp
  have hfitT : FitsLen (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r) :=
    fits_of_lt_limb htop
  have hmod : (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r) % limbBase =
      ((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r := Nat.mod_eq_of_lt htop
  have hdiv0 : (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r) / limbBase = 0 :=
    Nat.div_eq_of_lt htop
  have hlenb : SudoRt.listLen (embed [r]) = (1 : Int) := by rw [listLen_embed]; rfl
  unfold mulIStep
  dsimp [bigOf]
  rw [hlenb, subI_one_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  erw [addI_nat_zero 2 fits2]
  rw [ok_bind]
  erw [atL_embed [(a0 * r) % limbBase, ((a0 * r) / limbBase + a1 * r) % limbBase,
    ((a0 * r) / limbBase + a1 * r) / limbBase, 0] 2 (by simp)]
  rw [ok_bind]
  erw [atL_embed [a0, a1, a2] 2 (by simp)]
  rw [ok_bind]
  erw [atL_embed [r] 0 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [mulI_ofNat a2 r hfitR]
  rw [ok_bind]
  erw [addI_ofNat (((a0 * r) / limbBase + a1 * r) / limbBase) (a2 * r) hfitT]
  rw [ok_bind]
  erw [addI_nat_zero (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r) hfitT]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r)]
  rw [ok_bind, hmod]
  erw [putL_ofNat
    (embed [(a0 * r) % limbBase, ((a0 * r) / limbBase + a1 * r) % limbBase,
      ((a0 * r) / limbBase + a1 * r) / limbBase, 0]) 2
    (Int.ofNat (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r))
    (by simp [size_embed])]
  rw [ok_bind]
  erw [divI_nat_base (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r)]
  rw [ok_bind, hdiv0,
    embed4_set2 ((a0 * r) % limbBase) (((a0 * r) / limbBase + a1 * r) % limbBase)
      (((a0 * r) / limbBase + a1 * r) / limbBase) 0
      (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r),
    bind_pure_flow]
  dsimp [SudoRt.Flow.casesOn]
  simp only [toPure_eq_ok, match_ok_brk]
  have hlenOut : SudoRt.listLen
      (embed [(a0 * r) % limbBase, ((a0 * r) / limbBase + a1 * r) % limbBase,
        ((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r, 0]) = (4 : Int) := by
    rw [listLen_embed]; rfl
  rw [addI_two_one, ok_bind, hlenOut, subI_four_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  erw [mulKStep_idle_break
    (embed [(a0 * r) % limbBase, ((a0 * r) / limbBase + a1 * r) % limbBase,
      ((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r, 0]) 3]
  simp [pure_eq_ok]

/--
  Three-limb × one-limb schoolbook product whose value stays below `10^27`.
  The fourth scratch limb is zero.
-/
theorem big_mul_acc3_limbs (a0 a1 a2 r : Nat)
    (ha0 : a0 < limbBase) (ha1 : a1 < limbBase) (ha2_0 : 0 < a2) (ha2 : a2 < limbBase)
    (hr0 : 0 < r) (hr : r < limbBase)
    (hp : (a0 + limbBase * a1 + limbBase ^ 2 * a2) * r < limbBase ^ 3) :
    Megadreifach.big_mul (bigOf [a0, a1, a2]) (bigOf [r]) =
      .ok (bigNat ((a0 + limbBase * a1 + limbBase ^ 2 * a2) * r)) := by
  rw [big_mul_open3 a0 a1 a2 r]
  rw [show (3 : Nat) = 2 + 1 from rfl, runLoopOn_succ, mulIStep_i0 a0 a1 a2 r ha0 hr]
  simp only [match_ok_cont]
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ, mulIStep_i1 a0 a1 a2 r ha0 ha1 hr]
  simp only [match_ok_cont]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, mulIStep_i2 a0 a1 a2 r ha2 hr hp]
  simp only [match_ok_brk, except_bind_pure]
  let p := (a0 + limbBase * a1 + limbBase ^ 2 * a2) * r
  have hexpand := expand3 a0 a1 a2 r
  have hpge : limbBase ^ 2 ≤ p := by
    have ha2le : 1 ≤ a2 := Nat.succ_le_of_lt ha2_0
    have hlimb : limbBase ^ 2 ≤ limbBase ^ 2 * a2 := by
      simpa using Nat.mul_le_mul_left (limbBase ^ 2) ha2le
    have hsum : limbBase ^ 2 * a2 ≤ a0 + limbBase * a1 + limbBase ^ 2 * a2 :=
      Nat.le_add_left _ _
    have ha : limbBase ^ 2 ≤ a0 + limbBase * a1 + limbBase ^ 2 * a2 :=
      Nat.le_trans hlimb hsum
    exact Nat.le_trans ha (Nat.le_mul_of_pos_right _ hr0)
  have htop0 : ((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r ≠ 0 := by
    have hpos : 0 < a2 * r := Nat.mul_pos ha2_0 hr0
    have : 0 < ((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r :=
      Nat.lt_of_lt_of_le hpos (Nat.le_add_left _ _)
    exact Nat.ne_of_gt this
  have hd0lt : (a0 * r) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hd1lt : ((a0 * r) / limbBase + a1 * r) % limbBase < limbBase :=
    Nat.mod_lt _ limbBase_pos
  have hpack : p =
      (a0 * r) % limbBase +
        limbBase * (((a0 * r) / limbBase + a1 * r) % limbBase +
          limbBase * (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r)) :=
    hexpand.trans (pack3 ((a0 * r) % limbBase)
      (((a0 * r) / limbBase + a1 * r) % limbBase)
      (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r))
  have hdig0 : p % limbBase = (a0 * r) % limbBase := by
    rw [hpack, mod_low _ _ hd0lt]
  have hdiv : p / limbBase =
      ((a0 * r) / limbBase + a1 * r) % limbBase +
        limbBase * (((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r) := by
    rw [hpack, div_low _ _ hd0lt]
  have hdig1 : (p / limbBase) % limbBase = ((a0 * r) / limbBase + a1 * r) % limbBase := by
    rw [hdiv, mod_low _ _ hd1lt]
  have hdig2 : (p / limbBase) / limbBase =
      ((a0 * r) / limbBase + a1 * r) / limbBase + a2 * r := by
    rw [hdiv, div_low _ _ hd1lt]
  rw [← hdig0, ← hdig1, ← hdig2]
  rw [make_big_false [p % limbBase, (p / limbBase) % limbBase, (p / limbBase) / limbBase, 0]
      (by simpa using fits4),
    dropTrail_pad0 (p % limbBase) ((p / limbBase) % limbBase) ((p / limbBase) / limbBase)
      (by simpa [hdig2] using htop0)]
  exact congrArg Except.ok (bigNat_three p hpge hp).symm

/--
  Multiply a three-limb value by a one-limb factor. The product stays below
  `10^27` (the fourth scratch limb is zero). `10^18 ≤ a`, so the third limb
  of `a` is nonzero and the product's third limb is nonzero.
-/
theorem big_mul_acc3 (a r : Nat) (hr0 : 0 < r) (hr : r < limbBase)
    (hge : limbBase ^ 2 ≤ a) (hlt : a < limbBase ^ 3) (hp : a * r < limbBase ^ 3) :
    Megadreifach.big_mul (bigNat a) (bigNat r) = .ok (bigNat (a * r)) := by
  have ha0 : a % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have ha1 : (a / limbBase) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have ha2lt : (a / limbBase) / limbBase < limbBase := by
    have hlt' : a < limbBase ^ 2 * limbBase := by simpa [Nat.pow_succ] using hlt
    rw [Nat.div_div_eq_div_mul, ← limbBase_pow2]
    exact div_lt_of_lt_mul (Nat.pow_pos limbBase_pos) hlt'
  have ha2 : 0 < (a / limbBase) / limbBase := by
    rw [Nat.div_div_eq_div_mul, ← limbBase_pow2]
    exact div_pos_of_le (Nat.pow_pos limbBase_pos) hge
  have hrepr := repr3 a hlt
  rw [bigNat_three a hge hlt, bigNat_limb r hr (Nat.ne_of_gt hr0)]
  have hp' : (a % limbBase + limbBase * ((a / limbBase) % limbBase) +
      limbBase ^ 2 * ((a / limbBase) / limbBase)) * r < limbBase ^ 3 := by
    simpa [hrepr] using hp
  have hmul := big_mul_acc3_limbs (a % limbBase) ((a / limbBase) % limbBase)
    ((a / limbBase) / limbBase) r ha0 ha1 ha2 ha2lt hr0 hr hp'
  simpa [hrepr] using hmul

/-! ## `big_factorial` through `26!` -/

private theorem twenty_lt_limb : 20 < limbBase := by
  unfold limbBase
  decide

private theorem twentySix_lt_limb : 26 < limbBase := by
  unfold limbBase
  decide

private theorem factorial_19_lt_sq : factorial 19 < limbBase ^ 2 := by
  unfold factorial limbBase
  decide

private theorem factorial_19_ge : limbBase ≤ factorial 19 := by
  unfold factorial limbBase
  decide

private theorem factorial_20_ge_sq : limbBase ^ 2 ≤ factorial 20 := by
  unfold factorial limbBase
  decide

private theorem factorial_20_lt_cube : factorial 20 < limbBase ^ 3 := by
  unfold factorial limbBase
  decide

private theorem factorial_26_lt_cube : factorial 26 < limbBase ^ 3 := by
  unfold factorial limbBase
  decide

private theorem factorial_le_succ (b : Nat) : factorial b ≤ factorial (b + 1) := by
  have hmul : factorial b ≤ factorial b * (b + 1) :=
    Nat.le_mul_of_pos_right (factorial b) (Nat.succ_pos b)
  rw [factorial_succ, Nat.mul_comm]
  exact hmul

private theorem factorial_mono (a b : Nat) (h : a ≤ b) : factorial a ≤ factorial b := by
  induction b generalizing a with
  | zero =>
    have : a = 0 := Nat.eq_zero_of_le_zero h
    subst this
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hle : a ≤ b
    · exact Nat.le_trans (ih a hle) (factorial_le_succ b)
    · have heq : a = b + 1 := by omega
      subst heq
      exact Nat.le_refl _

private theorem factorial_lt_sq (n : Nat) (hn : n ≤ 19) : factorial n < limbBase ^ 2 :=
  Nat.lt_of_le_of_lt (factorial_mono n 19 hn) factorial_19_lt_sq

private theorem factorial_lt_cube (n : Nat) (hn : n ≤ 26) : factorial n < limbBase ^ 3 :=
  Nat.lt_of_le_of_lt (factorial_mono n 26 hn) factorial_26_lt_cube

private theorem factorial_pred_mul (i : Nat) (hi : 0 < i) :
    factorial (i - 1) * i = factorial i := by
  cases i with
  | zero => cases hi
  | succ k =>
    rw [show (k + 1) - 1 = k from by omega, factorial_succ, Nat.mul_comm]

private theorem twenty_mul_ge : limbBase ^ 2 ≤ factorial 19 * 20 := by
  rw [factorial_pred_mul 20 (by decide)]
  exact factorial_20_ge_sq

private theorem twenty_mul_lt : factorial 19 * 20 < limbBase ^ 3 := by
  rw [factorial_pred_mul 20 (by decide)]
  exact factorial_20_lt_cube

private theorem factMul_le26 (i : Nat) (hlo : 2 ≤ i) (hhi : i ≤ 26) :
    Megadreifach.big_mul (bigNat (factorial (i - 1))) (bigNat i) =
      .ok (bigNat (factorial i)) := by
  have hiPos : 0 < i := by omega
  have hilt : i < limbBase := Nat.lt_of_le_of_lt hhi twentySix_lt_limb
  by_cases h20 : i ≤ 20
  · by_cases heq : i = 20
    · subst heq
      have hmul := big_mul_three (factorial 19) 20 (by decide) twenty_lt_limb
        factorial_19_ge factorial_19_lt_sq twenty_mul_ge twenty_mul_lt
      rw [factorial_pred_mul 20 (by decide)] at hmul
      simpa [show (20 - 1) = 19 from by decide] using hmul
    · have hi19 : i ≤ 19 := by omega
      have hacc : factorial (i - 1) < limbBase ^ 2 := factorial_lt_sq (i - 1) (by omega)
      have hp : factorial (i - 1) * i < limbBase ^ 2 := by
        rw [factorial_pred_mul i hiPos]
        exact factorial_lt_sq i hi19
      by_cases hlimb : factorial (i - 1) < limbBase
      · have hmul := big_mul_acc (factorial (i - 1)) i hiPos hilt hlimb
        rw [factorial_pred_mul i hiPos] at hmul
        exact hmul
      · have hge : limbBase ≤ factorial (i - 1) := Nat.le_of_not_lt hlimb
        have hmul := big_mul_two (factorial (i - 1)) i hiPos hilt hge hacc hp
        rw [factorial_pred_mul i hiPos] at hmul
        exact hmul
  · have hacc_ge : limbBase ^ 2 ≤ factorial (i - 1) :=
      Nat.le_trans factorial_20_ge_sq (factorial_mono 20 (i - 1) (by omega))
    have hacc_lt : factorial (i - 1) < limbBase ^ 3 :=
      factorial_lt_cube (i - 1) (by omega)
    have hp : factorial (i - 1) * i < limbBase ^ 3 := by
      rw [factorial_pred_mul i hiPos]
      exact factorial_lt_cube i hhi
    have hmul := big_mul_acc3 (factorial (i - 1)) i hiPos hilt hacc_ge hacc_lt hp
    rw [factorial_pred_mul i hiPos] at hmul
    exact hmul

private theorem factStep_le26 (n i : Nat) (hlo : 2 ≤ i) (hhi : i ≤ n) (hn : n ≤ 26) :
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
  have hilt : i < limbBase := Nat.lt_of_le_of_lt (Nat.le_trans hhi hn) twentySix_lt_limb
  have hfits : FitsLen i := FitsLen.of_le fits26 (Nat.le_trans hhi hn)
  rw [show (i : Int) = Int.ofNat i from rfl, big_from_int_refines i hfits, ok_bind]
  have hlimbs : limbsOfNat i = [i] := by
    have hq : i / limbBase = 0 := Nat.div_eq_of_lt hilt
    simp [limbsOfNat, hi0, hq, Nat.mod_eq_of_lt hilt]
  rw [hlimbs, ← bigNat_limb i hilt hi0, factMul_le26 i hlo (Nat.le_trans hhi hn),
    ok_bind, pure_eq_ok, ok_bind]
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
    have hadd := addI_ofNat_one i (FitsLen.of_le fits26 (by omega))
    rw [ofNat_eq_natCast i] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

private theorem big_factorial_wide (n : Nat) (hn2 : 2 ≤ n) (hn : n ≤ 26) :
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
    have hs := factStep_le26 n i hlo hhi hn
    have hsub : (i + 1) - 1 = i := by omega
    simpa [hsub] using hs
  · have hsub : (n + 1) - 1 = n := by omega
    rw [hsub, pure_eq_ok]

/--
  `big_factorial n = n!` for `n ≤ 26`.

  `12!` is one limb. `13!` through `19!` are two limbs. `20!` through `26!`
  are three limbs (`10^18 ≤ 20!` and `26! < 10^27`). From `21!` on, the
  accumulator is already three limbs; `big_mul_acc3` multiplies it by `i ≤ 26`
  and the fourth scratch limb stays zero. Not `27!`. Not `51!`. Not `phi_chunk`.
  Not `v_Hash`.
-/
theorem big_factorial_acc3 (n : Nat) (hn : n ≤ 26) :
    Megadreifach.big_factorial (n : Int) = .ok (bigNat (factorial n)) := by
  by_cases h20 : n ≤ 20
  · exact big_factorial_three n h20
  · exact big_factorial_wide n (by omega) hn

end MegaDreifach.Link2
