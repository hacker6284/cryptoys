/-
  LINK 2. `peel_leading` of `d!` for `d ≤ 26`.

  `20!` through `26!` are three limbs (`10^18 ≤ 20!` and `26! < 10^27`).
  `big_divmod_small` on a value below `10^27`, divided by `0 < d < 10^9`,
  stays inside an i64: the running remainder is `< d < 10^9`, so each
  partial `rem * 10^9 + digit` is below `10^18`. Peeling `d!` divides that
  value by `2, …, d`. The quotient is `1`. Multiplying the digit by `d!`
  copies the three limbs, and subtracting them leaves `0`.

  Not an arbitrary positive three-limb rank. Not `27!` (four limbs).
  Not `51!`. Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.PeelFact
import MegaDreifach.Link2.AccThree

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

private theorem addI_zero_zero : SudoRt.addI (0 : Int) (0 : Int) = .ok (0 : Int) := by
  erw [addI_ofNat 0 0 FitsLen.zero]
  simp

private theorem addI_zero_one : SudoRt.addI (0 : Int) (1 : Int) = .ok (1 : Int) := by
  erw [addI_ofNat 0 1 FitsLen.one]
  simp [Nat.zero_add]

private theorem addI_one_one : SudoRt.addI (1 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen (1 + 1) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 1 1 h]
  rfl

private theorem addI_one_three : SudoRt.addI (1 : Int) (3 : Int) = .ok (4 : Int) := by
  have h : FitsLen (1 + 3) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 1 3 h]
  rfl

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

private theorem fits_sq : FitsLen (limbBase ^ 2) := limb_sq_fits

private theorem fits_scale (r : Nat) (hr : r < limbBase) : FitsLen (r * limbBase) := by
  have h : r * limbBase < limbBase ^ 2 := by
    rw [limbBase_pow2]
    exact Nat.mul_lt_mul_of_pos_right hr limbBase_pos
  exact Nat.le_trans (Nat.le_of_lt h) limb_sq_fits

private theorem two_lt_sq (lo hi : Nat) (hlo : lo < limbBase) (hhi : hi < limbBase) :
    lo + limbBase * hi < limbBase ^ 2 := by
  rw [limbBase_pow2]
  calc
    lo + limbBase * hi < limbBase + limbBase * hi := Nat.add_lt_add_right hlo _
    _ = limbBase * (hi + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ limbBase * limbBase := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hhi)

private theorem fits_cur (r x : Nat) (hr : r < limbBase) (hx : x < limbBase) :
    FitsLen (r * limbBase + x) := by
  have hswap : r * limbBase + x = x + limbBase * r := by
    rw [Nat.mul_comm r limbBase, Nat.add_comm]
  rw [hswap]
  exact Nat.le_trans (Nat.le_of_lt (two_lt_sq x r hx hr)) fits_sq

private theorem cur_lt_dv (r x dv : Nat) (hr : r < dv) (hx : x < limbBase) (hd0 : 0 < dv) :
    r * limbBase + x < dv * limbBase := by
  have hr' : r ≤ dv - 1 := by omega
  have hx' : x ≤ limbBase - 1 := by omega
  have hmul : r * limbBase ≤ (dv - 1) * limbBase := Nat.mul_le_mul_right _ hr'
  have hadd : r * limbBase + x ≤ (dv - 1) * limbBase + (limbBase - 1) :=
    Nat.add_le_add hmul hx'
  have hbase : (dv - 1) * limbBase + limbBase = dv * limbBase := by
    have hdv : (dv - 1) + 1 = dv := Nat.sub_add_cancel (Nat.succ_le_of_lt hd0)
    calc
      (dv - 1) * limbBase + limbBase
          = (dv - 1) * limbBase + 1 * limbBase := by rw [Nat.one_mul]
      _ = ((dv - 1) + 1) * limbBase := by rw [Nat.add_mul]
      _ = dv * limbBase := by rw [hdv]
  have hlt : (dv - 1) * limbBase + (limbBase - 1) < (dv - 1) * limbBase + limbBase :=
    Nat.add_lt_add_left (Nat.sub_lt limbBase_pos (by decide)) _
  have hlt' : (dv - 1) * limbBase + (limbBase - 1) < dv * limbBase := by
    simpa [hbase] using hlt
  exact Nat.lt_of_le_of_lt hadd hlt'

private theorem qdigit_lt (r x dv : Nat) (hr : r < dv) (hx : x < limbBase) (hd0 : 0 < dv) :
    (r * limbBase + x) / dv < limbBase :=
  div_lt_of_lt_mul hd0 (cur_lt_dv r x dv hr hx hd0)

/-! ## Three little-endian digits -/

private theorem val3 (q0 q1 q2 : Nat) :
    q0 + limbBase * q1 + limbBase ^ 2 * q2 =
      q0 + limbBase * (q1 + limbBase * q2) := by
  calc
    q0 + limbBase * q1 + limbBase ^ 2 * q2
        = q0 + limbBase * q1 + limbBase * (limbBase * q2) := by
          rw [← Nat.mul_assoc, ← limbBase_pow2]
    _ = q0 + (limbBase * q1 + limbBase * (limbBase * q2)) := by rw [Nat.add_assoc]
    _ = q0 + limbBase * (q1 + limbBase * q2) := by rw [← Nat.mul_add]

private theorem three_lt_cube (q0 q1 q2 : Nat)
    (h0 : q0 < limbBase) (h1 : q1 < limbBase) (h2 : q2 < limbBase) :
    q0 + limbBase * q1 + limbBase ^ 2 * q2 < limbBase ^ 3 := by
  have h0' : q0 ≤ limbBase - 1 := by omega
  have h1' : q1 ≤ limbBase - 1 := by omega
  have h2' : q2 ≤ limbBase - 1 := by omega
  have hle : q0 + limbBase * q1 + limbBase ^ 2 * q2 ≤
      (limbBase - 1) + limbBase * (limbBase - 1) + limbBase ^ 2 * (limbBase - 1) :=
    Nat.add_le_add (Nat.add_le_add h0' (Nat.mul_le_mul_left _ h1'))
      (Nat.mul_le_mul_left _ h2')
  have hconst :
      (limbBase - 1) + limbBase * (limbBase - 1) + limbBase ^ 2 * (limbBase - 1) =
        limbBase ^ 3 - 1 := by
    unfold limbBase
    decide
  have hlt : limbBase ^ 3 - 1 < limbBase ^ 3 := by
    have hp : 0 < limbBase ^ 3 := Nat.pow_pos limbBase_pos
    omega
  exact Nat.lt_of_le_of_lt (by simpa [hconst] using hle) hlt

private theorem repr3 (a : Nat) :
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

private theorem dropTrail_mem {xs : List Nat} {d : Nat} (hd : d ∈ dropTrail xs) : d ∈ xs := by
  induction xs with
  | nil => simp [dropTrail] at hd
  | cons a as ih =>
    cases h : dropTrail as with
    | nil =>
      by_cases ha : a = 0
      · simp [dropTrail, h, ha] at hd
      · simp [dropTrail, h, ha] at hd
        simp [hd]
    | cons b bs =>
      have hd' : d ∈ a :: b :: bs := by simpa [dropTrail, h] using hd
      simp at hd'
      cases hd' with
      | inl heq => simp [heq]
      | inr hmem =>
        exact List.mem_cons_of_mem a (ih (by simpa [h] using hmem))

private theorem limbVal_three (q0 q1 q2 : Nat) :
    limbVal [q0, q1, q2] = q0 + limbBase * q1 + limbBase ^ 2 * q2 := by
  simp [limbVal]
  exact (val3 q0 q1 q2).symm

private theorem canon_three (q0 q1 q2 : Nat)
    (h0 : q0 < limbBase) (h1 : q1 < limbBase) (h2 : q2 < limbBase) :
    dropTrail [q0, q1, q2] =
      limbsOfNat (q0 + limbBase * q1 + limbBase ^ 2 * q2) := by
  let xs := dropTrail [q0, q1, q2]
  have htrim : dropTrail xs = xs := dropTrail_idem [q0, q1, q2]
  have hdig : ∀ d ∈ xs, d < limbBase := by
    intro d hd
    have hmem := dropTrail_mem hd
    simp at hmem
    rcases hmem with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  have hlen : xs.length ≤ 3 := by
    simpa using dropTrail_length_le [q0, q1, q2]
  have hv : limbVal xs < limbBase ^ 3 := by
    rw [limbVal_dropTrail, limbVal_three]
    exact three_lt_cube q0 q1 q2 h0 h1 h2
  have heq := trimmed_eq_limbsOfNat xs htrim hdig hv hlen
  have hval : limbVal xs = q0 + limbBase * q1 + limbBase ^ 2 * q2 := by
    rw [limbVal_dropTrail, limbVal_three]
  rw [show dropTrail [q0, q1, q2] = xs from rfl, heq, hval]

/-! ## Schoolbook division of three limbs -/

private theorem triple_decomp (lo mid hi dv : Nat) (_hd0 : 0 < dv) :
    lo + limbBase * mid + limbBase ^ 2 * hi =
      dv * (((hi % dv * limbBase + mid) % dv * limbBase + lo) / dv
          + limbBase * ((hi % dv * limbBase + mid) / dv)
          + limbBase ^ 2 * (hi / dv))
        + ((hi % dv * limbBase + mid) % dv * limbBase + lo) % dv := by
  have hhi : hi = dv * (hi / dv) + hi % dv := (Nat.div_add_mod hi dv).symm
  let q2 := hi / dv
  let r2 := hi % dv
  let cur1 := r2 * limbBase + mid
  have hcur1 : cur1 = dv * (cur1 / dv) + cur1 % dv := (Nat.div_add_mod cur1 dv).symm
  let q1 := cur1 / dv
  let r1 := cur1 % dv
  let cur0 := r1 * limbBase + lo
  have hcur0 : cur0 = dv * (cur0 / dv) + cur0 % dv := (Nat.div_add_mod cur0 dv).symm
  let q0 := cur0 / dv
  let r0 := cur0 % dv
  have hscale2 : limbBase ^ 2 * (dv * q2) = dv * (limbBase ^ 2 * q2) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (limbBase ^ 2) dv, Nat.mul_assoc]
  have hscale1 : limbBase * (dv * q1) = dv * (limbBase * q1) := by
    rw [← Nat.mul_assoc, Nat.mul_comm limbBase dv, Nat.mul_assoc]
  have hmid : limbBase * mid + limbBase ^ 2 * r2 = limbBase * cur1 := by
    calc
      limbBase * mid + limbBase ^ 2 * r2
          = limbBase * mid + limbBase * (limbBase * r2) := by
            rw [← Nat.mul_assoc, ← limbBase_pow2]
      _ = limbBase * (mid + limbBase * r2) := by rw [← Nat.mul_add]
      _ = limbBase * (r2 * limbBase + mid) := by
            rw [Nat.mul_comm limbBase r2, Nat.add_comm]
  have hfactor : dv * q0 + dv * (limbBase * q1) + dv * (limbBase ^ 2 * q2) =
      dv * (q0 + limbBase * q1 + limbBase ^ 2 * q2) := by
    rw [← Nat.mul_add, ← Nat.mul_add]
  have hmove :
      (dv * q0 + r0 + dv * (limbBase * q1)) + dv * (limbBase ^ 2 * q2) =
        (dv * q0 + dv * (limbBase * q1) + dv * (limbBase ^ 2 * q2)) + r0 := by
    have hstep : dv * q0 + r0 + dv * (limbBase * q1) =
        dv * q0 + dv * (limbBase * q1) + r0 := by
      rw [Nat.add_assoc, Nat.add_comm r0 (dv * (limbBase * q1)), ← Nat.add_assoc]
    rw [hstep, Nat.add_right_comm]
  calc
    lo + limbBase * mid + limbBase ^ 2 * hi
        = lo + limbBase * mid + limbBase ^ 2 * (dv * q2 + r2) := by rw [hhi]
    _ = lo + limbBase * mid + (limbBase ^ 2 * (dv * q2) + limbBase ^ 2 * r2) := by
          rw [Nat.mul_add]
    _ = lo + limbBase * mid + (dv * (limbBase ^ 2 * q2) + limbBase ^ 2 * r2) := by
          rw [hscale2]
    _ = lo + limbBase * mid + (limbBase ^ 2 * r2 + dv * (limbBase ^ 2 * q2)) := by
          rw [Nat.add_comm (dv * (limbBase ^ 2 * q2))]
    _ = (lo + limbBase * mid + limbBase ^ 2 * r2) + dv * (limbBase ^ 2 * q2) := by
          rw [← Nat.add_assoc]
    _ = (lo + (limbBase * mid + limbBase ^ 2 * r2)) + dv * (limbBase ^ 2 * q2) := by
          rw [Nat.add_assoc lo (limbBase * mid) (limbBase ^ 2 * r2)]
    _ = (lo + limbBase * cur1) + dv * (limbBase ^ 2 * q2) := by rw [hmid]
    _ = (lo + limbBase * (dv * q1 + r1)) + dv * (limbBase ^ 2 * q2) := by rw [hcur1]
    _ = (lo + (limbBase * (dv * q1) + limbBase * r1)) + dv * (limbBase ^ 2 * q2) := by
          rw [Nat.mul_add]
    _ = (lo + (dv * (limbBase * q1) + limbBase * r1)) + dv * (limbBase ^ 2 * q2) := by
          rw [hscale1]
    _ = (lo + (limbBase * r1 + dv * (limbBase * q1))) + dv * (limbBase ^ 2 * q2) := by
          rw [Nat.add_comm (dv * (limbBase * q1)) (limbBase * r1)]
    _ = ((lo + limbBase * r1) + dv * (limbBase * q1)) + dv * (limbBase ^ 2 * q2) := by
          rw [← Nat.add_assoc]
    _ = ((limbBase * r1 + lo) + dv * (limbBase * q1)) + dv * (limbBase ^ 2 * q2) := by
          rw [Nat.add_comm lo (limbBase * r1)]
    _ = (cur0 + dv * (limbBase * q1)) + dv * (limbBase ^ 2 * q2) := by
          rw [Nat.mul_comm limbBase r1]
    _ = ((dv * q0 + r0) + dv * (limbBase * q1)) + dv * (limbBase ^ 2 * q2) := by rw [hcur0]
    _ = (dv * q0 + dv * (limbBase * q1) + dv * (limbBase ^ 2 * q2)) + r0 := hmove
    _ = dv * (q0 + limbBase * q1 + limbBase ^ 2 * q2) + r0 := by rw [hfactor]

private theorem triple_div (lo mid hi dv : Nat) (hd0 : 0 < dv) :
    (lo + limbBase * mid + limbBase ^ 2 * hi) / dv =
      ((hi % dv * limbBase + mid) % dv * limbBase + lo) / dv
        + limbBase * ((hi % dv * limbBase + mid) / dv)
        + limbBase ^ 2 * (hi / dv) := by
  have hdecomp := triple_decomp lo mid hi dv hd0
  have hr : ((hi % dv * limbBase + mid) % dv * limbBase + lo) % dv < dv :=
    Nat.mod_lt _ hd0
  rw [hdecomp, Nat.mul_add_div hd0, Nat.div_eq_of_lt hr, Nat.add_zero]

private theorem triple_mod (lo mid hi dv : Nat) (hd0 : 0 < dv) :
    (lo + limbBase * mid + limbBase ^ 2 * hi) % dv =
      ((hi % dv * limbBase + mid) % dv * limbBase + lo) % dv := by
  have hdecomp := triple_decomp lo mid hi dv hd0
  have hr : ((hi % dv * limbBase + mid) % dv * limbBase + lo) % dv < dv :=
    Nat.mod_lt _ hd0
  rw [hdecomp, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-! ## Three-limb `big_divmod_small` -/

private theorem divmodBy_at (dv : Nat) (xs : List Nat) (qArr : Array Int) (i r : Nat)
    (hd0 : 0 < dv) (hi : i < xs.length) (hr : r < limbBase) (hx : xs[i] < limbBase)
    (hsz : i < qArr.size) (hfiti : FitsLen i) :
    divmodByStep (Int.ofNat dv) (embed xs) (Int.ofNat i, qArr, Int.ofNat r) =
      (let cur := r * limbBase + xs[i]
      let q' := qArr.set ⟨i, hsz⟩ (Int.ofNat (cur / dv))
      let r' := Int.ofNat (cur % dv)
      if i = 0 then
        .ok (SudoRt.Flow.brk (Int.ofNat 0, q', r'))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i - 1), q', r'))) := by
  unfold divmodByStep
  dsimp
  rw [if_neg (Int.not_lt.mpr (Int.ofNat_zero_le i))]
  rw [limb_base_eq, ← ofNat_eq_natCast limbBase, ← ofNat_eq_natCast r,
    mulI_ofNat r limbBase (fits_scale r hr), ok_bind,
    ← ofNat_eq_natCast i, atL_embed xs i hi, ok_bind]
  have hcur : FitsLen (r * limbBase + xs[i]) := fits_cur r (xs[i]) hr hx
  rw [addI_ofNat (r * limbBase) (xs[i]) hcur, ok_bind,
    show (dv : Int) = Int.ofNat dv from rfl,
    divI_ofNat (r * limbBase + xs[i]) (Nat.ne_of_gt hd0), ok_bind,
    putL_ofNat qArr i _ hsz, ok_bind,
    modI_ofNat (r * limbBase + xs[i]) (Nat.ne_of_gt hd0), ok_bind]
  erw [ok_bind]
  dsimp
  by_cases hi0 : i = 0
  · simp [hi0]
    rfl
  · have hneI : ¬ (i : Int) = 0 := fun h => hi0 (Int.ofNat.inj h)
    have hsub := subI_ofNat_one i (Nat.pos_of_ne_zero hi0) hfiti
    rw [ofNat_eq_natCast i] at hsub
    rw [ite_int_beq, if_neg hneI, hsub, ok_bind, if_neg hi0]
    rfl

private theorem i0 (a b c : Nat) : 0 < ([a, b, c] : List Nat).length := by simp
private theorem i1 (a b c : Nat) : 1 < ([a, b, c] : List Nat).length := by simp
private theorem i2 (a b c : Nat) : 2 < ([a, b, c] : List Nat).length := by simp
private theorem d0 (a b c : Nat) : ([a, b, c] : List Nat)[0]'(i0 a b c) = a := rfl
private theorem d1 (a b c : Nat) : ([a, b, c] : List Nat)[1]'(i1 a b c) = b := rfl
private theorem d2 (a b c : Nat) : ([a, b, c] : List Nat)[2]'(i2 a b c) = c := rfl

private theorem embed_set3 (q0 q1 q2 : Nat)
    {h2 : 2 < (Array.mkArray 3 (0 : Int)).size}
    {h1 : 1 < ((Array.mkArray 3 (0 : Int)).set ⟨2, h2⟩ (Int.ofNat q2)).size}
    {h0 : 0 <
      (((Array.mkArray 3 (0 : Int)).set ⟨2, h2⟩ (Int.ofNat q2)).set ⟨1, h1⟩
        (Int.ofNat q1)).size} :
    (((Array.mkArray 3 (0 : Int)).set ⟨2, h2⟩ (Int.ofNat q2)).set ⟨1, h1⟩
        (Int.ofNat q1)).set ⟨0, h0⟩ (Int.ofNat q0) =
      embed [q0, q1, q2] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate,
    List.set_cons_zero, List.set_cons_succ]

private theorem runLoopOn_two {σ ρ α} (s0 : σ)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn s0 2 step after onRet =
      match step s0 with
      | .error e => .error e
      | .ok (.ret r) => onRet r
      | .ok (.brk s) => after s
      | .ok (.cont s) => SudoRt.runLoopOn s 1 step after onRet := by
  rw [show (2 : Nat) = 1 + 1 from rfl]
  exact runLoopOn_succ s0 1 step after onRet

private theorem runLoopOn_one {σ ρ α} (s0 : σ)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn s0 1 step after onRet =
      match step s0 with
      | .error e => .error e
      | .ok (.ret r) => onRet r
      | .ok (.brk s) => after s
      | .ok (.cont s) => SudoRt.runLoopOn s 0 step after onRet := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  exact runLoopOn_succ s0 0 step after onRet

/-- Divide three little-endian limbs by a positive one-limb divisor. -/
private theorem divmod_triple (lo mid hi dv : Nat)
    (hlo : lo < limbBase) (hmid : mid < limbBase) (hhi : hi < limbBase)
    (hd0 : 0 < dv) (hd : dv < limbBase) :
    Megadreifach.big_divmod_small (bigOf [lo, mid, hi]) (Int.ofNat dv) =
      .ok (bigNat ((lo + limbBase * mid + limbBase ^ 2 * hi) / dv),
        (((lo + limbBase * mid + limbBase ^ 2 * hi) % dv : Nat) : Int)) := by
  unfold Megadreifach.big_divmod_small
  dsimp [bigOf]
  have hgt : decide ((dv : Int) > (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    exact (ofNat_pos_iff dv).mpr hd0
  have hltb : decide ((dv : Int) < Megadreifach.limb_base) = true := by
    rw [limb_base_eq, decide_eq_true_eq]
    exact (ofNat_lt_iff dv limbBase).mpr hd
  rw [hgt]
  simp only [ite_true, hltb]
  rw [show (pure true : Except SudoRt.Trap Bool) = .ok true from rfl, ok_bind,
    sudoAssert_true, ok_bind, listLen_embed,
    show ([lo, mid, hi] : List Nat).length = 3 from rfl, sEq_ofNat_zero,
    decide_eq_false_iff_not.mpr (by decide : (3 : Nat) ≠ 0),
    if_neg (by decide : ¬ ((false : Bool) = true)),
    filledL_ofNat, ok_bind, subI_ofNat_one 3 (by decide) (fits_le3 (by decide)), ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := divmodByStep (Int.ofNat dv) (embed [lo, mid, hi]))
    intro σ
    unfold divmodByStep
    rfl
  rw [show (3 : Nat) = 2 + 1 from rfl, runLoopOn_succ]
  have hsz2 : 2 < (Array.mkArray 3 (Int.ofNat 0)).size := by
    rw [Array.size_mkArray]; decide
  have hmk : Array.mkArray (2 + 1) (Int.ofNat 0) = Array.mkArray 3 (Int.ofNat 0) := by simp
  have hx2 : ([lo, mid, hi] : List Nat)[2]'(i2 lo mid hi) < limbBase := by
    rw [d2]; exact hhi
  have h2 := divmodBy_at dv [lo, mid, hi] (Array.mkArray 3 (Int.ofNat 0)) 2 0
    hd0 (i2 lo mid hi) (by decide) hx2 hsz2 fits2
  rw [show (0 : Int) = Int.ofNat 0 from rfl, show (2 : Int) = Int.ofNat 2 from rfl, hmk, h2]
  simp only [(by decide : (2 = 0) = False), if_false]
  rw [runLoopOn_two]
  rw [show (2 : Nat) - 1 = 1 from rfl, d2]
  let hq2 :=
    (Array.mkArray 3 (Int.ofNat 0)).set ⟨2, hsz2⟩ (Int.ofNat ((0 * limbBase + hi) / dv))
  have hsz1 : 1 < hq2.size := by
    dsimp [hq2]
    rw [Array.size_set, Array.size_mkArray]
    decide
  have hr2 : (0 * limbBase + hi) % dv < limbBase :=
    Nat.lt_trans (Nat.mod_lt _ hd0) hd
  have hx1 : ([lo, mid, hi] : List Nat)[1]'(i1 lo mid hi) < limbBase := by
    rw [d1]; exact hmid
  have h1 := divmodBy_at dv [lo, mid, hi] hq2 1 ((0 * limbBase + hi) % dv)
    hd0 (i1 lo mid hi) hr2 hx1 hsz1 FitsLen.one
  rw [h1]
  simp only [(by decide : (1 = 0) = False), if_false]
  rw [runLoopOn_one]
  rw [d1]
  let r2n := (0 * limbBase + hi) % dv
  let cur1 := r2n * limbBase + mid
  let hq1 := hq2.set ⟨1, hsz1⟩ (Int.ofNat (cur1 / dv))
  have hsz0 : 0 < hq1.size := by
    dsimp [hq1, hq2]
    rw [Array.size_set, Array.size_set, Array.size_mkArray]
    decide
  have hr1 : cur1 % dv < limbBase := Nat.lt_trans (Nat.mod_lt _ hd0) hd
  have hx0 : ([lo, mid, hi] : List Nat)[0]'(i0 lo mid hi) < limbBase := by
    rw [d0]; exact hlo
  have h0 := divmodBy_at dv [lo, mid, hi] hq1 0 (cur1 % dv)
    hd0 (i0 lo mid hi) hr1 hx0 hsz0 FitsLen.zero
  rw [h0]
  simp only [d0, if_true]
  erw [embed_set3]
  rw [make_big_false
      [((cur1 % dv) * limbBase + lo) / dv, cur1 / dv, (0 * limbBase + hi) / dv]
      (fits_le3 (by simp [List.length_cons, List.length_nil])), ok_bind, pure_eq_ok]
  dsimp [cur1, r2n]
  simp only [Nat.zero_mul, Nat.zero_add]
  have hqHi : hi / dv < limbBase := Nat.lt_of_le_of_lt (Nat.div_le_self hi dv) hhi
  have hr2' : hi % dv < dv := Nat.mod_lt _ hd0
  have hqMid : ((hi % dv) * limbBase + mid) / dv < limbBase :=
    qdigit_lt (hi % dv) mid dv hr2' hmid hd0
  have hr1' : ((hi % dv) * limbBase + mid) % dv < dv := Nat.mod_lt _ hd0
  have hqLo : (((hi % dv) * limbBase + mid) % dv * limbBase + lo) / dv < limbBase :=
    qdigit_lt (((hi % dv) * limbBase + mid) % dv) lo dv hr1' hlo hd0
  rw [canon_three
      ((((hi % dv) * limbBase + mid) % dv * limbBase + lo) / dv)
      (((hi % dv) * limbBase + mid) / dv)
      (hi / dv) hqLo hqMid hqHi]
  rw [← triple_div lo mid hi dv hd0, ← Int.ofNat_emod, ← triple_mod lo mid hi dv hd0]
  rfl

/--
  `big_divmod_small (bigNat a) d = (a / d, a % d)` when `a < 10^27` and
  `0 < d < 10^9`. Fewer than three limbs reuse `divmod_sq`. Three limbs run
  the descending schoolbook step; every partial remainder fits in an i64.
-/
theorem divmod_cube (a dv : Nat) (ha : a < limbBase ^ 3) (hd0 : 0 < dv) (hd : dv < limbBase) :
    Megadreifach.big_divmod_small (bigNat a) (Int.ofNat dv) =
      .ok (bigNat (a / dv), (((a % dv : Nat) : Int))) := by
  by_cases hlt : a < limbBase ^ 2
  · exact divmod_sq a dv hlt hd0 hd
  · have hge : limbBase ^ 2 ≤ a := Nat.le_of_not_lt hlt
    have hlo : a % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
    have hmid : (a / limbBase) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
    have hhi : (a / limbBase) / limbBase < limbBase := by
      have hdiv : a / limbBase < limbBase ^ 2 := by
        rw [limbBase_pow3] at ha
        exact div_lt_of_lt_mul limbBase_pos ha
      rw [limbBase_pow2] at hdiv
      exact div_lt_of_lt_mul limbBase_pos hdiv
    rw [bigNat_three a hge ha]
    have h := divmod_triple (a % limbBase) ((a / limbBase) % limbBase)
      ((a / limbBase) / limbBase) dv hlo hmid hhi hd0 hd
    simpa [repr3 a] using h

/-! ## Multiply the one-limb digit `1` by a three-limb value -/

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

private theorem dropTrail_pad0 (a b c : Nat) (hc : c ≠ 0) :
    dropTrail [a, b, c, 0] = [a, b, c] := by
  simp [dropTrail, hc]

private theorem mulK_idle (out : Array Int) (k : Nat) :
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

set_option maxHeartbeats 8000000 in
private theorem mulStep_one3 (lo mid hi : Nat)
    (hlo : lo < limbBase) (hmid : mid < limbBase) (hhi : hi < limbBase) :
    mulIStep (bigOf [1]) (bigOf [lo, mid, hi]) (0 : Int)
        ((0 : Int), Array.mkArray 4 (0 : Int)) =
      .ok (SudoRt.Flow.brk ((0 : Int), embed [lo, mid, hi, 0])) := by
  have hfitLo : FitsLen (1 * lo) := by simpa [Nat.one_mul] using fits_of_lt_limb hlo
  have hfitMid : FitsLen (1 * mid) := by simpa [Nat.one_mul] using fits_of_lt_limb hmid
  have hfitHi : FitsLen (1 * hi) := by simpa [Nat.one_mul] using fits_of_lt_limb hhi
  have hlenb : SudoRt.listLen (embed [lo, mid, hi]) = (3 : Int) := by
    rw [listLen_embed]; rfl
  unfold mulIStep
  dsimp [bigOf]
  rw [hlenb, subI_three_one, ok_bind]
  dsimp
  rw [show (3 : Nat) = 2 + 1 from rfl, runLoopOn_succ]
  dsimp
  have hat0 : SudoRt.atL (Array.mkArray 4 (0 : Int)) (0 : Int) = .ok (0 : Int) := by
    erw [atL_ofNat (Array.mkArray 4 (0 : Int)) 0 (by simp [Array.size_mkArray])]
    simp [Array.getElem_mkArray]
  rw [addI_zero_zero, ok_bind, hat0, ok_bind]
  erw [atL_embed [1] 0 (by simp)]
  rw [ok_bind]
  erw [atL_embed [lo, mid, hi] 0 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_zero]
  erw [mulI_ofNat 1 lo hfitLo]
  rw [ok_bind]
  erw [addI_zero_nat (1 * lo) hfitLo]
  rw [ok_bind]
  erw [addI_nat_zero (1 * lo) hfitLo]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base (1 * lo)]
  rw [ok_bind]
  have hmodLo : (1 * lo) % limbBase = lo := by simp [Nat.one_mul, Nat.mod_eq_of_lt hlo]
  have hdivLo : (1 * lo) / limbBase = 0 := by simp [Nat.one_mul, Nat.div_eq_of_lt hlo]
  rw [hmodLo]
  erw [putL_ofNat (Array.mkArray 4 (0 : Int)) 0 (Int.ofNat lo) zeros4_size0]
  rw [ok_bind]
  erw [divI_nat_base (1 * lo)]
  rw [ok_bind, hdivLo, zeros4_set0 lo, bind_pure_flow, addI_zero_one]
  simp only [ok_bind, pure_eq_ok, Nat.one_mul]
  rw [runLoopOn_two]
  dsimp
  have hat1 : SudoRt.atL (embed [lo, 0, 0, 0]) (1 : Int) = .ok (0 : Int) := by
    erw [atL_embed [lo, 0, 0, 0] 1 (by simp)]
    simp
  rw [addI_zero_one, ok_bind, hat1, ok_bind]
  erw [atL_embed [lo, mid, hi] 1 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [mulI_ofNat 1 mid hfitMid]
  rw [ok_bind]
  erw [addI_zero_nat (1 * mid) hfitMid]
  rw [ok_bind]
  erw [addI_nat_zero (1 * mid) hfitMid]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base (1 * mid)]
  rw [ok_bind]
  have hmodMid : (1 * mid) % limbBase = mid := by simp [Nat.one_mul, Nat.mod_eq_of_lt hmid]
  have hdivMid : (1 * mid) / limbBase = 0 := by simp [Nat.one_mul, Nat.div_eq_of_lt hmid]
  rw [hmodMid]
  have hsz1 : 1 < (embed [lo, 0, 0, 0]).size := by simp [size_embed]
  erw [putL_ofNat (embed [lo, 0, 0, 0]) 1 (Int.ofNat mid) hsz1]
  rw [ok_bind]
  erw [divI_nat_base (1 * mid)]
  rw [ok_bind, hdivMid, embed4_set1 lo 0 0 0 mid, ok_bind, addI_one_one]
  simp only [ok_bind, pure_eq_ok, Nat.one_mul]
  rw [runLoopOn_one]
  dsimp
  have hat2 : SudoRt.atL (embed [lo, mid, 0, 0]) (2 : Int) = .ok (0 : Int) := by
    erw [atL_embed [lo, mid, 0, 0] 2 (by simp)]
    simp
  erw [addI_zero_nat 2 fits2]
  rw [ok_bind]
  erw [hat2]
  rw [ok_bind]
  erw [atL_embed [lo, mid, hi] 2 (by simp)]
  rw [ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [mulI_ofNat 1 hi hfitHi]
  rw [ok_bind]
  erw [addI_zero_nat (1 * hi) hfitHi]
  rw [ok_bind]
  erw [addI_nat_zero (1 * hi) hfitHi]
  rw [ok_bind, ok_bind]
  erw [modI_nat_base (1 * hi)]
  rw [ok_bind]
  have hmodHi : (1 * hi) % limbBase = hi := by simp [Nat.one_mul, Nat.mod_eq_of_lt hhi]
  have hdivHi : (1 * hi) / limbBase = 0 := by simp [Nat.one_mul, Nat.div_eq_of_lt hhi]
  rw [hmodHi]
  have hsz2 : 2 < (embed [lo, mid, 0, 0]).size := by simp [size_embed]
  erw [putL_ofNat (embed [lo, mid, 0, 0]) 2 (Int.ofNat hi) hsz2]
  rw [ok_bind]
  erw [divI_nat_base (1 * hi)]
  rw [ok_bind, hdivHi, embed4_set2 lo mid 0 0 hi]
  simp only [ok_bind, Nat.one_mul]
  have hlenOut : SudoRt.listLen (embed [lo, mid, hi, 0]) = (4 : Int) := by
    rw [listLen_embed]; rfl
  erw [addI_zero_nat 3 fits3]
  rw [ok_bind, hlenOut, subI_four_one, ok_bind]
  dsimp
  rw [runLoopOn_one]
  erw [mulK_idle (embed [lo, mid, hi, 0]) 3]
  simp only [match_ok_brk, pure_eq_ok, toPure_eq_ok, ok_bind]

private theorem big_mul_one_limbs (lo mid hi : Nat)
    (hlo : lo < limbBase) (hmid : mid < limbBase) (hhi0 : 0 < hi) (hhi : hi < limbBase) :
    Megadreifach.big_mul (bigOf [1]) (bigOf [lo, mid, hi]) =
      .ok (bigOf [lo, mid, hi]) := by
  unfold Megadreifach.big_mul
  dsimp [bigOf]
  have hlena : SudoRt.listLen (embed [1]) = (1 : Int) := by rw [listLen_embed]; rfl
  have hlenb : SudoRt.listLen (embed [lo, mid, hi]) = (3 : Int) := by
    rw [listLen_embed]; rfl
  rw [hlena]
  have hbeq1 : SudoRt.SEq.beq (1 : Int) (0 : Int) = false := by simp [sEq_int]
  have hbeq3 : SudoRt.SEq.beq (3 : Int) (0 : Int) = false := by simp [sEq_int]
  rw [hbeq1]
  dsimp
  rw [hlenb, hbeq3]
  rw [show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind,
    if_neg (by decide : ¬ ((false : Bool) = true))]
  rw [addI_one_three, ok_bind, filledL_four, ok_bind, subI_one_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := mulIStep (bigOf [1]) (bigOf [lo, mid, hi]) (0 : Int))
    intro σ
    unfold mulIStep mulKStep
    dsimp [bigOf]
    rfl
  rw [runLoopOn_one,
    mulStep_one3 lo mid hi hlo hmid hhi]
  simp only [match_ok_brk]
  rw [make_big_false [lo, mid, hi, 0] fits4, ok_bind,
    dropTrail_pad0 lo mid hi (Nat.ne_of_gt hhi0), pure_eq_ok]
  rfl

/-- `big_mul (bigNat 1) (bigNat a) = bigNat a` for a positive three-limb `a`. -/
theorem big_mul_one_three (a : Nat) (hge : limbBase ^ 2 ≤ a) (hlt : a < limbBase ^ 3) :
    Megadreifach.big_mul (bigNat 1) (bigNat a) = .ok (bigNat a) := by
  have h1lt : (1 : Nat) < limbBase := by unfold limbBase; decide
  have hlo : a % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hmid : (a / limbBase) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hhi : (a / limbBase) / limbBase < limbBase := by
    have hdiv : a / limbBase < limbBase ^ 2 := by
      rw [limbBase_pow3] at hlt
      exact div_lt_of_lt_mul limbBase_pos hlt
    rw [limbBase_pow2] at hdiv
    exact div_lt_of_lt_mul limbBase_pos hdiv
  have hhi0 : 0 < (a / limbBase) / limbBase := by
    rw [Nat.div_div_eq_div_mul, ← limbBase_pow2]
    exact div_pos_of_le (Nat.pow_pos limbBase_pos) hge
  rw [bigNat_limb 1 h1lt (by decide), bigNat_three a hge hlt]
  exact big_mul_one_limbs (a % limbBase) ((a / limbBase) % limbBase)
    ((a / limbBase) / limbBase) hlo hmid hhi0 hhi

/-! ## Subtract a three-limb value from itself -/

private theorem append0 (out : List Nat) :
    (SudoRt.appendL (embed out) (Int.ofNat 0)).1 = embed (out ++ [0]) := by
  simp [appendL_spec, embed, Array.push, List.concat_eq_append, List.map_append]

private theorem len_embed_three (x y z : Nat) :
    SudoRt.listLen (embed [x, y, z]) = (3 : Int) := by
  rw [listLen_embed]; rfl

private theorem magSub_same0 (a b c : Nat) (ha : a < limbBase) :
    magSubStep (embed [a, b, c]) (embed [a, b, c]) 2
        ((0 : Int), ((0 : Int), (#[] : Array Int))) =
      .ok (SudoRt.Flow.cont ((1 : Int), ((0 : Int), embed [0]))) := by
  unfold magSubStep
  dsimp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, atL_embed [a, b, c] 0 (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [subI_ofNat a 0 (fits_of_lt_limb ha) (Nat.zero_le _), ok_bind, Nat.sub_zero,
    len_embed_three a b c]
  have hlt : decide (Int.ofNat 0 < (3 : Int)) = true := by decide
  have hnn : decide (Int.ofNat 0 < Int.ofNat 0) = false := by decide
  rw [hlt]
  simp only [ite_true]
  rw [ok_bind]
  rw [subI_ofNat a a (fits_of_lt_limb ha) (Nat.le_refl _), ok_bind, Nat.sub_self, hnn]
  simp only [Bool.false_eq_true, ite_false]
  rw [show (SudoRt.appendL (#[] : Array Int) (Int.ofNat 0)).1 = embed [0] from by
    simp [appendL_spec, embed], bind_pure_flow]
  dsimp
  rw [addI_zero_one, ok_bind, pure_eq_ok]

private theorem magSub_same1 (a b c : Nat) (_ha : a < limbBase) (hb : b < limbBase) :
    magSubStep (embed [a, b, c]) (embed [a, b, c]) 2
        ((1 : Int), ((0 : Int), embed [0])) =
      .ok (SudoRt.Flow.cont ((2 : Int), ((0 : Int), embed [0, 0]))) := by
  unfold magSubStep
  dsimp
  rw [show (1 : Int) = Int.ofNat 1 from rfl, atL_embed [a, b, c] 1 (by simp), ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [subI_ofNat b 0 (fits_of_lt_limb hb) (Nat.zero_le _)]
  rw [ok_bind, Nat.sub_zero, len_embed_three a b c]
  have hlt : decide (Int.ofNat 1 < (3 : Int)) = true := by decide
  have hnn : decide (Int.ofNat 0 < (0 : Int)) = false := by decide
  rw [hlt]
  simp only [ite_true]
  rw [ok_bind]
  erw [subI_ofNat b b (fits_of_lt_limb hb) (Nat.le_refl _)]
  rw [ok_bind, Nat.sub_self, hnn]
  simp only [Bool.false_eq_true, ite_false]
  rw [append0 [0], bind_pure_flow]
  dsimp
  rw [addI_one_one, ok_bind, pure_eq_ok]

private theorem magSub_same2 (a b c : Nat) (_ha : a < limbBase) (_hb : b < limbBase)
    (hc : c < limbBase) :
    magSubStep (embed [a, b, c]) (embed [a, b, c]) 2
        ((2 : Int), ((0 : Int), embed [0, 0])) =
      .ok (SudoRt.Flow.brk ((2 : Int), ((0 : Int), embed [0, 0, 0]))) := by
  unfold magSubStep
  dsimp
  rw [show (2 : Int) = Int.ofNat 2 from rfl, atL_embed [a, b, c] 2 (by simp), ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [subI_ofNat c 0 (fits_of_lt_limb hc) (Nat.zero_le _)]
  rw [ok_bind, Nat.sub_zero, len_embed_three a b c]
  have hlt : decide (Int.ofNat 2 < (3 : Int)) = true := by decide
  have hnn : decide (Int.ofNat 0 < (0 : Int)) = false := by decide
  rw [hlt]
  simp only [ite_true]
  rw [ok_bind]
  erw [subI_ofNat c c (fits_of_lt_limb hc) (Nat.le_refl _)]
  rw [ok_bind, Nat.sub_self, hnn]
  simp only [Bool.false_eq_true, ite_false]
  rw [append0 [0, 0], bind_pure_flow]
  dsimp
  rw [pure_eq_ok]

/-- `mag_sub` of a three-limb value from itself is the empty limb list. -/
private theorem mag_sub_same3 (a : Nat) (hge : limbBase ^ 2 ≤ a) (hlt : a < limbBase ^ 3) :
    Megadreifach.mag_sub (bigNat a).sudo_6BigInt_5limbs (bigNat a).sudo_6BigInt_5limbs =
      .ok (embed ([] : List Nat)) := by
  have hlo : a % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hmid : (a / limbBase) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hhi : (a / limbBase) / limbBase < limbBase := by
    have hdiv : a / limbBase < limbBase ^ 2 := by
      rw [limbBase_pow3] at hlt
      exact div_lt_of_lt_mul limbBase_pos hlt
    rw [limbBase_pow2] at hdiv
    exact div_lt_of_lt_mul limbBase_pos hdiv
  rw [bigNat_three a hge hlt]
  dsimp [bigOf]
  unfold Megadreifach.mag_sub
  rw [len_embed_three (a % limbBase) ((a / limbBase) % limbBase) ((a / limbBase) / limbBase),
    subI_three_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := magSubStep
        (embed [a % limbBase, (a / limbBase) % limbBase, (a / limbBase) / limbBase])
        (embed [a % limbBase, (a / limbBase) % limbBase, (a / limbBase) / limbBase]) 2)
    intro σ
    unfold magSubStep
    dsimp
    rfl
  rw [show (3 : Nat) = 2 + 1 from rfl, runLoopOn_succ,
    magSub_same0 (a % limbBase) ((a / limbBase) % limbBase) ((a / limbBase) / limbBase) hlo]
  simp only [match_ok_cont]
  rw [runLoopOn_two,
    magSub_same1 (a % limbBase) ((a / limbBase) % limbBase) ((a / limbBase) / limbBase)
      hlo hmid]
  simp only [match_ok_cont]
  rw [runLoopOn_one,
    magSub_same2 (a % limbBase) ((a / limbBase) % limbBase) ((a / limbBase) / limbBase)
      hlo hmid hhi]
  simp only [match_ok_brk]
  rw [show embed [0, 0, 0] = embed ([0, 0, 0] : List Nat) from rfl,
    trim_embed [0, 0, 0] (fits_le3 (by decide)), ok_bind]
  simp [dropTrail, pure_eq_ok]

/-! ## `peel_leading (d!) = (0, 1)` through three limbs -/

private theorem factorial_26_lt_cube : factorial 26 < limbBase ^ 3 := by
  unfold factorial limbBase
  decide

private theorem factorial_20_ge : limbBase ^ 2 ≤ factorial 20 := by
  unfold factorial limbBase
  decide

private theorem twenty_six_lt_limb : 26 < limbBase := by
  unfold limbBase
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

private theorem factorial_lt_cube (n : Nat) (hn : n ≤ 26) : factorial n < limbBase ^ 3 :=
  Nat.lt_of_le_of_lt (factorial_mono n 26 hn) factorial_26_lt_cube

private theorem factorial_ge_pow2 (n : Nat) (hn : 20 ≤ n) : limbBase ^ 2 ≤ factorial n :=
  Nat.le_trans factorial_20_ge (factorial_mono 20 n hn)

private theorem factorial_pred_mul (i : Nat) (hi : 0 < i) :
    factorial (i - 1) * i = factorial i := by
  cases i with
  | zero => cases hi
  | succ k =>
    rw [show (k + 1) - 1 = k from by omega, factorial_succ, Nat.mul_comm]

private theorem div_fact_quot (d f : Nat) (hf0 : 0 < f) :
    (factorial d / factorial (f - 1)) / f = factorial d / factorial f := by
  rw [Nat.div_div_eq_div_mul, factorial_pred_mul f hf0]

private theorem peelDivStep_fact3 (d f : Nat) (hlo : 2 ≤ f) (hhi : f ≤ d)
    (hd : d ≤ 26) :
    peelDivStep (Int.ofNat d)
        (Int.ofNat f, bigNat (factorial d / factorial (f - 1))) =
      if f = d then
        .ok (SudoRt.Flow.brk (Int.ofNat f, bigNat (factorial d / factorial f)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (f + 1), bigNat (factorial d / factorial f))) := by
  unfold peelDivStep
  dsimp
  have hngt : ¬ (f : Int) > (d : Int) := ofNat_not_gt hhi
  rw [if_neg hngt]
  have hf0 : 0 < f := by omega
  have hflt : f < limbBase :=
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hd) twenty_six_lt_limb
  have hq : factorial d / factorial (f - 1) < limbBase ^ 3 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (factorial_lt_cube d hd)
  rw [show (f : Int) = Int.ofNat f from rfl,
    divmod_cube (factorial d / factorial (f - 1)) f hq hf0 hflt, ok_bind]
  rw [show ((bigNat ((factorial d / factorial (f - 1)) / f),
        ((((factorial d / factorial (f - 1)) % f : Nat) : Int))).1) =
      bigNat ((factorial d / factorial (f - 1)) / f) from rfl,
    div_fact_quot d f hf0, pure_eq_ok, ok_bind]
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
    have hadd := addI_ofNat_one f (FitsLen.of_le fits26 (by omega))
    rw [ofNat_eq_natCast f] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

private theorem peel_finish_fact3 (d : Nat) (hdLo : 20 ≤ d) (hd : d ≤ 26) :
    (do
      let idx ← Megadreifach.limb_to_small (bigNat 1)
      let fact ← Megadreifach.big_factorial (d : Int)
      let coeff ← Megadreifach.big_from_int idx
      let prod ← Megadreifach.big_mul coeff fact
      let diff ← Megadreifach.mag_sub (bigNat (factorial d)).sudo_6BigInt_5limbs
        prod.sudo_6BigInt_5limbs
      let rest ← Megadreifach.make_big false diff
      pure (rest, idx)) =
      .ok (bigNat 0, (1 : Int)) := by
  have h1 : (1 : Nat) < limbBase := by unfold limbBase; decide
  have hge : limbBase ^ 2 ≤ factorial d := factorial_ge_pow2 d hdLo
  have hlt : factorial d < limbBase ^ 3 := factorial_lt_cube d hd
  rw [limb_to_small_limb 1 h1, ok_bind, big_factorial_acc3 d hd, ok_bind]
  rw [show ((1 : Nat) : Int) = Int.ofNat 1 from rfl, big_from_int_refines 1 FitsLen.one,
    ok_bind]
  have hlimbs : limbsOfNat 1 = [1] := by
    have hq : 1 / limbBase = 0 := Nat.div_eq_of_lt h1
    simp [limbsOfNat, hq, Nat.mod_eq_of_lt h1]
  rw [hlimbs, show bigOf [1] = bigNat 1 from by
    rw [bigNat_limb 1 h1 (by decide)], big_mul_one_three (factorial d) hge hlt, ok_bind,
    mag_sub_same3 (factorial d) hge hlt, ok_bind,
    make_big_false [] FitsLen.zero, ok_bind]
  simp [dropTrail, bigNat_zero, pure_eq_ok]

/--
  `peel_leading (bigNat (d!)) d = (0, 1)` for `d ≤ 26`.

  The factoradic digit of `d!` at place `d` is `d! / d! = 1`, and the
  remainder is `0`. For `20 ≤ d` the factorial is three limbs. The closing
  product is the digit `1` times that factorial.
-/
theorem peel_leading_factorial_three (d : Nat) (hd : d ≤ 26) :
    Megadreifach.peel_leading (bigNat (factorial d)) (d : Int) =
      .ok (bigNat 0, (1 : Int)) := by
  by_cases h19 : d ≤ 19
  · exact peel_leading_factorial_two d h19
  · have hdLo : 20 ≤ d := by omega
    unfold Megadreifach.peel_leading
    dsimp
    rw [fuelRange_eq, except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise (step' := peelDivStep (d : Int))
      intro σ
      unfold peelDivStep
      dsimp
      rfl
    rw [show (2 : Int) = Int.ofNat 2 from rfl]
    have hdiv1 : factorial d / factorial (2 - 1) = factorial d := by
      have : factorial (2 - 1) = 1 := by simp [factorial]
      rw [this, Nat.div_one]
    have hpair :
        ((Int.ofNat 2, bigNat (factorial d)) : Int × Megadreifach.BigInt) =
          (Int.ofNat 2, bigNat (factorial d / factorial (2 - 1))) := by
      rw [hdiv1]
    rw [hpair]
    apply chain_loop
      (f := fun i => bigNat (factorial d / factorial (i - 1)))
      (fromN := 2) (toN := d)
      (hle := by omega)
      (goal := .ok (bigNat 0, (1 : Int)))
    · intro i hlo hhi
      simpa using peelDivStep_fact3 d i hlo hhi hd
    · rw [show (d + 1) - 1 = d from by omega, Nat.div_self (factorial_pos d)]
      exact peel_finish_fact3 d hdLo hd

end MegaDreifach.Link2
