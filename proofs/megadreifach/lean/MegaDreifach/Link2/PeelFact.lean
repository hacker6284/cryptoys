/-
  LINK 2. Positive `peel_leading` of `d!` for `d ≤ 19`.

  `12!` is one limb; `13!` through `19!` are two limbs (`19! < 10^18`).
  `big_divmod_small` on a value below `10^18`, divided by `0 < d < 10^9`,
  stays inside an i64: the running remainder is `< d * 10^9 ≤ 10^18`.
  Peeling `d!` itself divides that value by `2, …, d`. The quotient is `1`.
  Multiplying the digit by `d!` copies `d!`, and subtracting it leaves `0`.

  Not `20!` (three limbs). Not an arbitrary two-limb rank. Not `51!`.
  Not `phi_chunk`. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.PeelLimb
import MegaDreifach.Link2.FactTwo

namespace MegaDreifach.Link2

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

private theorem addI_one_two : SudoRt.addI (1 : Int) (2 : Int) = .ok (3 : Int) := by
  have h : FitsLen (1 + 2) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 1 2 h]
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

private theorem subI_two_one : SudoRt.subI (2 : Int) (1 : Int) = .ok (1 : Int) := by
  have h : FitsLen 2 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 2 1 h (by decide)]
  rfl

private theorem subI_three_one : SudoRt.subI (3 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen 3 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 3 1 h (by decide)]
  rfl

private theorem filledL_three :
    SudoRt.filledL (3 : Int) (0 : Int) = .ok (Array.mkArray 3 (0 : Int)) := by
  erw [filledL_ofNat 3 (0 : Int)]

private theorem modI_nat_base (n : Nat) :
    SudoRt.modI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n % limbBase)) := by
  erw [limb_base_eq, modI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem divI_nat_base (n : Nat) :
    SudoRt.divI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n / limbBase)) := by
  erw [limb_base_eq, divI_ofNat n (Nat.ne_of_gt limbBase_pos)]

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

/-- Schoolbook split: `lo + base * hi = dv * q + r` with `r` the low remainder. -/
private theorem pair_decomp (lo hi dv : Nat) (_hd0 : 0 < dv) :
    lo + limbBase * hi =
      dv * (((hi % dv) * limbBase + lo) / dv + limbBase * (hi / dv))
        + ((hi % dv) * limbBase + lo) % dv := by
  have hhi : hi = dv * (hi / dv) + hi % dv := (Nat.div_add_mod hi dv).symm
  let qhi := hi / dv
  let r1 := hi % dv
  let cur := r1 * limbBase + lo
  have hcur : cur = dv * (cur / dv) + cur % dv := (Nat.div_add_mod cur dv).symm
  have hscale : limbBase * (dv * qhi) = dv * (limbBase * qhi) := by
    rw [← Nat.mul_assoc, Nat.mul_comm limbBase dv, Nat.mul_assoc]
  calc
    lo + limbBase * hi
        = lo + limbBase * (dv * qhi + r1) := by rw [hhi]
    _ = lo + (limbBase * (dv * qhi) + limbBase * r1) := by rw [Nat.mul_add]
    _ = lo + (dv * (limbBase * qhi) + limbBase * r1) := by rw [hscale]
    _ = lo + (dv * (limbBase * qhi) + r1 * limbBase) := by rw [Nat.mul_comm limbBase r1]
    _ = lo + (r1 * limbBase + dv * (limbBase * qhi)) := by
          rw [Nat.add_comm (dv * (limbBase * qhi))]
    _ = (lo + r1 * limbBase) + dv * (limbBase * qhi) := by rw [← Nat.add_assoc]
    _ = cur + dv * (limbBase * qhi) := by rw [Nat.add_comm lo (r1 * limbBase)]
    _ = (dv * (cur / dv) + cur % dv) + dv * (limbBase * qhi) := by
          rw (config := {occs := .pos [1]}) [hcur]
    _ = dv * (cur / dv) + dv * (limbBase * qhi) + cur % dv := by
          rw [Nat.add_right_comm (dv * (cur / dv)) (cur % dv) (dv * (limbBase * qhi))]
    _ = dv * (cur / dv + limbBase * qhi) + cur % dv := by rw [← Nat.mul_add]

private theorem pair_div (lo hi dv : Nat) (hd0 : 0 < dv) :
    (lo + limbBase * hi) / dv =
      ((hi % dv) * limbBase + lo) / dv + limbBase * (hi / dv) := by
  have hdecomp := pair_decomp lo hi dv hd0
  have hr : ((hi % dv) * limbBase + lo) % dv < dv := Nat.mod_lt _ hd0
  rw [hdecomp, Nat.mul_add_div hd0, Nat.div_eq_of_lt hr, Nat.add_zero]

private theorem pair_mod (lo hi dv : Nat) (hd0 : 0 < dv) :
    (lo + limbBase * hi) % dv = ((hi % dv) * limbBase + lo) % dv := by
  have hdecomp := pair_decomp lo hi dv hd0
  have hr : ((hi % dv) * limbBase + lo) % dv < dv := Nat.mod_lt _ hd0
  rw [hdecomp, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

private theorem canon_two (qlo qhi : Nat) (hlo : qlo < limbBase) (hhi : qhi < limbBase) :
    dropTrail [qlo, qhi] = limbsOfNat (qlo + limbBase * qhi) := by
  have hlt := two_lt_sq qlo qhi hlo hhi
  by_cases h0 : qlo + limbBase * qhi = 0
  · have hqlo : qlo = 0 := (Nat.add_eq_zero_iff.mp h0).1
    have hmul0 : limbBase * qhi = 0 := (Nat.add_eq_zero_iff.mp h0).2
    have hqhi : qhi = 0 := by
      cases Nat.mul_eq_zero.mp hmul0 with
      | inl hbase => exact absurd hbase (Nat.ne_of_gt limbBase_pos)
      | inr hq => exact hq
    simp [dropTrail, limbsOfNat, h0, hqlo, hqhi]
  · have hpos : 0 < qlo + limbBase * qhi := Nat.pos_of_ne_zero h0
    have hdig : (qlo + limbBase * qhi) % limbBase = qlo := by
      rw [Nat.add_comm qlo (limbBase * qhi), Nat.mul_add_mod, Nat.mod_eq_of_lt hlo]
    have hdiv : (qlo + limbBase * qhi) / limbBase = qhi := by
      rw [Nat.mul_comm limbBase qhi, Nat.add_mul_div_right qlo qhi limbBase_pos,
        Nat.div_eq_of_lt hlo, Nat.zero_add]
    have h := limbs_prod (qlo + limbBase * qhi) hpos hlt
    rw [hdig, hdiv] at h
    exact h

/-! ## Two-limb `big_divmod_small` -/

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

private theorem len2 (a b : Nat) : 1 < ([a, b] : List Nat).length := by
  simp

private theorem len0 (a b : Nat) : 0 < ([a, b] : List Nat).length := by
  simp

private theorem digit0 (a b : Nat) : ([a, b] : List Nat)[0]'(len0 a b) = a := rfl

private theorem digit1 (a b : Nat) : ([a, b] : List Nat)[1]'(len2 a b) = b := rfl

private theorem embed_q_dv (lo hi dv : Nat)
    {h1 : 1 < (Array.mkArray 2 (0 : Int)).size}
    {h0 : 0 <
      ((Array.mkArray 2 (0 : Int)).set ⟨1, h1⟩
        ((0 * (limbBase : Int) + (hi : Int)) / (dv : Int))).size} :
    (((Array.mkArray 2 (0 : Int)).set ⟨1, h1⟩
        ((0 * (limbBase : Int) + (hi : Int)) / (dv : Int))).set ⟨0, h0⟩
        (((hi : Int) % (dv : Int) * (limbBase : Int) + (lo : Int)) / (dv : Int))) =
      embed [((hi % dv) * limbBase + lo) / dv, (0 * limbBase + hi) / dv] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate,
    List.set_cons_zero, List.set_cons_succ, ← Int.ofNat_ediv, ← Int.ofNat_emod,
    ← Int.natCast_mul, ← Int.natCast_add, Nat.zero_mul, Nat.zero_add]

private theorem rem_q_dv (lo hi dv : Nat) :
    ((hi : Int) % (dv : Int) * (limbBase : Int) + (lo : Int)) % (dv : Int) =
      ((((hi % dv) * limbBase + lo) % dv : Nat) : Int) := by
  simp [← Int.ofNat_emod, ← Int.natCast_mul, ← Int.natCast_add, Nat.zero_mul]

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

/-- Divide two little-endian limbs by a positive one-limb divisor. -/
private theorem divmod_pair (lo hi dv : Nat)
    (hlo : lo < limbBase) (hhi : hi < limbBase) (hd0 : 0 < dv) (hd : dv < limbBase) :
    Megadreifach.big_divmod_small (bigOf [lo, hi]) (Int.ofNat dv) =
      .ok (bigNat ((lo + limbBase * hi) / dv),
        (((lo + limbBase * hi) % dv : Nat) : Int)) := by
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
    show ([lo, hi] : List Nat).length = 2 from rfl, sEq_ofNat_zero,
    decide_eq_false_iff_not.mpr (by decide : (2 : Nat) ≠ 0),
    if_neg (by decide : ¬ ((false : Bool) = true)),
    filledL_ofNat, ok_bind, subI_ofNat_one 2 (by decide) (fits_le3 (by decide)), ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := divmodByStep (Int.ofNat dv) (embed [lo, hi]))
    intro σ
    unfold divmodByStep
    rfl
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
  have hsz1 : 1 < (Array.mkArray 2 (Int.ofNat 0)).size := by
    rw [Array.size_mkArray]; decide
  have h1 := divmodBy_at dv [lo, hi] (Array.mkArray 2 (Int.ofNat 0)) 1 0
    hd0 (len2 lo hi) (by decide) (by rw [digit1]; exact hhi) hsz1 FitsLen.one
  have hmk : Array.mkArray (1 + 1) (Int.ofNat 0) = Array.mkArray 2 (Int.ofNat 0) := by simp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, show (1 : Int) = Int.ofNat 1 from rfl, hmk, h1]
  simp only [(by decide : (1 = 0) = False), if_false]
  rw [runLoopOn_one]
  rw [show (1 : Nat) - 1 = 0 from rfl, digit1]
  let hq :=
    (Array.mkArray 2 (Int.ofNat 0)).set ⟨1, hsz1⟩ (Int.ofNat ((0 * limbBase + hi) / dv))
  have hsz0 : 0 < hq.size := by
    dsimp [hq]
    rw [Array.size_set, Array.size_mkArray]
    decide
  have hr1 : (0 * limbBase + hi) % dv < limbBase := by
    have hlt : (0 * limbBase + hi) % dv < dv := Nat.mod_lt _ hd0
    exact Nat.lt_trans hlt hd
  have hx0 : ([lo, hi] : List Nat)[0]'(len0 lo hi) < limbBase := by
    rw [digit0]; exact hlo
  have h0 := divmodBy_at dv [lo, hi] hq 0 ((0 * limbBase + hi) % dv)
    hd0 (len0 lo hi) hr1 hx0 hsz0 FitsLen.zero
  rw [h0]
  simp [digit0]
  erw [embed_q_dv lo hi dv, rem_q_dv lo hi dv]
  rw [make_big_false [((hi % dv) * limbBase + lo) / dv, (0 * limbBase + hi) / dv]
      (fits_le3 (by simp [List.length_cons, List.length_nil])), map_ok]
  simp only [Nat.zero_mul, Nat.zero_add]
  have hqhi : hi / dv < limbBase := Nat.lt_of_le_of_lt (Nat.div_le_self hi dv) hhi
  have hr0 : hi % dv < dv := Nat.mod_lt _ hd0
  have hqlo : ((hi % dv) * limbBase + lo) / dv < limbBase :=
    qdigit_lt (hi % dv) lo dv hr0 hlo hd0
  rw [canon_two (((hi % dv) * limbBase + lo) / dv) (hi / dv) hqlo hqhi]
  rw [pair_div lo hi dv hd0]
  have hmod :
      ((((hi % dv) * limbBase + lo) % dv : Nat) : Int) =
        ((lo : Int) + (limbBase : Int) * (hi : Int)) % (dv : Int) := by
    rw [← pair_mod lo hi dv hd0, Int.ofNat_emod, Int.ofNat_add, Int.ofNat_mul]
  rw [hmod]
  rfl

/--
  `big_divmod_small (bigNat a) d = (a / d, a % d)` when `a < 10^18` and
  `0 < d < 10^9`. One limb reuses `divmod_limb`. Two limbs run the
  descending schoolbook step; every partial remainder fits in an i64.
-/
theorem divmod_sq (a dv : Nat) (ha : a < limbBase ^ 2) (hd0 : 0 < dv) (hd : dv < limbBase) :
    Megadreifach.big_divmod_small (bigNat a) (Int.ofNat dv) =
      .ok (bigNat (a / dv), (((a % dv : Nat) : Int))) := by
  by_cases hlt : a < limbBase
  · exact divmod_limb a dv hlt hd0 hd
  · have hge : limbBase ≤ a := Nat.le_of_not_lt hlt
    have hlo : a % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
    have hhi : a / limbBase < limbBase := by
      rw [limbBase_pow2] at ha
      exact div_lt_of_lt_mul limbBase_pos ha
    rw [bigNat_two a hge ha]
    have h := divmod_pair (a % limbBase) (a / limbBase) dv hlo hhi hd0 hd
    have hrepr : a % limbBase + limbBase * (a / limbBase) = a := Nat.mod_add_div a limbBase
    simpa [hrepr] using h

/-! ## Multiply the one-limb digit `1` by a two-limb value -/

private theorem zeros3_size0 : 0 < (Array.mkArray 3 (0 : Int)).size := by
  simp [Array.size_mkArray]

private theorem zeros3_set0 (x : Nat) :
    (Array.mkArray 3 (0 : Int)).set ⟨0, zeros3_size0⟩ (Int.ofNat x) =
      embed [x, 0, 0] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate, List.set_cons_zero]

private theorem embed3_set1 (x y z v : Nat) :
    (embed [x, y, z]).set ⟨1, by simp [size_embed]⟩ (Int.ofNat v) =
      embed [x, v, z] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

private theorem dropTrail_pad0 (a b : Nat) (hb : b ≠ 0) :
    dropTrail [a, b, 0] = [a, b] := by
  simp [dropTrail, hb]

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

set_option maxHeartbeats 2000000 in
private theorem mulStep_one (lo hi : Nat) (hlo : lo < limbBase) (hhi : hi < limbBase) :
    mulIStep (bigOf [1]) (bigOf [lo, hi]) (0 : Int)
        ((0 : Int), Array.mkArray 3 (0 : Int)) =
      .ok (SudoRt.Flow.brk ((0 : Int), embed [lo, hi, 0])) := by
  have hfitLo : FitsLen (1 * lo) := by simpa [Nat.one_mul] using fits_of_lt_limb hlo
  have hfitHi : FitsLen (1 * hi) := by simpa [Nat.one_mul] using fits_of_lt_limb hhi
  have hlenb : SudoRt.listLen (embed [lo, hi]) = (2 : Int) := by rw [listLen_embed]; rfl
  unfold mulIStep
  dsimp [bigOf]
  rw [hlenb, subI_two_one, ok_bind]
  dsimp
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
  dsimp
  have hat0 : SudoRt.atL (Array.mkArray 3 (0 : Int)) (0 : Int) = .ok (0 : Int) := by
    erw [atL_ofNat (Array.mkArray 3 (0 : Int)) 0 (by simp [Array.size_mkArray])]
    simp [Array.getElem_mkArray]
  rw [addI_zero_zero, ok_bind, hat0, ok_bind]
  erw [atL_embed [1] 0 (by simp)]
  rw [ok_bind]
  erw [atL_embed [lo, hi] 0 (by simp)]
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
  erw [putL_ofNat (Array.mkArray 3 (0 : Int)) 0 (Int.ofNat lo) zeros3_size0]
  rw [ok_bind]
  erw [divI_nat_base (1 * lo)]
  rw [ok_bind, hdivLo, zeros3_set0 lo, bind_pure_flow, addI_zero_one]
  simp only [ok_bind, pure_eq_ok, Nat.one_mul]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  have hat1 : SudoRt.atL (embed [lo, 0, 0]) (1 : Int) = .ok (0 : Int) := by
    erw [atL_embed [lo, 0, 0] 1 (by simp)]
    simp
  rw [addI_zero_one, ok_bind, hat1, ok_bind]
  erw [atL_embed [lo, hi] 1 (by simp)]
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
  have hsz1 : 1 < (embed [lo, 0, 0]).size := by simp [size_embed]
  erw [putL_ofNat (embed [lo, 0, 0]) 1 (Int.ofNat hi) hsz1]
  rw [ok_bind]
  erw [divI_nat_base (1 * hi)]
  rw [ok_bind, hdivHi, embed3_set1 lo 0 0 hi]
  simp only [ok_bind, Nat.one_mul]
  have hlenOut : SudoRt.listLen (embed [lo, hi, 0]) = (3 : Int) := by
    rw [listLen_embed]; rfl
  erw [addI_zero_nat 2 (by unfold FitsLen i64MaxNat; decide)]
  rw [ok_bind, hlenOut, subI_three_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  erw [mulK_idle (embed [lo, hi, 0]) 2]
  simp only [match_ok_brk, pure_eq_ok, toPure_eq_ok, ok_bind]

set_option maxHeartbeats 2000000 in
private theorem big_mul_one_limbs (lo hi : Nat)
    (hlo : lo < limbBase) (hhi0 : 0 < hi) (hhi : hi < limbBase) :
    Megadreifach.big_mul (bigOf [1]) (bigOf [lo, hi]) =
      .ok (bigOf [lo, hi]) := by
  unfold Megadreifach.big_mul
  dsimp [bigOf]
  have hlena : SudoRt.listLen (embed [1]) = (1 : Int) := by rw [listLen_embed]; rfl
  have hlenb : SudoRt.listLen (embed [lo, hi]) = (2 : Int) := by rw [listLen_embed]; rfl
  rw [hlena]
  have hbeq1 : SudoRt.SEq.beq (1 : Int) (0 : Int) = false := by simp [sEq_int]
  have hbeq2 : SudoRt.SEq.beq (2 : Int) (0 : Int) = false := by simp [sEq_int]
  rw [hbeq1]
  dsimp
  rw [hlenb, hbeq2]
  rw [show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind,
    if_neg (by decide : ¬ ((false : Bool) = true))]
  rw [addI_one_two, ok_bind, filledL_three, ok_bind, subI_one_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := mulIStep (bigOf [1]) (bigOf [lo, hi]) (0 : Int))
    intro σ
    unfold mulIStep mulKStep
    dsimp [bigOf]
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ,
    mulStep_one lo hi hlo hhi]
  simp only [match_ok_brk]
  rw [make_big_false [lo, hi, 0] (fits_le3 (by simp [List.length_cons, List.length_nil])),
    ok_bind, dropTrail_pad0 lo hi (Nat.ne_of_gt hhi0), pure_eq_ok]
  rfl

/-- `big_mul (bigNat 1) (bigNat a) = bigNat a` for a positive two-limb `a`. -/
theorem big_mul_one (a : Nat) (hge : limbBase ≤ a) (hlt : a < limbBase ^ 2) :
    Megadreifach.big_mul (bigNat 1) (bigNat a) = .ok (bigNat a) := by
  have h1lt : (1 : Nat) < limbBase := by unfold limbBase; decide
  have hlo : a % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hhi : a / limbBase < limbBase := by
    rw [limbBase_pow2] at hlt
    exact div_lt_of_lt_mul limbBase_pos hlt
  have hhi0 : 0 < a / limbBase := div_pos_of_le limbBase_pos hge
  rw [bigNat_limb 1 h1lt (by decide), bigNat_two a hge hlt]
  exact big_mul_one_limbs (a % limbBase) (a / limbBase) hlo hhi0 hhi

/-! ## Subtract a two-limb value from itself -/

private theorem append0 (out : List Nat) :
    (SudoRt.appendL (embed out) (Int.ofNat 0)).1 = embed (out ++ [0]) := by
  simp [appendL_spec, embed, Array.push, List.concat_eq_append, List.map_append]

private theorem len_embed_two (x y : Nat) :
    SudoRt.listLen (embed [x, y]) = (2 : Int) := by
  rw [listLen_embed]; rfl

private theorem magSub_same0 (lo hi : Nat) (hlo : lo < limbBase) (_hhi : hi < limbBase) :
    magSubStep (embed [lo, hi]) (embed [lo, hi]) 1
        ((0 : Int), ((0 : Int), (#[] : Array Int))) =
      .ok (SudoRt.Flow.cont ((1 : Int), ((0 : Int), embed [0]))) := by
  unfold magSubStep
  dsimp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, atL_embed [lo, hi] 0 (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [subI_ofNat lo 0 (fits_of_lt_limb hlo) (Nat.zero_le _), ok_bind, Nat.sub_zero,
    len_embed_two lo hi]
  have hlt : decide (Int.ofNat 0 < (2 : Int)) = true := by decide
  have hnn : decide (Int.ofNat 0 < Int.ofNat 0) = false := by decide
  rw [hlt]
  simp only [ite_true]
  rw [ok_bind]
  rw [subI_ofNat lo lo (fits_of_lt_limb hlo) (Nat.le_refl _), ok_bind, Nat.sub_self, hnn]
  simp only [Bool.false_eq_true, ite_false]
  rw [show (SudoRt.appendL (#[] : Array Int) (Int.ofNat 0)).1 = embed [0] from by
    simp [appendL_spec, embed], bind_pure_flow]
  dsimp
  rw [addI_zero_one, ok_bind, pure_eq_ok]

private theorem magSub_same1 (lo hi : Nat) (_hlo : lo < limbBase) (hhi : hi < limbBase) :
    magSubStep (embed [lo, hi]) (embed [lo, hi]) 1
        ((1 : Int), ((0 : Int), embed [0])) =
      .ok (SudoRt.Flow.brk ((1 : Int), ((0 : Int), embed [0, 0]))) := by
  unfold magSubStep
  dsimp
  rw [show (1 : Int) = Int.ofNat 1 from rfl, atL_embed [lo, hi] 1 (by simp), ok_bind]
  simp only [List.getElem_cons_succ, List.getElem_cons_zero]
  erw [subI_ofNat hi 0 (fits_of_lt_limb hhi) (Nat.zero_le _)]
  rw [ok_bind, Nat.sub_zero, len_embed_two lo hi]
  have hlt : decide (Int.ofNat 1 < (2 : Int)) = true := by decide
  have hnn : decide (Int.ofNat 0 < (0 : Int)) = false := by decide
  rw [hlt]
  simp only [ite_true]
  rw [ok_bind]
  erw [subI_ofNat hi hi (fits_of_lt_limb hhi) (Nat.le_refl _)]
  rw [ok_bind, Nat.sub_self, hnn]
  simp only [Bool.false_eq_true, ite_false]
  rw [append0 [0], bind_pure_flow]
  dsimp
  rw [pure_eq_ok]

/-- `mag_sub` of a two-limb value from itself is the empty limb list. -/
private theorem mag_sub_same (a : Nat) (hge : limbBase ≤ a) (hlt : a < limbBase ^ 2) :
    Megadreifach.mag_sub (bigNat a).sudo_6BigInt_5limbs (bigNat a).sudo_6BigInt_5limbs =
      .ok (embed ([] : List Nat)) := by
  have hlo : a % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
  have hhi : a / limbBase < limbBase := by
    rw [limbBase_pow2] at hlt
    exact div_lt_of_lt_mul limbBase_pos hlt
  have hhi0 : 0 < a / limbBase := div_pos_of_le limbBase_pos hge
  rw [bigNat_two a hge hlt]
  dsimp [bigOf]
  unfold Megadreifach.mag_sub
  rw [len_embed_two (a % limbBase) (a / limbBase), subI_two_one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := magSubStep (embed [a % limbBase, a / limbBase])
        (embed [a % limbBase, a / limbBase]) 1)
    intro σ
    unfold magSubStep
    dsimp
    rfl
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ,
    magSub_same0 (a % limbBase) (a / limbBase) hlo hhi]
  simp only [match_ok_cont]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ,
    magSub_same1 (a % limbBase) (a / limbBase) hlo hhi]
  simp only [match_ok_brk]
  rw [show embed [0, 0] = embed ([0, 0] : List Nat) from rfl,
    trim_embed [0, 0] (fits_le3 (by decide)), ok_bind]
  simp [dropTrail, pure_eq_ok]

/-! ## `peel_leading (d!) = (0, 1)` -/

private theorem factorial_19_lt_sq : factorial 19 < limbBase ^ 2 := by
  unfold factorial limbBase
  decide

private theorem factorial_13_ge : limbBase ≤ factorial 13 := by
  unfold factorial limbBase
  decide

private theorem nineteen_lt_limb : 19 < limbBase := by
  unfold limbBase
  decide

private theorem fits19 : FitsLen 19 := by
  unfold FitsLen i64MaxNat
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

private theorem factorial_ge_limb (n : Nat) (hn : 13 ≤ n) : limbBase ≤ factorial n :=
  Nat.le_trans factorial_13_ge (factorial_mono 13 n hn)

private theorem factorial_pred_mul (i : Nat) (hi : 0 < i) :
    factorial (i - 1) * i = factorial i := by
  cases i with
  | zero => cases hi
  | succ k =>
    rw [show (k + 1) - 1 = k from by omega, factorial_succ, Nat.mul_comm]

private theorem div_fact_quot (d f : Nat) (hf0 : 0 < f) :
    (factorial d / factorial (f - 1)) / f = factorial d / factorial f := by
  rw [Nat.div_div_eq_div_mul, factorial_pred_mul f hf0]

private theorem peelDivStep_fact (d f : Nat) (hlo : 2 ≤ f) (hhi : f ≤ d)
    (hd : d ≤ 19) :
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
    Nat.lt_of_le_of_lt (Nat.le_trans hhi hd) nineteen_lt_limb
  have hq : factorial d / factorial (f - 1) < limbBase ^ 2 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (factorial_lt_sq d hd)
  rw [show (f : Int) = Int.ofNat f from rfl,
    divmod_sq (factorial d / factorial (f - 1)) f hq hf0 hflt, ok_bind]
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
    have hadd := addI_ofNat_one f (FitsLen.of_le fits19 (by omega))
    rw [ofNat_eq_natCast f] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

private theorem peel_finish_fact (d : Nat) (hdLo : 13 ≤ d) (hd : d ≤ 19) :
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
  have hge : limbBase ≤ factorial d := factorial_ge_limb d hdLo
  have hlt : factorial d < limbBase ^ 2 := factorial_lt_sq d hd
  rw [limb_to_small_limb 1 h1, ok_bind, big_factorial_two d hd, ok_bind]
  rw [show ((1 : Nat) : Int) = Int.ofNat 1 from rfl, big_from_int_refines 1 FitsLen.one, ok_bind]
  have hlimbs : limbsOfNat 1 = [1] := by
    have hq : 1 / limbBase = 0 := Nat.div_eq_of_lt h1
    simp [limbsOfNat, hq, Nat.mod_eq_of_lt h1]
  rw [hlimbs, show bigOf [1] = bigNat 1 from by
    rw [bigNat_limb 1 h1 (by decide)], big_mul_one (factorial d) hge hlt, ok_bind,
    mag_sub_same (factorial d) hge hlt, ok_bind,
    make_big_false [] FitsLen.zero, ok_bind]
  simp [dropTrail, bigNat_zero, pure_eq_ok]

/--
  `peel_leading (bigNat (d!)) d = (0, 1)` for `d ≤ 19`.

  The factoradic digit of `d!` at place `d` is `d! / d! = 1`, and the
  remainder is `0`. For `d ≥ 13` the factorial is two limbs; the closing
  product is the digit `1` times that factorial.
-/
theorem peel_leading_factorial_two (d : Nat) (hd : d ≤ 19) :
    Megadreifach.peel_leading (bigNat (factorial d)) (d : Int) =
      .ok (bigNat 0, (1 : Int)) := by
  by_cases h12 : d ≤ 12
  · exact peel_leading_factorial d h12
  · have hdLo : 13 ≤ d := by omega
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
      simpa using peelDivStep_fact d i hlo hhi hd
    · rw [show (d + 1) - 1 = d from by omega, Nat.div_self (factorial_pos d)]
      exact peel_finish_fact d hdLo hd

end MegaDreifach.Link2
