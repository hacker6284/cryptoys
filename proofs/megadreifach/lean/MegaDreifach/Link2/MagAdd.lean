/-
  LINK 2. `mag_add` / `big_add` at arbitrary width.

  Schoolbook addition of two canonical base-`10^9` limb strings.
  Each digit is `< 10^9` and the incoming carry is `0` or `1`, so a cell
  `a + b + carry` is `< 2 · 10^9` and fits in an i64. The trimmed digits
  are `natLimbs (n + m)`. A final carry, when it is `1`, is the new high limb.

  This is the Horner add in `big_from_be` once the accumulator passes
  two limbs. Not `phi_chunk`. Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.MagSub

namespace MegaDreifach.Link2

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem ite_false_eq {α} (a b : α) :
    (if false = true then a else b) = b := by
  simp [Bool.false_eq_true]

private theorem append_dig (out : List Nat) (k : Nat) :
    (SudoRt.appendL (embed out) (Int.ofNat k)).1 = embed (out ++ [k]) := by
  rw [appendL_spec]
  exact push_embed out k

private theorem modI_nat_base (n : Nat) :
    SudoRt.modI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n % limbBase)) := by
  erw [limb_base_eq, modI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem divI_nat_base (n : Nat) :
    SudoRt.divI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n / limbBase)) := by
  erw [limb_base_eq, divI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem two_le_base : 2 ≤ limbBase := by
  unfold limbBase
  decide

private theorem fits_limb_width : FitsLen limbBase := by
  unfold FitsLen i64MaxNat limbBase
  decide

private theorem fits_two_limb : FitsLen (2 * limbBase) := by
  unfold FitsLen i64MaxNat limbBase
  decide

private theorem sum2_fits (a c : Nat) (ha : a < limbBase) (hc : c ≤ 1) :
    FitsLen (c + a) := by
  have : c + a ≤ limbBase := by omega
  exact FitsLen.of_le fits_limb_width this

private theorem sum3_fits (a b c : Nat) (ha : a < limbBase) (hb : b < limbBase) (hc : c ≤ 1) :
    FitsLen (a + b + c) := by
  have : a + b + c ≤ 2 * limbBase := by omega
  exact FitsLen.of_le fits_two_limb this

private theorem div_le_one (s : Nat) (hs : s < 2 * limbBase) : s / limbBase ≤ 1 := by
  have hlt : s / limbBase < 2 := by
    have hmul : s < limbBase * 2 := by
      rw [Nat.mul_comm]
      exact hs
    exact div_lt_of_lt_mul limbBase_pos hmul
  omega

private theorem div_zero_lt {s : Nat} (h : s / limbBase = 0) : s < limbBase := by
  have hsplit := Nat.div_add_mod s limbBase
  rw [h, Nat.mul_zero, Nat.zero_add] at hsplit
  exact hsplit ▸ Nat.mod_lt s limbBase_pos

private theorem match_cont {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match SudoRt.Flow.cont s with
      | SudoRt.Flow.ret r => onRet r
      | SudoRt.Flow.brk s' => onBrk s'
      | SudoRt.Flow.cont s' => onCont s') = onCont s := by
  rfl

/-- Break or continue once a limb digit has been appended. -/
private theorem closeCont (i toV c : Nat) (out : List Nat)
    (hfits : FitsLen (i + 1)) :
    (if ((Int.ofNat i) == (Int.ofNat toV)) = true then
        (pure (SudoRt.Flow.brk (ρ := Array Int)
            (Int.ofNat i, (embed out, Int.ofNat c))) :
          Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Int)) (Array Int)))
      else
        SudoRt.addI (Int.ofNat i) (1 : Int) >>= fun i' =>
          pure (SudoRt.Flow.cont (ρ := Array Int)
            (i', (embed out, Int.ofNat c)))) =
      (if i = toV then
        .ok (SudoRt.Flow.brk (ρ := Array Int)
          (Int.ofNat i, (embed out, Int.ofNat c)))
      else
        .ok (SudoRt.Flow.cont (ρ := Array Int)
          (Int.ofNat (i + 1), (embed out, Int.ofNat c)))) := by
  by_cases heq : i = toV
  · subst heq
    have hbeq : ((Int.ofNat i) == (Int.ofNat i)) = true := by
      rw [beq_int_iff]
    rw [if_pos hbeq, pure_eq_ok, if_pos (rfl : i = i)]
  · have hneI : (Int.ofNat i) ≠ (Int.ofNat toV) := fun h => heq (Int.ofNat.inj h)
    have hbeq : ((Int.ofNat i) == (Int.ofNat toV)) = false := by
      cases hb : ((Int.ofNat i) == (Int.ofNat toV)) with
      | false => rfl
      | true => exact absurd ((beq_int_iff _ _).mp hb) hneI
    have hneB : ¬ ((Int.ofNat i) == (Int.ofNat toV)) = true := by
      rw [hbeq]
      decide
    have hadd := addI_ofNat_one i hfits
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]

/-! ## Carry scan -/

private theorem sum_split_mul (s p : Nat) :
    s * p = s % limbBase * p + (s / limbBase) * (limbBase * p) := by
  have h : limbBase * (s / limbBase) + s % limbBase = s := Nat.div_add_mod s limbBase
  have hmul : s * p = (limbBase * (s / limbBase) + s % limbBase) * p :=
    congrArg (fun t => t * p) h.symm
  calc
    s * p = (limbBase * (s / limbBase) + s % limbBase) * p := hmul
    _ = limbBase * (s / limbBase) * p + s % limbBase * p := by rw [Nat.add_mul]
    _ = s % limbBase * p + limbBase * (s / limbBase) * p := by ac_rfl
    _ = s % limbBase * p + (s / limbBase) * (limbBase * p) := by
        rw [Nat.mul_comm limbBase (s / limbBase), Nat.mul_assoc]

/-- Carry entering limb `i`. Digits past the end of a list are `0`. -/
def carryAt (xs ys : List Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => (digAt xs i + digAt ys i + carryAt xs ys i) / limbBase

/-- Little-endian sum digits through index `k`, before a final carry limb. -/
def addPref (xs ys : List Nat) : Nat → List Nat
  | 0 => []
  | i + 1 =>
      addPref xs ys i ++
        [(digAt xs i + digAt ys i + carryAt xs ys i) % limbBase]

@[simp] theorem carryAt_zero (xs ys : List Nat) : carryAt xs ys 0 = 0 := rfl

@[simp] theorem carryAt_succ (xs ys : List Nat) (i : Nat) :
    carryAt xs ys (i + 1) =
      (digAt xs i + digAt ys i + carryAt xs ys i) / limbBase := rfl

@[simp] theorem addPref_zero (xs ys : List Nat) : addPref xs ys 0 = [] := rfl

@[simp] theorem addPref_succ (xs ys : List Nat) (i : Nat) :
    addPref xs ys (i + 1) =
      addPref xs ys i ++
        [(digAt xs i + digAt ys i + carryAt xs ys i) % limbBase] := rfl

theorem addScan_inv (xs ys : List Nat)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase) :
    ∀ k,
      carryAt xs ys k ≤ 1 ∧
      (addPref xs ys k).length = k ∧
      (∀ d ∈ addPref xs ys k, d < limbBase) ∧
      limbVal (xs.take k) + limbVal (ys.take k) =
        limbVal (addPref xs ys k) + carryAt xs ys k * limbBase ^ k := by
  intro k
  induction k with
  | zero =>
    simp [limbVal, List.take_zero]
  | succ k ih =>
    obtain ⟨hc, hlen, hdig, hbal⟩ := ih
    have ha : digAt xs k < limbBase := digAt_bound xs k hxs
    have hb : digAt ys k < limbBase := digAt_bound ys k hys
    have hs_lt : digAt xs k + digAt ys k + carryAt xs ys k < 2 * limbBase := by
      omega
    have hc' : carryAt xs ys (k + 1) ≤ 1 := by
      rw [carryAt_succ]
      exact div_le_one _ hs_lt
    refine ⟨hc', ?_, ?_, ?_⟩
    · simp [hlen]
    · intro d hd
      simp only [addPref_succ, List.mem_append, List.mem_singleton] at hd
      cases hd with
      | inl hm => exact hdig d hm
      | inr hm =>
        subst hm
        exact Nat.mod_lt _ limbBase_pos
    · have hx := limbVal_take_succ_dig xs k
      have hy := limbVal_take_succ_dig ys k
      have hab : (digAt xs k + digAt ys k) * limbBase ^ k =
          digAt xs k * limbBase ^ k + digAt ys k * limbBase ^ k := by rw [Nat.add_mul]
      have hsum : (digAt xs k + digAt ys k + carryAt xs ys k) * limbBase ^ k =
          (digAt xs k + digAt ys k) * limbBase ^ k +
            carryAt xs ys k * limbBase ^ k := by rw [Nat.add_mul]
      have hsplit := sum_split_mul
          (digAt xs k + digAt ys k + carryAt xs ys k) (limbBase ^ k)
      have hpow : limbBase * limbBase ^ k = limbBase ^ (k + 1) := by
        rw [Nat.mul_comm, ← Nat.pow_succ]
      have hpref : limbVal (addPref xs ys (k + 1)) =
          limbVal (addPref xs ys k) +
            (digAt xs k + digAt ys k + carryAt xs ys k) % limbBase *
              limbBase ^ k := by
        rw [addPref_succ, limbVal_snoc, hlen]
      calc
        limbVal (xs.take (k + 1)) + limbVal (ys.take (k + 1))
            = limbVal (xs.take k) + digAt xs k * limbBase ^ k +
                (limbVal (ys.take k) + digAt ys k * limbBase ^ k) := by rw [hx, hy]
        _ = (limbVal (xs.take k) + limbVal (ys.take k)) +
              (digAt xs k * limbBase ^ k + digAt ys k * limbBase ^ k) := by ac_rfl
        _ = (limbVal (xs.take k) + limbVal (ys.take k)) +
              (digAt xs k + digAt ys k) * limbBase ^ k := by rw [← hab]
        _ = (limbVal (addPref xs ys k) + carryAt xs ys k * limbBase ^ k) +
              (digAt xs k + digAt ys k) * limbBase ^ k := by rw [hbal]
        _ = limbVal (addPref xs ys k) +
              ((digAt xs k + digAt ys k) * limbBase ^ k +
                carryAt xs ys k * limbBase ^ k) := by ac_rfl
        _ = limbVal (addPref xs ys k) +
              (digAt xs k + digAt ys k + carryAt xs ys k) * limbBase ^ k := by
              rw [← hsum]
        _ = limbVal (addPref xs ys k) +
              ((digAt xs k + digAt ys k + carryAt xs ys k) % limbBase * limbBase ^ k +
                (digAt xs k + digAt ys k + carryAt xs ys k) / limbBase *
                  (limbBase * limbBase ^ k)) := by rw [hsplit]
        _ = limbVal (addPref xs ys k) +
              ((digAt xs k + digAt ys k + carryAt xs ys k) % limbBase * limbBase ^ k +
                carryAt xs ys (k + 1) * limbBase ^ (k + 1)) := by
              rw [carryAt_succ, hpow]
        _ = (limbVal (addPref xs ys k) +
              (digAt xs k + digAt ys k + carryAt xs ys k) % limbBase * limbBase ^ k) +
              carryAt xs ys (k + 1) * limbBase ^ (k + 1) := by ac_rfl
        _ = limbVal (addPref xs ys (k + 1)) +
              carryAt xs ys (k + 1) * limbBase ^ (k + 1) := by rw [hpref]
private theorem dropTrail_snoc_ne (xs : List Nat) (d : Nat) (hd : d ≠ 0) :
    dropTrail (xs ++ [d]) = xs ++ [d] := by
  induction xs with
  | nil => simp [dropTrail, hd]
  | cons a xs ih =>
    rw [List.cons_append, dropTrail, ih]
    cases xs with
    | nil => simp [hd]
    | cons b bs => rfl

private theorem digAt_tail (a : Nat) (as : List Nat) (i : Nat) :
    digAt (a :: as) (i + 1) = digAt as i := by
  by_cases hi : i < as.length
  · have h : i + 1 < (a :: as).length := by simp [hi]
    simp [digAt, hi, h, List.getElem_cons_succ]
  · have h : ¬ i + 1 < (a :: as).length := by simp; omega
    simp [digAt, hi, h]

private theorem getElem_last_ne (xs : List Nat) (htr : dropTrail xs = xs)
    (hk : 0 < xs.length) :
    digAt xs (xs.length - 1) ≠ 0 := by
  induction xs with
  | nil => simp at hk
  | cons a as ih =>
    cases as with
    | nil =>
      by_cases ha : a = 0
      · simp [dropTrail, ha] at htr
      · simp [digAt, ha]
    | cons b bs =>
      have ih' := ih (trimmed_tail a (b :: bs) htr) (by simp)
      have hidx : (a :: b :: bs).length - 1 = ((b :: bs).length - 1) + 1 := by
        simp
      rw [hidx, digAt_tail]
      exact ih'

private theorem not_past_max (xs ys : List Nat) (i : Nat)
    (hi : i < max xs.length ys.length)
    (hxa : ¬ i < xs.length) (hyb : ¬ i < ys.length) : False := by
  by_cases hle : xs.length ≤ ys.length
  · have hk : max xs.length ys.length = ys.length := Nat.max_eq_right hle
    exact hyb (by simpa [hk] using hi)
  · have hk : max xs.length ys.length = xs.length :=
      Nat.max_eq_left (Nat.le_of_not_le hle)
    exact hxa (by simpa [hk] using hi)

/-- Sum digits, including a final carry limb when the high carry is `1`. -/
def addResult (xs ys : List Nat) : List Nat :=
  let k := max xs.length ys.length
  if carryAt xs ys k = 0 then addPref xs ys k
  else addPref xs ys k ++ [carryAt xs ys k]

theorem addResult_natLimbs (xs ys : List Nat)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase)
    (trx : dropTrail xs = xs) (try_ : dropTrail ys = ys) :
    addResult xs ys = natLimbs (limbVal xs + limbVal ys) := by
  let k := max xs.length ys.length
  obtain ⟨hc, hlen, hdig, hbal⟩ := addScan_inv xs ys hxs hys k
  have hx : xs.take k = xs := take_all xs k (Nat.le_max_left _ _)
  have hy : ys.take k = ys := take_all ys k (Nat.le_max_right _ _)
  have hsum : limbVal xs + limbVal ys =
      limbVal (addPref xs ys k) + carryAt xs ys k * limbBase ^ k := by
    simpa [hx, hy] using hbal
  have hraw : addResult xs ys =
      if carryAt xs ys k = 0 then addPref xs ys k
      else addPref xs ys k ++ [carryAt xs ys k] := by
    rfl
  by_cases hc0 : carryAt xs ys k = 0
  · have hval : limbVal (addPref xs ys k) = limbVal xs + limbVal ys := by
      simpa [hc0] using hsum.symm
    have htr : dropTrail (addPref xs ys k) = addPref xs ys k := by
      by_cases hk0 : k = 0
      · simp [hk0, addPref, dropTrail]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hcell : digAt xs (k - 1) + digAt ys (k - 1) + carryAt xs ys (k - 1) ≠ 0 := by
          by_cases hle : xs.length ≤ ys.length
          · have hkY : k = ys.length := Nat.max_eq_right hle
            have hposY : 0 < ys.length := by omega
            have hdg : digAt ys (ys.length - 1) ≠ 0 :=
              getElem_last_ne ys try_ hposY
            have : k - 1 = ys.length - 1 := by omega
            rw [this, hkY] at *
            omega
          · have hkX : k = xs.length := Nat.max_eq_left (Nat.le_of_not_le hle)
            have hposX : 0 < xs.length := by omega
            have hdg : digAt xs (xs.length - 1) ≠ 0 :=
              getElem_last_ne xs trx hposX
            have : k - 1 = xs.length - 1 := by omega
            rw [this, hkX] at *
            omega
        have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
        have hpref : addPref xs ys k =
            addPref xs ys (k - 1) ++
              [(digAt xs (k - 1) + digAt ys (k - 1) + carryAt xs ys (k - 1)) % limbBase] := by
          simpa [hk1] using addPref_succ xs ys (k - 1)
        have hdiv0 : (digAt xs (k - 1) + digAt ys (k - 1) + carryAt xs ys (k - 1)) /
            limbBase = 0 := by
          have hcLast := hc0
          rw [← hk1, carryAt_succ] at hcLast
          exact hcLast
        have hmod : (digAt xs (k - 1) + digAt ys (k - 1) + carryAt xs ys (k - 1)) %
            limbBase =
            digAt xs (k - 1) + digAt ys (k - 1) + carryAt xs ys (k - 1) :=
          Nat.mod_eq_of_lt (div_zero_lt hdiv0)
        rw [hpref, hmod]
        exact dropTrail_snoc_ne _ _ hcell
    have hmem : ∀ d ∈ addPref xs ys k, d < limbBase := hdig
    have heq := trimmed_eq_natLimbs (addPref xs ys k) hmem htr
    rw [hval] at heq
    simpa [addResult, hc0] using heq
  · have hc1 : carryAt xs ys k = 1 := by omega
    have hval : limbVal (addPref xs ys k ++ [carryAt xs ys k]) =
        limbVal xs + limbVal ys := by
      rw [limbVal_snoc, hlen, ← hsum]
    have htr := dropTrail_snoc_ne (addPref xs ys k) (carryAt xs ys k) (by
      rw [hc1]
      decide)
    have hmem : ∀ d ∈ addPref xs ys k ++ [carryAt xs ys k], d < limbBase := by
      intro d hd
      simp only [List.mem_append, List.mem_singleton] at hd
      cases hd with
      | inl hm => exact hdig d hm
      | inr hm =>
        subst hm
        rw [hc1]
        unfold limbBase
        decide
    have heq := trimmed_eq_natLimbs (addPref xs ys k ++ [carryAt xs ys k]) hmem htr
    rw [hval] at heq
    simpa [addResult, hc0] using heq

/-! ## One emitted limb -/

def magAddStep (a b : Array Int) (toV : Int) (σ : Int × (Array Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Int)) (Array Int)) :=
  let i := σ.1
  let out := σ.2.1
  let carry := σ.2.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (i, (out, carry)))
    else
      match ← ((do
        let cur := carry
        if decide (i < SudoRt.listLen a) then do
          let av ← SudoRt.atL a i
          let cur ← SudoRt.addI cur av
          if decide (i < SudoRt.listLen b) then do
            let bv ← SudoRt.atL b i
            let cur ← SudoRt.addI cur bv
            let dig ← SudoRt.modI cur Megadreifach.limb_base
            let out := (SudoRt.appendL out dig).1
            let carry ← SudoRt.divI cur Megadreifach.limb_base
            pure (SudoRt.Flow.cont (ρ := Array Int) (out, carry))
          else do
            let dig ← SudoRt.modI cur Megadreifach.limb_base
            let out := (SudoRt.appendL out dig).1
            let carry ← SudoRt.divI cur Megadreifach.limb_base
            pure (SudoRt.Flow.cont (ρ := Array Int) (out, carry))
        else do
          if decide (i < SudoRt.listLen b) then do
            let bv ← SudoRt.atL b i
            let cur ← SudoRt.addI cur bv
            let dig ← SudoRt.modI cur Megadreifach.limb_base
            let out := (SudoRt.appendL out dig).1
            let carry ← SudoRt.divI cur Megadreifach.limb_base
            pure (SudoRt.Flow.cont (ρ := Array Int) (out, carry))
          else do
            let dig ← SudoRt.modI cur Megadreifach.limb_base
            let out := (SudoRt.appendL out dig).1
            let carry ← SudoRt.divI cur Megadreifach.limb_base
            pure (SudoRt.Flow.cont (ρ := Array Int) (out, carry))) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int × Int) (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

private theorem decide_len (i : Nat) (xs : List Nat) :
    decide (Int.ofNat i < SudoRt.listLen (embed xs)) = decide (i < xs.length) := by
  rw [listLen_embed, decide_eq_decide, ofNat_lt_iff]

private theorem finish_cell (out : List Nat) (s i toV : Nat)
    (_hfitsS : FitsLen s) (_hiLe : i ≤ toV) (_hfits : FitsLen (i + 1)) :
    (do
      let dig ← SudoRt.modI (Int.ofNat s) Megadreifach.limb_base
      let out := (SudoRt.appendL (embed out) dig).1
      let carry ← SudoRt.divI (Int.ofNat s) Megadreifach.limb_base
      pure (SudoRt.Flow.cont (ρ := Array Int) (out, carry))) =
      .ok (SudoRt.Flow.cont
        (embed (out ++ [s % limbBase]), Int.ofNat (s / limbBase))) := by
  rw [modI_nat_base s, ok_bind, append_dig out (s % limbBase), divI_nat_base s,
    ok_bind, pure_eq_ok]

private theorem magAddStep_scan
    (xs ys : List Nat) (i toV : Nat)
    (hi : i < max xs.length ys.length) (hiLe : i ≤ toV)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase)
    (hc : carryAt xs ys i ≤ 1) (hfits : FitsLen (i + 1)) :
    magAddStep (embed xs) (embed ys) (Int.ofNat toV)
        (Int.ofNat i, (embed (addPref xs ys i), Int.ofNat (carryAt xs ys i))) =
      (if i = toV then
        .ok (SudoRt.Flow.brk (ρ := Array Int)
          (Int.ofNat i,
            (embed (addPref xs ys (i + 1)), Int.ofNat (carryAt xs ys (i + 1)))))
      else
        .ok (SudoRt.Flow.cont (ρ := Array Int)
          (Int.ofNat (i + 1),
            (embed (addPref xs ys (i + 1)), Int.ofNat (carryAt xs ys (i + 1)))))) := by
  have hngt : ¬ (i : Int) > (toV : Int) := by
    rw [← ofNat_eq_natCast i, ← ofNat_eq_natCast toV]
    exact ofNat_not_gt hiLe
  have ha : digAt xs i < limbBase := digAt_bound xs i hxs
  have hb : digAt ys i < limbBase := digAt_bound ys i hys
  have hsumFit := sum3_fits (digAt xs i) (digAt ys i) (carryAt xs ys i) ha hb hc
  unfold magAddStep
  dsimp
  rw [if_neg hngt]
  rw [← ofNat_eq_natCast i, ← ofNat_eq_natCast toV]
  by_cases hxa : i < xs.length
  · have hdecA : decide (Int.ofNat i < SudoRt.listLen (embed xs)) = true := by
      rw [decide_len, decide_eq_true_iff]; exact hxa
    rw [hdecA, if_pos (rfl : true = true)]
    rw [atL_embed xs i hxa, ok_bind, (digAt_get xs i hxa).symm]
    rw [← ofNat_eq_natCast (carryAt xs ys i)]
    rw [addI_ofNat (carryAt xs ys i) (digAt xs i)
        (sum2_fits (digAt xs i) (carryAt xs ys i) ha hc), ok_bind]
    by_cases hxb : i < ys.length
    · have hdecB : decide (Int.ofNat i < SudoRt.listLen (embed ys)) = true := by
        rw [decide_len, decide_eq_true_iff]; exact hxb
      rw [hdecB, if_pos (rfl : true = true)]
      rw [atL_embed ys i hxb, ok_bind, (digAt_get ys i hxb).symm]
      have hord : carryAt xs ys i + digAt xs i + digAt ys i =
          digAt xs i + digAt ys i + carryAt xs ys i := by ac_rfl
      rw [addI_ofNat (carryAt xs ys i + digAt xs i) (digAt ys i)
          (by simpa [Nat.add_assoc, hord] using hsumFit), ok_bind]
      rw [show Int.ofNat (carryAt xs ys i + digAt xs i + digAt ys i) =
            Int.ofNat (digAt xs i + digAt ys i + carryAt xs ys i) from
            congrArg Int.ofNat hord]
      rw [finish_cell (addPref xs ys i)
          (digAt xs i + digAt ys i + carryAt xs ys i) i toV hsumFit hiLe hfits]
      rw [ok_bind]
      dsimp
      simpa [addPref_succ, carryAt_succ] using
        closeCont i toV
          ((digAt xs i + digAt ys i + carryAt xs ys i) / limbBase)
          (addPref xs ys i ++
            [(digAt xs i + digAt ys i + carryAt xs ys i) % limbBase]) hfits
    · have hdecB : decide (Int.ofNat i < SudoRt.listLen (embed ys)) = false := by
        rw [decide_len, decide_eq_false_iff_not]; exact hxb
      rw [hdecB, ite_false_eq]
      have hb0 : digAt ys i = 0 := digAt_ge ys i (Nat.le_of_not_lt hxb)
      have hord : carryAt xs ys i + digAt xs i =
          digAt xs i + digAt ys i + carryAt xs ys i := by
        rw [hb0]; ac_rfl
      rw [show Int.ofNat (carryAt xs ys i + digAt xs i) =
            Int.ofNat (digAt xs i + digAt ys i + carryAt xs ys i) from
            congrArg Int.ofNat hord]
      rw [finish_cell (addPref xs ys i)
          (digAt xs i + digAt ys i + carryAt xs ys i) i toV hsumFit hiLe hfits]
      rw [ok_bind]
      dsimp
      simpa [addPref_succ, carryAt_succ] using
        closeCont i toV
          ((digAt xs i + digAt ys i + carryAt xs ys i) / limbBase)
          (addPref xs ys i ++
            [(digAt xs i + digAt ys i + carryAt xs ys i) % limbBase]) hfits
  · have hdecA : decide (Int.ofNat i < SudoRt.listLen (embed xs)) = false := by
      rw [decide_len, decide_eq_false_iff_not]; exact hxa
    rw [hdecA, ite_false_eq]
    by_cases hxb : i < ys.length
    · have hdecB : decide (Int.ofNat i < SudoRt.listLen (embed ys)) = true := by
        rw [decide_len, decide_eq_true_iff]; exact hxb
      rw [hdecB, if_pos (rfl : true = true)]
      rw [atL_embed ys i hxb, ok_bind, (digAt_get ys i hxb).symm]
      rw [← ofNat_eq_natCast (carryAt xs ys i)]
      have ha0 : digAt xs i = 0 := digAt_ge xs i (Nat.le_of_not_lt hxa)
      have hord : carryAt xs ys i + digAt ys i =
          digAt xs i + digAt ys i + carryAt xs ys i := by
        rw [ha0]; ac_rfl
      rw [addI_ofNat (carryAt xs ys i) (digAt ys i)
          (sum2_fits (digAt ys i) (carryAt xs ys i) hb hc), ok_bind]
      rw [show Int.ofNat (carryAt xs ys i + digAt ys i) =
            Int.ofNat (digAt xs i + digAt ys i + carryAt xs ys i) from
            congrArg Int.ofNat hord]
      rw [finish_cell (addPref xs ys i)
          (digAt xs i + digAt ys i + carryAt xs ys i) i toV hsumFit hiLe hfits]
      rw [ok_bind]
      dsimp
      simpa [addPref_succ, carryAt_succ] using
        closeCont i toV
          ((digAt xs i + digAt ys i + carryAt xs ys i) / limbBase)
          (addPref xs ys i ++
            [(digAt xs i + digAt ys i + carryAt xs ys i) % limbBase]) hfits
    · exact (not_past_max xs ys i hi hxa hxb).elim

private theorem decRec_pos {α : Sort _} {p : Prop} [d : Decidable p] (hp : p)
    (a : ¬p → α) (b : p → α) : Decidable.rec a b d = b hp := by
  cases d with
  | isFalse h => exact absurd hp h
  | isTrue h =>
    cases Subsingleton.elim h hp
    rfl

private theorem decRec_neg {α : Sort _} {p : Prop} [d : Decidable p] (hp : ¬p)
    (a : ¬p → α) (b : p → α) : Decidable.rec a b d = a hp := by
  cases d with
  | isTrue h => exact absurd h hp
  | isFalse h =>
    cases Subsingleton.elim h hp
    rfl

private theorem len_gt_decide (xs ys : List Nat) :
    decide (SudoRt.listLen (embed ys) > SudoRt.listLen (embed xs)) =
      decide (xs.length < ys.length) := by
  rw [listLen_embed, listLen_embed, decide_eq_decide]
  exact ofNat_lt_iff xs.length ys.length

private theorem magAdd_after (xs ys : List Nat) (k : Nat)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase)
    (trx : dropTrail xs = xs) (try_ : dropTrail ys = ys)
    (hk : k = max xs.length ys.length) :
    (let out := embed (addPref xs ys k)
     let carry := Int.ofNat (carryAt xs ys k)
     (if decide (carry > (0 : Int)) = true then
        (pure (SudoRt.appendL out carry).1 : Except SudoRt.Trap (Array Int))
      else
        pure out)) =
      .ok (embed (natLimbs (limbVal xs + limbVal ys))) := by
  simp only
  have hres := addResult_natLimbs xs ys hxs hys trx try_
  by_cases hc0 : carryAt xs ys k = 0
  · have hdec : decide (Int.ofNat (carryAt xs ys k) > (0 : Int)) = false := by
      rw [hc0]
      decide
    rw [hdec, ite_false_eq, pure_eq_ok]
    have hraw : addResult xs ys = addPref xs ys k := by
      simp [addResult, ← hk, hc0]
    rw [← hres, hraw]
  · have hpos : 0 < carryAt xs ys k := Nat.pos_of_ne_zero hc0
    have hdec : decide (Int.ofNat (carryAt xs ys k) > (0 : Int)) = true := by
      rw [decide_eq_true_iff, ofNat_pos_iff]
      exact hpos
    rw [hdec, if_pos (rfl : true = true), append_dig, pure_eq_ok]
    have hraw : addResult xs ys =
        addPref xs ys k ++ [carryAt xs ys k] := by
      simp [addResult, ← hk, hc0]
    rw [← hres, hraw]

private theorem run_add (xs ys : List Nat) (k : Nat)
    (hpos : 0 < k) (hk : k = max xs.length ys.length)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase)
    (trx : dropTrail xs = xs) (try_ : dropTrail ys = ys)
    (hfits : FitsLen (k + 1))
    (goal : Except SudoRt.Trap (Array Int))
    (hgoal : goal = .ok (embed (natLimbs (limbVal xs + limbVal ys)))) :
    SudoRt.runLoopOn
      (Int.ofNat 0, (embed (addPref xs ys 0), Int.ofNat (carryAt xs ys 0)))
      (fuelRange (Int.ofNat 0) (Int.ofNat (k - 1)))
      (magAddStep (embed xs) (embed ys) (Int.ofNat (k - 1)))
      (fun σ =>
        let out := σ.2.1
        let carry := σ.2.2
        if decide (carry > (0 : Int)) = true then
          pure (SudoRt.appendL out carry).1
        else
          pure out)
      (fun r => pure r) = goal := by
  apply chain_loop
    (f := fun i => (embed (addPref xs ys i), Int.ofNat (carryAt xs ys i)))
    (fromN := 0) (toN := k - 1)
    (hle := Nat.zero_le _)
    (goal := goal)
  · intro i _ hi2
    have hi : i < k := by omega
    have hfiti : FitsLen (i + 1) := FitsLen.of_le hfits (by omega)
    have hlt : i < max xs.length ys.length := by simpa [hk] using hi
    have hbr : carryAt xs ys i ≤ 1 :=
      (addScan_inv xs ys hxs hys i).1
    simpa using magAddStep_scan xs ys i (k - 1) hlt hi2 hxs hys hbr hfiti
  · have hk1 : (k - 1) + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    rw [hk1]
    have hafter := magAdd_after xs ys k hxs hys trx try_ hk
    rw [hafter, hgoal]

/--
  `mag_add` of two trimmed limb strings. The emitted digits are
  `natLimbs` of the sum. `FitsLen` is the length of the longer string, plus
  one, so the final carry limb and the index `i + 1` stay inside an i64.
-/
theorem mag_add_limbs (xs ys : List Nat)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase)
    (trx : dropTrail xs = xs) (try_ : dropTrail ys = ys)
    (hfits : FitsLen (max xs.length ys.length + 1)) :
    Megadreifach.mag_add (embed xs) (embed ys) =
      .ok (embed (natLimbs (limbVal xs + limbVal ys))) := by
  unfold Megadreifach.mag_add
  dsimp
  split
  · rename_i hdec
    have hlt : xs.length < ys.length := by
      rw [len_gt_decide] at hdec
      exact decide_eq_true_iff.mp hdec
    have hpos : 0 < ys.length := by omega
    have hk : ys.length = max xs.length ys.length :=
      (Nat.max_eq_right (Nat.le_of_lt hlt)).symm
    have hfit1 : FitsLen (ys.length + 1) := by
      rw [← hk] at hfits
      exact hfits
    have hfitK : FitsLen ys.length := FitsLen.succ_of_succ hfit1
    rw [listLen_embed, subI_ofNat_one ys.length hpos hfitK, ok_bind, except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise
        (step' := magAddStep (embed xs) (embed ys) (Int.ofNat (ys.length - 1)))
      intro σ
      unfold magAddStep
      simp only [listLen_embed]
      rfl
    · rw [show (0 : Int) = Int.ofNat 0 from rfl]
      exact run_add xs ys ys.length hpos hk hxs hys trx try_ hfit1
        (.ok (embed (natLimbs (limbVal xs + limbVal ys)))) rfl
  · rename_i hdec
    have hlt : ¬ xs.length < ys.length := by
      rw [len_gt_decide] at hdec
      intro hp
      exact hdec (decide_eq_true_iff.mpr hp)
    by_cases hxs0 : xs.length = 0
    · have hys0 : ys.length = 0 := by
        have hle : ys.length ≤ xs.length := Nat.le_of_not_lt hlt
        omega
      have hx0 : xs = [] := List.eq_nil_of_length_eq_zero hxs0
      have hy0 : ys = [] := List.eq_nil_of_length_eq_zero hys0
      subst hx0; subst hy0
      rw [listLen_embed, show ([] : List Nat).length = 0 from rfl]
      have hsub : SudoRt.subI (Int.ofNat 0) 1 = .ok (-1) := subI_zero_one
      rw [hsub, ok_bind, except_bind_pure]
      have hgt : (0 : Int) > (-1) := by decide
      rw [if_pos hgt,
        show (1 : Nat) = fuelRange (0 : Int) (-1) from (fuelRange_gt hgt).symm]
      apply Eq.trans
      · apply runLoopOn_step_pointwise
          (step' := magAddStep (embed ([] : List Nat)) (embed ([] : List Nat)) (-1))
        intro σ
        unfold magAddStep
        rfl
      · have hstep : magAddStep (embed ([] : List Nat)) (embed ([] : List Nat)) (-1)
            ((0 : Int), ((#[] : Array Int), (0 : Int))) =
            .ok (SudoRt.Flow.brk ((0 : Int), ((#[] : Array Int), (0 : Int)))) := by
          unfold magAddStep
          rw [if_pos hgt]
          rfl
        rw [asc_break (0 : Int) (-1) ((#[] : Array Int), (0 : Int)) _ _ _ hgt hstep]
        simp [limbVal, natLimbs_zero, embed_nil, pure_eq_ok]
    · have hposX : 0 < xs.length := Nat.pos_of_ne_zero hxs0
      have hleY : ys.length ≤ xs.length := Nat.le_of_not_lt hlt
      have hk : xs.length = max xs.length ys.length := (Nat.max_eq_left hleY).symm
      have hfit1 : FitsLen (xs.length + 1) := by
        rw [← hk] at hfits
        exact hfits
      have hfitK : FitsLen xs.length := FitsLen.succ_of_succ hfit1
      rw [listLen_embed, subI_ofNat_one xs.length hposX hfitK, ok_bind, except_bind_pure]
      apply Eq.trans
      · apply runLoopOn_step_pointwise
          (step' := magAddStep (embed xs) (embed ys) (Int.ofNat (xs.length - 1)))
        intro σ
        unfold magAddStep
        simp only [listLen_embed]
        rfl
      · rw [show (0 : Int) = Int.ofNat 0 from rfl]
        exact run_add xs ys xs.length hposX hk hxs hys trx try_ hfit1
          (.ok (embed (natLimbs (limbVal xs + limbVal ys)))) rfl

private theorem sum_lt_pow (n m k : Nat)
    (hn : n < limbBase ^ k) (hm : m < limbBase ^ k) :
    n + m < limbBase ^ (k + 1) := by
  have h2 : n + m < 2 * limbBase ^ k := by omega
  have hmul : 2 * limbBase ^ k ≤ limbBase * limbBase ^ k :=
    Nat.mul_le_mul_right _ two_le_base
  have hpow : limbBase * limbBase ^ k = limbBase ^ (k + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  exact Nat.lt_of_lt_of_le h2 (by simpa [hpow] using hmul)

private theorem nat_lt_limbpow (n k : Nat) (hk : (natLimbs n).length ≤ k) :
    n < limbBase ^ k := by
  have hlt : n < limbBase ^ (natLimbs n).length := by
    simpa [limbVal_natLimbs] using
      limbVal_lt_pow (natLimbs n) (natLimbs_digits n)
  exact Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right limbBase_pos hk)

private theorem sum_limb_len (n m : Nat) :
    (natLimbs (n + m)).length ≤
      max (natLimbs n).length (natLimbs m).length + 1 := by
  let k := max (natLimbs n).length (natLimbs m).length
  have hn := nat_lt_limbpow n k (Nat.le_max_left _ _)
  have hm := nat_lt_limbpow m k (Nat.le_max_right _ _)
  exact natLimbs_length_le (n + m) (k + 1) (sum_lt_pow n m k hn hm)

/-- `mag_add` on the canonical limbs of two natural numbers. -/
theorem mag_add_nat (n m : Nat)
    (hfits : FitsLen (max (natLimbs n).length (natLimbs m).length + 1)) :
    Megadreifach.mag_add (embed (natLimbs n)) (embed (natLimbs m)) =
      .ok (embed (natLimbs (n + m))) := by
  have h := mag_add_limbs (natLimbs n) (natLimbs m)
      (natLimbs_digits n) (natLimbs_digits m)
      (dropTrail_natLimbs n) (dropTrail_natLimbs m) hfits
  simpa [limbVal_natLimbs] using h

/-- `big_add` on the canonical limbs of two natural numbers. -/
theorem big_add_nat (n m : Nat)
    (hfits : FitsLen (max (natLimbs n).length (natLimbs m).length + 1)) :
    Megadreifach.big_add (bigOf (natLimbs n)) (bigOf (natLimbs m)) =
      .ok (bigOf (natLimbs (n + m))) := by
  unfold Megadreifach.big_add
  dsimp [bigOf]
  rw [mag_add_nat n m hfits, ok_bind]
  have hlen : FitsLen (natLimbs (n + m)).length :=
    FitsLen.of_le hfits (sum_limb_len n m)
  rw [make_big_false (natLimbs (n + m)) hlen, dropTrail_natLimbs, ok_bind, pure_eq_ok]
  rfl

end MegaDreifach.Link2
