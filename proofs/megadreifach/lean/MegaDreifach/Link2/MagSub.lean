/-
  LINK 2. `mag_sub` at arbitrary width.

  Schoolbook subtraction of two canonical base-`10^9` limb strings.
  The subtrahend is at most the minuend, so the final borrow is `0` and
  `trim` yields `natLimbs (n - m)`. Each limb stays inside an i64: a digit
  is `< 10^9` and the only negative intermediate is `≥ -10^9`.

  This is the remainder step of `peel_leading` once the digit times `d!`
  may have more than three limbs. Not `phi_chunk`. Not `v_Hash`.
  Not emitter soundness.
-/
import MegaDreifach.Link2.PeelOne
import MegaDreifach.Link2.DivInd

namespace MegaDreifach.Link2

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem bind_pure_flow {σ ρ β} (fl : SudoRt.Flow σ ρ)
    (f : SudoRt.Flow σ ρ → Except SudoRt.Trap β) :
    (pure fl >>= f) = f fl := rfl

private theorem not_neg (k : Nat) : decide (Int.ofNat k < 0) = false := by
  rw [decide_eq_false_iff_not]
  exact Int.not_lt.mpr (Int.ofNat_zero_le _)

private theorem neg_lt_zero (k : Nat) (hk : 0 < k) :
    decide (-(k : Int) < 0) = true := by
  rw [decide_eq_true_iff]
  have : (0 : Int) < (k : Int) := (ofNat_pos_iff k).mpr hk
  omega

private theorem append_dig (out : List Nat) (k : Nat) :
    (SudoRt.appendL (embed out) (Int.ofNat k)).1 = embed (out ++ [k]) := by
  rw [appendL_spec]
  exact push_embed out k

private theorem narrowI_neg (k : Nat) (hk : k ≤ limbBase) :
    SudoRt.narrowI (-(k : Int)) = .ok (-(k : Int)) := by
  unfold SudoRt.narrowI
  have hB : SudoRt.i64Min ≤ -(limbBase : Int) := by
    unfold SudoRt.i64Min limbBase
    decide
  have hlo : SudoRt.i64Min ≤ -(k : Int) := by
    have hkI : (k : Int) ≤ (limbBase : Int) := Int.ofNat_le.mpr hk
    exact Int.le_trans hB (Int.neg_le_neg hkI)
  have hhi : -(k : Int) ≤ SudoRt.i64Max := by
    have h0 : -(k : Int) ≤ 0 := Int.neg_nonpos_of_nonneg (Int.ofNat_nonneg k)
    have hmax : (0 : Int) ≤ SudoRt.i64Max := by decide
    exact Int.le_trans h0 hmax
  split
  · next ht =>
    simp only [Bool.or_eq_true, decide_eq_true_iff] at ht
    cases ht with
    | inl h => exact absurd h (Int.not_lt.mpr hlo)
    | inr h => exact absurd h (Int.not_lt.mpr hhi)
  · rfl

private theorem addI_neg_base (k : Nat) (hk0 : 0 < k) (hk : k ≤ limbBase) :
    SudoRt.addI (-(k : Int)) Megadreifach.limb_base =
      .ok (Int.ofNat (limbBase - k)) := by
  unfold SudoRt.addI
  rw [limb_base_eq]
  have hsum : -(k : Int) + (limbBase : Int) = Int.ofNat (limbBase - k) := by
    have : (limbBase : Int) - (k : Int) = Int.ofNat (limbBase - k) :=
      (Int.ofNat_sub hk).symm
    omega
  rw [hsum]
  exact narrowI_ofNat (limbBase - k) (fits_of_lt_limb (Nat.sub_lt limbBase_pos hk0))

private theorem decide_ge (i len : Nat) (h : len ≤ i) :
    decide (Int.ofNat i < Int.ofNat len) = false := by
  rw [decide_eq_false_iff_not, ofNat_lt_iff]
  exact Nat.not_lt.mpr h

/-- Break or continue once a limb digit has been appended. -/
private theorem closeCont (i toV br : Nat) (out : List Nat)
    (hfits : FitsLen (i + 1)) :
    (if ((Int.ofNat i) == (Int.ofNat toV)) = true then
        (pure (SudoRt.Flow.brk (ρ := Array Int)
            (Int.ofNat i, (Int.ofNat br, embed out))) :
          Except SudoRt.Trap (SudoRt.Flow (Int × (Int × Array Int)) (Array Int)))
      else
        SudoRt.addI (Int.ofNat i) (1 : Int) >>= fun i' =>
          pure (SudoRt.Flow.cont (ρ := Array Int)
            (i', (Int.ofNat br, embed out)))) =
      (if i = toV then
        .ok (SudoRt.Flow.brk (ρ := Array Int)
          (Int.ofNat i, (Int.ofNat br, embed out)))
      else
        .ok (SudoRt.Flow.cont (ρ := Array Int)
          (Int.ofNat (i + 1), (Int.ofNat br, embed out)))) := by
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

/-! ## Digit model -/

/-- Limb `i`, or `0` once the list runs out. -/
def digAt (xs : List Nat) (i : Nat) : Nat :=
  if h : i < xs.length then xs[i] else 0

theorem digAt_get (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    digAt xs i = xs[i] := by
  simp [digAt, hi]

theorem digAt_ge (xs : List Nat) (i : Nat) (hi : xs.length ≤ i) :
    digAt xs i = 0 := by
  simp [digAt, Nat.not_lt.mpr hi]

theorem digAt_bound (xs : List Nat) (i : Nat) (h : ∀ d ∈ xs, d < limbBase) :
    digAt xs i < limbBase := by
  by_cases hi : i < xs.length
  · rw [digAt_get xs i hi]
    exact h _ (List.getElem_mem hi)
  · rw [digAt_ge xs i (Nat.le_of_not_lt hi)]
    exact limbBase_pos

theorem subDigit_spec (a b br : Nat)
    (ha : a < limbBase) (hb : b < limbBase) (hbr : br ≤ 1) :
    (subDigit a b br).1 < limbBase ∧ (subDigit a b br).2 ≤ 1 ∧
      a + (subDigit a b br).2 * limbBase =
        (subDigit a b br).1 + b + br := by
  unfold subDigit
  by_cases hle : b + br ≤ a
  · simp only [hle, ↓reduceIte, Nat.zero_mul, Nat.zero_add]
    refine ⟨Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha, Nat.zero_le _, ?_⟩
    have : a - (b + br) + (b + br) = a := Nat.sub_add_cancel hle
    omega
  · simp only [hle, ↓reduceIte]
    have hlt : a < b + br := Nat.lt_of_not_le hle
    have hsum : b + br ≤ a + limbBase := by omega
    have hd : a + limbBase - (b + br) < limbBase := by omega
    refine ⟨hd, Nat.le_refl _, ?_⟩
    have : a + limbBase - (b + br) + (b + br) = a + limbBase :=
      Nat.sub_add_cancel hsum
    omega

/-- Borrow entering limb `i`. -/
def brAt (xs ys : List Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => (subDigit (digAt xs i) (digAt ys i) (brAt xs ys i)).2

/-- Little-endian difference digits through index `k` (not yet trimmed). -/
def subPref (xs ys : List Nat) : Nat → List Nat
  | 0 => []
  | i + 1 =>
      subPref xs ys i ++
        [(subDigit (digAt xs i) (digAt ys i) (brAt xs ys i)).1]

@[simp] theorem brAt_zero (xs ys : List Nat) : brAt xs ys 0 = 0 := rfl

@[simp] theorem brAt_succ (xs ys : List Nat) (i : Nat) :
    brAt xs ys (i + 1) =
      (subDigit (digAt xs i) (digAt ys i) (brAt xs ys i)).2 := rfl

@[simp] theorem subPref_zero (xs ys : List Nat) : subPref xs ys 0 = [] := rfl

@[simp] theorem subPref_succ (xs ys : List Nat) (i : Nat) :
    subPref xs ys (i + 1) =
      subPref xs ys i ++
        [(subDigit (digAt xs i) (digAt ys i) (brAt xs ys i)).1] := rfl

theorem limbVal_snoc (xs : List Nat) (x : Nat) :
    limbVal (xs ++ [x]) = limbVal xs + x * limbBase ^ xs.length := by
  induction xs with
  | nil => simp [limbVal]
  | cons a xs ih =>
    rw [List.cons_append, limbVal, ih]
    calc
      a + limbBase * (limbVal xs + x * limbBase ^ xs.length)
          = a + (limbBase * limbVal xs + limbBase * (x * limbBase ^ xs.length)) := by
            rw [Nat.mul_add]
      _ = (a + limbBase * limbVal xs) + limbBase * (x * limbBase ^ xs.length) := by
            rw [Nat.add_assoc]
      _ = (a + limbBase * limbVal xs) + (limbBase * x) * limbBase ^ xs.length := by
            rw [← Nat.mul_assoc]
      _ = (a + limbBase * limbVal xs) + (x * limbBase) * limbBase ^ xs.length := by
            rw [Nat.mul_comm limbBase x]
      _ = (a + limbBase * limbVal xs) + x * (limbBase * limbBase ^ xs.length) := by
            rw [Nat.mul_assoc]
      _ = (a + limbBase * limbVal xs) + x * (limbBase ^ xs.length * limbBase) := by
            rw [Nat.mul_comm limbBase (limbBase ^ xs.length)]
      _ = (a + limbBase * limbVal xs) + x * limbBase ^ (xs.length + 1) := by
            rw [← Nat.pow_succ]

theorem length_take_le (xs : List Nat) (k : Nat) (hk : k ≤ xs.length) :
    (xs.take k).length = k := by
  simpa [Nat.min_eq_left hk] using List.length_take k xs

theorem take_all (xs : List Nat) (k : Nat) (hk : xs.length ≤ k) : xs.take k = xs := by
  have hd : xs.drop k = [] := List.drop_eq_nil_of_le hk
  have happ := List.take_append_drop k xs
  rw [hd, List.append_nil] at happ
  exact happ

theorem limbVal_take_succ_dig (ys : List Nat) (k : Nat) :
    limbVal (ys.take (k + 1)) =
      limbVal (ys.take k) + digAt ys k * limbBase ^ k := by
  by_cases hk : k < ys.length
  · rw [take_succ_get ys k hk, limbVal_snoc,
      length_take_le ys k (Nat.le_of_lt hk), digAt_get ys k hk]
  · rw [take_all ys k (Nat.le_of_not_lt hk),
      take_all ys (k + 1) (Nat.le_succ_of_le (Nat.le_of_not_lt hk)),
      digAt_ge ys k (Nat.le_of_not_lt hk), Nat.zero_mul, Nat.add_zero]

theorem subScan_inv (xs ys : List Nat)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase) :
    ∀ k, k ≤ xs.length →
      brAt xs ys k ≤ 1 ∧
      (subPref xs ys k).length = k ∧
      (∀ d ∈ subPref xs ys k, d < limbBase) ∧
      limbVal (xs.take k) + brAt xs ys k * limbBase ^ k =
        limbVal (subPref xs ys k) + limbVal (ys.take k) := by
  intro k hk
  induction k with
  | zero =>
    simp [limbVal, List.take_zero]
  | succ k ih =>
    have hklt : k < xs.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
    obtain ⟨hbr, hlen, hdig, hbal⟩ := ih (Nat.le_of_lt hklt)
    have ha : digAt xs k < limbBase := digAt_bound xs k hxs
    have hb : digAt ys k < limbBase := digAt_bound ys k hys
    have hspec := subDigit_spec (digAt xs k) (digAt ys k) (brAt xs ys k) ha hb hbr
    have hdlt : (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).1 < limbBase :=
      hspec.1
    have hbr' : (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).2 ≤ 1 :=
      hspec.2.1
    have heq : digAt xs k +
          (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).2 * limbBase =
        (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).1 +
          digAt ys k + brAt xs ys k := hspec.2.2
    refine ⟨hbr', ?_, ?_, ?_⟩
    · simp [hlen]
    · intro d hd
      simp only [subPref_succ, List.mem_append, List.mem_singleton] at hd
      cases hd with
      | inl hm => exact hdig d hm
      | inr hm =>
        subst hm
        exact hdlt
    · have hxstake : limbVal (xs.take (k + 1)) =
          limbVal (xs.take k) + digAt xs k * limbBase ^ k := by
        rw [take_succ_get xs k hklt, limbVal_snoc,
          length_take_le xs k (Nat.le_of_lt hklt), digAt_get xs k hklt]
      have hystake := limbVal_take_succ_dig ys k
      have hpow : limbBase * limbBase ^ k = limbBase ^ (k + 1) := by
        rw [Nat.mul_comm, ← Nat.pow_succ]
      have hmul : (digAt xs k +
            (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).2 * limbBase) *
            limbBase ^ k =
          digAt xs k * limbBase ^ k +
            (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).2 *
              limbBase ^ (k + 1) := by
        calc
          (digAt xs k +
                (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).2 * limbBase) *
              limbBase ^ k
              = digAt xs k * limbBase ^ k +
                  ((subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).2 * limbBase) *
                    limbBase ^ k := by rw [Nat.add_mul]
          _ = digAt xs k * limbBase ^ k +
                (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).2 *
                  (limbBase * limbBase ^ k) := by rw [Nat.mul_assoc]
          _ = digAt xs k * limbBase ^ k +
                (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).2 *
                  limbBase ^ (k + 1) := by rw [hpow]
      have hmulR : ((subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).1 +
            digAt ys k + brAt xs ys k) * limbBase ^ k =
          (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).1 * limbBase ^ k +
            digAt ys k * limbBase ^ k + brAt xs ys k * limbBase ^ k := by
        simp [Nat.add_mul, Nat.add_assoc]
      have hscaled := congrArg (fun t => t * limbBase ^ k) heq
      dsimp at hscaled
      rw [hmul, hmulR] at hscaled
      have hpref : limbVal (subPref xs ys (k + 1)) =
          limbVal (subPref xs ys k) +
            (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).1 * limbBase ^ k := by
        rw [subPref_succ, limbVal_snoc, hlen]
      calc
        limbVal (xs.take (k + 1)) + brAt xs ys (k + 1) * limbBase ^ (k + 1)
            = limbVal (xs.take k) + digAt xs k * limbBase ^ k +
                (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).2 *
                  limbBase ^ (k + 1) := by
              rw [hxstake, brAt_succ]
        _ = limbVal (xs.take k) +
              (digAt xs k * limbBase ^ k +
                (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).2 *
                  limbBase ^ (k + 1)) := by rw [Nat.add_assoc]
        _ = limbVal (xs.take k) +
              ((subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).1 * limbBase ^ k +
                digAt ys k * limbBase ^ k + brAt xs ys k * limbBase ^ k) := by
              rw [hscaled]
        _ = (limbVal (xs.take k) + brAt xs ys k * limbBase ^ k) +
              ((subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).1 * limbBase ^ k +
                digAt ys k * limbBase ^ k) := by ac_rfl
        _ = (limbVal (subPref xs ys k) + limbVal (ys.take k)) +
              ((subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).1 * limbBase ^ k +
                digAt ys k * limbBase ^ k) := by rw [hbal]
        _ = (limbVal (subPref xs ys k) +
              (subDigit (digAt xs k) (digAt ys k) (brAt xs ys k)).1 * limbBase ^ k) +
              (limbVal (ys.take k) + digAt ys k * limbBase ^ k) := by ac_rfl
        _ = limbVal (subPref xs ys (k + 1)) + limbVal (ys.take (k + 1)) := by
              rw [hpref, hystake]

theorem natLimbs_len_mono (m n : Nat) (hmn : m ≤ n) :
    (natLimbs m).length ≤ (natLimbs n).length := by
  have hn : n < limbBase ^ (natLimbs n).length := by
    simpa [limbVal_natLimbs] using
      limbVal_lt_pow (natLimbs n) (natLimbs_digits n)
  exact natLimbs_length_le m _ (Nat.lt_of_le_of_lt hmn hn)

theorem subPref_trimmed (xs ys : List Nat)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase)
    (hlen : ys.length ≤ xs.length) (hle : limbVal ys ≤ limbVal xs) :
    dropTrail (subPref xs ys xs.length) =
      natLimbs (limbVal xs - limbVal ys) := by
  obtain ⟨hbr, hlenP, hdig, hbal⟩ :=
    subScan_inv xs ys hxs hys xs.length (Nat.le_refl _)
  have htakeX : xs.take xs.length = xs := List.take_length xs
  have htakeY : ys.take xs.length = ys := take_all ys xs.length hlen
  have hsum : limbVal xs + brAt xs ys xs.length * limbBase ^ xs.length =
      limbVal (subPref xs ys xs.length) + limbVal ys := by
    simpa [htakeX, htakeY] using hbal
  have hbr0 : brAt xs ys xs.length = 0 := by
    by_cases hbr1 : brAt xs ys xs.length = 1
    · have hlt := limbVal_lt_pow (subPref xs ys xs.length) hdig
      rw [hlenP] at hlt
      have hltN : limbVal xs < limbVal ys := by
        have hstrict : limbVal xs + limbBase ^ xs.length <
            limbBase ^ xs.length + limbVal ys := by
          calc
            limbVal xs + limbBase ^ xs.length
                = limbVal (subPref xs ys xs.length) + limbVal ys := by
                  simpa [hbr1, Nat.one_mul] using hsum
            _ < limbBase ^ xs.length + limbVal ys := Nat.add_lt_add_right hlt _
        omega
      omega
    · omega
  have hval : limbVal (subPref xs ys xs.length) = limbVal xs - limbVal ys := by
    have : limbVal xs = limbVal (subPref xs ys xs.length) + limbVal ys := by
      simpa [hbr0] using hsum
    omega
  have hmem : ∀ d ∈ dropTrail (subPref xs ys xs.length), d < limbBase :=
    fun d hd => hdig d (mem_dropTrail _ hd)
  have heq := trimmed_eq_natLimbs (dropTrail (subPref xs ys xs.length)) hmem
    (dropTrail_idem _)
  rw [limbVal_dropTrail, hval] at heq
  exact heq

/-! ## One emitted step past the subtrahend -/

/-- Subtract a literal `0` limb. Same arithmetic as the emitter's
    "index past `b`" branch, which never reads `b`. -/
private def pastLimb (cur : Int) (out : Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  if decide (cur < (0 : Int)) then do
    let cur ← SudoRt.addI cur Megadreifach.limb_base
    let out := (SudoRt.appendL out cur).1
    pure (SudoRt.Flow.cont (ρ := Array Int) ((1 : Int), out))
  else do
    let out := (SudoRt.appendL out cur).1
    pure (SudoRt.Flow.cont (ρ := Array Int) ((0 : Int), out))

private theorem ite_false_eq {α} (a b : α) :
    (if false = true then a else b) = b := by
  simp [Bool.false_eq_true]

private theorem pastLimb_nonneg (k : Nat) (out : List Nat) :
    pastLimb (Int.ofNat k) (embed out) =
      .ok (SudoRt.Flow.cont ((0 : Int), embed (out ++ [k]))) := by
  unfold pastLimb
  have hnn : decide (Int.ofNat k < 0) = false := by
    rw [decide_eq_false_iff_not]
    exact Int.not_lt.mpr (Int.ofNat_zero_le k)
  rw [hnn, ite_false_eq, append_dig out k]
  rfl

private theorem pastLimb_neg1 (out : List Nat) :
    pastLimb (-1) (embed out) =
      .ok (SudoRt.Flow.cont ((1 : Int), embed (out ++ [limbBase - 1]))) := by
  unfold pastLimb
  have hlt : decide ((-1 : Int) < 0) = true := by decide
  rw [hlt, if_pos (rfl : (true = true))]
  have hone : (1 : Nat) ≤ limbBase := by unfold limbBase; decide
  erw [addI_neg_base 1 (by decide) hone]
  rw [ok_bind, append_dig out (limbBase - 1)]
  rfl

/-- Limb `i` when `ys` has already ended. The missing digit is `0`. -/
private theorem magSubStep_past
    (xs ys out : List Nat) (i toV ai br : Nat)
    (hi : i < xs.length) (hpast : ys.length ≤ i)
    (hxi : xs[i] = ai) (hai : ai < limbBase) (hbr : br ≤ 1)
    (hiLe : i ≤ toV) (hfits : FitsLen (i + 1)) :
    magSubStep (embed xs) (embed ys) (Int.ofNat toV)
        (Int.ofNat i, (Int.ofNat br, embed out)) =
      (if i = toV then
        .ok (SudoRt.Flow.brk (ρ := Array Int)
          (Int.ofNat i, (Int.ofNat (subDigit ai 0 br).2,
            embed (out ++ [(subDigit ai 0 br).1]))))
      else
        .ok (SudoRt.Flow.cont (ρ := Array Int)
          (Int.ofNat (i + 1), (Int.ofNat (subDigit ai 0 br).2,
            embed (out ++ [(subDigit ai 0 br).1]))))) := by
  have hskip := decide_ge i ys.length hpast
  have hngt : ¬ Int.ofNat i > Int.ofNat toV := ofNat_not_gt hiLe
  unfold magSubStep
  rw [if_neg hngt]
  rw [atL_embed xs i hi, ok_bind, hxi]
  by_cases hbr0 : br = 0
  · subst hbr0
    rw [subI_ofNat ai 0 (fits_of_lt_limb hai) (Nat.zero_le _), ok_bind, Nat.sub_zero,
      listLen_embed, hskip, ite_false_eq]
    have hpastL : pastLimb (Int.ofNat ai) (embed out) =
        (if decide (Int.ofNat ai < 0) = true then do
          let cur ← SudoRt.addI (Int.ofNat ai) Megadreifach.limb_base
          let out := (SudoRt.appendL (embed out) cur).1
          pure (SudoRt.Flow.cont (ρ := Array Int) ((1 : Int), out))
        else do
          let out := (SudoRt.appendL (embed out) (Int.ofNat ai)).1
          pure (SudoRt.Flow.cont (ρ := Array Int) ((0 : Int), out))) := by
      unfold pastLimb
      rfl
    rw [← hpastL, pastLimb_nonneg ai out, ok_bind]
    dsimp
    have hdig : subDigit ai 0 0 = (ai, 0) := by
      unfold subDigit
      rw [if_pos (Nat.zero_le ai), Nat.sub_zero]
    rw [hdig]
    exact closeCont i toV 0 (out ++ [ai]) hfits
  · have hbr1 : br = 1 := by omega
    subst hbr1
    by_cases hai0 : ai = 0
    · subst hai0
      erw [subI_zero_one]
      rw [ok_bind, listLen_embed, hskip, ite_false_eq]
      have hpastL : pastLimb (-1) (embed out) =
          (if decide ((-1 : Int) < 0) = true then do
            let cur ← SudoRt.addI (-1) Megadreifach.limb_base
            let out := (SudoRt.appendL (embed out) cur).1
            pure (SudoRt.Flow.cont (ρ := Array Int) ((1 : Int), out))
          else do
            let out := (SudoRt.appendL (embed out) (-1)).1
            pure (SudoRt.Flow.cont (ρ := Array Int) ((0 : Int), out))) := by
        unfold pastLimb
        rfl
      rw [← hpastL, pastLimb_neg1 out, ok_bind]
      dsimp
      have hdig : subDigit 0 0 1 = (limbBase - 1, 1) := by
        unfold subDigit
        rw [if_neg (by omega : ¬ 0 + 1 ≤ 0)]
        exact Prod.ext (by omega) rfl
      rw [hdig]
      exact closeCont i toV 1 (out ++ [limbBase - 1]) hfits
    · have hai1 : 1 ≤ ai := by omega
      rw [subI_ofNat ai 1 (fits_of_lt_limb hai) hai1, ok_bind,
        listLen_embed, hskip, ite_false_eq]
      have hpastL : pastLimb (Int.ofNat (ai - 1)) (embed out) =
          (if decide (Int.ofNat (ai - 1) < 0) = true then do
            let cur ← SudoRt.addI (Int.ofNat (ai - 1)) Megadreifach.limb_base
            let out := (SudoRt.appendL (embed out) cur).1
            pure (SudoRt.Flow.cont (ρ := Array Int) ((1 : Int), out))
          else do
            let out := (SudoRt.appendL (embed out) (Int.ofNat (ai - 1))).1
            pure (SudoRt.Flow.cont (ρ := Array Int) ((0 : Int), out))) := by
        unfold pastLimb
        rfl
      rw [← hpastL, pastLimb_nonneg (ai - 1) out, ok_bind]
      dsimp
      have hdig : subDigit ai 0 1 = (ai - 1, 0) := by
        unfold subDigit
        rw [if_pos (by omega : 0 + 1 ≤ ai)]
      rw [hdig]
      exact closeCont i toV 0 (out ++ [ai - 1]) hfits

private theorem magSubStep_scan
    (xs ys : List Nat) (i toV : Nat)
    (hi : i < xs.length) (hiLe : i ≤ toV)
    (hxs : ∀ d ∈ xs, d < limbBase) (hys : ∀ d ∈ ys, d < limbBase)
    (hbr : brAt xs ys i ≤ 1) (hfits : FitsLen (i + 1)) :
    magSubStep (embed xs) (embed ys) (Int.ofNat toV)
        (Int.ofNat i, (Int.ofNat (brAt xs ys i), embed (subPref xs ys i))) =
      (if i = toV then
        .ok (SudoRt.Flow.brk (ρ := Array Int)
          (Int.ofNat i,
            (Int.ofNat (brAt xs ys (i + 1)), embed (subPref xs ys (i + 1)))))
      else
        .ok (SudoRt.Flow.cont (ρ := Array Int)
          (Int.ofNat (i + 1),
            (Int.ofNat (brAt xs ys (i + 1)), embed (subPref xs ys (i + 1)))))) := by
  by_cases hy : i < ys.length
  · have hs := magSub_at xs ys (subPref xs ys i) i toV
      (digAt xs i) (digAt ys i) (brAt xs ys i)
      hi hy (digAt_get xs i hi).symm (digAt_get ys i hy).symm
      (digAt_bound xs i hxs) (digAt_bound ys i hys) hbr hiLe hfits
    simpa [subPref_succ, brAt_succ] using hs
  · have hpast : ys.length ≤ i := Nat.le_of_not_lt hy
    have hs := magSubStep_past xs ys (subPref xs ys i) i toV
      (digAt xs i) (brAt xs ys i) hi hpast (digAt_get xs i hi).symm
      (digAt_bound xs i hxs) hbr hiLe hfits
    have h0 : digAt ys i = 0 := digAt_ge ys i hpast
    simpa [h0, subPref_succ, brAt_succ] using hs

/--
  `mag_sub` of canonical limb strings. `m ≤ n`, so the emitted borrow
  dies and the trimmed digits are `natLimbs (n - m)`.
-/
theorem mag_sub_nat (n m : Nat) (hmn : m ≤ n)
    (hfits : FitsLen (natLimbs n).length) :
    Megadreifach.mag_sub (embed (natLimbs n)) (embed (natLimbs m)) =
      .ok (embed (natLimbs (n - m))) := by
  by_cases hn0 : n = 0
  · have hm0 : m = 0 := Nat.eq_zero_of_le_zero (by simpa [hn0] using hmn)
    simp [hn0, hm0, natLimbs_zero, mag_sub_zeros, Nat.sub_self]
  · have hpos : 0 < (natLimbs n).length := by
      have hne : natLimbs n ≠ [] := by
        intro hempty
        have hv := limbVal_natLimbs n
        rw [hempty] at hv
        simp [limbVal] at hv
        exact hn0 hv.symm
      exact Nat.pos_of_ne_zero (fun h => hne (List.eq_nil_of_length_eq_zero h))
    let xs := natLimbs n
    let ys := natLimbs m
    have hxs : ∀ d ∈ xs, d < limbBase := natLimbs_digits n
    have hys : ∀ d ∈ ys, d < limbBase := natLimbs_digits m
    have hlen : ys.length ≤ xs.length := natLimbs_len_mono m n hmn
    have hle : limbVal ys ≤ limbVal xs := by
      show limbVal (natLimbs m) ≤ limbVal (natLimbs n)
      rw [limbVal_natLimbs, limbVal_natLimbs]
      exact hmn
    have htrim := subPref_trimmed xs ys hxs hys hlen hle
    unfold Megadreifach.mag_sub
    dsimp
    rw [listLen_embed, subI_ofNat_one xs.length hpos hfits, ok_bind]
    dsimp
    rw [except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise
        (step' := magSubStep (embed xs) (embed ys) (Int.ofNat (xs.length - 1)))
      intro σ
      unfold magSubStep
      dsimp
      rfl
    apply chain_loop
      (f := fun i => (Int.ofNat (brAt xs ys i), embed (subPref xs ys i)))
      (fromN := 0) (toN := xs.length - 1)
      (hle := Nat.zero_le _)
      (goal := .ok (embed (natLimbs (n - m))))
    · intro i _ hhi
      have hi : i < xs.length :=
        Nat.lt_of_le_of_lt hhi (Nat.sub_lt hpos (by decide : 0 < 1))
      have hfiti : FitsLen (i + 1) := FitsLen.succ_le hi hfits
      have hbr : brAt xs ys i ≤ 1 :=
        (subScan_inv xs ys hxs hys i (Nat.le_of_lt hi)).1
      exact magSubStep_scan xs ys i (xs.length - 1) hi hhi
        hxs hys hbr hfiti
    · dsimp
      rw [except_bind_pure]
      have hidx : (xs.length - 1) + 1 = xs.length :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
      have hfold :
          subPref xs ys (xs.length - 1) ++
            [(subDigit (digAt xs (xs.length - 1)) (digAt ys (xs.length - 1))
              (brAt xs ys (xs.length - 1))).1] =
            subPref xs ys xs.length := by
        rw [← subPref_succ, hidx]
      rw [hfold]
      have hfitP : FitsLen (subPref xs ys xs.length).length := by
        have hlenP : (subPref xs ys xs.length).length = xs.length :=
          (subScan_inv xs ys hxs hys xs.length (Nat.le_refl _)).2.1
        simpa [hlenP] using hfits
      rw [trim_embed (subPref xs ys xs.length) hfitP]
      rw [htrim, limbVal_natLimbs, limbVal_natLimbs]

end MegaDreifach.Link2
