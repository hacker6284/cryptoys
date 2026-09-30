/-
  LINK 2. Small shared helper lemmas (runtime arithmetic on literals, `FitsLen` /
  `limbBase` bounds, factorial facts, loop-flow matches) used by many Link 2
  modules. Each was a `private` copy in several modules; one public lemma here
  keeps the axiom audit's names unique (see proofs/doubledeal/check_axioms.py).
  Proof-only.
-/
import Megadreifach
import MegaDreifachV1.Basic
import MegaDreifachV1.Link2.Bytes
import MegaDreifachV1.Link2.Loop

namespace MegaDreifachV1.Link2

set_option autoImplicit false

/-! ### SudoRt arithmetic on literals (`addI` / `subI` / `divI` / `modI` / `narrowI`, `decide` on `Int` signs) -/

theorem addI_nat_zero (n : Nat) (_h : FitsLen n) :
    SudoRt.addI (Int.ofNat n) (0 : Int) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (n + 0) := by simpa [Nat.add_zero] using _h
  erw [addI_ofNat n 0 h0]
  simp [Nat.add_zero]

theorem addI_one_one : SudoRt.addI (1 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen (1 + 1) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 1 1 h]
  rfl

theorem addI_two_one : SudoRt.addI (2 : Int) (1 : Int) = .ok (3 : Int) := by
  have h : FitsLen (2 + 1) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 2 1 h]
  rfl

theorem addI_zero_nat (n : Nat) (_h : FitsLen n) :
    SudoRt.addI (0 : Int) (Int.ofNat n) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (0 + n) := by simpa [Nat.zero_add] using _h
  erw [addI_ofNat 0 n h0]
  simp [Nat.zero_add]

theorem addI_zero_one : SudoRt.addI (0 : Int) (1 : Int) = .ok (1 : Int) := by
  erw [addI_ofNat 0 1 FitsLen.one]
  simp [Nat.zero_add]

theorem addI_zero_zero : SudoRt.addI (0 : Int) (0 : Int) = .ok (0 : Int) := by
  erw [addI_ofNat 0 0 FitsLen.zero]
  simp

theorem limb_base_eq : Megadreifach.limb_base = (limbBase : Int) := rfl

theorem divI_nat_base (n : Nat) :
    SudoRt.divI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n / limbBase)) := by
  erw [limb_base_eq, divI_ofNat n (Nat.ne_of_gt limbBase_pos)]

theorem modI_nat_base (n : Nat) :
    SudoRt.modI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n % limbBase)) := by
  erw [limb_base_eq, modI_ofNat n (Nat.ne_of_gt limbBase_pos)]

theorem narrowI_neg (k : Nat) (hk : k ≤ limbBase) :
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

theorem decide_neg_lt_zero (k : Nat) (hk : 0 < k) :
    decide (-(k : Int) < 0) = true := by
  rw [decide_eq_true_iff]
  have : (0 : Int) < (k : Int) := (ofNat_pos_iff k).mpr hk
  omega

theorem decide_ofNat_lt_zero (k : Nat) : decide (Int.ofNat k < 0) = false := by
  rw [decide_eq_false_iff_not]
  exact Int.not_lt.mpr (Int.ofNat_zero_le _)

theorem subI_four_one : SudoRt.subI (4 : Int) (1 : Int) = .ok (3 : Int) := by
  have h : FitsLen 4 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 4 1 h (by decide)]
  rfl

theorem subI_one_one : SudoRt.subI (1 : Int) (1 : Int) = .ok (0 : Int) := by
  erw [subI_ofNat_one 1 (by decide) FitsLen.one]
  rfl

theorem subI_three_one : SudoRt.subI (3 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen 3 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 3 1 h (by decide)]
  rfl

theorem subI_two_one : SudoRt.subI (2 : Int) (1 : Int) = .ok (1 : Int) := by
  have h : FitsLen 2 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 2 1 h (by decide)]
  simp

/-! ### `FitsLen` literals and small bounds -/

theorem fits2 : FitsLen 2 := by
  unfold FitsLen i64MaxNat
  decide

theorem fits255 : FitsLen 255 := by
  unfold FitsLen i64MaxNat
  decide

theorem fits27 : FitsLen 27 := by
  unfold FitsLen i64MaxNat
  decide

theorem fits3 : FitsLen 3 := by
  unfold FitsLen i64MaxNat
  decide

theorem fits4 : FitsLen 4 := by
  unfold FitsLen i64MaxNat
  decide

theorem fits51 : FitsLen 51 := by
  unfold FitsLen i64MaxNat
  decide

theorem fits_byte {b : Nat} (hb : b ≤ 255) : FitsLen b :=
  FitsLen.of_le fits255 hb

/-! ### `limbBase` arithmetic (limb bounds, base-`10^9` digits, `256 ^ _`) -/

theorem limb_div_add_mul (q d : Nat) (hq : q < limbBase) :
    (q + limbBase * d) / limbBase = d := by
  have h := Nat.add_mul_div_right q d limbBase_pos
  rw [Nat.mul_comm d limbBase] at h
  rw [h, Nat.div_eq_of_lt hq, Nat.zero_add]

theorem limb_mod_add_mul (q d : Nat) (hq : q < limbBase) :
    (q + limbBase * d) % limbBase = q := by
  rw [Nat.add_comm q (limbBase * d), Nat.mul_add_mod, Nat.mod_eq_of_lt hq]

theorem pow256_mono {a b : Nat} (h : a ≤ b) : 256 ^ a ≤ 256 ^ b :=
  Nat.pow_le_pow_of_le_right (by decide : 256 > 0) h

theorem limb_prod_lt_sq {a b : Nat} (ha : a < limbBase) (hb : b < limbBase) :
    a * b < limbBase ^ 2 := by
  have ha' : a ≤ limbBase - 1 := by
    have : 0 < limbBase := limbBase_pos
    omega
  have hb' : b ≤ limbBase - 1 := by
    have : 0 < limbBase := limbBase_pos
    omega
  have hmul : a * b ≤ (limbBase - 1) * (limbBase - 1) := Nat.mul_le_mul ha' hb'
  have hconst : (limbBase - 1) * (limbBase - 1) < limbBase ^ 2 := by
    unfold limbBase
    decide
  exact Nat.lt_of_le_of_lt hmul hconst

theorem limb_sq_fits : limbBase ^ 2 ≤ i64MaxNat := by
  unfold i64MaxNat limbBase
  decide

theorem limb_prod_fits {a b : Nat} (ha : a < limbBase) (hb : b < limbBase) :
    FitsLen (a * b) := by
  have hsq : a * b < limbBase ^ 2 := limb_prod_lt_sq ha hb
  exact Nat.le_trans (Nat.le_of_lt hsq) limb_sq_fits

theorem c26_lt_limb : 26 < limbBase := by
  unfold limbBase
  decide

theorem c256_lt_limb : 256 < limbBase := by
  unfold limbBase
  decide

theorem limbs2_lt_sq (lo hi : Nat) (hlo : lo < limbBase) (hhi : hi < limbBase) :
    lo + limbBase * hi < limbBase ^ 2 := by
  rw [limbBase_pow2]
  calc
    lo + limbBase * hi < limbBase + limbBase * hi := Nat.add_lt_add_right hlo _
    _ = limbBase * (hi + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ limbBase * limbBase := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hhi)

/-! ### Factorial bounds -/

theorem factorial_pred_mul (i : Nat) (hi : 0 < i) :
    factorial (i - 1) * i = factorial i := by
  cases i with
  | zero => cases hi
  | succ k =>
    have : (k + 1) - 1 = k := by omega
    rw [this, factorial_succ, Nat.mul_comm]

/-- `(n / (f-1)!) / f = n / f!`. -/
theorem div_fact_step (n f : Nat) (hf : 0 < f) :
    (n / factorial (f - 1)) / f = n / factorial f := by
  rw [Nat.div_div_eq_div_mul, factorial_pred_mul f hf]

/-- `12!` fits in one limb. `13!` does not (`6_227_020_800 > 10^9`). -/
theorem factorial_12_lt_limb : factorial 12 < limbBase := by
  unfold factorial limbBase
  decide

theorem factorial_19_lt_sq : factorial 19 < limbBase ^ 2 := by
  unfold factorial limbBase
  decide

theorem factorial_20_ge_sq : limbBase ^ 2 ≤ factorial 20 := by
  unfold factorial limbBase
  decide

theorem factorial_26_lt_cube : factorial 26 < limbBase ^ 3 := by
  unfold factorial limbBase
  decide

theorem factorial_le_succ (b : Nat) : factorial b ≤ factorial (b + 1) := by
  have hmul : factorial b ≤ factorial b * (b + 1) :=
    Nat.le_mul_of_pos_right (factorial b) (Nat.succ_pos b)
  rw [factorial_succ, Nat.mul_comm]
  exact hmul

theorem factorial_mono (a b : Nat) (h : a ≤ b) : factorial a ≤ factorial b := by
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

theorem factorial_lt_cube (n : Nat) (hn : n ≤ 26) : factorial n < limbBase ^ 3 :=
  Nat.lt_of_le_of_lt (factorial_mono n 26 hn) factorial_26_lt_cube

theorem factorial_lt_sq (n : Nat) (hn : n ≤ 19) : factorial n < limbBase ^ 2 :=
  Nat.lt_of_le_of_lt (factorial_mono n 19 hn) factorial_19_lt_sq

/-! ### Loop flow (`match` on an emitted `Flow`, `runLoopOn` with fuel 1 and 2) -/

theorem match_ok_brk {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.brk s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onBrk s := by
  rfl

theorem match_ok_cont {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.cont s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onCont s := by
  rfl

theorem runLoopOn_one {σ ρ α} (s0 : σ)
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

theorem runLoopOn_two {σ ρ α} (s0 : σ)
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

/-! ### Arrays and lists (`fromBE`, `embed`, zero-filled arrays, `push` / `appendL`, `take`) -/

theorem fromBE_nil : fromBE [] = 0 := by
  simp [fromBE, mixEncode]

theorem push_embed (xs : List Nat) (b : Nat) :
    (embed xs).push (Int.ofNat b) = embed (xs ++ [b]) := by
  apply Array.ext'
  simp [embed, toList_push]

theorem append_dig (out : List Nat) (k : Nat) :
    (SudoRt.appendL (embed out) (Int.ofNat k)).1 = embed (out ++ [k]) := by
  rw [appendL_spec]
  exact push_embed out k

theorem embed3_set1 (x y z v : Nat) :
    (embed [x, y, z]).set ⟨1, by simp [size_embed]⟩ (Int.ofNat v) =
      embed [x, v, z] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

theorem embed4_set1 (w x y z v : Nat) :
    (embed [w, x, y, z]).set ⟨1, by simp [size_embed]⟩ (Int.ofNat v) =
      embed [w, v, y, z] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

theorem embed4_set2 (w x y z v : Nat) :
    (embed [w, x, y, z]).set ⟨2, by simp [size_embed]⟩ (Int.ofNat v) =
      embed [w, x, v, z] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

theorem filledL_four :
    SudoRt.filledL (4 : Int) (0 : Int) = .ok (Array.mkArray 4 (0 : Int)) := by
  erw [filledL_ofNat 4 (0 : Int)]

theorem filledL_three :
    SudoRt.filledL (3 : Int) (0 : Int) = .ok (Array.mkArray 3 (0 : Int)) := by
  erw [filledL_ofNat 3 (0 : Int)]

theorem zeros3_size0 : 0 < (Array.mkArray 3 (0 : Int)).size := by
  simp [Array.size_mkArray]

theorem zeros3_set0 (x : Nat) :
    (Array.mkArray 3 (0 : Int)).set ⟨0, zeros3_size0⟩ (Int.ofNat x) =
      embed [x, 0, 0] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate, List.set_cons_zero]

theorem zeros4_size0 : 0 < (Array.mkArray 4 (0 : Int)).size := by
  simp [Array.size_mkArray]

theorem zeros4_set0 (x : Nat) :
    (Array.mkArray 4 (0 : Int)).set ⟨0, zeros4_size0⟩ (Int.ofNat x) =
      embed [x, 0, 0, 0] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate, List.set_cons_zero]

theorem not_mem_take_self (perm : List Nat) (hnd : perm.Nodup) {i : Nat}
    (hi : i < perm.length) : perm[i] ∉ perm.take i := by
  induction perm generalizing i with
  | nil => cases hi
  | cons a as ih =>
    cases i with
    | zero => simp [List.take_zero]
    | succ i =>
      rw [List.nodup_cons] at hnd
      have hi' : i < as.length := Nat.lt_of_succ_lt_succ hi
      intro hmem
      rw [List.take_succ_cons, List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
        exact hnd.1 (heq ▸ List.getElem_mem hi')
      | inr hm =>
        exact ih hnd.2 hi' hm

end MegaDreifachV1.Link2
