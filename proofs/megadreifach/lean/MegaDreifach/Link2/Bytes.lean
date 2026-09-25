/-
  LINK 2. Algebraic byte and limb facts used by the pad bridge.
  Proof-only. Not collision resistance. `hashBlocks` is not `v_Hash`.
-/
import MegaDreifach.Pad
import MegaDreifach.Link2.Embed

namespace MegaDreifach.Link2

def leBytes : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, v => v % 256 :: leBytes n (v / 256)

theorem leBytes_length : ∀ (n v : Nat), (leBytes n v).length = n
  | 0, _ => rfl
  | n + 1, v => by simp [leBytes, leBytes_length n]

theorem pow256_succ (k : Nat) : 256 ^ (k + 1) = 256 * 256 ^ k := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem div_div_pow256 (v k : Nat) : (v / 256) / 256 ^ k = v / 256 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, pow256_succ, Nat.mul_comm]

theorem leBytes_succ_append (n v : Nat) :
    leBytes (n + 1) v = leBytes n v ++ [(v / 256 ^ n) % 256] := by
  induction n generalizing v with
  | zero => simp [leBytes, Nat.pow_zero]
  | succ n ih =>
    rw [leBytes, ih (v / 256), div_div_pow256, leBytes, List.cons_append]

theorem toBE_zero (v : Nat) : toBE 0 v = [] := by
  simp [toBE, mixDecode, List.replicate]

theorem toBE_succ_high (w v : Nat) :
    toBE (w + 1) v = (v / 256 ^ w) :: toBE w (v % 256 ^ w) := by
  simp [toBE, List.replicate_succ, mixDecode, product_replicate_256]

theorem div_lt_of_lt_mul {a b c : Nat} (hb : 0 < b) (h : a < b * c) : a / b < c := by
  rw [Nat.div_lt_iff_lt_mul hb, Nat.mul_comm]
  exact h

theorem div_pos_of_le {a b : Nat} (hb : 0 < b) (h : b ≤ a) : 0 < a / b := by
  have : 1 ≤ a / b := (Nat.le_div_iff_mul_le hb).mpr (by simpa using h)
  exact Nat.lt_of_lt_of_le (by decide : 0 < 1) this

theorem lt_of_div_eq_zero {a b : Nat} (hb : 0 < b) (h : a / b = 0) : a < b := by
  cases Nat.lt_or_ge a b with
  | inl hlt => exact hlt
  | inr hge => exact absurd h (Nat.ne_of_gt (div_pos_of_le hb hge))

theorem pow256_pos (k : Nat) : 0 < 256 ^ k := Nat.pow_pos (by decide)

/-- Big-endian `toBE` is the reversal of low-byte-first extraction, when the
    value fits in `n` bytes. -/
theorem toBE_low_byte (n v : Nat) (hv : v < 256 ^ (n + 1)) :
    toBE (n + 1) v = toBE n (v / 256) ++ [v % 256] := by
  induction n generalizing v with
  | zero =>
    have hv256 : v < 256 := by simpa [pow256_succ, Nat.pow_zero] using hv
    have hdiv : v / 256 = 0 := Nat.div_eq_of_lt hv256
    have hmod : v % 256 = v := Nat.mod_eq_of_lt hv256
    simp [toBE_succ_high, toBE_zero, Nat.pow_zero, hdiv, hmod]
  | succ k ih =>
    have hv' : v < 256 * 256 ^ (k + 1) := by
      simpa [pow256_succ] using hv
    have hqlt : v / 256 < 256 ^ (k + 1) := div_lt_of_lt_mul (by decide) hv'
    let q := v / 256
    let r := v % 256
    have hvq : v = 256 * q + r := (Nat.div_add_mod v 256).symm
    have hr : r < 256 := Nat.mod_lt _ (by decide)
    let qh := q / 256 ^ k
    let ql := q % 256 ^ k
    have hqdecomp : q = 256 ^ k * qh + ql := (Nat.div_add_mod q (256 ^ k)).symm
    have hql : ql < 256 ^ k := Nat.mod_lt _ (pow256_pos k)
    let low := 256 * ql + r
    have hlow : low < 256 ^ (k + 1) := by
      have h1 : 256 * ql + r < 256 * ql + 256 := Nat.add_lt_add_left hr _
      have h2 : 256 * ql + 256 = 256 * (ql + 1) := by rw [Nat.mul_succ]
      have h3 : 256 * (ql + 1) ≤ 256 * 256 ^ k :=
        Nat.mul_le_mul_left 256 (Nat.succ_le_of_lt hql)
      have h4 : 256 * 256 ^ k = 256 ^ (k + 1) := by rw [pow256_succ]
      omega
    have hvsplit : v = low + 256 ^ (k + 1) * qh := by
      have hstep : 256 * (256 ^ k * qh + ql) + r =
          256 ^ (k + 1) * qh + (256 * ql + r) := by
        rw [Nat.mul_add, ← Nat.mul_assoc, ← pow256_succ, ← Nat.add_assoc]
      calc
        v = 256 * q + r := hvq
        _ = 256 * (256 ^ k * qh + ql) + r := by rw [hqdecomp]
        _ = 256 ^ (k + 1) * qh + low := by rw [hstep]
        _ = low + 256 ^ (k + 1) * qh := Nat.add_comm _ _
    have hdivB : v / 256 ^ (k + 1) = qh := by
      rw [hvsplit, Nat.add_mul_div_left low qh (pow256_pos (k + 1)), Nat.div_eq_of_lt hlow]
      simp
    have hmodB : v % 256 ^ (k + 1) = low := by
      rw [hvsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlow]
    have hwdiv : low / 256 = ql := by
      rw [show low = 256 * ql + r from rfl, Nat.mul_add_div (by decide) ql r, Nat.div_eq_of_lt hr]
      simp
    have hwmod : low % 256 = r := by
      rw [show low = 256 * ql + r from rfl, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    have hih := ih low hlow
    rw [toBE_succ_high, hdivB, hmodB, hih, hwdiv, hwmod]
    rw [toBE_succ_high (w := k) (v := q)]
    simp [List.cons_append, qh, ql]

theorem toBE_eq_leRev (n v : Nat) (hv : v < 256 ^ n) :
    toBE n v = (leBytes n v).reverse := by
  induction n generalizing v with
  | zero =>
    simp [toBE_zero, leBytes]
  | succ n ih =>
    have hq : v / 256 < 256 ^ n := by
      have : v < 256 * 256 ^ n := by simpa [pow256_succ] using hv
      exact div_lt_of_lt_mul (by decide) this
    rw [toBE_low_byte n v hv, ih (v / 256) hq, leBytes, List.reverse_cons]

theorem padZ_lt_block (n : Nat) : padZ n < padBlock := by
  unfold padZ
  exact Nat.mod_lt _ (by decide : 0 < padBlock)

theorem ox80_eq : (0x80 : Nat) = 128 := rfl

/-! ## Base-10^9 limbs (emitted `limb_base`). -/

def limbBase : Nat := 1000000000

theorem limbBase_pos : 0 < limbBase := by decide

def limbVal : List Nat → Nat
  | [] => 0
  | a :: as => a + limbBase * limbVal as

/-- Canonical little-endian limbs. Exact for `v < limbBase ^ 3`. -/
def limbsOfNat (v : Nat) : List Nat :=
  if v = 0 then []
  else
    let a0 := v % limbBase
    let q := v / limbBase
    if q = 0 then [a0]
    else
      let a1 := q % limbBase
      let q2 := q / limbBase
      if q2 = 0 then [a0, a1]
      else [a0, a1, q2]

/-- Drop high zero limbs. -/
def dropTrail : List Nat → List Nat
  | [] => []
  | a :: as =>
    match dropTrail as with
    | [] => if a = 0 then [] else [a]
    | bs => a :: bs

theorem limbVal_dropTrail : ∀ xs, limbVal (dropTrail xs) = limbVal xs
  | [] => rfl
  | a :: as => by
    have ih := limbVal_dropTrail as
    cases h : dropTrail as with
    | nil =>
      rw [h] at ih
      have ih' : limbVal as = 0 := by simpa [limbVal] using ih.symm
      by_cases ha : a = 0
      · simp [dropTrail, h, ha, limbVal, ih']
      · simp [dropTrail, h, ha, limbVal, ih']
    | cons b bs =>
      rw [h] at ih
      simp [limbVal] at ih
      simp [dropTrail, h, limbVal, ih]

theorem dropTrail_prefix : ∀ xs, xs.take (dropTrail xs).length = dropTrail xs
  | [] => rfl
  | a :: as => by
    have ih := dropTrail_prefix as
    cases h : dropTrail as with
    | nil =>
      by_cases ha : a = 0 <;> simp [dropTrail, h, ha]
    | cons b bs =>
      rw [h] at ih
      simpa [dropTrail, h, List.length_cons, List.take_succ_cons] using ih

/-- Long division of little-endian limbs by 256. High limb first. -/
def divAll : List Nat → List Nat × Nat
  | [] => ([], 0)
  | x :: xs =>
    let qr := divAll xs
    let cur := qr.2 * limbBase + x
    (cur / 256 :: qr.1, cur % 256)

theorem quotDigit_lt (rh x : Nat) (hr : rh < 256) (hx : x < limbBase) :
    (rh * limbBase + x) / 256 < limbBase := by
  have hrh : rh ≤ 255 := Nat.lt_succ_iff.mp hr
  have hcur : rh * limbBase + x < 256 * limbBase := by
    calc
      rh * limbBase + x ≤ 255 * limbBase + x :=
        Nat.add_le_add_right (Nat.mul_le_mul_right _ hrh) _
      _ < 255 * limbBase + limbBase := Nat.add_lt_add_left hx _
      _ = 256 * limbBase := by
        rw [← Nat.succ_mul]
  exact div_lt_of_lt_mul (by decide) hcur

theorem divAll_spec (xs : List Nat) (h : ∀ d ∈ xs, d < limbBase) :
    limbVal (divAll xs).1 * 256 + (divAll xs).2 = limbVal xs ∧
      (divAll xs).2 < 256 ∧
      (∀ d ∈ (divAll xs).1, d < limbBase) ∧
      (divAll xs).1.length = xs.length := by
  induction xs with
  | nil => simp [divAll, limbVal]
  | cons x xs ih =>
    have hx : x < limbBase := h x (by simp)
    obtain ⟨hval, hr, hdig, hlen⟩ := ih (fun d hd => h d (List.mem_cons_of_mem x hd))
    simp only [divAll, limbVal]
    let qh := (divAll xs).1
    let rh := (divAll xs).2
    have hq0 := quotDigit_lt rh x hr hx
    have hr0 : (rh * limbBase + x) % 256 < 256 := Nat.mod_lt _ (by decide)
    have hcur : 256 * ((rh * limbBase + x) / 256) + (rh * limbBase + x) % 256 =
        rh * limbBase + x := Nat.div_add_mod _ 256
    refine ⟨?_, hr0, ?_, ?_⟩
    · have hih : limbVal qh * 256 + rh = limbVal xs := hval
      let q0 := (rh * limbBase + x) / 256
      let r0 := (rh * limbBase + x) % 256
      have hcur' : 256 * q0 + r0 = rh * limbBase + x := hcur
      have hmove : 256 * q0 + ((limbBase * limbVal qh) * 256 + r0) =
          256 * q0 + r0 + (limbBase * limbVal qh) * 256 := by
        rw [Nat.add_comm ((limbBase * limbVal qh) * 256) r0, ← Nat.add_assoc]
      have hmul : (limbBase * limbVal qh) * 256 = limbBase * (limbVal qh * 256) := by
        rw [Nat.mul_assoc, Nat.mul_comm (limbVal qh) 256]
      calc
        (q0 + limbBase * limbVal qh) * 256 + r0
          = q0 * 256 + (limbBase * limbVal qh) * 256 + r0 := by rw [Nat.add_mul]
        _ = 256 * q0 + ((limbBase * limbVal qh) * 256 + r0) := by
            rw [Nat.mul_comm q0 256, Nat.add_assoc]
        _ = 256 * q0 + r0 + limbBase * (limbVal qh * 256) := by rw [hmove, hmul]
        _ = rh * limbBase + x + limbBase * (limbVal qh * 256) := by rw [hcur']
        _ = x + (rh * limbBase + limbBase * (limbVal qh * 256)) := by
            rw [Nat.add_comm (rh * limbBase) x, ← Nat.add_assoc]
        _ = x + limbBase * (rh + limbVal qh * 256) := by
            rw [Nat.mul_comm rh limbBase, ← Nat.mul_add, Nat.mul_comm (limbVal qh) 256]
        _ = x + limbBase * limbVal xs := by rw [Nat.add_comm rh, hih]
    · intro d hd
      simp [List.mem_cons] at hd
      cases hd with
      | inl heq =>
        subst heq
        exact hq0
      | inr hmem =>
        exact hdig d hmem
    · simp [hlen]

theorem limbBase_pow3 : limbBase ^ 3 = limbBase * limbBase ^ 2 := by
  rw [Nat.pow_succ, Nat.mul_comm]

theorem limbBase_pow2 : limbBase ^ 2 = limbBase * limbBase := by
  rw [Nat.pow_succ, Nat.pow_one, Nat.mul_comm]

theorem limbsOfNat_val (v : Nat) (hv : v < limbBase ^ 3) : limbVal (limbsOfNat v) = v := by
  unfold limbsOfNat
  by_cases h0 : v = 0
  · simp [h0, limbVal]
  · have hqlt : v / limbBase < limbBase ^ 2 := by
      rw [limbBase_pow3] at hv
      exact div_lt_of_lt_mul limbBase_pos hv
    simp only [h0, ↓reduceIte]
    by_cases hq : v / limbBase = 0
    · have hlt : v < limbBase := lt_of_div_eq_zero limbBase_pos hq
      simp [hq, limbVal, Nat.mod_eq_of_lt hlt]
    · simp only [hq, ↓reduceIte]
      by_cases hq2 : (v / limbBase) / limbBase = 0
      · have hql : v / limbBase < limbBase := lt_of_div_eq_zero limbBase_pos hq2
        simp [hq2, limbVal, Nat.mod_eq_of_lt hql]
        exact Nat.mod_add_div v limbBase
      · have hq2lt : (v / limbBase) / limbBase < limbBase := by
          rw [limbBase_pow2] at hqlt
          exact div_lt_of_lt_mul limbBase_pos hqlt
        simp only [hq2, ↓reduceIte, limbVal]
        have hmid : v / limbBase =
            (v / limbBase) % limbBase + limbBase * ((v / limbBase) / limbBase) :=
          (Nat.mod_add_div (v / limbBase) limbBase).symm
        calc
          v % limbBase + limbBase * ((v / limbBase) % limbBase +
              limbBase * ((v / limbBase) / limbBase))
            = v % limbBase + limbBase * (v / limbBase) := by rw [← hmid]
          _ = v := Nat.mod_add_div v limbBase

theorem limbsOfNat_trimmed (v : Nat) (_hv : v < limbBase ^ 3) :
    dropTrail (limbsOfNat v) = limbsOfNat v := by
  unfold limbsOfNat
  by_cases h0 : v = 0
  · simp [h0, dropTrail]
  · have hvpos : 0 < v := Nat.pos_of_ne_zero h0
    simp only [h0, ↓reduceIte]
    by_cases hq : v / limbBase = 0
    · have hlt : v < limbBase := lt_of_div_eq_zero limbBase_pos hq
      have ha : v % limbBase ≠ 0 := by
        rw [Nat.mod_eq_of_lt hlt]
        exact h0
      simp [hq, dropTrail, ha]
    · simp only [hq, ↓reduceIte]
      by_cases hq2 : (v / limbBase) / limbBase = 0
      · have ha1 : (v / limbBase) % limbBase ≠ 0 := by
          have hql : v / limbBase < limbBase := lt_of_div_eq_zero limbBase_pos hq2
          rw [Nat.mod_eq_of_lt hql]
          exact hq
        simp [hq2, dropTrail, ha1]
      · have ha2 : (v / limbBase) / limbBase ≠ 0 := hq2
        simp [hq2, dropTrail, ha2]

theorem dropTrail_zero_tail : ∀ xs, (dropTrail (xs ++ [0])).length ≤ xs.length
  | [] => by simp [dropTrail]
  | a :: as => by
    have ih := dropTrail_zero_tail as
    cases h : dropTrail (as ++ [0]) with
    | nil =>
      simp [dropTrail, h]
      by_cases ha : a = 0
      · simp [ha]
      · simp [ha]
    | cons b bs =>
      have hlen : (b :: bs).length ≤ as.length := by simpa [h] using ih
      have hd : dropTrail ((a :: as) ++ [0]) = a :: b :: bs := by
        simp [dropTrail, h]
      rw [hd]
      exact Nat.succ_le_succ hlen

theorem dropTrail_eq_self_of_high {a b c : Nat} (hc : c ≠ 0) :
    dropTrail [a, b, c] = [a, b, c] := by
  simp [dropTrail, hc]

theorem trimmed_eq_limbsOfNat (xs : List Nat)
    (htrim : dropTrail xs = xs) (hdig : ∀ d ∈ xs, d < limbBase)
    (hv : limbVal xs < limbBase ^ 3) (hlen : xs.length ≤ 3) :
    xs = limbsOfNat (limbVal xs) := by
  match xs with
  | [] => simp [limbVal, limbsOfNat]
  | [a] =>
    have ha : a < limbBase := hdig a (by simp)
    have hpos : a ≠ 0 := by
      intro ha
      simp [dropTrail, ha] at htrim
    have hv' : limbVal [a] = a := by simp [limbVal]
    simp [limbsOfNat, hv', hpos, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]
  | [a, b] =>
    have ha : a < limbBase := hdig a (by simp)
    have hb : b < limbBase := hdig b (by simp)
    have hb0 : b ≠ 0 := by
      intro hbz
      subst hbz
      have hle := dropTrail_zero_tail [a]
      have heq := congrArg List.length htrim
      simp at hle heq
      omega
    have hv' : limbVal [a, b] = a + limbBase * b := by simp [limbVal]
    have hdiv : (a + limbBase * b) / limbBase = b := by
      rw [Nat.add_mul_div_left a b limbBase_pos, Nat.div_eq_of_lt ha]
      simp
    have hmod : (a + limbBase * b) % limbBase = a := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    have hq2 : b / limbBase = 0 := Nat.div_eq_of_lt hb
    have hnot : ¬ (a = 0 ∧ limbBase * b = 0) := by
      intro ⟨_, hz⟩
      exact hb0 ((Nat.mul_eq_zero.mp hz).resolve_left (Nat.ne_of_gt limbBase_pos))
    simp [limbsOfNat, hv', hdiv, hmod, hq2, hb0, hnot, Nat.mod_eq_of_lt hb]
  | [a, b, c] =>
    have ha : a < limbBase := hdig a (by simp)
    have hb : b < limbBase := hdig b (by simp)
    have hc : c < limbBase := hdig c (by simp)
    have hc0 : c ≠ 0 := by
      intro hz
      subst hz
      have hle := dropTrail_zero_tail [a, b]
      have heq := congrArg List.length htrim
      simp at hle heq
      omega
    have hv' : limbVal [a, b, c] = a + limbBase * (b + limbBase * c) := by simp [limbVal]
    have hinner : (b + limbBase * c) / limbBase = c := by
      rw [Nat.add_mul_div_left b c limbBase_pos, Nat.div_eq_of_lt hb]
      simp
    have hdiv1 : (a + limbBase * (b + limbBase * c)) / limbBase = b + limbBase * c := by
      rw [Nat.add_mul_div_left a (b + limbBase * c) limbBase_pos, Nat.div_eq_of_lt ha]
      simp
    have hmod1 : (a + limbBase * (b + limbBase * c)) % limbBase = a := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    have hmod2 : (b + limbBase * c) % limbBase = b := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]
    have hq : (a + limbBase * (b + limbBase * c)) / limbBase ≠ 0 := by
      rw [hdiv1]
      exact Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le b) (Nat.lt_add_of_pos_right
        (Nat.mul_pos limbBase_pos (Nat.pos_of_ne_zero hc0))))
    have hnot : ¬ (a = 0 ∧ limbBase * (b + limbBase * c) = 0) := by
      intro ⟨_, hz⟩
      have hsum : b + limbBase * c = 0 :=
        (Nat.mul_eq_zero.mp hz).resolve_left (Nat.ne_of_gt limbBase_pos)
      exact hc0 ((Nat.mul_eq_zero.mp (Nat.add_eq_zero_iff.mp hsum).2).resolve_left
        (Nat.ne_of_gt limbBase_pos))
    have hnot2 : ¬ (b = 0 ∧ limbBase * c = 0) := by
      intro ⟨_, hz⟩
      exact hc0 ((Nat.mul_eq_zero.mp hz).resolve_left (Nat.ne_of_gt limbBase_pos))
    simp [limbsOfNat, hv', hdiv1, hmod1, hinner, hmod2, hq, hc0, hnot, hnot2,
      Nat.mod_eq_of_lt hc]
  | a :: b :: c :: d :: rest =>
    simp at hlen

theorem i64Max_lt_be : i64MaxNat < 256 ^ 8 := by
  decide

theorem i64Max_lt_limb3 : i64MaxNat < limbBase ^ 3 := by
  decide

theorem fitsLen_lt_be {n : Nat} (h : FitsLen n) : n < 256 ^ 8 :=
  Nat.lt_of_le_of_lt h i64Max_lt_be

theorem fitsLen_lt_limb3 {n : Nat} (h : FitsLen n) : n < limbBase ^ 3 :=
  Nat.lt_of_le_of_lt h i64Max_lt_limb3

theorem bitlen_lt_be {n : Nat} (h : FitsBitlen n) : 8 * n < 256 ^ 8 :=
  Nat.lt_of_le_of_lt h i64Max_lt_be

end MegaDreifach.Link2
