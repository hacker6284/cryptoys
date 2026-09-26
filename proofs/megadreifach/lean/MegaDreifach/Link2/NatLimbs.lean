/-
  LINK 2. Canonical base-`10^9` limbs of an arbitrary natural number.
  `limbsOfNat` stops at three limbs. `51!` and a 28-byte block need more.
  Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.Bytes

namespace MegaDreifach.Link2
theorem limbBase_gt_one : 1 < limbBase := by decide
def natLimbs : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) % limbBase :: natLimbs ((n + 1) / limbBase)
termination_by n => n
decreasing_by
  simp_wf
  exact Nat.div_lt_self (Nat.succ_pos n) limbBase_gt_one
theorem natLimbs_zero : natLimbs 0 = [] := by simp [natLimbs]
theorem natLimbs_pos (n : Nat) (hn : 0 < n) :
    natLimbs n = n % limbBase :: natLimbs (n / limbBase) := by
  cases n with
  | zero => omega
  | succ _ => simp [natLimbs]
theorem limbVal_natLimbs (n : Nat) : limbVal (natLimbs n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [natLimbs, limbVal]
    | succ n =>
      rw [natLimbs_pos (n + 1) (Nat.succ_pos n), limbVal]
      have hdiv : (n + 1) / limbBase < n + 1 :=
        Nat.div_lt_self (Nat.succ_pos n) limbBase_gt_one
      rw [ih _ hdiv]
      exact Nat.mod_add_div _ _
theorem natLimbs_digits (n : Nat) : ∀ d ∈ natLimbs n, d < limbBase := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => intro d hd; simp [natLimbs] at hd
    | succ n =>
      rw [natLimbs_pos (n + 1) (Nat.succ_pos n)]
      intro d hd
      simp at hd
      cases hd with
      | inl h => subst h; exact Nat.mod_lt _ limbBase_pos
      | inr h =>
        exact ih _ (Nat.div_lt_self (Nat.succ_pos n) limbBase_gt_one) _ h
theorem dropTrail_natLimbs (n : Nat) : dropTrail (natLimbs n) = natLimbs n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp [natLimbs, dropTrail]
    | succ n =>
      have hdiv : (n + 1) / limbBase < n + 1 :=
        Nat.div_lt_self (Nat.succ_pos n) limbBase_gt_one
      rw [natLimbs_pos (n + 1) (Nat.succ_pos n)]
      have ht := ih _ hdiv
      cases htail : natLimbs ((n + 1) / limbBase) with
      | nil =>
        have hnz : (n + 1) % limbBase ≠ 0 := by
          intro hz
          have hsplit := Nat.div_add_mod (n + 1) limbBase
          rw [hz, Nat.add_zero] at hsplit
          have hv := limbVal_natLimbs ((n + 1) / limbBase)
          rw [htail] at hv
          simp [limbVal] at hv
          rw [← hv, Nat.mul_zero] at hsplit
          omega
        simp [dropTrail, htail, hnz]
      | cons b bs =>
        have ht' : dropTrail (b :: bs) = b :: bs := by simpa [htail] using ht
        unfold dropTrail
        rw [ht']

theorem natLimbs_of_pos_lt (n : Nat) (h0 : 0 < n) (hn : n < limbBase) :
    natLimbs n = [n] := by
  rw [natLimbs_pos n h0, Nat.div_eq_of_lt hn, Nat.mod_eq_of_lt hn, natLimbs_zero]

theorem natLimbs_of_lt (n : Nat) (hn : n < limbBase) :
    natLimbs n = if n = 0 then [] else [n] := by
  by_cases h0 : n = 0
  · simp [h0, natLimbs_zero]
  · simp [h0, natLimbs_of_pos_lt n (Nat.pos_of_ne_zero h0) hn]

theorem pow_pos_limb (k : Nat) : 0 < limbBase ^ k := Nat.pow_pos limbBase_pos

theorem limbVal_lt_pow (xs : List Nat) (h : ∀ d ∈ xs, d < limbBase) :
    limbVal xs < limbBase ^ xs.length := by
  induction xs with
  | nil => simp [limbVal]
  | cons x xs ih =>
    have hx : x < limbBase := h x (by simp)
    have hxs := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have hpow : 0 < limbBase ^ xs.length := pow_pos_limb xs.length
    have hle : limbVal xs ≤ limbBase ^ xs.length - 1 := by omega
    have hxle : x ≤ limbBase - 1 := by omega
    have hmul : limbBase * limbVal xs ≤ limbBase * (limbBase ^ xs.length - 1) :=
      Nat.mul_le_mul_left _ hle
    have hsum : x + limbBase * limbVal xs ≤
        (limbBase - 1) + limbBase * (limbBase ^ xs.length - 1) :=
      Nat.add_le_add hxle hmul
    have hconst : (limbBase - 1) + limbBase * (limbBase ^ xs.length - 1) + 1 =
        limbBase * limbBase ^ xs.length := by
      have h1 : (limbBase - 1) + 1 = limbBase := by omega
      calc
        (limbBase - 1) + limbBase * (limbBase ^ xs.length - 1) + 1
          = limbBase + limbBase * (limbBase ^ xs.length - 1) := by omega
        _ = limbBase * 1 + limbBase * (limbBase ^ xs.length - 1) := by rw [Nat.mul_one]
        _ = limbBase * (1 + (limbBase ^ xs.length - 1)) := by rw [← Nat.mul_add]
        _ = limbBase * limbBase ^ xs.length := by
            have : 1 + (limbBase ^ xs.length - 1) = limbBase ^ xs.length := by omega
            rw [this]
    have hlt : x + limbBase * limbVal xs < limbBase * limbBase ^ xs.length := by omega
    simpa [limbVal, List.length_cons, Nat.pow_succ, Nat.mul_comm] using hlt

theorem trimmed_tail (a : Nat) (as : List Nat) (htr : dropTrail (a :: as) = a :: as) :
    dropTrail as = as := by
  cases as with
  | nil => simp [dropTrail]
  | cons b bs =>
    have h := htr
    unfold dropTrail at h
    cases hdt : dropTrail (b :: bs) with
    | nil =>
      rw [hdt] at h
      by_cases ha0 : a = 0
      · simp [ha0] at h
      · simp [ha0] at h
    | cons c cs =>
      rw [hdt] at h
      have hc : c :: cs = b :: bs := by
        simpa using h
      simpa [hc] using hdt.symm

theorem trimmed_eq_natLimbs (xs : List Nat)
    (hdig : ∀ d ∈ xs, d < limbBase) (htr : dropTrail xs = xs) :
    xs = natLimbs (limbVal xs) := by
  induction xs with
  | nil => simp [limbVal, natLimbs]
  | cons a as ih =>
    have ha : a < limbBase := hdig a (by simp)
    have htr' := trimmed_tail a as htr
    have ih' := ih (fun d hd => hdig d (List.mem_cons_of_mem _ hd)) htr'
    have hne : limbVal (a :: as) ≠ 0 := by
      intro hz
      have hmod : (limbVal (a :: as)) % limbBase = 0 := by simp [hz]
      have hma : a = 0 := by
        simpa [limbVal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha] using hmod
      have hdiv : limbVal as = 0 := by
        have hd0 : (limbVal (a :: as)) / limbBase = 0 := by simp [hz]
        simpa [limbVal, Nat.add_mul_div_left _ _ limbBase_pos, Nat.div_eq_of_lt ha] using hd0
      have : as = [] := by simpa [hdiv, natLimbs_zero] using ih'
      subst hma this
      simp [dropTrail] at htr
    rw [natLimbs_pos _ (Nat.pos_of_ne_zero hne)]
    have hmod : limbVal (a :: as) % limbBase = a := by
      simpa [limbVal, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    have hdiv : limbVal (a :: as) / limbBase = limbVal as := by
      simpa [limbVal, Nat.add_mul_div_left _ _ limbBase_pos, Nat.div_eq_of_lt ha]
    rw [hmod, hdiv, ← ih']


def scanMul (q c : Nat) : List Nat → List Nat × Nat
  | [] => ([], c)
  | x :: xs =>
    let cur := x * q + c
    let r := scanMul q (cur / limbBase) xs
    (cur % limbBase :: r.1, r.2)

def scanCarry : Nat → Nat → List Nat → Nat → Nat
  | _, c, _, 0 => c
  | _, c, [], _ => c
  | q, c, x :: xs, j + 1 => scanCarry q ((x * q + c) / limbBase) xs j

theorem scan_step (x q c v B : Nat) :
    (x * q + c) % B + B * (q * v + (x * q + c) / B) = q * (x + B * v) + c := by
  have h := Nat.mod_add_div (x * q + c) B
  calc
    (x * q + c) % B + B * (q * v + (x * q + c) / B)
      = (x * q + c) % B + (B * (q * v) + B * ((x * q + c) / B)) := by rw [Nat.mul_add]
    _ = (x * q + c) % B + (B * ((x * q + c) / B) + B * (q * v)) := by
        rw [Nat.add_comm (B * (q * v))]
    _ = ((x * q + c) % B + B * ((x * q + c) / B)) + B * (q * v) := by rw [← Nat.add_assoc]
    _ = (x * q + c) + B * (q * v) := by rw [h]
    _ = (q * x + c) + B * (q * v) := by rw [Nat.mul_comm x q]
    _ = (q * x + c) + q * (B * v) := by
        rw [show B * (q * v) = q * (B * v) by
          rw [← Nat.mul_assoc, Nat.mul_comm B q, Nat.mul_assoc]]
    _ = (q * x + q * (B * v)) + c := by
        rw [Nat.add_assoc, Nat.add_comm c (q * (B * v)), ← Nat.add_assoc]
    _ = q * (x + B * v) + c := by rw [← Nat.mul_add]

theorem scanMul_length (q c : Nat) : ∀ xs, (scanMul q c xs).1.length = xs.length
  | [] => rfl
  | _ :: xs => by simp [scanMul, scanMul_length]

theorem scanMul_val (q c : Nat) : ∀ xs,
    limbVal ((scanMul q c xs).1 ++ [(scanMul q c xs).2]) = q * limbVal xs + c
  | [] => by simp [scanMul, limbVal]
  | x :: xs => by
    have ih := scanMul_val q ((x * q + c) / limbBase) xs
    unfold scanMul
    rw [List.cons_append, limbVal, ih]
    exact scan_step x q c (limbVal xs) limbBase

theorem mul_carry_lt (x q c : Nat) (hx : x < limbBase) (hq : q < limbBase) (hc : c < limbBase) :
    (x * q + c) / limbBase < limbBase := by
  have hsum : x * q + c ≤ (limbBase - 1) * limbBase := by
    have hx' : x ≤ limbBase - 1 := by omega
    have hq' : q ≤ limbBase - 1 := by omega
    have hc' : c ≤ limbBase - 1 := by omega
    have hmul : x * q ≤ (limbBase - 1) * (limbBase - 1) := Nat.mul_le_mul hx' hq'
    have hpair : (limbBase - 1) * (limbBase - 1) + (limbBase - 1) = (limbBase - 1) * limbBase := by
      calc
        (limbBase - 1) * (limbBase - 1) + (limbBase - 1)
          = (limbBase - 1) * (limbBase - 1) + (limbBase - 1) * 1 := by rw [Nat.mul_one]
        _ = (limbBase - 1) * ((limbBase - 1) + 1) := by rw [← Nat.mul_add]
        _ = (limbBase - 1) * limbBase := by
            have : (limbBase - 1) + 1 = limbBase := by omega
            rw [this]
    omega
  have hlt : x * q + c < limbBase * limbBase := by
    have : (limbBase - 1) * limbBase < limbBase * limbBase := by
      exact Nat.mul_lt_mul_of_pos_right (by omega : limbBase - 1 < limbBase) limbBase_pos
    omega
  exact div_lt_of_lt_mul limbBase_pos hlt

theorem scanMul_bounds (q c : Nat) (hq : q < limbBase) (hc : c < limbBase) :
    ∀ xs, (∀ d ∈ xs, d < limbBase) →
      (∀ d ∈ (scanMul q c xs).1, d < limbBase) ∧ (scanMul q c xs).2 < limbBase
  | [], _ => by simpa [scanMul] using hc
  | x :: xs, hxs => by
    have hx : x < limbBase := hxs x (by simp)
    have hc' := mul_carry_lt x q c hx hq hc
    obtain ⟨hds, hr⟩ := scanMul_bounds q ((x * q + c) / limbBase) hq hc' xs
      (fun d hd => hxs d (List.mem_cons_of_mem _ hd))
    refine ⟨?_, hr⟩
    intro d hd
    simp [scanMul] at hd
    cases hd with
    | inl h => subst h; exact Nat.mod_lt _ limbBase_pos
    | inr h => exact hds _ h

theorem scanMul_prefix (q c : Nat) :
    ∀ (xs : List Nat) (j : Nat), j ≤ xs.length →
      (scanMul q c (xs.take j)).1 = (scanMul q c xs).1.take j ∧
      (scanMul q c (xs.take j)).2 = scanCarry q c xs j
  | _, 0, _ => by simp [List.take_zero, scanMul, scanCarry]
  | [], j + 1, hj => by simp at hj
  | x :: xs, j + 1, hj => by
    simp only [List.take_succ_cons, scanMul, scanCarry]
    have hj' : j ≤ xs.length := by
      rw [List.length_cons] at hj
      omega
    obtain ⟨h1, h2⟩ := scanMul_prefix q ((x * q + c) / limbBase) xs j hj'
    simp [h1, h2]

def divLE (d : Nat) : List Nat → Nat → List Nat × Nat
  | [], rem => ([], rem)
  | x :: xs, rem =>
    let qr := divLE d xs rem
    let cur := qr.2 * limbBase + x
    (cur / d :: qr.1, cur % d)

theorem divLE_length (d rem : Nat) : ∀ xs, (divLE d xs rem).1.length = xs.length
  | [] => rfl
  | _ :: xs => by simp [divLE, divLE_length]

theorem div_step (d r x qv B : Nat) :
    d * ((r * B + x) / d) + (r * B + x) % d + B * (d * qv) = x + B * (d * qv + r) := by
  have h := Nat.div_add_mod (r * B + x) d
  rw [h]
  rw [Nat.add_comm (r * B) x]
  rw [Nat.mul_comm r B]
  -- x + B * r + B * (d * qv) = x + B * (d * qv + r)
  have hpull : x + B * r + B * (d * qv) = x + (B * r + B * (d * qv)) := by
    rw [Nat.add_assoc]
  rw [hpull, ← Nat.mul_add, Nat.add_comm r (d * qv)]


theorem mul_limb_cons (d digit v rmd B : Nat) :
    d * (digit + B * v) + rmd = d * digit + rmd + B * (d * v) := by
  have hmove : d * (B * v) = B * (d * v) := by
    rw [← Nat.mul_assoc, Nat.mul_comm d B, Nat.mul_assoc]
  calc
    d * (digit + B * v) + rmd = d * digit + d * (B * v) + rmd := by rw [Nat.mul_add]
    _ = d * digit + rmd + d * (B * v) := by
        rw [Nat.add_assoc, Nat.add_comm (d * (B * v)) rmd, ← Nat.add_assoc]
    _ = d * digit + rmd + B * (d * v) := by rw [hmove]

theorem divLE_val (d rem : Nat) : ∀ xs,
    d * limbVal (divLE d xs rem).1 + (divLE d xs rem).2 =
      limbVal xs + rem * limbBase ^ xs.length
  | [] => by simp [divLE, limbVal]
  | x :: xs => by
    have ih := divLE_val d rem xs
    unfold divLE
    simp only [limbVal, List.length_cons]
    have hcons := mul_limb_cons d (((divLE d xs rem).2 * limbBase + x) / d)
      (limbVal (divLE d xs rem).1) (((divLE d xs rem).2 * limbBase + x) % d) limbBase
    rw [hcons]
    have hstep := div_step d (divLE d xs rem).2 x (limbVal (divLE d xs rem).1) limbBase
    rw [hstep, ih]
    -- x + B * (Vxs + rem * B^len) = x + B * Vxs + rem * B^(len+1)
    rw [Nat.mul_add, ← Nat.add_assoc]
    have hplace : limbBase * (rem * limbBase ^ xs.length) =
        rem * (limbBase ^ xs.length * limbBase) := by
      rw [← Nat.mul_assoc, Nat.mul_comm limbBase rem, Nat.mul_assoc,
        Nat.mul_comm limbBase (limbBase ^ xs.length)]
    rw [hplace, ← Nat.pow_succ]

theorem divLE_rem_lt (d : Nat) (hd : 0 < d) (rem : Nat) (hrem : rem < d) :
    ∀ xs, (divLE d xs rem).2 < d
  | [] => hrem
  | _ :: xs => by
    unfold divLE
    exact Nat.mod_lt _ hd

theorem divLE_digits (d : Nat) (hd : 0 < d) (rem : Nat) (hrem : rem < d) :
    ∀ xs, (∀ a ∈ xs, a < limbBase) → ∀ q ∈ (divLE d xs rem).1, q < limbBase
  | [], _, _, _ => by simp [divLE] at *
  | x :: xs, hxs, q, hq => by
    have hx : x < limbBase := hxs x (by simp)
    have htail := divLE_digits d hd rem hrem xs (fun a ha => hxs a (List.mem_cons_of_mem _ ha))
    have hrem' := divLE_rem_lt d hd rem hrem xs
    unfold divLE at hq
    simp at hq
    cases hq with
    | inl heq =>
      subst heq
      have hcur : (divLE d xs rem).2 * limbBase + x < d * limbBase := by
        have hremle : (divLE d xs rem).2 ≤ d - 1 := by omega
        have hxle : x ≤ limbBase - 1 := by omega
        have hsum : (divLE d xs rem).2 * limbBase + x ≤ (d - 1) * limbBase + (limbBase - 1) :=
          Nat.add_le_add (Nat.mul_le_mul_right _ hremle) hxle
        have hconst : (d - 1) * limbBase + limbBase = d * limbBase := by
          cases d with
          | zero => omega
          | succ d =>
            rw [Nat.succ_sub_one]
            exact (Nat.succ_mul d limbBase).symm
        omega
      exact div_lt_of_lt_mul hd hcur
    | inr hmem => exact htail q hmem

theorem mul_add_div_mod (d q r n : Nat) (hd : 0 < d) (hr : r < d) (h : d * q + r = n) :
    n / d = q ∧ n % d = r := by
  have hdiv : n / d = (d * q + r) / d := by rw [h]
  have hmod : n % d = (d * q + r) % d := by rw [h]
  rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hr, Nat.add_zero] at hdiv
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr] at hmod
  exact ⟨hdiv, hmod⟩

theorem divLE_quot (d : Nat) (hd : 0 < d) (xs : List Nat) :
    limbVal (divLE d xs 0).1 = limbVal xs / d ∧ (divLE d xs 0).2 = limbVal xs % d := by
  have hsum : d * limbVal (divLE d xs 0).1 + (divLE d xs 0).2 = limbVal xs := by
    simpa [Nat.zero_mul, Nat.add_zero] using divLE_val d 0 xs
  have hr := divLE_rem_lt d hd 0 hd xs
  have h := mul_add_div_mod d _ _ _ hd hr hsum
  exact ⟨h.1.symm, h.2.symm⟩

end MegaDreifach.Link2
