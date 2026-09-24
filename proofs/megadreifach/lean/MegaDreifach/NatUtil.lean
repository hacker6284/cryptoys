/-
  Mixed-radix encoding and list helpers. Used by factoradic (M4),
  digest rank (M3), and SHA-2-style pad (M5). Zero sorry. No native_decide.
-/
import MegaDreifach.Basic

namespace MegaDreifach

def product : List Nat → Nat
  | [] => 1
  | x :: xs => x * product xs

@[simp] theorem product_nil : product [] = 1 := rfl
@[simp] theorem product_cons (x : Nat) (xs : List Nat) :
    product (x :: xs) = x * product xs := rfl

theorem product_pos (rs : List Nat) (h : ∀ r ∈ rs, 0 < r) : 0 < product rs := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
      have hr : 0 < r := h r (List.mem_cons_self r rs)
      have hrs : ∀ x ∈ rs, 0 < x := fun x hx => h x (List.mem_cons_of_mem r hx)
      exact Nat.mul_pos hr (ih hrs)

def sumNats : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNats xs

@[simp] theorem sumNats_nil : sumNats [] = 0 := rfl
@[simp] theorem sumNats_cons (x : Nat) (xs : List Nat) :
    sumNats (x :: xs) = x + sumNats xs := rfl

theorem sumNats_append (xs ys : List Nat) :
    sumNats (xs ++ ys) = sumNats xs + sumNats ys := by
  induction xs with
  | nil => simp [sumNats]
  | cons x xs ih => simp [sumNats, ih, Nat.add_assoc]

theorem sumNats_replicate_zero (n : Nat) : sumNats (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp [sumNats]
  | succ n ih => simp [List.replicate_succ, sumNats, ih]

/-- Mixed-radix encode, most-significant digit first. -/
def mixEncode (rs ds : List Nat) : Nat :=
  match rs, ds with
  | _r :: rs, d :: ds => d * product rs + mixEncode rs ds
  | _, _ => 0

/-- Mixed-radix decode, most-significant digit first. -/
def mixDecode (rs : List Nat) (val : Nat) : List Nat :=
  match rs with
  | [] => []
  | _r :: rs => (val / product rs) :: mixDecode rs (val % product rs)

@[simp] theorem mixDecode_nil (val : Nat) : mixDecode [] val = [] := rfl

theorem mixEncode_nil_rs (ds : List Nat) : mixEncode [] ds = 0 := by
  simp [mixEncode]

theorem mixEncode_nil_ds (rs : List Nat) : mixEncode rs [] = 0 := by
  cases rs <;> simp [mixEncode]

theorem mixDecode_length (rs : List Nat) (val : Nat) :
    (mixDecode rs val).length = rs.length := by
  induction rs generalizing val with
  | nil => simp
  | cons _r rs ih => simp [mixDecode, ih]

theorem mixEncode_cons (r : Nat) (rs : List Nat) (d : Nat) (ds : List Nat) :
    mixEncode (r :: rs) (d :: ds) = d * product rs + mixEncode rs ds := rfl

/-- `d * w + rem < r * w` when `rem < w` and `d < r`. -/
theorem mul_add_lt_mul (d rem r w : Nat) (hd : d < r) (hr : rem < w) :
    d * w + rem < r * w := by
  have h1 : d * w + rem < d * w + w := Nat.add_lt_add_left hr _
  have h2 : d * w + w = (d + 1) * w := by rw [Nat.succ_mul]
  have h3 : (d + 1) * w ≤ r * w := Nat.mul_le_mul_right w (Nat.succ_le_of_lt hd)
  exact Nat.lt_of_lt_of_le (h2 ▸ h1) h3

theorem mixEncode_lt (rs ds : List Nat)
    (hlen : ds.length = rs.length)
    (hbound : ∀ i, i < ds.length → ds[i]?.getD 0 < rs[i]?.getD 0) :
    mixEncode rs ds < product rs := by
  induction rs generalizing ds with
  | nil =>
      cases ds <;> simp [mixEncode, product]
  | cons r rs ih =>
      match ds with
      | [] => simp at hlen
      | d :: ds =>
          have hlen' : ds.length = rs.length := by
            simp at hlen; exact hlen
          have hbound' : ∀ i, i < ds.length → ds[i]?.getD 0 < rs[i]?.getD 0 := by
            intro i hi
            have := hbound (i + 1) (Nat.succ_lt_succ hi)
            simpa [List.getElem?_cons_succ] using this
          have hd : d < r := by
            have := hbound 0 (Nat.zero_lt_succ ds.length)
            simpa [List.getElem?_cons_zero] using this
          have ih' : mixEncode rs ds < product rs := ih ds hlen' hbound'
          simpa [mixEncode_cons, product_cons] using mul_add_lt_mul d (mixEncode rs ds) r (product rs) hd ih'

theorem mixDecode_encode (rs ds : List Nat)
    (hlen : ds.length = rs.length)
    (hbound : ∀ i, i < ds.length → ds[i]?.getD 0 < rs[i]?.getD 0) :
    mixDecode rs (mixEncode rs ds) = ds := by
  induction rs generalizing ds with
  | nil =>
      cases ds with
      | nil => rfl
      | cons _ _ => simp at hlen
  | cons r rs ih =>
      match ds with
      | [] => simp at hlen
      | d :: ds =>
          have hlen' : ds.length = rs.length := by simp at hlen; exact hlen
          have hbound' : ∀ i, i < ds.length → ds[i]?.getD 0 < rs[i]?.getD 0 := by
            intro i hi
            have := hbound (i + 1) (Nat.succ_lt_succ hi)
            simpa [List.getElem?_cons_succ] using this
          have hd : d < r := by
            have := hbound 0 (Nat.zero_lt_succ ds.length)
            simpa [List.getElem?_cons_zero] using this
          have ih' := ih ds hlen' hbound'
          have ihlt := mixEncode_lt rs ds hlen' hbound'
          have hw : 0 < product rs := by
            cases Nat.eq_zero_or_pos (product rs) with
            | inl hz =>
                rw [hz] at ihlt
                exact (Nat.not_lt_zero _ ihlt).elim
            | inr h => exact h
          have hdiv : (d * product rs + mixEncode rs ds) / product rs = d := by
            rw [Nat.add_comm, Nat.add_mul_div_right (mixEncode rs ds) d hw]
            have : mixEncode rs ds / product rs = 0 := Nat.div_eq_of_lt ihlt
            simp [this]
          have hmod : (d * product rs + mixEncode rs ds) % product rs =
              mixEncode rs ds := by
            rw [Nat.add_comm, Nat.add_mul_mod_self_right]
            exact Nat.mod_eq_of_lt ihlt
          simp [mixEncode_cons, mixDecode, hdiv, hmod, ih']

theorem mixDecode_bound (rs : List Nat) (val : Nat)
    (hval : val < product rs) (hpos : ∀ r ∈ rs, 0 < r) :
    ∀ i, i < (mixDecode rs val).length →
      (mixDecode rs val)[i]?.getD 0 < rs[i]?.getD 0 := by
  induction rs generalizing val with
  | nil =>
      intro i hi; simp [mixDecode] at hi
  | cons r rs ih =>
      intro i hi
      have hw : 0 < product rs := product_pos rs (fun x hx => hpos x (List.mem_cons_of_mem r hx))
      have hdiv : val / product rs < r :=
        Nat.div_lt_of_lt_mul (by simpa [product_cons, Nat.mul_comm] using hval)
      cases i with
      | zero =>
          simpa [mixDecode, List.getElem?_cons_zero] using hdiv
      | succ i =>
          have hlen : (mixDecode (r :: rs) val).length =
              (mixDecode rs (val % product rs)).length + 1 := by
            simp [mixDecode]
          have hi' : i < (mixDecode rs (val % product rs)).length := by
            simp [mixDecode] at hi
            exact hi
          have hval' : val % product rs < product rs := Nat.mod_lt _ hw
          have ih' := ih (val % product rs) hval'
            (fun x hx => hpos x (List.mem_cons_of_mem r hx)) i hi'
          simpa [mixDecode, List.getElem?_cons_succ] using ih'

theorem mixEncode_decode (rs : List Nat) (val : Nat)
    (hval : val < product rs) (hpos : ∀ r ∈ rs, 0 < r) :
    mixEncode rs (mixDecode rs val) = val := by
  induction rs generalizing val with
  | nil =>
      simp [mixEncode, mixDecode, product] at hval ⊢
      exact hval.symm
  | cons r rs ih =>
      have hw : 0 < product rs := product_pos rs (fun x hx => hpos x (List.mem_cons_of_mem r hx))
      have hval' : val % product rs < product rs := Nat.mod_lt _ hw
      have ih' := ih (val % product rs) hval' (fun x hx => hpos x (List.mem_cons_of_mem r hx))
      simp [mixDecode, mixEncode]
      rw [ih']
      have h := Nat.div_add_mod val (product rs)
      rw [Nat.mul_comm] at h
      exact h

/-- Mixed-radix encode is injective on in-range digit lists of matching length. -/
theorem mixEncode_inj (rs ds1 ds2 : List Nat)
    (h1 : ds1.length = rs.length) (h2 : ds2.length = rs.length)
    (b1 : ∀ i, i < ds1.length → ds1[i]?.getD 0 < rs[i]?.getD 0)
    (b2 : ∀ i, i < ds2.length → ds2[i]?.getD 0 < rs[i]?.getD 0)
    (heq : mixEncode rs ds1 = mixEncode rs ds2) : ds1 = ds2 := by
  have e1 := mixDecode_encode rs ds1 h1 b1
  have e2 := mixDecode_encode rs ds2 h2 b2
  calc
    ds1 = mixDecode rs (mixEncode rs ds1) := e1.symm
    _ = mixDecode rs (mixEncode rs ds2) := by rw [heq]
    _ = ds2 := e2

/-- `n, n-1, …, 1`. Product is `n!`. -/
def descending : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: descending n

@[simp] theorem descending_zero : descending 0 = [] := rfl
@[simp] theorem descending_succ (n : Nat) : descending (n + 1) = (n + 1) :: descending n := rfl

theorem descending_length (n : Nat) : (descending n).length = n := by
  induction n <;> simp [descending, *]

theorem mem_descending {n r : Nat} (h : r ∈ descending n) : 0 < r := by
  induction n with
  | zero => simp [descending] at h
  | succ n ih =>
      simp [descending] at h
      cases h with
      | inl h => subst h; exact Nat.succ_pos n
      | inr h => exact ih h

theorem product_descending (n : Nat) : product (descending n) = factorial n := by
  induction n with
  | zero => simp [descending, factorial]
  | succ n ih => simp [descending, factorial, ih]

/-- Radices `n, n-1, …, 3` for even-permutation prefixes (`n ≥ 2`). -/
def evenRadices : Nat → List Nat
  | 0 => []
  | 1 => []
  | n + 2 => (descending (n + 2)).take n

theorem evenRadices_length (n : Nat) (hn : 2 ≤ n) :
    (evenRadices n).length = n - 2 := by
  match n with
  | 0 => omega
  | 1 => omega
  | n + 2 =>
      simp [evenRadices, descending_length]
      omega

theorem product_replicate (r k : Nat) : product (List.replicate k r) = r ^ k := by
  induction k with
  | zero => simp [product]
  | succ k ih =>
      simp [List.replicate_succ, product, ih]
      rw [Nat.pow_succ, Nat.mul_comm]

def getD (xs : List Nat) (i : Nat) : Nat := xs[i]?.getD 0

theorem getD_cons_zero (x : Nat) (xs : List Nat) : getD (x :: xs) 0 = x := by
  simp [getD]

theorem getD_cons_succ (x : Nat) (xs : List Nat) (i : Nat) :
    getD (x :: xs) (i + 1) = getD xs i := by
  simp [getD]

end MegaDreifach
