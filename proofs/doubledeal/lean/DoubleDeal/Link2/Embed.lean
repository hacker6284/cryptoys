/-
  LINK 2 bridge types. Proof-only.

  Interprets Generated `Array Int` values into the algebraic `List Nat`
  model (and back). Does not edit Generated sources. Does not claim
  emitter soundness, bit-security, MDS, collision-resistance, or AEAD
  security. Link 1 (sudo → Generated via emit) stays trusted-not-proved.

  Well-formedness for PassKey: a list of Nats whose length fits in i64
  so emitted index arithmetic (`addI` / `subI` on seats) cannot Overflow.
  Card *values* need not be `< 52` — algebraic PassKey is List Nat, not
  the Fin packet. Encrypt (NEXT) will add length-52 / Perm52.
-/
import SudoRt

namespace DoubleDeal.Link2

/-- i64 upper bound as a Nat. Equals `SudoRt.i64Max.toNat`. -/
def i64MaxNat : Nat := 9223372036854775807

theorem i64MaxNat_spec : Int.ofNat i64MaxNat = SudoRt.i64Max := rfl

/-- Lengths that fit in a sudo i64, so `listLen` used in `addI`/`subI` cannot Overflow. -/
def FitsLen (n : Nat) : Prop := n ≤ i64MaxNat

theorem FitsLen.zero : FitsLen 0 := Nat.zero_le _

theorem FitsLen.one : FitsLen 1 := by
  unfold FitsLen i64MaxNat
  decide

theorem FitsLen.succ_of_succ {n : Nat} (h : FitsLen (n + 1)) : FitsLen n :=
  Nat.le_trans (Nat.le_succ n) h

theorem FitsLen.of_le {m n : Nat} (hm : FitsLen n) (hle : m ≤ n) : FitsLen m :=
  Nat.le_trans hle hm

theorem ofNat_le_i64Max {n : Nat} (h : FitsLen n) : Int.ofNat n ≤ SudoRt.i64Max := by
  rw [← i64MaxNat_spec]
  exact Int.ofNat_le.mpr h

/-- Algebraic deck → emitted list. Inverse of `decode` on the image. -/
def embed (xs : List Nat) : Array Int := Array.mk (xs.map Int.ofNat)

/-- Emitted list → algebraic deck. Faithful iff every cell is nonnegative. -/
def decode (a : Array Int) : List Nat := a.toList.map Int.toNat

def Nonneg (a : Array Int) : Prop :=
  ∀ i : Nat, (h : i < a.size) → 0 ≤ a[i]

/-- Well-formed generated deck for PassKey: embed-image, i64-safe length. -/
structure WellFormed (a : Array Int) : Prop where
  fits : FitsLen a.size
  nonneg : Nonneg a

theorem toList_embed (xs : List Nat) : (embed xs).toList = xs.map Int.ofNat := rfl

theorem size_embed (xs : List Nat) : (embed xs).size = xs.length := by
  simp [embed]

theorem get_embed (xs : List Nat) (i : Nat) (h : i < (embed xs).size) :
    (embed xs)[i] = Int.ofNat (xs[i]'(by rw [size_embed] at h; exact h)) := by
  have hi : i < xs.length := by rw [size_embed] at h; exact h
  simp [embed]

theorem nonneg_embed (xs : List Nat) : Nonneg (embed xs) := by
  intro i h
  rw [get_embed]
  exact Int.ofNat_zero_le _

theorem wellFormed_embed (xs : List Nat) (h : FitsLen xs.length) : WellFormed (embed xs) :=
  ⟨by rw [size_embed]; exact h, nonneg_embed xs⟩

private theorem toNat_ofNat_id : ∀ xs : List Nat, (xs.map Int.ofNat).map Int.toNat = xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons]
    exact congrArg (List.cons x) (toNat_ofNat_id xs)

theorem decode_embed (xs : List Nat) : decode (embed xs) = xs :=
  toNat_ofNat_id xs

private theorem map_ofNat_toNat_eq :
    ∀ {xs : List Int}, (∀ i : Nat, (hi : i < xs.length) → 0 ≤ xs[i]) →
      (xs.map Int.toNat).map Int.ofNat = xs
  | [], _ => rfl
  | x :: xs, h => by
    have hx : 0 ≤ x := h 0 (by simp)
    have hxs : ∀ i : Nat, (hi : i < xs.length) → 0 ≤ xs[i] := by
      intro i hi
      exact h (i + 1) (by simp [hi])
    have hx' : Int.ofNat x.toNat = x := Int.toNat_of_nonneg hx
    simp only [List.map_cons, hx', map_ofNat_toNat_eq hxs]

theorem embed_decode (a : Array Int) (hn : Nonneg a) : embed (decode a) = a := by
  apply Array.ext'
  change (a.toList.map Int.toNat).map Int.ofNat = a.toList
  refine map_ofNat_toNat_eq ?_
  intro i hi
  exact hn i hi

theorem embed_nil : embed [] = #[] := rfl

theorem toList_embed_cons (c : Nat) (rest : List Nat) :
    (embed (c :: rest)).toList = Int.ofNat c :: (embed rest).toList := rfl

theorem embed_inj {xs ys : List Nat} (h : embed xs = embed ys) : xs = ys := by
  have := congrArg decode h
  simpa [decode_embed] using this

end DoubleDeal.Link2
