/-
  LINK 2 bridge types for MegaDreifach. Proof-only.

  Interprets Generated `Array Int` into the algebraic `List Nat` model.
  Does not edit Generated sources. Does not claim emitter soundness,
  collision resistance, ideal-cipher-on-G, or bit-security.
  Link 1 (sudo → Generated via emit) stays trusted-not-proved.

  Pad domain: each byte is `≤ 255` (the emitted `pad_message` asserts
  that) and `8 * length` fits in an i64 (so `mulI` / `big_from_int`
  do not Overflow). Algebraic `pad` does not check bytes; the assert
  is why the refinement domain carries `Byte`.
-/
import SudoRt

namespace MegaDreifach.Link2

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

theorem FitsLen.succ_le {i n : Nat} (hi : i < n) (hn : FitsLen n) : FitsLen (i + 1) :=
  FitsLen.of_le hn (Nat.succ_le_of_lt hi)

theorem ofNat_le_i64Max {n : Nat} (h : FitsLen n) : Int.ofNat n ≤ SudoRt.i64Max := by
  rw [← i64MaxNat_spec]
  exact Int.ofNat_le.mpr h

/-- `8 * n` fits in an i64. Implies `FitsLen n` and room for `n + 9` (`pad_z`). -/
def FitsBitlen (n : Nat) : Prop := 8 * n ≤ i64MaxNat

theorem FitsBitlen.fitsLen {n : Nat} (h : FitsBitlen n) : FitsLen n := by
  have hmul : n ≤ 8 * n := by
    have : 1 * n ≤ 8 * n := Nat.mul_le_mul_right n (by decide : 1 ≤ 8)
    simpa using this
  exact Nat.le_trans hmul h

theorem FitsBitlen.room {n : Nat} (h : FitsBitlen n) : n + 9 ≤ i64MaxNat := by
  unfold FitsBitlen i64MaxNat at *
  omega

theorem FitsBitlen.fitsRoom {n : Nat} (h : FitsBitlen n) : FitsLen (n + 9) :=
  FitsBitlen.room h

/-- A message byte in the emitted assert range. -/
def Byte (b : Nat) : Prop := b ≤ 255

theorem Byte.fits {b : Nat} (h : Byte b) : FitsLen b := by
  unfold Byte FitsLen i64MaxNat at *
  omega

/-- Well-formed algebraic message for `pad_message`. -/
structure PadWf (msg : List Nat) : Prop where
  bytes : ∀ b ∈ msg, Byte b
  bitlen : FitsBitlen msg.length

/-- Algebraic list → emitted list. Inverse of `decode` on the image. -/
def embed (xs : List Nat) : Array Int := Array.mk (xs.map Int.ofNat)

/-- Emitted list → algebraic list. Faithful iff every cell is nonnegative. -/
def decode (a : Array Int) : List Nat := a.toList.map Int.toNat

def Nonneg (a : Array Int) : Prop :=
  ∀ i : Nat, (h : i < a.size) → 0 ≤ a[i]

/-- Emitted message whose bytes and bit length survive `pad_message`. -/
structure WellFormedPad (a : Array Int) : Prop where
  nonneg : Nonneg a
  bytes : ∀ i : Nat, (h : i < a.size) → a[i] ≤ 255
  bitlen : FitsBitlen a.size

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

theorem wellFormedPad_embed (msg : List Nat) (h : PadWf msg) : WellFormedPad (embed msg) := by
  refine ⟨nonneg_embed msg, ?_, ?_⟩
  · intro i hi
    rw [get_embed, size_embed] at *
    have hb : Byte (msg[i]'hi) := h.bytes _ (List.getElem_mem hi)
    exact Int.ofNat_le.mpr hb
  · rw [size_embed]
    exact h.bitlen

theorem padWf_decode (a : Array Int) (h : WellFormedPad a) : PadWf (decode a) := by
  refine ⟨?_, ?_⟩
  · intro b hb
    rw [decode] at hb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
    have hi' : i < a.size := by
      simpa [List.length_map] using hi
    have hb' : a[i] ≤ 255 := h.bytes i hi'
    have hnn : 0 ≤ a[i] := h.nonneg i hi'
    have hidx : (a.toList.map Int.toNat)[i] = a[i].toNat := by
      simp [List.getElem_map]
    rw [hidx]
    apply Int.ofNat_le.mp
    rw [Int.toNat_of_nonneg hnn]
    exact hb'
  · have : (decode a).length = a.size := by simp [decode]
    rw [this]
    exact h.bitlen

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

theorem embed_inj {xs ys : List Nat} (h : embed xs = embed ys) : xs = ys := by
  have := congrArg decode h
  simpa [decode_embed] using this

theorem embed_append (xs ys : List Nat) : embed (xs ++ ys) = embed xs ++ embed ys := by
  apply Array.ext'
  simp [embed]

theorem embed_singleton (b : Nat) : embed [b] = #[Int.ofNat b] := rfl

theorem toList_append_arrays (a b : Array Int) : (a ++ b).toList = a.toList ++ b.toList := by
  simp

end MegaDreifach.Link2
