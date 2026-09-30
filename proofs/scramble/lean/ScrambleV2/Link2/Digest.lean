/-
  LINK 2. The emitted `digest_bytes` against the model's `beBytes 9`: on `s3 < 2^61` and
  an 11-bit `eo`, the 12-byte little-endian buffer (fill, eleven carrying doublings,
  carrying add, three-zero-bytes assert, big-endian copy-out) is the 9-byte big-endian
  encoding of `s3 · 2048 + eo`. Proof-only.
-/
import ScrambleV2.Link2.Rank

namespace ScrambleV2.Link2
open MegaDreifach.Link2

/-! ## Byte arithmetic -/

/-- Byte `k` (little-endian) of `n`. -/
def dig (n k : Nat) : Nat := n / 256 ^ k % 256

theorem pow256_pos (k : Nat) : 0 < 256 ^ k := Nat.pos_pow_of_pos k (by decide)

theorem dig_lt (n k : Nat) : dig n k < 256 := Nat.mod_lt _ (by decide)

theorem div256_succ (s i : Nat) : s / 256 ^ i / 256 = s / 256 ^ (i + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem div_add_split (y o P : Nat) (hP : 0 < P) : (y + o) / P = y / P + (y % P + o) / P := by
  have h := Nat.div_add_mod y P
  have : y + o = (y % P + o) + P * (y / P) := by omega
  rw [this, Nat.add_mul_div_left _ _ hP]; omega

theorem mul2_div_split (y P : Nat) (hP : 0 < P) : 2 * y / P = 2 * (y / P) + 2 * (y % P) / P := by
  have h := Nat.div_add_mod y P
  have : 2 * y = 2 * (y % P) + P * (2 * (y / P)) := by
    rw [Nat.mul_left_comm]; omega
  rw [this, Nat.add_mul_div_left _ _ hP]; omega

/-- Carry into byte `j` when doubling `x`. -/
def dcarry (x j : Nat) : Nat := 2 * (x % 256 ^ j) / 256 ^ j

theorem dcarry_le (x j : Nat) : dcarry x j ≤ 1 := by
  unfold dcarry
  have hP := pow256_pos j
  have : 2 * (x % 256 ^ j) < 2 * 256 ^ j := by
    have := Nat.mod_lt x hP; omega
  have := (Nat.div_lt_iff_lt_mul hP).mpr this
  omega

theorem dcarry_zero (x : Nat) : dcarry x 0 = 0 := by simp [dcarry, Nat.mod_one]

theorem dig_double (x j : Nat) : dig (2 * x) j = (dig x j * 2 + dcarry x j) % 256 := by
  unfold dig dcarry
  rw [mul2_div_split x _ (pow256_pos j)]
  omega

theorem dcarry_succ (x j : Nat) : dcarry x (j + 1) = (dig x j * 2 + dcarry x j) / 256 := by
  unfold dcarry dig
  have hP := pow256_pos j
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, mul2_div_split _ _ hP,
    Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]
  omega

theorem dcarry_top (x : Nat) (h : 2 * x < 256 ^ 12) : dcarry x 12 = 0 := by
  unfold dcarry
  rw [Nat.mod_eq_of_lt (by omega)]
  exact Nat.div_eq_of_lt h

/-- Running carry-plus-addend when adding `o` to `y`, entering byte `j`. -/
def acarry (y o j : Nat) : Nat := (y % 256 ^ j + o) / 256 ^ j

theorem acarry_zero (y o : Nat) : acarry y o 0 = o := by simp [acarry, Nat.mod_one]

theorem acarry_le (y o j : Nat) : acarry y o j ≤ o + 1 := by
  unfold acarry
  have hP := pow256_pos j
  have h1 := Nat.mod_lt y hP
  have h2 : o ≤ o * 256 ^ j := Nat.le_mul_of_pos_right o hP
  have h3 : y % 256 ^ j + o < (o + 2) * 256 ^ j := by rw [Nat.add_mul]; omega
  have := (Nat.div_lt_iff_lt_mul hP).mpr h3
  omega

theorem dig_add (y o j : Nat) : dig (y + o) j = (dig y j + acarry y o j % 256) % 256 := by
  unfold dig acarry
  rw [div_add_split y o _ (pow256_pos j)]
  omega

theorem acarry_succ (y o j : Nat) :
    acarry y o (j + 1) = acarry y o j / 256 + (dig y j + acarry y o j % 256) / 256 := by
  have hP := pow256_pos j
  have e : acarry y o (j + 1) = (dig y j + acarry y o j) / 256 := by
    unfold acarry dig
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, div_add_split _ _ _ hP,
      Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]
  rw [e]; omega

theorem dig_high (Y k : Nat) (hY : Y < 256 ^ 9) (hk : 9 ≤ k) : dig Y k = 0 := by
  unfold dig
  rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hY (Nat.pow_le_pow_right (by decide) hk))]


/-! ## Twelve-byte buffers -/

def bytesOf (f : Nat → Nat) : List Nat := (List.range 12).map f

@[simp] theorem length_bytesOf (f : Nat → Nat) : (bytesOf f).length = 12 := by simp [bytesOf]

theorem getElem_bytesOf (f : Nat → Nat) (k : Nat) (h : k < (bytesOf f).length) :
    (bytesOf f)[k] = f k := by simp [bytesOf]

theorem bytesOf_congr {f g : Nat → Nat} (h : ∀ k, k < 12 → f k = g k) : bytesOf f = bytesOf g := by
  unfold bytesOf
  apply List.map_congr_left
  intro k hk; exact h k (List.mem_range.mp hk)

theorem set_bytesOf (f : Nat → Nat) (j v : Nat) :
    (bytesOf f).set j v = bytesOf (fun k => if k = j then v else f k) := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    rw [List.getElem_set, getElem_bytesOf, getElem_bytesOf]
    by_cases hk : j = k
    · subst hk; simp
    · simp [hk, Ne.symm hk]

theorem putL_embed' (xs : List Nat) (i v : Nat) (h : i < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat i) (Int.ofNat v) = .ok (embed (xs.set i v)) := by
  have hs : i < (embed xs).size := by rw [size_embed]; exact h
  rw [putL_ofNat _ _ _ hs]
  congr 1
  apply Array.ext
  · simp [embed]
  · intro k h1 h2
    simp [embed, Array.getElem_set, List.getElem_set]

theorem putL_bytesOf (f : Nat → Nat) (i v : Nat) (h : i < 12) :
    SudoRt.putL (embed (bytesOf f)) (Int.ofNat i) (Int.ofNat v) =
      .ok (embed (bytesOf (fun k => if k = i then v else f k))) := by
  rw [putL_embed' _ _ _ (by simpa using h), set_bytesOf]

theorem atL_bytesOf (f : Nat → Nat) (i : Nat) (h : i < 12) :
    SudoRt.atL (embed (bytesOf f)) (Int.ofNat i) = .ok (Int.ofNat (f i)) := by
  rw [atL_embed _ _ (by simpa using h), getElem_bytesOf]

theorem filled12 : SudoRt.filledL (12 : Int) (0 : Int) = .ok (embed (bytesOf fun _ => 0)) := by
  rw [show (12 : Int) = Int.ofNat 12 from rfl, filledL_ofNat]; rfl

theorem push_embed' (xs : List Nat) (v : Nat) : (embed xs).push (Int.ofNat v) = embed (xs ++ [v]) := by
  simp [embed]

theorem modI_256 (n : Nat) : SudoRt.modI (Int.ofNat n) (256 : Int) = .ok (Int.ofNat (n % 256)) :=
  modI_ofNat n (by decide)
theorem divI_256 (n : Nat) : SudoRt.divI (Int.ofNat n) (256 : Int) = .ok (Int.ofNat (n / 256)) :=
  divI_ofNat n (by decide)
theorem mulI_2 (n : Nat) (h : FitsLen (n * 2)) : SudoRt.mulI (Int.ofNat n) (2 : Int) = .ok (Int.ofNat (n * 2)) :=
  mulI_ofNat n 2 h

theorem fits_small {n : Nat} (h : n ≤ 1000000) : FitsLen n := by unfold FitsLen i64MaxNat; omega

/-- The emitted assert on a zero carry, at any source line (the line number is not
    pinned, so a regeneration that only moves lines keeps this proof). -/
theorem sudoAssertEq_zero (line : Nat) : SudoRt.sudoAssertEq (Int.ofNat 0) (0 : Int) line = .ok () := by
  unfold SudoRt.sudoAssertEq; rfl

theorem chain_eq {α ρ β}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (f : Nat → α) (fromN toN : Nat) (hle : fromN ≤ toN)
    (hstep : ∀ i, fromN ≤ i → i ≤ toN →
      step (Int.ofNat i, f i) =
        if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, f (i + 1)))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), f (i + 1))))
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat toN, f (toN + 1)) = goal)
    (s0 : α) (h0 : s0 = f fromN) :
    SudoRt.runLoopOn (Int.ofNat fromN, s0) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = goal := by
  subst h0; exact chain_loop step after onRet f fromN toN hle hstep goal hafter

theorem desc_tail {S ρ : Type} (i : Nat) (hfit : FitsLen i) (s : S) :
    (if (Int.ofNat i == (0 : Int)) = true then
        (Except.ok (SudoRt.Flow.brk (Int.ofNat i, s)) : Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else SudoRt.subI (Int.ofNat i) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont (i', s))) =
      if i = 0 then .ok (.brk (Int.ofNat i, s)) else .ok (.cont (Int.ofNat (i - 1), s)) := by
  by_cases h : i = 0
  · subst h; rfl
  · have hne : ¬ (Int.ofNat i = (0 : Int)) := fun e => h (Int.ofNat.inj e)
    simp only [beq_int_iff, hne, if_false, h]
    rw [subI_ofNat_one i (Nat.pos_of_ne_zero h) hfit]
    rfl

theorem take_rev9 : ∀ i, i < 9 →
    (List.range 9).reverse.take (9 - i) = (List.range 9).reverse.take (8 - i) ++ [i] := by
  decide

theorem double_pow (s b : Nat) : 2 * (s * 2 ^ b) = s * 2 ^ (b + 1) := by
  rw [Nat.pow_succ]; simp only [Nat.mul_comm, Nat.mul_left_comm]

/-- `digest_bytes s3 eo` is the 9-byte big-endian encoding of `s3 · 2048 + eo`, for
    `s3 < 2^61` and an 11-bit `eo` (the buffer is 12 bytes; the three high bytes must
    come out zero, which is the emitted assert). -/
theorem digest_bytes_refines (s o : Nat) (hs : s < 2 ^ 61) (ho : o < 2048) :
    Scramble.digest_bytes (Int.ofNat s) (Int.ofNat o) =
      .ok (embed (beBytes 9 (s * 2048 + o))) := by
  have h61 : s < 2305843009213693952 := by simpa using hs
  unfold Scramble.digest_bytes
  simp only [filled12, ok_bind, fuelRange_eq, fuelDown_eq, bind_pure_right]
  refine chain_eq _ _ _ (fun i => (embed (bytesOf fun k => if k < i then dig s k else 0),
    Int.ofNat (s / 256 ^ i))) 0 11 (by omega) ?s1 _ ?a1 _ ?i1
  case i1 => simp
  case s1 =>
    intro i _ hi
    have hil : i < 12 := by omega
    dsimp only
    rw [show (11 : Int) = Int.ofNat 11 from rfl, if_neg (ofNat_not_gt hi)]
    simp only [modI_256, ok_bind, putL_bytesOf _ _ _ hil, divI_256, pure_eq_ok, div256_succ]
    rw [asc_tail 11 i (fits_small (by omega))]
    have hb : bytesOf (fun k => if k = i then s / 256 ^ i % 256 else if k < i then dig s k else 0)
        = bytesOf (fun k => if k < i + 1 then dig s k else 0) := by
      apply bytesOf_congr; intro k _
      by_cases h1 : k = i
      · subst h1; simp [dig]
      · by_cases h2 : k < i
        · simp [h1, h2, show k < i + 1 by omega]
        · simp [h1, h2, show ¬ k < i + 1 by omega]
    rw [hb]
  case a1 =>
    dsimp only
    refine chain_eq _ _ _ (fun b => embed (bytesOf (dig (s * 2 ^ (b - 1))))) 1 11 (by omega)
      ?s2 _ ?a2 _ ?i2
    case i2 =>
      congr 1; apply bytesOf_congr; intro k hk; simp [hk]
    case s2 =>
      intro b hb1 hb2
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have hx : 2 * (s * 2 ^ b') < 256 ^ 12 := by
        have h1 : 2 ^ b' ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
        have h2 : s * 2 ^ b' ≤ s * 2 ^ 10 := Nat.mul_le_mul_left _ h1
        have h3 : (256 : Nat) ^ 12 = 79228162514264337593543950336 := by decide
        have h4 : (2 : Nat) ^ 10 = 1024 := by decide
        omega
      dsimp only
      rw [show (11 : Int) = Int.ofNat 11 from rfl, if_neg (ofNat_not_gt hb2)]
      simp only [Nat.add_sub_cancel]
      rw [bind_ok_of (v := SudoRt.Flow.cont (embed (bytesOf (dig (s * 2 ^ (b' + 1)))))) ?inner]
      · dsimp only
        simp only [pure_eq_ok]
        rw [asc_tail 11 (b' + 1) (fits_small (by omega))]
      · refine chain_eq _ _ _ (fun j => (embed (bytesOf fun k =>
          if k < j then dig (2 * (s * 2 ^ b')) k else dig (s * 2 ^ b') k),
          Int.ofNat (dcarry (s * 2 ^ b') j))) 0 11 (by omega) ?s3 _ ?a3 _ ?i3
        case i3 => dsimp only; rw [dcarry_zero]; simp
        case s3 =>
          intro j _ hj
          have hjl : j < 12 := by omega
          have hd := dig_lt (s * 2 ^ b') j
          have hc := dcarry_le (s * 2 ^ b') j
          dsimp only
          rw [if_neg (ofNat_not_gt hj)]
          simp only [atL_bytesOf _ _ hjl, Nat.lt_irrefl, if_false, ok_bind,
            mulI_2 (dig (s * 2 ^ b') j) (fits_small (by omega)),
            addI_ofNat (dig (s * 2 ^ b') j * 2) (dcarry (s * 2 ^ b') j) (fits_small (by omega)),
            modI_256, divI_256, putL_bytesOf _ _ _ hjl, pure_eq_ok]
          rw [asc_tail 11 j (fits_small (by omega)), ← dig_double, ← dcarry_succ]
          have hb : bytesOf (fun k => if k = j then dig (2 * (s * 2 ^ b')) j else
              if k < j then dig (2 * (s * 2 ^ b')) k else dig (s * 2 ^ b') k)
              = bytesOf (fun k => if k < j + 1 then dig (2 * (s * 2 ^ b')) k
                  else dig (s * 2 ^ b') k) := by
            apply bytesOf_congr; intro k _
            by_cases h1 : k = j
            · subst h1; simp
            · by_cases h2 : k < j
              · simp [h1, h2, show k < j + 1 by omega]
              · simp [h1, h2, show ¬ k < j + 1 by omega]
          rw [hb]
        case a3 =>
          dsimp only
          rw [dcarry_top _ hx, sudoAssertEq_zero,
            ok_bind, double_pow]
          congr 3
    case a2 =>
      dsimp only
      have hY : s * 2048 + o < 256 ^ 9 := by
        have h3 : (256 : Nat) ^ 9 = 4722366482869645213696 := by decide
        omega
      rw [show s * 2 ^ (11 + 1 - 1) = s * 2048 from rfl]
      refine chain_eq _ _ _ (fun j => (embed (bytesOf fun k =>
          if k < j then dig (s * 2048 + o) k else dig (s * 2048) k),
          Int.ofNat (acarry (s * 2048) o j))) 0 11 (by omega) ?s4 _ ?a4 _ ?i4
      case i4 => dsimp only; rw [acarry_zero]; simp
      case s4 =>
        intro j _ hj
        have hjl : j < 12 := by omega
        have hd := dig_lt (s * 2048) j
        have hc := acarry_le (s * 2048) o j
        dsimp only
        rw [show (11 : Int) = Int.ofNat 11 from rfl, if_neg (ofNat_not_gt hj)]
        simp only [atL_bytesOf _ _ hjl, Nat.lt_irrefl, if_false, ok_bind, modI_256,
          addI_ofNat (dig (s * 2048) j) (acarry (s * 2048) o j % 256) (fits_small (by omega)),
          divI_256, putL_bytesOf _ _ _ hjl,
          addI_ofNat (acarry (s * 2048) o j / 256) ((dig (s * 2048) j + acarry (s * 2048) o j % 256) / 256)
            (fits_small (by omega)), pure_eq_ok]
        rw [asc_tail 11 j (fits_small (by omega)), ← dig_add, ← acarry_succ]
        have hb : bytesOf (fun k => if k = j then dig (s * 2048 + o) j else
            if k < j then dig (s * 2048 + o) k else dig (s * 2048) k)
            = bytesOf (fun k => if k < j + 1 then dig (s * 2048 + o) k
                else dig (s * 2048) k) := by
          apply bytesOf_congr; intro k _
          by_cases h1 : k = j
          · subst h1; simp
          · by_cases h2 : k < j
            · simp [h1, h2, show k < j + 1 by omega]
            · simp [h1, h2, show ¬ k < j + 1 by omega]
        rw [hb]
      case a4 =>
        dsimp only
        have hbuf : bytesOf (fun k => if k < 11 + 1 then dig (s * 2048 + o) k else dig (s * 2048) k)
            = bytesOf (dig (s * 2048 + o)) := by
          apply bytesOf_congr; intro k hk; simp [show k < 11 + 1 by omega]
        rw [hbuf]
        simp only [show (9 : Int) = Int.ofNat 9 from rfl, show (10 : Int) = Int.ofNat 10 from rfl,
          show (11 : Int) = Int.ofNat 11 from rfl, atL_bytesOf _ _ (by decide : 9 < 12),
          atL_bytesOf _ _ (by decide : 10 < 12), atL_bytesOf _ _ (by decide : 11 < 12), ok_bind,
          dig_high _ 9 hY (by decide), dig_high _ 10 hY (by decide), dig_high _ 11 hY (by decide)]
        simp only [sEq_ofNat_zero, decide_True, if_true, pure_eq_ok, ok_bind, sudoAssert_true]
        refine chain_down _ _ _
          (fun i => embed (((List.range 9).reverse.take (8 - i)).map (dig (s * 2048 + o))))
          (fun i => embed (((List.range 9).reverse.take (9 - i)).map (dig (s * 2048 + o))))
          8 ?s5 ?l5 _ ?a5
        case s5 =>
          intro i hi
          have hil : i < 12 := by omega
          dsimp only
          rw [if_neg (show ¬ (Int.ofNat i < (0 : Int)) from
            Int.not_lt.mpr (Int.ofNat_zero_le i))]
          simp only [atL_bytesOf _ _ hil, ok_bind, appendL_spec, push_embed', pure_eq_ok]
          rw [desc_tail i (fits_small (by omega)), take_rev9 i (by omega), List.map_append]
          rfl
        case l5 =>
          intro i h1 h2
          dsimp only
          rw [show 9 - i = 8 - (i - 1) by omega]
        case a5 =>
          dsimp only
          rw [List.take_of_length_le (by simp)]
          rfl
end ScrambleV2.Link2
