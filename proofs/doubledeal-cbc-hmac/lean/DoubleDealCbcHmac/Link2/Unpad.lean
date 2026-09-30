import DoubleDealCbcHmac.Link2.Pad

/-!
  LINK 2 for `unpad_iso7816` (SPEC §3.1): on byte lists whose length fits an i64, the
  emitted function returns `embed p` exactly when the model `unpad` returns `some p`,
  and traps exactly when `unpad` returns `none`.
-/

namespace DoubleDealCbcHmac.Link2
open MegaDreifach.Link2

/-! ## The model, restated by the trailing-zero count -/

/-- Number of trailing `0` bytes of `m`. -/
def tz (m : List Nat) : Nat := (m.reverse.takeWhile (· == 0)).length

theorem tz_le (m : List Nat) : tz m ≤ m.length := by
  have h := congrArg List.length (List.takeWhile_append_dropWhile (· == 0) m.reverse)
  rw [List.length_append, List.length_reverse] at h
  unfold tz; omega

theorem dropWhile_eq_drop_tz (m : List Nat) :
    m.reverse.dropWhile (· == 0) = m.reverse.drop (tz m) := by
  conv => rhs; rw [← List.takeWhile_append_dropWhile (· == 0) m.reverse]
  rw [tz, List.drop_left]

theorem get_zero_of_lt_tz (m : List Nat) (k : Nat) (hk : k < tz m) :
    m[m.length - 1 - k]'(by have := tz_le m; omega) = 0 := by
  have hk' : k < (m.reverse.takeWhile (· == 0)).length := hk
  have hall := List.all_takeWhile (p := (· == 0)) (l := m.reverse)
  rw [List.all_eq_true] at hall
  have hp := hall _ (List.getElem_mem hk')
  have hrev : m.reverse[k]'(by have := tz_le m; simp; omega) =
      (m.reverse.takeWhile (· == 0))[k] := by
    conv => lhs; rw [List.getElem_of_eq (List.takeWhile_append_dropWhile (· == 0) m.reverse).symm]
    rw [List.getElem_append_left]
  rw [← hrev, List.getElem_reverse] at hp
  simpa using hp

theorem get_ne_zero_at_tz (m : List Nat) (h : tz m < m.length) :
    m[m.length - 1 - tz m]'(by omega) ≠ 0 := by
  have hne : m.reverse.dropWhile (· == 0) ≠ [] := by
    rw [dropWhile_eq_drop_tz]; simp; omega
  have hh := List.head_dropWhile_not (· == 0) m.reverse hne
  have hd : (m.reverse.dropWhile (· == 0)).head hne = m.reverse[tz m]'(by simp; omega) := by
    simp only [dropWhile_eq_drop_tz] at hne ⊢
    rw [List.head_drop]
  rw [hd, List.getElem_reverse] at hh
  simpa using hh

theorem unpad_eq (m : List Nat) (h0 : m.length ≠ 0) (hmod : m.length % hmacBlock = 0) :
    unpad m =
      if h : tz m < m.length then
        (if m[m.length - 1 - tz m]'(by omega) = 128 then
          some (m.take (m.length - 1 - tz m)) else none)
      else none := by
  unfold unpad
  have hc : ¬ (m.length = 0 ∨ m.length % hmacBlock ≠ 0) := by omega
  rw [if_neg hc, dropWhile_eq_drop_tz]
  by_cases h : tz m < m.length
  · rw [dif_pos h, List.drop_eq_getElem_cons (by simpa using h), List.getElem_reverse]
    by_cases h128 : m[m.length - 1 - tz m]'(by omega) = 128
    · rw [if_pos h128]
      simp only [h128, List.reverse_drop, List.reverse_reverse, List.length_reverse]
      congr 2; omega
    · rw [if_neg h128]
      split
      · next heq => exact absurd (List.cons.inj heq).1 h128
      · rfl
  · rw [dif_neg h, List.drop_eq_nil_of_le (by simp; omega)]

/-! ## Loop facts -/

/-- An emitted loop whose iteration `k` traps (after `fromN … k-1` continued) traps. -/
theorem chain_loop_err {α ρ β}
    (step : Int × α → Except SudoRt.Trap (SudoRt.Flow (Int × α) ρ))
    (after : Int × α → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (f : Nat → α) (fromN toN k : Nat) (h1 : fromN ≤ k) (h2 : k ≤ toN)
    (hstep : ∀ i, fromN ≤ i → i < k →
      step (Int.ofNat i, f i) = .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), f (i + 1))))
    (e : SudoRt.Trap) (herr : step (Int.ofNat k, f k) = .error e) :
    SudoRt.runLoopOn (Int.ofNat fromN, f fromN) (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
      step after onRet = .error e := by
  rw [fuelRange_le (by omega)]
  have key : ∀ d j, fromN ≤ j → j + d = k →
      SudoRt.runLoopOn (Int.ofNat j, f j) (toN - j + 1) step after onRet = .error e := by
    intro d
    induction d with
    | zero =>
      intro j _ hj
      subst hj
      simp only [Nat.add_zero] at herr
      rw [runLoopOn_succ, herr]
    | succ d ih =>
      intro j hj1 hj
      rw [runLoopOn_succ, hstep j hj1 (by omega)]
      rw [show toN - j = toN - (j + 1) + 1 by omega]
      exact ih (j + 1) (by omega) (by omega)
  exact key (k - fromN) fromN (Nat.le_refl _) (by omega)

/-- `asc_tail` for an index within the loop bound; the step `i + 1` is taken only when
    `i < toN`, so `FitsLen toN` suffices. -/
theorem asc_tail_le {S ρ : Type} (toN i : Nat) (hi : i ≤ toN) (hfit : FitsLen toN) (s : S) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (Except.ok (SudoRt.Flow.brk (Int.ofNat i, s)) : Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else SudoRt.addI (Int.ofNat i) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont (i', s))) =
      if i = toN then .ok (.brk (Int.ofNat i, s)) else .ok (.cont (Int.ofNat (i + 1), s)) := by
  by_cases h : i = toN
  · subst h; simp [beq_int_iff]
  · exact asc_tail toN i (FitsLen.of_le hfit (by omega)) s

/-- The loop index `i` as the emitted code holds it: `m - 1`, which is `-1` for `m = 0`. -/
def idx (m : Nat) : Int := Int.ofNat m - 1

theorem idx_pos {m : Nat} (h : 1 ≤ m) : idx m = Int.ofNat (m - 1) := by
  unfold idx; simp only [Int.ofNat_eq_coe]; omega

theorem subI_idx {m : Nat} (h : 1 ≤ m) (hfit : FitsLen m) :
    SudoRt.subI (idx m) 1 = .ok (idx (m - 1)) := by
  rw [idx_pos h]
  rcases Nat.lt_or_ge 1 m with hm | hm
  · rw [subI_ofNat_one (m - 1) (by omega) (FitsLen.of_le hfit (by omega)), idx_pos (by omega)]
  · have : m = 1 := by omega
    subst this
    rw [show Int.ofNat (1 - 1) = (0 : Int) from rfl, subI_zero_one]
    rfl

/-- The unpad scan state `(i, found)` on entry to iteration `n` (1-based). -/
def uState (len z n : Nat) : Int × Int :=
  if n - 1 ≤ z then (idx (len - (n - 1)), 0) else (idx (len - z), 1)

theorem uState_scan {len z n : Nat} (h : n - 1 ≤ z) :
    uState len z n = (idx (len - (n - 1)), 0) := if_pos h

theorem uState_found {len z n : Nat} (h : z < n - 1) :
    uState len z n = (idx (len - z), 1) := if_neg (by omega)

/-- The unpad scan loop: iterations `1 … z` step over trailing zeros, iteration `z + 1`
    either finds the `0x80` marker or traps (`bad`), later iterations are idle. -/
theorem scan_loop {ρ β : Type}
    (step : Int × (Int × Int) → Except SudoRt.Trap (SudoRt.Flow (Int × (Int × Int)) ρ))
    (after : Int × (Int × Int) → Except SudoRt.Trap β)
    (onRet : ρ → Except SudoRt.Trap β)
    (len z : Nat) (bad : Prop) [Decidable bad] (hpos : 1 ≤ len) (hbad : bad → z < len)
    (hstep : ∀ n, 1 ≤ n → n ≤ len →
      step (Int.ofNat n, uState len z n) =
        if n - 1 = z ∧ bad then SudoRt.fail "AssertFailed" "line 135"
        else if n = len then .ok (.brk (Int.ofNat n, uState len z (n + 1)))
        else .ok (.cont (Int.ofNat (n + 1), uState len z (n + 1)))) :
    SudoRt.runLoopOn (Int.ofNat 1, uState len z 1) (fuelRange (Int.ofNat 1) (Int.ofNat len))
        step after onRet =
      if bad then SudoRt.fail "AssertFailed" "line 135"
      else after (Int.ofNat len, uState len z (len + 1)) := by
  by_cases hb : bad
  · have hz := hbad hb
    rw [if_pos hb]
    refine chain_loop_err step after onRet (uState len z) 1 len (z + 1) (by omega) (by omega)
      ?_ _ ?_
    · intro i h1 h2
      rw [hstep i h1 (by omega), if_neg (by omega), if_neg (by omega)]
    · rw [hstep (z + 1) (by omega) (by omega), if_pos ⟨by omega, hb⟩]
      rfl
  · rw [if_neg hb]
    refine chain_loop step after onRet (uState len z) 1 len hpos ?_ _ rfl
    intro i h1 h2
    rw [hstep i h1 h2, if_neg (fun h => hb h.2)]

/-- What the emitted scan-and-copy computes on a nonempty, block-aligned byte list,
    including the exact trap on each rejecting path. -/
theorem unpad_iso7816_aligned (msg : List Nat) (hb : Bytes msg) (hfit : FitsLen msg.length)
    (h0 : msg.length ≠ 0) (hmod : msg.length % hmacBlock = 0) :
    Doubledeal_cbc_hmac.unpad_iso7816 (embed msg) =
      if h : tz msg < msg.length then
        (if msg[msg.length - 1 - tz msg]'(by omega) = 128 then
          .ok (embed (msg.take (msg.length - 1 - tz msg)))
        else SudoRt.fail "AssertFailed" "line 135")
      else SudoRt.fail "AssertFailed" "line 136: 0 != 1" := by
  unfold Doubledeal_cbc_hmac.unpad_iso7816
  have hpos : 0 < msg.length := Nat.pos_of_ne_zero h0
  have hA : SudoRt.sudoAssertEq (Int.ofNat 0) (0 : Int) 124 = .ok () := rfl
  simp only [listLen_embed, decide_ofNat_pos, decide_eq_true hpos, sudoAssert_true, ok_bind,
    hmacBlock_int, fuelRange_eq, pure_eq_ok, bind_ok_right]
  rw [modI_ofNat _ (by decide : hmacBlock ≠ 0), ok_bind, hmod, hA, ok_bind,
    require_bytes_refines msg hb hfit, ok_bind, subI_ofNat_one _ hpos hfit, ok_bind]
  rw [show ((1 : Int), (Int.ofNat (msg.length - 1), (0 : Int))) =
    (Int.ofNat 1, uState msg.length (tz msg) 1) by
      simp only [uState, Nat.sub_self, Nat.zero_le, if_true, Nat.sub_zero, idx_pos hpos]; rfl]
  have hz := tz_le msg
  refine (scan_loop _ _ _ msg.length (tz msg)
    (tz msg < msg.length ∧ msg.getD (msg.length - 1 - tz msg) 0 ≠ 128) hpos (fun h => h.1)
    ?_).trans ?_
  · intro n h1 h2
    rw [if_neg (ofNat_not_gt h2)]
    rcases Nat.lt_trichotomy (n - 1) (tz msg) with hk | hk | hk
    · rw [uState_scan (by omega), uState_scan (by omega),
        if_neg (show ¬ (n - 1 = tz msg ∧ _) from fun h => by omega)]
      have hlt : msg.length - 1 - (n - 1) < msg.length := by omega
      have hi : idx (msg.length - (n - 1)) = Int.ofNat (msg.length - 1 - (n - 1)) := by
        rw [idx_pos (by omega), show msg.length - (n - 1) - 1 = msg.length - 1 - (n - 1) by omega]
      have hs := subI_idx (m := msg.length - (n - 1)) (by omega) (FitsLen.of_le hfit (by omega))
      rw [show msg.length - (n - 1) - 1 = msg.length - (n + 1 - 1) by omega] at hs
      rw [hs]
      rw [hi, atL_embed msg _ hlt, get_zero_of_lt_tz msg (n - 1) hk]
      simp only [show SudoRt.SEq.beq (0 : Int) 0 = true from rfl, if_true, ok_bind,
        show SudoRt.SEq.beq (Int.ofNat 0) (0 : Int) = true from rfl]
      rw [asc_tail_le msg.length n h2 hfit]
    · have hzl : tz msg < msg.length := by omega
      have hlt : msg.length - 1 - tz msg < msg.length := by omega
      have hi : idx (msg.length - (n - 1)) = Int.ofNat (msg.length - 1 - tz msg) := by
        rw [idx_pos (by omega), hk, show msg.length - tz msg - 1 = msg.length - 1 - tz msg by omega]
      have hne := get_ne_zero_at_tz msg hzl
      have hne' : decide (Int.ofNat msg[msg.length - 1 - tz msg] = 0) = false :=
        decide_eq_false (fun h => hne (Int.ofNat.inj h))
      rw [uState_scan (by omega), uState_found (by omega), hi, atL_embed msg _ hlt,
        getD_eq_get msg _ hlt]
      simp only [show SudoRt.SEq.beq (0 : Int) 0 = true from rfl, if_true, ok_bind,
        hne', decide_False, Bool.false_eq_true, if_false, sEq_int,
        show (128 : Int) = Int.ofNat 128 from rfl, Int.ofNat.injEq]
      by_cases h128 : msg[msg.length - 1 - tz msg] = 128
      · simp only [h128, decide_True, if_true, ne_eq, not_true_eq_false, and_false, if_false,
          ok_bind]
        rw [asc_tail_le msg.length n h2 hfit, idx_pos (by omega),
          show msg.length - tz msg - 1 = msg.length - 1 - tz msg by omega]
      · simp only [h128, decide_False, Bool.false_eq_true, if_false, ne_eq, not_false_eq_true,
          and_true, hk, hzl, true_and, if_true]
        rfl
    · rw [uState_found (by omega), uState_found (by omega),
        if_neg (show ¬ (n - 1 = tz msg ∧ _) from fun h => by omega)]
      simp only [show SudoRt.SEq.beq (1 : Int) 0 = false from rfl, Bool.false_eq_true, if_false,
        ok_bind]
      rw [asc_tail_le msg.length n h2 hfit]
  · by_cases hzl : tz msg < msg.length
    · have hlt : msg.length - 1 - tz msg < msg.length := by omega
      rw [getD_eq_get msg _ hlt, dif_pos hzl]
      by_cases h128 : msg[msg.length - 1 - tz msg] = 128
      · simp only [h128, ne_eq, not_true_eq_false, and_false, if_false, if_true]
        rw [uState_found (by omega), idx_pos (by omega),
          show msg.length - tz msg - 1 = msg.length - 1 - tz msg by omega]
        have hB : SudoRt.sudoAssertEq (1 : Int) (1 : Int) 136 = .ok () := rfl
        simp only [hB, ok_bind, decide_zero_le_ofNat, ge_iff_le, sudoAssert_true,
          show (0 : Int) = Int.ofNat 0 from rfl, decide_ofNat_le_of (Nat.zero_le _)]
        generalize hc : msg.length - 1 - tz msg = c
        have hcl : c ≤ msg.length := by omega
        rcases Nat.eq_zero_or_pos c with rfl | hcpos
        · rw [show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
          rw [asc_break _ _ _ _ _ _ (by decide) (by rfl)]
          rfl
        · rw [subI_ofNat_one c hcpos (FitsLen.of_le hfit hcl), ok_bind]
          rw [show (#[] : Array Int) = embed [] from rfl]
          refine (push_loop 0 (c - 1) (Nat.zero_le _) (fun j => msg.getD j 0) [] _ _ _ ?_).trans ?_
          · intro j l _ hj
            have hjl : j < msg.length := by omega
            rw [if_neg (ofNat_not_gt hj)]
            simp only [atL_embed msg j hjl, ok_bind, SudoRt.appendL, push_embed']
            rw [asc_tail (c - 1) j (FitsLen.of_le hfit (by omega)), getD_eq_get msg j hjl]
          · rw [List.nil_append, Nat.sub_zero, Nat.sub_add_cancel hcpos,
              range'_map_getD msg 0 c (by omega), List.drop_zero]
      · simp only [h128, ne_eq, not_false_eq_true, and_self, if_true, if_false, hzl]
    · rw [dif_neg hzl, if_neg (fun h => hzl h.1), uState_scan (by omega), Nat.add_sub_cancel,
        Nat.sub_self]
      rfl

/-! ## Headline -/

/-- On any byte list whose length fits an i64, the emitted `unpad_iso7816` succeeds
    exactly when the model does, with the same output, and traps otherwise. -/
theorem unpad_iso7816_char (msg : List Nat) (hb : Bytes msg) (hfit : FitsLen msg.length) :
    (Doubledeal_cbc_hmac.unpad_iso7816 (embed msg)).toOption = (unpad msg).map embed := by
  by_cases h0 : msg.length = 0
  · have : msg = [] := List.eq_nil_of_length_eq_zero h0
    subst this
    rfl
  by_cases hmod : msg.length % hmacBlock = 0
  · rw [unpad_iso7816_aligned msg hb hfit h0 hmod, unpad_eq msg h0 hmod]
    by_cases hz : tz msg < msg.length
    · rw [dif_pos hz, dif_pos hz]
      by_cases h128 : msg[msg.length - 1 - tz msg] = 128
      · rw [if_pos h128, if_pos h128]; rfl
      · rw [if_neg h128, if_neg h128]; rfl
    · rw [dif_neg hz, dif_neg hz]; rfl
  · have hne : unpad msg = none := by
      unfold unpad; rw [if_pos (Or.inr hmod)]
    have hpos : 0 < msg.length := Nat.pos_of_ne_zero h0
    rw [hne]
    unfold Doubledeal_cbc_hmac.unpad_iso7816
    simp only [listLen_embed, decide_ofNat_pos, decide_eq_true hpos, sudoAssert_true, ok_bind,
      hmacBlock_int]
    rw [modI_ofNat _ (by decide : hmacBlock ≠ 0), ok_bind]
    have hB : SudoRt.sudoAssertEq (Int.ofNat (msg.length % hmacBlock)) (0 : Int) 124 =
        SudoRt.fail "AssertFailed"
          s!"line {124}: {SudoRt.Canon.canon (Int.ofNat (msg.length % hmacBlock))} != {SudoRt.Canon.canon (0 : Int)}" := by
      have hd : decide (Int.ofNat (msg.length % hmacBlock) = 0) = false :=
        decide_eq_false (fun h => hmod (Int.ofNat.inj h))
      unfold SudoRt.sudoAssertEq
      rw [sEq_int, hd]
      rfl
    rw [hB]
    rfl

/-- SPEC §3.1: where the model `unpad` accepts, the emitted function returns the same bytes. -/
theorem unpad_iso7816_refines (msg p : List Nat) (hb : Bytes msg) (hfit : FitsLen msg.length)
    (h : unpad msg = some p) :
    Doubledeal_cbc_hmac.unpad_iso7816 (embed msg) = .ok (embed p) := by
  have hc := unpad_iso7816_char msg hb hfit
  rw [h] at hc
  revert hc
  cases Doubledeal_cbc_hmac.unpad_iso7816 (embed msg) with
  | error e => intro hc; cases hc
  | ok v => intro hc; cases hc; rfl

/-- SPEC §3.1: where the model `unpad` rejects, the emitted function traps. -/
theorem unpad_iso7816_rejects (msg : List Nat) (hb : Bytes msg) (hfit : FitsLen msg.length)
    (h : unpad msg = none) :
    ∃ e, Doubledeal_cbc_hmac.unpad_iso7816 (embed msg) = .error e := by
  have hc := unpad_iso7816_char msg hb hfit
  rw [h] at hc
  revert hc
  cases Doubledeal_cbc_hmac.unpad_iso7816 (embed msg) with
  | error e => intro _; exact ⟨e, rfl⟩
  | ok v => intro hc; cases hc

end DoubleDealCbcHmac.Link2
