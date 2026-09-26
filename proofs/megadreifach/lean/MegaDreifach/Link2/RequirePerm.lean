/-
  LINK 2. `Generated.require_permutation` refines algebraic `requirePermutation`
  on a 52-card permutation.

  A deal is well-formed when it has length 52, every entry is a nonnegative
  card id below 52, and there are no duplicates (`isPermutation52`). Those
  integers fit in an i64, so the length assert, `atL` / `putL`, and `addI`
  do not trap. The seen-array marks each id exactly once.

  Algebraic Link 2 only. Not `v_Hash`. Not emitter soundness.
  Not collision resistance.
-/
import Megadreifach
import MegaDreifach.Domain
import MegaDreifach.Link2.Loop

namespace MegaDreifach.Link2

/-! ## Deal domain -/

/-- Trap-free domain for `Generated.require_permutation`.

    Length 52 matches `body_len`. Nonnegative in-range ids make the
    `(c ≥ 0) ∧ (c < 52)` assert succeed and keep `seen[c]` inside the
    filled length-52 array. `Nodup` makes `seen[c] == 0` succeed.
    Every index and card id fits in an i64. -/
structure DealWf (deal : Array Int) : Prop where
  len : deal.size = 52
  nn : Nonneg deal
  bound : ∀ x ∈ decode deal, x < 52
  nodup : (decode deal).Nodup

theorem isPermutation52_decode (deal : Array Int) (h : DealWf deal) :
    isPermutation52 (decode deal) := by
  refine ⟨?_, h.nodup, h.bound⟩
  simp [decode, h.len]

theorem dealWf_embed (deal : List Nat) (h : isPermutation52 deal) :
    DealWf (embed deal) where
  len := by simp [size_embed, h.1]
  nn := nonneg_embed deal
  bound := by
    rw [decode_embed]
    exact h.2.2
  nodup := by
    rw [decode_embed]
    exact h.2.1

/-! ## Seen array: cell `c` is 1 iff `c` occurs in the first `k` cards -/

private def seenBit (deal : List Nat) (k c : Nat) : Nat :=
  if c ∈ deal.take k then 1 else 0

private def seenList (deal : List Nat) (k : Nat) : List Nat :=
  (List.range 52).map (seenBit deal k)

private def seenArr (deal : List Nat) (k : Nat) : Array Int :=
  embed (seenList deal k)

private theorem seenArr_size (deal : List Nat) (k : Nat) :
    (seenArr deal k).size = 52 := by
  simp [seenArr, size_embed, seenList, List.length_map, List.length_range]

private theorem seen_get (deal : List Nat) (k c : Nat) (hc : c < 52) :
    (seenArr deal k)[c]'(by rw [seenArr_size]; exact hc) =
      Int.ofNat (seenBit deal k c) := by
  unfold seenArr
  simp [embed, seenList, seenBit, Array.getElem_eq_getElem_toList,
    List.getElem_map, List.getElem_range, hc]

private theorem seenArr_zero (deal : List Nat) :
    seenArr deal 0 = Array.mkArray 52 (0 : Int) := by
  apply Array.ext
  · simp [seenArr_size, Array.size_mkArray]
  · intro j hj₁ hj₂
    have hj : j < 52 := by rw [seenArr_size] at hj₁; exact hj₁
    rw [Array.getElem_mkArray, seen_get deal 0 j hj]
    simp [seenBit, List.take_zero]

/-- `deal[i]` is not among the earlier cards. -/
private theorem not_mem_take_self (deal : List Nat) (hnd : deal.Nodup)
    {i : Nat} (hi : i < deal.length) : deal[i] ∉ deal.take i := by
  induction deal generalizing i with
  | nil => cases hi
  | cons a as ih =>
    cases i with
    | zero =>
      simp [List.take_zero]
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

private theorem get_mem_take_succ (deal : List Nat) (i : Nat) (hi : i < deal.length) :
    deal[i] ∈ deal.take (i + 1) := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp [Option.toList, List.mem_append]

private theorem mem_take_succ_ne (deal : List Nat) {a : Nat} (i : Nat)
    (hi : i < deal.length) (hne : a ≠ deal[i]) :
    a ∈ deal.take (i + 1) ↔ a ∈ deal.take i := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp [Option.toList, List.mem_append, List.mem_singleton, hne]

private theorem seenArr_succ (deal : List Nat) (h : isPermutation52 deal)
    (i : Nat) (hi : i < 52) :
    (seenArr deal i).set
        ⟨deal[i]'(by rw [h.1]; exact hi), by
          rw [seenArr_size]
          exact h.2.2 _ (List.getElem_mem (by rw [h.1]; exact hi))⟩
        (1 : Int) =
      seenArr deal (i + 1) := by
  have hiLen : i < deal.length := by rw [h.1]; exact hi
  have hcard : deal[i]'hiLen < 52 := h.2.2 _ (List.getElem_mem hiLen)
  apply Array.ext
  · simp [Array.size_set, seenArr_size]
  · intro j hj₁ hj₂
    have hj : j < 52 := by rw [seenArr_size] at hj₂; exact hj₂
    by_cases hcj : deal[i]'hiLen = j
    · rw [Array.getElem_set_eq (eq := hcj)]
      rw [seen_get deal (i + 1) j hj]
      have hmem : j ∈ deal.take (i + 1) := by
        simpa [hcj] using get_mem_take_succ deal i hiLen
      simp [seenBit, hmem]
    · rw [Array.getElem_set_ne (h := hcj)]
      rw [seen_get deal i j hj, seen_get deal (i + 1) j hj]
      have hiff : j ∈ deal.take (i + 1) ↔ j ∈ deal.take i :=
        mem_take_succ_ne deal i hiLen (Ne.symm hcj)
      simp [seenBit, hiff]

/-! ## Emitted loop -/

private theorem coe_int (n : Nat) : (n : Int) = Int.ofNat n := rfl

private theorem sudoAssertEq_rfl (x : Int) (line : Nat) :
    SudoRt.sudoAssertEq x x line = .ok () := by
  have hb : SudoRt.SEq.beq x x = true := by simp [sEq_int]
  unfold SudoRt.sudoAssertEq
  rw [hb]
  rfl

private theorem assert_bodyLen (deal : List Nat) (hlen : deal.length = 52) :
    SudoRt.sudoAssertEq (SudoRt.listLen (embed deal)) Megadreifach.body_len 538 =
      .ok () := by
  rw [listLen_embed, hlen]
  unfold Megadreifach.body_len
  exact sudoAssertEq_rfl (Int.ofNat 52) 538

private theorem fits_idx (i : Nat) (hi : i ≤ 51) : FitsLen (i + 1) := by
  unfold FitsLen i64MaxNat
  omega

/-- Body of one seen-array iteration, in the shape `require_permutation` leaves. -/
private def permBody (deal seen : Array Int) (i : Int) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int) (Array Int)) :=
  do
    let c ← SudoRt.atL deal i
    let inRange ← (if decide (c ≥ (0 : Int)) then (do
      pure (decide (c < (52 : Int)))) else pure false)
    let _ ← SudoRt.sudoAssert inRange 542
    let prev ← SudoRt.atL seen c
    let _ ← SudoRt.sudoAssertEq prev (0 : Int) 543
    let seen ← SudoRt.putL seen c (1 : Int)
    pure (SudoRt.Flow.cont (ρ := Array Int) seen)

/-- One iteration of the emitted seen-array loop. -/
def permStep (deal : Array Int) (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  let i := σ.1
  let seen := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (i, seen))
    else
      match ← (permBody deal seen i) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

private theorem permBody_ok (deal : List Nat) (h : isPermutation52 deal)
    (i : Nat) (hi : i < 52) :
    permBody (embed deal) (seenArr deal i) (i : Int) =
      .ok (SudoRt.Flow.cont (seenArr deal (i + 1))) := by
  have hiLen : i < deal.length := by rw [h.1]; exact hi
  have hcard : deal[i]'hiLen < 52 := h.2.2 _ (List.getElem_mem hiLen)
  have hsz : deal[i]'hiLen < (seenArr deal i).size := by
    rw [seenArr_size]; exact hcard
  unfold permBody
  rw [coe_int i, atL_embed deal i hiLen, ok_bind]
  have hge : decide (Int.ofNat (deal[i]'hiLen) ≥ (0 : Int)) = true :=
    decide_eq_true (Int.ofNat_zero_le _)
  rw [hge, if_pos (rfl : (true = true))]
  have hpure :
      (pure (decide (Int.ofNat (deal[i]'hiLen) < (52 : Int))) : Except SudoRt.Trap Bool) =
        .ok (decide (Int.ofNat (deal[i]'hiLen) < (52 : Int))) := rfl
  rw [hpure]
  have hlt : decide (Int.ofNat (deal[i]'hiLen) < (52 : Int)) = true := by
    apply decide_eq_true
    rw [show (52 : Int) = Int.ofNat 52 from rfl, ofNat_lt_iff]
    exact hcard
  rw [hlt, ok_bind, sudoAssert_true, ok_bind]
  rw [atL_ofNat (seenArr deal i) (deal[i]'hiLen) hsz, ok_bind]
  have hzero : (seenArr deal i)[deal[i]'hiLen]'hsz = (0 : Int) := by
    rw [seen_get deal i (deal[i]'hiLen) hcard]
    unfold seenBit
    rw [if_neg (not_mem_take_self deal h.2.1 hiLen)]
    rfl
  rw [hzero, sudoAssertEq_rfl (0 : Int) 543, ok_bind]
  rw [putL_ofNat (seenArr deal i) (deal[i]'hiLen) (1 : Int) hsz, ok_bind]
  rw [seenArr_succ deal h i hi]
  rfl

private theorem permStep_hit (deal : List Nat) (h : isPermutation52 deal)
    (i : Nat) (hi : i ≤ 51) :
    permStep (embed deal) (51 : Int) (Int.ofNat i, seenArr deal i) =
      if i = 51 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, seenArr deal (i + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), seenArr deal (i + 1))) := by
  have hi52 : i < 52 := by omega
  unfold permStep
  dsimp
  have hngt : ¬ (i : Int) > (51 : Int) := ofNat_not_gt hi
  rw [if_neg hngt, permBody_ok deal h i hi52, ok_bind]
  dsimp
  by_cases heq : i = 51
  · subst heq
    simp [beq_int_iff]
    rfl
  · have hneI : ¬ (i : Int) = (51 : Int) := fun hq => heq (Int.ofNat.inj hq)
    have hadd := addI_ofNat_one i (fits_idx i hi)
    rw [ofNat_eq_natCast i] at hadd
    rw [ite_int_beq, if_neg hneI, hadd, ok_bind, if_neg heq, coe_int (i + 1)]
    rfl

private theorem runLoopOn_congr {σ ρ α} (s0 : σ) (fuel : Nat)
    (step step' : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after after' : σ → Except SudoRt.Trap α)
    (onRet onRet' : ρ → Except SudoRt.Trap α)
    (hstep : ∀ s, step s = step' s)
    (hafter : ∀ s, after s = after' s)
    (hret : ∀ r, onRet r = onRet' r) :
    SudoRt.runLoopOn (ρ := ρ) s0 fuel step after onRet =
      SudoRt.runLoopOn (ρ := ρ) s0 fuel step' after' onRet' := by
  rw [show step = step' from funext hstep,
    show after = after' from funext hafter,
    show onRet = onRet' from funext hret]

private theorem permRun_eq (deal : List Nat) (h : isPermutation52 deal) :
    SudoRt.runLoopOn (ρ := Array Int)
      ((0 : Int), seenArr deal 0)
      (fuelRange (0 : Int) (51 : Int))
      (permStep (embed deal) (51 : Int))
      (fun _ => pure (embed deal))
      (fun r => pure r) =
    .ok (embed deal) := by
  apply chain_loop (f := seenArr deal) (fromN := 0) (toN := 51)
    (goal := .ok (embed deal)) (hle := by decide)
  · intro i _ hi
    exact permStep_hit deal h i hi
  · rfl

/-- `Generated.require_permutation` on the embedding of a 52-card permutation
    returns that embedding, and algebraic `requirePermutation` returns `some`
    of the same list.

    Domain `isPermutation52`: length 52, ids in `0..51`, no duplicates.
    Trap-free i64 indices. Not `v_Hash`, not emitter soundness, not
    collision resistance. -/
theorem require_permutation_refines (deal : List Nat) (h : isPermutation52 deal) :
    Megadreifach.require_permutation (embed deal) = .ok (embed deal) ∧
      requirePermutation deal = some deal := by
  refine ⟨?_, (requirePermutation_iff deal).mpr h⟩
  unfold Megadreifach.require_permutation
  dsimp
  rw [assert_bodyLen deal h.1, ok_bind]
  rw [show (52 : Int) = Int.ofNat 52 from rfl, filledL_ofNat 52 (0 : Int), ok_bind]
  rw [except_bind_pure, ← seenArr_zero deal]
  apply Eq.trans
  · apply runLoopOn_congr
      (step' := permStep (embed deal) (51 : Int))
      (after' := fun _ => pure (embed deal))
      (onRet' := fun r => pure r)
    · intro σ
      unfold permStep permBody
      dsimp
      rfl
    · intro σ
      rfl
    · intro r
      rfl
  · exact permRun_eq deal h

/-- Same refinement on a `DealWf` array. `embed (decode a) = a`, and
    `decode a` is an `isPermutation52` list. -/
theorem require_permutation_refines_array (a : Array Int) (h : DealWf a) :
    Megadreifach.require_permutation a = .ok a ∧
      requirePermutation (decode a) = some (decode a) := by
  have hr := require_permutation_refines (decode a) (isPermutation52_decode a h)
  simpa [embed_decode a h.nn] using hr

end MegaDreifach.Link2
