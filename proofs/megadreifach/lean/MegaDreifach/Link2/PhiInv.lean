/-
  LINK 2. `phi_inv` refines the factoradic Lehmer rank on a 52-card deal,
  emitted as `toBE 28`.

  Generated `phi_inv` walks `i = 0..51`, finds `deal[i]`'s index in the
  remaining cards, folds `n := n * (52 - i) + idx`, erases that index, then
  asserts `n < 2^224` and emits `big_to_be n 28`.

  Domain `PhiInvWf` / `WellFormedPhiInv`: length 52, a permutation of `0..51`,
  and `lehmerRank < 2^224` (`phiMax`).

  Algebraic Link 2 only. Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.PhiChunk
import MegaDreifach.Link2.ToBePad
import MegaDreifach.Link2.MulWide
import MegaDreifach.Link2.MagAdd
import MegaDreifach.Factoradic

namespace MegaDreifach.Link2

set_option maxHeartbeats 8000000

/-! ## Domain -/

/-- Trap-free domain for the 52-card `phi_inv` on a deal list. -/
structure PhiInvWf (deal : List Nat) : Prop where
  len : deal.length = 52
  nodup : deal.Nodup
  bound : ∀ a ∈ deal, a < 52
  small : lehmerRank deal < phiMax

/-- Array-side domain: `phi_inv` input is a 52-card deal. -/
structure WellFormedPhiInv (a : Array Int) : Prop where
  size : a.size = 52
  nn : Nonneg a
  nodup : (decode a).Nodup
  bound : ∀ x ∈ decode a, x < 52
  small : lehmerRank (decode a) < phiMax

theorem phiInv_embed (deal : List Nat) (h : PhiInvWf deal) :
    WellFormedPhiInv (embed deal) where
  size := by simp [size_embed, h.len]
  nn := nonneg_embed deal
  nodup := by rw [decode_embed]; exact h.nodup
  bound := by rw [decode_embed]; exact h.bound
  small := by rw [decode_embed]; exact h.small

theorem phiInv_decode (a : Array Int) (h : WellFormedPhiInv a) :
    PhiInvWf (decode a) where
  len := by simp [decode, h.size]
  nodup := h.nodup
  bound := h.bound
  small := h.small

/-! ## Deal digits and the running Horner accumulator -/

/-- Lehmer digits of a deal, relative to the full 52-card deck. -/
abbrev dealDigits (deal : List Nat) : List Nat :=
  lehmerDigits (List.range 52) deal

/-- `dropUsed` of the first `k` cards: the cards still available at step `k`. -/
abbrev dealAvail (deal : List Nat) (k : Nat) : List Nat :=
  dropUsed (List.range 52) (deal.take k)

/-- Horner accumulator over the first `i` Lehmer digits, radices `52, 51, …`. -/
def accRank (deal : List Nat) (i : Nat) : Nat :=
  mixEncode ((descending 52).take i) ((dealDigits deal).take i)

theorem dealDigits_length (deal : List Nat) : (dealDigits deal).length = deal.length := by
  simp [dealDigits, lehmerDigits_length]

theorem dealAvail_zero (deal : List Nat) : dealAvail deal 0 = List.range 52 := by
  simp [dealAvail, dropUsed, List.take_zero]

theorem dealAvail_succ (deal : List Nat) (k : Nat) (hk : k < deal.length) :
    dealAvail deal (k + 1) =
      (dealAvail deal k).eraseIdx ((dealAvail deal k).findIdx (· == deal[k])) := by
  unfold dealAvail
  rw [take_succ_get deal k hk, dropUsed_snoc]

private theorem getElem_congr {α : Type} {xs ys : List α} (h : xs = ys) (i : Nat)
    (hi : i < xs.length) : xs[i] = ys[i]'(h ▸ hi) := by
  subst h
  rfl

/-- The deal digit at `k` is the first-hit index in the available cards. -/
theorem dealDigit_eq_find (deal : List Nat) (k : Nat) (hk : k < deal.length) :
    (dealDigits deal)[k]'(by rw [dealDigits_length]; exact hk) =
      (dealAvail deal k).findIdx (· == deal[k]) := by
  have hsplit : deal = deal.take k ++ deal.drop k := (List.take_append_drop k deal).symm
  have hlenTake : (deal.take k).length = k := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hdrop : deal.drop k = deal[k] :: deal.drop (k + 1) :=
    List.drop_eq_getElem_cons hk
  have hsplitD := lehmer_split (List.range 52) (deal.take k) (deal.drop k)
  rw [← hsplit] at hsplitD
  have hlen1 : (lehmerDigits (List.range 52) (deal.take k)).length = k := by
    rw [lehmerDigits_length, hlenTake]
  have hhead : lehmerDigits (dealAvail deal k) (deal.drop k) =
      (dealAvail deal k).findIdx (· == deal[k]) ::
        lehmerDigits
          ((dealAvail deal k).eraseIdx ((dealAvail deal k).findIdx (· == deal[k])))
          (deal.drop (k + 1)) := by
    rw [hdrop]
    rfl
  have hidx :=
    getElem_congr hsplitD k (by rw [lehmerDigits_length]; exact hk)
  unfold dealAvail at hhead
  rw [hidx, List.getElem_append_right (by rw [hlen1]; exact Nat.le_refl _)]
  simp only [hlen1, Nat.sub_self]
  have hge := getElem_congr hhead 0 (by rw [hhead]; exact Nat.succ_pos _)
  unfold dealAvail
  rw [hge, List.getElem_cons_zero]

/-! ## Mixed-radix snoc -/

theorem mixEncode_snoc (rs ds : List Nat) (r d : Nat) (hlen : rs.length = ds.length) :
    mixEncode (rs ++ [r]) (ds ++ [d]) = mixEncode rs ds * r + d := by
  induction rs generalizing ds with
  | nil =>
    cases ds <;> simp [mixEncode] at hlen ⊢
  | cons a rs ih =>
    cases ds with
    | nil => simp at hlen
    | cons b ds =>
      have hlen' : rs.length = ds.length := by simpa using hlen
      rw [List.cons_append, List.cons_append, mixEncode_cons, mixEncode_cons, ih ds hlen']
      rw [product_append]
      simp only [product_cons, product_nil, Nat.mul_one]
      rw [← Nat.mul_assoc, Nat.add_mul, Nat.add_assoc]

theorem descending_getElem (n i : Nat) (hi : i < n) :
    (descending n)[i]'(by rw [descending_length]; exact hi) = n - i := by
  have h := descending_getElem? n i hi
  rw [List.getElem?_eq_getElem (by rw [descending_length]; exact hi)] at h
  exact Option.some.inj h

/-- One Horner step: append the next digit and radix `52 - i`. -/
theorem accRank_succ (deal : List Nat) (h52 : deal.length = 52) (i : Nat) (hi : i < 52) :
    accRank deal (i + 1) =
      accRank deal i * (52 - i) + (dealDigits deal)[i]'(by rw [dealDigits_length, h52]; exact hi) := by
  unfold accRank
  have hdi : i < (dealDigits deal).length := by rw [dealDigits_length, h52]; exact hi
  have hrsi : i < (descending 52).length := by rw [descending_length]; exact hi
  rw [take_succ_get (dealDigits deal) i hdi, take_succ_get (descending 52) i hrsi,
    descending_getElem 52 i hi]
  rw [mixEncode_snoc _ _ _ _
    (by rw [List.length_take, List.length_take, descending_length, dealDigits_length, h52,
          Nat.min_eq_left (Nat.le_of_lt hi)])]

private theorem take_eq_self_len {l : List Nat} {n : Nat} (h : n = l.length) : l.take n = l := by
  subst h
  exact List.take_length l

theorem accRank_full (deal : List Nat) (h52 : deal.length = 52) :
    accRank deal 52 = lehmerRank deal := by
  unfold accRank lehmerRank dealDigits
  rw [h52]
  rw [take_eq_self_len (descending_length 52).symm,
    take_eq_self_len (by rw [lehmerDigits_length]; exact h52.symm)]

/-! ## Availability of the deal cards -/

theorem dealAvail_spec (deal : List Nat) (h : PhiInvWf deal) :
    ∀ k, k ≤ 52 →
      (dealAvail deal k).Nodup ∧
      (dealAvail deal k).length = 52 - k ∧
      (∀ x, x ∈ dealAvail deal k ↔ x < 52 ∧ x ∉ deal.take k) := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨List.nodup_range 52, by simp [dealAvail, dropUsed, List.take_zero], ?_⟩
    intro x
    simp [dealAvail, dropUsed, List.take_zero, List.mem_range]
  | succ k ih =>
    have hk0 : k ≤ 52 := Nat.le_trans (Nat.le_succ k) hk
    have hklt : k < 52 := Nat.lt_of_succ_le hk
    have hklen : k < deal.length := by rw [h.len]; exact hklt
    obtain ⟨hnd, hlen, hmem⟩ := ih hk0
    have hnot : deal[k] ∉ deal.take k := not_mem_take_self deal h.nodup hklen
    have hin : deal[k] ∈ dealAvail deal k := by
      rw [hmem]
      exact ⟨h.bound _ (List.getElem_mem hklen), hnot⟩
    have hidx : (dealAvail deal k).findIdx (· == deal[k]) < (dealAvail deal k).length :=
      findIdx_lt_mem _ hin
    have hget := get_findIdx (dealAvail deal k) hin
    refine ⟨?_, ?_, ?_⟩
    · rw [dealAvail_succ deal k hklen]
      exact List.Nodup.eraseIdx _ hnd
    · rw [dealAvail_succ deal k hklen, List.length_eraseIdx_of_lt hidx, hlen]
      omega
    · intro x
      rw [dealAvail_succ deal k hklen, mem_eraseIdx_of_nodup _ hnd hidx, hmem, hget]
      have htake : deal.take (k + 1) = deal.take k ++ [deal[k]] :=
        take_succ_get deal k hklen
      constructor
      · intro ⟨⟨hx, hnin⟩, hne⟩
        refine ⟨hx, ?_⟩
        rw [htake, List.mem_append]
        intro hbad
        cases hbad with
        | inl hm => exact hnin hm
        | inr hm =>
          simp at hm
          exact hne hm
      · intro ⟨hx, hnin⟩
        have hnin0 : x ∉ deal.take k := by
          intro hm
          exact hnin (by rw [htake, List.mem_append]; exact Or.inl hm)
        have hne : x ≠ deal[k] := by
          intro heq
          exact hnin (by rw [htake, List.mem_append]; exact Or.inr (by simp [heq]))
        exact ⟨⟨hx, hnin0⟩, hne⟩

theorem dealAvail_nodup (deal : List Nat) (h : PhiInvWf deal) (k : Nat) (hk : k ≤ 52) :
    (dealAvail deal k).Nodup :=
  (dealAvail_spec deal h k hk).1

theorem dealAvail_length (deal : List Nat) (h : PhiInvWf deal) (k : Nat) (hk : k ≤ 52) :
    (dealAvail deal k).length = 52 - k :=
  (dealAvail_spec deal h k hk).2.1

theorem mem_dealAvail (deal : List Nat) (h : PhiInvWf deal) (k : Nat) (hk : k < 52) :
    deal[k]'(by rw [h.len]; exact hk) ∈ dealAvail deal k := by
  have hmem := (dealAvail_spec deal h k (Nat.le_of_lt hk)).2.2
  have hklen : k < deal.length := by rw [h.len]; exact hk
  rw [hmem]
  exact ⟨h.bound _ (List.getElem_mem hklen), not_mem_take_self deal h.nodup hklen⟩

/-- The digit at `k` is below its radix `52 - k`. -/
theorem dealDigit_lt (deal : List Nat) (h : PhiInvWf deal) (k : Nat) (hk : k < 52) :
    (dealDigits deal)[k]'(by rw [dealDigits_length, h.len]; exact hk) < 52 - k := by
  have hklen : k < deal.length := by rw [h.len]; exact hk
  rw [dealDigit_eq_find deal k hklen, ← dealAvail_length deal h k (Nat.le_of_lt hk)]
  exact findIdx_lt_mem _ (mem_dealAvail deal h k hk)

/-! ## Inner first-hit loop (`ρ := Array Int`) -/

private theorem pure_find_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

def phiInvFindStep (avail : Array Int) (target toV : Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) (Array Int)) :=
  let t := σ.1
  let found := σ.2
  do
    if t > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (t, found))
    else
      match ← ((do
        let flag ← (if decide (found < (0 : Int)) then do
          let a ← SudoRt.atL avail t
          pure (SudoRt.SEq.beq a target)
        else
          pure false)
        if flag then
          pure (SudoRt.Flow.cont (ρ := Array Int) t)
        else
          pure (SudoRt.Flow.cont (ρ := Array Int) found)) :
          Except SudoRt.Trap (SudoRt.Flow Int (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (t, fs))
      | .cont fs => do
          if t == toV then
            pure (SudoRt.Flow.brk (ρ := Array Int) (t, fs))
          else do
            let t' ← SudoRt.addI t (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (t', fs))

private theorem beq_ofNat (a b : Nat) :
    SudoRt.SEq.beq (a : Int) (b : Int) = decide (a = b) := by
  rw [sEq_int, decide_eq_decide]
  constructor
  · intro h
    exact Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h)
  · intro h
    simp [h, ofNat_eq_natCast]

private def foundAt (idx t : Nat) : Int :=
  if t ≤ idx then -1 else Int.ofNat idx

private def foundNext (idx t : Nat) : Int :=
  if t < idx then -1 else Int.ofNat idx

private theorem contFinish (t toV : Nat) (st : Int) (_hle : t ≤ toV)
    (hfits : FitsLen (t + 1)) :
    (if ((t : Int) == (toV : Int)) = true then
        Except.ok (SudoRt.Flow.brk (ρ := Array Int) ((t : Int), st))
      else do
        let t' ← SudoRt.addI (t : Int) (1 : Int)
        Except.ok (SudoRt.Flow.cont (ρ := Array Int) (t', st))) =
      if t = toV then
        .ok (SudoRt.Flow.brk (Int.ofNat t, st))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (t + 1), st)) := by
  by_cases heq : t = toV
  · simp [heq, beq_int_iff]
  · have hneI : ¬ (t : Int) = (toV : Int) := fun h => heq (Int.ofNat.inj h)
    have hadd := addI_ofNat_one t hfits
    rw [ofNat_eq_natCast t] at hadd
    simp [beq_int_iff, hneI, hadd, heq, ofNat_eq_natCast]

private theorem phiInvFindStep_hit (avail : List Nat) (v : Nat) (hv : v ∈ avail)
    (hfits : FitsLen avail.length) (t : Nat) (ht : t < avail.length) :
    let idx := avail.findIdx (· == v)
    phiInvFindStep (embed avail) (Int.ofNat v) (Int.ofNat (avail.length - 1))
        (Int.ofNat t, foundAt idx t) =
      if t = avail.length - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat t, foundNext idx t))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (t + 1), foundNext idx t)) := by
  intro idx
  have hidxLt : idx < avail.length := findIdx_lt_mem avail hv
  have hget : avail[idx] = v := get_findIdx avail hv
  have hle : t ≤ avail.length - 1 := by omega
  have hstep : FitsLen (t + 1) := FitsLen.of_le hfits (by omega)
  unfold phiInvFindStep
  dsimp
  have hngt : ¬ (t : Int) > ((avail.length - 1 : Nat) : Int) := by
    simpa [ofNat_eq_natCast] using ofNat_not_gt hle
  rw [if_neg hngt]
  have hat := atL_embed avail t ht
  simp only [ofNat_eq_natCast] at hat
  have hneg : decide ((-1 : Int) < 0) = true := by decide
  have htail := contFinish t (avail.length - 1) (foundNext idx t) hle hstep
  by_cases hbefore : t < idx
  · have hfound : foundAt idx t = -1 := by simp [foundAt, Nat.le_of_lt hbefore]
    have hnext : foundNext idx t = -1 := by simp [foundNext, hbefore]
    have hne : decide (avail[t] = v) = false := by
      have hp := List.not_of_lt_findIdx (xs := avail) (p := (· == v)) hbefore
      simpa [BEq.beq] using hp
    rw [hfound, hneg, hat, ok_bind, beq_ofNat, hne, pure_find_eq_ok, hnext]
    simp only [if_true, Bool.false_eq_true, ite_false, ok_bind, pure_find_eq_ok]
    rw [hnext] at htail
    exact htail
  · have hge : idx ≤ t := Nat.le_of_not_lt hbefore
    have hnext : foundNext idx t = Int.ofNat idx := by simp [foundNext, hbefore]
    by_cases heq : t = idx
    · have hfound : foundAt idx t = -1 := by simp [foundAt, heq]
      have hvEq : avail[t] = v := by simpa [heq] using hget
      rw [hfound, hneg, hat, ok_bind, beq_ofNat]
      simp only [hvEq, decide_True, if_true, pure_find_eq_ok, ok_bind, hnext]
      rw [hnext] at htail
      rw [heq] at htail ⊢
      exact htail
    · have hgt : idx < t := Nat.lt_of_le_of_ne hge (Ne.symm heq)
      have hfound : foundAt idx t = Int.ofNat idx := by simp [foundAt, hgt]
      have hnn : decide (Int.ofNat idx < 0) = false := by
        simp [Int.not_lt.mpr (Int.ofNat_nonneg idx)]
      rw [hfound, hnn, pure_find_eq_ok, hnext]
      simp only [Bool.false_eq_true, ite_false, ok_bind, pure_find_eq_ok]
      rw [hnext] at htail
      exact htail

private theorem foundAt_zero (idx : Nat) : foundAt idx 0 = -1 := by
  simp [foundAt]

private theorem foundAt_succ (idx i : Nat) : foundNext idx i = foundAt idx (i + 1) := by
  simp only [foundNext, foundAt]
  by_cases h : i < idx
  · simp [h, Nat.succ_le_of_lt h]
  · have : ¬ i + 1 ≤ idx := by omega
    simp [h, this]

private theorem foundAt_done (avail : List Nat) (idx : Nat) (h : idx < avail.length) :
    foundAt idx avail.length = Int.ofNat idx := by
  simp [foundAt, Nat.not_le.mpr h]

/-- The first-hit loop lands on `findIdx`, as the emitted inner loop does. -/
theorem phiInvFind_breaks {α : Type} (avail : List Nat) (v : Nat) (hv : v ∈ avail)
    (hfits : FitsLen avail.length)
    (after : Int × Int → Except SudoRt.Trap α)
    (onRet : Array Int → Except SudoRt.Trap α) :
    let idx := avail.findIdx (· == v)
    SudoRt.runLoopOn (ρ := Array Int)
      ((0 : Int), (-1 : Int))
      (fuelRange (0 : Int) (Int.ofNat (avail.length - 1)))
      (phiInvFindStep (embed avail) (Int.ofNat v) (Int.ofNat (avail.length - 1)))
      after onRet =
      after (Int.ofNat (avail.length - 1), Int.ofNat idx) := by
  intro idx
  have hidxLt : idx < avail.length := findIdx_lt_mem avail hv
  have hpos : 0 < avail.length := Nat.zero_lt_of_lt hidxLt
  rw [show (-1 : Int) = foundAt idx 0 from (foundAt_zero idx).symm]
  apply chain_loop (f := fun i => foundAt idx i) (fromN := 0) (toN := avail.length - 1)
    (hle := Nat.zero_le _)
    (goal := after (Int.ofNat (avail.length - 1), Int.ofNat idx))
  · intro i _ hi
    have hi' : i < avail.length := by omega
    have hs := phiInvFindStep_hit avail v hv hfits i hi'
    simp only [ofNat_eq_natCast] at hs ⊢
    simp only [hs, foundAt_succ]
  · rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos), foundAt_done avail idx hidxLt]

/-! ## Outer `phi_inv` loop -/

abbrev PhiInvSt := Int × (Megadreifach.BigInt × Array Int)

/-- Loop state after `i` steps: running Horner rank and remaining cards. -/
def phiInvState (deal : List Nat) (i : Nat) : Megadreifach.BigInt × Array Int :=
  (bigOf (natLimbs (accRank deal i)), embed (dealAvail deal i))

theorem phiInvState_zero (deal : List Nat) :
    phiInvState deal 0 = (bigOf (natLimbs 0), embed (List.range 52)) := by
  simp [phiInvState, accRank, dealAvail, List.take_zero, dropUsed, mixEncode]

private theorem fits52 : FitsLen 52 := by unfold FitsLen i64MaxNat; decide

/-- Generated outer closure of `phi_inv`, in the shape the emitter leaves it. -/
def phiInvStep (deal : Array Int) (σ : PhiInvSt) :
    Except SudoRt.Trap (SudoRt.Flow PhiInvSt (Array Int)) :=
  let i := σ.1
  let n := σ.2.1
  let avail := σ.2.2
  do
    if i > (51 : Int) then
      pure (SudoRt.Flow.brk (ρ := Array Int) (i, (n, avail)))
    else
      match ← (do
        let v ← SudoRt.atL deal i
        let found ← SudoRt.negI (1 : Int)
        let _toV ← SudoRt.subI (SudoRt.listLen avail) (1 : Int)
        let _out ← SudoRt.runLoopOn (ρ := Array Int) ((0 : Int), found)
          (if (0 : Int) > _toV then 1 else (_toV - (0 : Int)).natAbs + 1)
          (phiInvFindStep avail v _toV)
          (fun σ =>
            let found := σ.2
            do
              let _as ← SudoRt.sudoAssert (decide (found ≥ (0 : Int))) 526
              let idx := found
              let _t549 ← SudoRt.subI (52 : Int) i
              let _t550 ← Megadreifach.big_from_int _t549
              let _t551 ← Megadreifach.big_mul n _t550
              let _t552 ← Megadreifach.big_from_int idx
              let _t553 ← Megadreifach.big_add _t551 _t552
              let n := _t553
              let fresh := (#[] : Array Int)
              let _t561 ← SudoRt.subI (SudoRt.listLen avail) (1 : Int)
              let _fuel : Nat := if (0 : Int) > _t561 then 1 else (_t561 - (0 : Int)).natAbs + 1
              let _out ← SudoRt.runLoopOn (ρ := Array Int) ((0 : Int), fresh) _fuel
                (phiEraseStep avail idx _t561)
                (fun σ =>
                  let fresh := σ.2
                  pure (SudoRt.Flow.cont (ρ := Array Int) (n, fresh)))
                (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r))
              pure _out)
          (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r))
        pure _out) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
      | .cont fs => do
          if i == (51 : Int) then
            pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

/-- Close the outer continuation when `i < 51` (no break). -/
private theorem phiInvFinish (i : Nat) (hi : i < 51)
    (st : Megadreifach.BigInt × Array Int) :
    (if (Int.ofNat i == Int.ofNat 51) = true then
        Except.ok (SudoRt.Flow.brk (ρ := Array Int) (Int.ofNat i, st))
      else do
        let i' ← SudoRt.addI (Int.ofNat i) (1 : Int)
        Except.ok (SudoRt.Flow.cont (ρ := Array Int) (i', st))) =
      .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), st)) := by
  have hne : ¬ ((Int.ofNat i == Int.ofNat 51) = true) := by
    intro h
    have h' : Int.ofNat i = Int.ofNat 51 := (beq_int_iff _ _).mp h
    exact absurd (Int.ofNat.inj h') (by omega)
  have hadd := addI_ofNat_one i (FitsLen.of_le fits52 (by omega))
  rw [if_neg hne, hadd, ok_bind]

private theorem phiInvFinish51
    (st : Megadreifach.BigInt × Array Int) :
    (if (Int.ofNat 51 == Int.ofNat 51) = true then
        Except.ok (SudoRt.Flow.brk (ρ := Array Int) (Int.ofNat 51, st))
      else do
        let i' ← SudoRt.addI (Int.ofNat 51) (1 : Int)
        Except.ok (SudoRt.Flow.cont (ρ := Array Int) (i', st))) =
      .ok (SudoRt.Flow.brk (Int.ofNat 51, st)) := by
  rw [if_pos (by rw [beq_int_iff])]

/-! ## Numeric bounds for the step -/

theorem phiMax_lt_limb8 : phiMax < limbBase ^ 8 := by
  rw [← pow256_28_eq_phiMax]
  exact pow256_28_lt_limb8

/-- The prefix accumulator never exceeds the full rank. -/
theorem accRank_le_full (deal : List Nat) (h52 : deal.length = 52) (i : Nat) (hi : i ≤ 52) :
    accRank deal i ≤ accRank deal 52 := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
  have h : ∀ e, i + e ≤ 52 → accRank deal i ≤ accRank deal (i + e) := by
    intro e
    induction e with
    | zero => intro _; simp
    | succ e ih =>
      intro he
      have he' : i + e ≤ 52 := by omega
      have hlt : i + e < 52 := by omega
      rw [show i + (e + 1) = (i + e) + 1 from by omega,
        accRank_succ deal h52 (i + e) hlt]
      have hrad : 1 ≤ 52 - (i + e) := by omega
      have hmul := Nat.mul_le_mul_left (accRank deal (i + e)) hrad
      rw [Nat.mul_one] at hmul
      exact Nat.le_trans (ih he') (by omega)
  rw [hd]
  exact h d (by omega)

theorem accRank_lt_phiMax (deal : List Nat) (h : PhiInvWf deal) (i : Nat) (hi : i ≤ 52) :
    accRank deal i < phiMax := by
  refine Nat.lt_of_le_of_lt (accRank_le_full deal h.len i hi) ?_
  rw [accRank_full deal h.len]
  exact h.small

theorem accRank_limbs_le8 (deal : List Nat) (h : PhiInvWf deal) (i : Nat) (hi : i ≤ 52) :
    (natLimbs (accRank deal i)).length ≤ 8 :=
  natLimbs_length_le _ 8 (Nat.lt_trans (accRank_lt_phiMax deal h i hi) phiMax_lt_limb8)

theorem accRank_limbs_fits (deal : List Nat) (h : PhiInvWf deal) (i : Nat) (hi : i ≤ 52) :
    FitsLen (natLimbs (accRank deal i)).length :=
  FitsLen.of_le fits52 (by have := accRank_limbs_le8 deal h i hi; omega)

theorem accRank_limbs_succ_fits (deal : List Nat) (h : PhiInvWf deal) (i : Nat) (hi : i ≤ 52) :
    FitsLen ((natLimbs (accRank deal i)).length + 1) :=
  FitsLen.of_le fits52 (by have := accRank_limbs_le8 deal h i hi; omega)

theorem radix_fits (i : Nat) (hi : i < 52) : FitsLen (52 - i) :=
  FitsLen.of_le fits52 (by omega)

theorem digit_fits (deal : List Nat) (h : PhiInvWf deal) (i : Nat) (hi : i < 52) :
    FitsLen ((dealDigits deal)[i]'(by rw [dealDigits_length, h.len]; exact hi)) := by
  have := dealDigit_lt deal h i hi
  exact FitsLen.of_le fits52 (by omega)

theorem radix_lt_limb (i : Nat) (_hi : i < 52) : 52 - i < limbBase :=
  Nat.lt_of_le_of_lt (Nat.sub_le 52 i) (by decide : 52 < limbBase)

/-- Below the limb base `limbsOfNat` and `natLimbs` agree. -/
private theorem limbsOfNat_eq_natLimbs {b : Nat} (hb : b < limbBase) :
    limbsOfNat b = natLimbs b := by
  rw [natLimbs_of_lt b hb]
  unfold limbsOfNat
  by_cases h0 : b = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    rw [Nat.div_eq_of_lt hb, Nat.mod_eq_of_lt hb]
    simp

/-- The product `(52 - i) * accRank` stays below `limbBase ^ 8`. -/
theorem accRank_mul_lt_limb8 (deal : List Nat) (h : PhiInvWf deal) (i : Nat) (hi : i < 52) :
    (52 - i) * accRank deal i < limbBase ^ 8 := by
  have ha := accRank_lt_phiMax deal h i (by omega)
  have h52lt : 52 * phiMax < limbBase ^ 8 := by
    rw [← pow256_28_eq_phiMax]
    decide
  calc
    (52 - i) * accRank deal i ≤ 52 * accRank deal i :=
      Nat.mul_le_mul_right _ (by omega)
    _ < 52 * phiMax := Nat.mul_lt_mul_of_pos_left ha (by decide)
    _ < limbBase ^ 8 := h52lt

theorem accRank_mul_limbs_le8 (deal : List Nat) (h : PhiInvWf deal) (i : Nat) (hi : i < 52) :
    (natLimbs ((52 - i) * accRank deal i)).length ≤ 8 :=
  natLimbs_length_le _ 8 (accRank_mul_lt_limb8 deal h i hi)

theorem digit_lt_limb (idx : Nat) (hidx : idx < 52) : idx < limbBase :=
  Nat.lt_trans hidx (by decide : 52 < limbBase)

theorem accRank_add_limbs_fits (deal : List Nat) (h : PhiInvWf deal) (i idx : Nat)
    (hi : i < 52) (hidx : idx < 52) :
    FitsLen (max (natLimbs ((52 - i) * accRank deal i)).length (natLimbs idx).length + 1) := by
  have h1 := accRank_mul_limbs_le8 deal h i hi
  have h2 : (natLimbs idx).length ≤ 1 :=
    natLimbs_length_le idx 1 (by rw [Nat.pow_one]; exact digit_lt_limb idx hidx)
  have hm : max (natLimbs ((52 - i) * accRank deal i)).length (natLimbs idx).length ≤ 8 :=
    Nat.max_le.mpr ⟨h1, Nat.le_trans h2 (by decide : 1 ≤ 8)⟩
  exact FitsLen.of_le fits52 (by omega)

/-! ## One outer step -/

/-- One step of the outer loop, `i < 51`. -/
theorem phiInvStep_lt (deal : List Nat) (h : PhiInvWf deal) (i : Nat) (hi : i < 51) :
    phiInvStep (embed deal) (Int.ofNat i, phiInvState deal i) =
      .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), phiInvState deal (i + 1))) := by
  have hi52 : i < 52 := by omega
  have hile : i ≤ 51 := by omega
  have hklen : i < deal.length := by rw [h.len]; exact hi52
  have hlen : (dealAvail deal i).length = 52 - i := dealAvail_length deal h i (by omega)
  have hpos : 0 < (dealAvail deal i).length := by rw [hlen]; omega
  have hfits : FitsLen (dealAvail deal i).length := by
    rw [hlen]; exact radix_fits i hi52
  have hmem : deal[i]'(by rw [h.len]; exact hi52) ∈ dealAvail deal i :=
    mem_dealAvail deal h i hi52
  have hidxlt : (dealAvail deal i).findIdx (· == deal[i]'(by rw [h.len]; exact hi52)) <
      (dealAvail deal i).length := findIdx_lt_mem _ hmem
  have hidx52 : (dealAvail deal i).findIdx (· == deal[i]'(by rw [h.len]; exact hi52)) < 52 := by
    rw [hlen] at hidxlt; omega
  have hidxfits :
      FitsLen ((dealAvail deal i).findIdx (· == deal[i]'(by rw [h.len]; exact hi52))) :=
    FitsLen.of_le fits52 (by omega)
  have hnew : (52 - i) * accRank deal i +
        (dealAvail deal i).findIdx (· == deal[i]'(by rw [h.len]; exact hi52)) =
      accRank deal (i + 1) := by
    rw [accRank_succ deal h.len i hi52, ← dealDigit_eq_find deal i hklen, Nat.mul_comm]
  unfold phiInvStep
  dsimp only
  dsimp only [phiInvState]
  rw [show (51 : Int) = Int.ofNat 51 from rfl]
  rw [if_neg (ofNat_not_gt hile)]
  rw [atL_embed deal i hklen, ok_bind, negI_one, ok_bind]
  simp only [listLen_embed, subI_ofNat_one (dealAvail deal i).length hpos hfits, ok_bind]
  rw [fuelRange_eq]
  rw [phiInvFind_breaks (dealAvail deal i) (deal[i]'(by rw [h.len]; exact hi52)) hmem hfits]
  dsimp only
  have hge : decide ((Int.ofNat
        ((dealAvail deal i).findIdx (· == deal[i]'(by rw [h.len]; exact hi52)))) ≥ (0 : Int)) =
      true := by
    rw [decide_eq_true_eq]; exact Int.ofNat_nonneg _
  rw [hge, sudoAssert_true, ok_bind]
  rw [show (52 : Int) = Int.ofNat 52 from rfl, subI_ofNat 52 i fits52 (by omega), ok_bind]
  rw [big_from_int_refines (52 - i) (radix_fits i hi52),
    limbsOfNat_eq_natLimbs (radix_lt_limb i hi52), ok_bind]
  rw [big_mul_nat (52 - i) (accRank deal i) (radix_lt_limb i hi52)
    (accRank_limbs_succ_fits deal h i (by omega)), ok_bind]
  rw [big_from_int_refines ((dealAvail deal i).findIdx (· == deal[i]'(by rw [h.len]; exact hi52)))
    hidxfits, limbsOfNat_eq_natLimbs (digit_lt_limb _ hidx52), ok_bind]
  rw [big_add_nat ((52 - i) * accRank deal i)
    ((dealAvail deal i).findIdx (· == deal[i]'(by rw [h.len]; exact hi52)))
    (accRank_add_limbs_fits deal h i _ hi52 hidx52), ok_bind]
  rw [show (#[] : Array Int) =
      embed (takeSkip (dealAvail deal i)
        ((dealAvail deal i).findIdx (· == deal[i]'(by rw [h.len]; exact hi52))) 0) from by
    rw [takeSkip_zero]; exact embed_nil.symm]
  rw [phiErase_breaks (dealAvail deal i)
    ((dealAvail deal i).findIdx (· == deal[i]'(by rw [h.len]; exact hi52))) hidxlt hfits]
  dsimp only
  rw [← dealAvail_succ deal i hklen, hnew]
  simp only [except_bind_pure, pure_find_eq_ok, ok_bind]
  rw [phiInvFinish i hi]

/-- One step of the outer loop at `i = 51` (emits the full rank, breaks). -/
theorem phiInvStep_51 (deal : List Nat) (h : PhiInvWf deal) :
    phiInvStep (embed deal) (Int.ofNat 51, phiInvState deal 51) =
      .ok (SudoRt.Flow.brk (Int.ofNat 51, phiInvState deal 52)) := by
  have hile : 51 ≤ 51 := Nat.le_refl _
  have hklen : 51 < deal.length := by rw [h.len]; decide
  have hlen : (dealAvail deal 51).length = 1 := by
    rw [dealAvail_length deal h 51 (by decide)]
  have hpos : 0 < (dealAvail deal 51).length := by rw [hlen]; decide
  have hfits : FitsLen (dealAvail deal 51).length := by
    rw [hlen]; exact FitsLen.of_le fits52 (by decide)
  have hmem : deal[51]'(by rw [h.len]; decide) ∈ dealAvail deal 51 :=
    mem_dealAvail deal h 51 (by decide)
  have hidxlt : (dealAvail deal 51).findIdx (· == deal[51]'(by rw [h.len]; decide)) <
      (dealAvail deal 51).length := findIdx_lt_mem _ hmem
  have hidxfits :
      FitsLen ((dealAvail deal 51).findIdx (· == deal[51]'(by rw [h.len]; decide))) :=
    FitsLen.of_le fits52 (by rw [hlen] at hidxlt; omega)
  have hdigit : (dealDigits deal)[51]'(by rw [dealDigits_length, h.len]; decide) = 0 := by
    have hlt := dealDigit_lt deal h 51 (by decide)
    rw [show 52 - 51 = 1 from rfl] at hlt
    omega
  have hidx0 : (dealAvail deal 51).findIdx (· == deal[51]'(by rw [h.len]; decide)) = 0 := by
    rw [← dealDigit_eq_find deal 51 hklen]
    exact hdigit
  have hnew : (52 - 51) * accRank deal 51 +
        (dealAvail deal 51).findIdx (· == deal[51]'(by rw [h.len]; decide)) =
      accRank deal 52 := by
    rw [accRank_succ deal h.len 51 (by decide), ← dealDigit_eq_find deal 51 hklen, Nat.mul_comm]
  unfold phiInvStep
  dsimp only
  dsimp only [phiInvState]
  rw [show (51 : Int) = Int.ofNat 51 from rfl]
  rw [if_neg (ofNat_not_gt hile)]
  rw [atL_embed deal 51 hklen, ok_bind, negI_one, ok_bind]
  simp only [listLen_embed, subI_ofNat_one (dealAvail deal 51).length hpos hfits, ok_bind]
  rw [fuelRange_eq]
  rw [phiInvFind_breaks (dealAvail deal 51) (deal[51]'(by rw [h.len]; decide)) hmem hfits]
  dsimp only
  have hge : decide ((Int.ofNat
        ((dealAvail deal 51).findIdx (· == deal[51]'(by rw [h.len]; decide)))) ≥ (0 : Int)) =
      true := by
    rw [decide_eq_true_eq]; exact Int.ofNat_nonneg _
  rw [hge, sudoAssert_true, ok_bind]
  rw [show (52 : Int) = Int.ofNat 52 from rfl, subI_ofNat 52 51 fits52 (by decide), ok_bind]
  rw [big_from_int_refines (52 - 51) (radix_fits 51 (by decide)),
    limbsOfNat_eq_natLimbs (radix_lt_limb 51 (by decide)), ok_bind]
  rw [big_mul_nat (52 - 51) (accRank deal 51) (radix_lt_limb 51 (by decide))
    (accRank_limbs_succ_fits deal h 51 (by decide)), ok_bind]
  rw [big_from_int_refines ((dealAvail deal 51).findIdx (· == deal[51]'(by rw [h.len]; decide)))
    hidxfits, limbsOfNat_eq_natLimbs (digit_lt_limb _ (by rw [hlen] at hidxlt; omega)), ok_bind]
  rw [big_add_nat ((52 - 51) * accRank deal 51)
    ((dealAvail deal 51).findIdx (· == deal[51]'(by rw [h.len]; decide)))
    (accRank_add_limbs_fits deal h 51 _ (by decide) (by rw [hlen] at hidxlt; omega)), ok_bind]
  rw [show (#[] : Array Int) =
      embed (takeSkip (dealAvail deal 51)
        ((dealAvail deal 51).findIdx (· == deal[51]'(by rw [h.len]; decide))) 0) from by
    rw [takeSkip_zero]; exact embed_nil.symm]
  rw [phiErase_breaks (dealAvail deal 51)
    ((dealAvail deal 51).findIdx (· == deal[51]'(by rw [h.len]; decide))) hidxlt hfits]
  dsimp only
  rw [← dealAvail_succ deal 51 hklen, hnew]
  simp only [except_bind_pure, pure_find_eq_ok, ok_bind]
  rw [phiInvFinish51]

/-- The full Horner accumulator is the Lehmer rank. -/
theorem phiInvState_full (deal : List Nat) (h : PhiInvWf deal) :
    phiInvState deal 52 = (bigOf (natLimbs (lehmerRank deal)), embed (dealAvail deal 52)) := by
  rw [phiInvState, accRank_full deal h.len]

/-- The outer `phi_inv` loop accumulates the Lehmer rank over 52 steps. -/
theorem phiInv_loop_breaks (deal : List Nat) (h : PhiInvWf deal)
    {α : Type} (after : PhiInvSt → Except SudoRt.Trap α)
    (onRet : Array Int → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (ρ := Array Int) (Int.ofNat 0, phiInvState deal 0)
      (fuelRange (Int.ofNat 0) (Int.ofNat 51)) (phiInvStep (embed deal)) after onRet =
      after (Int.ofNat 51, phiInvState deal 52) := by
  apply chain_loop (f := phiInvState deal) (fromN := 0) (toN := 51) (hle := by decide)
  · intro i _ hhi
    rcases (by omega : i < 51 ∨ i = 51) with hlt | heq
    · rw [if_neg (by omega)]
      exact phiInvStep_lt deal h i hlt
    · subst heq
      rw [if_pos rfl]
      exact phiInvStep_51 deal h
  · rfl

/-! ## `two224` = `2^224` -/

theorem two_pow_224_lt_limb8 : (2 : Nat) ^ 224 < limbBase ^ 8 :=
  phiMax_lt_limb8

private theorem fits224 : FitsLen 224 := by
  unfold FitsLen i64MaxNat
  decide

/-- Generated closure of `two224`, in the shape the emitter leaves it. -/
def two224Step (two : Megadreifach.BigInt) (σ : Int × Megadreifach.BigInt) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Megadreifach.BigInt) Megadreifach.BigInt) :=
  let i := σ.1
  let n := σ.2
  do
    if i > (224 : Int) then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, n))
    else
      match ← ((do
        let _t425 ← Megadreifach.big_mul n two
        pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) _t425)) :
          Except SudoRt.Trap (SudoRt.Flow Megadreifach.BigInt Megadreifach.BigInt)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, fs))
      | .cont fs => do
          if i == (224 : Int) then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (i', fs))

private theorem two224Finish (i : Nat) (hi : i < 224) (st : Megadreifach.BigInt) :
    (if (Int.ofNat i == Int.ofNat 224) = true then
        Except.ok (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (Int.ofNat i, st))
      else do
        let i' ← SudoRt.addI (Int.ofNat i) (1 : Int)
        Except.ok (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (i', st))) =
      .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), st)) := by
  have hne : ¬ ((Int.ofNat i == Int.ofNat 224) = true) := by
    intro h
    have h' : Int.ofNat i = Int.ofNat 224 := (beq_int_iff _ _).mp h
    exact absurd (Int.ofNat.inj h') (by omega)
  have hadd := addI_ofNat_one i (FitsLen.of_le fits224 (by omega))
  rw [if_neg hne, hadd, ok_bind]

theorem two224Step_hit (i n : Nat) (hi1 : 1 ≤ i) (hi : i ≤ 224)
    (hn : FitsLen ((natLimbs n).length + 1)) :
    two224Step (bigOf (natLimbs 2)) (Int.ofNat i, bigOf (natLimbs n)) =
      if i = 224 then
        .ok (SudoRt.Flow.brk (ρ := Megadreifach.BigInt)
          (Int.ofNat i, bigOf (natLimbs (2 * n))))
      else
        .ok (SudoRt.Flow.cont (ρ := Megadreifach.BigInt)
          (Int.ofNat (i + 1), bigOf (natLimbs (2 * n)))) := by
  unfold two224Step
  dsimp only
  rw [show (224 : Int) = Int.ofNat 224 from rfl]
  rw [if_neg (ofNat_not_gt hi)]
  rw [big_mul_nat 2 n (by decide) hn]
  simp only [pure_find_eq_ok, ok_bind]
  by_cases heq : i = 224
  · rw [if_pos (by rw [beq_int_iff]; exact congrArg Int.ofNat heq), if_pos heq]
  · rw [two224Finish i (by omega) (bigOf (natLimbs (2 * n))), if_neg heq]

theorem two224_spec : Megadreifach.two224 = .ok (bigOf (natLimbs (2 ^ 224))) := by
  unfold Megadreifach.two224
  rw [show (1 : Int) = Int.ofNat 1 from rfl, show (2 : Int) = Int.ofNat 2 from rfl]
  rw [big_from_int_refines 1 (FitsLen.of_le fits52 (by decide)),
      limbsOfNat_eq_natLimbs (by decide : 1 < limbBase), ok_bind,
      big_from_int_refines 2 (FitsLen.of_le fits52 (by decide)),
      limbsOfNat_eq_natLimbs (by decide : 2 < limbBase), ok_bind]
  dsimp only
  rw [fuelRange_eq]
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := two224Step (bigOf (natLimbs 2)))
    intro σ
    rfl
  · apply chain_loop (f := fun i => bigOf (natLimbs (2 ^ (i - 1)))) (fromN := 1) (toN := 224)
      (hle := by decide)
    · intro i hi1 hi2
      have hn : FitsLen ((natLimbs (2 ^ (i - 1))).length + 1) := by
        have hlt : 2 ^ (i - 1) < limbBase ^ 8 :=
          Nat.lt_of_le_of_lt
            (Nat.pow_le_pow_of_le_right (by decide) (by omega : i - 1 ≤ 224))
            two_pow_224_lt_limb8
        have hl := natLimbs_length_le _ 8 hlt
        exact FitsLen.of_le fits52 (by omega)
      rw [two224Step_hit i (2 ^ (i - 1)) hi1 hi2 hn]
      have hpow : 2 * 2 ^ (i - 1) = 2 ^ i := by
        rw [Nat.mul_comm, ← Nat.pow_succ]
        congr 1
        omega
      rw [hpow, show i + 1 - 1 = i from by omega]
    · rfl

/-! ## `mag_cmp` on canonical limbs -/

/-- Lexicographic comparison of the most significant limbs, index `i` downwards. -/
def cmpAux (a b : List Nat) : Nat → Int
  | 0 => if digAt a 0 < digAt b 0 then -1 else if digAt b 0 < digAt a 0 then 1 else 0
  | i + 1 =>
      if digAt a (i + 1) < digAt b (i + 1) then -1
      else if digAt b (i + 1) < digAt a (i + 1) then 1
      else cmpAux a b i

/-- Generated inner comparison closure of `mag_cmp`, in emitter shape. -/
def magCmpStep (a b : Array Int) (σ : Int) : Except SudoRt.Trap (SudoRt.Flow Int Int) :=
  let i := σ
  do
    if i < (0 : Int) then
      pure (SudoRt.Flow.brk (ρ := Int) i)
    else
      match ← ((do
        let x ← SudoRt.atL a i
        let y ← SudoRt.atL b i
        if decide (x < y) then (do
          let z ← SudoRt.negI (1 : Int)
          pure (SudoRt.Flow.ret (ρ := Int) z))
        else (do
          let y2 ← SudoRt.atL b i
          let x2 ← SudoRt.atL a i
          if decide (y2 < x2) then (do
            pure (SudoRt.Flow.ret (ρ := Int) (1 : Int)))
          else (do
            pure (SudoRt.Flow.cont (ρ := Int) ())))) :
          Except SudoRt.Trap (SudoRt.Flow Unit Int)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Int) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Int) i)
      | .cont fs => do
          if i == (0 : Int) then
            pure (SudoRt.Flow.brk (ρ := Int) i)
          else do
            let i' ← SudoRt.subI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Int) i')

theorem magCmpStep_hit (a b : List Nat) (i : Nat) (ha : i < a.length) (hb : i < b.length)
    (hfit : FitsLen i) :
    magCmpStep (embed a) (embed b) (Int.ofNat i) =
      if a[i] < b[i] then .ok (SudoRt.Flow.ret (ρ := Int) (-1))
      else if b[i] < a[i] then .ok (SudoRt.Flow.ret (ρ := Int) 1)
      else if i = 0 then .ok (SudoRt.Flow.brk (ρ := Int) (Int.ofNat i))
      else .ok (SudoRt.Flow.cont (ρ := Int) (Int.ofNat (i - 1))) := by
  have hnotlt : ¬ (Int.ofNat i < (0 : Int)) := Int.not_lt.mpr (Int.ofNat_zero_le i)
  have hdec1 : decide (Int.ofNat (a[i]) < Int.ofNat (b[i])) = decide (a[i] < b[i]) := by
    rw [decide_eq_decide]; exact ofNat_lt_iff _ _
  have hdec2 : decide (Int.ofNat (b[i]) < Int.ofNat (a[i])) = decide (b[i] < a[i]) := by
    rw [decide_eq_decide]; exact ofNat_lt_iff _ _
  have hbeq : (Int.ofNat i == (0 : Int)) = decide (i = 0) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_int_iff, decide_eq_true_eq, ofNat_eq_zero_iff]
  unfold magCmpStep
  dsimp only
  rw [if_neg hnotlt]
  simp only [atL_embed a i ha, atL_embed b i hb, ok_bind, hdec1]
  by_cases h1 : a[i] < b[i]
  · rw [if_pos (decide_eq_true_eq.mpr h1)]
    simp only [negI_one, ok_bind, pure_find_eq_ok]
    rw [if_pos h1]
  · rw [if_neg (fun h => h1 (of_decide_eq_true h))]
    simp only [atL_embed b i hb, atL_embed a i ha, ok_bind, hdec2]
    by_cases h2 : b[i] < a[i]
    · rw [if_pos (decide_eq_true_eq.mpr h2)]
      simp only [ok_bind, pure_find_eq_ok]
      rw [if_neg h1, if_pos h2]
    · rw [if_neg (fun h => h2 (of_decide_eq_true h))]
      simp only [ok_bind, pure_find_eq_ok]
      rw [hbeq]
      by_cases h3 : i = 0
      · rw [if_pos (decide_eq_true_eq.mpr h3)]
        rw [if_neg h1, if_neg h2, if_pos h3]
      · rw [if_neg (fun h => h3 (of_decide_eq_true h))]
        rw [subI_ofNat_one i (Nat.pos_of_ne_zero h3) hfit, ok_bind]
        rw [if_neg h1, if_neg h2, if_neg h3]

theorem cmpAux_eq (a b : List Nat) (i : Nat) (ha : i < a.length) (hb : i < b.length) :
    cmpAux a b i =
      if a[i] < b[i] then -1 else if b[i] < a[i] then 1
      else if i = 0 then 0 else cmpAux a b (i - 1) := by
  cases i with
  | zero => simp [cmpAux, digAt_get a 0 ha, digAt_get b 0 hb]
  | succ j =>
    simp only [cmpAux]
    rw [digAt_get a (j + 1) ha, digAt_get b (j + 1) hb,
      if_neg (Nat.succ_ne_zero j), show j + 1 - 1 = j from by omega]

/-- The generated inner comparison loop computes `cmpAux`. -/
theorem magCmpLoop_eq (a b : List Nat) :
    ∀ i, i < a.length → i < b.length → FitsLen i →
      SudoRt.runLoopOn (ρ := Int) (Int.ofNat i) (i + 1)
        (magCmpStep (embed a) (embed b)) (fun _ => pure (0 : Int)) (fun r => pure r) =
        .ok (cmpAux a b i) := by
  intro i
  induction i with
  | zero =>
    intro ha hb _
    rw [runLoopOn_succ,
      magCmpStep_hit a b 0 ha hb (FitsLen.of_le fits52 (by decide)),
      cmpAux_eq a b 0 ha hb]
    by_cases h1 : a[0] < b[0]
    · simp only [if_pos h1, pure_find_eq_ok]
    · by_cases h2 : b[0] < a[0]
      · simp only [if_neg h1, if_pos h2, pure_find_eq_ok]
      · simp only [if_neg h1, if_neg h2, pure_find_eq_ok]
        simp
  | succ j ih =>
    intro ha hb hfit
    have ha' : j < a.length := by omega
    have hb' : j < b.length := by omega
    have hfit' : FitsLen j := FitsLen.of_le hfit (by omega)
    rw [runLoopOn_succ,
      magCmpStep_hit a b (j + 1) ha hb hfit,
      cmpAux_eq a b (j + 1) ha hb]
    by_cases h1 : a[j + 1] < b[j + 1]
    · simp only [if_pos h1, pure_find_eq_ok]
    · by_cases h2 : b[j + 1] < a[j + 1]
      · simp only [if_neg h1, if_pos h2, pure_find_eq_ok]
      · simp only [if_neg h1, if_neg h2, if_neg (Nat.succ_ne_zero j),
          show j + 1 - 1 = j from by omega]
        exact ih ha' hb' hfit'

/-- Emitter shape of `mag_cmp`: compare limb counts, then scan downwards. -/
def magCmp (a b : Array Int) : Except SudoRt.Trap Int :=
  do
    if decide (SudoRt.listLen a < SudoRt.listLen b) then
      do
        let r ← SudoRt.negI (1 : Int)
        pure r
    else
      do
        if decide (SudoRt.listLen b < SudoRt.listLen a) then
          pure (1 : Int)
        else
          do
            let i ← SudoRt.subI (SudoRt.listLen a) (1 : Int)
            let out ← SudoRt.runLoopOn (ρ := Int) i
              (if i < (0 : Int) then 1 else (i - (0 : Int)).natAbs + 1)
              (magCmpStep a b) (fun _ => pure (0 : Int)) (fun r => pure r)
            pure out

theorem mag_cmp_eq : Megadreifach.mag_cmp = magCmp := by
  funext a b
  unfold Megadreifach.mag_cmp magCmp
  rfl

theorem digAt_lt (xs : List Nat) (i : Nat) (hd : ∀ d ∈ xs, d < limbBase) :
    digAt xs i < limbBase := by
  by_cases hi : i < xs.length
  · rw [digAt_get xs i hi]; exact hd _ (List.getElem_mem hi)
  · rw [digAt_ge xs i (Nat.le_of_not_lt hi)]; exact limbBase_pos

/-- A lower prefix with a smaller top limb is numerically smaller. -/
theorem limb_cmp_lt (A B P α β : Nat) (hA : A < P) (hβ : α < β) :
    A + α * P < B + β * P := by
  calc
    A + α * P < P + α * P := Nat.add_lt_add_right hA _
    _ = α * P + P := by rw [Nat.add_comm]
    _ = (α + 1) * P := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ β * P := Nat.mul_le_mul_right P (by omega)
    _ ≤ B + β * P := Nat.le_add_left _ _

/-- A lower prefix with a larger top limb is numerically larger. -/
theorem limb_cmp_gt (A B P α β : Nat) (hB : B < P) (hβ : β < α) :
    B + β * P < A + α * P := by
  calc
    B + β * P < P + β * P := Nat.add_lt_add_right hB _
    _ = β * P + P := by rw [Nat.add_comm]
    _ = (β + 1) * P := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ α * P := Nat.mul_le_mul_right P (by omega)
    _ ≤ A + α * P := Nat.le_add_left _ _

/-- `cmpAux` returns `-1` exactly when the prefix value is smaller. -/
theorem cmpAux_eq_neg (a b : List Nat) (hda : ∀ d ∈ a, d < limbBase)
    (hdb : ∀ d ∈ b, d < limbBase) :
    ∀ i, i < a.length → i < b.length →
      limbVal (a.take (i + 1)) < limbVal (b.take (i + 1)) → cmpAux a b i = -1 := by
  intro i
  induction i with
  | zero =>
    intro _ _ hlt
    have hlt' : digAt a 0 < digAt b 0 := by
      rw [limbVal_take_succ_dig a 0, limbVal_take_succ_dig b 0] at hlt
      simpa using hlt
    simp [cmpAux, hlt']
  | succ i ih =>
    intro ha hb hlt
    have ha' : i < a.length := by omega
    have hb' : i < b.length := by omega
    have hlt' : limbVal (a.take (i + 1)) + digAt a (i + 1) * limbBase ^ (i + 1) <
        limbVal (b.take (i + 1)) + digAt b (i + 1) * limbBase ^ (i + 1) := by
      rwa [limbVal_take_succ_dig a (i + 1), limbVal_take_succ_dig b (i + 1)] at hlt
    have hA : limbVal (a.take (i + 1)) < limbBase ^ (i + 1) := by
      have h := limbVal_lt_pow (a.take (i + 1))
        (fun d hd => hda d (List.mem_of_mem_take hd))
      rwa [length_take_le a (i + 1) (Nat.le_of_lt ha)] at h
    have hB : limbVal (b.take (i + 1)) < limbBase ^ (i + 1) := by
      have h := limbVal_lt_pow (b.take (i + 1))
        (fun d hd => hdb d (List.mem_of_mem_take hd))
      rwa [length_take_le b (i + 1) (Nat.le_of_lt hb)] at h
    rw [cmpAux]
    by_cases h1 : digAt a (i + 1) < digAt b (i + 1)
    · simp [h1]
    · rw [if_neg h1]
      by_cases h2 : digAt b (i + 1) < digAt a (i + 1)
      · exfalso
        have hc := limb_cmp_gt (limbVal (a.take (i + 1))) (limbVal (b.take (i + 1)))
          (limbBase ^ (i + 1)) (digAt a (i + 1)) (digAt b (i + 1)) hB h2
        omega
      · have heq : digAt a (i + 1) = digAt b (i + 1) := by omega
        rw [if_neg h2]
        exact ih ha' hb' (Nat.lt_of_add_lt_add_right (by rw [heq] at hlt'; exact hlt'))

/-! ## `mag_cmp` value on canonical limbs -/

/-- `mag_cmp` reports `-1` for `natLimbs x < natLimbs y`, among eight-limb values. -/
theorem magCmp_lt_natLimbs (x y : Nat) (hxy : x < y)
    (hx : (natLimbs x).length ≤ 8) (hy : (natLimbs y).length ≤ 8) :
    magCmp (embed (natLimbs x)) (embed (natLimbs y)) = .ok (-1) := by
  have hdax := natLimbs_digits x
  have hday := natLimbs_digits y
  have hle : (natLimbs x).length ≤ (natLimbs y).length :=
    natLimbs_len_mono x y (Nat.le_of_lt hxy)
  have hy0 : 0 < y := by omega
  have hypos : 0 < (natLimbs y).length := by
    rw [natLimbs_pos y hy0]; simp
  have hxlen : FitsLen (natLimbs x).length :=
    FitsLen.of_le (by unfold FitsLen i64MaxNat; decide) hx
  unfold magCmp
  rw [listLen_embed, listLen_embed]
  by_cases hlt : (natLimbs x).length < (natLimbs y).length
  · rw [if_pos (decide_eq_true_eq.mpr ((ofNat_lt_iff _ _).mpr hlt)), negI_one, ok_bind]
    rfl
  · rw [if_neg (fun hh => hlt ((ofNat_lt_iff _ _).mp (of_decide_eq_true hh)))]
    have hle' : (natLimbs y).length ≤ (natLimbs x).length := Nat.le_of_not_lt hlt
    have heq : (natLimbs x).length = (natLimbs y).length := Nat.le_antisymm hle hle'
    rw [if_neg (fun hh => absurd ((ofNat_lt_iff _ _).mp (of_decide_eq_true hh)) (by omega))]
    rw [subI_ofNat_one (natLimbs x).length (by omega) hxlen, ok_bind]
    rw [show (if (Int.ofNat ((natLimbs x).length - 1)) < (0 : Int) then 1
        else ((Int.ofNat ((natLimbs x).length - 1)) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat ((natLimbs x).length - 1)) 0 from rfl,
      fuelDown_toZero ((natLimbs x).length - 1)]
    have htake : limbVal ((natLimbs x).take ((natLimbs x).length - 1 + 1)) <
        limbVal ((natLimbs y).take ((natLimbs x).length - 1 + 1)) := by
      rw [show (natLimbs x).length - 1 + 1 = (natLimbs x).length from by omega]
      rw [List.take_length (natLimbs x), heq, List.take_length (natLimbs y),
        limbVal_natLimbs, limbVal_natLimbs]
      exact hxy
    rw [magCmpLoop_eq (natLimbs x) (natLimbs y) ((natLimbs x).length - 1)
      (by omega) (by rw [heq]; omega) (FitsLen.of_le hxlen (by omega))]
    rw [cmpAux_eq_neg (natLimbs x) (natLimbs y) hdax hday ((natLimbs x).length - 1)
      (by omega) (by rw [heq]; omega) htake]
    rw [ok_bind]
    rfl

/-! ## Post-handler and final assembly -/

/-- Generated `after` handler of `phi_inv`: assert `n < 2^224`, emit `big_to_be n 28`. -/
def phiInvPost (σ : PhiInvSt) : Except SudoRt.Trap (Array Int) :=
  let n := σ.2.1
  let _avail := σ.2.2
  do
    let t ← Megadreifach.two224
    let c ← Megadreifach.mag_cmp n.sudo_6BigInt_5limbs t.sudo_6BigInt_5limbs
    let _a ← SudoRt.sudoAssert (decide (c < (0 : Int))) 534
    let r ← Megadreifach.big_to_be n Megadreifach.pad_block
    pure r

theorem phiInvPost_ok (deal : List Nat) (h : PhiInvWf deal) :
    phiInvPost (Int.ofNat 51, phiInvState deal 52) =
      .ok (embed (toBE 28 (lehmerRank deal))) := by
  have hx : (natLimbs (lehmerRank deal)).length ≤ 8 := by
    have h8 := accRank_limbs_le8 deal h 52 (by decide)
    rwa [accRank_full deal h.len] at h8
  have hy : (natLimbs (2 ^ 224)).length ≤ 8 :=
    natLimbs_length_le _ 8 (by change phiMax < limbBase ^ 8; exact phiMax_lt_limb8)
  unfold phiInvPost
  rw [phiInvState_full deal h]
  dsimp only
  rw [two224_spec, ok_bind, mag_cmp_eq]
  rw [show (bigOf (natLimbs (2 ^ 224))).sudo_6BigInt_5limbs = embed (natLimbs (2 ^ 224)) from rfl,
    show (bigOf (natLimbs (lehmerRank deal))).sudo_6BigInt_5limbs =
      embed (natLimbs (lehmerRank deal)) from rfl]
  rw [magCmp_lt_natLimbs (lehmerRank deal) (2 ^ 224) h.small hx hy, ok_bind]
  rw [show decide ((-1 : Int) < (0 : Int)) = true from by decide, sudoAssert_true, ok_bind,
    show Megadreifach.pad_block = (28 : Int) from rfl,
    big_to_be_pad (lehmerRank deal) h.small, ok_bind]
  rfl

set_option maxRecDepth 40000

/-- `Generated.phi_inv` refines the Lehmer rank of a 52-card deal, emitted as
    `toBE 28` (28 bytes). -/
theorem phi_inv_refines (deal : List Nat) (h : PhiInvWf deal) :
    Megadreifach.phi_inv (embed deal) = .ok (embed (toBE 28 (lehmerRank deal))) := by
  have hinit : ((0 : Int), (bigOf [], embed (List.range 52))) =
      (Int.ofNat 0, phiInvState deal 0) := by
    rw [phiInvState_zero]
    simp [bigOf, natLimbs]
  unfold Megadreifach.phi_inv
  rw [show (52 : Int) = Int.ofNat 52 from rfl, range_list_refines 52 (by decide) fits52,
    ok_bind, big_zero_spec, ok_bind]
  dsimp only
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := phiInvStep (embed deal))
    intro σ
    unfold phiInvStep
    dsimp
    rfl
  · rw [hinit]
    rw [show (0 : Int) = Int.ofNat 0 from rfl,
      show (51 : Int) = Int.ofNat 51 from rfl, fuelRange_eq]
    rw [phiInv_loop_breaks deal h]
    exact phiInvPost_ok deal h

/-- Same refinement on a `WellFormedPhiInv` array. -/
theorem phi_inv_refines_array (a : Array Int) (h : WellFormedPhiInv a) :
    Megadreifach.phi_inv a = .ok (embed (toBE 28 (lehmerRank (decode a)))) := by
  have hr := phi_inv_refines (decode a) (phiInv_decode a h)
  simpa [embed_decode a h.nn] using hr

end MegaDreifach.Link2

