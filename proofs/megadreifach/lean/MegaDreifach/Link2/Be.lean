/-
  LINK 2. `big_divmod_small` / `trim` / `big_to_be` on i64 values refine
  base-256 `toBE`. Used for the pad length field. Not `v_Hash`.
-/
import Megadreifach
import MegaDreifach.Link2.Big
import MegaDreifach.Link2.Loop

namespace MegaDreifach.Link2

theorem limb_mul_fits (r d : Nat) (hr : r < 256) (hd : d < limbBase) :
    FitsLen (r * limbBase + d) := by
  have h1 : r * limbBase ≤ 255 * limbBase := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp hr)
  have h2 : r * limbBase + d < 256 * limbBase := by
    calc
      r * limbBase + d ≤ 255 * limbBase + d := Nat.add_le_add_right h1 _
      _ < 255 * limbBase + limbBase := Nat.add_lt_add_left hd _
      _ = 256 * limbBase := by rw [← Nat.succ_mul]
  have h3 : 256 * limbBase ≤ i64MaxNat := by
    unfold i64MaxNat limbBase
    decide
  exact Nat.le_of_lt (Nat.lt_of_lt_of_le h2 h3)

theorem rem_limb_fits (r : Nat) (hr : r < 256) : FitsLen (r * limbBase) := by
  have h1 : r * limbBase ≤ 255 * limbBase := Nat.mul_le_mul_right _ (Nat.lt_succ_iff.mp hr)
  have h2 : 255 * limbBase ≤ i64MaxNat := by
    unfold i64MaxNat limbBase
    decide
  exact Nat.le_trans h1 h2

theorem fits_le (n k : Nat) (hk : k ≤ i64MaxNat) (hn : n ≤ k) : FitsLen n :=
  Nat.le_trans hn hk

theorem fits_le3 {n : Nat} (h : n ≤ 3) : FitsLen n := by
  have : 3 ≤ i64MaxNat := by unfold i64MaxNat; decide
  exact fits_le n 3 this h

theorem fits_le9 {n : Nat} (h : n ≤ 9) : FitsLen n := by
  have : 9 ≤ i64MaxNat := by unfold i64MaxNat; decide
  exact fits_le n 9 this h

theorem fits_of_lt_limb {a : Nat} (ha : a < limbBase) : FitsLen a := by
  have : limbBase ≤ i64MaxNat := by unfold i64MaxNat limbBase; decide
  exact fits_le a limbBase this (Nat.le_of_lt ha)

/-! ## Limb algebra -/

theorem dropTrail_idem : ∀ xs, dropTrail (dropTrail xs) = dropTrail xs
  | [] => rfl
  | a :: as => by
    have ih := dropTrail_idem as
    cases h : dropTrail as with
    | nil =>
      by_cases ha : a = 0
      · simp [dropTrail, h, ha]
      · simp [dropTrail, h, ha]
    | cons b bs =>
      have hdt : dropTrail (b :: bs) = b :: bs := by simpa [h] using ih
      have hdx : dropTrail (a :: as) = a :: b :: bs := by
        unfold dropTrail; rw [h]
      rw [hdx]
      show dropTrail (a :: b :: bs) = a :: b :: bs
      unfold dropTrail
      rw [hdt]

theorem dropTrail_length_le : ∀ xs, (dropTrail xs).length ≤ xs.length
  | [] => Nat.le_refl _
  | a :: as => by
    have ih := dropTrail_length_le as
    cases h : dropTrail as with
    | nil =>
      by_cases ha : a = 0 <;> simp [dropTrail, h, ha]
    | cons b bs =>
      have hlen : (b :: bs).length ≤ as.length := by simpa [h] using ih
      have hdx : dropTrail (a :: as) = a :: b :: bs := by
        unfold dropTrail; rw [h]
      rw [hdx, List.length_cons, List.length_cons]
      exact Nat.add_le_add_right hlen 1

theorem mem_dropTrail {d : Nat} : ∀ xs, d ∈ dropTrail xs → d ∈ xs
  | [], h => by simp [dropTrail] at h
  | a :: as, h => by
    cases ht : dropTrail as with
    | nil =>
      by_cases ha : a = 0
      · simp [dropTrail, ht, ha] at h
      · simp [dropTrail, ht, ha] at h
        simp [h]
    | cons b bs =>
      simp [dropTrail, ht] at h
      cases h with
      | inl heq => simp [heq]
      | inr hmem =>
        exact List.mem_cons_of_mem a (mem_dropTrail as (by simpa [ht] using hmem))

theorem limbsOfNat_len (v : Nat) : (limbsOfNat v).length ≤ 3 := by
  unfold limbsOfNat
  by_cases h0 : v = 0
  · simp [h0]
  · simp only [h0, ↓reduceIte]
    by_cases hq : v / limbBase = 0
    · simp [hq]
    · simp only [hq, ↓reduceIte]
      by_cases hq2 : (v / limbBase) / limbBase = 0
      · simp [hq2]
      · simp [hq2]

theorem limbsOfNat_digits (v : Nat) (hv : v < limbBase ^ 3) :
    ∀ d ∈ limbsOfNat v, d < limbBase := by
  intro d hd
  unfold limbsOfNat at hd
  by_cases h0 : v = 0
  · simp [h0] at hd
  · simp only [h0, ↓reduceIte] at hd
    by_cases hq : v / limbBase = 0
    · simp [hq] at hd
      rw [hd]
      exact Nat.mod_lt _ limbBase_pos
    · simp only [hq, ↓reduceIte] at hd
      by_cases hq2 : (v / limbBase) / limbBase = 0
      · simp [hq2, List.mem_cons] at hd
        cases hd with
        | inl h =>
          subst h
          exact Nat.mod_lt _ limbBase_pos
        | inr hd =>
          simp at hd
          rw [hd]
          exact Nat.mod_lt _ limbBase_pos
      · have hc : (v / limbBase) / limbBase < limbBase := by
          have hqlt : v / limbBase < limbBase ^ 2 := by
            rw [limbBase_pow3] at hv
            exact div_lt_of_lt_mul limbBase_pos hv
          rw [limbBase_pow2] at hqlt
          exact div_lt_of_lt_mul limbBase_pos hqlt
        simp [hq2, List.mem_cons] at hd
        cases hd with
        | inl h =>
          subst h
          exact Nat.mod_lt _ limbBase_pos
        | inr hd =>
          cases hd with
          | inl h =>
            subst h
            exact Nat.mod_lt _ limbBase_pos
          | inr hd =>
            simp at hd
            rw [hd]
            exact hc

/-- Long division by 256, then dropping high zeros, is `limbsOfNat (v / 256)`. -/
theorem divAll_byte (v : Nat) (hv : v < limbBase ^ 3) :
    dropTrail (divAll (limbsOfNat v)).1 = limbsOfNat (v / 256) ∧
      (divAll (limbsOfNat v)).2 = v % 256 := by
  have hdigs := limbsOfNat_digits v hv
  obtain ⟨heq, hrem, hdig, hlen⟩ := divAll_spec (limbsOfNat v) hdigs
  have hval := limbsOfNat_val v hv
  rw [hval] at heq
  have hrem_eq : (divAll (limbsOfNat v)).2 = v % 256 := by
    have hmod : v % 256 =
        (limbVal (divAll (limbsOfNat v)).1 * 256 + (divAll (limbsOfNat v)).2) % 256 := by
      rw [heq]
    rw [hmod, Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem]
  have hquot : limbVal (divAll (limbsOfNat v)).1 = v / 256 := by
    have hdiv : v / 256 =
        (limbVal (divAll (limbsOfNat v)).1 * 256 + (divAll (limbsOfNat v)).2) / 256 := by
      rw [heq]
    rw [hdiv, Nat.mul_comm, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hrem, Nat.add_zero]
  have hlen' : (dropTrail (divAll (limbsOfNat v)).1).length ≤ 3 := by
    have hle := dropTrail_length_le (divAll (limbsOfNat v)).1
    have hlenq : (divAll (limbsOfNat v)).1.length = (limbsOfNat v).length := hlen
    have hlenxs : (limbsOfNat v).length ≤ 3 := limbsOfNat_len v
    omega
  have hmem : ∀ d ∈ dropTrail (divAll (limbsOfNat v)).1, d < limbBase :=
    fun d hd => hdig d (mem_dropTrail _ hd)
  have hvl : limbVal (dropTrail (divAll (limbsOfNat v)).1) < limbBase ^ 3 := by
    rw [limbVal_dropTrail, hquot]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hv
  have htr := trimmed_eq_limbsOfNat (dropTrail (divAll (limbsOfNat v)).1)
    (dropTrail_idem _) hmem hvl hlen'
  rw [limbVal_dropTrail, hquot] at htr
  exact ⟨htr, hrem_eq⟩

/-! ## Inclusive copy (same shape as the emitted byte loops) -/

theorem drop_eq_cons {α} (xs : List α) (i : Nat) (h : i < xs.length) :
    xs.drop i = xs.get ⟨i, h⟩ :: xs.drop (i + 1) := by
  induction i generalizing xs with
  | zero =>
    match xs with
    | [] => exact (Nat.not_lt_zero _ h).elim
    | _ :: _ => rfl
  | succ i ih =>
    match xs with
    | [] => exact (Nat.not_lt_zero _ h).elim
    | x :: xs =>
      have h' : i < xs.length := Nat.lt_of_succ_lt_succ h
      have : xs.drop i = xs.get ⟨i, h'⟩ :: xs.drop (i + 1) := ih xs h'
      simpa using this

theorem toList_length (a : Array Int) : a.toList.length = a.size := rfl

theorem copy_loop_gt_after {α} (xs : Array Int) (fromV toV : Int) (acc : Array Int)
    (after : Array Int → Except SudoRt.Trap α)
    (onRet : Array Int → Except SudoRt.Trap α)
    (hgt : fromV > toV) :
    SudoRt.runLoopOn (ρ := Array Int) (fromV, acc) (fuelRange fromV toV)
        (copyStep (Array Int) xs toV)
        (fun σ => after σ.2) onRet =
      after acc := by
  rw [fuelRange_gt hgt, show 1 = 0 + 1 from rfl, runLoopOn_succ]
  rw [copyStep_gt (Array Int) xs toV fromV acc hgt]

theorem copy_loop_after {α} (xs : Array Int) (fromN toN : Nat)
    (acc : Array Int) (after : Array Int → Except SudoRt.Trap α)
    (onRet : Array Int → Except SudoRt.Trap α)
    (hfrom : fromN ≤ toN + 1)
    (hto : toN < xs.size ∨ fromN = toN + 1)
    (hfits : FitsLen xs.size)
    (hfromB : fromN ≤ xs.size) :
    SudoRt.runLoopOn (ρ := Array Int) (Int.ofNat fromN, acc)
        (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        (copyStep (Array Int) xs (Int.ofNat toN))
        (fun σ => after σ.2) onRet =
      after (Array.mk (acc.toList ++
        List.take (toN + 1 - fromN) (xs.toList.drop fromN))) := by
  generalize hrem : toN + 1 - fromN = rem
  induction rem generalizing fromN acc with
  | zero =>
    have hEq : fromN = toN + 1 := by omega
    subst hEq
    have hgt : Int.ofNat (toN + 1) > Int.ofNat toN :=
      Int.ofNat_lt.mpr (Nat.lt_succ_self _)
    rw [copy_loop_gt_after xs (Int.ofNat (toN + 1)) (Int.ofNat toN) acc after onRet hgt]
    simp [Nat.sub_self, mk_toList]
  | succ rem ih =>
    have hle : fromN ≤ toN := by omega
    have hto' : toN < xs.size := by
      cases hto with
      | inl h => exact h
      | inr h => omega
    have hidx : fromN < xs.size := Nat.lt_of_le_of_lt hle hto'
    rw [fuelRange_le hle, runLoopOn_succ,
      copyStep_hit (Array Int) xs toN fromN acc hle hidx hfits]
    by_cases heq : fromN = toN
    · rw [if_pos heq]
      have htk : List.take 1 (List.drop fromN xs.toList) =
          [xs.get ⟨fromN, hidx⟩] := by
        have : fromN < xs.toList.length := by
          rw [toList_length]; exact hidx
        rw [drop_eq_cons xs.toList fromN this]
        rfl
      have hrem1 : rem + 1 = 1 := by omega
      simp [toList_push, htk, hrem1]
      apply congrArg after
      calc acc.push (xs.get ⟨fromN, hidx⟩)
          = Array.mk (acc.push (xs.get ⟨fromN, hidx⟩)).toList := (mk_toList _).symm
        _ = Array.mk (acc.toList ++ [xs.get ⟨fromN, hidx⟩]) := by rw [toList_push]
    · have hlt : fromN < toN := Nat.lt_of_le_of_ne hle heq
      rw [if_neg heq]
      simp
      have hfuel : toN - fromN = fuelRange (Int.ofNat (fromN + 1)) (Int.ofNat toN) := by
        rw [fuelRange_le (Nat.succ_le_of_lt hlt)]
        omega
      rw [hfuel]
      have ih' := ih (fromN + 1) (acc.push (xs.get ⟨fromN, hidx⟩))
        (by omega) (Or.inl hto') (by omega) (by omega)
      rw [natCast_succ fromN, ← ofNat_eq_natCast toN]
      have hg : xs[fromN] = xs.get ⟨fromN, hidx⟩ := rfl
      rw [hg, ih']
      have hdrop : List.drop fromN xs.toList =
          xs.get ⟨fromN, hidx⟩ :: List.drop (fromN + 1) xs.toList := by
        have : fromN < xs.toList.length := by
          rw [toList_length]; exact hidx
        exact drop_eq_cons xs.toList fromN this
      rw [toList_push, hdrop]
      simp [List.take]

theorem take_map_ofNat : ∀ (n : Nat) (xs : List Nat),
    List.take n (xs.map Int.ofNat) = (List.take n xs).map Int.ofNat
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, x :: xs => congrArg (List.cons (Int.ofNat x)) (take_map_ofNat n xs)

theorem copy_prefix (xs : List Nat) (n : Nat)
    (hn : 0 < n) (hle : n ≤ xs.length) (hfits : FitsLen xs.length) :
    SudoRt.runLoopOn (Int.ofNat 0, (#[] : Array Int))
        (fuelRange (Int.ofNat 0) (Int.ofNat (n - 1)))
        (copyStep (Array Int) (embed xs) (Int.ofNat (n - 1)))
        (fun σ => (pure σ.2 : Except SudoRt.Trap (Array Int)))
        (fun r => pure r) =
      .ok (embed (xs.take n)) := by
  have hfitsA : FitsLen (embed xs).size := by rw [size_embed]; exact hfits
  have hto : n - 1 < (embed xs).size := by rw [size_embed]; omega
  have hrun := copy_loop_after (embed xs) 0 (n - 1) (#[] : Array Int)
    (fun a => (pure a : Except SudoRt.Trap (Array Int))) (fun r => pure r)
    (by omega) (Or.inl hto) hfitsA (by rw [size_embed]; omega)
  rw [hrun, toList_embed, List.drop_zero, List.nil_append, take_map_ofNat]
  rw [show n - 1 + 1 - 0 = n by omega]
  rfl

/-! ## Trim -/

/-- `n` already found from a higher limb, or `i + 1` when this limb is the high nonzero. -/
def nupdate (n d i : Nat) : Nat :=
  if n = 0 then (if d = 0 then 0 else i + 1) else n

/-- Value of the trim counter on entry to index `i` (nothing at or below `i` has been seen). -/
def foundAbove (xs : List Nat) (i : Nat) : Nat :=
  let n := (dropTrail xs).length
  if n ≤ i + 1 then 0 else n

theorem idx_lt_drop_of_ne_zero (xs : List Nat) (i : Nat)
    (hi : i < xs.length) (hne : xs[i] ≠ 0) : i < (dropTrail xs).length := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero =>
      cases h : dropTrail as with
      | nil =>
        have : a ≠ 0 := by simpa using hne
        simp [dropTrail, h, this]
      | cons _ _ =>
        simp [dropTrail, h]
    | succ j =>
      have hj : j < as.length := by
        simp at hi
        exact hi
      have hne' : as[j] ≠ 0 := by simpa using hne
      have ihj := ih j hj hne'
      cases h : dropTrail as with
      | nil => simp [h] at ihj
      | cons b bs =>
        rw [h] at ihj
        have hlen : (a :: b :: bs).length = (b :: bs).length + 1 := rfl
        rw [dropTrail, h, hlen]
        exact Nat.succ_lt_succ ihj

theorem dropTrail_zero_at (xs : List Nat) (i : Nat)
    (hi : i < xs.length) (hle : (dropTrail xs).length ≤ i) : xs[i] = 0 := by
  by_cases hz : xs[i] = 0
  · exact hz
  · exact absurd (idx_lt_drop_of_ne_zero xs i hi hz) (Nat.not_lt.mpr hle)

theorem boundary_ne_zero (xs : List Nat) (i : Nat)
    (hi : i < xs.length) (hlen : (dropTrail xs).length = i + 1) : xs[i] ≠ 0 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero =>
      intro hz
      have ha : a = 0 := by simpa using hz
      cases h : dropTrail as with
      | nil =>
        simp [dropTrail, h, ha] at hlen
      | cons b bs =>
        simp [dropTrail, h] at hlen
    | succ j =>
      have hj : j < as.length := by
        simp at hi
        exact hi
      cases h : dropTrail as with
      | nil =>
        exfalso
        by_cases ha : a = 0
        · simp [dropTrail, h, ha, List.length_nil] at hlen
        · simp [dropTrail, h, ha, List.length_singleton] at hlen
      | cons b bs =>
        have hlen' : (b :: bs).length = j + 1 := by
          have heq : (b :: bs).length + 1 = j + 2 := by
            simpa [dropTrail, h, List.length_cons] using hlen
          omega
        have ihj := ih j hj (by simpa [h] using hlen')
        simpa using ihj

theorem foundAbove_step (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    nupdate (foundAbove xs i) (xs[i]) i =
      if i = 0 then (dropTrail xs).length else foundAbove xs (i - 1) := by
  have hle_len := dropTrail_length_le xs
  unfold foundAbove nupdate
  dsimp
  by_cases htop : (dropTrail xs).length ≤ i + 1
  · rw [if_pos htop, if_pos (rfl : (0 : Nat) = 0)]
    by_cases hlo : (dropTrail xs).length ≤ i
    · have hz : xs[i] = 0 := dropTrail_zero_at xs i hi hlo
      rw [hz, if_pos rfl]
      by_cases hi0 : i = 0
      · rw [hi0] at hlo ⊢
        have : (dropTrail xs).length = 0 := Nat.eq_zero_of_le_zero hlo
        simp [this, foundAbove]
      · rw [if_neg hi0]
        have : (dropTrail xs).length ≤ (i - 1) + 1 := by omega
        simp [foundAbove, this]
    · have heq : (dropTrail xs).length = i + 1 := by omega
      have hnz : xs[i] ≠ 0 := boundary_ne_zero xs i hi heq
      rw [if_neg hnz]
      by_cases hi0 : i = 0
      · simp [hi0, heq]
      · rw [if_neg hi0, heq]
        have : ¬ i + 1 ≤ (i - 1) + 1 := by omega
        simp [foundAbove, this]
  · have hpos : (dropTrail xs).length ≠ 0 := by omega
    rw [if_neg htop, if_neg hpos]
    by_cases hi0 : i = 0
    · rw [if_pos hi0]
    · rw [if_neg hi0]
      have : ¬ (dropTrail xs).length ≤ (i - 1) + 1 := by omega
      simp [foundAbove, this]

theorem foundAbove_top (xs : List Nat) (h : 0 < xs.length) :
    foundAbove xs (xs.length - 1) = 0 := by
  have hle := dropTrail_length_le xs
  unfold foundAbove
  have : (dropTrail xs).length ≤ (xs.length - 1) + 1 := by omega
  rw [if_pos this]

/-- One iteration of emitted `trim`'s descending scan. -/
def trimStep (limbs : Array Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) (Array Int)) :=
  let i := σ.1
  let n := σ.2
  do
    if i < (0 : Int) then
      pure (SudoRt.Flow.brk (ρ := Array Int) (i, n))
    else
      match ← ((do
        let flag ← (if SudoRt.SEq.beq n (0 : Int) then do
          let d ← SudoRt.atL limbs i
          pure (!(SudoRt.SEq.beq d (0 : Int)))
        else
          pure false)
        if flag then do
          let n' ← SudoRt.addI i (1 : Int)
          pure (SudoRt.Flow.cont (ρ := Array Int) n')
        else
          pure (SudoRt.Flow.cont (ρ := Array Int) n)
      ) : Except SudoRt.Trap (SudoRt.Flow Int (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
      | .cont fs => do
          if i == (0 : Int) then
            pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
          else do
            let i' ← SudoRt.subI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

theorem trimStep_hit (xs : List Nat) (i n : Nat)
    (hi : i < xs.length) (hfits : FitsLen xs.length) :
    trimStep (embed xs) (Int.ofNat i, Int.ofNat n) =
      if i = 0 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, Int.ofNat (nupdate n (xs[i]) i)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i - 1), Int.ofNat (nupdate n (xs[i]) i))) := by
  unfold trimStep
  dsimp
  have hngt : ¬ (i : Int) < 0 := Int.not_lt.mpr (Int.ofNat_zero_le i)
  rw [if_neg hngt]
  by_cases hn0 : n = 0
  · subst hn0
    rw [← ofNat_eq_natCast 0, sEq_ofNat_zero,
      show decide ((0 : Nat) = 0) = true from rfl, if_pos rfl]
    rw [show (i : Int) = Int.ofNat i from rfl, atL_embed xs i hi, ok_bind]
    by_cases hd0 : xs[i] = 0
    · rw [sEq_ofNat_zero, hd0, show decide ((0 : Nat) = 0) = true from rfl]
      have hnot : (!(true : Bool)) = false := rfl
      rw [hnot, show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind,
        if_neg (by decide : ¬ ((false : Bool) = true))]
      erw [ok_bind]
      dsimp
      rw [ite_int_beq]
      by_cases hi0 : i = 0
      · simp [hi0, nupdate, hd0]
        rfl
      · have hneI : ¬ (i : Int) = 0 := fun h => hi0 (Int.ofNat.inj h)
        have hsub := subI_ofNat_one i (Nat.pos_of_ne_zero hi0)
          (FitsLen.of_le hfits (Nat.le_of_lt hi))
        rw [ofNat_eq_natCast i] at hsub
        rw [if_neg hneI, hsub, ok_bind, if_neg hi0]
        simp [nupdate, hd0]
        rfl
    · rw [sEq_ofNat_zero, decide_eq_false_iff_not.mpr hd0]
      have hnot : (!(false : Bool)) = true := rfl
      rw [hnot, show (pure true : Except SudoRt.Trap Bool) = .ok true from rfl, ok_bind,
        if_pos rfl]
      have hadd := addI_ofNat_one i (FitsLen.succ_le hi hfits)
      rw [hadd, ok_bind]
      erw [ok_bind]
      dsimp
      rw [ite_int_beq]
      by_cases hi0 : i = 0
      · have hd0' : xs[0] ≠ 0 := by simpa [hi0] using hd0
        simp [hi0, nupdate, hd0']
        rfl
      · have hneI : ¬ (i : Int) = 0 := fun h => hi0 (Int.ofNat.inj h)
        have hsub := subI_ofNat_one i (Nat.pos_of_ne_zero hi0)
          (FitsLen.of_le hfits (Nat.le_of_lt hi))
        rw [ofNat_eq_natCast i] at hsub
        rw [if_neg hneI, hsub, ok_bind, if_neg hi0]
        simp [nupdate, hd0]
        rfl
  · rw [← ofNat_eq_natCast n, sEq_ofNat_zero, decide_eq_false_iff_not.mpr hn0,
      if_neg (by decide : ¬ ((false : Bool) = true))]
    erw [ok_bind]
    dsimp
    rw [ite_int_beq]
    by_cases hi0 : i = 0
    · simp [hi0, nupdate, hn0]
      rfl
    · have hneI : ¬ (i : Int) = 0 := fun h => hi0 (Int.ofNat.inj h)
      have hsub := subI_ofNat_one i (Nat.pos_of_ne_zero hi0)
        (FitsLen.of_le hfits (Nat.le_of_lt hi))
      rw [ofNat_eq_natCast i] at hsub
      rw [if_neg hneI, hsub, ok_bind, if_neg hi0]
      simp [nupdate, hn0]
      rfl

theorem trim_finish (xs : List Nat) (n : Nat)
    (hn : n = (dropTrail xs).length) (hfits : FitsLen xs.length) :
    (do
      let toV ← SudoRt.subI (Int.ofNat n) (1 : Int)
      let fuel := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
      let out ← SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel
        (copyStep (Array Int) (embed xs) toV)
        (fun σ => (pure σ.2 : Except SudoRt.Trap (Array Int)))
        (fun r => pure r)
      pure out) = .ok (embed (dropTrail xs)) := by
  rw [hn]
  by_cases h0 : (dropTrail xs).length = 0
  · have hempty : dropTrail xs = [] := List.eq_nil_of_length_eq_zero h0
    rw [h0, show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
    have hgt : (0 : Int) > (-1 : Int) := by decide
    rw [fuelRange_eq, fuelRange_gt hgt, show 1 = 0 + 1 from rfl, except_bind_pure,
      runLoopOn_succ, copyStep_gt (Array Int) (embed xs) (-1) 0 (#[] : Array Int) hgt]
    rw [hempty, embed_nil]
    rfl
  · have hpos : 0 < (dropTrail xs).length := Nat.pos_of_ne_zero h0
    have hle : (dropTrail xs).length ≤ xs.length := dropTrail_length_le xs
    rw [subI_ofNat_one _ hpos (FitsLen.of_le hfits hle), ok_bind, fuelRange_eq,
      show (0 : Int) = Int.ofNat 0 from rfl, except_bind_pure,
      copy_prefix xs (dropTrail xs).length hpos hle hfits, dropTrail_prefix]

private theorem trim_after (xs : List Nat) (n : Nat)
    (hn : n = (dropTrail xs).length) (hfits : FitsLen xs.length) :
    (do
      let toV ← SudoRt.subI (Int.ofNat n) 1
      let fuel := if (0 : Int) > toV then 1 else (toV - 0).natAbs + 1
      let copied ← SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel
        (copyStep (Array Int) (embed xs) toV)
        (fun σ => (pure σ.2 : Except SudoRt.Trap (Array Int)))
        (fun r => pure r)
      pure copied) = .ok (embed (dropTrail xs)) :=
  trim_finish xs n hn hfits

/-- Emitted copy stepper, whose `do` nests one bind deeper than `copyStep`. -/
theorem genCopy_eq (xs : Array Int) (toV : Int) (σ : Int × Array Int) :
    (if σ.fst > toV then pure (SudoRt.Flow.brk (ρ := Array Int) (σ.fst, σ.snd))
      else do
        let lift ←
          ((do
            let t ← SudoRt.atL xs σ.fst
            pure (SudoRt.Flow.cont (ρ := Array Int) (SudoRt.appendL σ.snd t).fst)) :
            Except SudoRt.Trap (SudoRt.Flow (Array Int) (Array Int)))
        match lift with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
        | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (σ.fst, fs))
        | .cont fs =>
          if (σ.fst == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array Int) (σ.fst, fs))
          else do
            let i' ← SudoRt.addI σ.fst 1
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))) =
      copyStep (Array Int) xs toV σ := by
  unfold copyStep
  by_cases hgt : σ.fst > toV
  · rw [if_pos hgt, if_pos hgt]
  · rw [if_neg hgt, if_neg hgt]
    cases hAt : SudoRt.atL xs σ.fst with
    | error e => simp [hAt]
    | ok t => simp [hAt, ok_bind]

/-- `trim (embed xs)` keeps the prefix through the highest nonzero limb. -/
theorem trim_embed (xs : List Nat) (hfits : FitsLen xs.length) :
    Megadreifach.trim (embed xs) = .ok (embed (dropTrail xs)) := by
  unfold Megadreifach.trim
  by_cases hnil : xs = []
  · subst hnil
    rw [listLen_embed, show ([] : List Nat).length = 0 from rfl,
      show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
    dsimp
    rw [show 1 = 0 + 1 from rfl, except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise (step' := trimStep (embed []))
      intro σ
      unfold trimStep
      dsimp
      rfl
    rw [runLoopOn_succ]
    have hbrk : trimStep (embed []) ((-1 : Int), 0) =
        .ok (SudoRt.Flow.brk ((-1 : Int), 0)) := by
      unfold trimStep
      rw [if_pos (by decide : (-1 : Int) < 0)]
      rfl
    rw [hbrk]
    exact trim_after [] 0 (by simp [dropTrail]) (by simpa using FitsLen.zero)
  · have hpos : 0 < xs.length :=
      Nat.pos_of_ne_zero (fun h => hnil (List.eq_nil_of_length_eq_zero h))
    rw [listLen_embed, subI_ofNat_one xs.length hpos hfits, ok_bind]
    dsimp
    rw [fuelDown_eq, show (0 : Int) = Int.ofNat 0 from rfl, except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise (step' := trimStep (embed xs))
      intro σ
      unfold trimStep
      dsimp
      rfl
    have htop := foundAbove_top xs hpos
    rw [← ofNat_eq_natCast (xs.length - 1)]
    have hstate :
        (Int.ofNat (xs.length - 1), Int.ofNat 0) =
          (Int.ofNat (xs.length - 1),
            Int.ofNat (foundAbove xs (xs.length - 1))) := by
      simp [htop]
    rw [hstate]
    apply chain_down
      (f := fun i => Int.ofNat (foundAbove xs i))
      (g := fun i =>
        Int.ofNat (if i = 0 then (dropTrail xs).length else foundAbove xs (i - 1)))
      (fromN := xs.length - 1)
      (goal := .ok (embed (dropTrail xs)))
    · intro i hiLe
      have hi : i < xs.length := by omega
      rw [trimStep_hit xs i (foundAbove xs i) hi hfits, foundAbove_step xs i hi]
    · intro i hp _
      dsimp
      rw [if_neg (Nat.ne_of_gt hp)]
    · dsimp
      rw [← ofNat_eq_natCast (dropTrail xs).length]
      by_cases h0 : (dropTrail xs).length = 0
      · have hempty : dropTrail xs = [] := List.eq_nil_of_length_eq_zero h0
        rw [h0, show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
        have hgt : (0 : Int) > (-1 : Int) := by decide
        rw [fuelRange_eq, fuelRange_gt hgt, show 1 = 0 + 1 from rfl, except_bind_pure]
        apply Eq.trans
        · apply runLoopOn_step_pointwise
            (step' := copyStep (Array Int) (embed xs) (-1))
          intro σ
          unfold copyStep
          by_cases hgtσ : σ.fst > (-1)
          · rw [if_pos hgtσ, if_pos hgtσ]
          · rw [if_neg hgtσ, if_neg hgtσ]
            cases hAt : SudoRt.atL (embed xs) σ.fst with
            | error e => simp [hAt]
            | ok t => simp [hAt, ok_bind]
        rw [runLoopOn_succ,
          copyStep_gt (Array Int) (embed xs) (-1) 0 (#[] : Array Int) hgt,
          hempty, embed_nil]
        rfl
      · have hposN : 0 < (dropTrail xs).length := Nat.pos_of_ne_zero h0
        have hleN : (dropTrail xs).length ≤ xs.length := dropTrail_length_le xs
        rw [subI_ofNat_one _ hposN (FitsLen.of_le hfits hleN), ok_bind, fuelRange_eq,
          show (0 : Int) = Int.ofNat 0 from rfl, except_bind_pure]
        apply Eq.trans
        · apply runLoopOn_step_pointwise
            (step' := copyStep (Array Int) (embed xs)
              (Int.ofNat ((dropTrail xs).length - 1)))
          intro σ
          unfold copyStep
          by_cases hgtσ : σ.fst > Int.ofNat ((dropTrail xs).length - 1)
          · rw [if_pos hgtσ, if_pos hgtσ]
          · rw [if_neg hgtσ, if_neg hgtσ]
            cases hAt : SudoRt.atL (embed xs) σ.fst with
            | error e => simp [hAt]
            | ok t => simp [hAt, ok_bind]
        rw [copy_prefix xs (dropTrail xs).length hposN hleN hfits, dropTrail_prefix]

theorem make_big_false (xs : List Nat) (hfits : FitsLen xs.length) :
    Megadreifach.make_big false (embed xs) = .ok (bigOf (dropTrail xs)) := by
  unfold Megadreifach.make_big
  rw [trim_embed xs hfits, ok_bind]
  dsimp
  by_cases h0 : dropTrail xs = []
  · rw [h0, listLen_embed, show ([] : List Nat).length = 0 from rfl, sEq_ofNat_zero,
      show decide ((0 : Nat) = 0) = true from rfl, if_pos rfl, big_zero_spec]
    rfl
  · have hpos : (dropTrail xs).length ≠ 0 :=
      fun h => h0 (List.eq_nil_of_length_eq_zero h)
    rw [listLen_embed, sEq_ofNat_zero, decide_eq_false_iff_not.mpr hpos,
      if_neg (by decide : ¬ ((false : Bool) = true))]
    rfl

theorem divmod_nil :
    Megadreifach.big_divmod_small (bigOf []) (256 : Int) =
      .ok (bigOf [], (0 : Int)) := by
  unfold Megadreifach.big_divmod_small
  dsimp [bigOf]
  have hlt : decide ((256 : Int) < Megadreifach.limb_base) = true := by
    simp [limb_base_eq]
    decide
  rw [hlt, show (pure true : Except SudoRt.Trap Bool) = .ok true from rfl, ok_bind,
    sudoAssert_true, ok_bind, listLen_embed,
    show ([] : List Nat).length = 0 from rfl, sEq_ofNat_zero,
    show decide ((0 : Nat) = 0) = true from rfl, if_pos rfl, big_zero_spec]
  rfl

theorem drop_singleton_limbs (q : Nat) (hq : q < limbBase) :
    dropTrail [q] = limbsOfNat q := by
  by_cases h : q = 0
  · simp [h, dropTrail, limbsOfNat]
  · simp [dropTrail, limbsOfNat, h, Nat.div_eq_of_lt hq, Nat.mod_eq_of_lt hq]

/-- One descending step of `big_divmod_small` by 256. -/
def divmodStep (limbs : Array Int) (σ : Int × (Array Int × Int)) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × (Array Int × Int)) (Megadreifach.BigInt × Int)) :=
  if σ.1 < 0 then
    pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (σ.1, σ.2.1, σ.2.2))
  else do
    let lift ←
      ((do
        let x ← SudoRt.mulI σ.2.2 Megadreifach.limb_base
        let d ← SudoRt.atL limbs σ.1
        let cur ← SudoRt.addI x d
        let qv ← SudoRt.divI cur (256 : Int)
        let q ← SudoRt.putL σ.2.1 σ.1 qv
        let r ← SudoRt.modI cur (256 : Int)
        pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt × Int) (q, r))) :
        Except SudoRt.Trap
          (SudoRt.Flow (Array Int × Int) (Megadreifach.BigInt × Int)))
    match lift with
    | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt × Int) r)
    | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (σ.1, fs))
    | .cont fs =>
      if (σ.1 == 0) = true then
        pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt × Int) (σ.1, fs))
      else do
        let i' ← SudoRt.subI σ.1 1
        pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt × Int) (i', fs))

theorem embed_set1 (q : Nat) {h : 0 < (Array.mkArray 1 (0 : Int)).size} :
    (Array.mkArray 1 (0 : Int)).set ⟨0, h⟩ (Int.ofNat q) = embed [q] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate, List.set_cons_zero]

theorem embed_quot (a : Nat) {h : 0 < (Array.mkArray 1 (0 : Int)).size} :
    (Array.mkArray 1 (0 : Int)).set ⟨0, h⟩ ((a : Int) / 256) = embed [a / 256] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate, List.set_cons_zero,
    Int.ofNat_ediv]

theorem divmod_one (a : Nat) (ha : a < limbBase) (hne : a ≠ 0) :
    Megadreifach.big_divmod_small (bigOf [a]) (256 : Int) =
      .ok (bigOf (limbsOfNat (a / 256)), Int.ofNat (a % 256)) := by
  have hfits : FitsLen ([a] : List Nat).length := by
    rw [show ([a] : List Nat).length = 1 from rfl]
    exact FitsLen.one
  unfold Megadreifach.big_divmod_small
  dsimp [bigOf]
  have hlt : decide ((256 : Int) < Megadreifach.limb_base) = true := by
    simp [limb_base_eq]
    decide
  rw [hlt, show (pure true : Except SudoRt.Trap Bool) = .ok true from rfl, ok_bind,
    sudoAssert_true, ok_bind, listLen_embed,
    show ([a] : List Nat).length = 1 from rfl, sEq_ofNat_zero,
    decide_eq_false_iff_not.mpr (by decide : (1 : Nat) ≠ 0),
    if_neg (by decide : ¬ ((false : Bool) = true)),
    filledL_ofNat, ok_bind, subI_ofNat_one 1 (by decide) FitsLen.one, ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := divmodStep (embed [a]))
    intro σ
    unfold divmodStep
    rfl
  rw [show 1 = 0 + 1 from rfl, runLoopOn_succ]
  have hsz : 0 < (Array.mkArray 1 (Int.ofNat 0)).size := by
    rw [Array.size_mkArray]
    decide
  have hstep :
      divmodStep (embed [a]) (Int.ofNat 0, Array.mkArray 1 (Int.ofNat 0), Int.ofNat 0) =
        .ok (SudoRt.Flow.brk (Int.ofNat 0,
          (Array.mkArray 1 (Int.ofNat 0)).set ⟨0, hsz⟩ (Int.ofNat (a / 256)),
          Int.ofNat (a % 256))) := by
    unfold divmodStep
    dsimp
    rw [limb_base_eq, ← ofNat_eq_natCast limbBase,
      show (0 : Int) = Int.ofNat 0 from rfl,
      mulI_ofNat 0 limbBase (rem_limb_fits 0 (by decide)), ok_bind]
    have hidx : 0 < ([a] : List Nat).length := by
      rw [List.length_cons, List.length_nil]
      decide
    rw [atL_embed [a] 0 hidx, ok_bind]
    have hhead : ([a] : List Nat)[0]'hidx = a := rfl
    have hcur : FitsLen (0 * limbBase + a) := limb_mul_fits 0 a (by decide) ha
    rw [hhead, addI_ofNat (0 * limbBase) a hcur, ok_bind]
    rw [show (256 : Int) = Int.ofNat 256 from rfl,
      divI_ofNat (0 * limbBase + a) (by decide), ok_bind]
    rw [putL_ofNat (Array.mkArray 1 (Int.ofNat 0)) 0 _ hsz, ok_bind,
      modI_ofNat (0 * limbBase + a) (by decide), ok_bind]
    simp [Nat.zero_mul, Nat.zero_add]
    rfl
  have hmk : Array.mkArray (0 + 1) (Int.ofNat 0) = Array.mkArray 1 (Int.ofNat 0) := by
    simp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, hmk, hstep]
  dsimp
  erw [embed_quot a]
  rw [make_big_false [a / 256] (by
    rw [show ([a / 256] : List Nat).length = 1 from rfl]
    exact FitsLen.one), ok_bind,
    drop_singleton_limbs (a / 256) (Nat.lt_of_le_of_lt (Nat.div_le_self a 256) ha)]
  rfl

theorem divmodStep_at (xs : List Nat) (qArr : Array Int) (i r : Nat)
    (hi : i < xs.length) (hr : r < 256) (hx : xs[i] < limbBase)
    (hsz : i < qArr.size) (hfiti : FitsLen i) :
    divmodStep (embed xs) (Int.ofNat i, qArr, Int.ofNat r) =
      (let cur := r * limbBase + xs[i]
      let q' := qArr.set ⟨i, hsz⟩ (Int.ofNat (cur / 256))
      let r' := Int.ofNat (cur % 256)
      if i = 0 then
        .ok (SudoRt.Flow.brk (Int.ofNat 0, q', r'))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i - 1), q', r'))) := by
  unfold divmodStep
  dsimp
  rw [if_neg (Int.not_lt.mpr (Int.ofNat_zero_le i))]
  rw [limb_base_eq, ← ofNat_eq_natCast limbBase, ← ofNat_eq_natCast r,
    mulI_ofNat r limbBase (rem_limb_fits r hr), ok_bind,
    ← ofNat_eq_natCast i, atL_embed xs i hi, ok_bind]
  have hcur : FitsLen (r * limbBase + xs[i]) := limb_mul_fits r (xs[i]) hr hx
  rw [addI_ofNat (r * limbBase) (xs[i]) hcur, ok_bind,
    show (256 : Int) = Int.ofNat 256 from rfl,
    divI_ofNat (r * limbBase + xs[i]) (by decide), ok_bind,
    putL_ofNat qArr i _ hsz, ok_bind,
    modI_ofNat (r * limbBase + xs[i]) (by decide), ok_bind]
  erw [ok_bind]
  dsimp
  by_cases hi0 : i = 0
  · simp [hi0]
    rfl
  · have hneI : ¬ (i : Int) = 0 := fun h => hi0 (Int.ofNat.inj h)
    have hsub := subI_ofNat_one i (Nat.pos_of_ne_zero hi0) hfiti
    rw [ofNat_eq_natCast i] at hsub
    rw [ite_int_beq, if_neg hneI, hsub, ok_bind, if_neg hi0]
    rfl

private theorem runLoopOn_one {σ ρ α} (s0 : σ)
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

private theorem len2 (a b : Nat) : 1 < ([a, b] : List Nat).length := by
  have : ([a, b] : List Nat).length = 2 := by simp
  rw [this]
  decide

private theorem len0 (a b : Nat) : 0 < ([a, b] : List Nat).length := by
  have : ([a, b] : List Nat).length = 2 := by simp
  rw [this]
  decide

private theorem digit0 (a b : Nat) : ([a, b] : List Nat)[0]'(len0 a b) = a := rfl

private theorem digit1 (a b : Nat) : ([a, b] : List Nat)[1]'(len2 a b) = b := rfl

theorem embed_q2 (a b : Nat)
    {h1 : 1 < (Array.mkArray 2 (0 : Int)).size}
    {h0 : 0 <
      ((Array.mkArray 2 (0 : Int)).set ⟨1, h1⟩
        ((0 * (limbBase : Int) + (b : Int)) / 256)).size} :
    (((Array.mkArray 2 (0 : Int)).set ⟨1, h1⟩
        ((0 * (limbBase : Int) + (b : Int)) / 256)).set ⟨0, h0⟩
        (((b : Int) % 256 * (limbBase : Int) + (a : Int)) / 256)) =
      embed [((b % 256) * limbBase + a) / 256, (0 * limbBase + b) / 256] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate,
    List.set_cons_zero, List.set_cons_succ, ← Int.ofNat_ediv, ← Int.ofNat_emod,
    ← Int.natCast_mul, ← Int.natCast_add, Nat.zero_mul, Nat.zero_add]
  refine ⟨?_, ?_⟩
  · erw [← Int.ofNat_emod b 256, ← Int.natCast_mul, ← Int.natCast_add, ← Int.ofNat_ediv]
  · erw [← Int.ofNat_ediv b 256]

theorem rem_q2 (a b : Nat) :
    ((b : Int) % 256 * (limbBase : Int) + (a : Int)) % 256 =
      (((b % 256) * limbBase + a) % 256 : Int) := by
  simp [← Int.ofNat_emod, ← Int.natCast_mul, ← Int.natCast_add, Nat.zero_mul]

theorem divmod_two (a b : Nat) (ha : a < limbBase) (hb : b < limbBase) :
    Megadreifach.big_divmod_small (bigOf [a, b]) (256 : Int) =
      .ok (bigOf (dropTrail (divAll [a, b]).1), ((divAll [a, b]).2 : Int)) := by
  unfold Megadreifach.big_divmod_small
  dsimp [bigOf]
  have hlt : decide ((256 : Int) < Megadreifach.limb_base) = true := by
    simp [limb_base_eq]; decide
  rw [hlt, show (pure true : Except SudoRt.Trap Bool) = .ok true from rfl, ok_bind,
    sudoAssert_true, ok_bind, listLen_embed,
    show ([a, b] : List Nat).length = 2 from rfl, sEq_ofNat_zero,
    decide_eq_false_iff_not.mpr (by decide : (2 : Nat) ≠ 0),
    if_neg (by decide : ¬ ((false : Bool) = true)),
    filledL_ofNat, ok_bind, subI_ofNat_one 2 (by decide) (fits_le3 (by decide)), ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := divmodStep (embed [a, b]))
    intro σ
    unfold divmodStep
    rfl
  -- fuel is the literal 2 when the start index is 1
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
  have hsz1 : 1 < (Array.mkArray 2 (Int.ofNat 0)).size := by
    rw [Array.size_mkArray]; decide
  have h1 := divmodStep_at [a, b] (Array.mkArray 2 (Int.ofNat 0)) 1 0
    (len2 a b) (by decide) (by rw [digit1]; exact hb) hsz1 FitsLen.one
  have hmk : Array.mkArray (1 + 1) (Int.ofNat 0) = Array.mkArray 2 (Int.ofNat 0) := by simp
  rw [show (0 : Int) = Int.ofNat 0 from rfl]
  rw [show (1 : Int) = Int.ofNat 1 from rfl]
  rw [hmk]
  rw [h1]
  simp only [(by decide : (1 = 0) = False), if_false]
  rw [runLoopOn_one]
  rw [show (1 : Nat) - 1 = 0 from rfl, digit1]
  let hq :=
    (Array.mkArray 2 (Int.ofNat 0)).set ⟨1, hsz1⟩ (Int.ofNat ((0 * limbBase + b) / 256))
  have hsz0 : 0 < hq.size := by
    dsimp [hq]
    rw [Array.size_set, Array.size_mkArray]
    decide
  have hr1 : (0 * limbBase + b) % 256 < 256 := Nat.mod_lt _ (by decide)
  have h0 := divmodStep_at [a, b] hq 0 ((0 * limbBase + b) % 256)
    (len0 a b) hr1 (by rw [digit0]; exact ha) hsz0 FitsLen.zero
  rw [h0]
  simp [digit0]
  erw [embed_q2 a b, rem_q2 a b]
  rw [make_big_false [((b % 256) * limbBase + a) / 256, (0 * limbBase + b) / 256]
      (fits_le3 (by simp [List.length_cons, List.length_nil])), map_ok]
  simp [divAll, Nat.zero_mul, Nat.zero_add]
  rfl

private theorem runLoopOn_succ_fuel {σ ρ α} (k : Nat) (s0 : σ)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn s0 (k + 1) step after onRet =
      match step s0 with
      | .error e => .error e
      | .ok (.ret r) => onRet r
      | .ok (.brk s) => after s
      | .ok (.cont s) => SudoRt.runLoopOn s k step after onRet :=
  runLoopOn_succ s0 k step after onRet

private theorem runLoopOn_three {σ ρ α} (s0 : σ)
    (step : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after : σ → Except SudoRt.Trap α)
    (onRet : ρ → Except SudoRt.Trap α) :
    SudoRt.runLoopOn s0 3 step after onRet =
      match step s0 with
      | .error e => .error e
      | .ok (.ret r) => onRet r
      | .ok (.brk s) => after s
      | .ok (.cont s) => SudoRt.runLoopOn s 2 step after onRet := by
  rw [show (3 : Nat) = 2 + 1 from rfl]
  exact runLoopOn_succ s0 2 step after onRet

private theorem runLoopOn_two {σ ρ α} (s0 : σ)
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

private theorem len3 (a b c : Nat) : 2 < ([a, b, c] : List Nat).length := by
  have : ([a, b, c] : List Nat).length = 3 := by simp
  rw [this]; decide

private theorem len3_1 (a b c : Nat) : 1 < ([a, b, c] : List Nat).length := by
  have : ([a, b, c] : List Nat).length = 3 := by simp
  rw [this]; decide

private theorem len3_0 (a b c : Nat) : 0 < ([a, b, c] : List Nat).length := by
  have : ([a, b, c] : List Nat).length = 3 := by simp
  rw [this]; decide

private theorem dig2 (a b c : Nat) : ([a, b, c] : List Nat)[2]'(len3 a b c) = c := rfl
private theorem dig1 (a b c : Nat) : ([a, b, c] : List Nat)[1]'(len3_1 a b c) = b := rfl
private theorem dig0 (a b c : Nat) : ([a, b, c] : List Nat)[0]'(len3_0 a b c) = a := rfl

theorem embed_q3 (a b c : Nat)
    {h2 : 2 < (Array.mkArray 3 (0 : Int)).size}
    {h1 : 1 < ((Array.mkArray 3 (0 : Int)).set ⟨2, h2⟩
        (Int.ofNat ((0 * limbBase + c) / 256))).size}
    {h0 : 0 < (((Array.mkArray 3 (0 : Int)).set ⟨2, h2⟩
        (Int.ofNat ((0 * limbBase + c) / 256))).set ⟨1, h1⟩
        (Int.ofNat ((((0 * limbBase + c) % 256) * limbBase + b) / 256))).size} :
    ((((Array.mkArray 3 (0 : Int)).set ⟨2, h2⟩
        (Int.ofNat ((0 * limbBase + c) / 256))).set ⟨1, h1⟩
        (Int.ofNat ((((0 * limbBase + c) % 256) * limbBase + b) / 256))).set ⟨0, h0⟩
        (((((c : Int) % 256 * (limbBase : Int) + (b : Int)) % 256) * (limbBase : Int) + (a : Int)) / 256)) =
      embed (divAll [a, b, c]).1 := by
  apply Array.ext'
  simp [divAll, embed, Array.toList_set, Array.toList_mkArray, List.replicate,
    List.set_cons_zero, List.set_cons_succ, ← Int.ofNat_ediv, ← Int.ofNat_emod,
    ← Int.natCast_mul, ← Int.natCast_add, Nat.zero_mul, Nat.zero_add]
  erw [← Int.ofNat_ediv (((c % 256) * limbBase + b) % 256 * limbBase + a) 256]

theorem rem_q3 (a b c : Nat) :
    (((((c : Int) % 256 * (limbBase : Int) + (b : Int)) % 256) * (limbBase : Int) + (a : Int)) % 256) =
      ((divAll [a, b, c]).2 : Int) := by
  simp [divAll, Nat.zero_mul, Nat.zero_add, ← Int.ofNat_emod, ← Int.natCast_mul, ← Int.natCast_add]
  erw [← Int.ofNat_emod (((c % 256) * limbBase + b) % 256 * limbBase + a) 256]

/-- Three little-endian limbs. The emitted quotient is `divAll`. -/
theorem divmod_three (a b c : Nat) (ha : a < limbBase) (hb : b < limbBase) (hc : c < limbBase) :
    Megadreifach.big_divmod_small (bigOf [a, b, c]) (256 : Int) =
      .ok (bigOf (dropTrail (divAll [a, b, c]).1), ((divAll [a, b, c]).2 : Int)) := by
  unfold Megadreifach.big_divmod_small
  dsimp [bigOf]
  have hlt : decide ((256 : Int) < Megadreifach.limb_base) = true := by
    simp [limb_base_eq]; decide
  rw [hlt, show (pure true : Except SudoRt.Trap Bool) = .ok true from rfl, ok_bind,
    sudoAssert_true, ok_bind, listLen_embed,
    show ([a, b, c] : List Nat).length = 3 from rfl, sEq_ofNat_zero,
    decide_eq_false_iff_not.mpr (by decide : (3 : Nat) ≠ 0),
    if_neg (by decide : ¬ ((false : Bool) = true)),
    filledL_ofNat, ok_bind, subI_ofNat_one 3 (by decide) (fits_le3 (by decide)), ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := divmodStep (embed [a, b, c]))
    intro σ
    unfold divmodStep
    rfl
  rw [runLoopOn_three]
  have hsz2 : 2 < (Array.mkArray 3 (Int.ofNat 0)).size := by
    rw [Array.size_mkArray]; decide
  have h2 := divmodStep_at [a, b, c] (Array.mkArray 3 (Int.ofNat 0)) 2 0
    (len3 a b c) (by decide) (by rw [dig2]; exact hc) hsz2 (fits_le3 (by decide))
  have hmk : Array.mkArray (2 + 1) (Int.ofNat 0) = Array.mkArray 3 (Int.ofNat 0) := by simp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, show (2 : Int) = Int.ofNat 2 from rfl, hmk, h2]
  simp only [(by decide : (2 = 0) = False), if_false, dig2]
  rw [show (2 : Nat) - 1 = 1 from rfl, runLoopOn_two]
  let q2 :=
    (Array.mkArray 3 (Int.ofNat 0)).set ⟨2, hsz2⟩ (Int.ofNat ((0 * limbBase + c) / 256))
  have hsz1 : 1 < q2.size := by
    dsimp [q2]; rw [Array.size_set, Array.size_mkArray]; decide
  have hr2 : (0 * limbBase + c) % 256 < 256 := Nat.mod_lt _ (by decide)
  have h1 := divmodStep_at [a, b, c] q2 1 ((0 * limbBase + c) % 256)
    (len3_1 a b c) hr2 (by rw [dig1]; exact hb) hsz1 FitsLen.one
  rw [show ((Array.mkArray 3 (Int.ofNat 0)).set ⟨2, hsz2⟩
      (Int.ofNat ((0 * limbBase + c) / 256))) = q2 from rfl]
  rw [h1]
  simp only [(by decide : (1 = 0) = False), if_false, dig1]
  rw [show (1 : Nat) - 1 = 0 from rfl, runLoopOn_one]
  let q1 := q2.set ⟨1, hsz1⟩
    (Int.ofNat ((((0 * limbBase + c) % 256) * limbBase + b) / 256))
  have hsz0 : 0 < q1.size := by
    dsimp [q1, q2]; rw [Array.size_set, Array.size_set, Array.size_mkArray]; decide
  have hr1 : (((0 * limbBase + c) % 256) * limbBase + b) % 256 < 256 :=
    Nat.mod_lt _ (by decide)
  have h0 := divmodStep_at [a, b, c] q1 0
      ((((0 * limbBase + c) % 256) * limbBase + b) % 256)
    (len3_0 a b c) hr1 (by rw [dig0]; exact ha) hsz0 FitsLen.zero
  rw [h0]
  simp [dig0]
  dsimp [q1, q2]
  erw [embed_q3 a b c, rem_q3 a b c]
  rw [make_big_false (divAll [a, b, c]).1
      (fits_le3 (by simp [divAll, List.length_cons, List.length_nil])), map_ok]
  rfl

/-- `big_divmod_small` by 256 on an i64 refines one base-256 digit. -/
theorem divmod256_refines (v : Nat) (hv : FitsLen v) :
    Megadreifach.big_divmod_small (bigOf (limbsOfNat v)) (256 : Int) =
      .ok (bigOf (limbsOfNat (v / 256)), (v % 256 : Int)) := by
  have hv3 := fitsLen_lt_limb3 hv
  have hbyte := divAll_byte v hv3
  by_cases h0 : v = 0
  · simp [limbsOfNat, h0, divmod_nil]
  · by_cases hq : v / limbBase = 0
    · have hlt : v < limbBase := lt_of_div_eq_zero limbBase_pos hq
      have hmod : v % limbBase = v := Nat.mod_eq_of_lt hlt
      have hlimb : limbsOfNat v = [v] := by simp [limbsOfNat, h0, hq, hmod]
      rw [hlimb]
      simpa using divmod_one v hlt h0
    · by_cases hq2 : (v / limbBase) / limbBase = 0
      · have hb_lt : v / limbBase < limbBase := lt_of_div_eq_zero limbBase_pos hq2
        have hbmod : (v / limbBase) % limbBase = v / limbBase := Nat.mod_eq_of_lt hb_lt
        have ha : v % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
        have hlimb : limbsOfNat v = [v % limbBase, v / limbBase] := by
          simp [limbsOfNat, h0, hq, hq2, hbmod]
        rw [hlimb] at hbyte
        rw [hlimb, divmod_two (v % limbBase) (v / limbBase) ha hb_lt, hbyte.1, hbyte.2]
        simp [Int.ofNat_emod]
      · have hc_lt : (v / limbBase) / limbBase < limbBase := by
          have hqlt : v / limbBase < limbBase ^ 2 := by
            rw [limbBase_pow3] at hv3
            exact div_lt_of_lt_mul limbBase_pos hv3
          rw [limbBase_pow2] at hqlt
          exact div_lt_of_lt_mul limbBase_pos hqlt
        have hcmod : ((v / limbBase) / limbBase) % limbBase =
            (v / limbBase) / limbBase := Nat.mod_eq_of_lt hc_lt
        have ha : v % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
        have hb : (v / limbBase) % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
        have hlimb : limbsOfNat v =
            [v % limbBase, (v / limbBase) % limbBase, (v / limbBase) / limbBase] := by
          simp [limbsOfNat, h0, hq, hq2, hcmod]
        rw [hlimb] at hbyte
        rw [hlimb,
          divmod_three (v % limbBase) ((v / limbBase) % limbBase)
            ((v / limbBase) / limbBase) ha hb hc_lt,
          hbyte.1, hbyte.2]
        simp [Int.ofNat_emod]

def beAcc (v i : Nat) : Megadreifach.BigInt × Array Int :=
  (bigOf (limbsOfNat (v / 256 ^ (i - 1))), embed (leBytes (i - 1) v))

theorem beAcc_one (v : Nat) : beAcc v 1 = (bigOf (limbsOfNat v), embed []) := by
  simp [beAcc, leBytes, Nat.pow_zero, Nat.div_one]

def beStep (width : Int) (σ : Int × (Megadreifach.BigInt × Array Int)) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × (Megadreifach.BigInt × Array Int)) (Array Int)) :=
  let i := σ.1
  let acc := σ.2.1
  let rev := σ.2.2
  do
    if i > width then
      pure (SudoRt.Flow.brk (ρ := Array Int) (i, acc, rev))
    else
      match ←
        ((do
          let pr ← Megadreifach.big_divmod_small acc (256 : Int)
          pure (SudoRt.Flow.cont (ρ := Array Int) (pr.1, (SudoRt.appendL rev pr.2).1))) :
          Except SudoRt.Trap (SudoRt.Flow (Megadreifach.BigInt × Array Int) (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
      | .cont fs =>
        if (i == width) = true then
          pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
        else do
          let i' ← SudoRt.addI i (1 : Int)
          pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

theorem beStep_hit (v i : Nat) (hv : FitsLen v) (hi1 : 1 ≤ i) (hi8 : i ≤ 8) :
    beStep 8 (Int.ofNat i, beAcc v i) =
      (if i = 8 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, beAcc v (i + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), beAcc v (i + 1)))) := by
  unfold beStep beAcc
  dsimp
  rw [← ofNat_eq_natCast i, show (8 : Int) = Int.ofNat 8 from rfl,
    if_neg (ofNat_not_gt (by omega : i ≤ 8))]
  have hv' : FitsLen (v / 256 ^ (i - 1)) := FitsLen.of_le hv (Nat.div_le_self _ _)
  rw [divmod256_refines _ hv', ok_bind, appendL_spec]
  have hdiv : (v / 256 ^ (i - 1)) / 256 = v / 256 ^ i := by
    have hi : (i - 1) + 1 = i := by omega
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← pow256_succ, hi]
  erw [← Int.ofNat_emod (v / 256 ^ (i - 1)) 256]
  rw [← ofNat_eq_natCast ((v / 256 ^ (i - 1)) % 256),
    push_embed (leBytes (i - 1) v) ((v / 256 ^ (i - 1)) % 256), hdiv]
  have hle :
      leBytes (i - 1) v ++ [(v / 256 ^ (i - 1)) % 256] = leBytes ((i - 1) + 1) v :=
    (leBytes_succ_append (i - 1) v).symm
  have hidx : (i - 1) + 1 = i := by omega
  rw [hle, hidx]
  have hnext : (i + 1) - 1 = i := by omega
  by_cases hi : i = 8
  · simp [hi, hle, hnext, beq_int_iff]
    rfl
  · have hne : ¬ (i : Int) = 8 := fun h => hi (Int.ofNat.inj h)
    have hadd := addI_ofNat_one i (fits_le9 (by omega))
    rw [ofNat_eq_natCast i] at hadd
    simp [hi, hle, hnext, ite_int_beq, hne, hadd, ok_bind]

def downCopyStep (xs : Array Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  if σ.1 < 0 then
    pure (SudoRt.Flow.brk (ρ := Array Int) (σ.1, σ.2))
  else do
    let lift ←
      ((do
        let t ← SudoRt.atL xs σ.1
        pure (SudoRt.Flow.cont (ρ := Array Int) (SudoRt.appendL σ.2 t).1)) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int) (Array Int)))
    match lift with
    | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
    | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (σ.1, fs))
    | .cont fs =>
      if (σ.1 == 0) = true then
        pure (SudoRt.Flow.brk (ρ := Array Int) (σ.1, fs))
      else do
        let i' ← SudoRt.subI σ.1 (1 : Int)
        pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

theorem down_hit (bs : List Nat) (i : Nat) (hi : i < bs.length) (hfits : FitsLen i) :
    downCopyStep (embed bs) (Int.ofNat i, embed ((bs.drop (i + 1)).reverse)) =
      (let acc := embed ((bs.drop i).reverse)
      if i = 0 then .ok (SudoRt.Flow.brk (Int.ofNat i, acc))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i - 1), acc))) := by
  unfold downCopyStep
  dsimp
  rw [if_neg (Int.not_lt.mpr (Int.ofNat_zero_le i))]
  rw [← ofNat_eq_natCast i, atL_embed bs i hi, ok_bind]
  have hrev : (bs.drop (i + 1)).reverse ++ [bs[i]] = (bs.drop i).reverse := by
    have hd := drop_eq_cons bs i hi
    have hg : bs.get ⟨i, hi⟩ = bs[i] := rfl
    rw [hd, hg, List.reverse_cons]
  rw [appendL_spec, push_embed, hrev]
  erw [ok_bind]
  by_cases hi0 : i = 0
  · simp [hi0]
    rfl
  · have hne : ¬ (i : Int) = 0 := fun h => hi0 (Int.ofNat.inj h)
    have hsub := subI_ofNat_one i (Nat.pos_of_ne_zero hi0) hfits
    rw [ofNat_eq_natCast i] at hsub
    simp [hi0, ite_int_beq, hne, hsub, ok_bind]

/-- Low byte first, then the emitted downto copy, is `toBE` when `v` fits. -/
theorem be_down (v : Nat) (hv : FitsLen v) :
    SudoRt.runLoopOn (Int.ofNat 7, embed ((leBytes 8 v).drop 8).reverse)
        (fuelDown (Int.ofNat 7) 0)
        (downCopyStep (embed (leBytes 8 v)))
        (fun σ => (pure σ.2 : Except SudoRt.Trap (Array Int)))
        (fun r => pure r) =
      .ok (embed (toBE 8 v)) := by
  apply chain_down (downCopyStep (embed (leBytes 8 v)))
    (f := fun i => embed ((leBytes 8 v).drop (i + 1)).reverse)
    (g := fun i => embed ((leBytes 8 v).drop i).reverse)
    (fromN := 7)
    (hstep := by
      intro i hi
      have hlt : i < (leBytes 8 v).length := by
        rw [leBytes_length]
        omega
      exact down_hit (leBytes 8 v) i hlt (fits_le9 (by omega)))
    (hlink := by
      intro i hp _
      dsimp
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hp)])
    (goal := .ok (embed (toBE 8 v)))
    (hafter := by
      simp only [List.drop_zero]
      rw [← toBE_eq_leRev 8 v (fitsLen_lt_be hv)]
      rfl)

theorem big_to_be_8 (v : Nat) (hv : FitsLen v) :
    Megadreifach.big_to_be (bigOf (limbsOfNat v)) (8 : Int) =
      .ok (embed (toBE 8 v)) := by
  unfold Megadreifach.big_to_be
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := beStep 8)
    intro σ
    unfold beStep
    rfl
  have hfuel : fuelRange (Int.ofNat 1) (Int.ofNat 8) = 8 := by
    rw [fuelRange_le (by decide : (1 : Nat) ≤ 8)]
  rw [← hfuel]
  rw [show (1 : Int) = Int.ofNat 1 from rfl, embed_nil.symm, ← beAcc_one v]
  apply chain_loop (beStep 8)
    (f := beAcc v) (fromN := 1) (toN := 8) (hle := by decide)
    (hstep := fun i hi1 hi8 => beStep_hit v i hv hi1 hi8)
    (goal := .ok (embed (toBE 8 v)))
    (hafter := by
      dsimp [beAcc]
      rw [listLen_embed, leBytes_length,
        subI_ofNat_one 8 (by decide) (fits_le9 (by decide))]
      rw [ok_bind]
      have hsub : (8 - 1 : Nat) = 7 := by decide
      rw [hsub, fuelDown_eq (Int.ofNat 7) 0]
      have hdrop : (leBytes 8 v).drop 8 = [] := by
        have h := List.drop_length (leBytes 8 v)
        rwa [leBytes_length 8 v] at h
      rw [show (embed [] : Array Int) =
          embed ((leBytes 8 v).drop 8).reverse by rw [hdrop]; rfl]
      rw [except_bind_pure]
      apply Eq.trans
      · apply runLoopOn_step_pointwise (step' := downCopyStep (embed (leBytes 8 v)))
        intro σ
        unfold downCopyStep
        rfl
      exact be_down v hv)

end MegaDreifach.Link2
