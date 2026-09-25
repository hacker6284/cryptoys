/-
  LINK 2. `drop_front` / `push_front` refine list cons/tail on the
  well-formed domain. Proof-only. Not emitter soundness.
-/
import Doubledeal
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo

set_option maxHeartbeats 800000

namespace DoubleDeal.Link2

/-- Range-copy stepper in the shape Lean leaves after unfolding emit
    (`drop_front` / `push_front` / `left_rotate` loops). Not a hand-edit of
    Generated — a proof-side twin used to state collect. -/
def copyStep (ρ : Type) (xs : Array Int) (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) ρ) :=
  if σ.1 > toV then
    pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, σ.2))
  else do
    let lift ← do
      let t ← SudoRt.atL xs σ.1
      pure (SudoRt.Flow.cont (ρ := ρ) (SudoRt.appendL σ.2 t).1)
    match lift with
    | .ret r => pure (SudoRt.Flow.ret (ρ := ρ) r)
    | .brk fs => pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, fs))
    | .cont fs =>
      if σ.1 == toV then
        pure (SudoRt.Flow.brk (ρ := ρ) (σ.1, fs))
      else do
        let i' ← SudoRt.addI σ.1 (1 : Int)
        pure (SudoRt.Flow.cont (ρ := ρ) (i', fs))

theorem copyStep_gt (ρ : Type) (xs : Array Int) (toV i : Int) (acc : Array Int)
    (h : i > toV) :
    copyStep ρ xs toV (i, acc) = .ok (.brk (i, acc)) := by
  unfold copyStep
  rw [if_pos h]
  rfl

theorem copyStep_hit (ρ : Type) (xs : Array Int) (toN fromN : Nat) (acc : Array Int)
    (hfrom : fromN ≤ toN) (hidx : fromN < xs.size) (hfits : FitsLen xs.size) :
    copyStep ρ xs (Int.ofNat toN) (Int.ofNat fromN, acc) =
      if fromN = toN then
        .ok (.brk (Int.ofNat fromN, acc.push (xs.get ⟨fromN, hidx⟩)))
      else
        .ok (.cont ((fromN : Int) + 1, acc.push (xs.get ⟨fromN, hidx⟩))) := by
  unfold copyStep
  dsimp
  have hngt : ¬ (fromN : Int) > (toN : Int) :=
    Int.not_lt.mpr (Int.ofNat_le.mpr hfrom)
  rw [if_neg hngt]
  have hat : SudoRt.atL xs (fromN : Int) = .ok (xs.get ⟨fromN, hidx⟩) :=
    ofNat_eq_natCast fromN ▸ atL_ofNat xs fromN hidx
  simp [hat, SudoRt.appendL]
  by_cases heq : fromN = toN
  · subst heq
    have hbeq : ((fromN : Int) == (fromN : Int)) = true := by simp
    simp [hbeq]
    rfl
  · have hneInt : ¬ (fromN : Int) = (toN : Int) := fun h => heq (Int.ofNat.inj h)
    rw [if_neg hneInt]
    have hadd : SudoRt.addI (fromN : Int) 1 = .ok ((fromN : Int) + 1) := by
      have h := addI_ofNat_one fromN (FitsLen.of_le hfits (Nat.succ_le_of_lt hidx))
      rw [ofNat_eq_natCast fromN] at h
      rwa [← natCast_succ fromN] at h
    rw [hadd, map_ok, if_neg heq]

theorem copy_loop_gt (ρ : Type) (xs : Array Int) (fromV toV : Int) (acc : Array Int)
    (finish : Array Int → ρ) (hgt : fromV > toV) :
    SudoRt.runLoopOn (ρ := ρ) (fromV, acc) (fuelRange fromV toV)
        (copyStep ρ xs toV)
        (fun σ => .ok (finish σ.2)) (fun r => .ok r) =
      .ok (finish acc) := by
  rw [fuelRange_gt hgt, show 1 = 0 + 1 from rfl, runLoopOn_succ]
  rw [copyStep_gt ρ xs toV fromV acc hgt]

theorem drop_eq_cons {α} (xs : List α) (i : Nat) (h : i < xs.length) :
    xs.drop i = xs.get ⟨i, h⟩ :: xs.drop (i + 1) := by
  induction i generalizing xs with
  | zero =>
    match xs with
    | [] => exact (Nat.not_lt_zero _ h).elim
    | x :: xs => rfl
  | succ i ih =>
    match xs with
    | [] => exact (Nat.not_lt_zero _ h).elim
    | x :: xs =>
      change (x :: xs).drop (i + 1) = (x :: xs).get ⟨i + 1, h⟩ :: (x :: xs).drop (i + 2)
      have h' : i < xs.length := Nat.lt_of_succ_lt_succ h
      have : xs.drop i = xs.get ⟨i, h'⟩ :: xs.drop (i + 1) := ih xs h'
      exact this

theorem toList_length (a : Array Int) : a.toList.length = a.size := rfl

/-- Inclusive copy of `xs[fromN ..= toN]` onto `acc`, or no-op when `fromN = toN+1`. -/
theorem copy_loop_collect (ρ : Type) (xs : Array Int) (fromN toN : Nat)
    (acc : Array Int) (finish : Array Int → ρ)
    (hfrom : fromN ≤ toN + 1)
    (hto : toN < xs.size ∨ fromN = toN + 1)
    (hfits : FitsLen xs.size)
    (hfromB : fromN ≤ xs.size) :
    SudoRt.runLoopOn (ρ := ρ) (Int.ofNat fromN, acc)
        (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        (copyStep ρ xs (Int.ofNat toN))
        (fun σ => .ok (finish σ.2)) (fun r => .ok r) =
      .ok (finish (Array.mk (acc.toList ++
        List.take (toN + 1 - fromN) (xs.toList.drop fromN)))) := by
  generalize hrem : toN + 1 - fromN = rem
  induction rem generalizing fromN acc with
  | zero =>
    have hEq : fromN = toN + 1 := by omega
    subst hEq
    have hgt : Int.ofNat (toN + 1) > Int.ofNat toN :=
      Int.ofNat_lt.mpr (Nat.lt_succ_self _)
    rw [copy_loop_gt ρ xs (Int.ofNat (toN + 1)) (Int.ofNat toN) acc finish hgt]
    simp [Nat.sub_self, mk_toList]
  | succ rem ih =>
    have hle : fromN ≤ toN := by omega
    have hto' : toN < xs.size := by
      cases hto with
      | inl h => exact h
      | inr h => omega
    have hidx : fromN < xs.size := Nat.lt_of_le_of_lt hle hto'
    rw [fuelRange_le hle, runLoopOn_succ,
        copyStep_hit ρ xs toN fromN acc hle hidx hfits]
    by_cases heq : fromN = toN
    · rw [if_pos heq]
      have htk : List.take 1 (List.drop fromN xs.toList) =
          [xs.get ⟨fromN, hidx⟩] := by
        have : fromN < xs.toList.length := by
          rw [toList_length]; exact hidx
        rw [drop_eq_cons xs.toList fromN this]
        rfl
      have hrem1 : rem + 1 = 1 := by
        have : fromN = toN := heq
        omega
      simp [toList_push, htk, hrem1]
      apply congrArg finish
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
      rw [natCast_succ fromN]
      rw [← ofNat_eq_natCast toN]
      have hg : xs[fromN] = xs.get ⟨fromN, hidx⟩ := rfl
      rw [hg, ih']
      have hdrop : List.drop fromN xs.toList =
          xs.get ⟨fromN, hidx⟩ :: List.drop (fromN + 1) xs.toList := by
        have : fromN < xs.toList.length := by
          rw [toList_length]; exact hidx
        exact drop_eq_cons xs.toList fromN this
      rw [toList_push, hdrop]
      simp [List.take]

theorem drop_front_singleton (c : Nat) :
    Doubledeal.drop_front (embed [c]) = .ok (Int.ofNat c, embed []) := by
  unfold Doubledeal.drop_front
  rw [atL_embed_zero]
  simp only [ok_bind]
  have hlen : SudoRt.listLen (embed [c]) = (1 : Int) := by
    rw [listLen_embed]; rfl
  rw [hlen]
  have hsub : SudoRt.subI (1 : Int) 1 = .ok (0 : Int) :=
    subI_ofNat_one 1 (by decide) FitsLen.one
  rw [hsub]
  simp only [ok_bind]
  have hfuel : (if (1 : Int) > (0 : Int) then 1 else ((0 : Int) - 1).natAbs + 1) = 1 := rfl
  rw [hfuel, show 1 = 0 + 1 from rfl, runLoopOn_succ]
  simp
  rfl

theorem push_front_nil (c : Nat) :
    Doubledeal.push_front (embed []) (Int.ofNat c) = .ok (embed [c]) := by
  unfold Doubledeal.push_front
  simp [SudoRt.appendL, listLen_embed, subI_zero_one]
  rw [show 1 = 0 + 1 from rfl, runLoopOn_succ]
  simp
  rfl

theorem take_map_ofNat : ∀ (n : Nat) (xs : List Nat),
    List.take n (xs.map Int.ofNat) = (List.take n xs).map Int.ofNat
  | 0, _ => rfl
  | _n + 1, [] => rfl
  | n + 1, _x :: xs => congrArg (List.cons _) (take_map_ofNat n xs)

theorem drop_map_ofNat : ∀ (n : Nat) (xs : List Nat),
    List.drop n (xs.map Int.ofNat) = (List.drop n xs).map Int.ofNat
  | 0, _ => rfl
  | _n + 1, [] => rfl
  | n + 1, _x :: xs => drop_map_ofNat n xs

theorem embed_drop_tail (c : Nat) (rest : List Nat) :
    Array.mk (List.take rest.length (embed (c :: rest)).toList.tail) =
      embed rest := by
  change Array.mk (List.take rest.length (Int.ofNat c :: rest.map Int.ofNat).tail) =
    embed rest
  change Array.mk (List.take rest.length (rest.map Int.ofNat)) = embed rest
  rw [take_map_ofNat, List.take_length]
  rfl

/-- Residual `drop_front` stepper after unfold, definitionally `copyStep`. -/
theorem drop_front_step_eq (xs : Array Int) (toV : Int) :
    (fun σ : Int × Array Int =>
      if σ.fst > toV then pure (SudoRt.Flow.brk (σ.fst, σ.snd))
      else do
        let __do_lift ← do
          let _t373 ← SudoRt.atL xs σ.fst
          pure (SudoRt.Flow.cont (SudoRt.appendL σ.snd _t373).fst)
        match __do_lift with
        | SudoRt.Flow.ret r => pure (SudoRt.Flow.ret r)
        | SudoRt.Flow.brk _fs => pure (SudoRt.Flow.brk (σ.fst, _fs))
        | SudoRt.Flow.cont _fs =>
          if (σ.fst == toV) = true then pure (SudoRt.Flow.brk (σ.fst, _fs))
          else do
            let i' ← SudoRt.addI σ.fst 1
            pure (SudoRt.Flow.cont (i', _fs)))
    = copyStep (Int × Array Int) xs toV := by
  funext σ
  unfold copyStep
  rfl

/-- Residual `push_front` stepper after unfold, definitionally `copyStep`. -/
theorem push_front_step_eq (xs : Array Int) (toV : Int) :
    (fun σ : Int × Array Int =>
      if σ.fst > toV then pure (SudoRt.Flow.brk (σ.fst, σ.snd))
      else do
        let __do_lift ← do
          let _t363 ← SudoRt.atL xs σ.fst
          pure (SudoRt.Flow.cont (σ.snd.push _t363))
        match __do_lift with
        | SudoRt.Flow.ret r => pure (SudoRt.Flow.ret r)
        | SudoRt.Flow.brk _fs => pure (SudoRt.Flow.brk (σ.fst, _fs))
        | SudoRt.Flow.cont _fs =>
          if (σ.fst == toV) = true then pure (SudoRt.Flow.brk (σ.fst, _fs))
          else do
            let i' ← SudoRt.addI σ.fst 1
            pure (SudoRt.Flow.cont (i', _fs)))
    = copyStep (Array Int) xs toV := by
  funext σ
  unfold copyStep
  simp [SudoRt.appendL]

theorem fuelRange_eq (fromV toV : Int) :
    (if fromV > toV then 1 else (toV - fromV).natAbs + 1) = fuelRange fromV toV :=
  rfl

/-- Inclusive copy, then an arbitrary continuation of the collected array.
    `onRet` is unused: `copyStep` never emits `.ret`. Used by `left_rotate`
    (copy the tail, then copy the head). -/
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
      have hrem1 : rem + 1 = 1 := by
        have : fromN = toN := heq
        omega
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
      rw [natCast_succ fromN]
      rw [← ofNat_eq_natCast toN]
      have hg : xs[fromN] = xs.get ⟨fromN, hidx⟩ := rfl
      rw [hg, ih']
      have hdrop : List.drop fromN xs.toList =
          xs.get ⟨fromN, hidx⟩ :: List.drop (fromN + 1) xs.toList := by
        have : fromN < xs.toList.length := by
          rw [toList_length]; exact hidx
        exact drop_eq_cons xs.toList fromN this
      rw [toList_push, hdrop]
      simp [List.take]

/-- Generated `drop_front` is algebraic `uncons` on a nonempty well-formed list. -/
theorem drop_front_refines (c : Nat) (rest : List Nat)
    (hfits : FitsLen (rest.length + 1)) :
    Doubledeal.drop_front (embed (c :: rest)) =
      .ok (Int.ofNat c, embed rest) := by
  unfold Doubledeal.drop_front
  rw [atL_embed_zero]
  simp only [ok_bind]
  have hlen : SudoRt.listLen (embed (c :: rest)) = Int.ofNat (rest.length + 1) := by
    rw [listLen_embed]; rfl
  rw [hlen]
  have hsub : SudoRt.subI (Int.ofNat (rest.length + 1)) 1 = .ok (Int.ofNat rest.length) :=
    subI_ofNat_one (rest.length + 1) (Nat.succ_pos _) hfits
  rw [hsub]
  simp only [ok_bind]
  rw [except_bind_pure, fuelRange_eq]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' :=
        copyStep (Int × Array Int) (embed (c :: rest)) (Int.ofNat rest.length))
    intro s
    unfold copyStep
    by_cases hgt : s.fst > Int.ofNat rest.length
    · simp [hgt]
    · simp [hgt]
  have h1 : (1 : Int) = Int.ofNat 1 := rfl
  rw [h1]
  have hafter :
      (fun σ : Int × Array Int =>
          (pure (Int.ofNat c, σ.snd) : Except SudoRt.Trap (Int × Array Int))) =
        (fun σ => .ok (Int.ofNat c, σ.2)) := rfl
  have hon :
      (fun r : Int × Array Int => (pure r : Except SudoRt.Trap (Int × Array Int))) =
        (fun r => .ok r) := rfl
  rw [hafter, hon]
  have hcollect := copy_loop_collect (Int × Array Int)
      (embed (c :: rest)) 1 rest.length #[] (fun a => (Int.ofNat c, a))
      (by omega)
      (Or.inl (by rw [size_embed]; exact Nat.lt_succ_self _))
      (by rw [size_embed]; exact hfits)
      (by rw [size_embed]; exact Nat.succ_le_succ (Nat.zero_le _))
  rw [hcollect]
  exact congrArg (fun a => Except.ok (Int.ofNat c, a)) (embed_drop_tail c rest)

/-- Generated `push_front` is algebraic `cons` on a well-formed list. -/
theorem push_front_refines (c : Nat) (rest : List Nat) (hfits : FitsLen rest.length) :
    Doubledeal.push_front (embed rest) (Int.ofNat c) = .ok (embed (c :: rest)) := by
  cases rest with
  | nil => exact push_front_nil c
  | cons r rs =>
    unfold Doubledeal.push_front
    simp only [SudoRt.appendL]
    have hlen : SudoRt.listLen (embed (r :: rs)) = Int.ofNat (rs.length + 1) := by
      rw [listLen_embed]; rfl
    rw [hlen]
    have hsub : SudoRt.subI (Int.ofNat (rs.length + 1)) 1 = .ok (Int.ofNat rs.length) :=
      subI_ofNat_one (rs.length + 1) (Nat.succ_pos _) hfits
    rw [hsub]
    simp only [ok_bind]
    rw [except_bind_pure, fuelRange_eq]
    apply Eq.trans
    · apply runLoopOn_step_pointwise (step' :=
          copyStep (Array Int) (embed (r :: rs)) (Int.ofNat rs.length))
      intro s
      unfold copyStep
      by_cases hgt : s.fst > Int.ofNat rs.length
      · have hlt : (rs.length : Int) < s.fst := hgt
        simp [hlt, SudoRt.appendL]
      · simp [hgt, SudoRt.appendL]
    have hon :
        (fun r : Array Int => (pure r : Except SudoRt.Trap (Array Int))) =
          (fun r => .ok r) := rfl
    rw [hon]
    have h0 : (0 : Int) = Int.ofNat 0 := rfl
    rw [h0]
    have hacc : (#[] : Array Int).push (Int.ofNat c) = Array.mk [Int.ofNat c] := rfl
    rw [hacc]
    have hsz : (embed (r :: rs)).size = rs.length + 1 := by
      rw [size_embed]; rfl
    have hcollect := copy_loop_collect (Array Int)
        (embed (r :: rs)) 0 rs.length (Array.mk [Int.ofNat c]) id
        (by omega)
        (Or.inl (by rw [hsz]; omega))
        (by rw [hsz]; exact hfits)
        (by rw [hsz]; omega)
    have hafter :
        (fun σ : Int × Array Int => (pure σ.snd : Except SudoRt.Trap (Array Int))) =
          (fun σ => .ok (id σ.2)) := rfl
    rw [hafter, hcollect]
    have htake :
        List.take (rs.length + 1) (embed (r :: rs)).toList =
          (embed (r :: rs)).toList :=
      List.take_of_length_le (by simp [toList_embed])
    simp [id, htake, toList_embed]
    rw [take_map_ofNat, List.take_length]
    rfl

end DoubleDeal.Link2
