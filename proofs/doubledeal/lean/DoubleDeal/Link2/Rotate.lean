/-
  LINK 2. Generated `left_rotate` refines algebraic `rotL` on the
  well-formed domain. Proof-only. Not emitter soundness.
-/
import Doubledeal
import DoubleDeal.Rotate
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Append

set_option maxHeartbeats 800000

namespace DoubleDeal.Link2

theorem embed_drop (xs : List Nat) (k : Nat) :
    embed (List.drop k xs) = Array.mk ((embed xs).toList.drop k) := by
  apply congrArg Array.mk
  rw [toList_embed, drop_map_ofNat]

theorem embed_take (xs : List Nat) (k : Nat) :
    embed (List.take k xs) = Array.mk ((embed xs).toList.take k) := by
  apply congrArg Array.mk
  rw [toList_embed, take_map_ofNat]

theorem embed_append (xs ys : List Nat) :
    embed (xs ++ ys) = Array.mk ((embed xs).toList ++ (embed ys).toList) := by
  simp [embed, List.map_append]

theorem rotL_eq_drop_take (xs : List Nat) (k : Nat) (hne : xs.length ≠ 0) :
    rotL xs k = xs.drop (k % xs.length) ++ xs.take (k % xs.length) := by
  unfold rotL
  simp [hne]

theorem take_drop_len (xs : List Nat) (k : Nat) (_hk : k ≤ xs.length) :
    List.take (xs.length - k) ((embed xs).toList.drop k) =
      (embed xs).toList.drop k := by
  apply List.take_of_length_le
  rw [List.length_drop, toList_embed, List.length_map]
  exact Nat.le_refl _

theorem rotL_mod_zero (xs : List Nat) (k : Nat) (hne : xs.length ≠ 0)
    (hk : k % xs.length = 0) : rotL xs k = xs := by
  rw [rotL_eq_drop_take xs k hne, hk, List.drop_zero, List.take_zero, List.append_nil]

theorem sEq_natCast_zero (n : Nat) :
    SudoRt.SEq.beq (n : Int) (0 : Int) = decide (n = 0) := by
  rw [← ofNat_eq_natCast n, sEq_ofNat_zero]

theorem not_sEq_zero {n : Nat} (h : n ≠ 0) :
    ¬ (SudoRt.SEq.beq (Int.ofNat n) (0 : Int) = true) := by
  rw [sEq_ofNat_zero, decide_eq_false h]
  decide

/-- Residual `left_rotate` copy stepper (`dsimp` / `__do_lift` shape) equals `copyStep`. -/
theorem left_rotate_copy_step (xs : Array Int) (toV : Int) (s : Int × Array Int) :
    (if s.fst > toV then
        (pure (SudoRt.Flow.brk (ρ := Array Int) (s.fst, s.snd)) :
          Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)))
      else do
        let __do_lift ← do
          let t ← SudoRt.atL xs s.fst
          pure (SudoRt.Flow.cont (ρ := Array Int) (SudoRt.appendL s.snd t).fst)
        match __do_lift with
        | .ret r => pure (SudoRt.Flow.ret r)
        | .brk fs => pure (SudoRt.Flow.brk (s.fst, fs))
        | .cont fs =>
          if (s.fst == toV) = true then
            pure (SudoRt.Flow.brk (s.fst, fs))
          else do
            let i' ← SudoRt.addI s.fst (1 : Int)
            pure (SudoRt.Flow.cont (i', fs))) =
      copyStep (Array Int) xs toV s := by
  unfold copyStep
  by_cases hgt : s.fst > toV
  · simp [hgt, SudoRt.appendL]
  · simp [hgt, SudoRt.appendL]

theorem left_rotate_nil (k : Nat) :
    Doubledeal.left_rotate (embed []) (Int.ofNat k) = .ok (embed []) := by
  unfold Doubledeal.left_rotate
  rw [listLen_embed]
  dsimp
  have hbeq : SudoRt.SEq.beq (0 : Int) (0 : Int) = true := rfl
  rw [hbeq]
  rfl

/-- Second copy `0 ..= k-1` onto an accumulator, then return it. -/
theorem left_rotate_second (xs : List Nat) (k : Nat) (acc : Array Int)
    (hfits : FitsLen xs.length) (hkpos : 0 < k) (hklt : k < xs.length) :
    (do
      let t21 ← SudoRt.subI (Int.ofNat k) (1 : Int)
      let fromV := (0 : Int)
      let toV := t21
      let fuel : Nat := if fromV > toV then 1 else (toV - fromV).natAbs + 1
      let out ← SudoRt.runLoopOn (ρ := Array Int) (fromV, acc) fuel
        (fun σ =>
          if σ.fst > toV then
            pure (SudoRt.Flow.brk (ρ := Array Int) (σ.fst, σ.snd))
          else do
            let __do_lift ← do
              let t ← SudoRt.atL (embed xs) σ.fst
              pure (SudoRt.Flow.cont (ρ := Array Int) (SudoRt.appendL σ.snd t).fst)
            match __do_lift with
            | .ret r => pure (SudoRt.Flow.ret r)
            | .brk fs => pure (SudoRt.Flow.brk (σ.fst, fs))
            | .cont fs =>
              if (σ.fst == toV) = true then
                pure (SudoRt.Flow.brk (σ.fst, fs))
              else do
                let i' ← SudoRt.addI σ.fst (1 : Int)
                pure (SudoRt.Flow.cont (i', fs)))
        (fun σ => pure σ.snd) (fun r => pure r)
      pure out) =
      .ok (Array.mk (acc.toList ++ List.take k (embed xs).toList)) := by
  have hsub : SudoRt.subI (Int.ofNat k) 1 = .ok (Int.ofNat (k - 1)) :=
    subI_ofNat_one k hkpos (FitsLen.of_le hfits (Nat.le_of_lt hklt))
  rw [hsub]
  simp only [ok_bind]
  rw [except_bind_pure, fuelRange_eq]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' :=
        copyStep (Array Int) (embed xs) (Int.ofNat (k - 1)))
    intro s
    exact left_rotate_copy_step (embed xs) (Int.ofNat (k - 1)) s
  have h0i : (0 : Int) = Int.ofNat 0 := rfl
  rw [h0i]
  have hcollect := copy_loop_after (embed xs) 0 (k - 1) acc
      (fun a => .ok a) (fun r => .ok r)
      (by omega)
      (Or.inl (by rw [size_embed]; omega))
      (by rw [size_embed]; exact hfits)
      (by rw [size_embed]; exact Nat.zero_le _)
  have hafter :
      (fun σ : Int × Array Int => (pure σ.snd : Except SudoRt.Trap (Array Int))) =
        (fun σ => .ok σ.2) := rfl
  have hon :
      (fun r : Array Int => (pure r : Except SudoRt.Trap (Array Int))) =
        (fun r => .ok r) := rfl
  rw [hafter, hon, hcollect]
  have htk : k - 1 + 1 - 0 = k := by omega
  simp [htk]

/-- Generated `left_rotate` is algebraic `rotL` on a well-formed list. -/
theorem left_rotate_refines (xs : List Nat) (k : Nat) (hfits : FitsLen xs.length) :
    Doubledeal.left_rotate (embed xs) (Int.ofNat k) =
      .ok (embed (rotL xs k)) := by
  by_cases h0 : xs.length = 0
  · have hxs : xs = [] := List.eq_nil_of_length_eq_zero h0
    subst hxs
    simpa [rotL] using left_rotate_nil k
  · unfold Doubledeal.left_rotate
    rw [listLen_embed]
    dsimp
    have hbeq : ¬ (SudoRt.SEq.beq (xs.length : Int) (0 : Int) = true) := by
      rw [sEq_natCast_zero, decide_eq_false h0]
      decide
    rw [if_neg hbeq]
    have hmod : SudoRt.modI (k : Int) (xs.length : Int) =
        .ok (Int.ofNat (k % xs.length)) := by
      rw [← ofNat_eq_natCast k, ← ofNat_eq_natCast xs.length]
      exact modI_ofNat k h0
    rw [hmod]
    simp only [ok_bind]
    by_cases hk0 : k % xs.length = 0
    · have hbeq0 : SudoRt.SEq.beq (Int.ofNat (k % xs.length)) (0 : Int) = true := by
        rw [hk0]; rfl
      -- residual may display `↑(k % xs.length)` or `0`
      rw [ofNat_eq_natCast (k % xs.length)] at hbeq0 ⊢
      rw [hk0] at hbeq0 ⊢
      dsimp at hbeq0 ⊢
      rw [show SudoRt.SEq.beq (0 : Int) (0 : Int) = true from rfl]
      change (if true = true then
          (pure (embed xs) : Except SudoRt.Trap (Array Int)) else _) = _
      simp only [↓reduceIte]
      rw [rotL_mod_zero xs k h0 hk0]
      rfl
    · have hbeq0 : ¬ (SudoRt.SEq.beq (Int.ofNat (k % xs.length)) (0 : Int) = true) :=
        not_sEq_zero hk0
      rw [ofNat_eq_natCast (k % xs.length)] at hbeq0 ⊢
      rw [if_neg hbeq0]
      have hkpos : 0 < k % xs.length := Nat.pos_of_ne_zero hk0
      have hklt : k % xs.length < xs.length :=
        Nat.mod_lt k (Nat.pos_of_ne_zero h0)
      have hsubn : SudoRt.subI (xs.length : Int) 1 =
          .ok (Int.ofNat (xs.length - 1)) := by
        rw [← ofNat_eq_natCast]
        exact subI_ofNat_one xs.length (Nat.pos_of_ne_zero h0) hfits
      rw [hsubn]
      simp only [ok_bind]
      rw [except_bind_pure, fuelRange_eq]
      apply Eq.trans
      · apply runLoopOn_step_pointwise (step' :=
            copyStep (Array Int) (embed xs) (Int.ofNat (xs.length - 1)))
        intro s
        unfold copyStep
        by_cases hgt : s.fst > Int.ofNat (xs.length - 1)
        · simp [hgt, SudoRt.appendL]
        · simp [hgt, SudoRt.appendL]
      rw [← ofNat_eq_natCast (k % xs.length)]
      have hsubk : SudoRt.subI (Int.ofNat (k % xs.length)) 1 =
          .ok (Int.ofNat (k % xs.length - 1)) :=
        subI_ofNat_one (k % xs.length) hkpos
          (FitsLen.of_le hfits (Nat.le_of_lt hklt))
      conv =>
        lhs
        arg 4
        ext σ
        simp [SudoRt.appendL]
        rw [natCast_mod k xs.length, hsubk]
        simp only [ok_bind]
      let k' := k % xs.length
      have hfuel2 :
          (if Int.ofNat (k' - 1) < 0 then 1
            else (Int.ofNat (k' - 1)).natAbs + 1) =
            fuelRange (Int.ofNat 0) (Int.ofNat (k' - 1)) := by
        have hn : ¬ Int.ofNat (k' - 1) < 0 :=
          Int.not_lt.mpr (Int.ofNat_zero_le _)
        have hle : 0 ≤ k' - 1 := Nat.zero_le _
        rw [fuelRange_le hle]
        simp [hn, Int.natAbs_ofNat]
        omega
      have hstep2 (s : Int × Array Int) :
          (if Int.ofNat (k' - 1) < s.fst then
              (pure (SudoRt.Flow.brk (s.fst, s.snd)) :
                Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)))
            else do
              let a ← SudoRt.atL (embed xs) s.fst
              if s.fst = Int.ofNat (k' - 1) then
                pure (SudoRt.Flow.brk (s.fst, s.snd.push a))
              else
                (fun a_1 => SudoRt.Flow.cont (a_1, s.snd.push a)) <$>
                  SudoRt.addI s.fst 1) =
            copyStep (Array Int) (embed xs) (Int.ofNat (k' - 1)) s := by
        unfold copyStep
        by_cases hgt : Int.ofNat (k' - 1) < s.fst
        · have : s.fst > Int.ofNat (k' - 1) := hgt
          simp [hgt, this, SudoRt.appendL]
        · have : ¬ s.fst > Int.ofNat (k' - 1) := hgt
          simp [hgt, this, SudoRt.appendL]
      let after1 : Array Int → Except SudoRt.Trap (Array Int) := fun acc =>
        SudoRt.runLoopOn (ρ := Array Int) (Int.ofNat 0, acc)
          (fuelRange (Int.ofNat 0) (Int.ofNat (k' - 1)))
          (copyStep (Array Int) (embed xs) (Int.ofNat (k' - 1)))
          (fun σ => .ok σ.2) (fun r => .ok r)
      have hafter :
          (fun σ : Int × Array Int =>
            SudoRt.runLoopOn (ρ := Array Int) ((0 : Int), σ.snd)
              (if Int.ofNat (k' - 1) < 0 then 1
                else (Int.ofNat (k' - 1)).natAbs + 1)
              (fun σ =>
                if Int.ofNat (k' - 1) < σ.fst then
                  pure (SudoRt.Flow.brk (σ.fst, σ.snd))
                else do
                  let a ← SudoRt.atL (embed xs) σ.fst
                  if σ.fst = Int.ofNat (k' - 1) then
                    pure (SudoRt.Flow.brk (σ.fst, σ.snd.push a))
                  else
                    (fun a_1 => SudoRt.Flow.cont (a_1, σ.snd.push a)) <$>
                      SudoRt.addI σ.fst 1)
              (fun σ => pure σ.snd) (fun r => pure r)) =
            fun σ => after1 σ.2 := by
        funext σ
        rw [hfuel2, show (0 : Int) = Int.ofNat 0 from rfl]
        apply Eq.trans
        · apply runLoopOn_step_pointwise (step' :=
              copyStep (Array Int) (embed xs) (Int.ofNat (k' - 1)))
          intro s
          exact hstep2 s
        rfl
      rw [hafter]
      have hcollect1 := copy_loop_after (embed xs) k' (xs.length - 1)
          (#[] : Array Int) after1
          (fun r => (pure r : Except SudoRt.Trap (Array Int)))
          (by omega)
          (Or.inl (by rw [size_embed]; omega))
          (by rw [size_embed]; exact hfits)
          (by rw [size_embed]; exact Nat.le_of_lt hklt)
      rw [hcollect1]
      simp only [List.nil_append]
      have htk1 :
          List.take (xs.length - 1 + 1 - k') ((embed xs).toList.drop k') =
            (embed xs).toList.drop k' := by
        have : xs.length - 1 + 1 - k' = xs.length - k' := by omega
        rw [this, take_drop_len xs k' (Nat.le_of_lt hklt)]
      rw [htk1]
      have hsecond :
          after1 (Array.mk ((embed xs).toList.drop k')) =
            .ok (Array.mk ((embed xs).toList.drop k' ++
              List.take k' (embed xs).toList)) := by
        have htk : k' - 1 + 1 - 0 = k' := by omega
        have hcollect2 := copy_loop_after (embed xs) 0 (k' - 1)
            (Array.mk ((embed xs).toList.drop k'))
            (fun a => .ok a) (fun r => .ok r)
            (by omega)
            (Or.inl (by rw [size_embed]; omega))
            (by rw [size_embed]; exact hfits)
            (by rw [size_embed]; exact Nat.zero_le _)
        simp [after1, htk] at hcollect2 ⊢
        exact hcollect2
      rw [hsecond]
      have hjoin :
          Array.mk ((embed xs).toList.drop k' ++
              List.take k' (embed xs).toList) =
            embed (xs.drop k' ++ xs.take k') := by
        rw [embed_append, embed_drop, embed_take]
      rw [hjoin, rotL_eq_drop_take xs k h0]

end DoubleDeal.Link2

