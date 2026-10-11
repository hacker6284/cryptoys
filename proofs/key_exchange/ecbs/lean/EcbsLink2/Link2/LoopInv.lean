/-
  The ladder loop carries the rung read. `ClimbInvL` is `ClimbInvK` plus the
  ladder array, a positive tally length, and the i64 fit of that length.
  `runLoop_drop_inv` asks for the step only on boards in this predicate.
-/
import EcbsLink2.Link2.InvertOpen
import EcbsLink2.Link2.MulKeep
import EcbsLink2.Link2.TailLen

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- `ClimbInvK` at list index `k`, with the ladder and the tally length the
    step reads. `m` is `s.tally`, which starts at 1 and then follows `tallyAfter`,
    not `k + 1`. `FitsLen m` is `m ≤ control` against `ClimbBudget.fitControl`. -/
structure ClimbInvL (L : List Nat) (k : Nat) (b : Ecbs.Board) (base : ClimbBudget) where
  done : List Nat
  rest : List Nat
  s : ClimbModel
  split : L = done ++ rest
  k_eq : k = done.length
  inv : ClimbInvK done rest b s base
  ladder : b.sudo_5Board_6ladder = embed L
  m_pos : 0 < s.tally
  m_le : s.tally ≤ base.control
  m_len : b.sudo_5Board_9tally_len = Int.ofNat s.tally

/-- The predicate `runLoop_drop_inv` carries. -/
def ClimbP (L : List Nat) (base : ClimbBudget) (k : Nat) (b : Ecbs.Board) : Prop :=
  Nonempty (ClimbInvL L k b base)

theorem ClimbInvL.m_fit {L : List Nat} {k : Nat} {b : Ecbs.Board} {base : ClimbBudget}
    (h : ClimbInvL L k b base) : FitsLen h.s.tally :=
  FitsLen.of_le base.fitControl (Nat.le_trans h.m_le (Nat.le_succ base.control))

/-- The three reads, for any board that still holds `L` and a natural length. -/
theorem inv_named_step
    (b : Ecbs.Board) (L : List Nat) (x : Int) (i m : Nat)
    (hi : i < L.length) (hpos : 0 < L.length) (hfitL : FitsLen L.length)
    (hL : b.sudo_5Board_6ladder = embed L)
    (hm : 0 < m) (hfit : FitsLen m)
    (hlen : b.sudo_5Board_9tally_len = Int.ofNat m) :
    let rung := (L[i]'hi)
    let last := (L.drop (i + 1)).isEmpty
    (do
      let t0 ← SudoRt.subI (SudoRt.listLen b.sudo_5Board_6ladder) (1 : Int)
      let lastB := SudoRt.SEq.beq (Int.ofNat i) t0
      let rv ← SudoRt.atL b.sudo_5Board_6ladder (Int.ofNat i)
      let b ← Ecbs.park_rung b rv
      let b ← Ecbs.copy_band b Ecbs.spare Ecbs.gap false
      let m0 := b.sudo_5Board_9tally_len
      let toW ← SudoRt.subI m0 (1 : Int)
      let fromW := (0 : Int)
      let fuelW : Nat := if fromW > toW then 1 else (toW - fromW).natAbs + 1
      SudoRt.runLoopOn fromW fuelW (whiteStep b toW)
        (fun _ => rungAfterNamed x rv lastB b m0)
        (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))) =
      (do
        let b ← climbRung b rung last x m
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) := by
  intro rung last
  have hsub : SudoRt.subI (Int.ofNat L.length) (1 : Int) =
      .ok (Int.ofNat (L.length - 1)) :=
    subI_ofNat_one L.length hpos hfitL
  have hlast : SudoRt.SEq.beq (Int.ofNat i) (Int.ofNat (L.length - 1)) = last := by
    simpa [last] using last_flag L i hi
  have hat : SudoRt.atL b.sudo_5Board_6ladder (Int.ofNat i) = .ok (rung : Int) := by
    rw [hL]
    simpa [rung] using atL_embed L i hi
  rw [show SudoRt.listLen b.sudo_5Board_6ladder = Int.ofNat L.length by
    rw [hL, listLen_embed]]
  exact named_rung_step b x (Int.ofNat i) (Int.ofNat L.length)
    (Int.ofNat (L.length - 1)) rung last m hm hfit hlen hsub hlast hat

/-- The same rung read, with the length written as `Int.ofNat L.length`.
    That is the length the index loop closes over. -/
theorem inv_named_step_len
    (b : Ecbs.Board) (L : List Nat) (x : Int) (i m : Nat)
    (hi : i < L.length) (hpos : 0 < L.length) (hfitL : FitsLen L.length)
    (hL : b.sudo_5Board_6ladder = embed L)
    (hm : 0 < m) (hfit : FitsLen m)
    (hlen : b.sudo_5Board_9tally_len = Int.ofNat m) :
    (do
      let t ← SudoRt.subI (Int.ofNat L.length) (1 : Int)
      let rv ← SudoRt.atL b.sudo_5Board_6ladder (i : Int)
      let b ← Ecbs.park_rung b rv
      let b ← Ecbs.copy_band b Ecbs.spare Ecbs.gap false
      let toW ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
      SudoRt.runLoopOn (0 : Int)
        (if (0 : Int) > toW then 1 else (toW - (0 : Int)).natAbs + 1)
        (whiteStep b toW)
        (fun _ =>
          rungAfterNamed x rv (SudoRt.SEq.beq (i : Int) t) b b.sudo_5Board_9tally_len)
        (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))) =
    (do
      let b ← climbRung b (L[i]'hi) ((L.drop (i + 1)).isEmpty) x m
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) := by
  change (do
      let t ← SudoRt.subI (Int.ofNat L.length) (1 : Int)
      let lastB := SudoRt.SEq.beq (Int.ofNat i) t
      let rv ← SudoRt.atL b.sudo_5Board_6ladder (Int.ofNat i)
      let b ← Ecbs.park_rung b rv
      let b ← Ecbs.copy_band b Ecbs.spare Ecbs.gap false
      let m0 := b.sudo_5Board_9tally_len
      let toW ← SudoRt.subI m0 (1 : Int)
      let fromW := (0 : Int)
      let fuelW : Nat := if fromW > toW then 1 else (toW - fromW).natAbs + 1
      SudoRt.runLoopOn fromW fuelW (whiteStep b toW)
        (fun _ => rungAfterNamed x rv lastB b m0)
        (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))) = _
  have hstep := inv_named_step b L x i m hi hpos hfitL hL hm hfit hlen
  have hlenL : SudoRt.listLen b.sudo_5Board_6ladder = Int.ofNat L.length := by
    rw [hL, listLen_embed]
  rw [hlenL] at hstep
  exact hstep

/-- `climbRung` then continue, wrapped as the index loop's break or next index.
    `idx > toV` is false on a real index, and `idx == toV` is the last-index flag. -/
theorem rung_flow (idx toV i' : Int) (last : Bool)
    (idle : Int × Ecbs.Board)
    (m : Except SudoRt.Trap Ecbs.Board)
    (hng : ¬ idx > toV)
    (hbeq : ((idx == toV) = true) = (last = true))
    (hadd : SudoRt.addI idx (1 : Int) = .ok i') :
    ((if idx > toV then
        pure (SudoRt.Flow.brk (ρ := Ecbs.Board) idle)
      else
        (m >>= fun b' => pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b')) >>= fun fl =>
          match fl with
          | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
          | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (idx, fs))
          | .cont fs =>
              if (idx == toV) = true then
                pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (idx, fs))
              else
                SudoRt.addI idx (1 : Int) >>= fun j =>
                  pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (j, fs))) :
        Except SudoRt.Trap (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board)) =
      (m >>= fun b' =>
        pure (if last = true then
            SudoRt.Flow.brk (ρ := Ecbs.Board) (idx, b')
          else
            SudoRt.Flow.cont (ρ := Ecbs.Board) (i', b'))) := by
  rw [if_neg hng]
  cases m with
  | error e =>
    simp only [error_bind]
  | ok b' =>
    simp only [ok_bind, pure_eq_ok, hadd, ok_bind, hbeq]
    cases last <;> simp

/-- The tail after the ladder reads only the board, so every index is the same call. -/
def finalTail (b : Ecbs.Board) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b ← Ecbs.unpark_rung b
    let b ← Ecbs.cube b Ecbs.gap Ecbs.gap
    let b ← Ecbs.settle b
    Ecbs.tally_clear b

theorem finalTail_idx (i : Int) (b : Ecbs.Board) :
    (do
      let b ← Ecbs.unpark_rung b
      let b ← Ecbs.cube b Ecbs.gap Ecbs.gap
      let b ← Ecbs.settle b
      Ecbs.tally_clear b) =
      finalTail b := rfl

/-- `place` does not write the ladder, and neither does `copy_band` when it
    returns that board. -/
theorem placeBoard_ladder (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_6ladder =
      b.sudo_5Board_6ladder := by
  simp [placeBoard]
  split <;> rfl

theorem copy_band_ladder (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (moves peak : Nat)
    (hHd : dst < b.sudo_5Board_4home.size)
    (hDd : dst < b.sudo_5Board_4held.size)
    (hHs : src < b.sudo_5Board_4home.size)
    (hDs : src < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hsrc : b.sudo_5Board_4held[src] = true)
    (harr : b.sudo_5Board_4home[src] = embed xs)
    (hempty : b.sudo_5Board_4held[dst] = false)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (xs.length : Int))
    (hf : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + pegCount xs))
    (b' : Ecbs.Board)
    (h : Ecbs.copy_band b (dst : Int) (src : Int) false = .ok b') :
    b'.sudo_5Board_6ladder = b.sudo_5Board_6ladder := by
  have heq := copy_band_refines b dst src xs moves peak hHd hDd hHs hDs h7 hsrc
    harr hempty hn hf hmoves hpeak hfit
  rw [heq] at h
  cases h
  exact placeBoard_ladder b dst hHd hDd xs moves peak

/-- One guarded rung rebuilds `ClimbInvL` at the next index. The length is the
    one `climb_step` stores (`tallyAfter`). The ladder is the board the rung
    returns. -/
theorem climbL_succ
    {L : List Nat} {i : Nat} {b b' : Ecbs.Board} {base : ClimbBudget}
    (h : ClimbInvL L i b base) (hi : i < L.length)
    (hPark : h.s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 h.done h.rest ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x)
    (hprog : climbRung b (L[i]'hi) ((L.drop (i + 1)).isEmpty)
        ((base.xHome : Nat) : Int) h.s.tally = .ok b') :
    ∃ inv : ClimbInvL L (i + 1) b' base, inv.s.parkAt = base.ladder0 + base.R := by
  have hlad := climbRung_ladder b (L[i]'hi) ((L.drop (i + 1)).isEmpty)
    ((base.xHome : Nat) : Int) h.s.tally b' hprog
  have hk : h.done.length = i := h.k_eq.symm
  have hrest : h.rest = L.drop i := by
    have happ : (h.done ++ h.rest).drop h.done.length = h.rest := by
      simp
    simpa [h.split, hk] using happ.symm
  have hcons : h.rest = (L[i]'hi) :: L.drop (i + 1) := by
    rw [hrest]
    exact drop_get_cons L i hi
  have hinv : ClimbInvK h.done ((L[i]'hi) :: L.drop (i + 1)) b h.s base := by
    simpa [hcons] using h.inv
  have hCap' : climbTallyPrefix base.tally0 h.done ((L[i]'hi) :: L.drop (i + 1)) ≤ base.mMax := by
    simpa [hcons] using hCap
  match climb_step hinv h.m_pos hPark hCap' hxLen hxT with
  | ⟨b1, hrun, hK⟩ =>
    have hb : b1 = b' := by
      rw [hrun] at hprog
      exact Except.ok.inj hprog
    subst hb
    let rung := L[i]'hi
    let last := (L.drop (i + 1)).isEmpty
    let s' := modelRung h.s base.x rung (climbAt base.ladder0 base.R h.s.ridx) last
    refine ⟨⟨h.done ++ [rung], L.drop (i + 1), s', ?split, ?k, ?inv, ?lad, ?pos, ?le, ?len⟩, ?park⟩
    · have hs := h.split
      rw [hcons] at hs
      simpa [List.append_assoc, rung] using hs
    · simp [List.length_append, List.length_singleton, h.k_eq, rung]
    · simpa [rung, last, s'] using hK
    · rw [hlad, h.ladder]
    · rw [modelRung_tally]
      exact Nat.lt_of_lt_of_le h.m_pos (tallyAfter_ge h.s.tally rung last)
    · exact Nat.le_trans hK.finalLe
        (Nat.le_trans (Nat.le_add_left _ _)
          (Nat.le_trans hK.tailFit (Nat.le_of_eq hK.shape.rowLen)))
    · have hlen := hK.inv.len
      simpa [s', ofNat_eq_natCast] using hlen
    · simp [s', modelRung, hPark]

/-- The index step of `invertWith`: break past `toV`, otherwise the named rung. -/
def invertIdx (x nr toV : Int) (σ : Int × Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board) :=
  let idx := σ.1
  let b := σ.2
  do
    if idx > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (idx, b))
    else
      match ← (do
        let t ← SudoRt.subI nr (1 : Int)
        let last := SudoRt.SEq.beq idx t
        let rv ← SudoRt.atL b.sudo_5Board_6ladder idx
        let b ← Ecbs.park_rung b rv
        let b ← Ecbs.copy_band b Ecbs.spare Ecbs.gap false
        let m := b.sudo_5Board_9tally_len
        let toW ← SudoRt.subI m (1 : Int)
        let fromW := (0 : Int)
        let fuelW : Nat := if fromW > toW then 1 else (toW - fromW).natAbs + 1
        let out ← SudoRt.runLoopOn (ρ := Ecbs.Board) fromW fuelW (whiteStep b toW)
          (fun _ => rungAfterNamed x rv last b m)
          (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))
        pure out) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (idx, fs))
      | .cont fs => do
          if idx == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (idx, fs))
          else do
            let i' ← SudoRt.addI idx (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs))

/-- Past the last rung the index step breaks on the board it was given. -/
theorem invertIdx_hi (x : Int) (n i : Nat) (b : Ecbs.Board) (hn : 0 < n) (hi : n ≤ i) :
    invertIdx x (Int.ofNat n) (Int.ofNat (n - 1)) ((i : Int), b) =
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) ((i : Int), b)) := by
  unfold invertIdx
  dsimp only
  have hgt : (i : Int) > Int.ofNat (n - 1) := by
    have hlt : n - 1 < i := by omega
    simpa [GT.gt] using (Int.ofNat_lt.mpr hlt)
  rw [if_pos hgt]

/-- One in-range index is the hand-written rung, then break on the last rung
    and continue with the next index otherwise. -/
theorem invertIdx_step
    (b : Ecbs.Board) (L : List Nat) (x : Int) (i m : Nat)
    (hi : i < L.length) (hfitL : FitsLen L.length)
    (hL : b.sudo_5Board_6ladder = embed L)
    (hm : 0 < m) (hfit : FitsLen m)
    (hlen : b.sudo_5Board_9tally_len = Int.ofNat m) :
    invertIdx x (Int.ofNat L.length) (Int.ofNat (L.length - 1)) ((i : Int), b) =
      (climbRung b (L[i]'hi) ((L.drop (i + 1)).isEmpty) x m >>= fun b' =>
        pure (if (L.drop (i + 1)).isEmpty = true then
          SudoRt.Flow.brk (ρ := Ecbs.Board) ((i : Int), b')
        else
          SudoRt.Flow.cont (ρ := Ecbs.Board) (((i + 1 : Nat) : Int), b'))) := by
  unfold invertIdx
  dsimp only
  have hpos : 0 < L.length := Nat.lt_of_le_of_lt (Nat.zero_le i) hi
  have hng : ¬ ((i : Int) > Int.ofNat (L.length - 1)) :=
    not_gt_cast (Nat.le_sub_one_of_lt hi)
  rw [if_neg hng]
  simp only [except_bind_pure]
  rw [inv_named_step_len b L x i m hi hpos hfitL hL hm hfit hlen]
  rw [bind_assoc]
  simp only [pure_bind]
  have hadd : SudoRt.addI (i : Int) (1 : Int) =
      .ok (((i + 1 : Nat) : Int)) :=
    addI_ofNat_one i (FitsLen.of_le hfitL (Nat.succ_le_of_lt hi))
  have hflag : ((i : Int) == Int.ofNat (L.length - 1)) =
      (L.drop (i + 1)).isEmpty := by
    have hbeq : ((i : Int) == Int.ofNat (L.length - 1)) =
        SudoRt.SEq.beq (Int.ofNat i) (Int.ofNat (L.length - 1)) := by
      simp [sEq_int, BEq.beq]
    rw [hbeq, last_flag L i hi]
  apply bind_pointwise
  intro b'
  rw [hflag]
  rw [hadd]
  simp only [ok_bind, pure_eq_ok]
  cases (L.drop (i + 1)).isEmpty <;> rfl

/-- The emitted ladder, with the final unpark-cube-settle-clear as the tail.
    `runLoop_drop_inv_bind` is the fuel induction. -/
theorem emit_bind
    (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (L : List Nat) (b : Ecbs.Board)
    (body : Int × Ecbs.Board → Except SudoRt.Trap
      (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board))
    (onRet : Ecbs.Board → Except SudoRt.Trap Ecbs.Board)
    (P : Nat → Ecbs.Board → Prop)
    (hP : P 0 b)
    (hpos : 0 < L.length) (fuel : Nat)
    (hfuel : fuelRange (Int.ofNat 0) (Int.ofNat (L.length - 1)) ≤ fuel)
    (hbody : ∀ i (b : Ecbs.Board) (hi : i < L.length),
      P i b →
      body (Int.ofNat i, b) =
        (step b (L[i]'hi) ((L.drop (i + 1)).isEmpty) >>= fun b' =>
          pure (if (L.drop (i + 1)).isEmpty = true then
            SudoRt.Flow.brk (Int.ofNat i, b')
          else
            SudoRt.Flow.cont (Int.ofNat (i + 1), b'))))
    (hkeep : ∀ i (b b' : Ecbs.Board) (hi : i < L.length),
      P i b →
      step b (L[i]'hi) ((L.drop (i + 1)).isEmpty) = .ok b' →
      P (i + 1) b')
    (hhi : ∀ i (b : Ecbs.Board), L.length ≤ i →
      body (Int.ofNat i, b) = pure (SudoRt.Flow.brk (Int.ofNat i, b))) :
    SudoRt.runLoopOn (Int.ofNat 0, b) fuel body (fun σ => finalTail σ.2) onRet =
      climbEmit step b L >>= finalTail :=
  runLoop_drop_inv_bind step L 0 b body (fun σ => finalTail σ.2) onRet finalTail P
    hP hpos (Nat.zero_le _) fuel hfuel hbody hkeep hhi (fun _ _ => rfl)

/-- The index loop, once the board carries `ClimbInvL`, is the climb bound into
    the unpark, final cube, settle, and tally clear. -/
theorem invert_loop_emit
    {L : List Nat} {b : Ecbs.Board} {base : ClimbBudget}
    (h : ClimbInvL L 0 b base)
    (hpos : 0 < L.length) (hfitL : FitsLen L.length)
    (hPark : h.s.parkAt = base.ladder0 + base.R)
    (hCap : ∀ done rest, L = done ++ rest →
      climbTallyPrefix base.tally0 done rest ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x)
    (onRet : Ecbs.Board → Except SudoRt.Trap Ecbs.Board) :
    let x : Int := ((base.xHome : Nat) : Int)
    SudoRt.runLoopOn (Int.ofNat 0, b)
        (fuelRange (Int.ofNat 0) (Int.ofNat (L.length - 1)))
        (invertIdx x (Int.ofNat L.length) (Int.ofNat (L.length - 1)))
        (fun σ => finalTail σ.2) onRet =
      climbEmit (climbStepBoard x) b L >>= finalTail := by
  intro x
  let step := climbStepBoard x
  let body := invertIdx x (Int.ofNat L.length) (Int.ofNat (L.length - 1))
  let P : Nat → Ecbs.Board → Prop := fun i b =>
    ∃ inv : ClimbInvL L i b base, inv.s.parkAt = base.ladder0 + base.R
  apply emit_bind step L b body onRet P ⟨h, hPark⟩ hpos
    (fuelRange (Int.ofNat 0) (Int.ofNat (L.length - 1))) (Nat.le_refl _)
  · intro i b0 hi hP
    rcases hP with ⟨inv, _hpark⟩
    have hfit := ClimbInvL.m_fit inv
    have hidx := invertIdx_step b0 L x i inv.s.tally hi hfitL inv.ladder
      inv.m_pos hfit inv.m_len
    have hto : b0.sudo_5Board_9tally_len.toNat = inv.s.tally := by
      rw [inv.m_len]
      exact Int.toNat_ofNat _
    simpa [step, climbStepBoard, hto] using hidx
  · intro i b0 b1 hi hP hrun
    rcases hP with ⟨inv, hpark⟩
    have hfit := ClimbInvL.m_fit inv
    have hto : b0.sudo_5Board_9tally_len.toNat = inv.s.tally := by
      rw [inv.m_len]
      exact Int.toNat_ofNat _
    have hprog : climbRung b0 (L[i]'hi) ((L.drop (i + 1)).isEmpty) x inv.s.tally =
        .ok b1 := by
      simpa [step, climbStepBoard, hto] using hrun
    exact climbL_succ inv hi hpark (hCap inv.done inv.rest inv.split) hxLen hxT hprog
  · intro i b0 hi
    simpa [body, x] using invertIdx_hi x L.length i b0 hpos hi

/-- The loop inside `invertWith`, on a board that already carries the climb,
    is the climb bound into the final tail. The length is the ladder's. -/
theorem invertWith_on_inv
    {L : List Nat} {b : Ecbs.Board} {base : ClimbBudget}
    (h : ClimbInvL L 0 b base)
    (hpos : 0 < L.length) (hfitL : FitsLen L.length)
    (hPark : h.s.parkAt = base.ladder0 + base.R)
    (hCap : ∀ done rest, L = done ++ rest →
      climbTallyPrefix base.tally0 done rest ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    (do
      let nr := SudoRt.listLen b.sudo_5Board_6ladder
      let toV ← SudoRt.subI nr (1 : Int)
      let fromV := (0 : Int)
      let fuel : Nat := if fromV > toV then 1 else (toV - fromV).natAbs + 1
      let out ← SudoRt.runLoopOn (ρ := Ecbs.Board) (fromV, b) fuel
        (invertIdx ((base.xHome : Nat) : Int) nr toV)
        (fun σ => finalTail σ.2)
        (fun r => pure r)
      pure out) =
      climbEmit (climbStepBoard ((base.xHome : Nat) : Int)) b L >>= finalTail := by
  have hlenL : SudoRt.listLen b.sudo_5Board_6ladder = Int.ofNat L.length := by
    rw [h.ladder, listLen_embed]
  have hfuel := tally_len_fuel L.length hpos hfitL
  simp only [hlenL, hfuel.1, ok_bind, hfuel.2, except_bind_pure]
  exact invert_loop_emit h hpos hfitL hPark hCap hxLen hxT (fun r => pure r)

/-- Unpark, the final cube, settle, and `tally_clear`, as the loop's after. -/
theorem invert_after_tail (σ : Int × Ecbs.Board) :
    (do
      let b := σ.2
      let b ← Ecbs.unpark_rung b
      let b ← Ecbs.cube b Ecbs.gap Ecbs.gap
      let b ← Ecbs.settle b
      let b ← Ecbs.tally_clear b
      pure b) = finalTail σ.2 := by
  simp [finalTail, except_bind_pure]

/-- `invertWith` on the named tail is the ops bump, the gap copy, and `tally_start`,
    then the index loop whose after is the final tail. -/
theorem invertWith_named_loop (b : Ecbs.Board) (x : Int) :
    invertWith rungAfterNamed b x =
      (do
        let ix := Ecbs.op_inv
        let t1 ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_inv
        let t2 ← SudoRt.addI t1 (1 : Int)
        let t3 ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops ix t2
        let cost := ({ b.sudo_5Board_4cost with sudo_5Costs_3ops := t3 } : Ecbs.Costs)
        let b := ({ b with sudo_5Board_4cost := cost } : Ecbs.Board)
        let b ← Ecbs.copy_band b Ecbs.gap x false
        let b ← Ecbs.tally_start b
        let nr := SudoRt.listLen b.sudo_5Board_6ladder
        let toV ← SudoRt.subI nr (1 : Int)
        let fromV := (0 : Int)
        let fuel : Nat := if fromV > toV then 1 else (toV - fromV).natAbs + 1
        let out ← SudoRt.runLoopOn (ρ := Ecbs.Board) (fromV, b) fuel
          (invertIdx x nr toV)
          (fun σ => finalTail σ.2)
          (fun r => pure r)
        pure out) := by
  unfold invertWith
  dsimp only
  conv =>
    lhs
    pattern (fun σ : Int × Ecbs.Board => _)
    change invertIdx x (SudoRt.listLen b.sudo_5Board_6ladder) toV
  simp only [invert_after_tail]

theorem invert_named_loop (b : Ecbs.Board) (x : Int) :
    Ecbs.invert b x =
      (do
        let ix := Ecbs.op_inv
        let t1 ← SudoRt.atL b.sudo_5Board_4cost.sudo_5Costs_3ops Ecbs.op_inv
        let t2 ← SudoRt.addI t1 (1 : Int)
        let t3 ← SudoRt.putL b.sudo_5Board_4cost.sudo_5Costs_3ops ix t2
        let cost := ({ b.sudo_5Board_4cost with sudo_5Costs_3ops := t3 } : Ecbs.Costs)
        let b := ({ b with sudo_5Board_4cost := cost } : Ecbs.Board)
        let b ← Ecbs.copy_band b Ecbs.gap x false
        let b ← Ecbs.tally_start b
        let nr := SudoRt.listLen b.sudo_5Board_6ladder
        let toV ← SudoRt.subI nr (1 : Int)
        let fromV := (0 : Int)
        let fuel : Nat := if fromV > toV then 1 else (toV - fromV).natAbs + 1
        let out ← SudoRt.runLoopOn (ρ := Ecbs.Board) (fromV, b) fuel
          (invertIdx x nr toV)
          (fun σ => finalTail σ.2)
          (fun r => pure r)
        pure out) := by
  rw [invert_steps]
  exact invertWith_named_loop b x

theorem modelClimb_onBench (s : ClimbModel) (x : List Nat)
    (hole : ClimbModel → Nat → Bool → Nat) (r : Nat) (rs : List Nat) :
    (modelClimb s x hole (r :: rs)).onBench = true := by
  induction rs generalizing s r with
  | nil => simp [modelClimb, modelRung]
  | cons r' rs ih =>
    rw [modelClimb]
    exact ih (modelRung s x r (hole s r ((r' :: rs).isEmpty)) ((r' :: rs).isEmpty)) r'

theorem modelClimb_fromHole (s : ClimbModel) (x : List Nat)
    (hole : ClimbModel → Nat → Bool → Nat) (r : Nat) (rs : List Nat) :
    0 ≤ (modelClimb s x hole (r :: rs)).fromHole := by
  induction rs generalizing s r with
  | nil =>
    simp [modelClimb, modelRung]
    exact Int.ofNat_nonneg _
  | cons r' rs ih =>
    rw [modelClimb]
    exact ih (modelRung s x r (hole s r ((r' :: rs).isEmpty)) ((r' :: rs).isEmpty)) r'

/-- The climb, then unpark, the final cube, settle, and `tally_clear`. -/
theorem climb_then_tail
    {L : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK [] L b s base)
    (hpos : 0 < L.length)
    (hPark : s.parkAt = base.ladder0 + base.R)
    (hm : 0 < s.tally)
    (hCap : ∀ done rest, L = done ++ rest →
      climbTallyPrefix base.tally0 done rest ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ bZ, climbEmit (climbStepBoard ((base.xHome : Nat) : Int)) b L >>= finalTail = .ok bZ := by
  obtain ⟨b', s', hrun, hs', hK, _, htally⟩ :=
    climb_refines_emit L b s base h hPark hm hCap hxLen hxT
  have hcons : ∃ r rs, L = r :: rs := by
    cases L with
    | nil =>
      simp at hpos
    | cons r rs => exact ⟨r, rs, rfl⟩
  obtain ⟨r, rs, hL⟩ := hcons
  have hon : s'.onBench = true := by
    rw [hs', hL]
    exact modelClimb_onBench s base.x
      (fun s _ _ => climbAt base.ladder0 base.R s.ridx) r rs
  have hge : 0 ≤ s'.fromHole := by
    rw [hs', hL]
    exact modelClimb_fromHole s base.x
      (fun s _ _ => climbAt base.ladder0 base.R s.ridx) r rs
  have hm' : 0 < s'.tally := by
    rw [hs', modelClimb_tally]
    exact Nat.lt_of_lt_of_le hm (climbTally_ge s.tally L)
  obtain ⟨bU, bC, bOut, bZ, _, _, _, hun, hc, hset, hz, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    final_cube_settle hK hon hge htally hm'
  refine ⟨bZ, ?_⟩
  rw [hrun, ok_bind]
  simp [finalTail, hun, hc, hset, hz, ok_bind]

end EcbsLink2.Link2
