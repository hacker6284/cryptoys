/-
  The ladder array on the tally board is climb order. Unfolding `Ecbs.invert`
  reaches `whiteStep`, `cubePegStep`, and `rungTail`.
-/
import EcbsLink2.Link2.GenRung
import EcbsLink2.Link2.EntryRung

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem gap_ladder (t : Spec.Tier) (xs : List Nat) :
    (gapBoard t xs).sudo_5Board_6ladder = embed (tierClimb t) := by
  simp [gapBoard, bumpedBoard, bumpOp, bottomBoard, builtBoard, midBoard, placed, blankOf,
    tierClimb]

theorem tally_ladder (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    (tallyBoard t xs sat hR).sudo_5Board_6ladder = embed (tierClimb t) := by
  simp [tallyBoard, gap_ladder]

theorem tierR_fit (t : Spec.Tier) (h : BoardOk t) : FitsLen (tierR t) := by
  apply FitsLen.of_le (fits_of h.fits_control)
  unfold tierR
  have hL := h.ladder
  omega

theorem entry_atL (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t)
    (i : Nat) (hi : i < tierR t) :
    SudoRt.atL (tallyBoard t xs sat hR).sudo_5Board_6ladder (Int.ofNat i) =
      .ok ((tierClimb t)[i]'(by
        unfold tierClimb
        rw [List.length_reverse]
        simpa [tierR] using hi) : Int) := by
  rw [tally_ladder t xs sat hR]
  exact atL_embed (tierClimb t) i (by
    unfold tierClimb
    rw [List.length_reverse]
    simpa [tierR] using hi)

/-- The white scan inside `Ecbs.invert`, ascription included, is `whiteStep`. -/
theorem white_ascribed (b : Ecbs.Board) (toV : Int) :
    (fun (σ : Int) =>
      (do
        if σ > toV then
          pure (SudoRt.Flow.brk (ρ := Ecbs.Board) σ)
        else
          match ← (do
            let ix ← SudoRt.addI b.sudo_5Board_6tally0 σ
            let c ← SudoRt.atL b.sudo_5Board_3row ix
            SudoRt.sudoAssertEq c (1 : Int) 703
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) ())) with
          | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
          | .brk _ => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) σ)
          | .cont _ =>
              if (σ == toV) = true then
                pure (SudoRt.Flow.brk (ρ := Ecbs.Board) σ)
              else do
                let i' ← SudoRt.addI σ (1 : Int)
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) i'))) =
      whiteStep b toV := by
  unfold whiteStep
  rfl

/-- The cube-peg step inlined in `Ecbs.invert`, as a name `cube_inline` rewrites. -/
def cubeInline (toV : Int) :
    (Int × Ecbs.Board) → Except SudoRt.Trap
      (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board) :=
  fun σ =>
    (do
      let j := σ.1
      let b := σ.2
      if j > toV then
        pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (j, b))
      else
        match ← (do
          let b ← Ecbs.cube b Ecbs.spare Ecbs.spare
          let b ← Ecbs.tally_put b j (2 : Int)
          let v ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
          let b := ({ b with sudo_5Board_4cost :=
            { b.sudo_5Board_4cost with sudo_5Costs_4ctrl := v } } : Ecbs.Board)
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
        | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (j, fs))
        | .cont fs => do
            if j == toV then
              pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (j, fs))
            else do
              let j' ← SudoRt.addI j (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (j', fs)))

theorem cubeInline_eq (toV : Int) : cubeInline toV = cubePegStep 6 toV := by
  unfold cubeInline
  exact cube_inline toV

/-- The mul-clear-nest tail inlined in `Ecbs.invert`. -/
def tailInline (rung x : Int) (last : Bool) :
    (Int × Ecbs.Board) → Except SudoRt.Trap (SudoRt.Flow Ecbs.Board Ecbs.Board) :=
  fun σ =>
    (do
      let b := σ.2
      let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
      let b ← Ecbs.clear b Ecbs.gap
      if (!(last)) then
        do
          let b ← Ecbs.tally_double b
          if (SudoRt.SEq.beq rung (2 : Int)) then
            do
              let b ← Ecbs.cube b Ecbs.spare Ecbs.gap
              let b ← Ecbs.mul b Ecbs.gap x Ecbs.spare false false false
              if (!(last)) then
                do
                  let b ← Ecbs.tally_add_one b
                  pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
              else
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
          else
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
      else
        do
          if (SudoRt.SEq.beq rung (2 : Int)) then
            do
              let b ← Ecbs.cube b Ecbs.spare Ecbs.gap
              let b ← Ecbs.mul b Ecbs.gap x Ecbs.spare false false false
              if (!(last)) then
                do
                  let b ← Ecbs.tally_add_one b
                  pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
              else
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
          else
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b))

theorem tailInline_eq (rung x : Int) (last : Bool) :
    tailInline rung x last = fun σ => rungTail rung x last σ.2 := by
  funext σ
  unfold tailInline
  dsimp only
  exact tail_inline rung x last σ.2

/-- Cube-peg loop and tail, still written as the emitted text. -/
def rungAfter (x rv : Int) (last : Bool) (b : Ecbs.Board) (m : Int) :
    Except SudoRt.Trap (SudoRt.Flow Ecbs.Board Ecbs.Board) :=
  do
    let toC ← SudoRt.subI m (1 : Int)
    let fromC := (0 : Int)
    let fuelC : Nat := if fromC > toC then 1 else (toC - fromC).natAbs + 1
    let out ← SudoRt.runLoopOn (ρ := Ecbs.Board) (fromC, b) fuelC (cubeInline toC)
      (tailInline rv x last)
      (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))
    pure out

/-- The same loop written as `cubePegStep` and `rungTail`. -/
def rungAfterNamed (x rv : Int) (last : Bool) (b : Ecbs.Board) (m : Int) :
    Except SudoRt.Trap (SudoRt.Flow Ecbs.Board Ecbs.Board) :=
  do
    let toC ← SudoRt.subI m (1 : Int)
    let fromC := (0 : Int)
    let fuelC : Nat := if fromC > toC then 1 else (toC - fromC).natAbs + 1
    let out ← SudoRt.runLoopOn (ρ := Ecbs.Board) (fromC, b) fuelC (cubePegStep 6 toC)
      (fun σ => rungTail rv x last σ.2)
      (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))
    pure out

theorem rungAfter_named (x rv : Int) (last : Bool) (b : Ecbs.Board) (m : Int) :
    rungAfter x rv last b m = rungAfterNamed x rv last b m := by
  unfold rungAfter rungAfterNamed
  apply bind_pointwise
  intro toC
  dsimp only
  rw [cubeInline_eq toC, tailInline_eq rv x last]

/-- `Ecbs.invert`, with the white scan, the cube-peg step, and the tail passed
    in as `nest`. -/
def invertWith
    (nest : Int → Int → Bool → Ecbs.Board → Int →
      Except SudoRt.Trap (SudoRt.Flow Ecbs.Board Ecbs.Board))
    (b : Ecbs.Board) (x : Int) : Except SudoRt.Trap Ecbs.Board :=
  do
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
    let out ← SudoRt.runLoopOn (ρ := Ecbs.Board) (fromV, b) fuel (fun σ =>
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
              (fun _ => nest x rv last b m)
              (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))
            pure out) with
          | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
          | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (idx, fs))
          | .cont fs => do
              if idx == toV then
                pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (idx, fs))
              else do
                let i' ← SudoRt.addI idx (1 : Int)
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs)))
      (fun σ => do
        let b := σ.2
        let b ← Ecbs.unpark_rung b
        let b ← Ecbs.cube b Ecbs.gap Ecbs.gap
        let b ← Ecbs.settle b
        let b ← Ecbs.tally_clear b
        pure b)
      (fun r => pure r)
    pure out

/-- Unfolding `Ecbs.invert` reaches `whiteStep`, `cubePegStep`, and `rungTail`.
    The white scan is definitionally `whiteStep`. The cube step and the tail
    are `cubeInline` and `tailInline`, which are those two names. -/
theorem invert_white (b : Ecbs.Board) (x : Int) :
    Ecbs.invert b x = invertWith rungAfter b x := by
  unfold Ecbs.invert invertWith rungAfter cubeInline tailInline whiteStep
  dsimp only
  rfl

theorem invert_with_named (b : Ecbs.Board) (x : Int) :
    invertWith rungAfter b x = invertWith rungAfterNamed b x := by
  unfold invertWith
  simp only [rungAfter_named]

/-- `Ecbs.invert` is the loop whose scans are `whiteStep`, `cubePegStep`, and
    `rungTail`. -/
theorem invert_steps (b : Ecbs.Board) (x : Int) :
    Ecbs.invert b x = invertWith rungAfterNamed b x := by
  rw [invert_white]
  exact invert_with_named b x

/-- The named cube-peg loop is the continuation `genRung_eq_climbRung` sequences
    after the white scan, when `m` is that board's tally length. -/
theorem rungAfterNamed_scan (x rv : Int) (last : Bool) (b : Ecbs.Board) :
    rungAfterNamed x rv last b b.sudo_5Board_9tally_len =
      (do
        let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
        let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
        SudoRt.runLoopOn ((0 : Int), b) fuel (cubePegStep 6 toV)
          (fun σ => rungTail rv x last σ.2)
          (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))) := by
  unfold rungAfterNamed
  dsimp only
  apply bind_pointwise
  intro toC
  rw [except_bind_pure]

/-- One rung of the named loop is `climbRung` then `Flow.cont`. The ladder read,
    the last-index flag, and `FitsLen` of the tally length are the facts the
    loop index and the invariant supply; they are not premises of `invert_steps`. -/
theorem named_rung_step
    (b : Ecbs.Board) (x idx nr lastIdx : Int) (rung : Nat) (last : Bool) (m : Nat)
    (hm : 0 < m) (hfit : FitsLen m)
    (hlen : b.sudo_5Board_9tally_len = Int.ofNat m)
    (hsub : SudoRt.subI nr (1 : Int) = .ok lastIdx)
    (hlast : SudoRt.SEq.beq idx lastIdx = last)
    (hat : SudoRt.atL b.sudo_5Board_6ladder idx = .ok (rung : Int)) :
    (do
      let t ← SudoRt.subI nr (1 : Int)
      let lastB := SudoRt.SEq.beq idx t
      let rv ← SudoRt.atL b.sudo_5Board_6ladder idx
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
  simp only [rungAfterNamed_scan]
  exact genRung_eq_climbRung b x idx nr lastIdx rung last m hm hfit hlen hsub hlast hat

theorem entry_ladder_len (t : Spec.Tier) (xs : List Nat) (sat : TierSat t) (hR : 0 < tierR t) :
    SudoRt.listLen (tallyBoard t xs sat hR).sudo_5Board_6ladder = Int.ofNat (tierR t) := by
  rw [tally_ladder t xs sat hR, listLen_embed]
  unfold tierClimb
  rw [List.length_reverse]
  simp [tierR]

/-- On the tally board the three reads are the tier: the ladder cell is the
    climb-order rung, the last-index flag is the empty tail, and the length is 1. -/
theorem entry_named_step
    (t : Spec.Tier) (h : BoardOk t) (xs : List Nat) (sat : TierSat t)
    (hR : 0 < tierR t) (x : Int) (i : Nat) (hi : i < tierR t) :
    let b := tallyBoard t xs sat hR
    let rung := (tierClimb t)[i]'(by
      unfold tierClimb
      rw [List.length_reverse]
      simpa [tierR] using hi)
    let last := ((tierClimb t).drop (i + 1)).isEmpty
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
        let b ← climbRung b rung last x 1
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) := by
  intro b rung last
  have hm : (0 : Nat) < 1 := by decide
  have hfit1 : FitsLen 1 := by unfold FitsLen i64MaxNat; decide
  have hlen : b.sudo_5Board_9tally_len = Int.ofNat 1 := by
    simp [b, tallyBoard]
  have hrung : i < (tierClimb t).length := by
    unfold tierClimb
    rw [List.length_reverse]
    simpa [tierR] using hi
  have hlenR : (tierClimb t).length = tierR t := by
    unfold tierClimb tierR
    rw [List.length_reverse]
  have hsub : SudoRt.subI (Int.ofNat (tierR t)) (1 : Int) =
      .ok (Int.ofNat (tierR t - 1)) :=
    subI_ofNat_one (tierR t) hR (tierR_fit t h)
  have hlast : SudoRt.SEq.beq (Int.ofNat i) (Int.ofNat (tierR t - 1)) = last := by
    have hflag := last_flag (tierClimb t) i hrung
    rw [hlenR] at hflag
    simpa [last] using hflag
  have hat : SudoRt.atL b.sudo_5Board_6ladder (Int.ofNat i) = .ok (rung : Int) := by
    simpa [b, rung] using entry_atL t xs sat hR i hi
  have hnr := entry_ladder_len t xs sat hR
  simp only [b] at hnr
  rw [hnr]
  exact named_rung_step b x (Int.ofNat i) (Int.ofNat (tierR t))
    (Int.ofNat (tierR t - 1)) rung last 1 hm hfit1 hlen hsub hlast hat

end EcbsLink2.Link2
