/-
  The white scan, the cube-peg step, and the mul-clear-nest inside `Ecbs.invert`
  are `whiteStep`, `cubePegStep`, and `rungTail`. `genRung_eq_climbRung` is that
  body, from the ladder read through `Flow.cont`, equal to `climbRung`.
-/
import EcbsLink2.Link2.RungBody

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- The white scan inlined in `invert` is `whiteStep`. -/
theorem white_inline (b : Ecbs.Board) (toV : Int) :
    (fun (j : Int) =>
      (do
        if j > toV then
          pure (SudoRt.Flow.brk (ρ := Ecbs.Board) j)
        else
          match ← (do
            let ix ← SudoRt.addI b.sudo_5Board_6tally0 j
            let c ← SudoRt.atL b.sudo_5Board_3row ix
            let _ ← SudoRt.sudoAssertEq c (1 : Int) 703
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) ())) with
          | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
          | .brk _ => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) j)
          | .cont _ => do
              if j == toV then
                pure (SudoRt.Flow.brk (ρ := Ecbs.Board) j)
              else do
                let j' ← SudoRt.addI j (1 : Int)
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) j')) :
        Int → Except SudoRt.Trap (SudoRt.Flow Int Ecbs.Board)) =
      whiteStep b toV := by
  unfold whiteStep
  rfl

/-- The inlined cube, red peg, and control bump, wrapped as `Flow.cont`. -/
private theorem cube_body_cont (b : Ecbs.Board) (j : Int) :
    (do
      let b ← Ecbs.cube b Ecbs.spare Ecbs.spare
      let b ← Ecbs.tally_put b j (2 : Int)
      let v ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board)
        ({ b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_4ctrl := v } } : Ecbs.Board))) =
      (do
        let b' ← cubePegBody 6 b j
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b')) := by
  unfold cubePegBody Ecbs.spare
  rw [bind_assoc]
  apply bind_pointwise
  intro b1
  rw [bind_assoc]
  apply bind_pointwise
  intro b2
  rw [bind_assoc]
  apply bind_pointwise
  intro v
  rw [pure_bind]

/-- The cube-peg step inlined in `invert` is `cubePegStep` at spare `6`. -/
theorem cube_inline (toV : Int) :
    (fun (σ : Int × Ecbs.Board) =>
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
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (j', fs))) :
        (Int × Ecbs.Board) → Except SudoRt.Trap
          (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board)) =
      cubePegStep 6 toV := by
  funext σ
  unfold cubePegStep
  dsimp only
  rw [cube_body_cont σ.2 σ.1]
  rfl

/-- Mul, clear, and the leaf `Flow.cont` nest are `rungTail`. -/
theorem tail_inline (rung x : Int) (last : Bool) (b : Ecbs.Board) :
    (do
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
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) =
      rungTail rung x last b := by
  rw [← bind_assoc]
  rw [← nest_under
      (Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false >>=
        fun b => Ecbs.clear b Ecbs.gap)]
  unfold Ecbs.spare Ecbs.gap
  rw [bind_assoc]
  apply Eq.symm
  rw [rungTail_eq]
  unfold rungNest
  rfl

/-- The ladder read, park, the spare copy, and the scans inside `Ecbs.invert`
    are `climbRung` then `Flow.cont`. `white_inline`, `cube_inline`, and
    `tail_inline` are those scans. The length that reaches the loops is the
    length `park_rung` and `copy_band` preserve. -/
theorem genRung_eq_climbRung
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
      let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
      let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
      SudoRt.runLoopOn (Int.ofNat 0) fuel (whiteStep b toV)
        (fun _ => do
          let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
          let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
          SudoRt.runLoopOn (Int.ofNat 0, b) fuel (cubePegStep 6 toV)
            (fun σ => rungTail rv x lastB σ.2)
            (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)))
        (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))) =
      (do
        let b ← climbRung b rung last x m
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) := by
  rw [hsub]
  simp only [ok_bind]
  rw [hlast, hat]
  simp only [ok_bind]
  unfold Ecbs.spare Ecbs.gap
  exact climbRung_nested b rung last x m hm hfit hlen

/-- `climb_holes` reads the ladder origin and the rung count. A tally write,
    which replaces the row, the length, and three cost fields, does not change it. -/
theorem climb_holes_idx (b1 b2 : Ecbs.Board)
    (h0 : b1.sudo_5Board_7ladder0 = b2.sudo_5Board_7ladder0)
    (hn : b1.sudo_5Board_6nrungs = b2.sudo_5Board_6nrungs) :
    Ecbs.climb_holes b1 = Ecbs.climb_holes b2 := by
  unfold Ecbs.climb_holes
  rw [h0, hn]

/-- `ClimbInvK` supplies the tally length. The ladder read, the last-index
    flag, and the i64 fit of that length are the facts the invariant does not
    store. -/
theorem genRung_of_inv
    {done rest : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (rung : Nat) (hK : ClimbInvK done (rung :: rest) b s base)
    (x idx nr lastIdx : Int) (last : Bool)
    (hm : 0 < s.tally) (hfit : FitsLen s.tally)
    (hsub : SudoRt.subI nr (1 : Int) = .ok lastIdx)
    (hlast : SudoRt.SEq.beq idx lastIdx = last)
    (hat : SudoRt.atL b.sudo_5Board_6ladder idx = .ok (rung : Int)) :
    (do
      let t ← SudoRt.subI nr (1 : Int)
      let lastB := SudoRt.SEq.beq idx t
      let rv ← SudoRt.atL b.sudo_5Board_6ladder idx
      let b ← Ecbs.park_rung b rv
      let b ← Ecbs.copy_band b Ecbs.spare Ecbs.gap false
      let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
      let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
      SudoRt.runLoopOn (Int.ofNat 0) fuel (whiteStep b toV)
        (fun _ => do
          let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
          let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
          SudoRt.runLoopOn (Int.ofNat 0, b) fuel (cubePegStep 6 toV)
            (fun σ => rungTail rv x lastB σ.2)
            (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)))
        (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))) =
      (do
        let b ← climbRung b rung last x s.tally
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) := by
  exact genRung_eq_climbRung b x idx nr lastIdx rung last s.tally hm hfit
    (by rw [hK.inv.len, ← ofNat_eq_natCast]) hsub hlast hat

end EcbsLink2.Link2
