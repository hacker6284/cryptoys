/-
  The generated rung nests the cube-peg loop, the gap mul, and clear as the
  `after` of the white scan. `whiteStep` and `cubePegStep` never return, so
  that nest is the sequenced pair of loops in `climbClear`. The fuel is
  `subI` of the tally length.
-/
import EcbsLink2.Link2.LadderKeep

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- Nested white scan then cube-peg loop, against the sequenced loops
    `climbClear` runs. The `onRet` handlers are unused. -/
theorem white_cube_nest {α : Type}
    (b : Ecbs.Board) (m : Nat) (hm : 0 < m) (hfit : FitsLen m)
    (hlen : b.sudo_5Board_9tally_len = Int.ofNat m)
    (rest : Ecbs.Board → Except SudoRt.Trap α)
    (onRetN : Ecbs.Board → Except SudoRt.Trap α)
    (onRetW : Ecbs.Board → Except SudoRt.Trap (Ecbs.Board × Int))
    (onRetIdW : Ecbs.Board → Except SudoRt.Trap Int)
    (onRetG : Ecbs.Board → Except SudoRt.Trap α)
    (onRetC : Ecbs.Board → Except SudoRt.Trap (Int × Ecbs.Board))
    (onRetIdC : Ecbs.Board → Except SudoRt.Trap (Int × Ecbs.Board)) :
    (do
      let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
      let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
      SudoRt.runLoopOn (Int.ofNat 0) fuel (whiteStep b toV)
        (fun _ => do
          let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
          let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
          let out ← SudoRt.runLoopOn (Int.ofNat 0, b) fuel (cubePegStep 6 toV)
            (fun σ => rest σ.2) onRetG
          pure out)
        onRetN) =
      (do
        let _ ← SudoRt.runLoopOn (Int.ofNat 0)
            (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
            (whiteStep b (Int.ofNat (m - 1)))
            (fun j => .ok (b, j)) onRetW
        let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
            (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
            (cubePegStep 6 (Int.ofNat (m - 1)))
            (fun σ => .ok σ) onRetC
        rest out.2) := by
  rw [hlen]
  have hsub : SudoRt.subI (Int.ofNat m) 1 = .ok (Int.ofNat (m - 1)) :=
    (tally_len_fuel m hm hfit).1
  have hfuel :
      (if (0 : Int) > Int.ofNat (m - 1) then (1 : Nat)
        else (Int.ofNat (m - 1) - (0 : Int)).natAbs + 1) =
        fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)) :=
    (tally_len_fuel m hm hfit).2
  rw [hsub]
  simp only [ok_bind, hfuel, except_bind_pure]
  rw [← cubePegStep_nest 6 (Int.ofNat (m - 1)) (Int.ofNat 0, b)
      (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
      (fun σ => rest σ.2) onRetG onRetC onRetIdC]
  rw [whiteStep_nest b (Int.ofNat (m - 1)) (Int.ofNat 0)
      (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
      (SudoRt.runLoopOn (Int.ofNat 0, b)
        (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (cubePegStep 6 (Int.ofNat (m - 1)))
        (fun σ => rest σ.2) onRetG)
      onRetW onRetN onRetIdW]

/-- `climbRung`'s `if not last` / `if rung = 2` nest, then `Flow.cont`, is the
    nest the generated ladder body writes after `clear`. `spare` is 6 and
    `gap` is 5. -/
theorem nest_cont (b : Ecbs.Board) (rung x : Int) (last : Bool) :
    (do
      let b ← (do
        if !last then
          do
            let b ← Ecbs.tally_double b
            if SudoRt.SEq.beq rung (2 : Int) then
              do
                let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
                let b ← Ecbs.mul b ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false
                if !last then Ecbs.tally_add_one b else pure b
            else pure b
        else if SudoRt.SEq.beq rung (2 : Int) then
          do
            let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
            let b ← Ecbs.mul b ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false
            if !last then Ecbs.tally_add_one b else pure b
        else pure b)
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) =
      (do
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
              pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) := by
  unfold Ecbs.spare Ecbs.gap
  cases last with
  | false =>
    rw [show (!false) = true from rfl]
    simp only [if_true]
    cases hb : SudoRt.SEq.beq rung (2 : Int) with
    | false =>
      simp only [hb, Bool.false_eq_true, if_false, bind_assoc, pure_bind]
    | true =>
      simp only [hb, if_true, show (!false) = true from rfl, if_true, bind_assoc, pure_bind]
      rfl
  | true =>
    rw [show (!true) = false from rfl]
    simp only [Bool.false_eq_true, if_false]
    cases hb : SudoRt.SEq.beq rung (2 : Int) with
    | false =>
      simp only [hb, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]
    | true =>
      simp only [hb, if_true, show (!true) = false from rfl, Bool.false_eq_true, if_false,
        bind_assoc, pure_bind]
      rfl

/-- Push `nest_cont` under a preceding bind. `simpa` on the whole rung nest
    exceeds the heartbeat limit, so the loops stay folded. -/
theorem nest_under (m : Except SudoRt.Trap Ecbs.Board) (rung x : Int) (last : Bool) :
    (m >>= fun b =>
        (do
          let b ← (do
            if !last then
              do
                let b ← Ecbs.tally_double b
                if SudoRt.SEq.beq rung (2 : Int) then
                  do
                    let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
                    let b ← Ecbs.mul b ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false
                    if !last then Ecbs.tally_add_one b else pure b
                else pure b
            else if SudoRt.SEq.beq rung (2 : Int) then
              do
                let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
                let b ← Ecbs.mul b ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false
                if !last then Ecbs.tally_add_one b else pure b
            else pure b)
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b))) =
      (m >>= fun b =>
        (do
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
                  else pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
              else pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
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
                  else pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
              else pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b))) := by
  apply congrArg (fun k => m >>= k)
  funext b
  exact nest_cont b rung x last

end EcbsLink2.Link2
