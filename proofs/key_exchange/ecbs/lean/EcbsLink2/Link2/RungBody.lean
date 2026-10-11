/-
  The generated rung nests the cube-peg loop, the gap mul, and clear as the
  `after` of the white scan. `whiteStep` and `cubePegStep` never return, so
  that nest is the sequenced pair of loops in `climbClear`. The fuel is
  `subI` of the tally length.
-/
import EcbsLink2.Link2.LadderKeep
import EcbsLink2.Link2.TallyLen

namespace EcbsLink2.Link2

open MegaDreifach.Link2

/-- Nested loop against the sequenced loops, for an arbitrary continuation.
    Both steppers are variables: the only premises are that they never return.
    `runLoopOn_after_split` twice, then `bind_assoc`. -/
theorem white_cube_nest_gen {α : Type}
    (j0 : Int) (s0 : Int × Ecbs.Board) (fuel : Nat)
    (whiteS : Int → Except SudoRt.Trap (SudoRt.Flow Int Ecbs.Board))
    (cubeS : Int × Ecbs.Board → Except SudoRt.Trap
        (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board))
    (K : Int × Ecbs.Board → Except SudoRt.Trap α)
    (onRetW : Ecbs.Board → Except SudoRt.Trap α)
    (onRetC : Ecbs.Board → Except SudoRt.Trap α)
    (onRetIdW : Ecbs.Board → Except SudoRt.Trap Int)
    (onRetIdC : Ecbs.Board → Except SudoRt.Trap (Int × Ecbs.Board))
    (hW : ∀ s r, whiteS s ≠ Except.ok (SudoRt.Flow.ret r))
    (hC : ∀ s r, cubeS s ≠ Except.ok (SudoRt.Flow.ret r)) :
    SudoRt.runLoopOn j0 fuel whiteS
        (fun _ => SudoRt.runLoopOn s0 fuel cubeS K onRetC) onRetW =
      ((SudoRt.runLoopOn j0 fuel whiteS (fun j => pure j) onRetIdW) >>= fun _ =>
          SudoRt.runLoopOn s0 fuel cubeS (fun σ => pure σ) onRetIdC) >>= K := by
  have hc :
      (fun _ : Int => SudoRt.runLoopOn s0 fuel cubeS K onRetC) =
        fun _ =>
          (SudoRt.runLoopOn s0 fuel cubeS (fun σ => pure σ) onRetIdC) >>= K :=
    funext fun _ => runLoopOn_after_split s0 fuel cubeS K onRetC onRetIdC hC
  rw [hc]
  rw [runLoopOn_after_split j0 fuel whiteS
      (fun _ =>
        (SudoRt.runLoopOn s0 fuel cubeS (fun σ => pure σ) onRetIdC) >>= K)
      onRetW onRetIdW hW]
  rw [← bind_assoc
      (SudoRt.runLoopOn j0 fuel whiteS (fun j => pure j) onRetIdW)
      (fun _ => SudoRt.runLoopOn s0 fuel cubeS (fun σ => pure σ) onRetIdC)
      K]

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

/-- The `if not last` / `if rung = 2` nest, as a board computation. -/
def rungNest (rung x : Int) (last : Bool) (b : Ecbs.Board) :
    Except SudoRt.Trap Ecbs.Board :=
  do
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
    else pure b

/-- Mul, clear, the nest, and `Flow.cont`. Irreducible so a loop rewrite cannot
    open it. `nest_cont` is a separate rewrite, after `unfold`. -/
@[irreducible] def rungTail (rung x : Int) (last : Bool) (b : Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow Ecbs.Board Ecbs.Board) :=
  do
    let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
    let b ← Ecbs.clear b (5 : Int)
    let b ← rungNest rung x last b
    pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)

theorem climbRung_nest (b : Ecbs.Board) (rung : Nat) (last : Bool) (x : Int) (m : Nat) :
    climbRung b rung last x m =
      (do
        let b ← climbClear b rung m
        rungNest (rung : Int) x last b) := by
  unfold climbRung rungNest
  rfl

theorem rungTail_eq (rung x : Int) (last : Bool) (b : Ecbs.Board) :
    rungTail rung x last b =
      (do
        let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
        let b ← Ecbs.clear b (5 : Int)
        let b ← rungNest rung x last b
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) := by
  unfold rungTail
  rfl

/-- The generated white/cube nest whose continuation is `rungTail` is the
    sequenced loops, then `rungTail`. Fuel is `tally_len_fuel`. The steppers
    and the continuation are generalized before the abstract lemma is applied. -/
theorem rung_loops (b : Ecbs.Board) (rung x : Int) (last : Bool) (m : Nat)
    (hm : 0 < m) (hfit : FitsLen m)
    (hlen : b.sudo_5Board_9tally_len = Int.ofNat m)
    (onRetW : Ecbs.Board → Except SudoRt.Trap (SudoRt.Flow Ecbs.Board Ecbs.Board))
    (onRetC : Ecbs.Board → Except SudoRt.Trap (SudoRt.Flow Ecbs.Board Ecbs.Board))
    (onRetIdW : Ecbs.Board → Except SudoRt.Trap Int)
    (onRetIdC : Ecbs.Board → Except SudoRt.Trap (Int × Ecbs.Board)) :
    (do
      let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
      let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
      SudoRt.runLoopOn (Int.ofNat 0) fuel (whiteStep b toV)
        (fun _ => do
          let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
          let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
          SudoRt.runLoopOn (Int.ofNat 0, b) fuel (cubePegStep 6 toV)
            (fun σ => rungTail rung x last σ.2) onRetC)
        onRetW) =
      ((SudoRt.runLoopOn (Int.ofNat 0)
          (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
          (whiteStep b (Int.ofNat (m - 1))) (fun j => pure j) onRetIdW) >>= fun _ =>
        SudoRt.runLoopOn (Int.ofNat 0, b)
          (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
          (cubePegStep 6 (Int.ofNat (m - 1))) (fun σ => pure σ) onRetIdC) >>=
        fun σ => rungTail rung x last σ.2 := by
  rw [hlen]
  have hsub : SudoRt.subI (Int.ofNat m) 1 = .ok (Int.ofNat (m - 1)) :=
    (tally_len_fuel m hm hfit).1
  have hfuel :
      (if (0 : Int) > Int.ofNat (m - 1) then (1 : Nat)
        else (Int.ofNat (m - 1) - (0 : Int)).natAbs + 1) =
        fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)) :=
    (tally_len_fuel m hm hfit).2
  rw [hsub, ok_bind, ok_bind, hfuel]
  dsimp only
  generalize hW : whiteStep b (Int.ofNat (m - 1)) = whiteS
  generalize hC : cubePegStep 6 (Int.ofNat (m - 1)) = cubeS
  generalize hK : (fun σ : Int × Ecbs.Board => rungTail rung x last σ.2) = K
  have hWno : ∀ s r, whiteS s ≠ Except.ok (SudoRt.Flow.ret r) := by
    intro s r
    rw [← hW]
    exact whiteStep_no_ret b (Int.ofNat (m - 1)) s r
  have hCno : ∀ s r, cubeS s ≠ Except.ok (SudoRt.Flow.ret r) := by
    intro s r
    rw [← hC]
    exact cubePegStep_no_ret 6 (Int.ofNat (m - 1)) s r
  exact white_cube_nest_gen (Int.ofNat 0) (Int.ofNat 0, b)
      (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
      whiteS cubeS K onRetW onRetC onRetIdW onRetIdC hWno hCno

/-- Same loops, with `climbClear`'s white continuation `(b, j)` instead of the
    index. The pair is discarded, so this is `runLoopOn_discard`. -/
theorem rung_loops_pair (b : Ecbs.Board) (rung x : Int) (last : Bool) (m : Nat)
    (hm : 0 < m) (hfit : FitsLen m)
    (hlen : b.sudo_5Board_9tally_len = Int.ofNat m)
    (onRetW : Ecbs.Board → Except SudoRt.Trap (SudoRt.Flow Ecbs.Board Ecbs.Board))
    (onRetC : Ecbs.Board → Except SudoRt.Trap (SudoRt.Flow Ecbs.Board Ecbs.Board))
    (onRetIdW : Ecbs.Board → Except SudoRt.Trap Int)
    (onRetIdC : Ecbs.Board → Except SudoRt.Trap (Int × Ecbs.Board))
    (onRetPack : Ecbs.Board → Except SudoRt.Trap (Ecbs.Board × Int)) :
    (do
      let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
      let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
      SudoRt.runLoopOn (Int.ofNat 0) fuel (whiteStep b toV)
        (fun _ => do
          let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
          let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
          SudoRt.runLoopOn (Int.ofNat 0, b) fuel (cubePegStep 6 toV)
            (fun σ => rungTail rung x last σ.2) onRetC)
        onRetW) =
      ((SudoRt.runLoopOn (Int.ofNat 0)
          (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
          (whiteStep b (Int.ofNat (m - 1))) (fun j => pure (b, j)) onRetPack) >>=
        fun _ =>
          SudoRt.runLoopOn (Int.ofNat 0, b)
            (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
            (cubePegStep 6 (Int.ofNat (m - 1))) (fun σ => pure σ) onRetIdC) >>=
        fun σ => rungTail rung x last σ.2 := by
  rw [rung_loops b rung x last m hm hfit hlen onRetW onRetC onRetIdW onRetIdC]
  rw [bind_assoc
      (SudoRt.runLoopOn (Int.ofNat 0) (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (whiteStep b (Int.ofNat (m - 1))) (fun j => pure j) onRetIdW)
      (fun _ =>
        SudoRt.runLoopOn (Int.ofNat 0, b) (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
          (cubePegStep 6 (Int.ofNat (m - 1))) (fun σ => pure σ) onRetIdC)
      (fun σ => rungTail rung x last σ.2)]
  rw [bind_assoc
      (SudoRt.runLoopOn (Int.ofNat 0) (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (whiteStep b (Int.ofNat (m - 1))) (fun j => pure (b, j)) onRetPack)
      (fun _ =>
        SudoRt.runLoopOn (Int.ofNat 0, b) (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
          (cubePegStep 6 (Int.ofNat (m - 1))) (fun σ => pure σ) onRetIdC)
      (fun σ => rungTail rung x last σ.2)]
  rw [← runLoopOn_discard (Int.ofNat 0) (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
      (whiteStep b (Int.ofNat (m - 1))) (fun j => (b, j))
      ((SudoRt.runLoopOn (Int.ofNat 0, b) (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
          (cubePegStep 6 (Int.ofNat (m - 1))) (fun σ => pure σ) onRetIdC) >>=
        fun σ => rungTail rung x last σ.2)
      onRetPack onRetIdW
      (fun s r => whiteStep_no_ret b (Int.ofNat (m - 1)) s r)]

/-- Mul, clear, the nest, and `Flow.cont` are `rungTail`, under any prefix. -/
theorem suffix_tail (pre : Except SudoRt.Trap Ecbs.Board) (rung x : Int) (last : Bool) :
    (do
      let b ← pre
      let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
      let b ← Ecbs.clear b (5 : Int)
      let b ← rungNest rung x last b
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) =
      (do
        let b ← pre
        rungTail rung x last b) := by
  cases pre with
  | error _ => simp [error_bind]
  | ok b0 =>
    rw [ok_bind, ← rungTail_eq]
    rfl

/-- Two continuations that agree pointwise agree under any prefix. -/
theorem bind_pointwise {α β : Type} (m : Except SudoRt.Trap α)
    (f g : α → Except SudoRt.Trap β) (h : ∀ a, f a = g a) :
    m >>= f = m >>= g := by
  cases m with
  | error _ => rfl
  | ok a =>
    rw [ok_bind, ok_bind, h]

/-- `climbRung`, then `Flow.cont`, is park, copy, the sequenced loops, and
    `rungTail`. The pure `let`s between binds are zeta'd before the tail
    rewrite, so `rungTail` stays sealed except for `rungTail_eq` on the right. -/
theorem climbRung_cont (b : Ecbs.Board) (rung : Nat) (last : Bool) (x : Int) (m : Nat) :
    (do
      let b ← climbRung b rung last x m
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) =
      (do
        let b ← Ecbs.park_rung b (rung : Int)
        let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
        let _ ← SudoRt.runLoopOn (Int.ofNat 0)
            (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
            (whiteStep b (Int.ofNat (m - 1)))
            (fun j => .ok (b, j))
            (fun _ => .ok (b, (0 : Int)))
        let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
            (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
            (cubePegStep 6 (Int.ofNat (m - 1)))
            (fun σ => .ok σ)
            (fun r => .ok ((0 : Int), r))
        rungTail (rung : Int) x last out.2) := by
  rw [climbRung_nest]
  unfold climbClear
  dsimp only
  rw [bind_assoc, bind_assoc]
  apply bind_pointwise
  intro b1
  rw [bind_assoc]
  apply bind_pointwise
  intro b2
  rw [bind_assoc]
  apply bind_pointwise
  intro _w
  rw [bind_assoc]
  apply bind_pointwise
  intro out
  rw [rungTail_eq (rung : Int) x last out.2, bind_assoc]

/-- Park, copy, and the generated nest, against `climbRung` then `Flow.cont`.
    The board that reaches the loops keeps the tally length. -/
theorem climbRung_nested (b : Ecbs.Board) (rung : Nat) (last : Bool) (x : Int) (m : Nat)
    (hm : 0 < m) (hfit : FitsLen m)
    (hlen : b.sudo_5Board_9tally_len = Int.ofNat m) :
    (do
      let b ← Ecbs.park_rung b (rung : Int)
      let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
      let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
      let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
      SudoRt.runLoopOn (Int.ofNat 0) fuel (whiteStep b toV)
        (fun _ => do
          let toV ← SudoRt.subI b.sudo_5Board_9tally_len (1 : Int)
          let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
          SudoRt.runLoopOn (Int.ofNat 0, b) fuel (cubePegStep 6 toV)
            (fun σ => rungTail (rung : Int) x last σ.2)
            (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)))
        (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))) =
      (do
        let b ← climbRung b rung last x m
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) := by
  rw [climbRung_cont]
  cases hp : Ecbs.park_rung b (rung : Int) with
  | error _ =>
    simp only [hp, error_bind]
  | ok b1 =>
    simp only [hp, ok_bind]
    cases hc : Ecbs.copy_band b1 ((6 : Nat) : Int) ((5 : Nat) : Int) false with
    | error _ =>
      simp only [hc, error_bind]
    | ok b2 =>
      simp only [hc, ok_bind]
      have hlen2 : b2.sudo_5Board_9tally_len = Int.ofNat m :=
        ((copy_band_tally_len ((6 : Nat) : Int) ((5 : Nat) : Int) false) b1 b2 hc).trans
          (((park_rung_tally_len (rung : Int)) b b1 hp).trans hlen)
      have hwhite :
          (fun j => (Except.ok (b2, j) : Except SudoRt.Trap (Ecbs.Board × Int))) =
            fun j => pure (b2, j) := by
        funext j
        exact (pure_eq_ok (b2, j)).symm
      have hcube :
          (fun σ => (Except.ok σ : Except SudoRt.Trap (Int × Ecbs.Board))) =
            fun σ => pure σ := by
        funext σ
        exact (pure_eq_ok σ).symm
      rw [hwhite, hcube]
      have hloops := rung_loops_pair b2 (rung : Int) x last m hm hfit hlen2
        (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))
        (fun r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r))
        (fun _ => pure (0 : Int))
        (fun r => .ok ((0 : Int), r))
        (fun _ => .ok (b2, (0 : Int)))
      dsimp only at hloops
      rw [bind_assoc] at hloops
      exact hloops

end EcbsLink2.Link2
