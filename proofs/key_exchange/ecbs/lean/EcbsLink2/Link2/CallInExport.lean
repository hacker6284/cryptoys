/-
  `call_in` is `start_calling`, then both destination bands, hole 0 through
  `n - 1`, `call_hole` on each. The close writes 0 into the calling hole and
  adds one to `ctrl`. `set_control` is the only other cost write in that close.
  The call does not invert, so it takes no `FieldOk`.
  Proof-only. Not a security claim.
-/
import Ecbs

namespace EcbsLink2.Link2

open Ecbs

/-- After the two bands: the calling peg goes back to empty, and `ctrl` grows by one. -/
def callInAfter (σ : Int × Board) : Except SudoRt.Trap Board :=
  do
    let b := σ.2
    let b ← set_control b b.sudo_5Board_12calling_hole (0 : Int)
    let c ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_4ctrl (1 : Int)
    pure { b with
      sudo_5Board_4cost := { b.sudo_5Board_4cost with sudo_5Costs_4ctrl := c } }

def callInCard («rec» : Board) (sender : Board) : Except SudoRt.Trap Board :=
  do
    let b := «rec»
    let _io1704 ← start_calling b
    let b := _io1704
    let _t1705 ← plan_dst b
    let dsts := _t1705
    let _fromV := (0 : Int)
    let _toV := (1 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init1716 := (_fromV, b)
    let _out ← (SudoRt.runLoopOn (ρ := Board) _init1716 fuel (fun σ =>
    let d := σ.1
    let b := σ.2
    do
      if d > _toV then
        pure (SudoRt.Flow.brk (ρ := Board) (d, b))
      else
        match ← ((do
  let _t1710 ← SudoRt.subI ((b).sudo_5Board_1t).sudo_4Tier_1n (1 : Int)
  let _fromV := (0 : Int)
  let _toV := _t1710
  let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
  let _init1711 := (_fromV, b)
  let _out ← (SudoRt.runLoopOn (ρ := Board) _init1711 fuel (fun σ =>
    let i := σ.1
    let b := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Board) (i, b))
      else
        match ← ((do
  let _t1708 ← SudoRt.atL dsts d
  let _io1709 ← call_hole b sender _t1708 i
  let b := _io1709
  pure (SudoRt.Flow.cont (ρ := Board) b)) : Except SudoRt.Trap (SudoRt.Flow _ (Board))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Board) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Board) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Board) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Board) (i', _fs))) (fun σ =>
    let b := σ.2
    do
      pure (SudoRt.Flow.cont (ρ := Board) b)) (fun r => pure (SudoRt.Flow.ret (ρ := Board) r)))
  pure _out) : Except SudoRt.Trap (SudoRt.Flow _ (Board))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Board) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Board) (d, _fs))
        | .cont _fs => do
            if d == _toV then
              pure (SudoRt.Flow.brk (ρ := Board) (d, _fs))
            else do
              let i' ← SudoRt.addI d (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Board) (i', _fs))) (fun σ =>
    callInAfter σ) (fun r => pure r))
    pure _out


theorem call_in_card («rec» sender : Board) :
    call_in «rec» sender = callInCard «rec» sender := by
  unfold call_in callInCard callInAfter
  conv =>
    lhs
    zeta
  conv =>
    rhs
    zeta
  rfl

end EcbsLink2.Link2
