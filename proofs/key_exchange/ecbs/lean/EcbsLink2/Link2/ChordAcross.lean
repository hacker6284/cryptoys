/-
  `bench_add` lays a home onto the bench, mirroring when asked.
  The bridge is the emitted loop. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordWhite

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The emitted `bench_add`, copied so the bridge is `rfl`. -/
def benchAddEmit (b : Ecbs.Board) (src : Int) (mirror : Bool) : Except SudoRt.Trap Ecbs.Board :=
  do
    let _t1073 ← SudoRt.atL (b).sudo_5Board_4home src
    let v := _t1073
    let _t1097 ← SudoRt.subI (SudoRt.listLen v) (1 : Int)
    let _fromV := (0 : Int)
    let _toV := _t1097
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _init1098 := (_fromV, b)
    let _out ← (SudoRt.runLoopOn (ρ := Ecbs.Board) _init1098 fuel (fun σ =>
    let i := σ.1
    let b := σ.2
    do
      if i > _toV then
        pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, b))
      else
        match ← ((do
  let _t1075 ← SudoRt.atL v i
  let c := _t1075
  if (!(SudoRt.SEq.beq c (0 : Int))) then
    do
      if mirror then
        do
          let _t1077 ← Ecbs.flip c
          let c := _t1077
          let _ix1078 := i
          let _t1079 ← SudoRt.atL (b).sudo_5Board_5bench i
          let _t1080 ← SudoRt.addI _t1079 c
          let _t1081 ← SudoRt.modI _t1080 (3 : Int)
          let _t1082 ← SudoRt.putL (b).sudo_5Board_5bench _ix1078 _t1081
          let _t1083 := ({ b with sudo_5Board_5bench := _t1082 } : Ecbs.Board)
          let b := _t1083
          let _t1084 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_5moves (1 : Int)
          let _t1085 := ({ (b).sudo_5Board_4cost with sudo_5Costs_5moves := _t1084 } : Ecbs.Costs)
          let _t1086 := ({ b with sudo_5Board_4cost := _t1085 } : Ecbs.Board)
          let b := _t1086
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
      else
        do
          let _ix1087 := i
          let _t1088 ← SudoRt.atL (b).sudo_5Board_5bench i
          let _t1089 ← SudoRt.addI _t1088 c
          let _t1090 ← SudoRt.modI _t1089 (3 : Int)
          let _t1091 ← SudoRt.putL (b).sudo_5Board_5bench _ix1087 _t1090
          let _t1092 := ({ b with sudo_5Board_5bench := _t1091 } : Ecbs.Board)
          let b := _t1092
          let _t1093 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_5moves (1 : Int)
          let _t1094 := ({ (b).sudo_5Board_4cost with sudo_5Costs_5moves := _t1093 } : Ecbs.Costs)
          let _t1095 := ({ b with sudo_5Board_4cost := _t1094 } : Ecbs.Board)
          let b := _t1095
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)
  else
    do
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board) b)) : Except SudoRt.Trap (SudoRt.Flow _ (Ecbs.Board))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, _fs))
        | .cont _fs => do
            if i == _toV then
              pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, _fs))
            else do
              let i' ← SudoRt.addI i (1 : Int)
              pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', _fs))) (fun σ =>
    let b := σ.2
    do
      pure b) (fun r => pure r))
    pure _out

theorem bench_add_emit (b : Ecbs.Board) (src : Int) (mirror : Bool) :
    Ecbs.bench_add b src mirror = benchAddEmit b src mirror := by
  unfold Ecbs.bench_add benchAddEmit
  rfl

end EcbsLink2.Link2
