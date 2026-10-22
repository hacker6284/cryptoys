/-
  `Ecbs.fform_add` split at the gap add. The prefix is the run, the rise,
  `u²`, `u²Z`, `v²`, `v²Z`, the sum, the zero-run check, and the add.
  It binds into the six-multiply tail. `mul` and `add` stay folded.
  Proof-only. Not a security claim.
-/
import Ecbs

namespace EcbsLink2.Link2

open Ecbs

attribute [local irreducible] Ecbs.mul Ecbs.add

/-- The success tail of `fform_add`: bottom, across, across again, up, up
    again, then `clear` of the gap. -/
def fformAddTail (b : Board) (red : Bool) : Except SudoRt.Trap (Bool × Board) :=
  do
    let b ← mul b bottom across bottom false false false
    let b ← mul b across gap across false false false
    let b ← mul b across base_across bottom true true false
    let b ← mul b up gap up false false true
    let b ← mul b up base_up bottom true true (!( red ))
    let b ← clear b gap
    pure (true, b)

/-- `fform_add` is the prefix through the gap add, then `fformAddTail`. -/
theorem fform_add_split (b : Board) (red : Bool) :
    fform_add b red =
      (do
        let _ix1239 := op_fadd
        let _t1240 ← SudoRt.atL ((b).sudo_5Board_4cost).sudo_5Costs_3ops op_fadd
        let _t1241 ← SudoRt.addI _t1240 (1 : Int)
        let _t1242 ← SudoRt.putL ((b).sudo_5Board_4cost).sudo_5Costs_3ops _ix1239 _t1241
        let _t1243 := ({ (b).sudo_5Board_4cost with sudo_5Costs_3ops := _t1242 } : Costs)
        let _t1244 := ({ b with sudo_5Board_4cost := _t1243 } : Board)
        let b := _t1244
        let _io1245 ← mirror b across
        let b := _io1245
        let _io1246 ← mul b across base_across bottom true true false
        let b := _io1246
        let _t1247 ← is_zero b across
        if _t1247 then
          do
            pure (false, b)
        else
          do
            let _io1248 ← mirror b up
            let b := _io1248
            let _io1249 ← mul b up base_up bottom true true red
            let b := _io1249
            let _io1250 ← mul b gap up up true false false
            let b := _io1250
            let _io1251 ← mul b gap bottom gap false false false
            let b := _io1251
            let _io1252 ← mul b spare across across true false false
            let b := _io1252
            let _io1253 ← mul b bottom spare bottom false false false
            let b := _io1253
            let _io1254 ← mul b gap across spare false true false
            let b := _io1254
            let _io1255 ← add b gap bottom false
            let b := _io1255
            fformAddTail b red) := by
  unfold fform_add
  rfl

end EcbsLink2.Link2
