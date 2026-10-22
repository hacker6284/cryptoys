/-
  One quarter of Demo's nonzero trit lists. Each kernel `decide` is one rung,
  one cube, or one multiply.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldOk

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem demoR1_1000000 : invRung 7 5 20 [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] 1 2 false = ([1, 0, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_1000000 : invRung 7 5 20 [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] 3 1 true = ([1, 0, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_1000000 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 0, 0] = [1, 0, 0, 0, 0, 0, 0] := by
  decide

theorem demoM_1000000 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1000000 : specInv 7 5 20 [1, 0, 0, 0, 0, 0, 0] = some [1, 0, 0, 0, 0, 0, 0] :=
  specInv_white_7 [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] demoR1_1000000 demoR2_1000000 demoC_1000000 demoM_1000000

theorem demoR1_2000000 : invRung 7 5 20 [2, 0, 0, 0, 0, 0, 0] [2, 0, 0, 0, 0, 0, 0] 1 2 false = ([2, 0, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_2000000 : invRung 7 5 20 [2, 0, 0, 0, 0, 0, 0] [2, 0, 0, 0, 0, 0, 0] 3 1 true = ([1, 0, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_2000000 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 0, 0] = [1, 0, 0, 0, 0, 0, 0] := by
  decide

theorem demoM_2000000 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 0, 0] [2, 0, 0, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000000 : mirrorTrits [1, 0, 0, 0, 0, 0, 0] = [2, 0, 0, 0, 0, 0, 0] := by
  decide

theorem demoInv_2000000 : specInv 7 5 20 [2, 0, 0, 0, 0, 0, 0] = some [2, 0, 0, 0, 0, 0, 0] :=
  specInv_mirror_7 [2, 0, 0, 0, 0, 0, 0] [2, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] [1, 0, 0, 0, 0, 0, 0] [2, 0, 0, 0, 0, 0, 0] demoR1_2000000 demoR2_2000000 demoC_2000000 demoM_2000000 demoMir_2000000

theorem demoR1_0100000 : invRung 7 5 20 [0, 1, 0, 0, 0, 0, 0] [0, 1, 0, 0, 0, 0, 0] 1 2 false = ([1, 0, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0100000 : invRung 7 5 20 [0, 1, 0, 0, 0, 0, 0] [1, 0, 1, 0, 1, 1, 1] 3 1 true = ([2, 1, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_0100000 : fieldCube 7 5 20 [2, 1, 0, 0, 1, 1, 1] = [0, 0, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_0100000 : fieldMul 7 5 20 [0, 0, 0, 0, 2, 0, 1] [0, 1, 0, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0100000 : specInv 7 5 20 [0, 1, 0, 0, 0, 0, 0] = some [0, 0, 0, 0, 2, 0, 1] :=
  specInv_white_7 [0, 1, 0, 0, 0, 0, 0] [1, 0, 1, 0, 1, 1, 1] [2, 1, 0, 0, 1, 1, 1] [0, 0, 0, 0, 2, 0, 1] demoR1_0100000 demoR2_0100000 demoC_0100000 demoM_0100000

theorem demoR1_1100000 : invRung 7 5 20 [1, 1, 0, 0, 0, 0, 0] [1, 1, 0, 0, 0, 0, 0] 1 2 false = ([0, 0, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_1100000 : invRung 7 5 20 [1, 1, 0, 0, 0, 0, 0] [0, 0, 2, 0, 2, 0, 0] 3 1 true = ([2, 2, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_1100000 : fieldCube 7 5 20 [2, 2, 2, 2, 0, 2, 1] = [0, 0, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_1100000 : fieldMul 7 5 20 [0, 0, 0, 0, 0, 2, 1] [1, 1, 0, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1100000 : specInv 7 5 20 [1, 1, 0, 0, 0, 0, 0] = some [0, 0, 0, 0, 0, 2, 1] :=
  specInv_white_7 [1, 1, 0, 0, 0, 0, 0] [0, 0, 2, 0, 2, 0, 0] [2, 2, 2, 2, 0, 2, 1] [0, 0, 0, 0, 0, 2, 1] demoR1_1100000 demoR2_1100000 demoC_1100000 demoM_1100000

theorem demoR1_2100000 : invRung 7 5 20 [2, 1, 0, 0, 0, 0, 0] [2, 1, 0, 0, 0, 0, 0] 1 2 false = ([1, 2, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_2100000 : invRung 7 5 20 [2, 1, 0, 0, 0, 0, 0] [1, 2, 2, 2, 0, 1, 2] 3 1 true = ([1, 1, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_2100000 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 1, 2] = [0, 0, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_2100000 : fieldMul 7 5 20 [0, 0, 0, 0, 0, 1, 1] [2, 1, 0, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2100000 : specInv 7 5 20 [2, 1, 0, 0, 0, 0, 0] = some [0, 0, 0, 0, 0, 1, 1] :=
  specInv_white_7 [2, 1, 0, 0, 0, 0, 0] [1, 2, 2, 2, 0, 1, 2] [1, 1, 0, 1, 0, 1, 2] [0, 0, 0, 0, 0, 1, 1] demoR1_2100000 demoR2_2100000 demoC_2100000 demoM_2100000

theorem demoR1_0200000 : invRung 7 5 20 [0, 2, 0, 0, 0, 0, 0] [0, 2, 0, 0, 0, 0, 0] 1 2 false = ([2, 0, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0200000 : invRung 7 5 20 [0, 2, 0, 0, 0, 0, 0] [2, 0, 2, 0, 2, 2, 2] 3 1 true = ([2, 1, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_0200000 : fieldCube 7 5 20 [2, 1, 0, 0, 1, 1, 1] = [0, 0, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_0200000 : fieldMul 7 5 20 [0, 0, 0, 0, 2, 0, 1] [0, 2, 0, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200000 : mirrorTrits [0, 0, 0, 0, 2, 0, 1] = [0, 0, 0, 0, 1, 0, 2] := by
  decide

theorem demoInv_0200000 : specInv 7 5 20 [0, 2, 0, 0, 0, 0, 0] = some [0, 0, 0, 0, 1, 0, 2] :=
  specInv_mirror_7 [0, 2, 0, 0, 0, 0, 0] [2, 0, 2, 0, 2, 2, 2] [2, 1, 0, 0, 1, 1, 1] [0, 0, 0, 0, 2, 0, 1] [0, 0, 0, 0, 1, 0, 2] demoR1_0200000 demoR2_0200000 demoC_0200000 demoM_0200000 demoMir_0200000

theorem demoR1_1200000 : invRung 7 5 20 [1, 2, 0, 0, 0, 0, 0] [1, 2, 0, 0, 0, 0, 0] 1 2 false = ([2, 1, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_1200000 : invRung 7 5 20 [1, 2, 0, 0, 0, 0, 0] [2, 1, 1, 1, 0, 2, 1] 3 1 true = ([1, 1, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_1200000 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 1, 2] = [0, 0, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_1200000 : fieldMul 7 5 20 [0, 0, 0, 0, 0, 1, 1] [1, 2, 0, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200000 : mirrorTrits [0, 0, 0, 0, 0, 1, 1] = [0, 0, 0, 0, 0, 2, 2] := by
  decide

theorem demoInv_1200000 : specInv 7 5 20 [1, 2, 0, 0, 0, 0, 0] = some [0, 0, 0, 0, 0, 2, 2] :=
  specInv_mirror_7 [1, 2, 0, 0, 0, 0, 0] [2, 1, 1, 1, 0, 2, 1] [1, 1, 0, 1, 0, 1, 2] [0, 0, 0, 0, 0, 1, 1] [0, 0, 0, 0, 0, 2, 2] demoR1_1200000 demoR2_1200000 demoC_1200000 demoM_1200000 demoMir_1200000

theorem demoR1_2200000 : invRung 7 5 20 [2, 2, 0, 0, 0, 0, 0] [2, 2, 0, 0, 0, 0, 0] 1 2 false = ([0, 0, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_2200000 : invRung 7 5 20 [2, 2, 0, 0, 0, 0, 0] [0, 0, 1, 0, 1, 0, 0] 3 1 true = ([2, 2, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_2200000 : fieldCube 7 5 20 [2, 2, 2, 2, 0, 2, 1] = [0, 0, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_2200000 : fieldMul 7 5 20 [0, 0, 0, 0, 0, 2, 1] [2, 2, 0, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200000 : mirrorTrits [0, 0, 0, 0, 0, 2, 1] = [0, 0, 0, 0, 0, 1, 2] := by
  decide

theorem demoInv_2200000 : specInv 7 5 20 [2, 2, 0, 0, 0, 0, 0] = some [0, 0, 0, 0, 0, 1, 2] :=
  specInv_mirror_7 [2, 2, 0, 0, 0, 0, 0] [0, 0, 1, 0, 1, 0, 0] [2, 2, 2, 2, 0, 2, 1] [0, 0, 0, 0, 0, 2, 1] [0, 0, 0, 0, 0, 1, 2] demoR1_2200000 demoR2_2200000 demoC_2200000 demoM_2200000 demoMir_2200000

theorem demoR1_0010000 : invRung 7 5 20 [0, 0, 1, 0, 0, 0, 0] [0, 0, 1, 0, 0, 0, 0] 1 2 false = ([1, 1, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_0010000 : invRung 7 5 20 [0, 0, 1, 0, 0, 0, 0] [1, 1, 0, 1, 2, 0, 2] 3 1 true = ([1, 0, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0010000 : fieldCube 7 5 20 [1, 0, 2, 1, 0, 1, 2] = [0, 0, 0, 2, 0, 1, 0] := by
  decide

theorem demoM_0010000 : fieldMul 7 5 20 [0, 0, 0, 2, 0, 1, 0] [0, 0, 1, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0010000 : specInv 7 5 20 [0, 0, 1, 0, 0, 0, 0] = some [0, 0, 0, 2, 0, 1, 0] :=
  specInv_white_7 [0, 0, 1, 0, 0, 0, 0] [1, 1, 0, 1, 2, 0, 2] [1, 0, 2, 1, 0, 1, 2] [0, 0, 0, 2, 0, 1, 0] demoR1_0010000 demoR2_0010000 demoC_0010000 demoM_0010000

theorem demoR1_1010000 : invRung 7 5 20 [1, 0, 1, 0, 0, 0, 0] [1, 0, 1, 0, 0, 0, 0] 1 2 false = ([0, 2, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1010000 : invRung 7 5 20 [1, 0, 1, 0, 0, 0, 0] [0, 2, 2, 2, 0, 1, 2] 3 1 true = ([0, 1, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1010000 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 2, 2] = [1, 2, 2, 1, 1, 1, 1] := by
  decide

theorem demoM_1010000 : fieldMul 7 5 20 [1, 2, 2, 1, 1, 1, 1] [1, 0, 1, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1010000 : mirrorTrits [1, 2, 2, 1, 1, 1, 1] = [2, 1, 1, 2, 2, 2, 2] := by
  decide

theorem demoInv_1010000 : specInv 7 5 20 [1, 0, 1, 0, 0, 0, 0] = some [2, 1, 1, 2, 2, 2, 2] :=
  specInv_mirror_7 [1, 0, 1, 0, 0, 0, 0] [0, 2, 2, 2, 0, 1, 2] [0, 1, 0, 2, 1, 2, 2] [1, 2, 2, 1, 1, 1, 1] [2, 1, 1, 2, 2, 2, 2] demoR1_1010000 demoR2_1010000 demoC_1010000 demoM_1010000 demoMir_1010000

theorem demoR1_2010000 : invRung 7 5 20 [2, 0, 1, 0, 0, 0, 0] [2, 0, 1, 0, 0, 0, 0] 1 2 false = ([2, 2, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_2010000 : invRung 7 5 20 [2, 0, 1, 0, 0, 0, 0] [2, 2, 1, 2, 0, 1, 0] 3 1 true = ([1, 1, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_2010000 : fieldCube 7 5 20 [1, 1, 2, 1, 0, 1, 2] = [0, 0, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_2010000 : fieldMul 7 5 20 [0, 0, 0, 0, 0, 1, 0] [2, 0, 1, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2010000 : specInv 7 5 20 [2, 0, 1, 0, 0, 0, 0] = some [0, 0, 0, 0, 0, 1, 0] :=
  specInv_white_7 [2, 0, 1, 0, 0, 0, 0] [2, 2, 1, 2, 0, 1, 0] [1, 1, 2, 1, 0, 1, 2] [0, 0, 0, 0, 0, 1, 0] demoR1_2010000 demoR2_2010000 demoC_2010000 demoM_2010000

theorem demoR1_0110000 : invRung 7 5 20 [0, 1, 1, 0, 0, 0, 0] [0, 1, 1, 0, 0, 0, 0] 1 2 false = ([1, 0, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_0110000 : invRung 7 5 20 [0, 1, 1, 0, 0, 0, 0] [1, 0, 1, 2, 1, 1, 1] 3 1 true = ([0, 2, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0110000 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 2, 0] = [0, 0, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_0110000 : fieldMul 7 5 20 [0, 0, 0, 0, 2, 1, 0] [0, 1, 1, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0110000 : specInv 7 5 20 [0, 1, 1, 0, 0, 0, 0] = some [0, 0, 0, 0, 2, 1, 0] :=
  specInv_white_7 [0, 1, 1, 0, 0, 0, 0] [1, 0, 1, 2, 1, 1, 1] [0, 2, 1, 1, 1, 2, 0] [0, 0, 0, 0, 2, 1, 0] demoR1_0110000 demoR2_0110000 demoC_0110000 demoM_0110000

theorem demoR1_1110000 : invRung 7 5 20 [1, 1, 1, 0, 0, 0, 0] [1, 1, 1, 0, 0, 0, 0] 1 2 false = ([1, 0, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_1110000 : invRung 7 5 20 [1, 1, 1, 0, 0, 0, 0] [1, 0, 2, 2, 1, 2, 2] 3 1 true = ([1, 0, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_1110000 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 0, 2] = [2, 2, 2, 2, 2, 0, 2] := by
  decide

theorem demoM_1110000 : fieldMul 7 5 20 [2, 2, 2, 2, 2, 0, 2] [1, 1, 1, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1110000 : specInv 7 5 20 [1, 1, 1, 0, 0, 0, 0] = some [2, 2, 2, 2, 2, 0, 2] :=
  specInv_white_7 [1, 1, 1, 0, 0, 0, 0] [1, 0, 2, 2, 1, 2, 2] [1, 0, 0, 1, 0, 0, 2] [2, 2, 2, 2, 2, 0, 2] demoR1_1110000 demoR2_1110000 demoC_1110000 demoM_1110000

theorem demoR1_2110000 : invRung 7 5 20 [2, 1, 1, 0, 0, 0, 0] [2, 1, 1, 0, 0, 0, 0] 1 2 false = ([0, 1, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_2110000 : invRung 7 5 20 [2, 1, 1, 0, 0, 0, 0] [0, 1, 2, 0, 0, 1, 1] 3 1 true = ([0, 1, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_2110000 : fieldCube 7 5 20 [0, 1, 1, 1, 2, 2, 1] = [0, 2, 2, 1, 0, 0, 2] := by
  decide

theorem demoM_2110000 : fieldMul 7 5 20 [0, 2, 2, 1, 0, 0, 2] [2, 1, 1, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110000 : mirrorTrits [0, 2, 2, 1, 0, 0, 2] = [0, 1, 1, 2, 0, 0, 1] := by
  decide

theorem demoInv_2110000 : specInv 7 5 20 [2, 1, 1, 0, 0, 0, 0] = some [0, 1, 1, 2, 0, 0, 1] :=
  specInv_mirror_7 [2, 1, 1, 0, 0, 0, 0] [0, 1, 2, 0, 0, 1, 1] [0, 1, 1, 1, 2, 2, 1] [0, 2, 2, 1, 0, 0, 2] [0, 1, 1, 2, 0, 0, 1] demoR1_2110000 demoR2_2110000 demoC_2110000 demoM_2110000 demoMir_2110000

theorem demoR1_0210000 : invRung 7 5 20 [0, 2, 1, 0, 0, 0, 0] [0, 2, 1, 0, 0, 0, 0] 1 2 false = ([2, 1, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0210000 : invRung 7 5 20 [0, 2, 1, 0, 0, 0, 0] [2, 1, 0, 0, 0, 0, 0] 3 1 true = ([2, 0, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0210000 : fieldCube 7 5 20 [2, 0, 0, 1, 2, 0, 1] = [0, 0, 0, 0, 1, 1, 0] := by
  decide

theorem demoM_0210000 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 1, 0] [0, 2, 1, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0210000 : specInv 7 5 20 [0, 2, 1, 0, 0, 0, 0] = some [0, 0, 0, 0, 1, 1, 0] :=
  specInv_white_7 [0, 2, 1, 0, 0, 0, 0] [2, 1, 0, 0, 0, 0, 0] [2, 0, 0, 1, 2, 0, 1] [0, 0, 0, 0, 1, 1, 0] demoR1_0210000 demoR2_0210000 demoC_0210000 demoM_0210000

theorem demoR1_1210000 : invRung 7 5 20 [1, 2, 1, 0, 0, 0, 0] [1, 2, 1, 0, 0, 0, 0] 1 2 false = ([0, 1, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1210000 : invRung 7 5 20 [1, 2, 1, 0, 0, 0, 0] [0, 1, 0, 0, 1, 0, 0] 3 1 true = ([0, 1, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1210000 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 1, 0] = [1, 2, 1, 2, 1, 2, 2] := by
  decide

theorem demoM_1210000 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 2, 2] [1, 2, 1, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1210000 : specInv 7 5 20 [1, 2, 1, 0, 0, 0, 0] = some [1, 2, 1, 2, 1, 2, 2] :=
  specInv_white_7 [1, 2, 1, 0, 0, 0, 0] [0, 1, 0, 0, 1, 0, 0] [0, 1, 2, 0, 1, 1, 0] [1, 2, 1, 2, 1, 2, 2] demoR1_1210000 demoR2_1210000 demoC_1210000 demoM_1210000

theorem demoR1_2210000 : invRung 7 5 20 [2, 2, 1, 0, 0, 0, 0] [2, 2, 1, 0, 0, 0, 0] 1 2 false = ([2, 1, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_2210000 : invRung 7 5 20 [2, 2, 1, 0, 0, 0, 0] [2, 1, 1, 0, 1, 0, 1] 3 1 true = ([1, 2, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2210000 : fieldCube 7 5 20 [1, 2, 2, 1, 2, 2, 0] = [1, 1, 0, 1, 2, 2, 2] := by
  decide

theorem demoM_2210000 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 2, 2] [2, 2, 1, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210000 : mirrorTrits [1, 1, 0, 1, 2, 2, 2] = [2, 2, 0, 2, 1, 1, 1] := by
  decide

theorem demoInv_2210000 : specInv 7 5 20 [2, 2, 1, 0, 0, 0, 0] = some [2, 2, 0, 2, 1, 1, 1] :=
  specInv_mirror_7 [2, 2, 1, 0, 0, 0, 0] [2, 1, 1, 0, 1, 0, 1] [1, 2, 2, 1, 2, 2, 0] [1, 1, 0, 1, 2, 2, 2] [2, 2, 0, 2, 1, 1, 1] demoR1_2210000 demoR2_2210000 demoC_2210000 demoM_2210000 demoMir_2210000

theorem demoR1_0020000 : invRung 7 5 20 [0, 0, 2, 0, 0, 0, 0] [0, 0, 2, 0, 0, 0, 0] 1 2 false = ([2, 2, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_0020000 : invRung 7 5 20 [0, 0, 2, 0, 0, 0, 0] [2, 2, 0, 2, 1, 0, 1] 3 1 true = ([1, 0, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0020000 : fieldCube 7 5 20 [1, 0, 2, 1, 0, 1, 2] = [0, 0, 0, 2, 0, 1, 0] := by
  decide

theorem demoM_0020000 : fieldMul 7 5 20 [0, 0, 0, 2, 0, 1, 0] [0, 0, 2, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020000 : mirrorTrits [0, 0, 0, 2, 0, 1, 0] = [0, 0, 0, 1, 0, 2, 0] := by
  decide

theorem demoInv_0020000 : specInv 7 5 20 [0, 0, 2, 0, 0, 0, 0] = some [0, 0, 0, 1, 0, 2, 0] :=
  specInv_mirror_7 [0, 0, 2, 0, 0, 0, 0] [2, 2, 0, 2, 1, 0, 1] [1, 0, 2, 1, 0, 1, 2] [0, 0, 0, 2, 0, 1, 0] [0, 0, 0, 1, 0, 2, 0] demoR1_0020000 demoR2_0020000 demoC_0020000 demoM_0020000 demoMir_0020000

theorem demoR1_1020000 : invRung 7 5 20 [1, 0, 2, 0, 0, 0, 0] [1, 0, 2, 0, 0, 0, 0] 1 2 false = ([1, 1, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_1020000 : invRung 7 5 20 [1, 0, 2, 0, 0, 0, 0] [1, 1, 2, 1, 0, 2, 0] 3 1 true = ([1, 1, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_1020000 : fieldCube 7 5 20 [1, 1, 2, 1, 0, 1, 2] = [0, 0, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_1020000 : fieldMul 7 5 20 [0, 0, 0, 0, 0, 1, 0] [1, 0, 2, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020000 : mirrorTrits [0, 0, 0, 0, 0, 1, 0] = [0, 0, 0, 0, 0, 2, 0] := by
  decide

theorem demoInv_1020000 : specInv 7 5 20 [1, 0, 2, 0, 0, 0, 0] = some [0, 0, 0, 0, 0, 2, 0] :=
  specInv_mirror_7 [1, 0, 2, 0, 0, 0, 0] [1, 1, 2, 1, 0, 2, 0] [1, 1, 2, 1, 0, 1, 2] [0, 0, 0, 0, 0, 1, 0] [0, 0, 0, 0, 0, 2, 0] demoR1_1020000 demoR2_1020000 demoC_1020000 demoM_1020000 demoMir_1020000

theorem demoR1_2020000 : invRung 7 5 20 [2, 0, 2, 0, 0, 0, 0] [2, 0, 2, 0, 0, 0, 0] 1 2 false = ([0, 1, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2020000 : invRung 7 5 20 [2, 0, 2, 0, 0, 0, 0] [0, 1, 1, 1, 0, 2, 1] 3 1 true = ([0, 1, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2020000 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 2, 2] = [1, 2, 2, 1, 1, 1, 1] := by
  decide

theorem demoM_2020000 : fieldMul 7 5 20 [1, 2, 2, 1, 1, 1, 1] [2, 0, 2, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2020000 : specInv 7 5 20 [2, 0, 2, 0, 0, 0, 0] = some [1, 2, 2, 1, 1, 1, 1] :=
  specInv_white_7 [2, 0, 2, 0, 0, 0, 0] [0, 1, 1, 1, 0, 2, 1] [0, 1, 0, 2, 1, 2, 2] [1, 2, 2, 1, 1, 1, 1] demoR1_2020000 demoR2_2020000 demoC_2020000 demoM_2020000

theorem demoR1_0120000 : invRung 7 5 20 [0, 1, 2, 0, 0, 0, 0] [0, 1, 2, 0, 0, 0, 0] 1 2 false = ([1, 2, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0120000 : invRung 7 5 20 [0, 1, 2, 0, 0, 0, 0] [1, 2, 0, 0, 0, 0, 0] 3 1 true = ([2, 0, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0120000 : fieldCube 7 5 20 [2, 0, 0, 1, 2, 0, 1] = [0, 0, 0, 0, 1, 1, 0] := by
  decide

theorem demoM_0120000 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 1, 0] [0, 1, 2, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0120000 : mirrorTrits [0, 0, 0, 0, 1, 1, 0] = [0, 0, 0, 0, 2, 2, 0] := by
  decide

theorem demoInv_0120000 : specInv 7 5 20 [0, 1, 2, 0, 0, 0, 0] = some [0, 0, 0, 0, 2, 2, 0] :=
  specInv_mirror_7 [0, 1, 2, 0, 0, 0, 0] [1, 2, 0, 0, 0, 0, 0] [2, 0, 0, 1, 2, 0, 1] [0, 0, 0, 0, 1, 1, 0] [0, 0, 0, 0, 2, 2, 0] demoR1_0120000 demoR2_0120000 demoC_0120000 demoM_0120000 demoMir_0120000

theorem demoR1_1120000 : invRung 7 5 20 [1, 1, 2, 0, 0, 0, 0] [1, 1, 2, 0, 0, 0, 0] 1 2 false = ([1, 2, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_1120000 : invRung 7 5 20 [1, 1, 2, 0, 0, 0, 0] [1, 2, 2, 0, 2, 0, 2] 3 1 true = ([1, 2, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1120000 : fieldCube 7 5 20 [1, 2, 2, 1, 2, 2, 0] = [1, 1, 0, 1, 2, 2, 2] := by
  decide

theorem demoM_1120000 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 2, 2] [1, 1, 2, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1120000 : specInv 7 5 20 [1, 1, 2, 0, 0, 0, 0] = some [1, 1, 0, 1, 2, 2, 2] :=
  specInv_white_7 [1, 1, 2, 0, 0, 0, 0] [1, 2, 2, 0, 2, 0, 2] [1, 2, 2, 1, 2, 2, 0] [1, 1, 0, 1, 2, 2, 2] demoR1_1120000 demoR2_1120000 demoC_1120000 demoM_1120000

theorem demoR1_2120000 : invRung 7 5 20 [2, 1, 2, 0, 0, 0, 0] [2, 1, 2, 0, 0, 0, 0] 1 2 false = ([0, 2, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2120000 : invRung 7 5 20 [2, 1, 2, 0, 0, 0, 0] [0, 2, 0, 0, 2, 0, 0] 3 1 true = ([0, 1, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2120000 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 1, 0] = [1, 2, 1, 2, 1, 2, 2] := by
  decide

theorem demoM_2120000 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 2, 2] [2, 1, 2, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120000 : mirrorTrits [1, 2, 1, 2, 1, 2, 2] = [2, 1, 2, 1, 2, 1, 1] := by
  decide

theorem demoInv_2120000 : specInv 7 5 20 [2, 1, 2, 0, 0, 0, 0] = some [2, 1, 2, 1, 2, 1, 1] :=
  specInv_mirror_7 [2, 1, 2, 0, 0, 0, 0] [0, 2, 0, 0, 2, 0, 0] [0, 1, 2, 0, 1, 1, 0] [1, 2, 1, 2, 1, 2, 2] [2, 1, 2, 1, 2, 1, 1] demoR1_2120000 demoR2_2120000 demoC_2120000 demoM_2120000 demoMir_2120000

theorem demoR1_0220000 : invRung 7 5 20 [0, 2, 2, 0, 0, 0, 0] [0, 2, 2, 0, 0, 0, 0] 1 2 false = ([2, 0, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_0220000 : invRung 7 5 20 [0, 2, 2, 0, 0, 0, 0] [2, 0, 2, 1, 2, 2, 2] 3 1 true = ([0, 2, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0220000 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 2, 0] = [0, 0, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_0220000 : fieldMul 7 5 20 [0, 0, 0, 0, 2, 1, 0] [0, 2, 2, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0220000 : mirrorTrits [0, 0, 0, 0, 2, 1, 0] = [0, 0, 0, 0, 1, 2, 0] := by
  decide

theorem demoInv_0220000 : specInv 7 5 20 [0, 2, 2, 0, 0, 0, 0] = some [0, 0, 0, 0, 1, 2, 0] :=
  specInv_mirror_7 [0, 2, 2, 0, 0, 0, 0] [2, 0, 2, 1, 2, 2, 2] [0, 2, 1, 1, 1, 2, 0] [0, 0, 0, 0, 2, 1, 0] [0, 0, 0, 0, 1, 2, 0] demoR1_0220000 demoR2_0220000 demoC_0220000 demoM_0220000 demoMir_0220000

theorem demoR1_1220000 : invRung 7 5 20 [1, 2, 2, 0, 0, 0, 0] [1, 2, 2, 0, 0, 0, 0] 1 2 false = ([0, 2, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_1220000 : invRung 7 5 20 [1, 2, 2, 0, 0, 0, 0] [0, 2, 1, 0, 0, 2, 2] 3 1 true = ([0, 1, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_1220000 : fieldCube 7 5 20 [0, 1, 1, 1, 2, 2, 1] = [0, 2, 2, 1, 0, 0, 2] := by
  decide

theorem demoM_1220000 : fieldMul 7 5 20 [0, 2, 2, 1, 0, 0, 2] [1, 2, 2, 0, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1220000 : specInv 7 5 20 [1, 2, 2, 0, 0, 0, 0] = some [0, 2, 2, 1, 0, 0, 2] :=
  specInv_white_7 [1, 2, 2, 0, 0, 0, 0] [0, 2, 1, 0, 0, 2, 2] [0, 1, 1, 1, 2, 2, 1] [0, 2, 2, 1, 0, 0, 2] demoR1_1220000 demoR2_1220000 demoC_1220000 demoM_1220000

theorem demoR1_2220000 : invRung 7 5 20 [2, 2, 2, 0, 0, 0, 0] [2, 2, 2, 0, 0, 0, 0] 1 2 false = ([2, 0, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_2220000 : invRung 7 5 20 [2, 2, 2, 0, 0, 0, 0] [2, 0, 1, 1, 2, 1, 1] 3 1 true = ([1, 0, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_2220000 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 0, 2] = [2, 2, 2, 2, 2, 0, 2] := by
  decide

theorem demoM_2220000 : fieldMul 7 5 20 [2, 2, 2, 2, 2, 0, 2] [2, 2, 2, 0, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220000 : mirrorTrits [2, 2, 2, 2, 2, 0, 2] = [1, 1, 1, 1, 1, 0, 1] := by
  decide

theorem demoInv_2220000 : specInv 7 5 20 [2, 2, 2, 0, 0, 0, 0] = some [1, 1, 1, 1, 1, 0, 1] :=
  specInv_mirror_7 [2, 2, 2, 0, 0, 0, 0] [2, 0, 1, 1, 2, 1, 1] [1, 0, 0, 1, 0, 0, 2] [2, 2, 2, 2, 2, 0, 2] [1, 1, 1, 1, 1, 0, 1] demoR1_2220000 demoR2_2220000 demoC_2220000 demoM_2220000 demoMir_2220000

theorem demoR1_0001000 : invRung 7 5 20 [0, 0, 0, 1, 0, 0, 0] [0, 0, 0, 1, 0, 0, 0] 1 2 false = ([2, 0, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_0001000 : invRung 7 5 20 [0, 0, 0, 1, 0, 0, 0] [2, 0, 0, 2, 2, 0, 2] 3 1 true = ([0, 0, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0001000 : fieldCube 7 5 20 [0, 0, 0, 0, 2, 0, 1] = [0, 0, 2, 0, 1, 0, 0] := by
  decide

theorem demoM_0001000 : fieldMul 7 5 20 [0, 0, 2, 0, 1, 0, 0] [0, 0, 0, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0001000 : specInv 7 5 20 [0, 0, 0, 1, 0, 0, 0] = some [0, 0, 2, 0, 1, 0, 0] :=
  specInv_white_7 [0, 0, 0, 1, 0, 0, 0] [2, 0, 0, 2, 2, 0, 2] [0, 0, 0, 0, 2, 0, 1] [0, 0, 2, 0, 1, 0, 0] demoR1_0001000 demoR2_0001000 demoC_0001000 demoM_0001000

theorem demoR1_1001000 : invRung 7 5 20 [1, 0, 0, 1, 0, 0, 0] [1, 0, 0, 1, 0, 0, 0] 1 2 false = ([0, 2, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_1001000 : invRung 7 5 20 [1, 0, 0, 1, 0, 0, 0] [0, 2, 0, 2, 0, 2, 1] 3 1 true = ([0, 0, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_1001000 : fieldCube 7 5 20 [0, 0, 0, 0, 0, 2, 1] = [2, 0, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_1001000 : fieldMul 7 5 20 [2, 0, 1, 1, 0, 0, 2] [1, 0, 0, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1001000 : specInv 7 5 20 [1, 0, 0, 1, 0, 0, 0] = some [2, 0, 1, 1, 0, 0, 2] :=
  specInv_white_7 [1, 0, 0, 1, 0, 0, 0] [0, 2, 0, 2, 0, 2, 1] [0, 0, 0, 0, 0, 2, 1] [2, 0, 1, 1, 0, 0, 2] demoR1_1001000 demoR2_1001000 demoC_1001000 demoM_1001000

theorem demoR1_2001000 : invRung 7 5 20 [2, 0, 0, 1, 0, 0, 0] [2, 0, 0, 1, 0, 0, 0] 1 2 false = ([1, 0, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_2001000 : invRung 7 5 20 [2, 0, 0, 1, 0, 0, 0] [1, 0, 1, 1, 0, 2, 0] 3 1 true = ([0, 0, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_2001000 : fieldCube 7 5 20 [0, 0, 0, 0, 0, 1, 1] = [1, 2, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_2001000 : fieldMul 7 5 20 [1, 2, 0, 1, 2, 2, 0] [2, 0, 0, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2001000 : specInv 7 5 20 [2, 0, 0, 1, 0, 0, 0] = some [1, 2, 0, 1, 2, 2, 0] :=
  specInv_white_7 [2, 0, 0, 1, 0, 0, 0] [1, 0, 1, 1, 0, 2, 0] [0, 0, 0, 0, 0, 1, 1] [1, 2, 0, 1, 2, 2, 0] demoR1_2001000 demoR2_2001000 demoC_2001000 demoM_2001000

theorem demoR1_0101000 : invRung 7 5 20 [0, 1, 0, 1, 0, 0, 0] [0, 1, 0, 1, 0, 0, 0] 1 2 false = ([1, 1, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0101000 : invRung 7 5 20 [0, 1, 0, 1, 0, 0, 0] [1, 1, 2, 0, 2, 2, 2] 3 1 true = ([2, 0, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_0101000 : fieldCube 7 5 20 [2, 0, 1, 2, 2, 1, 2] = [2, 2, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_0101000 : fieldMul 7 5 20 [2, 2, 1, 1, 0, 1, 1] [0, 1, 0, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101000 : mirrorTrits [2, 2, 1, 1, 0, 1, 1] = [1, 1, 2, 2, 0, 2, 2] := by
  decide

theorem demoInv_0101000 : specInv 7 5 20 [0, 1, 0, 1, 0, 0, 0] = some [1, 1, 2, 2, 0, 2, 2] :=
  specInv_mirror_7 [0, 1, 0, 1, 0, 0, 0] [1, 1, 2, 0, 2, 2, 2] [2, 0, 1, 2, 2, 1, 2] [2, 2, 1, 1, 0, 1, 1] [1, 1, 2, 2, 0, 2, 2] demoR1_0101000 demoR2_0101000 demoC_0101000 demoM_0101000 demoMir_0101000

theorem demoR1_1101000 : invRung 7 5 20 [1, 1, 0, 1, 0, 0, 0] [1, 1, 0, 1, 0, 0, 0] 1 2 false = ([1, 0, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1101000 : invRung 7 5 20 [1, 1, 0, 1, 0, 0, 0] [1, 0, 0, 0, 0, 2, 0] 3 1 true = ([1, 2, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1101000 : fieldCube 7 5 20 [1, 2, 0, 1, 0, 2, 0] = [1, 2, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_1101000 : fieldMul 7 5 20 [1, 2, 0, 2, 2, 0, 1] [1, 1, 0, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1101000 : mirrorTrits [1, 2, 0, 2, 2, 0, 1] = [2, 1, 0, 1, 1, 0, 2] := by
  decide

theorem demoInv_1101000 : specInv 7 5 20 [1, 1, 0, 1, 0, 0, 0] = some [2, 1, 0, 1, 1, 0, 2] :=
  specInv_mirror_7 [1, 1, 0, 1, 0, 0, 0] [1, 0, 0, 0, 0, 2, 0] [1, 2, 0, 1, 0, 2, 0] [1, 2, 0, 2, 2, 0, 1] [2, 1, 0, 1, 1, 0, 2] demoR1_1101000 demoR2_1101000 demoC_1101000 demoM_1101000 demoMir_1101000

theorem demoR1_2101000 : invRung 7 5 20 [2, 1, 0, 1, 0, 0, 0] [2, 1, 0, 1, 0, 0, 0] 1 2 false = ([0, 0, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2101000 : invRung 7 5 20 [2, 1, 0, 1, 0, 0, 0] [0, 0, 1, 1, 0, 2, 1] 3 1 true = ([2, 2, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_2101000 : fieldCube 7 5 20 [2, 2, 2, 0, 1, 1, 2] = [0, 1, 2, 2, 0, 1, 1] := by
  decide

theorem demoM_2101000 : fieldMul 7 5 20 [0, 1, 2, 2, 0, 1, 1] [2, 1, 0, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101000 : mirrorTrits [0, 1, 2, 2, 0, 1, 1] = [0, 2, 1, 1, 0, 2, 2] := by
  decide

theorem demoInv_2101000 : specInv 7 5 20 [2, 1, 0, 1, 0, 0, 0] = some [0, 2, 1, 1, 0, 2, 2] :=
  specInv_mirror_7 [2, 1, 0, 1, 0, 0, 0] [0, 0, 1, 1, 0, 2, 1] [2, 2, 2, 0, 1, 1, 2] [0, 1, 2, 2, 0, 1, 1] [0, 2, 1, 1, 0, 2, 2] demoR1_2101000 demoR2_2101000 demoC_2101000 demoM_2101000 demoMir_2101000

theorem demoR1_0201000 : invRung 7 5 20 [0, 2, 0, 1, 0, 0, 0] [0, 2, 0, 1, 0, 0, 0] 1 2 false = ([0, 0, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_0201000 : invRung 7 5 20 [0, 2, 0, 1, 0, 0, 0] [0, 0, 1, 2, 1, 2, 0] 3 1 true = ([1, 2, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0201000 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 2, 2] = [0, 0, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_0201000 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 0, 0] [0, 2, 0, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0201000 : specInv 7 5 20 [0, 2, 0, 1, 0, 0, 0] = some [0, 0, 0, 0, 1, 0, 0] :=
  specInv_white_7 [0, 2, 0, 1, 0, 0, 0] [0, 0, 1, 2, 1, 2, 0] [1, 2, 1, 0, 2, 2, 2] [0, 0, 0, 0, 1, 0, 0] demoR1_0201000 demoR2_0201000 demoC_0201000 demoM_0201000

theorem demoR1_1201000 : invRung 7 5 20 [1, 2, 0, 1, 0, 0, 0] [1, 2, 0, 1, 0, 0, 0] 1 2 false = ([2, 0, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_1201000 : invRung 7 5 20 [1, 2, 0, 1, 0, 0, 0] [2, 0, 0, 0, 1, 2, 1] 3 1 true = ([2, 1, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1201000 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 2, 0] = [2, 2, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_1201000 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 0, 2] [1, 2, 0, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1201000 : specInv 7 5 20 [1, 2, 0, 1, 0, 0, 0] = some [2, 2, 0, 1, 2, 0, 2] :=
  specInv_white_7 [1, 2, 0, 1, 0, 0, 0] [2, 0, 0, 0, 1, 2, 1] [2, 1, 1, 1, 0, 2, 0] [2, 2, 0, 1, 2, 0, 2] demoR1_1201000 demoR2_1201000 demoC_1201000 demoM_1201000

theorem demoR1_2201000 : invRung 7 5 20 [2, 2, 0, 1, 0, 0, 0] [2, 2, 0, 1, 0, 0, 0] 1 2 false = ([2, 0, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_2201000 : invRung 7 5 20 [2, 2, 0, 1, 0, 0, 0] [2, 0, 1, 1, 0, 1, 2] 3 1 true = ([0, 2, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_2201000 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 0, 1] = [0, 2, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_2201000 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 2, 1] [2, 2, 0, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2201000 : specInv 7 5 20 [2, 2, 0, 1, 0, 0, 0] = some [0, 2, 2, 1, 1, 2, 1] :=
  specInv_white_7 [2, 2, 0, 1, 0, 0, 0] [2, 0, 1, 1, 0, 1, 2] [0, 2, 2, 0, 1, 0, 1] [0, 2, 2, 1, 1, 2, 1] demoR1_2201000 demoR2_2201000 demoC_2201000 demoM_2201000

theorem demoR1_0011000 : invRung 7 5 20 [0, 0, 1, 1, 0, 0, 0] [0, 0, 1, 1, 0, 0, 0] 1 2 false = ([2, 0, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_0011000 : invRung 7 5 20 [0, 0, 1, 1, 0, 0, 0] [2, 0, 2, 0, 2, 0, 1] 3 1 true = ([1, 1, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0011000 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 2, 2] = [0, 0, 0, 2, 1, 0, 0] := by
  decide

theorem demoM_0011000 : fieldMul 7 5 20 [0, 0, 0, 2, 1, 0, 0] [0, 0, 1, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0011000 : specInv 7 5 20 [0, 0, 1, 1, 0, 0, 0] = some [0, 0, 0, 2, 1, 0, 0] :=
  specInv_white_7 [0, 0, 1, 1, 0, 0, 0] [2, 0, 2, 0, 2, 0, 1] [1, 1, 1, 0, 2, 2, 2] [0, 0, 0, 2, 1, 0, 0] demoR1_0011000 demoR2_0011000 demoC_0011000 demoM_0011000

theorem demoR1_1011000 : invRung 7 5 20 [1, 0, 1, 1, 0, 0, 0] [1, 0, 1, 1, 0, 0, 0] 1 2 false = ([1, 1, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_1011000 : invRung 7 5 20 [1, 0, 1, 1, 0, 0, 0] [1, 1, 2, 0, 0, 1, 1] 3 1 true = ([2, 1, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_1011000 : fieldCube 7 5 20 [2, 1, 0, 1, 0, 2, 2] = [2, 1, 1, 0, 1, 2, 0] := by
  decide

theorem demoM_1011000 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 2, 0] [1, 0, 1, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011000 : mirrorTrits [2, 1, 1, 0, 1, 2, 0] = [1, 2, 2, 0, 2, 1, 0] := by
  decide

theorem demoInv_1011000 : specInv 7 5 20 [1, 0, 1, 1, 0, 0, 0] = some [1, 2, 2, 0, 2, 1, 0] :=
  specInv_mirror_7 [1, 0, 1, 1, 0, 0, 0] [1, 1, 2, 0, 0, 1, 1] [2, 1, 0, 1, 0, 2, 2] [2, 1, 1, 0, 1, 2, 0] [1, 2, 2, 0, 2, 1, 0] demoR1_1011000 demoR2_1011000 demoC_1011000 demoM_1011000 demoMir_1011000

theorem demoR1_2011000 : invRung 7 5 20 [2, 0, 1, 1, 0, 0, 0] [2, 0, 1, 1, 0, 0, 0] 1 2 false = ([0, 0, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_2011000 : invRung 7 5 20 [2, 0, 1, 1, 0, 0, 0] [0, 0, 0, 1, 2, 2, 2] 3 1 true = ([2, 0, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_2011000 : fieldCube 7 5 20 [2, 0, 2, 1, 1, 0, 2] = [0, 0, 2, 0, 2, 1, 2] := by
  decide

theorem demoM_2011000 : fieldMul 7 5 20 [0, 0, 2, 0, 2, 1, 2] [2, 0, 1, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011000 : mirrorTrits [0, 0, 2, 0, 2, 1, 2] = [0, 0, 1, 0, 1, 2, 1] := by
  decide

theorem demoInv_2011000 : specInv 7 5 20 [2, 0, 1, 1, 0, 0, 0] = some [0, 0, 1, 0, 1, 2, 1] :=
  specInv_mirror_7 [2, 0, 1, 1, 0, 0, 0] [0, 0, 0, 1, 2, 2, 2] [2, 0, 2, 1, 1, 0, 2] [0, 0, 2, 0, 2, 1, 2] [0, 0, 1, 0, 1, 2, 1] demoR1_2011000 demoR2_2011000 demoC_2011000 demoM_2011000 demoMir_2011000

theorem demoR1_0111000 : invRung 7 5 20 [0, 1, 1, 1, 0, 0, 0] [0, 1, 1, 1, 0, 0, 0] 1 2 false = ([1, 2, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0111000 : invRung 7 5 20 [0, 1, 1, 1, 0, 0, 0] [1, 2, 0, 0, 2, 1, 2] 3 1 true = ([2, 0, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0111000 : fieldCube 7 5 20 [2, 0, 0, 0, 1, 0, 1] = [2, 2, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_0111000 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 2, 2] [0, 1, 1, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0111000 : specInv 7 5 20 [0, 1, 1, 1, 0, 0, 0] = some [2, 2, 2, 2, 1, 2, 2] :=
  specInv_white_7 [0, 1, 1, 1, 0, 0, 0] [1, 2, 0, 0, 2, 1, 2] [2, 0, 0, 0, 1, 0, 1] [2, 2, 2, 2, 1, 2, 2] demoR1_0111000 demoR2_0111000 demoC_0111000 demoM_0111000

theorem demoR1_1111000 : invRung 7 5 20 [1, 1, 1, 1, 0, 0, 0] [1, 1, 1, 1, 0, 0, 0] 1 2 false = ([2, 2, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_1111000 : invRung 7 5 20 [1, 1, 1, 1, 0, 0, 0] [2, 2, 2, 2, 1, 1, 0] 3 1 true = ([1, 0, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_1111000 : fieldCube 7 5 20 [1, 0, 1, 1, 2, 1, 2] = [0, 2, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_1111000 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 0, 1] [1, 1, 1, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111000 : mirrorTrits [0, 2, 0, 1, 0, 0, 1] = [0, 1, 0, 2, 0, 0, 2] := by
  decide

theorem demoInv_1111000 : specInv 7 5 20 [1, 1, 1, 1, 0, 0, 0] = some [0, 1, 0, 2, 0, 0, 2] :=
  specInv_mirror_7 [1, 1, 1, 1, 0, 0, 0] [2, 2, 2, 2, 1, 1, 0] [1, 0, 1, 1, 2, 1, 2] [0, 2, 0, 1, 0, 0, 1] [0, 1, 0, 2, 0, 0, 2] demoR1_1111000 demoR2_1111000 demoC_1111000 demoM_1111000 demoMir_1111000

theorem demoR1_2111000 : invRung 7 5 20 [2, 1, 1, 1, 0, 0, 0] [2, 1, 1, 1, 0, 0, 0] 1 2 false = ([2, 2, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_2111000 : invRung 7 5 20 [2, 1, 1, 1, 0, 0, 0] [2, 2, 1, 1, 1, 0, 2] 3 1 true = ([1, 0, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_2111000 : fieldCube 7 5 20 [1, 0, 2, 2, 0, 1, 2] = [1, 0, 1, 2, 0, 2, 0] := by
  decide

theorem demoM_2111000 : fieldMul 7 5 20 [1, 0, 1, 2, 0, 2, 0] [2, 1, 1, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2111000 : specInv 7 5 20 [2, 1, 1, 1, 0, 0, 0] = some [1, 0, 1, 2, 0, 2, 0] :=
  specInv_white_7 [2, 1, 1, 1, 0, 0, 0] [2, 2, 1, 1, 1, 0, 2] [1, 0, 2, 2, 0, 1, 2] [1, 0, 1, 2, 0, 2, 0] demoR1_2111000 demoR2_2111000 demoC_2111000 demoM_2111000

theorem demoR1_0211000 : invRung 7 5 20 [0, 2, 1, 1, 0, 0, 0] [0, 2, 1, 1, 0, 0, 0] 1 2 false = ([1, 1, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_0211000 : invRung 7 5 20 [0, 2, 1, 1, 0, 0, 0] [1, 1, 2, 1, 1, 1, 1] 3 1 true = ([0, 0, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_0211000 : fieldCube 7 5 20 [0, 0, 2, 0, 2, 2, 1] = [2, 2, 1, 0, 0, 2, 0] := by
  decide

theorem demoM_0211000 : fieldMul 7 5 20 [2, 2, 1, 0, 0, 2, 0] [0, 2, 1, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211000 : mirrorTrits [2, 2, 1, 0, 0, 2, 0] = [1, 1, 2, 0, 0, 1, 0] := by
  decide

theorem demoInv_0211000 : specInv 7 5 20 [0, 2, 1, 1, 0, 0, 0] = some [1, 1, 2, 0, 0, 1, 0] :=
  specInv_mirror_7 [0, 2, 1, 1, 0, 0, 0] [1, 1, 2, 1, 1, 1, 1] [0, 0, 2, 0, 2, 2, 1] [2, 2, 1, 0, 0, 2, 0] [1, 1, 2, 0, 0, 1, 0] demoR1_0211000 demoR2_0211000 demoC_0211000 demoM_0211000 demoMir_0211000

theorem demoR1_1211000 : invRung 7 5 20 [1, 2, 1, 1, 0, 0, 0] [1, 2, 1, 1, 0, 0, 0] 1 2 false = ([1, 1, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_1211000 : invRung 7 5 20 [1, 2, 1, 1, 0, 0, 0] [1, 1, 0, 0, 0, 2, 1] 3 1 true = ([1, 1, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1211000 : fieldCube 7 5 20 [1, 1, 1, 1, 0, 1, 1] = [0, 2, 1, 2, 2, 0, 1] := by
  decide

theorem demoM_1211000 : fieldMul 7 5 20 [0, 2, 1, 2, 2, 0, 1] [1, 2, 1, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1211000 : mirrorTrits [0, 2, 1, 2, 2, 0, 1] = [0, 1, 2, 1, 1, 0, 2] := by
  decide

theorem demoInv_1211000 : specInv 7 5 20 [1, 2, 1, 1, 0, 0, 0] = some [0, 1, 2, 1, 1, 0, 2] :=
  specInv_mirror_7 [1, 2, 1, 1, 0, 0, 0] [1, 1, 0, 0, 0, 2, 1] [1, 1, 1, 1, 0, 1, 1] [0, 2, 1, 2, 2, 0, 1] [0, 1, 2, 1, 1, 0, 2] demoR1_1211000 demoR2_1211000 demoC_1211000 demoM_1211000 demoMir_1211000

theorem demoR1_2211000 : invRung 7 5 20 [2, 2, 1, 1, 0, 0, 0] [2, 2, 1, 1, 0, 0, 0] 1 2 false = ([2, 0, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_2211000 : invRung 7 5 20 [2, 2, 1, 1, 0, 0, 0] [2, 0, 0, 1, 0, 1, 2] 3 1 true = ([2, 0, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_2211000 : fieldCube 7 5 20 [2, 0, 0, 2, 1, 0, 1] = [1, 2, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_2211000 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 1, 2] [2, 2, 1, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2211000 : specInv 7 5 20 [2, 2, 1, 1, 0, 0, 0] = some [1, 2, 1, 2, 1, 1, 2] :=
  specInv_white_7 [2, 2, 1, 1, 0, 0, 0] [2, 0, 0, 1, 0, 1, 2] [2, 0, 0, 2, 1, 0, 1] [1, 2, 1, 2, 1, 1, 2] demoR1_2211000 demoR2_2211000 demoC_2211000 demoM_2211000

theorem demoR1_0021000 : invRung 7 5 20 [0, 0, 2, 1, 0, 0, 0] [0, 0, 2, 1, 0, 0, 0] 1 2 false = ([0, 1, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_0021000 : invRung 7 5 20 [0, 0, 2, 1, 0, 0, 0] [0, 1, 2, 1, 2, 1, 0] 3 1 true = ([1, 0, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0021000 : fieldCube 7 5 20 [1, 0, 1, 0, 2, 2, 2] = [0, 0, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_0021000 : fieldMul 7 5 20 [0, 0, 0, 1, 1, 0, 0] [0, 0, 2, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0021000 : specInv 7 5 20 [0, 0, 2, 1, 0, 0, 0] = some [0, 0, 0, 1, 1, 0, 0] :=
  specInv_white_7 [0, 0, 2, 1, 0, 0, 0] [0, 1, 2, 1, 2, 1, 0] [1, 0, 1, 0, 2, 2, 2] [0, 0, 0, 1, 1, 0, 0] demoR1_0021000 demoR2_0021000 demoC_0021000 demoM_0021000

theorem demoR1_1021000 : invRung 7 5 20 [1, 0, 2, 1, 0, 0, 0] [1, 0, 2, 1, 0, 0, 0] 1 2 false = ([2, 1, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_1021000 : invRung 7 5 20 [1, 0, 2, 1, 0, 0, 0] [2, 1, 0, 1, 0, 1, 0] 3 1 true = ([2, 2, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_1021000 : fieldCube 7 5 20 [2, 2, 1, 2, 0, 2, 2] = [0, 1, 2, 1, 1, 0, 1] := by
  decide

theorem demoM_1021000 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 0, 1] [1, 0, 2, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021000 : mirrorTrits [0, 1, 2, 1, 1, 0, 1] = [0, 2, 1, 2, 2, 0, 2] := by
  decide

theorem demoInv_1021000 : specInv 7 5 20 [1, 0, 2, 1, 0, 0, 0] = some [0, 2, 1, 2, 2, 0, 2] :=
  specInv_mirror_7 [1, 0, 2, 1, 0, 0, 0] [2, 1, 0, 1, 0, 1, 0] [2, 2, 1, 2, 0, 2, 2] [0, 1, 2, 1, 1, 0, 1] [0, 2, 1, 2, 2, 0, 2] demoR1_1021000 demoR2_1021000 demoC_1021000 demoM_1021000 demoMir_1021000

theorem demoR1_2021000 : invRung 7 5 20 [2, 0, 2, 1, 0, 0, 0] [2, 0, 2, 1, 0, 0, 0] 1 2 false = ([1, 1, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_2021000 : invRung 7 5 20 [2, 0, 2, 1, 0, 0, 0] [1, 1, 2, 1, 1, 0, 2] 3 1 true = ([0, 0, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2021000 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 1, 0] = [2, 0, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_2021000 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 1, 1] [2, 0, 2, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021000 : mirrorTrits [2, 0, 2, 2, 1, 1, 1] = [1, 0, 1, 1, 2, 2, 2] := by
  decide

theorem demoInv_2021000 : specInv 7 5 20 [2, 0, 2, 1, 0, 0, 0] = some [1, 0, 1, 1, 2, 2, 2] :=
  specInv_mirror_7 [2, 0, 2, 1, 0, 0, 0] [1, 1, 2, 1, 1, 0, 2] [0, 0, 0, 1, 2, 1, 0] [2, 0, 2, 2, 1, 1, 1] [1, 0, 1, 1, 2, 2, 2] demoR1_2021000 demoR2_2021000 demoC_2021000 demoM_2021000 demoMir_2021000

theorem demoR1_0121000 : invRung 7 5 20 [0, 1, 2, 1, 0, 0, 0] [0, 1, 2, 1, 0, 0, 0] 1 2 false = ([2, 0, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_0121000 : invRung 7 5 20 [0, 1, 2, 1, 0, 0, 0] [2, 0, 1, 2, 1, 0, 1] 3 1 true = ([0, 1, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0121000 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 1, 0] = [2, 1, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_0121000 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 2, 1] [0, 1, 2, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0121000 : specInv 7 5 20 [0, 1, 2, 1, 0, 0, 0] = some [2, 1, 2, 1, 1, 2, 1] :=
  specInv_white_7 [0, 1, 2, 1, 0, 0, 0] [2, 0, 1, 2, 1, 0, 1] [0, 1, 2, 1, 0, 1, 0] [2, 1, 2, 1, 1, 2, 1] demoR1_0121000 demoR2_0121000 demoC_0121000 demoM_0121000

theorem demoR1_1121000 : invRung 7 5 20 [1, 1, 2, 1, 0, 0, 0] [1, 1, 2, 1, 0, 0, 0] 1 2 false = ([0, 1, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1121000 : invRung 7 5 20 [1, 1, 2, 1, 0, 0, 0] [0, 1, 2, 0, 1, 0, 1] 3 1 true = ([0, 0, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_1121000 : fieldCube 7 5 20 [0, 0, 1, 1, 2, 2, 1] = [0, 2, 2, 0, 0, 0, 2] := by
  decide

theorem demoM_1121000 : fieldMul 7 5 20 [0, 2, 2, 0, 0, 0, 2] [1, 1, 2, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1121000 : specInv 7 5 20 [1, 1, 2, 1, 0, 0, 0] = some [0, 2, 2, 0, 0, 0, 2] :=
  specInv_white_7 [1, 1, 2, 1, 0, 0, 0] [0, 1, 2, 0, 1, 0, 1] [0, 0, 1, 1, 2, 2, 1] [0, 2, 2, 0, 0, 0, 2] demoR1_1121000 demoR2_1121000 demoC_1121000 demoM_1121000

theorem demoR1_2121000 : invRung 7 5 20 [2, 1, 2, 1, 0, 0, 0] [2, 1, 2, 1, 0, 0, 0] 1 2 false = ([0, 1, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_2121000 : invRung 7 5 20 [2, 1, 2, 1, 0, 0, 0] [0, 1, 0, 0, 1, 1, 0] 3 1 true = ([0, 1, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_2121000 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 1, 1] = [2, 0, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_2121000 : fieldMul 7 5 20 [2, 0, 1, 0, 2, 1, 0] [2, 1, 2, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2121000 : mirrorTrits [2, 0, 1, 0, 2, 1, 0] = [1, 0, 2, 0, 1, 2, 0] := by
  decide

theorem demoInv_2121000 : specInv 7 5 20 [2, 1, 2, 1, 0, 0, 0] = some [1, 0, 2, 0, 1, 2, 0] :=
  specInv_mirror_7 [2, 1, 2, 1, 0, 0, 0] [0, 1, 0, 0, 1, 1, 0] [0, 1, 2, 1, 1, 1, 1] [2, 0, 1, 0, 2, 1, 0] [1, 0, 2, 0, 1, 2, 0] demoR1_2121000 demoR2_2121000 demoC_2121000 demoM_2121000 demoMir_2121000

theorem demoR1_0221000 : invRung 7 5 20 [0, 2, 2, 1, 0, 0, 0] [0, 2, 2, 1, 0, 0, 0] 1 2 false = ([0, 1, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_0221000 : invRung 7 5 20 [0, 2, 2, 1, 0, 0, 0] [0, 1, 2, 1, 2, 2, 0] 3 1 true = ([2, 2, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_0221000 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 0, 1] = [1, 0, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_0221000 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 2, 1] [0, 2, 2, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0221000 : mirrorTrits [1, 0, 1, 2, 1, 2, 1] = [2, 0, 2, 1, 2, 1, 2] := by
  decide

theorem demoInv_0221000 : specInv 7 5 20 [0, 2, 2, 1, 0, 0, 0] = some [2, 0, 2, 1, 2, 1, 2] :=
  specInv_mirror_7 [0, 2, 2, 1, 0, 0, 0] [0, 1, 2, 1, 2, 2, 0] [2, 2, 1, 2, 2, 0, 1] [1, 0, 1, 2, 1, 2, 1] [2, 0, 2, 1, 2, 1, 2] demoR1_0221000 demoR2_0221000 demoC_0221000 demoM_0221000 demoMir_0221000

theorem demoR1_1221000 : invRung 7 5 20 [1, 2, 2, 1, 0, 0, 0] [1, 2, 2, 1, 0, 0, 0] 1 2 false = ([0, 1, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_1221000 : invRung 7 5 20 [1, 2, 2, 1, 0, 0, 0] [0, 1, 0, 1, 0, 1, 1] 3 1 true = ([0, 1, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1221000 : fieldCube 7 5 20 [0, 1, 2, 0, 0, 1, 0] = [1, 1, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_1221000 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 1, 1] [1, 2, 2, 1, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1221000 : specInv 7 5 20 [1, 2, 2, 1, 0, 0, 0] = some [1, 1, 1, 1, 1, 1, 1] :=
  specInv_white_7 [1, 2, 2, 1, 0, 0, 0] [0, 1, 0, 1, 0, 1, 1] [0, 1, 2, 0, 0, 1, 0] [1, 1, 1, 1, 1, 1, 1] demoR1_1221000 demoR2_1221000 demoC_1221000 demoM_1221000

theorem demoR1_2221000 : invRung 7 5 20 [2, 2, 2, 1, 0, 0, 0] [2, 2, 2, 1, 0, 0, 0] 1 2 false = ([1, 2, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_2221000 : invRung 7 5 20 [2, 2, 2, 1, 0, 0, 0] [1, 2, 0, 2, 1, 0, 1] 3 1 true = ([2, 2, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_2221000 : fieldCube 7 5 20 [2, 2, 1, 1, 0, 0, 0] = [0, 0, 1, 2, 0, 1, 1] := by
  decide

theorem demoM_2221000 : fieldMul 7 5 20 [0, 0, 1, 2, 0, 1, 1] [2, 2, 2, 1, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221000 : mirrorTrits [0, 0, 1, 2, 0, 1, 1] = [0, 0, 2, 1, 0, 2, 2] := by
  decide

theorem demoInv_2221000 : specInv 7 5 20 [2, 2, 2, 1, 0, 0, 0] = some [0, 0, 2, 1, 0, 2, 2] :=
  specInv_mirror_7 [2, 2, 2, 1, 0, 0, 0] [1, 2, 0, 2, 1, 0, 1] [2, 2, 1, 1, 0, 0, 0] [0, 0, 1, 2, 0, 1, 1] [0, 0, 2, 1, 0, 2, 2] demoR1_2221000 demoR2_2221000 demoC_2221000 demoM_2221000 demoMir_2221000

theorem demoR1_0002000 : invRung 7 5 20 [0, 0, 0, 2, 0, 0, 0] [0, 0, 0, 2, 0, 0, 0] 1 2 false = ([1, 0, 0, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_0002000 : invRung 7 5 20 [0, 0, 0, 2, 0, 0, 0] [1, 0, 0, 1, 1, 0, 1] 3 1 true = ([0, 0, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0002000 : fieldCube 7 5 20 [0, 0, 0, 0, 2, 0, 1] = [0, 0, 2, 0, 1, 0, 0] := by
  decide

theorem demoM_0002000 : fieldMul 7 5 20 [0, 0, 2, 0, 1, 0, 0] [0, 0, 0, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002000 : mirrorTrits [0, 0, 2, 0, 1, 0, 0] = [0, 0, 1, 0, 2, 0, 0] := by
  decide

theorem demoInv_0002000 : specInv 7 5 20 [0, 0, 0, 2, 0, 0, 0] = some [0, 0, 1, 0, 2, 0, 0] :=
  specInv_mirror_7 [0, 0, 0, 2, 0, 0, 0] [1, 0, 0, 1, 1, 0, 1] [0, 0, 0, 0, 2, 0, 1] [0, 0, 2, 0, 1, 0, 0] [0, 0, 1, 0, 2, 0, 0] demoR1_0002000 demoR2_0002000 demoC_0002000 demoM_0002000 demoMir_0002000

theorem demoR1_1002000 : invRung 7 5 20 [1, 0, 0, 2, 0, 0, 0] [1, 0, 0, 2, 0, 0, 0] 1 2 false = ([2, 0, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_1002000 : invRung 7 5 20 [1, 0, 0, 2, 0, 0, 0] [2, 0, 2, 2, 0, 1, 0] 3 1 true = ([0, 0, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_1002000 : fieldCube 7 5 20 [0, 0, 0, 0, 0, 1, 1] = [1, 2, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_1002000 : fieldMul 7 5 20 [1, 2, 0, 1, 2, 2, 0] [1, 0, 0, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002000 : mirrorTrits [1, 2, 0, 1, 2, 2, 0] = [2, 1, 0, 2, 1, 1, 0] := by
  decide

theorem demoInv_1002000 : specInv 7 5 20 [1, 0, 0, 2, 0, 0, 0] = some [2, 1, 0, 2, 1, 1, 0] :=
  specInv_mirror_7 [1, 0, 0, 2, 0, 0, 0] [2, 0, 2, 2, 0, 1, 0] [0, 0, 0, 0, 0, 1, 1] [1, 2, 0, 1, 2, 2, 0] [2, 1, 0, 2, 1, 1, 0] demoR1_1002000 demoR2_1002000 demoC_1002000 demoM_1002000 demoMir_1002000

theorem demoR1_2002000 : invRung 7 5 20 [2, 0, 0, 2, 0, 0, 0] [2, 0, 0, 2, 0, 0, 0] 1 2 false = ([0, 1, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_2002000 : invRung 7 5 20 [2, 0, 0, 2, 0, 0, 0] [0, 1, 0, 1, 0, 1, 2] 3 1 true = ([0, 0, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_2002000 : fieldCube 7 5 20 [0, 0, 0, 0, 0, 2, 1] = [2, 0, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_2002000 : fieldMul 7 5 20 [2, 0, 1, 1, 0, 0, 2] [2, 0, 0, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002000 : mirrorTrits [2, 0, 1, 1, 0, 0, 2] = [1, 0, 2, 2, 0, 0, 1] := by
  decide

theorem demoInv_2002000 : specInv 7 5 20 [2, 0, 0, 2, 0, 0, 0] = some [1, 0, 2, 2, 0, 0, 1] :=
  specInv_mirror_7 [2, 0, 0, 2, 0, 0, 0] [0, 1, 0, 1, 0, 1, 2] [0, 0, 0, 0, 0, 2, 1] [2, 0, 1, 1, 0, 0, 2] [1, 0, 2, 2, 0, 0, 1] demoR1_2002000 demoR2_2002000 demoC_2002000 demoM_2002000 demoMir_2002000

theorem demoR1_0102000 : invRung 7 5 20 [0, 1, 0, 2, 0, 0, 0] [0, 1, 0, 2, 0, 0, 0] 1 2 false = ([0, 0, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_0102000 : invRung 7 5 20 [0, 1, 0, 2, 0, 0, 0] [0, 0, 2, 1, 2, 1, 0] 3 1 true = ([1, 2, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0102000 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 2, 2] = [0, 0, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_0102000 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 0, 0] [0, 1, 0, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102000 : mirrorTrits [0, 0, 0, 0, 1, 0, 0] = [0, 0, 0, 0, 2, 0, 0] := by
  decide

theorem demoInv_0102000 : specInv 7 5 20 [0, 1, 0, 2, 0, 0, 0] = some [0, 0, 0, 0, 2, 0, 0] :=
  specInv_mirror_7 [0, 1, 0, 2, 0, 0, 0] [0, 0, 2, 1, 2, 1, 0] [1, 2, 1, 0, 2, 2, 2] [0, 0, 0, 0, 1, 0, 0] [0, 0, 0, 0, 2, 0, 0] demoR1_0102000 demoR2_0102000 demoC_0102000 demoM_0102000 demoMir_0102000

theorem demoR1_1102000 : invRung 7 5 20 [1, 1, 0, 2, 0, 0, 0] [1, 1, 0, 2, 0, 0, 0] 1 2 false = ([1, 0, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_1102000 : invRung 7 5 20 [1, 1, 0, 2, 0, 0, 0] [1, 0, 2, 2, 0, 2, 1] 3 1 true = ([0, 2, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_1102000 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 0, 1] = [0, 2, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_1102000 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 2, 1] [1, 1, 0, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102000 : mirrorTrits [0, 2, 2, 1, 1, 2, 1] = [0, 1, 1, 2, 2, 1, 2] := by
  decide

theorem demoInv_1102000 : specInv 7 5 20 [1, 1, 0, 2, 0, 0, 0] = some [0, 1, 1, 2, 2, 1, 2] :=
  specInv_mirror_7 [1, 1, 0, 2, 0, 0, 0] [1, 0, 2, 2, 0, 2, 1] [0, 2, 2, 0, 1, 0, 1] [0, 2, 2, 1, 1, 2, 1] [0, 1, 1, 2, 2, 1, 2] demoR1_1102000 demoR2_1102000 demoC_1102000 demoM_1102000 demoMir_1102000

theorem demoR1_2102000 : invRung 7 5 20 [2, 1, 0, 2, 0, 0, 0] [2, 1, 0, 2, 0, 0, 0] 1 2 false = ([1, 0, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_2102000 : invRung 7 5 20 [2, 1, 0, 2, 0, 0, 0] [1, 0, 0, 0, 2, 1, 2] 3 1 true = ([2, 1, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2102000 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 2, 0] = [2, 2, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_2102000 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 0, 2] [2, 1, 0, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2102000 : mirrorTrits [2, 2, 0, 1, 2, 0, 2] = [1, 1, 0, 2, 1, 0, 1] := by
  decide

theorem demoInv_2102000 : specInv 7 5 20 [2, 1, 0, 2, 0, 0, 0] = some [1, 1, 0, 2, 1, 0, 1] :=
  specInv_mirror_7 [2, 1, 0, 2, 0, 0, 0] [1, 0, 0, 0, 2, 1, 2] [2, 1, 1, 1, 0, 2, 0] [2, 2, 0, 1, 2, 0, 2] [1, 1, 0, 2, 1, 0, 1] demoR1_2102000 demoR2_2102000 demoC_2102000 demoM_2102000 demoMir_2102000

theorem demoR1_0202000 : invRung 7 5 20 [0, 2, 0, 2, 0, 0, 0] [0, 2, 0, 2, 0, 0, 0] 1 2 false = ([2, 2, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0202000 : invRung 7 5 20 [0, 2, 0, 2, 0, 0, 0] [2, 2, 1, 0, 1, 1, 1] 3 1 true = ([2, 0, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_0202000 : fieldCube 7 5 20 [2, 0, 1, 2, 2, 1, 2] = [2, 2, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_0202000 : fieldMul 7 5 20 [2, 2, 1, 1, 0, 1, 1] [0, 2, 0, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0202000 : specInv 7 5 20 [0, 2, 0, 2, 0, 0, 0] = some [2, 2, 1, 1, 0, 1, 1] :=
  specInv_white_7 [0, 2, 0, 2, 0, 0, 0] [2, 2, 1, 0, 1, 1, 1] [2, 0, 1, 2, 2, 1, 2] [2, 2, 1, 1, 0, 1, 1] demoR1_0202000 demoR2_0202000 demoC_0202000 demoM_0202000

theorem demoR1_1202000 : invRung 7 5 20 [1, 2, 0, 2, 0, 0, 0] [1, 2, 0, 2, 0, 0, 0] 1 2 false = ([0, 0, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1202000 : invRung 7 5 20 [1, 2, 0, 2, 0, 0, 0] [0, 0, 2, 2, 0, 1, 2] 3 1 true = ([2, 2, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_1202000 : fieldCube 7 5 20 [2, 2, 2, 0, 1, 1, 2] = [0, 1, 2, 2, 0, 1, 1] := by
  decide

theorem demoM_1202000 : fieldMul 7 5 20 [0, 1, 2, 2, 0, 1, 1] [1, 2, 0, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1202000 : specInv 7 5 20 [1, 2, 0, 2, 0, 0, 0] = some [0, 1, 2, 2, 0, 1, 1] :=
  specInv_white_7 [1, 2, 0, 2, 0, 0, 0] [0, 0, 2, 2, 0, 1, 2] [2, 2, 2, 0, 1, 1, 2] [0, 1, 2, 2, 0, 1, 1] demoR1_1202000 demoR2_1202000 demoC_1202000 demoM_1202000

theorem demoR1_2202000 : invRung 7 5 20 [2, 2, 0, 2, 0, 0, 0] [2, 2, 0, 2, 0, 0, 0] 1 2 false = ([2, 0, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2202000 : invRung 7 5 20 [2, 2, 0, 2, 0, 0, 0] [2, 0, 0, 0, 0, 1, 0] 3 1 true = ([1, 2, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2202000 : fieldCube 7 5 20 [1, 2, 0, 1, 0, 2, 0] = [1, 2, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_2202000 : fieldMul 7 5 20 [1, 2, 0, 2, 2, 0, 1] [2, 2, 0, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2202000 : specInv 7 5 20 [2, 2, 0, 2, 0, 0, 0] = some [1, 2, 0, 2, 2, 0, 1] :=
  specInv_white_7 [2, 2, 0, 2, 0, 0, 0] [2, 0, 0, 0, 0, 1, 0] [1, 2, 0, 1, 0, 2, 0] [1, 2, 0, 2, 2, 0, 1] demoR1_2202000 demoR2_2202000 demoC_2202000 demoM_2202000

theorem demoR1_0012000 : invRung 7 5 20 [0, 0, 1, 2, 0, 0, 0] [0, 0, 1, 2, 0, 0, 0] 1 2 false = ([0, 2, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_0012000 : invRung 7 5 20 [0, 0, 1, 2, 0, 0, 0] [0, 2, 1, 2, 1, 2, 0] 3 1 true = ([1, 0, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0012000 : fieldCube 7 5 20 [1, 0, 1, 0, 2, 2, 2] = [0, 0, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_0012000 : fieldMul 7 5 20 [0, 0, 0, 1, 1, 0, 0] [0, 0, 1, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0012000 : mirrorTrits [0, 0, 0, 1, 1, 0, 0] = [0, 0, 0, 2, 2, 0, 0] := by
  decide

theorem demoInv_0012000 : specInv 7 5 20 [0, 0, 1, 2, 0, 0, 0] = some [0, 0, 0, 2, 2, 0, 0] :=
  specInv_mirror_7 [0, 0, 1, 2, 0, 0, 0] [0, 2, 1, 2, 1, 2, 0] [1, 0, 1, 0, 2, 2, 2] [0, 0, 0, 1, 1, 0, 0] [0, 0, 0, 2, 2, 0, 0] demoR1_0012000 demoR2_0012000 demoC_0012000 demoM_0012000 demoMir_0012000

theorem demoR1_1012000 : invRung 7 5 20 [1, 0, 1, 2, 0, 0, 0] [1, 0, 1, 2, 0, 0, 0] 1 2 false = ([2, 2, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_1012000 : invRung 7 5 20 [1, 0, 1, 2, 0, 0, 0] [2, 2, 1, 2, 2, 0, 1] 3 1 true = ([0, 0, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1012000 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 1, 0] = [2, 0, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_1012000 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 1, 1] [1, 0, 1, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1012000 : specInv 7 5 20 [1, 0, 1, 2, 0, 0, 0] = some [2, 0, 2, 2, 1, 1, 1] :=
  specInv_white_7 [1, 0, 1, 2, 0, 0, 0] [2, 2, 1, 2, 2, 0, 1] [0, 0, 0, 1, 2, 1, 0] [2, 0, 2, 2, 1, 1, 1] demoR1_1012000 demoR2_1012000 demoC_1012000 demoM_1012000

theorem demoR1_2012000 : invRung 7 5 20 [2, 0, 1, 2, 0, 0, 0] [2, 0, 1, 2, 0, 0, 0] 1 2 false = ([1, 2, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_2012000 : invRung 7 5 20 [2, 0, 1, 2, 0, 0, 0] [1, 2, 0, 2, 0, 2, 0] 3 1 true = ([2, 2, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_2012000 : fieldCube 7 5 20 [2, 2, 1, 2, 0, 2, 2] = [0, 1, 2, 1, 1, 0, 1] := by
  decide

theorem demoM_2012000 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 0, 1] [2, 0, 1, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2012000 : specInv 7 5 20 [2, 0, 1, 2, 0, 0, 0] = some [0, 1, 2, 1, 1, 0, 1] :=
  specInv_white_7 [2, 0, 1, 2, 0, 0, 0] [1, 2, 0, 2, 0, 2, 0] [2, 2, 1, 2, 0, 2, 2] [0, 1, 2, 1, 1, 0, 1] demoR1_2012000 demoR2_2012000 demoC_2012000 demoM_2012000

theorem demoR1_0112000 : invRung 7 5 20 [0, 1, 1, 2, 0, 0, 0] [0, 1, 1, 2, 0, 0, 0] 1 2 false = ([0, 2, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_0112000 : invRung 7 5 20 [0, 1, 1, 2, 0, 0, 0] [0, 2, 1, 2, 1, 1, 0] 3 1 true = ([2, 2, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_0112000 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 0, 1] = [1, 0, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_0112000 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 2, 1] [0, 1, 1, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0112000 : specInv 7 5 20 [0, 1, 1, 2, 0, 0, 0] = some [1, 0, 1, 2, 1, 2, 1] :=
  specInv_white_7 [0, 1, 1, 2, 0, 0, 0] [0, 2, 1, 2, 1, 1, 0] [2, 2, 1, 2, 2, 0, 1] [1, 0, 1, 2, 1, 2, 1] demoR1_0112000 demoR2_0112000 demoC_0112000 demoM_0112000

theorem demoR1_1112000 : invRung 7 5 20 [1, 1, 1, 2, 0, 0, 0] [1, 1, 1, 2, 0, 0, 0] 1 2 false = ([2, 1, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_1112000 : invRung 7 5 20 [1, 1, 1, 2, 0, 0, 0] [2, 1, 0, 1, 2, 0, 2] 3 1 true = ([2, 2, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_1112000 : fieldCube 7 5 20 [2, 2, 1, 1, 0, 0, 0] = [0, 0, 1, 2, 0, 1, 1] := by
  decide

theorem demoM_1112000 : fieldMul 7 5 20 [0, 0, 1, 2, 0, 1, 1] [1, 1, 1, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1112000 : specInv 7 5 20 [1, 1, 1, 2, 0, 0, 0] = some [0, 0, 1, 2, 0, 1, 1] :=
  specInv_white_7 [1, 1, 1, 2, 0, 0, 0] [2, 1, 0, 1, 2, 0, 2] [2, 2, 1, 1, 0, 0, 0] [0, 0, 1, 2, 0, 1, 1] demoR1_1112000 demoR2_1112000 demoC_1112000 demoM_1112000

theorem demoR1_2112000 : invRung 7 5 20 [2, 1, 1, 2, 0, 0, 0] [2, 1, 1, 2, 0, 0, 0] 1 2 false = ([0, 2, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_2112000 : invRung 7 5 20 [2, 1, 1, 2, 0, 0, 0] [0, 2, 0, 2, 0, 2, 2] 3 1 true = ([0, 1, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2112000 : fieldCube 7 5 20 [0, 1, 2, 0, 0, 1, 0] = [1, 1, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_2112000 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 1, 1] [2, 1, 1, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112000 : mirrorTrits [1, 1, 1, 1, 1, 1, 1] = [2, 2, 2, 2, 2, 2, 2] := by
  decide

theorem demoInv_2112000 : specInv 7 5 20 [2, 1, 1, 2, 0, 0, 0] = some [2, 2, 2, 2, 2, 2, 2] :=
  specInv_mirror_7 [2, 1, 1, 2, 0, 0, 0] [0, 2, 0, 2, 0, 2, 2] [0, 1, 2, 0, 0, 1, 0] [1, 1, 1, 1, 1, 1, 1] [2, 2, 2, 2, 2, 2, 2] demoR1_2112000 demoR2_2112000 demoC_2112000 demoM_2112000 demoMir_2112000

theorem demoR1_0212000 : invRung 7 5 20 [0, 2, 1, 2, 0, 0, 0] [0, 2, 1, 2, 0, 0, 0] 1 2 false = ([1, 0, 2, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_0212000 : invRung 7 5 20 [0, 2, 1, 2, 0, 0, 0] [1, 0, 2, 1, 2, 0, 2] 3 1 true = ([0, 1, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0212000 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 1, 0] = [2, 1, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_0212000 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 2, 1] [0, 2, 1, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212000 : mirrorTrits [2, 1, 2, 1, 1, 2, 1] = [1, 2, 1, 2, 2, 1, 2] := by
  decide

theorem demoInv_0212000 : specInv 7 5 20 [0, 2, 1, 2, 0, 0, 0] = some [1, 2, 1, 2, 2, 1, 2] :=
  specInv_mirror_7 [0, 2, 1, 2, 0, 0, 0] [1, 0, 2, 1, 2, 0, 2] [0, 1, 2, 1, 0, 1, 0] [2, 1, 2, 1, 1, 2, 1] [1, 2, 1, 2, 2, 1, 2] demoR1_0212000 demoR2_0212000 demoC_0212000 demoM_0212000 demoMir_0212000

theorem demoR1_1212000 : invRung 7 5 20 [1, 2, 1, 2, 0, 0, 0] [1, 2, 1, 2, 0, 0, 0] 1 2 false = ([0, 2, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_1212000 : invRung 7 5 20 [1, 2, 1, 2, 0, 0, 0] [0, 2, 0, 0, 2, 2, 0] 3 1 true = ([0, 1, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_1212000 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 1, 1] = [2, 0, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_1212000 : fieldMul 7 5 20 [2, 0, 1, 0, 2, 1, 0] [1, 2, 1, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1212000 : specInv 7 5 20 [1, 2, 1, 2, 0, 0, 0] = some [2, 0, 1, 0, 2, 1, 0] :=
  specInv_white_7 [1, 2, 1, 2, 0, 0, 0] [0, 2, 0, 0, 2, 2, 0] [0, 1, 2, 1, 1, 1, 1] [2, 0, 1, 0, 2, 1, 0] demoR1_1212000 demoR2_1212000 demoC_1212000 demoM_1212000

theorem demoR1_2212000 : invRung 7 5 20 [2, 2, 1, 2, 0, 0, 0] [2, 2, 1, 2, 0, 0, 0] 1 2 false = ([0, 2, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2212000 : invRung 7 5 20 [2, 2, 1, 2, 0, 0, 0] [0, 2, 1, 0, 2, 0, 2] 3 1 true = ([0, 0, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_2212000 : fieldCube 7 5 20 [0, 0, 1, 1, 2, 2, 1] = [0, 2, 2, 0, 0, 0, 2] := by
  decide

theorem demoM_2212000 : fieldMul 7 5 20 [0, 2, 2, 0, 0, 0, 2] [2, 2, 1, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212000 : mirrorTrits [0, 2, 2, 0, 0, 0, 2] = [0, 1, 1, 0, 0, 0, 1] := by
  decide

theorem demoInv_2212000 : specInv 7 5 20 [2, 2, 1, 2, 0, 0, 0] = some [0, 1, 1, 0, 0, 0, 1] :=
  specInv_mirror_7 [2, 2, 1, 2, 0, 0, 0] [0, 2, 1, 0, 2, 0, 2] [0, 0, 1, 1, 2, 2, 1] [0, 2, 2, 0, 0, 0, 2] [0, 1, 1, 0, 0, 0, 1] demoR1_2212000 demoR2_2212000 demoC_2212000 demoM_2212000 demoMir_2212000

theorem demoR1_0022000 : invRung 7 5 20 [0, 0, 2, 2, 0, 0, 0] [0, 0, 2, 2, 0, 0, 0] 1 2 false = ([1, 0, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_0022000 : invRung 7 5 20 [0, 0, 2, 2, 0, 0, 0] [1, 0, 1, 0, 1, 0, 2] 3 1 true = ([1, 1, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0022000 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 2, 2] = [0, 0, 0, 2, 1, 0, 0] := by
  decide

theorem demoM_0022000 : fieldMul 7 5 20 [0, 0, 0, 2, 1, 0, 0] [0, 0, 2, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022000 : mirrorTrits [0, 0, 0, 2, 1, 0, 0] = [0, 0, 0, 1, 2, 0, 0] := by
  decide

theorem demoInv_0022000 : specInv 7 5 20 [0, 0, 2, 2, 0, 0, 0] = some [0, 0, 0, 1, 2, 0, 0] :=
  specInv_mirror_7 [0, 0, 2, 2, 0, 0, 0] [1, 0, 1, 0, 1, 0, 2] [1, 1, 1, 0, 2, 2, 2] [0, 0, 0, 2, 1, 0, 0] [0, 0, 0, 1, 2, 0, 0] demoR1_0022000 demoR2_0022000 demoC_0022000 demoM_0022000 demoMir_0022000

theorem demoR1_1022000 : invRung 7 5 20 [1, 0, 2, 2, 0, 0, 0] [1, 0, 2, 2, 0, 0, 0] 1 2 false = ([0, 0, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_1022000 : invRung 7 5 20 [1, 0, 2, 2, 0, 0, 0] [0, 0, 0, 2, 1, 1, 1] 3 1 true = ([2, 0, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_1022000 : fieldCube 7 5 20 [2, 0, 2, 1, 1, 0, 2] = [0, 0, 2, 0, 2, 1, 2] := by
  decide

theorem demoM_1022000 : fieldMul 7 5 20 [0, 0, 2, 0, 2, 1, 2] [1, 0, 2, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1022000 : specInv 7 5 20 [1, 0, 2, 2, 0, 0, 0] = some [0, 0, 2, 0, 2, 1, 2] :=
  specInv_white_7 [1, 0, 2, 2, 0, 0, 0] [0, 0, 0, 2, 1, 1, 1] [2, 0, 2, 1, 1, 0, 2] [0, 0, 2, 0, 2, 1, 2] demoR1_1022000 demoR2_1022000 demoC_1022000 demoM_1022000

theorem demoR1_2022000 : invRung 7 5 20 [2, 0, 2, 2, 0, 0, 0] [2, 0, 2, 2, 0, 0, 0] 1 2 false = ([2, 2, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_2022000 : invRung 7 5 20 [2, 0, 2, 2, 0, 0, 0] [2, 2, 1, 0, 0, 2, 2] 3 1 true = ([2, 1, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_2022000 : fieldCube 7 5 20 [2, 1, 0, 1, 0, 2, 2] = [2, 1, 1, 0, 1, 2, 0] := by
  decide

theorem demoM_2022000 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 2, 0] [2, 0, 2, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2022000 : specInv 7 5 20 [2, 0, 2, 2, 0, 0, 0] = some [2, 1, 1, 0, 1, 2, 0] :=
  specInv_white_7 [2, 0, 2, 2, 0, 0, 0] [2, 2, 1, 0, 0, 2, 2] [2, 1, 0, 1, 0, 2, 2] [2, 1, 1, 0, 1, 2, 0] demoR1_2022000 demoR2_2022000 demoC_2022000 demoM_2022000

theorem demoR1_0122000 : invRung 7 5 20 [0, 1, 2, 2, 0, 0, 0] [0, 1, 2, 2, 0, 0, 0] 1 2 false = ([2, 2, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_0122000 : invRung 7 5 20 [0, 1, 2, 2, 0, 0, 0] [2, 2, 1, 2, 2, 2, 2] 3 1 true = ([0, 0, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_0122000 : fieldCube 7 5 20 [0, 0, 2, 0, 2, 2, 1] = [2, 2, 1, 0, 0, 2, 0] := by
  decide

theorem demoM_0122000 : fieldMul 7 5 20 [2, 2, 1, 0, 0, 2, 0] [0, 1, 2, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0122000 : specInv 7 5 20 [0, 1, 2, 2, 0, 0, 0] = some [2, 2, 1, 0, 0, 2, 0] :=
  specInv_white_7 [0, 1, 2, 2, 0, 0, 0] [2, 2, 1, 2, 2, 2, 2] [0, 0, 2, 0, 2, 2, 1] [2, 2, 1, 0, 0, 2, 0] demoR1_0122000 demoR2_0122000 demoC_0122000 demoM_0122000

theorem demoR1_1122000 : invRung 7 5 20 [1, 1, 2, 2, 0, 0, 0] [1, 1, 2, 2, 0, 0, 0] 1 2 false = ([1, 0, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_1122000 : invRung 7 5 20 [1, 1, 2, 2, 0, 0, 0] [1, 0, 0, 2, 0, 2, 1] 3 1 true = ([2, 0, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_1122000 : fieldCube 7 5 20 [2, 0, 0, 2, 1, 0, 1] = [1, 2, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_1122000 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 1, 2] [1, 1, 2, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122000 : mirrorTrits [1, 2, 1, 2, 1, 1, 2] = [2, 1, 2, 1, 2, 2, 1] := by
  decide

theorem demoInv_1122000 : specInv 7 5 20 [1, 1, 2, 2, 0, 0, 0] = some [2, 1, 2, 1, 2, 2, 1] :=
  specInv_mirror_7 [1, 1, 2, 2, 0, 0, 0] [1, 0, 0, 2, 0, 2, 1] [2, 0, 0, 2, 1, 0, 1] [1, 2, 1, 2, 1, 1, 2] [2, 1, 2, 1, 2, 2, 1] demoR1_1122000 demoR2_1122000 demoC_1122000 demoM_1122000 demoMir_1122000

theorem demoR1_2122000 : invRung 7 5 20 [2, 1, 2, 2, 0, 0, 0] [2, 1, 2, 2, 0, 0, 0] 1 2 false = ([2, 2, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_2122000 : invRung 7 5 20 [2, 1, 2, 2, 0, 0, 0] [2, 2, 0, 0, 0, 1, 2] 3 1 true = ([1, 1, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2122000 : fieldCube 7 5 20 [1, 1, 1, 1, 0, 1, 1] = [0, 2, 1, 2, 2, 0, 1] := by
  decide

theorem demoM_2122000 : fieldMul 7 5 20 [0, 2, 1, 2, 2, 0, 1] [2, 1, 2, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2122000 : specInv 7 5 20 [2, 1, 2, 2, 0, 0, 0] = some [0, 2, 1, 2, 2, 0, 1] :=
  specInv_white_7 [2, 1, 2, 2, 0, 0, 0] [2, 2, 0, 0, 0, 1, 2] [1, 1, 1, 1, 0, 1, 1] [0, 2, 1, 2, 2, 0, 1] demoR1_2122000 demoR2_2122000 demoC_2122000 demoM_2122000

theorem demoR1_0222000 : invRung 7 5 20 [0, 2, 2, 2, 0, 0, 0] [0, 2, 2, 2, 0, 0, 0] 1 2 false = ([2, 1, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0222000 : invRung 7 5 20 [0, 2, 2, 2, 0, 0, 0] [2, 1, 0, 0, 1, 2, 1] 3 1 true = ([2, 0, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0222000 : fieldCube 7 5 20 [2, 0, 0, 0, 1, 0, 1] = [2, 2, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_0222000 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 2, 2] [0, 2, 2, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222000 : mirrorTrits [2, 2, 2, 2, 1, 2, 2] = [1, 1, 1, 1, 2, 1, 1] := by
  decide

theorem demoInv_0222000 : specInv 7 5 20 [0, 2, 2, 2, 0, 0, 0] = some [1, 1, 1, 1, 2, 1, 1] :=
  specInv_mirror_7 [0, 2, 2, 2, 0, 0, 0] [2, 1, 0, 0, 1, 2, 1] [2, 0, 0, 0, 1, 0, 1] [2, 2, 2, 2, 1, 2, 2] [1, 1, 1, 1, 2, 1, 1] demoR1_0222000 demoR2_0222000 demoC_0222000 demoM_0222000 demoMir_0222000

theorem demoR1_1222000 : invRung 7 5 20 [1, 2, 2, 2, 0, 0, 0] [1, 2, 2, 2, 0, 0, 0] 1 2 false = ([1, 1, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_1222000 : invRung 7 5 20 [1, 2, 2, 2, 0, 0, 0] [1, 1, 2, 2, 2, 0, 1] 3 1 true = ([1, 0, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_1222000 : fieldCube 7 5 20 [1, 0, 2, 2, 0, 1, 2] = [1, 0, 1, 2, 0, 2, 0] := by
  decide

theorem demoM_1222000 : fieldMul 7 5 20 [1, 0, 1, 2, 0, 2, 0] [1, 2, 2, 2, 0, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222000 : mirrorTrits [1, 0, 1, 2, 0, 2, 0] = [2, 0, 2, 1, 0, 1, 0] := by
  decide

theorem demoInv_1222000 : specInv 7 5 20 [1, 2, 2, 2, 0, 0, 0] = some [2, 0, 2, 1, 0, 1, 0] :=
  specInv_mirror_7 [1, 2, 2, 2, 0, 0, 0] [1, 1, 2, 2, 2, 0, 1] [1, 0, 2, 2, 0, 1, 2] [1, 0, 1, 2, 0, 2, 0] [2, 0, 2, 1, 0, 1, 0] demoR1_1222000 demoR2_1222000 demoC_1222000 demoM_1222000 demoMir_1222000

theorem demoR1_2222000 : invRung 7 5 20 [2, 2, 2, 2, 0, 0, 0] [2, 2, 2, 2, 0, 0, 0] 1 2 false = ([1, 1, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_2222000 : invRung 7 5 20 [2, 2, 2, 2, 0, 0, 0] [1, 1, 1, 1, 2, 2, 0] 3 1 true = ([1, 0, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_2222000 : fieldCube 7 5 20 [1, 0, 1, 1, 2, 1, 2] = [0, 2, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_2222000 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 0, 1] [2, 2, 2, 2, 0, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2222000 : specInv 7 5 20 [2, 2, 2, 2, 0, 0, 0] = some [0, 2, 0, 1, 0, 0, 1] :=
  specInv_white_7 [2, 2, 2, 2, 0, 0, 0] [1, 1, 1, 1, 2, 2, 0] [1, 0, 1, 1, 2, 1, 2] [0, 2, 0, 1, 0, 0, 1] demoR1_2222000 demoR2_2222000 demoC_2222000 demoM_2222000

theorem demoR1_0000100 : invRung 7 5 20 [0, 0, 0, 0, 1, 0, 0] [0, 0, 0, 0, 1, 0, 0] 1 2 false = ([1, 0, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_0000100 : invRung 7 5 20 [0, 0, 0, 0, 1, 0, 0] [1, 0, 2, 2, 0, 2, 0] 3 1 true = ([1, 0, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0000100 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 1, 2] = [0, 2, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_0000100 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 0, 0] [0, 0, 0, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0000100 : specInv 7 5 20 [0, 0, 0, 0, 1, 0, 0] = some [0, 2, 0, 1, 0, 0, 0] :=
  specInv_white_7 [0, 0, 0, 0, 1, 0, 0] [1, 0, 2, 2, 0, 2, 0] [1, 0, 0, 1, 2, 1, 2] [0, 2, 0, 1, 0, 0, 0] demoR1_0000100 demoR2_0000100 demoC_0000100 demoM_0000100

theorem demoR1_1000100 : invRung 7 5 20 [1, 0, 0, 0, 1, 0, 0] [1, 0, 0, 0, 1, 0, 0] 1 2 false = ([2, 1, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1000100 : invRung 7 5 20 [1, 0, 0, 0, 1, 0, 0] [2, 1, 1, 2, 0, 0, 1] 3 1 true = ([2, 2, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1000100 : fieldCube 7 5 20 [2, 2, 2, 2, 0, 1, 0] = [2, 1, 0, 2, 1, 0, 1] := by
  decide

theorem demoM_1000100 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 0, 1] [1, 0, 0, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1000100 : specInv 7 5 20 [1, 0, 0, 0, 1, 0, 0] = some [2, 1, 0, 2, 1, 0, 1] :=
  specInv_white_7 [1, 0, 0, 0, 1, 0, 0] [2, 1, 1, 2, 0, 0, 1] [2, 2, 2, 2, 0, 1, 0] [2, 1, 0, 2, 1, 0, 1] demoR1_1000100 demoR2_1000100 demoC_1000100 demoM_1000100

theorem demoR1_2000100 : invRung 7 5 20 [2, 0, 0, 0, 1, 0, 0] [2, 0, 0, 0, 1, 0, 0] 1 2 false = ([1, 2, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_2000100 : invRung 7 5 20 [2, 0, 0, 0, 1, 0, 0] [1, 2, 2, 2, 0, 0, 1] 3 1 true = ([1, 2, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_2000100 : fieldCube 7 5 20 [1, 2, 2, 0, 1, 0, 1] = [1, 2, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_2000100 : fieldMul 7 5 20 [1, 2, 2, 1, 1, 2, 1] [2, 0, 0, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000100 : mirrorTrits [1, 2, 2, 1, 1, 2, 1] = [2, 1, 1, 2, 2, 1, 2] := by
  decide

theorem demoInv_2000100 : specInv 7 5 20 [2, 0, 0, 0, 1, 0, 0] = some [2, 1, 1, 2, 2, 1, 2] :=
  specInv_mirror_7 [2, 0, 0, 0, 1, 0, 0] [1, 2, 2, 2, 0, 0, 1] [1, 2, 2, 0, 1, 0, 1] [1, 2, 2, 1, 1, 2, 1] [2, 1, 1, 2, 2, 1, 2] demoR1_2000100 demoR2_2000100 demoC_2000100 demoM_2000100 demoMir_2000100

theorem demoR1_0100100 : invRung 7 5 20 [0, 1, 0, 0, 1, 0, 0] [0, 1, 0, 0, 1, 0, 0] 1 2 false = ([1, 0, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_0100100 : invRung 7 5 20 [0, 1, 0, 0, 1, 0, 0] [1, 0, 1, 2, 0, 2, 1] 3 1 true = ([0, 1, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_0100100 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 2, 2] = [0, 1, 1, 0, 1, 2, 2] := by
  decide

theorem demoM_0100100 : fieldMul 7 5 20 [0, 1, 1, 0, 1, 2, 2] [0, 1, 0, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0100100 : specInv 7 5 20 [0, 1, 0, 0, 1, 0, 0] = some [0, 1, 1, 0, 1, 2, 2] :=
  specInv_white_7 [0, 1, 0, 0, 1, 0, 0] [1, 0, 1, 2, 0, 2, 1] [0, 1, 2, 1, 0, 2, 2] [0, 1, 1, 0, 1, 2, 2] demoR1_0100100 demoR2_0100100 demoC_0100100 demoM_0100100

theorem demoR1_1100100 : invRung 7 5 20 [1, 1, 0, 0, 1, 0, 0] [1, 1, 0, 0, 1, 0, 0] 1 2 false = ([1, 1, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_1100100 : invRung 7 5 20 [1, 1, 0, 0, 1, 0, 0] [1, 1, 0, 2, 2, 2, 1] 3 1 true = ([0, 1, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1100100 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 1, 1] = [2, 2, 1, 2, 2, 0, 0] := by
  decide

theorem demoM_1100100 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 0, 0] [1, 1, 0, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1100100 : specInv 7 5 20 [1, 1, 0, 0, 1, 0, 0] = some [2, 2, 1, 2, 2, 0, 0] :=
  specInv_white_7 [1, 1, 0, 0, 1, 0, 0] [1, 1, 0, 2, 2, 2, 1] [0, 1, 0, 1, 0, 1, 1] [2, 2, 1, 2, 2, 0, 0] demoR1_1100100 demoR2_1100100 demoC_1100100 demoM_1100100

theorem demoR1_2100100 : invRung 7 5 20 [2, 1, 0, 0, 1, 0, 0] [2, 1, 0, 0, 1, 0, 0] 1 2 false = ([1, 1, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_2100100 : invRung 7 5 20 [2, 1, 0, 0, 1, 0, 0] [1, 1, 0, 1, 1, 0, 0] 3 1 true = ([0, 1, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_2100100 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 2, 1] = [2, 2, 1, 1, 0, 2, 0] := by
  decide

theorem demoM_2100100 : fieldMul 7 5 20 [2, 2, 1, 1, 0, 2, 0] [2, 1, 0, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2100100 : specInv 7 5 20 [2, 1, 0, 0, 1, 0, 0] = some [2, 2, 1, 1, 0, 2, 0] :=
  specInv_white_7 [2, 1, 0, 0, 1, 0, 0] [1, 1, 0, 1, 1, 0, 0] [0, 1, 2, 0, 2, 2, 1] [2, 2, 1, 1, 0, 2, 0] demoR1_2100100 demoR2_2100100 demoC_2100100 demoM_2100100

theorem demoR1_0200100 : invRung 7 5 20 [0, 2, 0, 0, 1, 0, 0] [0, 2, 0, 0, 1, 0, 0] 1 2 false = ([1, 1, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_0200100 : invRung 7 5 20 [0, 2, 0, 0, 1, 0, 0] [1, 1, 1, 0, 1, 1, 0] 3 1 true = ([1, 0, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0200100 : fieldCube 7 5 20 [1, 0, 0, 0, 2, 1, 0] = [2, 0, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_0200100 : fieldMul 7 5 20 [2, 0, 1, 2, 1, 0, 1] [0, 2, 0, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0200100 : specInv 7 5 20 [0, 2, 0, 0, 1, 0, 0] = some [2, 0, 1, 2, 1, 0, 1] :=
  specInv_white_7 [0, 2, 0, 0, 1, 0, 0] [1, 1, 1, 0, 1, 1, 0] [1, 0, 0, 0, 2, 1, 0] [2, 0, 1, 2, 1, 0, 1] demoR1_0200100 demoR2_0200100 demoC_0200100 demoM_0200100

theorem demoR1_1200100 : invRung 7 5 20 [1, 2, 0, 0, 1, 0, 0] [1, 2, 0, 0, 1, 0, 0] 1 2 false = ([0, 0, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_1200100 : invRung 7 5 20 [1, 2, 0, 0, 1, 0, 0] [0, 0, 0, 1, 1, 2, 0] 3 1 true = ([2, 1, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_1200100 : fieldCube 7 5 20 [2, 1, 1, 2, 0, 0, 1] = [1, 1, 1, 2, 1, 0, 2] := by
  decide

theorem demoM_1200100 : fieldMul 7 5 20 [1, 1, 1, 2, 1, 0, 2] [1, 2, 0, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1200100 : specInv 7 5 20 [1, 2, 0, 0, 1, 0, 0] = some [1, 1, 1, 2, 1, 0, 2] :=
  specInv_white_7 [1, 2, 0, 0, 1, 0, 0] [0, 0, 0, 1, 1, 2, 0] [2, 1, 1, 2, 0, 0, 1] [1, 1, 1, 2, 1, 0, 2] demoR1_1200100 demoR2_1200100 demoC_1200100 demoM_1200100

theorem demoR1_2200100 : invRung 7 5 20 [2, 2, 0, 0, 1, 0, 0] [2, 2, 0, 0, 1, 0, 0] 1 2 false = ([1, 0, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_2200100 : invRung 7 5 20 [2, 2, 0, 0, 1, 0, 0] [1, 0, 2, 0, 1, 0, 2] 3 1 true = ([1, 1, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_2200100 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 0, 0] = [1, 0, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_2200100 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 0, 1] [2, 2, 0, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200100 : mirrorTrits [1, 0, 0, 1, 0, 0, 1] = [2, 0, 0, 2, 0, 0, 2] := by
  decide

theorem demoInv_2200100 : specInv 7 5 20 [2, 2, 0, 0, 1, 0, 0] = some [2, 0, 0, 2, 0, 0, 2] :=
  specInv_mirror_7 [2, 2, 0, 0, 1, 0, 0] [1, 0, 2, 0, 1, 0, 2] [1, 1, 1, 0, 0, 0, 0] [1, 0, 0, 1, 0, 0, 1] [2, 0, 0, 2, 0, 0, 2] demoR1_2200100 demoR2_2200100 demoC_2200100 demoM_2200100 demoMir_2200100

theorem demoR1_0010100 : invRung 7 5 20 [0, 0, 1, 0, 1, 0, 0] [0, 0, 1, 0, 1, 0, 0] 1 2 false = ([2, 0, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_0010100 : invRung 7 5 20 [0, 0, 1, 0, 1, 0, 0] [2, 0, 2, 0, 0, 1, 1] 3 1 true = ([2, 2, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_0010100 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 0, 2] = [2, 1, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_0010100 : fieldMul 7 5 20 [2, 1, 1, 0, 2, 1, 2] [0, 0, 1, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010100 : mirrorTrits [2, 1, 1, 0, 2, 1, 2] = [1, 2, 2, 0, 1, 2, 1] := by
  decide

theorem demoInv_0010100 : specInv 7 5 20 [0, 0, 1, 0, 1, 0, 0] = some [1, 2, 2, 0, 1, 2, 1] :=
  specInv_mirror_7 [0, 0, 1, 0, 1, 0, 0] [2, 0, 2, 0, 0, 1, 1] [2, 2, 1, 0, 2, 0, 2] [2, 1, 1, 0, 2, 1, 2] [1, 2, 2, 0, 1, 2, 1] demoR1_0010100 demoR2_0010100 demoC_0010100 demoM_0010100 demoMir_0010100

theorem demoR1_1010100 : invRung 7 5 20 [1, 0, 1, 0, 1, 0, 0] [1, 0, 1, 0, 1, 0, 0] 1 2 false = ([0, 1, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_1010100 : invRung 7 5 20 [1, 0, 1, 0, 1, 0, 0] [0, 1, 2, 1, 0, 1, 1] 3 1 true = ([2, 2, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_1010100 : fieldCube 7 5 20 [2, 2, 1, 2, 1, 2, 1] = [0, 1, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_1010100 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 0, 1] [1, 0, 1, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1010100 : specInv 7 5 20 [1, 0, 1, 0, 1, 0, 0] = some [0, 1, 0, 1, 0, 0, 1] :=
  specInv_white_7 [1, 0, 1, 0, 1, 0, 0] [0, 1, 2, 1, 0, 1, 1] [2, 2, 1, 2, 1, 2, 1] [0, 1, 0, 1, 0, 0, 1] demoR1_1010100 demoR2_1010100 demoC_1010100 demoM_1010100

theorem demoR1_2010100 : invRung 7 5 20 [2, 0, 1, 0, 1, 0, 0] [2, 0, 1, 0, 1, 0, 0] 1 2 false = ([2, 1, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_2010100 : invRung 7 5 20 [2, 0, 1, 0, 1, 0, 0] [2, 1, 1, 1, 2, 2, 1] 3 1 true = ([2, 1, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_2010100 : fieldCube 7 5 20 [2, 1, 2, 2, 2, 0, 0] = [1, 2, 2, 0, 0, 1, 1] := by
  decide

theorem demoM_2010100 : fieldMul 7 5 20 [1, 2, 2, 0, 0, 1, 1] [2, 0, 1, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2010100 : specInv 7 5 20 [2, 0, 1, 0, 1, 0, 0] = some [1, 2, 2, 0, 0, 1, 1] :=
  specInv_white_7 [2, 0, 1, 0, 1, 0, 0] [2, 1, 1, 1, 2, 2, 1] [2, 1, 2, 2, 2, 0, 0] [1, 2, 2, 0, 0, 1, 1] demoR1_2010100 demoR2_2010100 demoC_2010100 demoM_2010100

theorem demoR1_0110100 : invRung 7 5 20 [0, 1, 1, 0, 1, 0, 0] [0, 1, 1, 0, 1, 0, 0] 1 2 false = ([1, 2, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0110100 : invRung 7 5 20 [0, 1, 1, 0, 1, 0, 0] [1, 2, 2, 2, 0, 0, 0] 3 1 true = ([1, 2, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_0110100 : fieldCube 7 5 20 [1, 2, 1, 1, 1, 0, 2] = [2, 0, 2, 2, 2, 1, 1] := by
  decide

theorem demoM_0110100 : fieldMul 7 5 20 [2, 0, 2, 2, 2, 1, 1] [0, 1, 1, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110100 : mirrorTrits [2, 0, 2, 2, 2, 1, 1] = [1, 0, 1, 1, 1, 2, 2] := by
  decide

theorem demoInv_0110100 : specInv 7 5 20 [0, 1, 1, 0, 1, 0, 0] = some [1, 0, 1, 1, 1, 2, 2] :=
  specInv_mirror_7 [0, 1, 1, 0, 1, 0, 0] [1, 2, 2, 2, 0, 0, 0] [1, 2, 1, 1, 1, 0, 2] [2, 0, 2, 2, 2, 1, 1] [1, 0, 1, 1, 1, 2, 2] demoR1_0110100 demoR2_0110100 demoC_0110100 demoM_0110100 demoMir_0110100

theorem demoR1_1110100 : invRung 7 5 20 [1, 1, 1, 0, 1, 0, 0] [1, 1, 1, 0, 1, 0, 0] 1 2 false = ([1, 2, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1110100 : invRung 7 5 20 [1, 1, 1, 0, 1, 0, 0] [1, 2, 0, 2, 0, 0, 1] 3 1 true = ([1, 0, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_1110100 : fieldCube 7 5 20 [1, 0, 1, 2, 2, 2, 2] = [2, 0, 2, 1, 1, 2, 0] := by
  decide

theorem demoM_1110100 : fieldMul 7 5 20 [2, 0, 2, 1, 1, 2, 0] [1, 1, 1, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1110100 : specInv 7 5 20 [1, 1, 1, 0, 1, 0, 0] = some [2, 0, 2, 1, 1, 2, 0] :=
  specInv_white_7 [1, 1, 1, 0, 1, 0, 0] [1, 2, 0, 2, 0, 0, 1] [1, 0, 1, 2, 2, 2, 2] [2, 0, 2, 1, 1, 2, 0] demoR1_1110100 demoR2_1110100 demoC_1110100 demoM_1110100

theorem demoR1_2110100 : invRung 7 5 20 [2, 1, 1, 0, 1, 0, 0] [2, 1, 1, 0, 1, 0, 0] 1 2 false = ([1, 0, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2110100 : invRung 7 5 20 [2, 1, 1, 0, 1, 0, 0] [1, 0, 2, 0, 2, 0, 2] 3 1 true = ([0, 2, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_2110100 : fieldCube 7 5 20 [0, 2, 2, 0, 2, 1, 2] = [1, 2, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_2110100 : fieldMul 7 5 20 [1, 2, 2, 0, 0, 2, 2] [2, 1, 1, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110100 : mirrorTrits [1, 2, 2, 0, 0, 2, 2] = [2, 1, 1, 0, 0, 1, 1] := by
  decide

theorem demoInv_2110100 : specInv 7 5 20 [2, 1, 1, 0, 1, 0, 0] = some [2, 1, 1, 0, 0, 1, 1] :=
  specInv_mirror_7 [2, 1, 1, 0, 1, 0, 0] [1, 0, 2, 0, 2, 0, 2] [0, 2, 2, 0, 2, 1, 2] [1, 2, 2, 0, 0, 2, 2] [2, 1, 1, 0, 0, 1, 1] demoR1_2110100 demoR2_2110100 demoC_2110100 demoM_2110100 demoMir_2110100

theorem demoR1_0210100 : invRung 7 5 20 [0, 2, 1, 0, 1, 0, 0] [0, 2, 1, 0, 1, 0, 0] 1 2 false = ([1, 1, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_0210100 : invRung 7 5 20 [0, 2, 1, 0, 1, 0, 0] [1, 1, 1, 2, 1, 2, 0] 3 1 true = ([0, 0, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_0210100 : fieldCube 7 5 20 [0, 0, 2, 2, 1, 2, 2] = [1, 2, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_0210100 : fieldMul 7 5 20 [1, 2, 2, 0, 1, 1, 0] [0, 2, 1, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210100 : mirrorTrits [1, 2, 2, 0, 1, 1, 0] = [2, 1, 1, 0, 2, 2, 0] := by
  decide

theorem demoInv_0210100 : specInv 7 5 20 [0, 2, 1, 0, 1, 0, 0] = some [2, 1, 1, 0, 2, 2, 0] :=
  specInv_mirror_7 [0, 2, 1, 0, 1, 0, 0] [1, 1, 1, 2, 1, 2, 0] [0, 0, 2, 2, 1, 2, 2] [1, 2, 2, 0, 1, 1, 0] [2, 1, 1, 0, 2, 2, 0] demoR1_0210100 demoR2_0210100 demoC_0210100 demoM_0210100 demoMir_0210100

theorem demoR1_1210100 : invRung 7 5 20 [1, 2, 1, 0, 1, 0, 0] [1, 2, 1, 0, 1, 0, 0] 1 2 false = ([0, 1, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_1210100 : invRung 7 5 20 [1, 2, 1, 0, 1, 0, 0] [0, 1, 0, 2, 0, 1, 0] 3 1 true = ([2, 2, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_1210100 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 1, 1] = [0, 1, 0, 2, 2, 1, 0] := by
  decide

theorem demoM_1210100 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 1, 0] [1, 2, 1, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1210100 : specInv 7 5 20 [1, 2, 1, 0, 1, 0, 0] = some [0, 1, 0, 2, 2, 1, 0] :=
  specInv_white_7 [1, 2, 1, 0, 1, 0, 0] [0, 1, 0, 2, 0, 1, 0] [2, 2, 1, 0, 2, 1, 1] [0, 1, 0, 2, 2, 1, 0] demoR1_1210100 demoR2_1210100 demoC_1210100 demoM_1210100

theorem demoR1_2210100 : invRung 7 5 20 [2, 2, 1, 0, 1, 0, 0] [2, 2, 1, 0, 1, 0, 0] 1 2 false = ([1, 1, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_2210100 : invRung 7 5 20 [2, 2, 1, 0, 1, 0, 0] [1, 1, 2, 2, 1, 2, 0] 3 1 true = ([2, 0, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_2210100 : fieldCube 7 5 20 [2, 0, 2, 0, 2, 0, 1] = [2, 0, 2, 0, 1, 0, 2] := by
  decide

theorem demoM_2210100 : fieldMul 7 5 20 [2, 0, 2, 0, 1, 0, 2] [2, 2, 1, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210100 : mirrorTrits [2, 0, 2, 0, 1, 0, 2] = [1, 0, 1, 0, 2, 0, 1] := by
  decide

theorem demoInv_2210100 : specInv 7 5 20 [2, 2, 1, 0, 1, 0, 0] = some [1, 0, 1, 0, 2, 0, 1] :=
  specInv_mirror_7 [2, 2, 1, 0, 1, 0, 0] [1, 1, 2, 2, 1, 2, 0] [2, 0, 2, 0, 2, 0, 1] [2, 0, 2, 0, 1, 0, 2] [1, 0, 1, 0, 2, 0, 1] demoR1_2210100 demoR2_2210100 demoC_2210100 demoM_2210100 demoMir_2210100

theorem demoR1_0020100 : invRung 7 5 20 [0, 0, 2, 0, 1, 0, 0] [0, 0, 2, 0, 1, 0, 0] 1 2 false = ([0, 1, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_0020100 : invRung 7 5 20 [0, 0, 2, 0, 1, 0, 0] [0, 1, 2, 2, 1, 1, 0] 3 1 true = ([0, 1, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_0020100 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 0, 0] = [0, 0, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_0020100 : fieldMul 7 5 20 [0, 0, 0, 1, 0, 0, 0] [0, 0, 2, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0020100 : specInv 7 5 20 [0, 0, 2, 0, 1, 0, 0] = some [0, 0, 0, 1, 0, 0, 0] :=
  specInv_white_7 [0, 0, 2, 0, 1, 0, 0] [0, 1, 2, 2, 1, 1, 0] [0, 1, 0, 0, 0, 0, 0] [0, 0, 0, 1, 0, 0, 0] demoR1_0020100 demoR2_0020100 demoC_0020100 demoM_0020100

theorem demoR1_1020100 : invRung 7 5 20 [1, 0, 2, 0, 1, 0, 0] [1, 0, 2, 0, 1, 0, 0] 1 2 false = ([0, 2, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_1020100 : invRung 7 5 20 [1, 0, 2, 0, 1, 0, 0] [0, 2, 1, 1, 1, 0, 1] 3 1 true = ([1, 0, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_1020100 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 1, 2] = [2, 0, 2, 2, 0, 0, 1] := by
  decide

theorem demoM_1020100 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 0, 1] [1, 0, 2, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1020100 : specInv 7 5 20 [1, 0, 2, 0, 1, 0, 0] = some [2, 0, 2, 2, 0, 0, 1] :=
  specInv_white_7 [1, 0, 2, 0, 1, 0, 0] [0, 2, 1, 1, 1, 0, 1] [1, 0, 0, 0, 0, 1, 2] [2, 0, 2, 2, 0, 0, 1] demoR1_1020100 demoR2_1020100 demoC_1020100 demoM_1020100

theorem demoR1_2020100 : invRung 7 5 20 [2, 0, 2, 0, 1, 0, 0] [2, 0, 2, 0, 1, 0, 0] 1 2 false = ([1, 1, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_2020100 : invRung 7 5 20 [2, 0, 2, 0, 1, 0, 0] [1, 1, 2, 1, 2, 2, 0] 3 1 true = ([1, 0, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_2020100 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 1, 1] = [2, 2, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_2020100 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 2, 0] [2, 0, 2, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020100 : mirrorTrits [2, 2, 0, 1, 2, 2, 0] = [1, 1, 0, 2, 1, 1, 0] := by
  decide

theorem demoInv_2020100 : specInv 7 5 20 [2, 0, 2, 0, 1, 0, 0] = some [1, 1, 0, 2, 1, 1, 0] :=
  specInv_mirror_7 [2, 0, 2, 0, 1, 0, 0] [1, 1, 2, 1, 2, 2, 0] [1, 0, 0, 0, 0, 1, 1] [2, 2, 0, 1, 2, 2, 0] [1, 1, 0, 2, 1, 1, 0] demoR1_2020100 demoR2_2020100 demoC_2020100 demoM_2020100 demoMir_2020100

theorem demoR1_0120100 : invRung 7 5 20 [0, 1, 2, 0, 1, 0, 0] [0, 1, 2, 0, 1, 0, 0] 1 2 false = ([1, 1, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_0120100 : invRung 7 5 20 [0, 1, 2, 0, 1, 0, 0] [1, 1, 2, 2, 0, 1, 2] 3 1 true = ([0, 2, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_0120100 : fieldCube 7 5 20 [0, 2, 2, 2, 2, 0, 1] = [2, 0, 1, 2, 1, 2, 2] := by
  decide

theorem demoM_0120100 : fieldMul 7 5 20 [2, 0, 1, 2, 1, 2, 2] [0, 1, 2, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0120100 : specInv 7 5 20 [0, 1, 2, 0, 1, 0, 0] = some [2, 0, 1, 2, 1, 2, 2] :=
  specInv_white_7 [0, 1, 2, 0, 1, 0, 0] [1, 1, 2, 2, 0, 1, 2] [0, 2, 2, 2, 2, 0, 1] [2, 0, 1, 2, 1, 2, 2] demoR1_0120100 demoR2_0120100 demoC_0120100 demoM_0120100

theorem demoR1_1120100 : invRung 7 5 20 [1, 1, 2, 0, 1, 0, 0] [1, 1, 2, 0, 1, 0, 0] 1 2 false = ([0, 0, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_1120100 : invRung 7 5 20 [1, 1, 2, 0, 1, 0, 0] [0, 0, 0, 2, 1, 1, 0] 3 1 true = ([1, 0, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_1120100 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 1, 1] = [1, 0, 2, 2, 2, 2, 2] := by
  decide

theorem demoM_1120100 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 2, 2] [1, 1, 2, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120100 : mirrorTrits [1, 0, 2, 2, 2, 2, 2] = [2, 0, 1, 1, 1, 1, 1] := by
  decide

theorem demoInv_1120100 : specInv 7 5 20 [1, 1, 2, 0, 1, 0, 0] = some [2, 0, 1, 1, 1, 1, 1] :=
  specInv_mirror_7 [1, 1, 2, 0, 1, 0, 0] [0, 0, 0, 2, 1, 1, 0] [1, 0, 1, 2, 1, 1, 1] [1, 0, 2, 2, 2, 2, 2] [2, 0, 1, 1, 1, 1, 1] demoR1_1120100 demoR2_1120100 demoC_1120100 demoM_1120100 demoMir_1120100

theorem demoR1_2120100 : invRung 7 5 20 [2, 1, 2, 0, 1, 0, 0] [2, 1, 2, 0, 1, 0, 0] 1 2 false = ([2, 2, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2120100 : invRung 7 5 20 [2, 1, 2, 0, 1, 0, 0] [2, 2, 2, 2, 0, 0, 2] 3 1 true = ([1, 0, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_2120100 : fieldCube 7 5 20 [1, 0, 2, 0, 2, 1, 1] = [2, 1, 0, 0, 2, 1, 1] := by
  decide

theorem demoM_2120100 : fieldMul 7 5 20 [2, 1, 0, 0, 2, 1, 1] [2, 1, 2, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120100 : mirrorTrits [2, 1, 0, 0, 2, 1, 1] = [1, 2, 0, 0, 1, 2, 2] := by
  decide

theorem demoInv_2120100 : specInv 7 5 20 [2, 1, 2, 0, 1, 0, 0] = some [1, 2, 0, 0, 1, 2, 2] :=
  specInv_mirror_7 [2, 1, 2, 0, 1, 0, 0] [2, 2, 2, 2, 0, 0, 2] [1, 0, 2, 0, 2, 1, 1] [2, 1, 0, 0, 2, 1, 1] [1, 2, 0, 0, 1, 2, 2] demoR1_2120100 demoR2_2120100 demoC_2120100 demoM_2120100 demoMir_2120100

theorem demoR1_0220100 : invRung 7 5 20 [0, 2, 2, 0, 1, 0, 0] [0, 2, 2, 0, 1, 0, 0] 1 2 false = ([1, 0, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_0220100 : invRung 7 5 20 [0, 2, 2, 0, 1, 0, 0] [1, 0, 2, 0, 0, 2, 2] 3 1 true = ([1, 1, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_0220100 : fieldCube 7 5 20 [1, 1, 2, 2, 0, 2, 0] = [2, 2, 1, 1, 2, 1, 0] := by
  decide

theorem demoM_0220100 : fieldMul 7 5 20 [2, 2, 1, 1, 2, 1, 0] [0, 2, 2, 0, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0220100 : specInv 7 5 20 [0, 2, 2, 0, 1, 0, 0] = some [2, 2, 1, 1, 2, 1, 0] :=
  specInv_white_7 [0, 2, 2, 0, 1, 0, 0] [1, 0, 2, 0, 0, 2, 2] [1, 1, 2, 2, 0, 2, 0] [2, 2, 1, 1, 2, 1, 0] demoR1_0220100 demoR2_0220100 demoC_0220100 demoM_0220100

theorem demoR1_1220100 : invRung 7 5 20 [1, 2, 2, 0, 1, 0, 0] [1, 2, 2, 0, 1, 0, 0] 1 2 false = ([2, 1, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_1220100 : invRung 7 5 20 [1, 2, 2, 0, 1, 0, 0] [2, 1, 2, 2, 1, 2, 1] 3 1 true = ([2, 1, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_1220100 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 0, 0] = [1, 1, 2, 2, 0, 0, 1] := by
  decide

theorem demoM_1220100 : fieldMul 7 5 20 [1, 1, 2, 2, 0, 0, 1] [1, 2, 2, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220100 : mirrorTrits [1, 1, 2, 2, 0, 0, 1] = [2, 2, 1, 1, 0, 0, 2] := by
  decide

theorem demoInv_1220100 : specInv 7 5 20 [1, 2, 2, 0, 1, 0, 0] = some [2, 2, 1, 1, 0, 0, 2] :=
  specInv_mirror_7 [1, 2, 2, 0, 1, 0, 0] [2, 1, 2, 2, 1, 2, 1] [2, 1, 0, 2, 1, 0, 0] [1, 1, 2, 2, 0, 0, 1] [2, 2, 1, 1, 0, 0, 2] demoR1_1220100 demoR2_1220100 demoC_1220100 demoM_1220100 demoMir_1220100

theorem demoR1_2220100 : invRung 7 5 20 [2, 2, 2, 0, 1, 0, 0] [2, 2, 2, 0, 1, 0, 0] 1 2 false = ([2, 1, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_2220100 : invRung 7 5 20 [2, 2, 2, 0, 1, 0, 0] [2, 1, 2, 0, 0, 0, 1] 3 1 true = ([0, 2, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_2220100 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 2, 1] = [2, 1, 1, 1, 0, 1, 0] := by
  decide

theorem demoM_2220100 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 1, 0] [2, 2, 2, 0, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220100 : mirrorTrits [2, 1, 1, 1, 0, 1, 0] = [1, 2, 2, 2, 0, 2, 0] := by
  decide

theorem demoInv_2220100 : specInv 7 5 20 [2, 2, 2, 0, 1, 0, 0] = some [1, 2, 2, 2, 0, 2, 0] :=
  specInv_mirror_7 [2, 2, 2, 0, 1, 0, 0] [2, 1, 2, 0, 0, 0, 1] [0, 2, 0, 0, 1, 2, 1] [2, 1, 1, 1, 0, 1, 0] [1, 2, 2, 2, 0, 2, 0] demoR1_2220100 demoR2_2220100 demoC_2220100 demoM_2220100 demoMir_2220100

theorem demoR1_0001100 : invRung 7 5 20 [0, 0, 0, 1, 1, 0, 0] [0, 0, 0, 1, 1, 0, 0] 1 2 false = ([1, 0, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_0001100 : invRung 7 5 20 [0, 0, 0, 1, 1, 0, 0] [1, 0, 1, 1, 1, 2, 1] 3 1 true = ([2, 2, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_0001100 : fieldCube 7 5 20 [2, 2, 2, 0, 0, 1, 2] = [0, 0, 2, 1, 0, 0, 0] := by
  decide

theorem demoM_0001100 : fieldMul 7 5 20 [0, 0, 2, 1, 0, 0, 0] [0, 0, 0, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0001100 : specInv 7 5 20 [0, 0, 0, 1, 1, 0, 0] = some [0, 0, 2, 1, 0, 0, 0] :=
  specInv_white_7 [0, 0, 0, 1, 1, 0, 0] [1, 0, 1, 1, 1, 2, 1] [2, 2, 2, 0, 0, 1, 2] [0, 0, 2, 1, 0, 0, 0] demoR1_0001100 demoR2_0001100 demoC_0001100 demoM_0001100

theorem demoR1_1001100 : invRung 7 5 20 [1, 0, 0, 1, 1, 0, 0] [1, 0, 0, 1, 1, 0, 0] 1 2 false = ([2, 0, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_1001100 : invRung 7 5 20 [1, 0, 0, 1, 1, 0, 0] [2, 0, 2, 0, 1, 1, 1] 3 1 true = ([0, 1, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1001100 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 1, 1] = [2, 2, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_1001100 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 0, 2] [1, 0, 0, 1, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1001100 : mirrorTrits [2, 2, 1, 2, 2, 0, 2] = [1, 1, 2, 1, 1, 0, 1] := by
  decide

theorem demoInv_1001100 : specInv 7 5 20 [1, 0, 0, 1, 1, 0, 0] = some [1, 1, 2, 1, 1, 0, 1] :=
  specInv_mirror_7 [1, 0, 0, 1, 1, 0, 0] [2, 0, 2, 0, 1, 1, 1] [0, 1, 2, 1, 0, 1, 1] [2, 2, 1, 2, 2, 0, 2] [1, 1, 2, 1, 1, 0, 1] demoR1_1001100 demoR2_1001100 demoC_1001100 demoM_1001100 demoMir_1001100

theorem demoR1_2001100 : invRung 7 5 20 [2, 0, 0, 1, 1, 0, 0] [2, 0, 0, 1, 1, 0, 0] 1 2 false = ([1, 2, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_2001100 : invRung 7 5 20 [2, 0, 0, 1, 1, 0, 0] [1, 2, 0, 1, 0, 0, 0] 3 1 true = ([2, 0, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2001100 : fieldCube 7 5 20 [2, 0, 0, 1, 2, 1, 0] = [1, 0, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_2001100 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 1, 1] [2, 0, 0, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2001100 : specInv 7 5 20 [2, 0, 0, 1, 1, 0, 0] = some [1, 0, 2, 2, 1, 1, 1] :=
  specInv_white_7 [2, 0, 0, 1, 1, 0, 0] [1, 2, 0, 1, 0, 0, 0] [2, 0, 0, 1, 2, 1, 0] [1, 0, 2, 2, 1, 1, 1] demoR1_2001100 demoR2_2001100 demoC_2001100 demoM_2001100

theorem demoR1_0101100 : invRung 7 5 20 [0, 1, 0, 1, 1, 0, 0] [0, 1, 0, 1, 1, 0, 0] 1 2 false = ([2, 1, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_0101100 : invRung 7 5 20 [0, 1, 0, 1, 1, 0, 0] [2, 1, 0, 1, 2, 2, 2] 3 1 true = ([0, 2, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0101100 : fieldCube 7 5 20 [0, 2, 2, 2, 1, 2, 1] = [1, 1, 0, 1, 0, 0, 2] := by
  decide

theorem demoM_0101100 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 0, 2] [0, 1, 0, 1, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101100 : mirrorTrits [1, 1, 0, 1, 0, 0, 2] = [2, 2, 0, 2, 0, 0, 1] := by
  decide

theorem demoInv_0101100 : specInv 7 5 20 [0, 1, 0, 1, 1, 0, 0] = some [2, 2, 0, 2, 0, 0, 1] :=
  specInv_mirror_7 [0, 1, 0, 1, 1, 0, 0] [2, 1, 0, 1, 2, 2, 2] [0, 2, 2, 2, 1, 2, 1] [1, 1, 0, 1, 0, 0, 2] [2, 2, 0, 2, 0, 0, 1] demoR1_0101100 demoR2_0101100 demoC_0101100 demoM_0101100 demoMir_0101100

theorem demoR1_1101100 : invRung 7 5 20 [1, 1, 0, 1, 1, 0, 0] [1, 1, 0, 1, 1, 0, 0] 1 2 false = ([0, 1, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_1101100 : invRung 7 5 20 [1, 1, 0, 1, 1, 0, 0] [0, 1, 1, 0, 0, 2, 1] 3 1 true = ([0, 2, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1101100 : fieldCube 7 5 20 [0, 2, 0, 2, 1, 2, 2] = [1, 2, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_1101100 : fieldMul 7 5 20 [1, 2, 2, 2, 1, 1, 1] [1, 1, 0, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1101100 : specInv 7 5 20 [1, 1, 0, 1, 1, 0, 0] = some [1, 2, 2, 2, 1, 1, 1] :=
  specInv_white_7 [1, 1, 0, 1, 1, 0, 0] [0, 1, 1, 0, 0, 2, 1] [0, 2, 0, 2, 1, 2, 2] [1, 2, 2, 2, 1, 1, 1] demoR1_1101100 demoR2_1101100 demoC_1101100 demoM_1101100

theorem demoR1_2101100 : invRung 7 5 20 [2, 1, 0, 1, 1, 0, 0] [2, 1, 0, 1, 1, 0, 0] 1 2 false = ([1, 2, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_2101100 : invRung 7 5 20 [2, 1, 0, 1, 1, 0, 0] [1, 2, 1, 0, 0, 1, 2] 3 1 true = ([2, 0, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_2101100 : fieldCube 7 5 20 [2, 0, 2, 0, 0, 0, 1] = [2, 1, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_2101100 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 1, 0] [2, 1, 0, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2101100 : specInv 7 5 20 [2, 1, 0, 1, 1, 0, 0] = some [2, 1, 2, 1, 1, 1, 0] :=
  specInv_white_7 [2, 1, 0, 1, 1, 0, 0] [1, 2, 1, 0, 0, 1, 2] [2, 0, 2, 0, 0, 0, 1] [2, 1, 2, 1, 1, 1, 0] demoR1_2101100 demoR2_2101100 demoC_2101100 demoM_2101100

theorem demoR1_0201100 : invRung 7 5 20 [0, 2, 0, 1, 1, 0, 0] [0, 2, 0, 1, 1, 0, 0] 1 2 false = ([0, 1, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_0201100 : invRung 7 5 20 [0, 2, 0, 1, 1, 0, 0] [0, 1, 0, 0, 0, 2, 2] 3 1 true = ([1, 2, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0201100 : fieldCube 7 5 20 [1, 2, 2, 0, 1, 2, 2] = [0, 2, 0, 2, 1, 2, 0] := by
  decide

theorem demoM_0201100 : fieldMul 7 5 20 [0, 2, 0, 2, 1, 2, 0] [0, 2, 0, 1, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201100 : mirrorTrits [0, 2, 0, 2, 1, 2, 0] = [0, 1, 0, 1, 2, 1, 0] := by
  decide

theorem demoInv_0201100 : specInv 7 5 20 [0, 2, 0, 1, 1, 0, 0] = some [0, 1, 0, 1, 2, 1, 0] :=
  specInv_mirror_7 [0, 2, 0, 1, 1, 0, 0] [0, 1, 0, 0, 0, 2, 2] [1, 2, 2, 0, 1, 2, 2] [0, 2, 0, 2, 1, 2, 0] [0, 1, 0, 1, 2, 1, 0] demoR1_0201100 demoR2_0201100 demoC_0201100 demoM_0201100 demoMir_0201100

theorem demoR1_1201100 : invRung 7 5 20 [1, 2, 0, 1, 1, 0, 0] [1, 2, 0, 1, 1, 0, 0] 1 2 false = ([1, 2, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_1201100 : invRung 7 5 20 [1, 2, 0, 1, 1, 0, 0] [1, 2, 1, 0, 1, 2, 1] 3 1 true = ([1, 1, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_1201100 : fieldCube 7 5 20 [1, 1, 0, 2, 2, 0, 1] = [0, 0, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_1201100 : fieldMul 7 5 20 [0, 0, 1, 1, 1, 2, 0] [1, 2, 0, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1201100 : specInv 7 5 20 [1, 2, 0, 1, 1, 0, 0] = some [0, 0, 1, 1, 1, 2, 0] :=
  specInv_white_7 [1, 2, 0, 1, 1, 0, 0] [1, 2, 1, 0, 1, 2, 1] [1, 1, 0, 2, 2, 0, 1] [0, 0, 1, 1, 1, 2, 0] demoR1_1201100 demoR2_1201100 demoC_1201100 demoM_1201100

theorem demoR1_2201100 : invRung 7 5 20 [2, 2, 0, 1, 1, 0, 0] [2, 2, 0, 1, 1, 0, 0] 1 2 false = ([1, 0, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_2201100 : invRung 7 5 20 [2, 2, 0, 1, 1, 0, 0] [1, 0, 0, 0, 1, 0, 2] 3 1 true = ([0, 1, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_2201100 : fieldCube 7 5 20 [0, 1, 2, 0, 0, 0, 2] = [0, 2, 1, 0, 2, 2, 1] := by
  decide

theorem demoM_2201100 : fieldMul 7 5 20 [0, 2, 1, 0, 2, 2, 1] [2, 2, 0, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2201100 : specInv 7 5 20 [2, 2, 0, 1, 1, 0, 0] = some [0, 2, 1, 0, 2, 2, 1] :=
  specInv_white_7 [2, 2, 0, 1, 1, 0, 0] [1, 0, 0, 0, 1, 0, 2] [0, 1, 2, 0, 0, 0, 2] [0, 2, 1, 0, 2, 2, 1] demoR1_2201100 demoR2_2201100 demoC_2201100 demoM_2201100

theorem demoR1_0011100 : invRung 7 5 20 [0, 0, 1, 1, 1, 0, 0] [0, 0, 1, 1, 1, 0, 0] 1 2 false = ([1, 1, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0011100 : invRung 7 5 20 [0, 0, 1, 1, 1, 0, 0] [1, 1, 1, 0, 0, 0, 0] 3 1 true = ([1, 0, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0011100 : fieldCube 7 5 20 [1, 0, 2, 0, 2, 1, 2] = [2, 2, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_0011100 : fieldMul 7 5 20 [2, 2, 2, 1, 0, 2, 2] [0, 0, 1, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0011100 : specInv 7 5 20 [0, 0, 1, 1, 1, 0, 0] = some [2, 2, 2, 1, 0, 2, 2] :=
  specInv_white_7 [0, 0, 1, 1, 1, 0, 0] [1, 1, 1, 0, 0, 0, 0] [1, 0, 2, 0, 2, 1, 2] [2, 2, 2, 1, 0, 2, 2] demoR1_0011100 demoR2_0011100 demoC_0011100 demoM_0011100

theorem demoR1_1011100 : invRung 7 5 20 [1, 0, 1, 1, 1, 0, 0] [1, 0, 1, 1, 1, 0, 0] 1 2 false = ([2, 2, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_1011100 : invRung 7 5 20 [1, 0, 1, 1, 1, 0, 0] [2, 2, 1, 2, 2, 2, 0] 3 1 true = ([2, 0, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_1011100 : fieldCube 7 5 20 [2, 0, 0, 1, 2, 0, 0] = [0, 2, 1, 2, 0, 0, 2] := by
  decide

theorem demoM_1011100 : fieldMul 7 5 20 [0, 2, 1, 2, 0, 0, 2] [1, 0, 1, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1011100 : specInv 7 5 20 [1, 0, 1, 1, 1, 0, 0] = some [0, 2, 1, 2, 0, 0, 2] :=
  specInv_white_7 [1, 0, 1, 1, 1, 0, 0] [2, 2, 1, 2, 2, 2, 0] [2, 0, 0, 1, 2, 0, 0] [0, 2, 1, 2, 0, 0, 2] demoR1_1011100 demoR2_1011100 demoC_1011100 demoM_1011100

theorem demoR1_2011100 : invRung 7 5 20 [2, 0, 1, 1, 1, 0, 0] [2, 0, 1, 1, 1, 0, 0] 1 2 false = ([1, 1, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2011100 : invRung 7 5 20 [2, 0, 1, 1, 1, 0, 0] [1, 1, 1, 2, 2, 0, 0] 3 1 true = ([2, 0, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_2011100 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 0, 0] = [1, 0, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_2011100 : fieldMul 7 5 20 [1, 0, 2, 0, 0, 2, 2] [2, 0, 1, 1, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011100 : mirrorTrits [1, 0, 2, 0, 0, 2, 2] = [2, 0, 1, 0, 0, 1, 1] := by
  decide

theorem demoInv_2011100 : specInv 7 5 20 [2, 0, 1, 1, 1, 0, 0] = some [2, 0, 1, 0, 0, 1, 1] :=
  specInv_mirror_7 [2, 0, 1, 1, 1, 0, 0] [1, 1, 1, 2, 2, 0, 0] [2, 0, 2, 2, 0, 0, 0] [1, 0, 2, 0, 0, 2, 2] [2, 0, 1, 0, 0, 1, 1] demoR1_2011100 demoR2_2011100 demoC_2011100 demoM_2011100 demoMir_2011100

theorem demoR1_0111100 : invRung 7 5 20 [0, 1, 1, 1, 1, 0, 0] [0, 1, 1, 1, 1, 0, 0] 1 2 false = ([2, 0, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_0111100 : invRung 7 5 20 [0, 1, 1, 1, 1, 0, 0] [2, 0, 0, 0, 0, 1, 2] 3 1 true = ([1, 0, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0111100 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 0, 0] = [2, 0, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_0111100 : fieldMul 7 5 20 [2, 0, 1, 0, 0, 1, 0] [0, 1, 1, 1, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111100 : mirrorTrits [2, 0, 1, 0, 0, 1, 0] = [1, 0, 2, 0, 0, 2, 0] := by
  decide

theorem demoInv_0111100 : specInv 7 5 20 [0, 1, 1, 1, 1, 0, 0] = some [1, 0, 2, 0, 0, 2, 0] :=
  specInv_mirror_7 [0, 1, 1, 1, 1, 0, 0] [2, 0, 0, 0, 0, 1, 2] [1, 0, 0, 1, 0, 0, 0] [2, 0, 1, 0, 0, 1, 0] [1, 0, 2, 0, 0, 2, 0] demoR1_0111100 demoR2_0111100 demoC_0111100 demoM_0111100 demoMir_0111100

theorem demoR1_1111100 : invRung 7 5 20 [1, 1, 1, 1, 1, 0, 0] [1, 1, 1, 1, 1, 0, 0] 1 2 false = ([0, 0, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_1111100 : invRung 7 5 20 [1, 1, 1, 1, 1, 0, 0] [0, 0, 1, 1, 1, 2, 0] 3 1 true = ([1, 0, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1111100 : fieldCube 7 5 20 [1, 0, 2, 0, 1, 0, 0] = [1, 1, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_1111100 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 1, 0] [1, 1, 1, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1111100 : specInv 7 5 20 [1, 1, 1, 1, 1, 0, 0] = some [1, 1, 0, 1, 0, 1, 0] :=
  specInv_white_7 [1, 1, 1, 1, 1, 0, 0] [0, 0, 1, 1, 1, 2, 0] [1, 0, 2, 0, 1, 0, 0] [1, 1, 0, 1, 0, 1, 0] demoR1_1111100 demoR2_1111100 demoC_1111100 demoM_1111100

theorem demoR1_2111100 : invRung 7 5 20 [2, 1, 1, 1, 1, 0, 0] [2, 1, 1, 1, 1, 0, 0] 1 2 false = ([1, 0, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_2111100 : invRung 7 5 20 [2, 1, 1, 1, 1, 0, 0] [1, 0, 1, 2, 0, 1, 1] 3 1 true = ([0, 1, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_2111100 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 1, 0] = [0, 2, 0, 2, 1, 1, 0] := by
  decide

theorem demoM_2111100 : fieldMul 7 5 20 [0, 2, 0, 2, 1, 1, 0] [2, 1, 1, 1, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2111100 : mirrorTrits [0, 2, 0, 2, 1, 1, 0] = [0, 1, 0, 1, 2, 2, 0] := by
  decide

theorem demoInv_2111100 : specInv 7 5 20 [2, 1, 1, 1, 1, 0, 0] = some [0, 1, 0, 1, 2, 2, 0] :=
  specInv_mirror_7 [2, 1, 1, 1, 1, 0, 0] [1, 0, 1, 2, 0, 1, 1] [0, 1, 0, 2, 1, 1, 0] [0, 2, 0, 2, 1, 1, 0] [0, 1, 0, 1, 2, 2, 0] demoR1_2111100 demoR2_2111100 demoC_2111100 demoM_2111100 demoMir_2111100

theorem demoR1_0211100 : invRung 7 5 20 [0, 2, 1, 1, 1, 0, 0] [0, 2, 1, 1, 1, 0, 0] 1 2 false = ([1, 0, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0211100 : invRung 7 5 20 [0, 2, 1, 1, 1, 0, 0] [1, 0, 1, 2, 0, 0, 0] 3 1 true = ([2, 1, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_0211100 : fieldCube 7 5 20 [2, 1, 1, 2, 0, 2, 2] = [0, 1, 2, 0, 1, 0, 1] := by
  decide

theorem demoM_0211100 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 0, 1] [0, 2, 1, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0211100 : specInv 7 5 20 [0, 2, 1, 1, 1, 0, 0] = some [0, 1, 2, 0, 1, 0, 1] :=
  specInv_white_7 [0, 2, 1, 1, 1, 0, 0] [1, 0, 1, 2, 0, 0, 0] [2, 1, 1, 2, 0, 2, 2] [0, 1, 2, 0, 1, 0, 1] demoR1_0211100 demoR2_0211100 demoC_0211100 demoM_0211100

theorem demoR1_1211100 : invRung 7 5 20 [1, 2, 1, 1, 1, 0, 0] [1, 2, 1, 1, 1, 0, 0] 1 2 false = ([2, 0, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_1211100 : invRung 7 5 20 [1, 2, 1, 1, 1, 0, 0] [2, 0, 0, 0, 2, 2, 0] 3 1 true = ([2, 1, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_1211100 : fieldCube 7 5 20 [2, 1, 0, 0, 2, 2, 0] = [1, 1, 2, 0, 2, 1, 0] := by
  decide

theorem demoM_1211100 : fieldMul 7 5 20 [1, 1, 2, 0, 2, 1, 0] [1, 2, 1, 1, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1211100 : mirrorTrits [1, 1, 2, 0, 2, 1, 0] = [2, 2, 1, 0, 1, 2, 0] := by
  decide

theorem demoInv_1211100 : specInv 7 5 20 [1, 2, 1, 1, 1, 0, 0] = some [2, 2, 1, 0, 1, 2, 0] :=
  specInv_mirror_7 [1, 2, 1, 1, 1, 0, 0] [2, 0, 0, 0, 2, 2, 0] [2, 1, 0, 0, 2, 2, 0] [1, 1, 2, 0, 2, 1, 0] [2, 2, 1, 0, 1, 2, 0] demoR1_1211100 demoR2_1211100 demoC_1211100 demoM_1211100 demoMir_1211100

theorem demoR1_2211100 : invRung 7 5 20 [2, 2, 1, 1, 1, 0, 0] [2, 2, 1, 1, 1, 0, 0] 1 2 false = ([2, 2, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_2211100 : invRung 7 5 20 [2, 2, 1, 1, 1, 0, 0] [2, 2, 0, 0, 2, 1, 0] 3 1 true = ([2, 1, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2211100 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 1, 0] = [0, 2, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_2211100 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 2, 1] [2, 2, 1, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2211100 : specInv 7 5 20 [2, 2, 1, 1, 1, 0, 0] = some [0, 2, 1, 2, 1, 2, 1] :=
  specInv_white_7 [2, 2, 1, 1, 1, 0, 0] [2, 2, 0, 0, 2, 1, 0] [2, 1, 1, 0, 1, 1, 0] [0, 2, 1, 2, 1, 2, 1] demoR1_2211100 demoR2_2211100 demoC_2211100 demoM_2211100

theorem demoR1_0021100 : invRung 7 5 20 [0, 0, 2, 1, 1, 0, 0] [0, 0, 2, 1, 1, 0, 0] 1 2 false = ([2, 1, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0021100 : invRung 7 5 20 [0, 0, 2, 1, 1, 0, 0] [2, 1, 2, 0, 0, 0, 0] 3 1 true = ([1, 1, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0021100 : fieldCube 7 5 20 [1, 1, 2, 2, 1, 2, 1] = [2, 1, 0, 0, 0, 0, 2] := by
  decide

theorem demoM_0021100 : fieldMul 7 5 20 [2, 1, 0, 0, 0, 0, 2] [0, 0, 2, 1, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021100 : mirrorTrits [2, 1, 0, 0, 0, 0, 2] = [1, 2, 0, 0, 0, 0, 1] := by
  decide

theorem demoInv_0021100 : specInv 7 5 20 [0, 0, 2, 1, 1, 0, 0] = some [1, 2, 0, 0, 0, 0, 1] :=
  specInv_mirror_7 [0, 0, 2, 1, 1, 0, 0] [2, 1, 2, 0, 0, 0, 0] [1, 1, 2, 2, 1, 2, 1] [2, 1, 0, 0, 0, 0, 2] [1, 2, 0, 0, 0, 0, 1] demoR1_0021100 demoR2_0021100 demoC_0021100 demoM_0021100 demoMir_0021100

theorem demoR1_1021100 : invRung 7 5 20 [1, 0, 2, 1, 1, 0, 0] [1, 0, 2, 1, 1, 0, 0] 1 2 false = ([2, 0, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_1021100 : invRung 7 5 20 [1, 0, 2, 1, 1, 0, 0] [2, 0, 2, 2, 1, 2, 2] 3 1 true = ([2, 2, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_1021100 : fieldCube 7 5 20 [2, 2, 2, 2, 2, 1, 0] = [2, 0, 0, 1, 1, 2, 0] := by
  decide

theorem demoM_1021100 : fieldMul 7 5 20 [2, 0, 0, 1, 1, 2, 0] [1, 0, 2, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1021100 : specInv 7 5 20 [1, 0, 2, 1, 1, 0, 0] = some [2, 0, 0, 1, 1, 2, 0] :=
  specInv_white_7 [1, 0, 2, 1, 1, 0, 0] [2, 0, 2, 2, 1, 2, 2] [2, 2, 2, 2, 2, 1, 0] [2, 0, 0, 1, 1, 2, 0] demoR1_1021100 demoR2_1021100 demoC_1021100 demoM_1021100

theorem demoR1_2021100 : invRung 7 5 20 [2, 0, 2, 1, 1, 0, 0] [2, 0, 2, 1, 1, 0, 0] 1 2 false = ([0, 2, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_2021100 : invRung 7 5 20 [2, 0, 2, 1, 1, 0, 0] [0, 2, 2, 1, 2, 2, 2] 3 1 true = ([2, 1, 2, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_2021100 : fieldCube 7 5 20 [2, 1, 2, 1, 2, 0, 2] = [0, 1, 2, 2, 2, 2, 0] := by
  decide

theorem demoM_2021100 : fieldMul 7 5 20 [0, 1, 2, 2, 2, 2, 0] [2, 0, 2, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2021100 : specInv 7 5 20 [2, 0, 2, 1, 1, 0, 0] = some [0, 1, 2, 2, 2, 2, 0] :=
  specInv_white_7 [2, 0, 2, 1, 1, 0, 0] [0, 2, 2, 1, 2, 2, 2] [2, 1, 2, 1, 2, 0, 2] [0, 1, 2, 2, 2, 2, 0] demoR1_2021100 demoR2_2021100 demoC_2021100 demoM_2021100

theorem demoR1_0121100 : invRung 7 5 20 [0, 1, 2, 1, 1, 0, 0] [0, 1, 2, 1, 1, 0, 0] 1 2 false = ([0, 0, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_0121100 : invRung 7 5 20 [0, 1, 2, 1, 1, 0, 0] [0, 0, 0, 2, 1, 1, 2] 3 1 true = ([1, 2, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_0121100 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 1, 2] = [2, 1, 2, 2, 0, 1, 0] := by
  decide

theorem demoM_0121100 : fieldMul 7 5 20 [2, 1, 2, 2, 0, 1, 0] [0, 1, 2, 1, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0121100 : mirrorTrits [2, 1, 2, 2, 0, 1, 0] = [1, 2, 1, 1, 0, 2, 0] := by
  decide

theorem demoInv_0121100 : specInv 7 5 20 [0, 1, 2, 1, 1, 0, 0] = some [1, 2, 1, 1, 0, 2, 0] :=
  specInv_mirror_7 [0, 1, 2, 1, 1, 0, 0] [0, 0, 0, 2, 1, 1, 2] [1, 2, 1, 0, 1, 1, 2] [2, 1, 2, 2, 0, 1, 0] [1, 2, 1, 1, 0, 2, 0] demoR1_0121100 demoR2_0121100 demoC_0121100 demoM_0121100 demoMir_0121100

theorem demoR1_1121100 : invRung 7 5 20 [1, 1, 2, 1, 1, 0, 0] [1, 1, 2, 1, 1, 0, 0] 1 2 false = ([0, 0, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_1121100 : invRung 7 5 20 [1, 1, 2, 1, 1, 0, 0] [0, 0, 2, 2, 2, 0, 1] 3 1 true = ([1, 0, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1121100 : fieldCube 7 5 20 [1, 0, 1, 2, 0, 1, 0] = [1, 1, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_1121100 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 0, 0] [1, 1, 2, 1, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121100 : mirrorTrits [1, 1, 0, 0, 1, 0, 0] = [2, 2, 0, 0, 2, 0, 0] := by
  decide

theorem demoInv_1121100 : specInv 7 5 20 [1, 1, 2, 1, 1, 0, 0] = some [2, 2, 0, 0, 2, 0, 0] :=
  specInv_mirror_7 [1, 1, 2, 1, 1, 0, 0] [0, 0, 2, 2, 2, 0, 1] [1, 0, 1, 2, 0, 1, 0] [1, 1, 0, 0, 1, 0, 0] [2, 2, 0, 0, 2, 0, 0] demoR1_1121100 demoR2_1121100 demoC_1121100 demoM_1121100 demoMir_1121100

theorem demoR1_2121100 : invRung 7 5 20 [2, 1, 2, 1, 1, 0, 0] [2, 1, 2, 1, 1, 0, 0] 1 2 false = ([0, 2, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2121100 : invRung 7 5 20 [2, 1, 2, 1, 1, 0, 0] [0, 2, 0, 1, 0, 2, 1] 3 1 true = ([1, 1, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_2121100 : fieldCube 7 5 20 [1, 1, 2, 1, 0, 2, 2] = [1, 1, 1, 0, 1, 2, 2] := by
  decide

theorem demoM_2121100 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 2, 2] [2, 1, 2, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2121100 : specInv 7 5 20 [2, 1, 2, 1, 1, 0, 0] = some [1, 1, 1, 0, 1, 2, 2] :=
  specInv_white_7 [2, 1, 2, 1, 1, 0, 0] [0, 2, 0, 1, 0, 2, 1] [1, 1, 2, 1, 0, 2, 2] [1, 1, 1, 0, 1, 2, 2] demoR1_2121100 demoR2_2121100 demoC_2121100 demoM_2121100

theorem demoR1_0221100 : invRung 7 5 20 [0, 2, 2, 1, 1, 0, 0] [0, 2, 2, 1, 1, 0, 0] 1 2 false = ([0, 2, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_0221100 : invRung 7 5 20 [0, 2, 2, 1, 1, 0, 0] [0, 2, 1, 0, 2, 1, 0] 3 1 true = ([2, 2, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_0221100 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 2, 1] = [2, 1, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_0221100 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 2, 1] [0, 2, 2, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0221100 : specInv 7 5 20 [0, 2, 2, 1, 1, 0, 0] = some [2, 1, 2, 1, 0, 2, 1] :=
  specInv_white_7 [0, 2, 2, 1, 1, 0, 0] [0, 2, 1, 0, 2, 1, 0] [2, 2, 1, 1, 1, 2, 1] [2, 1, 2, 1, 0, 2, 1] demoR1_0221100 demoR2_0221100 demoC_0221100 demoM_0221100

theorem demoR1_1221100 : invRung 7 5 20 [1, 2, 2, 1, 1, 0, 0] [1, 2, 2, 1, 1, 0, 0] 1 2 false = ([0, 1, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_1221100 : invRung 7 5 20 [1, 2, 2, 1, 1, 0, 0] [0, 1, 2, 2, 2, 2, 0] 3 1 true = ([0, 1, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_1221100 : fieldCube 7 5 20 [0, 1, 1, 2, 0, 0, 2] = [2, 2, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_1221100 : fieldMul 7 5 20 [2, 2, 0, 0, 2, 1, 0] [1, 2, 2, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1221100 : specInv 7 5 20 [1, 2, 2, 1, 1, 0, 0] = some [2, 2, 0, 0, 2, 1, 0] :=
  specInv_white_7 [1, 2, 2, 1, 1, 0, 0] [0, 1, 2, 2, 2, 2, 0] [0, 1, 1, 2, 0, 0, 2] [2, 2, 0, 0, 2, 1, 0] demoR1_1221100 demoR2_1221100 demoC_1221100 demoM_1221100

theorem demoR1_2221100 : invRung 7 5 20 [2, 2, 2, 1, 1, 0, 0] [2, 2, 2, 1, 1, 0, 0] 1 2 false = ([2, 1, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_2221100 : invRung 7 5 20 [2, 2, 2, 1, 1, 0, 0] [2, 1, 1, 2, 2, 2, 1] 3 1 true = ([2, 2, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_2221100 : fieldCube 7 5 20 [2, 2, 1, 0, 0, 2, 2] = [1, 1, 0, 1, 1, 1, 1] := by
  decide

theorem demoM_2221100 : fieldMul 7 5 20 [1, 1, 0, 1, 1, 1, 1] [2, 2, 2, 1, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2221100 : specInv 7 5 20 [2, 2, 2, 1, 1, 0, 0] = some [1, 1, 0, 1, 1, 1, 1] :=
  specInv_white_7 [2, 2, 2, 1, 1, 0, 0] [2, 1, 1, 2, 2, 2, 1] [2, 2, 1, 0, 0, 2, 2] [1, 1, 0, 1, 1, 1, 1] demoR1_2221100 demoR2_2221100 demoC_2221100 demoM_2221100

theorem demoR1_0002100 : invRung 7 5 20 [0, 0, 0, 2, 1, 0, 0] [0, 0, 0, 2, 1, 0, 0] 1 2 false = ([1, 0, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_0002100 : invRung 7 5 20 [0, 0, 0, 2, 1, 0, 0] [1, 0, 1, 2, 2, 1, 1] 3 1 true = ([1, 0, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0002100 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 2, 1] = [0, 0, 1, 1, 0, 0, 0] := by
  decide

theorem demoM_0002100 : fieldMul 7 5 20 [0, 0, 1, 1, 0, 0, 0] [0, 0, 0, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0002100 : specInv 7 5 20 [0, 0, 0, 2, 1, 0, 0] = some [0, 0, 1, 1, 0, 0, 0] :=
  specInv_white_7 [0, 0, 0, 2, 1, 0, 0] [1, 0, 1, 2, 2, 1, 1] [1, 0, 1, 0, 0, 2, 1] [0, 0, 1, 1, 0, 0, 0] demoR1_0002100 demoR2_0002100 demoC_0002100 demoM_0002100

theorem demoR1_1002100 : invRung 7 5 20 [1, 0, 0, 2, 1, 0, 0] [1, 0, 0, 2, 1, 0, 0] 1 2 false = ([2, 1, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_1002100 : invRung 7 5 20 [1, 0, 0, 2, 1, 0, 0] [2, 1, 0, 1, 2, 1, 1] 3 1 true = ([0, 2, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_1002100 : fieldCube 7 5 20 [0, 2, 0, 2, 0, 1, 1] = [0, 2, 2, 0, 2, 1, 0] := by
  decide

theorem demoM_1002100 : fieldMul 7 5 20 [0, 2, 2, 0, 2, 1, 0] [1, 0, 0, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002100 : mirrorTrits [0, 2, 2, 0, 2, 1, 0] = [0, 1, 1, 0, 1, 2, 0] := by
  decide

theorem demoInv_1002100 : specInv 7 5 20 [1, 0, 0, 2, 1, 0, 0] = some [0, 1, 1, 0, 1, 2, 0] :=
  specInv_mirror_7 [1, 0, 0, 2, 1, 0, 0] [2, 1, 0, 1, 2, 1, 1] [0, 2, 0, 2, 0, 1, 1] [0, 2, 2, 0, 2, 1, 0] [0, 1, 1, 0, 1, 2, 0] demoR1_1002100 demoR2_1002100 demoC_1002100 demoM_1002100 demoMir_1002100

theorem demoR1_2002100 : invRung 7 5 20 [2, 0, 0, 2, 1, 0, 0] [2, 0, 0, 2, 1, 0, 0] 1 2 false = ([1, 0, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_2002100 : invRung 7 5 20 [2, 0, 0, 2, 1, 0, 0] [1, 0, 0, 1, 0, 2, 0] 3 1 true = ([1, 0, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_2002100 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 0, 2] = [2, 0, 2, 0, 2, 1, 2] := by
  decide

theorem demoM_2002100 : fieldMul 7 5 20 [2, 0, 2, 0, 2, 1, 2] [2, 0, 0, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2002100 : specInv 7 5 20 [2, 0, 0, 2, 1, 0, 0] = some [2, 0, 2, 0, 2, 1, 2] :=
  specInv_white_7 [2, 0, 0, 2, 1, 0, 0] [1, 0, 0, 1, 0, 2, 0] [1, 0, 2, 1, 1, 0, 2] [2, 0, 2, 0, 2, 1, 2] demoR1_2002100 demoR2_2002100 demoC_2002100 demoM_2002100

theorem demoR1_0102100 : invRung 7 5 20 [0, 1, 0, 2, 1, 0, 0] [0, 1, 0, 2, 1, 0, 0] 1 2 false = ([2, 0, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_0102100 : invRung 7 5 20 [0, 1, 0, 2, 1, 0, 0] [2, 0, 2, 0, 0, 2, 2] 3 1 true = ([1, 0, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_0102100 : fieldCube 7 5 20 [1, 0, 0, 2, 2, 1, 2] = [1, 2, 1, 1, 0, 1, 0] := by
  decide

theorem demoM_0102100 : fieldMul 7 5 20 [1, 2, 1, 1, 0, 1, 0] [0, 1, 0, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102100 : mirrorTrits [1, 2, 1, 1, 0, 1, 0] = [2, 1, 2, 2, 0, 2, 0] := by
  decide

theorem demoInv_0102100 : specInv 7 5 20 [0, 1, 0, 2, 1, 0, 0] = some [2, 1, 2, 2, 0, 2, 0] :=
  specInv_mirror_7 [0, 1, 0, 2, 1, 0, 0] [2, 0, 2, 0, 0, 2, 2] [1, 0, 0, 2, 2, 1, 2] [1, 2, 1, 1, 0, 1, 0] [2, 1, 2, 2, 0, 2, 0] demoR1_0102100 demoR2_0102100 demoC_0102100 demoM_0102100 demoMir_0102100

theorem demoR1_1102100 : invRung 7 5 20 [1, 1, 0, 2, 1, 0, 0] [1, 1, 0, 2, 1, 0, 0] 1 2 false = ([1, 1, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_1102100 : invRung 7 5 20 [1, 1, 0, 2, 1, 0, 0] [1, 1, 1, 2, 0, 2, 1] 3 1 true = ([2, 0, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_1102100 : fieldCube 7 5 20 [2, 0, 0, 0, 1, 2, 2] = [1, 2, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_1102100 : fieldMul 7 5 20 [1, 2, 0, 0, 1, 2, 1] [1, 1, 0, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102100 : mirrorTrits [1, 2, 0, 0, 1, 2, 1] = [2, 1, 0, 0, 2, 1, 2] := by
  decide

theorem demoInv_1102100 : specInv 7 5 20 [1, 1, 0, 2, 1, 0, 0] = some [2, 1, 0, 0, 2, 1, 2] :=
  specInv_mirror_7 [1, 1, 0, 2, 1, 0, 0] [1, 1, 1, 2, 0, 2, 1] [2, 0, 0, 0, 1, 2, 2] [1, 2, 0, 0, 1, 2, 1] [2, 1, 0, 0, 2, 1, 2] demoR1_1102100 demoR2_1102100 demoC_1102100 demoM_1102100 demoMir_1102100

theorem demoR1_2102100 : invRung 7 5 20 [2, 1, 0, 2, 1, 0, 0] [2, 1, 0, 2, 1, 0, 0] 1 2 false = ([0, 2, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2102100 : invRung 7 5 20 [2, 1, 0, 2, 1, 0, 0] [0, 2, 0, 1, 1, 2, 2] 3 1 true = ([1, 0, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2102100 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 2, 0] = [1, 1, 0, 2, 2, 2, 0] := by
  decide

theorem demoM_2102100 : fieldMul 7 5 20 [1, 1, 0, 2, 2, 2, 0] [2, 1, 0, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2102100 : specInv 7 5 20 [2, 1, 0, 2, 1, 0, 0] = some [1, 1, 0, 2, 2, 2, 0] :=
  specInv_white_7 [2, 1, 0, 2, 1, 0, 0] [0, 2, 0, 1, 1, 2, 2] [1, 0, 0, 1, 2, 2, 0] [1, 1, 0, 2, 2, 2, 0] demoR1_2102100 demoR2_2102100 demoC_2102100 demoM_2102100

theorem demoR1_0202100 : invRung 7 5 20 [0, 2, 0, 2, 1, 0, 0] [0, 2, 0, 2, 1, 0, 0] 1 2 false = ([0, 0, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_0202100 : invRung 7 5 20 [0, 2, 0, 2, 1, 0, 0] [0, 0, 1, 1, 0, 1, 0] 3 1 true = ([0, 0, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0202100 : fieldCube 7 5 20 [0, 0, 2, 2, 0, 1, 1] = [0, 2, 2, 1, 2, 1, 2] := by
  decide

theorem demoM_0202100 : fieldMul 7 5 20 [0, 2, 2, 1, 2, 1, 2] [0, 2, 0, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202100 : mirrorTrits [0, 2, 2, 1, 2, 1, 2] = [0, 1, 1, 2, 1, 2, 1] := by
  decide

theorem demoInv_0202100 : specInv 7 5 20 [0, 2, 0, 2, 1, 0, 0] = some [0, 1, 1, 2, 1, 2, 1] :=
  specInv_mirror_7 [0, 2, 0, 2, 1, 0, 0] [0, 0, 1, 1, 0, 1, 0] [0, 0, 2, 2, 0, 1, 1] [0, 2, 2, 1, 2, 1, 2] [0, 1, 1, 2, 1, 2, 1] demoR1_0202100 demoR2_0202100 demoC_0202100 demoM_0202100 demoMir_0202100

theorem demoR1_1202100 : invRung 7 5 20 [1, 2, 0, 2, 1, 0, 0] [1, 2, 0, 2, 1, 0, 0] 1 2 false = ([0, 2, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_1202100 : invRung 7 5 20 [1, 2, 0, 2, 1, 0, 0] [0, 2, 0, 1, 2, 0, 2] 3 1 true = ([2, 1, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_1202100 : fieldCube 7 5 20 [2, 1, 1, 0, 0, 2, 0] = [1, 2, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_1202100 : fieldMul 7 5 20 [1, 2, 2, 1, 2, 2, 2] [1, 2, 0, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1202100 : specInv 7 5 20 [1, 2, 0, 2, 1, 0, 0] = some [1, 2, 2, 1, 2, 2, 2] :=
  specInv_white_7 [1, 2, 0, 2, 1, 0, 0] [0, 2, 0, 1, 2, 0, 2] [2, 1, 1, 0, 0, 2, 0] [1, 2, 2, 1, 2, 2, 2] demoR1_1202100 demoR2_1202100 demoC_1202100 demoM_1202100

theorem demoR1_2202100 : invRung 7 5 20 [2, 2, 0, 2, 1, 0, 0] [2, 2, 0, 2, 1, 0, 0] 1 2 false = ([2, 0, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_2202100 : invRung 7 5 20 [2, 2, 0, 2, 1, 0, 0] [2, 0, 1, 0, 2, 1, 0] 3 1 true = ([1, 0, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_2202100 : fieldCube 7 5 20 [1, 0, 2, 0, 1, 2, 2] = [0, 2, 0, 0, 1, 2, 0] := by
  decide

theorem demoM_2202100 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 2, 0] [2, 2, 0, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2202100 : specInv 7 5 20 [2, 2, 0, 2, 1, 0, 0] = some [0, 2, 0, 0, 1, 2, 0] :=
  specInv_white_7 [2, 2, 0, 2, 1, 0, 0] [2, 0, 1, 0, 2, 1, 0] [1, 0, 2, 0, 1, 2, 2] [0, 2, 0, 0, 1, 2, 0] demoR1_2202100 demoR2_2202100 demoC_2202100 demoM_2202100

theorem demoR1_0012100 : invRung 7 5 20 [0, 0, 1, 2, 1, 0, 0] [0, 0, 1, 2, 1, 0, 0] 1 2 false = ([0, 2, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_0012100 : invRung 7 5 20 [0, 0, 1, 2, 1, 0, 0] [0, 2, 1, 2, 2, 0, 1] 3 1 true = ([1, 0, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_0012100 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 1, 2] = [1, 2, 1, 1, 0, 1, 2] := by
  decide

theorem demoM_0012100 : fieldMul 7 5 20 [1, 2, 1, 1, 0, 1, 2] [0, 0, 1, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0012100 : specInv 7 5 20 [0, 0, 1, 2, 1, 0, 0] = some [1, 2, 1, 1, 0, 1, 2] :=
  specInv_white_7 [0, 0, 1, 2, 1, 0, 0] [0, 2, 1, 2, 2, 0, 1] [1, 0, 2, 2, 2, 1, 2] [1, 2, 1, 1, 0, 1, 2] demoR1_0012100 demoR2_0012100 demoC_0012100 demoM_0012100

theorem demoR1_1012100 : invRung 7 5 20 [1, 0, 1, 2, 1, 0, 0] [1, 0, 1, 2, 1, 0, 0] 1 2 false = ([1, 2, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_1012100 : invRung 7 5 20 [1, 0, 1, 2, 1, 0, 0] [1, 2, 0, 0, 0, 1, 2] 3 1 true = ([2, 2, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_1012100 : fieldCube 7 5 20 [2, 2, 1, 2, 1, 2, 0] = [0, 0, 1, 0, 2, 2, 0] := by
  decide

theorem demoM_1012100 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 2, 0] [1, 0, 1, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1012100 : mirrorTrits [0, 0, 1, 0, 2, 2, 0] = [0, 0, 2, 0, 1, 1, 0] := by
  decide

theorem demoInv_1012100 : specInv 7 5 20 [1, 0, 1, 2, 1, 0, 0] = some [0, 0, 2, 0, 1, 1, 0] :=
  specInv_mirror_7 [1, 0, 1, 2, 1, 0, 0] [1, 2, 0, 0, 0, 1, 2] [2, 2, 1, 2, 1, 2, 0] [0, 0, 1, 0, 2, 2, 0] [0, 0, 2, 0, 1, 1, 0] demoR1_1012100 demoR2_1012100 demoC_1012100 demoM_1012100 demoMir_1012100

theorem demoR1_2012100 : invRung 7 5 20 [2, 0, 1, 2, 1, 0, 0] [2, 0, 1, 2, 1, 0, 0] 1 2 false = ([0, 2, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2012100 : invRung 7 5 20 [2, 0, 1, 2, 1, 0, 0] [0, 2, 0, 1, 1, 2, 0] 3 1 true = ([2, 2, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_2012100 : fieldCube 7 5 20 [2, 2, 2, 1, 1, 1, 0] = [1, 2, 2, 0, 1, 0, 2] := by
  decide

theorem demoM_2012100 : fieldMul 7 5 20 [1, 2, 2, 0, 1, 0, 2] [2, 0, 1, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012100 : mirrorTrits [1, 2, 2, 0, 1, 0, 2] = [2, 1, 1, 0, 2, 0, 1] := by
  decide

theorem demoInv_2012100 : specInv 7 5 20 [2, 0, 1, 2, 1, 0, 0] = some [2, 1, 1, 0, 2, 0, 1] :=
  specInv_mirror_7 [2, 0, 1, 2, 1, 0, 0] [0, 2, 0, 1, 1, 2, 0] [2, 2, 2, 1, 1, 1, 0] [1, 2, 2, 0, 1, 0, 2] [2, 1, 1, 0, 2, 0, 1] demoR1_2012100 demoR2_2012100 demoC_2012100 demoM_2012100 demoMir_2012100

theorem demoR1_0112100 : invRung 7 5 20 [0, 1, 1, 2, 1, 0, 0] [0, 1, 1, 2, 1, 0, 0] 1 2 false = ([2, 2, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_0112100 : invRung 7 5 20 [0, 1, 1, 2, 1, 0, 0] [2, 2, 1, 1, 1, 1, 0] 3 1 true = ([2, 1, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_0112100 : fieldCube 7 5 20 [2, 1, 1, 0, 2, 0, 0] = [2, 2, 0, 0, 0, 2, 0] := by
  decide

theorem demoM_0112100 : fieldMul 7 5 20 [2, 2, 0, 0, 0, 2, 0] [0, 1, 1, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0112100 : specInv 7 5 20 [0, 1, 1, 2, 1, 0, 0] = some [2, 2, 0, 0, 0, 2, 0] :=
  specInv_white_7 [0, 1, 1, 2, 1, 0, 0] [2, 2, 1, 1, 1, 1, 0] [2, 1, 1, 0, 2, 0, 0] [2, 2, 0, 0, 0, 2, 0] demoR1_0112100 demoR2_0112100 demoC_0112100 demoM_0112100

theorem demoR1_1112100 : invRung 7 5 20 [1, 1, 1, 2, 1, 0, 0] [1, 1, 1, 2, 1, 0, 0] 1 2 false = ([1, 1, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_1112100 : invRung 7 5 20 [1, 1, 1, 2, 1, 0, 0] [1, 1, 1, 1, 0, 0, 2] 3 1 true = ([0, 1, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_1112100 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 2, 0] = [1, 0, 1, 2, 2, 2, 1] := by
  decide

theorem demoM_1112100 : fieldMul 7 5 20 [1, 0, 1, 2, 2, 2, 1] [1, 1, 1, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112100 : mirrorTrits [1, 0, 1, 2, 2, 2, 1] = [2, 0, 2, 1, 1, 1, 2] := by
  decide

theorem demoInv_1112100 : specInv 7 5 20 [1, 1, 1, 2, 1, 0, 0] = some [2, 0, 2, 1, 1, 1, 2] :=
  specInv_mirror_7 [1, 1, 1, 2, 1, 0, 0] [1, 1, 1, 1, 0, 0, 2] [0, 1, 2, 2, 1, 2, 0] [1, 0, 1, 2, 2, 2, 1] [2, 0, 2, 1, 1, 1, 2] demoR1_1112100 demoR2_1112100 demoC_1112100 demoM_1112100 demoMir_1112100

theorem demoR1_2112100 : invRung 7 5 20 [2, 1, 1, 2, 1, 0, 0] [2, 1, 1, 2, 1, 0, 0] 1 2 false = ([0, 2, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_2112100 : invRung 7 5 20 [2, 1, 1, 2, 1, 0, 0] [0, 2, 1, 0, 2, 1, 1] 3 1 true = ([0, 1, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_2112100 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 1, 0] = [2, 1, 2, 1, 1, 2, 0] := by
  decide

theorem demoM_2112100 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 2, 0] [2, 1, 1, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112100 : mirrorTrits [2, 1, 2, 1, 1, 2, 0] = [1, 2, 1, 2, 2, 1, 0] := by
  decide

theorem demoInv_2112100 : specInv 7 5 20 [2, 1, 1, 2, 1, 0, 0] = some [1, 2, 1, 2, 2, 1, 0] :=
  specInv_mirror_7 [2, 1, 1, 2, 1, 0, 0] [0, 2, 1, 0, 2, 1, 1] [0, 1, 1, 1, 0, 1, 0] [2, 1, 2, 1, 1, 2, 0] [1, 2, 1, 2, 2, 1, 0] demoR1_2112100 demoR2_2112100 demoC_2112100 demoM_2112100 demoMir_2112100

theorem demoR1_0212100 : invRung 7 5 20 [0, 2, 1, 2, 1, 0, 0] [0, 2, 1, 2, 1, 0, 0] 1 2 false = ([2, 1, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0212100 : invRung 7 5 20 [0, 2, 1, 2, 1, 0, 0] [2, 1, 0, 0, 2, 1, 2] 3 1 true = ([1, 1, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0212100 : fieldCube 7 5 20 [1, 1, 1, 2, 2, 0, 2] = [0, 1, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_0212100 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 0, 2] [0, 2, 1, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212100 : mirrorTrits [0, 1, 0, 2, 2, 0, 2] = [0, 2, 0, 1, 1, 0, 1] := by
  decide

theorem demoInv_0212100 : specInv 7 5 20 [0, 2, 1, 2, 1, 0, 0] = some [0, 2, 0, 1, 1, 0, 1] :=
  specInv_mirror_7 [0, 2, 1, 2, 1, 0, 0] [2, 1, 0, 0, 2, 1, 2] [1, 1, 1, 2, 2, 0, 2] [0, 1, 0, 2, 2, 0, 2] [0, 2, 0, 1, 1, 0, 1] demoR1_0212100 demoR2_0212100 demoC_0212100 demoM_0212100 demoMir_0212100

theorem demoR1_1212100 : invRung 7 5 20 [1, 2, 1, 2, 1, 0, 0] [1, 2, 1, 2, 1, 0, 0] 1 2 false = ([2, 0, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1212100 : invRung 7 5 20 [1, 2, 1, 2, 1, 0, 0] [2, 0, 1, 0, 1, 0, 0] 3 1 true = ([0, 0, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_1212100 : fieldCube 7 5 20 [0, 0, 1, 1, 0, 0, 1] = [1, 1, 0, 1, 1, 2, 2] := by
  decide

theorem demoM_1212100 : fieldMul 7 5 20 [1, 1, 0, 1, 1, 2, 2] [1, 2, 1, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1212100 : specInv 7 5 20 [1, 2, 1, 2, 1, 0, 0] = some [1, 1, 0, 1, 1, 2, 2] :=
  specInv_white_7 [1, 2, 1, 2, 1, 0, 0] [2, 0, 1, 0, 1, 0, 0] [0, 0, 1, 1, 0, 0, 1] [1, 1, 0, 1, 1, 2, 2] demoR1_1212100 demoR2_1212100 demoC_1212100 demoM_1212100

theorem demoR1_2212100 : invRung 7 5 20 [2, 2, 1, 2, 1, 0, 0] [2, 2, 1, 2, 1, 0, 0] 1 2 false = ([1, 0, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_2212100 : invRung 7 5 20 [2, 2, 1, 2, 1, 0, 0] [1, 0, 1, 1, 0, 0, 1] 3 1 true = ([1, 0, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2212100 : fieldCube 7 5 20 [1, 0, 1, 1, 0, 2, 0] = [1, 2, 0, 0, 2, 0, 2] := by
  decide

theorem demoM_2212100 : fieldMul 7 5 20 [1, 2, 0, 0, 2, 0, 2] [2, 2, 1, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212100 : mirrorTrits [1, 2, 0, 0, 2, 0, 2] = [2, 1, 0, 0, 1, 0, 1] := by
  decide

theorem demoInv_2212100 : specInv 7 5 20 [2, 2, 1, 2, 1, 0, 0] = some [2, 1, 0, 0, 1, 0, 1] :=
  specInv_mirror_7 [2, 2, 1, 2, 1, 0, 0] [1, 0, 1, 1, 0, 0, 1] [1, 0, 1, 1, 0, 2, 0] [1, 2, 0, 0, 2, 0, 2] [2, 1, 0, 0, 1, 0, 1] demoR1_2212100 demoR2_2212100 demoC_2212100 demoM_2212100 demoMir_2212100

theorem demoR1_0022100 : invRung 7 5 20 [0, 0, 2, 2, 1, 0, 0] [0, 0, 2, 2, 1, 0, 0] 1 2 false = ([1, 1, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_0022100 : invRung 7 5 20 [0, 0, 2, 2, 1, 0, 0] [1, 1, 0, 0, 0, 2, 2] 3 1 true = ([0, 0, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0022100 : fieldCube 7 5 20 [0, 0, 0, 0, 0, 0, 1] = [0, 1, 2, 1, 1, 1, 1] := by
  decide

theorem demoM_0022100 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 1, 1] [0, 0, 2, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022100 : mirrorTrits [0, 1, 2, 1, 1, 1, 1] = [0, 2, 1, 2, 2, 2, 2] := by
  decide

theorem demoInv_0022100 : specInv 7 5 20 [0, 0, 2, 2, 1, 0, 0] = some [0, 2, 1, 2, 2, 2, 2] :=
  specInv_mirror_7 [0, 0, 2, 2, 1, 0, 0] [1, 1, 0, 0, 0, 2, 2] [0, 0, 0, 0, 0, 0, 1] [0, 1, 2, 1, 1, 1, 1] [0, 2, 1, 2, 2, 2, 2] demoR1_0022100 demoR2_0022100 demoC_0022100 demoM_0022100 demoMir_0022100

theorem demoR1_1022100 : invRung 7 5 20 [1, 0, 2, 2, 1, 0, 0] [1, 0, 2, 2, 1, 0, 0] 1 2 false = ([1, 0, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_1022100 : invRung 7 5 20 [1, 0, 2, 2, 1, 0, 0] [1, 0, 0, 0, 2, 1, 0] 3 1 true = ([2, 1, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_1022100 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 1, 2] = [0, 1, 2, 1, 0, 1, 0] := by
  decide

theorem demoM_1022100 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 1, 0] [1, 0, 2, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1022100 : specInv 7 5 20 [1, 0, 2, 2, 1, 0, 0] = some [0, 1, 2, 1, 0, 1, 0] :=
  specInv_white_7 [1, 0, 2, 2, 1, 0, 0] [1, 0, 0, 0, 2, 1, 0] [2, 1, 1, 0, 1, 1, 2] [0, 1, 2, 1, 0, 1, 0] demoR1_1022100 demoR2_1022100 demoC_1022100 demoM_1022100

theorem demoR1_2022100 : invRung 7 5 20 [2, 0, 2, 2, 1, 0, 0] [2, 0, 2, 2, 1, 0, 0] 1 2 false = ([2, 1, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_2022100 : invRung 7 5 20 [2, 0, 2, 2, 1, 0, 0] [2, 1, 1, 2, 0, 2, 2] 3 1 true = ([2, 0, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_2022100 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 2, 0] = [0, 0, 1, 1, 2, 2, 1] := by
  decide

theorem demoM_2022100 : fieldMul 7 5 20 [0, 0, 1, 1, 2, 2, 1] [2, 0, 2, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2022100 : specInv 7 5 20 [2, 0, 2, 2, 1, 0, 0] = some [0, 0, 1, 1, 2, 2, 1] :=
  specInv_white_7 [2, 0, 2, 2, 1, 0, 0] [2, 1, 1, 2, 0, 2, 2] [2, 0, 2, 2, 1, 2, 0] [0, 0, 1, 1, 2, 2, 1] demoR1_2022100 demoR2_2022100 demoC_2022100 demoM_2022100

theorem demoR1_0122100 : invRung 7 5 20 [0, 1, 2, 2, 1, 0, 0] [0, 1, 2, 2, 1, 0, 0] 1 2 false = ([1, 0, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0122100 : invRung 7 5 20 [0, 1, 2, 2, 1, 0, 0] [1, 0, 1, 2, 2, 2, 1] 3 1 true = ([2, 2, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0122100 : fieldCube 7 5 20 [2, 2, 1, 0, 1, 2, 1] = [1, 1, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_0122100 : fieldMul 7 5 20 [1, 1, 1, 1, 0, 1, 1] [0, 1, 2, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0122100 : specInv 7 5 20 [0, 1, 2, 2, 1, 0, 0] = some [1, 1, 1, 1, 0, 1, 1] :=
  specInv_white_7 [0, 1, 2, 2, 1, 0, 0] [1, 0, 1, 2, 2, 2, 1] [2, 2, 1, 0, 1, 2, 1] [1, 1, 1, 1, 0, 1, 1] demoR1_0122100 demoR2_0122100 demoC_0122100 demoM_0122100

theorem demoR1_1122100 : invRung 7 5 20 [1, 1, 2, 2, 1, 0, 0] [1, 1, 2, 2, 1, 0, 0] 1 2 false = ([2, 0, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_1122100 : invRung 7 5 20 [1, 1, 2, 2, 1, 0, 0] [2, 0, 0, 0, 0, 0, 2] 3 1 true = ([0, 1, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_1122100 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 1, 1] = [0, 0, 2, 0, 2, 2, 1] := by
  decide

theorem demoM_1122100 : fieldMul 7 5 20 [0, 0, 2, 0, 2, 2, 1] [1, 1, 2, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1122100 : specInv 7 5 20 [1, 1, 2, 2, 1, 0, 0] = some [0, 0, 2, 0, 2, 2, 1] :=
  specInv_white_7 [1, 1, 2, 2, 1, 0, 0] [2, 0, 0, 0, 0, 0, 2] [0, 1, 0, 2, 1, 1, 1] [0, 0, 2, 0, 2, 2, 1] demoR1_1122100 demoR2_1122100 demoC_1122100 demoM_1122100

theorem demoR1_2122100 : invRung 7 5 20 [2, 1, 2, 2, 1, 0, 0] [2, 1, 2, 2, 1, 0, 0] 1 2 false = ([0, 1, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_2122100 : invRung 7 5 20 [2, 1, 2, 2, 1, 0, 0] [0, 1, 2, 2, 0, 2, 1] 3 1 true = ([0, 1, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_2122100 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 2, 2] = [2, 0, 0, 2, 1, 0, 1] := by
  decide

theorem demoM_2122100 : fieldMul 7 5 20 [2, 0, 0, 2, 1, 0, 1] [2, 1, 2, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122100 : mirrorTrits [2, 0, 0, 2, 1, 0, 1] = [1, 0, 0, 1, 2, 0, 2] := by
  decide

theorem demoInv_2122100 : specInv 7 5 20 [2, 1, 2, 2, 1, 0, 0] = some [1, 0, 0, 1, 2, 0, 2] :=
  specInv_mirror_7 [2, 1, 2, 2, 1, 0, 0] [0, 1, 2, 2, 0, 2, 1] [0, 1, 2, 0, 2, 2, 2] [2, 0, 0, 2, 1, 0, 1] [1, 0, 0, 1, 2, 0, 2] demoR1_2122100 demoR2_2122100 demoC_2122100 demoM_2122100 demoMir_2122100

theorem demoR1_0222100 : invRung 7 5 20 [0, 2, 2, 2, 1, 0, 0] [0, 2, 2, 2, 1, 0, 0] 1 2 false = ([0, 0, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_0222100 : invRung 7 5 20 [0, 2, 2, 2, 1, 0, 0] [0, 0, 2, 1, 0, 2, 0] 3 1 true = ([0, 2, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0222100 : fieldCube 7 5 20 [0, 2, 2, 0, 0, 0, 1] = [0, 1, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_0222100 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 1, 0] [0, 2, 2, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222100 : mirrorTrits [0, 1, 2, 0, 1, 1, 0] = [0, 2, 1, 0, 2, 2, 0] := by
  decide

theorem demoInv_0222100 : specInv 7 5 20 [0, 2, 2, 2, 1, 0, 0] = some [0, 2, 1, 0, 2, 2, 0] :=
  specInv_mirror_7 [0, 2, 2, 2, 1, 0, 0] [0, 0, 2, 1, 0, 2, 0] [0, 2, 2, 0, 0, 0, 1] [0, 1, 2, 0, 1, 1, 0] [0, 2, 1, 0, 2, 2, 0] demoR1_0222100 demoR2_0222100 demoC_0222100 demoM_0222100 demoMir_0222100

theorem demoR1_1222100 : invRung 7 5 20 [1, 2, 2, 2, 1, 0, 0] [1, 2, 2, 2, 1, 0, 0] 1 2 false = ([2, 2, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_1222100 : invRung 7 5 20 [1, 2, 2, 2, 1, 0, 0] [2, 2, 0, 1, 2, 1, 2] 3 1 true = ([1, 2, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1222100 : fieldCube 7 5 20 [1, 2, 0, 0, 1, 1, 1] = [2, 0, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_1222100 : fieldMul 7 5 20 [2, 0, 0, 1, 2, 0, 1] [1, 2, 2, 2, 1, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222100 : mirrorTrits [2, 0, 0, 1, 2, 0, 1] = [1, 0, 0, 2, 1, 0, 2] := by
  decide

theorem demoInv_1222100 : specInv 7 5 20 [1, 2, 2, 2, 1, 0, 0] = some [1, 0, 0, 2, 1, 0, 2] :=
  specInv_mirror_7 [1, 2, 2, 2, 1, 0, 0] [2, 2, 0, 1, 2, 1, 2] [1, 2, 0, 0, 1, 1, 1] [2, 0, 0, 1, 2, 0, 1] [1, 0, 0, 2, 1, 0, 2] demoR1_1222100 demoR2_1222100 demoC_1222100 demoM_1222100 demoMir_1222100

theorem demoR1_2222100 : invRung 7 5 20 [2, 2, 2, 2, 1, 0, 0] [2, 2, 2, 2, 1, 0, 0] 1 2 false = ([0, 1, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2222100 : invRung 7 5 20 [2, 2, 2, 2, 1, 0, 0] [0, 1, 0, 1, 0, 0, 2] 3 1 true = ([2, 1, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_2222100 : fieldCube 7 5 20 [2, 1, 2, 0, 0, 2, 0] = [1, 2, 2, 1, 2, 2, 0] := by
  decide

theorem demoM_2222100 : fieldMul 7 5 20 [1, 2, 2, 1, 2, 2, 0] [2, 2, 2, 2, 1, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2222100 : specInv 7 5 20 [2, 2, 2, 2, 1, 0, 0] = some [1, 2, 2, 1, 2, 2, 0] :=
  specInv_white_7 [2, 2, 2, 2, 1, 0, 0] [0, 1, 0, 1, 0, 0, 2] [2, 1, 2, 0, 0, 2, 0] [1, 2, 2, 1, 2, 2, 0] demoR1_2222100 demoR2_2222100 demoC_2222100 demoM_2222100

theorem demoR1_0000200 : invRung 7 5 20 [0, 0, 0, 0, 2, 0, 0] [0, 0, 0, 0, 2, 0, 0] 1 2 false = ([2, 0, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_0000200 : invRung 7 5 20 [0, 0, 0, 0, 2, 0, 0] [2, 0, 1, 1, 0, 1, 0] 3 1 true = ([1, 0, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0000200 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 1, 2] = [0, 2, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_0000200 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 0, 0] [0, 0, 0, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000200 : mirrorTrits [0, 2, 0, 1, 0, 0, 0] = [0, 1, 0, 2, 0, 0, 0] := by
  decide

theorem demoInv_0000200 : specInv 7 5 20 [0, 0, 0, 0, 2, 0, 0] = some [0, 1, 0, 2, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 0, 0, 2, 0, 0] [2, 0, 1, 1, 0, 1, 0] [1, 0, 0, 1, 2, 1, 2] [0, 2, 0, 1, 0, 0, 0] [0, 1, 0, 2, 0, 0, 0] demoR1_0000200 demoR2_0000200 demoC_0000200 demoM_0000200 demoMir_0000200

theorem demoR1_1000200 : invRung 7 5 20 [1, 0, 0, 0, 2, 0, 0] [1, 0, 0, 0, 2, 0, 0] 1 2 false = ([2, 1, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_1000200 : invRung 7 5 20 [1, 0, 0, 0, 2, 0, 0] [2, 1, 1, 1, 0, 0, 2] 3 1 true = ([1, 2, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_1000200 : fieldCube 7 5 20 [1, 2, 2, 0, 1, 0, 1] = [1, 2, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_1000200 : fieldMul 7 5 20 [1, 2, 2, 1, 1, 2, 1] [1, 0, 0, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1000200 : specInv 7 5 20 [1, 0, 0, 0, 2, 0, 0] = some [1, 2, 2, 1, 1, 2, 1] :=
  specInv_white_7 [1, 0, 0, 0, 2, 0, 0] [2, 1, 1, 1, 0, 0, 2] [1, 2, 2, 0, 1, 0, 1] [1, 2, 2, 1, 1, 2, 1] demoR1_1000200 demoR2_1000200 demoC_1000200 demoM_1000200

theorem demoR1_2000200 : invRung 7 5 20 [2, 0, 0, 0, 2, 0, 0] [2, 0, 0, 0, 2, 0, 0] 1 2 false = ([1, 2, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2000200 : invRung 7 5 20 [2, 0, 0, 0, 2, 0, 0] [1, 2, 2, 1, 0, 0, 2] 3 1 true = ([2, 2, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2000200 : fieldCube 7 5 20 [2, 2, 2, 2, 0, 1, 0] = [2, 1, 0, 2, 1, 0, 1] := by
  decide

theorem demoM_2000200 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 0, 1] [2, 0, 0, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000200 : mirrorTrits [2, 1, 0, 2, 1, 0, 1] = [1, 2, 0, 1, 2, 0, 2] := by
  decide

theorem demoInv_2000200 : specInv 7 5 20 [2, 0, 0, 0, 2, 0, 0] = some [1, 2, 0, 1, 2, 0, 2] :=
  specInv_mirror_7 [2, 0, 0, 0, 2, 0, 0] [1, 2, 2, 1, 0, 0, 2] [2, 2, 2, 2, 0, 1, 0] [2, 1, 0, 2, 1, 0, 1] [1, 2, 0, 1, 2, 0, 2] demoR1_2000200 demoR2_2000200 demoC_2000200 demoM_2000200 demoMir_2000200

theorem demoR1_0100200 : invRung 7 5 20 [0, 1, 0, 0, 2, 0, 0] [0, 1, 0, 0, 2, 0, 0] 1 2 false = ([2, 2, 2, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_0100200 : invRung 7 5 20 [0, 1, 0, 0, 2, 0, 0] [2, 2, 2, 0, 2, 2, 0] 3 1 true = ([1, 0, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0100200 : fieldCube 7 5 20 [1, 0, 0, 0, 2, 1, 0] = [2, 0, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_0100200 : fieldMul 7 5 20 [2, 0, 1, 2, 1, 0, 1] [0, 1, 0, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100200 : mirrorTrits [2, 0, 1, 2, 1, 0, 1] = [1, 0, 2, 1, 2, 0, 2] := by
  decide

theorem demoInv_0100200 : specInv 7 5 20 [0, 1, 0, 0, 2, 0, 0] = some [1, 0, 2, 1, 2, 0, 2] :=
  specInv_mirror_7 [0, 1, 0, 0, 2, 0, 0] [2, 2, 2, 0, 2, 2, 0] [1, 0, 0, 0, 2, 1, 0] [2, 0, 1, 2, 1, 0, 1] [1, 0, 2, 1, 2, 0, 2] demoR1_0100200 demoR2_0100200 demoC_0100200 demoM_0100200 demoMir_0100200

theorem demoR1_1100200 : invRung 7 5 20 [1, 1, 0, 0, 2, 0, 0] [1, 1, 0, 0, 2, 0, 0] 1 2 false = ([2, 0, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_1100200 : invRung 7 5 20 [1, 1, 0, 0, 2, 0, 0] [2, 0, 1, 0, 2, 0, 1] 3 1 true = ([1, 1, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_1100200 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 0, 0] = [1, 0, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_1100200 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 0, 1] [1, 1, 0, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1100200 : specInv 7 5 20 [1, 1, 0, 0, 2, 0, 0] = some [1, 0, 0, 1, 0, 0, 1] :=
  specInv_white_7 [1, 1, 0, 0, 2, 0, 0] [2, 0, 1, 0, 2, 0, 1] [1, 1, 1, 0, 0, 0, 0] [1, 0, 0, 1, 0, 0, 1] demoR1_1100200 demoR2_1100200 demoC_1100200 demoM_1100200

theorem demoR1_2100200 : invRung 7 5 20 [2, 1, 0, 0, 2, 0, 0] [2, 1, 0, 0, 2, 0, 0] 1 2 false = ([0, 0, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_2100200 : invRung 7 5 20 [2, 1, 0, 0, 2, 0, 0] [0, 0, 0, 2, 2, 1, 0] 3 1 true = ([2, 1, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_2100200 : fieldCube 7 5 20 [2, 1, 1, 2, 0, 0, 1] = [1, 1, 1, 2, 1, 0, 2] := by
  decide

theorem demoM_2100200 : fieldMul 7 5 20 [1, 1, 1, 2, 1, 0, 2] [2, 1, 0, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100200 : mirrorTrits [1, 1, 1, 2, 1, 0, 2] = [2, 2, 2, 1, 2, 0, 1] := by
  decide

theorem demoInv_2100200 : specInv 7 5 20 [2, 1, 0, 0, 2, 0, 0] = some [2, 2, 2, 1, 2, 0, 1] :=
  specInv_mirror_7 [2, 1, 0, 0, 2, 0, 0] [0, 0, 0, 2, 2, 1, 0] [2, 1, 1, 2, 0, 0, 1] [1, 1, 1, 2, 1, 0, 2] [2, 2, 2, 1, 2, 0, 1] demoR1_2100200 demoR2_2100200 demoC_2100200 demoM_2100200 demoMir_2100200

theorem demoR1_0200200 : invRung 7 5 20 [0, 2, 0, 0, 2, 0, 0] [0, 2, 0, 0, 2, 0, 0] 1 2 false = ([2, 0, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_0200200 : invRung 7 5 20 [0, 2, 0, 0, 2, 0, 0] [2, 0, 2, 1, 0, 1, 2] 3 1 true = ([0, 1, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_0200200 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 2, 2] = [0, 1, 1, 0, 1, 2, 2] := by
  decide

theorem demoM_0200200 : fieldMul 7 5 20 [0, 1, 1, 0, 1, 2, 2] [0, 2, 0, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200200 : mirrorTrits [0, 1, 1, 0, 1, 2, 2] = [0, 2, 2, 0, 2, 1, 1] := by
  decide

theorem demoInv_0200200 : specInv 7 5 20 [0, 2, 0, 0, 2, 0, 0] = some [0, 2, 2, 0, 2, 1, 1] :=
  specInv_mirror_7 [0, 2, 0, 0, 2, 0, 0] [2, 0, 2, 1, 0, 1, 2] [0, 1, 2, 1, 0, 2, 2] [0, 1, 1, 0, 1, 2, 2] [0, 2, 2, 0, 2, 1, 1] demoR1_0200200 demoR2_0200200 demoC_0200200 demoM_0200200 demoMir_0200200

theorem demoR1_1200200 : invRung 7 5 20 [1, 2, 0, 0, 2, 0, 0] [1, 2, 0, 0, 2, 0, 0] 1 2 false = ([2, 2, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_1200200 : invRung 7 5 20 [1, 2, 0, 0, 2, 0, 0] [2, 2, 0, 2, 2, 0, 0] 3 1 true = ([0, 1, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_1200200 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 2, 1] = [2, 2, 1, 1, 0, 2, 0] := by
  decide

theorem demoM_1200200 : fieldMul 7 5 20 [2, 2, 1, 1, 0, 2, 0] [1, 2, 0, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200200 : mirrorTrits [2, 2, 1, 1, 0, 2, 0] = [1, 1, 2, 2, 0, 1, 0] := by
  decide

theorem demoInv_1200200 : specInv 7 5 20 [1, 2, 0, 0, 2, 0, 0] = some [1, 1, 2, 2, 0, 1, 0] :=
  specInv_mirror_7 [1, 2, 0, 0, 2, 0, 0] [2, 2, 0, 2, 2, 0, 0] [0, 1, 2, 0, 2, 2, 1] [2, 2, 1, 1, 0, 2, 0] [1, 1, 2, 2, 0, 1, 0] demoR1_1200200 demoR2_1200200 demoC_1200200 demoM_1200200 demoMir_1200200

theorem demoR1_2200200 : invRung 7 5 20 [2, 2, 0, 0, 2, 0, 0] [2, 2, 0, 0, 2, 0, 0] 1 2 false = ([2, 2, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_2200200 : invRung 7 5 20 [2, 2, 0, 0, 2, 0, 0] [2, 2, 0, 1, 1, 1, 2] 3 1 true = ([0, 1, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2200200 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 1, 1] = [2, 2, 1, 2, 2, 0, 0] := by
  decide

theorem demoM_2200200 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 0, 0] [2, 2, 0, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200200 : mirrorTrits [2, 2, 1, 2, 2, 0, 0] = [1, 1, 2, 1, 1, 0, 0] := by
  decide

theorem demoInv_2200200 : specInv 7 5 20 [2, 2, 0, 0, 2, 0, 0] = some [1, 1, 2, 1, 1, 0, 0] :=
  specInv_mirror_7 [2, 2, 0, 0, 2, 0, 0] [2, 2, 0, 1, 1, 1, 2] [0, 1, 0, 1, 0, 1, 1] [2, 2, 1, 2, 2, 0, 0] [1, 1, 2, 1, 1, 0, 0] demoR1_2200200 demoR2_2200200 demoC_2200200 demoM_2200200 demoMir_2200200

theorem demoR1_0010200 : invRung 7 5 20 [0, 0, 1, 0, 2, 0, 0] [0, 0, 1, 0, 2, 0, 0] 1 2 false = ([0, 2, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_0010200 : invRung 7 5 20 [0, 0, 1, 0, 2, 0, 0] [0, 2, 1, 1, 2, 2, 0] 3 1 true = ([0, 1, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_0010200 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 0, 0] = [0, 0, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_0010200 : fieldMul 7 5 20 [0, 0, 0, 1, 0, 0, 0] [0, 0, 1, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010200 : mirrorTrits [0, 0, 0, 1, 0, 0, 0] = [0, 0, 0, 2, 0, 0, 0] := by
  decide

theorem demoInv_0010200 : specInv 7 5 20 [0, 0, 1, 0, 2, 0, 0] = some [0, 0, 0, 2, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 1, 0, 2, 0, 0] [0, 2, 1, 1, 2, 2, 0] [0, 1, 0, 0, 0, 0, 0] [0, 0, 0, 1, 0, 0, 0] [0, 0, 0, 2, 0, 0, 0] demoR1_0010200 demoR2_0010200 demoC_0010200 demoM_0010200 demoMir_0010200

theorem demoR1_1010200 : invRung 7 5 20 [1, 0, 1, 0, 2, 0, 0] [1, 0, 1, 0, 2, 0, 0] 1 2 false = ([2, 2, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_1010200 : invRung 7 5 20 [1, 0, 1, 0, 2, 0, 0] [2, 2, 1, 2, 1, 1, 0] 3 1 true = ([1, 0, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_1010200 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 1, 1] = [2, 2, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_1010200 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 2, 0] [1, 0, 1, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1010200 : specInv 7 5 20 [1, 0, 1, 0, 2, 0, 0] = some [2, 2, 0, 1, 2, 2, 0] :=
  specInv_white_7 [1, 0, 1, 0, 2, 0, 0] [2, 2, 1, 2, 1, 1, 0] [1, 0, 0, 0, 0, 1, 1] [2, 2, 0, 1, 2, 2, 0] demoR1_1010200 demoR2_1010200 demoC_1010200 demoM_1010200

theorem demoR1_2010200 : invRung 7 5 20 [2, 0, 1, 0, 2, 0, 0] [2, 0, 1, 0, 2, 0, 0] 1 2 false = ([0, 1, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_2010200 : invRung 7 5 20 [2, 0, 1, 0, 2, 0, 0] [0, 1, 2, 2, 2, 0, 2] 3 1 true = ([1, 0, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_2010200 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 1, 2] = [2, 0, 2, 2, 0, 0, 1] := by
  decide

theorem demoM_2010200 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 0, 1] [2, 0, 1, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010200 : mirrorTrits [2, 0, 2, 2, 0, 0, 1] = [1, 0, 1, 1, 0, 0, 2] := by
  decide

theorem demoInv_2010200 : specInv 7 5 20 [2, 0, 1, 0, 2, 0, 0] = some [1, 0, 1, 1, 0, 0, 2] :=
  specInv_mirror_7 [2, 0, 1, 0, 2, 0, 0] [0, 1, 2, 2, 2, 0, 2] [1, 0, 0, 0, 0, 1, 2] [2, 0, 2, 2, 0, 0, 1] [1, 0, 1, 1, 0, 0, 2] demoR1_2010200 demoR2_2010200 demoC_2010200 demoM_2010200 demoMir_2010200

theorem demoR1_0110200 : invRung 7 5 20 [0, 1, 1, 0, 2, 0, 0] [0, 1, 1, 0, 2, 0, 0] 1 2 false = ([2, 0, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_0110200 : invRung 7 5 20 [0, 1, 1, 0, 2, 0, 0] [2, 0, 1, 0, 0, 1, 1] 3 1 true = ([1, 1, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_0110200 : fieldCube 7 5 20 [1, 1, 2, 2, 0, 2, 0] = [2, 2, 1, 1, 2, 1, 0] := by
  decide

theorem demoM_0110200 : fieldMul 7 5 20 [2, 2, 1, 1, 2, 1, 0] [0, 1, 1, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110200 : mirrorTrits [2, 2, 1, 1, 2, 1, 0] = [1, 1, 2, 2, 1, 2, 0] := by
  decide

theorem demoInv_0110200 : specInv 7 5 20 [0, 1, 1, 0, 2, 0, 0] = some [1, 1, 2, 2, 1, 2, 0] :=
  specInv_mirror_7 [0, 1, 1, 0, 2, 0, 0] [2, 0, 1, 0, 0, 1, 1] [1, 1, 2, 2, 0, 2, 0] [2, 2, 1, 1, 2, 1, 0] [1, 1, 2, 2, 1, 2, 0] demoR1_0110200 demoR2_0110200 demoC_0110200 demoM_0110200 demoMir_0110200

theorem demoR1_1110200 : invRung 7 5 20 [1, 1, 1, 0, 2, 0, 0] [1, 1, 1, 0, 2, 0, 0] 1 2 false = ([1, 2, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_1110200 : invRung 7 5 20 [1, 1, 1, 0, 2, 0, 0] [1, 2, 1, 0, 0, 0, 2] 3 1 true = ([0, 2, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_1110200 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 2, 1] = [2, 1, 1, 1, 0, 1, 0] := by
  decide

theorem demoM_1110200 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 1, 0] [1, 1, 1, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1110200 : specInv 7 5 20 [1, 1, 1, 0, 2, 0, 0] = some [2, 1, 1, 1, 0, 1, 0] :=
  specInv_white_7 [1, 1, 1, 0, 2, 0, 0] [1, 2, 1, 0, 0, 0, 2] [0, 2, 0, 0, 1, 2, 1] [2, 1, 1, 1, 0, 1, 0] demoR1_1110200 demoR2_1110200 demoC_1110200 demoM_1110200

theorem demoR1_2110200 : invRung 7 5 20 [2, 1, 1, 0, 2, 0, 0] [2, 1, 1, 0, 2, 0, 0] 1 2 false = ([1, 2, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_2110200 : invRung 7 5 20 [2, 1, 1, 0, 2, 0, 0] [1, 2, 1, 1, 2, 1, 2] 3 1 true = ([2, 1, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_2110200 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 0, 0] = [1, 1, 2, 2, 0, 0, 1] := by
  decide

theorem demoM_2110200 : fieldMul 7 5 20 [1, 1, 2, 2, 0, 0, 1] [2, 1, 1, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2110200 : specInv 7 5 20 [2, 1, 1, 0, 2, 0, 0] = some [1, 1, 2, 2, 0, 0, 1] :=
  specInv_white_7 [2, 1, 1, 0, 2, 0, 0] [1, 2, 1, 1, 2, 1, 2] [2, 1, 0, 2, 1, 0, 0] [1, 1, 2, 2, 0, 0, 1] demoR1_2110200 demoR2_2110200 demoC_2110200 demoM_2110200

theorem demoR1_0210200 : invRung 7 5 20 [0, 2, 1, 0, 2, 0, 0] [0, 2, 1, 0, 2, 0, 0] 1 2 false = ([2, 2, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_0210200 : invRung 7 5 20 [0, 2, 1, 0, 2, 0, 0] [2, 2, 1, 1, 0, 2, 1] 3 1 true = ([0, 2, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_0210200 : fieldCube 7 5 20 [0, 2, 2, 2, 2, 0, 1] = [2, 0, 1, 2, 1, 2, 2] := by
  decide

theorem demoM_0210200 : fieldMul 7 5 20 [2, 0, 1, 2, 1, 2, 2] [0, 2, 1, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210200 : mirrorTrits [2, 0, 1, 2, 1, 2, 2] = [1, 0, 2, 1, 2, 1, 1] := by
  decide

theorem demoInv_0210200 : specInv 7 5 20 [0, 2, 1, 0, 2, 0, 0] = some [1, 0, 2, 1, 2, 1, 1] :=
  specInv_mirror_7 [0, 2, 1, 0, 2, 0, 0] [2, 2, 1, 1, 0, 2, 1] [0, 2, 2, 2, 2, 0, 1] [2, 0, 1, 2, 1, 2, 2] [1, 0, 2, 1, 2, 1, 1] demoR1_0210200 demoR2_0210200 demoC_0210200 demoM_0210200 demoMir_0210200

theorem demoR1_1210200 : invRung 7 5 20 [1, 2, 1, 0, 2, 0, 0] [1, 2, 1, 0, 2, 0, 0] 1 2 false = ([1, 1, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1210200 : invRung 7 5 20 [1, 2, 1, 0, 2, 0, 0] [1, 1, 1, 1, 0, 0, 1] 3 1 true = ([1, 0, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_1210200 : fieldCube 7 5 20 [1, 0, 2, 0, 2, 1, 1] = [2, 1, 0, 0, 2, 1, 1] := by
  decide

theorem demoM_1210200 : fieldMul 7 5 20 [2, 1, 0, 0, 2, 1, 1] [1, 2, 1, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1210200 : specInv 7 5 20 [1, 2, 1, 0, 2, 0, 0] = some [2, 1, 0, 0, 2, 1, 1] :=
  specInv_white_7 [1, 2, 1, 0, 2, 0, 0] [1, 1, 1, 1, 0, 0, 1] [1, 0, 2, 0, 2, 1, 1] [2, 1, 0, 0, 2, 1, 1] demoR1_1210200 demoR2_1210200 demoC_1210200 demoM_1210200

theorem demoR1_2210200 : invRung 7 5 20 [2, 2, 1, 0, 2, 0, 0] [2, 2, 1, 0, 2, 0, 0] 1 2 false = ([0, 0, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_2210200 : invRung 7 5 20 [2, 2, 1, 0, 2, 0, 0] [0, 0, 0, 1, 2, 2, 0] 3 1 true = ([1, 0, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_2210200 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 1, 1] = [1, 0, 2, 2, 2, 2, 2] := by
  decide

theorem demoM_2210200 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 2, 2] [2, 2, 1, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2210200 : specInv 7 5 20 [2, 2, 1, 0, 2, 0, 0] = some [1, 0, 2, 2, 2, 2, 2] :=
  specInv_white_7 [2, 2, 1, 0, 2, 0, 0] [0, 0, 0, 1, 2, 2, 0] [1, 0, 1, 2, 1, 1, 1] [1, 0, 2, 2, 2, 2, 2] demoR1_2210200 demoR2_2210200 demoC_2210200 demoM_2210200

theorem demoR1_0020200 : invRung 7 5 20 [0, 0, 2, 0, 2, 0, 0] [0, 0, 2, 0, 2, 0, 0] 1 2 false = ([1, 0, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_0020200 : invRung 7 5 20 [0, 0, 2, 0, 2, 0, 0] [1, 0, 1, 0, 0, 2, 2] 3 1 true = ([2, 2, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_0020200 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 0, 2] = [2, 1, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_0020200 : fieldMul 7 5 20 [2, 1, 1, 0, 2, 1, 2] [0, 0, 2, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0020200 : specInv 7 5 20 [0, 0, 2, 0, 2, 0, 0] = some [2, 1, 1, 0, 2, 1, 2] :=
  specInv_white_7 [0, 0, 2, 0, 2, 0, 0] [1, 0, 1, 0, 0, 2, 2] [2, 2, 1, 0, 2, 0, 2] [2, 1, 1, 0, 2, 1, 2] demoR1_0020200 demoR2_0020200 demoC_0020200 demoM_0020200

theorem demoR1_1020200 : invRung 7 5 20 [1, 0, 2, 0, 2, 0, 0] [1, 0, 2, 0, 2, 0, 0] 1 2 false = ([1, 2, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_1020200 : invRung 7 5 20 [1, 0, 2, 0, 2, 0, 0] [1, 2, 2, 2, 1, 1, 2] 3 1 true = ([2, 1, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_1020200 : fieldCube 7 5 20 [2, 1, 2, 2, 2, 0, 0] = [1, 2, 2, 0, 0, 1, 1] := by
  decide

theorem demoM_1020200 : fieldMul 7 5 20 [1, 2, 2, 0, 0, 1, 1] [1, 0, 2, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020200 : mirrorTrits [1, 2, 2, 0, 0, 1, 1] = [2, 1, 1, 0, 0, 2, 2] := by
  decide

theorem demoInv_1020200 : specInv 7 5 20 [1, 0, 2, 0, 2, 0, 0] = some [2, 1, 1, 0, 0, 2, 2] :=
  specInv_mirror_7 [1, 0, 2, 0, 2, 0, 0] [1, 2, 2, 2, 1, 1, 2] [2, 1, 2, 2, 2, 0, 0] [1, 2, 2, 0, 0, 1, 1] [2, 1, 1, 0, 0, 2, 2] demoR1_1020200 demoR2_1020200 demoC_1020200 demoM_1020200 demoMir_1020200

theorem demoR1_2020200 : invRung 7 5 20 [2, 0, 2, 0, 2, 0, 0] [2, 0, 2, 0, 2, 0, 0] 1 2 false = ([0, 2, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_2020200 : invRung 7 5 20 [2, 0, 2, 0, 2, 0, 0] [0, 2, 1, 2, 0, 2, 2] 3 1 true = ([2, 2, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_2020200 : fieldCube 7 5 20 [2, 2, 1, 2, 1, 2, 1] = [0, 1, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_2020200 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 0, 1] [2, 0, 2, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020200 : mirrorTrits [0, 1, 0, 1, 0, 0, 1] = [0, 2, 0, 2, 0, 0, 2] := by
  decide

theorem demoInv_2020200 : specInv 7 5 20 [2, 0, 2, 0, 2, 0, 0] = some [0, 2, 0, 2, 0, 0, 2] :=
  specInv_mirror_7 [2, 0, 2, 0, 2, 0, 0] [0, 2, 1, 2, 0, 2, 2] [2, 2, 1, 2, 1, 2, 1] [0, 1, 0, 1, 0, 0, 1] [0, 2, 0, 2, 0, 0, 2] demoR1_2020200 demoR2_2020200 demoC_2020200 demoM_2020200 demoMir_2020200

theorem demoR1_0120200 : invRung 7 5 20 [0, 1, 2, 0, 2, 0, 0] [0, 1, 2, 0, 2, 0, 0] 1 2 false = ([2, 2, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_0120200 : invRung 7 5 20 [0, 1, 2, 0, 2, 0, 0] [2, 2, 2, 1, 2, 1, 0] 3 1 true = ([0, 0, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_0120200 : fieldCube 7 5 20 [0, 0, 2, 2, 1, 2, 2] = [1, 2, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_0120200 : fieldMul 7 5 20 [1, 2, 2, 0, 1, 1, 0] [0, 1, 2, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0120200 : specInv 7 5 20 [0, 1, 2, 0, 2, 0, 0] = some [1, 2, 2, 0, 1, 1, 0] :=
  specInv_white_7 [0, 1, 2, 0, 2, 0, 0] [2, 2, 2, 1, 2, 1, 0] [0, 0, 2, 2, 1, 2, 2] [1, 2, 2, 0, 1, 1, 0] demoR1_0120200 demoR2_0120200 demoC_0120200 demoM_0120200

theorem demoR1_1120200 : invRung 7 5 20 [1, 1, 2, 0, 2, 0, 0] [1, 1, 2, 0, 2, 0, 0] 1 2 false = ([2, 2, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_1120200 : invRung 7 5 20 [1, 1, 2, 0, 2, 0, 0] [2, 2, 1, 1, 2, 1, 0] 3 1 true = ([2, 0, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_1120200 : fieldCube 7 5 20 [2, 0, 2, 0, 2, 0, 1] = [2, 0, 2, 0, 1, 0, 2] := by
  decide

theorem demoM_1120200 : fieldMul 7 5 20 [2, 0, 2, 0, 1, 0, 2] [1, 1, 2, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1120200 : specInv 7 5 20 [1, 1, 2, 0, 2, 0, 0] = some [2, 0, 2, 0, 1, 0, 2] :=
  specInv_white_7 [1, 1, 2, 0, 2, 0, 0] [2, 2, 1, 1, 2, 1, 0] [2, 0, 2, 0, 2, 0, 1] [2, 0, 2, 0, 1, 0, 2] demoR1_1120200 demoR2_1120200 demoC_1120200 demoM_1120200

theorem demoR1_2120200 : invRung 7 5 20 [2, 1, 2, 0, 2, 0, 0] [2, 1, 2, 0, 2, 0, 0] 1 2 false = ([0, 2, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_2120200 : invRung 7 5 20 [2, 1, 2, 0, 2, 0, 0] [0, 2, 0, 1, 0, 2, 0] 3 1 true = ([2, 2, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_2120200 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 1, 1] = [0, 1, 0, 2, 2, 1, 0] := by
  decide

theorem demoM_2120200 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 1, 0] [2, 1, 2, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120200 : mirrorTrits [0, 1, 0, 2, 2, 1, 0] = [0, 2, 0, 1, 1, 2, 0] := by
  decide

theorem demoInv_2120200 : specInv 7 5 20 [2, 1, 2, 0, 2, 0, 0] = some [0, 2, 0, 1, 1, 2, 0] :=
  specInv_mirror_7 [2, 1, 2, 0, 2, 0, 0] [0, 2, 0, 1, 0, 2, 0] [2, 2, 1, 0, 2, 1, 1] [0, 1, 0, 2, 2, 1, 0] [0, 2, 0, 1, 1, 2, 0] demoR1_2120200 demoR2_2120200 demoC_2120200 demoM_2120200 demoMir_2120200

theorem demoR1_0220200 : invRung 7 5 20 [0, 2, 2, 0, 2, 0, 0] [0, 2, 2, 0, 2, 0, 0] 1 2 false = ([2, 1, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0220200 : invRung 7 5 20 [0, 2, 2, 0, 2, 0, 0] [2, 1, 1, 1, 0, 0, 0] 3 1 true = ([1, 2, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_0220200 : fieldCube 7 5 20 [1, 2, 1, 1, 1, 0, 2] = [2, 0, 2, 2, 2, 1, 1] := by
  decide

theorem demoM_0220200 : fieldMul 7 5 20 [2, 0, 2, 2, 2, 1, 1] [0, 2, 2, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0220200 : specInv 7 5 20 [0, 2, 2, 0, 2, 0, 0] = some [2, 0, 2, 2, 2, 1, 1] :=
  specInv_white_7 [0, 2, 2, 0, 2, 0, 0] [2, 1, 1, 1, 0, 0, 0] [1, 2, 1, 1, 1, 0, 2] [2, 0, 2, 2, 2, 1, 1] demoR1_0220200 demoR2_0220200 demoC_0220200 demoM_0220200

theorem demoR1_1220200 : invRung 7 5 20 [1, 2, 2, 0, 2, 0, 0] [1, 2, 2, 0, 2, 0, 0] 1 2 false = ([2, 0, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1220200 : invRung 7 5 20 [1, 2, 2, 0, 2, 0, 0] [2, 0, 1, 0, 1, 0, 1] 3 1 true = ([0, 2, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_1220200 : fieldCube 7 5 20 [0, 2, 2, 0, 2, 1, 2] = [1, 2, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_1220200 : fieldMul 7 5 20 [1, 2, 2, 0, 0, 2, 2] [1, 2, 2, 0, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1220200 : specInv 7 5 20 [1, 2, 2, 0, 2, 0, 0] = some [1, 2, 2, 0, 0, 2, 2] :=
  specInv_white_7 [1, 2, 2, 0, 2, 0, 0] [2, 0, 1, 0, 1, 0, 1] [0, 2, 2, 0, 2, 1, 2] [1, 2, 2, 0, 0, 2, 2] demoR1_1220200 demoR2_1220200 demoC_1220200 demoM_1220200

theorem demoR1_2220200 : invRung 7 5 20 [2, 2, 2, 0, 2, 0, 0] [2, 2, 2, 0, 2, 0, 0] 1 2 false = ([2, 1, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2220200 : invRung 7 5 20 [2, 2, 2, 0, 2, 0, 0] [2, 1, 0, 1, 0, 0, 2] 3 1 true = ([1, 0, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_2220200 : fieldCube 7 5 20 [1, 0, 1, 2, 2, 2, 2] = [2, 0, 2, 1, 1, 2, 0] := by
  decide

theorem demoM_2220200 : fieldMul 7 5 20 [2, 0, 2, 1, 1, 2, 0] [2, 2, 2, 0, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220200 : mirrorTrits [2, 0, 2, 1, 1, 2, 0] = [1, 0, 1, 2, 2, 1, 0] := by
  decide

theorem demoInv_2220200 : specInv 7 5 20 [2, 2, 2, 0, 2, 0, 0] = some [1, 0, 1, 2, 2, 1, 0] :=
  specInv_mirror_7 [2, 2, 2, 0, 2, 0, 0] [2, 1, 0, 1, 0, 0, 2] [1, 0, 1, 2, 2, 2, 2] [2, 0, 2, 1, 1, 2, 0] [1, 0, 1, 2, 2, 1, 0] demoR1_2220200 demoR2_2220200 demoC_2220200 demoM_2220200 demoMir_2220200

theorem demoR1_0001200 : invRung 7 5 20 [0, 0, 0, 1, 2, 0, 0] [0, 0, 0, 1, 2, 0, 0] 1 2 false = ([2, 0, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_0001200 : invRung 7 5 20 [0, 0, 0, 1, 2, 0, 0] [2, 0, 2, 1, 1, 2, 2] 3 1 true = ([1, 0, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0001200 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 2, 1] = [0, 0, 1, 1, 0, 0, 0] := by
  decide

theorem demoM_0001200 : fieldMul 7 5 20 [0, 0, 1, 1, 0, 0, 0] [0, 0, 0, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001200 : mirrorTrits [0, 0, 1, 1, 0, 0, 0] = [0, 0, 2, 2, 0, 0, 0] := by
  decide

theorem demoInv_0001200 : specInv 7 5 20 [0, 0, 0, 1, 2, 0, 0] = some [0, 0, 2, 2, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 0, 1, 2, 0, 0] [2, 0, 2, 1, 1, 2, 2] [1, 0, 1, 0, 0, 2, 1] [0, 0, 1, 1, 0, 0, 0] [0, 0, 2, 2, 0, 0, 0] demoR1_0001200 demoR2_0001200 demoC_0001200 demoM_0001200 demoMir_0001200

theorem demoR1_1001200 : invRung 7 5 20 [1, 0, 0, 1, 2, 0, 0] [1, 0, 0, 1, 2, 0, 0] 1 2 false = ([2, 0, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_1001200 : invRung 7 5 20 [1, 0, 0, 1, 2, 0, 0] [2, 0, 0, 2, 0, 1, 0] 3 1 true = ([1, 0, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_1001200 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 0, 2] = [2, 0, 2, 0, 2, 1, 2] := by
  decide

theorem demoM_1001200 : fieldMul 7 5 20 [2, 0, 2, 0, 2, 1, 2] [1, 0, 0, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1001200 : mirrorTrits [2, 0, 2, 0, 2, 1, 2] = [1, 0, 1, 0, 1, 2, 1] := by
  decide

theorem demoInv_1001200 : specInv 7 5 20 [1, 0, 0, 1, 2, 0, 0] = some [1, 0, 1, 0, 1, 2, 1] :=
  specInv_mirror_7 [1, 0, 0, 1, 2, 0, 0] [2, 0, 0, 2, 0, 1, 0] [1, 0, 2, 1, 1, 0, 2] [2, 0, 2, 0, 2, 1, 2] [1, 0, 1, 0, 1, 2, 1] demoR1_1001200 demoR2_1001200 demoC_1001200 demoM_1001200 demoMir_1001200

theorem demoR1_2001200 : invRung 7 5 20 [2, 0, 0, 1, 2, 0, 0] [2, 0, 0, 1, 2, 0, 0] 1 2 false = ([1, 2, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_2001200 : invRung 7 5 20 [2, 0, 0, 1, 2, 0, 0] [1, 2, 0, 2, 1, 2, 2] 3 1 true = ([0, 2, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_2001200 : fieldCube 7 5 20 [0, 2, 0, 2, 0, 1, 1] = [0, 2, 2, 0, 2, 1, 0] := by
  decide

theorem demoM_2001200 : fieldMul 7 5 20 [0, 2, 2, 0, 2, 1, 0] [2, 0, 0, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2001200 : specInv 7 5 20 [2, 0, 0, 1, 2, 0, 0] = some [0, 2, 2, 0, 2, 1, 0] :=
  specInv_white_7 [2, 0, 0, 1, 2, 0, 0] [1, 2, 0, 2, 1, 2, 2] [0, 2, 0, 2, 0, 1, 1] [0, 2, 2, 0, 2, 1, 0] demoR1_2001200 demoR2_2001200 demoC_2001200 demoM_2001200

theorem demoR1_0101200 : invRung 7 5 20 [0, 1, 0, 1, 2, 0, 0] [0, 1, 0, 1, 2, 0, 0] 1 2 false = ([0, 0, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_0101200 : invRung 7 5 20 [0, 1, 0, 1, 2, 0, 0] [0, 0, 2, 2, 0, 2, 0] 3 1 true = ([0, 0, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0101200 : fieldCube 7 5 20 [0, 0, 2, 2, 0, 1, 1] = [0, 2, 2, 1, 2, 1, 2] := by
  decide

theorem demoM_0101200 : fieldMul 7 5 20 [0, 2, 2, 1, 2, 1, 2] [0, 1, 0, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0101200 : specInv 7 5 20 [0, 1, 0, 1, 2, 0, 0] = some [0, 2, 2, 1, 2, 1, 2] :=
  specInv_white_7 [0, 1, 0, 1, 2, 0, 0] [0, 0, 2, 2, 0, 2, 0] [0, 0, 2, 2, 0, 1, 1] [0, 2, 2, 1, 2, 1, 2] demoR1_0101200 demoR2_0101200 demoC_0101200 demoM_0101200

theorem demoR1_1101200 : invRung 7 5 20 [1, 1, 0, 1, 2, 0, 0] [1, 1, 0, 1, 2, 0, 0] 1 2 false = ([1, 0, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_1101200 : invRung 7 5 20 [1, 1, 0, 1, 2, 0, 0] [1, 0, 2, 0, 1, 2, 0] 3 1 true = ([1, 0, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_1101200 : fieldCube 7 5 20 [1, 0, 2, 0, 1, 2, 2] = [0, 2, 0, 0, 1, 2, 0] := by
  decide

theorem demoM_1101200 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 2, 0] [1, 1, 0, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1101200 : mirrorTrits [0, 2, 0, 0, 1, 2, 0] = [0, 1, 0, 0, 2, 1, 0] := by
  decide

theorem demoInv_1101200 : specInv 7 5 20 [1, 1, 0, 1, 2, 0, 0] = some [0, 1, 0, 0, 2, 1, 0] :=
  specInv_mirror_7 [1, 1, 0, 1, 2, 0, 0] [1, 0, 2, 0, 1, 2, 0] [1, 0, 2, 0, 1, 2, 2] [0, 2, 0, 0, 1, 2, 0] [0, 1, 0, 0, 2, 1, 0] demoR1_1101200 demoR2_1101200 demoC_1101200 demoM_1101200 demoMir_1101200

theorem demoR1_2101200 : invRung 7 5 20 [2, 1, 0, 1, 2, 0, 0] [2, 1, 0, 1, 2, 0, 0] 1 2 false = ([0, 1, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_2101200 : invRung 7 5 20 [2, 1, 0, 1, 2, 0, 0] [0, 1, 0, 2, 1, 0, 1] 3 1 true = ([2, 1, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_2101200 : fieldCube 7 5 20 [2, 1, 1, 0, 0, 2, 0] = [1, 2, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_2101200 : fieldMul 7 5 20 [1, 2, 2, 1, 2, 2, 2] [2, 1, 0, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101200 : mirrorTrits [1, 2, 2, 1, 2, 2, 2] = [2, 1, 1, 2, 1, 1, 1] := by
  decide

theorem demoInv_2101200 : specInv 7 5 20 [2, 1, 0, 1, 2, 0, 0] = some [2, 1, 1, 2, 1, 1, 1] :=
  specInv_mirror_7 [2, 1, 0, 1, 2, 0, 0] [0, 1, 0, 2, 1, 0, 1] [2, 1, 1, 0, 0, 2, 0] [1, 2, 2, 1, 2, 2, 2] [2, 1, 1, 2, 1, 1, 1] demoR1_2101200 demoR2_2101200 demoC_2101200 demoM_2101200 demoMir_2101200

theorem demoR1_0201200 : invRung 7 5 20 [0, 2, 0, 1, 2, 0, 0] [0, 2, 0, 1, 2, 0, 0] 1 2 false = ([1, 0, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_0201200 : invRung 7 5 20 [0, 2, 0, 1, 2, 0, 0] [1, 0, 1, 0, 0, 1, 1] 3 1 true = ([1, 0, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_0201200 : fieldCube 7 5 20 [1, 0, 0, 2, 2, 1, 2] = [1, 2, 1, 1, 0, 1, 0] := by
  decide

theorem demoM_0201200 : fieldMul 7 5 20 [1, 2, 1, 1, 0, 1, 0] [0, 2, 0, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0201200 : specInv 7 5 20 [0, 2, 0, 1, 2, 0, 0] = some [1, 2, 1, 1, 0, 1, 0] :=
  specInv_white_7 [0, 2, 0, 1, 2, 0, 0] [1, 0, 1, 0, 0, 1, 1] [1, 0, 0, 2, 2, 1, 2] [1, 2, 1, 1, 0, 1, 0] demoR1_0201200 demoR2_0201200 demoC_0201200 demoM_0201200

theorem demoR1_1201200 : invRung 7 5 20 [1, 2, 0, 1, 2, 0, 0] [1, 2, 0, 1, 2, 0, 0] 1 2 false = ([0, 1, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1201200 : invRung 7 5 20 [1, 2, 0, 1, 2, 0, 0] [0, 1, 0, 2, 2, 1, 1] 3 1 true = ([1, 0, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1201200 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 2, 0] = [1, 1, 0, 2, 2, 2, 0] := by
  decide

theorem demoM_1201200 : fieldMul 7 5 20 [1, 1, 0, 2, 2, 2, 0] [1, 2, 0, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201200 : mirrorTrits [1, 1, 0, 2, 2, 2, 0] = [2, 2, 0, 1, 1, 1, 0] := by
  decide

theorem demoInv_1201200 : specInv 7 5 20 [1, 2, 0, 1, 2, 0, 0] = some [2, 2, 0, 1, 1, 1, 0] :=
  specInv_mirror_7 [1, 2, 0, 1, 2, 0, 0] [0, 1, 0, 2, 2, 1, 1] [1, 0, 0, 1, 2, 2, 0] [1, 1, 0, 2, 2, 2, 0] [2, 2, 0, 1, 1, 1, 0] demoR1_1201200 demoR2_1201200 demoC_1201200 demoM_1201200 demoMir_1201200

theorem demoR1_2201200 : invRung 7 5 20 [2, 2, 0, 1, 2, 0, 0] [2, 2, 0, 1, 2, 0, 0] 1 2 false = ([2, 2, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_2201200 : invRung 7 5 20 [2, 2, 0, 1, 2, 0, 0] [2, 2, 2, 1, 0, 1, 2] 3 1 true = ([2, 0, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_2201200 : fieldCube 7 5 20 [2, 0, 0, 0, 1, 2, 2] = [1, 2, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_2201200 : fieldMul 7 5 20 [1, 2, 0, 0, 1, 2, 1] [2, 2, 0, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2201200 : specInv 7 5 20 [2, 2, 0, 1, 2, 0, 0] = some [1, 2, 0, 0, 1, 2, 1] :=
  specInv_white_7 [2, 2, 0, 1, 2, 0, 0] [2, 2, 2, 1, 0, 1, 2] [2, 0, 0, 0, 1, 2, 2] [1, 2, 0, 0, 1, 2, 1] demoR1_2201200 demoR2_2201200 demoC_2201200 demoM_2201200

theorem demoR1_0011200 : invRung 7 5 20 [0, 0, 1, 1, 2, 0, 0] [0, 0, 1, 1, 2, 0, 0] 1 2 false = ([2, 2, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_0011200 : invRung 7 5 20 [0, 0, 1, 1, 2, 0, 0] [2, 2, 0, 0, 0, 1, 1] 3 1 true = ([0, 0, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0011200 : fieldCube 7 5 20 [0, 0, 0, 0, 0, 0, 1] = [0, 1, 2, 1, 1, 1, 1] := by
  decide

theorem demoM_0011200 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 1, 1] [0, 0, 1, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0011200 : specInv 7 5 20 [0, 0, 1, 1, 2, 0, 0] = some [0, 1, 2, 1, 1, 1, 1] :=
  specInv_white_7 [0, 0, 1, 1, 2, 0, 0] [2, 2, 0, 0, 0, 1, 1] [0, 0, 0, 0, 0, 0, 1] [0, 1, 2, 1, 1, 1, 1] demoR1_0011200 demoR2_0011200 demoC_0011200 demoM_0011200

theorem demoR1_1011200 : invRung 7 5 20 [1, 0, 1, 1, 2, 0, 0] [1, 0, 1, 1, 2, 0, 0] 1 2 false = ([1, 2, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_1011200 : invRung 7 5 20 [1, 0, 1, 1, 2, 0, 0] [1, 2, 2, 1, 0, 1, 1] 3 1 true = ([2, 0, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_1011200 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 2, 0] = [0, 0, 1, 1, 2, 2, 1] := by
  decide

theorem demoM_1011200 : fieldMul 7 5 20 [0, 0, 1, 1, 2, 2, 1] [1, 0, 1, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011200 : mirrorTrits [0, 0, 1, 1, 2, 2, 1] = [0, 0, 2, 2, 1, 1, 2] := by
  decide

theorem demoInv_1011200 : specInv 7 5 20 [1, 0, 1, 1, 2, 0, 0] = some [0, 0, 2, 2, 1, 1, 2] :=
  specInv_mirror_7 [1, 0, 1, 1, 2, 0, 0] [1, 2, 2, 1, 0, 1, 1] [2, 0, 2, 2, 1, 2, 0] [0, 0, 1, 1, 2, 2, 1] [0, 0, 2, 2, 1, 1, 2] demoR1_1011200 demoR2_1011200 demoC_1011200 demoM_1011200 demoMir_1011200

theorem demoR1_2011200 : invRung 7 5 20 [2, 0, 1, 1, 2, 0, 0] [2, 0, 1, 1, 2, 0, 0] 1 2 false = ([2, 0, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_2011200 : invRung 7 5 20 [2, 0, 1, 1, 2, 0, 0] [2, 0, 0, 0, 1, 2, 0] 3 1 true = ([2, 1, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_2011200 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 1, 2] = [0, 1, 2, 1, 0, 1, 0] := by
  decide

theorem demoM_2011200 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 1, 0] [2, 0, 1, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011200 : mirrorTrits [0, 1, 2, 1, 0, 1, 0] = [0, 2, 1, 2, 0, 2, 0] := by
  decide

theorem demoInv_2011200 : specInv 7 5 20 [2, 0, 1, 1, 2, 0, 0] = some [0, 2, 1, 2, 0, 2, 0] :=
  specInv_mirror_7 [2, 0, 1, 1, 2, 0, 0] [2, 0, 0, 0, 1, 2, 0] [2, 1, 1, 0, 1, 1, 2] [0, 1, 2, 1, 0, 1, 0] [0, 2, 1, 2, 0, 2, 0] demoR1_2011200 demoR2_2011200 demoC_2011200 demoM_2011200 demoMir_2011200

theorem demoR1_0111200 : invRung 7 5 20 [0, 1, 1, 1, 2, 0, 0] [0, 1, 1, 1, 2, 0, 0] 1 2 false = ([0, 0, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_0111200 : invRung 7 5 20 [0, 1, 1, 1, 2, 0, 0] [0, 0, 1, 2, 0, 1, 0] 3 1 true = ([0, 2, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0111200 : fieldCube 7 5 20 [0, 2, 2, 0, 0, 0, 1] = [0, 1, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_0111200 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 1, 0] [0, 1, 1, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0111200 : specInv 7 5 20 [0, 1, 1, 1, 2, 0, 0] = some [0, 1, 2, 0, 1, 1, 0] :=
  specInv_white_7 [0, 1, 1, 1, 2, 0, 0] [0, 0, 1, 2, 0, 1, 0] [0, 2, 2, 0, 0, 0, 1] [0, 1, 2, 0, 1, 1, 0] demoR1_0111200 demoR2_0111200 demoC_0111200 demoM_0111200

theorem demoR1_1111200 : invRung 7 5 20 [1, 1, 1, 1, 2, 0, 0] [1, 1, 1, 1, 2, 0, 0] 1 2 false = ([0, 2, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1111200 : invRung 7 5 20 [1, 1, 1, 1, 2, 0, 0] [0, 2, 0, 2, 0, 0, 1] 3 1 true = ([2, 1, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_1111200 : fieldCube 7 5 20 [2, 1, 2, 0, 0, 2, 0] = [1, 2, 2, 1, 2, 2, 0] := by
  decide

theorem demoM_1111200 : fieldMul 7 5 20 [1, 2, 2, 1, 2, 2, 0] [1, 1, 1, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111200 : mirrorTrits [1, 2, 2, 1, 2, 2, 0] = [2, 1, 1, 2, 1, 1, 0] := by
  decide

theorem demoInv_1111200 : specInv 7 5 20 [1, 1, 1, 1, 2, 0, 0] = some [2, 1, 1, 2, 1, 1, 0] :=
  specInv_mirror_7 [1, 1, 1, 1, 2, 0, 0] [0, 2, 0, 2, 0, 0, 1] [2, 1, 2, 0, 0, 2, 0] [1, 2, 2, 1, 2, 2, 0] [2, 1, 1, 2, 1, 1, 0] demoR1_1111200 demoR2_1111200 demoC_1111200 demoM_1111200 demoMir_1111200

theorem demoR1_2111200 : invRung 7 5 20 [2, 1, 1, 1, 2, 0, 0] [2, 1, 1, 1, 2, 0, 0] 1 2 false = ([1, 1, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_2111200 : invRung 7 5 20 [2, 1, 1, 1, 2, 0, 0] [1, 1, 0, 2, 1, 2, 1] 3 1 true = ([1, 2, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2111200 : fieldCube 7 5 20 [1, 2, 0, 0, 1, 1, 1] = [2, 0, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_2111200 : fieldMul 7 5 20 [2, 0, 0, 1, 2, 0, 1] [2, 1, 1, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2111200 : specInv 7 5 20 [2, 1, 1, 1, 2, 0, 0] = some [2, 0, 0, 1, 2, 0, 1] :=
  specInv_white_7 [2, 1, 1, 1, 2, 0, 0] [1, 1, 0, 2, 1, 2, 1] [1, 2, 0, 0, 1, 1, 1] [2, 0, 0, 1, 2, 0, 1] demoR1_2111200 demoR2_2111200 demoC_2111200 demoM_2111200

theorem demoR1_0211200 : invRung 7 5 20 [0, 2, 1, 1, 2, 0, 0] [0, 2, 1, 1, 2, 0, 0] 1 2 false = ([2, 0, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0211200 : invRung 7 5 20 [0, 2, 1, 1, 2, 0, 0] [2, 0, 2, 1, 1, 1, 2] 3 1 true = ([2, 2, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0211200 : fieldCube 7 5 20 [2, 2, 1, 0, 1, 2, 1] = [1, 1, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_0211200 : fieldMul 7 5 20 [1, 1, 1, 1, 0, 1, 1] [0, 2, 1, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211200 : mirrorTrits [1, 1, 1, 1, 0, 1, 1] = [2, 2, 2, 2, 0, 2, 2] := by
  decide

theorem demoInv_0211200 : specInv 7 5 20 [0, 2, 1, 1, 2, 0, 0] = some [2, 2, 2, 2, 0, 2, 2] :=
  specInv_mirror_7 [0, 2, 1, 1, 2, 0, 0] [2, 0, 2, 1, 1, 1, 2] [2, 2, 1, 0, 1, 2, 1] [1, 1, 1, 1, 0, 1, 1] [2, 2, 2, 2, 0, 2, 2] demoR1_0211200 demoR2_0211200 demoC_0211200 demoM_0211200 demoMir_0211200

theorem demoR1_1211200 : invRung 7 5 20 [1, 2, 1, 1, 2, 0, 0] [1, 2, 1, 1, 2, 0, 0] 1 2 false = ([0, 2, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_1211200 : invRung 7 5 20 [1, 2, 1, 1, 2, 0, 0] [0, 2, 1, 1, 0, 1, 2] 3 1 true = ([0, 1, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_1211200 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 2, 2] = [2, 0, 0, 2, 1, 0, 1] := by
  decide

theorem demoM_1211200 : fieldMul 7 5 20 [2, 0, 0, 2, 1, 0, 1] [1, 2, 1, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1211200 : specInv 7 5 20 [1, 2, 1, 1, 2, 0, 0] = some [2, 0, 0, 2, 1, 0, 1] :=
  specInv_white_7 [1, 2, 1, 1, 2, 0, 0] [0, 2, 1, 1, 0, 1, 2] [0, 1, 2, 0, 2, 2, 2] [2, 0, 0, 2, 1, 0, 1] demoR1_1211200 demoR2_1211200 demoC_1211200 demoM_1211200

theorem demoR1_2211200 : invRung 7 5 20 [2, 2, 1, 1, 2, 0, 0] [2, 2, 1, 1, 2, 0, 0] 1 2 false = ([1, 0, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_2211200 : invRung 7 5 20 [2, 2, 1, 1, 2, 0, 0] [1, 0, 0, 0, 0, 0, 1] 3 1 true = ([0, 1, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_2211200 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 1, 1] = [0, 0, 2, 0, 2, 2, 1] := by
  decide

theorem demoM_2211200 : fieldMul 7 5 20 [0, 0, 2, 0, 2, 2, 1] [2, 2, 1, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211200 : mirrorTrits [0, 0, 2, 0, 2, 2, 1] = [0, 0, 1, 0, 1, 1, 2] := by
  decide

theorem demoInv_2211200 : specInv 7 5 20 [2, 2, 1, 1, 2, 0, 0] = some [0, 0, 1, 0, 1, 1, 2] :=
  specInv_mirror_7 [2, 2, 1, 1, 2, 0, 0] [1, 0, 0, 0, 0, 0, 1] [0, 1, 0, 2, 1, 1, 1] [0, 0, 2, 0, 2, 2, 1] [0, 0, 1, 0, 1, 1, 2] demoR1_2211200 demoR2_2211200 demoC_2211200 demoM_2211200 demoMir_2211200

theorem demoR1_0021200 : invRung 7 5 20 [0, 0, 2, 1, 2, 0, 0] [0, 0, 2, 1, 2, 0, 0] 1 2 false = ([0, 1, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_0021200 : invRung 7 5 20 [0, 0, 2, 1, 2, 0, 0] [0, 1, 2, 1, 1, 0, 2] 3 1 true = ([1, 0, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_0021200 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 1, 2] = [1, 2, 1, 1, 0, 1, 2] := by
  decide

theorem demoM_0021200 : fieldMul 7 5 20 [1, 2, 1, 1, 0, 1, 2] [0, 0, 2, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021200 : mirrorTrits [1, 2, 1, 1, 0, 1, 2] = [2, 1, 2, 2, 0, 2, 1] := by
  decide

theorem demoInv_0021200 : specInv 7 5 20 [0, 0, 2, 1, 2, 0, 0] = some [2, 1, 2, 2, 0, 2, 1] :=
  specInv_mirror_7 [0, 0, 2, 1, 2, 0, 0] [0, 1, 2, 1, 1, 0, 2] [1, 0, 2, 2, 2, 1, 2] [1, 2, 1, 1, 0, 1, 2] [2, 1, 2, 2, 0, 2, 1] demoR1_0021200 demoR2_0021200 demoC_0021200 demoM_0021200 demoMir_0021200

theorem demoR1_1021200 : invRung 7 5 20 [1, 0, 2, 1, 2, 0, 0] [1, 0, 2, 1, 2, 0, 0] 1 2 false = ([0, 1, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1021200 : invRung 7 5 20 [1, 0, 2, 1, 2, 0, 0] [0, 1, 0, 2, 2, 1, 0] 3 1 true = ([2, 2, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_1021200 : fieldCube 7 5 20 [2, 2, 2, 1, 1, 1, 0] = [1, 2, 2, 0, 1, 0, 2] := by
  decide

theorem demoM_1021200 : fieldMul 7 5 20 [1, 2, 2, 0, 1, 0, 2] [1, 0, 2, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1021200 : specInv 7 5 20 [1, 0, 2, 1, 2, 0, 0] = some [1, 2, 2, 0, 1, 0, 2] :=
  specInv_white_7 [1, 0, 2, 1, 2, 0, 0] [0, 1, 0, 2, 2, 1, 0] [2, 2, 2, 1, 1, 1, 0] [1, 2, 2, 0, 1, 0, 2] demoR1_1021200 demoR2_1021200 demoC_1021200 demoM_1021200

theorem demoR1_2021200 : invRung 7 5 20 [2, 0, 2, 1, 2, 0, 0] [2, 0, 2, 1, 2, 0, 0] 1 2 false = ([2, 1, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_2021200 : invRung 7 5 20 [2, 0, 2, 1, 2, 0, 0] [2, 1, 0, 0, 0, 2, 1] 3 1 true = ([2, 2, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_2021200 : fieldCube 7 5 20 [2, 2, 1, 2, 1, 2, 0] = [0, 0, 1, 0, 2, 2, 0] := by
  decide

theorem demoM_2021200 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 2, 0] [2, 0, 2, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2021200 : specInv 7 5 20 [2, 0, 2, 1, 2, 0, 0] = some [0, 0, 1, 0, 2, 2, 0] :=
  specInv_white_7 [2, 0, 2, 1, 2, 0, 0] [2, 1, 0, 0, 0, 2, 1] [2, 2, 1, 2, 1, 2, 0] [0, 0, 1, 0, 2, 2, 0] demoR1_2021200 demoR2_2021200 demoC_2021200 demoM_2021200

theorem demoR1_0121200 : invRung 7 5 20 [0, 1, 2, 1, 2, 0, 0] [0, 1, 2, 1, 2, 0, 0] 1 2 false = ([1, 2, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0121200 : invRung 7 5 20 [0, 1, 2, 1, 2, 0, 0] [1, 2, 0, 0, 1, 2, 1] 3 1 true = ([1, 1, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0121200 : fieldCube 7 5 20 [1, 1, 1, 2, 2, 0, 2] = [0, 1, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_0121200 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 0, 2] [0, 1, 2, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0121200 : specInv 7 5 20 [0, 1, 2, 1, 2, 0, 0] = some [0, 1, 0, 2, 2, 0, 2] :=
  specInv_white_7 [0, 1, 2, 1, 2, 0, 0] [1, 2, 0, 0, 1, 2, 1] [1, 1, 1, 2, 2, 0, 2] [0, 1, 0, 2, 2, 0, 2] demoR1_0121200 demoR2_0121200 demoC_0121200 demoM_0121200

theorem demoR1_1121200 : invRung 7 5 20 [1, 1, 2, 1, 2, 0, 0] [1, 1, 2, 1, 2, 0, 0] 1 2 false = ([2, 0, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_1121200 : invRung 7 5 20 [1, 1, 2, 1, 2, 0, 0] [2, 0, 2, 2, 0, 0, 2] 3 1 true = ([1, 0, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1121200 : fieldCube 7 5 20 [1, 0, 1, 1, 0, 2, 0] = [1, 2, 0, 0, 2, 0, 2] := by
  decide

theorem demoM_1121200 : fieldMul 7 5 20 [1, 2, 0, 0, 2, 0, 2] [1, 1, 2, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1121200 : specInv 7 5 20 [1, 1, 2, 1, 2, 0, 0] = some [1, 2, 0, 0, 2, 0, 2] :=
  specInv_white_7 [1, 1, 2, 1, 2, 0, 0] [2, 0, 2, 2, 0, 0, 2] [1, 0, 1, 1, 0, 2, 0] [1, 2, 0, 0, 2, 0, 2] demoR1_1121200 demoR2_1121200 demoC_1121200 demoM_1121200

theorem demoR1_2121200 : invRung 7 5 20 [2, 1, 2, 1, 2, 0, 0] [2, 1, 2, 1, 2, 0, 0] 1 2 false = ([1, 0, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2121200 : invRung 7 5 20 [2, 1, 2, 1, 2, 0, 0] [1, 0, 2, 0, 2, 0, 0] 3 1 true = ([0, 0, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_2121200 : fieldCube 7 5 20 [0, 0, 1, 1, 0, 0, 1] = [1, 1, 0, 1, 1, 2, 2] := by
  decide

theorem demoM_2121200 : fieldMul 7 5 20 [1, 1, 0, 1, 1, 2, 2] [2, 1, 2, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2121200 : mirrorTrits [1, 1, 0, 1, 1, 2, 2] = [2, 2, 0, 2, 2, 1, 1] := by
  decide

theorem demoInv_2121200 : specInv 7 5 20 [2, 1, 2, 1, 2, 0, 0] = some [2, 2, 0, 2, 2, 1, 1] :=
  specInv_mirror_7 [2, 1, 2, 1, 2, 0, 0] [1, 0, 2, 0, 2, 0, 0] [0, 0, 1, 1, 0, 0, 1] [1, 1, 0, 1, 1, 2, 2] [2, 2, 0, 2, 2, 1, 1] demoR1_2121200 demoR2_2121200 demoC_2121200 demoM_2121200 demoMir_2121200

theorem demoR1_0221200 : invRung 7 5 20 [0, 2, 2, 1, 2, 0, 0] [0, 2, 2, 1, 2, 0, 0] 1 2 false = ([1, 1, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_0221200 : invRung 7 5 20 [0, 2, 2, 1, 2, 0, 0] [1, 1, 2, 2, 2, 2, 0] 3 1 true = ([2, 1, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_0221200 : fieldCube 7 5 20 [2, 1, 1, 0, 2, 0, 0] = [2, 2, 0, 0, 0, 2, 0] := by
  decide

theorem demoM_0221200 : fieldMul 7 5 20 [2, 2, 0, 0, 0, 2, 0] [0, 2, 2, 1, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0221200 : mirrorTrits [2, 2, 0, 0, 0, 2, 0] = [1, 1, 0, 0, 0, 1, 0] := by
  decide

theorem demoInv_0221200 : specInv 7 5 20 [0, 2, 2, 1, 2, 0, 0] = some [1, 1, 0, 0, 0, 1, 0] :=
  specInv_mirror_7 [0, 2, 2, 1, 2, 0, 0] [1, 1, 2, 2, 2, 2, 0] [2, 1, 1, 0, 2, 0, 0] [2, 2, 0, 0, 0, 2, 0] [1, 1, 0, 0, 0, 1, 0] demoR1_0221200 demoR2_0221200 demoC_0221200 demoM_0221200 demoMir_0221200

theorem demoR1_1221200 : invRung 7 5 20 [1, 2, 2, 1, 2, 0, 0] [1, 2, 2, 1, 2, 0, 0] 1 2 false = ([0, 1, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_1221200 : invRung 7 5 20 [1, 2, 2, 1, 2, 0, 0] [0, 1, 2, 0, 1, 2, 2] 3 1 true = ([0, 1, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_1221200 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 1, 0] = [2, 1, 2, 1, 1, 2, 0] := by
  decide

theorem demoM_1221200 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 2, 0] [1, 2, 2, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1221200 : specInv 7 5 20 [1, 2, 2, 1, 2, 0, 0] = some [2, 1, 2, 1, 1, 2, 0] :=
  specInv_white_7 [1, 2, 2, 1, 2, 0, 0] [0, 1, 2, 0, 1, 2, 2] [0, 1, 1, 1, 0, 1, 0] [2, 1, 2, 1, 1, 2, 0] demoR1_1221200 demoR2_1221200 demoC_1221200 demoM_1221200

theorem demoR1_2221200 : invRung 7 5 20 [2, 2, 2, 1, 2, 0, 0] [2, 2, 2, 1, 2, 0, 0] 1 2 false = ([2, 2, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_2221200 : invRung 7 5 20 [2, 2, 2, 1, 2, 0, 0] [2, 2, 2, 2, 0, 0, 1] 3 1 true = ([0, 1, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_2221200 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 2, 0] = [1, 0, 1, 2, 2, 2, 1] := by
  decide

theorem demoM_2221200 : fieldMul 7 5 20 [1, 0, 1, 2, 2, 2, 1] [2, 2, 2, 1, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2221200 : specInv 7 5 20 [2, 2, 2, 1, 2, 0, 0] = some [1, 0, 1, 2, 2, 2, 1] :=
  specInv_white_7 [2, 2, 2, 1, 2, 0, 0] [2, 2, 2, 2, 0, 0, 1] [0, 1, 2, 2, 1, 2, 0] [1, 0, 1, 2, 2, 2, 1] demoR1_2221200 demoR2_2221200 demoC_2221200 demoM_2221200

theorem demoR1_0002200 : invRung 7 5 20 [0, 0, 0, 2, 2, 0, 0] [0, 0, 0, 2, 2, 0, 0] 1 2 false = ([2, 0, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_0002200 : invRung 7 5 20 [0, 0, 0, 2, 2, 0, 0] [2, 0, 2, 2, 2, 1, 2] 3 1 true = ([2, 2, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_0002200 : fieldCube 7 5 20 [2, 2, 2, 0, 0, 1, 2] = [0, 0, 2, 1, 0, 0, 0] := by
  decide

theorem demoM_0002200 : fieldMul 7 5 20 [0, 0, 2, 1, 0, 0, 0] [0, 0, 0, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002200 : mirrorTrits [0, 0, 2, 1, 0, 0, 0] = [0, 0, 1, 2, 0, 0, 0] := by
  decide

theorem demoInv_0002200 : specInv 7 5 20 [0, 0, 0, 2, 2, 0, 0] = some [0, 0, 1, 2, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 0, 2, 2, 0, 0] [2, 0, 2, 2, 2, 1, 2] [2, 2, 2, 0, 0, 1, 2] [0, 0, 2, 1, 0, 0, 0] [0, 0, 1, 2, 0, 0, 0] demoR1_0002200 demoR2_0002200 demoC_0002200 demoM_0002200 demoMir_0002200

theorem demoR1_1002200 : invRung 7 5 20 [1, 0, 0, 2, 2, 0, 0] [1, 0, 0, 2, 2, 0, 0] 1 2 false = ([2, 1, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_1002200 : invRung 7 5 20 [1, 0, 0, 2, 2, 0, 0] [2, 1, 0, 2, 0, 0, 0] 3 1 true = ([2, 0, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1002200 : fieldCube 7 5 20 [2, 0, 0, 1, 2, 1, 0] = [1, 0, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_1002200 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 1, 1] [1, 0, 0, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002200 : mirrorTrits [1, 0, 2, 2, 1, 1, 1] = [2, 0, 1, 1, 2, 2, 2] := by
  decide

theorem demoInv_1002200 : specInv 7 5 20 [1, 0, 0, 2, 2, 0, 0] = some [2, 0, 1, 1, 2, 2, 2] :=
  specInv_mirror_7 [1, 0, 0, 2, 2, 0, 0] [2, 1, 0, 2, 0, 0, 0] [2, 0, 0, 1, 2, 1, 0] [1, 0, 2, 2, 1, 1, 1] [2, 0, 1, 1, 2, 2, 2] demoR1_1002200 demoR2_1002200 demoC_1002200 demoM_1002200 demoMir_1002200

theorem demoR1_2002200 : invRung 7 5 20 [2, 0, 0, 2, 2, 0, 0] [2, 0, 0, 2, 2, 0, 0] 1 2 false = ([1, 0, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_2002200 : invRung 7 5 20 [2, 0, 0, 2, 2, 0, 0] [1, 0, 1, 0, 2, 2, 2] 3 1 true = ([0, 1, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2002200 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 1, 1] = [2, 2, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_2002200 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 0, 2] [2, 0, 0, 2, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2002200 : specInv 7 5 20 [2, 0, 0, 2, 2, 0, 0] = some [2, 2, 1, 2, 2, 0, 2] :=
  specInv_white_7 [2, 0, 0, 2, 2, 0, 0] [1, 0, 1, 0, 2, 2, 2] [0, 1, 2, 1, 0, 1, 1] [2, 2, 1, 2, 2, 0, 2] demoR1_2002200 demoR2_2002200 demoC_2002200 demoM_2002200

theorem demoR1_0102200 : invRung 7 5 20 [0, 1, 0, 2, 2, 0, 0] [0, 1, 0, 2, 2, 0, 0] 1 2 false = ([0, 2, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_0102200 : invRung 7 5 20 [0, 1, 0, 2, 2, 0, 0] [0, 2, 0, 0, 0, 1, 1] 3 1 true = ([1, 2, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0102200 : fieldCube 7 5 20 [1, 2, 2, 0, 1, 2, 2] = [0, 2, 0, 2, 1, 2, 0] := by
  decide

theorem demoM_0102200 : fieldMul 7 5 20 [0, 2, 0, 2, 1, 2, 0] [0, 1, 0, 2, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0102200 : specInv 7 5 20 [0, 1, 0, 2, 2, 0, 0] = some [0, 2, 0, 2, 1, 2, 0] :=
  specInv_white_7 [0, 1, 0, 2, 2, 0, 0] [0, 2, 0, 0, 0, 1, 1] [1, 2, 2, 0, 1, 2, 2] [0, 2, 0, 2, 1, 2, 0] demoR1_0102200 demoR2_0102200 demoC_0102200 demoM_0102200

theorem demoR1_1102200 : invRung 7 5 20 [1, 1, 0, 2, 2, 0, 0] [1, 1, 0, 2, 2, 0, 0] 1 2 false = ([2, 0, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_1102200 : invRung 7 5 20 [1, 1, 0, 2, 2, 0, 0] [2, 0, 0, 0, 2, 0, 1] 3 1 true = ([0, 1, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_1102200 : fieldCube 7 5 20 [0, 1, 2, 0, 0, 0, 2] = [0, 2, 1, 0, 2, 2, 1] := by
  decide

theorem demoM_1102200 : fieldMul 7 5 20 [0, 2, 1, 0, 2, 2, 1] [1, 1, 0, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102200 : mirrorTrits [0, 2, 1, 0, 2, 2, 1] = [0, 1, 2, 0, 1, 1, 2] := by
  decide

theorem demoInv_1102200 : specInv 7 5 20 [1, 1, 0, 2, 2, 0, 0] = some [0, 1, 2, 0, 1, 1, 2] :=
  specInv_mirror_7 [1, 1, 0, 2, 2, 0, 0] [2, 0, 0, 0, 2, 0, 1] [0, 1, 2, 0, 0, 0, 2] [0, 2, 1, 0, 2, 2, 1] [0, 1, 2, 0, 1, 1, 2] demoR1_1102200 demoR2_1102200 demoC_1102200 demoM_1102200 demoMir_1102200

theorem demoR1_2102200 : invRung 7 5 20 [2, 1, 0, 2, 2, 0, 0] [2, 1, 0, 2, 2, 0, 0] 1 2 false = ([2, 1, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_2102200 : invRung 7 5 20 [2, 1, 0, 2, 2, 0, 0] [2, 1, 2, 0, 2, 1, 2] 3 1 true = ([1, 1, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_2102200 : fieldCube 7 5 20 [1, 1, 0, 2, 2, 0, 1] = [0, 0, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_2102200 : fieldMul 7 5 20 [0, 0, 1, 1, 1, 2, 0] [2, 1, 0, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2102200 : mirrorTrits [0, 0, 1, 1, 1, 2, 0] = [0, 0, 2, 2, 2, 1, 0] := by
  decide

theorem demoInv_2102200 : specInv 7 5 20 [2, 1, 0, 2, 2, 0, 0] = some [0, 0, 2, 2, 2, 1, 0] :=
  specInv_mirror_7 [2, 1, 0, 2, 2, 0, 0] [2, 1, 2, 0, 2, 1, 2] [1, 1, 0, 2, 2, 0, 1] [0, 0, 1, 1, 1, 2, 0] [0, 0, 2, 2, 2, 1, 0] demoR1_2102200 demoR2_2102200 demoC_2102200 demoM_2102200 demoMir_2102200

theorem demoR1_0202200 : invRung 7 5 20 [0, 2, 0, 2, 2, 0, 0] [0, 2, 0, 2, 2, 0, 0] 1 2 false = ([1, 2, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_0202200 : invRung 7 5 20 [0, 2, 0, 2, 2, 0, 0] [1, 2, 0, 2, 1, 1, 1] 3 1 true = ([0, 2, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0202200 : fieldCube 7 5 20 [0, 2, 2, 2, 1, 2, 1] = [1, 1, 0, 1, 0, 0, 2] := by
  decide

theorem demoM_0202200 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 0, 2] [0, 2, 0, 2, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0202200 : specInv 7 5 20 [0, 2, 0, 2, 2, 0, 0] = some [1, 1, 0, 1, 0, 0, 2] :=
  specInv_white_7 [0, 2, 0, 2, 2, 0, 0] [1, 2, 0, 2, 1, 1, 1] [0, 2, 2, 2, 1, 2, 1] [1, 1, 0, 1, 0, 0, 2] demoR1_0202200 demoR2_0202200 demoC_0202200 demoM_0202200

theorem demoR1_1202200 : invRung 7 5 20 [1, 2, 0, 2, 2, 0, 0] [1, 2, 0, 2, 2, 0, 0] 1 2 false = ([2, 1, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_1202200 : invRung 7 5 20 [1, 2, 0, 2, 2, 0, 0] [2, 1, 2, 0, 0, 2, 1] 3 1 true = ([2, 0, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_1202200 : fieldCube 7 5 20 [2, 0, 2, 0, 0, 0, 1] = [2, 1, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_1202200 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 1, 0] [1, 2, 0, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202200 : mirrorTrits [2, 1, 2, 1, 1, 1, 0] = [1, 2, 1, 2, 2, 2, 0] := by
  decide

theorem demoInv_1202200 : specInv 7 5 20 [1, 2, 0, 2, 2, 0, 0] = some [1, 2, 1, 2, 2, 2, 0] :=
  specInv_mirror_7 [1, 2, 0, 2, 2, 0, 0] [2, 1, 2, 0, 0, 2, 1] [2, 0, 2, 0, 0, 0, 1] [2, 1, 2, 1, 1, 1, 0] [1, 2, 1, 2, 2, 2, 0] demoR1_1202200 demoR2_1202200 demoC_1202200 demoM_1202200 demoMir_1202200

theorem demoR1_2202200 : invRung 7 5 20 [2, 2, 0, 2, 2, 0, 0] [2, 2, 0, 2, 2, 0, 0] 1 2 false = ([0, 2, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_2202200 : invRung 7 5 20 [2, 2, 0, 2, 2, 0, 0] [0, 2, 2, 0, 0, 1, 2] 3 1 true = ([0, 2, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2202200 : fieldCube 7 5 20 [0, 2, 0, 2, 1, 2, 2] = [1, 2, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_2202200 : fieldMul 7 5 20 [1, 2, 2, 2, 1, 1, 1] [2, 2, 0, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202200 : mirrorTrits [1, 2, 2, 2, 1, 1, 1] = [2, 1, 1, 1, 2, 2, 2] := by
  decide

theorem demoInv_2202200 : specInv 7 5 20 [2, 2, 0, 2, 2, 0, 0] = some [2, 1, 1, 1, 2, 2, 2] :=
  specInv_mirror_7 [2, 2, 0, 2, 2, 0, 0] [0, 2, 2, 0, 0, 1, 2] [0, 2, 0, 2, 1, 2, 2] [1, 2, 2, 2, 1, 1, 1] [2, 1, 1, 1, 2, 2, 2] demoR1_2202200 demoR2_2202200 demoC_2202200 demoM_2202200 demoMir_2202200

theorem demoR1_0012200 : invRung 7 5 20 [0, 0, 1, 2, 2, 0, 0] [0, 0, 1, 2, 2, 0, 0] 1 2 false = ([1, 2, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0012200 : invRung 7 5 20 [0, 0, 1, 2, 2, 0, 0] [1, 2, 1, 0, 0, 0, 0] 3 1 true = ([1, 1, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0012200 : fieldCube 7 5 20 [1, 1, 2, 2, 1, 2, 1] = [2, 1, 0, 0, 0, 0, 2] := by
  decide

theorem demoM_0012200 : fieldMul 7 5 20 [2, 1, 0, 0, 0, 0, 2] [0, 0, 1, 2, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0012200 : specInv 7 5 20 [0, 0, 1, 2, 2, 0, 0] = some [2, 1, 0, 0, 0, 0, 2] :=
  specInv_white_7 [0, 0, 1, 2, 2, 0, 0] [1, 2, 1, 0, 0, 0, 0] [1, 1, 2, 2, 1, 2, 1] [2, 1, 0, 0, 0, 0, 2] demoR1_0012200 demoR2_0012200 demoC_0012200 demoM_0012200

theorem demoR1_1012200 : invRung 7 5 20 [1, 0, 1, 2, 2, 0, 0] [1, 0, 1, 2, 2, 0, 0] 1 2 false = ([0, 1, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_1012200 : invRung 7 5 20 [1, 0, 1, 2, 2, 0, 0] [0, 1, 1, 2, 1, 1, 1] 3 1 true = ([2, 1, 2, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_1012200 : fieldCube 7 5 20 [2, 1, 2, 1, 2, 0, 2] = [0, 1, 2, 2, 2, 2, 0] := by
  decide

theorem demoM_1012200 : fieldMul 7 5 20 [0, 1, 2, 2, 2, 2, 0] [1, 0, 1, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1012200 : mirrorTrits [0, 1, 2, 2, 2, 2, 0] = [0, 2, 1, 1, 1, 1, 0] := by
  decide

theorem demoInv_1012200 : specInv 7 5 20 [1, 0, 1, 2, 2, 0, 0] = some [0, 2, 1, 1, 1, 1, 0] :=
  specInv_mirror_7 [1, 0, 1, 2, 2, 0, 0] [0, 1, 1, 2, 1, 1, 1] [2, 1, 2, 1, 2, 0, 2] [0, 1, 2, 2, 2, 2, 0] [0, 2, 1, 1, 1, 1, 0] demoR1_1012200 demoR2_1012200 demoC_1012200 demoM_1012200 demoMir_1012200

theorem demoR1_2012200 : invRung 7 5 20 [2, 0, 1, 2, 2, 0, 0] [2, 0, 1, 2, 2, 0, 0] 1 2 false = ([1, 0, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_2012200 : invRung 7 5 20 [2, 0, 1, 2, 2, 0, 0] [1, 0, 1, 1, 2, 1, 1] 3 1 true = ([2, 2, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_2012200 : fieldCube 7 5 20 [2, 2, 2, 2, 2, 1, 0] = [2, 0, 0, 1, 1, 2, 0] := by
  decide

theorem demoM_2012200 : fieldMul 7 5 20 [2, 0, 0, 1, 1, 2, 0] [2, 0, 1, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012200 : mirrorTrits [2, 0, 0, 1, 1, 2, 0] = [1, 0, 0, 2, 2, 1, 0] := by
  decide

theorem demoInv_2012200 : specInv 7 5 20 [2, 0, 1, 2, 2, 0, 0] = some [1, 0, 0, 2, 2, 1, 0] :=
  specInv_mirror_7 [2, 0, 1, 2, 2, 0, 0] [1, 0, 1, 1, 2, 1, 1] [2, 2, 2, 2, 2, 1, 0] [2, 0, 0, 1, 1, 2, 0] [1, 0, 0, 2, 2, 1, 0] demoR1_2012200 demoR2_2012200 demoC_2012200 demoM_2012200 demoMir_2012200

theorem demoR1_0112200 : invRung 7 5 20 [0, 1, 1, 2, 2, 0, 0] [0, 1, 1, 2, 2, 0, 0] 1 2 false = ([0, 1, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_0112200 : invRung 7 5 20 [0, 1, 1, 2, 2, 0, 0] [0, 1, 2, 0, 1, 2, 0] 3 1 true = ([2, 2, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_0112200 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 2, 1] = [2, 1, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_0112200 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 2, 1] [0, 1, 1, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112200 : mirrorTrits [2, 1, 2, 1, 0, 2, 1] = [1, 2, 1, 2, 0, 1, 2] := by
  decide

theorem demoInv_0112200 : specInv 7 5 20 [0, 1, 1, 2, 2, 0, 0] = some [1, 2, 1, 2, 0, 1, 2] :=
  specInv_mirror_7 [0, 1, 1, 2, 2, 0, 0] [0, 1, 2, 0, 1, 2, 0] [2, 2, 1, 1, 1, 2, 1] [2, 1, 2, 1, 0, 2, 1] [1, 2, 1, 2, 0, 1, 2] demoR1_0112200 demoR2_0112200 demoC_0112200 demoM_0112200 demoMir_0112200

theorem demoR1_1112200 : invRung 7 5 20 [1, 1, 1, 2, 2, 0, 0] [1, 1, 1, 2, 2, 0, 0] 1 2 false = ([1, 2, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_1112200 : invRung 7 5 20 [1, 1, 1, 2, 2, 0, 0] [1, 2, 2, 1, 1, 1, 2] 3 1 true = ([2, 2, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_1112200 : fieldCube 7 5 20 [2, 2, 1, 0, 0, 2, 2] = [1, 1, 0, 1, 1, 1, 1] := by
  decide

theorem demoM_1112200 : fieldMul 7 5 20 [1, 1, 0, 1, 1, 1, 1] [1, 1, 1, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112200 : mirrorTrits [1, 1, 0, 1, 1, 1, 1] = [2, 2, 0, 2, 2, 2, 2] := by
  decide

theorem demoInv_1112200 : specInv 7 5 20 [1, 1, 1, 2, 2, 0, 0] = some [2, 2, 0, 2, 2, 2, 2] :=
  specInv_mirror_7 [1, 1, 1, 2, 2, 0, 0] [1, 2, 2, 1, 1, 1, 2] [2, 2, 1, 0, 0, 2, 2] [1, 1, 0, 1, 1, 1, 1] [2, 2, 0, 2, 2, 2, 2] demoR1_1112200 demoR2_1112200 demoC_1112200 demoM_1112200 demoMir_1112200

theorem demoR1_2112200 : invRung 7 5 20 [2, 1, 1, 2, 2, 0, 0] [2, 1, 1, 2, 2, 0, 0] 1 2 false = ([0, 2, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_2112200 : invRung 7 5 20 [2, 1, 1, 2, 2, 0, 0] [0, 2, 1, 1, 1, 1, 0] 3 1 true = ([0, 1, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_2112200 : fieldCube 7 5 20 [0, 1, 1, 2, 0, 0, 2] = [2, 2, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_2112200 : fieldMul 7 5 20 [2, 2, 0, 0, 2, 1, 0] [2, 1, 1, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112200 : mirrorTrits [2, 2, 0, 0, 2, 1, 0] = [1, 1, 0, 0, 1, 2, 0] := by
  decide

theorem demoInv_2112200 : specInv 7 5 20 [2, 1, 1, 2, 2, 0, 0] = some [1, 1, 0, 0, 1, 2, 0] :=
  specInv_mirror_7 [2, 1, 1, 2, 2, 0, 0] [0, 2, 1, 1, 1, 1, 0] [0, 1, 1, 2, 0, 0, 2] [2, 2, 0, 0, 2, 1, 0] [1, 1, 0, 0, 1, 2, 0] demoR1_2112200 demoR2_2112200 demoC_2112200 demoM_2112200 demoMir_2112200

theorem demoR1_0212200 : invRung 7 5 20 [0, 2, 1, 2, 2, 0, 0] [0, 2, 1, 2, 2, 0, 0] 1 2 false = ([0, 0, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_0212200 : invRung 7 5 20 [0, 2, 1, 2, 2, 0, 0] [0, 0, 0, 1, 2, 2, 1] 3 1 true = ([1, 2, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_0212200 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 1, 2] = [2, 1, 2, 2, 0, 1, 0] := by
  decide

theorem demoM_0212200 : fieldMul 7 5 20 [2, 1, 2, 2, 0, 1, 0] [0, 2, 1, 2, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0212200 : specInv 7 5 20 [0, 2, 1, 2, 2, 0, 0] = some [2, 1, 2, 2, 0, 1, 0] :=
  specInv_white_7 [0, 2, 1, 2, 2, 0, 0] [0, 0, 0, 1, 2, 2, 1] [1, 2, 1, 0, 1, 1, 2] [2, 1, 2, 2, 0, 1, 0] demoR1_0212200 demoR2_0212200 demoC_0212200 demoM_0212200

theorem demoR1_1212200 : invRung 7 5 20 [1, 2, 1, 2, 2, 0, 0] [1, 2, 1, 2, 2, 0, 0] 1 2 false = ([0, 1, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1212200 : invRung 7 5 20 [1, 2, 1, 2, 2, 0, 0] [0, 1, 0, 2, 0, 1, 2] 3 1 true = ([1, 1, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_1212200 : fieldCube 7 5 20 [1, 1, 2, 1, 0, 2, 2] = [1, 1, 1, 0, 1, 2, 2] := by
  decide

theorem demoM_1212200 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 2, 2] [1, 2, 1, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212200 : mirrorTrits [1, 1, 1, 0, 1, 2, 2] = [2, 2, 2, 0, 2, 1, 1] := by
  decide

theorem demoInv_1212200 : specInv 7 5 20 [1, 2, 1, 2, 2, 0, 0] = some [2, 2, 2, 0, 2, 1, 1] :=
  specInv_mirror_7 [1, 2, 1, 2, 2, 0, 0] [0, 1, 0, 2, 0, 1, 2] [1, 1, 2, 1, 0, 2, 2] [1, 1, 1, 0, 1, 2, 2] [2, 2, 2, 0, 2, 1, 1] demoR1_1212200 demoR2_1212200 demoC_1212200 demoM_1212200 demoMir_1212200

theorem demoR1_2212200 : invRung 7 5 20 [2, 2, 1, 2, 2, 0, 0] [2, 2, 1, 2, 2, 0, 0] 1 2 false = ([0, 0, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_2212200 : invRung 7 5 20 [2, 2, 1, 2, 2, 0, 0] [0, 0, 1, 1, 1, 0, 2] 3 1 true = ([1, 0, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2212200 : fieldCube 7 5 20 [1, 0, 1, 2, 0, 1, 0] = [1, 1, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_2212200 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 0, 0] [2, 2, 1, 2, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2212200 : specInv 7 5 20 [2, 2, 1, 2, 2, 0, 0] = some [1, 1, 0, 0, 1, 0, 0] :=
  specInv_white_7 [2, 2, 1, 2, 2, 0, 0] [0, 0, 1, 1, 1, 0, 2] [1, 0, 1, 2, 0, 1, 0] [1, 1, 0, 0, 1, 0, 0] demoR1_2212200 demoR2_2212200 demoC_2212200 demoM_2212200

theorem demoR1_0022200 : invRung 7 5 20 [0, 0, 2, 2, 2, 0, 0] [0, 0, 2, 2, 2, 0, 0] 1 2 false = ([2, 2, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0022200 : invRung 7 5 20 [0, 0, 2, 2, 2, 0, 0] [2, 2, 2, 0, 0, 0, 0] 3 1 true = ([1, 0, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0022200 : fieldCube 7 5 20 [1, 0, 2, 0, 2, 1, 2] = [2, 2, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_0022200 : fieldMul 7 5 20 [2, 2, 2, 1, 0, 2, 2] [0, 0, 2, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022200 : mirrorTrits [2, 2, 2, 1, 0, 2, 2] = [1, 1, 1, 2, 0, 1, 1] := by
  decide

theorem demoInv_0022200 : specInv 7 5 20 [0, 0, 2, 2, 2, 0, 0] = some [1, 1, 1, 2, 0, 1, 1] :=
  specInv_mirror_7 [0, 0, 2, 2, 2, 0, 0] [2, 2, 2, 0, 0, 0, 0] [1, 0, 2, 0, 2, 1, 2] [2, 2, 2, 1, 0, 2, 2] [1, 1, 1, 2, 0, 1, 1] demoR1_0022200 demoR2_0022200 demoC_0022200 demoM_0022200 demoMir_0022200

theorem demoR1_1022200 : invRung 7 5 20 [1, 0, 2, 2, 2, 0, 0] [1, 0, 2, 2, 2, 0, 0] 1 2 false = ([2, 2, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1022200 : invRung 7 5 20 [1, 0, 2, 2, 2, 0, 0] [2, 2, 2, 1, 1, 0, 0] 3 1 true = ([2, 0, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_1022200 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 0, 0] = [1, 0, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_1022200 : fieldMul 7 5 20 [1, 0, 2, 0, 0, 2, 2] [1, 0, 2, 2, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1022200 : specInv 7 5 20 [1, 0, 2, 2, 2, 0, 0] = some [1, 0, 2, 0, 0, 2, 2] :=
  specInv_white_7 [1, 0, 2, 2, 2, 0, 0] [2, 2, 2, 1, 1, 0, 0] [2, 0, 2, 2, 0, 0, 0] [1, 0, 2, 0, 0, 2, 2] demoR1_1022200 demoR2_1022200 demoC_1022200 demoM_1022200

theorem demoR1_2022200 : invRung 7 5 20 [2, 0, 2, 2, 2, 0, 0] [2, 0, 2, 2, 2, 0, 0] 1 2 false = ([1, 1, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_2022200 : invRung 7 5 20 [2, 0, 2, 2, 2, 0, 0] [1, 1, 2, 1, 1, 1, 0] 3 1 true = ([2, 0, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_2022200 : fieldCube 7 5 20 [2, 0, 0, 1, 2, 0, 0] = [0, 2, 1, 2, 0, 0, 2] := by
  decide

theorem demoM_2022200 : fieldMul 7 5 20 [0, 2, 1, 2, 0, 0, 2] [2, 0, 2, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022200 : mirrorTrits [0, 2, 1, 2, 0, 0, 2] = [0, 1, 2, 1, 0, 0, 1] := by
  decide

theorem demoInv_2022200 : specInv 7 5 20 [2, 0, 2, 2, 2, 0, 0] = some [0, 1, 2, 1, 0, 0, 1] :=
  specInv_mirror_7 [2, 0, 2, 2, 2, 0, 0] [1, 1, 2, 1, 1, 1, 0] [2, 0, 0, 1, 2, 0, 0] [0, 2, 1, 2, 0, 0, 2] [0, 1, 2, 1, 0, 0, 1] demoR1_2022200 demoR2_2022200 demoC_2022200 demoM_2022200 demoMir_2022200

theorem demoR1_0122200 : invRung 7 5 20 [0, 1, 2, 2, 2, 0, 0] [0, 1, 2, 2, 2, 0, 0] 1 2 false = ([2, 0, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0122200 : invRung 7 5 20 [0, 1, 2, 2, 2, 0, 0] [2, 0, 2, 1, 0, 0, 0] 3 1 true = ([2, 1, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_0122200 : fieldCube 7 5 20 [2, 1, 1, 2, 0, 2, 2] = [0, 1, 2, 0, 1, 0, 1] := by
  decide

theorem demoM_0122200 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 0, 1] [0, 1, 2, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122200 : mirrorTrits [0, 1, 2, 0, 1, 0, 1] = [0, 2, 1, 0, 2, 0, 2] := by
  decide

theorem demoInv_0122200 : specInv 7 5 20 [0, 1, 2, 2, 2, 0, 0] = some [0, 2, 1, 0, 2, 0, 2] :=
  specInv_mirror_7 [0, 1, 2, 2, 2, 0, 0] [2, 0, 2, 1, 0, 0, 0] [2, 1, 1, 2, 0, 2, 2] [0, 1, 2, 0, 1, 0, 1] [0, 2, 1, 0, 2, 0, 2] demoR1_0122200 demoR2_0122200 demoC_0122200 demoM_0122200 demoMir_0122200

theorem demoR1_1122200 : invRung 7 5 20 [1, 1, 2, 2, 2, 0, 0] [1, 1, 2, 2, 2, 0, 0] 1 2 false = ([1, 1, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_1122200 : invRung 7 5 20 [1, 1, 2, 2, 2, 0, 0] [1, 1, 0, 0, 1, 2, 0] 3 1 true = ([2, 1, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1122200 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 1, 0] = [0, 2, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_1122200 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 2, 1] [1, 1, 2, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122200 : mirrorTrits [0, 2, 1, 2, 1, 2, 1] = [0, 1, 2, 1, 2, 1, 2] := by
  decide

theorem demoInv_1122200 : specInv 7 5 20 [1, 1, 2, 2, 2, 0, 0] = some [0, 1, 2, 1, 2, 1, 2] :=
  specInv_mirror_7 [1, 1, 2, 2, 2, 0, 0] [1, 1, 0, 0, 1, 2, 0] [2, 1, 1, 0, 1, 1, 0] [0, 2, 1, 2, 1, 2, 1] [0, 1, 2, 1, 2, 1, 2] demoR1_1122200 demoR2_1122200 demoC_1122200 demoM_1122200 demoMir_1122200

theorem demoR1_2122200 : invRung 7 5 20 [2, 1, 2, 2, 2, 0, 0] [2, 1, 2, 2, 2, 0, 0] 1 2 false = ([1, 0, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_2122200 : invRung 7 5 20 [2, 1, 2, 2, 2, 0, 0] [1, 0, 0, 0, 1, 1, 0] 3 1 true = ([2, 1, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_2122200 : fieldCube 7 5 20 [2, 1, 0, 0, 2, 2, 0] = [1, 1, 2, 0, 2, 1, 0] := by
  decide

theorem demoM_2122200 : fieldMul 7 5 20 [1, 1, 2, 0, 2, 1, 0] [2, 1, 2, 2, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2122200 : specInv 7 5 20 [2, 1, 2, 2, 2, 0, 0] = some [1, 1, 2, 0, 2, 1, 0] :=
  specInv_white_7 [2, 1, 2, 2, 2, 0, 0] [1, 0, 0, 0, 1, 1, 0] [2, 1, 0, 0, 2, 2, 0] [1, 1, 2, 0, 2, 1, 0] demoR1_2122200 demoR2_2122200 demoC_2122200 demoM_2122200

theorem demoR1_0222200 : invRung 7 5 20 [0, 2, 2, 2, 2, 0, 0] [0, 2, 2, 2, 2, 0, 0] 1 2 false = ([1, 0, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_0222200 : invRung 7 5 20 [0, 2, 2, 2, 2, 0, 0] [1, 0, 0, 0, 0, 2, 1] 3 1 true = ([1, 0, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0222200 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 0, 0] = [2, 0, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_0222200 : fieldMul 7 5 20 [2, 0, 1, 0, 0, 1, 0] [0, 2, 2, 2, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0222200 : specInv 7 5 20 [0, 2, 2, 2, 2, 0, 0] = some [2, 0, 1, 0, 0, 1, 0] :=
  specInv_white_7 [0, 2, 2, 2, 2, 0, 0] [1, 0, 0, 0, 0, 2, 1] [1, 0, 0, 1, 0, 0, 0] [2, 0, 1, 0, 0, 1, 0] demoR1_0222200 demoR2_0222200 demoC_0222200 demoM_0222200

theorem demoR1_1222200 : invRung 7 5 20 [1, 2, 2, 2, 2, 0, 0] [1, 2, 2, 2, 2, 0, 0] 1 2 false = ([2, 0, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_1222200 : invRung 7 5 20 [1, 2, 2, 2, 2, 0, 0] [2, 0, 2, 1, 0, 2, 2] 3 1 true = ([0, 1, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_1222200 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 1, 0] = [0, 2, 0, 2, 1, 1, 0] := by
  decide

theorem demoM_1222200 : fieldMul 7 5 20 [0, 2, 0, 2, 1, 1, 0] [1, 2, 2, 2, 2, 0, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1222200 : specInv 7 5 20 [1, 2, 2, 2, 2, 0, 0] = some [0, 2, 0, 2, 1, 1, 0] :=
  specInv_white_7 [1, 2, 2, 2, 2, 0, 0] [2, 0, 2, 1, 0, 2, 2] [0, 1, 0, 2, 1, 1, 0] [0, 2, 0, 2, 1, 1, 0] demoR1_1222200 demoR2_1222200 demoC_1222200 demoM_1222200

theorem demoR1_2222200 : invRung 7 5 20 [2, 2, 2, 2, 2, 0, 0] [2, 2, 2, 2, 2, 0, 0] 1 2 false = ([0, 0, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_2222200 : invRung 7 5 20 [2, 2, 2, 2, 2, 0, 0] [0, 0, 2, 2, 2, 1, 0] 3 1 true = ([1, 0, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2222200 : fieldCube 7 5 20 [1, 0, 2, 0, 1, 0, 0] = [1, 1, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_2222200 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 1, 0] [2, 2, 2, 2, 2, 0, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222200 : mirrorTrits [1, 1, 0, 1, 0, 1, 0] = [2, 2, 0, 2, 0, 2, 0] := by
  decide

theorem demoInv_2222200 : specInv 7 5 20 [2, 2, 2, 2, 2, 0, 0] = some [2, 2, 0, 2, 0, 2, 0] :=
  specInv_mirror_7 [2, 2, 2, 2, 2, 0, 0] [0, 0, 2, 2, 2, 1, 0] [1, 0, 2, 0, 1, 0, 0] [1, 1, 0, 1, 0, 1, 0] [2, 2, 0, 2, 0, 2, 0] demoR1_2222200 demoR2_2222200 demoC_2222200 demoM_2222200 demoMir_2222200

theorem demoR1_0000010 : invRung 7 5 20 [0, 0, 0, 0, 0, 1, 0] [0, 0, 0, 0, 0, 1, 0] 1 2 false = ([1, 0, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_0000010 : invRung 7 5 20 [0, 0, 0, 0, 0, 1, 0] [1, 0, 0, 1, 2, 2, 0] 3 1 true = ([0, 2, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0000010 : fieldCube 7 5 20 [0, 2, 1, 0, 0, 2, 1] = [2, 0, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_0000010 : fieldMul 7 5 20 [2, 0, 1, 0, 0, 0, 0] [0, 0, 0, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0000010 : specInv 7 5 20 [0, 0, 0, 0, 0, 1, 0] = some [2, 0, 1, 0, 0, 0, 0] :=
  specInv_white_7 [0, 0, 0, 0, 0, 1, 0] [1, 0, 0, 1, 2, 2, 0] [0, 2, 1, 0, 0, 2, 1] [2, 0, 1, 0, 0, 0, 0] demoR1_0000010 demoR2_0000010 demoC_0000010 demoM_0000010

theorem demoR1_1000010 : invRung 7 5 20 [1, 0, 0, 0, 0, 1, 0] [1, 0, 0, 0, 0, 1, 0] 1 2 false = ([0, 2, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_1000010 : invRung 7 5 20 [1, 0, 0, 0, 0, 1, 0] [0, 2, 1, 0, 0, 0, 0] 3 1 true = ([0, 0, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_1000010 : fieldCube 7 5 20 [0, 0, 1, 2, 0, 2, 1] = [1, 0, 0, 1, 0, 2, 0] := by
  decide

theorem demoM_1000010 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 2, 0] [1, 0, 0, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1000010 : specInv 7 5 20 [1, 0, 0, 0, 0, 1, 0] = some [1, 0, 0, 1, 0, 2, 0] :=
  specInv_white_7 [1, 0, 0, 0, 0, 1, 0] [0, 2, 1, 0, 0, 0, 0] [0, 0, 1, 2, 0, 2, 1] [1, 0, 0, 1, 0, 2, 0] demoR1_1000010 demoR2_1000010 demoC_1000010 demoM_1000010

theorem demoR1_2000010 : invRung 7 5 20 [2, 0, 0, 0, 0, 1, 0] [2, 0, 0, 0, 0, 1, 0] 1 2 false = ([2, 2, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_2000010 : invRung 7 5 20 [2, 0, 0, 0, 0, 1, 0] [2, 2, 2, 1, 0, 1, 1] 3 1 true = ([2, 1, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2000010 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 2, 2] = [0, 2, 2, 1, 1, 1, 1] := by
  decide

theorem demoM_2000010 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 1, 1] [2, 0, 0, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2000010 : specInv 7 5 20 [2, 0, 0, 0, 0, 1, 0] = some [0, 2, 2, 1, 1, 1, 1] :=
  specInv_white_7 [2, 0, 0, 0, 0, 1, 0] [2, 2, 2, 1, 0, 1, 1] [2, 1, 0, 2, 1, 2, 2] [0, 2, 2, 1, 1, 1, 1] demoR1_2000010 demoR2_2000010 demoC_2000010 demoM_2000010

theorem demoR1_0100010 : invRung 7 5 20 [0, 1, 0, 0, 0, 1, 0] [0, 1, 0, 0, 0, 1, 0] 1 2 false = ([0, 1, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_0100010 : invRung 7 5 20 [0, 1, 0, 0, 0, 1, 0] [0, 1, 0, 2, 1, 1, 2] 3 1 true = ([2, 2, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_0100010 : fieldCube 7 5 20 [2, 2, 1, 1, 2, 1, 0] = [1, 0, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_0100010 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 1, 2] [0, 1, 0, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0100010 : specInv 7 5 20 [0, 1, 0, 0, 0, 1, 0] = some [1, 0, 2, 1, 1, 1, 2] :=
  specInv_white_7 [0, 1, 0, 0, 0, 1, 0] [0, 1, 0, 2, 1, 1, 2] [2, 2, 1, 1, 2, 1, 0] [1, 0, 2, 1, 1, 1, 2] demoR1_0100010 demoR2_0100010 demoC_0100010 demoM_0100010

theorem demoR1_1100010 : invRung 7 5 20 [1, 1, 0, 0, 0, 1, 0] [1, 1, 0, 0, 0, 1, 0] 1 2 false = ([0, 1, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_1100010 : invRung 7 5 20 [1, 1, 0, 0, 0, 1, 0] [0, 1, 0, 0, 0, 0, 2] 3 1 true = ([1, 1, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_1100010 : fieldCube 7 5 20 [1, 1, 2, 2, 0, 0, 1] = [0, 1, 1, 2, 1, 0, 0] := by
  decide

theorem demoM_1100010 : fieldMul 7 5 20 [0, 1, 1, 2, 1, 0, 0] [1, 1, 0, 0, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1100010 : mirrorTrits [0, 1, 1, 2, 1, 0, 0] = [0, 2, 2, 1, 2, 0, 0] := by
  decide

theorem demoInv_1100010 : specInv 7 5 20 [1, 1, 0, 0, 0, 1, 0] = some [0, 2, 2, 1, 2, 0, 0] :=
  specInv_mirror_7 [1, 1, 0, 0, 0, 1, 0] [0, 1, 0, 0, 0, 0, 2] [1, 1, 2, 2, 0, 0, 1] [0, 1, 1, 2, 1, 0, 0] [0, 2, 2, 1, 2, 0, 0] demoR1_1100010 demoR2_1100010 demoC_1100010 demoM_1100010 demoMir_1100010

theorem demoR1_2100010 : invRung 7 5 20 [2, 1, 0, 0, 0, 1, 0] [2, 1, 0, 0, 0, 1, 0] 1 2 false = ([2, 1, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_2100010 : invRung 7 5 20 [2, 1, 0, 0, 0, 1, 0] [2, 1, 2, 2, 1, 1, 0] 3 1 true = ([2, 1, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_2100010 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 1, 0] = [1, 1, 2, 1, 1, 2, 0] := by
  decide

theorem demoM_2100010 : fieldMul 7 5 20 [1, 1, 2, 1, 1, 2, 0] [2, 1, 0, 0, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100010 : mirrorTrits [1, 1, 2, 1, 1, 2, 0] = [2, 2, 1, 2, 2, 1, 0] := by
  decide

theorem demoInv_2100010 : specInv 7 5 20 [2, 1, 0, 0, 0, 1, 0] = some [2, 2, 1, 2, 2, 1, 0] :=
  specInv_mirror_7 [2, 1, 0, 0, 0, 1, 0] [2, 1, 2, 2, 1, 1, 0] [2, 1, 1, 1, 0, 1, 0] [1, 1, 2, 1, 1, 2, 0] [2, 2, 1, 2, 2, 1, 0] demoR1_2100010 demoR2_2100010 demoC_2100010 demoM_2100010 demoMir_2100010

theorem demoR1_0200010 : invRung 7 5 20 [0, 2, 0, 0, 0, 1, 0] [0, 2, 0, 0, 0, 1, 0] 1 2 false = ([1, 0, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_0200010 : invRung 7 5 20 [0, 2, 0, 0, 0, 1, 0] [1, 0, 0, 0, 1, 0, 1] 3 1 true = ([0, 2, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0200010 : fieldCube 7 5 20 [0, 2, 2, 2, 1, 0, 1] = [2, 2, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_0200010 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 1, 1] [0, 2, 0, 0, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200010 : mirrorTrits [2, 2, 1, 1, 1, 1, 1] = [1, 1, 2, 2, 2, 2, 2] := by
  decide

theorem demoInv_0200010 : specInv 7 5 20 [0, 2, 0, 0, 0, 1, 0] = some [1, 1, 2, 2, 2, 2, 2] :=
  specInv_mirror_7 [0, 2, 0, 0, 0, 1, 0] [1, 0, 0, 0, 1, 0, 1] [0, 2, 2, 2, 1, 0, 1] [2, 2, 1, 1, 1, 1, 1] [1, 1, 2, 2, 2, 2, 2] demoR1_0200010 demoR2_0200010 demoC_0200010 demoM_0200010 demoMir_0200010

theorem demoR1_1200010 : invRung 7 5 20 [1, 2, 0, 0, 0, 1, 0] [1, 2, 0, 0, 0, 1, 0] 1 2 false = ([2, 2, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_1200010 : invRung 7 5 20 [1, 2, 0, 0, 0, 1, 0] [2, 2, 2, 1, 0, 2, 2] 3 1 true = ([2, 1, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_1200010 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 1, 2] = [1, 1, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_1200010 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 2, 1] [1, 2, 0, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1200010 : specInv 7 5 20 [1, 2, 0, 0, 0, 1, 0] = some [1, 1, 0, 1, 0, 2, 1] :=
  specInv_white_7 [1, 2, 0, 0, 0, 1, 0] [2, 2, 2, 1, 0, 2, 2] [2, 1, 2, 1, 1, 1, 2] [1, 1, 0, 1, 0, 2, 1] demoR1_1200010 demoR2_1200010 demoC_1200010 demoM_1200010

theorem demoR1_2200010 : invRung 7 5 20 [2, 2, 0, 0, 0, 1, 0] [2, 2, 0, 0, 0, 1, 0] 1 2 false = ([1, 0, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_2200010 : invRung 7 5 20 [2, 2, 0, 0, 0, 1, 0] [1, 0, 2, 2, 1, 2, 1] 3 1 true = ([1, 0, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_2200010 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 2, 0] = [0, 2, 2, 0, 2, 2, 2] := by
  decide

theorem demoM_2200010 : fieldMul 7 5 20 [0, 2, 2, 0, 2, 2, 2] [2, 2, 0, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2200010 : specInv 7 5 20 [2, 2, 0, 0, 0, 1, 0] = some [0, 2, 2, 0, 2, 2, 2] :=
  specInv_white_7 [2, 2, 0, 0, 0, 1, 0] [1, 0, 2, 2, 1, 2, 1] [1, 0, 1, 0, 0, 2, 0] [0, 2, 2, 0, 2, 2, 2] demoR1_2200010 demoR2_2200010 demoC_2200010 demoM_2200010

theorem demoR1_0010010 : invRung 7 5 20 [0, 0, 1, 0, 0, 1, 0] [0, 0, 1, 0, 0, 1, 0] 1 2 false = ([1, 2, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_0010010 : invRung 7 5 20 [0, 0, 1, 0, 0, 1, 0] [1, 2, 0, 0, 2, 0, 2] 3 1 true = ([1, 2, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_0010010 : fieldCube 7 5 20 [1, 2, 0, 1, 2, 2, 0] = [1, 1, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_0010010 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 2, 0] [0, 0, 1, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0010010 : specInv 7 5 20 [0, 0, 1, 0, 0, 1, 0] = some [1, 1, 0, 1, 2, 2, 0] :=
  specInv_white_7 [0, 0, 1, 0, 0, 1, 0] [1, 2, 0, 0, 2, 0, 2] [1, 2, 0, 1, 2, 2, 0] [1, 1, 0, 1, 2, 2, 0] demoR1_0010010 demoR2_0010010 demoC_0010010 demoM_0010010

theorem demoR1_1010010 : invRung 7 5 20 [1, 0, 1, 0, 0, 1, 0] [1, 0, 1, 0, 0, 1, 0] 1 2 false = ([1, 1, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_1010010 : invRung 7 5 20 [1, 0, 1, 0, 0, 1, 0] [1, 1, 0, 1, 2, 0, 1] 3 1 true = ([0, 0, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1010010 : fieldCube 7 5 20 [0, 0, 2, 0, 1, 0, 0] = [0, 1, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_1010010 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 1, 0] [1, 0, 1, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1010010 : specInv 7 5 20 [1, 0, 1, 0, 0, 1, 0] = some [0, 1, 0, 1, 0, 1, 0] :=
  specInv_white_7 [1, 0, 1, 0, 0, 1, 0] [1, 1, 0, 1, 2, 0, 1] [0, 0, 2, 0, 1, 0, 0] [0, 1, 0, 1, 0, 1, 0] demoR1_1010010 demoR2_1010010 demoC_1010010 demoM_1010010

theorem demoR1_2010010 : invRung 7 5 20 [2, 0, 1, 0, 0, 1, 0] [2, 0, 1, 0, 0, 1, 0] 1 2 false = ([1, 0, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_2010010 : invRung 7 5 20 [2, 0, 1, 0, 0, 1, 0] [1, 0, 0, 0, 0, 2, 2] 3 1 true = ([2, 0, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_2010010 : fieldCube 7 5 20 [2, 0, 1, 1, 0, 0, 2] = [0, 2, 2, 2, 2, 0, 0] := by
  decide

theorem demoM_2010010 : fieldMul 7 5 20 [0, 2, 2, 2, 2, 0, 0] [2, 0, 1, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2010010 : specInv 7 5 20 [2, 0, 1, 0, 0, 1, 0] = some [0, 2, 2, 2, 2, 0, 0] :=
  specInv_white_7 [2, 0, 1, 0, 0, 1, 0] [1, 0, 0, 0, 0, 2, 2] [2, 0, 1, 1, 0, 0, 2] [0, 2, 2, 2, 2, 0, 0] demoR1_2010010 demoR2_2010010 demoC_2010010 demoM_2010010

theorem demoR1_0110010 : invRung 7 5 20 [0, 1, 1, 0, 0, 1, 0] [0, 1, 1, 0, 0, 1, 0] 1 2 false = ([0, 0, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_0110010 : invRung 7 5 20 [0, 1, 1, 0, 0, 1, 0] [0, 0, 1, 0, 0, 0, 1] 3 1 true = ([1, 0, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_0110010 : fieldCube 7 5 20 [1, 0, 2, 2, 0, 2, 2] = [2, 1, 2, 2, 1, 0, 2] := by
  decide

theorem demoM_0110010 : fieldMul 7 5 20 [2, 1, 2, 2, 1, 0, 2] [0, 1, 1, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0110010 : specInv 7 5 20 [0, 1, 1, 0, 0, 1, 0] = some [2, 1, 2, 2, 1, 0, 2] :=
  specInv_white_7 [0, 1, 1, 0, 0, 1, 0] [0, 0, 1, 0, 0, 0, 1] [1, 0, 2, 2, 0, 2, 2] [2, 1, 2, 2, 1, 0, 2] demoR1_0110010 demoR2_0110010 demoC_0110010 demoM_0110010

theorem demoR1_1110010 : invRung 7 5 20 [1, 1, 1, 0, 0, 1, 0] [1, 1, 1, 0, 0, 1, 0] 1 2 false = ([1, 2, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_1110010 : invRung 7 5 20 [1, 1, 1, 0, 0, 1, 0] [1, 2, 1, 2, 2, 2, 2] 3 1 true = ([2, 1, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1110010 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 2, 0] = [2, 1, 0, 0, 2, 2, 1] := by
  decide

theorem demoM_1110010 : fieldMul 7 5 20 [2, 1, 0, 0, 2, 2, 1] [1, 1, 1, 0, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1110010 : mirrorTrits [2, 1, 0, 0, 2, 2, 1] = [1, 2, 0, 0, 1, 1, 2] := by
  decide

theorem demoInv_1110010 : specInv 7 5 20 [1, 1, 1, 0, 0, 1, 0] = some [1, 2, 0, 0, 1, 1, 2] :=
  specInv_mirror_7 [1, 1, 1, 0, 0, 1, 0] [1, 2, 1, 2, 2, 2, 2] [2, 1, 1, 1, 2, 2, 0] [2, 1, 0, 0, 2, 2, 1] [1, 2, 0, 0, 1, 1, 2] demoR1_1110010 demoR2_1110010 demoC_1110010 demoM_1110010 demoMir_1110010

theorem demoR1_2110010 : invRung 7 5 20 [2, 1, 1, 0, 0, 1, 0] [2, 1, 1, 0, 0, 1, 0] 1 2 false = ([1, 0, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_2110010 : invRung 7 5 20 [2, 1, 1, 0, 0, 1, 0] [1, 0, 0, 1, 2, 2, 2] 3 1 true = ([1, 2, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_2110010 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 1, 2] = [2, 2, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_2110010 : fieldMul 7 5 20 [2, 2, 2, 0, 0, 2, 1] [2, 1, 1, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2110010 : specInv 7 5 20 [2, 1, 1, 0, 0, 1, 0] = some [2, 2, 2, 0, 0, 2, 1] :=
  specInv_white_7 [2, 1, 1, 0, 0, 1, 0] [1, 0, 0, 1, 2, 2, 2] [1, 2, 1, 0, 2, 1, 2] [2, 2, 2, 0, 0, 2, 1] demoR1_2110010 demoR2_2110010 demoC_2110010 demoM_2110010

theorem demoR1_0210010 : invRung 7 5 20 [0, 2, 1, 0, 0, 1, 0] [0, 2, 1, 0, 0, 1, 0] 1 2 false = ([2, 1, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_0210010 : invRung 7 5 20 [0, 2, 1, 0, 0, 1, 0] [2, 1, 0, 0, 2, 1, 0] 3 1 true = ([2, 0, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0210010 : fieldCube 7 5 20 [2, 0, 0, 2, 1, 1, 2] = [2, 1, 1, 0, 0, 0, 2] := by
  decide

theorem demoM_0210010 : fieldMul 7 5 20 [2, 1, 1, 0, 0, 0, 2] [0, 2, 1, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0210010 : specInv 7 5 20 [0, 2, 1, 0, 0, 1, 0] = some [2, 1, 1, 0, 0, 0, 2] :=
  specInv_white_7 [0, 2, 1, 0, 0, 1, 0] [2, 1, 0, 0, 2, 1, 0] [2, 0, 0, 2, 1, 1, 2] [2, 1, 1, 0, 0, 0, 2] demoR1_0210010 demoR2_0210010 demoC_0210010 demoM_0210010

theorem demoR1_1210010 : invRung 7 5 20 [1, 2, 1, 0, 0, 1, 0] [1, 2, 1, 0, 0, 1, 0] 1 2 false = ([1, 1, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_1210010 : invRung 7 5 20 [1, 2, 1, 0, 0, 1, 0] [1, 1, 0, 1, 2, 1, 1] 3 1 true = ([1, 2, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_1210010 : fieldCube 7 5 20 [1, 2, 0, 0, 0, 2, 2] = [0, 1, 0, 1, 1, 1, 0] := by
  decide

theorem demoM_1210010 : fieldMul 7 5 20 [0, 1, 0, 1, 1, 1, 0] [1, 2, 1, 0, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1210010 : mirrorTrits [0, 1, 0, 1, 1, 1, 0] = [0, 2, 0, 2, 2, 2, 0] := by
  decide

theorem demoInv_1210010 : specInv 7 5 20 [1, 2, 1, 0, 0, 1, 0] = some [0, 2, 0, 2, 2, 2, 0] :=
  specInv_mirror_7 [1, 2, 1, 0, 0, 1, 0] [1, 1, 0, 1, 2, 1, 1] [1, 2, 0, 0, 0, 2, 2] [0, 1, 0, 1, 1, 1, 0] [0, 2, 0, 2, 2, 2, 0] demoR1_1210010 demoR2_1210010 demoC_1210010 demoM_1210010 demoMir_1210010

theorem demoR1_2210010 : invRung 7 5 20 [2, 2, 1, 0, 0, 1, 0] [2, 2, 1, 0, 0, 1, 0] 1 2 false = ([1, 2, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_2210010 : invRung 7 5 20 [2, 2, 1, 0, 0, 1, 0] [1, 2, 1, 1, 0, 1, 1] 3 1 true = ([0, 2, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_2210010 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 1, 0] = [0, 2, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_2210010 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 1, 1] [2, 2, 1, 0, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210010 : mirrorTrits [0, 2, 0, 0, 1, 1, 1] = [0, 1, 0, 0, 2, 2, 2] := by
  decide

theorem demoInv_2210010 : specInv 7 5 20 [2, 2, 1, 0, 0, 1, 0] = some [0, 1, 0, 0, 2, 2, 2] :=
  specInv_mirror_7 [2, 2, 1, 0, 0, 1, 0] [1, 2, 1, 1, 0, 1, 1] [0, 2, 1, 2, 1, 1, 0] [0, 2, 0, 0, 1, 1, 1] [0, 1, 0, 0, 2, 2, 2] demoR1_2210010 demoR2_2210010 demoC_2210010 demoM_2210010 demoMir_2210010

theorem demoR1_0020010 : invRung 7 5 20 [0, 0, 2, 0, 0, 1, 0] [0, 0, 2, 0, 0, 1, 0] 1 2 false = ([1, 2, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_0020010 : invRung 7 5 20 [0, 0, 2, 0, 0, 1, 0] [1, 2, 2, 0, 1, 0, 2] 3 1 true = ([0, 0, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0020010 : fieldCube 7 5 20 [0, 0, 1, 0, 0, 0, 1] = [0, 1, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_0020010 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 1, 2] [0, 0, 2, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0020010 : specInv 7 5 20 [0, 0, 2, 0, 0, 1, 0] = some [0, 1, 2, 1, 1, 1, 2] :=
  specInv_white_7 [0, 0, 2, 0, 0, 1, 0] [1, 2, 2, 0, 1, 0, 2] [0, 0, 1, 0, 0, 0, 1] [0, 1, 2, 1, 1, 1, 2] demoR1_0020010 demoR2_0020010 demoC_0020010 demoM_0020010

theorem demoR1_1020010 : invRung 7 5 20 [1, 0, 2, 0, 0, 1, 0] [1, 0, 2, 0, 0, 1, 0] 1 2 false = ([1, 1, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_1020010 : invRung 7 5 20 [1, 0, 2, 0, 0, 1, 0] [1, 1, 2, 0, 0, 2, 2] 3 1 true = ([1, 2, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_1020010 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 2, 0] = [2, 1, 1, 1, 2, 0, 2] := by
  decide

theorem demoM_1020010 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 0, 2] [1, 0, 2, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1020010 : specInv 7 5 20 [1, 0, 2, 0, 0, 1, 0] = some [2, 1, 1, 1, 2, 0, 2] :=
  specInv_white_7 [1, 0, 2, 0, 0, 1, 0] [1, 1, 2, 0, 0, 2, 2] [1, 2, 2, 2, 2, 2, 0] [2, 1, 1, 1, 2, 0, 2] demoR1_1020010 demoR2_1020010 demoC_1020010 demoM_1020010

theorem demoR1_2020010 : invRung 7 5 20 [2, 0, 2, 0, 0, 1, 0] [2, 0, 2, 0, 0, 1, 0] 1 2 false = ([1, 2, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_2020010 : invRung 7 5 20 [2, 0, 2, 0, 0, 1, 0] [1, 2, 2, 0, 2, 2, 2] 3 1 true = ([1, 0, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_2020010 : fieldCube 7 5 20 [1, 0, 0, 2, 1, 1, 1] = [1, 0, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_2020010 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 2, 1] [2, 0, 2, 0, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020010 : mirrorTrits [1, 0, 2, 2, 2, 2, 1] = [2, 0, 1, 1, 1, 1, 2] := by
  decide

theorem demoInv_2020010 : specInv 7 5 20 [2, 0, 2, 0, 0, 1, 0] = some [2, 0, 1, 1, 1, 1, 2] :=
  specInv_mirror_7 [2, 0, 2, 0, 0, 1, 0] [1, 2, 2, 0, 2, 2, 2] [1, 0, 0, 2, 1, 1, 1] [1, 0, 2, 2, 2, 2, 1] [2, 0, 1, 1, 1, 1, 2] demoR1_2020010 demoR2_2020010 demoC_2020010 demoM_2020010 demoMir_2020010

theorem demoR1_0120010 : invRung 7 5 20 [0, 1, 2, 0, 0, 1, 0] [0, 1, 2, 0, 0, 1, 0] 1 2 false = ([0, 2, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0120010 : invRung 7 5 20 [0, 1, 2, 0, 0, 1, 0] [0, 2, 0, 1, 0, 0, 0] 3 1 true = ([0, 0, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_0120010 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 0, 2] = [1, 1, 2, 1, 2, 2, 1] := by
  decide

theorem demoM_0120010 : fieldMul 7 5 20 [1, 1, 2, 1, 2, 2, 1] [0, 1, 2, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0120010 : specInv 7 5 20 [0, 1, 2, 0, 0, 1, 0] = some [1, 1, 2, 1, 2, 2, 1] :=
  specInv_white_7 [0, 1, 2, 0, 0, 1, 0] [0, 2, 0, 1, 0, 0, 0] [0, 0, 0, 1, 2, 0, 2] [1, 1, 2, 1, 2, 2, 1] demoR1_0120010 demoR2_0120010 demoC_0120010 demoM_0120010

theorem demoR1_1120010 : invRung 7 5 20 [1, 1, 2, 0, 0, 1, 0] [1, 1, 2, 0, 0, 1, 0] 1 2 false = ([1, 0, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1120010 : invRung 7 5 20 [1, 1, 2, 0, 0, 1, 0] [1, 0, 1, 1, 2, 2, 1] 3 1 true = ([1, 1, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_1120010 : fieldCube 7 5 20 [1, 1, 2, 2, 1, 0, 0] = [0, 1, 2, 2, 0, 0, 0] := by
  decide

theorem demoM_1120010 : fieldMul 7 5 20 [0, 1, 2, 2, 0, 0, 0] [1, 1, 2, 0, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120010 : mirrorTrits [0, 1, 2, 2, 0, 0, 0] = [0, 2, 1, 1, 0, 0, 0] := by
  decide

theorem demoInv_1120010 : specInv 7 5 20 [1, 1, 2, 0, 0, 1, 0] = some [0, 2, 1, 1, 0, 0, 0] :=
  specInv_mirror_7 [1, 1, 2, 0, 0, 1, 0] [1, 0, 1, 1, 2, 2, 1] [1, 1, 2, 2, 1, 0, 0] [0, 1, 2, 2, 0, 0, 0] [0, 2, 1, 1, 0, 0, 0] demoR1_1120010 demoR2_1120010 demoC_1120010 demoM_1120010 demoMir_1120010

theorem demoR1_2120010 : invRung 7 5 20 [2, 1, 2, 0, 0, 1, 0] [2, 1, 2, 0, 0, 1, 0] 1 2 false = ([1, 2, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2120010 : invRung 7 5 20 [2, 1, 2, 0, 0, 1, 0] [1, 2, 1, 0, 1, 1, 2] 3 1 true = ([2, 1, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2120010 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 1, 1] = [1, 2, 1, 2, 2, 0, 1] := by
  decide

theorem demoM_2120010 : fieldMul 7 5 20 [1, 2, 1, 2, 2, 0, 1] [2, 1, 2, 0, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2120010 : specInv 7 5 20 [2, 1, 2, 0, 0, 1, 0] = some [1, 2, 1, 2, 2, 0, 1] :=
  specInv_white_7 [2, 1, 2, 0, 0, 1, 0] [1, 2, 1, 0, 1, 1, 2] [2, 1, 1, 1, 0, 1, 1] [1, 2, 1, 2, 2, 0, 1] demoR1_2120010 demoR2_2120010 demoC_2120010 demoM_2120010

theorem demoR1_0220010 : invRung 7 5 20 [0, 2, 2, 0, 0, 1, 0] [0, 2, 2, 0, 0, 1, 0] 1 2 false = ([0, 1, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_0220010 : invRung 7 5 20 [0, 2, 2, 0, 0, 1, 0] [0, 1, 0, 2, 0, 2, 1] 3 1 true = ([1, 1, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_0220010 : fieldCube 7 5 20 [1, 1, 0, 1, 1, 1, 1] = [0, 0, 1, 0, 2, 1, 1] := by
  decide

theorem demoM_0220010 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 1, 1] [0, 2, 2, 0, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0220010 : mirrorTrits [0, 0, 1, 0, 2, 1, 1] = [0, 0, 2, 0, 1, 2, 2] := by
  decide

theorem demoInv_0220010 : specInv 7 5 20 [0, 2, 2, 0, 0, 1, 0] = some [0, 0, 2, 0, 1, 2, 2] :=
  specInv_mirror_7 [0, 2, 2, 0, 0, 1, 0] [0, 1, 0, 2, 0, 2, 1] [1, 1, 0, 1, 1, 1, 1] [0, 0, 1, 0, 2, 1, 1] [0, 0, 2, 0, 1, 2, 2] demoR1_0220010 demoR2_0220010 demoC_0220010 demoM_0220010 demoMir_0220010

theorem demoR1_1220010 : invRung 7 5 20 [1, 2, 2, 0, 0, 1, 0] [1, 2, 2, 0, 0, 1, 0] 1 2 false = ([2, 2, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1220010 : invRung 7 5 20 [1, 2, 2, 0, 0, 1, 0] [2, 2, 2, 0, 1, 0, 1] 3 1 true = ([2, 2, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_1220010 : fieldCube 7 5 20 [2, 2, 0, 0, 2, 1, 0] = [0, 0, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_1220010 : fieldMul 7 5 20 [0, 0, 1, 1, 1, 0, 1] [1, 2, 2, 0, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220010 : mirrorTrits [0, 0, 1, 1, 1, 0, 1] = [0, 0, 2, 2, 2, 0, 2] := by
  decide

theorem demoInv_1220010 : specInv 7 5 20 [1, 2, 2, 0, 0, 1, 0] = some [0, 0, 2, 2, 2, 0, 2] :=
  specInv_mirror_7 [1, 2, 2, 0, 0, 1, 0] [2, 2, 2, 0, 1, 0, 1] [2, 2, 0, 0, 2, 1, 0] [0, 0, 1, 1, 1, 0, 1] [0, 0, 2, 2, 2, 0, 2] demoR1_1220010 demoR2_1220010 demoC_1220010 demoM_1220010 demoMir_1220010

theorem demoR1_2220010 : invRung 7 5 20 [2, 2, 2, 0, 0, 1, 0] [2, 2, 2, 0, 0, 1, 0] 1 2 false = ([2, 0, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2220010 : invRung 7 5 20 [2, 2, 2, 0, 0, 1, 0] [2, 0, 2, 2, 2, 0, 1] 3 1 true = ([2, 1, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2220010 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 2, 1] = [2, 0, 2, 2, 0, 1, 1] := by
  decide

theorem demoM_2220010 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 1, 1] [2, 2, 2, 0, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220010 : mirrorTrits [2, 0, 2, 2, 0, 1, 1] = [1, 0, 1, 1, 0, 2, 2] := by
  decide

theorem demoInv_2220010 : specInv 7 5 20 [2, 2, 2, 0, 0, 1, 0] = some [1, 0, 1, 1, 0, 2, 2] :=
  specInv_mirror_7 [2, 2, 2, 0, 0, 1, 0] [2, 0, 2, 2, 2, 0, 1] [2, 1, 2, 1, 0, 2, 1] [2, 0, 2, 2, 0, 1, 1] [1, 0, 1, 1, 0, 2, 2] demoR1_2220010 demoR2_2220010 demoC_2220010 demoM_2220010 demoMir_2220010

theorem demoR1_0001010 : invRung 7 5 20 [0, 0, 0, 1, 0, 1, 0] [0, 0, 0, 1, 0, 1, 0] 1 2 false = ([2, 0, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_0001010 : invRung 7 5 20 [0, 0, 0, 1, 0, 1, 0] [2, 0, 1, 0, 0, 1, 2] 3 1 true = ([1, 0, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_0001010 : fieldCube 7 5 20 [1, 0, 2, 1, 2, 2, 0] = [1, 1, 0, 2, 2, 2, 2] := by
  decide

theorem demoM_0001010 : fieldMul 7 5 20 [1, 1, 0, 2, 2, 2, 2] [0, 0, 0, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001010 : mirrorTrits [1, 1, 0, 2, 2, 2, 2] = [2, 2, 0, 1, 1, 1, 1] := by
  decide

theorem demoInv_0001010 : specInv 7 5 20 [0, 0, 0, 1, 0, 1, 0] = some [2, 2, 0, 1, 1, 1, 1] :=
  specInv_mirror_7 [0, 0, 0, 1, 0, 1, 0] [2, 0, 1, 0, 0, 1, 2] [1, 0, 2, 1, 2, 2, 0] [1, 1, 0, 2, 2, 2, 2] [2, 2, 0, 1, 1, 1, 1] demoR1_0001010 demoR2_0001010 demoC_0001010 demoM_0001010 demoMir_0001010

theorem demoR1_1001010 : invRung 7 5 20 [1, 0, 0, 1, 0, 1, 0] [1, 0, 0, 1, 0, 1, 0] 1 2 false = ([1, 2, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_1001010 : invRung 7 5 20 [1, 0, 0, 1, 0, 1, 0] [1, 2, 2, 0, 0, 0, 0] 3 1 true = ([2, 2, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_1001010 : fieldCube 7 5 20 [2, 2, 2, 0, 2, 0, 2] = [2, 1, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_1001010 : fieldMul 7 5 20 [2, 1, 1, 0, 2, 1, 0] [1, 0, 0, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1001010 : specInv 7 5 20 [1, 0, 0, 1, 0, 1, 0] = some [2, 1, 1, 0, 2, 1, 0] :=
  specInv_white_7 [1, 0, 0, 1, 0, 1, 0] [1, 2, 2, 0, 0, 0, 0] [2, 2, 2, 0, 2, 0, 2] [2, 1, 1, 0, 2, 1, 0] demoR1_1001010 demoR2_1001010 demoC_1001010 demoM_1001010

theorem demoR1_2001010 : invRung 7 5 20 [2, 0, 0, 1, 0, 1, 0] [2, 0, 0, 1, 0, 1, 0] 1 2 false = ([0, 1, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_2001010 : invRung 7 5 20 [2, 0, 0, 1, 0, 1, 0] [0, 1, 1, 1, 1, 0, 2] 3 1 true = ([1, 2, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_2001010 : fieldCube 7 5 20 [1, 2, 2, 2, 1, 0, 2] = [0, 0, 0, 2, 2, 2, 2] := by
  decide

theorem demoM_2001010 : fieldMul 7 5 20 [0, 0, 0, 2, 2, 2, 2] [2, 0, 0, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001010 : mirrorTrits [0, 0, 0, 2, 2, 2, 2] = [0, 0, 0, 1, 1, 1, 1] := by
  decide

theorem demoInv_2001010 : specInv 7 5 20 [2, 0, 0, 1, 0, 1, 0] = some [0, 0, 0, 1, 1, 1, 1] :=
  specInv_mirror_7 [2, 0, 0, 1, 0, 1, 0] [0, 1, 1, 1, 1, 0, 2] [1, 2, 2, 2, 1, 0, 2] [0, 0, 0, 2, 2, 2, 2] [0, 0, 0, 1, 1, 1, 1] demoR1_2001010 demoR2_2001010 demoC_2001010 demoM_2001010 demoMir_2001010

theorem demoR1_0101010 : invRung 7 5 20 [0, 1, 0, 1, 0, 1, 0] [0, 1, 0, 1, 0, 1, 0] 1 2 false = ([0, 2, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_0101010 : invRung 7 5 20 [0, 1, 0, 1, 0, 1, 0] [0, 2, 0, 2, 1, 1, 2] 3 1 true = ([0, 0, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0101010 : fieldCube 7 5 20 [0, 0, 0, 1, 0, 0, 0] = [1, 0, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_0101010 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 1, 0] [0, 1, 0, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0101010 : specInv 7 5 20 [0, 1, 0, 1, 0, 1, 0] = some [1, 0, 1, 0, 0, 1, 0] :=
  specInv_white_7 [0, 1, 0, 1, 0, 1, 0] [0, 2, 0, 2, 1, 1, 2] [0, 0, 0, 1, 0, 0, 0] [1, 0, 1, 0, 0, 1, 0] demoR1_0101010 demoR2_0101010 demoC_0101010 demoM_0101010

theorem demoR1_1101010 : invRung 7 5 20 [1, 1, 0, 1, 0, 1, 0] [1, 1, 0, 1, 0, 1, 0] 1 2 false = ([1, 2, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1101010 : invRung 7 5 20 [1, 1, 0, 1, 0, 1, 0] [1, 2, 0, 1, 1, 0, 0] 3 1 true = ([2, 0, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_1101010 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 0, 1] = [1, 1, 1, 1, 1, 0, 0] := by
  decide

theorem demoM_1101010 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 0, 0] [1, 1, 0, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1101010 : specInv 7 5 20 [1, 1, 0, 1, 0, 1, 0] = some [1, 1, 1, 1, 1, 0, 0] :=
  specInv_white_7 [1, 1, 0, 1, 0, 1, 0] [1, 2, 0, 1, 1, 0, 0] [2, 0, 2, 2, 0, 0, 1] [1, 1, 1, 1, 1, 0, 0] demoR1_1101010 demoR2_1101010 demoC_1101010 demoM_1101010

theorem demoR1_2101010 : invRung 7 5 20 [2, 1, 0, 1, 0, 1, 0] [2, 1, 0, 1, 0, 1, 0] 1 2 false = ([1, 1, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_2101010 : invRung 7 5 20 [2, 1, 0, 1, 0, 1, 0] [1, 1, 0, 0, 2, 2, 2] 3 1 true = ([2, 2, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2101010 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 2, 0] = [2, 1, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_2101010 : fieldMul 7 5 20 [2, 1, 0, 1, 2, 2, 0] [2, 1, 0, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101010 : mirrorTrits [2, 1, 0, 1, 2, 2, 0] = [1, 2, 0, 2, 1, 1, 0] := by
  decide

theorem demoInv_2101010 : specInv 7 5 20 [2, 1, 0, 1, 0, 1, 0] = some [1, 2, 0, 2, 1, 1, 0] :=
  specInv_mirror_7 [2, 1, 0, 1, 0, 1, 0] [1, 1, 0, 0, 2, 2, 2] [2, 2, 0, 1, 2, 2, 0] [2, 1, 0, 1, 2, 2, 0] [1, 2, 0, 2, 1, 1, 0] demoR1_2101010 demoR2_2101010 demoC_2101010 demoM_2101010 demoMir_2101010

theorem demoR1_0201010 : invRung 7 5 20 [0, 2, 0, 1, 0, 1, 0] [0, 2, 0, 1, 0, 1, 0] 1 2 false = ([0, 0, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_0201010 : invRung 7 5 20 [0, 2, 0, 1, 0, 1, 0] [0, 0, 2, 2, 2, 2, 0] 3 1 true = ([1, 0, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_0201010 : fieldCube 7 5 20 [1, 0, 0, 2, 2, 2, 1] = [2, 2, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_0201010 : fieldMul 7 5 20 [2, 2, 0, 0, 0, 1, 1] [0, 2, 0, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0201010 : specInv 7 5 20 [0, 2, 0, 1, 0, 1, 0] = some [2, 2, 0, 0, 0, 1, 1] :=
  specInv_white_7 [0, 2, 0, 1, 0, 1, 0] [0, 0, 2, 2, 2, 2, 0] [1, 0, 0, 2, 2, 2, 1] [2, 2, 0, 0, 0, 1, 1] demoR1_0201010 demoR2_0201010 demoC_0201010 demoM_0201010

theorem demoR1_1201010 : invRung 7 5 20 [1, 2, 0, 1, 0, 1, 0] [1, 2, 0, 1, 0, 1, 0] 1 2 false = ([0, 2, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1201010 : invRung 7 5 20 [1, 2, 0, 1, 0, 1, 0] [0, 2, 1, 1, 1, 0, 2] 3 1 true = ([1, 2, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1201010 : fieldCube 7 5 20 [1, 2, 2, 1, 2, 1, 0] = [0, 0, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_1201010 : fieldMul 7 5 20 [0, 0, 2, 1, 1, 1, 0] [1, 2, 0, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1201010 : specInv 7 5 20 [1, 2, 0, 1, 0, 1, 0] = some [0, 0, 2, 1, 1, 1, 0] :=
  specInv_white_7 [1, 2, 0, 1, 0, 1, 0] [0, 2, 1, 1, 1, 0, 2] [1, 2, 2, 1, 2, 1, 0] [0, 0, 2, 1, 1, 1, 0] demoR1_1201010 demoR2_1201010 demoC_1201010 demoM_1201010

theorem demoR1_2201010 : invRung 7 5 20 [2, 2, 0, 1, 0, 1, 0] [2, 2, 0, 1, 0, 1, 0] 1 2 false = ([1, 2, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_2201010 : invRung 7 5 20 [2, 2, 0, 1, 0, 1, 0] [1, 2, 2, 2, 1, 0, 2] 3 1 true = ([1, 0, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_2201010 : fieldCube 7 5 20 [1, 0, 1, 1, 2, 0, 1] = [2, 0, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_2201010 : fieldMul 7 5 20 [2, 0, 0, 0, 1, 1, 1] [2, 2, 0, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2201010 : specInv 7 5 20 [2, 2, 0, 1, 0, 1, 0] = some [2, 0, 0, 0, 1, 1, 1] :=
  specInv_white_7 [2, 2, 0, 1, 0, 1, 0] [1, 2, 2, 2, 1, 0, 2] [1, 0, 1, 1, 2, 0, 1] [2, 0, 0, 0, 1, 1, 1] demoR1_2201010 demoR2_2201010 demoC_2201010 demoM_2201010

theorem demoR1_0011010 : invRung 7 5 20 [0, 0, 1, 1, 0, 1, 0] [0, 0, 1, 1, 0, 1, 0] 1 2 false = ([0, 0, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_0011010 : invRung 7 5 20 [0, 0, 1, 1, 0, 1, 0] [0, 0, 2, 1, 0, 1, 0] 3 1 true = ([0, 1, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0011010 : fieldCube 7 5 20 [0, 1, 2, 2, 0, 1, 1] = [0, 2, 2, 2, 2, 1, 2] := by
  decide

theorem demoM_0011010 : fieldMul 7 5 20 [0, 2, 2, 2, 2, 1, 2] [0, 0, 1, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011010 : mirrorTrits [0, 2, 2, 2, 2, 1, 2] = [0, 1, 1, 1, 1, 2, 1] := by
  decide

theorem demoInv_0011010 : specInv 7 5 20 [0, 0, 1, 1, 0, 1, 0] = some [0, 1, 1, 1, 1, 2, 1] :=
  specInv_mirror_7 [0, 0, 1, 1, 0, 1, 0] [0, 0, 2, 1, 0, 1, 0] [0, 1, 2, 2, 0, 1, 1] [0, 2, 2, 2, 2, 1, 2] [0, 1, 1, 1, 1, 2, 1] demoR1_0011010 demoR2_0011010 demoC_0011010 demoM_0011010 demoMir_0011010

theorem demoR1_1011010 : invRung 7 5 20 [1, 0, 1, 1, 0, 1, 0] [1, 0, 1, 1, 0, 1, 0] 1 2 false = ([0, 0, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_1011010 : invRung 7 5 20 [1, 0, 1, 1, 0, 1, 0] [0, 0, 0, 2, 1, 0, 1] 3 1 true = ([2, 2, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1011010 : fieldCube 7 5 20 [2, 2, 1, 1, 0, 1, 1] = [1, 2, 1, 0, 2, 0, 1] := by
  decide

theorem demoM_1011010 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 0, 1] [1, 0, 1, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011010 : mirrorTrits [1, 2, 1, 0, 2, 0, 1] = [2, 1, 2, 0, 1, 0, 2] := by
  decide

theorem demoInv_1011010 : specInv 7 5 20 [1, 0, 1, 1, 0, 1, 0] = some [2, 1, 2, 0, 1, 0, 2] :=
  specInv_mirror_7 [1, 0, 1, 1, 0, 1, 0] [0, 0, 0, 2, 1, 0, 1] [2, 2, 1, 1, 0, 1, 1] [1, 2, 1, 0, 2, 0, 1] [2, 1, 2, 0, 1, 0, 2] demoR1_1011010 demoR2_1011010 demoC_1011010 demoM_1011010 demoMir_1011010

theorem demoR1_2011010 : invRung 7 5 20 [2, 0, 1, 1, 0, 1, 0] [2, 0, 1, 1, 0, 1, 0] 1 2 false = ([0, 2, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_2011010 : invRung 7 5 20 [2, 0, 1, 1, 0, 1, 0] [0, 2, 2, 0, 2, 2, 1] 3 1 true = ([1, 2, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_2011010 : fieldCube 7 5 20 [1, 2, 0, 2, 2, 0, 1] = [0, 0, 1, 2, 1, 2, 0] := by
  decide

theorem demoM_2011010 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 2, 0] [2, 0, 1, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011010 : mirrorTrits [0, 0, 1, 2, 1, 2, 0] = [0, 0, 2, 1, 2, 1, 0] := by
  decide

theorem demoInv_2011010 : specInv 7 5 20 [2, 0, 1, 1, 0, 1, 0] = some [0, 0, 2, 1, 2, 1, 0] :=
  specInv_mirror_7 [2, 0, 1, 1, 0, 1, 0] [0, 2, 2, 0, 2, 2, 1] [1, 2, 0, 2, 2, 0, 1] [0, 0, 1, 2, 1, 2, 0] [0, 0, 2, 1, 2, 1, 0] demoR1_2011010 demoR2_2011010 demoC_2011010 demoM_2011010 demoMir_2011010

theorem demoR1_0111010 : invRung 7 5 20 [0, 1, 1, 1, 0, 1, 0] [0, 1, 1, 1, 0, 1, 0] 1 2 false = ([2, 1, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_0111010 : invRung 7 5 20 [0, 1, 1, 1, 0, 1, 0] [2, 1, 1, 0, 2, 1, 0] 3 1 true = ([2, 2, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_0111010 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 0, 0] = [0, 2, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_0111010 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 0, 2] [0, 1, 1, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0111010 : specInv 7 5 20 [0, 1, 1, 1, 0, 1, 0] = some [0, 2, 1, 1, 0, 0, 2] :=
  specInv_white_7 [0, 1, 1, 1, 0, 1, 0] [2, 1, 1, 0, 2, 1, 0] [2, 2, 0, 1, 2, 0, 0] [0, 2, 1, 1, 0, 0, 2] demoR1_0111010 demoR2_0111010 demoC_0111010 demoM_0111010

theorem demoR1_1111010 : invRung 7 5 20 [1, 1, 1, 1, 0, 1, 0] [1, 1, 1, 1, 0, 1, 0] 1 2 false = ([1, 1, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_1111010 : invRung 7 5 20 [1, 1, 1, 1, 0, 1, 0] [1, 1, 2, 2, 1, 1, 0] 3 1 true = ([0, 1, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_1111010 : fieldCube 7 5 20 [0, 1, 2, 2, 0, 2, 0] = [1, 2, 1, 1, 2, 1, 0] := by
  decide

theorem demoM_1111010 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 1, 0] [1, 1, 1, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1111010 : specInv 7 5 20 [1, 1, 1, 1, 0, 1, 0] = some [1, 2, 1, 1, 2, 1, 0] :=
  specInv_white_7 [1, 1, 1, 1, 0, 1, 0] [1, 1, 2, 2, 1, 1, 0] [0, 1, 2, 2, 0, 2, 0] [1, 2, 1, 1, 2, 1, 0] demoR1_1111010 demoR2_1111010 demoC_1111010 demoM_1111010

theorem demoR1_2111010 : invRung 7 5 20 [2, 1, 1, 1, 0, 1, 0] [2, 1, 1, 1, 0, 1, 0] 1 2 false = ([2, 2, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_2111010 : invRung 7 5 20 [2, 1, 1, 1, 0, 1, 0] [2, 2, 0, 0, 0, 0, 2] 3 1 true = ([0, 1, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_2111010 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 2, 0] = [1, 1, 1, 0, 2, 0, 0] := by
  decide

theorem demoM_2111010 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 0, 0] [2, 1, 1, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2111010 : specInv 7 5 20 [2, 1, 1, 1, 0, 1, 0] = some [1, 1, 1, 0, 2, 0, 0] :=
  specInv_white_7 [2, 1, 1, 1, 0, 1, 0] [2, 2, 0, 0, 0, 0, 2] [0, 1, 0, 2, 2, 2, 0] [1, 1, 1, 0, 2, 0, 0] demoR1_2111010 demoR2_2111010 demoC_2111010 demoM_2111010

theorem demoR1_0211010 : invRung 7 5 20 [0, 2, 1, 1, 0, 1, 0] [0, 2, 1, 1, 0, 1, 0] 1 2 false = ([1, 0, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_0211010 : invRung 7 5 20 [0, 2, 1, 1, 0, 1, 0] [1, 0, 1, 0, 1, 0, 1] 3 1 true = ([0, 0, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0211010 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 2, 2] = [2, 2, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_0211010 : fieldMul 7 5 20 [2, 2, 0, 0, 1, 2, 1] [0, 2, 1, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211010 : mirrorTrits [2, 2, 0, 0, 1, 2, 1] = [1, 1, 0, 0, 2, 1, 2] := by
  decide

theorem demoInv_0211010 : specInv 7 5 20 [0, 2, 1, 1, 0, 1, 0] = some [1, 1, 0, 0, 2, 1, 2] :=
  specInv_mirror_7 [0, 2, 1, 1, 0, 1, 0] [1, 0, 1, 0, 1, 0, 1] [0, 0, 0, 0, 1, 2, 2] [2, 2, 0, 0, 1, 2, 1] [1, 1, 0, 0, 2, 1, 2] demoR1_0211010 demoR2_0211010 demoC_0211010 demoM_0211010 demoMir_0211010

theorem demoR1_1211010 : invRung 7 5 20 [1, 2, 1, 1, 0, 1, 0] [1, 2, 1, 1, 0, 1, 0] 1 2 false = ([2, 1, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1211010 : invRung 7 5 20 [1, 2, 1, 1, 0, 1, 0] [2, 1, 2, 1, 0, 0, 1] 3 1 true = ([0, 1, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1211010 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 2, 0] = [0, 2, 0, 1, 2, 0, 0] := by
  decide

theorem demoM_1211010 : fieldMul 7 5 20 [0, 2, 0, 1, 2, 0, 0] [1, 2, 1, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1211010 : specInv 7 5 20 [1, 2, 1, 1, 0, 1, 0] = some [0, 2, 0, 1, 2, 0, 0] :=
  specInv_white_7 [1, 2, 1, 1, 0, 1, 0] [2, 1, 2, 1, 0, 0, 1] [0, 1, 2, 1, 0, 2, 0] [0, 2, 0, 1, 2, 0, 0] demoR1_1211010 demoR2_1211010 demoC_1211010 demoM_1211010

theorem demoR1_2211010 : invRung 7 5 20 [2, 2, 1, 1, 0, 1, 0] [2, 2, 1, 1, 0, 1, 0] 1 2 false = ([1, 2, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_2211010 : invRung 7 5 20 [2, 2, 1, 1, 0, 1, 0] [1, 2, 2, 0, 2, 1, 0] 3 1 true = ([1, 0, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_2211010 : fieldCube 7 5 20 [1, 0, 0, 2, 1, 1, 0] = [1, 2, 0, 1, 1, 1, 0] := by
  decide

theorem demoM_2211010 : fieldMul 7 5 20 [1, 2, 0, 1, 1, 1, 0] [2, 2, 1, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211010 : mirrorTrits [1, 2, 0, 1, 1, 1, 0] = [2, 1, 0, 2, 2, 2, 0] := by
  decide

theorem demoInv_2211010 : specInv 7 5 20 [2, 2, 1, 1, 0, 1, 0] = some [2, 1, 0, 2, 2, 2, 0] :=
  specInv_mirror_7 [2, 2, 1, 1, 0, 1, 0] [1, 2, 2, 0, 2, 1, 0] [1, 0, 0, 2, 1, 1, 0] [1, 2, 0, 1, 1, 1, 0] [2, 1, 0, 2, 2, 2, 0] demoR1_2211010 demoR2_2211010 demoC_2211010 demoM_2211010 demoMir_2211010

theorem demoR1_0021010 : invRung 7 5 20 [0, 0, 2, 1, 0, 1, 0] [0, 0, 2, 1, 0, 1, 0] 1 2 false = ([2, 2, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0021010 : invRung 7 5 20 [0, 0, 2, 1, 0, 1, 0] [2, 2, 0, 0, 2, 1, 2] 3 1 true = ([0, 0, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0021010 : fieldCube 7 5 20 [0, 0, 1, 1, 2, 1, 2] = [2, 2, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_0021010 : fieldMul 7 5 20 [2, 2, 0, 1, 0, 0, 1] [0, 0, 2, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021010 : mirrorTrits [2, 2, 0, 1, 0, 0, 1] = [1, 1, 0, 2, 0, 0, 2] := by
  decide

theorem demoInv_0021010 : specInv 7 5 20 [0, 0, 2, 1, 0, 1, 0] = some [1, 1, 0, 2, 0, 0, 2] :=
  specInv_mirror_7 [0, 0, 2, 1, 0, 1, 0] [2, 2, 0, 0, 2, 1, 2] [0, 0, 1, 1, 2, 1, 2] [2, 2, 0, 1, 0, 0, 1] [1, 1, 0, 2, 0, 0, 2] demoR1_0021010 demoR2_0021010 demoC_0021010 demoM_0021010 demoMir_0021010

theorem demoR1_1021010 : invRung 7 5 20 [1, 0, 2, 1, 0, 1, 0] [1, 0, 2, 1, 0, 1, 0] 1 2 false = ([2, 0, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1021010 : invRung 7 5 20 [1, 0, 2, 1, 0, 1, 0] [2, 0, 2, 2, 1, 0, 2] 3 1 true = ([2, 0, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_1021010 : fieldCube 7 5 20 [2, 0, 0, 0, 2, 0, 2] = [2, 1, 1, 1, 2, 1, 1] := by
  decide

theorem demoM_1021010 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 1, 1] [1, 0, 2, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021010 : mirrorTrits [2, 1, 1, 1, 2, 1, 1] = [1, 2, 2, 2, 1, 2, 2] := by
  decide

theorem demoInv_1021010 : specInv 7 5 20 [1, 0, 2, 1, 0, 1, 0] = some [1, 2, 2, 2, 1, 2, 2] :=
  specInv_mirror_7 [1, 0, 2, 1, 0, 1, 0] [2, 0, 2, 2, 1, 0, 2] [2, 0, 0, 0, 2, 0, 2] [2, 1, 1, 1, 2, 1, 1] [1, 2, 2, 2, 1, 2, 2] demoR1_1021010 demoR2_1021010 demoC_1021010 demoM_1021010 demoMir_1021010

theorem demoR1_2021010 : invRung 7 5 20 [2, 0, 2, 1, 0, 1, 0] [2, 0, 2, 1, 0, 1, 0] 1 2 false = ([2, 2, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_2021010 : invRung 7 5 20 [2, 0, 2, 1, 0, 1, 0] [2, 2, 2, 0, 2, 1, 2] 3 1 true = ([2, 1, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_2021010 : fieldCube 7 5 20 [2, 1, 1, 2, 1, 1, 2] = [2, 1, 1, 1, 0, 0, 0] := by
  decide

theorem demoM_2021010 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 0, 0] [2, 0, 2, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021010 : mirrorTrits [2, 1, 1, 1, 0, 0, 0] = [1, 2, 2, 2, 0, 0, 0] := by
  decide

theorem demoInv_2021010 : specInv 7 5 20 [2, 0, 2, 1, 0, 1, 0] = some [1, 2, 2, 2, 0, 0, 0] :=
  specInv_mirror_7 [2, 0, 2, 1, 0, 1, 0] [2, 2, 2, 0, 2, 1, 2] [2, 1, 1, 2, 1, 1, 2] [2, 1, 1, 1, 0, 0, 0] [1, 2, 2, 2, 0, 0, 0] demoR1_2021010 demoR2_2021010 demoC_2021010 demoM_2021010 demoMir_2021010

theorem demoR1_0121010 : invRung 7 5 20 [0, 1, 2, 1, 0, 1, 0] [0, 1, 2, 1, 0, 1, 0] 1 2 false = ([2, 1, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_0121010 : invRung 7 5 20 [0, 1, 2, 1, 0, 1, 0] [2, 1, 1, 1, 1, 0, 1] 3 1 true = ([1, 2, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0121010 : fieldCube 7 5 20 [1, 2, 0, 0, 2, 0, 1] = [1, 0, 2, 2, 1, 0, 0] := by
  decide

theorem demoM_0121010 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 0, 0] [0, 1, 2, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0121010 : specInv 7 5 20 [0, 1, 2, 1, 0, 1, 0] = some [1, 0, 2, 2, 1, 0, 0] :=
  specInv_white_7 [0, 1, 2, 1, 0, 1, 0] [2, 1, 1, 1, 1, 0, 1] [1, 2, 0, 0, 2, 0, 1] [1, 0, 2, 2, 1, 0, 0] demoR1_0121010 demoR2_0121010 demoC_0121010 demoM_0121010

theorem demoR1_1121010 : invRung 7 5 20 [1, 1, 2, 1, 0, 1, 0] [1, 1, 2, 1, 0, 1, 0] 1 2 false = ([1, 1, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_1121010 : invRung 7 5 20 [1, 1, 2, 1, 0, 1, 0] [1, 1, 1, 0, 2, 1, 2] 3 1 true = ([2, 0, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1121010 : fieldCube 7 5 20 [2, 0, 1, 1, 2, 1, 0] = [1, 0, 2, 2, 1, 1, 2] := by
  decide

theorem demoM_1121010 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 1, 2] [1, 1, 2, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1121010 : specInv 7 5 20 [1, 1, 2, 1, 0, 1, 0] = some [1, 0, 2, 2, 1, 1, 2] :=
  specInv_white_7 [1, 1, 2, 1, 0, 1, 0] [1, 1, 1, 0, 2, 1, 2] [2, 0, 1, 1, 2, 1, 0] [1, 0, 2, 2, 1, 1, 2] demoR1_1121010 demoR2_1121010 demoC_1121010 demoM_1121010

theorem demoR1_2121010 : invRung 7 5 20 [2, 1, 2, 1, 0, 1, 0] [2, 1, 2, 1, 0, 1, 0] 1 2 false = ([2, 1, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2121010 : invRung 7 5 20 [2, 1, 2, 1, 0, 1, 0] [2, 1, 1, 0, 2, 0, 0] 3 1 true = ([2, 0, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_2121010 : fieldCube 7 5 20 [2, 0, 0, 0, 0, 0, 1] = [2, 1, 2, 1, 1, 1, 1] := by
  decide

theorem demoM_2121010 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 1, 1] [2, 1, 2, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2121010 : specInv 7 5 20 [2, 1, 2, 1, 0, 1, 0] = some [2, 1, 2, 1, 1, 1, 1] :=
  specInv_white_7 [2, 1, 2, 1, 0, 1, 0] [2, 1, 1, 0, 2, 0, 0] [2, 0, 0, 0, 0, 0, 1] [2, 1, 2, 1, 1, 1, 1] demoR1_2121010 demoR2_2121010 demoC_2121010 demoM_2121010

theorem demoR1_0221010 : invRung 7 5 20 [0, 2, 2, 1, 0, 1, 0] [0, 2, 2, 1, 0, 1, 0] 1 2 false = ([0, 0, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_0221010 : invRung 7 5 20 [0, 2, 2, 1, 0, 1, 0] [0, 0, 1, 0, 0, 2, 1] 3 1 true = ([1, 1, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0221010 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 2, 2] = [0, 2, 0, 1, 1, 2, 2] := by
  decide

theorem demoM_0221010 : fieldMul 7 5 20 [0, 2, 0, 1, 1, 2, 2] [0, 2, 2, 1, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0221010 : mirrorTrits [0, 2, 0, 1, 1, 2, 2] = [0, 1, 0, 2, 2, 1, 1] := by
  decide

theorem demoInv_0221010 : specInv 7 5 20 [0, 2, 2, 1, 0, 1, 0] = some [0, 1, 0, 2, 2, 1, 1] :=
  specInv_mirror_7 [0, 2, 2, 1, 0, 1, 0] [0, 0, 1, 0, 0, 2, 1] [1, 1, 1, 0, 1, 2, 2] [0, 2, 0, 1, 1, 2, 2] [0, 1, 0, 2, 2, 1, 1] demoR1_0221010 demoR2_0221010 demoC_0221010 demoM_0221010 demoMir_0221010

theorem demoR1_1221010 : invRung 7 5 20 [1, 2, 2, 1, 0, 1, 0] [1, 2, 2, 1, 0, 1, 0] 1 2 false = ([1, 0, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_1221010 : invRung 7 5 20 [1, 2, 2, 1, 0, 1, 0] [1, 0, 2, 0, 2, 1, 1] 3 1 true = ([1, 1, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1221010 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 0, 0] = [1, 1, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_1221010 : fieldMul 7 5 20 [1, 1, 0, 2, 0, 1, 1] [1, 2, 2, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1221010 : specInv 7 5 20 [1, 2, 2, 1, 0, 1, 0] = some [1, 1, 0, 2, 0, 1, 1] :=
  specInv_white_7 [1, 2, 2, 1, 0, 1, 0] [1, 0, 2, 0, 2, 1, 1] [1, 1, 0, 0, 1, 0, 0] [1, 1, 0, 2, 0, 1, 1] demoR1_1221010 demoR2_1221010 demoC_1221010 demoM_1221010

theorem demoR1_2221010 : invRung 7 5 20 [2, 2, 2, 1, 0, 1, 0] [2, 2, 2, 1, 0, 1, 0] 1 2 false = ([0, 2, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_2221010 : invRung 7 5 20 [2, 2, 2, 1, 0, 1, 0] [0, 2, 2, 0, 0, 0, 1] 3 1 true = ([2, 1, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2221010 : fieldCube 7 5 20 [2, 1, 2, 2, 0, 1, 0] = [2, 1, 0, 1, 1, 0, 1] := by
  decide

theorem demoM_2221010 : fieldMul 7 5 20 [2, 1, 0, 1, 1, 0, 1] [2, 2, 2, 1, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2221010 : specInv 7 5 20 [2, 2, 2, 1, 0, 1, 0] = some [2, 1, 0, 1, 1, 0, 1] :=
  specInv_white_7 [2, 2, 2, 1, 0, 1, 0] [0, 2, 2, 0, 0, 0, 1] [2, 1, 2, 2, 0, 1, 0] [2, 1, 0, 1, 1, 0, 1] demoR1_2221010 demoR2_2221010 demoC_2221010 demoM_2221010

theorem demoR1_0002010 : invRung 7 5 20 [0, 0, 0, 2, 0, 1, 0] [0, 0, 0, 2, 0, 1, 0] 1 2 false = ([2, 2, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_0002010 : invRung 7 5 20 [0, 0, 0, 2, 0, 1, 0] [2, 2, 1, 2, 1, 0, 2] 3 1 true = ([1, 2, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0002010 : fieldCube 7 5 20 [1, 2, 1, 0, 0, 2, 1] = [0, 0, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_0002010 : fieldMul 7 5 20 [0, 0, 1, 0, 0, 0, 0] [0, 0, 0, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0002010 : specInv 7 5 20 [0, 0, 0, 2, 0, 1, 0] = some [0, 0, 1, 0, 0, 0, 0] :=
  specInv_white_7 [0, 0, 0, 2, 0, 1, 0] [2, 2, 1, 2, 1, 0, 2] [1, 2, 1, 0, 0, 2, 1] [0, 0, 1, 0, 0, 0, 0] demoR1_0002010 demoR2_0002010 demoC_0002010 demoM_0002010

theorem demoR1_1002010 : invRung 7 5 20 [1, 0, 0, 2, 0, 1, 0] [1, 0, 0, 2, 0, 1, 0] 1 2 false = ([1, 0, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_1002010 : invRung 7 5 20 [1, 0, 0, 2, 0, 1, 0] [1, 0, 1, 1, 0, 0, 2] 3 1 true = ([2, 2, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_1002010 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 1, 1] = [1, 1, 1, 2, 2, 2, 2] := by
  decide

theorem demoM_1002010 : fieldMul 7 5 20 [1, 1, 1, 2, 2, 2, 2] [1, 0, 0, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002010 : mirrorTrits [1, 1, 1, 2, 2, 2, 2] = [2, 2, 2, 1, 1, 1, 1] := by
  decide

theorem demoInv_1002010 : specInv 7 5 20 [1, 0, 0, 2, 0, 1, 0] = some [2, 2, 2, 1, 1, 1, 1] :=
  specInv_mirror_7 [1, 0, 0, 2, 0, 1, 0] [1, 0, 1, 1, 0, 0, 2] [2, 2, 0, 1, 2, 1, 1] [1, 1, 1, 2, 2, 2, 2] [2, 2, 2, 1, 1, 1, 1] demoR1_1002010 demoR2_1002010 demoC_1002010 demoM_1002010 demoMir_1002010

theorem demoR1_2002010 : invRung 7 5 20 [2, 0, 0, 2, 0, 1, 0] [2, 0, 0, 2, 0, 1, 0] 1 2 false = ([0, 0, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2002010 : invRung 7 5 20 [2, 0, 0, 2, 0, 1, 0] [0, 0, 0, 0, 2, 2, 0] 3 1 true = ([2, 1, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_2002010 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 1, 2] = [1, 0, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_2002010 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 1, 0] [2, 0, 0, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002010 : mirrorTrits [1, 0, 0, 0, 0, 1, 0] = [2, 0, 0, 0, 0, 2, 0] := by
  decide

theorem demoInv_2002010 : specInv 7 5 20 [2, 0, 0, 2, 0, 1, 0] = some [2, 0, 0, 0, 0, 2, 0] :=
  specInv_mirror_7 [2, 0, 0, 2, 0, 1, 0] [0, 0, 0, 0, 2, 2, 0] [2, 1, 2, 1, 0, 1, 2] [1, 0, 0, 0, 0, 1, 0] [2, 0, 0, 0, 0, 2, 0] demoR1_2002010 demoR2_2002010 demoC_2002010 demoM_2002010 demoMir_2002010

theorem demoR1_0102010 : invRung 7 5 20 [0, 1, 0, 2, 0, 1, 0] [0, 1, 0, 2, 0, 1, 0] 1 2 false = ([1, 0, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_0102010 : invRung 7 5 20 [0, 1, 0, 2, 0, 1, 0] [1, 0, 1, 0, 0, 2, 0] 3 1 true = ([2, 0, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_0102010 : fieldCube 7 5 20 [2, 0, 1, 2, 1, 2, 2] = [0, 2, 2, 0, 1, 1, 2] := by
  decide

theorem demoM_0102010 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 1, 2] [0, 1, 0, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0102010 : specInv 7 5 20 [0, 1, 0, 2, 0, 1, 0] = some [0, 2, 2, 0, 1, 1, 2] :=
  specInv_white_7 [0, 1, 0, 2, 0, 1, 0] [1, 0, 1, 0, 0, 2, 0] [2, 0, 1, 2, 1, 2, 2] [0, 2, 2, 0, 1, 1, 2] demoR1_0102010 demoR2_0102010 demoC_0102010 demoM_0102010

theorem demoR1_1102010 : invRung 7 5 20 [1, 1, 0, 2, 0, 1, 0] [1, 1, 0, 2, 0, 1, 0] 1 2 false = ([0, 2, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_1102010 : invRung 7 5 20 [1, 1, 0, 2, 0, 1, 0] [0, 2, 0, 1, 1, 1, 0] 3 1 true = ([1, 0, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_1102010 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 2, 2] = [2, 0, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_1102010 : fieldMul 7 5 20 [2, 0, 2, 1, 1, 2, 1] [1, 1, 0, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102010 : mirrorTrits [2, 0, 2, 1, 1, 2, 1] = [1, 0, 1, 2, 2, 1, 2] := by
  decide

theorem demoInv_1102010 : specInv 7 5 20 [1, 1, 0, 2, 0, 1, 0] = some [1, 0, 1, 2, 2, 1, 2] :=
  specInv_mirror_7 [1, 1, 0, 2, 0, 1, 0] [0, 2, 0, 1, 1, 1, 0] [1, 0, 2, 2, 2, 2, 2] [2, 0, 2, 1, 1, 2, 1] [1, 0, 1, 2, 2, 1, 2] demoR1_1102010 demoR2_1102010 demoC_1102010 demoM_1102010 demoMir_1102010

theorem demoR1_2102010 : invRung 7 5 20 [2, 1, 0, 2, 0, 1, 0] [2, 1, 0, 2, 0, 1, 0] 1 2 false = ([1, 2, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_2102010 : invRung 7 5 20 [2, 1, 0, 2, 0, 1, 0] [1, 2, 0, 1, 2, 1, 1] 3 1 true = ([2, 1, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_2102010 : fieldCube 7 5 20 [2, 1, 0, 0, 2, 1, 1] = [0, 1, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_2102010 : fieldMul 7 5 20 [0, 1, 0, 1, 2, 1, 2] [2, 1, 0, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2102010 : mirrorTrits [0, 1, 0, 1, 2, 1, 2] = [0, 2, 0, 2, 1, 2, 1] := by
  decide

theorem demoInv_2102010 : specInv 7 5 20 [2, 1, 0, 2, 0, 1, 0] = some [0, 2, 0, 2, 1, 2, 1] :=
  specInv_mirror_7 [2, 1, 0, 2, 0, 1, 0] [1, 2, 0, 1, 2, 1, 1] [2, 1, 0, 0, 2, 1, 1] [0, 1, 0, 1, 2, 1, 2] [0, 2, 0, 2, 1, 2, 1] demoR1_2102010 demoR2_2102010 demoC_2102010 demoM_2102010 demoMir_2102010

theorem demoR1_0202010 : invRung 7 5 20 [0, 2, 0, 2, 0, 1, 0] [0, 2, 0, 2, 0, 1, 0] 1 2 false = ([2, 1, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_0202010 : invRung 7 5 20 [0, 2, 0, 2, 0, 1, 0] [2, 1, 1, 0, 1, 0, 0] 3 1 true = ([0, 1, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0202010 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 2, 1] = [2, 0, 1, 2, 0, 0, 2] := by
  decide

theorem demoM_0202010 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 0, 2] [0, 2, 0, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202010 : mirrorTrits [2, 0, 1, 2, 0, 0, 2] = [1, 0, 2, 1, 0, 0, 1] := by
  decide

theorem demoInv_0202010 : specInv 7 5 20 [0, 2, 0, 2, 0, 1, 0] = some [1, 0, 2, 1, 0, 0, 1] :=
  specInv_mirror_7 [0, 2, 0, 2, 0, 1, 0] [2, 1, 1, 0, 1, 0, 0] [0, 1, 0, 0, 0, 2, 1] [2, 0, 1, 2, 0, 0, 2] [1, 0, 2, 1, 0, 0, 1] demoR1_0202010 demoR2_0202010 demoC_0202010 demoM_0202010 demoMir_0202010

theorem demoR1_1202010 : invRung 7 5 20 [1, 2, 0, 2, 0, 1, 0] [1, 2, 0, 2, 0, 1, 0] 1 2 false = ([1, 2, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1202010 : invRung 7 5 20 [1, 2, 0, 2, 0, 1, 0] [1, 2, 2, 1, 0, 0, 1] 3 1 true = ([1, 0, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_1202010 : fieldCube 7 5 20 [1, 0, 0, 2, 2, 1, 1] = [1, 1, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_1202010 : fieldMul 7 5 20 [1, 1, 2, 0, 2, 0, 2] [1, 2, 0, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1202010 : specInv 7 5 20 [1, 2, 0, 2, 0, 1, 0] = some [1, 1, 2, 0, 2, 0, 2] :=
  specInv_white_7 [1, 2, 0, 2, 0, 1, 0] [1, 2, 2, 1, 0, 0, 1] [1, 0, 0, 2, 2, 1, 1] [1, 1, 2, 0, 2, 0, 2] demoR1_1202010 demoR2_1202010 demoC_1202010 demoM_1202010

theorem demoR1_2202010 : invRung 7 5 20 [2, 2, 0, 2, 0, 1, 0] [2, 2, 0, 2, 0, 1, 0] 1 2 false = ([1, 0, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2202010 : invRung 7 5 20 [2, 2, 0, 2, 0, 1, 0] [1, 0, 0, 0, 2, 0, 0] 3 1 true = ([2, 1, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_2202010 : fieldCube 7 5 20 [2, 1, 2, 2, 0, 0, 2] = [1, 2, 0, 0, 2, 1, 1] := by
  decide

theorem demoM_2202010 : fieldMul 7 5 20 [1, 2, 0, 0, 2, 1, 1] [2, 2, 0, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2202010 : specInv 7 5 20 [2, 2, 0, 2, 0, 1, 0] = some [1, 2, 0, 0, 2, 1, 1] :=
  specInv_white_7 [2, 2, 0, 2, 0, 1, 0] [1, 0, 0, 0, 2, 0, 0] [2, 1, 2, 2, 0, 0, 2] [1, 2, 0, 0, 2, 1, 1] demoR1_2202010 demoR2_2202010 demoC_2202010 demoM_2202010

theorem demoR1_0012010 : invRung 7 5 20 [0, 0, 1, 2, 0, 1, 0] [0, 0, 1, 2, 0, 1, 0] 1 2 false = ([1, 0, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_0012010 : invRung 7 5 20 [0, 0, 1, 2, 0, 1, 0] [1, 0, 0, 2, 0, 1, 2] 3 1 true = ([0, 2, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_0012010 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 2, 1] = [0, 1, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_0012010 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 2, 2] [0, 0, 1, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0012010 : specInv 7 5 20 [0, 0, 1, 2, 0, 1, 0] = some [0, 1, 2, 1, 0, 2, 2] :=
  specInv_white_7 [0, 0, 1, 2, 0, 1, 0] [1, 0, 0, 2, 0, 1, 2] [0, 2, 2, 1, 1, 2, 1] [0, 1, 2, 1, 0, 2, 2] demoR1_0012010 demoR2_0012010 demoC_0012010 demoM_0012010

theorem demoR1_1012010 : invRung 7 5 20 [1, 0, 1, 2, 0, 1, 0] [1, 0, 1, 2, 0, 1, 0] 1 2 false = ([1, 0, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_1012010 : invRung 7 5 20 [1, 0, 1, 2, 0, 1, 0] [1, 0, 1, 1, 2, 2, 0] 3 1 true = ([0, 0, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1012010 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 0, 0] = [0, 1, 0, 1, 0, 1, 1] := by
  decide

theorem demoM_1012010 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 1, 1] [1, 0, 1, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1012010 : specInv 7 5 20 [1, 0, 1, 2, 0, 1, 0] = some [0, 1, 0, 1, 0, 1, 1] :=
  specInv_white_7 [1, 0, 1, 2, 0, 1, 0] [1, 0, 1, 1, 2, 2, 0] [0, 0, 0, 0, 1, 0, 0] [0, 1, 0, 1, 0, 1, 1] demoR1_1012010 demoR2_1012010 demoC_1012010 demoM_1012010

theorem demoR1_2012010 : invRung 7 5 20 [2, 0, 1, 2, 0, 1, 0] [2, 0, 1, 2, 0, 1, 0] 1 2 false = ([1, 1, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_2012010 : invRung 7 5 20 [2, 0, 1, 2, 0, 1, 0] [1, 1, 1, 2, 0, 1, 0] 3 1 true = ([2, 2, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_2012010 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 0, 2] = [0, 1, 2, 0, 2, 2, 1] := by
  decide

theorem demoM_2012010 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 2, 1] [2, 0, 1, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2012010 : specInv 7 5 20 [2, 0, 1, 2, 0, 1, 0] = some [0, 1, 2, 0, 2, 2, 1] :=
  specInv_white_7 [2, 0, 1, 2, 0, 1, 0] [1, 1, 1, 2, 0, 1, 0] [2, 2, 0, 1, 2, 0, 2] [0, 1, 2, 0, 2, 2, 1] demoR1_2012010 demoR2_2012010 demoC_2012010 demoM_2012010

theorem demoR1_0112010 : invRung 7 5 20 [0, 1, 1, 2, 0, 1, 0] [0, 1, 1, 2, 0, 1, 0] 1 2 false = ([2, 2, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_0112010 : invRung 7 5 20 [0, 1, 1, 2, 0, 1, 0] [2, 2, 2, 1, 2, 2, 0] 3 1 true = ([0, 0, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0112010 : fieldCube 7 5 20 [0, 0, 2, 0, 1, 0, 1] = [0, 2, 2, 2, 1, 2, 1] := by
  decide

theorem demoM_0112010 : fieldMul 7 5 20 [0, 2, 2, 2, 1, 2, 1] [0, 1, 1, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112010 : mirrorTrits [0, 2, 2, 2, 1, 2, 1] = [0, 1, 1, 1, 2, 1, 2] := by
  decide

theorem demoInv_0112010 : specInv 7 5 20 [0, 1, 1, 2, 0, 1, 0] = some [0, 1, 1, 1, 2, 1, 2] :=
  specInv_mirror_7 [0, 1, 1, 2, 0, 1, 0] [2, 2, 2, 1, 2, 2, 0] [0, 0, 2, 0, 1, 0, 1] [0, 2, 2, 2, 1, 2, 1] [0, 1, 1, 1, 2, 1, 2] demoR1_0112010 demoR2_0112010 demoC_0112010 demoM_0112010 demoMir_0112010

theorem demoR1_1112010 : invRung 7 5 20 [1, 1, 1, 2, 0, 1, 0] [1, 1, 1, 2, 0, 1, 0] 1 2 false = ([2, 2, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1112010 : invRung 7 5 20 [1, 1, 1, 2, 0, 1, 0] [2, 2, 0, 1, 1, 0, 0] 3 1 true = ([1, 2, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_1112010 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 2, 2] = [0, 2, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_1112010 : fieldMul 7 5 20 [0, 2, 0, 2, 1, 2, 2] [1, 1, 1, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1112010 : specInv 7 5 20 [1, 1, 1, 2, 0, 1, 0] = some [0, 2, 0, 2, 1, 2, 2] :=
  specInv_white_7 [1, 1, 1, 2, 0, 1, 0] [2, 2, 0, 1, 1, 0, 0] [1, 2, 1, 0, 1, 2, 2] [0, 2, 0, 2, 1, 2, 2] demoR1_1112010 demoR2_1112010 demoC_1112010 demoM_1112010

theorem demoR1_2112010 : invRung 7 5 20 [2, 1, 1, 2, 0, 1, 0] [2, 1, 1, 2, 0, 1, 0] 1 2 false = ([1, 2, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2112010 : invRung 7 5 20 [2, 1, 1, 2, 0, 1, 0] [1, 2, 2, 2, 2, 1, 2] 3 1 true = ([1, 1, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_2112010 : fieldCube 7 5 20 [1, 1, 0, 0, 0, 1, 2] = [2, 0, 2, 0, 0, 0, 1] := by
  decide

theorem demoM_2112010 : fieldMul 7 5 20 [2, 0, 2, 0, 0, 0, 1] [2, 1, 1, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2112010 : specInv 7 5 20 [2, 1, 1, 2, 0, 1, 0] = some [2, 0, 2, 0, 0, 0, 1] :=
  specInv_white_7 [2, 1, 1, 2, 0, 1, 0] [1, 2, 2, 2, 2, 1, 2] [1, 1, 0, 0, 0, 1, 2] [2, 0, 2, 0, 0, 0, 1] demoR1_2112010 demoR2_2112010 demoC_2112010 demoM_2112010

theorem demoR1_0212010 : invRung 7 5 20 [0, 2, 1, 2, 0, 1, 0] [0, 2, 1, 2, 0, 1, 0] 1 2 false = ([0, 0, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0212010 : invRung 7 5 20 [0, 2, 1, 2, 0, 1, 0] [0, 0, 2, 2, 0, 0, 0] 3 1 true = ([1, 1, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0212010 : fieldCube 7 5 20 [1, 1, 0, 1, 1, 2, 0] = [1, 0, 0, 2, 2, 1, 2] := by
  decide

theorem demoM_0212010 : fieldMul 7 5 20 [1, 0, 0, 2, 2, 1, 2] [0, 2, 1, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212010 : mirrorTrits [1, 0, 0, 2, 2, 1, 2] = [2, 0, 0, 1, 1, 2, 1] := by
  decide

theorem demoInv_0212010 : specInv 7 5 20 [0, 2, 1, 2, 0, 1, 0] = some [2, 0, 0, 1, 1, 2, 1] :=
  specInv_mirror_7 [0, 2, 1, 2, 0, 1, 0] [0, 0, 2, 2, 0, 0, 0] [1, 1, 0, 1, 1, 2, 0] [1, 0, 0, 2, 2, 1, 2] [2, 0, 0, 1, 1, 2, 1] demoR1_0212010 demoR2_0212010 demoC_0212010 demoM_0212010 demoMir_0212010

theorem demoR1_1212010 : invRung 7 5 20 [1, 2, 1, 2, 0, 1, 0] [1, 2, 1, 2, 0, 1, 0] 1 2 false = ([0, 1, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1212010 : invRung 7 5 20 [1, 2, 1, 2, 0, 1, 0] [0, 1, 0, 1, 1, 0, 0] 3 1 true = ([2, 1, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_1212010 : fieldCube 7 5 20 [2, 1, 1, 2, 2, 1, 0] = [2, 0, 0, 0, 1, 2, 2] := by
  decide

theorem demoM_1212010 : fieldMul 7 5 20 [2, 0, 0, 0, 1, 2, 2] [1, 2, 1, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212010 : mirrorTrits [2, 0, 0, 0, 1, 2, 2] = [1, 0, 0, 0, 2, 1, 1] := by
  decide

theorem demoInv_1212010 : specInv 7 5 20 [1, 2, 1, 2, 0, 1, 0] = some [1, 0, 0, 0, 2, 1, 1] :=
  specInv_mirror_7 [1, 2, 1, 2, 0, 1, 0] [0, 1, 0, 1, 1, 0, 0] [2, 1, 1, 2, 2, 1, 0] [2, 0, 0, 0, 1, 2, 2] [1, 0, 0, 0, 2, 1, 1] demoR1_1212010 demoR2_1212010 demoC_1212010 demoM_1212010 demoMir_1212010

theorem demoR1_2212010 : invRung 7 5 20 [2, 2, 1, 2, 0, 1, 0] [2, 2, 1, 2, 0, 1, 0] 1 2 false = ([1, 1, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_2212010 : invRung 7 5 20 [2, 2, 1, 2, 0, 1, 0] [1, 1, 1, 0, 1, 2, 2] 3 1 true = ([2, 1, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_2212010 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 0, 2] = [1, 0, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_2212010 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 2, 0] [2, 2, 1, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2212010 : specInv 7 5 20 [2, 2, 1, 2, 0, 1, 0] = some [1, 0, 0, 1, 2, 2, 0] :=
  specInv_white_7 [2, 2, 1, 2, 0, 1, 0] [1, 1, 1, 0, 1, 2, 2] [2, 1, 0, 2, 1, 0, 2] [1, 0, 0, 1, 2, 2, 0] demoR1_2212010 demoR2_2212010 demoC_2212010 demoM_2212010

theorem demoR1_0022010 : invRung 7 5 20 [0, 0, 2, 2, 0, 1, 0] [0, 0, 2, 2, 0, 1, 0] 1 2 false = ([2, 1, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_0022010 : invRung 7 5 20 [0, 0, 2, 2, 0, 1, 0] [2, 1, 0, 0, 1, 0, 0] 3 1 true = ([1, 0, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_0022010 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 2, 0] = [2, 1, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_0022010 : fieldMul 7 5 20 [2, 1, 1, 2, 2, 0, 2] [0, 0, 2, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0022010 : specInv 7 5 20 [0, 0, 2, 2, 0, 1, 0] = some [2, 1, 1, 2, 2, 0, 2] :=
  specInv_white_7 [0, 0, 2, 2, 0, 1, 0] [2, 1, 0, 0, 1, 0, 0] [1, 0, 2, 2, 2, 2, 0] [2, 1, 1, 2, 2, 0, 2] demoR1_0022010 demoR2_0022010 demoC_0022010 demoM_0022010

theorem demoR1_1022010 : invRung 7 5 20 [1, 0, 2, 2, 0, 1, 0] [1, 0, 2, 2, 0, 1, 0] 1 2 false = ([2, 0, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_1022010 : invRung 7 5 20 [1, 0, 2, 2, 0, 1, 0] [2, 0, 0, 2, 0, 2, 1] 3 1 true = ([1, 0, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_1022010 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 1, 2] = [2, 0, 2, 2, 0, 0, 2] := by
  decide

theorem demoM_1022010 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 0, 2] [1, 0, 2, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1022010 : specInv 7 5 20 [1, 0, 2, 2, 0, 1, 0] = some [2, 0, 2, 2, 0, 0, 2] :=
  specInv_white_7 [1, 0, 2, 2, 0, 1, 0] [2, 0, 0, 2, 0, 2, 1] [1, 0, 1, 0, 0, 1, 2] [2, 0, 2, 2, 0, 0, 2] demoR1_1022010 demoR2_1022010 demoC_1022010 demoM_1022010

theorem demoR1_2022010 : invRung 7 5 20 [2, 0, 2, 2, 0, 1, 0] [2, 0, 2, 2, 0, 1, 0] 1 2 false = ([2, 2, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_2022010 : invRung 7 5 20 [2, 0, 2, 2, 0, 1, 0] [2, 2, 2, 2, 0, 1, 2] 3 1 true = ([1, 1, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_2022010 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 0, 2] = [1, 1, 1, 2, 2, 1, 1] := by
  decide

theorem demoM_2022010 : fieldMul 7 5 20 [1, 1, 1, 2, 2, 1, 1] [2, 0, 2, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022010 : mirrorTrits [1, 1, 1, 2, 2, 1, 1] = [2, 2, 2, 1, 1, 2, 2] := by
  decide

theorem demoInv_2022010 : specInv 7 5 20 [2, 0, 2, 2, 0, 1, 0] = some [2, 2, 2, 1, 1, 2, 2] :=
  specInv_mirror_7 [2, 0, 2, 2, 0, 1, 0] [2, 2, 2, 2, 0, 1, 2] [1, 1, 0, 0, 2, 0, 2] [1, 1, 1, 2, 2, 1, 1] [2, 2, 2, 1, 1, 2, 2] demoR1_2022010 demoR2_2022010 demoC_2022010 demoM_2022010 demoMir_2022010

theorem demoR1_0122010 : invRung 7 5 20 [0, 1, 2, 2, 0, 1, 0] [0, 1, 2, 2, 0, 1, 0] 1 2 false = ([2, 0, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_0122010 : invRung 7 5 20 [0, 1, 2, 2, 0, 1, 0] [2, 0, 0, 2, 2, 2, 0] 3 1 true = ([1, 2, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0122010 : fieldCube 7 5 20 [1, 2, 1, 2, 0, 1, 1] = [1, 2, 2, 0, 2, 1, 1] := by
  decide

theorem demoM_0122010 : fieldMul 7 5 20 [1, 2, 2, 0, 2, 1, 1] [0, 1, 2, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122010 : mirrorTrits [1, 2, 2, 0, 2, 1, 1] = [2, 1, 1, 0, 1, 2, 2] := by
  decide

theorem demoInv_0122010 : specInv 7 5 20 [0, 1, 2, 2, 0, 1, 0] = some [2, 1, 1, 0, 1, 2, 2] :=
  specInv_mirror_7 [0, 1, 2, 2, 0, 1, 0] [2, 0, 0, 2, 2, 2, 0] [1, 2, 1, 2, 0, 1, 1] [1, 2, 2, 0, 2, 1, 1] [2, 1, 1, 0, 1, 2, 2] demoR1_0122010 demoR2_0122010 demoC_0122010 demoM_0122010 demoMir_0122010

theorem demoR1_1122010 : invRung 7 5 20 [1, 1, 2, 2, 0, 1, 0] [1, 1, 2, 2, 0, 1, 0] 1 2 false = ([2, 1, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_1122010 : invRung 7 5 20 [1, 1, 2, 2, 0, 1, 0] [2, 1, 1, 1, 2, 2, 2] 3 1 true = ([2, 0, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1122010 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 1, 0] = [2, 1, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_1122010 : fieldMul 7 5 20 [2, 1, 0, 0, 1, 0, 0] [1, 1, 2, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122010 : mirrorTrits [2, 1, 0, 0, 1, 0, 0] = [1, 2, 0, 0, 2, 0, 0] := by
  decide

theorem demoInv_1122010 : specInv 7 5 20 [1, 1, 2, 2, 0, 1, 0] = some [1, 2, 0, 0, 2, 0, 0] :=
  specInv_mirror_7 [1, 1, 2, 2, 0, 1, 0] [2, 1, 1, 1, 2, 2, 2] [2, 0, 1, 2, 0, 1, 0] [2, 1, 0, 0, 1, 0, 0] [1, 2, 0, 0, 2, 0, 0] demoR1_1122010 demoR2_1122010 demoC_1122010 demoM_1122010 demoMir_1122010

theorem demoR1_2122010 : invRung 7 5 20 [2, 1, 2, 2, 0, 1, 0] [2, 1, 2, 2, 0, 1, 0] 1 2 false = ([1, 1, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_2122010 : invRung 7 5 20 [2, 1, 2, 2, 0, 1, 0] [1, 1, 0, 0, 0, 1, 1] 3 1 true = ([1, 1, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2122010 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 1, 1] = [0, 2, 1, 2, 2, 0, 0] := by
  decide

theorem demoM_2122010 : fieldMul 7 5 20 [0, 2, 1, 2, 2, 0, 0] [2, 1, 2, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2122010 : specInv 7 5 20 [2, 1, 2, 2, 0, 1, 0] = some [0, 2, 1, 2, 2, 0, 0] :=
  specInv_white_7 [2, 1, 2, 2, 0, 1, 0] [1, 1, 0, 0, 0, 1, 1] [1, 1, 0, 1, 0, 1, 1] [0, 2, 1, 2, 2, 0, 0] demoR1_2122010 demoR2_2122010 demoC_2122010 demoM_2122010

theorem demoR1_0222010 : invRung 7 5 20 [0, 2, 2, 2, 0, 1, 0] [0, 2, 2, 2, 0, 1, 0] 1 2 false = ([0, 0, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0222010 : invRung 7 5 20 [0, 2, 2, 2, 0, 1, 0] [0, 0, 2, 0, 2, 2, 2] 3 1 true = ([0, 1, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_0222010 : fieldCube 7 5 20 [0, 1, 2, 2, 2, 2, 0] = [1, 1, 1, 0, 2, 0, 2] := by
  decide

theorem demoM_0222010 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 0, 2] [0, 2, 2, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222010 : mirrorTrits [1, 1, 1, 0, 2, 0, 2] = [2, 2, 2, 0, 1, 0, 1] := by
  decide

theorem demoInv_0222010 : specInv 7 5 20 [0, 2, 2, 2, 0, 1, 0] = some [2, 2, 2, 0, 1, 0, 1] :=
  specInv_mirror_7 [0, 2, 2, 2, 0, 1, 0] [0, 0, 2, 0, 2, 2, 2] [0, 1, 2, 2, 2, 2, 0] [1, 1, 1, 0, 2, 0, 2] [2, 2, 2, 0, 1, 0, 1] demoR1_0222010 demoR2_0222010 demoC_0222010 demoM_0222010 demoMir_0222010

theorem demoR1_1222010 : invRung 7 5 20 [1, 2, 2, 2, 0, 1, 0] [1, 2, 2, 2, 0, 1, 0] 1 2 false = ([0, 1, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_1222010 : invRung 7 5 20 [1, 2, 2, 2, 0, 1, 0] [0, 1, 1, 0, 2, 2, 0] 3 1 true = ([2, 0, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_1222010 : fieldCube 7 5 20 [2, 0, 0, 1, 1, 2, 0] = [2, 0, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_1222010 : fieldMul 7 5 20 [2, 0, 0, 1, 2, 1, 2] [1, 2, 2, 2, 0, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222010 : mirrorTrits [2, 0, 0, 1, 2, 1, 2] = [1, 0, 0, 2, 1, 2, 1] := by
  decide

theorem demoInv_1222010 : specInv 7 5 20 [1, 2, 2, 2, 0, 1, 0] = some [1, 0, 0, 2, 1, 2, 1] :=
  specInv_mirror_7 [1, 2, 2, 2, 0, 1, 0] [0, 1, 1, 0, 2, 2, 0] [2, 0, 0, 1, 1, 2, 0] [2, 0, 0, 1, 2, 1, 2] [1, 0, 0, 2, 1, 2, 1] demoR1_1222010 demoR2_1222010 demoC_1222010 demoM_1222010 demoMir_1222010

theorem demoR1_2222010 : invRung 7 5 20 [2, 2, 2, 2, 0, 1, 0] [2, 2, 2, 2, 0, 1, 0] 1 2 false = ([1, 0, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_2222010 : invRung 7 5 20 [2, 2, 2, 2, 0, 1, 0] [1, 0, 0, 2, 0, 0, 1] 3 1 true = ([2, 1, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_2222010 : fieldCube 7 5 20 [2, 1, 0, 0, 0, 0, 2] = [2, 2, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_2222010 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 2, 2] [2, 2, 2, 2, 0, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2222010 : specInv 7 5 20 [2, 2, 2, 2, 0, 1, 0] = some [2, 2, 1, 0, 2, 2, 2] :=
  specInv_white_7 [2, 2, 2, 2, 0, 1, 0] [1, 0, 0, 2, 0, 0, 1] [2, 1, 0, 0, 0, 0, 2] [2, 2, 1, 0, 2, 2, 2] demoR1_2222010 demoR2_2222010 demoC_2222010 demoM_2222010

theorem demoR1_0000110 : invRung 7 5 20 [0, 0, 0, 0, 1, 1, 0] [0, 0, 0, 0, 1, 1, 0] 1 2 false = ([0, 0, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_0000110 : invRung 7 5 20 [0, 0, 0, 0, 1, 1, 0] [0, 0, 0, 0, 0, 1, 1] 3 1 true = ([2, 1, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_0000110 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 0, 0] = [0, 2, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_0000110 : fieldMul 7 5 20 [0, 2, 1, 0, 0, 0, 0] [0, 0, 0, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0000110 : specInv 7 5 20 [0, 0, 0, 0, 1, 1, 0] = some [0, 2, 1, 0, 0, 0, 0] :=
  specInv_white_7 [0, 0, 0, 0, 1, 1, 0] [0, 0, 0, 0, 0, 1, 1] [2, 1, 1, 1, 2, 0, 0] [0, 2, 1, 0, 0, 0, 0] demoR1_0000110 demoR2_0000110 demoC_0000110 demoM_0000110

theorem demoR1_1000110 : invRung 7 5 20 [1, 0, 0, 0, 1, 1, 0] [1, 0, 0, 0, 1, 1, 0] 1 2 false = ([2, 1, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_1000110 : invRung 7 5 20 [1, 0, 0, 0, 1, 1, 0] [2, 1, 1, 1, 0, 2, 2] 3 1 true = ([1, 2, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_1000110 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 2, 0] = [0, 1, 2, 1, 2, 1, 1] := by
  decide

theorem demoM_1000110 : fieldMul 7 5 20 [0, 1, 2, 1, 2, 1, 1] [1, 0, 0, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1000110 : specInv 7 5 20 [1, 0, 0, 0, 1, 1, 0] = some [0, 1, 2, 1, 2, 1, 1] :=
  specInv_white_7 [1, 0, 0, 0, 1, 1, 0] [2, 1, 1, 1, 0, 2, 2] [1, 2, 1, 0, 2, 2, 0] [0, 1, 2, 1, 2, 1, 1] demoR1_1000110 demoR2_1000110 demoC_1000110 demoM_1000110

theorem demoR1_2000110 : invRung 7 5 20 [2, 0, 0, 0, 1, 1, 0] [2, 0, 0, 0, 1, 1, 0] 1 2 false = ([2, 0, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_2000110 : invRung 7 5 20 [2, 0, 0, 0, 1, 1, 0] [2, 0, 1, 1, 2, 2, 0] 3 1 true = ([0, 2, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2000110 : fieldCube 7 5 20 [0, 2, 2, 1, 2, 2, 0] = [0, 1, 0, 1, 2, 2, 2] := by
  decide

theorem demoM_2000110 : fieldMul 7 5 20 [0, 1, 0, 1, 2, 2, 2] [2, 0, 0, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2000110 : specInv 7 5 20 [2, 0, 0, 0, 1, 1, 0] = some [0, 1, 0, 1, 2, 2, 2] :=
  specInv_white_7 [2, 0, 0, 0, 1, 1, 0] [2, 0, 1, 1, 2, 2, 0] [0, 2, 2, 1, 2, 2, 0] [0, 1, 0, 1, 2, 2, 2] demoR1_2000110 demoR2_2000110 demoC_2000110 demoM_2000110

theorem demoR1_0100110 : invRung 7 5 20 [0, 1, 0, 0, 1, 1, 0] [0, 1, 0, 0, 1, 1, 0] 1 2 false = ([0, 2, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_0100110 : invRung 7 5 20 [0, 1, 0, 0, 1, 1, 0] [0, 2, 2, 1, 1, 2, 2] 3 1 true = ([0, 2, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0100110 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 1, 0] = [2, 1, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_0100110 : fieldMul 7 5 20 [2, 1, 2, 2, 1, 2, 2] [0, 1, 0, 0, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100110 : mirrorTrits [2, 1, 2, 2, 1, 2, 2] = [1, 2, 1, 1, 2, 1, 1] := by
  decide

theorem demoInv_0100110 : specInv 7 5 20 [0, 1, 0, 0, 1, 1, 0] = some [1, 2, 1, 1, 2, 1, 1] :=
  specInv_mirror_7 [0, 1, 0, 0, 1, 1, 0] [0, 2, 2, 1, 1, 2, 2] [0, 2, 0, 1, 0, 1, 0] [2, 1, 2, 2, 1, 2, 2] [1, 2, 1, 1, 2, 1, 1] demoR1_0100110 demoR2_0100110 demoC_0100110 demoM_0100110 demoMir_0100110

theorem demoR1_1100110 : invRung 7 5 20 [1, 1, 0, 0, 1, 1, 0] [1, 1, 0, 0, 1, 1, 0] 1 2 false = ([1, 1, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_1100110 : invRung 7 5 20 [1, 1, 0, 0, 1, 1, 0] [1, 1, 1, 1, 0, 1, 0] 3 1 true = ([0, 0, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1100110 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 1, 1] = [1, 0, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_1100110 : fieldMul 7 5 20 [1, 0, 0, 2, 2, 0, 1] [1, 1, 0, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1100110 : specInv 7 5 20 [1, 1, 0, 0, 1, 1, 0] = some [1, 0, 0, 2, 2, 0, 1] :=
  specInv_white_7 [1, 1, 0, 0, 1, 1, 0] [1, 1, 1, 1, 0, 1, 0] [0, 0, 0, 0, 1, 1, 1] [1, 0, 0, 2, 2, 0, 1] demoR1_1100110 demoR2_1100110 demoC_1100110 demoM_1100110

theorem demoR1_2100110 : invRung 7 5 20 [2, 1, 0, 0, 1, 1, 0] [2, 1, 0, 0, 1, 1, 0] 1 2 false = ([2, 0, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_2100110 : invRung 7 5 20 [2, 1, 0, 0, 1, 1, 0] [2, 0, 1, 2, 1, 1, 1] 3 1 true = ([1, 0, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_2100110 : fieldCube 7 5 20 [1, 0, 1, 2, 2, 2, 0] = [2, 1, 1, 2, 2, 0, 1] := by
  decide

theorem demoM_2100110 : fieldMul 7 5 20 [2, 1, 1, 2, 2, 0, 1] [2, 1, 0, 0, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100110 : mirrorTrits [2, 1, 1, 2, 2, 0, 1] = [1, 2, 2, 1, 1, 0, 2] := by
  decide

theorem demoInv_2100110 : specInv 7 5 20 [2, 1, 0, 0, 1, 1, 0] = some [1, 2, 2, 1, 1, 0, 2] :=
  specInv_mirror_7 [2, 1, 0, 0, 1, 1, 0] [2, 0, 1, 2, 1, 1, 1] [1, 0, 1, 2, 2, 2, 0] [2, 1, 1, 2, 2, 0, 1] [1, 2, 2, 1, 1, 0, 2] demoR1_2100110 demoR2_2100110 demoC_2100110 demoM_2100110 demoMir_2100110

theorem demoR1_0200110 : invRung 7 5 20 [0, 2, 0, 0, 1, 1, 0] [0, 2, 0, 0, 1, 1, 0] 1 2 false = ([2, 0, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0200110 : invRung 7 5 20 [0, 2, 0, 0, 1, 1, 0] [2, 0, 2, 0, 1, 2, 1] 3 1 true = ([1, 2, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_0200110 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 0, 0] = [0, 2, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_0200110 : fieldMul 7 5 20 [0, 2, 2, 1, 0, 1, 1] [0, 2, 0, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0200110 : specInv 7 5 20 [0, 2, 0, 0, 1, 1, 0] = some [0, 2, 2, 1, 0, 1, 1] :=
  specInv_white_7 [0, 2, 0, 0, 1, 1, 0] [2, 0, 2, 0, 1, 2, 1] [1, 2, 2, 2, 2, 0, 0] [0, 2, 2, 1, 0, 1, 1] demoR1_0200110 demoR2_0200110 demoC_0200110 demoM_0200110

theorem demoR1_1200110 : invRung 7 5 20 [1, 2, 0, 0, 1, 1, 0] [1, 2, 0, 0, 1, 1, 0] 1 2 false = ([2, 1, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1200110 : invRung 7 5 20 [1, 2, 0, 0, 1, 1, 0] [2, 1, 2, 0, 1, 1, 0] 3 1 true = ([1, 2, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_1200110 : fieldCube 7 5 20 [1, 2, 0, 2, 0, 2, 0] = [2, 2, 1, 2, 2, 1, 1] := by
  decide

theorem demoM_1200110 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 1, 1] [1, 2, 0, 0, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200110 : mirrorTrits [2, 2, 1, 2, 2, 1, 1] = [1, 1, 2, 1, 1, 2, 2] := by
  decide

theorem demoInv_1200110 : specInv 7 5 20 [1, 2, 0, 0, 1, 1, 0] = some [1, 1, 2, 1, 1, 2, 2] :=
  specInv_mirror_7 [1, 2, 0, 0, 1, 1, 0] [2, 1, 2, 0, 1, 1, 0] [1, 2, 0, 2, 0, 2, 0] [2, 2, 1, 2, 2, 1, 1] [1, 1, 2, 1, 1, 2, 2] demoR1_1200110 demoR2_1200110 demoC_1200110 demoM_1200110 demoMir_1200110

theorem demoR1_2200110 : invRung 7 5 20 [2, 2, 0, 0, 1, 1, 0] [2, 2, 0, 0, 1, 1, 0] 1 2 false = ([1, 1, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_2200110 : invRung 7 5 20 [2, 2, 0, 0, 1, 1, 0] [1, 1, 2, 0, 0, 0, 2] 3 1 true = ([0, 0, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2200110 : fieldCube 7 5 20 [0, 0, 1, 0, 0, 1, 0] = [1, 1, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_2200110 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 1, 0] [2, 2, 0, 0, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200110 : mirrorTrits [1, 1, 1, 0, 1, 1, 0] = [2, 2, 2, 0, 2, 2, 0] := by
  decide

theorem demoInv_2200110 : specInv 7 5 20 [2, 2, 0, 0, 1, 1, 0] = some [2, 2, 2, 0, 2, 2, 0] :=
  specInv_mirror_7 [2, 2, 0, 0, 1, 1, 0] [1, 1, 2, 0, 0, 0, 2] [0, 0, 1, 0, 0, 1, 0] [1, 1, 1, 0, 1, 1, 0] [2, 2, 2, 0, 2, 2, 0] demoR1_2200110 demoR2_2200110 demoC_2200110 demoM_2200110 demoMir_2200110

theorem demoR1_0010110 : invRung 7 5 20 [0, 0, 1, 0, 1, 1, 0] [0, 0, 1, 0, 1, 1, 0] 1 2 false = ([0, 2, 2, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_0010110 : invRung 7 5 20 [0, 0, 1, 0, 1, 1, 0] [0, 2, 2, 1, 2, 0, 2] 3 1 true = ([0, 2, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_0010110 : fieldCube 7 5 20 [0, 2, 2, 2, 1, 2, 0] = [1, 0, 1, 0, 2, 2, 1] := by
  decide

theorem demoM_0010110 : fieldMul 7 5 20 [1, 0, 1, 0, 2, 2, 1] [0, 0, 1, 0, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010110 : mirrorTrits [1, 0, 1, 0, 2, 2, 1] = [2, 0, 2, 0, 1, 1, 2] := by
  decide

theorem demoInv_0010110 : specInv 7 5 20 [0, 0, 1, 0, 1, 1, 0] = some [2, 0, 2, 0, 1, 1, 2] :=
  specInv_mirror_7 [0, 0, 1, 0, 1, 1, 0] [0, 2, 2, 1, 2, 0, 2] [0, 2, 2, 2, 1, 2, 0] [1, 0, 1, 0, 2, 2, 1] [2, 0, 2, 0, 1, 1, 2] demoR1_0010110 demoR2_0010110 demoC_0010110 demoM_0010110 demoMir_0010110

theorem demoR1_1010110 : invRung 7 5 20 [1, 0, 1, 0, 1, 1, 0] [1, 0, 1, 0, 1, 1, 0] 1 2 false = ([2, 2, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_1010110 : invRung 7 5 20 [1, 0, 1, 0, 1, 1, 0] [2, 2, 1, 1, 0, 1, 1] 3 1 true = ([1, 0, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_1010110 : fieldCube 7 5 20 [1, 0, 0, 2, 2, 0, 2] = [0, 1, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_1010110 : fieldMul 7 5 20 [0, 1, 0, 1, 2, 0, 1] [1, 0, 1, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1010110 : specInv 7 5 20 [1, 0, 1, 0, 1, 1, 0] = some [0, 1, 0, 1, 2, 0, 1] :=
  specInv_white_7 [1, 0, 1, 0, 1, 1, 0] [2, 2, 1, 1, 0, 1, 1] [1, 0, 0, 2, 2, 0, 2] [0, 1, 0, 1, 2, 0, 1] demoR1_1010110 demoR2_1010110 demoC_1010110 demoM_1010110

theorem demoR1_2010110 : invRung 7 5 20 [2, 0, 1, 0, 1, 1, 0] [2, 0, 1, 0, 1, 1, 0] 1 2 false = ([2, 2, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2010110 : invRung 7 5 20 [2, 0, 1, 0, 1, 1, 0] [2, 2, 2, 2, 2, 0, 1] 3 1 true = ([1, 2, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2010110 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 2, 0] = [1, 1, 0, 1, 2, 2, 1] := by
  decide

theorem demoM_2010110 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 2, 1] [2, 0, 1, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2010110 : specInv 7 5 20 [2, 0, 1, 0, 1, 1, 0] = some [1, 1, 0, 1, 2, 2, 1] :=
  specInv_white_7 [2, 0, 1, 0, 1, 1, 0] [2, 2, 2, 2, 2, 0, 1] [1, 2, 1, 1, 2, 2, 0] [1, 1, 0, 1, 2, 2, 1] demoR1_2010110 demoR2_2010110 demoC_2010110 demoM_2010110

theorem demoR1_0110110 : invRung 7 5 20 [0, 1, 1, 0, 1, 1, 0] [0, 1, 1, 0, 1, 1, 0] 1 2 false = ([0, 1, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_0110110 : invRung 7 5 20 [0, 1, 1, 0, 1, 1, 0] [0, 1, 0, 2, 1, 1, 0] 3 1 true = ([0, 2, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_0110110 : fieldCube 7 5 20 [0, 2, 2, 2, 2, 0, 0] = [2, 2, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_0110110 : fieldMul 7 5 20 [2, 2, 2, 1, 0, 1, 1] [0, 1, 1, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0110110 : specInv 7 5 20 [0, 1, 1, 0, 1, 1, 0] = some [2, 2, 2, 1, 0, 1, 1] :=
  specInv_white_7 [0, 1, 1, 0, 1, 1, 0] [0, 1, 0, 2, 1, 1, 0] [0, 2, 2, 2, 2, 0, 0] [2, 2, 2, 1, 0, 1, 1] demoR1_0110110 demoR2_0110110 demoC_0110110 demoM_0110110

theorem demoR1_1110110 : invRung 7 5 20 [1, 1, 1, 0, 1, 1, 0] [1, 1, 1, 0, 1, 1, 0] 1 2 false = ([1, 1, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_1110110 : invRung 7 5 20 [1, 1, 1, 0, 1, 1, 0] [1, 1, 1, 0, 2, 1, 1] 3 1 true = ([1, 1, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1110110 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 2, 0] = [1, 1, 0, 0, 2, 2, 0] := by
  decide

theorem demoM_1110110 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 2, 0] [1, 1, 1, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1110110 : specInv 7 5 20 [1, 1, 1, 0, 1, 1, 0] = some [1, 1, 0, 0, 2, 2, 0] :=
  specInv_white_7 [1, 1, 1, 0, 1, 1, 0] [1, 1, 1, 0, 2, 1, 1] [1, 1, 0, 1, 2, 2, 0] [1, 1, 0, 0, 2, 2, 0] demoR1_1110110 demoR2_1110110 demoC_1110110 demoM_1110110

theorem demoR1_2110110 : invRung 7 5 20 [2, 1, 1, 0, 1, 1, 0] [2, 1, 1, 0, 1, 1, 0] 1 2 false = ([2, 0, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_2110110 : invRung 7 5 20 [2, 1, 1, 0, 1, 1, 0] [2, 0, 0, 1, 1, 1, 0] 3 1 true = ([0, 1, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_2110110 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 1, 0] = [2, 1, 2, 1, 1, 2, 2] := by
  decide

theorem demoM_2110110 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 2, 2] [2, 1, 1, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2110110 : specInv 7 5 20 [2, 1, 1, 0, 1, 1, 0] = some [2, 1, 2, 1, 1, 2, 2] :=
  specInv_white_7 [2, 1, 1, 0, 1, 1, 0] [2, 0, 0, 1, 1, 1, 0] [0, 1, 0, 1, 0, 1, 0] [2, 1, 2, 1, 1, 2, 2] demoR1_2110110 demoR2_2110110 demoC_2110110 demoM_2110110

theorem demoR1_0210110 : invRung 7 5 20 [0, 2, 1, 0, 1, 1, 0] [0, 2, 1, 0, 1, 1, 0] 1 2 false = ([0, 1, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_0210110 : invRung 7 5 20 [0, 2, 1, 0, 1, 1, 0] [0, 1, 0, 1, 2, 2, 2] 3 1 true = ([2, 0, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0210110 : fieldCube 7 5 20 [2, 0, 2, 1, 0, 1, 1] = [1, 2, 1, 1, 2, 0, 2] := by
  decide

theorem demoM_0210110 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 0, 2] [0, 2, 1, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0210110 : specInv 7 5 20 [0, 2, 1, 0, 1, 1, 0] = some [1, 2, 1, 1, 2, 0, 2] :=
  specInv_white_7 [0, 2, 1, 0, 1, 1, 0] [0, 1, 0, 1, 2, 2, 2] [2, 0, 2, 1, 0, 1, 1] [1, 2, 1, 1, 2, 0, 2] demoR1_0210110 demoR2_0210110 demoC_0210110 demoM_0210110

theorem demoR1_1210110 : invRung 7 5 20 [1, 2, 1, 0, 1, 1, 0] [1, 2, 1, 0, 1, 1, 0] 1 2 false = ([0, 2, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_1210110 : invRung 7 5 20 [1, 2, 1, 0, 1, 1, 0] [0, 2, 0, 1, 2, 0, 0] 3 1 true = ([2, 2, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_1210110 : fieldCube 7 5 20 [2, 2, 2, 1, 1, 1, 2] = [1, 1, 0, 2, 0, 2, 1] := by
  decide

theorem demoM_1210110 : fieldMul 7 5 20 [1, 1, 0, 2, 0, 2, 1] [1, 2, 1, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1210110 : specInv 7 5 20 [1, 2, 1, 0, 1, 1, 0] = some [1, 1, 0, 2, 0, 2, 1] :=
  specInv_white_7 [1, 2, 1, 0, 1, 1, 0] [0, 2, 0, 1, 2, 0, 0] [2, 2, 2, 1, 1, 1, 2] [1, 1, 0, 2, 0, 2, 1] demoR1_1210110 demoR2_1210110 demoC_1210110 demoM_1210110

theorem demoR1_2210110 : invRung 7 5 20 [2, 2, 1, 0, 1, 1, 0] [2, 2, 1, 0, 1, 1, 0] 1 2 false = ([2, 1, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_2210110 : invRung 7 5 20 [2, 2, 1, 0, 1, 1, 0] [2, 1, 0, 0, 0, 0, 2] 3 1 true = ([0, 2, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2210110 : fieldCube 7 5 20 [0, 2, 2, 1, 0, 2, 1] = [0, 0, 2, 0, 0, 1, 1] := by
  decide

theorem demoM_2210110 : fieldMul 7 5 20 [0, 0, 2, 0, 0, 1, 1] [2, 2, 1, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2210110 : specInv 7 5 20 [2, 2, 1, 0, 1, 1, 0] = some [0, 0, 2, 0, 0, 1, 1] :=
  specInv_white_7 [2, 2, 1, 0, 1, 1, 0] [2, 1, 0, 0, 0, 0, 2] [0, 2, 2, 1, 0, 2, 1] [0, 0, 2, 0, 0, 1, 1] demoR1_2210110 demoR2_2210110 demoC_2210110 demoM_2210110

theorem demoR1_0020110 : invRung 7 5 20 [0, 0, 2, 0, 1, 1, 0] [0, 0, 2, 0, 1, 1, 0] 1 2 false = ([0, 0, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_0020110 : invRung 7 5 20 [0, 0, 2, 0, 1, 1, 0] [0, 0, 0, 1, 1, 2, 2] 3 1 true = ([0, 0, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_0020110 : fieldCube 7 5 20 [0, 0, 1, 0, 1, 2, 0] = [2, 0, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_0020110 : fieldMul 7 5 20 [2, 0, 2, 1, 2, 0, 0] [0, 0, 2, 0, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020110 : mirrorTrits [2, 0, 2, 1, 2, 0, 0] = [1, 0, 1, 2, 1, 0, 0] := by
  decide

theorem demoInv_0020110 : specInv 7 5 20 [0, 0, 2, 0, 1, 1, 0] = some [1, 0, 1, 2, 1, 0, 0] :=
  specInv_mirror_7 [0, 0, 2, 0, 1, 1, 0] [0, 0, 0, 1, 1, 2, 2] [0, 0, 1, 0, 1, 2, 0] [2, 0, 2, 1, 2, 0, 0] [1, 0, 1, 2, 1, 0, 0] demoR1_0020110 demoR2_0020110 demoC_0020110 demoM_0020110 demoMir_0020110

theorem demoR1_1020110 : invRung 7 5 20 [1, 0, 2, 0, 1, 1, 0] [1, 0, 2, 0, 1, 1, 0] 1 2 false = ([1, 2, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_1020110 : invRung 7 5 20 [1, 0, 2, 0, 1, 1, 0] [1, 2, 1, 0, 0, 0, 1] 3 1 true = ([0, 2, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_1020110 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 1, 0] = [2, 2, 2, 0, 1, 0, 2] := by
  decide

theorem demoM_1020110 : fieldMul 7 5 20 [2, 2, 2, 0, 1, 0, 2] [1, 0, 2, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1020110 : specInv 7 5 20 [1, 0, 2, 0, 1, 1, 0] = some [2, 2, 2, 0, 1, 0, 2] :=
  specInv_white_7 [1, 0, 2, 0, 1, 1, 0] [1, 2, 1, 0, 0, 0, 1] [0, 2, 2, 1, 1, 1, 0] [2, 2, 2, 0, 1, 0, 2] demoR1_1020110 demoR2_1020110 demoC_1020110 demoM_1020110

theorem demoR1_2020110 : invRung 7 5 20 [2, 0, 2, 0, 1, 1, 0] [2, 0, 2, 0, 1, 1, 0] 1 2 false = ([0, 0, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2020110 : invRung 7 5 20 [2, 0, 2, 0, 1, 1, 0] [0, 0, 1, 2, 2, 1, 2] 3 1 true = ([1, 0, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2020110 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 2, 1] = [1, 1, 2, 2, 0, 2, 1] := by
  decide

theorem demoM_2020110 : fieldMul 7 5 20 [1, 1, 2, 2, 0, 2, 1] [2, 0, 2, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2020110 : specInv 7 5 20 [2, 0, 2, 0, 1, 1, 0] = some [1, 1, 2, 2, 0, 2, 1] :=
  specInv_white_7 [2, 0, 2, 0, 1, 1, 0] [0, 0, 1, 2, 2, 1, 2] [1, 0, 1, 1, 1, 2, 1] [1, 1, 2, 2, 0, 2, 1] demoR1_2020110 demoR2_2020110 demoC_2020110 demoM_2020110

theorem demoR1_0120110 : invRung 7 5 20 [0, 1, 2, 0, 1, 1, 0] [0, 1, 2, 0, 1, 1, 0] 1 2 false = ([0, 1, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_0120110 : invRung 7 5 20 [0, 1, 2, 0, 1, 1, 0] [0, 1, 2, 1, 0, 2, 2] 3 1 true = ([2, 2, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_0120110 : fieldCube 7 5 20 [2, 2, 0, 2, 2, 2, 0] = [0, 1, 1, 1, 2, 0, 0] := by
  decide

theorem demoM_0120110 : fieldMul 7 5 20 [0, 1, 1, 1, 2, 0, 0] [0, 1, 2, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0120110 : specInv 7 5 20 [0, 1, 2, 0, 1, 1, 0] = some [0, 1, 1, 1, 2, 0, 0] :=
  specInv_white_7 [0, 1, 2, 0, 1, 1, 0] [0, 1, 2, 1, 0, 2, 2] [2, 2, 0, 2, 2, 2, 0] [0, 1, 1, 1, 2, 0, 0] demoR1_0120110 demoR2_0120110 demoC_0120110 demoM_0120110

theorem demoR1_1120110 : invRung 7 5 20 [1, 1, 2, 0, 1, 1, 0] [1, 1, 2, 0, 1, 1, 0] 1 2 false = ([0, 2, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_1120110 : invRung 7 5 20 [1, 1, 2, 0, 1, 1, 0] [0, 2, 0, 0, 0, 0, 2] 3 1 true = ([0, 2, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1120110 : fieldCube 7 5 20 [0, 2, 1, 0, 0, 1, 0] = [1, 1, 1, 2, 1, 1, 0] := by
  decide

theorem demoM_1120110 : fieldMul 7 5 20 [1, 1, 1, 2, 1, 1, 0] [1, 1, 2, 0, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120110 : mirrorTrits [1, 1, 1, 2, 1, 1, 0] = [2, 2, 2, 1, 2, 2, 0] := by
  decide

theorem demoInv_1120110 : specInv 7 5 20 [1, 1, 2, 0, 1, 1, 0] = some [2, 2, 2, 1, 2, 2, 0] :=
  specInv_mirror_7 [1, 1, 2, 0, 1, 1, 0] [0, 2, 0, 0, 0, 0, 2] [0, 2, 1, 0, 0, 1, 0] [1, 1, 1, 2, 1, 1, 0] [2, 2, 2, 1, 2, 2, 0] demoR1_1120110 demoR2_1120110 demoC_1120110 demoM_1120110 demoMir_1120110

theorem demoR1_2120110 : invRung 7 5 20 [2, 1, 2, 0, 1, 1, 0] [2, 1, 2, 0, 1, 1, 0] 1 2 false = ([0, 1, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_2120110 : invRung 7 5 20 [2, 1, 2, 0, 1, 1, 0] [0, 1, 2, 1, 0, 0, 1] 3 1 true = ([2, 2, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2120110 : fieldCube 7 5 20 [2, 2, 0, 0, 1, 1, 1] = [0, 0, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_2120110 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 0, 1] [2, 1, 2, 0, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120110 : mirrorTrits [0, 0, 0, 1, 2, 0, 1] = [0, 0, 0, 2, 1, 0, 2] := by
  decide

theorem demoInv_2120110 : specInv 7 5 20 [2, 1, 2, 0, 1, 1, 0] = some [0, 0, 0, 2, 1, 0, 2] :=
  specInv_mirror_7 [2, 1, 2, 0, 1, 1, 0] [0, 1, 2, 1, 0, 0, 1] [2, 2, 0, 0, 1, 1, 1] [0, 0, 0, 1, 2, 0, 1] [0, 0, 0, 2, 1, 0, 2] demoR1_2120110 demoR2_2120110 demoC_2120110 demoM_2120110 demoMir_2120110

theorem demoR1_0220110 : invRung 7 5 20 [0, 2, 2, 0, 1, 1, 0] [0, 2, 2, 0, 1, 1, 0] 1 2 false = ([1, 2, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_0220110 : invRung 7 5 20 [0, 2, 2, 0, 1, 1, 0] [1, 2, 1, 2, 1, 0, 0] 3 1 true = ([1, 2, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_0220110 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 1, 1] = [2, 1, 0, 2, 2, 1, 0] := by
  decide

theorem demoM_0220110 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 1, 0] [0, 2, 2, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0220110 : specInv 7 5 20 [0, 2, 2, 0, 1, 1, 0] = some [2, 1, 0, 2, 2, 1, 0] :=
  specInv_white_7 [0, 2, 2, 0, 1, 1, 0] [1, 2, 1, 2, 1, 0, 0] [1, 2, 1, 0, 2, 1, 1] [2, 1, 0, 2, 2, 1, 0] demoR1_0220110 demoR2_0220110 demoC_0220110 demoM_0220110

theorem demoR1_1220110 : invRung 7 5 20 [1, 2, 2, 0, 1, 1, 0] [1, 2, 2, 0, 1, 1, 0] 1 2 false = ([0, 0, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1220110 : invRung 7 5 20 [1, 2, 2, 0, 1, 1, 0] [0, 0, 2, 2, 1, 0, 2] 3 1 true = ([0, 0, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_1220110 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 1, 1] = [0, 1, 2, 0, 2, 0, 0] := by
  decide

theorem demoM_1220110 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 0, 0] [1, 2, 2, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1220110 : specInv 7 5 20 [1, 2, 2, 0, 1, 1, 0] = some [0, 1, 2, 0, 2, 0, 0] :=
  specInv_white_7 [1, 2, 2, 0, 1, 1, 0] [0, 0, 2, 2, 1, 0, 2] [0, 0, 1, 2, 2, 1, 1] [0, 1, 2, 0, 2, 0, 0] demoR1_1220110 demoR2_1220110 demoC_1220110 demoM_1220110

theorem demoR1_2220110 : invRung 7 5 20 [2, 2, 2, 0, 1, 1, 0] [2, 2, 2, 0, 1, 1, 0] 1 2 false = ([1, 1, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_2220110 : invRung 7 5 20 [2, 2, 2, 0, 1, 1, 0] [1, 1, 0, 0, 1, 1, 0] 3 1 true = ([2, 0, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_2220110 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 0, 2] = [2, 0, 1, 0, 2, 0, 1] := by
  decide

theorem demoM_2220110 : fieldMul 7 5 20 [2, 0, 1, 0, 2, 0, 1] [2, 2, 2, 0, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2220110 : specInv 7 5 20 [2, 2, 2, 0, 1, 1, 0] = some [2, 0, 1, 0, 2, 0, 1] :=
  specInv_white_7 [2, 2, 2, 0, 1, 1, 0] [1, 1, 0, 0, 1, 1, 0] [2, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0, 1] demoR1_2220110 demoR2_2220110 demoC_2220110 demoM_2220110

theorem demoR1_0001110 : invRung 7 5 20 [0, 0, 0, 1, 1, 1, 0] [0, 0, 0, 1, 1, 1, 0] 1 2 false = ([0, 2, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_0001110 : invRung 7 5 20 [0, 0, 0, 1, 1, 1, 0] [0, 2, 2, 1, 2, 1, 1] 3 1 true = ([0, 0, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_0001110 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 2, 1] = [2, 2, 1, 0, 0, 2, 2] := by
  decide

theorem demoM_0001110 : fieldMul 7 5 20 [2, 2, 1, 0, 0, 2, 2] [0, 0, 0, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0001110 : specInv 7 5 20 [0, 0, 0, 1, 1, 1, 0] = some [2, 2, 1, 0, 0, 2, 2] :=
  specInv_white_7 [0, 0, 0, 1, 1, 1, 0] [0, 2, 2, 1, 2, 1, 1] [0, 0, 1, 0, 2, 2, 1] [2, 2, 1, 0, 0, 2, 2] demoR1_0001110 demoR2_0001110 demoC_0001110 demoM_0001110

theorem demoR1_1001110 : invRung 7 5 20 [1, 0, 0, 1, 1, 1, 0] [1, 0, 0, 1, 1, 1, 0] 1 2 false = ([2, 0, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_1001110 : invRung 7 5 20 [1, 0, 0, 1, 1, 1, 0] [2, 0, 2, 2, 0, 2, 0] 3 1 true = ([1, 0, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1001110 : fieldCube 7 5 20 [1, 0, 1, 0, 1, 1, 0] = [2, 2, 1, 1, 1, 2, 1] := by
  decide

theorem demoM_1001110 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 2, 1] [1, 0, 0, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1001110 : specInv 7 5 20 [1, 0, 0, 1, 1, 1, 0] = some [2, 2, 1, 1, 1, 2, 1] :=
  specInv_white_7 [1, 0, 0, 1, 1, 1, 0] [2, 0, 2, 2, 0, 2, 0] [1, 0, 1, 0, 1, 1, 0] [2, 2, 1, 1, 1, 2, 1] demoR1_1001110 demoR2_1001110 demoC_1001110 demoM_1001110

theorem demoR1_2001110 : invRung 7 5 20 [2, 0, 0, 1, 1, 1, 0] [2, 0, 0, 1, 1, 1, 0] 1 2 false = ([2, 1, 2, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_2001110 : invRung 7 5 20 [2, 0, 0, 1, 1, 1, 0] [2, 1, 2, 1, 2, 0, 2] 3 1 true = ([0, 2, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_2001110 : fieldCube 7 5 20 [0, 2, 0, 2, 1, 1, 2] = [0, 1, 1, 2, 0, 0, 2] := by
  decide

theorem demoM_2001110 : fieldMul 7 5 20 [0, 1, 1, 2, 0, 0, 2] [2, 0, 0, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2001110 : specInv 7 5 20 [2, 0, 0, 1, 1, 1, 0] = some [0, 1, 1, 2, 0, 0, 2] :=
  specInv_white_7 [2, 0, 0, 1, 1, 1, 0] [2, 1, 2, 1, 2, 0, 2] [0, 2, 0, 2, 1, 1, 2] [0, 1, 1, 2, 0, 0, 2] demoR1_2001110 demoR2_2001110 demoC_2001110 demoM_2001110

theorem demoR1_0101110 : invRung 7 5 20 [0, 1, 0, 1, 1, 1, 0] [0, 1, 0, 1, 1, 1, 0] 1 2 false = ([2, 2, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0101110 : invRung 7 5 20 [0, 1, 0, 1, 1, 1, 0] [2, 2, 2, 2, 1, 2, 1] 3 1 true = ([2, 1, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_0101110 : fieldCube 7 5 20 [2, 1, 0, 1, 1, 2, 1] = [2, 1, 2, 0, 0, 2, 0] := by
  decide

theorem demoM_0101110 : fieldMul 7 5 20 [2, 1, 2, 0, 0, 2, 0] [0, 1, 0, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0101110 : specInv 7 5 20 [0, 1, 0, 1, 1, 1, 0] = some [2, 1, 2, 0, 0, 2, 0] :=
  specInv_white_7 [0, 1, 0, 1, 1, 1, 0] [2, 2, 2, 2, 1, 2, 1] [2, 1, 0, 1, 1, 2, 1] [2, 1, 2, 0, 0, 2, 0] demoR1_0101110 demoR2_0101110 demoC_0101110 demoM_0101110

theorem demoR1_1101110 : invRung 7 5 20 [1, 1, 0, 1, 1, 1, 0] [1, 1, 0, 1, 1, 1, 0] 1 2 false = ([1, 1, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_1101110 : invRung 7 5 20 [1, 1, 0, 1, 1, 1, 0] [1, 1, 0, 2, 0, 0, 0] 3 1 true = ([0, 0, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_1101110 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 2, 1] = [0, 2, 2, 0, 0, 0, 1] := by
  decide

theorem demoM_1101110 : fieldMul 7 5 20 [0, 2, 2, 0, 0, 0, 1] [1, 1, 0, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1101110 : mirrorTrits [0, 2, 2, 0, 0, 0, 1] = [0, 1, 1, 0, 0, 0, 2] := by
  decide

theorem demoInv_1101110 : specInv 7 5 20 [1, 1, 0, 1, 1, 1, 0] = some [0, 1, 1, 0, 0, 0, 2] :=
  specInv_mirror_7 [1, 1, 0, 1, 1, 1, 0] [1, 1, 0, 2, 0, 0, 0] [0, 0, 0, 1, 2, 2, 1] [0, 2, 2, 0, 0, 0, 1] [0, 1, 1, 0, 0, 0, 2] demoR1_1101110 demoR2_1101110 demoC_1101110 demoM_1101110 demoMir_1101110

theorem demoR1_2101110 : invRung 7 5 20 [2, 1, 0, 1, 1, 1, 0] [2, 1, 0, 1, 1, 1, 0] 1 2 false = ([0, 2, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2101110 : invRung 7 5 20 [2, 1, 0, 1, 1, 1, 0] [0, 2, 0, 2, 0, 0, 2] 3 1 true = ([1, 2, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_2101110 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 1, 0] = [1, 2, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_2101110 : fieldMul 7 5 20 [1, 2, 0, 0, 1, 1, 1] [2, 1, 0, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101110 : mirrorTrits [1, 2, 0, 0, 1, 1, 1] = [2, 1, 0, 0, 2, 2, 2] := by
  decide

theorem demoInv_2101110 : specInv 7 5 20 [2, 1, 0, 1, 1, 1, 0] = some [2, 1, 0, 0, 2, 2, 2] :=
  specInv_mirror_7 [2, 1, 0, 1, 1, 1, 0] [0, 2, 0, 2, 0, 0, 2] [1, 2, 1, 2, 1, 1, 0] [1, 2, 0, 0, 1, 1, 1] [2, 1, 0, 0, 2, 2, 2] demoR1_2101110 demoR2_2101110 demoC_2101110 demoM_2101110 demoMir_2101110

theorem demoR1_0201110 : invRung 7 5 20 [0, 2, 0, 1, 1, 1, 0] [0, 2, 0, 1, 1, 1, 0] 1 2 false = ([0, 2, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_0201110 : invRung 7 5 20 [0, 2, 0, 1, 1, 1, 0] [0, 2, 0, 2, 1, 0, 0] 3 1 true = ([1, 0, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0201110 : fieldCube 7 5 20 [1, 0, 0, 0, 1, 2, 2] = [0, 2, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_0201110 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 2, 1] [0, 2, 0, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201110 : mirrorTrits [0, 2, 0, 0, 1, 2, 1] = [0, 1, 0, 0, 2, 1, 2] := by
  decide

theorem demoInv_0201110 : specInv 7 5 20 [0, 2, 0, 1, 1, 1, 0] = some [0, 1, 0, 0, 2, 1, 2] :=
  specInv_mirror_7 [0, 2, 0, 1, 1, 1, 0] [0, 2, 0, 2, 1, 0, 0] [1, 0, 0, 0, 1, 2, 2] [0, 2, 0, 0, 1, 2, 1] [0, 1, 0, 0, 2, 1, 2] demoR1_0201110 demoR2_0201110 demoC_0201110 demoM_0201110 demoMir_0201110

theorem demoR1_1201110 : invRung 7 5 20 [1, 2, 0, 1, 1, 1, 0] [1, 2, 0, 1, 1, 1, 0] 1 2 false = ([2, 0, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_1201110 : invRung 7 5 20 [1, 2, 0, 1, 1, 1, 0] [2, 0, 2, 2, 0, 0, 0] 3 1 true = ([1, 0, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1201110 : fieldCube 7 5 20 [1, 0, 0, 1, 1, 2, 1] = [1, 1, 2, 2, 0, 2, 0] := by
  decide

theorem demoM_1201110 : fieldMul 7 5 20 [1, 1, 2, 2, 0, 2, 0] [1, 2, 0, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1201110 : specInv 7 5 20 [1, 2, 0, 1, 1, 1, 0] = some [1, 1, 2, 2, 0, 2, 0] :=
  specInv_white_7 [1, 2, 0, 1, 1, 1, 0] [2, 0, 2, 2, 0, 0, 0] [1, 0, 0, 1, 1, 2, 1] [1, 1, 2, 2, 0, 2, 0] demoR1_1201110 demoR2_1201110 demoC_1201110 demoM_1201110

theorem demoR1_2201110 : invRung 7 5 20 [2, 2, 0, 1, 1, 1, 0] [2, 2, 0, 1, 1, 1, 0] 1 2 false = ([0, 2, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_2201110 : invRung 7 5 20 [2, 2, 0, 1, 1, 1, 0] [0, 2, 2, 1, 0, 1, 0] 3 1 true = ([2, 2, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2201110 : fieldCube 7 5 20 [2, 2, 1, 2, 0, 1, 0] = [2, 1, 0, 2, 1, 0, 0] := by
  decide

theorem demoM_2201110 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 0, 0] [2, 2, 0, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2201110 : mirrorTrits [2, 1, 0, 2, 1, 0, 0] = [1, 2, 0, 1, 2, 0, 0] := by
  decide

theorem demoInv_2201110 : specInv 7 5 20 [2, 2, 0, 1, 1, 1, 0] = some [1, 2, 0, 1, 2, 0, 0] :=
  specInv_mirror_7 [2, 2, 0, 1, 1, 1, 0] [0, 2, 2, 1, 0, 1, 0] [2, 2, 1, 2, 0, 1, 0] [2, 1, 0, 2, 1, 0, 0] [1, 2, 0, 1, 2, 0, 0] demoR1_2201110 demoR2_2201110 demoC_2201110 demoM_2201110 demoMir_2201110

theorem demoR1_0011110 : invRung 7 5 20 [0, 0, 1, 1, 1, 1, 0] [0, 0, 1, 1, 1, 1, 0] 1 2 false = ([1, 1, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_0011110 : invRung 7 5 20 [0, 0, 1, 1, 1, 1, 0] [1, 1, 0, 2, 2, 1, 2] 3 1 true = ([1, 2, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0011110 : fieldCube 7 5 20 [1, 2, 1, 2, 2, 0, 2] = [0, 1, 0, 0, 2, 0, 2] := by
  decide

theorem demoM_0011110 : fieldMul 7 5 20 [0, 1, 0, 0, 2, 0, 2] [0, 0, 1, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011110 : mirrorTrits [0, 1, 0, 0, 2, 0, 2] = [0, 2, 0, 0, 1, 0, 1] := by
  decide

theorem demoInv_0011110 : specInv 7 5 20 [0, 0, 1, 1, 1, 1, 0] = some [0, 2, 0, 0, 1, 0, 1] :=
  specInv_mirror_7 [0, 0, 1, 1, 1, 1, 0] [1, 1, 0, 2, 2, 1, 2] [1, 2, 1, 2, 2, 0, 2] [0, 1, 0, 0, 2, 0, 2] [0, 2, 0, 0, 1, 0, 1] demoR1_0011110 demoR2_0011110 demoC_0011110 demoM_0011110 demoMir_0011110

theorem demoR1_1011110 : invRung 7 5 20 [1, 0, 1, 1, 1, 1, 0] [1, 0, 1, 1, 1, 1, 0] 1 2 false = ([0, 2, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_1011110 : invRung 7 5 20 [1, 0, 1, 1, 1, 1, 0] [0, 2, 2, 1, 0, 0, 0] 3 1 true = ([1, 0, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_1011110 : fieldCube 7 5 20 [1, 0, 1, 2, 0, 0, 0] = [0, 0, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_1011110 : fieldMul 7 5 20 [0, 0, 2, 0, 0, 2, 1] [1, 0, 1, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011110 : mirrorTrits [0, 0, 2, 0, 0, 2, 1] = [0, 0, 1, 0, 0, 1, 2] := by
  decide

theorem demoInv_1011110 : specInv 7 5 20 [1, 0, 1, 1, 1, 1, 0] = some [0, 0, 1, 0, 0, 1, 2] :=
  specInv_mirror_7 [1, 0, 1, 1, 1, 1, 0] [0, 2, 2, 1, 0, 0, 0] [1, 0, 1, 2, 0, 0, 0] [0, 0, 2, 0, 0, 2, 1] [0, 0, 1, 0, 0, 1, 2] demoR1_1011110 demoR2_1011110 demoC_1011110 demoM_1011110 demoMir_1011110

theorem demoR1_2011110 : invRung 7 5 20 [2, 0, 1, 1, 1, 1, 0] [2, 0, 1, 1, 1, 1, 0] 1 2 false = ([0, 2, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2011110 : invRung 7 5 20 [2, 0, 1, 1, 1, 1, 0] [0, 2, 1, 0, 1, 1, 2] 3 1 true = ([2, 0, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_2011110 : fieldCube 7 5 20 [2, 0, 0, 1, 1, 0, 0] = [0, 1, 1, 1, 0, 2, 1] := by
  decide

theorem demoM_2011110 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 2, 1] [2, 0, 1, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011110 : mirrorTrits [0, 1, 1, 1, 0, 2, 1] = [0, 2, 2, 2, 0, 1, 2] := by
  decide

theorem demoInv_2011110 : specInv 7 5 20 [2, 0, 1, 1, 1, 1, 0] = some [0, 2, 2, 2, 0, 1, 2] :=
  specInv_mirror_7 [2, 0, 1, 1, 1, 1, 0] [0, 2, 1, 0, 1, 1, 2] [2, 0, 0, 1, 1, 0, 0] [0, 1, 1, 1, 0, 2, 1] [0, 2, 2, 2, 0, 1, 2] demoR1_2011110 demoR2_2011110 demoC_2011110 demoM_2011110 demoMir_2011110

theorem demoR1_0111110 : invRung 7 5 20 [0, 1, 1, 1, 1, 1, 0] [0, 1, 1, 1, 1, 1, 0] 1 2 false = ([1, 0, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0111110 : invRung 7 5 20 [0, 1, 1, 1, 1, 1, 0] [1, 0, 1, 1, 1, 1, 2] 3 1 true = ([2, 2, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0111110 : fieldCube 7 5 20 [2, 2, 2, 0, 0, 2, 1] = [1, 0, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_0111110 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 0, 1] [0, 1, 1, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0111110 : specInv 7 5 20 [0, 1, 1, 1, 1, 1, 0] = some [1, 0, 1, 0, 0, 0, 1] :=
  specInv_white_7 [0, 1, 1, 1, 1, 1, 0] [1, 0, 1, 1, 1, 1, 2] [2, 2, 2, 0, 0, 2, 1] [1, 0, 1, 0, 0, 0, 1] demoR1_0111110 demoR2_0111110 demoC_0111110 demoM_0111110

theorem demoR1_1111110 : invRung 7 5 20 [1, 1, 1, 1, 1, 1, 0] [1, 1, 1, 1, 1, 1, 0] 1 2 false = ([0, 1, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_1111110 : invRung 7 5 20 [1, 1, 1, 1, 1, 1, 0] [0, 1, 2, 1, 1, 1, 2] 3 1 true = ([2, 1, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_1111110 : fieldCube 7 5 20 [2, 1, 2, 2, 1, 0, 2] = [1, 0, 0, 1, 2, 2, 2] := by
  decide

theorem demoM_1111110 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 2, 2] [1, 1, 1, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1111110 : specInv 7 5 20 [1, 1, 1, 1, 1, 1, 0] = some [1, 0, 0, 1, 2, 2, 2] :=
  specInv_white_7 [1, 1, 1, 1, 1, 1, 0] [0, 1, 2, 1, 1, 1, 2] [2, 1, 2, 2, 1, 0, 2] [1, 0, 0, 1, 2, 2, 2] demoR1_1111110 demoR2_1111110 demoC_1111110 demoM_1111110

theorem demoR1_2111110 : invRung 7 5 20 [2, 1, 1, 1, 1, 1, 0] [2, 1, 1, 1, 1, 1, 0] 1 2 false = ([2, 0, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_2111110 : invRung 7 5 20 [2, 1, 1, 1, 1, 1, 0] [2, 0, 2, 0, 1, 2, 0] 3 1 true = ([2, 1, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_2111110 : fieldCube 7 5 20 [2, 1, 0, 0, 2, 2, 1] = [1, 2, 1, 1, 0, 2, 1] := by
  decide

theorem demoM_2111110 : fieldMul 7 5 20 [1, 2, 1, 1, 0, 2, 1] [2, 1, 1, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2111110 : mirrorTrits [1, 2, 1, 1, 0, 2, 1] = [2, 1, 2, 2, 0, 1, 2] := by
  decide

theorem demoInv_2111110 : specInv 7 5 20 [2, 1, 1, 1, 1, 1, 0] = some [2, 1, 2, 2, 0, 1, 2] :=
  specInv_mirror_7 [2, 1, 1, 1, 1, 1, 0] [2, 0, 2, 0, 1, 2, 0] [2, 1, 0, 0, 2, 2, 1] [1, 2, 1, 1, 0, 2, 1] [2, 1, 2, 2, 0, 1, 2] demoR1_2111110 demoR2_2111110 demoC_2111110 demoM_2111110 demoMir_2111110

theorem demoR1_0211110 : invRung 7 5 20 [0, 2, 1, 1, 1, 1, 0] [0, 2, 1, 1, 1, 1, 0] 1 2 false = ([1, 1, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0211110 : invRung 7 5 20 [0, 2, 1, 1, 1, 1, 0] [1, 1, 1, 2, 1, 2, 1] 3 1 true = ([2, 1, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0211110 : fieldCube 7 5 20 [2, 1, 0, 0, 2, 0, 1] = [2, 0, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_0211110 : fieldMul 7 5 20 [2, 0, 2, 1, 1, 0, 0] [0, 2, 1, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211110 : mirrorTrits [2, 0, 2, 1, 1, 0, 0] = [1, 0, 1, 2, 2, 0, 0] := by
  decide

theorem demoInv_0211110 : specInv 7 5 20 [0, 2, 1, 1, 1, 1, 0] = some [1, 0, 1, 2, 2, 0, 0] :=
  specInv_mirror_7 [0, 2, 1, 1, 1, 1, 0] [1, 1, 1, 2, 1, 2, 1] [2, 1, 0, 0, 2, 0, 1] [2, 0, 2, 1, 1, 0, 0] [1, 0, 1, 2, 2, 0, 0] demoR1_0211110 demoR2_0211110 demoC_0211110 demoM_0211110 demoMir_0211110

theorem demoR1_1211110 : invRung 7 5 20 [1, 2, 1, 1, 1, 1, 0] [1, 2, 1, 1, 1, 1, 0] 1 2 false = ([0, 0, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1211110 : invRung 7 5 20 [1, 2, 1, 1, 1, 1, 0] [0, 0, 1, 1, 2, 2, 1] 3 1 true = ([0, 2, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_1211110 : fieldCube 7 5 20 [0, 2, 2, 2, 2, 1, 0] = [0, 0, 0, 1, 1, 2, 0] := by
  decide

theorem demoM_1211110 : fieldMul 7 5 20 [0, 0, 0, 1, 1, 2, 0] [1, 2, 1, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1211110 : specInv 7 5 20 [1, 2, 1, 1, 1, 1, 0] = some [0, 0, 0, 1, 1, 2, 0] :=
  specInv_white_7 [1, 2, 1, 1, 1, 1, 0] [0, 0, 1, 1, 2, 2, 1] [0, 2, 2, 2, 2, 1, 0] [0, 0, 0, 1, 1, 2, 0] demoR1_1211110 demoR2_1211110 demoC_1211110 demoM_1211110

theorem demoR1_2211110 : invRung 7 5 20 [2, 2, 1, 1, 1, 1, 0] [2, 2, 1, 1, 1, 1, 0] 1 2 false = ([1, 2, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_2211110 : invRung 7 5 20 [2, 2, 1, 1, 1, 1, 0] [1, 2, 2, 1, 0, 2, 2] 3 1 true = ([1, 2, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_2211110 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 1, 2] = [0, 2, 0, 0, 0, 0, 1] := by
  decide

theorem demoM_2211110 : fieldMul 7 5 20 [0, 2, 0, 0, 0, 0, 1] [2, 2, 1, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2211110 : specInv 7 5 20 [2, 2, 1, 1, 1, 1, 0] = some [0, 2, 0, 0, 0, 0, 1] :=
  specInv_white_7 [2, 2, 1, 1, 1, 1, 0] [1, 2, 2, 1, 0, 2, 2] [1, 2, 1, 1, 2, 1, 2] [0, 2, 0, 0, 0, 0, 1] demoR1_2211110 demoR2_2211110 demoC_2211110 demoM_2211110

theorem demoR1_0021110 : invRung 7 5 20 [0, 0, 2, 1, 1, 1, 0] [0, 0, 2, 1, 1, 1, 0] 1 2 false = ([0, 0, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_0021110 : invRung 7 5 20 [0, 0, 2, 1, 1, 1, 0] [0, 0, 1, 2, 2, 2, 2] 3 1 true = ([0, 1, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_0021110 : fieldCube 7 5 20 [0, 1, 2, 2, 2, 2, 1] = [1, 2, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_0021110 : fieldMul 7 5 20 [1, 2, 0, 1, 0, 1, 0] [0, 0, 2, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0021110 : specInv 7 5 20 [0, 0, 2, 1, 1, 1, 0] = some [1, 2, 0, 1, 0, 1, 0] :=
  specInv_white_7 [0, 0, 2, 1, 1, 1, 0] [0, 0, 1, 2, 2, 2, 2] [0, 1, 2, 2, 2, 2, 1] [1, 2, 0, 1, 0, 1, 0] demoR1_0021110 demoR2_0021110 demoC_0021110 demoM_0021110

theorem demoR1_1021110 : invRung 7 5 20 [1, 0, 2, 1, 1, 1, 0] [1, 0, 2, 1, 1, 1, 0] 1 2 false = ([1, 1, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_1021110 : invRung 7 5 20 [1, 0, 2, 1, 1, 1, 0] [1, 1, 0, 2, 0, 2, 1] 3 1 true = ([0, 0, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_1021110 : fieldCube 7 5 20 [0, 0, 2, 2, 1, 0, 2] = [2, 0, 0, 0, 2, 2, 2] := by
  decide

theorem demoM_1021110 : fieldMul 7 5 20 [2, 0, 0, 0, 2, 2, 2] [1, 0, 2, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1021110 : specInv 7 5 20 [1, 0, 2, 1, 1, 1, 0] = some [2, 0, 0, 0, 2, 2, 2] :=
  specInv_white_7 [1, 0, 2, 1, 1, 1, 0] [1, 1, 0, 2, 0, 2, 1] [0, 0, 2, 2, 1, 0, 2] [2, 0, 0, 0, 2, 2, 2] demoR1_1021110 demoR2_1021110 demoC_1021110 demoM_1021110

theorem demoR1_2021110 : invRung 7 5 20 [2, 0, 2, 1, 1, 1, 0] [2, 0, 2, 1, 1, 1, 0] 1 2 false = ([0, 0, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2021110 : invRung 7 5 20 [2, 0, 2, 1, 1, 1, 0] [0, 0, 2, 1, 0, 0, 2] 3 1 true = ([2, 0, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_2021110 : fieldCube 7 5 20 [2, 0, 0, 2, 2, 2, 1] = [0, 2, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_2021110 : fieldMul 7 5 20 [0, 2, 0, 0, 0, 1, 1] [2, 0, 2, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021110 : mirrorTrits [0, 2, 0, 0, 0, 1, 1] = [0, 1, 0, 0, 0, 2, 2] := by
  decide

theorem demoInv_2021110 : specInv 7 5 20 [2, 0, 2, 1, 1, 1, 0] = some [0, 1, 0, 0, 0, 2, 2] :=
  specInv_mirror_7 [2, 0, 2, 1, 1, 1, 0] [0, 0, 2, 1, 0, 0, 2] [2, 0, 0, 2, 2, 2, 1] [0, 2, 0, 0, 0, 1, 1] [0, 1, 0, 0, 0, 2, 2] demoR1_2021110 demoR2_2021110 demoC_2021110 demoM_2021110 demoMir_2021110

theorem demoR1_0121110 : invRung 7 5 20 [0, 1, 2, 1, 1, 1, 0] [0, 1, 2, 1, 1, 1, 0] 1 2 false = ([1, 0, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_0121110 : invRung 7 5 20 [0, 1, 2, 1, 1, 1, 0] [1, 0, 2, 1, 0, 0, 1] 3 1 true = ([2, 1, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0121110 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 1, 2] = [1, 2, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_0121110 : fieldMul 7 5 20 [1, 2, 0, 2, 0, 0, 1] [0, 1, 2, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0121110 : mirrorTrits [1, 2, 0, 2, 0, 0, 1] = [2, 1, 0, 1, 0, 0, 2] := by
  decide

theorem demoInv_0121110 : specInv 7 5 20 [0, 1, 2, 1, 1, 1, 0] = some [2, 1, 0, 1, 0, 0, 2] :=
  specInv_mirror_7 [0, 1, 2, 1, 1, 1, 0] [1, 0, 2, 1, 0, 0, 1] [2, 1, 1, 1, 2, 1, 2] [1, 2, 0, 2, 0, 0, 1] [2, 1, 0, 1, 0, 0, 2] demoR1_0121110 demoR2_0121110 demoC_0121110 demoM_0121110 demoMir_0121110

theorem demoR1_1121110 : invRung 7 5 20 [1, 1, 2, 1, 1, 1, 0] [1, 1, 2, 1, 1, 1, 0] 1 2 false = ([2, 0, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1121110 : invRung 7 5 20 [1, 1, 2, 1, 1, 1, 0] [2, 0, 1, 1, 1, 2, 1] 3 1 true = ([1, 2, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1121110 : fieldCube 7 5 20 [1, 2, 0, 2, 1, 2, 2] = [2, 2, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_1121110 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 1, 1] [1, 1, 2, 1, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121110 : mirrorTrits [2, 2, 2, 2, 1, 1, 1] = [1, 1, 1, 1, 2, 2, 2] := by
  decide

theorem demoInv_1121110 : specInv 7 5 20 [1, 1, 2, 1, 1, 1, 0] = some [1, 1, 1, 1, 2, 2, 2] :=
  specInv_mirror_7 [1, 1, 2, 1, 1, 1, 0] [2, 0, 1, 1, 1, 2, 1] [1, 2, 0, 2, 1, 2, 2] [2, 2, 2, 2, 1, 1, 1] [1, 1, 1, 1, 2, 2, 2] demoR1_1121110 demoR2_1121110 demoC_1121110 demoM_1121110 demoMir_1121110

theorem demoR1_2121110 : invRung 7 5 20 [2, 1, 2, 1, 1, 1, 0] [2, 1, 2, 1, 1, 1, 0] 1 2 false = ([0, 0, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_2121110 : invRung 7 5 20 [2, 1, 2, 1, 1, 1, 0] [0, 0, 2, 2, 1, 1, 0] 3 1 true = ([2, 1, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2121110 : fieldCube 7 5 20 [2, 1, 1, 2, 0, 1, 0] = [2, 1, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_2121110 : fieldMul 7 5 20 [2, 1, 0, 1, 1, 0, 0] [2, 1, 2, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2121110 : specInv 7 5 20 [2, 1, 2, 1, 1, 1, 0] = some [2, 1, 0, 1, 1, 0, 0] :=
  specInv_white_7 [2, 1, 2, 1, 1, 1, 0] [0, 0, 2, 2, 1, 1, 0] [2, 1, 1, 2, 0, 1, 0] [2, 1, 0, 1, 1, 0, 0] demoR1_2121110 demoR2_2121110 demoC_2121110 demoM_2121110

theorem demoR1_0221110 : invRung 7 5 20 [0, 2, 2, 1, 1, 1, 0] [0, 2, 2, 1, 1, 1, 0] 1 2 false = ([0, 1, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_0221110 : invRung 7 5 20 [0, 2, 2, 1, 1, 1, 0] [0, 1, 0, 2, 2, 0, 2] 3 1 true = ([0, 2, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_0221110 : fieldCube 7 5 20 [0, 2, 0, 0, 2, 2, 0] = [2, 1, 2, 1, 2, 1, 0] := by
  decide

theorem demoM_0221110 : fieldMul 7 5 20 [2, 1, 2, 1, 2, 1, 0] [0, 2, 2, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0221110 : specInv 7 5 20 [0, 2, 2, 1, 1, 1, 0] = some [2, 1, 2, 1, 2, 1, 0] :=
  specInv_white_7 [0, 2, 2, 1, 1, 1, 0] [0, 1, 0, 2, 2, 0, 2] [0, 2, 0, 0, 2, 2, 0] [2, 1, 2, 1, 2, 1, 0] demoR1_0221110 demoR2_0221110 demoC_0221110 demoM_0221110

theorem demoR1_1221110 : invRung 7 5 20 [1, 2, 2, 1, 1, 1, 0] [1, 2, 2, 1, 1, 1, 0] 1 2 false = ([1, 1, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_1221110 : invRung 7 5 20 [1, 2, 2, 1, 1, 1, 0] [1, 1, 2, 0, 2, 0, 1] 3 1 true = ([2, 2, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_1221110 : fieldCube 7 5 20 [2, 2, 2, 1, 1, 0, 2] = [0, 0, 2, 2, 2, 1, 2] := by
  decide

theorem demoM_1221110 : fieldMul 7 5 20 [0, 0, 2, 2, 2, 1, 2] [1, 2, 2, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1221110 : specInv 7 5 20 [1, 2, 2, 1, 1, 1, 0] = some [0, 0, 2, 2, 2, 1, 2] :=
  specInv_white_7 [1, 2, 2, 1, 1, 1, 0] [1, 1, 2, 0, 2, 0, 1] [2, 2, 2, 1, 1, 0, 2] [0, 0, 2, 2, 2, 1, 2] demoR1_1221110 demoR2_1221110 demoC_1221110 demoM_1221110

theorem demoR1_2221110 : invRung 7 5 20 [2, 2, 2, 1, 1, 1, 0] [2, 2, 2, 1, 1, 1, 0] 1 2 false = ([1, 0, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2221110 : invRung 7 5 20 [2, 2, 2, 1, 1, 1, 0] [1, 0, 2, 1, 1, 2, 2] 3 1 true = ([0, 0, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_2221110 : fieldCube 7 5 20 [0, 0, 0, 2, 2, 0, 1] = [2, 0, 1, 0, 1, 2, 0] := by
  decide

theorem demoM_2221110 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 2, 0] [2, 2, 2, 1, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2221110 : specInv 7 5 20 [2, 2, 2, 1, 1, 1, 0] = some [2, 0, 1, 0, 1, 2, 0] :=
  specInv_white_7 [2, 2, 2, 1, 1, 1, 0] [1, 0, 2, 1, 1, 2, 2] [0, 0, 0, 2, 2, 0, 1] [2, 0, 1, 0, 1, 2, 0] demoR1_2221110 demoR2_2221110 demoC_2221110 demoM_2221110

theorem demoR1_0002110 : invRung 7 5 20 [0, 0, 0, 2, 1, 1, 0] [0, 0, 0, 2, 1, 1, 0] 1 2 false = ([2, 0, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_0002110 : invRung 7 5 20 [0, 0, 0, 2, 1, 1, 0] [2, 0, 1, 1, 1, 0, 1] 3 1 true = ([1, 1, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_0002110 : fieldCube 7 5 20 [1, 1, 1, 2, 2, 1, 0] = [1, 0, 0, 0, 1, 2, 2] := by
  decide

theorem demoM_0002110 : fieldMul 7 5 20 [1, 0, 0, 0, 1, 2, 2] [0, 0, 0, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002110 : mirrorTrits [1, 0, 0, 0, 1, 2, 2] = [2, 0, 0, 0, 2, 1, 1] := by
  decide

theorem demoInv_0002110 : specInv 7 5 20 [0, 0, 0, 2, 1, 1, 0] = some [2, 0, 0, 0, 2, 1, 1] :=
  specInv_mirror_7 [0, 0, 0, 2, 1, 1, 0] [2, 0, 1, 1, 1, 0, 1] [1, 1, 1, 2, 2, 1, 0] [1, 0, 0, 0, 1, 2, 2] [2, 0, 0, 0, 2, 1, 1] demoR1_0002110 demoR2_0002110 demoC_0002110 demoM_0002110 demoMir_0002110

theorem demoR1_1002110 : invRung 7 5 20 [1, 0, 0, 2, 1, 1, 0] [1, 0, 0, 2, 1, 1, 0] 1 2 false = ([1, 0, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_1002110 : invRung 7 5 20 [1, 0, 0, 2, 1, 1, 0] [1, 0, 2, 0, 0, 1, 2] 3 1 true = ([1, 2, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_1002110 : fieldCube 7 5 20 [1, 2, 0, 2, 2, 1, 0] = [1, 0, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_1002110 : fieldMul 7 5 20 [1, 0, 0, 1, 1, 2, 1] [1, 0, 0, 2, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1002110 : specInv 7 5 20 [1, 0, 0, 2, 1, 1, 0] = some [1, 0, 0, 1, 1, 2, 1] :=
  specInv_white_7 [1, 0, 0, 2, 1, 1, 0] [1, 0, 2, 0, 0, 1, 2] [1, 2, 0, 2, 2, 1, 0] [1, 0, 0, 1, 1, 2, 1] demoR1_1002110 demoR2_1002110 demoC_1002110 demoM_1002110

theorem demoR1_2002110 : invRung 7 5 20 [2, 0, 0, 2, 1, 1, 0] [2, 0, 0, 2, 1, 1, 0] 1 2 false = ([1, 2, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2002110 : invRung 7 5 20 [2, 0, 0, 2, 1, 1, 0] [1, 2, 1, 2, 2, 0, 0] 3 1 true = ([2, 1, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_2002110 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 1, 2] = [2, 2, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_2002110 : fieldMul 7 5 20 [2, 2, 1, 2, 0, 1, 0] [2, 0, 0, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002110 : mirrorTrits [2, 2, 1, 2, 0, 1, 0] = [1, 1, 2, 1, 0, 2, 0] := by
  decide

theorem demoInv_2002110 : specInv 7 5 20 [2, 0, 0, 2, 1, 1, 0] = some [1, 1, 2, 1, 0, 2, 0] :=
  specInv_mirror_7 [2, 0, 0, 2, 1, 1, 0] [1, 2, 1, 2, 2, 0, 0] [2, 1, 0, 2, 2, 1, 2] [2, 2, 1, 2, 0, 1, 0] [1, 1, 2, 1, 0, 2, 0] demoR1_2002110 demoR2_2002110 demoC_2002110 demoM_2002110 demoMir_2002110

theorem demoR1_0102110 : invRung 7 5 20 [0, 1, 0, 2, 1, 1, 0] [0, 1, 0, 2, 1, 1, 0] 1 2 false = ([2, 2, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_0102110 : invRung 7 5 20 [0, 1, 0, 2, 1, 1, 0] [2, 2, 1, 0, 0, 2, 0] 3 1 true = ([1, 0, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0102110 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 2, 1] = [0, 0, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_0102110 : fieldMul 7 5 20 [0, 0, 1, 1, 0, 0, 2] [0, 1, 0, 2, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0102110 : specInv 7 5 20 [0, 1, 0, 2, 1, 1, 0] = some [0, 0, 1, 1, 0, 0, 2] :=
  specInv_white_7 [0, 1, 0, 2, 1, 1, 0] [2, 2, 1, 0, 0, 2, 0] [1, 0, 0, 0, 0, 2, 1] [0, 0, 1, 1, 0, 0, 2] demoR1_0102110 demoR2_0102110 demoC_0102110 demoM_0102110

theorem demoR1_1102110 : invRung 7 5 20 [1, 1, 0, 2, 1, 1, 0] [1, 1, 0, 2, 1, 1, 0] 1 2 false = ([2, 0, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1102110 : invRung 7 5 20 [1, 1, 0, 2, 1, 1, 0] [2, 0, 0, 1, 2, 2, 1] 3 1 true = ([1, 0, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_1102110 : fieldCube 7 5 20 [1, 0, 0, 0, 1, 0, 2] = [1, 0, 1, 0, 2, 0, 0] := by
  decide

theorem demoM_1102110 : fieldMul 7 5 20 [1, 0, 1, 0, 2, 0, 0] [1, 1, 0, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102110 : mirrorTrits [1, 0, 1, 0, 2, 0, 0] = [2, 0, 2, 0, 1, 0, 0] := by
  decide

theorem demoInv_1102110 : specInv 7 5 20 [1, 1, 0, 2, 1, 1, 0] = some [2, 0, 2, 0, 1, 0, 0] :=
  specInv_mirror_7 [1, 1, 0, 2, 1, 1, 0] [2, 0, 0, 1, 2, 2, 1] [1, 0, 0, 0, 1, 0, 2] [1, 0, 1, 0, 2, 0, 0] [2, 0, 2, 0, 1, 0, 0] demoR1_1102110 demoR2_1102110 demoC_1102110 demoM_1102110 demoMir_1102110

theorem demoR1_2102110 : invRung 7 5 20 [2, 1, 0, 2, 1, 1, 0] [2, 1, 0, 2, 1, 1, 0] 1 2 false = ([2, 2, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2102110 : invRung 7 5 20 [2, 1, 0, 2, 1, 1, 0] [2, 2, 2, 1, 1, 2, 2] 3 1 true = ([2, 1, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_2102110 : fieldCube 7 5 20 [2, 1, 0, 0, 0, 0, 0] = [2, 0, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_2102110 : fieldMul 7 5 20 [2, 0, 0, 1, 0, 0, 0] [2, 1, 0, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2102110 : mirrorTrits [2, 0, 0, 1, 0, 0, 0] = [1, 0, 0, 2, 0, 0, 0] := by
  decide

theorem demoInv_2102110 : specInv 7 5 20 [2, 1, 0, 2, 1, 1, 0] = some [1, 0, 0, 2, 0, 0, 0] :=
  specInv_mirror_7 [2, 1, 0, 2, 1, 1, 0] [2, 2, 2, 1, 1, 2, 2] [2, 1, 0, 0, 0, 0, 0] [2, 0, 0, 1, 0, 0, 0] [1, 0, 0, 2, 0, 0, 0] demoR1_2102110 demoR2_2102110 demoC_2102110 demoM_2102110 demoMir_2102110

theorem demoR1_0202110 : invRung 7 5 20 [0, 2, 0, 2, 1, 1, 0] [0, 2, 0, 2, 1, 1, 0] 1 2 false = ([1, 2, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_0202110 : invRung 7 5 20 [0, 2, 0, 2, 1, 1, 0] [1, 2, 2, 2, 2, 2, 2] 3 1 true = ([0, 0, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_0202110 : fieldCube 7 5 20 [0, 0, 1, 1, 0, 0, 2] = [1, 2, 2, 2, 2, 0, 0] := by
  decide

theorem demoM_0202110 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 0, 0] [0, 2, 0, 2, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0202110 : specInv 7 5 20 [0, 2, 0, 2, 1, 1, 0] = some [1, 2, 2, 2, 2, 0, 0] :=
  specInv_white_7 [0, 2, 0, 2, 1, 1, 0] [1, 2, 2, 2, 2, 2, 2] [0, 0, 1, 1, 0, 0, 2] [1, 2, 2, 2, 2, 0, 0] demoR1_0202110 demoR2_0202110 demoC_0202110 demoM_0202110

theorem demoR1_1202110 : invRung 7 5 20 [1, 2, 0, 2, 1, 1, 0] [1, 2, 0, 2, 1, 1, 0] 1 2 false = ([2, 2, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_1202110 : invRung 7 5 20 [1, 2, 0, 2, 1, 1, 0] [2, 2, 2, 0, 0, 0, 1] 3 1 true = ([1, 0, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_1202110 : fieldCube 7 5 20 [1, 0, 1, 0, 2, 0, 0] = [1, 2, 0, 2, 0, 2, 0] := by
  decide

theorem demoM_1202110 : fieldMul 7 5 20 [1, 2, 0, 2, 0, 2, 0] [1, 2, 0, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202110 : mirrorTrits [1, 2, 0, 2, 0, 2, 0] = [2, 1, 0, 1, 0, 1, 0] := by
  decide

theorem demoInv_1202110 : specInv 7 5 20 [1, 2, 0, 2, 1, 1, 0] = some [2, 1, 0, 1, 0, 1, 0] :=
  specInv_mirror_7 [1, 2, 0, 2, 1, 1, 0] [2, 2, 2, 0, 0, 0, 1] [1, 0, 1, 0, 2, 0, 0] [1, 2, 0, 2, 0, 2, 0] [2, 1, 0, 1, 0, 1, 0] demoR1_1202110 demoR2_1202110 demoC_1202110 demoM_1202110 demoMir_1202110

theorem demoR1_2202110 : invRung 7 5 20 [2, 2, 0, 2, 1, 1, 0] [2, 2, 0, 2, 1, 1, 0] 1 2 false = ([2, 2, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_2202110 : invRung 7 5 20 [2, 2, 0, 2, 1, 1, 0] [2, 2, 1, 2, 1, 0, 0] 3 1 true = ([2, 0, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_2202110 : fieldCube 7 5 20 [2, 0, 0, 1, 0, 0, 0] = [0, 0, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_2202110 : fieldMul 7 5 20 [0, 0, 1, 0, 0, 1, 0] [2, 2, 0, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202110 : mirrorTrits [0, 0, 1, 0, 0, 1, 0] = [0, 0, 2, 0, 0, 2, 0] := by
  decide

theorem demoInv_2202110 : specInv 7 5 20 [2, 2, 0, 2, 1, 1, 0] = some [0, 0, 2, 0, 0, 2, 0] :=
  specInv_mirror_7 [2, 2, 0, 2, 1, 1, 0] [2, 2, 1, 2, 1, 0, 0] [2, 0, 0, 1, 0, 0, 0] [0, 0, 1, 0, 0, 1, 0] [0, 0, 2, 0, 0, 2, 0] demoR1_2202110 demoR2_2202110 demoC_2202110 demoM_2202110 demoMir_2202110

theorem demoR1_0012110 : invRung 7 5 20 [0, 0, 1, 2, 1, 1, 0] [0, 0, 1, 2, 1, 1, 0] 1 2 false = ([1, 2, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_0012110 : invRung 7 5 20 [0, 0, 1, 2, 1, 1, 0] [1, 2, 1, 2, 1, 0, 2] 3 1 true = ([0, 1, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_0012110 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 0, 2] = [1, 2, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_0012110 : fieldMul 7 5 20 [1, 2, 2, 0, 2, 0, 2] [0, 0, 1, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0012110 : mirrorTrits [1, 2, 2, 0, 2, 0, 2] = [2, 1, 1, 0, 1, 0, 1] := by
  decide

theorem demoInv_0012110 : specInv 7 5 20 [0, 0, 1, 2, 1, 1, 0] = some [2, 1, 1, 0, 1, 0, 1] :=
  specInv_mirror_7 [0, 0, 1, 2, 1, 1, 0] [1, 2, 1, 2, 1, 0, 2] [0, 1, 0, 1, 0, 0, 2] [1, 2, 2, 0, 2, 0, 2] [2, 1, 1, 0, 1, 0, 1] demoR1_0012110 demoR2_0012110 demoC_0012110 demoM_0012110 demoMir_0012110

theorem demoR1_1012110 : invRung 7 5 20 [1, 0, 1, 2, 1, 1, 0] [1, 0, 1, 2, 1, 1, 0] 1 2 false = ([0, 0, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_1012110 : invRung 7 5 20 [1, 0, 1, 2, 1, 1, 0] [0, 0, 2, 1, 2, 0, 0] 3 1 true = ([2, 2, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_1012110 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 2, 0] = [0, 1, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_1012110 : fieldMul 7 5 20 [0, 1, 1, 1, 2, 0, 1] [1, 0, 1, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1012110 : mirrorTrits [0, 1, 1, 1, 2, 0, 1] = [0, 2, 2, 2, 1, 0, 2] := by
  decide

theorem demoInv_1012110 : specInv 7 5 20 [1, 0, 1, 2, 1, 1, 0] = some [0, 2, 2, 2, 1, 0, 2] :=
  specInv_mirror_7 [1, 0, 1, 2, 1, 1, 0] [0, 0, 2, 1, 2, 0, 0] [2, 2, 1, 2, 2, 2, 0] [0, 1, 1, 1, 2, 0, 1] [0, 2, 2, 2, 1, 0, 2] demoR1_1012110 demoR2_1012110 demoC_1012110 demoM_1012110 demoMir_1012110

theorem demoR1_2012110 : invRung 7 5 20 [2, 0, 1, 2, 1, 1, 0] [2, 0, 1, 2, 1, 1, 0] 1 2 false = ([0, 2, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_2012110 : invRung 7 5 20 [2, 0, 1, 2, 1, 1, 0] [0, 2, 1, 2, 2, 0, 2] 3 1 true = ([1, 1, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_2012110 : fieldCube 7 5 20 [1, 1, 0, 1, 1, 0, 0] = [2, 1, 1, 2, 0, 2, 1] := by
  decide

theorem demoM_2012110 : fieldMul 7 5 20 [2, 1, 1, 2, 0, 2, 1] [2, 0, 1, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012110 : mirrorTrits [2, 1, 1, 2, 0, 2, 1] = [1, 2, 2, 1, 0, 1, 2] := by
  decide

theorem demoInv_2012110 : specInv 7 5 20 [2, 0, 1, 2, 1, 1, 0] = some [1, 2, 2, 1, 0, 1, 2] :=
  specInv_mirror_7 [2, 0, 1, 2, 1, 1, 0] [0, 2, 1, 2, 2, 0, 2] [1, 1, 0, 1, 1, 0, 0] [2, 1, 1, 2, 0, 2, 1] [1, 2, 2, 1, 0, 1, 2] demoR1_2012110 demoR2_2012110 demoC_2012110 demoM_2012110 demoMir_2012110

theorem demoR1_0112110 : invRung 7 5 20 [0, 1, 1, 2, 1, 1, 0] [0, 1, 1, 2, 1, 1, 0] 1 2 false = ([0, 2, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_0112110 : invRung 7 5 20 [0, 1, 1, 2, 1, 1, 0] [0, 2, 1, 0, 2, 0, 1] 3 1 true = ([0, 2, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_0112110 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 1, 1] = [1, 0, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_0112110 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 0, 1] [0, 1, 1, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112110 : mirrorTrits [1, 0, 0, 1, 2, 0, 1] = [2, 0, 0, 2, 1, 0, 2] := by
  decide

theorem demoInv_0112110 : specInv 7 5 20 [0, 1, 1, 2, 1, 1, 0] = some [2, 0, 0, 2, 1, 0, 2] :=
  specInv_mirror_7 [0, 1, 1, 2, 1, 1, 0] [0, 2, 1, 0, 2, 0, 1] [0, 2, 0, 0, 1, 1, 1] [1, 0, 0, 1, 2, 0, 1] [2, 0, 0, 2, 1, 0, 2] demoR1_0112110 demoR2_0112110 demoC_0112110 demoM_0112110 demoMir_0112110

theorem demoR1_1112110 : invRung 7 5 20 [1, 1, 1, 2, 1, 1, 0] [1, 1, 1, 2, 1, 1, 0] 1 2 false = ([0, 0, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1112110 : invRung 7 5 20 [1, 1, 1, 2, 1, 1, 0] [0, 0, 1, 0, 1, 0, 1] 3 1 true = ([2, 1, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_1112110 : fieldCube 7 5 20 [2, 1, 1, 0, 0, 0, 2] = [2, 2, 1, 0, 2, 2, 0] := by
  decide

theorem demoM_1112110 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 2, 0] [1, 1, 1, 2, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1112110 : specInv 7 5 20 [1, 1, 1, 2, 1, 1, 0] = some [2, 2, 1, 0, 2, 2, 0] :=
  specInv_white_7 [1, 1, 1, 2, 1, 1, 0] [0, 0, 1, 0, 1, 0, 1] [2, 1, 1, 0, 0, 0, 2] [2, 2, 1, 0, 2, 2, 0] demoR1_1112110 demoR2_1112110 demoC_1112110 demoM_1112110

theorem demoR1_2112110 : invRung 7 5 20 [2, 1, 1, 2, 1, 1, 0] [2, 1, 1, 2, 1, 1, 0] 1 2 false = ([0, 1, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_2112110 : invRung 7 5 20 [2, 1, 1, 2, 1, 1, 0] [0, 1, 1, 1, 2, 2, 2] 3 1 true = ([0, 1, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_2112110 : fieldCube 7 5 20 [0, 1, 0, 1, 1, 1, 0] = [2, 2, 2, 2, 1, 0, 0] := by
  decide

theorem demoM_2112110 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 0, 0] [2, 1, 1, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112110 : mirrorTrits [2, 2, 2, 2, 1, 0, 0] = [1, 1, 1, 1, 2, 0, 0] := by
  decide

theorem demoInv_2112110 : specInv 7 5 20 [2, 1, 1, 2, 1, 1, 0] = some [1, 1, 1, 1, 2, 0, 0] :=
  specInv_mirror_7 [2, 1, 1, 2, 1, 1, 0] [0, 1, 1, 1, 2, 2, 2] [0, 1, 0, 1, 1, 1, 0] [2, 2, 2, 2, 1, 0, 0] [1, 1, 1, 1, 2, 0, 0] demoR1_2112110 demoR2_2112110 demoC_2112110 demoM_2112110 demoMir_2112110

theorem demoR1_0212110 : invRung 7 5 20 [0, 2, 1, 2, 1, 1, 0] [0, 2, 1, 2, 1, 1, 0] 1 2 false = ([2, 2, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_0212110 : invRung 7 5 20 [0, 2, 1, 2, 1, 1, 0] [2, 2, 0, 1, 0, 2, 0] 3 1 true = ([0, 0, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0212110 : fieldCube 7 5 20 [0, 0, 0, 1, 0, 0, 1] = [1, 1, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_0212110 : fieldMul 7 5 20 [1, 1, 0, 1, 1, 2, 1] [0, 2, 1, 2, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0212110 : specInv 7 5 20 [0, 2, 1, 2, 1, 1, 0] = some [1, 1, 0, 1, 1, 2, 1] :=
  specInv_white_7 [0, 2, 1, 2, 1, 1, 0] [2, 2, 0, 1, 0, 2, 0] [0, 0, 0, 1, 0, 0, 1] [1, 1, 0, 1, 1, 2, 1] demoR1_0212110 demoR2_0212110 demoC_0212110 demoM_0212110

theorem demoR1_1212110 : invRung 7 5 20 [1, 2, 1, 2, 1, 1, 0] [1, 2, 1, 2, 1, 1, 0] 1 2 false = ([0, 1, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_1212110 : invRung 7 5 20 [1, 2, 1, 2, 1, 1, 0] [0, 1, 2, 0, 2, 1, 0] 3 1 true = ([0, 2, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1212110 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 0, 0] = [0, 1, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_1212110 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 1, 1] [1, 2, 1, 2, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1212110 : specInv 7 5 20 [1, 2, 1, 2, 1, 1, 0] = some [0, 1, 0, 0, 0, 1, 1] :=
  specInv_white_7 [1, 2, 1, 2, 1, 1, 0] [0, 1, 2, 0, 2, 1, 0] [0, 2, 0, 0, 1, 0, 0] [0, 1, 0, 0, 0, 1, 1] demoR1_1212110 demoR2_1212110 demoC_1212110 demoM_1212110

theorem demoR1_2212110 : invRung 7 5 20 [2, 2, 1, 2, 1, 1, 0] [2, 2, 1, 2, 1, 1, 0] 1 2 false = ([0, 2, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_2212110 : invRung 7 5 20 [2, 2, 1, 2, 1, 1, 0] [0, 2, 0, 2, 0, 1, 1] 3 1 true = ([0, 2, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_2212110 : fieldCube 7 5 20 [0, 2, 2, 1, 2, 0, 1] = [1, 0, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_2212110 : fieldMul 7 5 20 [1, 0, 0, 2, 1, 1, 2] [2, 2, 1, 2, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2212110 : specInv 7 5 20 [2, 2, 1, 2, 1, 1, 0] = some [1, 0, 0, 2, 1, 1, 2] :=
  specInv_white_7 [2, 2, 1, 2, 1, 1, 0] [0, 2, 0, 2, 0, 1, 1] [0, 2, 2, 1, 2, 0, 1] [1, 0, 0, 2, 1, 1, 2] demoR1_2212110 demoR2_2212110 demoC_2212110 demoM_2212110

theorem demoR1_0022110 : invRung 7 5 20 [0, 0, 2, 2, 1, 1, 0] [0, 0, 2, 2, 1, 1, 0] 1 2 false = ([2, 2, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_0022110 : invRung 7 5 20 [0, 0, 2, 2, 1, 1, 0] [2, 2, 2, 2, 1, 2, 2] 3 1 true = ([1, 2, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_0022110 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 1, 2] = [1, 2, 1, 0, 0, 1, 2] := by
  decide

theorem demoM_0022110 : fieldMul 7 5 20 [1, 2, 1, 0, 0, 1, 2] [0, 0, 2, 2, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0022110 : specInv 7 5 20 [0, 0, 2, 2, 1, 1, 0] = some [1, 2, 1, 0, 0, 1, 2] :=
  specInv_white_7 [0, 0, 2, 2, 1, 1, 0] [2, 2, 2, 2, 1, 2, 2] [1, 2, 2, 2, 2, 1, 2] [1, 2, 1, 0, 0, 1, 2] demoR1_0022110 demoR2_0022110 demoC_0022110 demoM_0022110

theorem demoR1_1022110 : invRung 7 5 20 [1, 0, 2, 2, 1, 1, 0] [1, 0, 2, 2, 1, 1, 0] 1 2 false = ([0, 1, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_1022110 : invRung 7 5 20 [1, 0, 2, 2, 1, 1, 0] [0, 1, 1, 1, 1, 1, 2] 3 1 true = ([0, 1, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_1022110 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 0, 2] = [0, 0, 1, 1, 2, 0, 2] := by
  decide

theorem demoM_1022110 : fieldMul 7 5 20 [0, 0, 1, 1, 2, 0, 2] [1, 0, 2, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1022110 : mirrorTrits [0, 0, 1, 1, 2, 0, 2] = [0, 0, 2, 2, 1, 0, 1] := by
  decide

theorem demoInv_1022110 : specInv 7 5 20 [1, 0, 2, 2, 1, 1, 0] = some [0, 0, 2, 2, 1, 0, 1] :=
  specInv_mirror_7 [1, 0, 2, 2, 1, 1, 0] [0, 1, 1, 1, 1, 1, 2] [0, 1, 2, 0, 1, 0, 2] [0, 0, 1, 1, 2, 0, 2] [0, 0, 2, 2, 1, 0, 1] demoR1_1022110 demoR2_1022110 demoC_1022110 demoM_1022110 demoMir_1022110

theorem demoR1_2022110 : invRung 7 5 20 [2, 0, 2, 2, 1, 1, 0] [2, 0, 2, 2, 1, 1, 0] 1 2 false = ([2, 0, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_2022110 : invRung 7 5 20 [2, 0, 2, 2, 1, 1, 0] [2, 0, 1, 1, 2, 2, 1] 3 1 true = ([1, 0, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_2022110 : fieldCube 7 5 20 [1, 0, 2, 2, 0, 2, 0] = [2, 2, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_2022110 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 1, 0] [2, 0, 2, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022110 : mirrorTrits [2, 2, 1, 0, 2, 1, 0] = [1, 1, 2, 0, 1, 2, 0] := by
  decide

theorem demoInv_2022110 : specInv 7 5 20 [2, 0, 2, 2, 1, 1, 0] = some [1, 1, 2, 0, 1, 2, 0] :=
  specInv_mirror_7 [2, 0, 2, 2, 1, 1, 0] [2, 0, 1, 1, 2, 2, 1] [1, 0, 2, 2, 0, 2, 0] [2, 2, 1, 0, 2, 1, 0] [1, 1, 2, 0, 1, 2, 0] demoR1_2022110 demoR2_2022110 demoC_2022110 demoM_2022110 demoMir_2022110

theorem demoR1_0122110 : invRung 7 5 20 [0, 1, 2, 2, 1, 1, 0] [0, 1, 2, 2, 1, 1, 0] 1 2 false = ([0, 2, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_0122110 : invRung 7 5 20 [0, 1, 2, 2, 1, 1, 0] [0, 2, 1, 1, 0, 2, 0] 3 1 true = ([1, 0, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_0122110 : fieldCube 7 5 20 [1, 0, 1, 0, 1, 1, 1] = [2, 0, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_0122110 : fieldMul 7 5 20 [2, 0, 0, 2, 2, 0, 2] [0, 1, 2, 2, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0122110 : specInv 7 5 20 [0, 1, 2, 2, 1, 1, 0] = some [2, 0, 0, 2, 2, 0, 2] :=
  specInv_white_7 [0, 1, 2, 2, 1, 1, 0] [0, 2, 1, 1, 0, 2, 0] [1, 0, 1, 0, 1, 1, 1] [2, 0, 0, 2, 2, 0, 2] demoR1_0122110 demoR2_0122110 demoC_0122110 demoM_0122110

theorem demoR1_1122110 : invRung 7 5 20 [1, 1, 2, 2, 1, 1, 0] [1, 1, 2, 2, 1, 1, 0] 1 2 false = ([2, 0, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1122110 : invRung 7 5 20 [1, 1, 2, 2, 1, 1, 0] [2, 0, 0, 0, 2, 2, 1] 3 1 true = ([2, 0, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_1122110 : fieldCube 7 5 20 [2, 0, 2, 0, 2, 0, 2] = [2, 1, 1, 1, 2, 1, 0] := by
  decide

theorem demoM_1122110 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 1, 0] [1, 1, 2, 2, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1122110 : specInv 7 5 20 [1, 1, 2, 2, 1, 1, 0] = some [2, 1, 1, 1, 2, 1, 0] :=
  specInv_white_7 [1, 1, 2, 2, 1, 1, 0] [2, 0, 0, 0, 2, 2, 1] [2, 0, 2, 0, 2, 0, 2] [2, 1, 1, 1, 2, 1, 0] demoR1_1122110 demoR2_1122110 demoC_1122110 demoM_1122110

theorem demoR1_2122110 : invRung 7 5 20 [2, 1, 2, 2, 1, 1, 0] [2, 1, 2, 2, 1, 1, 0] 1 2 false = ([1, 0, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2122110 : invRung 7 5 20 [2, 1, 2, 2, 1, 1, 0] [1, 0, 2, 2, 2, 0, 1] 3 1 true = ([2, 2, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_2122110 : fieldCube 7 5 20 [2, 2, 0, 0, 0, 0, 2] = [2, 2, 1, 1, 2, 2, 2] := by
  decide

theorem demoM_2122110 : fieldMul 7 5 20 [2, 2, 1, 1, 2, 2, 2] [2, 1, 2, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122110 : mirrorTrits [2, 2, 1, 1, 2, 2, 2] = [1, 1, 2, 2, 1, 1, 1] := by
  decide

theorem demoInv_2122110 : specInv 7 5 20 [2, 1, 2, 2, 1, 1, 0] = some [1, 1, 2, 2, 1, 1, 1] :=
  specInv_mirror_7 [2, 1, 2, 2, 1, 1, 0] [1, 0, 2, 2, 2, 0, 1] [2, 2, 0, 0, 0, 0, 2] [2, 2, 1, 1, 2, 2, 2] [1, 1, 2, 2, 1, 1, 1] demoR1_2122110 demoR2_2122110 demoC_2122110 demoM_2122110 demoMir_2122110

theorem demoR1_0222110 : invRung 7 5 20 [0, 2, 2, 2, 1, 1, 0] [0, 2, 2, 2, 1, 1, 0] 1 2 false = ([2, 1, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_0222110 : invRung 7 5 20 [0, 2, 2, 2, 1, 1, 0] [2, 1, 0, 0, 2, 2, 1] 3 1 true = ([0, 1, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0222110 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 0, 0] = [1, 0, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_0222110 : fieldMul 7 5 20 [1, 0, 1, 1, 0, 1, 1] [0, 2, 2, 2, 1, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0222110 : specInv 7 5 20 [0, 2, 2, 2, 1, 1, 0] = some [1, 0, 1, 1, 0, 1, 1] :=
  specInv_white_7 [0, 2, 2, 2, 1, 1, 0] [2, 1, 0, 0, 2, 2, 1] [0, 1, 1, 1, 0, 0, 0] [1, 0, 1, 1, 0, 1, 1] demoR1_0222110 demoR2_0222110 demoC_0222110 demoM_0222110

theorem demoR1_1222110 : invRung 7 5 20 [1, 2, 2, 2, 1, 1, 0] [1, 2, 2, 2, 1, 1, 0] 1 2 false = ([2, 2, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1222110 : invRung 7 5 20 [1, 2, 2, 2, 1, 1, 0] [2, 2, 2, 0, 2, 2, 1] 3 1 true = ([2, 1, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_1222110 : fieldCube 7 5 20 [2, 1, 0, 2, 0, 0, 2] = [1, 2, 0, 0, 2, 1, 2] := by
  decide

theorem demoM_1222110 : fieldMul 7 5 20 [1, 2, 0, 0, 2, 1, 2] [1, 2, 2, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222110 : mirrorTrits [1, 2, 0, 0, 2, 1, 2] = [2, 1, 0, 0, 1, 2, 1] := by
  decide

theorem demoInv_1222110 : specInv 7 5 20 [1, 2, 2, 2, 1, 1, 0] = some [2, 1, 0, 0, 1, 2, 1] :=
  specInv_mirror_7 [1, 2, 2, 2, 1, 1, 0] [2, 2, 2, 0, 2, 2, 1] [2, 1, 0, 2, 0, 0, 2] [1, 2, 0, 0, 2, 1, 2] [2, 1, 0, 0, 1, 2, 1] demoR1_1222110 demoR2_1222110 demoC_1222110 demoM_1222110 demoMir_1222110

theorem demoR1_2222110 : invRung 7 5 20 [2, 2, 2, 2, 1, 1, 0] [2, 2, 2, 2, 1, 1, 0] 1 2 false = ([1, 1, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_2222110 : invRung 7 5 20 [2, 2, 2, 2, 1, 1, 0] [1, 1, 0, 2, 0, 2, 0] 3 1 true = ([2, 0, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_2222110 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 2, 0] = [0, 2, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_2222110 : fieldMul 7 5 20 [0, 2, 1, 0, 2, 1, 2] [2, 2, 2, 2, 1, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222110 : mirrorTrits [0, 2, 1, 0, 2, 1, 2] = [0, 1, 2, 0, 1, 2, 1] := by
  decide

theorem demoInv_2222110 : specInv 7 5 20 [2, 2, 2, 2, 1, 1, 0] = some [0, 1, 2, 0, 1, 2, 1] :=
  specInv_mirror_7 [2, 2, 2, 2, 1, 1, 0] [1, 1, 0, 2, 0, 2, 0] [2, 0, 1, 2, 0, 2, 0] [0, 2, 1, 0, 2, 1, 2] [0, 1, 2, 0, 1, 2, 1] demoR1_2222110 demoR2_2222110 demoC_2222110 demoM_2222110 demoMir_2222110

theorem demoR1_0000210 : invRung 7 5 20 [0, 0, 0, 0, 2, 1, 0] [0, 0, 0, 0, 2, 1, 0] 1 2 false = ([0, 2, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_0000210 : invRung 7 5 20 [0, 0, 0, 0, 2, 1, 0] [0, 2, 0, 1, 0, 1, 1] 3 1 true = ([0, 0, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0000210 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 1, 2] = [0, 1, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_0000210 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 0, 0] [0, 0, 0, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0000210 : specInv 7 5 20 [0, 0, 0, 0, 2, 1, 0] = some [0, 1, 1, 0, 0, 0, 0] :=
  specInv_white_7 [0, 0, 0, 0, 2, 1, 0] [0, 2, 0, 1, 0, 1, 1] [0, 0, 1, 2, 1, 1, 2] [0, 1, 1, 0, 0, 0, 0] demoR1_0000210 demoR2_0000210 demoC_0000210 demoM_0000210

theorem demoR1_1000210 : invRung 7 5 20 [1, 0, 0, 0, 2, 1, 0] [1, 0, 0, 0, 2, 1, 0] 1 2 false = ([1, 1, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_1000210 : invRung 7 5 20 [1, 0, 0, 0, 2, 1, 0] [1, 1, 0, 1, 2, 2, 0] 3 1 true = ([0, 0, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_1000210 : fieldCube 7 5 20 [0, 0, 0, 2, 0, 0, 1] = [2, 1, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_1000210 : fieldMul 7 5 20 [2, 1, 1, 1, 1, 0, 1] [1, 0, 0, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1000210 : specInv 7 5 20 [1, 0, 0, 0, 2, 1, 0] = some [2, 1, 1, 1, 1, 0, 1] :=
  specInv_white_7 [1, 0, 0, 0, 2, 1, 0] [1, 1, 0, 1, 2, 2, 0] [0, 0, 0, 2, 0, 0, 1] [2, 1, 1, 1, 1, 0, 1] demoR1_1000210 demoR2_1000210 demoC_1000210 demoM_1000210

theorem demoR1_2000210 : invRung 7 5 20 [2, 0, 0, 0, 2, 1, 0] [2, 0, 0, 0, 2, 1, 0] 1 2 false = ([1, 1, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_2000210 : invRung 7 5 20 [2, 0, 0, 0, 2, 1, 0] [1, 1, 1, 0, 0, 1, 1] 3 1 true = ([2, 1, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_2000210 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 2, 1] = [2, 2, 2, 1, 0, 0, 2] := by
  decide

theorem demoM_2000210 : fieldMul 7 5 20 [2, 2, 2, 1, 0, 0, 2] [2, 0, 0, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2000210 : specInv 7 5 20 [2, 0, 0, 0, 2, 1, 0] = some [2, 2, 2, 1, 0, 0, 2] :=
  specInv_white_7 [2, 0, 0, 0, 2, 1, 0] [1, 1, 1, 0, 0, 1, 1] [2, 1, 1, 1, 2, 2, 1] [2, 2, 2, 1, 0, 0, 2] demoR1_2000210 demoR2_2000210 demoC_2000210 demoM_2000210

theorem demoR1_0100210 : invRung 7 5 20 [0, 1, 0, 0, 2, 1, 0] [0, 1, 0, 0, 2, 1, 0] 1 2 false = ([2, 1, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0100210 : invRung 7 5 20 [0, 1, 0, 0, 2, 1, 0] [2, 1, 2, 1, 0, 0, 0] 3 1 true = ([1, 0, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_0100210 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 0, 1] = [2, 2, 0, 2, 1, 0, 0] := by
  decide

theorem demoM_0100210 : fieldMul 7 5 20 [2, 2, 0, 2, 1, 0, 0] [0, 1, 0, 0, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100210 : mirrorTrits [2, 2, 0, 2, 1, 0, 0] = [1, 1, 0, 1, 2, 0, 0] := by
  decide

theorem demoInv_0100210 : specInv 7 5 20 [0, 1, 0, 0, 2, 1, 0] = some [1, 1, 0, 1, 2, 0, 0] :=
  specInv_mirror_7 [0, 1, 0, 0, 2, 1, 0] [2, 1, 2, 1, 0, 0, 0] [1, 0, 1, 1, 1, 0, 1] [2, 2, 0, 2, 1, 0, 0] [1, 1, 0, 1, 2, 0, 0] demoR1_0100210 demoR2_0100210 demoC_0100210 demoM_0100210 demoMir_0100210

theorem demoR1_1100210 : invRung 7 5 20 [1, 1, 0, 0, 2, 1, 0] [1, 1, 0, 0, 2, 1, 0] 1 2 false = ([0, 1, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_1100210 : invRung 7 5 20 [1, 1, 0, 0, 2, 1, 0] [0, 1, 2, 0, 2, 2, 2] 3 1 true = ([0, 1, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_1100210 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 2, 0] = [2, 2, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_1100210 : fieldMul 7 5 20 [2, 2, 2, 1, 2, 2, 2] [1, 1, 0, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1100210 : specInv 7 5 20 [1, 1, 0, 0, 2, 1, 0] = some [2, 2, 2, 1, 2, 2, 2] :=
  specInv_white_7 [1, 1, 0, 0, 2, 1, 0] [0, 1, 2, 0, 2, 2, 2] [0, 1, 1, 0, 0, 2, 0] [2, 2, 2, 1, 2, 2, 2] demoR1_1100210 demoR2_1100210 demoC_1100210 demoM_1100210

theorem demoR1_2100210 : invRung 7 5 20 [2, 1, 0, 0, 2, 1, 0] [2, 1, 0, 0, 2, 1, 0] 1 2 false = ([2, 1, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2100210 : invRung 7 5 20 [2, 1, 0, 0, 2, 1, 0] [2, 1, 2, 0, 0, 1, 0] 3 1 true = ([2, 0, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_2100210 : fieldCube 7 5 20 [2, 0, 1, 1, 0, 2, 2] = [2, 1, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_2100210 : fieldMul 7 5 20 [2, 1, 1, 2, 1, 2, 1] [2, 1, 0, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2100210 : specInv 7 5 20 [2, 1, 0, 0, 2, 1, 0] = some [2, 1, 1, 2, 1, 2, 1] :=
  specInv_white_7 [2, 1, 0, 0, 2, 1, 0] [2, 1, 2, 0, 0, 1, 0] [2, 0, 1, 1, 0, 2, 2] [2, 1, 1, 2, 1, 2, 1] demoR1_2100210 demoR2_2100210 demoC_2100210 demoM_2100210

theorem demoR1_0200210 : invRung 7 5 20 [0, 2, 0, 0, 2, 1, 0] [0, 2, 0, 0, 2, 1, 0] 1 2 false = ([0, 0, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_0200210 : invRung 7 5 20 [0, 2, 0, 0, 2, 1, 0] [0, 0, 0, 0, 0, 0, 1] 3 1 true = ([2, 1, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0200210 : fieldCube 7 5 20 [2, 1, 2, 0, 0, 1, 1] = [0, 2, 0, 2, 2, 2, 2] := by
  decide

theorem demoM_0200210 : fieldMul 7 5 20 [0, 2, 0, 2, 2, 2, 2] [0, 2, 0, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0200210 : specInv 7 5 20 [0, 2, 0, 0, 2, 1, 0] = some [0, 2, 0, 2, 2, 2, 2] :=
  specInv_white_7 [0, 2, 0, 0, 2, 1, 0] [0, 0, 0, 0, 0, 0, 1] [2, 1, 2, 0, 0, 1, 1] [0, 2, 0, 2, 2, 2, 2] demoR1_0200210 demoR2_0200210 demoC_0200210 demoM_0200210

theorem demoR1_1200210 : invRung 7 5 20 [1, 2, 0, 0, 2, 1, 0] [1, 2, 0, 0, 2, 1, 0] 1 2 false = ([1, 2, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_1200210 : invRung 7 5 20 [1, 2, 0, 0, 2, 1, 0] [1, 2, 0, 2, 1, 2, 1] 3 1 true = ([0, 2, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1200210 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 2, 1] = [0, 1, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_1200210 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 2, 1] [1, 2, 0, 0, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200210 : mirrorTrits [0, 1, 2, 1, 0, 2, 1] = [0, 2, 1, 2, 0, 1, 2] := by
  decide

theorem demoInv_1200210 : specInv 7 5 20 [1, 2, 0, 0, 2, 1, 0] = some [0, 2, 1, 2, 0, 1, 2] :=
  specInv_mirror_7 [1, 2, 0, 0, 2, 1, 0] [1, 2, 0, 2, 1, 2, 1] [0, 2, 1, 1, 1, 2, 1] [0, 1, 2, 1, 0, 2, 1] [0, 2, 1, 2, 0, 1, 2] demoR1_1200210 demoR2_1200210 demoC_1200210 demoM_1200210 demoMir_1200210

theorem demoR1_2200210 : invRung 7 5 20 [2, 2, 0, 0, 2, 1, 0] [2, 2, 0, 0, 2, 1, 0] 1 2 false = ([2, 0, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_2200210 : invRung 7 5 20 [2, 2, 0, 0, 2, 1, 0] [2, 0, 2, 1, 1, 0, 0] 3 1 true = ([2, 0, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_2200210 : fieldCube 7 5 20 [2, 0, 0, 1, 1, 1, 0] = [1, 2, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_2200210 : fieldMul 7 5 20 [1, 2, 2, 1, 1, 0, 0] [2, 2, 0, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2200210 : specInv 7 5 20 [2, 2, 0, 0, 2, 1, 0] = some [1, 2, 2, 1, 1, 0, 0] :=
  specInv_white_7 [2, 2, 0, 0, 2, 1, 0] [2, 0, 2, 1, 1, 0, 0] [2, 0, 0, 1, 1, 1, 0] [1, 2, 2, 1, 1, 0, 0] demoR1_2200210 demoR2_2200210 demoC_2200210 demoM_2200210

theorem demoR1_0010210 : invRung 7 5 20 [0, 0, 1, 0, 2, 1, 0] [0, 0, 1, 0, 2, 1, 0] 1 2 false = ([0, 1, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_0010210 : invRung 7 5 20 [0, 0, 1, 0, 2, 1, 0] [0, 1, 1, 0, 2, 1, 1] 3 1 true = ([2, 0, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0010210 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 1, 2] = [2, 1, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_0010210 : fieldMul 7 5 20 [2, 1, 1, 0, 0, 0, 1] [0, 0, 1, 0, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010210 : mirrorTrits [2, 1, 1, 0, 0, 0, 1] = [1, 2, 2, 0, 0, 0, 2] := by
  decide

theorem demoInv_0010210 : specInv 7 5 20 [0, 0, 1, 0, 2, 1, 0] = some [1, 2, 2, 0, 0, 0, 2] :=
  specInv_mirror_7 [0, 0, 1, 0, 2, 1, 0] [0, 1, 1, 0, 2, 1, 1] [2, 0, 2, 2, 1, 1, 2] [2, 1, 1, 0, 0, 0, 1] [1, 2, 2, 0, 0, 0, 2] demoR1_0010210 demoR2_0010210 demoC_0010210 demoM_0010210 demoMir_0010210

theorem demoR1_1010210 : invRung 7 5 20 [1, 0, 1, 0, 2, 1, 0] [1, 0, 1, 0, 2, 1, 0] 1 2 false = ([0, 1, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_1010210 : invRung 7 5 20 [1, 0, 1, 0, 2, 1, 0] [0, 1, 1, 2, 1, 0, 0] 3 1 true = ([2, 1, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_1010210 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 1, 0] = [1, 1, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_1010210 : fieldMul 7 5 20 [1, 1, 2, 1, 1, 2, 1] [1, 0, 1, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1010210 : specInv 7 5 20 [1, 0, 1, 0, 2, 1, 0] = some [1, 1, 2, 1, 1, 2, 1] :=
  specInv_white_7 [1, 0, 1, 0, 2, 1, 0] [0, 1, 1, 2, 1, 0, 0] [2, 1, 2, 1, 0, 1, 0] [1, 1, 2, 1, 1, 2, 1] demoR1_1010210 demoR2_1010210 demoC_1010210 demoM_1010210

theorem demoR1_2010210 : invRung 7 5 20 [2, 0, 1, 0, 2, 1, 0] [2, 0, 1, 0, 2, 1, 0] 1 2 false = ([2, 1, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_2010210 : invRung 7 5 20 [2, 0, 1, 0, 2, 1, 0] [2, 1, 2, 2, 1, 2, 2] 3 1 true = ([0, 0, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_2010210 : fieldCube 7 5 20 [0, 0, 1, 1, 2, 0, 0] = [1, 2, 1, 2, 0, 0, 0] := by
  decide

theorem demoM_2010210 : fieldMul 7 5 20 [1, 2, 1, 2, 0, 0, 0] [2, 0, 1, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2010210 : specInv 7 5 20 [2, 0, 1, 0, 2, 1, 0] = some [1, 2, 1, 2, 0, 0, 0] :=
  specInv_white_7 [2, 0, 1, 0, 2, 1, 0] [2, 1, 2, 2, 1, 2, 2] [0, 0, 1, 1, 2, 0, 0] [1, 2, 1, 2, 0, 0, 0] demoR1_2010210 demoR2_2010210 demoC_2010210 demoM_2010210

theorem demoR1_0110210 : invRung 7 5 20 [0, 1, 1, 0, 2, 1, 0] [0, 1, 1, 0, 2, 1, 0] 1 2 false = ([2, 0, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_0110210 : invRung 7 5 20 [0, 1, 1, 0, 2, 1, 0] [2, 0, 0, 1, 2, 2, 0] 3 1 true = ([1, 1, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0110210 : fieldCube 7 5 20 [1, 1, 1, 1, 2, 0, 1] = [2, 0, 0, 1, 1, 1, 1] := by
  decide

theorem demoM_0110210 : fieldMul 7 5 20 [2, 0, 0, 1, 1, 1, 1] [0, 1, 1, 0, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110210 : mirrorTrits [2, 0, 0, 1, 1, 1, 1] = [1, 0, 0, 2, 2, 2, 2] := by
  decide

theorem demoInv_0110210 : specInv 7 5 20 [0, 1, 1, 0, 2, 1, 0] = some [1, 0, 0, 2, 2, 2, 2] :=
  specInv_mirror_7 [0, 1, 1, 0, 2, 1, 0] [2, 0, 0, 1, 2, 2, 0] [1, 1, 1, 1, 2, 0, 1] [2, 0, 0, 1, 1, 1, 1] [1, 0, 0, 2, 2, 2, 2] demoR1_0110210 demoR2_0110210 demoC_0110210 demoM_0110210 demoMir_0110210

theorem demoR1_1110210 : invRung 7 5 20 [1, 1, 1, 0, 2, 1, 0] [1, 1, 1, 0, 2, 1, 0] 1 2 false = ([2, 0, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_1110210 : invRung 7 5 20 [1, 1, 1, 0, 2, 1, 0] [2, 0, 1, 1, 2, 0, 1] 3 1 true = ([0, 0, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1110210 : fieldCube 7 5 20 [0, 0, 2, 1, 2, 2, 0] = [0, 1, 0, 2, 2, 2, 2] := by
  decide

theorem demoM_1110210 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 2, 2] [1, 1, 1, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1110210 : specInv 7 5 20 [1, 1, 1, 0, 2, 1, 0] = some [0, 1, 0, 2, 2, 2, 2] :=
  specInv_white_7 [1, 1, 1, 0, 2, 1, 0] [2, 0, 1, 1, 2, 0, 1] [0, 0, 2, 1, 2, 2, 0] [0, 1, 0, 2, 2, 2, 2] demoR1_1110210 demoR2_1110210 demoC_1110210 demoM_1110210

theorem demoR1_2110210 : invRung 7 5 20 [2, 1, 1, 0, 2, 1, 0] [2, 1, 1, 0, 2, 1, 0] 1 2 false = ([0, 2, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2110210 : invRung 7 5 20 [2, 1, 1, 0, 2, 1, 0] [0, 2, 2, 1, 0, 0, 2] 3 1 true = ([2, 2, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_2110210 : fieldCube 7 5 20 [2, 2, 2, 1, 0, 1, 2] = [1, 0, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_2110210 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 1, 0] [2, 1, 1, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2110210 : specInv 7 5 20 [2, 1, 1, 0, 2, 1, 0] = some [1, 0, 0, 1, 0, 1, 0] :=
  specInv_white_7 [2, 1, 1, 0, 2, 1, 0] [0, 2, 2, 1, 0, 0, 2] [2, 2, 2, 1, 0, 1, 2] [1, 0, 0, 1, 0, 1, 0] demoR1_2110210 demoR2_2110210 demoC_2110210 demoM_2110210

theorem demoR1_0210210 : invRung 7 5 20 [0, 2, 1, 0, 2, 1, 0] [0, 2, 1, 0, 2, 1, 0] 1 2 false = ([1, 1, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_0210210 : invRung 7 5 20 [0, 2, 1, 0, 2, 1, 0] [1, 1, 2, 1, 2, 2, 1] 3 1 true = ([1, 2, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0210210 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 0, 1] = [1, 0, 2, 2, 1, 0, 1] := by
  decide

theorem demoM_0210210 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 0, 1] [0, 2, 1, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0210210 : specInv 7 5 20 [0, 2, 1, 0, 2, 1, 0] = some [1, 0, 2, 2, 1, 0, 1] :=
  specInv_white_7 [0, 2, 1, 0, 2, 1, 0] [1, 1, 2, 1, 2, 2, 1] [1, 2, 1, 0, 2, 0, 1] [1, 0, 2, 2, 1, 0, 1] demoR1_0210210 demoR2_0210210 demoC_0210210 demoM_0210210

theorem demoR1_1210210 : invRung 7 5 20 [1, 2, 1, 0, 2, 1, 0] [1, 2, 1, 0, 2, 1, 0] 1 2 false = ([1, 2, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_1210210 : invRung 7 5 20 [1, 2, 1, 0, 2, 1, 0] [1, 2, 1, 0, 2, 1, 2] 3 1 true = ([0, 2, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_1210210 : fieldCube 7 5 20 [0, 2, 2, 2, 2, 1, 2] = [0, 2, 1, 0, 0, 1, 2] := by
  decide

theorem demoM_1210210 : fieldMul 7 5 20 [0, 2, 1, 0, 0, 1, 2] [1, 2, 1, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1210210 : specInv 7 5 20 [1, 2, 1, 0, 2, 1, 0] = some [0, 2, 1, 0, 0, 1, 2] :=
  specInv_white_7 [1, 2, 1, 0, 2, 1, 0] [1, 2, 1, 0, 2, 1, 2] [0, 2, 2, 2, 2, 1, 2] [0, 2, 1, 0, 0, 1, 2] demoR1_1210210 demoR2_1210210 demoC_1210210 demoM_1210210

theorem demoR1_2210210 : invRung 7 5 20 [2, 2, 1, 0, 2, 1, 0] [2, 2, 1, 0, 2, 1, 0] 1 2 false = ([1, 1, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_2210210 : invRung 7 5 20 [2, 2, 1, 0, 2, 1, 0] [1, 1, 2, 1, 0, 1, 0] 3 1 true = ([0, 0, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_2210210 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 2, 0] = [1, 0, 1, 1, 2, 2, 0] := by
  decide

theorem demoM_2210210 : fieldMul 7 5 20 [1, 0, 1, 1, 2, 2, 0] [2, 2, 1, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2210210 : specInv 7 5 20 [2, 2, 1, 0, 2, 1, 0] = some [1, 0, 1, 1, 2, 2, 0] :=
  specInv_white_7 [2, 2, 1, 0, 2, 1, 0] [1, 1, 2, 1, 0, 1, 0] [0, 0, 1, 2, 1, 2, 0] [1, 0, 1, 1, 2, 2, 0] demoR1_2210210 demoR2_2210210 demoC_2210210 demoM_2210210

theorem demoR1_0020210 : invRung 7 5 20 [0, 0, 2, 0, 2, 1, 0] [0, 0, 2, 0, 2, 1, 0] 1 2 false = ([0, 0, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0020210 : invRung 7 5 20 [0, 0, 2, 0, 2, 1, 0] [0, 0, 1, 2, 2, 2, 1] 3 1 true = ([1, 1, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_0020210 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 1, 0] = [2, 2, 1, 2, 1, 2, 0] := by
  decide

theorem demoM_0020210 : fieldMul 7 5 20 [2, 2, 1, 2, 1, 2, 0] [0, 0, 2, 0, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020210 : mirrorTrits [2, 2, 1, 2, 1, 2, 0] = [1, 1, 2, 1, 2, 1, 0] := by
  decide

theorem demoInv_0020210 : specInv 7 5 20 [0, 0, 2, 0, 2, 1, 0] = some [1, 1, 2, 1, 2, 1, 0] :=
  specInv_mirror_7 [0, 0, 2, 0, 2, 1, 0] [0, 0, 1, 2, 2, 2, 1] [1, 1, 0, 0, 1, 1, 0] [2, 2, 1, 2, 1, 2, 0] [1, 1, 2, 1, 2, 1, 0] demoR1_0020210 demoR2_0020210 demoC_0020210 demoM_0020210 demoMir_0020210

theorem demoR1_1020210 : invRung 7 5 20 [1, 0, 2, 0, 2, 1, 0] [1, 0, 2, 0, 2, 1, 0] 1 2 false = ([1, 1, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_1020210 : invRung 7 5 20 [1, 0, 2, 0, 2, 1, 0] [1, 1, 2, 0, 1, 2, 2] 3 1 true = ([1, 1, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1020210 : fieldCube 7 5 20 [1, 1, 2, 2, 1, 2, 2] = [2, 2, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_1020210 : fieldMul 7 5 20 [2, 2, 2, 1, 1, 1, 0] [1, 0, 2, 0, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020210 : mirrorTrits [2, 2, 2, 1, 1, 1, 0] = [1, 1, 1, 2, 2, 2, 0] := by
  decide

theorem demoInv_1020210 : specInv 7 5 20 [1, 0, 2, 0, 2, 1, 0] = some [1, 1, 1, 2, 2, 2, 0] :=
  specInv_mirror_7 [1, 0, 2, 0, 2, 1, 0] [1, 1, 2, 0, 1, 2, 2] [1, 1, 2, 2, 1, 2, 2] [2, 2, 2, 1, 1, 1, 0] [1, 1, 1, 2, 2, 2, 0] demoR1_1020210 demoR2_1020210 demoC_1020210 demoM_1020210 demoMir_1020210

theorem demoR1_2020210 : invRung 7 5 20 [2, 0, 2, 0, 2, 1, 0] [2, 0, 2, 0, 2, 1, 0] 1 2 false = ([1, 1, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_2020210 : invRung 7 5 20 [2, 0, 2, 0, 2, 1, 0] [1, 1, 1, 1, 0, 1, 1] 3 1 true = ([0, 2, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_2020210 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 0, 2] = [1, 0, 2, 2, 2, 1, 2] := by
  decide

theorem demoM_2020210 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 1, 2] [2, 0, 2, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2020210 : specInv 7 5 20 [2, 0, 2, 0, 2, 1, 0] = some [1, 0, 2, 2, 2, 1, 2] :=
  specInv_white_7 [2, 0, 2, 0, 2, 1, 0] [1, 1, 1, 1, 0, 1, 1] [0, 2, 2, 1, 1, 0, 2] [1, 0, 2, 2, 2, 1, 2] demoR1_2020210 demoR2_2020210 demoC_2020210 demoM_2020210

theorem demoR1_0120210 : invRung 7 5 20 [0, 1, 2, 0, 2, 1, 0] [0, 1, 2, 0, 2, 1, 0] 1 2 false = ([2, 1, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_0120210 : invRung 7 5 20 [0, 1, 2, 0, 2, 1, 0] [2, 1, 2, 0, 1, 1, 2] 3 1 true = ([1, 1, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_0120210 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 1, 0] = [2, 2, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_0120210 : fieldMul 7 5 20 [2, 2, 1, 2, 1, 2, 1] [0, 1, 2, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0120210 : specInv 7 5 20 [0, 1, 2, 0, 2, 1, 0] = some [2, 2, 1, 2, 1, 2, 1] :=
  specInv_white_7 [0, 1, 2, 0, 2, 1, 0] [2, 1, 2, 0, 1, 1, 2] [1, 1, 1, 0, 1, 1, 0] [2, 2, 1, 2, 1, 2, 1] demoR1_0120210 demoR2_0120210 demoC_0120210 demoM_0120210

theorem demoR1_1120210 : invRung 7 5 20 [1, 1, 2, 0, 2, 1, 0] [1, 1, 2, 0, 2, 1, 0] 1 2 false = ([0, 1, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_1120210 : invRung 7 5 20 [1, 1, 2, 0, 2, 1, 0] [0, 1, 2, 1, 2, 1, 1] 3 1 true = ([2, 2, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_1120210 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 1, 1] = [2, 1, 2, 2, 2, 0, 0] := by
  decide

theorem demoM_1120210 : fieldMul 7 5 20 [2, 1, 2, 2, 2, 0, 0] [1, 1, 2, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1120210 : specInv 7 5 20 [1, 1, 2, 0, 2, 1, 0] = some [2, 1, 2, 2, 2, 0, 0] :=
  specInv_white_7 [1, 1, 2, 0, 2, 1, 0] [0, 1, 2, 1, 2, 1, 1] [2, 2, 1, 2, 2, 1, 1] [2, 1, 2, 2, 2, 0, 0] demoR1_1120210 demoR2_1120210 demoC_1120210 demoM_1120210

theorem demoR1_2120210 : invRung 7 5 20 [2, 1, 2, 0, 2, 1, 0] [2, 1, 2, 0, 2, 1, 0] 1 2 false = ([2, 2, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2120210 : invRung 7 5 20 [2, 1, 2, 0, 2, 1, 0] [2, 2, 2, 1, 0, 2, 1] 3 1 true = ([0, 2, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2120210 : fieldCube 7 5 20 [0, 2, 2, 1, 0, 1, 1] = [2, 2, 1, 0, 2, 0, 2] := by
  decide

theorem demoM_2120210 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 0, 2] [2, 1, 2, 0, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120210 : mirrorTrits [2, 2, 1, 0, 2, 0, 2] = [1, 1, 2, 0, 1, 0, 1] := by
  decide

theorem demoInv_2120210 : specInv 7 5 20 [2, 1, 2, 0, 2, 1, 0] = some [1, 1, 2, 0, 1, 0, 1] :=
  specInv_mirror_7 [2, 1, 2, 0, 2, 1, 0] [2, 2, 2, 1, 0, 2, 1] [0, 2, 2, 1, 0, 1, 1] [2, 2, 1, 0, 2, 0, 2] [1, 1, 2, 0, 1, 0, 1] demoR1_2120210 demoR2_2120210 demoC_2120210 demoM_2120210 demoMir_2120210

theorem demoR1_0220210 : invRung 7 5 20 [0, 2, 2, 0, 2, 1, 0] [0, 2, 2, 0, 2, 1, 0] 1 2 false = ([2, 0, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_0220210 : invRung 7 5 20 [0, 2, 2, 0, 2, 1, 0] [2, 0, 1, 0, 0, 0, 2] 3 1 true = ([1, 2, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_0220210 : fieldCube 7 5 20 [1, 2, 2, 0, 1, 1, 1] = [2, 0, 0, 1, 2, 0, 0] := by
  decide

theorem demoM_0220210 : fieldMul 7 5 20 [2, 0, 0, 1, 2, 0, 0] [0, 2, 2, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0220210 : specInv 7 5 20 [0, 2, 2, 0, 2, 1, 0] = some [2, 0, 0, 1, 2, 0, 0] :=
  specInv_white_7 [0, 2, 2, 0, 2, 1, 0] [2, 0, 1, 0, 0, 0, 2] [1, 2, 2, 0, 1, 1, 1] [2, 0, 0, 1, 2, 0, 0] demoR1_0220210 demoR2_0220210 demoC_0220210 demoM_0220210

theorem demoR1_1220210 : invRung 7 5 20 [1, 2, 2, 0, 2, 1, 0] [1, 2, 2, 0, 2, 1, 0] 1 2 false = ([0, 0, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_1220210 : invRung 7 5 20 [1, 2, 2, 0, 2, 1, 0] [0, 0, 0, 2, 2, 2, 0] 3 1 true = ([1, 0, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_1220210 : fieldCube 7 5 20 [1, 0, 2, 0, 0, 1, 2] = [2, 0, 2, 2, 0, 0, 0] := by
  decide

theorem demoM_1220210 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 0, 0] [1, 2, 2, 0, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220210 : mirrorTrits [2, 0, 2, 2, 0, 0, 0] = [1, 0, 1, 1, 0, 0, 0] := by
  decide

theorem demoInv_1220210 : specInv 7 5 20 [1, 2, 2, 0, 2, 1, 0] = some [1, 0, 1, 1, 0, 0, 0] :=
  specInv_mirror_7 [1, 2, 2, 0, 2, 1, 0] [0, 0, 0, 2, 2, 2, 0] [1, 0, 2, 0, 0, 1, 2] [2, 0, 2, 2, 0, 0, 0] [1, 0, 1, 1, 0, 0, 0] demoR1_1220210 demoR2_1220210 demoC_1220210 demoM_1220210 demoMir_1220210

theorem demoR1_2220210 : invRung 7 5 20 [2, 2, 2, 0, 2, 1, 0] [2, 2, 2, 0, 2, 1, 0] 1 2 false = ([1, 0, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2220210 : invRung 7 5 20 [2, 2, 2, 0, 2, 1, 0] [1, 0, 1, 2, 1, 1, 2] 3 1 true = ([0, 0, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_2220210 : fieldCube 7 5 20 [0, 0, 2, 1, 1, 0, 2] = [1, 0, 2, 0, 2, 1, 2] := by
  decide

theorem demoM_2220210 : fieldMul 7 5 20 [1, 0, 2, 0, 2, 1, 2] [2, 2, 2, 0, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2220210 : specInv 7 5 20 [2, 2, 2, 0, 2, 1, 0] = some [1, 0, 2, 0, 2, 1, 2] :=
  specInv_white_7 [2, 2, 2, 0, 2, 1, 0] [1, 0, 1, 2, 1, 1, 2] [0, 0, 2, 1, 1, 0, 2] [1, 0, 2, 0, 2, 1, 2] demoR1_2220210 demoR2_2220210 demoC_2220210 demoM_2220210

theorem demoR1_0001210 : invRung 7 5 20 [0, 0, 0, 1, 2, 1, 0] [0, 0, 0, 1, 2, 1, 0] 1 2 false = ([1, 0, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_0001210 : invRung 7 5 20 [0, 0, 0, 1, 2, 1, 0] [1, 0, 0, 2, 1, 0, 1] 3 1 true = ([1, 2, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0001210 : fieldCube 7 5 20 [1, 2, 0, 1, 1, 0, 0] = [2, 1, 1, 0, 0, 2, 1] := by
  decide

theorem demoM_0001210 : fieldMul 7 5 20 [2, 1, 1, 0, 0, 2, 1] [0, 0, 0, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0001210 : specInv 7 5 20 [0, 0, 0, 1, 2, 1, 0] = some [2, 1, 1, 0, 0, 2, 1] :=
  specInv_white_7 [0, 0, 0, 1, 2, 1, 0] [1, 0, 0, 2, 1, 0, 1] [1, 2, 0, 1, 1, 0, 0] [2, 1, 1, 0, 0, 2, 1] demoR1_0001210 demoR2_0001210 demoC_0001210 demoM_0001210

theorem demoR1_1001210 : invRung 7 5 20 [1, 0, 0, 1, 2, 1, 0] [1, 0, 0, 1, 2, 1, 0] 1 2 false = ([2, 2, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1001210 : invRung 7 5 20 [1, 0, 0, 1, 2, 1, 0] [2, 2, 1, 1, 0, 0, 1] 3 1 true = ([1, 1, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_1001210 : fieldCube 7 5 20 [1, 1, 2, 0, 1, 1, 2] = [2, 1, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_1001210 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 1, 1] [1, 0, 0, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1001210 : specInv 7 5 20 [1, 0, 0, 1, 2, 1, 0] = some [2, 1, 2, 1, 0, 1, 1] :=
  specInv_white_7 [1, 0, 0, 1, 2, 1, 0] [2, 2, 1, 1, 0, 0, 1] [1, 1, 2, 0, 1, 1, 2] [2, 1, 2, 1, 0, 1, 1] demoR1_1001210 demoR2_1001210 demoC_1001210 demoM_1001210

theorem demoR1_2001210 : invRung 7 5 20 [2, 0, 0, 1, 2, 1, 0] [2, 0, 0, 1, 2, 1, 0] 1 2 false = ([2, 1, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_2001210 : invRung 7 5 20 [2, 0, 0, 1, 2, 1, 0] [2, 1, 1, 1, 0, 2, 0] 3 1 true = ([2, 2, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_2001210 : fieldCube 7 5 20 [2, 2, 0, 2, 1, 2, 0] = [0, 0, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_2001210 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 2, 2] [2, 0, 0, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2001210 : specInv 7 5 20 [2, 0, 0, 1, 2, 1, 0] = some [0, 0, 1, 0, 2, 2, 2] :=
  specInv_white_7 [2, 0, 0, 1, 2, 1, 0] [2, 1, 1, 1, 0, 2, 0] [2, 2, 0, 2, 1, 2, 0] [0, 0, 1, 0, 2, 2, 2] demoR1_2001210 demoR2_2001210 demoC_2001210 demoM_2001210

theorem demoR1_0101210 : invRung 7 5 20 [0, 1, 0, 1, 2, 1, 0] [0, 1, 0, 1, 2, 1, 0] 1 2 false = ([2, 0, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_0101210 : invRung 7 5 20 [0, 1, 0, 1, 2, 1, 0] [2, 0, 2, 1, 1, 1, 0] 3 1 true = ([1, 1, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0101210 : fieldCube 7 5 20 [1, 1, 2, 2, 2, 0, 2] = [0, 1, 0, 2, 2, 0, 0] := by
  decide

theorem demoM_0101210 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 0, 0] [0, 1, 0, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101210 : mirrorTrits [0, 1, 0, 2, 2, 0, 0] = [0, 2, 0, 1, 1, 0, 0] := by
  decide

theorem demoInv_0101210 : specInv 7 5 20 [0, 1, 0, 1, 2, 1, 0] = some [0, 2, 0, 1, 1, 0, 0] :=
  specInv_mirror_7 [0, 1, 0, 1, 2, 1, 0] [2, 0, 2, 1, 1, 1, 0] [1, 1, 2, 2, 2, 0, 2] [0, 1, 0, 2, 2, 0, 0] [0, 2, 0, 1, 1, 0, 0] demoR1_0101210 demoR2_0101210 demoC_0101210 demoM_0101210 demoMir_0101210

theorem demoR1_1101210 : invRung 7 5 20 [1, 1, 0, 1, 2, 1, 0] [1, 1, 0, 1, 2, 1, 0] 1 2 false = ([1, 0, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1101210 : invRung 7 5 20 [1, 1, 0, 1, 2, 1, 0] [1, 0, 0, 2, 2, 1, 0] 3 1 true = ([0, 1, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_1101210 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 0, 1] = [2, 0, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_1101210 : fieldMul 7 5 20 [2, 0, 1, 1, 1, 2, 0] [1, 1, 0, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1101210 : mirrorTrits [2, 0, 1, 1, 1, 2, 0] = [1, 0, 2, 2, 2, 1, 0] := by
  decide

theorem demoInv_1101210 : specInv 7 5 20 [1, 1, 0, 1, 2, 1, 0] = some [1, 0, 2, 2, 2, 1, 0] :=
  specInv_mirror_7 [1, 1, 0, 1, 2, 1, 0] [1, 0, 0, 2, 2, 1, 0] [0, 1, 0, 2, 2, 0, 1] [2, 0, 1, 1, 1, 2, 0] [1, 0, 2, 2, 2, 1, 0] demoR1_1101210 demoR2_1101210 demoC_1101210 demoM_1101210 demoMir_1101210

theorem demoR1_2101210 : invRung 7 5 20 [2, 1, 0, 1, 2, 1, 0] [2, 1, 0, 1, 2, 1, 0] 1 2 false = ([1, 2, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_2101210 : invRung 7 5 20 [2, 1, 0, 1, 2, 1, 0] [1, 2, 2, 0, 1, 2, 2] 3 1 true = ([2, 2, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_2101210 : fieldCube 7 5 20 [2, 2, 1, 0, 0, 0, 1] = [2, 1, 2, 0, 1, 1, 2] := by
  decide

theorem demoM_2101210 : fieldMul 7 5 20 [2, 1, 2, 0, 1, 1, 2] [2, 1, 0, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2101210 : specInv 7 5 20 [2, 1, 0, 1, 2, 1, 0] = some [2, 1, 2, 0, 1, 1, 2] :=
  specInv_white_7 [2, 1, 0, 1, 2, 1, 0] [1, 2, 2, 0, 1, 2, 2] [2, 2, 1, 0, 0, 0, 1] [2, 1, 2, 0, 1, 1, 2] demoR1_2101210 demoR2_2101210 demoC_2101210 demoM_2101210

theorem demoR1_0201210 : invRung 7 5 20 [0, 2, 0, 1, 2, 1, 0] [0, 2, 0, 1, 2, 1, 0] 1 2 false = ([2, 1, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_0201210 : invRung 7 5 20 [0, 2, 0, 1, 2, 1, 0] [2, 1, 0, 0, 0, 1, 2] 3 1 true = ([1, 0, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0201210 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 1, 1] = [2, 2, 0, 1, 2, 2, 1] := by
  decide

theorem demoM_0201210 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 2, 1] [0, 2, 0, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201210 : mirrorTrits [2, 2, 0, 1, 2, 2, 1] = [1, 1, 0, 2, 1, 1, 2] := by
  decide

theorem demoInv_0201210 : specInv 7 5 20 [0, 2, 0, 1, 2, 1, 0] = some [1, 1, 0, 2, 1, 1, 2] :=
  specInv_mirror_7 [0, 2, 0, 1, 2, 1, 0] [2, 1, 0, 0, 0, 1, 2] [1, 0, 1, 0, 0, 1, 1] [2, 2, 0, 1, 2, 2, 1] [1, 1, 0, 2, 1, 1, 2] demoR1_0201210 demoR2_0201210 demoC_0201210 demoM_0201210 demoMir_0201210

theorem demoR1_1201210 : invRung 7 5 20 [1, 2, 0, 1, 2, 1, 0] [1, 2, 0, 1, 2, 1, 0] 1 2 false = ([2, 0, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_1201210 : invRung 7 5 20 [1, 2, 0, 1, 2, 1, 0] [2, 0, 1, 1, 2, 0, 0] 3 1 true = ([0, 2, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_1201210 : fieldCube 7 5 20 [0, 2, 2, 1, 0, 2, 2] = [0, 1, 1, 1, 1, 2, 2] := by
  decide

theorem demoM_1201210 : fieldMul 7 5 20 [0, 1, 1, 1, 1, 2, 2] [1, 2, 0, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201210 : mirrorTrits [0, 1, 1, 1, 1, 2, 2] = [0, 2, 2, 2, 2, 1, 1] := by
  decide

theorem demoInv_1201210 : specInv 7 5 20 [1, 2, 0, 1, 2, 1, 0] = some [0, 2, 2, 2, 2, 1, 1] :=
  specInv_mirror_7 [1, 2, 0, 1, 2, 1, 0] [2, 0, 1, 1, 2, 0, 0] [0, 2, 2, 1, 0, 2, 2] [0, 1, 1, 1, 1, 2, 2] [0, 2, 2, 2, 2, 1, 1] demoR1_1201210 demoR2_1201210 demoC_1201210 demoM_1201210 demoMir_1201210

theorem demoR1_2201210 : invRung 7 5 20 [2, 2, 0, 1, 2, 1, 0] [2, 2, 0, 1, 2, 1, 0] 1 2 false = ([2, 0, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_2201210 : invRung 7 5 20 [2, 2, 0, 1, 2, 1, 0] [2, 0, 2, 1, 2, 2, 0] 3 1 true = ([1, 0, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_2201210 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 0, 0] = [2, 1, 1, 1, 0, 2, 2] := by
  decide

theorem demoM_2201210 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 2, 2] [2, 2, 0, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2201210 : specInv 7 5 20 [2, 2, 0, 1, 2, 1, 0] = some [2, 1, 1, 1, 0, 2, 2] :=
  specInv_white_7 [2, 2, 0, 1, 2, 1, 0] [2, 0, 2, 1, 2, 2, 0] [1, 0, 1, 1, 1, 0, 0] [2, 1, 1, 1, 0, 2, 2] demoR1_2201210 demoR2_2201210 demoC_2201210 demoM_2201210

theorem demoR1_0011210 : invRung 7 5 20 [0, 0, 1, 1, 2, 1, 0] [0, 0, 1, 1, 2, 1, 0] 1 2 false = ([2, 1, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_0011210 : invRung 7 5 20 [0, 0, 1, 1, 2, 1, 0] [2, 1, 1, 2, 2, 0, 2] 3 1 true = ([2, 0, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_0011210 : fieldCube 7 5 20 [2, 0, 2, 0, 0, 0, 0] = [2, 0, 0, 0, 0, 0, 2] := by
  decide

theorem demoM_0011210 : fieldMul 7 5 20 [2, 0, 0, 0, 0, 0, 2] [0, 0, 1, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0011210 : specInv 7 5 20 [0, 0, 1, 1, 2, 1, 0] = some [2, 0, 0, 0, 0, 0, 2] :=
  specInv_white_7 [0, 0, 1, 1, 2, 1, 0] [2, 1, 1, 2, 2, 0, 2] [2, 0, 2, 0, 0, 0, 0] [2, 0, 0, 0, 0, 0, 2] demoR1_0011210 demoR2_0011210 demoC_0011210 demoM_0011210

theorem demoR1_1011210 : invRung 7 5 20 [1, 0, 1, 1, 2, 1, 0] [1, 0, 1, 1, 2, 1, 0] 1 2 false = ([2, 2, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_1011210 : invRung 7 5 20 [1, 0, 1, 1, 2, 1, 0] [2, 2, 0, 2, 0, 2, 0] 3 1 true = ([2, 0, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1011210 : fieldCube 7 5 20 [2, 0, 0, 1, 0, 2, 0] = [2, 2, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_1011210 : fieldMul 7 5 20 [2, 2, 0, 0, 2, 0, 1] [1, 0, 1, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011210 : mirrorTrits [2, 2, 0, 0, 2, 0, 1] = [1, 1, 0, 0, 1, 0, 2] := by
  decide

theorem demoInv_1011210 : specInv 7 5 20 [1, 0, 1, 1, 2, 1, 0] = some [1, 1, 0, 0, 1, 0, 2] :=
  specInv_mirror_7 [1, 0, 1, 1, 2, 1, 0] [2, 2, 0, 2, 0, 2, 0] [2, 0, 0, 1, 0, 2, 0] [2, 2, 0, 0, 2, 0, 1] [1, 1, 0, 0, 1, 0, 2] demoR1_1011210 demoR2_1011210 demoC_1011210 demoM_1011210 demoMir_1011210

theorem demoR1_2011210 : invRung 7 5 20 [2, 0, 1, 1, 2, 1, 0] [2, 0, 1, 1, 2, 1, 0] 1 2 false = ([1, 2, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_2011210 : invRung 7 5 20 [2, 0, 1, 1, 2, 1, 0] [1, 2, 1, 2, 1, 2, 1] 3 1 true = ([2, 0, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2011210 : fieldCube 7 5 20 [2, 0, 0, 0, 0, 1, 0] = [0, 1, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_2011210 : fieldMul 7 5 20 [0, 1, 1, 0, 1, 1, 2] [2, 0, 1, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2011210 : specInv 7 5 20 [2, 0, 1, 1, 2, 1, 0] = some [0, 1, 1, 0, 1, 1, 2] :=
  specInv_white_7 [2, 0, 1, 1, 2, 1, 0] [1, 2, 1, 2, 1, 2, 1] [2, 0, 0, 0, 0, 1, 0] [0, 1, 1, 0, 1, 1, 2] demoR1_2011210 demoR2_2011210 demoC_2011210 demoM_2011210

theorem demoR1_0111210 : invRung 7 5 20 [0, 1, 1, 1, 2, 1, 0] [0, 1, 1, 1, 2, 1, 0] 1 2 false = ([1, 0, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0111210 : invRung 7 5 20 [0, 1, 1, 1, 2, 1, 0] [1, 0, 2, 0, 1, 2, 1] 3 1 true = ([0, 1, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0111210 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 0, 1] = [0, 1, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_0111210 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 1, 1] [0, 1, 1, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111210 : mirrorTrits [0, 1, 2, 2, 1, 1, 1] = [0, 2, 1, 1, 2, 2, 2] := by
  decide

theorem demoInv_0111210 : specInv 7 5 20 [0, 1, 1, 1, 2, 1, 0] = some [0, 2, 1, 1, 2, 2, 2] :=
  specInv_mirror_7 [0, 1, 1, 1, 2, 1, 0] [1, 0, 2, 0, 1, 2, 1] [0, 1, 0, 0, 0, 0, 1] [0, 1, 2, 2, 1, 1, 1] [0, 2, 1, 1, 2, 2, 2] demoR1_0111210 demoR2_0111210 demoC_0111210 demoM_0111210 demoMir_0111210

theorem demoR1_1111210 : invRung 7 5 20 [1, 1, 1, 1, 2, 1, 0] [1, 1, 1, 1, 2, 1, 0] 1 2 false = ([2, 1, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1111210 : invRung 7 5 20 [1, 1, 1, 1, 2, 1, 0] [2, 1, 2, 1, 2, 2, 1] 3 1 true = ([2, 0, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1111210 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 1, 1] = [0, 0, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_1111210 : fieldMul 7 5 20 [0, 0, 0, 2, 2, 0, 2] [1, 1, 1, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111210 : mirrorTrits [0, 0, 0, 2, 2, 0, 2] = [0, 0, 0, 1, 1, 0, 1] := by
  decide

theorem demoInv_1111210 : specInv 7 5 20 [1, 1, 1, 1, 2, 1, 0] = some [0, 0, 0, 1, 1, 0, 1] :=
  specInv_mirror_7 [1, 1, 1, 1, 2, 1, 0] [2, 1, 2, 1, 2, 2, 1] [2, 0, 1, 0, 1, 1, 1] [0, 0, 0, 2, 2, 0, 2] [0, 0, 0, 1, 1, 0, 1] demoR1_1111210 demoR2_1111210 demoC_1111210 demoM_1111210 demoMir_1111210

theorem demoR1_2111210 : invRung 7 5 20 [2, 1, 1, 1, 2, 1, 0] [2, 1, 1, 1, 2, 1, 0] 1 2 false = ([1, 0, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2111210 : invRung 7 5 20 [2, 1, 1, 1, 2, 1, 0] [1, 0, 0, 1, 0, 2, 1] 3 1 true = ([1, 1, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_2111210 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 0, 1] = [1, 1, 2, 2, 1, 1, 0] := by
  decide

theorem demoM_2111210 : fieldMul 7 5 20 [1, 1, 2, 2, 1, 1, 0] [2, 1, 1, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2111210 : specInv 7 5 20 [2, 1, 1, 1, 2, 1, 0] = some [1, 1, 2, 2, 1, 1, 0] :=
  specInv_white_7 [2, 1, 1, 1, 2, 1, 0] [1, 0, 0, 1, 0, 2, 1] [1, 1, 2, 0, 0, 0, 1] [1, 1, 2, 2, 1, 1, 0] demoR1_2111210 demoR2_2111210 demoC_2111210 demoM_2111210

theorem demoR1_0211210 : invRung 7 5 20 [0, 2, 1, 1, 2, 1, 0] [0, 2, 1, 1, 2, 1, 0] 1 2 false = ([0, 2, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_0211210 : invRung 7 5 20 [0, 2, 1, 1, 2, 1, 0] [0, 2, 0, 1, 2, 1, 0] 3 1 true = ([0, 2, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_0211210 : fieldCube 7 5 20 [0, 2, 0, 1, 2, 0, 0] = [1, 2, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_0211210 : fieldMul 7 5 20 [1, 2, 1, 1, 0, 0, 2] [0, 2, 1, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211210 : mirrorTrits [1, 2, 1, 1, 0, 0, 2] = [2, 1, 2, 2, 0, 0, 1] := by
  decide

theorem demoInv_0211210 : specInv 7 5 20 [0, 2, 1, 1, 2, 1, 0] = some [2, 1, 2, 2, 0, 0, 1] :=
  specInv_mirror_7 [0, 2, 1, 1, 2, 1, 0] [0, 2, 0, 1, 2, 1, 0] [0, 2, 0, 1, 2, 0, 0] [1, 2, 1, 1, 0, 0, 2] [2, 1, 2, 2, 0, 0, 1] demoR1_0211210 demoR2_0211210 demoC_0211210 demoM_0211210 demoMir_0211210

theorem demoR1_1211210 : invRung 7 5 20 [1, 2, 1, 1, 2, 1, 0] [1, 2, 1, 1, 2, 1, 0] 1 2 false = ([2, 1, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_1211210 : invRung 7 5 20 [1, 2, 1, 1, 2, 1, 0] [2, 1, 1, 1, 2, 1, 0] 3 1 true = ([2, 2, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_1211210 : fieldCube 7 5 20 [2, 2, 0, 0, 1, 2, 1] = [1, 1, 1, 1, 0, 1, 0] := by
  decide

theorem demoM_1211210 : fieldMul 7 5 20 [1, 1, 1, 1, 0, 1, 0] [1, 2, 1, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1211210 : specInv 7 5 20 [1, 2, 1, 1, 2, 1, 0] = some [1, 1, 1, 1, 0, 1, 0] :=
  specInv_white_7 [1, 2, 1, 1, 2, 1, 0] [2, 1, 1, 1, 2, 1, 0] [2, 2, 0, 0, 1, 2, 1] [1, 1, 1, 1, 0, 1, 0] demoR1_1211210 demoR2_1211210 demoC_1211210 demoM_1211210

theorem demoR1_2211210 : invRung 7 5 20 [2, 2, 1, 1, 2, 1, 0] [2, 2, 1, 1, 2, 1, 0] 1 2 false = ([1, 0, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2211210 : invRung 7 5 20 [2, 2, 1, 1, 2, 1, 0] [1, 0, 2, 2, 2, 0, 0] 3 1 true = ([1, 2, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_2211210 : fieldCube 7 5 20 [1, 2, 0, 1, 1, 1, 0] = [0, 2, 2, 0, 1, 0, 0] := by
  decide

theorem demoM_2211210 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 0, 0] [2, 2, 1, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2211210 : specInv 7 5 20 [2, 2, 1, 1, 2, 1, 0] = some [0, 2, 2, 0, 1, 0, 0] :=
  specInv_white_7 [2, 2, 1, 1, 2, 1, 0] [1, 0, 2, 2, 2, 0, 0] [1, 2, 0, 1, 1, 1, 0] [0, 2, 2, 0, 1, 0, 0] demoR1_2211210 demoR2_2211210 demoC_2211210 demoM_2211210

theorem demoR1_0021210 : invRung 7 5 20 [0, 0, 2, 1, 2, 1, 0] [0, 0, 2, 1, 2, 1, 0] 1 2 false = ([1, 0, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_0021210 : invRung 7 5 20 [0, 0, 2, 1, 2, 1, 0] [1, 0, 2, 2, 1, 2, 0] 3 1 true = ([2, 2, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_0021210 : fieldCube 7 5 20 [2, 2, 0, 2, 0, 0, 0] = [1, 0, 2, 2, 0, 2, 0] := by
  decide

theorem demoM_0021210 : fieldMul 7 5 20 [1, 0, 2, 2, 0, 2, 0] [0, 0, 2, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021210 : mirrorTrits [1, 0, 2, 2, 0, 2, 0] = [2, 0, 1, 1, 0, 1, 0] := by
  decide

theorem demoInv_0021210 : specInv 7 5 20 [0, 0, 2, 1, 2, 1, 0] = some [2, 0, 1, 1, 0, 1, 0] :=
  specInv_mirror_7 [0, 0, 2, 1, 2, 1, 0] [1, 0, 2, 2, 1, 2, 0] [2, 2, 0, 2, 0, 0, 0] [1, 0, 2, 2, 0, 2, 0] [2, 0, 1, 1, 0, 1, 0] demoR1_0021210 demoR2_0021210 demoC_0021210 demoM_0021210 demoMir_0021210

theorem demoR1_1021210 : invRung 7 5 20 [1, 0, 2, 1, 2, 1, 0] [1, 0, 2, 1, 2, 1, 0] 1 2 false = ([2, 0, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1021210 : invRung 7 5 20 [1, 0, 2, 1, 2, 1, 0] [2, 0, 0, 0, 1, 0, 1] 3 1 true = ([1, 1, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_1021210 : fieldCube 7 5 20 [1, 1, 2, 2, 0, 1, 1] = [1, 2, 2, 2, 2, 1, 2] := by
  decide

theorem demoM_1021210 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 1, 2] [1, 0, 2, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1021210 : specInv 7 5 20 [1, 0, 2, 1, 2, 1, 0] = some [1, 2, 2, 2, 2, 1, 2] :=
  specInv_white_7 [1, 0, 2, 1, 2, 1, 0] [2, 0, 0, 0, 1, 0, 1] [1, 1, 2, 2, 0, 1, 1] [1, 2, 2, 2, 2, 1, 2] demoR1_1021210 demoR2_1021210 demoC_1021210 demoM_1021210

theorem demoR1_2021210 : invRung 7 5 20 [2, 0, 2, 1, 2, 1, 0] [2, 0, 2, 1, 2, 1, 0] 1 2 false = ([2, 1, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2021210 : invRung 7 5 20 [2, 0, 2, 1, 2, 1, 0] [2, 1, 0, 0, 0, 1, 0] 3 1 true = ([2, 1, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_2021210 : fieldCube 7 5 20 [2, 1, 2, 2, 0, 2, 2] = [0, 1, 2, 0, 1, 0, 2] := by
  decide

theorem demoM_2021210 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 0, 2] [2, 0, 2, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021210 : mirrorTrits [0, 1, 2, 0, 1, 0, 2] = [0, 2, 1, 0, 2, 0, 1] := by
  decide

theorem demoInv_2021210 : specInv 7 5 20 [2, 0, 2, 1, 2, 1, 0] = some [0, 2, 1, 0, 2, 0, 1] :=
  specInv_mirror_7 [2, 0, 2, 1, 2, 1, 0] [2, 1, 0, 0, 0, 1, 0] [2, 1, 2, 2, 0, 2, 2] [0, 1, 2, 0, 1, 0, 2] [0, 2, 1, 0, 2, 0, 1] demoR1_2021210 demoR2_2021210 demoC_2021210 demoM_2021210 demoMir_2021210

theorem demoR1_0121210 : invRung 7 5 20 [0, 1, 2, 1, 2, 1, 0] [0, 1, 2, 1, 2, 1, 0] 1 2 false = ([1, 0, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_0121210 : invRung 7 5 20 [0, 1, 2, 1, 2, 1, 0] [1, 0, 1, 1, 1, 1, 1] 3 1 true = ([2, 1, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_0121210 : fieldCube 7 5 20 [2, 1, 1, 2, 2, 0, 1] = [1, 0, 1, 1, 1, 2, 1] := by
  decide

theorem demoM_0121210 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 2, 1] [0, 1, 2, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0121210 : specInv 7 5 20 [0, 1, 2, 1, 2, 1, 0] = some [1, 0, 1, 1, 1, 2, 1] :=
  specInv_white_7 [0, 1, 2, 1, 2, 1, 0] [1, 0, 1, 1, 1, 1, 1] [2, 1, 1, 2, 2, 0, 1] [1, 0, 1, 1, 1, 2, 1] demoR1_0121210 demoR2_0121210 demoC_0121210 demoM_0121210

theorem demoR1_1121210 : invRung 7 5 20 [1, 1, 2, 1, 2, 1, 0] [1, 1, 2, 1, 2, 1, 0] 1 2 false = ([0, 2, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1121210 : invRung 7 5 20 [1, 1, 2, 1, 2, 1, 0] [0, 2, 1, 2, 2, 1, 0] 3 1 true = ([1, 0, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_1121210 : fieldCube 7 5 20 [1, 0, 0, 2, 2, 0, 1] = [0, 0, 1, 0, 1, 2, 0] := by
  decide

theorem demoM_1121210 : fieldMul 7 5 20 [0, 0, 1, 0, 1, 2, 0] [1, 1, 2, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121210 : mirrorTrits [0, 0, 1, 0, 1, 2, 0] = [0, 0, 2, 0, 2, 1, 0] := by
  decide

theorem demoInv_1121210 : specInv 7 5 20 [1, 1, 2, 1, 2, 1, 0] = some [0, 0, 2, 0, 2, 1, 0] :=
  specInv_mirror_7 [1, 1, 2, 1, 2, 1, 0] [0, 2, 1, 2, 2, 1, 0] [1, 0, 0, 2, 2, 0, 1] [0, 0, 1, 0, 1, 2, 0] [0, 0, 2, 0, 2, 1, 0] demoR1_1121210 demoR2_1121210 demoC_1121210 demoM_1121210 demoMir_1121210

theorem demoR1_2121210 : invRung 7 5 20 [2, 1, 2, 1, 2, 1, 0] [2, 1, 2, 1, 2, 1, 0] 1 2 false = ([0, 1, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_2121210 : invRung 7 5 20 [2, 1, 2, 1, 2, 1, 0] [0, 1, 2, 1, 2, 0, 0] 3 1 true = ([2, 1, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2121210 : fieldCube 7 5 20 [2, 1, 2, 2, 1, 2, 2] = [0, 2, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_2121210 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 1, 0] [2, 1, 2, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2121210 : specInv 7 5 20 [2, 1, 2, 1, 2, 1, 0] = some [0, 2, 2, 1, 1, 1, 0] :=
  specInv_white_7 [2, 1, 2, 1, 2, 1, 0] [0, 1, 2, 1, 2, 0, 0] [2, 1, 2, 2, 1, 2, 2] [0, 2, 2, 1, 1, 1, 0] demoR1_2121210 demoR2_2121210 demoC_2121210 demoM_2121210

theorem demoR1_0221210 : invRung 7 5 20 [0, 2, 2, 1, 2, 1, 0] [0, 2, 2, 1, 2, 1, 0] 1 2 false = ([2, 2, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_0221210 : invRung 7 5 20 [0, 2, 2, 1, 2, 1, 0] [2, 2, 1, 0, 0, 1, 2] 3 1 true = ([0, 2, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_0221210 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 0, 2] = [2, 0, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_0221210 : fieldMul 7 5 20 [2, 0, 0, 2, 2, 2, 1] [0, 2, 2, 1, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0221210 : mirrorTrits [2, 0, 0, 2, 2, 2, 1] = [1, 0, 0, 1, 1, 1, 2] := by
  decide

theorem demoInv_0221210 : specInv 7 5 20 [0, 2, 2, 1, 2, 1, 0] = some [1, 0, 0, 1, 1, 1, 2] :=
  specInv_mirror_7 [0, 2, 2, 1, 2, 1, 0] [2, 2, 1, 0, 0, 1, 2] [0, 2, 1, 2, 1, 0, 2] [2, 0, 0, 2, 2, 2, 1] [1, 0, 0, 1, 1, 1, 2] demoR1_0221210 demoR2_0221210 demoC_0221210 demoM_0221210 demoMir_0221210

theorem demoR1_1221210 : invRung 7 5 20 [1, 2, 2, 1, 2, 1, 0] [1, 2, 2, 1, 2, 1, 0] 1 2 false = ([2, 1, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_1221210 : invRung 7 5 20 [1, 2, 2, 1, 2, 1, 0] [2, 1, 0, 2, 1, 2, 0] 3 1 true = ([2, 1, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_1221210 : fieldCube 7 5 20 [2, 1, 0, 1, 2, 0, 2] = [0, 1, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_1221210 : fieldMul 7 5 20 [0, 1, 2, 2, 2, 2, 1] [1, 2, 2, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1221210 : specInv 7 5 20 [1, 2, 2, 1, 2, 1, 0] = some [0, 1, 2, 2, 2, 2, 1] :=
  specInv_white_7 [1, 2, 2, 1, 2, 1, 0] [2, 1, 0, 2, 1, 2, 0] [2, 1, 0, 1, 2, 0, 2] [0, 1, 2, 2, 2, 2, 1] demoR1_1221210 demoR2_1221210 demoC_1221210 demoM_1221210

theorem demoR1_2221210 : invRung 7 5 20 [2, 2, 2, 1, 2, 1, 0] [2, 2, 2, 1, 2, 1, 0] 1 2 false = ([2, 2, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_2221210 : invRung 7 5 20 [2, 2, 2, 1, 2, 1, 0] [2, 2, 2, 1, 1, 1, 2] 3 1 true = ([0, 2, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_2221210 : fieldCube 7 5 20 [0, 2, 2, 0, 2, 0, 1] = [0, 0, 2, 2, 1, 0, 2] := by
  decide

theorem demoM_2221210 : fieldMul 7 5 20 [0, 0, 2, 2, 1, 0, 2] [2, 2, 2, 1, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2221210 : specInv 7 5 20 [2, 2, 2, 1, 2, 1, 0] = some [0, 0, 2, 2, 1, 0, 2] :=
  specInv_white_7 [2, 2, 2, 1, 2, 1, 0] [2, 2, 2, 1, 1, 1, 2] [0, 2, 2, 0, 2, 0, 1] [0, 0, 2, 2, 1, 0, 2] demoR1_2221210 demoR2_2221210 demoC_2221210 demoM_2221210

theorem demoR1_0002210 : invRung 7 5 20 [0, 0, 0, 2, 2, 1, 0] [0, 0, 0, 2, 2, 1, 0] 1 2 false = ([1, 0, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_0002210 : invRung 7 5 20 [0, 0, 0, 2, 2, 1, 0] [1, 0, 1, 1, 2, 0, 0] 3 1 true = ([2, 2, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0002210 : fieldCube 7 5 20 [2, 2, 1, 2, 1, 0, 1] = [1, 2, 1, 1, 1, 1, 0] := by
  decide

theorem demoM_0002210 : fieldMul 7 5 20 [1, 2, 1, 1, 1, 1, 0] [0, 0, 0, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002210 : mirrorTrits [1, 2, 1, 1, 1, 1, 0] = [2, 1, 2, 2, 2, 2, 0] := by
  decide

theorem demoInv_0002210 : specInv 7 5 20 [0, 0, 0, 2, 2, 1, 0] = some [2, 1, 2, 2, 2, 2, 0] :=
  specInv_mirror_7 [0, 0, 0, 2, 2, 1, 0] [1, 0, 1, 1, 2, 0, 0] [2, 2, 1, 2, 1, 0, 1] [1, 2, 1, 1, 1, 1, 0] [2, 1, 2, 2, 2, 2, 0] demoR1_0002210 demoR2_0002210 demoC_0002210 demoM_0002210 demoMir_0002210

theorem demoR1_1002210 : invRung 7 5 20 [1, 0, 0, 2, 2, 1, 0] [1, 0, 0, 2, 2, 1, 0] 1 2 false = ([2, 1, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_1002210 : invRung 7 5 20 [1, 0, 0, 2, 2, 1, 0] [2, 1, 2, 0, 1, 2, 2] 3 1 true = ([1, 1, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_1002210 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 0, 1] = [1, 0, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_1002210 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 0, 0] [1, 0, 0, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002210 : mirrorTrits [1, 0, 2, 1, 1, 0, 0] = [2, 0, 1, 2, 2, 0, 0] := by
  decide

theorem demoInv_1002210 : specInv 7 5 20 [1, 0, 0, 2, 2, 1, 0] = some [2, 0, 1, 2, 2, 0, 0] :=
  specInv_mirror_7 [1, 0, 0, 2, 2, 1, 0] [2, 1, 2, 0, 1, 2, 2] [1, 1, 0, 0, 2, 0, 1] [1, 0, 2, 1, 1, 0, 0] [2, 0, 1, 2, 2, 0, 0] demoR1_1002210 demoR2_1002210 demoC_1002210 demoM_1002210 demoMir_1002210

theorem demoR1_2002210 : invRung 7 5 20 [2, 0, 0, 2, 2, 1, 0] [2, 0, 0, 2, 2, 1, 0] 1 2 false = ([2, 1, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_2002210 : invRung 7 5 20 [2, 0, 0, 2, 2, 1, 0] [2, 1, 0, 2, 0, 1, 0] 3 1 true = ([0, 1, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_2002210 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 2, 1] = [1, 1, 0, 0, 0, 0, 2] := by
  decide

theorem demoM_2002210 : fieldMul 7 5 20 [1, 1, 0, 0, 0, 0, 2] [2, 0, 0, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002210 : mirrorTrits [1, 1, 0, 0, 0, 0, 2] = [2, 2, 0, 0, 0, 0, 1] := by
  decide

theorem demoInv_2002210 : specInv 7 5 20 [2, 0, 0, 2, 2, 1, 0] = some [2, 2, 0, 0, 0, 0, 1] :=
  specInv_mirror_7 [2, 0, 0, 2, 2, 1, 0] [2, 1, 0, 2, 0, 1, 0] [0, 1, 2, 2, 1, 2, 1] [1, 1, 0, 0, 0, 0, 2] [2, 2, 0, 0, 0, 0, 1] demoR1_2002210 demoR2_2002210 demoC_2002210 demoM_2002210 demoMir_2002210

theorem demoR1_0102210 : invRung 7 5 20 [0, 1, 0, 2, 2, 1, 0] [0, 1, 0, 2, 2, 1, 0] 1 2 false = ([0, 2, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_0102210 : invRung 7 5 20 [0, 1, 0, 2, 2, 1, 0] [0, 2, 2, 0, 1, 1, 2] 3 1 true = ([1, 0, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0102210 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 2, 2] = [1, 2, 1, 0, 1, 0, 0] := by
  decide

theorem demoM_0102210 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 0, 0] [0, 1, 0, 2, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0102210 : specInv 7 5 20 [0, 1, 0, 2, 2, 1, 0] = some [1, 2, 1, 0, 1, 0, 0] :=
  specInv_white_7 [0, 1, 0, 2, 2, 1, 0] [0, 2, 2, 0, 1, 1, 2] [1, 0, 2, 1, 1, 2, 2] [1, 2, 1, 0, 1, 0, 0] demoR1_0102210 demoR2_0102210 demoC_0102210 demoM_0102210

theorem demoR1_1102210 : invRung 7 5 20 [1, 1, 0, 2, 2, 1, 0] [1, 1, 0, 2, 2, 1, 0] 1 2 false = ([0, 1, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1102210 : invRung 7 5 20 [1, 1, 0, 2, 2, 1, 0] [0, 1, 0, 1, 1, 2, 1] 3 1 true = ([0, 0, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_1102210 : fieldCube 7 5 20 [0, 0, 1, 0, 1, 0, 2] = [0, 0, 1, 0, 2, 0, 1] := by
  decide

theorem demoM_1102210 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 0, 1] [1, 1, 0, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102210 : mirrorTrits [0, 0, 1, 0, 2, 0, 1] = [0, 0, 2, 0, 1, 0, 2] := by
  decide

theorem demoInv_1102210 : specInv 7 5 20 [1, 1, 0, 2, 2, 1, 0] = some [0, 0, 2, 0, 1, 0, 2] :=
  specInv_mirror_7 [1, 1, 0, 2, 2, 1, 0] [0, 1, 0, 1, 1, 2, 1] [0, 0, 1, 0, 1, 0, 2] [0, 0, 1, 0, 2, 0, 1] [0, 0, 2, 0, 1, 0, 2] demoR1_1102210 demoR2_1102210 demoC_1102210 demoM_1102210 demoMir_1102210

theorem demoR1_2102210 : invRung 7 5 20 [2, 1, 0, 2, 2, 1, 0] [2, 1, 0, 2, 2, 1, 0] 1 2 false = ([1, 1, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2102210 : invRung 7 5 20 [2, 1, 0, 2, 2, 1, 0] [1, 1, 0, 1, 1, 2, 2] 3 1 true = ([2, 0, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2102210 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 2, 2] = [0, 2, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_2102210 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 1, 0] [2, 1, 0, 2, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2102210 : specInv 7 5 20 [2, 1, 0, 2, 2, 1, 0] = some [0, 2, 2, 0, 1, 1, 0] :=
  specInv_white_7 [2, 1, 0, 2, 2, 1, 0] [1, 1, 0, 1, 1, 2, 2] [2, 0, 2, 2, 1, 2, 2] [0, 2, 2, 0, 1, 1, 0] demoR1_2102210 demoR2_2102210 demoC_2102210 demoM_2102210

theorem demoR1_0202210 : invRung 7 5 20 [0, 2, 0, 2, 2, 1, 0] [0, 2, 0, 2, 2, 1, 0] 1 2 false = ([1, 0, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_0202210 : invRung 7 5 20 [0, 2, 0, 2, 2, 1, 0] [1, 0, 2, 0, 1, 2, 2] 3 1 true = ([0, 1, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_0202210 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 0, 2] = [0, 1, 1, 2, 2, 1, 0] := by
  decide

theorem demoM_0202210 : fieldMul 7 5 20 [0, 1, 1, 2, 2, 1, 0] [0, 2, 0, 2, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0202210 : specInv 7 5 20 [0, 2, 0, 2, 2, 1, 0] = some [0, 1, 1, 2, 2, 1, 0] :=
  specInv_white_7 [0, 2, 0, 2, 2, 1, 0] [1, 0, 2, 0, 1, 2, 2] [0, 1, 2, 0, 2, 0, 2] [0, 1, 1, 2, 2, 1, 0] demoR1_0202210 demoR2_0202210 demoC_0202210 demoM_0202210

theorem demoR1_1202210 : invRung 7 5 20 [1, 2, 0, 2, 2, 1, 0] [1, 2, 0, 2, 2, 1, 0] 1 2 false = ([0, 1, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_1202210 : invRung 7 5 20 [1, 2, 0, 2, 2, 1, 0] [0, 1, 0, 1, 1, 1, 2] 3 1 true = ([0, 1, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1202210 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 2, 0] = [0, 2, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_1202210 : fieldMul 7 5 20 [0, 2, 0, 1, 2, 0, 1] [1, 2, 0, 2, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1202210 : specInv 7 5 20 [1, 2, 0, 2, 2, 1, 0] = some [0, 2, 0, 1, 2, 0, 1] :=
  specInv_white_7 [1, 2, 0, 2, 2, 1, 0] [0, 1, 0, 1, 1, 1, 2] [0, 1, 0, 1, 0, 2, 0] [0, 2, 0, 1, 2, 0, 1] demoR1_1202210 demoR2_1202210 demoC_1202210 demoM_1202210

theorem demoR1_2202210 : invRung 7 5 20 [2, 2, 0, 2, 2, 1, 0] [2, 2, 0, 2, 2, 1, 0] 1 2 false = ([2, 2, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_2202210 : invRung 7 5 20 [2, 2, 0, 2, 2, 1, 0] [2, 2, 2, 0, 1, 1, 1] 3 1 true = ([1, 1, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_2202210 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 2, 2] = [0, 2, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_2202210 : fieldMul 7 5 20 [0, 2, 0, 1, 1, 2, 1] [2, 2, 0, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202210 : mirrorTrits [0, 2, 0, 1, 1, 2, 1] = [0, 1, 0, 2, 2, 1, 2] := by
  decide

theorem demoInv_2202210 : specInv 7 5 20 [2, 2, 0, 2, 2, 1, 0] = some [0, 1, 0, 2, 2, 1, 2] :=
  specInv_mirror_7 [2, 2, 0, 2, 2, 1, 0] [2, 2, 2, 0, 1, 1, 1] [1, 1, 0, 0, 1, 2, 2] [0, 2, 0, 1, 1, 2, 1] [0, 1, 0, 2, 2, 1, 2] demoR1_2202210 demoR2_2202210 demoC_2202210 demoM_2202210 demoMir_2202210

theorem demoR1_0012210 : invRung 7 5 20 [0, 0, 1, 2, 2, 1, 0] [0, 0, 1, 2, 2, 1, 0] 1 2 false = ([0, 0, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_0012210 : invRung 7 5 20 [0, 0, 1, 2, 2, 1, 0] [0, 0, 2, 2, 1, 2, 2] 3 1 true = ([2, 1, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0012210 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 2, 1] = [1, 1, 1, 0, 0, 1, 1] := by
  decide

theorem demoM_0012210 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 1, 1] [0, 0, 1, 2, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0012210 : specInv 7 5 20 [0, 0, 1, 2, 2, 1, 0] = some [1, 1, 1, 0, 0, 1, 1] :=
  specInv_white_7 [0, 0, 1, 2, 2, 1, 0] [0, 0, 2, 2, 1, 2, 2] [2, 1, 1, 0, 1, 2, 1] [1, 1, 1, 0, 0, 1, 1] demoR1_0012210 demoR2_0012210 demoC_0012210 demoM_0012210

theorem demoR1_1012210 : invRung 7 5 20 [1, 0, 1, 2, 2, 1, 0] [1, 0, 1, 2, 2, 1, 0] 1 2 false = ([0, 1, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_1012210 : invRung 7 5 20 [1, 0, 1, 2, 2, 1, 0] [0, 1, 2, 1, 1, 1, 0] 3 1 true = ([2, 2, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_1012210 : fieldCube 7 5 20 [2, 2, 2, 2, 0, 0, 1] = [1, 1, 1, 0, 1, 0, 0] := by
  decide

theorem demoM_1012210 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 0, 0] [1, 0, 1, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1012210 : mirrorTrits [1, 1, 1, 0, 1, 0, 0] = [2, 2, 2, 0, 2, 0, 0] := by
  decide

theorem demoInv_1012210 : specInv 7 5 20 [1, 0, 1, 2, 2, 1, 0] = some [2, 2, 2, 0, 2, 0, 0] :=
  specInv_mirror_7 [1, 0, 1, 2, 2, 1, 0] [0, 1, 2, 1, 1, 1, 0] [2, 2, 2, 2, 0, 0, 1] [1, 1, 1, 0, 1, 0, 0] [2, 2, 2, 0, 2, 0, 0] demoR1_1012210 demoR2_1012210 demoC_1012210 demoM_1012210 demoMir_1012210

theorem demoR1_2012210 : invRung 7 5 20 [2, 0, 1, 2, 2, 1, 0] [2, 0, 1, 2, 2, 1, 0] 1 2 false = ([2, 0, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_2012210 : invRung 7 5 20 [2, 0, 1, 2, 2, 1, 0] [2, 0, 2, 2, 0, 2, 1] 3 1 true = ([0, 2, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_2012210 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 0, 2] = [1, 0, 2, 2, 2, 1, 1] := by
  decide

theorem demoM_2012210 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 1, 1] [2, 0, 1, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012210 : mirrorTrits [1, 0, 2, 2, 2, 1, 1] = [2, 0, 1, 1, 1, 2, 2] := by
  decide

theorem demoInv_2012210 : specInv 7 5 20 [2, 0, 1, 2, 2, 1, 0] = some [2, 0, 1, 1, 1, 2, 2] :=
  specInv_mirror_7 [2, 0, 1, 2, 2, 1, 0] [2, 0, 2, 2, 0, 2, 1] [0, 2, 1, 1, 1, 0, 2] [1, 0, 2, 2, 2, 1, 1] [2, 0, 1, 1, 1, 2, 2] demoR1_2012210 demoR2_2012210 demoC_2012210 demoM_2012210 demoMir_2012210

theorem demoR1_0112210 : invRung 7 5 20 [0, 1, 1, 2, 2, 1, 0] [0, 1, 1, 2, 2, 1, 0] 1 2 false = ([1, 0, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_0112210 : invRung 7 5 20 [0, 1, 1, 2, 2, 1, 0] [1, 0, 1, 1, 1, 0, 1] 3 1 true = ([1, 0, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_0112210 : fieldCube 7 5 20 [1, 0, 1, 2, 0, 0, 2] = [0, 2, 0, 2, 2, 1, 0] := by
  decide

theorem demoM_0112210 : fieldMul 7 5 20 [0, 2, 0, 2, 2, 1, 0] [0, 1, 1, 2, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0112210 : specInv 7 5 20 [0, 1, 1, 2, 2, 1, 0] = some [0, 2, 0, 2, 2, 1, 0] :=
  specInv_white_7 [0, 1, 1, 2, 2, 1, 0] [1, 0, 1, 1, 1, 0, 1] [1, 0, 1, 2, 0, 0, 2] [0, 2, 0, 2, 2, 1, 0] demoR1_0112210 demoR2_0112210 demoC_0112210 demoM_0112210

theorem demoR1_1112210 : invRung 7 5 20 [1, 1, 1, 2, 2, 1, 0] [1, 1, 1, 2, 2, 1, 0] 1 2 false = ([0, 1, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_1112210 : invRung 7 5 20 [1, 1, 1, 2, 2, 1, 0] [0, 1, 2, 1, 0, 2, 1] 3 1 true = ([1, 2, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1112210 : fieldCube 7 5 20 [1, 2, 0, 2, 0, 1, 0] = [1, 1, 0, 2, 1, 0, 2] := by
  decide

theorem demoM_1112210 : fieldMul 7 5 20 [1, 1, 0, 2, 1, 0, 2] [1, 1, 1, 2, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1112210 : specInv 7 5 20 [1, 1, 1, 2, 2, 1, 0] = some [1, 1, 0, 2, 1, 0, 2] :=
  specInv_white_7 [1, 1, 1, 2, 2, 1, 0] [0, 1, 2, 1, 0, 2, 1] [1, 2, 0, 2, 0, 1, 0] [1, 1, 0, 2, 1, 0, 2] demoR1_1112210 demoR2_1112210 demoC_1112210 demoM_1112210

theorem demoR1_2112210 : invRung 7 5 20 [2, 1, 1, 2, 2, 1, 0] [2, 1, 1, 2, 2, 1, 0] 1 2 false = ([0, 2, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_2112210 : invRung 7 5 20 [2, 1, 1, 2, 2, 1, 0] [0, 2, 2, 2, 1, 2, 1] 3 1 true = ([0, 1, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_2112210 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 2, 2] = [2, 2, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_2112210 : fieldMul 7 5 20 [2, 2, 0, 1, 1, 2, 1] [2, 1, 1, 2, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2112210 : specInv 7 5 20 [2, 1, 1, 2, 2, 1, 0] = some [2, 2, 0, 1, 1, 2, 1] :=
  specInv_white_7 [2, 1, 1, 2, 2, 1, 0] [0, 2, 2, 2, 1, 2, 1] [0, 1, 0, 0, 1, 2, 2] [2, 2, 0, 1, 1, 2, 1] demoR1_2112210 demoR2_2112210 demoC_2112210 demoM_2112210

theorem demoR1_0212210 : invRung 7 5 20 [0, 2, 1, 2, 2, 1, 0] [0, 2, 1, 2, 2, 1, 0] 1 2 false = ([2, 1, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_0212210 : invRung 7 5 20 [0, 2, 1, 2, 2, 1, 0] [2, 1, 0, 1, 2, 2, 1] 3 1 true = ([1, 2, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_0212210 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 1, 0] = [0, 0, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_0212210 : fieldMul 7 5 20 [0, 0, 2, 1, 1, 1, 2] [0, 2, 1, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212210 : mirrorTrits [0, 0, 2, 1, 1, 1, 2] = [0, 0, 1, 2, 2, 2, 1] := by
  decide

theorem demoInv_0212210 : specInv 7 5 20 [0, 2, 1, 2, 2, 1, 0] = some [0, 0, 1, 2, 2, 2, 1] :=
  specInv_mirror_7 [0, 2, 1, 2, 2, 1, 0] [2, 1, 0, 1, 2, 2, 1] [1, 2, 1, 1, 2, 1, 0] [0, 0, 2, 1, 1, 1, 2] [0, 0, 1, 2, 2, 2, 1] demoR1_0212210 demoR2_0212210 demoC_0212210 demoM_0212210 demoMir_0212210

theorem demoR1_1212210 : invRung 7 5 20 [1, 2, 1, 2, 2, 1, 0] [1, 2, 1, 2, 2, 1, 0] 1 2 false = ([0, 0, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_1212210 : invRung 7 5 20 [1, 2, 1, 2, 2, 1, 0] [0, 0, 2, 0, 2, 0, 1] 3 1 true = ([0, 2, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_1212210 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 0, 2] = [1, 2, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_1212210 : fieldMul 7 5 20 [1, 2, 2, 1, 2, 0, 0] [1, 2, 1, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212210 : mirrorTrits [1, 2, 2, 1, 2, 0, 0] = [2, 1, 1, 2, 1, 0, 0] := by
  decide

theorem demoInv_1212210 : specInv 7 5 20 [1, 2, 1, 2, 2, 1, 0] = some [2, 1, 1, 2, 1, 0, 0] :=
  specInv_mirror_7 [1, 2, 1, 2, 2, 1, 0] [0, 0, 2, 0, 2, 0, 1] [0, 2, 1, 1, 0, 0, 2] [1, 2, 2, 1, 2, 0, 0] [2, 1, 1, 2, 1, 0, 0] demoR1_1212210 demoR2_1212210 demoC_1212210 demoM_1212210 demoMir_1212210

theorem demoR1_2212210 : invRung 7 5 20 [2, 2, 1, 2, 2, 1, 0] [2, 2, 1, 2, 2, 1, 0] 1 2 false = ([1, 1, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_2212210 : invRung 7 5 20 [2, 2, 1, 2, 2, 1, 0] [1, 1, 2, 2, 1, 1, 1] 3 1 true = ([1, 1, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_2212210 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 0, 0] = [1, 2, 0, 0, 0, 2, 0] := by
  decide

theorem demoM_2212210 : fieldMul 7 5 20 [1, 2, 0, 0, 0, 2, 0] [2, 2, 1, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212210 : mirrorTrits [1, 2, 0, 0, 0, 2, 0] = [2, 1, 0, 0, 0, 1, 0] := by
  decide

theorem demoInv_2212210 : specInv 7 5 20 [2, 2, 1, 2, 2, 1, 0] = some [2, 1, 0, 0, 0, 1, 0] :=
  specInv_mirror_7 [2, 2, 1, 2, 2, 1, 0] [1, 1, 2, 2, 1, 1, 1] [1, 1, 1, 0, 2, 0, 0] [1, 2, 0, 0, 0, 2, 0] [2, 1, 0, 0, 0, 1, 0] demoR1_2212210 demoR2_2212210 demoC_2212210 demoM_2212210 demoMir_2212210

theorem demoR1_0022210 : invRung 7 5 20 [0, 0, 2, 2, 2, 1, 0] [0, 0, 2, 2, 2, 1, 0] 1 2 false = ([1, 2, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0022210 : invRung 7 5 20 [0, 0, 2, 2, 2, 1, 0] [1, 2, 1, 0, 1, 1, 1] 3 1 true = ([0, 2, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_0022210 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 0, 1] = [1, 2, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_0022210 : fieldMul 7 5 20 [1, 2, 0, 1, 1, 0, 0] [0, 0, 2, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022210 : mirrorTrits [1, 2, 0, 1, 1, 0, 0] = [2, 1, 0, 2, 2, 0, 0] := by
  decide

theorem demoInv_0022210 : specInv 7 5 20 [0, 0, 2, 2, 2, 1, 0] = some [2, 1, 0, 2, 2, 0, 0] :=
  specInv_mirror_7 [0, 0, 2, 2, 2, 1, 0] [1, 2, 1, 0, 1, 1, 1] [0, 2, 1, 1, 1, 0, 1] [1, 2, 0, 1, 1, 0, 0] [2, 1, 0, 2, 2, 0, 0] demoR1_0022210 demoR2_0022210 demoC_0022210 demoM_0022210 demoMir_0022210

theorem demoR1_1022210 : invRung 7 5 20 [1, 0, 2, 2, 2, 1, 0] [1, 0, 2, 2, 2, 1, 0] 1 2 false = ([2, 0, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_1022210 : invRung 7 5 20 [1, 0, 2, 2, 2, 1, 0] [2, 0, 1, 2, 2, 0, 0] 3 1 true = ([0, 2, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_1022210 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 2, 2] = [2, 2, 0, 2, 1, 2, 0] := by
  decide

theorem demoM_1022210 : fieldMul 7 5 20 [2, 2, 0, 2, 1, 2, 0] [1, 0, 2, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1022210 : mirrorTrits [2, 2, 0, 2, 1, 2, 0] = [1, 1, 0, 1, 2, 1, 0] := by
  decide

theorem demoInv_1022210 : specInv 7 5 20 [1, 0, 2, 2, 2, 1, 0] = some [1, 1, 0, 1, 2, 1, 0] :=
  specInv_mirror_7 [1, 0, 2, 2, 2, 1, 0] [2, 0, 1, 2, 2, 0, 0] [0, 2, 2, 0, 1, 2, 2] [2, 2, 0, 2, 1, 2, 0] [1, 1, 0, 1, 2, 1, 0] demoR1_1022210 demoR2_1022210 demoC_1022210 demoM_1022210 demoMir_1022210

theorem demoR1_2022210 : invRung 7 5 20 [2, 0, 2, 2, 2, 1, 0] [2, 0, 2, 2, 2, 1, 0] 1 2 false = ([2, 1, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_2022210 : invRung 7 5 20 [2, 0, 2, 2, 2, 1, 0] [2, 1, 1, 2, 1, 0, 0] 3 1 true = ([1, 2, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_2022210 : fieldCube 7 5 20 [1, 2, 1, 0, 0, 0, 1] = [1, 1, 2, 0, 1, 1, 2] := by
  decide

theorem demoM_2022210 : fieldMul 7 5 20 [1, 1, 2, 0, 1, 1, 2] [2, 0, 2, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022210 : mirrorTrits [1, 1, 2, 0, 1, 1, 2] = [2, 2, 1, 0, 2, 2, 1] := by
  decide

theorem demoInv_2022210 : specInv 7 5 20 [2, 0, 2, 2, 2, 1, 0] = some [2, 2, 1, 0, 2, 2, 1] :=
  specInv_mirror_7 [2, 0, 2, 2, 2, 1, 0] [2, 1, 1, 2, 1, 0, 0] [1, 2, 1, 0, 0, 0, 1] [1, 1, 2, 0, 1, 1, 2] [2, 2, 1, 0, 2, 2, 1] demoR1_2022210 demoR2_2022210 demoC_2022210 demoM_2022210 demoMir_2022210

theorem demoR1_0122210 : invRung 7 5 20 [0, 1, 2, 2, 2, 1, 0] [0, 1, 2, 2, 2, 1, 0] 1 2 false = ([1, 2, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0122210 : invRung 7 5 20 [0, 1, 2, 2, 2, 1, 0] [1, 2, 0, 1, 1, 1, 2] 3 1 true = ([0, 1, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0122210 : fieldCube 7 5 20 [0, 1, 0, 1, 2, 2, 2] = [0, 0, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_0122210 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 1, 2] [0, 1, 2, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122210 : mirrorTrits [0, 0, 1, 2, 1, 1, 2] = [0, 0, 2, 1, 2, 2, 1] := by
  decide

theorem demoInv_0122210 : specInv 7 5 20 [0, 1, 2, 2, 2, 1, 0] = some [0, 0, 2, 1, 2, 2, 1] :=
  specInv_mirror_7 [0, 1, 2, 2, 2, 1, 0] [1, 2, 0, 1, 1, 1, 2] [0, 1, 0, 1, 2, 2, 2] [0, 0, 1, 2, 1, 1, 2] [0, 0, 2, 1, 2, 2, 1] demoR1_0122210 demoR2_0122210 demoC_0122210 demoM_0122210 demoMir_0122210

theorem demoR1_1122210 : invRung 7 5 20 [1, 1, 2, 2, 2, 1, 0] [1, 1, 2, 2, 2, 1, 0] 1 2 false = ([1, 2, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_1122210 : invRung 7 5 20 [1, 1, 2, 2, 2, 1, 0] [1, 2, 2, 0, 2, 1, 2] 3 1 true = ([0, 1, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_1122210 : fieldCube 7 5 20 [0, 1, 2, 1, 2, 1, 1] = [2, 1, 1, 1, 2, 2, 1] := by
  decide

theorem demoM_1122210 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 2, 1] [1, 1, 2, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122210 : mirrorTrits [2, 1, 1, 1, 2, 2, 1] = [1, 2, 2, 2, 1, 1, 2] := by
  decide

theorem demoInv_1122210 : specInv 7 5 20 [1, 1, 2, 2, 2, 1, 0] = some [1, 2, 2, 2, 1, 1, 2] :=
  specInv_mirror_7 [1, 1, 2, 2, 2, 1, 0] [1, 2, 2, 0, 2, 1, 2] [0, 1, 2, 1, 2, 1, 1] [2, 1, 1, 1, 2, 2, 1] [1, 2, 2, 2, 1, 1, 2] demoR1_1122210 demoR2_1122210 demoC_1122210 demoM_1122210 demoMir_1122210

theorem demoR1_2122210 : invRung 7 5 20 [2, 1, 2, 2, 2, 1, 0] [2, 1, 2, 2, 2, 1, 0] 1 2 false = ([2, 1, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_2122210 : invRung 7 5 20 [2, 1, 2, 2, 2, 1, 0] [2, 1, 0, 2, 1, 1, 0] 3 1 true = ([0, 2, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_2122210 : fieldCube 7 5 20 [0, 2, 1, 0, 0, 0, 0] = [0, 0, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_2122210 : fieldMul 7 5 20 [0, 0, 0, 2, 0, 0, 1] [2, 1, 2, 2, 2, 1, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122210 : mirrorTrits [0, 0, 0, 2, 0, 0, 1] = [0, 0, 0, 1, 0, 0, 2] := by
  decide

theorem demoInv_2122210 : specInv 7 5 20 [2, 1, 2, 2, 2, 1, 0] = some [0, 0, 0, 1, 0, 0, 2] :=
  specInv_mirror_7 [2, 1, 2, 2, 2, 1, 0] [2, 1, 0, 2, 1, 1, 0] [0, 2, 1, 0, 0, 0, 0] [0, 0, 0, 2, 0, 0, 1] [0, 0, 0, 1, 0, 0, 2] demoR1_2122210 demoR2_2122210 demoC_2122210 demoM_2122210 demoMir_2122210

theorem demoR1_0222210 : invRung 7 5 20 [0, 2, 2, 2, 2, 1, 0] [0, 2, 2, 2, 2, 1, 0] 1 2 false = ([2, 2, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_0222210 : invRung 7 5 20 [0, 2, 2, 2, 2, 1, 0] [2, 2, 0, 0, 2, 0, 1] 3 1 true = ([2, 2, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0222210 : fieldCube 7 5 20 [2, 2, 0, 1, 1, 2, 2] = [2, 2, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_0222210 : fieldMul 7 5 20 [2, 2, 1, 2, 1, 0, 1] [0, 2, 2, 2, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0222210 : specInv 7 5 20 [0, 2, 2, 2, 2, 1, 0] = some [2, 2, 1, 2, 1, 0, 1] :=
  specInv_white_7 [0, 2, 2, 2, 2, 1, 0] [2, 2, 0, 0, 2, 0, 1] [2, 2, 0, 1, 1, 2, 2] [2, 2, 1, 2, 1, 0, 1] demoR1_0222210 demoR2_0222210 demoC_0222210 demoM_0222210

theorem demoR1_1222210 : invRung 7 5 20 [1, 2, 2, 2, 2, 1, 0] [1, 2, 2, 2, 2, 1, 0] 1 2 false = ([1, 2, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_1222210 : invRung 7 5 20 [1, 2, 2, 2, 2, 1, 0] [1, 2, 1, 0, 2, 0, 0] 3 1 true = ([1, 2, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_1222210 : fieldCube 7 5 20 [1, 2, 2, 1, 0, 1, 0] = [0, 1, 2, 2, 1, 2, 1] := by
  decide

theorem demoM_1222210 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 2, 1] [1, 2, 2, 2, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1222210 : specInv 7 5 20 [1, 2, 2, 2, 2, 1, 0] = some [0, 1, 2, 2, 1, 2, 1] :=
  specInv_white_7 [1, 2, 2, 2, 2, 1, 0] [1, 2, 1, 0, 2, 0, 0] [1, 2, 2, 1, 0, 1, 0] [0, 1, 2, 2, 1, 2, 1] demoR1_1222210 demoR2_1222210 demoC_1222210 demoM_1222210

theorem demoR1_2222210 : invRung 7 5 20 [2, 2, 2, 2, 2, 1, 0] [2, 2, 2, 2, 2, 1, 0] 1 2 false = ([0, 0, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_2222210 : invRung 7 5 20 [2, 2, 2, 2, 2, 1, 0] [0, 0, 0, 2, 0, 2, 0] 3 1 true = ([2, 2, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_2222210 : fieldCube 7 5 20 [2, 2, 0, 2, 2, 0, 2] = [1, 1, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_2222210 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 0, 1] [2, 2, 2, 2, 2, 1, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2222210 : specInv 7 5 20 [2, 2, 2, 2, 2, 1, 0] = some [1, 1, 0, 0, 2, 0, 1] :=
  specInv_white_7 [2, 2, 2, 2, 2, 1, 0] [0, 0, 0, 2, 0, 2, 0] [2, 2, 0, 2, 2, 0, 2] [1, 1, 0, 0, 2, 0, 1] demoR1_2222210 demoR2_2222210 demoC_2222210 demoM_2222210

theorem demoR1_0000020 : invRung 7 5 20 [0, 0, 0, 0, 0, 2, 0] [0, 0, 0, 0, 0, 2, 0] 1 2 false = ([2, 0, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_0000020 : invRung 7 5 20 [0, 0, 0, 0, 0, 2, 0] [2, 0, 0, 2, 1, 1, 0] 3 1 true = ([0, 2, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0000020 : fieldCube 7 5 20 [0, 2, 1, 0, 0, 2, 1] = [2, 0, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_0000020 : fieldMul 7 5 20 [2, 0, 1, 0, 0, 0, 0] [0, 0, 0, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000020 : mirrorTrits [2, 0, 1, 0, 0, 0, 0] = [1, 0, 2, 0, 0, 0, 0] := by
  decide

theorem demoInv_0000020 : specInv 7 5 20 [0, 0, 0, 0, 0, 2, 0] = some [1, 0, 2, 0, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 0, 0, 0, 2, 0] [2, 0, 0, 2, 1, 1, 0] [0, 2, 1, 0, 0, 2, 1] [2, 0, 1, 0, 0, 0, 0] [1, 0, 2, 0, 0, 0, 0] demoR1_0000020 demoR2_0000020 demoC_0000020 demoM_0000020 demoMir_0000020

theorem demoR1_1000020 : invRung 7 5 20 [1, 0, 0, 0, 0, 2, 0] [1, 0, 0, 0, 0, 2, 0] 1 2 false = ([1, 1, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_1000020 : invRung 7 5 20 [1, 0, 0, 0, 0, 2, 0] [1, 1, 1, 2, 0, 2, 2] 3 1 true = ([2, 1, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1000020 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 2, 2] = [0, 2, 2, 1, 1, 1, 1] := by
  decide

theorem demoM_1000020 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 1, 1] [1, 0, 0, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000020 : mirrorTrits [0, 2, 2, 1, 1, 1, 1] = [0, 1, 1, 2, 2, 2, 2] := by
  decide

theorem demoInv_1000020 : specInv 7 5 20 [1, 0, 0, 0, 0, 2, 0] = some [0, 1, 1, 2, 2, 2, 2] :=
  specInv_mirror_7 [1, 0, 0, 0, 0, 2, 0] [1, 1, 1, 2, 0, 2, 2] [2, 1, 0, 2, 1, 2, 2] [0, 2, 2, 1, 1, 1, 1] [0, 1, 1, 2, 2, 2, 2] demoR1_1000020 demoR2_1000020 demoC_1000020 demoM_1000020 demoMir_1000020

theorem demoR1_2000020 : invRung 7 5 20 [2, 0, 0, 0, 0, 2, 0] [2, 0, 0, 0, 0, 2, 0] 1 2 false = ([0, 1, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_2000020 : invRung 7 5 20 [2, 0, 0, 0, 0, 2, 0] [0, 1, 2, 0, 0, 0, 0] 3 1 true = ([0, 0, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_2000020 : fieldCube 7 5 20 [0, 0, 1, 2, 0, 2, 1] = [1, 0, 0, 1, 0, 2, 0] := by
  decide

theorem demoM_2000020 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 2, 0] [2, 0, 0, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000020 : mirrorTrits [1, 0, 0, 1, 0, 2, 0] = [2, 0, 0, 2, 0, 1, 0] := by
  decide

theorem demoInv_2000020 : specInv 7 5 20 [2, 0, 0, 0, 0, 2, 0] = some [2, 0, 0, 2, 0, 1, 0] :=
  specInv_mirror_7 [2, 0, 0, 0, 0, 2, 0] [0, 1, 2, 0, 0, 0, 0] [0, 0, 1, 2, 0, 2, 1] [1, 0, 0, 1, 0, 2, 0] [2, 0, 0, 2, 0, 1, 0] demoR1_2000020 demoR2_2000020 demoC_2000020 demoM_2000020 demoMir_2000020

theorem demoR1_0100020 : invRung 7 5 20 [0, 1, 0, 0, 0, 2, 0] [0, 1, 0, 0, 0, 2, 0] 1 2 false = ([2, 0, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_0100020 : invRung 7 5 20 [0, 1, 0, 0, 0, 2, 0] [2, 0, 0, 0, 2, 0, 2] 3 1 true = ([0, 2, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0100020 : fieldCube 7 5 20 [0, 2, 2, 2, 1, 0, 1] = [2, 2, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_0100020 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 1, 1] [0, 1, 0, 0, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0100020 : specInv 7 5 20 [0, 1, 0, 0, 0, 2, 0] = some [2, 2, 1, 1, 1, 1, 1] :=
  specInv_white_7 [0, 1, 0, 0, 0, 2, 0] [2, 0, 0, 0, 2, 0, 2] [0, 2, 2, 2, 1, 0, 1] [2, 2, 1, 1, 1, 1, 1] demoR1_0100020 demoR2_0100020 demoC_0100020 demoM_0100020

theorem demoR1_1100020 : invRung 7 5 20 [1, 1, 0, 0, 0, 2, 0] [1, 1, 0, 0, 0, 2, 0] 1 2 false = ([2, 0, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_1100020 : invRung 7 5 20 [1, 1, 0, 0, 0, 2, 0] [2, 0, 1, 1, 2, 1, 2] 3 1 true = ([1, 0, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_1100020 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 2, 0] = [0, 2, 2, 0, 2, 2, 2] := by
  decide

theorem demoM_1100020 : fieldMul 7 5 20 [0, 2, 2, 0, 2, 2, 2] [1, 1, 0, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1100020 : mirrorTrits [0, 2, 2, 0, 2, 2, 2] = [0, 1, 1, 0, 1, 1, 1] := by
  decide

theorem demoInv_1100020 : specInv 7 5 20 [1, 1, 0, 0, 0, 2, 0] = some [0, 1, 1, 0, 1, 1, 1] :=
  specInv_mirror_7 [1, 1, 0, 0, 0, 2, 0] [2, 0, 1, 1, 2, 1, 2] [1, 0, 1, 0, 0, 2, 0] [0, 2, 2, 0, 2, 2, 2] [0, 1, 1, 0, 1, 1, 1] demoR1_1100020 demoR2_1100020 demoC_1100020 demoM_1100020 demoMir_1100020

theorem demoR1_2100020 : invRung 7 5 20 [2, 1, 0, 0, 0, 2, 0] [2, 1, 0, 0, 0, 2, 0] 1 2 false = ([1, 1, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_2100020 : invRung 7 5 20 [2, 1, 0, 0, 0, 2, 0] [1, 1, 1, 2, 0, 1, 1] 3 1 true = ([2, 1, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_2100020 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 1, 2] = [1, 1, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_2100020 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 2, 1] [2, 1, 0, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100020 : mirrorTrits [1, 1, 0, 1, 0, 2, 1] = [2, 2, 0, 2, 0, 1, 2] := by
  decide

theorem demoInv_2100020 : specInv 7 5 20 [2, 1, 0, 0, 0, 2, 0] = some [2, 2, 0, 2, 0, 1, 2] :=
  specInv_mirror_7 [2, 1, 0, 0, 0, 2, 0] [1, 1, 1, 2, 0, 1, 1] [2, 1, 2, 1, 1, 1, 2] [1, 1, 0, 1, 0, 2, 1] [2, 2, 0, 2, 0, 1, 2] demoR1_2100020 demoR2_2100020 demoC_2100020 demoM_2100020 demoMir_2100020

theorem demoR1_0200020 : invRung 7 5 20 [0, 2, 0, 0, 0, 2, 0] [0, 2, 0, 0, 0, 2, 0] 1 2 false = ([0, 2, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_0200020 : invRung 7 5 20 [0, 2, 0, 0, 0, 2, 0] [0, 2, 0, 1, 2, 2, 1] 3 1 true = ([2, 2, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_0200020 : fieldCube 7 5 20 [2, 2, 1, 1, 2, 1, 0] = [1, 0, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_0200020 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 1, 2] [0, 2, 0, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200020 : mirrorTrits [1, 0, 2, 1, 1, 1, 2] = [2, 0, 1, 2, 2, 2, 1] := by
  decide

theorem demoInv_0200020 : specInv 7 5 20 [0, 2, 0, 0, 0, 2, 0] = some [2, 0, 1, 2, 2, 2, 1] :=
  specInv_mirror_7 [0, 2, 0, 0, 0, 2, 0] [0, 2, 0, 1, 2, 2, 1] [2, 2, 1, 1, 2, 1, 0] [1, 0, 2, 1, 1, 1, 2] [2, 0, 1, 2, 2, 2, 1] demoR1_0200020 demoR2_0200020 demoC_0200020 demoM_0200020 demoMir_0200020

theorem demoR1_1200020 : invRung 7 5 20 [1, 2, 0, 0, 0, 2, 0] [1, 2, 0, 0, 0, 2, 0] 1 2 false = ([1, 2, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_1200020 : invRung 7 5 20 [1, 2, 0, 0, 0, 2, 0] [1, 2, 1, 1, 2, 2, 0] 3 1 true = ([2, 1, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_1200020 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 1, 0] = [1, 1, 2, 1, 1, 2, 0] := by
  decide

theorem demoM_1200020 : fieldMul 7 5 20 [1, 1, 2, 1, 1, 2, 0] [1, 2, 0, 0, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1200020 : specInv 7 5 20 [1, 2, 0, 0, 0, 2, 0] = some [1, 1, 2, 1, 1, 2, 0] :=
  specInv_white_7 [1, 2, 0, 0, 0, 2, 0] [1, 2, 1, 1, 2, 2, 0] [2, 1, 1, 1, 0, 1, 0] [1, 1, 2, 1, 1, 2, 0] demoR1_1200020 demoR2_1200020 demoC_1200020 demoM_1200020

theorem demoR1_2200020 : invRung 7 5 20 [2, 2, 0, 0, 0, 2, 0] [2, 2, 0, 0, 0, 2, 0] 1 2 false = ([0, 2, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_2200020 : invRung 7 5 20 [2, 2, 0, 0, 0, 2, 0] [0, 2, 0, 0, 0, 0, 1] 3 1 true = ([1, 1, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_2200020 : fieldCube 7 5 20 [1, 1, 2, 2, 0, 0, 1] = [0, 1, 1, 2, 1, 0, 0] := by
  decide

theorem demoM_2200020 : fieldMul 7 5 20 [0, 1, 1, 2, 1, 0, 0] [2, 2, 0, 0, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2200020 : specInv 7 5 20 [2, 2, 0, 0, 0, 2, 0] = some [0, 1, 1, 2, 1, 0, 0] :=
  specInv_white_7 [2, 2, 0, 0, 0, 2, 0] [0, 2, 0, 0, 0, 0, 1] [1, 1, 2, 2, 0, 0, 1] [0, 1, 1, 2, 1, 0, 0] demoR1_2200020 demoR2_2200020 demoC_2200020 demoM_2200020

theorem demoR1_0010020 : invRung 7 5 20 [0, 0, 1, 0, 0, 2, 0] [0, 0, 1, 0, 0, 2, 0] 1 2 false = ([2, 1, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_0010020 : invRung 7 5 20 [0, 0, 1, 0, 0, 2, 0] [2, 1, 1, 0, 2, 0, 1] 3 1 true = ([0, 0, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0010020 : fieldCube 7 5 20 [0, 0, 1, 0, 0, 0, 1] = [0, 1, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_0010020 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 1, 2] [0, 0, 1, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010020 : mirrorTrits [0, 1, 2, 1, 1, 1, 2] = [0, 2, 1, 2, 2, 2, 1] := by
  decide

theorem demoInv_0010020 : specInv 7 5 20 [0, 0, 1, 0, 0, 2, 0] = some [0, 2, 1, 2, 2, 2, 1] :=
  specInv_mirror_7 [0, 0, 1, 0, 0, 2, 0] [2, 1, 1, 0, 2, 0, 1] [0, 0, 1, 0, 0, 0, 1] [0, 1, 2, 1, 1, 1, 2] [0, 2, 1, 2, 2, 2, 1] demoR1_0010020 demoR2_0010020 demoC_0010020 demoM_0010020 demoMir_0010020

theorem demoR1_1010020 : invRung 7 5 20 [1, 0, 1, 0, 0, 2, 0] [1, 0, 1, 0, 0, 2, 0] 1 2 false = ([2, 1, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_1010020 : invRung 7 5 20 [1, 0, 1, 0, 0, 2, 0] [2, 1, 1, 0, 1, 1, 1] 3 1 true = ([1, 0, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_1010020 : fieldCube 7 5 20 [1, 0, 0, 2, 1, 1, 1] = [1, 0, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_1010020 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 2, 1] [1, 0, 1, 0, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1010020 : specInv 7 5 20 [1, 0, 1, 0, 0, 2, 0] = some [1, 0, 2, 2, 2, 2, 1] :=
  specInv_white_7 [1, 0, 1, 0, 0, 2, 0] [2, 1, 1, 0, 1, 1, 1] [1, 0, 0, 2, 1, 1, 1] [1, 0, 2, 2, 2, 2, 1] demoR1_1010020 demoR2_1010020 demoC_1010020 demoM_1010020

theorem demoR1_2010020 : invRung 7 5 20 [2, 0, 1, 0, 0, 2, 0] [2, 0, 1, 0, 0, 2, 0] 1 2 false = ([2, 2, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_2010020 : invRung 7 5 20 [2, 0, 1, 0, 0, 2, 0] [2, 2, 1, 0, 0, 1, 1] 3 1 true = ([1, 2, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_2010020 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 2, 0] = [2, 1, 1, 1, 2, 0, 2] := by
  decide

theorem demoM_2010020 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 0, 2] [2, 0, 1, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010020 : mirrorTrits [2, 1, 1, 1, 2, 0, 2] = [1, 2, 2, 2, 1, 0, 1] := by
  decide

theorem demoInv_2010020 : specInv 7 5 20 [2, 0, 1, 0, 0, 2, 0] = some [1, 2, 2, 2, 1, 0, 1] :=
  specInv_mirror_7 [2, 0, 1, 0, 0, 2, 0] [2, 2, 1, 0, 0, 1, 1] [1, 2, 2, 2, 2, 2, 0] [2, 1, 1, 1, 2, 0, 2] [1, 2, 2, 2, 1, 0, 1] demoR1_2010020 demoR2_2010020 demoC_2010020 demoM_2010020 demoMir_2010020

theorem demoR1_0110020 : invRung 7 5 20 [0, 1, 1, 0, 0, 2, 0] [0, 1, 1, 0, 0, 2, 0] 1 2 false = ([0, 2, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_0110020 : invRung 7 5 20 [0, 1, 1, 0, 0, 2, 0] [0, 2, 0, 1, 0, 1, 2] 3 1 true = ([1, 1, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_0110020 : fieldCube 7 5 20 [1, 1, 0, 1, 1, 1, 1] = [0, 0, 1, 0, 2, 1, 1] := by
  decide

theorem demoM_0110020 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 1, 1] [0, 1, 1, 0, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0110020 : specInv 7 5 20 [0, 1, 1, 0, 0, 2, 0] = some [0, 0, 1, 0, 2, 1, 1] :=
  specInv_white_7 [0, 1, 1, 0, 0, 2, 0] [0, 2, 0, 1, 0, 1, 2] [1, 1, 0, 1, 1, 1, 1] [0, 0, 1, 0, 2, 1, 1] demoR1_0110020 demoR2_0110020 demoC_0110020 demoM_0110020

theorem demoR1_1110020 : invRung 7 5 20 [1, 1, 1, 0, 0, 2, 0] [1, 1, 1, 0, 0, 2, 0] 1 2 false = ([1, 0, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1110020 : invRung 7 5 20 [1, 1, 1, 0, 0, 2, 0] [1, 0, 1, 1, 1, 0, 2] 3 1 true = ([2, 1, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1110020 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 2, 1] = [2, 0, 2, 2, 0, 1, 1] := by
  decide

theorem demoM_1110020 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 1, 1] [1, 1, 1, 0, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1110020 : specInv 7 5 20 [1, 1, 1, 0, 0, 2, 0] = some [2, 0, 2, 2, 0, 1, 1] :=
  specInv_white_7 [1, 1, 1, 0, 0, 2, 0] [1, 0, 1, 1, 1, 0, 2] [2, 1, 2, 1, 0, 2, 1] [2, 0, 2, 2, 0, 1, 1] demoR1_1110020 demoR2_1110020 demoC_1110020 demoM_1110020

theorem demoR1_2110020 : invRung 7 5 20 [2, 1, 1, 0, 0, 2, 0] [2, 1, 1, 0, 0, 2, 0] 1 2 false = ([1, 1, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2110020 : invRung 7 5 20 [2, 1, 1, 0, 0, 2, 0] [1, 1, 1, 0, 2, 0, 2] 3 1 true = ([2, 2, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_2110020 : fieldCube 7 5 20 [2, 2, 0, 0, 2, 1, 0] = [0, 0, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_2110020 : fieldMul 7 5 20 [0, 0, 1, 1, 1, 0, 1] [2, 1, 1, 0, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2110020 : specInv 7 5 20 [2, 1, 1, 0, 0, 2, 0] = some [0, 0, 1, 1, 1, 0, 1] :=
  specInv_white_7 [2, 1, 1, 0, 0, 2, 0] [1, 1, 1, 0, 2, 0, 2] [2, 2, 0, 0, 2, 1, 0] [0, 0, 1, 1, 1, 0, 1] demoR1_2110020 demoR2_2110020 demoC_2110020 demoM_2110020

theorem demoR1_0210020 : invRung 7 5 20 [0, 2, 1, 0, 0, 2, 0] [0, 2, 1, 0, 0, 2, 0] 1 2 false = ([0, 1, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0210020 : invRung 7 5 20 [0, 2, 1, 0, 0, 2, 0] [0, 1, 0, 2, 0, 0, 0] 3 1 true = ([0, 0, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_0210020 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 0, 2] = [1, 1, 2, 1, 2, 2, 1] := by
  decide

theorem demoM_0210020 : fieldMul 7 5 20 [1, 1, 2, 1, 2, 2, 1] [0, 2, 1, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210020 : mirrorTrits [1, 1, 2, 1, 2, 2, 1] = [2, 2, 1, 2, 1, 1, 2] := by
  decide

theorem demoInv_0210020 : specInv 7 5 20 [0, 2, 1, 0, 0, 2, 0] = some [2, 2, 1, 2, 1, 1, 2] :=
  specInv_mirror_7 [0, 2, 1, 0, 0, 2, 0] [0, 1, 0, 2, 0, 0, 0] [0, 0, 0, 1, 2, 0, 2] [1, 1, 2, 1, 2, 2, 1] [2, 2, 1, 2, 1, 1, 2] demoR1_0210020 demoR2_0210020 demoC_0210020 demoM_0210020 demoMir_0210020

theorem demoR1_1210020 : invRung 7 5 20 [1, 2, 1, 0, 0, 2, 0] [1, 2, 1, 0, 0, 2, 0] 1 2 false = ([2, 1, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1210020 : invRung 7 5 20 [1, 2, 1, 0, 0, 2, 0] [2, 1, 2, 0, 2, 2, 1] 3 1 true = ([2, 1, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1210020 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 1, 1] = [1, 2, 1, 2, 2, 0, 1] := by
  decide

theorem demoM_1210020 : fieldMul 7 5 20 [1, 2, 1, 2, 2, 0, 1] [1, 2, 1, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1210020 : mirrorTrits [1, 2, 1, 2, 2, 0, 1] = [2, 1, 2, 1, 1, 0, 2] := by
  decide

theorem demoInv_1210020 : specInv 7 5 20 [1, 2, 1, 0, 0, 2, 0] = some [2, 1, 2, 1, 1, 0, 2] :=
  specInv_mirror_7 [1, 2, 1, 0, 0, 2, 0] [2, 1, 2, 0, 2, 2, 1] [2, 1, 1, 1, 0, 1, 1] [1, 2, 1, 2, 2, 0, 1] [2, 1, 2, 1, 1, 0, 2] demoR1_1210020 demoR2_1210020 demoC_1210020 demoM_1210020 demoMir_1210020

theorem demoR1_2210020 : invRung 7 5 20 [2, 2, 1, 0, 0, 2, 0] [2, 2, 1, 0, 0, 2, 0] 1 2 false = ([2, 0, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2210020 : invRung 7 5 20 [2, 2, 1, 0, 0, 2, 0] [2, 0, 2, 2, 1, 1, 2] 3 1 true = ([1, 1, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_2210020 : fieldCube 7 5 20 [1, 1, 2, 2, 1, 0, 0] = [0, 1, 2, 2, 0, 0, 0] := by
  decide

theorem demoM_2210020 : fieldMul 7 5 20 [0, 1, 2, 2, 0, 0, 0] [2, 2, 1, 0, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2210020 : specInv 7 5 20 [2, 2, 1, 0, 0, 2, 0] = some [0, 1, 2, 2, 0, 0, 0] :=
  specInv_white_7 [2, 2, 1, 0, 0, 2, 0] [2, 0, 2, 2, 1, 1, 2] [1, 1, 2, 2, 1, 0, 0] [0, 1, 2, 2, 0, 0, 0] demoR1_2210020 demoR2_2210020 demoC_2210020 demoM_2210020

theorem demoR1_0020020 : invRung 7 5 20 [0, 0, 2, 0, 0, 2, 0] [0, 0, 2, 0, 0, 2, 0] 1 2 false = ([2, 1, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_0020020 : invRung 7 5 20 [0, 0, 2, 0, 0, 2, 0] [2, 1, 0, 0, 1, 0, 1] 3 1 true = ([1, 2, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_0020020 : fieldCube 7 5 20 [1, 2, 0, 1, 2, 2, 0] = [1, 1, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_0020020 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 2, 0] [0, 0, 2, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020020 : mirrorTrits [1, 1, 0, 1, 2, 2, 0] = [2, 2, 0, 2, 1, 1, 0] := by
  decide

theorem demoInv_0020020 : specInv 7 5 20 [0, 0, 2, 0, 0, 2, 0] = some [2, 2, 0, 2, 1, 1, 0] :=
  specInv_mirror_7 [0, 0, 2, 0, 0, 2, 0] [2, 1, 0, 0, 1, 0, 1] [1, 2, 0, 1, 2, 2, 0] [1, 1, 0, 1, 2, 2, 0] [2, 2, 0, 2, 1, 1, 0] demoR1_0020020 demoR2_0020020 demoC_0020020 demoM_0020020 demoMir_0020020

theorem demoR1_1020020 : invRung 7 5 20 [1, 0, 2, 0, 0, 2, 0] [1, 0, 2, 0, 0, 2, 0] 1 2 false = ([2, 0, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_1020020 : invRung 7 5 20 [1, 0, 2, 0, 0, 2, 0] [2, 0, 0, 0, 0, 1, 1] 3 1 true = ([2, 0, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_1020020 : fieldCube 7 5 20 [2, 0, 1, 1, 0, 0, 2] = [0, 2, 2, 2, 2, 0, 0] := by
  decide

theorem demoM_1020020 : fieldMul 7 5 20 [0, 2, 2, 2, 2, 0, 0] [1, 0, 2, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020020 : mirrorTrits [0, 2, 2, 2, 2, 0, 0] = [0, 1, 1, 1, 1, 0, 0] := by
  decide

theorem demoInv_1020020 : specInv 7 5 20 [1, 0, 2, 0, 0, 2, 0] = some [0, 1, 1, 1, 1, 0, 0] :=
  specInv_mirror_7 [1, 0, 2, 0, 0, 2, 0] [2, 0, 0, 0, 0, 1, 1] [2, 0, 1, 1, 0, 0, 2] [0, 2, 2, 2, 2, 0, 0] [0, 1, 1, 1, 1, 0, 0] demoR1_1020020 demoR2_1020020 demoC_1020020 demoM_1020020 demoMir_1020020

theorem demoR1_2020020 : invRung 7 5 20 [2, 0, 2, 0, 0, 2, 0] [2, 0, 2, 0, 0, 2, 0] 1 2 false = ([2, 2, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_2020020 : invRung 7 5 20 [2, 0, 2, 0, 0, 2, 0] [2, 2, 0, 2, 1, 0, 2] 3 1 true = ([0, 0, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2020020 : fieldCube 7 5 20 [0, 0, 2, 0, 1, 0, 0] = [0, 1, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_2020020 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 1, 0] [2, 0, 2, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020020 : mirrorTrits [0, 1, 0, 1, 0, 1, 0] = [0, 2, 0, 2, 0, 2, 0] := by
  decide

theorem demoInv_2020020 : specInv 7 5 20 [2, 0, 2, 0, 0, 2, 0] = some [0, 2, 0, 2, 0, 2, 0] :=
  specInv_mirror_7 [2, 0, 2, 0, 0, 2, 0] [2, 2, 0, 2, 1, 0, 2] [0, 0, 2, 0, 1, 0, 0] [0, 1, 0, 1, 0, 1, 0] [0, 2, 0, 2, 0, 2, 0] demoR1_2020020 demoR2_2020020 demoC_2020020 demoM_2020020 demoMir_2020020

theorem demoR1_0120020 : invRung 7 5 20 [0, 1, 2, 0, 0, 2, 0] [0, 1, 2, 0, 0, 2, 0] 1 2 false = ([1, 2, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_0120020 : invRung 7 5 20 [0, 1, 2, 0, 0, 2, 0] [1, 2, 0, 0, 1, 2, 0] 3 1 true = ([2, 0, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0120020 : fieldCube 7 5 20 [2, 0, 0, 2, 1, 1, 2] = [2, 1, 1, 0, 0, 0, 2] := by
  decide

theorem demoM_0120020 : fieldMul 7 5 20 [2, 1, 1, 0, 0, 0, 2] [0, 1, 2, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0120020 : mirrorTrits [2, 1, 1, 0, 0, 0, 2] = [1, 2, 2, 0, 0, 0, 1] := by
  decide

theorem demoInv_0120020 : specInv 7 5 20 [0, 1, 2, 0, 0, 2, 0] = some [1, 2, 2, 0, 0, 0, 1] :=
  specInv_mirror_7 [0, 1, 2, 0, 0, 2, 0] [1, 2, 0, 0, 1, 2, 0] [2, 0, 0, 2, 1, 1, 2] [2, 1, 1, 0, 0, 0, 2] [1, 2, 2, 0, 0, 0, 1] demoR1_0120020 demoR2_0120020 demoC_0120020 demoM_0120020 demoMir_0120020

theorem demoR1_1120020 : invRung 7 5 20 [1, 1, 2, 0, 0, 2, 0] [1, 1, 2, 0, 0, 2, 0] 1 2 false = ([2, 1, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_1120020 : invRung 7 5 20 [1, 1, 2, 0, 0, 2, 0] [2, 1, 2, 2, 0, 2, 2] 3 1 true = ([0, 2, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_1120020 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 1, 0] = [0, 2, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_1120020 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 1, 1] [1, 1, 2, 0, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1120020 : specInv 7 5 20 [1, 1, 2, 0, 0, 2, 0] = some [0, 2, 0, 0, 1, 1, 1] :=
  specInv_white_7 [1, 1, 2, 0, 0, 2, 0] [2, 1, 2, 2, 0, 2, 2] [0, 2, 1, 2, 1, 1, 0] [0, 2, 0, 0, 1, 1, 1] demoR1_1120020 demoR2_1120020 demoC_1120020 demoM_1120020

theorem demoR1_2120020 : invRung 7 5 20 [2, 1, 2, 0, 0, 2, 0] [2, 1, 2, 0, 0, 2, 0] 1 2 false = ([2, 2, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_2120020 : invRung 7 5 20 [2, 1, 2, 0, 0, 2, 0] [2, 2, 0, 2, 1, 2, 2] 3 1 true = ([1, 2, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_2120020 : fieldCube 7 5 20 [1, 2, 0, 0, 0, 2, 2] = [0, 1, 0, 1, 1, 1, 0] := by
  decide

theorem demoM_2120020 : fieldMul 7 5 20 [0, 1, 0, 1, 1, 1, 0] [2, 1, 2, 0, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2120020 : specInv 7 5 20 [2, 1, 2, 0, 0, 2, 0] = some [0, 1, 0, 1, 1, 1, 0] :=
  specInv_white_7 [2, 1, 2, 0, 0, 2, 0] [2, 2, 0, 2, 1, 2, 2] [1, 2, 0, 0, 0, 2, 2] [0, 1, 0, 1, 1, 1, 0] demoR1_2120020 demoR2_2120020 demoC_2120020 demoM_2120020

theorem demoR1_0220020 : invRung 7 5 20 [0, 2, 2, 0, 0, 2, 0] [0, 2, 2, 0, 0, 2, 0] 1 2 false = ([0, 0, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_0220020 : invRung 7 5 20 [0, 2, 2, 0, 0, 2, 0] [0, 0, 2, 0, 0, 0, 2] 3 1 true = ([1, 0, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_0220020 : fieldCube 7 5 20 [1, 0, 2, 2, 0, 2, 2] = [2, 1, 2, 2, 1, 0, 2] := by
  decide

theorem demoM_0220020 : fieldMul 7 5 20 [2, 1, 2, 2, 1, 0, 2] [0, 2, 2, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0220020 : mirrorTrits [2, 1, 2, 2, 1, 0, 2] = [1, 2, 1, 1, 2, 0, 1] := by
  decide

theorem demoInv_0220020 : specInv 7 5 20 [0, 2, 2, 0, 0, 2, 0] = some [1, 2, 1, 1, 2, 0, 1] :=
  specInv_mirror_7 [0, 2, 2, 0, 0, 2, 0] [0, 0, 2, 0, 0, 0, 2] [1, 0, 2, 2, 0, 2, 2] [2, 1, 2, 2, 1, 0, 2] [1, 2, 1, 1, 2, 0, 1] demoR1_0220020 demoR2_0220020 demoC_0220020 demoM_0220020 demoMir_0220020

theorem demoR1_1220020 : invRung 7 5 20 [1, 2, 2, 0, 0, 2, 0] [1, 2, 2, 0, 0, 2, 0] 1 2 false = ([2, 0, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_1220020 : invRung 7 5 20 [1, 2, 2, 0, 0, 2, 0] [2, 0, 0, 2, 1, 1, 1] 3 1 true = ([1, 2, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_1220020 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 1, 2] = [2, 2, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_1220020 : fieldMul 7 5 20 [2, 2, 2, 0, 0, 2, 1] [1, 2, 2, 0, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220020 : mirrorTrits [2, 2, 2, 0, 0, 2, 1] = [1, 1, 1, 0, 0, 1, 2] := by
  decide

theorem demoInv_1220020 : specInv 7 5 20 [1, 2, 2, 0, 0, 2, 0] = some [1, 1, 1, 0, 0, 1, 2] :=
  specInv_mirror_7 [1, 2, 2, 0, 0, 2, 0] [2, 0, 0, 2, 1, 1, 1] [1, 2, 1, 0, 2, 1, 2] [2, 2, 2, 0, 0, 2, 1] [1, 1, 1, 0, 0, 1, 2] demoR1_1220020 demoR2_1220020 demoC_1220020 demoM_1220020 demoMir_1220020

theorem demoR1_2220020 : invRung 7 5 20 [2, 2, 2, 0, 0, 2, 0] [2, 2, 2, 0, 0, 2, 0] 1 2 false = ([2, 1, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_2220020 : invRung 7 5 20 [2, 2, 2, 0, 0, 2, 0] [2, 1, 2, 1, 1, 1, 1] 3 1 true = ([2, 1, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2220020 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 2, 0] = [2, 1, 0, 0, 2, 2, 1] := by
  decide

theorem demoM_2220020 : fieldMul 7 5 20 [2, 1, 0, 0, 2, 2, 1] [2, 2, 2, 0, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2220020 : specInv 7 5 20 [2, 2, 2, 0, 0, 2, 0] = some [2, 1, 0, 0, 2, 2, 1] :=
  specInv_white_7 [2, 2, 2, 0, 0, 2, 0] [2, 1, 2, 1, 1, 1, 1] [2, 1, 1, 1, 2, 2, 0] [2, 1, 0, 0, 2, 2, 1] demoR1_2220020 demoR2_2220020 demoC_2220020 demoM_2220020

theorem demoR1_0001020 : invRung 7 5 20 [0, 0, 0, 1, 0, 2, 0] [0, 0, 0, 1, 0, 2, 0] 1 2 false = ([1, 1, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_0001020 : invRung 7 5 20 [0, 0, 0, 1, 0, 2, 0] [1, 1, 2, 1, 2, 0, 1] 3 1 true = ([1, 2, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0001020 : fieldCube 7 5 20 [1, 2, 1, 0, 0, 2, 1] = [0, 0, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_0001020 : fieldMul 7 5 20 [0, 0, 1, 0, 0, 0, 0] [0, 0, 0, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001020 : mirrorTrits [0, 0, 1, 0, 0, 0, 0] = [0, 0, 2, 0, 0, 0, 0] := by
  decide

theorem demoInv_0001020 : specInv 7 5 20 [0, 0, 0, 1, 0, 2, 0] = some [0, 0, 2, 0, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 0, 1, 0, 2, 0] [1, 1, 2, 1, 2, 0, 1] [1, 2, 1, 0, 0, 2, 1] [0, 0, 1, 0, 0, 0, 0] [0, 0, 2, 0, 0, 0, 0] demoR1_0001020 demoR2_0001020 demoC_0001020 demoM_0001020 demoMir_0001020

theorem demoR1_1001020 : invRung 7 5 20 [1, 0, 0, 1, 0, 2, 0] [1, 0, 0, 1, 0, 2, 0] 1 2 false = ([0, 0, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1001020 : invRung 7 5 20 [1, 0, 0, 1, 0, 2, 0] [0, 0, 0, 0, 1, 1, 0] 3 1 true = ([2, 1, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_1001020 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 1, 2] = [1, 0, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_1001020 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 1, 0] [1, 0, 0, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1001020 : specInv 7 5 20 [1, 0, 0, 1, 0, 2, 0] = some [1, 0, 0, 0, 0, 1, 0] :=
  specInv_white_7 [1, 0, 0, 1, 0, 2, 0] [0, 0, 0, 0, 1, 1, 0] [2, 1, 2, 1, 0, 1, 2] [1, 0, 0, 0, 0, 1, 0] demoR1_1001020 demoR2_1001020 demoC_1001020 demoM_1001020

theorem demoR1_2001020 : invRung 7 5 20 [2, 0, 0, 1, 0, 2, 0] [2, 0, 0, 1, 0, 2, 0] 1 2 false = ([2, 0, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_2001020 : invRung 7 5 20 [2, 0, 0, 1, 0, 2, 0] [2, 0, 2, 2, 0, 0, 1] 3 1 true = ([2, 2, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_2001020 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 1, 1] = [1, 1, 1, 2, 2, 2, 2] := by
  decide

theorem demoM_2001020 : fieldMul 7 5 20 [1, 1, 1, 2, 2, 2, 2] [2, 0, 0, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2001020 : specInv 7 5 20 [2, 0, 0, 1, 0, 2, 0] = some [1, 1, 1, 2, 2, 2, 2] :=
  specInv_white_7 [2, 0, 0, 1, 0, 2, 0] [2, 0, 2, 2, 0, 0, 1] [2, 2, 0, 1, 2, 1, 1] [1, 1, 1, 2, 2, 2, 2] demoR1_2001020 demoR2_2001020 demoC_2001020 demoM_2001020

theorem demoR1_0101020 : invRung 7 5 20 [0, 1, 0, 1, 0, 2, 0] [0, 1, 0, 1, 0, 2, 0] 1 2 false = ([1, 2, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_0101020 : invRung 7 5 20 [0, 1, 0, 1, 0, 2, 0] [1, 2, 2, 0, 2, 0, 0] 3 1 true = ([0, 1, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0101020 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 2, 1] = [2, 0, 1, 2, 0, 0, 2] := by
  decide

theorem demoM_0101020 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 0, 2] [0, 1, 0, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0101020 : specInv 7 5 20 [0, 1, 0, 1, 0, 2, 0] = some [2, 0, 1, 2, 0, 0, 2] :=
  specInv_white_7 [0, 1, 0, 1, 0, 2, 0] [1, 2, 2, 0, 2, 0, 0] [0, 1, 0, 0, 0, 2, 1] [2, 0, 1, 2, 0, 0, 2] demoR1_0101020 demoR2_0101020 demoC_0101020 demoM_0101020

theorem demoR1_1101020 : invRung 7 5 20 [1, 1, 0, 1, 0, 2, 0] [1, 1, 0, 1, 0, 2, 0] 1 2 false = ([2, 0, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1101020 : invRung 7 5 20 [1, 1, 0, 1, 0, 2, 0] [2, 0, 0, 0, 1, 0, 0] 3 1 true = ([2, 1, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_1101020 : fieldCube 7 5 20 [2, 1, 2, 2, 0, 0, 2] = [1, 2, 0, 0, 2, 1, 1] := by
  decide

theorem demoM_1101020 : fieldMul 7 5 20 [1, 2, 0, 0, 2, 1, 1] [1, 1, 0, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1101020 : mirrorTrits [1, 2, 0, 0, 2, 1, 1] = [2, 1, 0, 0, 1, 2, 2] := by
  decide

theorem demoInv_1101020 : specInv 7 5 20 [1, 1, 0, 1, 0, 2, 0] = some [2, 1, 0, 0, 1, 2, 2] :=
  specInv_mirror_7 [1, 1, 0, 1, 0, 2, 0] [2, 0, 0, 0, 1, 0, 0] [2, 1, 2, 2, 0, 0, 2] [1, 2, 0, 0, 2, 1, 1] [2, 1, 0, 0, 1, 2, 2] demoR1_1101020 demoR2_1101020 demoC_1101020 demoM_1101020 demoMir_1101020

theorem demoR1_2101020 : invRung 7 5 20 [2, 1, 0, 1, 0, 2, 0] [2, 1, 0, 1, 0, 2, 0] 1 2 false = ([2, 1, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2101020 : invRung 7 5 20 [2, 1, 0, 1, 0, 2, 0] [2, 1, 1, 2, 0, 0, 2] 3 1 true = ([1, 0, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_2101020 : fieldCube 7 5 20 [1, 0, 0, 2, 2, 1, 1] = [1, 1, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_2101020 : fieldMul 7 5 20 [1, 1, 2, 0, 2, 0, 2] [2, 1, 0, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101020 : mirrorTrits [1, 1, 2, 0, 2, 0, 2] = [2, 2, 1, 0, 1, 0, 1] := by
  decide

theorem demoInv_2101020 : specInv 7 5 20 [2, 1, 0, 1, 0, 2, 0] = some [2, 2, 1, 0, 1, 0, 1] :=
  specInv_mirror_7 [2, 1, 0, 1, 0, 2, 0] [2, 1, 1, 2, 0, 0, 2] [1, 0, 0, 2, 2, 1, 1] [1, 1, 2, 0, 2, 0, 2] [2, 2, 1, 0, 1, 0, 1] demoR1_2101020 demoR2_2101020 demoC_2101020 demoM_2101020 demoMir_2101020

theorem demoR1_0201020 : invRung 7 5 20 [0, 2, 0, 1, 0, 2, 0] [0, 2, 0, 1, 0, 2, 0] 1 2 false = ([2, 0, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_0201020 : invRung 7 5 20 [0, 2, 0, 1, 0, 2, 0] [2, 0, 2, 0, 0, 1, 0] 3 1 true = ([2, 0, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_0201020 : fieldCube 7 5 20 [2, 0, 1, 2, 1, 2, 2] = [0, 2, 2, 0, 1, 1, 2] := by
  decide

theorem demoM_0201020 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 1, 2] [0, 2, 0, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201020 : mirrorTrits [0, 2, 2, 0, 1, 1, 2] = [0, 1, 1, 0, 2, 2, 1] := by
  decide

theorem demoInv_0201020 : specInv 7 5 20 [0, 2, 0, 1, 0, 2, 0] = some [0, 1, 1, 0, 2, 2, 1] :=
  specInv_mirror_7 [0, 2, 0, 1, 0, 2, 0] [2, 0, 2, 0, 0, 1, 0] [2, 0, 1, 2, 1, 2, 2] [0, 2, 2, 0, 1, 1, 2] [0, 1, 1, 0, 2, 2, 1] demoR1_0201020 demoR2_0201020 demoC_0201020 demoM_0201020 demoMir_0201020

theorem demoR1_1201020 : invRung 7 5 20 [1, 2, 0, 1, 0, 2, 0] [1, 2, 0, 1, 0, 2, 0] 1 2 false = ([2, 1, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_1201020 : invRung 7 5 20 [1, 2, 0, 1, 0, 2, 0] [2, 1, 0, 2, 1, 2, 2] 3 1 true = ([2, 1, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_1201020 : fieldCube 7 5 20 [2, 1, 0, 0, 2, 1, 1] = [0, 1, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_1201020 : fieldMul 7 5 20 [0, 1, 0, 1, 2, 1, 2] [1, 2, 0, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1201020 : specInv 7 5 20 [1, 2, 0, 1, 0, 2, 0] = some [0, 1, 0, 1, 2, 1, 2] :=
  specInv_white_7 [1, 2, 0, 1, 0, 2, 0] [2, 1, 0, 2, 1, 2, 2] [2, 1, 0, 0, 2, 1, 1] [0, 1, 0, 1, 2, 1, 2] demoR1_1201020 demoR2_1201020 demoC_1201020 demoM_1201020

theorem demoR1_2201020 : invRung 7 5 20 [2, 2, 0, 1, 0, 2, 0] [2, 2, 0, 1, 0, 2, 0] 1 2 false = ([0, 1, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_2201020 : invRung 7 5 20 [2, 2, 0, 1, 0, 2, 0] [0, 1, 0, 2, 2, 2, 0] 3 1 true = ([1, 0, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_2201020 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 2, 2] = [2, 0, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_2201020 : fieldMul 7 5 20 [2, 0, 2, 1, 1, 2, 1] [2, 2, 0, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2201020 : specInv 7 5 20 [2, 2, 0, 1, 0, 2, 0] = some [2, 0, 2, 1, 1, 2, 1] :=
  specInv_white_7 [2, 2, 0, 1, 0, 2, 0] [0, 1, 0, 2, 2, 2, 0] [1, 0, 2, 2, 2, 2, 2] [2, 0, 2, 1, 1, 2, 1] demoR1_2201020 demoR2_2201020 demoC_2201020 demoM_2201020

theorem demoR1_0011020 : invRung 7 5 20 [0, 0, 1, 1, 0, 2, 0] [0, 0, 1, 1, 0, 2, 0] 1 2 false = ([1, 2, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_0011020 : invRung 7 5 20 [0, 0, 1, 1, 0, 2, 0] [1, 2, 0, 0, 2, 0, 0] 3 1 true = ([1, 0, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_0011020 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 2, 0] = [2, 1, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_0011020 : fieldMul 7 5 20 [2, 1, 1, 2, 2, 0, 2] [0, 0, 1, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011020 : mirrorTrits [2, 1, 1, 2, 2, 0, 2] = [1, 2, 2, 1, 1, 0, 1] := by
  decide

theorem demoInv_0011020 : specInv 7 5 20 [0, 0, 1, 1, 0, 2, 0] = some [1, 2, 2, 1, 1, 0, 1] :=
  specInv_mirror_7 [0, 0, 1, 1, 0, 2, 0] [1, 2, 0, 0, 2, 0, 0] [1, 0, 2, 2, 2, 2, 0] [2, 1, 1, 2, 2, 0, 2] [1, 2, 2, 1, 1, 0, 1] demoR1_0011020 demoR2_0011020 demoC_0011020 demoM_0011020 demoMir_0011020

theorem demoR1_1011020 : invRung 7 5 20 [1, 0, 1, 1, 0, 2, 0] [1, 0, 1, 1, 0, 2, 0] 1 2 false = ([1, 1, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_1011020 : invRung 7 5 20 [1, 0, 1, 1, 0, 2, 0] [1, 1, 1, 1, 0, 2, 1] 3 1 true = ([1, 1, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_1011020 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 0, 2] = [1, 1, 1, 2, 2, 1, 1] := by
  decide

theorem demoM_1011020 : fieldMul 7 5 20 [1, 1, 1, 2, 2, 1, 1] [1, 0, 1, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1011020 : specInv 7 5 20 [1, 0, 1, 1, 0, 2, 0] = some [1, 1, 1, 2, 2, 1, 1] :=
  specInv_white_7 [1, 0, 1, 1, 0, 2, 0] [1, 1, 1, 1, 0, 2, 1] [1, 1, 0, 0, 2, 0, 2] [1, 1, 1, 2, 2, 1, 1] demoR1_1011020 demoR2_1011020 demoC_1011020 demoM_1011020

theorem demoR1_2011020 : invRung 7 5 20 [2, 0, 1, 1, 0, 2, 0] [2, 0, 1, 1, 0, 2, 0] 1 2 false = ([1, 0, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_2011020 : invRung 7 5 20 [2, 0, 1, 1, 0, 2, 0] [1, 0, 0, 1, 0, 1, 2] 3 1 true = ([1, 0, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_2011020 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 1, 2] = [2, 0, 2, 2, 0, 0, 2] := by
  decide

theorem demoM_2011020 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 0, 2] [2, 0, 1, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011020 : mirrorTrits [2, 0, 2, 2, 0, 0, 2] = [1, 0, 1, 1, 0, 0, 1] := by
  decide

theorem demoInv_2011020 : specInv 7 5 20 [2, 0, 1, 1, 0, 2, 0] = some [1, 0, 1, 1, 0, 0, 1] :=
  specInv_mirror_7 [2, 0, 1, 1, 0, 2, 0] [1, 0, 0, 1, 0, 1, 2] [1, 0, 1, 0, 0, 1, 2] [2, 0, 2, 2, 0, 0, 2] [1, 0, 1, 1, 0, 0, 1] demoR1_2011020 demoR2_2011020 demoC_2011020 demoM_2011020 demoMir_2011020

theorem demoR1_0111020 : invRung 7 5 20 [0, 1, 1, 1, 0, 2, 0] [0, 1, 1, 1, 0, 2, 0] 1 2 false = ([0, 0, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0111020 : invRung 7 5 20 [0, 1, 1, 1, 0, 2, 0] [0, 0, 1, 0, 1, 1, 1] 3 1 true = ([0, 1, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_0111020 : fieldCube 7 5 20 [0, 1, 2, 2, 2, 2, 0] = [1, 1, 1, 0, 2, 0, 2] := by
  decide

theorem demoM_0111020 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 0, 2] [0, 1, 1, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0111020 : specInv 7 5 20 [0, 1, 1, 1, 0, 2, 0] = some [1, 1, 1, 0, 2, 0, 2] :=
  specInv_white_7 [0, 1, 1, 1, 0, 2, 0] [0, 0, 1, 0, 1, 1, 1] [0, 1, 2, 2, 2, 2, 0] [1, 1, 1, 0, 2, 0, 2] demoR1_0111020 demoR2_0111020 demoC_0111020 demoM_0111020

theorem demoR1_1111020 : invRung 7 5 20 [1, 1, 1, 1, 0, 2, 0] [1, 1, 1, 1, 0, 2, 0] 1 2 false = ([2, 0, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_1111020 : invRung 7 5 20 [1, 1, 1, 1, 0, 2, 0] [2, 0, 0, 1, 0, 0, 2] 3 1 true = ([2, 1, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_1111020 : fieldCube 7 5 20 [2, 1, 0, 0, 0, 0, 2] = [2, 2, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_1111020 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 2, 2] [1, 1, 1, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111020 : mirrorTrits [2, 2, 1, 0, 2, 2, 2] = [1, 1, 2, 0, 1, 1, 1] := by
  decide

theorem demoInv_1111020 : specInv 7 5 20 [1, 1, 1, 1, 0, 2, 0] = some [1, 1, 2, 0, 1, 1, 1] :=
  specInv_mirror_7 [1, 1, 1, 1, 0, 2, 0] [2, 0, 0, 1, 0, 0, 2] [2, 1, 0, 0, 0, 0, 2] [2, 2, 1, 0, 2, 2, 2] [1, 1, 2, 0, 1, 1, 1] demoR1_1111020 demoR2_1111020 demoC_1111020 demoM_1111020 demoMir_1111020

theorem demoR1_2111020 : invRung 7 5 20 [2, 1, 1, 1, 0, 2, 0] [2, 1, 1, 1, 0, 2, 0] 1 2 false = ([0, 2, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_2111020 : invRung 7 5 20 [2, 1, 1, 1, 0, 2, 0] [0, 2, 2, 0, 1, 1, 0] 3 1 true = ([2, 0, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_2111020 : fieldCube 7 5 20 [2, 0, 0, 1, 1, 2, 0] = [2, 0, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_2111020 : fieldMul 7 5 20 [2, 0, 0, 1, 2, 1, 2] [2, 1, 1, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2111020 : specInv 7 5 20 [2, 1, 1, 1, 0, 2, 0] = some [2, 0, 0, 1, 2, 1, 2] :=
  specInv_white_7 [2, 1, 1, 1, 0, 2, 0] [0, 2, 2, 0, 1, 1, 0] [2, 0, 0, 1, 1, 2, 0] [2, 0, 0, 1, 2, 1, 2] demoR1_2111020 demoR2_2111020 demoC_2111020 demoM_2111020

theorem demoR1_0211020 : invRung 7 5 20 [0, 2, 1, 1, 0, 2, 0] [0, 2, 1, 1, 0, 2, 0] 1 2 false = ([1, 0, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_0211020 : invRung 7 5 20 [0, 2, 1, 1, 0, 2, 0] [1, 0, 0, 1, 1, 1, 0] 3 1 true = ([1, 2, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0211020 : fieldCube 7 5 20 [1, 2, 1, 2, 0, 1, 1] = [1, 2, 2, 0, 2, 1, 1] := by
  decide

theorem demoM_0211020 : fieldMul 7 5 20 [1, 2, 2, 0, 2, 1, 1] [0, 2, 1, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0211020 : specInv 7 5 20 [0, 2, 1, 1, 0, 2, 0] = some [1, 2, 2, 0, 2, 1, 1] :=
  specInv_white_7 [0, 2, 1, 1, 0, 2, 0] [1, 0, 0, 1, 1, 1, 0] [1, 2, 1, 2, 0, 1, 1] [1, 2, 2, 0, 2, 1, 1] demoR1_0211020 demoR2_0211020 demoC_0211020 demoM_0211020

theorem demoR1_1211020 : invRung 7 5 20 [1, 2, 1, 1, 0, 2, 0] [1, 2, 1, 1, 0, 2, 0] 1 2 false = ([2, 2, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_1211020 : invRung 7 5 20 [1, 2, 1, 1, 0, 2, 0] [2, 2, 0, 0, 0, 2, 2] 3 1 true = ([1, 1, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1211020 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 1, 1] = [0, 2, 1, 2, 2, 0, 0] := by
  decide

theorem demoM_1211020 : fieldMul 7 5 20 [0, 2, 1, 2, 2, 0, 0] [1, 2, 1, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1211020 : mirrorTrits [0, 2, 1, 2, 2, 0, 0] = [0, 1, 2, 1, 1, 0, 0] := by
  decide

theorem demoInv_1211020 : specInv 7 5 20 [1, 2, 1, 1, 0, 2, 0] = some [0, 1, 2, 1, 1, 0, 0] :=
  specInv_mirror_7 [1, 2, 1, 1, 0, 2, 0] [2, 2, 0, 0, 0, 2, 2] [1, 1, 0, 1, 0, 1, 1] [0, 2, 1, 2, 2, 0, 0] [0, 1, 2, 1, 1, 0, 0] demoR1_1211020 demoR2_1211020 demoC_1211020 demoM_1211020 demoMir_1211020

theorem demoR1_2211020 : invRung 7 5 20 [2, 2, 1, 1, 0, 2, 0] [2, 2, 1, 1, 0, 2, 0] 1 2 false = ([1, 2, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_2211020 : invRung 7 5 20 [2, 2, 1, 1, 0, 2, 0] [1, 2, 2, 2, 1, 1, 1] 3 1 true = ([2, 0, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2211020 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 1, 0] = [2, 1, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_2211020 : fieldMul 7 5 20 [2, 1, 0, 0, 1, 0, 0] [2, 2, 1, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2211020 : specInv 7 5 20 [2, 2, 1, 1, 0, 2, 0] = some [2, 1, 0, 0, 1, 0, 0] :=
  specInv_white_7 [2, 2, 1, 1, 0, 2, 0] [1, 2, 2, 2, 1, 1, 1] [2, 0, 1, 2, 0, 1, 0] [2, 1, 0, 0, 1, 0, 0] demoR1_2211020 demoR2_2211020 demoC_2211020 demoM_2211020

theorem demoR1_0021020 : invRung 7 5 20 [0, 0, 2, 1, 0, 2, 0] [0, 0, 2, 1, 0, 2, 0] 1 2 false = ([2, 0, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_0021020 : invRung 7 5 20 [0, 0, 2, 1, 0, 2, 0] [2, 0, 0, 1, 0, 2, 1] 3 1 true = ([0, 2, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_0021020 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 2, 1] = [0, 1, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_0021020 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 2, 2] [0, 0, 2, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021020 : mirrorTrits [0, 1, 2, 1, 0, 2, 2] = [0, 2, 1, 2, 0, 1, 1] := by
  decide

theorem demoInv_0021020 : specInv 7 5 20 [0, 0, 2, 1, 0, 2, 0] = some [0, 2, 1, 2, 0, 1, 1] :=
  specInv_mirror_7 [0, 0, 2, 1, 0, 2, 0] [2, 0, 0, 1, 0, 2, 1] [0, 2, 2, 1, 1, 2, 1] [0, 1, 2, 1, 0, 2, 2] [0, 2, 1, 2, 0, 1, 1] demoR1_0021020 demoR2_0021020 demoC_0021020 demoM_0021020 demoMir_0021020

theorem demoR1_1021020 : invRung 7 5 20 [1, 0, 2, 1, 0, 2, 0] [1, 0, 2, 1, 0, 2, 0] 1 2 false = ([2, 2, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_1021020 : invRung 7 5 20 [1, 0, 2, 1, 0, 2, 0] [2, 2, 2, 1, 0, 2, 0] 3 1 true = ([2, 2, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_1021020 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 0, 2] = [0, 1, 2, 0, 2, 2, 1] := by
  decide

theorem demoM_1021020 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 2, 1] [1, 0, 2, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021020 : mirrorTrits [0, 1, 2, 0, 2, 2, 1] = [0, 2, 1, 0, 1, 1, 2] := by
  decide

theorem demoInv_1021020 : specInv 7 5 20 [1, 0, 2, 1, 0, 2, 0] = some [0, 2, 1, 0, 1, 1, 2] :=
  specInv_mirror_7 [1, 0, 2, 1, 0, 2, 0] [2, 2, 2, 1, 0, 2, 0] [2, 2, 0, 1, 2, 0, 2] [0, 1, 2, 0, 2, 2, 1] [0, 2, 1, 0, 1, 1, 2] demoR1_1021020 demoR2_1021020 demoC_1021020 demoM_1021020 demoMir_1021020

theorem demoR1_2021020 : invRung 7 5 20 [2, 0, 2, 1, 0, 2, 0] [2, 0, 2, 1, 0, 2, 0] 1 2 false = ([2, 0, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_2021020 : invRung 7 5 20 [2, 0, 2, 1, 0, 2, 0] [2, 0, 2, 2, 1, 1, 0] 3 1 true = ([0, 0, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2021020 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 0, 0] = [0, 1, 0, 1, 0, 1, 1] := by
  decide

theorem demoM_2021020 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 1, 1] [2, 0, 2, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021020 : mirrorTrits [0, 1, 0, 1, 0, 1, 1] = [0, 2, 0, 2, 0, 2, 2] := by
  decide

theorem demoInv_2021020 : specInv 7 5 20 [2, 0, 2, 1, 0, 2, 0] = some [0, 2, 0, 2, 0, 2, 2] :=
  specInv_mirror_7 [2, 0, 2, 1, 0, 2, 0] [2, 0, 2, 2, 1, 1, 0] [0, 0, 0, 0, 1, 0, 0] [0, 1, 0, 1, 0, 1, 1] [0, 2, 0, 2, 0, 2, 2] demoR1_2021020 demoR2_2021020 demoC_2021020 demoM_2021020 demoMir_2021020

theorem demoR1_0121020 : invRung 7 5 20 [0, 1, 2, 1, 0, 2, 0] [0, 1, 2, 1, 0, 2, 0] 1 2 false = ([0, 0, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0121020 : invRung 7 5 20 [0, 1, 2, 1, 0, 2, 0] [0, 0, 1, 1, 0, 0, 0] 3 1 true = ([1, 1, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0121020 : fieldCube 7 5 20 [1, 1, 0, 1, 1, 2, 0] = [1, 0, 0, 2, 2, 1, 2] := by
  decide

theorem demoM_0121020 : fieldMul 7 5 20 [1, 0, 0, 2, 2, 1, 2] [0, 1, 2, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0121020 : specInv 7 5 20 [0, 1, 2, 1, 0, 2, 0] = some [1, 0, 0, 2, 2, 1, 2] :=
  specInv_white_7 [0, 1, 2, 1, 0, 2, 0] [0, 0, 1, 1, 0, 0, 0] [1, 1, 0, 1, 1, 2, 0] [1, 0, 0, 2, 2, 1, 2] demoR1_0121020 demoR2_0121020 demoC_0121020 demoM_0121020

theorem demoR1_1121020 : invRung 7 5 20 [1, 1, 2, 1, 0, 2, 0] [1, 1, 2, 1, 0, 2, 0] 1 2 false = ([2, 2, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_1121020 : invRung 7 5 20 [1, 1, 2, 1, 0, 2, 0] [2, 2, 2, 0, 2, 1, 1] 3 1 true = ([2, 1, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_1121020 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 0, 2] = [1, 0, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_1121020 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 2, 0] [1, 1, 2, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121020 : mirrorTrits [1, 0, 0, 1, 2, 2, 0] = [2, 0, 0, 2, 1, 1, 0] := by
  decide

theorem demoInv_1121020 : specInv 7 5 20 [1, 1, 2, 1, 0, 2, 0] = some [2, 0, 0, 2, 1, 1, 0] :=
  specInv_mirror_7 [1, 1, 2, 1, 0, 2, 0] [2, 2, 2, 0, 2, 1, 1] [2, 1, 0, 2, 1, 0, 2] [1, 0, 0, 1, 2, 2, 0] [2, 0, 0, 2, 1, 1, 0] demoR1_1121020 demoR2_1121020 demoC_1121020 demoM_1121020 demoMir_1121020

theorem demoR1_2121020 : invRung 7 5 20 [2, 1, 2, 1, 0, 2, 0] [2, 1, 2, 1, 0, 2, 0] 1 2 false = ([0, 2, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2121020 : invRung 7 5 20 [2, 1, 2, 1, 0, 2, 0] [0, 2, 0, 2, 2, 0, 0] 3 1 true = ([2, 1, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_2121020 : fieldCube 7 5 20 [2, 1, 1, 2, 2, 1, 0] = [2, 0, 0, 0, 1, 2, 2] := by
  decide

theorem demoM_2121020 : fieldMul 7 5 20 [2, 0, 0, 0, 1, 2, 2] [2, 1, 2, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2121020 : specInv 7 5 20 [2, 1, 2, 1, 0, 2, 0] = some [2, 0, 0, 0, 1, 2, 2] :=
  specInv_white_7 [2, 1, 2, 1, 0, 2, 0] [0, 2, 0, 2, 2, 0, 0] [2, 1, 1, 2, 2, 1, 0] [2, 0, 0, 0, 1, 2, 2] demoR1_2121020 demoR2_2121020 demoC_2121020 demoM_2121020

theorem demoR1_0221020 : invRung 7 5 20 [0, 2, 2, 1, 0, 2, 0] [0, 2, 2, 1, 0, 2, 0] 1 2 false = ([1, 1, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_0221020 : invRung 7 5 20 [0, 2, 2, 1, 0, 2, 0] [1, 1, 1, 2, 1, 1, 0] 3 1 true = ([0, 0, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0221020 : fieldCube 7 5 20 [0, 0, 2, 0, 1, 0, 1] = [0, 2, 2, 2, 1, 2, 1] := by
  decide

theorem demoM_0221020 : fieldMul 7 5 20 [0, 2, 2, 2, 1, 2, 1] [0, 2, 2, 1, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0221020 : specInv 7 5 20 [0, 2, 2, 1, 0, 2, 0] = some [0, 2, 2, 2, 1, 2, 1] :=
  specInv_white_7 [0, 2, 2, 1, 0, 2, 0] [1, 1, 1, 2, 1, 1, 0] [0, 0, 2, 0, 1, 0, 1] [0, 2, 2, 2, 1, 2, 1] demoR1_0221020 demoR2_0221020 demoC_0221020 demoM_0221020

theorem demoR1_1221020 : invRung 7 5 20 [1, 2, 2, 1, 0, 2, 0] [1, 2, 2, 1, 0, 2, 0] 1 2 false = ([2, 1, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1221020 : invRung 7 5 20 [1, 2, 2, 1, 0, 2, 0] [2, 1, 1, 1, 1, 2, 1] 3 1 true = ([1, 1, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_1221020 : fieldCube 7 5 20 [1, 1, 0, 0, 0, 1, 2] = [2, 0, 2, 0, 0, 0, 1] := by
  decide

theorem demoM_1221020 : fieldMul 7 5 20 [2, 0, 2, 0, 0, 0, 1] [1, 2, 2, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221020 : mirrorTrits [2, 0, 2, 0, 0, 0, 1] = [1, 0, 1, 0, 0, 0, 2] := by
  decide

theorem demoInv_1221020 : specInv 7 5 20 [1, 2, 2, 1, 0, 2, 0] = some [1, 0, 1, 0, 0, 0, 2] :=
  specInv_mirror_7 [1, 2, 2, 1, 0, 2, 0] [2, 1, 1, 1, 1, 2, 1] [1, 1, 0, 0, 0, 1, 2] [2, 0, 2, 0, 0, 0, 1] [1, 0, 1, 0, 0, 0, 2] demoR1_1221020 demoR2_1221020 demoC_1221020 demoM_1221020 demoMir_1221020

theorem demoR1_2221020 : invRung 7 5 20 [2, 2, 2, 1, 0, 2, 0] [2, 2, 2, 1, 0, 2, 0] 1 2 false = ([1, 1, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2221020 : invRung 7 5 20 [2, 2, 2, 1, 0, 2, 0] [1, 1, 0, 2, 2, 0, 0] 3 1 true = ([1, 2, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_2221020 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 2, 2] = [0, 2, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_2221020 : fieldMul 7 5 20 [0, 2, 0, 2, 1, 2, 2] [2, 2, 2, 1, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221020 : mirrorTrits [0, 2, 0, 2, 1, 2, 2] = [0, 1, 0, 1, 2, 1, 1] := by
  decide

theorem demoInv_2221020 : specInv 7 5 20 [2, 2, 2, 1, 0, 2, 0] = some [0, 1, 0, 1, 2, 1, 1] :=
  specInv_mirror_7 [2, 2, 2, 1, 0, 2, 0] [1, 1, 0, 2, 2, 0, 0] [1, 2, 1, 0, 1, 2, 2] [0, 2, 0, 2, 1, 2, 2] [0, 1, 0, 1, 2, 1, 1] demoR1_2221020 demoR2_2221020 demoC_2221020 demoM_2221020 demoMir_2221020

theorem demoR1_0002020 : invRung 7 5 20 [0, 0, 0, 2, 0, 2, 0] [0, 0, 0, 2, 0, 2, 0] 1 2 false = ([1, 0, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_0002020 : invRung 7 5 20 [0, 0, 0, 2, 0, 2, 0] [1, 0, 2, 0, 0, 2, 1] 3 1 true = ([1, 0, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_0002020 : fieldCube 7 5 20 [1, 0, 2, 1, 2, 2, 0] = [1, 1, 0, 2, 2, 2, 2] := by
  decide

theorem demoM_0002020 : fieldMul 7 5 20 [1, 1, 0, 2, 2, 2, 2] [0, 0, 0, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0002020 : specInv 7 5 20 [0, 0, 0, 2, 0, 2, 0] = some [1, 1, 0, 2, 2, 2, 2] :=
  specInv_white_7 [0, 0, 0, 2, 0, 2, 0] [1, 0, 2, 0, 0, 2, 1] [1, 0, 2, 1, 2, 2, 0] [1, 1, 0, 2, 2, 2, 2] demoR1_0002020 demoR2_0002020 demoC_0002020 demoM_0002020

theorem demoR1_1002020 : invRung 7 5 20 [1, 0, 0, 2, 0, 2, 0] [1, 0, 0, 2, 0, 2, 0] 1 2 false = ([0, 2, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_1002020 : invRung 7 5 20 [1, 0, 0, 2, 0, 2, 0] [0, 2, 2, 2, 2, 0, 1] 3 1 true = ([1, 2, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_1002020 : fieldCube 7 5 20 [1, 2, 2, 2, 1, 0, 2] = [0, 0, 0, 2, 2, 2, 2] := by
  decide

theorem demoM_1002020 : fieldMul 7 5 20 [0, 0, 0, 2, 2, 2, 2] [1, 0, 0, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1002020 : specInv 7 5 20 [1, 0, 0, 2, 0, 2, 0] = some [0, 0, 0, 2, 2, 2, 2] :=
  specInv_white_7 [1, 0, 0, 2, 0, 2, 0] [0, 2, 2, 2, 2, 0, 1] [1, 2, 2, 2, 1, 0, 2] [0, 0, 0, 2, 2, 2, 2] demoR1_1002020 demoR2_1002020 demoC_1002020 demoM_1002020

theorem demoR1_2002020 : invRung 7 5 20 [2, 0, 0, 2, 0, 2, 0] [2, 0, 0, 2, 0, 2, 0] 1 2 false = ([2, 1, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_2002020 : invRung 7 5 20 [2, 0, 0, 2, 0, 2, 0] [2, 1, 1, 0, 0, 0, 0] 3 1 true = ([2, 2, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_2002020 : fieldCube 7 5 20 [2, 2, 2, 0, 2, 0, 2] = [2, 1, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_2002020 : fieldMul 7 5 20 [2, 1, 1, 0, 2, 1, 0] [2, 0, 0, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002020 : mirrorTrits [2, 1, 1, 0, 2, 1, 0] = [1, 2, 2, 0, 1, 2, 0] := by
  decide

theorem demoInv_2002020 : specInv 7 5 20 [2, 0, 0, 2, 0, 2, 0] = some [1, 2, 2, 0, 1, 2, 0] :=
  specInv_mirror_7 [2, 0, 0, 2, 0, 2, 0] [2, 1, 1, 0, 0, 0, 0] [2, 2, 2, 0, 2, 0, 2] [2, 1, 1, 0, 2, 1, 0] [1, 2, 2, 0, 1, 2, 0] demoR1_2002020 demoR2_2002020 demoC_2002020 demoM_2002020 demoMir_2002020

theorem demoR1_0102020 : invRung 7 5 20 [0, 1, 0, 2, 0, 2, 0] [0, 1, 0, 2, 0, 2, 0] 1 2 false = ([0, 0, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_0102020 : invRung 7 5 20 [0, 1, 0, 2, 0, 2, 0] [0, 0, 1, 1, 1, 1, 0] 3 1 true = ([1, 0, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_0102020 : fieldCube 7 5 20 [1, 0, 0, 2, 2, 2, 1] = [2, 2, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_0102020 : fieldMul 7 5 20 [2, 2, 0, 0, 0, 1, 1] [0, 1, 0, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102020 : mirrorTrits [2, 2, 0, 0, 0, 1, 1] = [1, 1, 0, 0, 0, 2, 2] := by
  decide

theorem demoInv_0102020 : specInv 7 5 20 [0, 1, 0, 2, 0, 2, 0] = some [1, 1, 0, 0, 0, 2, 2] :=
  specInv_mirror_7 [0, 1, 0, 2, 0, 2, 0] [0, 0, 1, 1, 1, 1, 0] [1, 0, 0, 2, 2, 2, 1] [2, 2, 0, 0, 0, 1, 1] [1, 1, 0, 0, 0, 2, 2] demoR1_0102020 demoR2_0102020 demoC_0102020 demoM_0102020 demoMir_0102020

theorem demoR1_1102020 : invRung 7 5 20 [1, 1, 0, 2, 0, 2, 0] [1, 1, 0, 2, 0, 2, 0] 1 2 false = ([2, 1, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_1102020 : invRung 7 5 20 [1, 1, 0, 2, 0, 2, 0] [2, 1, 1, 1, 2, 0, 1] 3 1 true = ([1, 0, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_1102020 : fieldCube 7 5 20 [1, 0, 1, 1, 2, 0, 1] = [2, 0, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_1102020 : fieldMul 7 5 20 [2, 0, 0, 0, 1, 1, 1] [1, 1, 0, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102020 : mirrorTrits [2, 0, 0, 0, 1, 1, 1] = [1, 0, 0, 0, 2, 2, 2] := by
  decide

theorem demoInv_1102020 : specInv 7 5 20 [1, 1, 0, 2, 0, 2, 0] = some [1, 0, 0, 0, 2, 2, 2] :=
  specInv_mirror_7 [1, 1, 0, 2, 0, 2, 0] [2, 1, 1, 1, 2, 0, 1] [1, 0, 1, 1, 2, 0, 1] [2, 0, 0, 0, 1, 1, 1] [1, 0, 0, 0, 2, 2, 2] demoR1_1102020 demoR2_1102020 demoC_1102020 demoM_1102020 demoMir_1102020

theorem demoR1_2102020 : invRung 7 5 20 [2, 1, 0, 2, 0, 2, 0] [2, 1, 0, 2, 0, 2, 0] 1 2 false = ([0, 1, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2102020 : invRung 7 5 20 [2, 1, 0, 2, 0, 2, 0] [0, 1, 2, 2, 2, 0, 1] 3 1 true = ([1, 2, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2102020 : fieldCube 7 5 20 [1, 2, 2, 1, 2, 1, 0] = [0, 0, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_2102020 : fieldMul 7 5 20 [0, 0, 2, 1, 1, 1, 0] [2, 1, 0, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2102020 : mirrorTrits [0, 0, 2, 1, 1, 1, 0] = [0, 0, 1, 2, 2, 2, 0] := by
  decide

theorem demoInv_2102020 : specInv 7 5 20 [2, 1, 0, 2, 0, 2, 0] = some [0, 0, 1, 2, 2, 2, 0] :=
  specInv_mirror_7 [2, 1, 0, 2, 0, 2, 0] [0, 1, 2, 2, 2, 0, 1] [1, 2, 2, 1, 2, 1, 0] [0, 0, 2, 1, 1, 1, 0] [0, 0, 1, 2, 2, 2, 0] demoR1_2102020 demoR2_2102020 demoC_2102020 demoM_2102020 demoMir_2102020

theorem demoR1_0202020 : invRung 7 5 20 [0, 2, 0, 2, 0, 2, 0] [0, 2, 0, 2, 0, 2, 0] 1 2 false = ([0, 1, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_0202020 : invRung 7 5 20 [0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 2, 2, 1] 3 1 true = ([0, 0, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0202020 : fieldCube 7 5 20 [0, 0, 0, 1, 0, 0, 0] = [1, 0, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_0202020 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 1, 0] [0, 2, 0, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202020 : mirrorTrits [1, 0, 1, 0, 0, 1, 0] = [2, 0, 2, 0, 0, 2, 0] := by
  decide

theorem demoInv_0202020 : specInv 7 5 20 [0, 2, 0, 2, 0, 2, 0] = some [2, 0, 2, 0, 0, 2, 0] :=
  specInv_mirror_7 [0, 2, 0, 2, 0, 2, 0] [0, 1, 0, 1, 2, 2, 1] [0, 0, 0, 1, 0, 0, 0] [1, 0, 1, 0, 0, 1, 0] [2, 0, 2, 0, 0, 2, 0] demoR1_0202020 demoR2_0202020 demoC_0202020 demoM_0202020 demoMir_0202020

end EcbsLink2.Link2
