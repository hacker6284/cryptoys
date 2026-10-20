/-
  One quarter of Demo's nonzero trit lists. Each kernel `decide` is one rung,
  one cube, or one multiply.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldOk

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem demoR1_2020202 : invRung 7 5 20 [2, 0, 2, 0, 2, 0, 2] [2, 0, 2, 0, 2, 0, 2] 1 2 false = ([0, 0, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_2020202 : invRung 7 5 20 [2, 0, 2, 0, 2, 0, 2] [0, 0, 2, 2, 0, 2, 1] 3 1 true = ([2, 2, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_2020202 : fieldCube 7 5 20 [2, 2, 0, 2, 1, 0, 0] = [1, 1, 2, 0, 0, 0, 1] := by
  decide

theorem demoM_2020202 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 0, 1] [2, 0, 2, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2020202 : specInv 7 5 20 [2, 0, 2, 0, 2, 0, 2] = some [1, 1, 2, 0, 0, 0, 1] :=
  specInv_white_7 [2, 0, 2, 0, 2, 0, 2] [0, 0, 2, 2, 0, 2, 1] [2, 2, 0, 2, 1, 0, 0] [1, 1, 2, 0, 0, 0, 1] demoR1_2020202 demoR2_2020202 demoC_2020202 demoM_2020202

theorem demoR1_0120202 : invRung 7 5 20 [0, 1, 2, 0, 2, 0, 2] [0, 1, 2, 0, 2, 0, 2] 1 2 false = ([0, 2, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_0120202 : invRung 7 5 20 [0, 1, 2, 0, 2, 0, 2] [0, 2, 0, 0, 2, 1, 0] 3 1 true = ([2, 1, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0120202 : fieldCube 7 5 20 [2, 1, 0, 0, 0, 2, 1] = [1, 0, 1, 2, 0, 0, 2] := by
  decide

theorem demoM_0120202 : fieldMul 7 5 20 [1, 0, 1, 2, 0, 0, 2] [0, 1, 2, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0120202 : specInv 7 5 20 [0, 1, 2, 0, 2, 0, 2] = some [1, 0, 1, 2, 0, 0, 2] :=
  specInv_white_7 [0, 1, 2, 0, 2, 0, 2] [0, 2, 0, 0, 2, 1, 0] [2, 1, 0, 0, 0, 2, 1] [1, 0, 1, 2, 0, 0, 2] demoR1_0120202 demoR2_0120202 demoC_0120202 demoM_0120202

theorem demoR1_1120202 : invRung 7 5 20 [1, 1, 2, 0, 2, 0, 2] [1, 1, 2, 0, 2, 0, 2] 1 2 false = ([0, 2, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1120202 : invRung 7 5 20 [1, 1, 2, 0, 2, 0, 2] [0, 2, 1, 1, 1, 2, 1] 3 1 true = ([0, 2, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_1120202 : fieldCube 7 5 20 [0, 2, 2, 2, 2, 2, 1] = [1, 2, 0, 2, 0, 1, 0] := by
  decide

theorem demoM_1120202 : fieldMul 7 5 20 [1, 2, 0, 2, 0, 1, 0] [1, 1, 2, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1120202 : specInv 7 5 20 [1, 1, 2, 0, 2, 0, 2] = some [1, 2, 0, 2, 0, 1, 0] :=
  specInv_white_7 [1, 1, 2, 0, 2, 0, 2] [0, 2, 1, 1, 1, 2, 1] [0, 2, 2, 2, 2, 2, 1] [1, 2, 0, 2, 0, 1, 0] demoR1_1120202 demoR2_1120202 demoC_1120202 demoM_1120202

theorem demoR1_2120202 : invRung 7 5 20 [2, 1, 2, 0, 2, 0, 2] [2, 1, 2, 0, 2, 0, 2] 1 2 false = ([0, 0, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_2120202 : invRung 7 5 20 [2, 1, 2, 0, 2, 0, 2] [0, 0, 2, 0, 1, 0, 1] 3 1 true = ([2, 2, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_2120202 : fieldCube 7 5 20 [2, 2, 1, 1, 0, 0, 1] = [0, 1, 0, 0, 1, 2, 2] := by
  decide

theorem demoM_2120202 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 2, 2] [2, 1, 2, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2120202 : specInv 7 5 20 [2, 1, 2, 0, 2, 0, 2] = some [0, 1, 0, 0, 1, 2, 2] :=
  specInv_white_7 [2, 1, 2, 0, 2, 0, 2] [0, 0, 2, 0, 1, 0, 1] [2, 2, 1, 1, 0, 0, 1] [0, 1, 0, 0, 1, 2, 2] demoR1_2120202 demoR2_2120202 demoC_2120202 demoM_2120202

theorem demoR1_0220202 : invRung 7 5 20 [0, 2, 2, 0, 2, 0, 2] [0, 2, 2, 0, 2, 0, 2] 1 2 false = ([0, 1, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_0220202 : invRung 7 5 20 [0, 2, 2, 0, 2, 0, 2] [0, 1, 0, 2, 1, 0, 2] 3 1 true = ([0, 2, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_0220202 : fieldCube 7 5 20 [0, 2, 1, 2, 2, 2, 0] = [1, 1, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_0220202 : fieldMul 7 5 20 [1, 1, 1, 1, 2, 0, 1] [0, 2, 2, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0220202 : mirrorTrits [1, 1, 1, 1, 2, 0, 1] = [2, 2, 2, 2, 1, 0, 2] := by
  decide

theorem demoInv_0220202 : specInv 7 5 20 [0, 2, 2, 0, 2, 0, 2] = some [2, 2, 2, 2, 1, 0, 2] :=
  specInv_mirror_7 [0, 2, 2, 0, 2, 0, 2] [0, 1, 0, 2, 1, 0, 2] [0, 2, 1, 2, 2, 2, 0] [1, 1, 1, 1, 2, 0, 1] [2, 2, 2, 2, 1, 0, 2] demoR1_0220202 demoR2_0220202 demoC_0220202 demoM_0220202 demoMir_0220202

theorem demoR1_1220202 : invRung 7 5 20 [1, 2, 2, 0, 2, 0, 2] [1, 2, 2, 0, 2, 0, 2] 1 2 false = ([2, 1, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_1220202 : invRung 7 5 20 [1, 2, 2, 0, 2, 0, 2] [2, 1, 1, 0, 1, 0, 2] 3 1 true = ([0, 2, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_1220202 : fieldCube 7 5 20 [0, 2, 2, 2, 1, 1, 1] = [0, 0, 2, 1, 2, 2, 0] := by
  decide

theorem demoM_1220202 : fieldMul 7 5 20 [0, 0, 2, 1, 2, 2, 0] [1, 2, 2, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1220202 : specInv 7 5 20 [1, 2, 2, 0, 2, 0, 2] = some [0, 0, 2, 1, 2, 2, 0] :=
  specInv_white_7 [1, 2, 2, 0, 2, 0, 2] [2, 1, 1, 0, 1, 0, 2] [0, 2, 2, 2, 1, 1, 1] [0, 0, 2, 1, 2, 2, 0] demoR1_1220202 demoR2_1220202 demoC_1220202 demoM_1220202

theorem demoR1_2220202 : invRung 7 5 20 [2, 2, 2, 0, 2, 0, 2] [2, 2, 2, 0, 2, 0, 2] 1 2 false = ([0, 1, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_2220202 : invRung 7 5 20 [2, 2, 2, 0, 2, 0, 2] [0, 1, 1, 1, 2, 2, 1] 3 1 true = ([0, 2, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_2220202 : fieldCube 7 5 20 [0, 2, 0, 2, 2, 0, 0] = [2, 2, 2, 1, 0, 1, 2] := by
  decide

theorem demoM_2220202 : fieldMul 7 5 20 [2, 2, 2, 1, 0, 1, 2] [2, 2, 2, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2220202 : specInv 7 5 20 [2, 2, 2, 0, 2, 0, 2] = some [2, 2, 2, 1, 0, 1, 2] :=
  specInv_white_7 [2, 2, 2, 0, 2, 0, 2] [0, 1, 1, 1, 2, 2, 1] [0, 2, 0, 2, 2, 0, 0] [2, 2, 2, 1, 0, 1, 2] demoR1_2220202 demoR2_2220202 demoC_2220202 demoM_2220202

theorem demoR1_0001202 : invRung 7 5 20 [0, 0, 0, 1, 2, 0, 2] [0, 0, 0, 1, 2, 0, 2] 1 2 false = ([1, 2, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0001202 : invRung 7 5 20 [0, 0, 0, 1, 2, 0, 2] [1, 2, 1, 0, 2, 2, 2] 3 1 true = ([2, 2, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0001202 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 2, 2] = [2, 0, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_0001202 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 1, 2] [0, 0, 0, 1, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0001202 : specInv 7 5 20 [0, 0, 0, 1, 2, 0, 2] = some [2, 0, 1, 0, 1, 1, 2] :=
  specInv_white_7 [0, 0, 0, 1, 2, 0, 2] [1, 2, 1, 0, 2, 2, 2] [2, 2, 0, 1, 2, 2, 2] [2, 0, 1, 0, 1, 1, 2] demoR1_0001202 demoR2_0001202 demoC_0001202 demoM_0001202

theorem demoR1_1001202 : invRung 7 5 20 [1, 0, 0, 1, 2, 0, 2] [1, 0, 0, 1, 2, 0, 2] 1 2 false = ([0, 1, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_1001202 : invRung 7 5 20 [1, 0, 0, 1, 2, 0, 2] [0, 1, 1, 0, 2, 0, 1] 3 1 true = ([2, 0, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1001202 : fieldCube 7 5 20 [2, 0, 0, 1, 0, 1, 1] = [1, 2, 1, 1, 2, 0, 0] := by
  decide

theorem demoM_1001202 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 0, 0] [1, 0, 0, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1001202 : mirrorTrits [1, 2, 1, 1, 2, 0, 0] = [2, 1, 2, 2, 1, 0, 0] := by
  decide

theorem demoInv_1001202 : specInv 7 5 20 [1, 0, 0, 1, 2, 0, 2] = some [2, 1, 2, 2, 1, 0, 0] :=
  specInv_mirror_7 [1, 0, 0, 1, 2, 0, 2] [0, 1, 1, 0, 2, 0, 1] [2, 0, 0, 1, 0, 1, 1] [1, 2, 1, 1, 2, 0, 0] [2, 1, 2, 2, 1, 0, 0] demoR1_1001202 demoR2_1001202 demoC_1001202 demoM_1001202 demoMir_1001202

theorem demoR1_2001202 : invRung 7 5 20 [2, 0, 0, 1, 2, 0, 2] [2, 0, 0, 1, 2, 0, 2] 1 2 false = ([0, 0, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_2001202 : invRung 7 5 20 [2, 0, 0, 1, 2, 0, 2] [0, 0, 0, 0, 1, 2, 0] 3 1 true = ([1, 2, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_2001202 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 2, 1] = [0, 1, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_2001202 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 1, 1] [2, 0, 0, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001202 : mirrorTrits [0, 1, 1, 1, 0, 1, 1] = [0, 2, 2, 2, 0, 2, 2] := by
  decide

theorem demoInv_2001202 : specInv 7 5 20 [2, 0, 0, 1, 2, 0, 2] = some [0, 2, 2, 2, 0, 2, 2] :=
  specInv_mirror_7 [2, 0, 0, 1, 2, 0, 2] [0, 0, 0, 0, 1, 2, 0] [1, 2, 1, 0, 1, 2, 1] [0, 1, 1, 1, 0, 1, 1] [0, 2, 2, 2, 0, 2, 2] demoR1_2001202 demoR2_2001202 demoC_2001202 demoM_2001202 demoMir_2001202

theorem demoR1_0101202 : invRung 7 5 20 [0, 1, 0, 1, 2, 0, 2] [0, 1, 0, 1, 2, 0, 2] 1 2 false = ([2, 0, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_0101202 : invRung 7 5 20 [0, 1, 0, 1, 2, 0, 2] [2, 0, 2, 0, 0, 0, 1] 3 1 true = ([2, 2, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_0101202 : fieldCube 7 5 20 [2, 2, 1, 2, 0, 0, 1] = [1, 1, 1, 0, 1, 0, 2] := by
  decide

theorem demoM_0101202 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 0, 2] [0, 1, 0, 1, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0101202 : specInv 7 5 20 [0, 1, 0, 1, 2, 0, 2] = some [1, 1, 1, 0, 1, 0, 2] :=
  specInv_white_7 [0, 1, 0, 1, 2, 0, 2] [2, 0, 2, 0, 0, 0, 1] [2, 2, 1, 2, 0, 0, 1] [1, 1, 1, 0, 1, 0, 2] demoR1_0101202 demoR2_0101202 demoC_0101202 demoM_0101202

theorem demoR1_1101202 : invRung 7 5 20 [1, 1, 0, 1, 2, 0, 2] [1, 1, 0, 1, 2, 0, 2] 1 2 false = ([1, 0, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_1101202 : invRung 7 5 20 [1, 1, 0, 1, 2, 0, 2] [1, 0, 0, 1, 2, 1, 0] 3 1 true = ([2, 2, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_1101202 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 2, 2] = [2, 2, 1, 2, 1, 0, 2] := by
  decide

theorem demoM_1101202 : fieldMul 7 5 20 [2, 2, 1, 2, 1, 0, 2] [1, 1, 0, 1, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1101202 : specInv 7 5 20 [1, 1, 0, 1, 2, 0, 2] = some [2, 2, 1, 2, 1, 0, 2] :=
  specInv_white_7 [1, 1, 0, 1, 2, 0, 2] [1, 0, 0, 1, 2, 1, 0] [2, 2, 1, 1, 1, 2, 2] [2, 2, 1, 2, 1, 0, 2] demoR1_1101202 demoR2_1101202 demoC_1101202 demoM_1101202

theorem demoR1_2101202 : invRung 7 5 20 [2, 1, 0, 1, 2, 0, 2] [2, 1, 0, 1, 2, 0, 2] 1 2 false = ([0, 2, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_2101202 : invRung 7 5 20 [2, 1, 0, 1, 2, 0, 2] [0, 2, 2, 1, 0, 2, 2] 3 1 true = ([2, 0, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_2101202 : fieldCube 7 5 20 [2, 0, 0, 1, 0, 1, 2] = [1, 0, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_2101202 : fieldMul 7 5 20 [1, 0, 0, 2, 0, 1, 1] [2, 1, 0, 1, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2101202 : specInv 7 5 20 [2, 1, 0, 1, 2, 0, 2] = some [1, 0, 0, 2, 0, 1, 1] :=
  specInv_white_7 [2, 1, 0, 1, 2, 0, 2] [0, 2, 2, 1, 0, 2, 2] [2, 0, 0, 1, 0, 1, 2] [1, 0, 0, 2, 0, 1, 1] demoR1_2101202 demoR2_2101202 demoC_2101202 demoM_2101202

theorem demoR1_0201202 : invRung 7 5 20 [0, 2, 0, 1, 2, 0, 2] [0, 2, 0, 1, 2, 0, 2] 1 2 false = ([1, 0, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_0201202 : invRung 7 5 20 [0, 2, 0, 1, 2, 0, 2] [1, 0, 0, 2, 2, 0, 2] 3 1 true = ([1, 1, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_0201202 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 0, 2] = [1, 1, 1, 2, 2, 1, 2] := by
  decide

theorem demoM_0201202 : fieldMul 7 5 20 [1, 1, 1, 2, 2, 1, 2] [0, 2, 0, 1, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0201202 : specInv 7 5 20 [0, 2, 0, 1, 2, 0, 2] = some [1, 1, 1, 2, 2, 1, 2] :=
  specInv_white_7 [0, 2, 0, 1, 2, 0, 2] [1, 0, 0, 2, 2, 0, 2] [1, 1, 1, 0, 2, 0, 2] [1, 1, 1, 2, 2, 1, 2] demoR1_0201202 demoR2_0201202 demoC_0201202 demoM_0201202

theorem demoR1_1201202 : invRung 7 5 20 [1, 2, 0, 1, 2, 0, 2] [1, 2, 0, 1, 2, 0, 2] 1 2 false = ([0, 2, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_1201202 : invRung 7 5 20 [1, 2, 0, 1, 2, 0, 2] [0, 2, 2, 2, 2, 0, 2] 3 1 true = ([2, 2, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_1201202 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 2, 2] = [1, 0, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_1201202 : fieldMul 7 5 20 [1, 0, 0, 0, 1, 0, 0] [1, 2, 0, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201202 : mirrorTrits [1, 0, 0, 0, 1, 0, 0] = [2, 0, 0, 0, 2, 0, 0] := by
  decide

theorem demoInv_1201202 : specInv 7 5 20 [1, 2, 0, 1, 2, 0, 2] = some [2, 0, 0, 0, 2, 0, 0] :=
  specInv_mirror_7 [1, 2, 0, 1, 2, 0, 2] [0, 2, 2, 2, 2, 0, 2] [2, 2, 1, 0, 2, 2, 2] [1, 0, 0, 0, 1, 0, 0] [2, 0, 0, 0, 2, 0, 0] demoR1_1201202 demoR2_1201202 demoC_1201202 demoM_1201202 demoMir_1201202

theorem demoR1_2201202 : invRung 7 5 20 [2, 2, 0, 1, 2, 0, 2] [2, 2, 0, 1, 2, 0, 2] 1 2 false = ([1, 2, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_2201202 : invRung 7 5 20 [2, 2, 0, 1, 2, 0, 2] [1, 2, 1, 0, 1, 2, 2] 3 1 true = ([2, 0, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_2201202 : fieldCube 7 5 20 [2, 0, 0, 1, 2, 1, 2] = [1, 2, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_2201202 : fieldMul 7 5 20 [1, 2, 0, 1, 0, 0, 0] [2, 2, 0, 1, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2201202 : specInv 7 5 20 [2, 2, 0, 1, 2, 0, 2] = some [1, 2, 0, 1, 0, 0, 0] :=
  specInv_white_7 [2, 2, 0, 1, 2, 0, 2] [1, 2, 1, 0, 1, 2, 2] [2, 0, 0, 1, 2, 1, 2] [1, 2, 0, 1, 0, 0, 0] demoR1_2201202 demoR2_2201202 demoC_2201202 demoM_2201202

theorem demoR1_0011202 : invRung 7 5 20 [0, 0, 1, 1, 2, 0, 2] [0, 0, 1, 1, 2, 0, 2] 1 2 false = ([1, 0, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_0011202 : invRung 7 5 20 [0, 0, 1, 1, 2, 0, 2] [1, 0, 0, 2, 2, 1, 1] 3 1 true = ([1, 0, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_0011202 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 2, 0] = [2, 0, 1, 1, 2, 2, 0] := by
  decide

theorem demoM_0011202 : fieldMul 7 5 20 [2, 0, 1, 1, 2, 2, 0] [0, 0, 1, 1, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0011202 : specInv 7 5 20 [0, 0, 1, 1, 2, 0, 2] = some [2, 0, 1, 1, 2, 2, 0] :=
  specInv_white_7 [0, 0, 1, 1, 2, 0, 2] [1, 0, 0, 2, 2, 1, 1] [1, 0, 1, 2, 1, 2, 0] [2, 0, 1, 1, 2, 2, 0] demoR1_0011202 demoR2_0011202 demoC_0011202 demoM_0011202

theorem demoR1_1011202 : invRung 7 5 20 [1, 0, 1, 1, 2, 0, 2] [1, 0, 1, 1, 2, 0, 2] 1 2 false = ([0, 0, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_1011202 : invRung 7 5 20 [1, 0, 1, 1, 2, 0, 2] [0, 0, 1, 0, 2, 0, 0] 3 1 true = ([1, 1, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1011202 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 2, 1] = [1, 1, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_1011202 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 2, 1] [1, 0, 1, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011202 : mirrorTrits [1, 1, 2, 0, 0, 2, 1] = [2, 2, 1, 0, 0, 1, 2] := by
  decide

theorem demoInv_1011202 : specInv 7 5 20 [1, 0, 1, 1, 2, 0, 2] = some [2, 2, 1, 0, 0, 1, 2] :=
  specInv_mirror_7 [1, 0, 1, 1, 2, 0, 2] [0, 0, 1, 0, 2, 0, 0] [1, 1, 1, 1, 1, 2, 1] [1, 1, 2, 0, 0, 2, 1] [2, 2, 1, 0, 0, 1, 2] demoR1_1011202 demoR2_1011202 demoC_1011202 demoM_1011202 demoMir_1011202

theorem demoR1_2011202 : invRung 7 5 20 [2, 0, 1, 1, 2, 0, 2] [2, 0, 1, 1, 2, 0, 2] 1 2 false = ([0, 2, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_2011202 : invRung 7 5 20 [2, 0, 1, 1, 2, 0, 2] [0, 2, 1, 0, 0, 2, 0] 3 1 true = ([2, 0, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_2011202 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 2, 0] = [0, 2, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_2011202 : fieldMul 7 5 20 [0, 2, 1, 0, 2, 1, 0] [2, 0, 1, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011202 : mirrorTrits [0, 2, 1, 0, 2, 1, 0] = [0, 1, 2, 0, 1, 2, 0] := by
  decide

theorem demoInv_2011202 : specInv 7 5 20 [2, 0, 1, 1, 2, 0, 2] = some [0, 1, 2, 0, 1, 2, 0] :=
  specInv_mirror_7 [2, 0, 1, 1, 2, 0, 2] [0, 2, 1, 0, 0, 2, 0] [2, 0, 2, 2, 0, 2, 0] [0, 2, 1, 0, 2, 1, 0] [0, 1, 2, 0, 1, 2, 0] demoR1_2011202 demoR2_2011202 demoC_2011202 demoM_2011202 demoMir_2011202

theorem demoR1_0111202 : invRung 7 5 20 [0, 1, 1, 1, 2, 0, 2] [0, 1, 1, 1, 2, 0, 2] 1 2 false = ([1, 2, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_0111202 : invRung 7 5 20 [0, 1, 1, 1, 2, 0, 2] [1, 2, 0, 2, 0, 1, 2] 3 1 true = ([1, 0, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0111202 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 2, 2] = [1, 0, 1, 1, 1, 1, 2] := by
  decide

theorem demoM_0111202 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 1, 2] [0, 1, 1, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111202 : mirrorTrits [1, 0, 1, 1, 1, 1, 2] = [2, 0, 2, 2, 2, 2, 1] := by
  decide

theorem demoInv_0111202 : specInv 7 5 20 [0, 1, 1, 1, 2, 0, 2] = some [2, 0, 2, 2, 2, 2, 1] :=
  specInv_mirror_7 [0, 1, 1, 1, 2, 0, 2] [1, 2, 0, 2, 0, 1, 2] [1, 0, 0, 1, 2, 2, 2] [1, 0, 1, 1, 1, 1, 2] [2, 0, 2, 2, 2, 2, 1] demoR1_0111202 demoR2_0111202 demoC_0111202 demoM_0111202 demoMir_0111202

theorem demoR1_1111202 : invRung 7 5 20 [1, 1, 1, 1, 2, 0, 2] [1, 1, 1, 1, 2, 0, 2] 1 2 false = ([0, 2, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_1111202 : invRung 7 5 20 [1, 1, 1, 1, 2, 0, 2] [0, 2, 0, 0, 0, 1, 0] 3 1 true = ([1, 0, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_1111202 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 0, 1] = [1, 1, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_1111202 : fieldMul 7 5 20 [1, 1, 2, 1, 1, 1, 2] [1, 1, 1, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111202 : mirrorTrits [1, 1, 2, 1, 1, 1, 2] = [2, 2, 1, 2, 2, 2, 1] := by
  decide

theorem demoInv_1111202 : specInv 7 5 20 [1, 1, 1, 1, 2, 0, 2] = some [2, 2, 1, 2, 2, 2, 1] :=
  specInv_mirror_7 [1, 1, 1, 1, 2, 0, 2] [0, 2, 0, 0, 0, 1, 0] [1, 0, 1, 0, 0, 0, 1] [1, 1, 2, 1, 1, 1, 2] [2, 2, 1, 2, 2, 2, 1] demoR1_1111202 demoR2_1111202 demoC_1111202 demoM_1111202 demoMir_1111202

theorem demoR1_2111202 : invRung 7 5 20 [2, 1, 1, 1, 2, 0, 2] [2, 1, 1, 1, 2, 0, 2] 1 2 false = ([2, 0, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_2111202 : invRung 7 5 20 [2, 1, 1, 1, 2, 0, 2] [2, 0, 1, 2, 1, 0, 2] 3 1 true = ([1, 2, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2111202 : fieldCube 7 5 20 [1, 2, 1, 1, 0, 2, 1] = [1, 0, 2, 0, 0, 1, 0] := by
  decide

theorem demoM_2111202 : fieldMul 7 5 20 [1, 0, 2, 0, 0, 1, 0] [2, 1, 1, 1, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2111202 : specInv 7 5 20 [2, 1, 1, 1, 2, 0, 2] = some [1, 0, 2, 0, 0, 1, 0] :=
  specInv_white_7 [2, 1, 1, 1, 2, 0, 2] [2, 0, 1, 2, 1, 0, 2] [1, 2, 1, 1, 0, 2, 1] [1, 0, 2, 0, 0, 1, 0] demoR1_2111202 demoR2_2111202 demoC_2111202 demoM_2111202

theorem demoR1_0211202 : invRung 7 5 20 [0, 2, 1, 1, 2, 0, 2] [0, 2, 1, 1, 2, 0, 2] 1 2 false = ([0, 2, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0211202 : invRung 7 5 20 [0, 2, 1, 1, 2, 0, 2] [0, 2, 1, 1, 2, 1, 2] 3 1 true = ([1, 2, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_0211202 : fieldCube 7 5 20 [1, 2, 2, 1, 0, 2, 1] = [1, 0, 2, 0, 0, 1, 1] := by
  decide

theorem demoM_0211202 : fieldMul 7 5 20 [1, 0, 2, 0, 0, 1, 1] [0, 2, 1, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211202 : mirrorTrits [1, 0, 2, 0, 0, 1, 1] = [2, 0, 1, 0, 0, 2, 2] := by
  decide

theorem demoInv_0211202 : specInv 7 5 20 [0, 2, 1, 1, 2, 0, 2] = some [2, 0, 1, 0, 0, 2, 2] :=
  specInv_mirror_7 [0, 2, 1, 1, 2, 0, 2] [0, 2, 1, 1, 2, 1, 2] [1, 2, 2, 1, 0, 2, 1] [1, 0, 2, 0, 0, 1, 1] [2, 0, 1, 0, 0, 2, 2] demoR1_0211202 demoR2_0211202 demoC_0211202 demoM_0211202 demoMir_0211202

theorem demoR1_1211202 : invRung 7 5 20 [1, 2, 1, 1, 2, 0, 2] [1, 2, 1, 1, 2, 0, 2] 1 2 false = ([2, 0, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1211202 : invRung 7 5 20 [1, 2, 1, 1, 2, 0, 2] [2, 0, 0, 0, 1, 1, 0] 3 1 true = ([1, 1, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_1211202 : fieldCube 7 5 20 [1, 1, 1, 2, 1, 0, 1] = [0, 2, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_1211202 : fieldMul 7 5 20 [0, 2, 1, 0, 1, 1, 0] [1, 2, 1, 1, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1211202 : specInv 7 5 20 [1, 2, 1, 1, 2, 0, 2] = some [0, 2, 1, 0, 1, 1, 0] :=
  specInv_white_7 [1, 2, 1, 1, 2, 0, 2] [2, 0, 0, 0, 1, 1, 0] [1, 1, 1, 2, 1, 0, 1] [0, 2, 1, 0, 1, 1, 0] demoR1_1211202 demoR2_1211202 demoC_1211202 demoM_1211202

theorem demoR1_2211202 : invRung 7 5 20 [2, 2, 1, 1, 2, 0, 2] [2, 2, 1, 1, 2, 0, 2] 1 2 false = ([0, 1, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_2211202 : invRung 7 5 20 [2, 2, 1, 1, 2, 0, 2] [0, 1, 2, 2, 1, 2, 2] 3 1 true = ([2, 1, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_2211202 : fieldCube 7 5 20 [2, 1, 1, 2, 2, 2, 1] = [0, 2, 0, 1, 0, 1, 2] := by
  decide

theorem demoM_2211202 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 1, 2] [2, 2, 1, 1, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2211202 : specInv 7 5 20 [2, 2, 1, 1, 2, 0, 2] = some [0, 2, 0, 1, 0, 1, 2] :=
  specInv_white_7 [2, 2, 1, 1, 2, 0, 2] [0, 1, 2, 2, 1, 2, 2] [2, 1, 1, 2, 2, 2, 1] [0, 2, 0, 1, 0, 1, 2] demoR1_2211202 demoR2_2211202 demoC_2211202 demoM_2211202

theorem demoR1_0021202 : invRung 7 5 20 [0, 0, 2, 1, 2, 0, 2] [0, 0, 2, 1, 2, 0, 2] 1 2 false = ([1, 1, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0021202 : invRung 7 5 20 [0, 0, 2, 1, 2, 0, 2] [1, 1, 0, 1, 1, 1, 2] 3 1 true = ([2, 2, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_0021202 : fieldCube 7 5 20 [2, 2, 2, 1, 0, 0, 2] = [0, 2, 2, 1, 2, 0, 1] := by
  decide

theorem demoM_0021202 : fieldMul 7 5 20 [0, 2, 2, 1, 2, 0, 1] [0, 0, 2, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021202 : mirrorTrits [0, 2, 2, 1, 2, 0, 1] = [0, 1, 1, 2, 1, 0, 2] := by
  decide

theorem demoInv_0021202 : specInv 7 5 20 [0, 0, 2, 1, 2, 0, 2] = some [0, 1, 1, 2, 1, 0, 2] :=
  specInv_mirror_7 [0, 0, 2, 1, 2, 0, 2] [1, 1, 0, 1, 1, 1, 2] [2, 2, 2, 1, 0, 0, 2] [0, 2, 2, 1, 2, 0, 1] [0, 1, 1, 2, 1, 0, 2] demoR1_0021202 demoR2_0021202 demoC_0021202 demoM_0021202 demoMir_0021202

theorem demoR1_1021202 : invRung 7 5 20 [1, 0, 2, 1, 2, 0, 2] [1, 0, 2, 1, 2, 0, 2] 1 2 false = ([2, 2, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1021202 : invRung 7 5 20 [1, 0, 2, 1, 2, 0, 2] [2, 2, 0, 0, 1, 1, 0] 3 1 true = ([2, 1, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_1021202 : fieldCube 7 5 20 [2, 1, 1, 1, 1, 0, 1] = [0, 2, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_1021202 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 0, 0] [1, 0, 2, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021202 : mirrorTrits [0, 2, 0, 0, 1, 0, 0] = [0, 1, 0, 0, 2, 0, 0] := by
  decide

theorem demoInv_1021202 : specInv 7 5 20 [1, 0, 2, 1, 2, 0, 2] = some [0, 1, 0, 0, 2, 0, 0] :=
  specInv_mirror_7 [1, 0, 2, 1, 2, 0, 2] [2, 2, 0, 0, 1, 1, 0] [2, 1, 1, 1, 1, 0, 1] [0, 2, 0, 0, 1, 0, 0] [0, 1, 0, 0, 2, 0, 0] demoR1_1021202 demoR2_1021202 demoC_1021202 demoM_1021202 demoMir_1021202

theorem demoR1_2021202 : invRung 7 5 20 [2, 0, 2, 1, 2, 0, 2] [2, 0, 2, 1, 2, 0, 2] 1 2 false = ([1, 1, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_2021202 : invRung 7 5 20 [2, 0, 2, 1, 2, 0, 2] [1, 1, 2, 0, 1, 0, 0] 3 1 true = ([0, 1, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_2021202 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 0, 0] = [0, 0, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_2021202 : fieldMul 7 5 20 [0, 0, 0, 1, 0, 0, 1] [2, 0, 2, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021202 : mirrorTrits [0, 0, 0, 1, 0, 0, 1] = [0, 0, 0, 2, 0, 0, 2] := by
  decide

theorem demoInv_2021202 : specInv 7 5 20 [2, 0, 2, 1, 2, 0, 2] = some [0, 0, 0, 2, 0, 0, 2] :=
  specInv_mirror_7 [2, 0, 2, 1, 2, 0, 2] [1, 1, 2, 0, 1, 0, 0] [0, 1, 1, 0, 0, 0, 0] [0, 0, 0, 1, 0, 0, 1] [0, 0, 0, 2, 0, 0, 2] demoR1_2021202 demoR2_2021202 demoC_2021202 demoM_2021202 demoMir_2021202

theorem demoR1_0121202 : invRung 7 5 20 [0, 1, 2, 1, 2, 0, 2] [0, 1, 2, 1, 2, 0, 2] 1 2 false = ([0, 0, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0121202 : invRung 7 5 20 [0, 1, 2, 1, 2, 0, 2] [0, 0, 1, 0, 1, 2, 1] 3 1 true = ([0, 1, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_0121202 : fieldCube 7 5 20 [0, 1, 1, 2, 0, 2, 0] = [1, 2, 1, 1, 2, 1, 2] := by
  decide

theorem demoM_0121202 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 1, 2] [0, 1, 2, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0121202 : mirrorTrits [1, 2, 1, 1, 2, 1, 2] = [2, 1, 2, 2, 1, 2, 1] := by
  decide

theorem demoInv_0121202 : specInv 7 5 20 [0, 1, 2, 1, 2, 0, 2] = some [2, 1, 2, 2, 1, 2, 1] :=
  specInv_mirror_7 [0, 1, 2, 1, 2, 0, 2] [0, 0, 1, 0, 1, 2, 1] [0, 1, 1, 2, 0, 2, 0] [1, 2, 1, 1, 2, 1, 2] [2, 1, 2, 2, 1, 2, 1] demoR1_0121202 demoR2_0121202 demoC_0121202 demoM_0121202 demoMir_0121202

theorem demoR1_1121202 : invRung 7 5 20 [1, 1, 2, 1, 2, 0, 2] [1, 1, 2, 1, 2, 0, 2] 1 2 false = ([1, 0, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_1121202 : invRung 7 5 20 [1, 1, 2, 1, 2, 0, 2] [1, 0, 1, 1, 2, 1, 0] 3 1 true = ([0, 1, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_1121202 : fieldCube 7 5 20 [0, 1, 0, 2, 0, 1, 1] = [0, 2, 2, 2, 2, 1, 0] := by
  decide

theorem demoM_1121202 : fieldMul 7 5 20 [0, 2, 2, 2, 2, 1, 0] [1, 1, 2, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121202 : mirrorTrits [0, 2, 2, 2, 2, 1, 0] = [0, 1, 1, 1, 1, 2, 0] := by
  decide

theorem demoInv_1121202 : specInv 7 5 20 [1, 1, 2, 1, 2, 0, 2] = some [0, 1, 1, 1, 1, 2, 0] :=
  specInv_mirror_7 [1, 1, 2, 1, 2, 0, 2] [1, 0, 1, 1, 2, 1, 0] [0, 1, 0, 2, 0, 1, 1] [0, 2, 2, 2, 2, 1, 0] [0, 1, 1, 1, 1, 2, 0] demoR1_1121202 demoR2_1121202 demoC_1121202 demoM_1121202 demoMir_1121202

theorem demoR1_2121202 : invRung 7 5 20 [2, 1, 2, 1, 2, 0, 2] [2, 1, 2, 1, 2, 0, 2] 1 2 false = ([2, 0, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_2121202 : invRung 7 5 20 [2, 1, 2, 1, 2, 0, 2] [2, 0, 2, 2, 0, 1, 1] 3 1 true = ([0, 2, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_2121202 : fieldCube 7 5 20 [0, 2, 0, 2, 2, 0, 2] = [2, 1, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_2121202 : fieldMul 7 5 20 [2, 1, 0, 0, 2, 0, 1] [2, 1, 2, 1, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2121202 : specInv 7 5 20 [2, 1, 2, 1, 2, 0, 2] = some [2, 1, 0, 0, 2, 0, 1] :=
  specInv_white_7 [2, 1, 2, 1, 2, 0, 2] [2, 0, 2, 2, 0, 1, 1] [0, 2, 0, 2, 2, 0, 2] [2, 1, 0, 0, 2, 0, 1] demoR1_2121202 demoR2_2121202 demoC_2121202 demoM_2121202

theorem demoR1_0221202 : invRung 7 5 20 [0, 2, 2, 1, 2, 0, 2] [0, 2, 2, 1, 2, 0, 2] 1 2 false = ([2, 2, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0221202 : invRung 7 5 20 [0, 2, 2, 1, 2, 0, 2] [2, 2, 1, 1, 2, 1, 2] 3 1 true = ([2, 0, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0221202 : fieldCube 7 5 20 [2, 0, 1, 0, 2, 1, 2] = [0, 2, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_0221202 : fieldMul 7 5 20 [0, 2, 2, 1, 0, 2, 1] [0, 2, 2, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0221202 : mirrorTrits [0, 2, 2, 1, 0, 2, 1] = [0, 1, 1, 2, 0, 1, 2] := by
  decide

theorem demoInv_0221202 : specInv 7 5 20 [0, 2, 2, 1, 2, 0, 2] = some [0, 1, 1, 2, 0, 1, 2] :=
  specInv_mirror_7 [0, 2, 2, 1, 2, 0, 2] [2, 2, 1, 1, 2, 1, 2] [2, 0, 1, 0, 2, 1, 2] [0, 2, 2, 1, 0, 2, 1] [0, 1, 1, 2, 0, 1, 2] demoR1_0221202 demoR2_0221202 demoC_0221202 demoM_0221202 demoMir_0221202

theorem demoR1_1221202 : invRung 7 5 20 [1, 2, 2, 1, 2, 0, 2] [1, 2, 2, 1, 2, 0, 2] 1 2 false = ([0, 2, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_1221202 : invRung 7 5 20 [1, 2, 2, 1, 2, 0, 2] [0, 2, 1, 2, 0, 1, 0] 3 1 true = ([1, 1, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1221202 : fieldCube 7 5 20 [1, 1, 1, 2, 1, 2, 2] = [2, 2, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_1221202 : fieldMul 7 5 20 [2, 2, 2, 1, 1, 1, 2] [1, 2, 2, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221202 : mirrorTrits [2, 2, 2, 1, 1, 1, 2] = [1, 1, 1, 2, 2, 2, 1] := by
  decide

theorem demoInv_1221202 : specInv 7 5 20 [1, 2, 2, 1, 2, 0, 2] = some [1, 1, 1, 2, 2, 2, 1] :=
  specInv_mirror_7 [1, 2, 2, 1, 2, 0, 2] [0, 2, 1, 2, 0, 1, 0] [1, 1, 1, 2, 1, 2, 2] [2, 2, 2, 1, 1, 1, 2] [1, 1, 1, 2, 2, 2, 1] demoR1_1221202 demoR2_1221202 demoC_1221202 demoM_1221202 demoMir_1221202

theorem demoR1_2221202 : invRung 7 5 20 [2, 2, 2, 1, 2, 0, 2] [2, 2, 2, 1, 2, 0, 2] 1 2 false = ([0, 1, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_2221202 : invRung 7 5 20 [2, 2, 2, 1, 2, 0, 2] [0, 1, 1, 2, 1, 1, 0] 3 1 true = ([2, 0, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2221202 : fieldCube 7 5 20 [2, 0, 2, 1, 0, 2, 1] = [2, 0, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_2221202 : fieldMul 7 5 20 [2, 0, 2, 1, 0, 1, 1] [2, 2, 2, 1, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221202 : mirrorTrits [2, 0, 2, 1, 0, 1, 1] = [1, 0, 1, 2, 0, 2, 2] := by
  decide

theorem demoInv_2221202 : specInv 7 5 20 [2, 2, 2, 1, 2, 0, 2] = some [1, 0, 1, 2, 0, 2, 2] :=
  specInv_mirror_7 [2, 2, 2, 1, 2, 0, 2] [0, 1, 1, 2, 1, 1, 0] [2, 0, 2, 1, 0, 2, 1] [2, 0, 2, 1, 0, 1, 1] [1, 0, 1, 2, 0, 2, 2] demoR1_2221202 demoR2_2221202 demoC_2221202 demoM_2221202 demoMir_2221202

theorem demoR1_0002202 : invRung 7 5 20 [0, 0, 0, 2, 2, 0, 2] [0, 0, 0, 2, 2, 0, 2] 1 2 false = ([2, 2, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0002202 : invRung 7 5 20 [0, 0, 0, 2, 2, 0, 2] [2, 2, 1, 1, 0, 0, 0] 3 1 true = ([2, 0, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0002202 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 0, 1] = [2, 2, 2, 2, 1, 2, 0] := by
  decide

theorem demoM_0002202 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 2, 0] [0, 0, 0, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0002202 : specInv 7 5 20 [0, 0, 0, 2, 2, 0, 2] = some [2, 2, 2, 2, 1, 2, 0] :=
  specInv_white_7 [0, 0, 0, 2, 2, 0, 2] [2, 2, 1, 1, 0, 0, 0] [2, 0, 1, 0, 1, 0, 1] [2, 2, 2, 2, 1, 2, 0] demoR1_0002202 demoR2_0002202 demoC_0002202 demoM_0002202

theorem demoR1_1002202 : invRung 7 5 20 [1, 0, 0, 2, 2, 0, 2] [1, 0, 0, 2, 2, 0, 2] 1 2 false = ([1, 1, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_1002202 : invRung 7 5 20 [1, 0, 0, 2, 2, 0, 2] [1, 1, 0, 1, 2, 1, 2] 3 1 true = ([1, 2, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_1002202 : fieldCube 7 5 20 [1, 2, 0, 0, 0, 0, 2] = [1, 2, 1, 1, 2, 2, 2] := by
  decide

theorem demoM_1002202 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 2, 2] [1, 0, 0, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1002202 : specInv 7 5 20 [1, 0, 0, 2, 2, 0, 2] = some [1, 2, 1, 1, 2, 2, 2] :=
  specInv_white_7 [1, 0, 0, 2, 2, 0, 2] [1, 1, 0, 1, 2, 1, 2] [1, 2, 0, 0, 0, 0, 2] [1, 2, 1, 1, 2, 2, 2] demoR1_1002202 demoR2_1002202 demoC_1002202 demoM_1002202

theorem demoR1_2002202 : invRung 7 5 20 [2, 0, 0, 2, 2, 0, 2] [2, 0, 0, 2, 2, 0, 2] 1 2 false = ([1, 2, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_2002202 : invRung 7 5 20 [2, 0, 0, 2, 2, 0, 2] [1, 2, 2, 0, 2, 1, 1] 3 1 true = ([0, 1, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_2002202 : fieldCube 7 5 20 [0, 1, 2, 0, 0, 0, 1] = [0, 1, 2, 2, 1, 1, 0] := by
  decide

theorem demoM_2002202 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 1, 0] [2, 0, 0, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2002202 : specInv 7 5 20 [2, 0, 0, 2, 2, 0, 2] = some [0, 1, 2, 2, 1, 1, 0] :=
  specInv_white_7 [2, 0, 0, 2, 2, 0, 2] [1, 2, 2, 0, 2, 1, 1] [0, 1, 2, 0, 0, 0, 1] [0, 1, 2, 2, 1, 1, 0] demoR1_2002202 demoR2_2002202 demoC_2002202 demoM_2002202

theorem demoR1_0102202 : invRung 7 5 20 [0, 1, 0, 2, 2, 0, 2] [0, 1, 0, 2, 2, 0, 2] 1 2 false = ([2, 2, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_0102202 : invRung 7 5 20 [0, 1, 0, 2, 2, 0, 2] [2, 2, 0, 1, 2, 0, 0] 3 1 true = ([0, 1, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_0102202 : fieldCube 7 5 20 [0, 1, 1, 2, 2, 1, 1] = [0, 1, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_0102202 : fieldMul 7 5 20 [0, 1, 2, 1, 2, 0, 0] [0, 1, 0, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0102202 : specInv 7 5 20 [0, 1, 0, 2, 2, 0, 2] = some [0, 1, 2, 1, 2, 0, 0] :=
  specInv_white_7 [0, 1, 0, 2, 2, 0, 2] [2, 2, 0, 1, 2, 0, 0] [0, 1, 1, 2, 2, 1, 1] [0, 1, 2, 1, 2, 0, 0] demoR1_0102202 demoR2_0102202 demoC_0102202 demoM_0102202

theorem demoR1_1102202 : invRung 7 5 20 [1, 1, 0, 2, 2, 0, 2] [1, 1, 0, 2, 2, 0, 2] 1 2 false = ([2, 2, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_1102202 : invRung 7 5 20 [1, 1, 0, 2, 2, 0, 2] [2, 2, 0, 2, 2, 0, 2] 3 1 true = ([0, 0, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1102202 : fieldCube 7 5 20 [0, 0, 2, 2, 0, 1, 0] = [0, 1, 0, 0, 1, 0, 1] := by
  decide

theorem demoM_1102202 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 0, 1] [1, 1, 0, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1102202 : specInv 7 5 20 [1, 1, 0, 2, 2, 0, 2] = some [0, 1, 0, 0, 1, 0, 1] :=
  specInv_white_7 [1, 1, 0, 2, 2, 0, 2] [2, 2, 0, 2, 2, 0, 2] [0, 0, 2, 2, 0, 1, 0] [0, 1, 0, 0, 1, 0, 1] demoR1_1102202 demoR2_1102202 demoC_1102202 demoM_1102202

theorem demoR1_2102202 : invRung 7 5 20 [2, 1, 0, 2, 2, 0, 2] [2, 1, 0, 2, 2, 0, 2] 1 2 false = ([2, 0, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_2102202 : invRung 7 5 20 [2, 1, 0, 2, 2, 0, 2] [2, 0, 2, 1, 0, 1, 1] 3 1 true = ([2, 0, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_2102202 : fieldCube 7 5 20 [2, 0, 1, 1, 0, 0, 1] = [0, 1, 0, 1, 1, 2, 2] := by
  decide

theorem demoM_2102202 : fieldMul 7 5 20 [0, 1, 0, 1, 1, 2, 2] [2, 1, 0, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2102202 : specInv 7 5 20 [2, 1, 0, 2, 2, 0, 2] = some [0, 1, 0, 1, 1, 2, 2] :=
  specInv_white_7 [2, 1, 0, 2, 2, 0, 2] [2, 0, 2, 1, 0, 1, 1] [2, 0, 1, 1, 0, 0, 1] [0, 1, 0, 1, 1, 2, 2] demoR1_2102202 demoR2_2102202 demoC_2102202 demoM_2102202

theorem demoR1_0202202 : invRung 7 5 20 [0, 2, 0, 2, 2, 0, 2] [0, 2, 0, 2, 2, 0, 2] 1 2 false = ([0, 2, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_0202202 : invRung 7 5 20 [0, 2, 0, 2, 2, 0, 2] [0, 2, 2, 1, 1, 0, 0] 3 1 true = ([1, 2, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_0202202 : fieldCube 7 5 20 [1, 2, 2, 0, 2, 1, 1] = [2, 1, 0, 2, 2, 1, 1] := by
  decide

theorem demoM_0202202 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 1, 1] [0, 2, 0, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0202202 : specInv 7 5 20 [0, 2, 0, 2, 2, 0, 2] = some [2, 1, 0, 2, 2, 1, 1] :=
  specInv_white_7 [0, 2, 0, 2, 2, 0, 2] [0, 2, 2, 1, 1, 0, 0] [1, 2, 2, 0, 2, 1, 1] [2, 1, 0, 2, 2, 1, 1] demoR1_0202202 demoR2_0202202 demoC_0202202 demoM_0202202

theorem demoR1_1202202 : invRung 7 5 20 [1, 2, 0, 2, 2, 0, 2] [1, 2, 0, 2, 2, 0, 2] 1 2 false = ([1, 1, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_1202202 : invRung 7 5 20 [1, 2, 0, 2, 2, 0, 2] [1, 1, 0, 1, 1, 1, 0] 3 1 true = ([0, 2, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_1202202 : fieldCube 7 5 20 [0, 2, 1, 2, 2, 0, 0] = [2, 2, 2, 1, 0, 1, 0] := by
  decide

theorem demoM_1202202 : fieldMul 7 5 20 [2, 2, 2, 1, 0, 1, 0] [1, 2, 0, 2, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202202 : mirrorTrits [2, 2, 2, 1, 0, 1, 0] = [1, 1, 1, 2, 0, 2, 0] := by
  decide

theorem demoInv_1202202 : specInv 7 5 20 [1, 2, 0, 2, 2, 0, 2] = some [1, 1, 1, 2, 0, 2, 0] :=
  specInv_mirror_7 [1, 2, 0, 2, 2, 0, 2] [1, 1, 0, 1, 1, 1, 0] [0, 2, 1, 2, 2, 0, 0] [2, 2, 2, 1, 0, 1, 0] [1, 1, 1, 2, 0, 2, 0] demoR1_1202202 demoR2_1202202 demoC_1202202 demoM_1202202 demoMir_1202202

theorem demoR1_2202202 : invRung 7 5 20 [2, 2, 0, 2, 2, 0, 2] [2, 2, 0, 2, 2, 0, 2] 1 2 false = ([1, 0, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_2202202 : invRung 7 5 20 [2, 2, 0, 2, 2, 0, 2] [1, 0, 2, 1, 2, 2, 0] 3 1 true = ([2, 1, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2202202 : fieldCube 7 5 20 [2, 1, 0, 0, 1, 0, 0] = [2, 1, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_2202202 : fieldMul 7 5 20 [2, 1, 0, 2, 0, 1, 1] [2, 2, 0, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2202202 : specInv 7 5 20 [2, 2, 0, 2, 2, 0, 2] = some [2, 1, 0, 2, 0, 1, 1] :=
  specInv_white_7 [2, 2, 0, 2, 2, 0, 2] [1, 0, 2, 1, 2, 2, 0] [2, 1, 0, 0, 1, 0, 0] [2, 1, 0, 2, 0, 1, 1] demoR1_2202202 demoR2_2202202 demoC_2202202 demoM_2202202

theorem demoR1_0012202 : invRung 7 5 20 [0, 0, 1, 2, 2, 0, 2] [0, 0, 1, 2, 2, 0, 2] 1 2 false = ([2, 0, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0012202 : invRung 7 5 20 [0, 0, 1, 2, 2, 0, 2] [2, 0, 2, 0, 2, 1, 2] 3 1 true = ([0, 2, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0012202 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 1, 2] = [2, 0, 0, 1, 0, 1, 2] := by
  decide

theorem demoM_0012202 : fieldMul 7 5 20 [2, 0, 0, 1, 0, 1, 2] [0, 0, 1, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0012202 : specInv 7 5 20 [0, 0, 1, 2, 2, 0, 2] = some [2, 0, 0, 1, 0, 1, 2] :=
  specInv_white_7 [0, 0, 1, 2, 2, 0, 2] [2, 0, 2, 0, 2, 1, 2] [0, 2, 1, 1, 0, 1, 2] [2, 0, 0, 1, 0, 1, 2] demoR1_0012202 demoR2_0012202 demoC_0012202 demoM_0012202

theorem demoR1_1012202 : invRung 7 5 20 [1, 0, 1, 2, 2, 0, 2] [1, 0, 1, 2, 2, 0, 2] 1 2 false = ([1, 1, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_1012202 : invRung 7 5 20 [1, 0, 1, 2, 2, 0, 2] [1, 1, 0, 0, 0, 1, 2] 3 1 true = ([1, 0, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_1012202 : fieldCube 7 5 20 [1, 0, 2, 1, 2, 0, 0] = [2, 2, 1, 2, 0, 0, 1] := by
  decide

theorem demoM_1012202 : fieldMul 7 5 20 [2, 2, 1, 2, 0, 0, 1] [1, 0, 1, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1012202 : specInv 7 5 20 [1, 0, 1, 2, 2, 0, 2] = some [2, 2, 1, 2, 0, 0, 1] :=
  specInv_white_7 [1, 0, 1, 2, 2, 0, 2] [1, 1, 0, 0, 0, 1, 2] [1, 0, 2, 1, 2, 0, 0] [2, 2, 1, 2, 0, 0, 1] demoR1_1012202 demoR2_1012202 demoC_1012202 demoM_1012202

theorem demoR1_2012202 : invRung 7 5 20 [2, 0, 1, 2, 2, 0, 2] [2, 0, 1, 2, 2, 0, 2] 1 2 false = ([1, 0, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2012202 : invRung 7 5 20 [2, 0, 1, 2, 2, 0, 2] [1, 0, 1, 1, 1, 2, 0] 3 1 true = ([1, 0, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2012202 : fieldCube 7 5 20 [1, 0, 2, 0, 1, 1, 0] = [2, 2, 1, 1, 1, 2, 2] := by
  decide

theorem demoM_2012202 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 2, 2] [2, 0, 1, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2012202 : specInv 7 5 20 [2, 0, 1, 2, 2, 0, 2] = some [2, 2, 1, 1, 1, 2, 2] :=
  specInv_white_7 [2, 0, 1, 2, 2, 0, 2] [1, 0, 1, 1, 1, 2, 0] [1, 0, 2, 0, 1, 1, 0] [2, 2, 1, 1, 1, 2, 2] demoR1_2012202 demoR2_2012202 demoC_2012202 demoM_2012202

theorem demoR1_0112202 : invRung 7 5 20 [0, 1, 1, 2, 2, 0, 2] [0, 1, 1, 2, 2, 0, 2] 1 2 false = ([2, 0, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_0112202 : invRung 7 5 20 [0, 1, 1, 2, 2, 0, 2] [2, 0, 2, 1, 0, 2, 1] 3 1 true = ([0, 0, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0112202 : fieldCube 7 5 20 [0, 0, 2, 0, 0, 2, 1] = [2, 0, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_0112202 : fieldMul 7 5 20 [2, 0, 1, 1, 0, 0, 1] [0, 1, 1, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0112202 : specInv 7 5 20 [0, 1, 1, 2, 2, 0, 2] = some [2, 0, 1, 1, 0, 0, 1] :=
  specInv_white_7 [0, 1, 1, 2, 2, 0, 2] [2, 0, 2, 1, 0, 2, 1] [0, 0, 2, 0, 0, 2, 1] [2, 0, 1, 1, 0, 0, 1] demoR1_0112202 demoR2_0112202 demoC_0112202 demoM_0112202

theorem demoR1_1112202 : invRung 7 5 20 [1, 1, 1, 2, 2, 0, 2] [1, 1, 1, 2, 2, 0, 2] 1 2 false = ([2, 1, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_1112202 : invRung 7 5 20 [1, 1, 1, 2, 2, 0, 2] [2, 1, 2, 1, 0, 2, 0] 3 1 true = ([0, 1, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_1112202 : fieldCube 7 5 20 [0, 1, 0, 0, 2, 0, 2] = [0, 1, 1, 2, 2, 1, 1] := by
  decide

theorem demoM_1112202 : fieldMul 7 5 20 [0, 1, 1, 2, 2, 1, 1] [1, 1, 1, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1112202 : specInv 7 5 20 [1, 1, 1, 2, 2, 0, 2] = some [0, 1, 1, 2, 2, 1, 1] :=
  specInv_white_7 [1, 1, 1, 2, 2, 0, 2] [2, 1, 2, 1, 0, 2, 0] [0, 1, 0, 0, 2, 0, 2] [0, 1, 1, 2, 2, 1, 1] demoR1_1112202 demoR2_1112202 demoC_1112202 demoM_1112202

theorem demoR1_2112202 : invRung 7 5 20 [2, 1, 1, 2, 2, 0, 2] [2, 1, 1, 2, 2, 0, 2] 1 2 false = ([2, 2, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_2112202 : invRung 7 5 20 [2, 1, 1, 2, 2, 0, 2] [2, 2, 1, 1, 0, 2, 0] 3 1 true = ([0, 1, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2112202 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 2, 1] = [0, 0, 2, 2, 0, 1, 0] := by
  decide

theorem demoM_2112202 : fieldMul 7 5 20 [0, 0, 2, 2, 0, 1, 0] [2, 1, 1, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2112202 : specInv 7 5 20 [2, 1, 1, 2, 2, 0, 2] = some [0, 0, 2, 2, 0, 1, 0] :=
  specInv_white_7 [2, 1, 1, 2, 2, 0, 2] [2, 2, 1, 1, 0, 2, 0] [0, 1, 1, 1, 0, 2, 1] [0, 0, 2, 2, 0, 1, 0] demoR1_2112202 demoR2_2112202 demoC_2112202 demoM_2112202

theorem demoR1_0212202 : invRung 7 5 20 [0, 2, 1, 2, 2, 0, 2] [0, 2, 1, 2, 2, 0, 2] 1 2 false = ([1, 2, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_0212202 : invRung 7 5 20 [0, 2, 1, 2, 2, 0, 2] [1, 2, 0, 2, 1, 1, 0] 3 1 true = ([0, 1, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0212202 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 2, 1] = [2, 0, 1, 2, 0, 0, 0] := by
  decide

theorem demoM_0212202 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 0, 0] [0, 2, 1, 2, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212202 : mirrorTrits [2, 0, 1, 2, 0, 0, 0] = [1, 0, 2, 1, 0, 0, 0] := by
  decide

theorem demoInv_0212202 : specInv 7 5 20 [0, 2, 1, 2, 2, 0, 2] = some [1, 0, 2, 1, 0, 0, 0] :=
  specInv_mirror_7 [0, 2, 1, 2, 2, 0, 2] [1, 2, 0, 2, 1, 1, 0] [0, 1, 1, 0, 0, 2, 1] [2, 0, 1, 2, 0, 0, 0] [1, 0, 2, 1, 0, 0, 0] demoR1_0212202 demoR2_0212202 demoC_0212202 demoM_0212202 demoMir_0212202

theorem demoR1_1212202 : invRung 7 5 20 [1, 2, 1, 2, 2, 0, 2] [1, 2, 1, 2, 2, 0, 2] 1 2 false = ([2, 1, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_1212202 : invRung 7 5 20 [1, 2, 1, 2, 2, 0, 2] [2, 1, 2, 0, 2, 0, 2] 3 1 true = ([1, 0, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1212202 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 1, 0] = [0, 0, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_1212202 : fieldMul 7 5 20 [0, 0, 2, 2, 1, 1, 1] [1, 2, 1, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1212202 : specInv 7 5 20 [1, 2, 1, 2, 2, 0, 2] = some [0, 0, 2, 2, 1, 1, 1] :=
  specInv_white_7 [1, 2, 1, 2, 2, 0, 2] [2, 1, 2, 0, 2, 0, 2] [1, 0, 0, 1, 2, 1, 0] [0, 0, 2, 2, 1, 1, 1] demoR1_1212202 demoR2_1212202 demoC_1212202 demoM_1212202

theorem demoR1_2212202 : invRung 7 5 20 [2, 2, 1, 2, 2, 0, 2] [2, 2, 1, 2, 2, 0, 2] 1 2 false = ([2, 2, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_2212202 : invRung 7 5 20 [2, 2, 1, 2, 2, 0, 2] [2, 2, 2, 0, 0, 1, 2] 3 1 true = ([1, 0, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2212202 : fieldCube 7 5 20 [1, 0, 2, 0, 1, 1, 1] = [2, 0, 0, 2, 2, 0, 0] := by
  decide

theorem demoM_2212202 : fieldMul 7 5 20 [2, 0, 0, 2, 2, 0, 0] [2, 2, 1, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2212202 : specInv 7 5 20 [2, 2, 1, 2, 2, 0, 2] = some [2, 0, 0, 2, 2, 0, 0] :=
  specInv_white_7 [2, 2, 1, 2, 2, 0, 2] [2, 2, 2, 0, 0, 1, 2] [1, 0, 2, 0, 1, 1, 1] [2, 0, 0, 2, 2, 0, 0] demoR1_2212202 demoR2_2212202 demoC_2212202 demoM_2212202

theorem demoR1_0022202 : invRung 7 5 20 [0, 0, 2, 2, 2, 0, 2] [0, 0, 2, 2, 2, 0, 2] 1 2 false = ([0, 2, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_0022202 : invRung 7 5 20 [0, 0, 2, 2, 2, 0, 2] [0, 2, 2, 2, 0, 1, 0] 3 1 true = ([1, 2, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0022202 : fieldCube 7 5 20 [1, 2, 2, 1, 1, 0, 0] = [2, 1, 1, 0, 0, 2, 0] := by
  decide

theorem demoM_0022202 : fieldMul 7 5 20 [2, 1, 1, 0, 0, 2, 0] [0, 0, 2, 2, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022202 : mirrorTrits [2, 1, 1, 0, 0, 2, 0] = [1, 2, 2, 0, 0, 1, 0] := by
  decide

theorem demoInv_0022202 : specInv 7 5 20 [0, 0, 2, 2, 2, 0, 2] = some [1, 2, 2, 0, 0, 1, 0] :=
  specInv_mirror_7 [0, 0, 2, 2, 2, 0, 2] [0, 2, 2, 2, 0, 1, 0] [1, 2, 2, 1, 1, 0, 0] [2, 1, 1, 0, 0, 2, 0] [1, 2, 2, 0, 0, 1, 0] demoR1_0022202 demoR2_0022202 demoC_0022202 demoM_0022202 demoMir_0022202

theorem demoR1_1022202 : invRung 7 5 20 [1, 0, 2, 2, 2, 0, 2] [1, 0, 2, 2, 2, 0, 2] 1 2 false = ([1, 2, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_1022202 : invRung 7 5 20 [1, 0, 2, 2, 2, 0, 2] [1, 2, 0, 2, 0, 0, 0] 3 1 true = ([0, 1, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1022202 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 2, 1] = [0, 0, 2, 2, 0, 1, 1] := by
  decide

theorem demoM_1022202 : fieldMul 7 5 20 [0, 0, 2, 2, 0, 1, 1] [1, 0, 2, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1022202 : specInv 7 5 20 [1, 0, 2, 2, 2, 0, 2] = some [0, 0, 2, 2, 0, 1, 1] :=
  specInv_white_7 [1, 0, 2, 2, 2, 0, 2] [1, 2, 0, 2, 0, 0, 0] [0, 1, 2, 1, 0, 2, 1] [0, 0, 2, 2, 0, 1, 1] demoR1_1022202 demoR2_1022202 demoC_1022202 demoM_1022202

theorem demoR1_2022202 : invRung 7 5 20 [2, 0, 2, 2, 2, 0, 2] [2, 0, 2, 2, 2, 0, 2] 1 2 false = ([0, 2, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_2022202 : invRung 7 5 20 [2, 0, 2, 2, 2, 0, 2] [0, 2, 1, 2, 2, 2, 2] 3 1 true = ([0, 2, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_2022202 : fieldCube 7 5 20 [0, 2, 0, 2, 2, 2, 2] = [1, 0, 2, 0, 1, 2, 2] := by
  decide

theorem demoM_2022202 : fieldMul 7 5 20 [1, 0, 2, 0, 1, 2, 2] [2, 0, 2, 2, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022202 : mirrorTrits [1, 0, 2, 0, 1, 2, 2] = [2, 0, 1, 0, 2, 1, 1] := by
  decide

theorem demoInv_2022202 : specInv 7 5 20 [2, 0, 2, 2, 2, 0, 2] = some [2, 0, 1, 0, 2, 1, 1] :=
  specInv_mirror_7 [2, 0, 2, 2, 2, 0, 2] [0, 2, 1, 2, 2, 2, 2] [0, 2, 0, 2, 2, 2, 2] [1, 0, 2, 0, 1, 2, 2] [2, 0, 1, 0, 2, 1, 1] demoR1_2022202 demoR2_2022202 demoC_2022202 demoM_2022202 demoMir_2022202

theorem demoR1_0122202 : invRung 7 5 20 [0, 1, 2, 2, 2, 0, 2] [0, 1, 2, 2, 2, 0, 2] 1 2 false = ([0, 1, 2, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_0122202 : invRung 7 5 20 [0, 1, 2, 2, 2, 0, 2] [0, 1, 2, 0, 2, 2, 0] 3 1 true = ([2, 1, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0122202 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 0, 2] = [1, 1, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_0122202 : fieldMul 7 5 20 [1, 1, 0, 2, 2, 0, 1] [0, 1, 2, 2, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122202 : mirrorTrits [1, 1, 0, 2, 2, 0, 1] = [2, 2, 0, 1, 1, 0, 2] := by
  decide

theorem demoInv_0122202 : specInv 7 5 20 [0, 1, 2, 2, 2, 0, 2] = some [2, 2, 0, 1, 1, 0, 2] :=
  specInv_mirror_7 [0, 1, 2, 2, 2, 0, 2] [0, 1, 2, 0, 2, 2, 0] [2, 1, 0, 2, 2, 0, 2] [1, 1, 0, 2, 2, 0, 1] [2, 2, 0, 1, 1, 0, 2] demoR1_0122202 demoR2_0122202 demoC_0122202 demoM_0122202 demoMir_0122202

theorem demoR1_1122202 : invRung 7 5 20 [1, 1, 2, 2, 2, 0, 2] [1, 1, 2, 2, 2, 0, 2] 1 2 false = ([2, 0, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_1122202 : invRung 7 5 20 [1, 1, 2, 2, 2, 0, 2] [2, 0, 0, 2, 2, 2, 1] 3 1 true = ([1, 1, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_1122202 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 0, 1] = [1, 2, 2, 0, 1, 2, 2] := by
  decide

theorem demoM_1122202 : fieldMul 7 5 20 [1, 2, 2, 0, 1, 2, 2] [1, 1, 2, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1122202 : specInv 7 5 20 [1, 1, 2, 2, 2, 0, 2] = some [1, 2, 2, 0, 1, 2, 2] :=
  specInv_white_7 [1, 1, 2, 2, 2, 0, 2] [2, 0, 0, 2, 2, 2, 1] [1, 1, 0, 0, 1, 0, 1] [1, 2, 2, 0, 1, 2, 2] demoR1_1122202 demoR2_1122202 demoC_1122202 demoM_1122202

theorem demoR1_2122202 : invRung 7 5 20 [2, 1, 2, 2, 2, 0, 2] [2, 1, 2, 2, 2, 0, 2] 1 2 false = ([1, 1, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_2122202 : invRung 7 5 20 [2, 1, 2, 2, 2, 0, 2] [1, 1, 0, 0, 1, 1, 1] 3 1 true = ([1, 2, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_2122202 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 0, 0] = [0, 1, 2, 0, 0, 0, 2] := by
  decide

theorem demoM_2122202 : fieldMul 7 5 20 [0, 1, 2, 0, 0, 0, 2] [2, 1, 2, 2, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122202 : mirrorTrits [0, 1, 2, 0, 0, 0, 2] = [0, 2, 1, 0, 0, 0, 1] := by
  decide

theorem demoInv_2122202 : specInv 7 5 20 [2, 1, 2, 2, 2, 0, 2] = some [0, 2, 1, 0, 0, 0, 1] :=
  specInv_mirror_7 [2, 1, 2, 2, 2, 0, 2] [1, 1, 0, 0, 1, 1, 1] [1, 2, 1, 2, 1, 0, 0] [0, 1, 2, 0, 0, 0, 2] [0, 2, 1, 0, 0, 0, 1] demoR1_2122202 demoR2_2122202 demoC_2122202 demoM_2122202 demoMir_2122202

theorem demoR1_0222202 : invRung 7 5 20 [0, 2, 2, 2, 2, 0, 2] [0, 2, 2, 2, 2, 0, 2] 1 2 false = ([0, 1, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_0222202 : invRung 7 5 20 [0, 2, 2, 2, 2, 0, 2] [0, 1, 1, 1, 1, 2, 0] 3 1 true = ([2, 2, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0222202 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 1, 2] = [2, 1, 1, 2, 0, 0, 1] := by
  decide

theorem demoM_0222202 : fieldMul 7 5 20 [2, 1, 1, 2, 0, 0, 1] [0, 2, 2, 2, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222202 : mirrorTrits [2, 1, 1, 2, 0, 0, 1] = [1, 2, 2, 1, 0, 0, 2] := by
  decide

theorem demoInv_0222202 : specInv 7 5 20 [0, 2, 2, 2, 2, 0, 2] = some [1, 2, 2, 1, 0, 0, 2] :=
  specInv_mirror_7 [0, 2, 2, 2, 2, 0, 2] [0, 1, 1, 1, 1, 2, 0] [2, 2, 2, 2, 1, 1, 2] [2, 1, 1, 2, 0, 0, 1] [1, 2, 2, 1, 0, 0, 2] demoR1_0222202 demoR2_0222202 demoC_0222202 demoM_0222202 demoMir_0222202

theorem demoR1_1222202 : invRung 7 5 20 [1, 2, 2, 2, 2, 0, 2] [1, 2, 2, 2, 2, 0, 2] 1 2 false = ([0, 0, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1222202 : invRung 7 5 20 [1, 2, 2, 2, 2, 0, 2] [0, 0, 2, 0, 0, 2, 0] 3 1 true = ([1, 2, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_1222202 : fieldCube 7 5 20 [1, 2, 1, 1, 1, 2, 0] = [1, 0, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_1222202 : fieldMul 7 5 20 [1, 0, 0, 0, 2, 1, 0] [1, 2, 2, 2, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222202 : mirrorTrits [1, 0, 0, 0, 2, 1, 0] = [2, 0, 0, 0, 1, 2, 0] := by
  decide

theorem demoInv_1222202 : specInv 7 5 20 [1, 2, 2, 2, 2, 0, 2] = some [2, 0, 0, 0, 1, 2, 0] :=
  specInv_mirror_7 [1, 2, 2, 2, 2, 0, 2] [0, 0, 2, 0, 0, 2, 0] [1, 2, 1, 1, 1, 2, 0] [1, 0, 0, 0, 2, 1, 0] [2, 0, 0, 0, 1, 2, 0] demoR1_1222202 demoR2_1222202 demoC_1222202 demoM_1222202 demoMir_1222202

theorem demoR1_2222202 : invRung 7 5 20 [2, 2, 2, 2, 2, 0, 2] [2, 2, 2, 2, 2, 0, 2] 1 2 false = ([2, 0, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_2222202 : invRung 7 5 20 [2, 2, 2, 2, 2, 0, 2] [2, 0, 1, 0, 1, 0, 2] 3 1 true = ([1, 0, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_2222202 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 1, 2] = [1, 1, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_2222202 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 0, 0] [2, 2, 2, 2, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2222202 : specInv 7 5 20 [2, 2, 2, 2, 2, 0, 2] = some [1, 1, 1, 0, 0, 0, 0] :=
  specInv_white_7 [2, 2, 2, 2, 2, 0, 2] [2, 0, 1, 0, 1, 0, 2] [1, 0, 1, 2, 1, 1, 2] [1, 1, 1, 0, 0, 0, 0] demoR1_2222202 demoR2_2222202 demoC_2222202 demoM_2222202

theorem demoR1_0000012 : invRung 7 5 20 [0, 0, 0, 0, 0, 1, 2] [0, 0, 0, 0, 0, 1, 2] 1 2 false = ([1, 2, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0000012 : invRung 7 5 20 [0, 0, 0, 0, 0, 1, 2] [1, 2, 2, 0, 1, 2, 1] 3 1 true = ([0, 1, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0000012 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 2, 1] = [1, 1, 0, 0, 0, 0, 0] := by
  decide

theorem demoM_0000012 : fieldMul 7 5 20 [1, 1, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000012 : mirrorTrits [1, 1, 0, 0, 0, 0, 0] = [2, 2, 0, 0, 0, 0, 0] := by
  decide

theorem demoInv_0000012 : specInv 7 5 20 [0, 0, 0, 0, 0, 1, 2] = some [2, 2, 0, 0, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 0, 0, 0, 1, 2] [1, 2, 2, 0, 1, 2, 1] [0, 1, 0, 2, 1, 2, 1] [1, 1, 0, 0, 0, 0, 0] [2, 2, 0, 0, 0, 0, 0] demoR1_0000012 demoR2_0000012 demoC_0000012 demoM_0000012 demoMir_0000012

theorem demoR1_1000012 : invRung 7 5 20 [1, 0, 0, 0, 0, 1, 2] [1, 0, 0, 0, 0, 1, 2] 1 2 false = ([2, 1, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_1000012 : invRung 7 5 20 [1, 0, 0, 0, 0, 1, 2] [2, 1, 0, 2, 2, 0, 2] 3 1 true = ([0, 1, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1000012 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 1, 1] = [1, 0, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_1000012 : fieldMul 7 5 20 [1, 0, 0, 0, 2, 0, 1] [1, 0, 0, 0, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1000012 : specInv 7 5 20 [1, 0, 0, 0, 0, 1, 2] = some [1, 0, 0, 0, 2, 0, 1] :=
  specInv_white_7 [1, 0, 0, 0, 0, 1, 2] [2, 1, 0, 2, 2, 0, 2] [0, 1, 0, 0, 1, 1, 1] [1, 0, 0, 0, 2, 0, 1] demoR1_1000012 demoR2_1000012 demoC_1000012 demoM_1000012

theorem demoR1_2000012 : invRung 7 5 20 [2, 0, 0, 0, 0, 1, 2] [2, 0, 0, 0, 0, 1, 2] 1 2 false = ([2, 2, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_2000012 : invRung 7 5 20 [2, 0, 0, 0, 0, 1, 2] [2, 2, 1, 1, 2, 0, 0] 3 1 true = ([0, 2, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_2000012 : fieldCube 7 5 20 [0, 2, 0, 2, 0, 2, 1] = [1, 0, 0, 0, 0, 2, 2] := by
  decide

theorem demoM_2000012 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 2, 2] [2, 0, 0, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000012 : mirrorTrits [1, 0, 0, 0, 0, 2, 2] = [2, 0, 0, 0, 0, 1, 1] := by
  decide

theorem demoInv_2000012 : specInv 7 5 20 [2, 0, 0, 0, 0, 1, 2] = some [2, 0, 0, 0, 0, 1, 1] :=
  specInv_mirror_7 [2, 0, 0, 0, 0, 1, 2] [2, 2, 1, 1, 2, 0, 0] [0, 2, 0, 2, 0, 2, 1] [1, 0, 0, 0, 0, 2, 2] [2, 0, 0, 0, 0, 1, 1] demoR1_2000012 demoR2_2000012 demoC_2000012 demoM_2000012 demoMir_2000012

theorem demoR1_0100012 : invRung 7 5 20 [0, 1, 0, 0, 0, 1, 2] [0, 1, 0, 0, 0, 1, 2] 1 2 false = ([2, 0, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_0100012 : invRung 7 5 20 [0, 1, 0, 0, 0, 1, 2] [2, 0, 1, 2, 2, 2, 0] 3 1 true = ([1, 2, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_0100012 : fieldCube 7 5 20 [1, 2, 2, 0, 1, 1, 0] = [2, 2, 1, 0, 1, 2, 2] := by
  decide

theorem demoM_0100012 : fieldMul 7 5 20 [2, 2, 1, 0, 1, 2, 2] [0, 1, 0, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100012 : mirrorTrits [2, 2, 1, 0, 1, 2, 2] = [1, 1, 2, 0, 2, 1, 1] := by
  decide

theorem demoInv_0100012 : specInv 7 5 20 [0, 1, 0, 0, 0, 1, 2] = some [1, 1, 2, 0, 2, 1, 1] :=
  specInv_mirror_7 [0, 1, 0, 0, 0, 1, 2] [2, 0, 1, 2, 2, 2, 0] [1, 2, 2, 0, 1, 1, 0] [2, 2, 1, 0, 1, 2, 2] [1, 1, 2, 0, 2, 1, 1] demoR1_0100012 demoR2_0100012 demoC_0100012 demoM_0100012 demoMir_0100012

theorem demoR1_1100012 : invRung 7 5 20 [1, 1, 0, 0, 0, 1, 2] [1, 1, 0, 0, 0, 1, 2] 1 2 false = ([0, 1, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1100012 : invRung 7 5 20 [1, 1, 0, 0, 0, 1, 2] [0, 1, 0, 1, 1, 0, 2] 3 1 true = ([0, 1, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_1100012 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 1, 0] = [0, 0, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_1100012 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 2, 1] [1, 1, 0, 0, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1100012 : specInv 7 5 20 [1, 1, 0, 0, 0, 1, 2] = some [0, 0, 0, 0, 1, 2, 1] :=
  specInv_white_7 [1, 1, 0, 0, 0, 1, 2] [0, 1, 0, 1, 1, 0, 2] [0, 1, 0, 2, 2, 1, 0] [0, 0, 0, 0, 1, 2, 1] demoR1_1100012 demoR2_1100012 demoC_1100012 demoM_1100012

theorem demoR1_2100012 : invRung 7 5 20 [2, 1, 0, 0, 0, 1, 2] [2, 1, 0, 0, 0, 1, 2] 1 2 false = ([2, 0, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_2100012 : invRung 7 5 20 [2, 1, 0, 0, 0, 1, 2] [2, 0, 1, 2, 2, 2, 1] 3 1 true = ([2, 0, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_2100012 : fieldCube 7 5 20 [2, 0, 2, 0, 1, 0, 2] = [2, 0, 1, 0, 2, 0, 2] := by
  decide

theorem demoM_2100012 : fieldMul 7 5 20 [2, 0, 1, 0, 2, 0, 2] [2, 1, 0, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100012 : mirrorTrits [2, 0, 1, 0, 2, 0, 2] = [1, 0, 2, 0, 1, 0, 1] := by
  decide

theorem demoInv_2100012 : specInv 7 5 20 [2, 1, 0, 0, 0, 1, 2] = some [1, 0, 2, 0, 1, 0, 1] :=
  specInv_mirror_7 [2, 1, 0, 0, 0, 1, 2] [2, 0, 1, 2, 2, 2, 1] [2, 0, 2, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0, 2] [1, 0, 2, 0, 1, 0, 1] demoR1_2100012 demoR2_2100012 demoC_2100012 demoM_2100012 demoMir_2100012

theorem demoR1_0200012 : invRung 7 5 20 [0, 2, 0, 0, 0, 1, 2] [0, 2, 0, 0, 0, 1, 2] 1 2 false = ([0, 1, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0200012 : invRung 7 5 20 [0, 2, 0, 0, 0, 1, 2] [0, 1, 1, 0, 1, 2, 1] 3 1 true = ([0, 1, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_0200012 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 1, 0] = [1, 1, 1, 1, 1, 1, 2] := by
  decide

theorem demoM_0200012 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 1, 2] [0, 2, 0, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200012 : mirrorTrits [1, 1, 1, 1, 1, 1, 2] = [2, 2, 2, 2, 2, 2, 1] := by
  decide

theorem demoInv_0200012 : specInv 7 5 20 [0, 2, 0, 0, 0, 1, 2] = some [2, 2, 2, 2, 2, 2, 1] :=
  specInv_mirror_7 [0, 2, 0, 0, 0, 1, 2] [0, 1, 1, 0, 1, 2, 1] [0, 1, 0, 0, 0, 1, 0] [1, 1, 1, 1, 1, 1, 2] [2, 2, 2, 2, 2, 2, 1] demoR1_0200012 demoR2_0200012 demoC_0200012 demoM_0200012 demoMir_0200012

theorem demoR1_1200012 : invRung 7 5 20 [1, 2, 0, 0, 0, 1, 2] [1, 2, 0, 0, 0, 1, 2] 1 2 false = ([1, 2, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_1200012 : invRung 7 5 20 [1, 2, 0, 0, 0, 1, 2] [1, 2, 1, 0, 0, 2, 2] 3 1 true = ([0, 1, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_1200012 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 2, 0] = [0, 0, 0, 2, 2, 1, 1] := by
  decide

theorem demoM_1200012 : fieldMul 7 5 20 [0, 0, 0, 2, 2, 1, 1] [1, 2, 0, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200012 : mirrorTrits [0, 0, 0, 2, 2, 1, 1] = [0, 0, 0, 1, 1, 2, 2] := by
  decide

theorem demoInv_1200012 : specInv 7 5 20 [1, 2, 0, 0, 0, 1, 2] = some [0, 0, 0, 1, 1, 2, 2] :=
  specInv_mirror_7 [1, 2, 0, 0, 0, 1, 2] [1, 2, 1, 0, 0, 2, 2] [0, 1, 2, 1, 1, 2, 0] [0, 0, 0, 2, 2, 1, 1] [0, 0, 0, 1, 1, 2, 2] demoR1_1200012 demoR2_1200012 demoC_1200012 demoM_1200012 demoMir_1200012

theorem demoR1_2200012 : invRung 7 5 20 [2, 2, 0, 0, 0, 1, 2] [2, 2, 0, 0, 0, 1, 2] 1 2 false = ([2, 0, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2200012 : invRung 7 5 20 [2, 2, 0, 0, 0, 1, 2] [2, 0, 2, 1, 1, 2, 0] 3 1 true = ([2, 2, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_2200012 : fieldCube 7 5 20 [2, 2, 2, 1, 2, 0, 0] = [0, 2, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_2200012 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 0, 1] [2, 2, 0, 0, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2200012 : specInv 7 5 20 [2, 2, 0, 0, 0, 1, 2] = some [0, 2, 1, 1, 0, 0, 1] :=
  specInv_white_7 [2, 2, 0, 0, 0, 1, 2] [2, 0, 2, 1, 1, 2, 0] [2, 2, 2, 1, 2, 0, 0] [0, 2, 1, 1, 0, 0, 1] demoR1_2200012 demoR2_2200012 demoC_2200012 demoM_2200012

theorem demoR1_0010012 : invRung 7 5 20 [0, 0, 1, 0, 0, 1, 2] [0, 0, 1, 0, 0, 1, 2] 1 2 false = ([2, 0, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0010012 : invRung 7 5 20 [0, 0, 1, 0, 0, 1, 2] [2, 0, 2, 1, 2, 1, 2] 3 1 true = ([2, 0, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_0010012 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 1, 1] = [2, 0, 2, 2, 2, 2, 0] := by
  decide

theorem demoM_0010012 : fieldMul 7 5 20 [2, 0, 2, 2, 2, 2, 0] [0, 0, 1, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010012 : mirrorTrits [2, 0, 2, 2, 2, 2, 0] = [1, 0, 1, 1, 1, 1, 0] := by
  decide

theorem demoInv_0010012 : specInv 7 5 20 [0, 0, 1, 0, 0, 1, 2] = some [1, 0, 1, 1, 1, 1, 0] :=
  specInv_mirror_7 [0, 0, 1, 0, 0, 1, 2] [2, 0, 2, 1, 2, 1, 2] [2, 0, 2, 2, 1, 1, 1] [2, 0, 2, 2, 2, 2, 0] [1, 0, 1, 1, 1, 1, 0] demoR1_0010012 demoR2_0010012 demoC_0010012 demoM_0010012 demoMir_0010012

theorem demoR1_1010012 : invRung 7 5 20 [1, 0, 1, 0, 0, 1, 2] [1, 0, 1, 0, 0, 1, 2] 1 2 false = ([2, 0, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1010012 : invRung 7 5 20 [1, 0, 1, 0, 0, 1, 2] [2, 0, 2, 0, 1, 1, 0] 3 1 true = ([0, 0, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_1010012 : fieldCube 7 5 20 [0, 0, 0, 1, 1, 0, 0] = [1, 1, 1, 1, 0, 2, 1] := by
  decide

theorem demoM_1010012 : fieldMul 7 5 20 [1, 1, 1, 1, 0, 2, 1] [1, 0, 1, 0, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1010012 : specInv 7 5 20 [1, 0, 1, 0, 0, 1, 2] = some [1, 1, 1, 1, 0, 2, 1] :=
  specInv_white_7 [1, 0, 1, 0, 0, 1, 2] [2, 0, 2, 0, 1, 1, 0] [0, 0, 0, 1, 1, 0, 0] [1, 1, 1, 1, 0, 2, 1] demoR1_1010012 demoR2_1010012 demoC_1010012 demoM_1010012

theorem demoR1_2010012 : invRung 7 5 20 [2, 0, 1, 0, 0, 1, 2] [2, 0, 1, 0, 0, 1, 2] 1 2 false = ([1, 1, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2010012 : invRung 7 5 20 [2, 0, 1, 0, 0, 1, 2] [1, 1, 2, 1, 1, 2, 2] 3 1 true = ([0, 1, 2, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_2010012 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 0, 1] = [1, 2, 0, 0, 1, 0, 1] := by
  decide

theorem demoM_2010012 : fieldMul 7 5 20 [1, 2, 0, 0, 1, 0, 1] [2, 0, 1, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010012 : mirrorTrits [1, 2, 0, 0, 1, 0, 1] = [2, 1, 0, 0, 2, 0, 2] := by
  decide

theorem demoInv_2010012 : specInv 7 5 20 [2, 0, 1, 0, 0, 1, 2] = some [2, 1, 0, 0, 2, 0, 2] :=
  specInv_mirror_7 [2, 0, 1, 0, 0, 1, 2] [1, 1, 2, 1, 1, 2, 2] [0, 1, 2, 1, 1, 0, 1] [1, 2, 0, 0, 1, 0, 1] [2, 1, 0, 0, 2, 0, 2] demoR1_2010012 demoR2_2010012 demoC_2010012 demoM_2010012 demoMir_2010012

theorem demoR1_0110012 : invRung 7 5 20 [0, 1, 1, 0, 0, 1, 2] [0, 1, 1, 0, 0, 1, 2] 1 2 false = ([2, 1, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0110012 : invRung 7 5 20 [0, 1, 1, 0, 0, 1, 2] [2, 1, 0, 1, 1, 1, 2] 3 1 true = ([0, 0, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0110012 : fieldCube 7 5 20 [0, 0, 1, 1, 0, 1, 1] = [2, 2, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_0110012 : fieldMul 7 5 20 [2, 2, 1, 1, 2, 0, 1] [0, 1, 1, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110012 : mirrorTrits [2, 2, 1, 1, 2, 0, 1] = [1, 1, 2, 2, 1, 0, 2] := by
  decide

theorem demoInv_0110012 : specInv 7 5 20 [0, 1, 1, 0, 0, 1, 2] = some [1, 1, 2, 2, 1, 0, 2] :=
  specInv_mirror_7 [0, 1, 1, 0, 0, 1, 2] [2, 1, 0, 1, 1, 1, 2] [0, 0, 1, 1, 0, 1, 1] [2, 2, 1, 1, 2, 0, 1] [1, 1, 2, 2, 1, 0, 2] demoR1_0110012 demoR2_0110012 demoC_0110012 demoM_0110012 demoMir_0110012

theorem demoR1_1110012 : invRung 7 5 20 [1, 1, 1, 0, 0, 1, 2] [1, 1, 1, 0, 0, 1, 2] 1 2 false = ([2, 2, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_1110012 : invRung 7 5 20 [1, 1, 1, 0, 0, 1, 2] [2, 2, 2, 2, 2, 2, 0] 3 1 true = ([0, 1, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_1110012 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 2, 1] = [2, 1, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_1110012 : fieldMul 7 5 20 [2, 1, 1, 0, 0, 1, 0] [1, 1, 1, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1110012 : mirrorTrits [2, 1, 1, 0, 0, 1, 0] = [1, 2, 2, 0, 0, 2, 0] := by
  decide

theorem demoInv_1110012 : specInv 7 5 20 [1, 1, 1, 0, 0, 1, 2] = some [1, 2, 2, 0, 0, 2, 0] :=
  specInv_mirror_7 [1, 1, 1, 0, 0, 1, 2] [2, 2, 2, 2, 2, 2, 0] [0, 1, 0, 0, 1, 2, 1] [2, 1, 1, 0, 0, 1, 0] [1, 2, 2, 0, 0, 2, 0] demoR1_1110012 demoR2_1110012 demoC_1110012 demoM_1110012 demoMir_1110012

theorem demoR1_2110012 : invRung 7 5 20 [2, 1, 1, 0, 0, 1, 2] [2, 1, 1, 0, 0, 1, 2] 1 2 false = ([0, 0, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_2110012 : invRung 7 5 20 [2, 1, 1, 0, 0, 1, 2] [0, 0, 0, 1, 1, 0, 2] 3 1 true = ([1, 1, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2110012 : fieldCube 7 5 20 [1, 1, 1, 1, 2, 2, 0] = [1, 1, 0, 0, 2, 2, 1] := by
  decide

theorem demoM_2110012 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 2, 1] [2, 1, 1, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110012 : mirrorTrits [1, 1, 0, 0, 2, 2, 1] = [2, 2, 0, 0, 1, 1, 2] := by
  decide

theorem demoInv_2110012 : specInv 7 5 20 [2, 1, 1, 0, 0, 1, 2] = some [2, 2, 0, 0, 1, 1, 2] :=
  specInv_mirror_7 [2, 1, 1, 0, 0, 1, 2] [0, 0, 0, 1, 1, 0, 2] [1, 1, 1, 1, 2, 2, 0] [1, 1, 0, 0, 2, 2, 1] [2, 2, 0, 0, 1, 1, 2] demoR1_2110012 demoR2_2110012 demoC_2110012 demoM_2110012 demoMir_2110012

theorem demoR1_0210012 : invRung 7 5 20 [0, 2, 1, 0, 0, 1, 2] [0, 2, 1, 0, 0, 1, 2] 1 2 false = ([0, 1, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0210012 : invRung 7 5 20 [0, 2, 1, 0, 0, 1, 2] [0, 1, 0, 0, 1, 2, 1] 3 1 true = ([0, 0, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_0210012 : fieldCube 7 5 20 [0, 0, 2, 2, 0, 2, 0] = [1, 2, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_0210012 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 1, 0] [0, 2, 1, 0, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0210012 : specInv 7 5 20 [0, 2, 1, 0, 0, 1, 2] = some [1, 2, 1, 0, 2, 1, 0] :=
  specInv_white_7 [0, 2, 1, 0, 0, 1, 2] [0, 1, 0, 0, 1, 2, 1] [0, 0, 2, 2, 0, 2, 0] [1, 2, 1, 0, 2, 1, 0] demoR1_0210012 demoR2_0210012 demoC_0210012 demoM_0210012

theorem demoR1_1210012 : invRung 7 5 20 [1, 2, 1, 0, 0, 1, 2] [1, 2, 1, 0, 0, 1, 2] 1 2 false = ([0, 1, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_1210012 : invRung 7 5 20 [1, 2, 1, 0, 0, 1, 2] [0, 1, 1, 1, 0, 0, 0] 3 1 true = ([1, 0, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1210012 : fieldCube 7 5 20 [1, 0, 2, 1, 2, 1, 0] = [0, 0, 2, 2, 1, 1, 0] := by
  decide

theorem demoM_1210012 : fieldMul 7 5 20 [0, 0, 2, 2, 1, 1, 0] [1, 2, 1, 0, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1210012 : specInv 7 5 20 [1, 2, 1, 0, 0, 1, 2] = some [0, 0, 2, 2, 1, 1, 0] :=
  specInv_white_7 [1, 2, 1, 0, 0, 1, 2] [0, 1, 1, 1, 0, 0, 0] [1, 0, 2, 1, 2, 1, 0] [0, 0, 2, 2, 1, 1, 0] demoR1_1210012 demoR2_1210012 demoC_1210012 demoM_1210012

theorem demoR1_2210012 : invRung 7 5 20 [2, 2, 1, 0, 0, 1, 2] [2, 2, 1, 0, 0, 1, 2] 1 2 false = ([0, 0, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_2210012 : invRung 7 5 20 [2, 2, 1, 0, 0, 1, 2] [0, 0, 0, 2, 0, 0, 0] 3 1 true = ([2, 2, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_2210012 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 0, 1] = [2, 0, 2, 2, 1, 0, 1] := by
  decide

theorem demoM_2210012 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 0, 1] [2, 2, 1, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210012 : mirrorTrits [2, 0, 2, 2, 1, 0, 1] = [1, 0, 1, 1, 2, 0, 2] := by
  decide

theorem demoInv_2210012 : specInv 7 5 20 [2, 2, 1, 0, 0, 1, 2] = some [1, 0, 1, 1, 2, 0, 2] :=
  specInv_mirror_7 [2, 2, 1, 0, 0, 1, 2] [0, 0, 0, 2, 0, 0, 0] [2, 2, 1, 0, 2, 0, 1] [2, 0, 2, 2, 1, 0, 1] [1, 0, 1, 1, 2, 0, 2] demoR1_2210012 demoR2_2210012 demoC_2210012 demoM_2210012 demoMir_2210012

theorem demoR1_0020012 : invRung 7 5 20 [0, 0, 2, 0, 0, 1, 2] [0, 0, 2, 0, 0, 1, 2] 1 2 false = ([2, 2, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_0020012 : invRung 7 5 20 [0, 0, 2, 0, 0, 1, 2] [2, 2, 1, 1, 2, 0, 1] 3 1 true = ([2, 1, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0020012 : fieldCube 7 5 20 [2, 1, 2, 0, 2, 0, 1] = [2, 0, 2, 1, 1, 0, 2] := by
  decide

theorem demoM_0020012 : fieldMul 7 5 20 [2, 0, 2, 1, 1, 0, 2] [0, 0, 2, 0, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0020012 : specInv 7 5 20 [0, 0, 2, 0, 0, 1, 2] = some [2, 0, 2, 1, 1, 0, 2] :=
  specInv_white_7 [0, 0, 2, 0, 0, 1, 2] [2, 2, 1, 1, 2, 0, 1] [2, 1, 2, 0, 2, 0, 1] [2, 0, 2, 1, 1, 0, 2] demoR1_0020012 demoR2_0020012 demoC_0020012 demoM_0020012

theorem demoR1_1020012 : invRung 7 5 20 [1, 0, 2, 0, 0, 1, 2] [1, 0, 2, 0, 0, 1, 2] 1 2 false = ([0, 0, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1020012 : invRung 7 5 20 [1, 0, 2, 0, 0, 1, 2] [0, 0, 1, 0, 2, 2, 1] 3 1 true = ([0, 1, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_1020012 : fieldCube 7 5 20 [0, 1, 0, 1, 1, 1, 2] = [2, 1, 0, 1, 0, 2, 2] := by
  decide

theorem demoM_1020012 : fieldMul 7 5 20 [2, 1, 0, 1, 0, 2, 2] [1, 0, 2, 0, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1020012 : specInv 7 5 20 [1, 0, 2, 0, 0, 1, 2] = some [2, 1, 0, 1, 0, 2, 2] :=
  specInv_white_7 [1, 0, 2, 0, 0, 1, 2] [0, 0, 1, 0, 2, 2, 1] [0, 1, 0, 1, 1, 1, 2] [2, 1, 0, 1, 0, 2, 2] demoR1_1020012 demoR2_1020012 demoC_1020012 demoM_1020012

theorem demoR1_2020012 : invRung 7 5 20 [2, 0, 2, 0, 0, 1, 2] [2, 0, 2, 0, 0, 1, 2] 1 2 false = ([0, 1, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_2020012 : invRung 7 5 20 [2, 0, 2, 0, 0, 1, 2] [0, 1, 1, 0, 2, 1, 0] 3 1 true = ([2, 0, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_2020012 : fieldCube 7 5 20 [2, 0, 0, 1, 2, 1, 1] = [1, 1, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_2020012 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 2, 2] [2, 0, 2, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020012 : mirrorTrits [1, 1, 1, 0, 2, 2, 2] = [2, 2, 2, 0, 1, 1, 1] := by
  decide

theorem demoInv_2020012 : specInv 7 5 20 [2, 0, 2, 0, 0, 1, 2] = some [2, 2, 2, 0, 1, 1, 1] :=
  specInv_mirror_7 [2, 0, 2, 0, 0, 1, 2] [0, 1, 1, 0, 2, 1, 0] [2, 0, 0, 1, 2, 1, 1] [1, 1, 1, 0, 2, 2, 2] [2, 2, 2, 0, 1, 1, 1] demoR1_2020012 demoR2_2020012 demoC_2020012 demoM_2020012 demoMir_2020012

theorem demoR1_0120012 : invRung 7 5 20 [0, 1, 2, 0, 0, 1, 2] [0, 1, 2, 0, 0, 1, 2] 1 2 false = ([1, 2, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_0120012 : invRung 7 5 20 [0, 1, 2, 0, 0, 1, 2] [1, 2, 0, 1, 1, 2, 1] 3 1 true = ([0, 1, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_0120012 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 1, 2] = [1, 1, 2, 1, 0, 1, 2] := by
  decide

theorem demoM_0120012 : fieldMul 7 5 20 [1, 1, 2, 1, 0, 1, 2] [0, 1, 2, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0120012 : mirrorTrits [1, 1, 2, 1, 0, 1, 2] = [2, 2, 1, 2, 0, 2, 1] := by
  decide

theorem demoInv_0120012 : specInv 7 5 20 [0, 1, 2, 0, 0, 1, 2] = some [2, 2, 1, 2, 0, 2, 1] :=
  specInv_mirror_7 [0, 1, 2, 0, 0, 1, 2] [1, 2, 0, 1, 1, 2, 1] [0, 1, 0, 0, 1, 1, 2] [1, 1, 2, 1, 0, 1, 2] [2, 2, 1, 2, 0, 2, 1] demoR1_0120012 demoR2_0120012 demoC_0120012 demoM_0120012 demoMir_0120012

theorem demoR1_1120012 : invRung 7 5 20 [1, 1, 2, 0, 0, 1, 2] [1, 1, 2, 0, 0, 1, 2] 1 2 false = ([2, 0, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1120012 : invRung 7 5 20 [1, 1, 2, 0, 0, 1, 2] [2, 0, 0, 1, 1, 0, 0] 3 1 true = ([2, 1, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_1120012 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 0, 1] = [0, 1, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_1120012 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 2, 2] [1, 1, 2, 0, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1120012 : specInv 7 5 20 [1, 1, 2, 0, 0, 1, 2] = some [0, 1, 0, 2, 1, 2, 2] :=
  specInv_white_7 [1, 1, 2, 0, 0, 1, 2] [2, 0, 0, 1, 1, 0, 0] [2, 1, 1, 1, 0, 0, 1] [0, 1, 0, 2, 1, 2, 2] demoR1_1120012 demoR2_1120012 demoC_1120012 demoM_1120012

theorem demoR1_2120012 : invRung 7 5 20 [2, 1, 2, 0, 0, 1, 2] [2, 1, 2, 0, 0, 1, 2] 1 2 false = ([1, 0, 2, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_2120012 : invRung 7 5 20 [2, 1, 2, 0, 0, 1, 2] [1, 0, 2, 1, 1, 0, 1] 3 1 true = ([1, 0, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2120012 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 2, 1] = [1, 0, 2, 1, 0, 1, 2] := by
  decide

theorem demoM_2120012 : fieldMul 7 5 20 [1, 0, 2, 1, 0, 1, 2] [2, 1, 2, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120012 : mirrorTrits [1, 0, 2, 1, 0, 1, 2] = [2, 0, 1, 2, 0, 2, 1] := by
  decide

theorem demoInv_2120012 : specInv 7 5 20 [2, 1, 2, 0, 0, 1, 2] = some [2, 0, 1, 2, 0, 2, 1] :=
  specInv_mirror_7 [2, 1, 2, 0, 0, 1, 2] [1, 0, 2, 1, 1, 0, 1] [1, 0, 0, 1, 0, 2, 1] [1, 0, 2, 1, 0, 1, 2] [2, 0, 1, 2, 0, 2, 1] demoR1_2120012 demoR2_2120012 demoC_2120012 demoM_2120012 demoMir_2120012

theorem demoR1_0220012 : invRung 7 5 20 [0, 2, 2, 0, 0, 1, 2] [0, 2, 2, 0, 0, 1, 2] 1 2 false = ([2, 0, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_0220012 : invRung 7 5 20 [0, 2, 2, 0, 0, 1, 2] [2, 0, 2, 0, 1, 0, 0] 3 1 true = ([0, 2, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_0220012 : fieldCube 7 5 20 [0, 2, 1, 0, 2, 2, 1] = [2, 2, 1, 2, 0, 2, 2] := by
  decide

theorem demoM_0220012 : fieldMul 7 5 20 [2, 2, 1, 2, 0, 2, 2] [0, 2, 2, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0220012 : mirrorTrits [2, 2, 1, 2, 0, 2, 2] = [1, 1, 2, 1, 0, 1, 1] := by
  decide

theorem demoInv_0220012 : specInv 7 5 20 [0, 2, 2, 0, 0, 1, 2] = some [1, 1, 2, 1, 0, 1, 1] :=
  specInv_mirror_7 [0, 2, 2, 0, 0, 1, 2] [2, 0, 2, 0, 1, 0, 0] [0, 2, 1, 0, 2, 2, 1] [2, 2, 1, 2, 0, 2, 2] [1, 1, 2, 1, 0, 1, 1] demoR1_0220012 demoR2_0220012 demoC_0220012 demoM_0220012 demoMir_0220012

theorem demoR1_1220012 : invRung 7 5 20 [1, 2, 2, 0, 0, 1, 2] [1, 2, 2, 0, 0, 1, 2] 1 2 false = ([0, 2, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_1220012 : invRung 7 5 20 [1, 2, 2, 0, 0, 1, 2] [0, 2, 2, 2, 0, 2, 2] 3 1 true = ([0, 0, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_1220012 : fieldCube 7 5 20 [0, 0, 1, 1, 1, 2, 0] = [0, 0, 0, 1, 2, 1, 0] := by
  decide

theorem demoM_1220012 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 1, 0] [1, 2, 2, 0, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220012 : mirrorTrits [0, 0, 0, 1, 2, 1, 0] = [0, 0, 0, 2, 1, 2, 0] := by
  decide

theorem demoInv_1220012 : specInv 7 5 20 [1, 2, 2, 0, 0, 1, 2] = some [0, 0, 0, 2, 1, 2, 0] :=
  specInv_mirror_7 [1, 2, 2, 0, 0, 1, 2] [0, 2, 2, 2, 0, 2, 2] [0, 0, 1, 1, 1, 2, 0] [0, 0, 0, 1, 2, 1, 0] [0, 0, 0, 2, 1, 2, 0] demoR1_1220012 demoR2_1220012 demoC_1220012 demoM_1220012 demoMir_1220012

theorem demoR1_2220012 : invRung 7 5 20 [2, 2, 2, 0, 0, 1, 2] [2, 2, 2, 0, 0, 1, 2] 1 2 false = ([1, 2, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2220012 : invRung 7 5 20 [2, 2, 2, 0, 0, 1, 2] [1, 2, 0, 0, 2, 2, 0] 3 1 true = ([0, 2, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_2220012 : fieldCube 7 5 20 [0, 2, 0, 2, 1, 2, 0] = [1, 0, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_2220012 : fieldMul 7 5 20 [1, 0, 1, 0, 2, 2, 2] [2, 2, 2, 0, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2220012 : specInv 7 5 20 [2, 2, 2, 0, 0, 1, 2] = some [1, 0, 1, 0, 2, 2, 2] :=
  specInv_white_7 [2, 2, 2, 0, 0, 1, 2] [1, 2, 0, 0, 2, 2, 0] [0, 2, 0, 2, 1, 2, 0] [1, 0, 1, 0, 2, 2, 2] demoR1_2220012 demoR2_2220012 demoC_2220012 demoM_2220012

theorem demoR1_0001012 : invRung 7 5 20 [0, 0, 0, 1, 0, 1, 2] [0, 0, 0, 1, 0, 1, 2] 1 2 false = ([1, 0, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_0001012 : invRung 7 5 20 [0, 0, 0, 1, 0, 1, 2] [1, 0, 2, 1, 0, 2, 2] 3 1 true = ([0, 0, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_0001012 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 0, 0] = [2, 1, 2, 1, 0, 0, 2] := by
  decide

theorem demoM_0001012 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 0, 2] [0, 0, 0, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0001012 : specInv 7 5 20 [0, 0, 0, 1, 0, 1, 2] = some [2, 1, 2, 1, 0, 0, 2] :=
  specInv_white_7 [0, 0, 0, 1, 0, 1, 2] [1, 0, 2, 1, 0, 2, 2] [0, 0, 1, 2, 1, 0, 0] [2, 1, 2, 1, 0, 0, 2] demoR1_0001012 demoR2_0001012 demoC_0001012 demoM_0001012

theorem demoR1_1001012 : invRung 7 5 20 [1, 0, 0, 1, 0, 1, 2] [1, 0, 0, 1, 0, 1, 2] 1 2 false = ([2, 1, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_1001012 : invRung 7 5 20 [1, 0, 0, 1, 0, 1, 2] [2, 1, 2, 2, 0, 1, 1] 3 1 true = ([2, 0, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1001012 : fieldCube 7 5 20 [2, 0, 2, 0, 1, 1, 0] = [0, 2, 1, 1, 1, 2, 2] := by
  decide

theorem demoM_1001012 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 2, 2] [1, 0, 0, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1001012 : mirrorTrits [0, 2, 1, 1, 1, 2, 2] = [0, 1, 2, 2, 2, 1, 1] := by
  decide

theorem demoInv_1001012 : specInv 7 5 20 [1, 0, 0, 1, 0, 1, 2] = some [0, 1, 2, 2, 2, 1, 1] :=
  specInv_mirror_7 [1, 0, 0, 1, 0, 1, 2] [2, 1, 2, 2, 0, 1, 1] [2, 0, 2, 0, 1, 1, 0] [0, 2, 1, 1, 1, 2, 2] [0, 1, 2, 2, 2, 1, 1] demoR1_1001012 demoR2_1001012 demoC_1001012 demoM_1001012 demoMir_1001012

theorem demoR1_2001012 : invRung 7 5 20 [2, 0, 0, 1, 0, 1, 2] [2, 0, 0, 1, 0, 1, 2] 1 2 false = ([2, 0, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_2001012 : invRung 7 5 20 [2, 0, 0, 1, 0, 1, 2] [2, 0, 0, 2, 1, 0, 0] 3 1 true = ([0, 2, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_2001012 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 0, 2] = [0, 0, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_2001012 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 0, 2] [2, 0, 0, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2001012 : specInv 7 5 20 [2, 0, 0, 1, 0, 1, 2] = some [0, 0, 1, 2, 2, 0, 2] :=
  specInv_white_7 [2, 0, 0, 1, 0, 1, 2] [2, 0, 0, 2, 1, 0, 0] [0, 2, 2, 0, 1, 0, 2] [0, 0, 1, 2, 2, 0, 2] demoR1_2001012 demoR2_2001012 demoC_2001012 demoM_2001012

theorem demoR1_0101012 : invRung 7 5 20 [0, 1, 0, 1, 0, 1, 2] [0, 1, 0, 1, 0, 1, 2] 1 2 false = ([0, 2, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_0101012 : invRung 7 5 20 [0, 1, 0, 1, 0, 1, 2] [0, 2, 0, 1, 2, 2, 2] 3 1 true = ([2, 1, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0101012 : fieldCube 7 5 20 [2, 1, 1, 0, 2, 1, 2] = [0, 2, 2, 2, 0, 2, 1] := by
  decide

theorem demoM_0101012 : fieldMul 7 5 20 [0, 2, 2, 2, 0, 2, 1] [0, 1, 0, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101012 : mirrorTrits [0, 2, 2, 2, 0, 2, 1] = [0, 1, 1, 1, 0, 1, 2] := by
  decide

theorem demoInv_0101012 : specInv 7 5 20 [0, 1, 0, 1, 0, 1, 2] = some [0, 1, 1, 1, 0, 1, 2] :=
  specInv_mirror_7 [0, 1, 0, 1, 0, 1, 2] [0, 2, 0, 1, 2, 2, 2] [2, 1, 1, 0, 2, 1, 2] [0, 2, 2, 2, 0, 2, 1] [0, 1, 1, 1, 0, 1, 2] demoR1_0101012 demoR2_0101012 demoC_0101012 demoM_0101012 demoMir_0101012

theorem demoR1_1101012 : invRung 7 5 20 [1, 1, 0, 1, 0, 1, 2] [1, 1, 0, 1, 0, 1, 2] 1 2 false = ([2, 2, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_1101012 : invRung 7 5 20 [1, 1, 0, 1, 0, 1, 2] [2, 2, 1, 2, 2, 0, 2] 3 1 true = ([0, 1, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_1101012 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 0, 1] = [1, 1, 0, 2, 1, 2, 1] := by
  decide

theorem demoM_1101012 : fieldMul 7 5 20 [1, 1, 0, 2, 1, 2, 1] [1, 1, 0, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1101012 : specInv 7 5 20 [1, 1, 0, 1, 0, 1, 2] = some [1, 1, 0, 2, 1, 2, 1] :=
  specInv_white_7 [1, 1, 0, 1, 0, 1, 2] [2, 2, 1, 2, 2, 0, 2] [0, 1, 0, 1, 0, 0, 1] [1, 1, 0, 2, 1, 2, 1] demoR1_1101012 demoR2_1101012 demoC_1101012 demoM_1101012

theorem demoR1_2101012 : invRung 7 5 20 [2, 1, 0, 1, 0, 1, 2] [2, 1, 0, 1, 0, 1, 2] 1 2 false = ([2, 2, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2101012 : invRung 7 5 20 [2, 1, 0, 1, 0, 1, 2] [2, 2, 2, 1, 0, 0, 2] 3 1 true = ([1, 2, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_2101012 : fieldCube 7 5 20 [1, 2, 2, 0, 0, 1, 1] = [2, 2, 0, 0, 2, 2, 2] := by
  decide

theorem demoM_2101012 : fieldMul 7 5 20 [2, 2, 0, 0, 2, 2, 2] [2, 1, 0, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2101012 : specInv 7 5 20 [2, 1, 0, 1, 0, 1, 2] = some [2, 2, 0, 0, 2, 2, 2] :=
  specInv_white_7 [2, 1, 0, 1, 0, 1, 2] [2, 2, 2, 1, 0, 0, 2] [1, 2, 2, 0, 0, 1, 1] [2, 2, 0, 0, 2, 2, 2] demoR1_2101012 demoR2_2101012 demoC_2101012 demoM_2101012

theorem demoR1_0201012 : invRung 7 5 20 [0, 2, 0, 1, 0, 1, 2] [0, 2, 0, 1, 0, 1, 2] 1 2 false = ([2, 2, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_0201012 : invRung 7 5 20 [0, 2, 0, 1, 0, 1, 2] [2, 2, 2, 1, 1, 0, 2] 3 1 true = ([0, 0, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0201012 : fieldCube 7 5 20 [0, 0, 2, 1, 0, 1, 1] = [2, 2, 1, 1, 2, 0, 2] := by
  decide

theorem demoM_0201012 : fieldMul 7 5 20 [2, 2, 1, 1, 2, 0, 2] [0, 2, 0, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0201012 : specInv 7 5 20 [0, 2, 0, 1, 0, 1, 2] = some [2, 2, 1, 1, 2, 0, 2] :=
  specInv_white_7 [0, 2, 0, 1, 0, 1, 2] [2, 2, 2, 1, 1, 0, 2] [0, 0, 2, 1, 0, 1, 1] [2, 2, 1, 1, 2, 0, 2] demoR1_0201012 demoR2_0201012 demoC_0201012 demoM_0201012

theorem demoR1_1201012 : invRung 7 5 20 [1, 2, 0, 1, 0, 1, 2] [1, 2, 0, 1, 0, 1, 2] 1 2 false = ([2, 2, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_1201012 : invRung 7 5 20 [1, 2, 0, 1, 0, 1, 2] [2, 2, 1, 0, 0, 2, 1] 3 1 true = ([1, 1, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_1201012 : fieldCube 7 5 20 [1, 1, 1, 2, 0, 1, 2] = [1, 0, 1, 0, 0, 2, 2] := by
  decide

theorem demoM_1201012 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 2, 2] [1, 2, 0, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201012 : mirrorTrits [1, 0, 1, 0, 0, 2, 2] = [2, 0, 2, 0, 0, 1, 1] := by
  decide

theorem demoInv_1201012 : specInv 7 5 20 [1, 2, 0, 1, 0, 1, 2] = some [2, 0, 2, 0, 0, 1, 1] :=
  specInv_mirror_7 [1, 2, 0, 1, 0, 1, 2] [2, 2, 1, 0, 0, 2, 1] [1, 1, 1, 2, 0, 1, 2] [1, 0, 1, 0, 0, 2, 2] [2, 0, 2, 0, 0, 1, 1] demoR1_1201012 demoR2_1201012 demoC_1201012 demoM_1201012 demoMir_1201012

theorem demoR1_2201012 : invRung 7 5 20 [2, 2, 0, 1, 0, 1, 2] [2, 2, 0, 1, 0, 1, 2] 1 2 false = ([2, 1, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_2201012 : invRung 7 5 20 [2, 2, 0, 1, 0, 1, 2] [2, 1, 2, 2, 0, 2, 0] 3 1 true = ([2, 1, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_2201012 : fieldCube 7 5 20 [2, 1, 1, 2, 1, 0, 1] = [1, 2, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_2201012 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 1, 0] [2, 2, 0, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2201012 : mirrorTrits [1, 2, 1, 0, 1, 1, 0] = [2, 1, 2, 0, 2, 2, 0] := by
  decide

theorem demoInv_2201012 : specInv 7 5 20 [2, 2, 0, 1, 0, 1, 2] = some [2, 1, 2, 0, 2, 2, 0] :=
  specInv_mirror_7 [2, 2, 0, 1, 0, 1, 2] [2, 1, 2, 2, 0, 2, 0] [2, 1, 1, 2, 1, 0, 1] [1, 2, 1, 0, 1, 1, 0] [2, 1, 2, 0, 2, 2, 0] demoR1_2201012 demoR2_2201012 demoC_2201012 demoM_2201012 demoMir_2201012

theorem demoR1_0011012 : invRung 7 5 20 [0, 0, 1, 1, 0, 1, 2] [0, 0, 1, 1, 0, 1, 2] 1 2 false = ([1, 2, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_0011012 : invRung 7 5 20 [0, 0, 1, 1, 0, 1, 2] [1, 2, 1, 2, 1, 2, 0] 3 1 true = ([2, 0, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0011012 : fieldCube 7 5 20 [2, 0, 1, 0, 2, 1, 0] = [0, 0, 1, 2, 1, 0, 2] := by
  decide

theorem demoM_0011012 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 0, 2] [0, 0, 1, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011012 : mirrorTrits [0, 0, 1, 2, 1, 0, 2] = [0, 0, 2, 1, 2, 0, 1] := by
  decide

theorem demoInv_0011012 : specInv 7 5 20 [0, 0, 1, 1, 0, 1, 2] = some [0, 0, 2, 1, 2, 0, 1] :=
  specInv_mirror_7 [0, 0, 1, 1, 0, 1, 2] [1, 2, 1, 2, 1, 2, 0] [2, 0, 1, 0, 2, 1, 0] [0, 0, 1, 2, 1, 0, 2] [0, 0, 2, 1, 2, 0, 1] demoR1_0011012 demoR2_0011012 demoC_0011012 demoM_0011012 demoMir_0011012

theorem demoR1_1011012 : invRung 7 5 20 [1, 0, 1, 1, 0, 1, 2] [1, 0, 1, 1, 0, 1, 2] 1 2 false = ([1, 2, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_1011012 : invRung 7 5 20 [1, 0, 1, 1, 0, 1, 2] [1, 2, 1, 2, 1, 1, 0] 3 1 true = ([2, 1, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1011012 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 2, 1] = [2, 1, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_1011012 : fieldMul 7 5 20 [2, 1, 2, 0, 0, 2, 2] [1, 0, 1, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1011012 : specInv 7 5 20 [1, 0, 1, 1, 0, 1, 2] = some [2, 1, 2, 0, 0, 2, 2] :=
  specInv_white_7 [1, 0, 1, 1, 0, 1, 2] [1, 2, 1, 2, 1, 1, 0] [2, 1, 2, 1, 1, 2, 1] [2, 1, 2, 0, 0, 2, 2] demoR1_1011012 demoR2_1011012 demoC_1011012 demoM_1011012

theorem demoR1_2011012 : invRung 7 5 20 [2, 0, 1, 1, 0, 1, 2] [2, 0, 1, 1, 0, 1, 2] 1 2 false = ([0, 2, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_2011012 : invRung 7 5 20 [2, 0, 1, 1, 0, 1, 2] [0, 2, 2, 0, 1, 2, 1] 3 1 true = ([0, 2, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_2011012 : fieldCube 7 5 20 [0, 2, 2, 0, 0, 0, 2] = [0, 2, 1, 1, 2, 2, 1] := by
  decide

theorem demoM_2011012 : fieldMul 7 5 20 [0, 2, 1, 1, 2, 2, 1] [2, 0, 1, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2011012 : specInv 7 5 20 [2, 0, 1, 1, 0, 1, 2] = some [0, 2, 1, 1, 2, 2, 1] :=
  specInv_white_7 [2, 0, 1, 1, 0, 1, 2] [0, 2, 2, 0, 1, 2, 1] [0, 2, 2, 0, 0, 0, 2] [0, 2, 1, 1, 2, 2, 1] demoR1_2011012 demoR2_2011012 demoC_2011012 demoM_2011012

theorem demoR1_0111012 : invRung 7 5 20 [0, 1, 1, 1, 0, 1, 2] [0, 1, 1, 1, 0, 1, 2] 1 2 false = ([0, 0, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_0111012 : invRung 7 5 20 [0, 1, 1, 1, 0, 1, 2] [0, 0, 0, 1, 0, 1, 1] 3 1 true = ([0, 0, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_0111012 : fieldCube 7 5 20 [0, 0, 2, 0, 2, 0, 0] = [0, 2, 0, 2, 0, 2, 1] := by
  decide

theorem demoM_0111012 : fieldMul 7 5 20 [0, 2, 0, 2, 0, 2, 1] [0, 1, 1, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111012 : mirrorTrits [0, 2, 0, 2, 0, 2, 1] = [0, 1, 0, 1, 0, 1, 2] := by
  decide

theorem demoInv_0111012 : specInv 7 5 20 [0, 1, 1, 1, 0, 1, 2] = some [0, 1, 0, 1, 0, 1, 2] :=
  specInv_mirror_7 [0, 1, 1, 1, 0, 1, 2] [0, 0, 0, 1, 0, 1, 1] [0, 0, 2, 0, 2, 0, 0] [0, 2, 0, 2, 0, 2, 1] [0, 1, 0, 1, 0, 1, 2] demoR1_0111012 demoR2_0111012 demoC_0111012 demoM_0111012 demoMir_0111012

theorem demoR1_1111012 : invRung 7 5 20 [1, 1, 1, 1, 0, 1, 2] [1, 1, 1, 1, 0, 1, 2] 1 2 false = ([1, 1, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1111012 : invRung 7 5 20 [1, 1, 1, 1, 0, 1, 2] [1, 1, 2, 0, 1, 0, 1] 3 1 true = ([2, 1, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_1111012 : fieldCube 7 5 20 [2, 1, 0, 1, 0, 0, 1] = [0, 1, 0, 2, 1, 2, 1] := by
  decide

theorem demoM_1111012 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 2, 1] [1, 1, 1, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111012 : mirrorTrits [0, 1, 0, 2, 1, 2, 1] = [0, 2, 0, 1, 2, 1, 2] := by
  decide

theorem demoInv_1111012 : specInv 7 5 20 [1, 1, 1, 1, 0, 1, 2] = some [0, 2, 0, 1, 2, 1, 2] :=
  specInv_mirror_7 [1, 1, 1, 1, 0, 1, 2] [1, 1, 2, 0, 1, 0, 1] [2, 1, 0, 1, 0, 0, 1] [0, 1, 0, 2, 1, 2, 1] [0, 2, 0, 1, 2, 1, 2] demoR1_1111012 demoR2_1111012 demoC_1111012 demoM_1111012 demoMir_1111012

theorem demoR1_2111012 : invRung 7 5 20 [2, 1, 1, 1, 0, 1, 2] [2, 1, 1, 1, 0, 1, 2] 1 2 false = ([0, 1, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_2111012 : invRung 7 5 20 [2, 1, 1, 1, 0, 1, 2] [0, 1, 1, 2, 2, 0, 2] 3 1 true = ([1, 1, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_2111012 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 2, 2] = [0, 1, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_2111012 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 1, 1] [2, 1, 1, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2111012 : specInv 7 5 20 [2, 1, 1, 1, 0, 1, 2] = some [0, 1, 0, 0, 1, 1, 1] :=
  specInv_white_7 [2, 1, 1, 1, 0, 1, 2] [0, 1, 1, 2, 2, 0, 2] [1, 1, 1, 0, 0, 2, 2] [0, 1, 0, 0, 1, 1, 1] demoR1_2111012 demoR2_2111012 demoC_2111012 demoM_2111012

theorem demoR1_0211012 : invRung 7 5 20 [0, 2, 1, 1, 0, 1, 2] [0, 2, 1, 1, 0, 1, 2] 1 2 false = ([0, 1, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0211012 : invRung 7 5 20 [0, 2, 1, 1, 0, 1, 2] [0, 1, 1, 0, 2, 2, 2] 3 1 true = ([1, 2, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_0211012 : fieldCube 7 5 20 [1, 2, 2, 1, 1, 1, 0] = [0, 2, 2, 0, 1, 0, 2] := by
  decide

theorem demoM_0211012 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 0, 2] [0, 2, 1, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0211012 : specInv 7 5 20 [0, 2, 1, 1, 0, 1, 2] = some [0, 2, 2, 0, 1, 0, 2] :=
  specInv_white_7 [0, 2, 1, 1, 0, 1, 2] [0, 1, 1, 0, 2, 2, 2] [1, 2, 2, 1, 1, 1, 0] [0, 2, 2, 0, 1, 0, 2] demoR1_0211012 demoR2_0211012 demoC_0211012 demoM_0211012

theorem demoR1_1211012 : invRung 7 5 20 [1, 2, 1, 1, 0, 1, 2] [1, 2, 1, 1, 0, 1, 2] 1 2 false = ([2, 1, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_1211012 : invRung 7 5 20 [1, 2, 1, 1, 0, 1, 2] [2, 1, 2, 2, 0, 0, 0] 3 1 true = ([2, 0, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_1211012 : fieldCube 7 5 20 [2, 0, 2, 0, 2, 1, 0] = [0, 0, 1, 2, 1, 0, 0] := by
  decide

theorem demoM_1211012 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 0, 0] [1, 2, 1, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1211012 : specInv 7 5 20 [1, 2, 1, 1, 0, 1, 2] = some [0, 0, 1, 2, 1, 0, 0] :=
  specInv_white_7 [1, 2, 1, 1, 0, 1, 2] [2, 1, 2, 2, 0, 0, 0] [2, 0, 2, 0, 2, 1, 0] [0, 0, 1, 2, 1, 0, 0] demoR1_1211012 demoR2_1211012 demoC_1211012 demoM_1211012

theorem demoR1_2211012 : invRung 7 5 20 [2, 2, 1, 1, 0, 1, 2] [2, 2, 1, 1, 0, 1, 2] 1 2 false = ([1, 2, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2211012 : invRung 7 5 20 [2, 2, 1, 1, 0, 1, 2] [1, 2, 2, 0, 1, 1, 2] 3 1 true = ([0, 1, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2211012 : fieldCube 7 5 20 [0, 1, 2, 1, 2, 1, 0] = [2, 0, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_2211012 : fieldMul 7 5 20 [2, 0, 2, 0, 1, 1, 0] [2, 2, 1, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211012 : mirrorTrits [2, 0, 2, 0, 1, 1, 0] = [1, 0, 1, 0, 2, 2, 0] := by
  decide

theorem demoInv_2211012 : specInv 7 5 20 [2, 2, 1, 1, 0, 1, 2] = some [1, 0, 1, 0, 2, 2, 0] :=
  specInv_mirror_7 [2, 2, 1, 1, 0, 1, 2] [1, 2, 2, 0, 1, 1, 2] [0, 1, 2, 1, 2, 1, 0] [2, 0, 2, 0, 1, 1, 0] [1, 0, 1, 0, 2, 2, 0] demoR1_2211012 demoR2_2211012 demoC_2211012 demoM_2211012 demoMir_2211012

theorem demoR1_0021012 : invRung 7 5 20 [0, 0, 2, 1, 0, 1, 2] [0, 0, 2, 1, 0, 1, 2] 1 2 false = ([1, 0, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_0021012 : invRung 7 5 20 [0, 0, 2, 1, 0, 1, 2] [1, 0, 0, 2, 1, 0, 2] 3 1 true = ([1, 1, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_0021012 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 1, 2] = [2, 1, 2, 1, 0, 1, 2] := by
  decide

theorem demoM_0021012 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 1, 2] [0, 0, 2, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021012 : mirrorTrits [2, 1, 2, 1, 0, 1, 2] = [1, 2, 1, 2, 0, 2, 1] := by
  decide

theorem demoInv_0021012 : specInv 7 5 20 [0, 0, 2, 1, 0, 1, 2] = some [1, 2, 1, 2, 0, 2, 1] :=
  specInv_mirror_7 [0, 0, 2, 1, 0, 1, 2] [1, 0, 0, 2, 1, 0, 2] [1, 1, 0, 0, 1, 1, 2] [2, 1, 2, 1, 0, 1, 2] [1, 2, 1, 2, 0, 2, 1] demoR1_0021012 demoR2_0021012 demoC_0021012 demoM_0021012 demoMir_0021012

theorem demoR1_1021012 : invRung 7 5 20 [1, 0, 2, 1, 0, 1, 2] [1, 0, 2, 1, 0, 1, 2] 1 2 false = ([2, 2, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_1021012 : invRung 7 5 20 [1, 0, 2, 1, 0, 1, 2] [2, 2, 1, 1, 1, 2, 2] 3 1 true = ([2, 0, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_1021012 : fieldCube 7 5 20 [2, 0, 0, 0, 2, 2, 1] = [1, 2, 1, 0, 0, 2, 1] := by
  decide

theorem demoM_1021012 : fieldMul 7 5 20 [1, 2, 1, 0, 0, 2, 1] [1, 0, 2, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1021012 : specInv 7 5 20 [1, 0, 2, 1, 0, 1, 2] = some [1, 2, 1, 0, 0, 2, 1] :=
  specInv_white_7 [1, 0, 2, 1, 0, 1, 2] [2, 2, 1, 1, 1, 2, 2] [2, 0, 0, 0, 2, 2, 1] [1, 2, 1, 0, 0, 2, 1] demoR1_1021012 demoR2_1021012 demoC_1021012 demoM_1021012

theorem demoR1_2021012 : invRung 7 5 20 [2, 0, 2, 1, 0, 1, 2] [2, 0, 2, 1, 0, 1, 2] 1 2 false = ([2, 0, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_2021012 : invRung 7 5 20 [2, 0, 2, 1, 0, 1, 2] [2, 0, 0, 0, 0, 2, 1] 3 1 true = ([0, 2, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_2021012 : fieldCube 7 5 20 [0, 2, 2, 2, 0, 0, 2] = [2, 2, 0, 1, 2, 1, 1] := by
  decide

theorem demoM_2021012 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 1, 1] [2, 0, 2, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021012 : mirrorTrits [2, 2, 0, 1, 2, 1, 1] = [1, 1, 0, 2, 1, 2, 2] := by
  decide

theorem demoInv_2021012 : specInv 7 5 20 [2, 0, 2, 1, 0, 1, 2] = some [1, 1, 0, 2, 1, 2, 2] :=
  specInv_mirror_7 [2, 0, 2, 1, 0, 1, 2] [2, 0, 0, 0, 0, 2, 1] [0, 2, 2, 2, 0, 0, 2] [2, 2, 0, 1, 2, 1, 1] [1, 1, 0, 2, 1, 2, 2] demoR1_2021012 demoR2_2021012 demoC_2021012 demoM_2021012 demoMir_2021012

theorem demoR1_0121012 : invRung 7 5 20 [0, 1, 2, 1, 0, 1, 2] [0, 1, 2, 1, 0, 1, 2] 1 2 false = ([0, 2, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_0121012 : invRung 7 5 20 [0, 1, 2, 1, 0, 1, 2] [0, 2, 2, 2, 2, 0, 0] 3 1 true = ([1, 1, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0121012 : fieldCube 7 5 20 [1, 1, 1, 1, 0, 0, 1] = [2, 1, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_0121012 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 2, 2] [0, 1, 2, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0121012 : specInv 7 5 20 [0, 1, 2, 1, 0, 1, 2] = some [2, 1, 0, 2, 1, 2, 2] :=
  specInv_white_7 [0, 1, 2, 1, 0, 1, 2] [0, 2, 2, 2, 2, 0, 0] [1, 1, 1, 1, 0, 0, 1] [2, 1, 0, 2, 1, 2, 2] demoR1_0121012 demoR2_0121012 demoC_0121012 demoM_0121012

theorem demoR1_1121012 : invRung 7 5 20 [1, 1, 2, 1, 0, 1, 2] [1, 1, 2, 1, 0, 1, 2] 1 2 false = ([2, 1, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1121012 : invRung 7 5 20 [1, 1, 2, 1, 0, 1, 2] [2, 1, 0, 2, 1, 0, 2] 3 1 true = ([1, 0, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_1121012 : fieldCube 7 5 20 [1, 0, 0, 0, 2, 2, 1] = [0, 2, 1, 0, 0, 2, 1] := by
  decide

theorem demoM_1121012 : fieldMul 7 5 20 [0, 2, 1, 0, 0, 2, 1] [1, 1, 2, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1121012 : specInv 7 5 20 [1, 1, 2, 1, 0, 1, 2] = some [0, 2, 1, 0, 0, 2, 1] :=
  specInv_white_7 [1, 1, 2, 1, 0, 1, 2] [2, 1, 0, 2, 1, 0, 2] [1, 0, 0, 0, 2, 2, 1] [0, 2, 1, 0, 0, 2, 1] demoR1_1121012 demoR2_1121012 demoC_1121012 demoM_1121012

theorem demoR1_2121012 : invRung 7 5 20 [2, 1, 2, 1, 0, 1, 2] [2, 1, 2, 1, 0, 1, 2] 1 2 false = ([2, 1, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_2121012 : invRung 7 5 20 [2, 1, 2, 1, 0, 1, 2] [2, 1, 1, 1, 2, 0, 0] 3 1 true = ([0, 0, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_2121012 : fieldCube 7 5 20 [0, 0, 0, 2, 0, 1, 2] = [0, 0, 1, 2, 0, 2, 1] := by
  decide

theorem demoM_2121012 : fieldMul 7 5 20 [0, 0, 1, 2, 0, 2, 1] [2, 1, 2, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2121012 : specInv 7 5 20 [2, 1, 2, 1, 0, 1, 2] = some [0, 0, 1, 2, 0, 2, 1] :=
  specInv_white_7 [2, 1, 2, 1, 0, 1, 2] [2, 1, 1, 1, 2, 0, 0] [0, 0, 0, 2, 0, 1, 2] [0, 0, 1, 2, 0, 2, 1] demoR1_2121012 demoR2_2121012 demoC_2121012 demoM_2121012

theorem demoR1_0221012 : invRung 7 5 20 [0, 2, 2, 1, 0, 1, 2] [0, 2, 2, 1, 0, 1, 2] 1 2 false = ([1, 0, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_0221012 : invRung 7 5 20 [0, 2, 2, 1, 0, 1, 2] [1, 0, 1, 2, 0, 0, 1] 3 1 true = ([2, 1, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_0221012 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 1, 0] = [1, 2, 2, 2, 1, 0, 2] := by
  decide

theorem demoM_0221012 : fieldMul 7 5 20 [1, 2, 2, 2, 1, 0, 2] [0, 2, 2, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0221012 : mirrorTrits [1, 2, 2, 2, 1, 0, 2] = [2, 1, 1, 1, 2, 0, 1] := by
  decide

theorem demoInv_0221012 : specInv 7 5 20 [0, 2, 2, 1, 0, 1, 2] = some [2, 1, 1, 1, 2, 0, 1] :=
  specInv_mirror_7 [0, 2, 2, 1, 0, 1, 2] [1, 0, 1, 2, 0, 0, 1] [2, 1, 2, 1, 1, 1, 0] [1, 2, 2, 2, 1, 0, 2] [2, 1, 1, 1, 2, 0, 1] demoR1_0221012 demoR2_0221012 demoC_0221012 demoM_0221012 demoMir_0221012

theorem demoR1_1221012 : invRung 7 5 20 [1, 2, 2, 1, 0, 1, 2] [1, 2, 2, 1, 0, 1, 2] 1 2 false = ([1, 0, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_1221012 : invRung 7 5 20 [1, 2, 2, 1, 0, 1, 2] [1, 0, 2, 1, 0, 0, 0] 3 1 true = ([1, 2, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_1221012 : fieldCube 7 5 20 [1, 2, 2, 2, 1, 1, 1] = [1, 0, 2, 1, 2, 2, 0] := by
  decide

theorem demoM_1221012 : fieldMul 7 5 20 [1, 0, 2, 1, 2, 2, 0] [1, 2, 2, 1, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221012 : mirrorTrits [1, 0, 2, 1, 2, 2, 0] = [2, 0, 1, 2, 1, 1, 0] := by
  decide

theorem demoInv_1221012 : specInv 7 5 20 [1, 2, 2, 1, 0, 1, 2] = some [2, 0, 1, 2, 1, 1, 0] :=
  specInv_mirror_7 [1, 2, 2, 1, 0, 1, 2] [1, 0, 2, 1, 0, 0, 0] [1, 2, 2, 2, 1, 1, 1] [1, 0, 2, 1, 2, 2, 0] [2, 0, 1, 2, 1, 1, 0] demoR1_1221012 demoR2_1221012 demoC_1221012 demoM_1221012 demoMir_1221012

theorem demoR1_2221012 : invRung 7 5 20 [2, 2, 2, 1, 0, 1, 2] [2, 2, 2, 1, 0, 1, 2] 1 2 false = ([1, 0, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_2221012 : invRung 7 5 20 [2, 2, 2, 1, 0, 1, 2] [1, 0, 2, 1, 2, 2, 1] 3 1 true = ([1, 1, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_2221012 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 0, 2] = [2, 2, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_2221012 : fieldMul 7 5 20 [2, 2, 2, 0, 2, 0, 2] [2, 2, 2, 1, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2221012 : specInv 7 5 20 [2, 2, 2, 1, 0, 1, 2] = some [2, 2, 2, 0, 2, 0, 2] :=
  specInv_white_7 [2, 2, 2, 1, 0, 1, 2] [1, 0, 2, 1, 2, 2, 1] [1, 1, 0, 1, 0, 0, 2] [2, 2, 2, 0, 2, 0, 2] demoR1_2221012 demoR2_2221012 demoC_2221012 demoM_2221012

theorem demoR1_0002012 : invRung 7 5 20 [0, 0, 0, 2, 0, 1, 2] [0, 0, 0, 2, 0, 1, 2] 1 2 false = ([1, 2, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0002012 : invRung 7 5 20 [0, 0, 0, 2, 0, 1, 2] [1, 2, 0, 0, 1, 1, 1] 3 1 true = ([2, 1, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_0002012 : fieldCube 7 5 20 [2, 1, 2, 0, 0, 2, 2] = [1, 1, 0, 0, 1, 1, 2] := by
  decide

theorem demoM_0002012 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 1, 2] [0, 0, 0, 2, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0002012 : specInv 7 5 20 [0, 0, 0, 2, 0, 1, 2] = some [1, 1, 0, 0, 1, 1, 2] :=
  specInv_white_7 [0, 0, 0, 2, 0, 1, 2] [1, 2, 0, 0, 1, 1, 1] [2, 1, 2, 0, 0, 2, 2] [1, 1, 0, 0, 1, 1, 2] demoR1_0002012 demoR2_0002012 demoC_0002012 demoM_0002012

theorem demoR1_1002012 : invRung 7 5 20 [1, 0, 0, 2, 0, 1, 2] [1, 0, 0, 2, 0, 1, 2] 1 2 false = ([2, 1, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_1002012 : invRung 7 5 20 [1, 0, 0, 2, 0, 1, 2] [2, 1, 1, 1, 0, 1, 2] 3 1 true = ([0, 2, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_1002012 : fieldCube 7 5 20 [0, 2, 1, 1, 2, 2, 1] = [0, 2, 2, 2, 0, 0, 2] := by
  decide

theorem demoM_1002012 : fieldMul 7 5 20 [0, 2, 2, 2, 0, 0, 2] [1, 0, 0, 2, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1002012 : specInv 7 5 20 [1, 0, 0, 2, 0, 1, 2] = some [0, 2, 2, 2, 0, 0, 2] :=
  specInv_white_7 [1, 0, 0, 2, 0, 1, 2] [2, 1, 1, 1, 0, 1, 2] [0, 2, 1, 1, 2, 2, 1] [0, 2, 2, 2, 0, 0, 2] demoR1_1002012 demoR2_1002012 demoC_1002012 demoM_1002012

theorem demoR1_2002012 : invRung 7 5 20 [2, 0, 0, 2, 0, 1, 2] [2, 0, 0, 2, 0, 1, 2] 1 2 false = ([2, 0, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2002012 : invRung 7 5 20 [2, 0, 0, 2, 0, 1, 2] [2, 0, 1, 0, 2, 2, 0] 3 1 true = ([0, 0, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_2002012 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 0, 2] = [2, 0, 0, 0, 2, 2, 1] := by
  decide

theorem demoM_2002012 : fieldMul 7 5 20 [2, 0, 0, 0, 2, 2, 1] [2, 0, 0, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002012 : mirrorTrits [2, 0, 0, 0, 2, 2, 1] = [1, 0, 0, 0, 1, 1, 2] := by
  decide

theorem demoInv_2002012 : specInv 7 5 20 [2, 0, 0, 2, 0, 1, 2] = some [1, 0, 0, 0, 1, 1, 2] :=
  specInv_mirror_7 [2, 0, 0, 2, 0, 1, 2] [2, 0, 1, 0, 2, 2, 0] [0, 0, 1, 2, 1, 0, 2] [2, 0, 0, 0, 2, 2, 1] [1, 0, 0, 0, 1, 1, 2] demoR1_2002012 demoR2_2002012 demoC_2002012 demoM_2002012 demoMir_2002012

theorem demoR1_0102012 : invRung 7 5 20 [0, 1, 0, 2, 0, 1, 2] [0, 1, 0, 2, 0, 1, 2] 1 2 false = ([0, 0, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_0102012 : invRung 7 5 20 [0, 1, 0, 2, 0, 1, 2] [0, 0, 2, 2, 0, 2, 2] 3 1 true = ([2, 0, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_0102012 : fieldCube 7 5 20 [2, 0, 2, 2, 2, 1, 1] = [2, 1, 2, 0, 2, 0, 1] := by
  decide

theorem demoM_0102012 : fieldMul 7 5 20 [2, 1, 2, 0, 2, 0, 1] [0, 1, 0, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102012 : mirrorTrits [2, 1, 2, 0, 2, 0, 1] = [1, 2, 1, 0, 1, 0, 2] := by
  decide

theorem demoInv_0102012 : specInv 7 5 20 [0, 1, 0, 2, 0, 1, 2] = some [1, 2, 1, 0, 1, 0, 2] :=
  specInv_mirror_7 [0, 1, 0, 2, 0, 1, 2] [0, 0, 2, 2, 0, 2, 2] [2, 0, 2, 2, 2, 1, 1] [2, 1, 2, 0, 2, 0, 1] [1, 2, 1, 0, 1, 0, 2] demoR1_0102012 demoR2_0102012 demoC_0102012 demoM_0102012 demoMir_0102012

theorem demoR1_1102012 : invRung 7 5 20 [1, 1, 0, 2, 0, 1, 2] [1, 1, 0, 2, 0, 1, 2] 1 2 false = ([0, 1, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1102012 : invRung 7 5 20 [1, 1, 0, 2, 0, 1, 2] [0, 1, 1, 0, 1, 0, 1] 3 1 true = ([2, 0, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_1102012 : fieldCube 7 5 20 [2, 0, 2, 1, 1, 2, 0] = [2, 0, 0, 1, 2, 1, 1] := by
  decide

theorem demoM_1102012 : fieldMul 7 5 20 [2, 0, 0, 1, 2, 1, 1] [1, 1, 0, 2, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1102012 : specInv 7 5 20 [1, 1, 0, 2, 0, 1, 2] = some [2, 0, 0, 1, 2, 1, 1] :=
  specInv_white_7 [1, 1, 0, 2, 0, 1, 2] [0, 1, 1, 0, 1, 0, 1] [2, 0, 2, 1, 1, 2, 0] [2, 0, 0, 1, 2, 1, 1] demoR1_1102012 demoR2_1102012 demoC_1102012 demoM_1102012

theorem demoR1_2102012 : invRung 7 5 20 [2, 1, 0, 2, 0, 1, 2] [2, 1, 0, 2, 0, 1, 2] 1 2 false = ([1, 1, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_2102012 : invRung 7 5 20 [2, 1, 0, 2, 0, 1, 2] [1, 1, 1, 1, 2, 1, 0] 3 1 true = ([1, 2, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_2102012 : fieldCube 7 5 20 [1, 2, 2, 0, 0, 2, 2] = [0, 1, 0, 1, 1, 1, 2] := by
  decide

theorem demoM_2102012 : fieldMul 7 5 20 [0, 1, 0, 1, 1, 1, 2] [2, 1, 0, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2102012 : mirrorTrits [0, 1, 0, 1, 1, 1, 2] = [0, 2, 0, 2, 2, 2, 1] := by
  decide

theorem demoInv_2102012 : specInv 7 5 20 [2, 1, 0, 2, 0, 1, 2] = some [0, 2, 0, 2, 2, 2, 1] :=
  specInv_mirror_7 [2, 1, 0, 2, 0, 1, 2] [1, 1, 1, 1, 2, 1, 0] [1, 2, 2, 0, 0, 2, 2] [0, 1, 0, 1, 1, 1, 2] [0, 2, 0, 2, 2, 2, 1] demoR1_2102012 demoR2_2102012 demoC_2102012 demoM_2102012 demoMir_2102012

theorem demoR1_0202012 : invRung 7 5 20 [0, 2, 0, 2, 0, 1, 2] [0, 2, 0, 2, 0, 1, 2] 1 2 false = ([2, 0, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0202012 : invRung 7 5 20 [0, 2, 0, 2, 0, 1, 2] [2, 0, 2, 2, 1, 2, 1] 3 1 true = ([2, 2, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0202012 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 0, 1] = [1, 2, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_0202012 : fieldMul 7 5 20 [1, 2, 1, 1, 1, 1, 1] [0, 2, 0, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202012 : mirrorTrits [1, 2, 1, 1, 1, 1, 1] = [2, 1, 2, 2, 2, 2, 2] := by
  decide

theorem demoInv_0202012 : specInv 7 5 20 [0, 2, 0, 2, 0, 1, 2] = some [2, 1, 2, 2, 2, 2, 2] :=
  specInv_mirror_7 [0, 2, 0, 2, 0, 1, 2] [2, 0, 2, 2, 1, 2, 1] [2, 2, 2, 2, 1, 0, 1] [1, 2, 1, 1, 1, 1, 1] [2, 1, 2, 2, 2, 2, 2] demoR1_0202012 demoR2_0202012 demoC_0202012 demoM_0202012 demoMir_0202012

theorem demoR1_1202012 : invRung 7 5 20 [1, 2, 0, 2, 0, 1, 2] [1, 2, 0, 2, 0, 1, 2] 1 2 false = ([1, 1, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_1202012 : invRung 7 5 20 [1, 2, 0, 2, 0, 1, 2] [1, 1, 2, 1, 0, 0, 2] 3 1 true = ([0, 0, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1202012 : fieldCube 7 5 20 [0, 0, 2, 0, 0, 1, 0] = [1, 1, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_1202012 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 1, 1] [1, 2, 0, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202012 : mirrorTrits [1, 1, 1, 0, 1, 1, 1] = [2, 2, 2, 0, 2, 2, 2] := by
  decide

theorem demoInv_1202012 : specInv 7 5 20 [1, 2, 0, 2, 0, 1, 2] = some [2, 2, 2, 0, 2, 2, 2] :=
  specInv_mirror_7 [1, 2, 0, 2, 0, 1, 2] [1, 1, 2, 1, 0, 0, 2] [0, 0, 2, 0, 0, 1, 0] [1, 1, 1, 0, 1, 1, 1] [2, 2, 2, 0, 2, 2, 2] demoR1_1202012 demoR2_1202012 demoC_1202012 demoM_1202012 demoMir_1202012

theorem demoR1_2202012 : invRung 7 5 20 [2, 2, 0, 2, 0, 1, 2] [2, 2, 0, 2, 0, 1, 2] 1 2 false = ([0, 0, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2202012 : invRung 7 5 20 [2, 2, 0, 2, 0, 1, 2] [0, 0, 2, 2, 2, 0, 0] 3 1 true = ([0, 0, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_2202012 : fieldCube 7 5 20 [0, 0, 2, 2, 2, 2, 1] = [1, 2, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_2202012 : fieldMul 7 5 20 [1, 2, 0, 0, 0, 1, 0] [2, 2, 0, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202012 : mirrorTrits [1, 2, 0, 0, 0, 1, 0] = [2, 1, 0, 0, 0, 2, 0] := by
  decide

theorem demoInv_2202012 : specInv 7 5 20 [2, 2, 0, 2, 0, 1, 2] = some [2, 1, 0, 0, 0, 2, 0] :=
  specInv_mirror_7 [2, 2, 0, 2, 0, 1, 2] [0, 0, 2, 2, 2, 0, 0] [0, 0, 2, 2, 2, 2, 1] [1, 2, 0, 0, 0, 1, 0] [2, 1, 0, 0, 0, 2, 0] demoR1_2202012 demoR2_2202012 demoC_2202012 demoM_2202012 demoMir_2202012

theorem demoR1_0012012 : invRung 7 5 20 [0, 0, 1, 2, 0, 1, 2] [0, 0, 1, 2, 0, 1, 2] 1 2 false = ([0, 2, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0012012 : invRung 7 5 20 [0, 0, 1, 2, 0, 1, 2] [0, 2, 1, 1, 1, 1, 2] 3 1 true = ([0, 0, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0012012 : fieldCube 7 5 20 [0, 0, 1, 2, 0, 1, 1] = [0, 2, 2, 1, 2, 1, 1] := by
  decide

theorem demoM_0012012 : fieldMul 7 5 20 [0, 2, 2, 1, 2, 1, 1] [0, 0, 1, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0012012 : mirrorTrits [0, 2, 2, 1, 2, 1, 1] = [0, 1, 1, 2, 1, 2, 2] := by
  decide

theorem demoInv_0012012 : specInv 7 5 20 [0, 0, 1, 2, 0, 1, 2] = some [0, 1, 1, 2, 1, 2, 2] :=
  specInv_mirror_7 [0, 0, 1, 2, 0, 1, 2] [0, 2, 1, 1, 1, 1, 2] [0, 0, 1, 2, 0, 1, 1] [0, 2, 2, 1, 2, 1, 1] [0, 1, 1, 2, 1, 2, 2] demoR1_0012012 demoR2_0012012 demoC_0012012 demoM_0012012 demoMir_0012012

theorem demoR1_1012012 : invRung 7 5 20 [1, 0, 1, 2, 0, 1, 2] [1, 0, 1, 2, 0, 1, 2] 1 2 false = ([0, 1, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_1012012 : invRung 7 5 20 [1, 0, 1, 2, 0, 1, 2] [0, 1, 0, 0, 2, 2, 2] 3 1 true = ([1, 0, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_1012012 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 2, 1] = [2, 1, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_1012012 : fieldMul 7 5 20 [2, 1, 0, 2, 0, 0, 1] [1, 0, 1, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1012012 : mirrorTrits [2, 1, 0, 2, 0, 0, 1] = [1, 2, 0, 1, 0, 0, 2] := by
  decide

theorem demoInv_1012012 : specInv 7 5 20 [1, 0, 1, 2, 0, 1, 2] = some [1, 2, 0, 1, 0, 0, 2] :=
  specInv_mirror_7 [1, 0, 1, 2, 0, 1, 2] [0, 1, 0, 0, 2, 2, 2] [1, 0, 1, 2, 1, 2, 1] [2, 1, 0, 2, 0, 0, 1] [1, 2, 0, 1, 0, 0, 2] demoR1_1012012 demoR2_1012012 demoC_1012012 demoM_1012012 demoMir_1012012

theorem demoR1_2012012 : invRung 7 5 20 [2, 0, 1, 2, 0, 1, 2] [2, 0, 1, 2, 0, 1, 2] 1 2 false = ([2, 2, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2012012 : invRung 7 5 20 [2, 0, 1, 2, 0, 1, 2] [2, 2, 1, 2, 2, 0, 0] 3 1 true = ([1, 1, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_2012012 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 1, 1] = [0, 0, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_2012012 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 1, 2] [2, 0, 1, 2, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2012012 : specInv 7 5 20 [2, 0, 1, 2, 0, 1, 2] = some [0, 0, 1, 0, 2, 1, 2] :=
  specInv_white_7 [2, 0, 1, 2, 0, 1, 2] [2, 2, 1, 2, 2, 0, 0] [1, 1, 1, 1, 1, 1, 1] [0, 0, 1, 0, 2, 1, 2] demoR1_2012012 demoR2_2012012 demoC_2012012 demoM_2012012

theorem demoR1_0112012 : invRung 7 5 20 [0, 1, 1, 2, 0, 1, 2] [0, 1, 1, 2, 0, 1, 2] 1 2 false = ([0, 1, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_0112012 : invRung 7 5 20 [0, 1, 1, 2, 0, 1, 2] [0, 1, 0, 0, 2, 0, 1] 3 1 true = ([1, 1, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_0112012 : fieldCube 7 5 20 [1, 1, 0, 2, 0, 0, 1] = [0, 1, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_0112012 : fieldMul 7 5 20 [0, 1, 1, 2, 1, 0, 1] [0, 1, 1, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112012 : mirrorTrits [0, 1, 1, 2, 1, 0, 1] = [0, 2, 2, 1, 2, 0, 2] := by
  decide

theorem demoInv_0112012 : specInv 7 5 20 [0, 1, 1, 2, 0, 1, 2] = some [0, 2, 2, 1, 2, 0, 2] :=
  specInv_mirror_7 [0, 1, 1, 2, 0, 1, 2] [0, 1, 0, 0, 2, 0, 1] [1, 1, 0, 2, 0, 0, 1] [0, 1, 1, 2, 1, 0, 1] [0, 2, 2, 1, 2, 0, 2] demoR1_0112012 demoR2_0112012 demoC_0112012 demoM_0112012 demoMir_0112012

theorem demoR1_1112012 : invRung 7 5 20 [1, 1, 1, 2, 0, 1, 2] [1, 1, 1, 2, 0, 1, 2] 1 2 false = ([2, 1, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1112012 : invRung 7 5 20 [1, 1, 1, 2, 0, 1, 2] [2, 1, 1, 1, 0, 0, 1] 3 1 true = ([2, 1, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1112012 : fieldCube 7 5 20 [2, 1, 1, 2, 1, 2, 2] = [0, 2, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_1112012 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 1, 2] [1, 1, 1, 2, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1112012 : specInv 7 5 20 [1, 1, 1, 2, 0, 1, 2] = some [0, 2, 2, 1, 1, 1, 2] :=
  specInv_white_7 [1, 1, 1, 2, 0, 1, 2] [2, 1, 1, 1, 0, 0, 1] [2, 1, 1, 2, 1, 2, 2] [0, 2, 2, 1, 1, 1, 2] demoR1_1112012 demoR2_1112012 demoC_1112012 demoM_1112012

theorem demoR1_2112012 : invRung 7 5 20 [2, 1, 1, 2, 0, 1, 2] [2, 1, 1, 2, 0, 1, 2] 1 2 false = ([2, 2, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_2112012 : invRung 7 5 20 [2, 1, 1, 2, 0, 1, 2] [2, 2, 0, 1, 0, 2, 2] 3 1 true = ([2, 0, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_2112012 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 1, 2] = [2, 0, 1, 2, 0, 2, 2] := by
  decide

theorem demoM_2112012 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 2, 2] [2, 1, 1, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112012 : mirrorTrits [2, 0, 1, 2, 0, 2, 2] = [1, 0, 2, 1, 0, 1, 1] := by
  decide

theorem demoInv_2112012 : specInv 7 5 20 [2, 1, 1, 2, 0, 1, 2] = some [1, 0, 2, 1, 0, 1, 1] :=
  specInv_mirror_7 [2, 1, 1, 2, 0, 1, 2] [2, 2, 0, 1, 0, 2, 2] [2, 0, 1, 2, 0, 1, 2] [2, 0, 1, 2, 0, 2, 2] [1, 0, 2, 1, 0, 1, 1] demoR1_2112012 demoR2_2112012 demoC_2112012 demoM_2112012 demoMir_2112012

theorem demoR1_0212012 : invRung 7 5 20 [0, 2, 1, 2, 0, 1, 2] [0, 2, 1, 2, 0, 1, 2] 1 2 false = ([1, 1, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_0212012 : invRung 7 5 20 [0, 2, 1, 2, 0, 1, 2] [1, 1, 1, 0, 2, 2, 1] 3 1 true = ([1, 2, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0212012 : fieldCube 7 5 20 [1, 2, 2, 1, 0, 0, 1] = [2, 1, 0, 0, 1, 2, 0] := by
  decide

theorem demoM_0212012 : fieldMul 7 5 20 [2, 1, 0, 0, 1, 2, 0] [0, 2, 1, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212012 : mirrorTrits [2, 1, 0, 0, 1, 2, 0] = [1, 2, 0, 0, 2, 1, 0] := by
  decide

theorem demoInv_0212012 : specInv 7 5 20 [0, 2, 1, 2, 0, 1, 2] = some [1, 2, 0, 0, 2, 1, 0] :=
  specInv_mirror_7 [0, 2, 1, 2, 0, 1, 2] [1, 1, 1, 0, 2, 2, 1] [1, 2, 2, 1, 0, 0, 1] [2, 1, 0, 0, 1, 2, 0] [1, 2, 0, 0, 2, 1, 0] demoR1_0212012 demoR2_0212012 demoC_0212012 demoM_0212012 demoMir_0212012

theorem demoR1_1212012 : invRung 7 5 20 [1, 2, 1, 2, 0, 1, 2] [1, 2, 1, 2, 0, 1, 2] 1 2 false = ([2, 0, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_1212012 : invRung 7 5 20 [1, 2, 1, 2, 0, 1, 2] [2, 0, 1, 1, 2, 0, 2] 3 1 true = ([1, 0, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_1212012 : fieldCube 7 5 20 [1, 0, 0, 1, 1, 1, 0] = [0, 2, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_1212012 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 0, 0] [1, 2, 1, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212012 : mirrorTrits [0, 2, 2, 1, 1, 0, 0] = [0, 1, 1, 2, 2, 0, 0] := by
  decide

theorem demoInv_1212012 : specInv 7 5 20 [1, 2, 1, 2, 0, 1, 2] = some [0, 1, 1, 2, 2, 0, 0] :=
  specInv_mirror_7 [1, 2, 1, 2, 0, 1, 2] [2, 0, 1, 1, 2, 0, 2] [1, 0, 0, 1, 1, 1, 0] [0, 2, 2, 1, 1, 0, 0] [0, 1, 1, 2, 2, 0, 0] demoR1_1212012 demoR2_1212012 demoC_1212012 demoM_1212012 demoMir_1212012

theorem demoR1_2212012 : invRung 7 5 20 [2, 2, 1, 2, 0, 1, 2] [2, 2, 1, 2, 0, 1, 2] 1 2 false = ([0, 2, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_2212012 : invRung 7 5 20 [2, 2, 1, 2, 0, 1, 2] [0, 2, 1, 0, 1, 2, 1] 3 1 true = ([0, 2, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_2212012 : fieldCube 7 5 20 [0, 2, 1, 0, 0, 2, 2] = [2, 1, 0, 1, 1, 1, 1] := by
  decide

theorem demoM_2212012 : fieldMul 7 5 20 [2, 1, 0, 1, 1, 1, 1] [2, 2, 1, 2, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2212012 : specInv 7 5 20 [2, 2, 1, 2, 0, 1, 2] = some [2, 1, 0, 1, 1, 1, 1] :=
  specInv_white_7 [2, 2, 1, 2, 0, 1, 2] [0, 2, 1, 0, 1, 2, 1] [0, 2, 1, 0, 0, 2, 2] [2, 1, 0, 1, 1, 1, 1] demoR1_2212012 demoR2_2212012 demoC_2212012 demoM_2212012

theorem demoR1_0022012 : invRung 7 5 20 [0, 0, 2, 2, 0, 1, 2] [0, 0, 2, 2, 0, 1, 2] 1 2 false = ([0, 2, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_0022012 : invRung 7 5 20 [0, 0, 2, 2, 0, 1, 2] [0, 2, 0, 1, 0, 0, 1] 3 1 true = ([1, 2, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_0022012 : fieldCube 7 5 20 [1, 2, 1, 1, 1, 1, 1] = [0, 0, 1, 1, 2, 1, 2] := by
  decide

theorem demoM_0022012 : fieldMul 7 5 20 [0, 0, 1, 1, 2, 1, 2] [0, 0, 2, 2, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0022012 : specInv 7 5 20 [0, 0, 2, 2, 0, 1, 2] = some [0, 0, 1, 1, 2, 1, 2] :=
  specInv_white_7 [0, 0, 2, 2, 0, 1, 2] [0, 2, 0, 1, 0, 0, 1] [1, 2, 1, 1, 1, 1, 1] [0, 0, 1, 1, 2, 1, 2] demoR1_0022012 demoR2_0022012 demoC_0022012 demoM_0022012

theorem demoR1_1022012 : invRung 7 5 20 [1, 0, 2, 2, 0, 1, 2] [1, 0, 2, 2, 0, 1, 2] 1 2 false = ([1, 1, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_1022012 : invRung 7 5 20 [1, 0, 2, 2, 0, 1, 2] [1, 1, 1, 1, 0, 2, 2] 3 1 true = ([1, 2, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1022012 : fieldCube 7 5 20 [1, 2, 0, 0, 0, 1, 0] = [2, 1, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_1022012 : fieldMul 7 5 20 [2, 1, 1, 2, 1, 1, 2] [1, 0, 2, 2, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1022012 : specInv 7 5 20 [1, 0, 2, 2, 0, 1, 2] = some [2, 1, 1, 2, 1, 1, 2] :=
  specInv_white_7 [1, 0, 2, 2, 0, 1, 2] [1, 1, 1, 1, 0, 2, 2] [1, 2, 0, 0, 0, 1, 0] [2, 1, 1, 2, 1, 1, 2] demoR1_1022012 demoR2_1022012 demoC_1022012 demoM_1022012

theorem demoR1_2022012 : invRung 7 5 20 [2, 0, 2, 2, 0, 1, 2] [2, 0, 2, 2, 0, 1, 2] 1 2 false = ([1, 1, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_2022012 : invRung 7 5 20 [2, 0, 2, 2, 0, 1, 2] [1, 1, 1, 0, 1, 0, 2] 3 1 true = ([1, 1, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2022012 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 1, 1] = [2, 0, 0, 0, 2, 0, 2] := by
  decide

theorem demoM_2022012 : fieldMul 7 5 20 [2, 0, 0, 0, 2, 0, 2] [2, 0, 2, 2, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2022012 : specInv 7 5 20 [2, 0, 2, 2, 0, 1, 2] = some [2, 0, 0, 0, 2, 0, 2] :=
  specInv_white_7 [2, 0, 2, 2, 0, 1, 2] [1, 1, 1, 0, 1, 0, 2] [1, 1, 1, 0, 1, 1, 1] [2, 0, 0, 0, 2, 0, 2] demoR1_2022012 demoR2_2022012 demoC_2022012 demoM_2022012

theorem demoR1_0122012 : invRung 7 5 20 [0, 1, 2, 2, 0, 1, 2] [0, 1, 2, 2, 0, 1, 2] 1 2 false = ([1, 1, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_0122012 : invRung 7 5 20 [0, 1, 2, 2, 0, 1, 2] [1, 1, 1, 2, 2, 2, 0] 3 1 true = ([1, 2, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0122012 : fieldCube 7 5 20 [1, 2, 2, 0, 0, 2, 1] = [0, 0, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_0122012 : fieldMul 7 5 20 [0, 0, 1, 0, 0, 0, 1] [0, 1, 2, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122012 : mirrorTrits [0, 0, 1, 0, 0, 0, 1] = [0, 0, 2, 0, 0, 0, 2] := by
  decide

theorem demoInv_0122012 : specInv 7 5 20 [0, 1, 2, 2, 0, 1, 2] = some [0, 0, 2, 0, 0, 0, 2] :=
  specInv_mirror_7 [0, 1, 2, 2, 0, 1, 2] [1, 1, 1, 2, 2, 2, 0] [1, 2, 2, 0, 0, 2, 1] [0, 0, 1, 0, 0, 0, 1] [0, 0, 2, 0, 0, 0, 2] demoR1_0122012 demoR2_0122012 demoC_0122012 demoM_0122012 demoMir_0122012

theorem demoR1_1122012 : invRung 7 5 20 [1, 1, 2, 2, 0, 1, 2] [1, 1, 2, 2, 0, 1, 2] 1 2 false = ([1, 0, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_1122012 : invRung 7 5 20 [1, 1, 2, 2, 0, 1, 2] [1, 0, 2, 0, 0, 1, 0] 3 1 true = ([0, 2, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_1122012 : fieldCube 7 5 20 [0, 2, 1, 1, 2, 0, 1] = [1, 0, 0, 2, 1, 1, 1] := by
  decide

theorem demoM_1122012 : fieldMul 7 5 20 [1, 0, 0, 2, 1, 1, 1] [1, 1, 2, 2, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1122012 : specInv 7 5 20 [1, 1, 2, 2, 0, 1, 2] = some [1, 0, 0, 2, 1, 1, 1] :=
  specInv_white_7 [1, 1, 2, 2, 0, 1, 2] [1, 0, 2, 0, 0, 1, 0] [0, 2, 1, 1, 2, 0, 1] [1, 0, 0, 2, 1, 1, 1] demoR1_1122012 demoR2_1122012 demoC_1122012 demoM_1122012

theorem demoR1_2122012 : invRung 7 5 20 [2, 1, 2, 2, 0, 1, 2] [2, 1, 2, 2, 0, 1, 2] 1 2 false = ([2, 2, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2122012 : invRung 7 5 20 [2, 1, 2, 2, 0, 1, 2] [2, 2, 1, 2, 2, 1, 2] 3 1 true = ([2, 2, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_2122012 : fieldCube 7 5 20 [2, 2, 2, 0, 0, 2, 0] = [1, 2, 2, 2, 2, 2, 0] := by
  decide

theorem demoM_2122012 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 2, 0] [2, 1, 2, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122012 : mirrorTrits [1, 2, 2, 2, 2, 2, 0] = [2, 1, 1, 1, 1, 1, 0] := by
  decide

theorem demoInv_2122012 : specInv 7 5 20 [2, 1, 2, 2, 0, 1, 2] = some [2, 1, 1, 1, 1, 1, 0] :=
  specInv_mirror_7 [2, 1, 2, 2, 0, 1, 2] [2, 2, 1, 2, 2, 1, 2] [2, 2, 2, 0, 0, 2, 0] [1, 2, 2, 2, 2, 2, 0] [2, 1, 1, 1, 1, 1, 0] demoR1_2122012 demoR2_2122012 demoC_2122012 demoM_2122012 demoMir_2122012

theorem demoR1_0222012 : invRung 7 5 20 [0, 2, 2, 2, 0, 1, 2] [0, 2, 2, 2, 0, 1, 2] 1 2 false = ([1, 0, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_0222012 : invRung 7 5 20 [0, 2, 2, 2, 0, 1, 2] [1, 0, 2, 1, 0, 2, 0] 3 1 true = ([1, 0, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_0222012 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 1, 1] = [1, 0, 2, 2, 2, 2, 0] := by
  decide

theorem demoM_0222012 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 2, 0] [0, 2, 2, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222012 : mirrorTrits [1, 0, 2, 2, 2, 2, 0] = [2, 0, 1, 1, 1, 1, 0] := by
  decide

theorem demoInv_0222012 : specInv 7 5 20 [0, 2, 2, 2, 0, 1, 2] = some [2, 0, 1, 1, 1, 1, 0] :=
  specInv_mirror_7 [0, 2, 2, 2, 0, 1, 2] [1, 0, 2, 1, 0, 2, 0] [1, 0, 2, 2, 1, 1, 1] [1, 0, 2, 2, 2, 2, 0] [2, 0, 1, 1, 1, 1, 0] demoR1_0222012 demoR2_0222012 demoC_0222012 demoM_0222012 demoMir_0222012

theorem demoR1_1222012 : invRung 7 5 20 [1, 2, 2, 2, 0, 1, 2] [1, 2, 2, 2, 0, 1, 2] 1 2 false = ([0, 0, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1222012 : invRung 7 5 20 [1, 2, 2, 2, 0, 1, 2] [0, 0, 0, 1, 1, 0, 0] 3 1 true = ([2, 2, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_1222012 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 0, 2] = [1, 1, 0, 0, 2, 0, 2] := by
  decide

theorem demoM_1222012 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 0, 2] [1, 2, 2, 2, 0, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1222012 : specInv 7 5 20 [1, 2, 2, 2, 0, 1, 2] = some [1, 1, 0, 0, 2, 0, 2] :=
  specInv_white_7 [1, 2, 2, 2, 0, 1, 2] [0, 0, 0, 1, 1, 0, 0] [2, 2, 1, 2, 2, 0, 2] [1, 1, 0, 0, 2, 0, 2] demoR1_1222012 demoR2_1222012 demoC_1222012 demoM_1222012

theorem demoR1_2222012 : invRung 7 5 20 [2, 2, 2, 2, 0, 1, 2] [2, 2, 2, 2, 0, 1, 2] 1 2 false = ([2, 2, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_2222012 : invRung 7 5 20 [2, 2, 2, 2, 0, 1, 2] [2, 2, 1, 1, 0, 1, 2] 3 1 true = ([0, 0, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_2222012 : fieldCube 7 5 20 [0, 0, 2, 1, 0, 0, 0] = [1, 0, 1, 0, 0, 1, 2] := by
  decide

theorem demoM_2222012 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 1, 2] [2, 2, 2, 2, 0, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222012 : mirrorTrits [1, 0, 1, 0, 0, 1, 2] = [2, 0, 2, 0, 0, 2, 1] := by
  decide

theorem demoInv_2222012 : specInv 7 5 20 [2, 2, 2, 2, 0, 1, 2] = some [2, 0, 2, 0, 0, 2, 1] :=
  specInv_mirror_7 [2, 2, 2, 2, 0, 1, 2] [2, 2, 1, 1, 0, 1, 2] [0, 0, 2, 1, 0, 0, 0] [1, 0, 1, 0, 0, 1, 2] [2, 0, 2, 0, 0, 2, 1] demoR1_2222012 demoR2_2222012 demoC_2222012 demoM_2222012 demoMir_2222012

theorem demoR1_0000112 : invRung 7 5 20 [0, 0, 0, 0, 1, 1, 2] [0, 0, 0, 0, 1, 1, 2] 1 2 false = ([0, 0, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0000112 : invRung 7 5 20 [0, 0, 0, 0, 1, 1, 2] [0, 0, 1, 0, 2, 2, 2] 3 1 true = ([2, 1, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0000112 : fieldCube 7 5 20 [2, 1, 2, 2, 1, 1, 2] = [2, 1, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_0000112 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 0, 1] [0, 0, 0, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0000112 : specInv 7 5 20 [0, 0, 0, 0, 1, 1, 2] = some [2, 1, 1, 1, 0, 0, 1] :=
  specInv_white_7 [0, 0, 0, 0, 1, 1, 2] [0, 0, 1, 0, 2, 2, 2] [2, 1, 2, 2, 1, 1, 2] [2, 1, 1, 1, 0, 0, 1] demoR1_0000112 demoR2_0000112 demoC_0000112 demoM_0000112

theorem demoR1_1000112 : invRung 7 5 20 [1, 0, 0, 0, 1, 1, 2] [1, 0, 0, 0, 1, 1, 2] 1 2 false = ([1, 1, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_1000112 : invRung 7 5 20 [1, 0, 0, 0, 1, 1, 2] [1, 1, 1, 0, 2, 0, 1] 3 1 true = ([0, 0, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_1000112 : fieldCube 7 5 20 [0, 0, 2, 2, 0, 2, 1] = [1, 0, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_1000112 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 2, 1] [1, 0, 0, 0, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000112 : mirrorTrits [1, 0, 0, 1, 0, 2, 1] = [2, 0, 0, 2, 0, 1, 2] := by
  decide

theorem demoInv_1000112 : specInv 7 5 20 [1, 0, 0, 0, 1, 1, 2] = some [2, 0, 0, 2, 0, 1, 2] :=
  specInv_mirror_7 [1, 0, 0, 0, 1, 1, 2] [1, 1, 1, 0, 2, 0, 1] [0, 0, 2, 2, 0, 2, 1] [1, 0, 0, 1, 0, 2, 1] [2, 0, 0, 2, 0, 1, 2] demoR1_1000112 demoR2_1000112 demoC_1000112 demoM_1000112 demoMir_1000112

theorem demoR1_2000112 : invRung 7 5 20 [2, 0, 0, 0, 1, 1, 2] [2, 0, 0, 0, 1, 1, 2] 1 2 false = ([2, 1, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_2000112 : invRung 7 5 20 [2, 0, 0, 0, 1, 1, 2] [2, 1, 0, 0, 1, 2, 2] 3 1 true = ([1, 1, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_2000112 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 2, 2] = [0, 1, 0, 0, 1, 1, 2] := by
  decide

theorem demoM_2000112 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 1, 2] [2, 0, 0, 0, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000112 : mirrorTrits [0, 1, 0, 0, 1, 1, 2] = [0, 2, 0, 0, 2, 2, 1] := by
  decide

theorem demoInv_2000112 : specInv 7 5 20 [2, 0, 0, 0, 1, 1, 2] = some [0, 2, 0, 0, 2, 2, 1] :=
  specInv_mirror_7 [2, 0, 0, 0, 1, 1, 2] [2, 1, 0, 0, 1, 2, 2] [1, 1, 2, 0, 0, 2, 2] [0, 1, 0, 0, 1, 1, 2] [0, 2, 0, 0, 2, 2, 1] demoR1_2000112 demoR2_2000112 demoC_2000112 demoM_2000112 demoMir_2000112

theorem demoR1_0100112 : invRung 7 5 20 [0, 1, 0, 0, 1, 1, 2] [0, 1, 0, 0, 1, 1, 2] 1 2 false = ([2, 2, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_0100112 : invRung 7 5 20 [0, 1, 0, 0, 1, 1, 2] [2, 2, 0, 2, 0, 1, 0] 3 1 true = ([2, 0, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_0100112 : fieldCube 7 5 20 [2, 0, 1, 2, 1, 0, 2] = [1, 0, 0, 0, 2, 2, 1] := by
  decide

theorem demoM_0100112 : fieldMul 7 5 20 [1, 0, 0, 0, 2, 2, 1] [0, 1, 0, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0100112 : specInv 7 5 20 [0, 1, 0, 0, 1, 1, 2] = some [1, 0, 0, 0, 2, 2, 1] :=
  specInv_white_7 [0, 1, 0, 0, 1, 1, 2] [2, 2, 0, 2, 0, 1, 0] [2, 0, 1, 2, 1, 0, 2] [1, 0, 0, 0, 2, 2, 1] demoR1_0100112 demoR2_0100112 demoC_0100112 demoM_0100112

theorem demoR1_1100112 : invRung 7 5 20 [1, 1, 0, 0, 1, 1, 2] [1, 1, 0, 0, 1, 1, 2] 1 2 false = ([1, 2, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_1100112 : invRung 7 5 20 [1, 1, 0, 0, 1, 1, 2] [1, 2, 0, 2, 2, 2, 0] 3 1 true = ([1, 0, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_1100112 : fieldCube 7 5 20 [1, 0, 1, 1, 0, 1, 2] = [0, 0, 0, 2, 0, 1, 2] := by
  decide

theorem demoM_1100112 : fieldMul 7 5 20 [0, 0, 0, 2, 0, 1, 2] [1, 1, 0, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1100112 : specInv 7 5 20 [1, 1, 0, 0, 1, 1, 2] = some [0, 0, 0, 2, 0, 1, 2] :=
  specInv_white_7 [1, 1, 0, 0, 1, 1, 2] [1, 2, 0, 2, 2, 2, 0] [1, 0, 1, 1, 0, 1, 2] [0, 0, 0, 2, 0, 1, 2] demoR1_1100112 demoR2_1100112 demoC_1100112 demoM_1100112

theorem demoR1_2100112 : invRung 7 5 20 [2, 1, 0, 0, 1, 1, 2] [2, 1, 0, 0, 1, 1, 2] 1 2 false = ([2, 0, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2100112 : invRung 7 5 20 [2, 1, 0, 0, 1, 1, 2] [2, 0, 1, 1, 0, 0, 2] 3 1 true = ([1, 1, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_2100112 : fieldCube 7 5 20 [1, 1, 2, 2, 1, 1, 2] = [1, 1, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_2100112 : fieldMul 7 5 20 [1, 1, 1, 1, 0, 0, 1] [2, 1, 0, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2100112 : specInv 7 5 20 [2, 1, 0, 0, 1, 1, 2] = some [1, 1, 1, 1, 0, 0, 1] :=
  specInv_white_7 [2, 1, 0, 0, 1, 1, 2] [2, 0, 1, 1, 0, 0, 2] [1, 1, 2, 2, 1, 1, 2] [1, 1, 1, 1, 0, 0, 1] demoR1_2100112 demoR2_2100112 demoC_2100112 demoM_2100112

theorem demoR1_0200112 : invRung 7 5 20 [0, 2, 0, 0, 1, 1, 2] [0, 2, 0, 0, 1, 1, 2] 1 2 false = ([1, 2, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_0200112 : invRung 7 5 20 [0, 2, 0, 0, 1, 1, 2] [1, 2, 1, 1, 0, 2, 1] 3 1 true = ([1, 0, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0200112 : fieldCube 7 5 20 [1, 0, 1, 1, 0, 1, 1] = [0, 2, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_0200112 : fieldMul 7 5 20 [0, 2, 1, 1, 2, 0, 1] [0, 2, 0, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0200112 : specInv 7 5 20 [0, 2, 0, 0, 1, 1, 2] = some [0, 2, 1, 1, 2, 0, 1] :=
  specInv_white_7 [0, 2, 0, 0, 1, 1, 2] [1, 2, 1, 1, 0, 2, 1] [1, 0, 1, 1, 0, 1, 1] [0, 2, 1, 1, 2, 0, 1] demoR1_0200112 demoR2_0200112 demoC_0200112 demoM_0200112

theorem demoR1_1200112 : invRung 7 5 20 [1, 2, 0, 0, 1, 1, 2] [1, 2, 0, 0, 1, 1, 2] 1 2 false = ([1, 2, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_1200112 : invRung 7 5 20 [1, 2, 0, 0, 1, 1, 2] [1, 2, 1, 2, 0, 2, 0] 3 1 true = ([1, 2, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_1200112 : fieldCube 7 5 20 [1, 2, 0, 0, 2, 1, 2] = [2, 2, 2, 0, 0, 2, 0] := by
  decide

theorem demoM_1200112 : fieldMul 7 5 20 [2, 2, 2, 0, 0, 2, 0] [1, 2, 0, 0, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200112 : mirrorTrits [2, 2, 2, 0, 0, 2, 0] = [1, 1, 1, 0, 0, 1, 0] := by
  decide

theorem demoInv_1200112 : specInv 7 5 20 [1, 2, 0, 0, 1, 1, 2] = some [1, 1, 1, 0, 0, 1, 0] :=
  specInv_mirror_7 [1, 2, 0, 0, 1, 1, 2] [1, 2, 1, 2, 0, 2, 0] [1, 2, 0, 0, 2, 1, 2] [2, 2, 2, 0, 0, 2, 0] [1, 1, 1, 0, 0, 1, 0] demoR1_1200112 demoR2_1200112 demoC_1200112 demoM_1200112 demoMir_1200112

theorem demoR1_2200112 : invRung 7 5 20 [2, 2, 0, 0, 1, 1, 2] [2, 2, 0, 0, 1, 1, 2] 1 2 false = ([2, 2, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_2200112 : invRung 7 5 20 [2, 2, 0, 0, 1, 1, 2] [2, 2, 1, 1, 2, 1, 1] 3 1 true = ([0, 2, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_2200112 : fieldCube 7 5 20 [0, 2, 1, 0, 2, 1, 2] = [1, 2, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_2200112 : fieldMul 7 5 20 [1, 2, 2, 0, 0, 2, 1] [2, 2, 0, 0, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200112 : mirrorTrits [1, 2, 2, 0, 0, 2, 1] = [2, 1, 1, 0, 0, 1, 2] := by
  decide

theorem demoInv_2200112 : specInv 7 5 20 [2, 2, 0, 0, 1, 1, 2] = some [2, 1, 1, 0, 0, 1, 2] :=
  specInv_mirror_7 [2, 2, 0, 0, 1, 1, 2] [2, 2, 1, 1, 2, 1, 1] [0, 2, 1, 0, 2, 1, 2] [1, 2, 2, 0, 0, 2, 1] [2, 1, 1, 0, 0, 1, 2] demoR1_2200112 demoR2_2200112 demoC_2200112 demoM_2200112 demoMir_2200112

theorem demoR1_0010112 : invRung 7 5 20 [0, 0, 1, 0, 1, 1, 2] [0, 0, 1, 0, 1, 1, 2] 1 2 false = ([0, 0, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_0010112 : invRung 7 5 20 [0, 0, 1, 0, 1, 1, 2] [0, 0, 2, 2, 1, 2, 0] 3 1 true = ([0, 0, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_0010112 : fieldCube 7 5 20 [0, 0, 0, 2, 0, 2, 2] = [1, 1, 2, 2, 1, 0, 0] := by
  decide

theorem demoM_0010112 : fieldMul 7 5 20 [1, 1, 2, 2, 1, 0, 0] [0, 0, 1, 0, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010112 : mirrorTrits [1, 1, 2, 2, 1, 0, 0] = [2, 2, 1, 1, 2, 0, 0] := by
  decide

theorem demoInv_0010112 : specInv 7 5 20 [0, 0, 1, 0, 1, 1, 2] = some [2, 2, 1, 1, 2, 0, 0] :=
  specInv_mirror_7 [0, 0, 1, 0, 1, 1, 2] [0, 0, 2, 2, 1, 2, 0] [0, 0, 0, 2, 0, 2, 2] [1, 1, 2, 2, 1, 0, 0] [2, 2, 1, 1, 2, 0, 0] demoR1_0010112 demoR2_0010112 demoC_0010112 demoM_0010112 demoMir_0010112

theorem demoR1_1010112 : invRung 7 5 20 [1, 0, 1, 0, 1, 1, 2] [1, 0, 1, 0, 1, 1, 2] 1 2 false = ([2, 1, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_1010112 : invRung 7 5 20 [1, 0, 1, 0, 1, 1, 2] [2, 1, 0, 2, 1, 0, 1] 3 1 true = ([0, 2, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_1010112 : fieldCube 7 5 20 [0, 2, 1, 0, 1, 2, 1] = [2, 1, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_1010112 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 1, 1] [1, 0, 1, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1010112 : specInv 7 5 20 [1, 0, 1, 0, 1, 1, 2] = some [2, 1, 1, 1, 0, 1, 1] :=
  specInv_white_7 [1, 0, 1, 0, 1, 1, 2] [2, 1, 0, 2, 1, 0, 1] [0, 2, 1, 0, 1, 2, 1] [2, 1, 1, 1, 0, 1, 1] demoR1_1010112 demoR2_1010112 demoC_1010112 demoM_1010112

theorem demoR1_2010112 : invRung 7 5 20 [2, 0, 1, 0, 1, 1, 2] [2, 0, 1, 0, 1, 1, 2] 1 2 false = ([1, 0, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_2010112 : invRung 7 5 20 [2, 0, 1, 0, 1, 1, 2] [1, 0, 0, 1, 2, 1, 2] 3 1 true = ([2, 2, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2010112 : fieldCube 7 5 20 [2, 2, 1, 0, 1, 1, 1] = [0, 0, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_2010112 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 0, 2] [2, 0, 1, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2010112 : specInv 7 5 20 [2, 0, 1, 0, 1, 1, 2] = some [0, 0, 0, 1, 2, 0, 2] :=
  specInv_white_7 [2, 0, 1, 0, 1, 1, 2] [1, 0, 0, 1, 2, 1, 2] [2, 2, 1, 0, 1, 1, 1] [0, 0, 0, 1, 2, 0, 2] demoR1_2010112 demoR2_2010112 demoC_2010112 demoM_2010112

theorem demoR1_0110112 : invRung 7 5 20 [0, 1, 1, 0, 1, 1, 2] [0, 1, 1, 0, 1, 1, 2] 1 2 false = ([1, 2, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_0110112 : invRung 7 5 20 [0, 1, 1, 0, 1, 1, 2] [1, 2, 1, 0, 2, 0, 2] 3 1 true = ([0, 2, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_0110112 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 1, 1] = [2, 0, 1, 1, 2, 1, 0] := by
  decide

theorem demoM_0110112 : fieldMul 7 5 20 [2, 0, 1, 1, 2, 1, 0] [0, 1, 1, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0110112 : specInv 7 5 20 [0, 1, 1, 0, 1, 1, 2] = some [2, 0, 1, 1, 2, 1, 0] :=
  specInv_white_7 [0, 1, 1, 0, 1, 1, 2] [1, 2, 1, 0, 2, 0, 2] [0, 2, 2, 1, 1, 1, 1] [2, 0, 1, 1, 2, 1, 0] demoR1_0110112 demoR2_0110112 demoC_0110112 demoM_0110112

theorem demoR1_1110112 : invRung 7 5 20 [1, 1, 1, 0, 1, 1, 2] [1, 1, 1, 0, 1, 1, 2] 1 2 false = ([1, 1, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_1110112 : invRung 7 5 20 [1, 1, 1, 0, 1, 1, 2] [1, 1, 0, 2, 2, 2, 0] 3 1 true = ([2, 0, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_1110112 : fieldCube 7 5 20 [2, 0, 1, 0, 0, 0, 0] = [2, 0, 0, 0, 0, 0, 1] := by
  decide

theorem demoM_1110112 : fieldMul 7 5 20 [2, 0, 0, 0, 0, 0, 1] [1, 1, 1, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1110112 : specInv 7 5 20 [1, 1, 1, 0, 1, 1, 2] = some [2, 0, 0, 0, 0, 0, 1] :=
  specInv_white_7 [1, 1, 1, 0, 1, 1, 2] [1, 1, 0, 2, 2, 2, 0] [2, 0, 1, 0, 0, 0, 0] [2, 0, 0, 0, 0, 0, 1] demoR1_1110112 demoR2_1110112 demoC_1110112 demoM_1110112

theorem demoR1_2110112 : invRung 7 5 20 [2, 1, 1, 0, 1, 1, 2] [2, 1, 1, 0, 1, 1, 2] 1 2 false = ([0, 0, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_2110112 : invRung 7 5 20 [2, 1, 1, 0, 1, 1, 2] [0, 0, 0, 2, 0, 0, 1] 3 1 true = ([1, 0, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2110112 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 2, 0] = [1, 2, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_2110112 : fieldMul 7 5 20 [1, 2, 0, 0, 2, 0, 1] [2, 1, 1, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2110112 : specInv 7 5 20 [2, 1, 1, 0, 1, 1, 2] = some [1, 2, 0, 0, 2, 0, 1] :=
  specInv_white_7 [2, 1, 1, 0, 1, 1, 2] [0, 0, 0, 2, 0, 0, 1] [1, 0, 0, 1, 0, 2, 0] [1, 2, 0, 0, 2, 0, 1] demoR1_2110112 demoR2_2110112 demoC_2110112 demoM_2110112

theorem demoR1_0210112 : invRung 7 5 20 [0, 2, 1, 0, 1, 1, 2] [0, 2, 1, 0, 1, 1, 2] 1 2 false = ([0, 1, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_0210112 : invRung 7 5 20 [0, 2, 1, 0, 1, 1, 2] [0, 1, 0, 1, 2, 1, 1] 3 1 true = ([1, 2, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0210112 : fieldCube 7 5 20 [1, 2, 0, 1, 0, 0, 0] = [2, 0, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_0210112 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 1, 0] [0, 2, 1, 0, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210112 : mirrorTrits [2, 0, 1, 2, 0, 1, 0] = [1, 0, 2, 1, 0, 2, 0] := by
  decide

theorem demoInv_0210112 : specInv 7 5 20 [0, 2, 1, 0, 1, 1, 2] = some [1, 0, 2, 1, 0, 2, 0] :=
  specInv_mirror_7 [0, 2, 1, 0, 1, 1, 2] [0, 1, 0, 1, 2, 1, 1] [1, 2, 0, 1, 0, 0, 0] [2, 0, 1, 2, 0, 1, 0] [1, 0, 2, 1, 0, 2, 0] demoR1_0210112 demoR2_0210112 demoC_0210112 demoM_0210112 demoMir_0210112

theorem demoR1_1210112 : invRung 7 5 20 [1, 2, 1, 0, 1, 1, 2] [1, 2, 1, 0, 1, 1, 2] 1 2 false = ([1, 2, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1210112 : invRung 7 5 20 [1, 2, 1, 0, 1, 1, 2] [1, 2, 0, 0, 1, 0, 0] 3 1 true = ([1, 0, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1210112 : fieldCube 7 5 20 [1, 0, 0, 0, 1, 0, 0] = [1, 1, 0, 1, 0, 1, 1] := by
  decide

theorem demoM_1210112 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 1, 1] [1, 2, 1, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1210112 : specInv 7 5 20 [1, 2, 1, 0, 1, 1, 2] = some [1, 1, 0, 1, 0, 1, 1] :=
  specInv_white_7 [1, 2, 1, 0, 1, 1, 2] [1, 2, 0, 0, 1, 0, 0] [1, 0, 0, 0, 1, 0, 0] [1, 1, 0, 1, 0, 1, 1] demoR1_1210112 demoR2_1210112 demoC_1210112 demoM_1210112

theorem demoR1_2210112 : invRung 7 5 20 [2, 2, 1, 0, 1, 1, 2] [2, 2, 1, 0, 1, 1, 2] 1 2 false = ([0, 2, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_2210112 : invRung 7 5 20 [2, 2, 1, 0, 1, 1, 2] [0, 2, 0, 2, 1, 0, 2] 3 1 true = ([1, 1, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_2210112 : fieldCube 7 5 20 [1, 1, 1, 2, 2, 1, 2] = [1, 2, 1, 2, 0, 1, 1] := by
  decide

theorem demoM_2210112 : fieldMul 7 5 20 [1, 2, 1, 2, 0, 1, 1] [2, 2, 1, 0, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210112 : mirrorTrits [1, 2, 1, 2, 0, 1, 1] = [2, 1, 2, 1, 0, 2, 2] := by
  decide

theorem demoInv_2210112 : specInv 7 5 20 [2, 2, 1, 0, 1, 1, 2] = some [2, 1, 2, 1, 0, 2, 2] :=
  specInv_mirror_7 [2, 2, 1, 0, 1, 1, 2] [0, 2, 0, 2, 1, 0, 2] [1, 1, 1, 2, 2, 1, 2] [1, 2, 1, 2, 0, 1, 1] [2, 1, 2, 1, 0, 2, 2] demoR1_2210112 demoR2_2210112 demoC_2210112 demoM_2210112 demoMir_2210112

theorem demoR1_0020112 : invRung 7 5 20 [0, 0, 2, 0, 1, 1, 2] [0, 0, 2, 0, 1, 1, 2] 1 2 false = ([2, 2, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0020112 : invRung 7 5 20 [0, 0, 2, 0, 1, 1, 2] [2, 2, 2, 1, 0, 0, 0] 3 1 true = ([0, 0, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0020112 : fieldCube 7 5 20 [0, 0, 0, 2, 2, 0, 2] = [2, 1, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_0020112 : fieldMul 7 5 20 [2, 1, 0, 1, 2, 0, 1] [0, 0, 2, 0, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020112 : mirrorTrits [2, 1, 0, 1, 2, 0, 1] = [1, 2, 0, 2, 1, 0, 2] := by
  decide

theorem demoInv_0020112 : specInv 7 5 20 [0, 0, 2, 0, 1, 1, 2] = some [1, 2, 0, 2, 1, 0, 2] :=
  specInv_mirror_7 [0, 0, 2, 0, 1, 1, 2] [2, 2, 2, 1, 0, 0, 0] [0, 0, 0, 2, 2, 0, 2] [2, 1, 0, 1, 2, 0, 1] [1, 2, 0, 2, 1, 0, 2] demoR1_0020112 demoR2_0020112 demoC_0020112 demoM_0020112 demoMir_0020112

theorem demoR1_1020112 : invRung 7 5 20 [1, 0, 2, 0, 1, 1, 2] [1, 0, 2, 0, 1, 1, 2] 1 2 false = ([1, 0, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_1020112 : invRung 7 5 20 [1, 0, 2, 0, 1, 1, 2] [1, 0, 2, 1, 0, 1, 2] 3 1 true = ([1, 1, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_1020112 : fieldCube 7 5 20 [1, 1, 2, 2, 1, 1, 0] = [1, 2, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_1020112 : fieldMul 7 5 20 [1, 2, 0, 2, 1, 1, 2] [1, 0, 2, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1020112 : specInv 7 5 20 [1, 0, 2, 0, 1, 1, 2] = some [1, 2, 0, 2, 1, 1, 2] :=
  specInv_white_7 [1, 0, 2, 0, 1, 1, 2] [1, 0, 2, 1, 0, 1, 2] [1, 1, 2, 2, 1, 1, 0] [1, 2, 0, 2, 1, 1, 2] demoR1_1020112 demoR2_1020112 demoC_1020112 demoM_1020112

theorem demoR1_2020112 : invRung 7 5 20 [2, 0, 2, 0, 1, 1, 2] [2, 0, 2, 0, 1, 1, 2] 1 2 false = ([0, 1, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_2020112 : invRung 7 5 20 [2, 0, 2, 0, 1, 1, 2] [0, 1, 1, 2, 0, 1, 2] 3 1 true = ([0, 1, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_2020112 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 1, 1] = [0, 0, 2, 0, 2, 2, 0] := by
  decide

theorem demoM_2020112 : fieldMul 7 5 20 [0, 0, 2, 0, 2, 2, 0] [2, 0, 2, 0, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020112 : mirrorTrits [0, 0, 2, 0, 2, 2, 0] = [0, 0, 1, 0, 1, 1, 0] := by
  decide

theorem demoInv_2020112 : specInv 7 5 20 [2, 0, 2, 0, 1, 1, 2] = some [0, 0, 1, 0, 1, 1, 0] :=
  specInv_mirror_7 [2, 0, 2, 0, 1, 1, 2] [0, 1, 1, 2, 0, 1, 2] [0, 1, 2, 2, 1, 1, 1] [0, 0, 2, 0, 2, 2, 0] [0, 0, 1, 0, 1, 1, 0] demoR1_2020112 demoR2_2020112 demoC_2020112 demoM_2020112 demoMir_2020112

theorem demoR1_0120112 : invRung 7 5 20 [0, 1, 2, 0, 1, 1, 2] [0, 1, 2, 0, 1, 1, 2] 1 2 false = ([2, 0, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_0120112 : invRung 7 5 20 [0, 1, 2, 0, 1, 1, 2] [2, 0, 0, 0, 0, 2, 2] 3 1 true = ([1, 2, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_0120112 : fieldCube 7 5 20 [1, 2, 1, 1, 1, 0, 1] = [2, 2, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_0120112 : fieldMul 7 5 20 [2, 2, 0, 1, 1, 0, 0] [0, 1, 2, 0, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0120112 : mirrorTrits [2, 2, 0, 1, 1, 0, 0] = [1, 1, 0, 2, 2, 0, 0] := by
  decide

theorem demoInv_0120112 : specInv 7 5 20 [0, 1, 2, 0, 1, 1, 2] = some [1, 1, 0, 2, 2, 0, 0] :=
  specInv_mirror_7 [0, 1, 2, 0, 1, 1, 2] [2, 0, 0, 0, 0, 2, 2] [1, 2, 1, 1, 1, 0, 1] [2, 2, 0, 1, 1, 0, 0] [1, 1, 0, 2, 2, 0, 0] demoR1_0120112 demoR2_0120112 demoC_0120112 demoM_0120112 demoMir_0120112

theorem demoR1_1120112 : invRung 7 5 20 [1, 1, 2, 0, 1, 1, 2] [1, 1, 2, 0, 1, 1, 2] 1 2 false = ([2, 1, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_1120112 : invRung 7 5 20 [1, 1, 2, 0, 1, 1, 2] [2, 1, 2, 1, 1, 2, 0] 3 1 true = ([2, 1, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_1120112 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 0, 1] = [1, 0, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_1120112 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 2, 0] [1, 1, 2, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1120112 : specInv 7 5 20 [1, 1, 2, 0, 1, 1, 2] = some [1, 0, 1, 1, 1, 2, 0] :=
  specInv_white_7 [1, 1, 2, 0, 1, 1, 2] [2, 1, 2, 1, 1, 2, 0] [2, 1, 0, 2, 2, 0, 1] [1, 0, 1, 1, 1, 2, 0] demoR1_1120112 demoR2_1120112 demoC_1120112 demoM_1120112

theorem demoR1_2120112 : invRung 7 5 20 [2, 1, 2, 0, 1, 1, 2] [2, 1, 2, 0, 1, 1, 2] 1 2 false = ([1, 1, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_2120112 : invRung 7 5 20 [2, 1, 2, 0, 1, 1, 2] [1, 1, 2, 2, 2, 0, 2] 3 1 true = ([1, 1, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_2120112 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 1, 1] = [2, 1, 0, 1, 2, 1, 0] := by
  decide

theorem demoM_2120112 : fieldMul 7 5 20 [2, 1, 0, 1, 2, 1, 0] [2, 1, 2, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2120112 : specInv 7 5 20 [2, 1, 2, 0, 1, 1, 2] = some [2, 1, 0, 1, 2, 1, 0] :=
  specInv_white_7 [2, 1, 2, 0, 1, 1, 2] [1, 1, 2, 2, 2, 0, 2] [1, 1, 1, 0, 2, 1, 1] [2, 1, 0, 1, 2, 1, 0] demoR1_2120112 demoR2_2120112 demoC_2120112 demoM_2120112

theorem demoR1_0220112 : invRung 7 5 20 [0, 2, 2, 0, 1, 1, 2] [0, 2, 2, 0, 1, 1, 2] 1 2 false = ([1, 0, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0220112 : invRung 7 5 20 [0, 2, 2, 0, 1, 1, 2] [1, 0, 2, 2, 2, 2, 1] 3 1 true = ([0, 1, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_0220112 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 0, 0] = [0, 1, 0, 2, 0, 1, 0] := by
  decide

theorem demoM_0220112 : fieldMul 7 5 20 [0, 1, 0, 2, 0, 1, 0] [0, 2, 2, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0220112 : specInv 7 5 20 [0, 2, 2, 0, 1, 1, 2] = some [0, 1, 0, 2, 0, 1, 0] :=
  specInv_white_7 [0, 2, 2, 0, 1, 1, 2] [1, 0, 2, 2, 2, 2, 1] [0, 1, 2, 0, 1, 0, 0] [0, 1, 0, 2, 0, 1, 0] demoR1_0220112 demoR2_0220112 demoC_0220112 demoM_0220112

theorem demoR1_1220112 : invRung 7 5 20 [1, 2, 2, 0, 1, 1, 2] [1, 2, 2, 0, 1, 1, 2] 1 2 false = ([2, 2, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_1220112 : invRung 7 5 20 [1, 2, 2, 0, 1, 1, 2] [2, 2, 0, 2, 0, 0, 2] 3 1 true = ([1, 0, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_1220112 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 1, 1] = [0, 0, 1, 2, 2, 1, 2] := by
  decide

theorem demoM_1220112 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 1, 2] [1, 2, 2, 0, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220112 : mirrorTrits [0, 0, 1, 2, 2, 1, 2] = [0, 0, 2, 1, 1, 2, 1] := by
  decide

theorem demoInv_1220112 : specInv 7 5 20 [1, 2, 2, 0, 1, 1, 2] = some [0, 0, 2, 1, 1, 2, 1] :=
  specInv_mirror_7 [1, 2, 2, 0, 1, 1, 2] [2, 2, 0, 2, 0, 0, 2] [1, 0, 1, 1, 1, 1, 1] [0, 0, 1, 2, 2, 1, 2] [0, 0, 2, 1, 1, 2, 1] demoR1_1220112 demoR2_1220112 demoC_1220112 demoM_1220112 demoMir_1220112

theorem demoR1_2220112 : invRung 7 5 20 [2, 2, 2, 0, 1, 1, 2] [2, 2, 2, 0, 1, 1, 2] 1 2 false = ([1, 2, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_2220112 : invRung 7 5 20 [2, 2, 2, 0, 1, 1, 2] [1, 2, 1, 1, 1, 1, 1] 3 1 true = ([1, 1, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_2220112 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 1, 1] = [2, 1, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_2220112 : fieldMul 7 5 20 [2, 1, 0, 1, 2, 1, 2] [2, 2, 2, 0, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2220112 : specInv 7 5 20 [2, 2, 2, 0, 1, 1, 2] = some [2, 1, 0, 1, 2, 1, 2] :=
  specInv_white_7 [2, 2, 2, 0, 1, 1, 2] [1, 2, 1, 1, 1, 1, 1] [1, 1, 0, 0, 2, 1, 1] [2, 1, 0, 1, 2, 1, 2] demoR1_2220112 demoR2_2220112 demoC_2220112 demoM_2220112

theorem demoR1_0001112 : invRung 7 5 20 [0, 0, 0, 1, 1, 1, 2] [0, 0, 0, 1, 1, 1, 2] 1 2 false = ([0, 0, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_0001112 : invRung 7 5 20 [0, 0, 0, 1, 1, 1, 2] [0, 0, 0, 0, 1, 2, 2] 3 1 true = ([2, 1, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_0001112 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 0, 2] = [2, 0, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_0001112 : fieldMul 7 5 20 [2, 0, 1, 1, 2, 0, 1] [0, 0, 0, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0001112 : specInv 7 5 20 [0, 0, 0, 1, 1, 1, 2] = some [2, 0, 1, 1, 2, 0, 1] :=
  specInv_white_7 [0, 0, 0, 1, 1, 1, 2] [0, 0, 0, 0, 1, 2, 2] [2, 1, 1, 0, 1, 0, 2] [2, 0, 1, 1, 2, 0, 1] demoR1_0001112 demoR2_0001112 demoC_0001112 demoM_0001112

theorem demoR1_1001112 : invRung 7 5 20 [1, 0, 0, 1, 1, 1, 2] [1, 0, 0, 1, 1, 1, 2] 1 2 false = ([1, 0, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_1001112 : invRung 7 5 20 [1, 0, 0, 1, 1, 1, 2] [1, 0, 1, 1, 2, 0, 2] 3 1 true = ([0, 0, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_1001112 : fieldCube 7 5 20 [0, 0, 0, 1, 0, 2, 2] = [0, 1, 1, 2, 1, 2, 0] := by
  decide

theorem demoM_1001112 : fieldMul 7 5 20 [0, 1, 1, 2, 1, 2, 0] [1, 0, 0, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1001112 : mirrorTrits [0, 1, 1, 2, 1, 2, 0] = [0, 2, 2, 1, 2, 1, 0] := by
  decide

theorem demoInv_1001112 : specInv 7 5 20 [1, 0, 0, 1, 1, 1, 2] = some [0, 2, 2, 1, 2, 1, 0] :=
  specInv_mirror_7 [1, 0, 0, 1, 1, 1, 2] [1, 0, 1, 1, 2, 0, 2] [0, 0, 0, 1, 0, 2, 2] [0, 1, 1, 2, 1, 2, 0] [0, 2, 2, 1, 2, 1, 0] demoR1_1001112 demoR2_1001112 demoC_1001112 demoM_1001112 demoMir_1001112

theorem demoR1_2001112 : invRung 7 5 20 [2, 0, 0, 1, 1, 1, 2] [2, 0, 0, 1, 1, 1, 2] 1 2 false = ([2, 1, 2, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_2001112 : invRung 7 5 20 [2, 0, 0, 1, 1, 1, 2] [2, 1, 2, 1, 1, 0, 1] 3 1 true = ([1, 1, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_2001112 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 0, 2] = [2, 1, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_2001112 : fieldMul 7 5 20 [2, 1, 2, 2, 2, 2, 1] [2, 0, 0, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001112 : mirrorTrits [2, 1, 2, 2, 2, 2, 1] = [1, 2, 1, 1, 1, 1, 2] := by
  decide

theorem demoInv_2001112 : specInv 7 5 20 [2, 0, 0, 1, 1, 1, 2] = some [1, 2, 1, 1, 1, 1, 2] :=
  specInv_mirror_7 [2, 0, 0, 1, 1, 1, 2] [2, 1, 2, 1, 1, 0, 1] [1, 1, 0, 1, 2, 0, 2] [2, 1, 2, 2, 2, 2, 1] [1, 2, 1, 1, 1, 1, 2] demoR1_2001112 demoR2_2001112 demoC_2001112 demoM_2001112 demoMir_2001112

theorem demoR1_0101112 : invRung 7 5 20 [0, 1, 0, 1, 1, 1, 2] [0, 1, 0, 1, 1, 1, 2] 1 2 false = ([0, 0, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_0101112 : invRung 7 5 20 [0, 1, 0, 1, 1, 1, 2] [0, 0, 0, 2, 2, 0, 2] 3 1 true = ([1, 2, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_0101112 : fieldCube 7 5 20 [1, 2, 2, 0, 2, 0, 0] = [1, 2, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_0101112 : fieldMul 7 5 20 [1, 2, 0, 1, 0, 2, 1] [0, 1, 0, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0101112 : specInv 7 5 20 [0, 1, 0, 1, 1, 1, 2] = some [1, 2, 0, 1, 0, 2, 1] :=
  specInv_white_7 [0, 1, 0, 1, 1, 1, 2] [0, 0, 0, 2, 2, 0, 2] [1, 2, 2, 0, 2, 0, 0] [1, 2, 0, 1, 0, 2, 1] demoR1_0101112 demoR2_0101112 demoC_0101112 demoM_0101112

theorem demoR1_1101112 : invRung 7 5 20 [1, 1, 0, 1, 1, 1, 2] [1, 1, 0, 1, 1, 1, 2] 1 2 false = ([0, 2, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1101112 : invRung 7 5 20 [1, 1, 0, 1, 1, 1, 2] [0, 2, 1, 0, 1, 0, 0] 3 1 true = ([0, 0, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_1101112 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 1, 0] = [0, 0, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_1101112 : fieldMul 7 5 20 [0, 0, 0, 2, 1, 2, 2] [1, 1, 0, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1101112 : mirrorTrits [0, 0, 0, 2, 1, 2, 2] = [0, 0, 0, 1, 2, 1, 1] := by
  decide

theorem demoInv_1101112 : specInv 7 5 20 [1, 1, 0, 1, 1, 1, 2] = some [0, 0, 0, 1, 2, 1, 1] :=
  specInv_mirror_7 [1, 1, 0, 1, 1, 1, 2] [0, 2, 1, 0, 1, 0, 0] [0, 0, 1, 2, 2, 1, 0] [0, 0, 0, 2, 1, 2, 2] [0, 0, 0, 1, 2, 1, 1] demoR1_1101112 demoR2_1101112 demoC_1101112 demoM_1101112 demoMir_1101112

theorem demoR1_2101112 : invRung 7 5 20 [2, 1, 0, 1, 1, 1, 2] [2, 1, 0, 1, 1, 1, 2] 1 2 false = ([2, 1, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_2101112 : invRung 7 5 20 [2, 1, 0, 1, 1, 1, 2] [2, 1, 1, 2, 1, 1, 0] 3 1 true = ([0, 0, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_2101112 : fieldCube 7 5 20 [0, 0, 2, 2, 2, 1, 1] = [0, 1, 2, 0, 2, 0, 1] := by
  decide

theorem demoM_2101112 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 0, 1] [2, 1, 0, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101112 : mirrorTrits [0, 1, 2, 0, 2, 0, 1] = [0, 2, 1, 0, 1, 0, 2] := by
  decide

theorem demoInv_2101112 : specInv 7 5 20 [2, 1, 0, 1, 1, 1, 2] = some [0, 2, 1, 0, 1, 0, 2] :=
  specInv_mirror_7 [2, 1, 0, 1, 1, 1, 2] [2, 1, 1, 2, 1, 1, 0] [0, 0, 2, 2, 2, 1, 1] [0, 1, 2, 0, 2, 0, 1] [0, 2, 1, 0, 1, 0, 2] demoR1_2101112 demoR2_2101112 demoC_2101112 demoM_2101112 demoMir_2101112

theorem demoR1_0201112 : invRung 7 5 20 [0, 2, 0, 1, 1, 1, 2] [0, 2, 0, 1, 1, 1, 2] 1 2 false = ([0, 2, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_0201112 : invRung 7 5 20 [0, 2, 0, 1, 1, 1, 2] [0, 2, 2, 2, 1, 1, 0] 3 1 true = ([1, 2, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_0201112 : fieldCube 7 5 20 [1, 2, 1, 0, 0, 1, 2] = [2, 0, 2, 1, 0, 0, 2] := by
  decide

theorem demoM_0201112 : fieldMul 7 5 20 [2, 0, 2, 1, 0, 0, 2] [0, 2, 0, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0201112 : specInv 7 5 20 [0, 2, 0, 1, 1, 1, 2] = some [2, 0, 2, 1, 0, 0, 2] :=
  specInv_white_7 [0, 2, 0, 1, 1, 1, 2] [0, 2, 2, 2, 1, 1, 0] [1, 2, 1, 0, 0, 1, 2] [2, 0, 2, 1, 0, 0, 2] demoR1_0201112 demoR2_0201112 demoC_0201112 demoM_0201112

theorem demoR1_1201112 : invRung 7 5 20 [1, 2, 0, 1, 1, 1, 2] [1, 2, 0, 1, 1, 1, 2] 1 2 false = ([2, 1, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_1201112 : invRung 7 5 20 [1, 2, 0, 1, 1, 1, 2] [2, 1, 0, 1, 0, 2, 0] 3 1 true = ([0, 0, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_1201112 : fieldCube 7 5 20 [0, 0, 1, 1, 2, 0, 2] = [1, 1, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_1201112 : fieldMul 7 5 20 [1, 1, 2, 1, 2, 2, 2] [1, 2, 0, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201112 : mirrorTrits [1, 1, 2, 1, 2, 2, 2] = [2, 2, 1, 2, 1, 1, 1] := by
  decide

theorem demoInv_1201112 : specInv 7 5 20 [1, 2, 0, 1, 1, 1, 2] = some [2, 2, 1, 2, 1, 1, 1] :=
  specInv_mirror_7 [1, 2, 0, 1, 1, 1, 2] [2, 1, 0, 1, 0, 2, 0] [0, 0, 1, 1, 2, 0, 2] [1, 1, 2, 1, 2, 2, 2] [2, 2, 1, 2, 1, 1, 1] demoR1_1201112 demoR2_1201112 demoC_1201112 demoM_1201112 demoMir_1201112

theorem demoR1_2201112 : invRung 7 5 20 [2, 2, 0, 1, 1, 1, 2] [2, 2, 0, 1, 1, 1, 2] 1 2 false = ([2, 2, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_2201112 : invRung 7 5 20 [2, 2, 0, 1, 1, 1, 2] [2, 2, 2, 0, 0, 0, 2] 3 1 true = ([2, 2, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_2201112 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 1, 0] = [0, 0, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_2201112 : fieldMul 7 5 20 [0, 0, 1, 1, 1, 0, 2] [2, 2, 0, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2201112 : mirrorTrits [0, 0, 1, 1, 1, 0, 2] = [0, 0, 2, 2, 2, 0, 1] := by
  decide

theorem demoInv_2201112 : specInv 7 5 20 [2, 2, 0, 1, 1, 1, 2] = some [0, 0, 2, 2, 2, 0, 1] :=
  specInv_mirror_7 [2, 2, 0, 1, 1, 1, 2] [2, 2, 2, 0, 0, 0, 2] [2, 2, 1, 0, 2, 1, 0] [0, 0, 1, 1, 1, 0, 2] [0, 0, 2, 2, 2, 0, 1] demoR1_2201112 demoR2_2201112 demoC_2201112 demoM_2201112 demoMir_2201112

theorem demoR1_0011112 : invRung 7 5 20 [0, 0, 1, 1, 1, 1, 2] [0, 0, 1, 1, 1, 1, 2] 1 2 false = ([2, 0, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0011112 : invRung 7 5 20 [0, 0, 1, 1, 1, 1, 2] [2, 0, 1, 0, 1, 2, 1] 3 1 true = ([2, 0, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0011112 : fieldCube 7 5 20 [2, 0, 1, 0, 0, 0, 1] = [2, 1, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_0011112 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 1, 2] [0, 0, 1, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011112 : mirrorTrits [2, 1, 2, 1, 1, 1, 2] = [1, 2, 1, 2, 2, 2, 1] := by
  decide

theorem demoInv_0011112 : specInv 7 5 20 [0, 0, 1, 1, 1, 1, 2] = some [1, 2, 1, 2, 2, 2, 1] :=
  specInv_mirror_7 [0, 0, 1, 1, 1, 1, 2] [2, 0, 1, 0, 1, 2, 1] [2, 0, 1, 0, 0, 0, 1] [2, 1, 2, 1, 1, 1, 2] [1, 2, 1, 2, 2, 2, 1] demoR1_0011112 demoR2_0011112 demoC_0011112 demoM_0011112 demoMir_0011112

theorem demoR1_1011112 : invRung 7 5 20 [1, 0, 1, 1, 1, 1, 2] [1, 0, 1, 1, 1, 1, 2] 1 2 false = ([1, 1, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_1011112 : invRung 7 5 20 [1, 0, 1, 1, 1, 1, 2] [1, 1, 1, 0, 1, 1, 1] 3 1 true = ([1, 1, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_1011112 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 1, 0] = [0, 2, 2, 2, 1, 0, 1] := by
  decide

theorem demoM_1011112 : fieldMul 7 5 20 [0, 2, 2, 2, 1, 0, 1] [1, 0, 1, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1011112 : specInv 7 5 20 [1, 0, 1, 1, 1, 1, 2] = some [0, 2, 2, 2, 1, 0, 1] :=
  specInv_white_7 [1, 0, 1, 1, 1, 1, 2] [1, 1, 1, 0, 1, 1, 1] [1, 1, 1, 1, 1, 1, 0] [0, 2, 2, 2, 1, 0, 1] demoR1_1011112 demoR2_1011112 demoC_1011112 demoM_1011112

theorem demoR1_2011112 : invRung 7 5 20 [2, 0, 1, 1, 1, 1, 2] [2, 0, 1, 1, 1, 1, 2] 1 2 false = ([0, 2, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_2011112 : invRung 7 5 20 [2, 0, 1, 1, 1, 1, 2] [0, 2, 1, 1, 1, 1, 1] 3 1 true = ([1, 1, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_2011112 : fieldCube 7 5 20 [1, 1, 2, 2, 0, 1, 2] = [1, 0, 1, 0, 0, 2, 0] := by
  decide

theorem demoM_2011112 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 2, 0] [2, 0, 1, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011112 : mirrorTrits [1, 0, 1, 0, 0, 2, 0] = [2, 0, 2, 0, 0, 1, 0] := by
  decide

theorem demoInv_2011112 : specInv 7 5 20 [2, 0, 1, 1, 1, 1, 2] = some [2, 0, 2, 0, 0, 1, 0] :=
  specInv_mirror_7 [2, 0, 1, 1, 1, 1, 2] [0, 2, 1, 1, 1, 1, 1] [1, 1, 2, 2, 0, 1, 2] [1, 0, 1, 0, 0, 2, 0] [2, 0, 2, 0, 0, 1, 0] demoR1_2011112 demoR2_2011112 demoC_2011112 demoM_2011112 demoMir_2011112

theorem demoR1_0111112 : invRung 7 5 20 [0, 1, 1, 1, 1, 1, 2] [0, 1, 1, 1, 1, 1, 2] 1 2 false = ([2, 2, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_0111112 : invRung 7 5 20 [0, 1, 1, 1, 1, 1, 2] [2, 2, 0, 2, 1, 1, 2] 3 1 true = ([1, 1, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0111112 : fieldCube 7 5 20 [1, 1, 2, 1, 1, 2, 0] = [1, 0, 0, 2, 2, 1, 1] := by
  decide

theorem demoM_0111112 : fieldMul 7 5 20 [1, 0, 0, 2, 2, 1, 1] [0, 1, 1, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111112 : mirrorTrits [1, 0, 0, 2, 2, 1, 1] = [2, 0, 0, 1, 1, 2, 2] := by
  decide

theorem demoInv_0111112 : specInv 7 5 20 [0, 1, 1, 1, 1, 1, 2] = some [2, 0, 0, 1, 1, 2, 2] :=
  specInv_mirror_7 [0, 1, 1, 1, 1, 1, 2] [2, 2, 0, 2, 1, 1, 2] [1, 1, 2, 1, 1, 2, 0] [1, 0, 0, 2, 2, 1, 1] [2, 0, 0, 1, 1, 2, 2] demoR1_0111112 demoR2_0111112 demoC_0111112 demoM_0111112 demoMir_0111112

theorem demoR1_1111112 : invRung 7 5 20 [1, 1, 1, 1, 1, 1, 2] [1, 1, 1, 1, 1, 1, 2] 1 2 false = ([0, 1, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_1111112 : invRung 7 5 20 [1, 1, 1, 1, 1, 1, 2] [0, 1, 1, 1, 0, 0, 2] 3 1 true = ([1, 0, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_1111112 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 1, 2] = [0, 1, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_1111112 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 2, 1] [1, 1, 1, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1111112 : specInv 7 5 20 [1, 1, 1, 1, 1, 1, 2] = some [0, 1, 0, 0, 0, 2, 1] :=
  specInv_white_7 [1, 1, 1, 1, 1, 1, 2] [0, 1, 1, 1, 0, 0, 2] [1, 0, 2, 1, 1, 1, 2] [0, 1, 0, 0, 0, 2, 1] demoR1_1111112 demoR2_1111112 demoC_1111112 demoM_1111112

theorem demoR1_2111112 : invRung 7 5 20 [2, 1, 1, 1, 1, 1, 2] [2, 1, 1, 1, 1, 1, 2] 1 2 false = ([0, 2, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_2111112 : invRung 7 5 20 [2, 1, 1, 1, 1, 1, 2] [0, 2, 1, 0, 2, 2, 2] 3 1 true = ([0, 1, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_2111112 : fieldCube 7 5 20 [0, 1, 1, 2, 1, 0, 0] = [2, 1, 2, 2, 0, 0, 2] := by
  decide

theorem demoM_2111112 : fieldMul 7 5 20 [2, 1, 2, 2, 0, 0, 2] [2, 1, 1, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2111112 : mirrorTrits [2, 1, 2, 2, 0, 0, 2] = [1, 2, 1, 1, 0, 0, 1] := by
  decide

theorem demoInv_2111112 : specInv 7 5 20 [2, 1, 1, 1, 1, 1, 2] = some [1, 2, 1, 1, 0, 0, 1] :=
  specInv_mirror_7 [2, 1, 1, 1, 1, 1, 2] [0, 2, 1, 0, 2, 2, 2] [0, 1, 1, 2, 1, 0, 0] [2, 1, 2, 2, 0, 0, 2] [1, 2, 1, 1, 0, 0, 1] demoR1_2111112 demoR2_2111112 demoC_2111112 demoM_2111112 demoMir_2111112

theorem demoR1_0211112 : invRung 7 5 20 [0, 2, 1, 1, 1, 1, 2] [0, 2, 1, 1, 1, 1, 2] 1 2 false = ([0, 2, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_0211112 : invRung 7 5 20 [0, 2, 1, 1, 1, 1, 2] [0, 2, 2, 2, 2, 1, 1] 3 1 true = ([1, 0, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0211112 : fieldCube 7 5 20 [1, 0, 0, 2, 0, 1, 1] = [1, 2, 2, 1, 2, 1, 0] := by
  decide

theorem demoM_0211112 : fieldMul 7 5 20 [1, 2, 2, 1, 2, 1, 0] [0, 2, 1, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211112 : mirrorTrits [1, 2, 2, 1, 2, 1, 0] = [2, 1, 1, 2, 1, 2, 0] := by
  decide

theorem demoInv_0211112 : specInv 7 5 20 [0, 2, 1, 1, 1, 1, 2] = some [2, 1, 1, 2, 1, 2, 0] :=
  specInv_mirror_7 [0, 2, 1, 1, 1, 1, 2] [0, 2, 2, 2, 2, 1, 1] [1, 0, 0, 2, 0, 1, 1] [1, 2, 2, 1, 2, 1, 0] [2, 1, 1, 2, 1, 2, 0] demoR1_0211112 demoR2_0211112 demoC_0211112 demoM_0211112 demoMir_0211112

theorem demoR1_1211112 : invRung 7 5 20 [1, 2, 1, 1, 1, 1, 2] [1, 2, 1, 1, 1, 1, 2] 1 2 false = ([0, 0, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_1211112 : invRung 7 5 20 [1, 2, 1, 1, 1, 1, 2] [0, 0, 1, 1, 2, 2, 2] 3 1 true = ([2, 2, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_1211112 : fieldCube 7 5 20 [2, 2, 1, 2, 1, 0, 2] = [1, 0, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_1211112 : fieldMul 7 5 20 [1, 0, 0, 2, 2, 2, 1] [1, 2, 1, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1211112 : mirrorTrits [1, 0, 0, 2, 2, 2, 1] = [2, 0, 0, 1, 1, 1, 2] := by
  decide

theorem demoInv_1211112 : specInv 7 5 20 [1, 2, 1, 1, 1, 1, 2] = some [2, 0, 0, 1, 1, 1, 2] :=
  specInv_mirror_7 [1, 2, 1, 1, 1, 1, 2] [0, 0, 1, 1, 2, 2, 2] [2, 2, 1, 2, 1, 0, 2] [1, 0, 0, 2, 2, 2, 1] [2, 0, 0, 1, 1, 1, 2] demoR1_1211112 demoR2_1211112 demoC_1211112 demoM_1211112 demoMir_1211112

theorem demoR1_2211112 : invRung 7 5 20 [2, 2, 1, 1, 1, 1, 2] [2, 2, 1, 1, 1, 1, 2] 1 2 false = ([1, 2, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_2211112 : invRung 7 5 20 [2, 2, 1, 1, 1, 1, 2] [1, 2, 1, 2, 2, 2, 0] 3 1 true = ([1, 1, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_2211112 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 0, 2] = [1, 0, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_2211112 : fieldMul 7 5 20 [1, 0, 1, 1, 2, 0, 1] [2, 2, 1, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211112 : mirrorTrits [1, 0, 1, 1, 2, 0, 1] = [2, 0, 2, 2, 1, 0, 2] := by
  decide

theorem demoInv_2211112 : specInv 7 5 20 [2, 2, 1, 1, 1, 1, 2] = some [2, 0, 2, 2, 1, 0, 2] :=
  specInv_mirror_7 [2, 2, 1, 1, 1, 1, 2] [1, 2, 1, 2, 2, 2, 0] [1, 1, 1, 0, 1, 0, 2] [1, 0, 1, 1, 2, 0, 1] [2, 0, 2, 2, 1, 0, 2] demoR1_2211112 demoR2_2211112 demoC_2211112 demoM_2211112 demoMir_2211112

theorem demoR1_0021112 : invRung 7 5 20 [0, 0, 2, 1, 1, 1, 2] [0, 0, 2, 1, 1, 1, 2] 1 2 false = ([1, 0, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_0021112 : invRung 7 5 20 [0, 0, 2, 1, 1, 1, 2] [1, 0, 2, 0, 1, 1, 2] 3 1 true = ([1, 1, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0021112 : fieldCube 7 5 20 [1, 1, 1, 1, 0, 1, 0] = [0, 1, 2, 1, 1, 2, 0] := by
  decide

theorem demoM_0021112 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 2, 0] [0, 0, 2, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0021112 : specInv 7 5 20 [0, 0, 2, 1, 1, 1, 2] = some [0, 1, 2, 1, 1, 2, 0] :=
  specInv_white_7 [0, 0, 2, 1, 1, 1, 2] [1, 0, 2, 0, 1, 1, 2] [1, 1, 1, 1, 0, 1, 0] [0, 1, 2, 1, 1, 2, 0] demoR1_0021112 demoR2_0021112 demoC_0021112 demoM_0021112

theorem demoR1_1021112 : invRung 7 5 20 [1, 0, 2, 1, 1, 1, 2] [1, 0, 2, 1, 1, 1, 2] 1 2 false = ([0, 2, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_1021112 : invRung 7 5 20 [1, 0, 2, 1, 1, 1, 2] [0, 2, 2, 2, 0, 1, 1] 3 1 true = ([0, 2, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1021112 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 0, 0] = [0, 1, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_1021112 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 1, 0] [1, 0, 2, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1021112 : specInv 7 5 20 [1, 0, 2, 1, 1, 1, 2] = some [0, 1, 0, 0, 0, 1, 0] :=
  specInv_white_7 [1, 0, 2, 1, 1, 1, 2] [0, 2, 2, 2, 0, 1, 1] [0, 2, 2, 0, 1, 0, 0] [0, 1, 0, 0, 0, 1, 0] demoR1_1021112 demoR2_1021112 demoC_1021112 demoM_1021112

theorem demoR1_2021112 : invRung 7 5 20 [2, 0, 2, 1, 1, 1, 2] [2, 0, 2, 1, 1, 1, 2] 1 2 false = ([2, 0, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_2021112 : invRung 7 5 20 [2, 0, 2, 1, 1, 1, 2] [2, 0, 2, 1, 1, 1, 1] 3 1 true = ([1, 2, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_2021112 : fieldCube 7 5 20 [1, 2, 1, 1, 0, 0, 2] = [2, 2, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_2021112 : fieldMul 7 5 20 [2, 2, 2, 1, 2, 0, 0] [2, 0, 2, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021112 : mirrorTrits [2, 2, 2, 1, 2, 0, 0] = [1, 1, 1, 2, 1, 0, 0] := by
  decide

theorem demoInv_2021112 : specInv 7 5 20 [2, 0, 2, 1, 1, 1, 2] = some [1, 1, 1, 2, 1, 0, 0] :=
  specInv_mirror_7 [2, 0, 2, 1, 1, 1, 2] [2, 0, 2, 1, 1, 1, 1] [1, 2, 1, 1, 0, 0, 2] [2, 2, 2, 1, 2, 0, 0] [1, 1, 1, 2, 1, 0, 0] demoR1_2021112 demoR2_2021112 demoC_2021112 demoM_2021112 demoMir_2021112

theorem demoR1_0121112 : invRung 7 5 20 [0, 1, 2, 1, 1, 1, 2] [0, 1, 2, 1, 1, 1, 2] 1 2 false = ([1, 0, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_0121112 : invRung 7 5 20 [0, 1, 2, 1, 1, 1, 2] [1, 0, 2, 1, 2, 0, 0] 3 1 true = ([0, 2, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_0121112 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 2, 1] = [0, 0, 2, 0, 0, 1, 0] := by
  decide

theorem demoM_0121112 : fieldMul 7 5 20 [0, 0, 2, 0, 0, 1, 0] [0, 1, 2, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0121112 : specInv 7 5 20 [0, 1, 2, 1, 1, 1, 2] = some [0, 0, 2, 0, 0, 1, 0] :=
  specInv_white_7 [0, 1, 2, 1, 1, 1, 2] [1, 0, 2, 1, 2, 0, 0] [0, 2, 1, 1, 0, 2, 1] [0, 0, 2, 0, 0, 1, 0] demoR1_0121112 demoR2_0121112 demoC_0121112 demoM_0121112

theorem demoR1_1121112 : invRung 7 5 20 [1, 1, 2, 1, 1, 1, 2] [1, 1, 2, 1, 1, 1, 2] 1 2 false = ([2, 2, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_1121112 : invRung 7 5 20 [1, 1, 2, 1, 1, 1, 2] [2, 2, 1, 1, 1, 1, 1] 3 1 true = ([0, 1, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_1121112 : fieldCube 7 5 20 [0, 1, 1, 1, 1, 1, 0] = [2, 2, 2, 2, 1, 0, 1] := by
  decide

theorem demoM_1121112 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 0, 1] [1, 1, 2, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1121112 : specInv 7 5 20 [1, 1, 2, 1, 1, 1, 2] = some [2, 2, 2, 2, 1, 0, 1] :=
  specInv_white_7 [1, 1, 2, 1, 1, 1, 2] [2, 2, 1, 1, 1, 1, 1] [0, 1, 1, 1, 1, 1, 0] [2, 2, 2, 2, 1, 0, 1] demoR1_1121112 demoR2_1121112 demoC_1121112 demoM_1121112

theorem demoR1_2121112 : invRung 7 5 20 [2, 1, 2, 1, 1, 1, 2] [2, 1, 2, 1, 1, 1, 2] 1 2 false = ([2, 2, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_2121112 : invRung 7 5 20 [2, 1, 2, 1, 1, 1, 2] [2, 2, 2, 0, 2, 1, 0] 3 1 true = ([0, 0, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_2121112 : fieldCube 7 5 20 [0, 0, 0, 2, 1, 1, 1] = [0, 0, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_2121112 : fieldMul 7 5 20 [0, 0, 2, 2, 2, 2, 1] [2, 1, 2, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2121112 : specInv 7 5 20 [2, 1, 2, 1, 1, 1, 2] = some [0, 0, 2, 2, 2, 2, 1] :=
  specInv_white_7 [2, 1, 2, 1, 1, 1, 2] [2, 2, 2, 0, 2, 1, 0] [0, 0, 0, 2, 1, 1, 1] [0, 0, 2, 2, 2, 2, 1] demoR1_2121112 demoR2_2121112 demoC_2121112 demoM_2121112

theorem demoR1_0221112 : invRung 7 5 20 [0, 2, 2, 1, 1, 1, 2] [0, 2, 2, 1, 1, 1, 2] 1 2 false = ([0, 0, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_0221112 : invRung 7 5 20 [0, 2, 2, 1, 1, 1, 2] [0, 0, 0, 0, 1, 1, 2] 3 1 true = ([2, 0, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0221112 : fieldCube 7 5 20 [2, 0, 2, 0, 1, 2, 1] = [1, 1, 1, 2, 0, 1, 2] := by
  decide

theorem demoM_0221112 : fieldMul 7 5 20 [1, 1, 1, 2, 0, 1, 2] [0, 2, 2, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0221112 : specInv 7 5 20 [0, 2, 2, 1, 1, 1, 2] = some [1, 1, 1, 2, 0, 1, 2] :=
  specInv_white_7 [0, 2, 2, 1, 1, 1, 2] [0, 0, 0, 0, 1, 1, 2] [2, 0, 2, 0, 1, 2, 1] [1, 1, 1, 2, 0, 1, 2] demoR1_0221112 demoR2_0221112 demoC_0221112 demoM_0221112

theorem demoR1_1221112 : invRung 7 5 20 [1, 2, 2, 1, 1, 1, 2] [1, 2, 2, 1, 1, 1, 2] 1 2 false = ([0, 0, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_1221112 : invRung 7 5 20 [1, 2, 2, 1, 1, 1, 2] [0, 0, 1, 2, 2, 2, 0] 3 1 true = ([0, 0, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1221112 : fieldCube 7 5 20 [0, 0, 2, 1, 0, 2, 1] = [0, 0, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_1221112 : fieldMul 7 5 20 [0, 0, 2, 1, 0, 1, 1] [1, 2, 2, 1, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221112 : mirrorTrits [0, 0, 2, 1, 0, 1, 1] = [0, 0, 1, 2, 0, 2, 2] := by
  decide

theorem demoInv_1221112 : specInv 7 5 20 [1, 2, 2, 1, 1, 1, 2] = some [0, 0, 1, 2, 0, 2, 2] :=
  specInv_mirror_7 [1, 2, 2, 1, 1, 1, 2] [0, 0, 1, 2, 2, 2, 0] [0, 0, 2, 1, 0, 2, 1] [0, 0, 2, 1, 0, 1, 1] [0, 0, 1, 2, 0, 2, 2] demoR1_1221112 demoR2_1221112 demoC_1221112 demoM_1221112 demoMir_1221112

theorem demoR1_2221112 : invRung 7 5 20 [2, 2, 2, 1, 1, 1, 2] [2, 2, 2, 1, 1, 1, 2] 1 2 false = ([1, 0, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2221112 : invRung 7 5 20 [2, 2, 2, 1, 1, 1, 2] [1, 0, 0, 2, 2, 1, 2] 3 1 true = ([0, 1, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_2221112 : fieldCube 7 5 20 [0, 1, 0, 2, 0, 0, 1] = [2, 1, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_2221112 : fieldMul 7 5 20 [2, 1, 1, 2, 1, 0, 1] [2, 2, 2, 1, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2221112 : specInv 7 5 20 [2, 2, 2, 1, 1, 1, 2] = some [2, 1, 1, 2, 1, 0, 1] :=
  specInv_white_7 [2, 2, 2, 1, 1, 1, 2] [1, 0, 0, 2, 2, 1, 2] [0, 1, 0, 2, 0, 0, 1] [2, 1, 1, 2, 1, 0, 1] demoR1_2221112 demoR2_2221112 demoC_2221112 demoM_2221112

theorem demoR1_0002112 : invRung 7 5 20 [0, 0, 0, 2, 1, 1, 2] [0, 0, 0, 2, 1, 1, 2] 1 2 false = ([0, 1, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_0002112 : invRung 7 5 20 [0, 0, 0, 2, 1, 1, 2] [0, 1, 1, 0, 2, 0, 2] 3 1 true = ([1, 2, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_0002112 : fieldCube 7 5 20 [1, 2, 0, 0, 1, 0, 0] = [1, 1, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_0002112 : fieldMul 7 5 20 [1, 1, 0, 0, 0, 1, 1] [0, 0, 0, 2, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002112 : mirrorTrits [1, 1, 0, 0, 0, 1, 1] = [2, 2, 0, 0, 0, 2, 2] := by
  decide

theorem demoInv_0002112 : specInv 7 5 20 [0, 0, 0, 2, 1, 1, 2] = some [2, 2, 0, 0, 0, 2, 2] :=
  specInv_mirror_7 [0, 0, 0, 2, 1, 1, 2] [0, 1, 1, 0, 2, 0, 2] [1, 2, 0, 0, 1, 0, 0] [1, 1, 0, 0, 0, 1, 1] [2, 2, 0, 0, 0, 2, 2] demoR1_0002112 demoR2_0002112 demoC_0002112 demoM_0002112 demoMir_0002112

theorem demoR1_1002112 : invRung 7 5 20 [1, 0, 0, 2, 1, 1, 2] [1, 0, 0, 2, 1, 1, 2] 1 2 false = ([1, 2, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_1002112 : invRung 7 5 20 [1, 0, 0, 2, 1, 1, 2] [1, 2, 2, 0, 1, 1, 1] 3 1 true = ([0, 0, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_1002112 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 0, 1] = [2, 2, 1, 2, 1, 1, 0] := by
  decide

theorem demoM_1002112 : fieldMul 7 5 20 [2, 2, 1, 2, 1, 1, 0] [1, 0, 0, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1002112 : specInv 7 5 20 [1, 0, 0, 2, 1, 1, 2] = some [2, 2, 1, 2, 1, 1, 0] :=
  specInv_white_7 [1, 0, 0, 2, 1, 1, 2] [1, 2, 2, 0, 1, 1, 1] [0, 0, 1, 2, 1, 0, 1] [2, 2, 1, 2, 1, 1, 0] demoR1_1002112 demoR2_1002112 demoC_1002112 demoM_1002112

theorem demoR1_2002112 : invRung 7 5 20 [2, 0, 0, 2, 1, 1, 2] [2, 0, 0, 2, 1, 1, 2] 1 2 false = ([2, 0, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_2002112 : invRung 7 5 20 [2, 0, 0, 2, 1, 1, 2] [2, 0, 1, 1, 0, 2, 2] 3 1 true = ([1, 0, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_2002112 : fieldCube 7 5 20 [1, 0, 0, 2, 0, 0, 2] = [0, 2, 0, 2, 2, 1, 2] := by
  decide

theorem demoM_2002112 : fieldMul 7 5 20 [0, 2, 0, 2, 2, 1, 2] [2, 0, 0, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2002112 : specInv 7 5 20 [2, 0, 0, 2, 1, 1, 2] = some [0, 2, 0, 2, 2, 1, 2] :=
  specInv_white_7 [2, 0, 0, 2, 1, 1, 2] [2, 0, 1, 1, 0, 2, 2] [1, 0, 0, 2, 0, 0, 2] [0, 2, 0, 2, 2, 1, 2] demoR1_2002112 demoR2_2002112 demoC_2002112 demoM_2002112

theorem demoR1_0102112 : invRung 7 5 20 [0, 1, 0, 2, 1, 1, 2] [0, 1, 0, 2, 1, 1, 2] 1 2 false = ([0, 0, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_0102112 : invRung 7 5 20 [0, 1, 0, 2, 1, 1, 2] [0, 0, 1, 0, 2, 1, 1] 3 1 true = ([1, 0, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_0102112 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 0, 0] = [0, 2, 2, 2, 0, 1, 1] := by
  decide

theorem demoM_0102112 : fieldMul 7 5 20 [0, 2, 2, 2, 0, 1, 1] [0, 1, 0, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0102112 : specInv 7 5 20 [0, 1, 0, 2, 1, 1, 2] = some [0, 2, 2, 2, 0, 1, 1] :=
  specInv_white_7 [0, 1, 0, 2, 1, 1, 2] [0, 0, 1, 0, 2, 1, 1] [1, 0, 2, 2, 2, 0, 0] [0, 2, 2, 2, 0, 1, 1] demoR1_0102112 demoR2_0102112 demoC_0102112 demoM_0102112

theorem demoR1_1102112 : invRung 7 5 20 [1, 1, 0, 2, 1, 1, 2] [1, 1, 0, 2, 1, 1, 2] 1 2 false = ([1, 0, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1102112 : invRung 7 5 20 [1, 1, 0, 2, 1, 1, 2] [1, 0, 2, 0, 1, 0, 1] 3 1 true = ([2, 1, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_1102112 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 0, 1] = [0, 1, 0, 2, 1, 2, 0] := by
  decide

theorem demoM_1102112 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 2, 0] [1, 1, 0, 2, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102112 : mirrorTrits [0, 1, 0, 2, 1, 2, 0] = [0, 2, 0, 1, 2, 1, 0] := by
  decide

theorem demoInv_1102112 : specInv 7 5 20 [1, 1, 0, 2, 1, 1, 2] = some [0, 2, 0, 1, 2, 1, 0] :=
  specInv_mirror_7 [1, 1, 0, 2, 1, 1, 2] [1, 0, 2, 0, 1, 0, 1] [2, 1, 2, 1, 0, 0, 1] [0, 1, 0, 2, 1, 2, 0] [0, 2, 0, 1, 2, 1, 0] demoR1_1102112 demoR2_1102112 demoC_1102112 demoM_1102112 demoMir_1102112

theorem demoR1_2102112 : invRung 7 5 20 [2, 1, 0, 2, 1, 1, 2] [2, 1, 0, 2, 1, 1, 2] 1 2 false = ([1, 2, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2102112 : invRung 7 5 20 [2, 1, 0, 2, 1, 1, 2] [1, 2, 0, 0, 0, 1, 0] 3 1 true = ([1, 2, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_2102112 : fieldCube 7 5 20 [1, 2, 2, 1, 0, 2, 2] = [1, 1, 1, 1, 1, 2, 2] := by
  decide

theorem demoM_2102112 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 2, 2] [2, 1, 0, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2102112 : specInv 7 5 20 [2, 1, 0, 2, 1, 1, 2] = some [1, 1, 1, 1, 1, 2, 2] :=
  specInv_white_7 [2, 1, 0, 2, 1, 1, 2] [1, 2, 0, 0, 0, 1, 0] [1, 2, 2, 1, 0, 2, 2] [1, 1, 1, 1, 1, 2, 2] demoR1_2102112 demoR2_2102112 demoC_2102112 demoM_2102112

theorem demoR1_0202112 : invRung 7 5 20 [0, 2, 0, 2, 1, 1, 2] [0, 2, 0, 2, 1, 1, 2] 1 2 false = ([0, 2, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_0202112 : invRung 7 5 20 [0, 2, 0, 2, 1, 1, 2] [0, 2, 0, 2, 2, 0, 2] 3 1 true = ([2, 0, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0202112 : fieldCube 7 5 20 [2, 0, 0, 2, 2, 0, 2] = [1, 1, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_0202112 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 0, 1] [0, 2, 0, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0202112 : specInv 7 5 20 [0, 2, 0, 2, 1, 1, 2] = some [1, 1, 0, 1, 2, 0, 1] :=
  specInv_white_7 [0, 2, 0, 2, 1, 1, 2] [0, 2, 0, 2, 2, 0, 2] [2, 0, 0, 2, 2, 0, 2] [1, 1, 0, 1, 2, 0, 1] demoR1_0202112 demoR2_0202112 demoC_0202112 demoM_0202112

theorem demoR1_1202112 : invRung 7 5 20 [1, 2, 0, 2, 1, 1, 2] [1, 2, 0, 2, 1, 1, 2] 1 2 false = ([1, 2, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_1202112 : invRung 7 5 20 [1, 2, 0, 2, 1, 1, 2] [1, 2, 1, 0, 0, 2, 1] 3 1 true = ([2, 1, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1202112 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 1, 0] = [1, 0, 2, 0, 1, 1, 2] := by
  decide

theorem demoM_1202112 : fieldMul 7 5 20 [1, 0, 2, 0, 1, 1, 2] [1, 2, 0, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1202112 : specInv 7 5 20 [1, 2, 0, 2, 1, 1, 2] = some [1, 0, 2, 0, 1, 1, 2] :=
  specInv_white_7 [1, 2, 0, 2, 1, 1, 2] [1, 2, 1, 0, 0, 2, 1] [2, 1, 1, 1, 2, 1, 0] [1, 0, 2, 0, 1, 1, 2] demoR1_1202112 demoR2_1202112 demoC_1202112 demoM_1202112

theorem demoR1_2202112 : invRung 7 5 20 [2, 2, 0, 2, 1, 1, 2] [2, 2, 0, 2, 1, 1, 2] 1 2 false = ([0, 0, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_2202112 : invRung 7 5 20 [2, 2, 0, 2, 1, 1, 2] [0, 0, 1, 0, 1, 2, 2] 3 1 true = ([2, 2, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_2202112 : fieldCube 7 5 20 [2, 2, 1, 1, 2, 2, 2] = [2, 0, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_2202112 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 1, 0] [2, 2, 0, 2, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202112 : mirrorTrits [2, 0, 1, 0, 1, 1, 0] = [1, 0, 2, 0, 2, 2, 0] := by
  decide

theorem demoInv_2202112 : specInv 7 5 20 [2, 2, 0, 2, 1, 1, 2] = some [1, 0, 2, 0, 2, 2, 0] :=
  specInv_mirror_7 [2, 2, 0, 2, 1, 1, 2] [0, 0, 1, 0, 1, 2, 2] [2, 2, 1, 1, 2, 2, 2] [2, 0, 1, 0, 1, 1, 0] [1, 0, 2, 0, 2, 2, 0] demoR1_2202112 demoR2_2202112 demoC_2202112 demoM_2202112 demoMir_2202112

theorem demoR1_0012112 : invRung 7 5 20 [0, 0, 1, 2, 1, 1, 2] [0, 0, 1, 2, 1, 1, 2] 1 2 false = ([1, 1, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_0012112 : invRung 7 5 20 [0, 0, 1, 2, 1, 1, 2] [1, 1, 2, 1, 2, 2, 2] 3 1 true = ([2, 0, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_0012112 : fieldCube 7 5 20 [2, 0, 0, 0, 1, 1, 0] = [0, 2, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_0012112 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 2, 0] [0, 0, 1, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0012112 : specInv 7 5 20 [0, 0, 1, 2, 1, 1, 2] = some [0, 2, 1, 1, 1, 2, 0] :=
  specInv_white_7 [0, 0, 1, 2, 1, 1, 2] [1, 1, 2, 1, 2, 2, 2] [2, 0, 0, 0, 1, 1, 0] [0, 2, 1, 1, 1, 2, 0] demoR1_0012112 demoR2_0012112 demoC_0012112 demoM_0012112

theorem demoR1_1012112 : invRung 7 5 20 [1, 0, 1, 2, 1, 1, 2] [1, 0, 1, 2, 1, 1, 2] 1 2 false = ([0, 1, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_1012112 : invRung 7 5 20 [1, 0, 1, 2, 1, 1, 2] [0, 1, 0, 2, 2, 2, 2] 3 1 true = ([1, 1, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_1012112 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 0, 0] = [1, 0, 0, 1, 0, 0, 2] := by
  decide

theorem demoM_1012112 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 0, 2] [1, 0, 1, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1012112 : specInv 7 5 20 [1, 0, 1, 2, 1, 1, 2] = some [1, 0, 0, 1, 0, 0, 2] :=
  specInv_white_7 [1, 0, 1, 2, 1, 1, 2] [0, 1, 0, 2, 2, 2, 2] [1, 1, 2, 0, 0, 0, 0] [1, 0, 0, 1, 0, 0, 2] demoR1_1012112 demoR2_1012112 demoC_1012112 demoM_1012112

theorem demoR1_2012112 : invRung 7 5 20 [2, 0, 1, 2, 1, 1, 2] [2, 0, 1, 2, 1, 1, 2] 1 2 false = ([2, 0, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2012112 : invRung 7 5 20 [2, 0, 1, 2, 1, 1, 2] [2, 0, 2, 0, 1, 1, 2] 3 1 true = ([1, 1, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_2012112 : fieldCube 7 5 20 [1, 1, 2, 1, 2, 1, 1] = [0, 1, 1, 1, 2, 2, 1] := by
  decide

theorem demoM_2012112 : fieldMul 7 5 20 [0, 1, 1, 1, 2, 2, 1] [2, 0, 1, 2, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012112 : mirrorTrits [0, 1, 1, 1, 2, 2, 1] = [0, 2, 2, 2, 1, 1, 2] := by
  decide

theorem demoInv_2012112 : specInv 7 5 20 [2, 0, 1, 2, 1, 1, 2] = some [0, 2, 2, 2, 1, 1, 2] :=
  specInv_mirror_7 [2, 0, 1, 2, 1, 1, 2] [2, 0, 2, 0, 1, 1, 2] [1, 1, 2, 1, 2, 1, 1] [0, 1, 1, 1, 2, 2, 1] [0, 2, 2, 2, 1, 1, 2] demoR1_2012112 demoR2_2012112 demoC_2012112 demoM_2012112 demoMir_2012112

theorem demoR1_0112112 : invRung 7 5 20 [0, 1, 1, 2, 1, 1, 2] [0, 1, 1, 2, 1, 1, 2] 1 2 false = ([2, 1, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_0112112 : invRung 7 5 20 [0, 1, 1, 2, 1, 1, 2] [2, 1, 0, 2, 0, 0, 2] 3 1 true = ([0, 2, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0112112 : fieldCube 7 5 20 [0, 2, 2, 0, 2, 2, 2] = [2, 0, 0, 0, 1, 0, 1] := by
  decide

theorem demoM_0112112 : fieldMul 7 5 20 [2, 0, 0, 0, 1, 0, 1] [0, 1, 1, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0112112 : specInv 7 5 20 [0, 1, 1, 2, 1, 1, 2] = some [2, 0, 0, 0, 1, 0, 1] :=
  specInv_white_7 [0, 1, 1, 2, 1, 1, 2] [2, 1, 0, 2, 0, 0, 2] [0, 2, 2, 0, 2, 2, 2] [2, 0, 0, 0, 1, 0, 1] demoR1_0112112 demoR2_0112112 demoC_0112112 demoM_0112112

theorem demoR1_1112112 : invRung 7 5 20 [1, 1, 1, 2, 1, 1, 2] [1, 1, 1, 2, 1, 1, 2] 1 2 false = ([1, 2, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_1112112 : invRung 7 5 20 [1, 1, 1, 2, 1, 1, 2] [1, 2, 2, 2, 1, 2, 2] 3 1 true = ([2, 2, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_1112112 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 1, 1] = [1, 0, 1, 1, 2, 1, 2] := by
  decide

theorem demoM_1112112 : fieldMul 7 5 20 [1, 0, 1, 1, 2, 1, 2] [1, 1, 1, 2, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112112 : mirrorTrits [1, 0, 1, 1, 2, 1, 2] = [2, 0, 2, 2, 1, 2, 1] := by
  decide

theorem demoInv_1112112 : specInv 7 5 20 [1, 1, 1, 2, 1, 1, 2] = some [2, 0, 2, 2, 1, 2, 1] :=
  specInv_mirror_7 [1, 1, 1, 2, 1, 1, 2] [1, 2, 2, 2, 1, 2, 2] [2, 2, 1, 1, 1, 1, 1] [1, 0, 1, 1, 2, 1, 2] [2, 0, 2, 2, 1, 2, 1] demoR1_1112112 demoR2_1112112 demoC_1112112 demoM_1112112 demoMir_1112112

theorem demoR1_2112112 : invRung 7 5 20 [2, 1, 1, 2, 1, 1, 2] [2, 1, 1, 2, 1, 1, 2] 1 2 false = ([2, 1, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2112112 : invRung 7 5 20 [2, 1, 1, 2, 1, 1, 2] [2, 1, 1, 1, 1, 2, 2] 3 1 true = ([1, 1, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2112112 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 2, 1] = [1, 0, 2, 2, 0, 1, 2] := by
  decide

theorem demoM_2112112 : fieldMul 7 5 20 [1, 0, 2, 2, 0, 1, 2] [2, 1, 1, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2112112 : specInv 7 5 20 [2, 1, 1, 2, 1, 1, 2] = some [1, 0, 2, 2, 0, 1, 2] :=
  specInv_white_7 [2, 1, 1, 2, 1, 1, 2] [2, 1, 1, 1, 1, 2, 2] [1, 1, 0, 1, 0, 2, 1] [1, 0, 2, 2, 0, 1, 2] demoR1_2112112 demoR2_2112112 demoC_2112112 demoM_2112112

theorem demoR1_0212112 : invRung 7 5 20 [0, 2, 1, 2, 1, 1, 2] [0, 2, 1, 2, 1, 1, 2] 1 2 false = ([1, 0, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_0212112 : invRung 7 5 20 [0, 2, 1, 2, 1, 1, 2] [1, 0, 1, 2, 1, 0, 1] 3 1 true = ([0, 1, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0212112 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 1, 1] = [2, 2, 1, 2, 2, 0, 1] := by
  decide

theorem demoM_0212112 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 0, 1] [0, 2, 1, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0212112 : specInv 7 5 20 [0, 2, 1, 2, 1, 1, 2] = some [2, 2, 1, 2, 2, 0, 1] :=
  specInv_white_7 [0, 2, 1, 2, 1, 1, 2] [1, 0, 1, 2, 1, 0, 1] [0, 1, 1, 1, 0, 1, 1] [2, 2, 1, 2, 2, 0, 1] demoR1_0212112 demoR2_0212112 demoC_0212112 demoM_0212112

theorem demoR1_1212112 : invRung 7 5 20 [1, 2, 1, 2, 1, 1, 2] [1, 2, 1, 2, 1, 1, 2] 1 2 false = ([0, 0, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_1212112 : invRung 7 5 20 [1, 2, 1, 2, 1, 1, 2] [0, 0, 1, 2, 2, 0, 2] 3 1 true = ([1, 2, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_1212112 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 0, 0] = [2, 2, 1, 1, 0, 0, 0] := by
  decide

theorem demoM_1212112 : fieldMul 7 5 20 [2, 2, 1, 1, 0, 0, 0] [1, 2, 1, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1212112 : specInv 7 5 20 [1, 2, 1, 2, 1, 1, 2] = some [2, 2, 1, 1, 0, 0, 0] :=
  specInv_white_7 [1, 2, 1, 2, 1, 1, 2] [0, 0, 1, 2, 2, 0, 2] [1, 2, 1, 1, 2, 0, 0] [2, 2, 1, 1, 0, 0, 0] demoR1_1212112 demoR2_1212112 demoC_1212112 demoM_1212112

theorem demoR1_2212112 : invRung 7 5 20 [2, 2, 1, 2, 1, 1, 2] [2, 2, 1, 2, 1, 1, 2] 1 2 false = ([0, 0, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2212112 : invRung 7 5 20 [2, 2, 1, 2, 1, 1, 2] [0, 0, 0, 0, 2, 0, 0] 3 1 true = ([2, 0, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_2212112 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 1, 2] = [0, 1, 2, 0, 0, 1, 0] := by
  decide

theorem demoM_2212112 : fieldMul 7 5 20 [0, 1, 2, 0, 0, 1, 0] [2, 2, 1, 2, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212112 : mirrorTrits [0, 1, 2, 0, 0, 1, 0] = [0, 2, 1, 0, 0, 2, 0] := by
  decide

theorem demoInv_2212112 : specInv 7 5 20 [2, 2, 1, 2, 1, 1, 2] = some [0, 2, 1, 0, 0, 2, 0] :=
  specInv_mirror_7 [2, 2, 1, 2, 1, 1, 2] [0, 0, 0, 0, 2, 0, 0] [2, 0, 1, 0, 1, 1, 2] [0, 1, 2, 0, 0, 1, 0] [0, 2, 1, 0, 0, 2, 0] demoR1_2212112 demoR2_2212112 demoC_2212112 demoM_2212112 demoMir_2212112

theorem demoR1_0022112 : invRung 7 5 20 [0, 0, 2, 2, 1, 1, 2] [0, 0, 2, 2, 1, 1, 2] 1 2 false = ([0, 2, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_0022112 : invRung 7 5 20 [0, 0, 2, 2, 1, 1, 2] [0, 2, 1, 2, 2, 1, 1] 3 1 true = ([2, 2, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0022112 : fieldCube 7 5 20 [2, 2, 0, 0, 2, 0, 1] = [2, 0, 2, 2, 1, 0, 0] := by
  decide

theorem demoM_0022112 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 0, 0] [0, 0, 2, 2, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022112 : mirrorTrits [2, 0, 2, 2, 1, 0, 0] = [1, 0, 1, 1, 2, 0, 0] := by
  decide

theorem demoInv_0022112 : specInv 7 5 20 [0, 0, 2, 2, 1, 1, 2] = some [1, 0, 1, 1, 2, 0, 0] :=
  specInv_mirror_7 [0, 0, 2, 2, 1, 1, 2] [0, 2, 1, 2, 2, 1, 1] [2, 2, 0, 0, 2, 0, 1] [2, 0, 2, 2, 1, 0, 0] [1, 0, 1, 1, 2, 0, 0] demoR1_0022112 demoR2_0022112 demoC_0022112 demoM_0022112 demoMir_0022112

theorem demoR1_1022112 : invRung 7 5 20 [1, 0, 2, 2, 1, 1, 2] [1, 0, 2, 2, 1, 1, 2] 1 2 false = ([2, 1, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1022112 : invRung 7 5 20 [1, 0, 2, 2, 1, 1, 2] [2, 1, 0, 1, 0, 0, 1] 3 1 true = ([0, 1, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_1022112 : fieldCube 7 5 20 [0, 1, 1, 0, 1, 1, 2] = [1, 1, 2, 1, 0, 1, 0] := by
  decide

theorem demoM_1022112 : fieldMul 7 5 20 [1, 1, 2, 1, 0, 1, 0] [1, 0, 2, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1022112 : specInv 7 5 20 [1, 0, 2, 2, 1, 1, 2] = some [1, 1, 2, 1, 0, 1, 0] :=
  specInv_white_7 [1, 0, 2, 2, 1, 1, 2] [2, 1, 0, 1, 0, 0, 1] [0, 1, 1, 0, 1, 1, 2] [1, 1, 2, 1, 0, 1, 0] demoR1_1022112 demoR2_1022112 demoC_1022112 demoM_1022112

theorem demoR1_2022112 : invRung 7 5 20 [2, 0, 2, 2, 1, 1, 2] [2, 0, 2, 2, 1, 1, 2] 1 2 false = ([1, 1, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_2022112 : invRung 7 5 20 [2, 0, 2, 2, 1, 1, 2] [1, 1, 0, 2, 2, 0, 2] 3 1 true = ([2, 0, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_2022112 : fieldCube 7 5 20 [2, 0, 0, 0, 0, 0, 2] = [2, 2, 1, 2, 2, 2, 2] := by
  decide

theorem demoM_2022112 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 2, 2] [2, 0, 2, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2022112 : specInv 7 5 20 [2, 0, 2, 2, 1, 1, 2] = some [2, 2, 1, 2, 2, 2, 2] :=
  specInv_white_7 [2, 0, 2, 2, 1, 1, 2] [1, 1, 0, 2, 2, 0, 2] [2, 0, 0, 0, 0, 0, 2] [2, 2, 1, 2, 2, 2, 2] demoR1_2022112 demoR2_2022112 demoC_2022112 demoM_2022112

theorem demoR1_0122112 : invRung 7 5 20 [0, 1, 2, 2, 1, 1, 2] [0, 1, 2, 2, 1, 1, 2] 1 2 false = ([2, 2, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_0122112 : invRung 7 5 20 [0, 1, 2, 2, 1, 1, 2] [2, 2, 2, 0, 0, 1, 1] 3 1 true = ([1, 1, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0122112 : fieldCube 7 5 20 [1, 1, 2, 1, 0, 0, 0] = [2, 0, 1, 1, 0, 1, 2] := by
  decide

theorem demoM_0122112 : fieldMul 7 5 20 [2, 0, 1, 1, 0, 1, 2] [0, 1, 2, 2, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122112 : mirrorTrits [2, 0, 1, 1, 0, 1, 2] = [1, 0, 2, 2, 0, 2, 1] := by
  decide

theorem demoInv_0122112 : specInv 7 5 20 [0, 1, 2, 2, 1, 1, 2] = some [1, 0, 2, 2, 0, 2, 1] :=
  specInv_mirror_7 [0, 1, 2, 2, 1, 1, 2] [2, 2, 2, 0, 0, 1, 1] [1, 1, 2, 1, 0, 0, 0] [2, 0, 1, 1, 0, 1, 2] [1, 0, 2, 2, 0, 2, 1] demoR1_0122112 demoR2_0122112 demoC_0122112 demoM_0122112 demoMir_0122112

theorem demoR1_1122112 : invRung 7 5 20 [1, 1, 2, 2, 1, 1, 2] [1, 1, 2, 2, 1, 1, 2] 1 2 false = ([1, 1, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_1122112 : invRung 7 5 20 [1, 1, 2, 2, 1, 1, 2] [1, 1, 0, 0, 0, 0, 0] 3 1 true = ([0, 1, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1122112 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 2, 1] = [0, 1, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_1122112 : fieldMul 7 5 20 [0, 1, 2, 0, 0, 2, 2] [1, 1, 2, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1122112 : specInv 7 5 20 [1, 1, 2, 2, 1, 1, 2] = some [0, 1, 2, 0, 0, 2, 2] :=
  specInv_white_7 [1, 1, 2, 2, 1, 1, 2] [1, 1, 0, 0, 0, 0, 0] [0, 1, 2, 1, 1, 2, 1] [0, 1, 2, 0, 0, 2, 2] demoR1_1122112 demoR2_1122112 demoC_1122112 demoM_1122112

theorem demoR1_2122112 : invRung 7 5 20 [2, 1, 2, 2, 1, 1, 2] [2, 1, 2, 2, 1, 1, 2] 1 2 false = ([2, 0, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2122112 : invRung 7 5 20 [2, 1, 2, 2, 1, 1, 2] [2, 0, 1, 1, 1, 2, 0] 3 1 true = ([0, 0, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_2122112 : fieldCube 7 5 20 [0, 0, 2, 0, 1, 2, 0] = [2, 0, 2, 1, 2, 0, 1] := by
  decide

theorem demoM_2122112 : fieldMul 7 5 20 [2, 0, 2, 1, 2, 0, 1] [2, 1, 2, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2122112 : specInv 7 5 20 [2, 1, 2, 2, 1, 1, 2] = some [2, 0, 2, 1, 2, 0, 1] :=
  specInv_white_7 [2, 1, 2, 2, 1, 1, 2] [2, 0, 1, 1, 1, 2, 0] [0, 0, 2, 0, 1, 2, 0] [2, 0, 2, 1, 2, 0, 1] demoR1_2122112 demoR2_2122112 demoC_2122112 demoM_2122112

theorem demoR1_0222112 : invRung 7 5 20 [0, 2, 2, 2, 1, 1, 2] [0, 2, 2, 2, 1, 1, 2] 1 2 false = ([0, 0, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_0222112 : invRung 7 5 20 [0, 2, 2, 2, 1, 1, 2] [0, 0, 1, 0, 1, 1, 0] 3 1 true = ([1, 2, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_0222112 : fieldCube 7 5 20 [1, 2, 0, 2, 1, 1, 1] = [1, 0, 2, 1, 2, 2, 1] := by
  decide

theorem demoM_0222112 : fieldMul 7 5 20 [1, 0, 2, 1, 2, 2, 1] [0, 2, 2, 2, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222112 : mirrorTrits [1, 0, 2, 1, 2, 2, 1] = [2, 0, 1, 2, 1, 1, 2] := by
  decide

theorem demoInv_0222112 : specInv 7 5 20 [0, 2, 2, 2, 1, 1, 2] = some [2, 0, 1, 2, 1, 1, 2] :=
  specInv_mirror_7 [0, 2, 2, 2, 1, 1, 2] [0, 0, 1, 0, 1, 1, 0] [1, 2, 0, 2, 1, 1, 1] [1, 0, 2, 1, 2, 2, 1] [2, 0, 1, 2, 1, 1, 2] demoR1_0222112 demoR2_0222112 demoC_0222112 demoM_0222112 demoMir_0222112

theorem demoR1_1222112 : invRung 7 5 20 [1, 2, 2, 2, 1, 1, 2] [1, 2, 2, 2, 1, 1, 2] 1 2 false = ([2, 0, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_1222112 : invRung 7 5 20 [1, 2, 2, 2, 1, 1, 2] [2, 0, 1, 2, 2, 2, 2] 3 1 true = ([1, 0, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1222112 : fieldCube 7 5 20 [1, 0, 0, 0, 1, 1, 0] = [2, 2, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_1222112 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 2, 0] [1, 2, 2, 2, 1, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222112 : mirrorTrits [2, 2, 1, 1, 1, 2, 0] = [1, 1, 2, 2, 2, 1, 0] := by
  decide

theorem demoInv_1222112 : specInv 7 5 20 [1, 2, 2, 2, 1, 1, 2] = some [1, 1, 2, 2, 2, 1, 0] :=
  specInv_mirror_7 [1, 2, 2, 2, 1, 1, 2] [2, 0, 1, 2, 2, 2, 2] [1, 0, 0, 0, 1, 1, 0] [2, 2, 1, 1, 1, 2, 0] [1, 1, 2, 2, 2, 1, 0] demoR1_1222112 demoR2_1222112 demoC_1222112 demoM_1222112 demoMir_1222112

theorem demoR1_2222112 : invRung 7 5 20 [2, 2, 2, 2, 1, 1, 2] [2, 2, 2, 2, 1, 1, 2] 1 2 false = ([2, 2, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2222112 : invRung 7 5 20 [2, 2, 2, 2, 1, 1, 2] [2, 2, 0, 1, 1, 2, 2] 3 1 true = ([1, 2, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_2222112 : fieldCube 7 5 20 [1, 2, 1, 0, 0, 0, 0] = [1, 0, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_2222112 : fieldMul 7 5 20 [1, 0, 0, 2, 0, 0, 1] [2, 2, 2, 2, 1, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2222112 : specInv 7 5 20 [2, 2, 2, 2, 1, 1, 2] = some [1, 0, 0, 2, 0, 0, 1] :=
  specInv_white_7 [2, 2, 2, 2, 1, 1, 2] [2, 2, 0, 1, 1, 2, 2] [1, 2, 1, 0, 0, 0, 0] [1, 0, 0, 2, 0, 0, 1] demoR1_2222112 demoR2_2222112 demoC_2222112 demoM_2222112

theorem demoR1_0000212 : invRung 7 5 20 [0, 0, 0, 0, 2, 1, 2] [0, 0, 0, 0, 2, 1, 2] 1 2 false = ([2, 2, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_0000212 : invRung 7 5 20 [0, 0, 0, 0, 2, 1, 2] [2, 2, 1, 1, 0, 2, 2] 3 1 true = ([1, 2, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_0000212 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 0, 0] = [1, 1, 0, 0, 0, 1, 2] := by
  decide

theorem demoM_0000212 : fieldMul 7 5 20 [1, 1, 0, 0, 0, 1, 2] [0, 0, 0, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000212 : mirrorTrits [1, 1, 0, 0, 0, 1, 2] = [2, 2, 0, 0, 0, 2, 1] := by
  decide

theorem demoInv_0000212 : specInv 7 5 20 [0, 0, 0, 0, 2, 1, 2] = some [2, 2, 0, 0, 0, 2, 1] :=
  specInv_mirror_7 [0, 0, 0, 0, 2, 1, 2] [2, 2, 1, 1, 0, 2, 2] [1, 2, 1, 0, 1, 0, 0] [1, 1, 0, 0, 0, 1, 2] [2, 2, 0, 0, 0, 2, 1] demoR1_0000212 demoR2_0000212 demoC_0000212 demoM_0000212 demoMir_0000212

theorem demoR1_1000212 : invRung 7 5 20 [1, 0, 0, 0, 2, 1, 2] [1, 0, 0, 0, 2, 1, 2] 1 2 false = ([2, 1, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_1000212 : invRung 7 5 20 [1, 0, 0, 0, 2, 1, 2] [2, 1, 2, 2, 2, 0, 2] 3 1 true = ([0, 2, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1000212 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 1, 0] = [1, 2, 1, 0, 1, 2, 2] := by
  decide

theorem demoM_1000212 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 2, 2] [1, 0, 0, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000212 : mirrorTrits [1, 2, 1, 0, 1, 2, 2] = [2, 1, 2, 0, 2, 1, 1] := by
  decide

theorem demoInv_1000212 : specInv 7 5 20 [1, 0, 0, 0, 2, 1, 2] = some [2, 1, 2, 0, 2, 1, 1] :=
  specInv_mirror_7 [1, 0, 0, 0, 2, 1, 2] [2, 1, 2, 2, 2, 0, 2] [0, 2, 2, 0, 1, 1, 0] [1, 2, 1, 0, 1, 2, 2] [2, 1, 2, 0, 2, 1, 1] demoR1_1000212 demoR2_1000212 demoC_1000212 demoM_1000212 demoMir_1000212

theorem demoR1_2000212 : invRung 7 5 20 [2, 0, 0, 0, 2, 1, 2] [2, 0, 0, 0, 2, 1, 2] 1 2 false = ([0, 2, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2000212 : invRung 7 5 20 [2, 0, 0, 0, 2, 1, 2] [0, 2, 1, 0, 0, 1, 0] 3 1 true = ([0, 0, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_2000212 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 0, 1] = [0, 0, 2, 0, 1, 0, 1] := by
  decide

theorem demoM_2000212 : fieldMul 7 5 20 [0, 0, 2, 0, 1, 0, 1] [2, 0, 0, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2000212 : specInv 7 5 20 [2, 0, 0, 0, 2, 1, 2] = some [0, 0, 2, 0, 1, 0, 1] :=
  specInv_white_7 [2, 0, 0, 0, 2, 1, 2] [0, 2, 1, 0, 0, 1, 0] [0, 0, 1, 0, 2, 0, 1] [0, 0, 2, 0, 1, 0, 1] demoR1_2000212 demoR2_2000212 demoC_2000212 demoM_2000212

theorem demoR1_0100212 : invRung 7 5 20 [0, 1, 0, 0, 2, 1, 2] [0, 1, 0, 0, 2, 1, 2] 1 2 false = ([0, 1, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0100212 : invRung 7 5 20 [0, 1, 0, 0, 2, 1, 2] [0, 1, 1, 2, 1, 2, 1] 3 1 true = ([0, 0, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_0100212 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 2, 0] = [0, 1, 0, 2, 2, 2, 0] := by
  decide

theorem demoM_0100212 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 2, 0] [0, 1, 0, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100212 : mirrorTrits [0, 1, 0, 2, 2, 2, 0] = [0, 2, 0, 1, 1, 1, 0] := by
  decide

theorem demoInv_0100212 : specInv 7 5 20 [0, 1, 0, 0, 2, 1, 2] = some [0, 2, 0, 1, 1, 1, 0] :=
  specInv_mirror_7 [0, 1, 0, 0, 2, 1, 2] [0, 1, 1, 2, 1, 2, 1] [0, 0, 0, 1, 2, 2, 0] [0, 1, 0, 2, 2, 2, 0] [0, 2, 0, 1, 1, 1, 0] demoR1_0100212 demoR2_0100212 demoC_0100212 demoM_0100212 demoMir_0100212

theorem demoR1_1100212 : invRung 7 5 20 [1, 1, 0, 0, 2, 1, 2] [1, 1, 0, 0, 2, 1, 2] 1 2 false = ([2, 2, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_1100212 : invRung 7 5 20 [1, 1, 0, 0, 2, 1, 2] [2, 2, 1, 0, 0, 0, 2] 3 1 true = ([0, 0, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1100212 : fieldCube 7 5 20 [0, 0, 0, 1, 1, 2, 1] = [0, 1, 2, 2, 0, 2, 0] := by
  decide

theorem demoM_1100212 : fieldMul 7 5 20 [0, 1, 2, 2, 0, 2, 0] [1, 1, 0, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1100212 : mirrorTrits [0, 1, 2, 2, 0, 2, 0] = [0, 2, 1, 1, 0, 1, 0] := by
  decide

theorem demoInv_1100212 : specInv 7 5 20 [1, 1, 0, 0, 2, 1, 2] = some [0, 2, 1, 1, 0, 1, 0] :=
  specInv_mirror_7 [1, 1, 0, 0, 2, 1, 2] [2, 2, 1, 0, 0, 0, 2] [0, 0, 0, 1, 1, 2, 1] [0, 1, 2, 2, 0, 2, 0] [0, 2, 1, 1, 0, 1, 0] demoR1_1100212 demoR2_1100212 demoC_1100212 demoM_1100212 demoMir_1100212

theorem demoR1_2100212 : invRung 7 5 20 [2, 1, 0, 0, 2, 1, 2] [2, 1, 0, 0, 2, 1, 2] 1 2 false = ([1, 1, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_2100212 : invRung 7 5 20 [2, 1, 0, 0, 2, 1, 2] [1, 1, 1, 0, 1, 0, 1] 3 1 true = ([2, 1, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2100212 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 2, 0] = [2, 2, 0, 1, 2, 0, 0] := by
  decide

theorem demoM_2100212 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 0, 0] [2, 1, 0, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100212 : mirrorTrits [2, 2, 0, 1, 2, 0, 0] = [1, 1, 0, 2, 1, 0, 0] := by
  decide

theorem demoInv_2100212 : specInv 7 5 20 [2, 1, 0, 0, 2, 1, 2] = some [1, 1, 0, 2, 1, 0, 0] :=
  specInv_mirror_7 [2, 1, 0, 0, 2, 1, 2] [1, 1, 1, 0, 1, 0, 1] [2, 1, 2, 1, 0, 2, 0] [2, 2, 0, 1, 2, 0, 0] [1, 1, 0, 2, 1, 0, 0] demoR1_2100212 demoR2_2100212 demoC_2100212 demoM_2100212 demoMir_2100212

theorem demoR1_0200212 : invRung 7 5 20 [0, 2, 0, 0, 2, 1, 2] [0, 2, 0, 0, 2, 1, 2] 1 2 false = ([1, 2, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_0200212 : invRung 7 5 20 [0, 2, 0, 0, 2, 1, 2] [1, 2, 1, 1, 2, 0, 1] 3 1 true = ([0, 0, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_0200212 : fieldCube 7 5 20 [0, 0, 1, 2, 0, 2, 0] = [1, 2, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_0200212 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 1, 2] [0, 2, 0, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200212 : mirrorTrits [1, 2, 1, 0, 2, 1, 2] = [2, 1, 2, 0, 1, 2, 1] := by
  decide

theorem demoInv_0200212 : specInv 7 5 20 [0, 2, 0, 0, 2, 1, 2] = some [2, 1, 2, 0, 1, 2, 1] :=
  specInv_mirror_7 [0, 2, 0, 0, 2, 1, 2] [1, 2, 1, 1, 2, 0, 1] [0, 0, 1, 2, 0, 2, 0] [1, 2, 1, 0, 2, 1, 2] [2, 1, 2, 0, 1, 2, 1] demoR1_0200212 demoR2_0200212 demoC_0200212 demoM_0200212 demoMir_0200212

theorem demoR1_1200212 : invRung 7 5 20 [1, 2, 0, 0, 2, 1, 2] [1, 2, 0, 0, 2, 1, 2] 1 2 false = ([2, 0, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_1200212 : invRung 7 5 20 [1, 2, 0, 0, 2, 1, 2] [2, 0, 0, 0, 0, 0, 1] 3 1 true = ([0, 1, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_1200212 : fieldCube 7 5 20 [0, 1, 1, 1, 2, 1, 1] = [2, 1, 1, 1, 2, 2, 0] := by
  decide

theorem demoM_1200212 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 2, 0] [1, 2, 0, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1200212 : specInv 7 5 20 [1, 2, 0, 0, 2, 1, 2] = some [2, 1, 1, 1, 2, 2, 0] :=
  specInv_white_7 [1, 2, 0, 0, 2, 1, 2] [2, 0, 0, 0, 0, 0, 1] [0, 1, 1, 1, 2, 1, 1] [2, 1, 1, 1, 2, 2, 0] demoR1_1200212 demoR2_1200212 demoC_1200212 demoM_1200212

theorem demoR1_2200212 : invRung 7 5 20 [2, 2, 0, 0, 2, 1, 2] [2, 2, 0, 0, 2, 1, 2] 1 2 false = ([2, 1, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_2200212 : invRung 7 5 20 [2, 2, 0, 0, 2, 1, 2] [2, 1, 1, 0, 0, 1, 2] 3 1 true = ([2, 2, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_2200212 : fieldCube 7 5 20 [2, 2, 2, 2, 0, 0, 0] = [1, 0, 2, 2, 0, 2, 2] := by
  decide

theorem demoM_2200212 : fieldMul 7 5 20 [1, 0, 2, 2, 0, 2, 2] [2, 2, 0, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200212 : mirrorTrits [1, 0, 2, 2, 0, 2, 2] = [2, 0, 1, 1, 0, 1, 1] := by
  decide

theorem demoInv_2200212 : specInv 7 5 20 [2, 2, 0, 0, 2, 1, 2] = some [2, 0, 1, 1, 0, 1, 1] :=
  specInv_mirror_7 [2, 2, 0, 0, 2, 1, 2] [2, 1, 1, 0, 0, 1, 2] [2, 2, 2, 2, 0, 0, 0] [1, 0, 2, 2, 0, 2, 2] [2, 0, 1, 1, 0, 1, 1] demoR1_2200212 demoR2_2200212 demoC_2200212 demoM_2200212 demoMir_2200212

theorem demoR1_0010212 : invRung 7 5 20 [0, 0, 1, 0, 2, 1, 2] [0, 0, 1, 0, 2, 1, 2] 1 2 false = ([1, 1, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_0010212 : invRung 7 5 20 [0, 0, 1, 0, 2, 1, 2] [1, 1, 0, 0, 1, 0, 0] 3 1 true = ([1, 2, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0010212 : fieldCube 7 5 20 [1, 2, 2, 1, 0, 0, 0] = [2, 0, 1, 2, 0, 1, 2] := by
  decide

theorem demoM_0010212 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 1, 2] [0, 0, 1, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0010212 : specInv 7 5 20 [0, 0, 1, 0, 2, 1, 2] = some [2, 0, 1, 2, 0, 1, 2] :=
  specInv_white_7 [0, 0, 1, 0, 2, 1, 2] [1, 1, 0, 0, 1, 0, 0] [1, 2, 2, 1, 0, 0, 0] [2, 0, 1, 2, 0, 1, 2] demoR1_0010212 demoR2_0010212 demoC_0010212 demoM_0010212

theorem demoR1_1010212 : invRung 7 5 20 [1, 0, 1, 0, 2, 1, 2] [1, 0, 1, 0, 2, 1, 2] 1 2 false = ([1, 2, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1010212 : invRung 7 5 20 [1, 0, 1, 0, 2, 1, 2] [1, 2, 1, 1, 2, 2, 1] 3 1 true = ([2, 0, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_1010212 : fieldCube 7 5 20 [2, 0, 2, 1, 0, 2, 2] = [2, 1, 1, 2, 1, 2, 2] := by
  decide

theorem demoM_1010212 : fieldMul 7 5 20 [2, 1, 1, 2, 1, 2, 2] [1, 0, 1, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1010212 : mirrorTrits [2, 1, 1, 2, 1, 2, 2] = [1, 2, 2, 1, 2, 1, 1] := by
  decide

theorem demoInv_1010212 : specInv 7 5 20 [1, 0, 1, 0, 2, 1, 2] = some [1, 2, 2, 1, 2, 1, 1] :=
  specInv_mirror_7 [1, 0, 1, 0, 2, 1, 2] [1, 2, 1, 1, 2, 2, 1] [2, 0, 2, 1, 0, 2, 2] [2, 1, 1, 2, 1, 2, 2] [1, 2, 2, 1, 2, 1, 1] demoR1_1010212 demoR2_1010212 demoC_1010212 demoM_1010212 demoMir_1010212

theorem demoR1_2010212 : invRung 7 5 20 [2, 0, 1, 0, 2, 1, 2] [2, 0, 1, 0, 2, 1, 2] 1 2 false = ([2, 1, 0, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_2010212 : invRung 7 5 20 [2, 0, 1, 0, 2, 1, 2] [2, 1, 0, 1, 1, 0, 1] 3 1 true = ([0, 0, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_2010212 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 2, 1] = [1, 1, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_2010212 : fieldMul 7 5 20 [1, 1, 0, 2, 0, 0, 1] [2, 0, 1, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2010212 : specInv 7 5 20 [2, 0, 1, 0, 2, 1, 2] = some [1, 1, 0, 2, 0, 0, 1] :=
  specInv_white_7 [2, 0, 1, 0, 2, 1, 2] [2, 1, 0, 1, 1, 0, 1] [0, 0, 1, 2, 1, 2, 1] [1, 1, 0, 2, 0, 0, 1] demoR1_2010212 demoR2_2010212 demoC_2010212 demoM_2010212

theorem demoR1_0110212 : invRung 7 5 20 [0, 1, 1, 0, 2, 1, 2] [0, 1, 1, 0, 2, 1, 2] 1 2 false = ([1, 0, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_0110212 : invRung 7 5 20 [0, 1, 1, 0, 2, 1, 2] [1, 0, 1, 1, 1, 1, 0] 3 1 true = ([0, 2, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0110212 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 0, 0] = [1, 1, 1, 0, 0, 2, 2] := by
  decide

theorem demoM_0110212 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 2, 2] [0, 1, 1, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110212 : mirrorTrits [1, 1, 1, 0, 0, 2, 2] = [2, 2, 2, 0, 0, 1, 1] := by
  decide

theorem demoInv_0110212 : specInv 7 5 20 [0, 1, 1, 0, 2, 1, 2] = some [2, 2, 2, 0, 0, 1, 1] :=
  specInv_mirror_7 [0, 1, 1, 0, 2, 1, 2] [1, 0, 1, 1, 1, 1, 0] [0, 2, 1, 1, 1, 0, 0] [1, 1, 1, 0, 0, 2, 2] [2, 2, 2, 0, 0, 1, 1] demoR1_0110212 demoR2_0110212 demoC_0110212 demoM_0110212 demoMir_0110212

theorem demoR1_1110212 : invRung 7 5 20 [1, 1, 1, 0, 2, 1, 2] [1, 1, 1, 0, 2, 1, 2] 1 2 false = ([0, 2, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_1110212 : invRung 7 5 20 [1, 1, 1, 0, 2, 1, 2] [0, 2, 2, 1, 0, 1, 1] 3 1 true = ([1, 2, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_1110212 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 2, 1] = [2, 1, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_1110212 : fieldMul 7 5 20 [2, 1, 0, 1, 0, 0, 1] [1, 1, 1, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1110212 : specInv 7 5 20 [1, 1, 1, 0, 2, 1, 2] = some [2, 1, 0, 1, 0, 0, 1] :=
  specInv_white_7 [1, 1, 1, 0, 2, 1, 2] [0, 2, 2, 1, 0, 1, 1] [1, 2, 1, 2, 1, 2, 1] [2, 1, 0, 1, 0, 0, 1] demoR1_1110212 demoR2_1110212 demoC_1110212 demoM_1110212

theorem demoR1_2110212 : invRung 7 5 20 [2, 1, 1, 0, 2, 1, 2] [2, 1, 1, 0, 2, 1, 2] 1 2 false = ([2, 1, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_2110212 : invRung 7 5 20 [2, 1, 1, 0, 2, 1, 2] [2, 1, 0, 2, 0, 2, 1] 3 1 true = ([1, 2, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_2110212 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 2, 0] = [0, 0, 2, 0, 2, 0, 0] := by
  decide

theorem demoM_2110212 : fieldMul 7 5 20 [0, 0, 2, 0, 2, 0, 0] [2, 1, 1, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2110212 : specInv 7 5 20 [2, 1, 1, 0, 2, 1, 2] = some [0, 0, 2, 0, 2, 0, 0] :=
  specInv_white_7 [2, 1, 1, 0, 2, 1, 2] [2, 1, 0, 2, 0, 2, 1] [1, 2, 1, 0, 1, 2, 0] [0, 0, 2, 0, 2, 0, 0] demoR1_2110212 demoR2_2110212 demoC_2110212 demoM_2110212

theorem demoR1_0210212 : invRung 7 5 20 [0, 2, 1, 0, 2, 1, 2] [0, 2, 1, 0, 2, 1, 2] 1 2 false = ([2, 0, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0210212 : invRung 7 5 20 [0, 2, 1, 0, 2, 1, 2] [2, 0, 0, 0, 1, 1, 1] 3 1 true = ([2, 1, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_0210212 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 1, 1] = [1, 1, 1, 1, 2, 2, 0] := by
  decide

theorem demoM_0210212 : fieldMul 7 5 20 [1, 1, 1, 1, 2, 2, 0] [0, 2, 1, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0210212 : specInv 7 5 20 [0, 2, 1, 0, 2, 1, 2] = some [1, 1, 1, 1, 2, 2, 0] :=
  specInv_white_7 [0, 2, 1, 0, 2, 1, 2] [2, 0, 0, 0, 1, 1, 1] [2, 1, 1, 1, 2, 1, 1] [1, 1, 1, 1, 2, 2, 0] demoR1_0210212 demoR2_0210212 demoC_0210212 demoM_0210212

theorem demoR1_1210212 : invRung 7 5 20 [1, 2, 1, 0, 2, 1, 2] [1, 2, 1, 0, 2, 1, 2] 1 2 false = ([0, 1, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_1210212 : invRung 7 5 20 [1, 2, 1, 0, 2, 1, 2] [0, 1, 1, 0, 0, 1, 0] 3 1 true = ([2, 2, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_1210212 : fieldCube 7 5 20 [2, 2, 0, 1, 0, 0, 1] = [0, 1, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_1210212 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 2, 1] [1, 2, 1, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1210212 : specInv 7 5 20 [1, 2, 1, 0, 2, 1, 2] = some [0, 1, 0, 0, 1, 2, 1] :=
  specInv_white_7 [1, 2, 1, 0, 2, 1, 2] [0, 1, 1, 0, 0, 1, 0] [2, 2, 0, 1, 0, 0, 1] [0, 1, 0, 0, 1, 2, 1] demoR1_1210212 demoR2_1210212 demoC_1210212 demoM_1210212

theorem demoR1_2210212 : invRung 7 5 20 [2, 2, 1, 0, 2, 1, 2] [2, 2, 1, 0, 2, 1, 2] 1 2 false = ([0, 1, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_2210212 : invRung 7 5 20 [2, 2, 1, 0, 2, 1, 2] [0, 1, 1, 0, 0, 1, 1] 3 1 true = ([2, 1, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_2210212 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 0, 0] = [0, 0, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_2210212 : fieldMul 7 5 20 [0, 0, 1, 1, 0, 1, 1] [2, 2, 1, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2210212 : specInv 7 5 20 [2, 2, 1, 0, 2, 1, 2] = some [0, 0, 1, 1, 0, 1, 1] :=
  specInv_white_7 [2, 2, 1, 0, 2, 1, 2] [0, 1, 1, 0, 0, 1, 1] [2, 1, 1, 1, 0, 0, 0] [0, 0, 1, 1, 0, 1, 1] demoR1_2210212 demoR2_2210212 demoC_2210212 demoM_2210212

theorem demoR1_0020212 : invRung 7 5 20 [0, 0, 2, 0, 2, 1, 2] [0, 0, 2, 0, 2, 1, 2] 1 2 false = ([2, 0, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_0020212 : invRung 7 5 20 [0, 0, 2, 0, 2, 1, 2] [2, 0, 1, 0, 0, 0, 1] 3 1 true = ([0, 0, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_0020212 : fieldCube 7 5 20 [0, 0, 2, 0, 0, 1, 2] = [1, 0, 2, 2, 0, 0, 0] := by
  decide

theorem demoM_0020212 : fieldMul 7 5 20 [1, 0, 2, 2, 0, 0, 0] [0, 0, 2, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0020212 : specInv 7 5 20 [0, 0, 2, 0, 2, 1, 2] = some [1, 0, 2, 2, 0, 0, 0] :=
  specInv_white_7 [0, 0, 2, 0, 2, 1, 2] [2, 0, 1, 0, 0, 0, 1] [0, 0, 2, 0, 0, 1, 2] [1, 0, 2, 2, 0, 0, 0] demoR1_0020212 demoR2_0020212 demoC_0020212 demoM_0020212

theorem demoR1_1020212 : invRung 7 5 20 [1, 0, 2, 0, 2, 1, 2] [1, 0, 2, 0, 2, 1, 2] 1 2 false = ([1, 0, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_1020212 : invRung 7 5 20 [1, 0, 2, 0, 2, 1, 2] [1, 0, 0, 1, 0, 0, 2] 3 1 true = ([2, 2, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_1020212 : fieldCube 7 5 20 [2, 2, 0, 2, 0, 1, 1] = [2, 2, 2, 0, 2, 1, 0] := by
  decide

theorem demoM_1020212 : fieldMul 7 5 20 [2, 2, 2, 0, 2, 1, 0] [1, 0, 2, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1020212 : specInv 7 5 20 [1, 0, 2, 0, 2, 1, 2] = some [2, 2, 2, 0, 2, 1, 0] :=
  specInv_white_7 [1, 0, 2, 0, 2, 1, 2] [1, 0, 0, 1, 0, 0, 2] [2, 2, 0, 2, 0, 1, 1] [2, 2, 2, 0, 2, 1, 0] demoR1_1020212 demoR2_1020212 demoC_1020212 demoM_1020212

theorem demoR1_2020212 : invRung 7 5 20 [2, 0, 2, 0, 2, 1, 2] [2, 0, 2, 0, 2, 1, 2] 1 2 false = ([1, 0, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2020212 : invRung 7 5 20 [2, 0, 2, 0, 2, 1, 2] [1, 0, 0, 0, 0, 1, 0] 3 1 true = ([0, 1, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_2020212 : fieldCube 7 5 20 [0, 1, 1, 0, 2, 2, 2] = [2, 0, 0, 2, 1, 0, 0] := by
  decide

theorem demoM_2020212 : fieldMul 7 5 20 [2, 0, 0, 2, 1, 0, 0] [2, 0, 2, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2020212 : specInv 7 5 20 [2, 0, 2, 0, 2, 1, 2] = some [2, 0, 0, 2, 1, 0, 0] :=
  specInv_white_7 [2, 0, 2, 0, 2, 1, 2] [1, 0, 0, 0, 0, 1, 0] [0, 1, 1, 0, 2, 2, 2] [2, 0, 0, 2, 1, 0, 0] demoR1_2020212 demoR2_2020212 demoC_2020212 demoM_2020212

theorem demoR1_0120212 : invRung 7 5 20 [0, 1, 2, 0, 2, 1, 2] [0, 1, 2, 0, 2, 1, 2] 1 2 false = ([1, 1, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0120212 : invRung 7 5 20 [0, 1, 2, 0, 2, 1, 2] [1, 1, 2, 0, 1, 1, 1] 3 1 true = ([0, 0, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0120212 : fieldCube 7 5 20 [0, 0, 2, 0, 0, 1, 1] = [1, 2, 0, 1, 2, 2, 2] := by
  decide

theorem demoM_0120212 : fieldMul 7 5 20 [1, 2, 0, 1, 2, 2, 2] [0, 1, 2, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0120212 : mirrorTrits [1, 2, 0, 1, 2, 2, 2] = [2, 1, 0, 2, 1, 1, 1] := by
  decide

theorem demoInv_0120212 : specInv 7 5 20 [0, 1, 2, 0, 2, 1, 2] = some [2, 1, 0, 2, 1, 1, 1] :=
  specInv_mirror_7 [0, 1, 2, 0, 2, 1, 2] [1, 1, 2, 0, 1, 1, 1] [0, 0, 2, 0, 0, 1, 1] [1, 2, 0, 1, 2, 2, 2] [2, 1, 0, 2, 1, 1, 1] demoR1_0120212 demoR2_0120212 demoC_0120212 demoM_0120212 demoMir_0120212

theorem demoR1_1120212 : invRung 7 5 20 [1, 1, 2, 0, 2, 1, 2] [1, 1, 2, 0, 2, 1, 2] 1 2 false = ([2, 1, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1120212 : invRung 7 5 20 [1, 1, 2, 0, 2, 1, 2] [2, 1, 2, 2, 0, 0, 1] 3 1 true = ([1, 1, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_1120212 : fieldCube 7 5 20 [1, 1, 0, 2, 0, 2, 1] = [2, 0, 0, 2, 0, 2, 2] := by
  decide

theorem demoM_1120212 : fieldMul 7 5 20 [2, 0, 0, 2, 0, 2, 2] [1, 1, 2, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120212 : mirrorTrits [2, 0, 0, 2, 0, 2, 2] = [1, 0, 0, 1, 0, 1, 1] := by
  decide

theorem demoInv_1120212 : specInv 7 5 20 [1, 1, 2, 0, 2, 1, 2] = some [1, 0, 0, 1, 0, 1, 1] :=
  specInv_mirror_7 [1, 1, 2, 0, 2, 1, 2] [2, 1, 2, 2, 0, 0, 1] [1, 1, 0, 2, 0, 2, 1] [2, 0, 0, 2, 0, 2, 2] [1, 0, 0, 1, 0, 1, 1] demoR1_1120212 demoR2_1120212 demoC_1120212 demoM_1120212 demoMir_1120212

theorem demoR1_2120212 : invRung 7 5 20 [2, 1, 2, 0, 2, 1, 2] [2, 1, 2, 0, 2, 1, 2] 1 2 false = ([0, 0, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_2120212 : invRung 7 5 20 [2, 1, 2, 0, 2, 1, 2] [0, 0, 2, 1, 2, 2, 1] 3 1 true = ([1, 2, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_2120212 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 0, 2] = [2, 1, 2, 0, 2, 2, 2] := by
  decide

theorem demoM_2120212 : fieldMul 7 5 20 [2, 1, 2, 0, 2, 2, 2] [2, 1, 2, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120212 : mirrorTrits [2, 1, 2, 0, 2, 2, 2] = [1, 2, 1, 0, 1, 1, 1] := by
  decide

theorem demoInv_2120212 : specInv 7 5 20 [2, 1, 2, 0, 2, 1, 2] = some [1, 2, 1, 0, 1, 1, 1] :=
  specInv_mirror_7 [2, 1, 2, 0, 2, 1, 2] [0, 0, 2, 1, 2, 2, 1] [1, 2, 1, 1, 2, 0, 2] [2, 1, 2, 0, 2, 2, 2] [1, 2, 1, 0, 1, 1, 1] demoR1_2120212 demoR2_2120212 demoC_2120212 demoM_2120212 demoMir_2120212

theorem demoR1_0220212 : invRung 7 5 20 [0, 2, 2, 0, 2, 1, 2] [0, 2, 2, 0, 2, 1, 2] 1 2 false = ([2, 2, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_0220212 : invRung 7 5 20 [0, 2, 2, 0, 2, 1, 2] [2, 2, 2, 1, 2, 2, 2] 3 1 true = ([0, 1, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0220212 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 1, 2] = [0, 1, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_0220212 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 0, 2] [0, 2, 2, 0, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0220212 : specInv 7 5 20 [0, 2, 2, 0, 2, 1, 2] = some [0, 1, 1, 1, 0, 0, 2] :=
  specInv_white_7 [0, 2, 2, 0, 2, 1, 2] [2, 2, 2, 1, 2, 2, 2] [0, 1, 0, 2, 1, 1, 2] [0, 1, 1, 1, 0, 0, 2] demoR1_0220212 demoR2_0220212 demoC_0220212 demoM_0220212

theorem demoR1_1220212 : invRung 7 5 20 [1, 2, 2, 0, 2, 1, 2] [1, 2, 2, 0, 2, 1, 2] 1 2 false = ([2, 0, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_1220212 : invRung 7 5 20 [1, 2, 2, 0, 2, 1, 2] [2, 0, 0, 2, 2, 2, 2] 3 1 true = ([2, 2, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1220212 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 1, 0] = [1, 0, 2, 1, 1, 1, 1] := by
  decide

theorem demoM_1220212 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 1, 1] [1, 2, 2, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220212 : mirrorTrits [1, 0, 2, 1, 1, 1, 1] = [2, 0, 1, 2, 2, 2, 2] := by
  decide

theorem demoInv_1220212 : specInv 7 5 20 [1, 2, 2, 0, 2, 1, 2] = some [2, 0, 1, 2, 2, 2, 2] :=
  specInv_mirror_7 [1, 2, 2, 0, 2, 1, 2] [2, 0, 0, 2, 2, 2, 2] [2, 2, 0, 1, 2, 1, 0] [1, 0, 2, 1, 1, 1, 1] [2, 0, 1, 2, 2, 2, 2] demoR1_1220212 demoR2_1220212 demoC_1220212 demoM_1220212 demoMir_1220212

theorem demoR1_2220212 : invRung 7 5 20 [2, 2, 2, 0, 2, 1, 2] [2, 2, 2, 0, 2, 1, 2] 1 2 false = ([1, 2, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2220212 : invRung 7 5 20 [2, 2, 2, 0, 2, 1, 2] [1, 2, 0, 2, 2, 1, 2] 3 1 true = ([2, 1, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_2220212 : fieldCube 7 5 20 [2, 1, 1, 1, 1, 2, 2] = [2, 2, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_2220212 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 0, 2] [2, 2, 2, 0, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220212 : mirrorTrits [2, 2, 1, 1, 1, 0, 2] = [1, 1, 2, 2, 2, 0, 1] := by
  decide

theorem demoInv_2220212 : specInv 7 5 20 [2, 2, 2, 0, 2, 1, 2] = some [1, 1, 2, 2, 2, 0, 1] :=
  specInv_mirror_7 [2, 2, 2, 0, 2, 1, 2] [1, 2, 0, 2, 2, 1, 2] [2, 1, 1, 1, 1, 2, 2] [2, 2, 1, 1, 1, 0, 2] [1, 1, 2, 2, 2, 0, 1] demoR1_2220212 demoR2_2220212 demoC_2220212 demoM_2220212 demoMir_2220212

theorem demoR1_0001212 : invRung 7 5 20 [0, 0, 0, 1, 2, 1, 2] [0, 0, 0, 1, 2, 1, 2] 1 2 false = ([1, 1, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0001212 : invRung 7 5 20 [0, 0, 0, 1, 2, 1, 2] [1, 1, 2, 1, 0, 0, 0] 3 1 true = ([1, 2, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_0001212 : fieldCube 7 5 20 [1, 2, 1, 1, 1, 1, 0] = [0, 2, 2, 0, 1, 0, 1] := by
  decide

theorem demoM_0001212 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 0, 1] [0, 0, 0, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0001212 : specInv 7 5 20 [0, 0, 0, 1, 2, 1, 2] = some [0, 2, 2, 0, 1, 0, 1] :=
  specInv_white_7 [0, 0, 0, 1, 2, 1, 2] [1, 1, 2, 1, 0, 0, 0] [1, 2, 1, 1, 1, 1, 0] [0, 2, 2, 0, 1, 0, 1] demoR1_0001212 demoR2_0001212 demoC_0001212 demoM_0001212

theorem demoR1_1001212 : invRung 7 5 20 [1, 0, 0, 1, 2, 1, 2] [1, 0, 0, 1, 2, 1, 2] 1 2 false = ([1, 2, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_1001212 : invRung 7 5 20 [1, 0, 0, 1, 2, 1, 2] [1, 2, 0, 2, 2, 0, 1] 3 1 true = ([1, 1, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_1001212 : fieldCube 7 5 20 [1, 1, 0, 0, 0, 0, 2] = [1, 2, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_1001212 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 2, 2] [1, 0, 0, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1001212 : specInv 7 5 20 [1, 0, 0, 1, 2, 1, 2] = some [1, 2, 1, 0, 2, 2, 2] :=
  specInv_white_7 [1, 0, 0, 1, 2, 1, 2] [1, 2, 0, 2, 2, 0, 1] [1, 1, 0, 0, 0, 0, 2] [1, 2, 1, 0, 2, 2, 2] demoR1_1001212 demoR2_1001212 demoC_1001212 demoM_1001212

theorem demoR1_2001212 : invRung 7 5 20 [2, 0, 0, 1, 2, 1, 2] [2, 0, 0, 1, 2, 1, 2] 1 2 false = ([2, 1, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_2001212 : invRung 7 5 20 [2, 0, 0, 1, 2, 1, 2] [2, 1, 0, 2, 2, 1, 0] 3 1 true = ([1, 0, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_2001212 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 0, 0] = [2, 1, 1, 1, 0, 2, 0] := by
  decide

theorem demoM_2001212 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 2, 0] [2, 0, 0, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2001212 : specInv 7 5 20 [2, 0, 0, 1, 2, 1, 2] = some [2, 1, 1, 1, 0, 2, 0] :=
  specInv_white_7 [2, 0, 0, 1, 2, 1, 2] [2, 1, 0, 2, 2, 1, 0] [1, 0, 2, 1, 1, 0, 0] [2, 1, 1, 1, 0, 2, 0] demoR1_2001212 demoR2_2001212 demoC_2001212 demoM_2001212

theorem demoR1_0101212 : invRung 7 5 20 [0, 1, 0, 1, 2, 1, 2] [0, 1, 0, 1, 2, 1, 2] 1 2 false = ([0, 1, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_0101212 : invRung 7 5 20 [0, 1, 0, 1, 2, 1, 2] [0, 1, 2, 1, 0, 1, 2] 3 1 true = ([1, 2, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_0101212 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 0, 0] = [1, 2, 0, 1, 0, 2, 0] := by
  decide

theorem demoM_0101212 : fieldMul 7 5 20 [1, 2, 0, 1, 0, 2, 0] [0, 1, 0, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0101212 : specInv 7 5 20 [0, 1, 0, 1, 2, 1, 2] = some [1, 2, 0, 1, 0, 2, 0] :=
  specInv_white_7 [0, 1, 0, 1, 2, 1, 2] [0, 1, 2, 1, 0, 1, 2] [1, 2, 1, 0, 2, 0, 0] [1, 2, 0, 1, 0, 2, 0] demoR1_0101212 demoR2_0101212 demoC_0101212 demoM_0101212

theorem demoR1_1101212 : invRung 7 5 20 [1, 1, 0, 1, 2, 1, 2] [1, 1, 0, 1, 2, 1, 2] 1 2 false = ([0, 1, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_1101212 : invRung 7 5 20 [1, 1, 0, 1, 2, 1, 2] [0, 1, 2, 2, 1, 0, 1] 3 1 true = ([0, 0, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_1101212 : fieldCube 7 5 20 [0, 0, 1, 1, 1, 1, 1] = [2, 0, 1, 2, 2, 1, 2] := by
  decide

theorem demoM_1101212 : fieldMul 7 5 20 [2, 0, 1, 2, 2, 1, 2] [1, 1, 0, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1101212 : specInv 7 5 20 [1, 1, 0, 1, 2, 1, 2] = some [2, 0, 1, 2, 2, 1, 2] :=
  specInv_white_7 [1, 1, 0, 1, 2, 1, 2] [0, 1, 2, 2, 1, 0, 1] [0, 0, 1, 1, 1, 1, 1] [2, 0, 1, 2, 2, 1, 2] demoR1_1101212 demoR2_1101212 demoC_1101212 demoM_1101212

theorem demoR1_2101212 : invRung 7 5 20 [2, 1, 0, 1, 2, 1, 2] [2, 1, 0, 1, 2, 1, 2] 1 2 false = ([0, 1, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2101212 : invRung 7 5 20 [2, 1, 0, 1, 2, 1, 2] [0, 1, 0, 1, 0, 2, 1] 3 1 true = ([1, 0, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2101212 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 2, 2] = [2, 2, 2, 0, 1, 1, 2] := by
  decide

theorem demoM_2101212 : fieldMul 7 5 20 [2, 2, 2, 0, 1, 1, 2] [2, 1, 0, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2101212 : specInv 7 5 20 [2, 1, 0, 1, 2, 1, 2] = some [2, 2, 2, 0, 1, 1, 2] :=
  specInv_white_7 [2, 1, 0, 1, 2, 1, 2] [0, 1, 0, 1, 0, 2, 1] [1, 0, 1, 2, 1, 2, 2] [2, 2, 2, 0, 1, 1, 2] demoR1_2101212 demoR2_2101212 demoC_2101212 demoM_2101212

theorem demoR1_0201212 : invRung 7 5 20 [0, 2, 0, 1, 2, 1, 2] [0, 2, 0, 1, 2, 1, 2] 1 2 false = ([2, 1, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_0201212 : invRung 7 5 20 [0, 2, 0, 1, 2, 1, 2] [2, 1, 2, 0, 2, 1, 0] 3 1 true = ([1, 1, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0201212 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 1, 2] = [2, 2, 2, 2, 0, 2, 1] := by
  decide

theorem demoM_0201212 : fieldMul 7 5 20 [2, 2, 2, 2, 0, 2, 1] [0, 2, 0, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201212 : mirrorTrits [2, 2, 2, 2, 0, 2, 1] = [1, 1, 1, 1, 0, 1, 2] := by
  decide

theorem demoInv_0201212 : specInv 7 5 20 [0, 2, 0, 1, 2, 1, 2] = some [1, 1, 1, 1, 0, 1, 2] :=
  specInv_mirror_7 [0, 2, 0, 1, 2, 1, 2] [2, 1, 2, 0, 2, 1, 0] [1, 1, 1, 0, 2, 1, 2] [2, 2, 2, 2, 0, 2, 1] [1, 1, 1, 1, 0, 1, 2] demoR1_0201212 demoR2_0201212 demoC_0201212 demoM_0201212 demoMir_0201212

theorem demoR1_1201212 : invRung 7 5 20 [1, 2, 0, 1, 2, 1, 2] [1, 2, 0, 1, 2, 1, 2] 1 2 false = ([2, 1, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_1201212 : invRung 7 5 20 [1, 2, 0, 1, 2, 1, 2] [2, 1, 1, 2, 1, 1, 1] 3 1 true = ([0, 1, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_1201212 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 2, 2] = [2, 1, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_1201212 : fieldMul 7 5 20 [2, 1, 0, 0, 1, 1, 1] [1, 2, 0, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201212 : mirrorTrits [2, 1, 0, 0, 1, 1, 1] = [1, 2, 0, 0, 2, 2, 2] := by
  decide

theorem demoInv_1201212 : specInv 7 5 20 [1, 2, 0, 1, 2, 1, 2] = some [1, 2, 0, 0, 2, 2, 2] :=
  specInv_mirror_7 [1, 2, 0, 1, 2, 1, 2] [2, 1, 1, 2, 1, 1, 1] [0, 1, 1, 0, 0, 2, 2] [2, 1, 0, 0, 1, 1, 1] [1, 2, 0, 0, 2, 2, 2] demoR1_1201212 demoR2_1201212 demoC_1201212 demoM_1201212 demoMir_1201212

theorem demoR1_2201212 : invRung 7 5 20 [2, 2, 0, 1, 2, 1, 2] [2, 2, 0, 1, 2, 1, 2] 1 2 false = ([1, 0, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_2201212 : invRung 7 5 20 [2, 2, 0, 1, 2, 1, 2] [1, 0, 0, 1, 1, 0, 0] 3 1 true = ([1, 0, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2201212 : fieldCube 7 5 20 [1, 0, 1, 0, 1, 0, 0] = [1, 1, 0, 1, 0, 1, 2] := by
  decide

theorem demoM_2201212 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 1, 2] [2, 2, 0, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2201212 : mirrorTrits [1, 1, 0, 1, 0, 1, 2] = [2, 2, 0, 2, 0, 2, 1] := by
  decide

theorem demoInv_2201212 : specInv 7 5 20 [2, 2, 0, 1, 2, 1, 2] = some [2, 2, 0, 2, 0, 2, 1] :=
  specInv_mirror_7 [2, 2, 0, 1, 2, 1, 2] [1, 0, 0, 1, 1, 0, 0] [1, 0, 1, 0, 1, 0, 0] [1, 1, 0, 1, 0, 1, 2] [2, 2, 0, 2, 0, 2, 1] demoR1_2201212 demoR2_2201212 demoC_2201212 demoM_2201212 demoMir_2201212

theorem demoR1_0011212 : invRung 7 5 20 [0, 0, 1, 1, 2, 1, 2] [0, 0, 1, 1, 2, 1, 2] 1 2 false = ([2, 2, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0011212 : invRung 7 5 20 [0, 0, 1, 1, 2, 1, 2] [2, 2, 2, 2, 0, 0, 0] 3 1 true = ([0, 1, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_0011212 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 2, 1] = [0, 0, 2, 2, 0, 1, 2] := by
  decide

theorem demoM_0011212 : fieldMul 7 5 20 [0, 0, 2, 2, 0, 1, 2] [0, 0, 1, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0011212 : specInv 7 5 20 [0, 0, 1, 1, 2, 1, 2] = some [0, 0, 2, 2, 0, 1, 2] :=
  specInv_white_7 [0, 0, 1, 1, 2, 1, 2] [2, 2, 2, 2, 0, 0, 0] [0, 1, 0, 1, 0, 2, 1] [0, 0, 2, 2, 0, 1, 2] demoR1_0011212 demoR2_0011212 demoC_0011212 demoM_0011212

theorem demoR1_1011212 : invRung 7 5 20 [1, 0, 1, 1, 2, 1, 2] [1, 0, 1, 1, 2, 1, 2] 1 2 false = ([2, 0, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_1011212 : invRung 7 5 20 [1, 0, 1, 1, 2, 1, 2] [2, 0, 1, 2, 0, 2, 0] 3 1 true = ([0, 1, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_1011212 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 2, 0] = [2, 2, 2, 1, 2, 2, 1] := by
  decide

theorem demoM_1011212 : fieldMul 7 5 20 [2, 2, 2, 1, 2, 2, 1] [1, 0, 1, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1011212 : specInv 7 5 20 [1, 0, 1, 1, 2, 1, 2] = some [2, 2, 2, 1, 2, 2, 1] :=
  specInv_white_7 [1, 0, 1, 1, 2, 1, 2] [2, 0, 1, 2, 0, 2, 0] [0, 1, 0, 0, 0, 2, 0] [2, 2, 2, 1, 2, 2, 1] demoR1_1011212 demoR2_1011212 demoC_1011212 demoM_1011212

theorem demoR1_2011212 : invRung 7 5 20 [2, 0, 1, 1, 2, 1, 2] [2, 0, 1, 1, 2, 1, 2] 1 2 false = ([0, 1, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_2011212 : invRung 7 5 20 [2, 0, 1, 1, 2, 1, 2] [0, 1, 2, 0, 0, 1, 2] 3 1 true = ([2, 1, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2011212 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 1, 1] = [0, 0, 0, 0, 2, 0, 2] := by
  decide

theorem demoM_2011212 : fieldMul 7 5 20 [0, 0, 0, 0, 2, 0, 2] [2, 0, 1, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011212 : mirrorTrits [0, 0, 0, 0, 2, 0, 2] = [0, 0, 0, 0, 1, 0, 1] := by
  decide

theorem demoInv_2011212 : specInv 7 5 20 [2, 0, 1, 1, 2, 1, 2] = some [0, 0, 0, 0, 1, 0, 1] :=
  specInv_mirror_7 [2, 0, 1, 1, 2, 1, 2] [0, 1, 2, 0, 0, 1, 2] [2, 1, 1, 0, 1, 1, 1] [0, 0, 0, 0, 2, 0, 2] [0, 0, 0, 0, 1, 0, 1] demoR1_2011212 demoR2_2011212 demoC_2011212 demoM_2011212 demoMir_2011212

theorem demoR1_0111212 : invRung 7 5 20 [0, 1, 1, 1, 2, 1, 2] [0, 1, 1, 1, 2, 1, 2] 1 2 false = ([1, 1, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_0111212 : invRung 7 5 20 [0, 1, 1, 1, 2, 1, 2] [1, 1, 2, 0, 1, 1, 0] 3 1 true = ([2, 0, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0111212 : fieldCube 7 5 20 [2, 0, 0, 0, 2, 1, 2] = [0, 2, 2, 1, 0, 2, 0] := by
  decide

theorem demoM_0111212 : fieldMul 7 5 20 [0, 2, 2, 1, 0, 2, 0] [0, 1, 1, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111212 : mirrorTrits [0, 2, 2, 1, 0, 2, 0] = [0, 1, 1, 2, 0, 1, 0] := by
  decide

theorem demoInv_0111212 : specInv 7 5 20 [0, 1, 1, 1, 2, 1, 2] = some [0, 1, 1, 2, 0, 1, 0] :=
  specInv_mirror_7 [0, 1, 1, 1, 2, 1, 2] [1, 1, 2, 0, 1, 1, 0] [2, 0, 0, 0, 2, 1, 2] [0, 2, 2, 1, 0, 2, 0] [0, 1, 1, 2, 0, 1, 0] demoR1_0111212 demoR2_0111212 demoC_0111212 demoM_0111212 demoMir_0111212

theorem demoR1_1111212 : invRung 7 5 20 [1, 1, 1, 1, 2, 1, 2] [1, 1, 1, 1, 2, 1, 2] 1 2 false = ([1, 0, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_1111212 : invRung 7 5 20 [1, 1, 1, 1, 2, 1, 2] [1, 0, 1, 2, 1, 0, 0] 3 1 true = ([0, 2, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_1111212 : fieldCube 7 5 20 [0, 2, 1, 0, 1, 2, 2] = [2, 2, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_1111212 : fieldMul 7 5 20 [2, 2, 0, 2, 1, 2, 2] [1, 1, 1, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111212 : mirrorTrits [2, 2, 0, 2, 1, 2, 2] = [1, 1, 0, 1, 2, 1, 1] := by
  decide

theorem demoInv_1111212 : specInv 7 5 20 [1, 1, 1, 1, 2, 1, 2] = some [1, 1, 0, 1, 2, 1, 1] :=
  specInv_mirror_7 [1, 1, 1, 1, 2, 1, 2] [1, 0, 1, 2, 1, 0, 0] [0, 2, 1, 0, 1, 2, 2] [2, 2, 0, 2, 1, 2, 2] [1, 1, 0, 1, 2, 1, 1] demoR1_1111212 demoR2_1111212 demoC_1111212 demoM_1111212 demoMir_1111212

theorem demoR1_2111212 : invRung 7 5 20 [2, 1, 1, 1, 2, 1, 2] [2, 1, 1, 1, 2, 1, 2] 1 2 false = ([1, 1, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_2111212 : invRung 7 5 20 [2, 1, 1, 1, 2, 1, 2] [1, 1, 1, 1, 1, 1, 2] 3 1 true = ([1, 2, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_2111212 : fieldCube 7 5 20 [1, 2, 0, 0, 0, 2, 1] = [0, 0, 1, 0, 0, 0, 2] := by
  decide

theorem demoM_2111212 : fieldMul 7 5 20 [0, 0, 1, 0, 0, 0, 2] [2, 1, 1, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2111212 : specInv 7 5 20 [2, 1, 1, 1, 2, 1, 2] = some [0, 0, 1, 0, 0, 0, 2] :=
  specInv_white_7 [2, 1, 1, 1, 2, 1, 2] [1, 1, 1, 1, 1, 1, 2] [1, 2, 0, 0, 0, 2, 1] [0, 0, 1, 0, 0, 0, 2] demoR1_2111212 demoR2_2111212 demoC_2111212 demoM_2111212

theorem demoR1_0211212 : invRung 7 5 20 [0, 2, 1, 1, 2, 1, 2] [0, 2, 1, 1, 2, 1, 2] 1 2 false = ([1, 2, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_0211212 : invRung 7 5 20 [0, 2, 1, 1, 2, 1, 2] [1, 2, 0, 0, 1, 2, 2] 3 1 true = ([1, 1, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0211212 : fieldCube 7 5 20 [1, 1, 0, 2, 0, 1, 1] = [1, 2, 2, 2, 2, 1, 0] := by
  decide

theorem demoM_0211212 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 1, 0] [0, 2, 1, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211212 : mirrorTrits [1, 2, 2, 2, 2, 1, 0] = [2, 1, 1, 1, 1, 2, 0] := by
  decide

theorem demoInv_0211212 : specInv 7 5 20 [0, 2, 1, 1, 2, 1, 2] = some [2, 1, 1, 1, 1, 2, 0] :=
  specInv_mirror_7 [0, 2, 1, 1, 2, 1, 2] [1, 2, 0, 0, 1, 2, 2] [1, 1, 0, 2, 0, 1, 1] [1, 2, 2, 2, 2, 1, 0] [2, 1, 1, 1, 1, 2, 0] demoR1_0211212 demoR2_0211212 demoC_0211212 demoM_0211212 demoMir_0211212

theorem demoR1_1211212 : invRung 7 5 20 [1, 2, 1, 1, 2, 1, 2] [1, 2, 1, 1, 2, 1, 2] 1 2 false = ([1, 0, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_1211212 : invRung 7 5 20 [1, 2, 1, 1, 2, 1, 2] [1, 0, 2, 2, 0, 0, 0] 3 1 true = ([0, 2, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_1211212 : fieldCube 7 5 20 [0, 2, 0, 1, 1, 2, 2] = [0, 2, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_1211212 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 0, 1] [1, 2, 1, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1211212 : specInv 7 5 20 [1, 2, 1, 1, 2, 1, 2] = some [0, 2, 1, 2, 1, 0, 1] :=
  specInv_white_7 [1, 2, 1, 1, 2, 1, 2] [1, 0, 2, 2, 0, 0, 0] [0, 2, 0, 1, 1, 2, 2] [0, 2, 1, 2, 1, 0, 1] demoR1_1211212 demoR2_1211212 demoC_1211212 demoM_1211212

theorem demoR1_2211212 : invRung 7 5 20 [2, 2, 1, 1, 2, 1, 2] [2, 2, 1, 1, 2, 1, 2] 1 2 false = ([0, 2, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2211212 : invRung 7 5 20 [2, 2, 1, 1, 2, 1, 2] [0, 2, 1, 0, 2, 2, 0] 3 1 true = ([2, 1, 0, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_2211212 : fieldCube 7 5 20 [2, 1, 0, 1, 1, 0, 1] = [0, 2, 0, 0, 1, 0, 2] := by
  decide

theorem demoM_2211212 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 0, 2] [2, 2, 1, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211212 : mirrorTrits [0, 2, 0, 0, 1, 0, 2] = [0, 1, 0, 0, 2, 0, 1] := by
  decide

theorem demoInv_2211212 : specInv 7 5 20 [2, 2, 1, 1, 2, 1, 2] = some [0, 1, 0, 0, 2, 0, 1] :=
  specInv_mirror_7 [2, 2, 1, 1, 2, 1, 2] [0, 2, 1, 0, 2, 2, 0] [2, 1, 0, 1, 1, 0, 1] [0, 2, 0, 0, 1, 0, 2] [0, 1, 0, 0, 2, 0, 1] demoR1_2211212 demoR2_2211212 demoC_2211212 demoM_2211212 demoMir_2211212

theorem demoR1_0021212 : invRung 7 5 20 [0, 0, 2, 1, 2, 1, 2] [0, 0, 2, 1, 2, 1, 2] 1 2 false = ([0, 1, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_0021212 : invRung 7 5 20 [0, 0, 2, 1, 2, 1, 2] [0, 1, 2, 1, 1, 0, 0] 3 1 true = ([2, 1, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_0021212 : fieldCube 7 5 20 [2, 1, 2, 0, 0, 1, 0] = [0, 1, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_0021212 : fieldMul 7 5 20 [0, 1, 1, 1, 1, 1, 1] [0, 0, 2, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021212 : mirrorTrits [0, 1, 1, 1, 1, 1, 1] = [0, 2, 2, 2, 2, 2, 2] := by
  decide

theorem demoInv_0021212 : specInv 7 5 20 [0, 0, 2, 1, 2, 1, 2] = some [0, 2, 2, 2, 2, 2, 2] :=
  specInv_mirror_7 [0, 0, 2, 1, 2, 1, 2] [0, 1, 2, 1, 1, 0, 0] [2, 1, 2, 0, 0, 1, 0] [0, 1, 1, 1, 1, 1, 1] [0, 2, 2, 2, 2, 2, 2] demoR1_0021212 demoR2_0021212 demoC_0021212 demoM_0021212 demoMir_0021212

theorem demoR1_1021212 : invRung 7 5 20 [1, 0, 2, 1, 2, 1, 2] [1, 0, 2, 1, 2, 1, 2] 1 2 false = ([2, 2, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_1021212 : invRung 7 5 20 [1, 0, 2, 1, 2, 1, 2] [2, 2, 0, 0, 2, 1, 1] 3 1 true = ([2, 1, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_1021212 : fieldCube 7 5 20 [2, 1, 2, 2, 0, 0, 0] = [1, 0, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_1021212 : fieldMul 7 5 20 [1, 0, 2, 1, 0, 2, 2] [1, 0, 2, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021212 : mirrorTrits [1, 0, 2, 1, 0, 2, 2] = [2, 0, 1, 2, 0, 1, 1] := by
  decide

theorem demoInv_1021212 : specInv 7 5 20 [1, 0, 2, 1, 2, 1, 2] = some [2, 0, 1, 2, 0, 1, 1] :=
  specInv_mirror_7 [1, 0, 2, 1, 2, 1, 2] [2, 2, 0, 0, 2, 1, 1] [2, 1, 2, 2, 0, 0, 0] [1, 0, 2, 1, 0, 2, 2] [2, 0, 1, 2, 0, 1, 1] demoR1_1021212 demoR2_1021212 demoC_1021212 demoM_1021212 demoMir_1021212

theorem demoR1_2021212 : invRung 7 5 20 [2, 0, 2, 1, 2, 1, 2] [2, 0, 2, 1, 2, 1, 2] 1 2 false = ([2, 2, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2021212 : invRung 7 5 20 [2, 0, 2, 1, 2, 1, 2] [2, 2, 0, 2, 2, 1, 2] 3 1 true = ([0, 2, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_2021212 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 1, 2] = [0, 1, 1, 2, 0, 0, 0] := by
  decide

theorem demoM_2021212 : fieldMul 7 5 20 [0, 1, 1, 2, 0, 0, 0] [2, 0, 2, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021212 : mirrorTrits [0, 1, 1, 2, 0, 0, 0] = [0, 2, 2, 1, 0, 0, 0] := by
  decide

theorem demoInv_2021212 : specInv 7 5 20 [2, 0, 2, 1, 2, 1, 2] = some [0, 2, 2, 1, 0, 0, 0] :=
  specInv_mirror_7 [2, 0, 2, 1, 2, 1, 2] [2, 2, 0, 2, 2, 1, 2] [0, 2, 1, 2, 1, 1, 2] [0, 1, 1, 2, 0, 0, 0] [0, 2, 2, 1, 0, 0, 0] demoR1_2021212 demoR2_2021212 demoC_2021212 demoM_2021212 demoMir_2021212

theorem demoR1_0121212 : invRung 7 5 20 [0, 1, 2, 1, 2, 1, 2] [0, 1, 2, 1, 2, 1, 2] 1 2 false = ([2, 1, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_0121212 : invRung 7 5 20 [0, 1, 2, 1, 2, 1, 2] [2, 1, 1, 2, 2, 0, 0] 3 1 true = ([2, 1, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0121212 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 2, 2] = [2, 2, 1, 1, 1, 0, 0] := by
  decide

theorem demoM_0121212 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 0, 0] [0, 1, 2, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0121212 : mirrorTrits [2, 2, 1, 1, 1, 0, 0] = [1, 1, 2, 2, 2, 0, 0] := by
  decide

theorem demoInv_0121212 : specInv 7 5 20 [0, 1, 2, 1, 2, 1, 2] = some [1, 1, 2, 2, 2, 0, 0] :=
  specInv_mirror_7 [0, 1, 2, 1, 2, 1, 2] [2, 1, 1, 2, 2, 0, 0] [2, 1, 2, 1, 1, 2, 2] [2, 2, 1, 1, 1, 0, 0] [1, 1, 2, 2, 2, 0, 0] demoR1_0121212 demoR2_0121212 demoC_0121212 demoM_0121212 demoMir_0121212

theorem demoR1_1121212 : invRung 7 5 20 [1, 1, 2, 1, 2, 1, 2] [1, 1, 2, 1, 2, 1, 2] 1 2 false = ([1, 2, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_1121212 : invRung 7 5 20 [1, 1, 2, 1, 2, 1, 2] [1, 2, 0, 2, 1, 2, 0] 3 1 true = ([1, 1, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_1121212 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 2, 0] = [0, 1, 2, 0, 2, 1, 0] := by
  decide

theorem demoM_1121212 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 1, 0] [1, 1, 2, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121212 : mirrorTrits [0, 1, 2, 0, 2, 1, 0] = [0, 2, 1, 0, 1, 2, 0] := by
  decide

theorem demoInv_1121212 : specInv 7 5 20 [1, 1, 2, 1, 2, 1, 2] = some [0, 2, 1, 0, 1, 2, 0] :=
  specInv_mirror_7 [1, 1, 2, 1, 2, 1, 2] [1, 2, 0, 2, 1, 2, 0] [1, 1, 0, 0, 2, 2, 0] [0, 1, 2, 0, 2, 1, 0] [0, 2, 1, 0, 1, 2, 0] demoR1_1121212 demoR2_1121212 demoC_1121212 demoM_1121212 demoMir_1121212

theorem demoR1_2121212 : invRung 7 5 20 [2, 1, 2, 1, 2, 1, 2] [2, 1, 2, 1, 2, 1, 2] 1 2 false = ([0, 1, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_2121212 : invRung 7 5 20 [2, 1, 2, 1, 2, 1, 2] [0, 1, 0, 1, 2, 2, 0] 3 1 true = ([2, 2, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2121212 : fieldCube 7 5 20 [2, 2, 2, 1, 0, 1, 1] = [1, 2, 1, 0, 2, 0, 2] := by
  decide

theorem demoM_2121212 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 0, 2] [2, 1, 2, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2121212 : mirrorTrits [1, 2, 1, 0, 2, 0, 2] = [2, 1, 2, 0, 1, 0, 1] := by
  decide

theorem demoInv_2121212 : specInv 7 5 20 [2, 1, 2, 1, 2, 1, 2] = some [2, 1, 2, 0, 1, 0, 1] :=
  specInv_mirror_7 [2, 1, 2, 1, 2, 1, 2] [0, 1, 0, 1, 2, 2, 0] [2, 2, 2, 1, 0, 1, 1] [1, 2, 1, 0, 2, 0, 2] [2, 1, 2, 0, 1, 0, 1] demoR1_2121212 demoR2_2121212 demoC_2121212 demoM_2121212 demoMir_2121212

theorem demoR1_0221212 : invRung 7 5 20 [0, 2, 2, 1, 2, 1, 2] [0, 2, 2, 1, 2, 1, 2] 1 2 false = ([0, 2, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_0221212 : invRung 7 5 20 [0, 2, 2, 1, 2, 1, 2] [0, 2, 2, 2, 2, 1, 2] 3 1 true = ([1, 0, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0221212 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 0, 2] = [0, 1, 0, 1, 2, 0, 0] := by
  decide

theorem demoM_0221212 : fieldMul 7 5 20 [0, 1, 0, 1, 2, 0, 0] [0, 2, 2, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0221212 : specInv 7 5 20 [0, 2, 2, 1, 2, 1, 2] = some [0, 1, 0, 1, 2, 0, 0] :=
  specInv_white_7 [0, 2, 2, 1, 2, 1, 2] [0, 2, 2, 2, 2, 1, 2] [1, 0, 2, 2, 2, 0, 2] [0, 1, 0, 1, 2, 0, 0] demoR1_0221212 demoR2_0221212 demoC_0221212 demoM_0221212

theorem demoR1_1221212 : invRung 7 5 20 [1, 2, 2, 1, 2, 1, 2] [1, 2, 2, 1, 2, 1, 2] 1 2 false = ([2, 1, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1221212 : invRung 7 5 20 [1, 2, 2, 1, 2, 1, 2] [2, 1, 2, 1, 1, 0, 2] 3 1 true = ([1, 0, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_1221212 : fieldCube 7 5 20 [1, 0, 1, 0, 2, 1, 1] = [2, 1, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_1221212 : fieldMul 7 5 20 [2, 1, 0, 0, 2, 1, 0] [1, 2, 2, 1, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221212 : mirrorTrits [2, 1, 0, 0, 2, 1, 0] = [1, 2, 0, 0, 1, 2, 0] := by
  decide

theorem demoInv_1221212 : specInv 7 5 20 [1, 2, 2, 1, 2, 1, 2] = some [1, 2, 0, 0, 1, 2, 0] :=
  specInv_mirror_7 [1, 2, 2, 1, 2, 1, 2] [2, 1, 2, 1, 1, 0, 2] [1, 0, 1, 0, 2, 1, 1] [2, 1, 0, 0, 2, 1, 0] [1, 2, 0, 0, 1, 2, 0] demoR1_1221212 demoR2_1221212 demoC_1221212 demoM_1221212 demoMir_1221212

theorem demoR1_2221212 : invRung 7 5 20 [2, 2, 2, 1, 2, 1, 2] [2, 2, 2, 1, 2, 1, 2] 1 2 false = ([0, 0, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_2221212 : invRung 7 5 20 [2, 2, 2, 1, 2, 1, 2] [0, 0, 2, 1, 2, 2, 2] 3 1 true = ([1, 1, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_2221212 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 2, 0] = [0, 2, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_2221212 : fieldMul 7 5 20 [0, 2, 2, 1, 2, 2, 2] [2, 2, 2, 1, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2221212 : specInv 7 5 20 [2, 2, 2, 1, 2, 1, 2] = some [0, 2, 2, 1, 2, 2, 2] :=
  specInv_white_7 [2, 2, 2, 1, 2, 1, 2] [0, 0, 2, 1, 2, 2, 2] [1, 1, 1, 0, 0, 2, 0] [0, 2, 2, 1, 2, 2, 2] demoR1_2221212 demoR2_2221212 demoC_2221212 demoM_2221212

theorem demoR1_0002212 : invRung 7 5 20 [0, 0, 0, 2, 2, 1, 2] [0, 0, 0, 2, 2, 1, 2] 1 2 false = ([0, 1, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_0002212 : invRung 7 5 20 [0, 0, 0, 2, 2, 1, 2] [0, 1, 0, 0, 2, 1, 0] 3 1 true = ([0, 1, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_0002212 : fieldCube 7 5 20 [0, 1, 1, 2, 2, 1, 0] = [0, 0, 0, 0, 1, 2, 2] := by
  decide

theorem demoM_0002212 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 2, 2] [0, 0, 0, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002212 : mirrorTrits [0, 0, 0, 0, 1, 2, 2] = [0, 0, 0, 0, 2, 1, 1] := by
  decide

theorem demoInv_0002212 : specInv 7 5 20 [0, 0, 0, 2, 2, 1, 2] = some [0, 0, 0, 0, 2, 1, 1] :=
  specInv_mirror_7 [0, 0, 0, 2, 2, 1, 2] [0, 1, 0, 0, 2, 1, 0] [0, 1, 1, 2, 2, 1, 0] [0, 0, 0, 0, 1, 2, 2] [0, 0, 0, 0, 2, 1, 1] demoR1_0002212 demoR2_0002212 demoC_0002212 demoM_0002212 demoMir_0002212

theorem demoR1_1002212 : invRung 7 5 20 [1, 0, 0, 2, 2, 1, 2] [1, 0, 0, 2, 2, 1, 2] 1 2 false = ([0, 0, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_1002212 : invRung 7 5 20 [1, 0, 0, 2, 2, 1, 2] [0, 0, 0, 2, 1, 0, 0] 3 1 true = ([0, 2, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1002212 : fieldCube 7 5 20 [0, 2, 0, 1, 1, 2, 1] = [0, 1, 2, 1, 0, 2, 0] := by
  decide

theorem demoM_1002212 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 2, 0] [1, 0, 0, 2, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1002212 : specInv 7 5 20 [1, 0, 0, 2, 2, 1, 2] = some [0, 1, 2, 1, 0, 2, 0] :=
  specInv_white_7 [1, 0, 0, 2, 2, 1, 2] [0, 0, 0, 2, 1, 0, 0] [0, 2, 0, 1, 1, 2, 1] [0, 1, 2, 1, 0, 2, 0] demoR1_1002212 demoR2_1002212 demoC_1002212 demoM_1002212

theorem demoR1_2002212 : invRung 7 5 20 [2, 0, 0, 2, 2, 1, 2] [2, 0, 0, 2, 2, 1, 2] 1 2 false = ([1, 2, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_2002212 : invRung 7 5 20 [2, 0, 0, 2, 2, 1, 2] [1, 2, 0, 2, 0, 1, 1] 3 1 true = ([0, 2, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_2002212 : fieldCube 7 5 20 [0, 2, 0, 1, 2, 0, 1] = [1, 0, 0, 2, 1, 1, 0] := by
  decide

theorem demoM_2002212 : fieldMul 7 5 20 [1, 0, 0, 2, 1, 1, 0] [2, 0, 0, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002212 : mirrorTrits [1, 0, 0, 2, 1, 1, 0] = [2, 0, 0, 1, 2, 2, 0] := by
  decide

theorem demoInv_2002212 : specInv 7 5 20 [2, 0, 0, 2, 2, 1, 2] = some [2, 0, 0, 1, 2, 2, 0] :=
  specInv_mirror_7 [2, 0, 0, 2, 2, 1, 2] [1, 2, 0, 2, 0, 1, 1] [0, 2, 0, 1, 2, 0, 1] [1, 0, 0, 2, 1, 1, 0] [2, 0, 0, 1, 2, 2, 0] demoR1_2002212 demoR2_2002212 demoC_2002212 demoM_2002212 demoMir_2002212

theorem demoR1_0102212 : invRung 7 5 20 [0, 1, 0, 2, 2, 1, 2] [0, 1, 0, 2, 2, 1, 2] 1 2 false = ([2, 0, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_0102212 : invRung 7 5 20 [0, 1, 0, 2, 2, 1, 2] [2, 0, 2, 0, 0, 1, 2] 3 1 true = ([0, 0, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0102212 : fieldCube 7 5 20 [0, 0, 2, 1, 0, 0, 1] = [1, 1, 0, 1, 1, 2, 0] := by
  decide

theorem demoM_0102212 : fieldMul 7 5 20 [1, 1, 0, 1, 1, 2, 0] [0, 1, 0, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102212 : mirrorTrits [1, 1, 0, 1, 1, 2, 0] = [2, 2, 0, 2, 2, 1, 0] := by
  decide

theorem demoInv_0102212 : specInv 7 5 20 [0, 1, 0, 2, 2, 1, 2] = some [2, 2, 0, 2, 2, 1, 0] :=
  specInv_mirror_7 [0, 1, 0, 2, 2, 1, 2] [2, 0, 2, 0, 0, 1, 2] [0, 0, 2, 1, 0, 0, 1] [1, 1, 0, 1, 1, 2, 0] [2, 2, 0, 2, 2, 1, 0] demoR1_0102212 demoR2_0102212 demoC_0102212 demoM_0102212 demoMir_0102212

theorem demoR1_1102212 : invRung 7 5 20 [1, 1, 0, 2, 2, 1, 2] [1, 1, 0, 2, 2, 1, 2] 1 2 false = ([0, 1, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_1102212 : invRung 7 5 20 [1, 1, 0, 2, 2, 1, 2] [0, 1, 1, 2, 0, 1, 0] 3 1 true = ([2, 1, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_1102212 : fieldCube 7 5 20 [2, 1, 2, 0, 2, 0, 2] = [2, 1, 1, 2, 2, 1, 0] := by
  decide

theorem demoM_1102212 : fieldMul 7 5 20 [2, 1, 1, 2, 2, 1, 0] [1, 1, 0, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102212 : mirrorTrits [2, 1, 1, 2, 2, 1, 0] = [1, 2, 2, 1, 1, 2, 0] := by
  decide

theorem demoInv_1102212 : specInv 7 5 20 [1, 1, 0, 2, 2, 1, 2] = some [1, 2, 2, 1, 1, 2, 0] :=
  specInv_mirror_7 [1, 1, 0, 2, 2, 1, 2] [0, 1, 1, 2, 0, 1, 0] [2, 1, 2, 0, 2, 0, 2] [2, 1, 1, 2, 2, 1, 0] [1, 2, 2, 1, 1, 2, 0] demoR1_1102212 demoR2_1102212 demoC_1102212 demoM_1102212 demoMir_1102212

theorem demoR1_2102212 : invRung 7 5 20 [2, 1, 0, 2, 2, 1, 2] [2, 1, 0, 2, 2, 1, 2] 1 2 false = ([1, 1, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_2102212 : invRung 7 5 20 [2, 1, 0, 2, 2, 1, 2] [1, 1, 2, 1, 0, 2, 2] 3 1 true = ([2, 2, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2102212 : fieldCube 7 5 20 [2, 2, 0, 2, 0, 1, 0] = [2, 1, 0, 2, 1, 0, 2] := by
  decide

theorem demoM_2102212 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 0, 2] [2, 1, 0, 2, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2102212 : specInv 7 5 20 [2, 1, 0, 2, 2, 1, 2] = some [2, 1, 0, 2, 1, 0, 2] :=
  specInv_white_7 [2, 1, 0, 2, 2, 1, 2] [1, 1, 2, 1, 0, 2, 2] [2, 2, 0, 2, 0, 1, 0] [2, 1, 0, 2, 1, 0, 2] demoR1_2102212 demoR2_2102212 demoC_2102212 demoM_2102212

theorem demoR1_0202212 : invRung 7 5 20 [0, 2, 0, 2, 2, 1, 2] [0, 2, 0, 2, 2, 1, 2] 1 2 false = ([1, 0, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_0202212 : invRung 7 5 20 [0, 2, 0, 2, 2, 1, 2] [1, 0, 1, 0, 2, 1, 1] 3 1 true = ([1, 2, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0202212 : fieldCube 7 5 20 [1, 2, 2, 1, 2, 0, 1] = [2, 0, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_0202212 : fieldMul 7 5 20 [2, 0, 0, 2, 1, 1, 2] [0, 2, 0, 2, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0202212 : specInv 7 5 20 [0, 2, 0, 2, 2, 1, 2] = some [2, 0, 0, 2, 1, 1, 2] :=
  specInv_white_7 [0, 2, 0, 2, 2, 1, 2] [1, 0, 1, 0, 2, 1, 1] [1, 2, 2, 1, 2, 0, 1] [2, 0, 0, 2, 1, 1, 2] demoR1_0202212 demoR2_0202212 demoC_0202212 demoM_0202212

theorem demoR1_1202212 : invRung 7 5 20 [1, 2, 0, 2, 2, 1, 2] [1, 2, 0, 2, 2, 1, 2] 1 2 false = ([0, 1, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_1202212 : invRung 7 5 20 [1, 2, 0, 2, 2, 1, 2] [0, 1, 2, 0, 2, 1, 1] 3 1 true = ([1, 1, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_1202212 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 0, 0] = [1, 2, 0, 0, 0, 2, 2] := by
  decide

theorem demoM_1202212 : fieldMul 7 5 20 [1, 2, 0, 0, 0, 2, 2] [1, 2, 0, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202212 : mirrorTrits [1, 2, 0, 0, 0, 2, 2] = [2, 1, 0, 0, 0, 1, 1] := by
  decide

theorem demoInv_1202212 : specInv 7 5 20 [1, 2, 0, 2, 2, 1, 2] = some [2, 1, 0, 0, 0, 1, 1] :=
  specInv_mirror_7 [1, 2, 0, 2, 2, 1, 2] [0, 1, 2, 0, 2, 1, 1] [1, 1, 0, 0, 2, 0, 0] [1, 2, 0, 0, 0, 2, 2] [2, 1, 0, 0, 0, 1, 1] demoR1_1202212 demoR2_1202212 demoC_1202212 demoM_1202212 demoMir_1202212

theorem demoR1_2202212 : invRung 7 5 20 [2, 2, 0, 2, 2, 1, 2] [2, 2, 0, 2, 2, 1, 2] 1 2 false = ([1, 0, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2202212 : invRung 7 5 20 [2, 2, 0, 2, 2, 1, 2] [1, 0, 1, 2, 2, 1, 2] 3 1 true = ([1, 0, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_2202212 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 0, 1] = [0, 2, 1, 2, 1, 1, 0] := by
  decide

theorem demoM_2202212 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 1, 0] [2, 2, 0, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202212 : mirrorTrits [0, 2, 1, 2, 1, 1, 0] = [0, 1, 2, 1, 2, 2, 0] := by
  decide

theorem demoInv_2202212 : specInv 7 5 20 [2, 2, 0, 2, 2, 1, 2] = some [0, 1, 2, 1, 2, 2, 0] :=
  specInv_mirror_7 [2, 2, 0, 2, 2, 1, 2] [1, 0, 1, 2, 2, 1, 2] [1, 0, 1, 2, 1, 0, 1] [0, 2, 1, 2, 1, 1, 0] [0, 1, 2, 1, 2, 2, 0] demoR1_2202212 demoR2_2202212 demoC_2202212 demoM_2202212 demoMir_2202212

theorem demoR1_0012212 : invRung 7 5 20 [0, 0, 1, 2, 2, 1, 2] [0, 0, 1, 2, 2, 1, 2] 1 2 false = ([0, 1, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_0012212 : invRung 7 5 20 [0, 0, 1, 2, 2, 1, 2] [0, 1, 1, 0, 0, 2, 2] 3 1 true = ([0, 0, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_0012212 : fieldCube 7 5 20 [0, 0, 2, 1, 2, 1, 1] = [2, 1, 1, 0, 2, 2, 1] := by
  decide

theorem demoM_0012212 : fieldMul 7 5 20 [2, 1, 1, 0, 2, 2, 1] [0, 0, 1, 2, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0012212 : specInv 7 5 20 [0, 0, 1, 2, 2, 1, 2] = some [2, 1, 1, 0, 2, 2, 1] :=
  specInv_white_7 [0, 0, 1, 2, 2, 1, 2] [0, 1, 1, 0, 0, 2, 2] [0, 0, 2, 1, 2, 1, 1] [2, 1, 1, 0, 2, 2, 1] demoR1_0012212 demoR2_0012212 demoC_0012212 demoM_0012212

theorem demoR1_1012212 : invRung 7 5 20 [1, 0, 1, 2, 2, 1, 2] [1, 0, 1, 2, 2, 1, 2] 1 2 false = ([0, 1, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_1012212 : invRung 7 5 20 [1, 0, 1, 2, 2, 1, 2] [0, 1, 0, 0, 2, 1, 2] 3 1 true = ([2, 2, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_1012212 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 0, 0] = [2, 2, 0, 1, 0, 2, 0] := by
  decide

theorem demoM_1012212 : fieldMul 7 5 20 [2, 2, 0, 1, 0, 2, 0] [1, 0, 1, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1012212 : mirrorTrits [2, 2, 0, 1, 0, 2, 0] = [1, 1, 0, 2, 0, 1, 0] := by
  decide

theorem demoInv_1012212 : specInv 7 5 20 [1, 0, 1, 2, 2, 1, 2] = some [1, 1, 0, 2, 0, 1, 0] :=
  specInv_mirror_7 [1, 0, 1, 2, 2, 1, 2] [0, 1, 0, 0, 2, 1, 2] [2, 2, 1, 0, 2, 0, 0] [2, 2, 0, 1, 0, 2, 0] [1, 1, 0, 2, 0, 1, 0] demoR1_1012212 demoR2_1012212 demoC_1012212 demoM_1012212 demoMir_1012212

theorem demoR1_2012212 : invRung 7 5 20 [2, 0, 1, 2, 2, 1, 2] [2, 0, 1, 2, 2, 1, 2] 1 2 false = ([1, 0, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_2012212 : invRung 7 5 20 [2, 0, 1, 2, 2, 1, 2] [1, 0, 2, 0, 0, 1, 1] 3 1 true = ([0, 1, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_2012212 : fieldCube 7 5 20 [0, 1, 0, 0, 2, 1, 1] = [1, 1, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_2012212 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 1, 2] [2, 0, 1, 2, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2012212 : specInv 7 5 20 [2, 0, 1, 2, 2, 1, 2] = some [1, 1, 0, 1, 2, 1, 2] :=
  specInv_white_7 [2, 0, 1, 2, 2, 1, 2] [1, 0, 2, 0, 0, 1, 1] [0, 1, 0, 0, 2, 1, 1] [1, 1, 0, 1, 2, 1, 2] demoR1_2012212 demoR2_2012212 demoC_2012212 demoM_2012212

theorem demoR1_0112212 : invRung 7 5 20 [0, 1, 1, 2, 2, 1, 2] [0, 1, 1, 2, 2, 1, 2] 1 2 false = ([0, 1, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_0112212 : invRung 7 5 20 [0, 1, 1, 2, 2, 1, 2] [0, 1, 2, 2, 1, 1, 2] 3 1 true = ([0, 0, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0112212 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 1, 2] = [2, 2, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_0112212 : fieldMul 7 5 20 [2, 2, 0, 1, 0, 0, 0] [0, 1, 1, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112212 : mirrorTrits [2, 2, 0, 1, 0, 0, 0] = [1, 1, 0, 2, 0, 0, 0] := by
  decide

theorem demoInv_0112212 : specInv 7 5 20 [0, 1, 1, 2, 2, 1, 2] = some [1, 1, 0, 2, 0, 0, 0] :=
  specInv_mirror_7 [0, 1, 1, 2, 2, 1, 2] [0, 1, 2, 2, 1, 1, 2] [0, 0, 0, 1, 2, 1, 2] [2, 2, 0, 1, 0, 0, 0] [1, 1, 0, 2, 0, 0, 0] demoR1_0112212 demoR2_0112212 demoC_0112212 demoM_0112212 demoMir_0112212

theorem demoR1_1112212 : invRung 7 5 20 [1, 1, 1, 2, 2, 1, 2] [1, 1, 1, 2, 2, 1, 2] 1 2 false = ([1, 2, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_1112212 : invRung 7 5 20 [1, 1, 1, 2, 2, 1, 2] [1, 2, 1, 1, 2, 2, 2] 3 1 true = ([0, 1, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1112212 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 2, 0] = [0, 2, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_1112212 : fieldMul 7 5 20 [0, 2, 0, 1, 2, 0, 2] [1, 1, 1, 2, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1112212 : specInv 7 5 20 [1, 1, 1, 2, 2, 1, 2] = some [0, 2, 0, 1, 2, 0, 2] :=
  specInv_white_7 [1, 1, 1, 2, 2, 1, 2] [1, 2, 1, 1, 2, 2, 2] [0, 1, 1, 1, 0, 2, 0] [0, 2, 0, 1, 2, 0, 2] demoR1_1112212 demoR2_1112212 demoC_1112212 demoM_1112212

theorem demoR1_2112212 : invRung 7 5 20 [2, 1, 1, 2, 2, 1, 2] [2, 1, 1, 2, 2, 1, 2] 1 2 false = ([2, 1, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2112212 : invRung 7 5 20 [2, 1, 1, 2, 2, 1, 2] [2, 1, 2, 2, 2, 0, 1] 3 1 true = ([0, 1, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2112212 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 1, 1] = [1, 0, 0, 0, 2, 0, 0] := by
  decide

theorem demoM_2112212 : fieldMul 7 5 20 [1, 0, 0, 0, 2, 0, 0] [2, 1, 1, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112212 : mirrorTrits [1, 0, 0, 0, 2, 0, 0] = [2, 0, 0, 0, 1, 0, 0] := by
  decide

theorem demoInv_2112212 : specInv 7 5 20 [2, 1, 1, 2, 2, 1, 2] = some [2, 0, 0, 0, 1, 0, 0] :=
  specInv_mirror_7 [2, 1, 1, 2, 2, 1, 2] [2, 1, 2, 2, 2, 0, 1] [0, 1, 2, 0, 1, 1, 1] [1, 0, 0, 0, 2, 0, 0] [2, 0, 0, 0, 1, 0, 0] demoR1_2112212 demoR2_2112212 demoC_2112212 demoM_2112212 demoMir_2112212

theorem demoR1_0212212 : invRung 7 5 20 [0, 2, 1, 2, 2, 1, 2] [0, 2, 1, 2, 2, 1, 2] 1 2 false = ([1, 1, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_0212212 : invRung 7 5 20 [0, 2, 1, 2, 2, 1, 2] [1, 1, 1, 1, 0, 1, 2] 3 1 true = ([1, 0, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0212212 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 1, 2] = [1, 1, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_0212212 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 0, 1] [0, 2, 1, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212212 : mirrorTrits [1, 1, 1, 0, 0, 0, 1] = [2, 2, 2, 0, 0, 0, 2] := by
  decide

theorem demoInv_0212212 : specInv 7 5 20 [0, 2, 1, 2, 2, 1, 2] = some [2, 2, 2, 0, 0, 0, 2] :=
  specInv_mirror_7 [0, 2, 1, 2, 2, 1, 2] [1, 1, 1, 1, 0, 1, 2] [1, 0, 2, 2, 1, 1, 2] [1, 1, 1, 0, 0, 0, 1] [2, 2, 2, 0, 0, 0, 2] demoR1_0212212 demoR2_0212212 demoC_0212212 demoM_0212212 demoMir_0212212

theorem demoR1_1212212 : invRung 7 5 20 [1, 2, 1, 2, 2, 1, 2] [1, 2, 1, 2, 2, 1, 2] 1 2 false = ([0, 1, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_1212212 : invRung 7 5 20 [1, 2, 1, 2, 2, 1, 2] [0, 1, 0, 0, 2, 0, 0] 3 1 true = ([1, 0, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_1212212 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 0, 0] = [0, 1, 2, 1, 0, 0, 0] := by
  decide

theorem demoM_1212212 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 0, 0] [1, 2, 1, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212212 : mirrorTrits [0, 1, 2, 1, 0, 0, 0] = [0, 2, 1, 2, 0, 0, 0] := by
  decide

theorem demoInv_1212212 : specInv 7 5 20 [1, 2, 1, 2, 2, 1, 2] = some [0, 2, 1, 2, 0, 0, 0] :=
  specInv_mirror_7 [1, 2, 1, 2, 2, 1, 2] [0, 1, 0, 0, 2, 0, 0] [1, 0, 2, 2, 1, 0, 0] [0, 1, 2, 1, 0, 0, 0] [0, 2, 1, 2, 0, 0, 0] demoR1_1212212 demoR2_1212212 demoC_1212212 demoM_1212212 demoMir_1212212

theorem demoR1_2212212 : invRung 7 5 20 [2, 2, 1, 2, 2, 1, 2] [2, 2, 1, 2, 2, 1, 2] 1 2 false = ([1, 1, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2212212 : invRung 7 5 20 [2, 2, 1, 2, 2, 1, 2] [1, 1, 0, 0, 0, 1, 0] 3 1 true = ([2, 1, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_2212212 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 1, 1] = [1, 0, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_2212212 : fieldMul 7 5 20 [1, 0, 1, 0, 2, 1, 0] [2, 2, 1, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212212 : mirrorTrits [1, 0, 1, 0, 2, 1, 0] = [2, 0, 2, 0, 1, 2, 0] := by
  decide

theorem demoInv_2212212 : specInv 7 5 20 [2, 2, 1, 2, 2, 1, 2] = some [2, 0, 2, 0, 1, 2, 0] :=
  specInv_mirror_7 [2, 2, 1, 2, 2, 1, 2] [1, 1, 0, 0, 0, 1, 0] [2, 1, 2, 1, 1, 1, 1] [1, 0, 1, 0, 2, 1, 0] [2, 0, 2, 0, 1, 2, 0] demoR1_2212212 demoR2_2212212 demoC_2212212 demoM_2212212 demoMir_2212212

theorem demoR1_0022212 : invRung 7 5 20 [0, 0, 2, 2, 2, 1, 2] [0, 0, 2, 2, 2, 1, 2] 1 2 false = ([1, 0, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_0022212 : invRung 7 5 20 [0, 0, 2, 2, 2, 1, 2] [1, 0, 0, 1, 2, 1, 1] 3 1 true = ([0, 1, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_0022212 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 2, 2] = [1, 2, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_0022212 : fieldMul 7 5 20 [1, 2, 2, 1, 1, 1, 0] [0, 0, 2, 2, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0022212 : specInv 7 5 20 [0, 0, 2, 2, 2, 1, 2] = some [1, 2, 2, 1, 1, 1, 0] :=
  specInv_white_7 [0, 0, 2, 2, 2, 1, 2] [1, 0, 0, 1, 2, 1, 1] [0, 1, 2, 2, 1, 2, 2] [1, 2, 2, 1, 1, 1, 0] demoR1_0022212 demoR2_0022212 demoC_0022212 demoM_0022212

theorem demoR1_1022212 : invRung 7 5 20 [1, 0, 2, 2, 2, 1, 2] [1, 0, 2, 2, 2, 1, 2] 1 2 false = ([0, 1, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_1022212 : invRung 7 5 20 [1, 0, 2, 2, 2, 1, 2] [0, 1, 2, 2, 1, 0, 0] 3 1 true = ([1, 0, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_1022212 : fieldCube 7 5 20 [1, 0, 0, 1, 1, 0, 2] = [2, 0, 2, 0, 2, 1, 0] := by
  decide

theorem demoM_1022212 : fieldMul 7 5 20 [2, 0, 2, 0, 2, 1, 0] [1, 0, 2, 2, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1022212 : specInv 7 5 20 [1, 0, 2, 2, 2, 1, 2] = some [2, 0, 2, 0, 2, 1, 0] :=
  specInv_white_7 [1, 0, 2, 2, 2, 1, 2] [0, 1, 2, 2, 1, 0, 0] [1, 0, 0, 1, 1, 0, 2] [2, 0, 2, 0, 2, 1, 0] demoR1_1022212 demoR2_1022212 demoC_1022212 demoM_1022212

theorem demoR1_2022212 : invRung 7 5 20 [2, 0, 2, 2, 2, 1, 2] [2, 0, 2, 2, 2, 1, 2] 1 2 false = ([0, 0, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_2022212 : invRung 7 5 20 [2, 0, 2, 2, 2, 1, 2] [0, 0, 1, 2, 1, 2, 2] 3 1 true = ([1, 2, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_2022212 : fieldCube 7 5 20 [1, 2, 0, 0, 2, 2, 0] = [0, 1, 2, 1, 2, 1, 0] := by
  decide

theorem demoM_2022212 : fieldMul 7 5 20 [0, 1, 2, 1, 2, 1, 0] [2, 0, 2, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022212 : mirrorTrits [0, 1, 2, 1, 2, 1, 0] = [0, 2, 1, 2, 1, 2, 0] := by
  decide

theorem demoInv_2022212 : specInv 7 5 20 [2, 0, 2, 2, 2, 1, 2] = some [0, 2, 1, 2, 1, 2, 0] :=
  specInv_mirror_7 [2, 0, 2, 2, 2, 1, 2] [0, 0, 1, 2, 1, 2, 2] [1, 2, 0, 0, 2, 2, 0] [0, 1, 2, 1, 2, 1, 0] [0, 2, 1, 2, 1, 2, 0] demoR1_2022212 demoR2_2022212 demoC_2022212 demoM_2022212 demoMir_2022212

theorem demoR1_0122212 : invRung 7 5 20 [0, 1, 2, 2, 2, 1, 2] [0, 1, 2, 2, 2, 1, 2] 1 2 false = ([2, 0, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_0122212 : invRung 7 5 20 [0, 1, 2, 2, 2, 1, 2] [2, 0, 2, 1, 2, 1, 1] 3 1 true = ([1, 1, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_0122212 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 2, 1] = [1, 2, 2, 1, 0, 0, 1] := by
  decide

theorem demoM_0122212 : fieldMul 7 5 20 [1, 2, 2, 1, 0, 0, 1] [0, 1, 2, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122212 : mirrorTrits [1, 2, 2, 1, 0, 0, 1] = [2, 1, 1, 2, 0, 0, 2] := by
  decide

theorem demoInv_0122212 : specInv 7 5 20 [0, 1, 2, 2, 2, 1, 2] = some [2, 1, 1, 2, 0, 0, 2] :=
  specInv_mirror_7 [0, 1, 2, 2, 2, 1, 2] [2, 0, 2, 1, 2, 1, 1] [1, 1, 0, 1, 2, 2, 1] [1, 2, 2, 1, 0, 0, 1] [2, 1, 1, 2, 0, 0, 2] demoR1_0122212 demoR2_0122212 demoC_0122212 demoM_0122212 demoMir_0122212

theorem demoR1_1122212 : invRung 7 5 20 [1, 1, 2, 2, 2, 1, 2] [1, 1, 2, 2, 2, 1, 2] 1 2 false = ([2, 1, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_1122212 : invRung 7 5 20 [1, 1, 2, 2, 2, 1, 2] [2, 1, 2, 0, 1, 0, 2] 3 1 true = ([0, 1, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_1122212 : fieldCube 7 5 20 [0, 1, 0, 1, 2, 0, 1] = [1, 0, 0, 1, 1, 1, 0] := by
  decide

theorem demoM_1122212 : fieldMul 7 5 20 [1, 0, 0, 1, 1, 1, 0] [1, 1, 2, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122212 : mirrorTrits [1, 0, 0, 1, 1, 1, 0] = [2, 0, 0, 2, 2, 2, 0] := by
  decide

theorem demoInv_1122212 : specInv 7 5 20 [1, 1, 2, 2, 2, 1, 2] = some [2, 0, 0, 2, 2, 2, 0] :=
  specInv_mirror_7 [1, 1, 2, 2, 2, 1, 2] [2, 1, 2, 0, 1, 0, 2] [0, 1, 0, 1, 2, 0, 1] [1, 0, 0, 1, 1, 1, 0] [2, 0, 0, 2, 2, 2, 0] demoR1_1122212 demoR2_1122212 demoC_1122212 demoM_1122212 demoMir_1122212

theorem demoR1_2122212 : invRung 7 5 20 [2, 1, 2, 2, 2, 1, 2] [2, 1, 2, 2, 2, 1, 2] 1 2 false = ([2, 2, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_2122212 : invRung 7 5 20 [2, 1, 2, 2, 2, 1, 2] [2, 2, 1, 0, 1, 1, 0] 3 1 true = ([1, 0, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_2122212 : fieldCube 7 5 20 [1, 0, 1, 0, 2, 2, 1] = [0, 2, 1, 0, 0, 2, 2] := by
  decide

theorem demoM_2122212 : fieldMul 7 5 20 [0, 2, 1, 0, 0, 2, 2] [2, 1, 2, 2, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2122212 : specInv 7 5 20 [2, 1, 2, 2, 2, 1, 2] = some [0, 2, 1, 0, 0, 2, 2] :=
  specInv_white_7 [2, 1, 2, 2, 2, 1, 2] [2, 2, 1, 0, 1, 1, 0] [1, 0, 1, 0, 2, 2, 1] [0, 2, 1, 0, 0, 2, 2] demoR1_2122212 demoR2_2122212 demoC_2122212 demoM_2122212

theorem demoR1_0222212 : invRung 7 5 20 [0, 2, 2, 2, 2, 1, 2] [0, 2, 2, 2, 2, 1, 2] 1 2 false = ([2, 2, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_0222212 : invRung 7 5 20 [0, 2, 2, 2, 2, 1, 2] [2, 2, 0, 1, 0, 0, 1] 3 1 true = ([1, 2, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_0222212 : fieldCube 7 5 20 [1, 2, 0, 2, 0, 0, 0] = [0, 0, 2, 2, 0, 2, 0] := by
  decide

theorem demoM_0222212 : fieldMul 7 5 20 [0, 0, 2, 2, 0, 2, 0] [0, 2, 2, 2, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0222212 : specInv 7 5 20 [0, 2, 2, 2, 2, 1, 2] = some [0, 0, 2, 2, 0, 2, 0] :=
  specInv_white_7 [0, 2, 2, 2, 2, 1, 2] [2, 2, 0, 1, 0, 0, 1] [1, 2, 0, 2, 0, 0, 0] [0, 0, 2, 2, 0, 2, 0] demoR1_0222212 demoR2_0222212 demoC_0222212 demoM_0222212

theorem demoR1_1222212 : invRung 7 5 20 [1, 2, 2, 2, 2, 1, 2] [1, 2, 2, 2, 2, 1, 2] 1 2 false = ([0, 1, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_1222212 : invRung 7 5 20 [1, 2, 2, 2, 2, 1, 2] [0, 1, 1, 2, 1, 1, 2] 3 1 true = ([0, 1, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_1222212 : fieldCube 7 5 20 [0, 1, 0, 1, 1, 0, 2] = [1, 0, 2, 1, 2, 1, 0] := by
  decide

theorem demoM_1222212 : fieldMul 7 5 20 [1, 0, 2, 1, 2, 1, 0] [1, 2, 2, 2, 2, 1, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1222212 : specInv 7 5 20 [1, 2, 2, 2, 2, 1, 2] = some [1, 0, 2, 1, 2, 1, 0] :=
  specInv_white_7 [1, 2, 2, 2, 2, 1, 2] [0, 1, 1, 2, 1, 1, 2] [0, 1, 0, 1, 1, 0, 2] [1, 0, 2, 1, 2, 1, 0] demoR1_1222212 demoR2_1222212 demoC_1222212 demoM_1222212

theorem demoR1_2222212 : invRung 7 5 20 [2, 2, 2, 2, 2, 1, 2] [2, 2, 2, 2, 2, 1, 2] 1 2 false = ([0, 2, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_2222212 : invRung 7 5 20 [2, 2, 2, 2, 2, 1, 2] [0, 2, 0, 0, 0, 0, 0] 3 1 true = ([0, 2, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2222212 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 1, 1] = [2, 2, 1, 0, 2, 0, 1] := by
  decide

theorem demoM_2222212 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 0, 1] [2, 2, 2, 2, 2, 1, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222212 : mirrorTrits [2, 2, 1, 0, 2, 0, 1] = [1, 1, 2, 0, 1, 0, 2] := by
  decide

theorem demoInv_2222212 : specInv 7 5 20 [2, 2, 2, 2, 2, 1, 2] = some [1, 1, 2, 0, 1, 0, 2] :=
  specInv_mirror_7 [2, 2, 2, 2, 2, 1, 2] [0, 2, 0, 0, 0, 0, 0] [0, 2, 1, 1, 0, 1, 1] [2, 2, 1, 0, 2, 0, 1] [1, 1, 2, 0, 1, 0, 2] demoR1_2222212 demoR2_2222212 demoC_2222212 demoM_2222212 demoMir_2222212

theorem demoR1_0000022 : invRung 7 5 20 [0, 0, 0, 0, 0, 2, 2] [0, 0, 0, 0, 0, 2, 2] 1 2 false = ([2, 2, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_0000022 : invRung 7 5 20 [0, 0, 0, 0, 0, 2, 2] [2, 2, 0, 0, 1, 0, 1] 3 1 true = ([1, 1, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0000022 : fieldCube 7 5 20 [1, 1, 0, 2, 1, 2, 1] = [2, 1, 0, 0, 0, 0, 0] := by
  decide

theorem demoM_0000022 : fieldMul 7 5 20 [2, 1, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000022 : mirrorTrits [2, 1, 0, 0, 0, 0, 0] = [1, 2, 0, 0, 0, 0, 0] := by
  decide

theorem demoInv_0000022 : specInv 7 5 20 [0, 0, 0, 0, 0, 2, 2] = some [1, 2, 0, 0, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 0, 0, 0, 2, 2] [2, 2, 0, 0, 1, 0, 1] [1, 1, 0, 2, 1, 2, 1] [2, 1, 0, 0, 0, 0, 0] [1, 2, 0, 0, 0, 0, 0] demoR1_0000022 demoR2_0000022 demoC_0000022 demoM_0000022 demoMir_0000022

theorem demoR1_1000022 : invRung 7 5 20 [1, 0, 0, 0, 0, 2, 2] [1, 0, 0, 0, 0, 2, 2] 1 2 false = ([0, 0, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1000022 : invRung 7 5 20 [1, 0, 0, 0, 0, 2, 2] [0, 0, 2, 0, 2, 2, 1] 3 1 true = ([0, 2, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_1000022 : fieldCube 7 5 20 [0, 2, 2, 2, 0, 2, 1] = [1, 0, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_1000022 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 2, 1] [1, 0, 0, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1000022 : specInv 7 5 20 [1, 0, 0, 0, 0, 2, 2] = some [1, 0, 0, 0, 0, 2, 1] :=
  specInv_white_7 [1, 0, 0, 0, 0, 2, 2] [0, 0, 2, 0, 2, 2, 1] [0, 2, 2, 2, 0, 2, 1] [1, 0, 0, 0, 0, 2, 1] demoR1_1000022 demoR2_1000022 demoC_1000022 demoM_1000022

theorem demoR1_2000022 : invRung 7 5 20 [2, 0, 0, 0, 0, 2, 2] [2, 0, 0, 0, 0, 2, 2] 1 2 false = ([0, 1, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_2000022 : invRung 7 5 20 [2, 0, 0, 0, 0, 2, 2] [0, 1, 1, 2, 1, 0, 2] 3 1 true = ([2, 2, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_2000022 : fieldCube 7 5 20 [2, 2, 0, 0, 2, 2, 2] = [1, 0, 0, 0, 1, 0, 2] := by
  decide

theorem demoM_2000022 : fieldMul 7 5 20 [1, 0, 0, 0, 1, 0, 2] [2, 0, 0, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000022 : mirrorTrits [1, 0, 0, 0, 1, 0, 2] = [2, 0, 0, 0, 2, 0, 1] := by
  decide

theorem demoInv_2000022 : specInv 7 5 20 [2, 0, 0, 0, 0, 2, 2] = some [2, 0, 0, 0, 2, 0, 1] :=
  specInv_mirror_7 [2, 0, 0, 0, 0, 2, 2] [0, 1, 1, 2, 1, 0, 2] [2, 2, 0, 0, 2, 2, 2] [1, 0, 0, 0, 1, 0, 2] [2, 0, 0, 0, 2, 0, 1] demoR1_2000022 demoR2_2000022 demoC_2000022 demoM_2000022 demoMir_2000022

theorem demoR1_0100022 : invRung 7 5 20 [0, 1, 0, 0, 0, 2, 2] [0, 1, 0, 0, 0, 2, 2] 1 2 false = ([2, 1, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_0100022 : invRung 7 5 20 [0, 1, 0, 0, 0, 2, 2] [2, 1, 2, 1, 2, 2, 2] 3 1 true = ([0, 1, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_0100022 : fieldCube 7 5 20 [0, 1, 1, 2, 1, 2, 0] = [1, 0, 1, 2, 2, 2, 0] := by
  decide

theorem demoM_0100022 : fieldMul 7 5 20 [1, 0, 1, 2, 2, 2, 0] [0, 1, 0, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100022 : mirrorTrits [1, 0, 1, 2, 2, 2, 0] = [2, 0, 2, 1, 1, 1, 0] := by
  decide

theorem demoInv_0100022 : specInv 7 5 20 [0, 1, 0, 0, 0, 2, 2] = some [2, 0, 2, 1, 1, 1, 0] :=
  specInv_mirror_7 [0, 1, 0, 0, 0, 2, 2] [2, 1, 2, 1, 2, 2, 2] [0, 1, 1, 2, 1, 2, 0] [1, 0, 1, 2, 2, 2, 0] [2, 0, 2, 1, 1, 1, 0] demoR1_0100022 demoR2_0100022 demoC_0100022 demoM_0100022 demoMir_0100022

theorem demoR1_1100022 : invRung 7 5 20 [1, 1, 0, 0, 0, 2, 2] [1, 1, 0, 0, 0, 2, 2] 1 2 false = ([0, 2, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1100022 : invRung 7 5 20 [1, 1, 0, 0, 0, 2, 2] [0, 2, 0, 0, 1, 0, 1] 3 1 true = ([2, 1, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_1100022 : fieldCube 7 5 20 [2, 1, 2, 2, 2, 2, 1] = [0, 2, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_1100022 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 1, 0] [1, 1, 0, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1100022 : mirrorTrits [0, 2, 0, 1, 0, 1, 0] = [0, 1, 0, 2, 0, 2, 0] := by
  decide

theorem demoInv_1100022 : specInv 7 5 20 [1, 1, 0, 0, 0, 2, 2] = some [0, 1, 0, 2, 0, 2, 0] :=
  specInv_mirror_7 [1, 1, 0, 0, 0, 2, 2] [0, 2, 0, 0, 1, 0, 1] [2, 1, 2, 2, 2, 2, 1] [0, 2, 0, 1, 0, 1, 0] [0, 1, 0, 2, 0, 2, 0] demoR1_1100022 demoR2_1100022 demoC_1100022 demoM_1100022 demoMir_1100022

theorem demoR1_2100022 : invRung 7 5 20 [2, 1, 0, 0, 0, 2, 2] [2, 1, 0, 0, 0, 2, 2] 1 2 false = ([2, 2, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_2100022 : invRung 7 5 20 [2, 1, 0, 0, 0, 2, 2] [2, 2, 0, 0, 1, 2, 1] 3 1 true = ([2, 0, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_2100022 : fieldCube 7 5 20 [2, 0, 1, 1, 2, 0, 1] = [0, 0, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_2100022 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 1, 1] [2, 1, 0, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2100022 : specInv 7 5 20 [2, 1, 0, 0, 0, 2, 2] = some [0, 0, 0, 0, 1, 1, 1] :=
  specInv_white_7 [2, 1, 0, 0, 0, 2, 2] [2, 2, 0, 0, 1, 2, 1] [2, 0, 1, 1, 2, 0, 1] [0, 0, 0, 0, 1, 1, 1] demoR1_2100022 demoR2_2100022 demoC_2100022 demoM_2100022

theorem demoR1_0200022 : invRung 7 5 20 [0, 2, 0, 0, 0, 2, 2] [0, 2, 0, 0, 0, 2, 2] 1 2 false = ([1, 1, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0200022 : invRung 7 5 20 [0, 2, 0, 0, 0, 2, 2] [1, 1, 2, 1, 2, 1, 2] 3 1 true = ([2, 0, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0200022 : fieldCube 7 5 20 [2, 0, 1, 2, 1, 0, 1] = [1, 2, 1, 2, 1, 1, 0] := by
  decide

theorem demoM_0200022 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 1, 0] [0, 2, 0, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200022 : mirrorTrits [1, 2, 1, 2, 1, 1, 0] = [2, 1, 2, 1, 2, 2, 0] := by
  decide

theorem demoInv_0200022 : specInv 7 5 20 [0, 2, 0, 0, 0, 2, 2] = some [2, 1, 2, 1, 2, 2, 0] :=
  specInv_mirror_7 [0, 2, 0, 0, 0, 2, 2] [1, 1, 2, 1, 2, 1, 2] [2, 0, 1, 2, 1, 0, 1] [1, 2, 1, 2, 1, 1, 0] [2, 1, 2, 1, 2, 2, 0] demoR1_0200022 demoR2_0200022 demoC_0200022 demoM_0200022 demoMir_0200022

theorem demoR1_1200022 : invRung 7 5 20 [1, 2, 0, 0, 0, 2, 2] [1, 2, 0, 0, 0, 2, 2] 1 2 false = ([2, 0, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1200022 : invRung 7 5 20 [1, 2, 0, 0, 0, 2, 2] [2, 0, 2, 0, 1, 0, 1] 3 1 true = ([1, 0, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_1200022 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 0, 1] = [2, 1, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_1200022 : fieldMul 7 5 20 [2, 1, 0, 1, 1, 2, 1] [1, 2, 0, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1200022 : specInv 7 5 20 [1, 2, 0, 0, 0, 2, 2] = some [2, 1, 0, 1, 1, 2, 1] :=
  specInv_white_7 [1, 2, 0, 0, 0, 2, 2] [2, 0, 2, 0, 1, 0, 1] [1, 0, 0, 1, 0, 0, 1] [2, 1, 0, 1, 1, 2, 1] demoR1_1200022 demoR2_1200022 demoC_1200022 demoM_1200022

theorem demoR1_2200022 : invRung 7 5 20 [2, 2, 0, 0, 0, 2, 2] [2, 2, 0, 0, 0, 2, 2] 1 2 false = ([0, 0, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_2200022 : invRung 7 5 20 [2, 2, 0, 0, 0, 2, 2] [0, 0, 0, 2, 1, 2, 1] 3 1 true = ([1, 1, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_2200022 : fieldCube 7 5 20 [1, 1, 1, 2, 1, 0, 2] = [0, 0, 0, 1, 2, 2, 1] := by
  decide

theorem demoM_2200022 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 2, 1] [2, 2, 0, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200022 : mirrorTrits [0, 0, 0, 1, 2, 2, 1] = [0, 0, 0, 2, 1, 1, 2] := by
  decide

theorem demoInv_2200022 : specInv 7 5 20 [2, 2, 0, 0, 0, 2, 2] = some [0, 0, 0, 2, 1, 1, 2] :=
  specInv_mirror_7 [2, 2, 0, 0, 0, 2, 2] [0, 0, 0, 2, 1, 2, 1] [1, 1, 1, 2, 1, 0, 2] [0, 0, 0, 1, 2, 2, 1] [0, 0, 0, 2, 1, 1, 2] demoR1_2200022 demoR2_2200022 demoC_2200022 demoM_2200022 demoMir_2200022

theorem demoR1_0010022 : invRung 7 5 20 [0, 0, 1, 0, 0, 2, 2] [0, 0, 1, 0, 0, 2, 2] 1 2 false = ([0, 0, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_0010022 : invRung 7 5 20 [0, 0, 1, 0, 0, 2, 2] [0, 0, 2, 1, 1, 0, 0] 3 1 true = ([0, 1, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0010022 : fieldCube 7 5 20 [0, 1, 1, 2, 1, 0, 1] = [2, 2, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_0010022 : fieldMul 7 5 20 [2, 2, 1, 0, 1, 1, 0] [0, 0, 1, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010022 : mirrorTrits [2, 2, 1, 0, 1, 1, 0] = [1, 1, 2, 0, 2, 2, 0] := by
  decide

theorem demoInv_0010022 : specInv 7 5 20 [0, 0, 1, 0, 0, 2, 2] = some [1, 1, 2, 0, 2, 2, 0] :=
  specInv_mirror_7 [0, 0, 1, 0, 0, 2, 2] [0, 0, 2, 1, 1, 0, 0] [0, 1, 1, 2, 1, 0, 1] [2, 2, 1, 0, 1, 1, 0] [1, 1, 2, 0, 2, 2, 0] demoR1_0010022 demoR2_0010022 demoC_0010022 demoM_0010022 demoMir_0010022

theorem demoR1_1010022 : invRung 7 5 20 [1, 0, 1, 0, 0, 2, 2] [1, 0, 1, 0, 0, 2, 2] 1 2 false = ([0, 1, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_1010022 : invRung 7 5 20 [1, 0, 1, 0, 0, 2, 2] [0, 1, 0, 2, 1, 2, 2] 3 1 true = ([0, 2, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_1010022 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 1, 2] = [2, 1, 0, 2, 0, 2, 1] := by
  decide

theorem demoM_1010022 : fieldMul 7 5 20 [2, 1, 0, 2, 0, 2, 1] [1, 0, 1, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1010022 : specInv 7 5 20 [1, 0, 1, 0, 0, 2, 2] = some [2, 1, 0, 2, 0, 2, 1] :=
  specInv_white_7 [1, 0, 1, 0, 0, 2, 2] [0, 1, 0, 2, 1, 2, 2] [0, 2, 2, 1, 1, 1, 2] [2, 1, 0, 2, 0, 2, 1] demoR1_1010022 demoR2_1010022 demoC_1010022 demoM_1010022

theorem demoR1_2010022 : invRung 7 5 20 [2, 0, 1, 0, 0, 2, 2] [2, 0, 1, 0, 0, 2, 2] 1 2 false = ([2, 1, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2010022 : invRung 7 5 20 [2, 0, 1, 0, 0, 2, 2] [2, 1, 1, 1, 1, 2, 0] 3 1 true = ([2, 0, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_2010022 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 2, 2] = [0, 1, 2, 2, 1, 0, 1] := by
  decide

theorem demoM_2010022 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 0, 1] [2, 0, 1, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010022 : mirrorTrits [0, 1, 2, 2, 1, 0, 1] = [0, 2, 1, 1, 2, 0, 2] := by
  decide

theorem demoInv_2010022 : specInv 7 5 20 [2, 0, 1, 0, 0, 2, 2] = some [0, 2, 1, 1, 2, 0, 2] :=
  specInv_mirror_7 [2, 0, 1, 0, 0, 2, 2] [2, 1, 1, 1, 1, 2, 0] [2, 0, 1, 2, 0, 2, 2] [0, 1, 2, 2, 1, 0, 1] [0, 2, 1, 1, 2, 0, 2] demoR1_2010022 demoR2_2010022 demoC_2010022 demoM_2010022 demoMir_2010022

theorem demoR1_0110022 : invRung 7 5 20 [0, 1, 1, 0, 0, 2, 2] [0, 1, 1, 0, 0, 2, 2] 1 2 false = ([0, 0, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_0110022 : invRung 7 5 20 [0, 1, 1, 0, 0, 2, 2] [0, 0, 1, 1, 1, 0, 1] 3 1 true = ([0, 2, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0110022 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 2, 1] = [1, 1, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_0110022 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 0, 1] [0, 1, 1, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0110022 : specInv 7 5 20 [0, 1, 1, 0, 0, 2, 2] = some [1, 1, 0, 1, 0, 0, 1] :=
  specInv_white_7 [0, 1, 1, 0, 0, 2, 2] [0, 0, 1, 1, 1, 0, 1] [0, 2, 1, 2, 1, 2, 1] [1, 1, 0, 1, 0, 0, 1] demoR1_0110022 demoR2_0110022 demoC_0110022 demoM_0110022

theorem demoR1_1110022 : invRung 7 5 20 [1, 1, 1, 0, 0, 2, 2] [1, 1, 1, 0, 0, 2, 2] 1 2 false = ([0, 0, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_1110022 : invRung 7 5 20 [1, 1, 1, 0, 0, 2, 2] [0, 0, 2, 0, 0, 2, 1] 3 1 true = ([0, 1, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_1110022 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 0, 1] = [0, 2, 2, 0, 1, 2, 1] := by
  decide

theorem demoM_1110022 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 2, 1] [1, 1, 1, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1110022 : specInv 7 5 20 [1, 1, 1, 0, 0, 2, 2] = some [0, 2, 2, 0, 1, 2, 1] :=
  specInv_white_7 [1, 1, 1, 0, 0, 2, 2] [0, 0, 2, 0, 0, 2, 1] [0, 1, 2, 0, 1, 0, 1] [0, 2, 2, 0, 1, 2, 1] demoR1_1110022 demoR2_1110022 demoC_1110022 demoM_1110022

theorem demoR1_2110022 : invRung 7 5 20 [2, 1, 1, 0, 0, 2, 2] [2, 1, 1, 0, 0, 2, 2] 1 2 false = ([1, 1, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_2110022 : invRung 7 5 20 [2, 1, 1, 0, 0, 2, 2] [1, 1, 2, 2, 2, 1, 0] 3 1 true = ([1, 1, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_2110022 : fieldCube 7 5 20 [1, 1, 2, 0, 2, 1, 0] = [2, 0, 1, 0, 1, 0, 0] := by
  decide

theorem demoM_2110022 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 0, 0] [2, 1, 1, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110022 : mirrorTrits [2, 0, 1, 0, 1, 0, 0] = [1, 0, 2, 0, 2, 0, 0] := by
  decide

theorem demoInv_2110022 : specInv 7 5 20 [2, 1, 1, 0, 0, 2, 2] = some [1, 0, 2, 0, 2, 0, 0] :=
  specInv_mirror_7 [2, 1, 1, 0, 0, 2, 2] [1, 1, 2, 2, 2, 1, 0] [1, 1, 2, 0, 2, 1, 0] [2, 0, 1, 0, 1, 0, 0] [1, 0, 2, 0, 2, 0, 0] demoR1_2110022 demoR2_2110022 demoC_2110022 demoM_2110022 demoMir_2110022

theorem demoR1_0210022 : invRung 7 5 20 [0, 2, 1, 0, 0, 2, 2] [0, 2, 1, 0, 0, 2, 2] 1 2 false = ([0, 0, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_0210022 : invRung 7 5 20 [0, 2, 1, 0, 0, 2, 2] [0, 0, 2, 0, 0, 1, 1] 3 1 true = ([0, 0, 2, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_0210022 : fieldCube 7 5 20 [0, 0, 2, 0, 2, 2, 0] = [2, 1, 2, 2, 2, 1, 2] := by
  decide

theorem demoM_0210022 : fieldMul 7 5 20 [2, 1, 2, 2, 2, 1, 2] [0, 2, 1, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0210022 : specInv 7 5 20 [0, 2, 1, 0, 0, 2, 2] = some [2, 1, 2, 2, 2, 1, 2] :=
  specInv_white_7 [0, 2, 1, 0, 0, 2, 2] [0, 0, 2, 0, 0, 1, 1] [0, 0, 2, 0, 2, 2, 0] [2, 1, 2, 2, 2, 1, 2] demoR1_0210022 demoR2_0210022 demoC_0210022 demoM_0210022

theorem demoR1_1210022 : invRung 7 5 20 [1, 2, 1, 0, 0, 2, 2] [1, 2, 1, 0, 0, 2, 2] 1 2 false = ([0, 0, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_1210022 : invRung 7 5 20 [1, 2, 1, 0, 0, 2, 2] [0, 0, 0, 1, 0, 2, 0] 3 1 true = ([1, 2, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_1210022 : fieldCube 7 5 20 [1, 2, 0, 2, 1, 1, 2] = [1, 1, 1, 2, 0, 0, 2] := by
  decide

theorem demoM_1210022 : fieldMul 7 5 20 [1, 1, 1, 2, 0, 0, 2] [1, 2, 1, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1210022 : mirrorTrits [1, 1, 1, 2, 0, 0, 2] = [2, 2, 2, 1, 0, 0, 1] := by
  decide

theorem demoInv_1210022 : specInv 7 5 20 [1, 2, 1, 0, 0, 2, 2] = some [2, 2, 2, 1, 0, 0, 1] :=
  specInv_mirror_7 [1, 2, 1, 0, 0, 2, 2] [0, 0, 0, 1, 0, 2, 0] [1, 2, 0, 2, 1, 1, 2] [1, 1, 1, 2, 0, 0, 2] [2, 2, 2, 1, 0, 0, 1] demoR1_1210022 demoR2_1210022 demoC_1210022 demoM_1210022 demoMir_1210022

theorem demoR1_2210022 : invRung 7 5 20 [2, 2, 1, 0, 0, 2, 2] [2, 2, 1, 0, 0, 2, 2] 1 2 false = ([0, 0, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2210022 : invRung 7 5 20 [2, 2, 1, 0, 0, 2, 2] [0, 0, 2, 1, 0, 2, 1] 3 1 true = ([2, 1, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_2210022 : fieldCube 7 5 20 [2, 1, 0, 1, 2, 0, 1] = [0, 0, 0, 1, 1, 1, 0] := by
  decide

theorem demoM_2210022 : fieldMul 7 5 20 [0, 0, 0, 1, 1, 1, 0] [2, 2, 1, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2210022 : specInv 7 5 20 [2, 2, 1, 0, 0, 2, 2] = some [0, 0, 0, 1, 1, 1, 0] :=
  specInv_white_7 [2, 2, 1, 0, 0, 2, 2] [0, 0, 2, 1, 0, 2, 1] [2, 1, 0, 1, 2, 0, 1] [0, 0, 0, 1, 1, 1, 0] demoR1_2210022 demoR2_2210022 demoC_2210022 demoM_2210022

theorem demoR1_0020022 : invRung 7 5 20 [0, 0, 2, 0, 0, 2, 2] [0, 0, 2, 0, 0, 2, 2] 1 2 false = ([0, 0, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0020022 : invRung 7 5 20 [0, 0, 2, 0, 0, 2, 2] [0, 0, 2, 2, 2, 2, 1] 3 1 true = ([0, 0, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0020022 : fieldCube 7 5 20 [0, 0, 2, 0, 2, 1, 2] = [1, 2, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_0020022 : fieldMul 7 5 20 [1, 2, 2, 1, 0, 2, 2] [0, 0, 2, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0020022 : specInv 7 5 20 [0, 0, 2, 0, 0, 2, 2] = some [1, 2, 2, 1, 0, 2, 2] :=
  specInv_white_7 [0, 0, 2, 0, 0, 2, 2] [0, 0, 2, 2, 2, 2, 1] [0, 0, 2, 0, 2, 1, 2] [1, 2, 2, 1, 0, 2, 2] demoR1_0020022 demoR2_0020022 demoC_0020022 demoM_0020022

theorem demoR1_1020022 : invRung 7 5 20 [1, 0, 2, 0, 0, 2, 2] [1, 0, 2, 0, 0, 2, 2] 1 2 false = ([1, 1, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_1020022 : invRung 7 5 20 [1, 0, 2, 0, 0, 2, 2] [1, 1, 0, 1, 1, 1, 1] 3 1 true = ([2, 1, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_1020022 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 2, 0] = [1, 0, 2, 2, 2, 0, 0] := by
  decide

theorem demoM_1020022 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 0, 0] [1, 0, 2, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1020022 : specInv 7 5 20 [1, 0, 2, 0, 0, 2, 2] = some [1, 0, 2, 2, 2, 0, 0] :=
  specInv_white_7 [1, 0, 2, 0, 0, 2, 2] [1, 1, 0, 1, 1, 1, 1] [2, 1, 1, 0, 1, 2, 0] [1, 0, 2, 2, 2, 0, 0] demoR1_1020022 demoR2_1020022 demoC_1020022 demoM_1020022

theorem demoR1_2020022 : invRung 7 5 20 [2, 0, 2, 0, 0, 2, 2] [2, 0, 2, 0, 0, 2, 2] 1 2 false = ([1, 0, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_2020022 : invRung 7 5 20 [2, 0, 2, 0, 0, 2, 2] [1, 0, 1, 0, 2, 0, 1] 3 1 true = ([0, 0, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_2020022 : fieldCube 7 5 20 [0, 0, 0, 2, 1, 0, 0] = [2, 1, 2, 1, 0, 0, 1] := by
  decide

theorem demoM_2020022 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 0, 1] [2, 0, 2, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020022 : mirrorTrits [2, 1, 2, 1, 0, 0, 1] = [1, 2, 1, 2, 0, 0, 2] := by
  decide

theorem demoInv_2020022 : specInv 7 5 20 [2, 0, 2, 0, 0, 2, 2] = some [1, 2, 1, 2, 0, 0, 2] :=
  specInv_mirror_7 [2, 0, 2, 0, 0, 2, 2] [1, 0, 1, 0, 2, 0, 1] [0, 0, 0, 2, 1, 0, 0] [2, 1, 2, 1, 0, 0, 1] [1, 2, 1, 2, 0, 0, 2] demoR1_2020022 demoR2_2020022 demoC_2020022 demoM_2020022 demoMir_2020022

theorem demoR1_0120022 : invRung 7 5 20 [0, 1, 2, 0, 0, 2, 2] [0, 1, 2, 0, 0, 2, 2] 1 2 false = ([0, 0, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_0120022 : invRung 7 5 20 [0, 1, 2, 0, 0, 2, 2] [0, 0, 0, 0, 0, 2, 1] 3 1 true = ([1, 1, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0120022 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 0, 1] = [1, 1, 2, 2, 1, 1, 2] := by
  decide

theorem demoM_0120022 : fieldMul 7 5 20 [1, 1, 2, 2, 1, 1, 2] [0, 1, 2, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0120022 : specInv 7 5 20 [0, 1, 2, 0, 0, 2, 2] = some [1, 1, 2, 2, 1, 1, 2] :=
  specInv_white_7 [0, 1, 2, 0, 0, 2, 2] [0, 0, 0, 0, 0, 2, 1] [1, 1, 1, 0, 0, 0, 1] [1, 1, 2, 2, 1, 1, 2] demoR1_0120022 demoR2_0120022 demoC_0120022 demoM_0120022

theorem demoR1_1120022 : invRung 7 5 20 [1, 1, 2, 0, 0, 2, 2] [1, 1, 2, 0, 0, 2, 2] 1 2 false = ([1, 2, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_1120022 : invRung 7 5 20 [1, 1, 2, 0, 0, 2, 2] [1, 2, 2, 2, 2, 2, 1] 3 1 true = ([1, 0, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_1120022 : fieldCube 7 5 20 [1, 0, 1, 0, 2, 1, 0] = [2, 0, 1, 2, 1, 0, 2] := by
  decide

theorem demoM_1120022 : fieldMul 7 5 20 [2, 0, 1, 2, 1, 0, 2] [1, 1, 2, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1120022 : specInv 7 5 20 [1, 1, 2, 0, 0, 2, 2] = some [2, 0, 1, 2, 1, 0, 2] :=
  specInv_white_7 [1, 1, 2, 0, 0, 2, 2] [1, 2, 2, 2, 2, 2, 1] [1, 0, 1, 0, 2, 1, 0] [2, 0, 1, 2, 1, 0, 2] demoR1_1120022 demoR2_1120022 demoC_1120022 demoM_1120022

theorem demoR1_2120022 : invRung 7 5 20 [2, 1, 2, 0, 0, 2, 2] [2, 1, 2, 0, 0, 2, 2] 1 2 false = ([0, 1, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_2120022 : invRung 7 5 20 [2, 1, 2, 0, 0, 2, 2] [0, 1, 0, 0, 0, 1, 1] 3 1 true = ([0, 1, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_2120022 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 0, 0] = [1, 0, 1, 1, 0, 1, 2] := by
  decide

theorem demoM_2120022 : fieldMul 7 5 20 [1, 0, 1, 1, 0, 1, 2] [2, 1, 2, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2120022 : specInv 7 5 20 [2, 1, 2, 0, 0, 2, 2] = some [1, 0, 1, 1, 0, 1, 2] :=
  specInv_white_7 [2, 1, 2, 0, 0, 2, 2] [0, 1, 0, 0, 0, 1, 1] [0, 1, 2, 1, 0, 0, 0] [1, 0, 1, 1, 0, 1, 2] demoR1_2120022 demoR2_2120022 demoC_2120022 demoM_2120022

theorem demoR1_0220022 : invRung 7 5 20 [0, 2, 2, 0, 0, 2, 2] [0, 2, 2, 0, 0, 2, 2] 1 2 false = ([1, 2, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_0220022 : invRung 7 5 20 [0, 2, 2, 0, 0, 2, 2] [1, 2, 1, 0, 0, 1, 0] 3 1 true = ([2, 2, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_0220022 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 0, 2] = [0, 0, 2, 2, 2, 1, 1] := by
  decide

theorem demoM_0220022 : fieldMul 7 5 20 [0, 0, 2, 2, 2, 1, 1] [0, 2, 2, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0220022 : mirrorTrits [0, 0, 2, 2, 2, 1, 1] = [0, 0, 1, 1, 1, 2, 2] := by
  decide

theorem demoInv_0220022 : specInv 7 5 20 [0, 2, 2, 0, 0, 2, 2] = some [0, 0, 1, 1, 1, 2, 2] :=
  specInv_mirror_7 [0, 2, 2, 0, 0, 2, 2] [1, 2, 1, 0, 0, 1, 0] [2, 2, 1, 1, 1, 0, 2] [0, 0, 2, 2, 2, 1, 1] [0, 0, 1, 1, 1, 2, 2] demoR1_0220022 demoR2_0220022 demoC_0220022 demoM_0220022 demoMir_0220022

theorem demoR1_1220022 : invRung 7 5 20 [1, 2, 2, 0, 0, 2, 2] [1, 2, 2, 0, 0, 2, 2] 1 2 false = ([2, 0, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_1220022 : invRung 7 5 20 [1, 2, 2, 0, 0, 2, 2] [2, 0, 1, 0, 1, 1, 1] 3 1 true = ([0, 1, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_1220022 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 0, 2] = [1, 2, 2, 0, 2, 0, 0] := by
  decide

theorem demoM_1220022 : fieldMul 7 5 20 [1, 2, 2, 0, 2, 0, 0] [1, 2, 2, 0, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1220022 : specInv 7 5 20 [1, 2, 2, 0, 0, 2, 2] = some [1, 2, 2, 0, 2, 0, 0] :=
  specInv_white_7 [1, 2, 2, 0, 0, 2, 2] [2, 0, 1, 0, 1, 1, 1] [0, 1, 1, 1, 0, 0, 2] [1, 2, 2, 0, 2, 0, 0] demoR1_1220022 demoR2_1220022 demoC_1220022 demoM_1220022

theorem demoR1_2220022 : invRung 7 5 20 [2, 2, 2, 0, 0, 2, 2] [2, 2, 2, 0, 0, 2, 2] 1 2 false = ([0, 0, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2220022 : invRung 7 5 20 [2, 2, 2, 0, 0, 2, 2] [0, 0, 2, 1, 1, 2, 2] 3 1 true = ([1, 0, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_2220022 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 1, 1] = [0, 0, 1, 2, 2, 1, 0] := by
  decide

theorem demoM_2220022 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 1, 0] [2, 2, 2, 0, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220022 : mirrorTrits [0, 0, 1, 2, 2, 1, 0] = [0, 0, 2, 1, 1, 2, 0] := by
  decide

theorem demoInv_2220022 : specInv 7 5 20 [2, 2, 2, 0, 0, 2, 2] = some [0, 0, 2, 1, 1, 2, 0] :=
  specInv_mirror_7 [2, 2, 2, 0, 0, 2, 2] [0, 0, 2, 1, 1, 2, 2] [1, 0, 2, 1, 1, 1, 1] [0, 0, 1, 2, 2, 1, 0] [0, 0, 2, 1, 1, 2, 0] demoR1_2220022 demoR2_2220022 demoC_2220022 demoM_2220022 demoMir_2220022

theorem demoR1_0001022 : invRung 7 5 20 [0, 0, 0, 1, 0, 2, 2] [0, 0, 0, 1, 0, 2, 2] 1 2 false = ([1, 1, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_0001022 : invRung 7 5 20 [0, 0, 0, 1, 0, 2, 2] [1, 1, 1, 1, 1, 2, 1] 3 1 true = ([0, 2, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0001022 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 2, 2] = [0, 2, 1, 2, 1, 0, 2] := by
  decide

theorem demoM_0001022 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 0, 2] [0, 0, 0, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0001022 : specInv 7 5 20 [0, 0, 0, 1, 0, 2, 2] = some [0, 2, 1, 2, 1, 0, 2] :=
  specInv_white_7 [0, 0, 0, 1, 0, 2, 2] [1, 1, 1, 1, 1, 2, 1] [0, 2, 1, 1, 1, 2, 2] [0, 2, 1, 2, 1, 0, 2] demoR1_0001022 demoR2_0001022 demoC_0001022 demoM_0001022

theorem demoR1_1001022 : invRung 7 5 20 [1, 0, 0, 1, 0, 2, 2] [1, 0, 0, 1, 0, 2, 2] 1 2 false = ([2, 2, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_1001022 : invRung 7 5 20 [1, 0, 0, 1, 0, 2, 2] [2, 2, 2, 1, 2, 1, 1] 3 1 true = ([2, 1, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_1001022 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 0, 2] = [0, 2, 2, 0, 2, 0, 1] := by
  decide

theorem demoM_1001022 : fieldMul 7 5 20 [0, 2, 2, 0, 2, 0, 1] [1, 0, 0, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1001022 : mirrorTrits [0, 2, 2, 0, 2, 0, 1] = [0, 1, 1, 0, 1, 0, 2] := by
  decide

theorem demoInv_1001022 : specInv 7 5 20 [1, 0, 0, 1, 0, 2, 2] = some [0, 1, 1, 0, 1, 0, 2] :=
  specInv_mirror_7 [1, 0, 0, 1, 0, 2, 2] [2, 2, 2, 1, 2, 1, 1] [2, 1, 2, 1, 0, 0, 2] [0, 2, 2, 0, 2, 0, 1] [0, 1, 1, 0, 1, 0, 2] demoR1_1001022 demoR2_1001022 demoC_1001022 demoM_1001022 demoMir_1001022

theorem demoR1_2001022 : invRung 7 5 20 [2, 0, 0, 1, 0, 2, 2] [2, 0, 0, 1, 0, 2, 2] 1 2 false = ([2, 2, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2001022 : invRung 7 5 20 [2, 0, 0, 1, 0, 2, 2] [2, 2, 1, 2, 0, 0, 2] 3 1 true = ([0, 0, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_2001022 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 0, 2] = [2, 1, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_2001022 : fieldMul 7 5 20 [2, 1, 0, 1, 2, 0, 2] [2, 0, 0, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001022 : mirrorTrits [2, 1, 0, 1, 2, 0, 2] = [1, 2, 0, 2, 1, 0, 1] := by
  decide

theorem demoInv_2001022 : specInv 7 5 20 [2, 0, 0, 1, 0, 2, 2] = some [1, 2, 0, 2, 1, 0, 1] :=
  specInv_mirror_7 [2, 0, 0, 1, 0, 2, 2] [2, 2, 1, 2, 0, 0, 2] [0, 0, 1, 2, 2, 0, 2] [2, 1, 0, 1, 2, 0, 2] [1, 2, 0, 2, 1, 0, 1] demoR1_2001022 demoR2_2001022 demoC_2001022 demoM_2001022 demoMir_2001022

theorem demoR1_0101022 : invRung 7 5 20 [0, 1, 0, 1, 0, 2, 2] [0, 1, 0, 1, 0, 2, 2] 1 2 false = ([0, 1, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_0101022 : invRung 7 5 20 [0, 1, 0, 1, 0, 2, 2] [0, 1, 0, 0, 0, 1, 2] 3 1 true = ([0, 0, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_0101022 : fieldCube 7 5 20 [0, 0, 0, 2, 1, 2, 2] = [1, 2, 2, 0, 1, 1, 1] := by
  decide

theorem demoM_0101022 : fieldMul 7 5 20 [1, 2, 2, 0, 1, 1, 1] [0, 1, 0, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101022 : mirrorTrits [1, 2, 2, 0, 1, 1, 1] = [2, 1, 1, 0, 2, 2, 2] := by
  decide

theorem demoInv_0101022 : specInv 7 5 20 [0, 1, 0, 1, 0, 2, 2] = some [2, 1, 1, 0, 2, 2, 2] :=
  specInv_mirror_7 [0, 1, 0, 1, 0, 2, 2] [0, 1, 0, 0, 0, 1, 2] [0, 0, 0, 2, 1, 2, 2] [1, 2, 2, 0, 1, 1, 1] [2, 1, 1, 0, 2, 2, 2] demoR1_0101022 demoR2_0101022 demoC_0101022 demoM_0101022 demoMir_0101022

theorem demoR1_1101022 : invRung 7 5 20 [1, 1, 0, 1, 0, 2, 2] [1, 1, 0, 1, 0, 2, 2] 1 2 false = ([2, 2, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_1101022 : invRung 7 5 20 [1, 1, 0, 1, 0, 2, 2] [2, 2, 0, 2, 1, 1, 1] 3 1 true = ([0, 1, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_1101022 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 0, 1] = [0, 0, 2, 1, 1, 0, 2] := by
  decide

theorem demoM_1101022 : fieldMul 7 5 20 [0, 0, 2, 1, 1, 0, 2] [1, 1, 0, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1101022 : mirrorTrits [0, 0, 2, 1, 1, 0, 2] = [0, 0, 1, 2, 2, 0, 1] := by
  decide

theorem demoInv_1101022 : specInv 7 5 20 [1, 1, 0, 1, 0, 2, 2] = some [0, 0, 1, 2, 2, 0, 1] :=
  specInv_mirror_7 [1, 1, 0, 1, 0, 2, 2] [2, 2, 0, 2, 1, 1, 1] [0, 1, 2, 0, 2, 0, 1] [0, 0, 2, 1, 1, 0, 2] [0, 0, 1, 2, 2, 0, 1] demoR1_1101022 demoR2_1101022 demoC_1101022 demoM_1101022 demoMir_1101022

theorem demoR1_2101022 : invRung 7 5 20 [2, 1, 0, 1, 0, 2, 2] [2, 1, 0, 1, 0, 2, 2] 1 2 false = ([2, 1, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2101022 : invRung 7 5 20 [2, 1, 0, 1, 0, 2, 2] [2, 1, 0, 1, 2, 0, 1] 3 1 true = ([1, 2, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2101022 : fieldCube 7 5 20 [1, 2, 0, 1, 0, 2, 1] = [1, 0, 2, 0, 0, 1, 2] := by
  decide

theorem demoM_2101022 : fieldMul 7 5 20 [1, 0, 2, 0, 0, 1, 2] [2, 1, 0, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2101022 : specInv 7 5 20 [2, 1, 0, 1, 0, 2, 2] = some [1, 0, 2, 0, 0, 1, 2] :=
  specInv_white_7 [2, 1, 0, 1, 0, 2, 2] [2, 1, 0, 1, 2, 0, 1] [1, 2, 0, 1, 0, 2, 1] [1, 0, 2, 0, 0, 1, 2] demoR1_2101022 demoR2_2101022 demoC_2101022 demoM_2101022

theorem demoR1_0201022 : invRung 7 5 20 [0, 2, 0, 1, 0, 2, 2] [0, 2, 0, 1, 0, 2, 2] 1 2 false = ([1, 0, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_0201022 : invRung 7 5 20 [0, 2, 0, 1, 0, 2, 2] [1, 0, 0, 2, 0, 1, 0] 3 1 true = ([0, 1, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0201022 : fieldCube 7 5 20 [0, 1, 1, 0, 1, 2, 2] = [2, 2, 0, 1, 1, 2, 2] := by
  decide

theorem demoM_0201022 : fieldMul 7 5 20 [2, 2, 0, 1, 1, 2, 2] [0, 2, 0, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201022 : mirrorTrits [2, 2, 0, 1, 1, 2, 2] = [1, 1, 0, 2, 2, 1, 1] := by
  decide

theorem demoInv_0201022 : specInv 7 5 20 [0, 2, 0, 1, 0, 2, 2] = some [1, 1, 0, 2, 2, 1, 1] :=
  specInv_mirror_7 [0, 2, 0, 1, 0, 2, 2] [1, 0, 0, 2, 0, 1, 0] [0, 1, 1, 0, 1, 2, 2] [2, 2, 0, 1, 1, 2, 2] [1, 1, 0, 2, 2, 1, 1] demoR1_0201022 demoR2_0201022 demoC_0201022 demoM_0201022 demoMir_0201022

theorem demoR1_1201022 : invRung 7 5 20 [1, 2, 0, 1, 0, 2, 2] [1, 2, 0, 1, 0, 2, 2] 1 2 false = ([1, 2, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_1201022 : invRung 7 5 20 [1, 2, 0, 1, 0, 2, 2] [1, 2, 2, 1, 0, 1, 2] 3 1 true = ([2, 2, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1201022 : fieldCube 7 5 20 [2, 2, 1, 1, 0, 2, 0] = [2, 2, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_1201022 : fieldMul 7 5 20 [2, 2, 0, 2, 2, 0, 2] [1, 2, 0, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201022 : mirrorTrits [2, 2, 0, 2, 2, 0, 2] = [1, 1, 0, 1, 1, 0, 1] := by
  decide

theorem demoInv_1201022 : specInv 7 5 20 [1, 2, 0, 1, 0, 2, 2] = some [1, 1, 0, 1, 1, 0, 1] :=
  specInv_mirror_7 [1, 2, 0, 1, 0, 2, 2] [1, 2, 2, 1, 0, 1, 2] [2, 2, 1, 1, 0, 2, 0] [2, 2, 0, 2, 2, 0, 2] [1, 1, 0, 1, 1, 0, 1] demoR1_1201022 demoR2_1201022 demoC_1201022 demoM_1201022 demoMir_1201022

theorem demoR1_2201022 : invRung 7 5 20 [2, 2, 0, 1, 0, 2, 2] [2, 2, 0, 1, 0, 2, 2] 1 2 false = ([1, 1, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_2201022 : invRung 7 5 20 [2, 2, 0, 1, 0, 2, 2] [1, 1, 0, 2, 0, 2, 2] 3 1 true = ([2, 2, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_2201022 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 0, 0] = [1, 2, 2, 1, 0, 1, 0] := by
  decide

theorem demoM_2201022 : fieldMul 7 5 20 [1, 2, 2, 1, 0, 1, 0] [2, 2, 0, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2201022 : mirrorTrits [1, 2, 2, 1, 0, 1, 0] = [2, 1, 1, 2, 0, 2, 0] := by
  decide

theorem demoInv_2201022 : specInv 7 5 20 [2, 2, 0, 1, 0, 2, 2] = some [2, 1, 1, 2, 0, 2, 0] :=
  specInv_mirror_7 [2, 2, 0, 1, 0, 2, 2] [1, 1, 0, 2, 0, 2, 2] [2, 2, 1, 2, 2, 0, 0] [1, 2, 2, 1, 0, 1, 0] [2, 1, 1, 2, 0, 2, 0] demoR1_2201022 demoR2_2201022 demoC_2201022 demoM_2201022 demoMir_2201022

theorem demoR1_0011022 : invRung 7 5 20 [0, 0, 1, 1, 0, 2, 2] [0, 0, 1, 1, 0, 2, 2] 1 2 false = ([0, 2, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_0011022 : invRung 7 5 20 [0, 0, 1, 1, 0, 2, 2] [0, 2, 1, 1, 0, 2, 2] 3 1 true = ([2, 1, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_0011022 : fieldCube 7 5 20 [2, 1, 0, 0, 1, 2, 0] = [1, 0, 2, 2, 2, 0, 2] := by
  decide

theorem demoM_0011022 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 0, 2] [0, 0, 1, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011022 : mirrorTrits [1, 0, 2, 2, 2, 0, 2] = [2, 0, 1, 1, 1, 0, 1] := by
  decide

theorem demoInv_0011022 : specInv 7 5 20 [0, 0, 1, 1, 0, 2, 2] = some [2, 0, 1, 1, 1, 0, 1] :=
  specInv_mirror_7 [0, 0, 1, 1, 0, 2, 2] [0, 2, 1, 1, 0, 2, 2] [2, 1, 0, 0, 1, 2, 0] [1, 0, 2, 2, 2, 0, 2] [2, 0, 1, 1, 1, 0, 1] demoR1_0011022 demoR2_0011022 demoC_0011022 demoM_0011022 demoMir_0011022

theorem demoR1_1011022 : invRung 7 5 20 [1, 0, 1, 1, 0, 2, 2] [1, 0, 1, 1, 0, 2, 2] 1 2 false = ([0, 1, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_1011022 : invRung 7 5 20 [1, 0, 1, 1, 0, 2, 2] [0, 1, 2, 1, 2, 2, 2] 3 1 true = ([0, 2, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_1011022 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 0, 0] = [1, 1, 1, 0, 0, 2, 0] := by
  decide

theorem demoM_1011022 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 2, 0] [1, 0, 1, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011022 : mirrorTrits [1, 1, 1, 0, 0, 2, 0] = [2, 2, 2, 0, 0, 1, 0] := by
  decide

theorem demoInv_1011022 : specInv 7 5 20 [1, 0, 1, 1, 0, 2, 2] = some [2, 2, 2, 0, 0, 1, 0] :=
  specInv_mirror_7 [1, 0, 1, 1, 0, 2, 2] [0, 1, 2, 1, 2, 2, 2] [0, 2, 2, 1, 1, 0, 0] [1, 1, 1, 0, 0, 2, 0] [2, 2, 2, 0, 0, 1, 0] demoR1_1011022 demoR2_1011022 demoC_1011022 demoM_1011022 demoMir_1011022

theorem demoR1_2011022 : invRung 7 5 20 [2, 0, 1, 1, 0, 2, 2] [2, 0, 1, 1, 0, 2, 2] 1 2 false = ([2, 1, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_2011022 : invRung 7 5 20 [2, 0, 1, 1, 0, 2, 2] [2, 1, 1, 1, 0, 1, 1] 3 1 true = ([2, 1, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_2011022 : fieldCube 7 5 20 [2, 1, 0, 1, 1, 1, 1] = [1, 0, 1, 0, 2, 1, 1] := by
  decide

theorem demoM_2011022 : fieldMul 7 5 20 [1, 0, 1, 0, 2, 1, 1] [2, 0, 1, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2011022 : specInv 7 5 20 [2, 0, 1, 1, 0, 2, 2] = some [1, 0, 1, 0, 2, 1, 1] :=
  specInv_white_7 [2, 0, 1, 1, 0, 2, 2] [2, 1, 1, 1, 0, 1, 1] [2, 1, 0, 1, 1, 1, 1] [1, 0, 1, 0, 2, 1, 1] demoR1_2011022 demoR2_2011022 demoC_2011022 demoM_2011022

theorem demoR1_0111022 : invRung 7 5 20 [0, 1, 1, 1, 0, 2, 2] [0, 1, 1, 1, 0, 2, 2] 1 2 false = ([0, 2, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_0111022 : invRung 7 5 20 [0, 1, 1, 1, 0, 2, 2] [0, 2, 2, 0, 0, 1, 0] 3 1 true = ([1, 0, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_0111022 : fieldCube 7 5 20 [1, 0, 2, 0, 0, 2, 2] = [0, 1, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_0111022 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 1, 2] [0, 1, 1, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111022 : mirrorTrits [0, 1, 0, 2, 1, 1, 2] = [0, 2, 0, 1, 2, 2, 1] := by
  decide

theorem demoInv_0111022 : specInv 7 5 20 [0, 1, 1, 1, 0, 2, 2] = some [0, 2, 0, 1, 2, 2, 1] :=
  specInv_mirror_7 [0, 1, 1, 1, 0, 2, 2] [0, 2, 2, 0, 0, 1, 0] [1, 0, 2, 0, 0, 2, 2] [0, 1, 0, 2, 1, 1, 2] [0, 2, 0, 1, 2, 2, 1] demoR1_0111022 demoR2_0111022 demoC_0111022 demoM_0111022 demoMir_0111022

theorem demoR1_1111022 : invRung 7 5 20 [1, 1, 1, 1, 0, 2, 2] [1, 1, 1, 1, 0, 2, 2] 1 2 false = ([1, 0, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1111022 : invRung 7 5 20 [1, 1, 1, 1, 0, 2, 2] [1, 0, 0, 1, 0, 0, 1] 3 1 true = ([2, 2, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_1111022 : fieldCube 7 5 20 [2, 2, 2, 1, 0, 2, 2] = [2, 1, 1, 1, 1, 2, 2] := by
  decide

theorem demoM_1111022 : fieldMul 7 5 20 [2, 1, 1, 1, 1, 2, 2] [1, 1, 1, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1111022 : specInv 7 5 20 [1, 1, 1, 1, 0, 2, 2] = some [2, 1, 1, 1, 1, 2, 2] :=
  specInv_white_7 [1, 1, 1, 1, 0, 2, 2] [1, 0, 0, 1, 0, 0, 1] [2, 2, 2, 1, 0, 2, 2] [2, 1, 1, 1, 1, 2, 2] demoR1_1111022 demoR2_1111022 demoC_1111022 demoM_1111022

theorem demoR1_2111022 : invRung 7 5 20 [2, 1, 1, 1, 0, 2, 2] [2, 1, 1, 1, 0, 2, 2] 1 2 false = ([0, 1, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2111022 : invRung 7 5 20 [2, 1, 1, 1, 0, 2, 2] [0, 1, 1, 1, 2, 0, 1] 3 1 true = ([0, 2, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_2111022 : fieldCube 7 5 20 [0, 2, 1, 2, 0, 0, 2] = [2, 2, 0, 1, 2, 1, 0] := by
  decide

theorem demoM_2111022 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 1, 0] [2, 1, 1, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2111022 : specInv 7 5 20 [2, 1, 1, 1, 0, 2, 2] = some [2, 2, 0, 1, 2, 1, 0] :=
  specInv_white_7 [2, 1, 1, 1, 0, 2, 2] [0, 1, 1, 1, 2, 0, 1] [0, 2, 1, 2, 0, 0, 2] [2, 2, 0, 1, 2, 1, 0] demoR1_2111022 demoR2_2111022 demoC_2111022 demoM_2111022

theorem demoR1_0211022 : invRung 7 5 20 [0, 2, 1, 1, 0, 2, 2] [0, 2, 1, 1, 0, 2, 2] 1 2 false = ([0, 0, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0211022 : invRung 7 5 20 [0, 2, 1, 1, 0, 2, 2] [0, 0, 2, 2, 1, 2, 1] 3 1 true = ([2, 1, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0211022 : fieldCube 7 5 20 [2, 1, 0, 1, 2, 1, 2] = [1, 2, 0, 2, 0, 0, 0] := by
  decide

theorem demoM_0211022 : fieldMul 7 5 20 [1, 2, 0, 2, 0, 0, 0] [0, 2, 1, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211022 : mirrorTrits [1, 2, 0, 2, 0, 0, 0] = [2, 1, 0, 1, 0, 0, 0] := by
  decide

theorem demoInv_0211022 : specInv 7 5 20 [0, 2, 1, 1, 0, 2, 2] = some [2, 1, 0, 1, 0, 0, 0] :=
  specInv_mirror_7 [0, 2, 1, 1, 0, 2, 2] [0, 0, 2, 2, 1, 2, 1] [2, 1, 0, 1, 2, 1, 2] [1, 2, 0, 2, 0, 0, 0] [2, 1, 0, 1, 0, 0, 0] demoR1_0211022 demoR2_0211022 demoC_0211022 demoM_0211022 demoMir_0211022

theorem demoR1_1211022 : invRung 7 5 20 [1, 2, 1, 1, 0, 2, 2] [1, 2, 1, 1, 0, 2, 2] 1 2 false = ([2, 1, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_1211022 : invRung 7 5 20 [1, 2, 1, 1, 0, 2, 2] [2, 1, 0, 2, 1, 2, 1] 3 1 true = ([0, 0, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_1211022 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 1, 2] = [0, 2, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_1211022 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 1, 1] [1, 2, 1, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1211022 : specInv 7 5 20 [1, 2, 1, 1, 0, 2, 2] = some [0, 2, 1, 1, 0, 1, 1] :=
  specInv_white_7 [1, 2, 1, 1, 0, 2, 2] [2, 1, 0, 2, 1, 2, 1] [0, 0, 1, 2, 2, 1, 2] [0, 2, 1, 1, 0, 1, 1] demoR1_1211022 demoR2_1211022 demoC_1211022 demoM_1211022

theorem demoR1_2211022 : invRung 7 5 20 [2, 2, 1, 1, 0, 2, 2] [2, 2, 1, 1, 0, 2, 2] 1 2 false = ([1, 1, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_2211022 : invRung 7 5 20 [2, 2, 1, 1, 0, 2, 2] [1, 1, 0, 0, 0, 2, 0] 3 1 true = ([0, 1, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2211022 : fieldCube 7 5 20 [0, 1, 0, 2, 0, 1, 0] = [0, 1, 0, 1, 1, 0, 2] := by
  decide

theorem demoM_2211022 : fieldMul 7 5 20 [0, 1, 0, 1, 1, 0, 2] [2, 2, 1, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211022 : mirrorTrits [0, 1, 0, 1, 1, 0, 2] = [0, 2, 0, 2, 2, 0, 1] := by
  decide

theorem demoInv_2211022 : specInv 7 5 20 [2, 2, 1, 1, 0, 2, 2] = some [0, 2, 0, 2, 2, 0, 1] :=
  specInv_mirror_7 [2, 2, 1, 1, 0, 2, 2] [1, 1, 0, 0, 0, 2, 0] [0, 1, 0, 2, 0, 1, 0] [0, 1, 0, 1, 1, 0, 2] [0, 2, 0, 2, 2, 0, 1] demoR1_2211022 demoR2_2211022 demoC_2211022 demoM_2211022 demoMir_2211022

theorem demoR1_0021022 : invRung 7 5 20 [0, 0, 2, 1, 0, 2, 2] [0, 0, 2, 1, 0, 2, 2] 1 2 false = ([2, 0, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_0021022 : invRung 7 5 20 [0, 0, 2, 1, 0, 2, 2] [2, 0, 0, 1, 0, 2, 2] 3 1 true = ([1, 2, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0021022 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 1, 2] = [1, 1, 1, 2, 0, 0, 0] := by
  decide

theorem demoM_0021022 : fieldMul 7 5 20 [1, 1, 1, 2, 0, 0, 0] [0, 0, 2, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021022 : mirrorTrits [1, 1, 1, 2, 0, 0, 0] = [2, 2, 2, 1, 0, 0, 0] := by
  decide

theorem demoInv_0021022 : specInv 7 5 20 [0, 0, 2, 1, 0, 2, 2] = some [2, 2, 2, 1, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 2, 1, 0, 2, 2] [2, 0, 0, 1, 0, 2, 2] [1, 2, 1, 2, 1, 1, 2] [1, 1, 1, 2, 0, 0, 0] [2, 2, 2, 1, 0, 0, 0] demoR1_0021022 demoR2_0021022 demoC_0021022 demoM_0021022 demoMir_0021022

theorem demoR1_1021022 : invRung 7 5 20 [1, 0, 2, 1, 0, 2, 2] [1, 0, 2, 1, 0, 2, 2] 1 2 false = ([0, 0, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1021022 : invRung 7 5 20 [1, 0, 2, 1, 0, 2, 2] [0, 0, 2, 1, 0, 0, 1] 3 1 true = ([0, 2, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_1021022 : fieldCube 7 5 20 [0, 2, 1, 2, 2, 0, 1] = [2, 0, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_1021022 : fieldMul 7 5 20 [2, 0, 1, 2, 1, 2, 1] [1, 0, 2, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1021022 : specInv 7 5 20 [1, 0, 2, 1, 0, 2, 2] = some [2, 0, 1, 2, 1, 2, 1] :=
  specInv_white_7 [1, 0, 2, 1, 0, 2, 2] [0, 0, 2, 1, 0, 0, 1] [0, 2, 1, 2, 2, 0, 1] [2, 0, 1, 2, 1, 2, 1] demoR1_1021022 demoR2_1021022 demoC_1021022 demoM_1021022

theorem demoR1_2021022 : invRung 7 5 20 [2, 0, 2, 1, 0, 2, 2] [2, 0, 2, 1, 0, 2, 2] 1 2 false = ([0, 0, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_2021022 : invRung 7 5 20 [2, 0, 2, 1, 0, 2, 2] [0, 0, 2, 0, 1, 2, 0] 3 1 true = ([2, 2, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_2021022 : fieldCube 7 5 20 [2, 2, 1, 0, 0, 2, 0] = [1, 2, 2, 2, 2, 2, 2] := by
  decide

theorem demoM_2021022 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 2, 2] [2, 0, 2, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2021022 : specInv 7 5 20 [2, 0, 2, 1, 0, 2, 2] = some [1, 2, 2, 2, 2, 2, 2] :=
  specInv_white_7 [2, 0, 2, 1, 0, 2, 2] [0, 0, 2, 0, 1, 2, 0] [2, 2, 1, 0, 0, 2, 0] [1, 2, 2, 2, 2, 2, 2] demoR1_2021022 demoR2_2021022 demoC_2021022 demoM_2021022

theorem demoR1_0121022 : invRung 7 5 20 [0, 1, 2, 1, 0, 2, 2] [0, 1, 2, 1, 0, 2, 2] 1 2 false = ([0, 2, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_0121022 : invRung 7 5 20 [0, 1, 2, 1, 0, 2, 2] [0, 2, 2, 2, 0, 0, 2] 3 1 true = ([2, 2, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0121022 : fieldCube 7 5 20 [2, 2, 0, 1, 0, 0, 0] = [0, 0, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_0121022 : fieldMul 7 5 20 [0, 0, 1, 2, 0, 1, 0] [0, 1, 2, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0121022 : specInv 7 5 20 [0, 1, 2, 1, 0, 2, 2] = some [0, 0, 1, 2, 0, 1, 0] :=
  specInv_white_7 [0, 1, 2, 1, 0, 2, 2] [0, 2, 2, 2, 0, 0, 2] [2, 2, 0, 1, 0, 0, 0] [0, 0, 1, 2, 0, 1, 0] demoR1_0121022 demoR2_0121022 demoC_0121022 demoM_0121022

theorem demoR1_1121022 : invRung 7 5 20 [1, 1, 2, 1, 0, 2, 2] [1, 1, 2, 1, 0, 2, 2] 1 2 false = ([2, 0, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1121022 : invRung 7 5 20 [1, 1, 2, 1, 0, 2, 2] [2, 0, 2, 2, 2, 1, 1] 3 1 true = ([1, 0, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_1121022 : fieldCube 7 5 20 [1, 0, 0, 0, 2, 0, 0] = [1, 2, 0, 2, 0, 2, 2] := by
  decide

theorem demoM_1121022 : fieldMul 7 5 20 [1, 2, 0, 2, 0, 2, 2] [1, 1, 2, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1121022 : specInv 7 5 20 [1, 1, 2, 1, 0, 2, 2] = some [1, 2, 0, 2, 0, 2, 2] :=
  specInv_white_7 [1, 1, 2, 1, 0, 2, 2] [2, 0, 2, 2, 2, 1, 1] [1, 0, 0, 0, 2, 0, 0] [1, 2, 0, 2, 0, 2, 2] demoR1_1121022 demoR2_1121022 demoC_1121022 demoM_1121022

theorem demoR1_2121022 : invRung 7 5 20 [2, 1, 2, 1, 0, 2, 2] [2, 1, 2, 1, 0, 2, 2] 1 2 false = ([2, 0, 2, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2121022 : invRung 7 5 20 [2, 1, 2, 1, 0, 2, 2] [2, 0, 2, 0, 2, 2, 0] 3 1 true = ([0, 2, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_2121022 : fieldCube 7 5 20 [0, 2, 0, 1, 2, 0, 2] = [1, 1, 2, 0, 2, 2, 1] := by
  decide

theorem demoM_2121022 : fieldMul 7 5 20 [1, 1, 2, 0, 2, 2, 1] [2, 1, 2, 1, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2121022 : mirrorTrits [1, 1, 2, 0, 2, 2, 1] = [2, 2, 1, 0, 1, 1, 2] := by
  decide

theorem demoInv_2121022 : specInv 7 5 20 [2, 1, 2, 1, 0, 2, 2] = some [2, 2, 1, 0, 1, 1, 2] :=
  specInv_mirror_7 [2, 1, 2, 1, 0, 2, 2] [2, 0, 2, 0, 2, 2, 0] [0, 2, 0, 1, 2, 0, 2] [1, 1, 2, 0, 2, 2, 1] [2, 2, 1, 0, 1, 1, 2] demoR1_2121022 demoR2_2121022 demoC_2121022 demoM_2121022 demoMir_2121022

theorem demoR1_0221022 : invRung 7 5 20 [0, 2, 2, 1, 0, 2, 2] [0, 2, 2, 1, 0, 2, 2] 1 2 false = ([2, 1, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_0221022 : invRung 7 5 20 [0, 2, 2, 1, 0, 2, 2] [2, 1, 1, 0, 1, 1, 2] 3 1 true = ([2, 0, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_0221022 : fieldCube 7 5 20 [2, 0, 0, 2, 1, 0, 0] = [1, 1, 2, 1, 0, 0, 1] := by
  decide

theorem demoM_0221022 : fieldMul 7 5 20 [1, 1, 2, 1, 0, 0, 1] [0, 2, 2, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0221022 : specInv 7 5 20 [0, 2, 2, 1, 0, 2, 2] = some [1, 1, 2, 1, 0, 0, 1] :=
  specInv_white_7 [0, 2, 2, 1, 0, 2, 2] [2, 1, 1, 0, 1, 1, 2] [2, 0, 0, 2, 1, 0, 0] [1, 1, 2, 1, 0, 0, 1] demoR1_0221022 demoR2_0221022 demoC_0221022 demoM_0221022

theorem demoR1_1221022 : invRung 7 5 20 [1, 2, 2, 1, 0, 2, 2] [1, 2, 2, 1, 0, 2, 2] 1 2 false = ([2, 1, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_1221022 : invRung 7 5 20 [1, 2, 2, 1, 0, 2, 2] [2, 1, 2, 1, 1, 1, 2] 3 1 true = ([1, 0, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_1221022 : fieldCube 7 5 20 [1, 0, 2, 2, 0, 0, 0] = [0, 0, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_1221022 : fieldMul 7 5 20 [0, 0, 2, 0, 0, 2, 2] [1, 2, 2, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1221022 : specInv 7 5 20 [1, 2, 2, 1, 0, 2, 2] = some [0, 0, 2, 0, 0, 2, 2] :=
  specInv_white_7 [1, 2, 2, 1, 0, 2, 2] [2, 1, 2, 1, 1, 1, 2] [1, 0, 2, 2, 0, 0, 0] [0, 0, 2, 0, 0, 2, 2] demoR1_1221022 demoR2_1221022 demoC_1221022 demoM_1221022

theorem demoR1_2221022 : invRung 7 5 20 [2, 2, 2, 1, 0, 2, 2] [2, 2, 2, 1, 0, 2, 2] 1 2 false = ([2, 2, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_2221022 : invRung 7 5 20 [2, 2, 2, 1, 0, 2, 2] [2, 2, 2, 2, 2, 0, 2] 3 1 true = ([2, 2, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_2221022 : fieldCube 7 5 20 [2, 2, 2, 0, 2, 1, 0] = [0, 0, 1, 1, 1, 0, 0] := by
  decide

theorem demoM_2221022 : fieldMul 7 5 20 [0, 0, 1, 1, 1, 0, 0] [2, 2, 2, 1, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2221022 : specInv 7 5 20 [2, 2, 2, 1, 0, 2, 2] = some [0, 0, 1, 1, 1, 0, 0] :=
  specInv_white_7 [2, 2, 2, 1, 0, 2, 2] [2, 2, 2, 2, 2, 0, 2] [2, 2, 2, 0, 2, 1, 0] [0, 0, 1, 1, 1, 0, 0] demoR1_2221022 demoR2_2221022 demoC_2221022 demoM_2221022

theorem demoR1_0002022 : invRung 7 5 20 [0, 0, 0, 2, 0, 2, 2] [0, 0, 0, 2, 0, 2, 2] 1 2 false = ([2, 0, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0002022 : invRung 7 5 20 [0, 0, 0, 2, 0, 2, 2] [2, 0, 2, 0, 0, 0, 0] 3 1 true = ([1, 0, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_0002022 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 2, 2] = [0, 1, 0, 2, 1, 1, 1] := by
  decide

theorem demoM_0002022 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 1, 1] [0, 0, 0, 2, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0002022 : specInv 7 5 20 [0, 0, 0, 2, 0, 2, 2] = some [0, 1, 0, 2, 1, 1, 1] :=
  specInv_white_7 [0, 0, 0, 2, 0, 2, 2] [2, 0, 2, 0, 0, 0, 0] [1, 0, 1, 0, 0, 2, 2] [0, 1, 0, 2, 1, 1, 1] demoR1_0002022 demoR2_0002022 demoC_0002022 demoM_0002022

theorem demoR1_1002022 : invRung 7 5 20 [1, 0, 0, 2, 0, 2, 2] [1, 0, 0, 2, 0, 2, 2] 1 2 false = ([0, 0, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1002022 : invRung 7 5 20 [1, 0, 0, 2, 0, 2, 2] [0, 0, 1, 1, 1, 2, 1] 3 1 true = ([2, 2, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_1002022 : fieldCube 7 5 20 [2, 2, 1, 1, 2, 0, 2] = [0, 1, 2, 0, 2, 2, 2] := by
  decide

theorem demoM_1002022 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 2, 2] [1, 0, 0, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002022 : mirrorTrits [0, 1, 2, 0, 2, 2, 2] = [0, 2, 1, 0, 1, 1, 1] := by
  decide

theorem demoInv_1002022 : specInv 7 5 20 [1, 0, 0, 2, 0, 2, 2] = some [0, 2, 1, 0, 1, 1, 1] :=
  specInv_mirror_7 [1, 0, 0, 2, 0, 2, 2] [0, 0, 1, 1, 1, 2, 1] [2, 2, 1, 1, 2, 0, 2] [0, 1, 2, 0, 2, 2, 2] [0, 2, 1, 0, 1, 1, 1] demoR1_1002022 demoR2_1002022 demoC_1002022 demoM_1002022 demoMir_1002022

theorem demoR1_2002022 : invRung 7 5 20 [2, 0, 0, 2, 0, 2, 2] [2, 0, 0, 2, 0, 2, 2] 1 2 false = ([0, 1, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_2002022 : invRung 7 5 20 [2, 0, 0, 2, 0, 2, 2] [0, 1, 2, 2, 1, 2, 0] 3 1 true = ([1, 2, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2002022 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 1, 0] = [2, 2, 1, 0, 1, 2, 1] := by
  decide

theorem demoM_2002022 : fieldMul 7 5 20 [2, 2, 1, 0, 1, 2, 1] [2, 0, 0, 2, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2002022 : specInv 7 5 20 [2, 0, 0, 2, 0, 2, 2] = some [2, 2, 1, 0, 1, 2, 1] :=
  specInv_white_7 [2, 0, 0, 2, 0, 2, 2] [0, 1, 2, 2, 1, 2, 0] [1, 2, 1, 0, 1, 1, 0] [2, 2, 1, 0, 1, 2, 1] demoR1_2002022 demoR2_2002022 demoC_2002022 demoM_2002022

theorem demoR1_0102022 : invRung 7 5 20 [0, 1, 0, 2, 0, 2, 2] [0, 1, 0, 2, 0, 2, 2] 1 2 false = ([2, 2, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_0102022 : invRung 7 5 20 [0, 1, 0, 2, 0, 2, 2] [2, 2, 0, 1, 2, 0, 1] 3 1 true = ([1, 1, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0102022 : fieldCube 7 5 20 [1, 1, 2, 1, 2, 2, 2] = [1, 0, 1, 2, 1, 1, 1] := by
  decide

theorem demoM_0102022 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 1, 1] [0, 1, 0, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102022 : mirrorTrits [1, 0, 1, 2, 1, 1, 1] = [2, 0, 2, 1, 2, 2, 2] := by
  decide

theorem demoInv_0102022 : specInv 7 5 20 [0, 1, 0, 2, 0, 2, 2] = some [2, 0, 2, 1, 2, 2, 2] :=
  specInv_mirror_7 [0, 1, 0, 2, 0, 2, 2] [2, 2, 0, 1, 2, 0, 1] [1, 1, 2, 1, 2, 2, 2] [1, 0, 1, 2, 1, 1, 1] [2, 0, 2, 1, 2, 2, 2] demoR1_0102022 demoR2_0102022 demoC_0102022 demoM_0102022 demoMir_0102022

theorem demoR1_1102022 : invRung 7 5 20 [1, 1, 0, 2, 0, 2, 2] [1, 1, 0, 2, 0, 2, 2] 1 2 false = ([2, 2, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1102022 : invRung 7 5 20 [1, 1, 0, 2, 0, 2, 2] [2, 2, 1, 1, 2, 2, 1] 3 1 true = ([0, 0, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_1102022 : fieldCube 7 5 20 [0, 0, 1, 1, 1, 0, 2] = [1, 0, 2, 0, 2, 1, 1] := by
  decide

theorem demoM_1102022 : fieldMul 7 5 20 [1, 0, 2, 0, 2, 1, 1] [1, 1, 0, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102022 : mirrorTrits [1, 0, 2, 0, 2, 1, 1] = [2, 0, 1, 0, 1, 2, 2] := by
  decide

theorem demoInv_1102022 : specInv 7 5 20 [1, 1, 0, 2, 0, 2, 2] = some [2, 0, 1, 0, 1, 2, 2] :=
  specInv_mirror_7 [1, 1, 0, 2, 0, 2, 2] [2, 2, 1, 1, 2, 2, 1] [0, 0, 1, 1, 1, 0, 2] [1, 0, 2, 0, 2, 1, 1] [2, 0, 1, 0, 1, 2, 2] demoR1_1102022 demoR2_1102022 demoC_1102022 demoM_1102022 demoMir_1102022

theorem demoR1_2102022 : invRung 7 5 20 [2, 1, 0, 2, 0, 2, 2] [2, 1, 0, 2, 0, 2, 2] 1 2 false = ([0, 2, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2102022 : invRung 7 5 20 [2, 1, 0, 2, 0, 2, 2] [0, 2, 0, 0, 1, 1, 2] 3 1 true = ([2, 0, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_2102022 : fieldCube 7 5 20 [2, 0, 2, 1, 0, 0, 2] = [0, 2, 2, 2, 2, 0, 1] := by
  decide

theorem demoM_2102022 : fieldMul 7 5 20 [0, 2, 2, 2, 2, 0, 1] [2, 1, 0, 2, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2102022 : specInv 7 5 20 [2, 1, 0, 2, 0, 2, 2] = some [0, 2, 2, 2, 2, 0, 1] :=
  specInv_white_7 [2, 1, 0, 2, 0, 2, 2] [0, 2, 0, 0, 1, 1, 2] [2, 0, 2, 1, 0, 0, 2] [0, 2, 2, 2, 2, 0, 1] demoR1_2102022 demoR2_2102022 demoC_2102022 demoM_2102022

theorem demoR1_0202022 : invRung 7 5 20 [0, 2, 0, 2, 0, 2, 2] [0, 2, 0, 2, 0, 2, 2] 1 2 false = ([1, 1, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_0202022 : invRung 7 5 20 [0, 2, 0, 2, 0, 2, 2] [1, 1, 2, 0, 1, 2, 0] 3 1 true = ([0, 2, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0202022 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 0, 0] = [1, 0, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_0202022 : fieldMul 7 5 20 [1, 0, 1, 2, 0, 1, 0] [0, 2, 0, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202022 : mirrorTrits [1, 0, 1, 2, 0, 1, 0] = [2, 0, 2, 1, 0, 2, 0] := by
  decide

theorem demoInv_0202022 : specInv 7 5 20 [0, 2, 0, 2, 0, 2, 2] = some [2, 0, 2, 1, 0, 2, 0] :=
  specInv_mirror_7 [0, 2, 0, 2, 0, 2, 2] [1, 1, 2, 0, 1, 2, 0] [0, 2, 0, 1, 0, 0, 0] [1, 0, 1, 2, 0, 1, 0] [2, 0, 2, 1, 0, 2, 0] demoR1_0202022 demoR2_0202022 demoC_0202022 demoM_0202022 demoMir_0202022

theorem demoR1_1202022 : invRung 7 5 20 [1, 2, 0, 2, 0, 2, 2] [1, 2, 0, 2, 0, 2, 2] 1 2 false = ([0, 2, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_1202022 : invRung 7 5 20 [1, 2, 0, 2, 0, 2, 2] [0, 2, 2, 0, 2, 0, 0] 3 1 true = ([1, 2, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1202022 : fieldCube 7 5 20 [1, 2, 2, 1, 1, 2, 1] = [1, 1, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_1202022 : fieldMul 7 5 20 [1, 1, 2, 1, 0, 2, 2] [1, 2, 0, 2, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1202022 : specInv 7 5 20 [1, 2, 0, 2, 0, 2, 2] = some [1, 1, 2, 1, 0, 2, 2] :=
  specInv_white_7 [1, 2, 0, 2, 0, 2, 2] [0, 2, 2, 0, 2, 0, 0] [1, 2, 2, 1, 1, 2, 1] [1, 1, 2, 1, 0, 2, 2] demoR1_1202022 demoR2_1202022 demoC_1202022 demoM_1202022

theorem demoR1_2202022 : invRung 7 5 20 [2, 2, 0, 2, 0, 2, 2] [2, 2, 0, 2, 0, 2, 2] 1 2 false = ([2, 2, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2202022 : invRung 7 5 20 [2, 2, 0, 2, 0, 2, 2] [2, 2, 2, 1, 2, 0, 1] 3 1 true = ([2, 1, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_2202022 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 0, 1] = [1, 2, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_2202022 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 1, 2] [2, 2, 0, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202022 : mirrorTrits [1, 2, 1, 0, 1, 1, 2] = [2, 1, 2, 0, 2, 2, 1] := by
  decide

theorem demoInv_2202022 : specInv 7 5 20 [2, 2, 0, 2, 0, 2, 2] = some [2, 1, 2, 0, 2, 2, 1] :=
  specInv_mirror_7 [2, 2, 0, 2, 0, 2, 2] [2, 2, 2, 1, 2, 0, 1] [2, 1, 0, 2, 1, 0, 1] [1, 2, 1, 0, 1, 1, 2] [2, 1, 2, 0, 2, 2, 1] demoR1_2202022 demoR2_2202022 demoC_2202022 demoM_2202022 demoMir_2202022

theorem demoR1_0012022 : invRung 7 5 20 [0, 0, 1, 2, 0, 2, 2] [0, 0, 1, 2, 0, 2, 2] 1 2 false = ([2, 1, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_0012022 : invRung 7 5 20 [0, 0, 1, 2, 0, 2, 2] [2, 1, 0, 2, 0, 2, 0] 3 1 true = ([0, 2, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_0012022 : fieldCube 7 5 20 [0, 2, 2, 1, 2, 1, 1] = [2, 1, 1, 2, 2, 2, 1] := by
  decide

theorem demoM_0012022 : fieldMul 7 5 20 [2, 1, 1, 2, 2, 2, 1] [0, 0, 1, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0012022 : mirrorTrits [2, 1, 1, 2, 2, 2, 1] = [1, 2, 2, 1, 1, 1, 2] := by
  decide

theorem demoInv_0012022 : specInv 7 5 20 [0, 0, 1, 2, 0, 2, 2] = some [1, 2, 2, 1, 1, 1, 2] :=
  specInv_mirror_7 [0, 0, 1, 2, 0, 2, 2] [2, 1, 0, 2, 0, 2, 0] [0, 2, 2, 1, 2, 1, 1] [2, 1, 1, 2, 2, 2, 1] [1, 2, 2, 1, 1, 1, 2] demoR1_0012022 demoR2_0012022 demoC_0012022 demoM_0012022 demoMir_0012022

theorem demoR1_1012022 : invRung 7 5 20 [1, 0, 1, 2, 0, 2, 2] [1, 0, 1, 2, 0, 2, 2] 1 2 false = ([2, 0, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1012022 : invRung 7 5 20 [1, 0, 1, 2, 0, 2, 2] [2, 0, 0, 2, 1, 0, 2] 3 1 true = ([2, 1, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_1012022 : fieldCube 7 5 20 [2, 1, 0, 2, 0, 0, 1] = [1, 1, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_1012022 : fieldMul 7 5 20 [1, 1, 1, 2, 1, 0, 1] [1, 0, 1, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1012022 : mirrorTrits [1, 1, 1, 2, 1, 0, 1] = [2, 2, 2, 1, 2, 0, 2] := by
  decide

theorem demoInv_1012022 : specInv 7 5 20 [1, 0, 1, 2, 0, 2, 2] = some [2, 2, 2, 1, 2, 0, 2] :=
  specInv_mirror_7 [1, 0, 1, 2, 0, 2, 2] [2, 0, 0, 2, 1, 0, 2] [2, 1, 0, 2, 0, 0, 1] [1, 1, 1, 2, 1, 0, 1] [2, 2, 2, 1, 2, 0, 2] demoR1_1012022 demoR2_1012022 demoC_1012022 demoM_1012022 demoMir_1012022

theorem demoR1_2012022 : invRung 7 5 20 [2, 0, 1, 2, 0, 2, 2] [2, 0, 1, 2, 0, 2, 2] 1 2 false = ([1, 2, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_2012022 : invRung 7 5 20 [2, 0, 1, 2, 0, 2, 2] [1, 2, 2, 1, 0, 1, 0] 3 1 true = ([0, 0, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_2012022 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 1, 2] = [1, 2, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_2012022 : fieldMul 7 5 20 [1, 2, 2, 1, 0, 2, 1] [2, 0, 1, 2, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2012022 : specInv 7 5 20 [2, 0, 1, 2, 0, 2, 2] = some [1, 2, 2, 1, 0, 2, 1] :=
  specInv_white_7 [2, 0, 1, 2, 0, 2, 2] [1, 2, 2, 1, 0, 1, 0] [0, 0, 1, 0, 2, 1, 2] [1, 2, 2, 1, 0, 2, 1] demoR1_2012022 demoR2_2012022 demoC_2012022 demoM_2012022

theorem demoR1_0112022 : invRung 7 5 20 [0, 1, 1, 2, 0, 2, 2] [0, 1, 1, 2, 0, 2, 2] 1 2 false = ([1, 2, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_0112022 : invRung 7 5 20 [0, 1, 1, 2, 0, 2, 2] [1, 2, 2, 1, 2, 1, 1] 3 1 true = ([0, 2, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_0112022 : fieldCube 7 5 20 [0, 2, 0, 2, 1, 1, 0] = [0, 2, 0, 0, 1, 1, 0] := by
  decide

theorem demoM_0112022 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 1, 0] [0, 1, 1, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112022 : mirrorTrits [0, 2, 0, 0, 1, 1, 0] = [0, 1, 0, 0, 2, 2, 0] := by
  decide

theorem demoInv_0112022 : specInv 7 5 20 [0, 1, 1, 2, 0, 2, 2] = some [0, 1, 0, 0, 2, 2, 0] :=
  specInv_mirror_7 [0, 1, 1, 2, 0, 2, 2] [1, 2, 2, 1, 2, 1, 1] [0, 2, 0, 2, 1, 1, 0] [0, 2, 0, 0, 1, 1, 0] [0, 1, 0, 0, 2, 2, 0] demoR1_0112022 demoR2_0112022 demoC_0112022 demoM_0112022 demoMir_0112022

theorem demoR1_1112022 : invRung 7 5 20 [1, 1, 1, 2, 0, 2, 2] [1, 1, 1, 2, 0, 2, 2] 1 2 false = ([0, 0, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1112022 : invRung 7 5 20 [1, 1, 1, 2, 0, 2, 2] [0, 0, 2, 2, 0, 0, 1] 3 1 true = ([2, 0, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1112022 : fieldCube 7 5 20 [2, 0, 1, 0, 0, 1, 0] = [0, 1, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_1112022 : fieldMul 7 5 20 [0, 1, 1, 0, 1, 1, 0] [1, 1, 1, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112022 : mirrorTrits [0, 1, 1, 0, 1, 1, 0] = [0, 2, 2, 0, 2, 2, 0] := by
  decide

theorem demoInv_1112022 : specInv 7 5 20 [1, 1, 1, 2, 0, 2, 2] = some [0, 2, 2, 0, 2, 2, 0] :=
  specInv_mirror_7 [1, 1, 1, 2, 0, 2, 2] [0, 0, 2, 2, 0, 0, 1] [2, 0, 1, 0, 0, 1, 0] [0, 1, 1, 0, 1, 1, 0] [0, 2, 2, 0, 2, 2, 0] demoR1_1112022 demoR2_1112022 demoC_1112022 demoM_1112022 demoMir_1112022

theorem demoR1_2112022 : invRung 7 5 20 [2, 1, 1, 2, 0, 2, 2] [2, 1, 1, 2, 0, 2, 2] 1 2 false = ([0, 0, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_2112022 : invRung 7 5 20 [2, 1, 1, 2, 0, 2, 2] [0, 0, 0, 1, 2, 1, 0] 3 1 true = ([1, 1, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_2112022 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 1, 0] = [0, 1, 2, 1, 1, 2, 2] := by
  decide

theorem demoM_2112022 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 2, 2] [2, 1, 1, 2, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2112022 : specInv 7 5 20 [2, 1, 1, 2, 0, 2, 2] = some [0, 1, 2, 1, 1, 2, 2] :=
  specInv_white_7 [2, 1, 1, 2, 0, 2, 2] [0, 0, 0, 1, 2, 1, 0] [1, 1, 0, 1, 0, 1, 0] [0, 1, 2, 1, 1, 2, 2] demoR1_2112022 demoR2_2112022 demoC_2112022 demoM_2112022

theorem demoR1_0212022 : invRung 7 5 20 [0, 2, 1, 2, 0, 2, 2] [0, 2, 1, 2, 0, 2, 2] 1 2 false = ([0, 2, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_0212022 : invRung 7 5 20 [0, 2, 1, 2, 0, 2, 2] [0, 2, 0, 1, 1, 0, 0] 3 1 true = ([2, 1, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_0212022 : fieldCube 7 5 20 [2, 1, 0, 1, 2, 1, 0] = [1, 0, 2, 0, 1, 1, 1] := by
  decide

theorem demoM_0212022 : fieldMul 7 5 20 [1, 0, 2, 0, 1, 1, 1] [0, 2, 1, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212022 : mirrorTrits [1, 0, 2, 0, 1, 1, 1] = [2, 0, 1, 0, 2, 2, 2] := by
  decide

theorem demoInv_0212022 : specInv 7 5 20 [0, 2, 1, 2, 0, 2, 2] = some [2, 0, 1, 0, 2, 2, 2] :=
  specInv_mirror_7 [0, 2, 1, 2, 0, 2, 2] [0, 2, 0, 1, 1, 0, 0] [2, 1, 0, 1, 2, 1, 0] [1, 0, 2, 0, 1, 1, 1] [2, 0, 1, 0, 2, 2, 2] demoR1_0212022 demoR2_0212022 demoC_0212022 demoM_0212022 demoMir_0212022

theorem demoR1_1212022 : invRung 7 5 20 [1, 2, 1, 2, 0, 2, 2] [1, 2, 1, 2, 0, 2, 2] 1 2 false = ([1, 0, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_1212022 : invRung 7 5 20 [1, 2, 1, 2, 0, 2, 2] [1, 0, 0, 1, 1, 2, 2] 3 1 true = ([1, 0, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_1212022 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 2, 0] = [1, 0, 0, 1, 2, 1, 0] := by
  decide

theorem demoM_1212022 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 1, 0] [1, 2, 1, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212022 : mirrorTrits [1, 0, 0, 1, 2, 1, 0] = [2, 0, 0, 2, 1, 2, 0] := by
  decide

theorem demoInv_1212022 : specInv 7 5 20 [1, 2, 1, 2, 0, 2, 2] = some [2, 0, 0, 2, 1, 2, 0] :=
  specInv_mirror_7 [1, 2, 1, 2, 0, 2, 2] [1, 0, 0, 1, 1, 2, 2] [1, 0, 1, 1, 1, 2, 0] [1, 0, 0, 1, 2, 1, 0] [2, 0, 0, 2, 1, 2, 0] demoR1_1212022 demoR2_1212022 demoC_1212022 demoM_1212022 demoMir_1212022

theorem demoR1_2212022 : invRung 7 5 20 [2, 2, 1, 2, 0, 2, 2] [2, 2, 1, 2, 0, 2, 2] 1 2 false = ([2, 2, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_2212022 : invRung 7 5 20 [2, 2, 1, 2, 0, 2, 2] [2, 2, 0, 1, 2, 2, 0] 3 1 true = ([2, 2, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_2212022 : fieldCube 7 5 20 [2, 2, 0, 1, 1, 0, 0] = [0, 1, 1, 0, 0, 2, 1] := by
  decide

theorem demoM_2212022 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 2, 1] [2, 2, 1, 2, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2212022 : specInv 7 5 20 [2, 2, 1, 2, 0, 2, 2] = some [0, 1, 1, 0, 0, 2, 1] :=
  specInv_white_7 [2, 2, 1, 2, 0, 2, 2] [2, 2, 0, 1, 2, 2, 0] [2, 2, 0, 1, 1, 0, 0] [0, 1, 1, 0, 0, 2, 1] demoR1_2212022 demoR2_2212022 demoC_2212022 demoM_2212022

theorem demoR1_0022022 : invRung 7 5 20 [0, 0, 2, 2, 0, 2, 2] [0, 0, 2, 2, 0, 2, 2] 1 2 false = ([0, 0, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_0022022 : invRung 7 5 20 [0, 0, 2, 2, 0, 2, 2] [0, 0, 1, 1, 1, 2, 2] 3 1 true = ([1, 0, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_0022022 : fieldCube 7 5 20 [1, 0, 1, 2, 0, 2, 0] = [2, 2, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_0022022 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 1, 2] [0, 0, 2, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022022 : mirrorTrits [2, 2, 1, 0, 2, 1, 2] = [1, 1, 2, 0, 1, 2, 1] := by
  decide

theorem demoInv_0022022 : specInv 7 5 20 [0, 0, 2, 2, 0, 2, 2] = some [1, 1, 2, 0, 1, 2, 1] :=
  specInv_mirror_7 [0, 0, 2, 2, 0, 2, 2] [0, 0, 1, 1, 1, 2, 2] [1, 0, 1, 2, 0, 2, 0] [2, 2, 1, 0, 2, 1, 2] [1, 1, 2, 0, 1, 2, 1] demoR1_0022022 demoR2_0022022 demoC_0022022 demoM_0022022 demoMir_0022022

theorem demoR1_1022022 : invRung 7 5 20 [1, 0, 2, 2, 0, 2, 2] [1, 0, 2, 2, 0, 2, 2] 1 2 false = ([1, 1, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1022022 : invRung 7 5 20 [1, 0, 2, 2, 0, 2, 2] [1, 1, 0, 0, 2, 2, 1] 3 1 true = ([0, 2, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_1022022 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 0, 1] = [1, 1, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_1022022 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 2, 1] [1, 0, 2, 2, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1022022 : specInv 7 5 20 [1, 0, 2, 2, 0, 2, 2] = some [1, 1, 0, 0, 1, 2, 1] :=
  specInv_white_7 [1, 0, 2, 2, 0, 2, 2] [1, 1, 0, 0, 2, 2, 1] [0, 2, 0, 1, 0, 0, 1] [1, 1, 0, 0, 1, 2, 1] demoR1_1022022 demoR2_1022022 demoC_1022022 demoM_1022022

theorem demoR1_2022022 : invRung 7 5 20 [2, 0, 2, 2, 0, 2, 2] [2, 0, 2, 2, 0, 2, 2] 1 2 false = ([1, 1, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2022022 : invRung 7 5 20 [2, 0, 2, 2, 0, 2, 2] [1, 1, 1, 0, 0, 1, 0] 3 1 true = ([2, 2, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2022022 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 2, 2] = [0, 2, 2, 2, 1, 1, 0] := by
  decide

theorem demoM_2022022 : fieldMul 7 5 20 [0, 2, 2, 2, 1, 1, 0] [2, 0, 2, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022022 : mirrorTrits [0, 2, 2, 2, 1, 1, 0] = [0, 1, 1, 1, 2, 2, 0] := by
  decide

theorem demoInv_2022022 : specInv 7 5 20 [2, 0, 2, 2, 0, 2, 2] = some [0, 1, 1, 1, 2, 2, 0] :=
  specInv_mirror_7 [2, 0, 2, 2, 0, 2, 2] [1, 1, 1, 0, 0, 1, 0] [2, 2, 2, 2, 1, 2, 2] [0, 2, 2, 2, 1, 1, 0] [0, 1, 1, 1, 2, 2, 0] demoR1_2022022 demoR2_2022022 demoC_2022022 demoM_2022022 demoMir_2022022

theorem demoR1_0122022 : invRung 7 5 20 [0, 1, 2, 2, 0, 2, 2] [0, 1, 2, 2, 0, 2, 2] 1 2 false = ([1, 2, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0122022 : invRung 7 5 20 [0, 1, 2, 2, 0, 2, 2] [1, 2, 0, 0, 2, 2, 2] 3 1 true = ([2, 1, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_0122022 : fieldCube 7 5 20 [2, 1, 1, 0, 2, 2, 1] = [1, 2, 1, 1, 0, 2, 2] := by
  decide

theorem demoM_0122022 : fieldMul 7 5 20 [1, 2, 1, 1, 0, 2, 2] [0, 1, 2, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122022 : mirrorTrits [1, 2, 1, 1, 0, 2, 2] = [2, 1, 2, 2, 0, 1, 1] := by
  decide

theorem demoInv_0122022 : specInv 7 5 20 [0, 1, 2, 2, 0, 2, 2] = some [2, 1, 2, 2, 0, 1, 1] :=
  specInv_mirror_7 [0, 1, 2, 2, 0, 2, 2] [1, 2, 0, 0, 2, 2, 2] [2, 1, 1, 0, 2, 2, 1] [1, 2, 1, 1, 0, 2, 2] [2, 1, 2, 2, 0, 1, 1] demoR1_0122022 demoR2_0122022 demoC_0122022 demoM_0122022 demoMir_0122022

theorem demoR1_1122022 : invRung 7 5 20 [1, 1, 2, 2, 0, 2, 2] [1, 1, 2, 2, 0, 2, 2] 1 2 false = ([1, 1, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_1122022 : invRung 7 5 20 [1, 1, 2, 2, 0, 2, 2] [1, 1, 0, 2, 1, 1, 1] 3 1 true = ([1, 1, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_1122022 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 1, 2] = [0, 2, 0, 2, 0, 0, 0] := by
  decide

theorem demoM_1122022 : fieldMul 7 5 20 [0, 2, 0, 2, 0, 0, 0] [1, 1, 2, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122022 : mirrorTrits [0, 2, 0, 2, 0, 0, 0] = [0, 1, 0, 1, 0, 0, 0] := by
  decide

theorem demoInv_1122022 : specInv 7 5 20 [1, 1, 2, 2, 0, 2, 2] = some [0, 1, 0, 1, 0, 0, 0] :=
  specInv_mirror_7 [1, 1, 2, 2, 0, 2, 2] [1, 1, 0, 2, 1, 1, 1] [1, 1, 0, 1, 2, 1, 2] [0, 2, 0, 2, 0, 0, 0] [0, 1, 0, 1, 0, 0, 0] demoR1_1122022 demoR2_1122022 demoC_1122022 demoM_1122022 demoMir_1122022

theorem demoR1_2122022 : invRung 7 5 20 [2, 1, 2, 2, 0, 2, 2] [2, 1, 2, 2, 0, 2, 2] 1 2 false = ([2, 1, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_2122022 : invRung 7 5 20 [2, 1, 2, 2, 0, 2, 2] [2, 1, 1, 1, 0, 1, 0] 3 1 true = ([2, 2, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2122022 : fieldCube 7 5 20 [2, 2, 0, 1, 0, 2, 0] = [2, 2, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_2122022 : fieldMul 7 5 20 [2, 2, 0, 2, 2, 0, 1] [2, 1, 2, 2, 0, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2122022 : specInv 7 5 20 [2, 1, 2, 2, 0, 2, 2] = some [2, 2, 0, 2, 2, 0, 1] :=
  specInv_white_7 [2, 1, 2, 2, 0, 2, 2] [2, 1, 1, 1, 0, 1, 0] [2, 2, 0, 1, 0, 2, 0] [2, 2, 0, 2, 2, 0, 1] demoR1_2122022 demoR2_2122022 demoC_2122022 demoM_2122022

theorem demoR1_0222022 : invRung 7 5 20 [0, 2, 2, 2, 0, 2, 2] [0, 2, 2, 2, 0, 2, 2] 1 2 false = ([0, 2, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0222022 : invRung 7 5 20 [0, 2, 2, 2, 0, 2, 2] [0, 2, 2, 0, 0, 0, 0] 3 1 true = ([2, 1, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0222022 : fieldCube 7 5 20 [2, 1, 2, 0, 2, 2, 2] = [1, 0, 0, 2, 1, 0, 1] := by
  decide

theorem demoM_0222022 : fieldMul 7 5 20 [1, 0, 0, 2, 1, 0, 1] [0, 2, 2, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222022 : mirrorTrits [1, 0, 0, 2, 1, 0, 1] = [2, 0, 0, 1, 2, 0, 2] := by
  decide

theorem demoInv_0222022 : specInv 7 5 20 [0, 2, 2, 2, 0, 2, 2] = some [2, 0, 0, 1, 2, 0, 2] :=
  specInv_mirror_7 [0, 2, 2, 2, 0, 2, 2] [0, 2, 2, 0, 0, 0, 0] [2, 1, 2, 0, 2, 2, 2] [1, 0, 0, 2, 1, 0, 1] [2, 0, 0, 1, 2, 0, 2] demoR1_0222022 demoR2_0222022 demoC_0222022 demoM_0222022 demoMir_0222022

theorem demoR1_1222022 : invRung 7 5 20 [1, 2, 2, 2, 0, 2, 2] [1, 2, 2, 2, 0, 2, 2] 1 2 false = ([2, 0, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_1222022 : invRung 7 5 20 [1, 2, 2, 2, 0, 2, 2] [2, 0, 0, 0, 2, 0, 0] 3 1 true = ([1, 2, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_1222022 : fieldCube 7 5 20 [1, 2, 0, 1, 2, 2, 2] = [1, 0, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_1222022 : fieldMul 7 5 20 [1, 0, 1, 0, 1, 1, 2] [1, 2, 2, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222022 : mirrorTrits [1, 0, 1, 0, 1, 1, 2] = [2, 0, 2, 0, 2, 2, 1] := by
  decide

theorem demoInv_1222022 : specInv 7 5 20 [1, 2, 2, 2, 0, 2, 2] = some [2, 0, 2, 0, 2, 2, 1] :=
  specInv_mirror_7 [1, 2, 2, 2, 0, 2, 2] [2, 0, 0, 0, 2, 0, 0] [1, 2, 0, 1, 2, 2, 2] [1, 0, 1, 0, 1, 1, 2] [2, 0, 2, 0, 2, 2, 1] demoR1_1222022 demoR2_1222022 demoC_1222022 demoM_1222022 demoMir_1222022

theorem demoR1_2222022 : invRung 7 5 20 [2, 2, 2, 2, 0, 2, 2] [2, 2, 2, 2, 0, 2, 2] 1 2 false = ([1, 1, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_2222022 : invRung 7 5 20 [2, 2, 2, 2, 0, 2, 2] [1, 1, 1, 2, 1, 0, 0] 3 1 true = ([2, 0, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_2222022 : fieldCube 7 5 20 [2, 0, 0, 2, 0, 2, 2] = [0, 1, 2, 2, 1, 0, 0] := by
  decide

theorem demoM_2222022 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 0, 0] [2, 2, 2, 2, 0, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222022 : mirrorTrits [0, 1, 2, 2, 1, 0, 0] = [0, 2, 1, 1, 2, 0, 0] := by
  decide

theorem demoInv_2222022 : specInv 7 5 20 [2, 2, 2, 2, 0, 2, 2] = some [0, 2, 1, 1, 2, 0, 0] :=
  specInv_mirror_7 [2, 2, 2, 2, 0, 2, 2] [1, 1, 1, 2, 1, 0, 0] [2, 0, 0, 2, 0, 2, 2] [0, 1, 2, 2, 1, 0, 0] [0, 2, 1, 1, 2, 0, 0] demoR1_2222022 demoR2_2222022 demoC_2222022 demoM_2222022 demoMir_2222022

theorem demoR1_0000122 : invRung 7 5 20 [0, 0, 0, 0, 1, 2, 2] [0, 0, 0, 0, 1, 2, 2] 1 2 false = ([2, 2, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_0000122 : invRung 7 5 20 [0, 0, 0, 0, 1, 2, 2] [2, 2, 0, 2, 1, 0, 0] 3 1 true = ([0, 2, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_0000122 : fieldCube 7 5 20 [0, 2, 0, 2, 2, 1, 0] = [0, 0, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_0000122 : fieldMul 7 5 20 [0, 0, 0, 1, 1, 2, 1] [0, 0, 0, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0000122 : specInv 7 5 20 [0, 0, 0, 0, 1, 2, 2] = some [0, 0, 0, 1, 1, 2, 1] :=
  specInv_white_7 [0, 0, 0, 0, 1, 2, 2] [2, 2, 0, 2, 1, 0, 0] [0, 2, 0, 2, 2, 1, 0] [0, 0, 0, 1, 1, 2, 1] demoR1_0000122 demoR2_0000122 demoC_0000122 demoM_0000122

theorem demoR1_1000122 : invRung 7 5 20 [1, 0, 0, 0, 1, 2, 2] [1, 0, 0, 0, 1, 2, 2] 1 2 false = ([0, 0, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_1000122 : invRung 7 5 20 [1, 0, 0, 0, 1, 2, 2] [0, 0, 2, 2, 0, 1, 1] 3 1 true = ([1, 1, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_1000122 : fieldCube 7 5 20 [1, 1, 0, 2, 1, 0, 2] = [0, 0, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_1000122 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 2, 0] [1, 0, 0, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1000122 : specInv 7 5 20 [1, 0, 0, 0, 1, 2, 2] = some [0, 0, 0, 1, 2, 2, 0] :=
  specInv_white_7 [1, 0, 0, 0, 1, 2, 2] [0, 0, 2, 2, 0, 1, 1] [1, 1, 0, 2, 1, 0, 2] [0, 0, 0, 1, 2, 2, 0] demoR1_1000122 demoR2_1000122 demoC_1000122 demoM_1000122

theorem demoR1_2000122 : invRung 7 5 20 [2, 0, 0, 0, 1, 2, 2] [2, 0, 0, 0, 1, 2, 2] 1 2 false = ([1, 1, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2000122 : invRung 7 5 20 [2, 0, 0, 0, 1, 2, 2] [1, 1, 0, 1, 0, 0, 2] 3 1 true = ([2, 2, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2000122 : fieldCube 7 5 20 [2, 2, 0, 1, 1, 2, 1] = [2, 1, 2, 1, 0, 2, 0] := by
  decide

theorem demoM_2000122 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 2, 0] [2, 0, 0, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2000122 : specInv 7 5 20 [2, 0, 0, 0, 1, 2, 2] = some [2, 1, 2, 1, 0, 2, 0] :=
  specInv_white_7 [2, 0, 0, 0, 1, 2, 2] [1, 1, 0, 1, 0, 0, 2] [2, 2, 0, 1, 1, 2, 1] [2, 1, 2, 1, 0, 2, 0] demoR1_2000122 demoR2_2000122 demoC_2000122 demoM_2000122

theorem demoR1_0100122 : invRung 7 5 20 [0, 1, 0, 0, 1, 2, 2] [0, 1, 0, 0, 1, 2, 2] 1 2 false = ([2, 0, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0100122 : invRung 7 5 20 [0, 1, 0, 0, 1, 2, 2] [2, 0, 0, 0, 2, 1, 2] 3 1 true = ([2, 0, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_0100122 : fieldCube 7 5 20 [2, 0, 0, 2, 2, 1, 1] = [2, 1, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_0100122 : fieldMul 7 5 20 [2, 1, 2, 0, 2, 0, 2] [0, 1, 0, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0100122 : specInv 7 5 20 [0, 1, 0, 0, 1, 2, 2] = some [2, 1, 2, 0, 2, 0, 2] :=
  specInv_white_7 [0, 1, 0, 0, 1, 2, 2] [2, 0, 0, 0, 2, 1, 2] [2, 0, 0, 2, 2, 1, 1] [2, 1, 2, 0, 2, 0, 2] demoR1_0100122 demoR2_0100122 demoC_0100122 demoM_0100122

theorem demoR1_1100122 : invRung 7 5 20 [1, 1, 0, 0, 1, 2, 2] [1, 1, 0, 0, 1, 2, 2] 1 2 false = ([1, 1, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1100122 : invRung 7 5 20 [1, 1, 0, 0, 1, 2, 2] [1, 1, 0, 2, 0, 1, 2] 3 1 true = ([2, 2, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_1100122 : fieldCube 7 5 20 [2, 2, 0, 0, 0, 1, 2] = [0, 0, 2, 1, 0, 0, 1] := by
  decide

theorem demoM_1100122 : fieldMul 7 5 20 [0, 0, 2, 1, 0, 0, 1] [1, 1, 0, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1100122 : specInv 7 5 20 [1, 1, 0, 0, 1, 2, 2] = some [0, 0, 2, 1, 0, 0, 1] :=
  specInv_white_7 [1, 1, 0, 0, 1, 2, 2] [1, 1, 0, 2, 0, 1, 2] [2, 2, 0, 0, 0, 1, 2] [0, 0, 2, 1, 0, 0, 1] demoR1_1100122 demoR2_1100122 demoC_1100122 demoM_1100122

theorem demoR1_2100122 : invRung 7 5 20 [2, 1, 0, 0, 1, 2, 2] [2, 1, 0, 0, 1, 2, 2] 1 2 false = ([2, 1, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2100122 : invRung 7 5 20 [2, 1, 0, 0, 1, 2, 2] [2, 1, 1, 2, 2, 1, 2] 3 1 true = ([1, 2, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_2100122 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 2, 1] = [2, 2, 0, 2, 0, 1, 0] := by
  decide

theorem demoM_2100122 : fieldMul 7 5 20 [2, 2, 0, 2, 0, 1, 0] [2, 1, 0, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100122 : mirrorTrits [2, 2, 0, 2, 0, 1, 0] = [1, 1, 0, 1, 0, 2, 0] := by
  decide

theorem demoInv_2100122 : specInv 7 5 20 [2, 1, 0, 0, 1, 2, 2] = some [1, 1, 0, 1, 0, 2, 0] :=
  specInv_mirror_7 [2, 1, 0, 0, 1, 2, 2] [2, 1, 1, 2, 2, 1, 2] [1, 2, 2, 2, 2, 2, 1] [2, 2, 0, 2, 0, 1, 0] [1, 1, 0, 1, 0, 2, 0] demoR1_2100122 demoR2_2100122 demoC_2100122 demoM_2100122 demoMir_2100122

theorem demoR1_0200122 : invRung 7 5 20 [0, 2, 0, 0, 1, 2, 2] [0, 2, 0, 0, 1, 2, 2] 1 2 false = ([1, 0, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_0200122 : invRung 7 5 20 [0, 2, 0, 0, 1, 2, 2] [1, 0, 2, 1, 0, 1, 1] 3 1 true = ([0, 0, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0200122 : fieldCube 7 5 20 [0, 0, 2, 1, 2, 2, 2] = [0, 0, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_0200122 : fieldMul 7 5 20 [0, 0, 1, 1, 1, 1, 1] [0, 2, 0, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200122 : mirrorTrits [0, 0, 1, 1, 1, 1, 1] = [0, 0, 2, 2, 2, 2, 2] := by
  decide

theorem demoInv_0200122 : specInv 7 5 20 [0, 2, 0, 0, 1, 2, 2] = some [0, 0, 2, 2, 2, 2, 2] :=
  specInv_mirror_7 [0, 2, 0, 0, 1, 2, 2] [1, 0, 2, 1, 0, 1, 1] [0, 0, 2, 1, 2, 2, 2] [0, 0, 1, 1, 1, 1, 1] [0, 0, 2, 2, 2, 2, 2] demoR1_0200122 demoR2_0200122 demoC_0200122 demoM_0200122 demoMir_0200122

theorem demoR1_1200122 : invRung 7 5 20 [1, 2, 0, 0, 1, 2, 2] [1, 2, 0, 0, 1, 2, 2] 1 2 false = ([1, 2, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1200122 : invRung 7 5 20 [1, 2, 0, 0, 1, 2, 2] [1, 2, 0, 0, 2, 2, 1] 3 1 true = ([2, 2, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1200122 : fieldCube 7 5 20 [2, 2, 0, 1, 0, 1, 1] = [1, 2, 1, 0, 2, 0, 0] := by
  decide

theorem demoM_1200122 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 0, 0] [1, 2, 0, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200122 : mirrorTrits [1, 2, 1, 0, 2, 0, 0] = [2, 1, 2, 0, 1, 0, 0] := by
  decide

theorem demoInv_1200122 : specInv 7 5 20 [1, 2, 0, 0, 1, 2, 2] = some [2, 1, 2, 0, 1, 0, 0] :=
  specInv_mirror_7 [1, 2, 0, 0, 1, 2, 2] [1, 2, 0, 0, 2, 2, 1] [2, 2, 0, 1, 0, 1, 1] [1, 2, 1, 0, 2, 0, 0] [2, 1, 2, 0, 1, 0, 0] demoR1_1200122 demoR2_1200122 demoC_1200122 demoM_1200122 demoMir_1200122

theorem demoR1_2200122 : invRung 7 5 20 [2, 2, 0, 0, 1, 2, 2] [2, 2, 0, 0, 1, 2, 2] 1 2 false = ([2, 2, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_2200122 : invRung 7 5 20 [2, 2, 0, 0, 1, 2, 2] [2, 2, 1, 2, 2, 2, 1] 3 1 true = ([2, 2, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_2200122 : fieldCube 7 5 20 [2, 2, 2, 2, 2, 0, 1] = [1, 0, 1, 2, 1, 2, 2] := by
  decide

theorem demoM_2200122 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 2, 2] [2, 2, 0, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200122 : mirrorTrits [1, 0, 1, 2, 1, 2, 2] = [2, 0, 2, 1, 2, 1, 1] := by
  decide

theorem demoInv_2200122 : specInv 7 5 20 [2, 2, 0, 0, 1, 2, 2] = some [2, 0, 2, 1, 2, 1, 1] :=
  specInv_mirror_7 [2, 2, 0, 0, 1, 2, 2] [2, 2, 1, 2, 2, 2, 1] [2, 2, 2, 2, 2, 0, 1] [1, 0, 1, 2, 1, 2, 2] [2, 0, 2, 1, 2, 1, 1] demoR1_2200122 demoR2_2200122 demoC_2200122 demoM_2200122 demoMir_2200122

theorem demoR1_0010122 : invRung 7 5 20 [0, 0, 1, 0, 1, 2, 2] [0, 0, 1, 0, 1, 2, 2] 1 2 false = ([2, 0, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_0010122 : invRung 7 5 20 [0, 0, 1, 0, 1, 2, 2] [2, 0, 2, 0, 0, 0, 2] 3 1 true = ([1, 0, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_0010122 : fieldCube 7 5 20 [1, 0, 2, 1, 0, 0, 2] = [2, 2, 2, 2, 2, 0, 1] := by
  decide

theorem demoM_0010122 : fieldMul 7 5 20 [2, 2, 2, 2, 2, 0, 1] [0, 0, 1, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010122 : mirrorTrits [2, 2, 2, 2, 2, 0, 1] = [1, 1, 1, 1, 1, 0, 2] := by
  decide

theorem demoInv_0010122 : specInv 7 5 20 [0, 0, 1, 0, 1, 2, 2] = some [1, 1, 1, 1, 1, 0, 2] :=
  specInv_mirror_7 [0, 0, 1, 0, 1, 2, 2] [2, 0, 2, 0, 0, 0, 2] [1, 0, 2, 1, 0, 0, 2] [2, 2, 2, 2, 2, 0, 1] [1, 1, 1, 1, 1, 0, 2] demoR1_0010122 demoR2_0010122 demoC_0010122 demoM_0010122 demoMir_0010122

theorem demoR1_1010122 : invRung 7 5 20 [1, 0, 1, 0, 1, 2, 2] [1, 0, 1, 0, 1, 2, 2] 1 2 false = ([1, 0, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_1010122 : invRung 7 5 20 [1, 0, 1, 0, 1, 2, 2] [1, 0, 2, 1, 0, 2, 1] 3 1 true = ([0, 2, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_1010122 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 1, 1] = [0, 0, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_1010122 : fieldMul 7 5 20 [0, 0, 2, 1, 2, 2, 2] [1, 0, 1, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1010122 : mirrorTrits [0, 0, 2, 1, 2, 2, 2] = [0, 0, 1, 2, 1, 1, 1] := by
  decide

theorem demoInv_1010122 : specInv 7 5 20 [1, 0, 1, 0, 1, 2, 2] = some [0, 0, 1, 2, 1, 1, 1] :=
  specInv_mirror_7 [1, 0, 1, 0, 1, 2, 2] [1, 0, 2, 1, 0, 2, 1] [0, 2, 1, 2, 1, 1, 1] [0, 0, 2, 1, 2, 2, 2] [0, 0, 1, 2, 1, 1, 1] demoR1_1010122 demoR2_1010122 demoC_1010122 demoM_1010122 demoMir_1010122

theorem demoR1_2010122 : invRung 7 5 20 [2, 0, 1, 0, 1, 2, 2] [2, 0, 1, 0, 1, 2, 2] 1 2 false = ([0, 2, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_2010122 : invRung 7 5 20 [2, 0, 1, 0, 1, 2, 2] [0, 2, 1, 0, 0, 1, 1] 3 1 true = ([1, 1, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_2010122 : fieldCube 7 5 20 [1, 1, 0, 2, 2, 2, 1] = [2, 2, 0, 1, 0, 1, 1] := by
  decide

theorem demoM_2010122 : fieldMul 7 5 20 [2, 2, 0, 1, 0, 1, 1] [2, 0, 1, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010122 : mirrorTrits [2, 2, 0, 1, 0, 1, 1] = [1, 1, 0, 2, 0, 2, 2] := by
  decide

theorem demoInv_2010122 : specInv 7 5 20 [2, 0, 1, 0, 1, 2, 2] = some [1, 1, 0, 2, 0, 2, 2] :=
  specInv_mirror_7 [2, 0, 1, 0, 1, 2, 2] [0, 2, 1, 0, 0, 1, 1] [1, 1, 0, 2, 2, 2, 1] [2, 2, 0, 1, 0, 1, 1] [1, 1, 0, 2, 0, 2, 2] demoR1_2010122 demoR2_2010122 demoC_2010122 demoM_2010122 demoMir_2010122

theorem demoR1_0110122 : invRung 7 5 20 [0, 1, 1, 0, 1, 2, 2] [0, 1, 1, 0, 1, 2, 2] 1 2 false = ([2, 2, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_0110122 : invRung 7 5 20 [0, 1, 1, 0, 1, 2, 2] [2, 2, 0, 1, 2, 1, 1] 3 1 true = ([0, 0, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_0110122 : fieldCube 7 5 20 [0, 0, 1, 2, 0, 1, 0] = [0, 1, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_0110122 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 0, 0] [0, 1, 1, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0110122 : specInv 7 5 20 [0, 1, 1, 0, 1, 2, 2] = some [0, 1, 0, 0, 1, 0, 0] :=
  specInv_white_7 [0, 1, 1, 0, 1, 2, 2] [2, 2, 0, 1, 2, 1, 1] [0, 0, 1, 2, 0, 1, 0] [0, 1, 0, 0, 1, 0, 0] demoR1_0110122 demoR2_0110122 demoC_0110122 demoM_0110122

theorem demoR1_1110122 : invRung 7 5 20 [1, 1, 1, 0, 1, 2, 2] [1, 1, 1, 0, 1, 2, 2] 1 2 false = ([2, 1, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_1110122 : invRung 7 5 20 [1, 1, 1, 0, 1, 2, 2] [2, 1, 2, 0, 2, 0, 1] 3 1 true = ([1, 2, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_1110122 : fieldCube 7 5 20 [1, 2, 0, 2, 0, 2, 2] = [2, 1, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_1110122 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 0, 0] [1, 1, 1, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1110122 : specInv 7 5 20 [1, 1, 1, 0, 1, 2, 2] = some [2, 1, 2, 1, 1, 0, 0] :=
  specInv_white_7 [1, 1, 1, 0, 1, 2, 2] [2, 1, 2, 0, 2, 0, 1] [1, 2, 0, 2, 0, 2, 2] [2, 1, 2, 1, 1, 0, 0] demoR1_1110122 demoR2_1110122 demoC_1110122 demoM_1110122

theorem demoR1_2110122 : invRung 7 5 20 [2, 1, 1, 0, 1, 2, 2] [2, 1, 1, 0, 1, 2, 2] 1 2 false = ([1, 1, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2110122 : invRung 7 5 20 [2, 1, 1, 0, 1, 2, 2] [1, 1, 2, 2, 2, 1, 2] 3 1 true = ([1, 1, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_2110122 : fieldCube 7 5 20 [1, 1, 2, 0, 2, 2, 1] = [0, 2, 1, 1, 0, 2, 0] := by
  decide

theorem demoM_2110122 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 2, 0] [2, 1, 1, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110122 : mirrorTrits [0, 2, 1, 1, 0, 2, 0] = [0, 1, 2, 2, 0, 1, 0] := by
  decide

theorem demoInv_2110122 : specInv 7 5 20 [2, 1, 1, 0, 1, 2, 2] = some [0, 1, 2, 2, 0, 1, 0] :=
  specInv_mirror_7 [2, 1, 1, 0, 1, 2, 2] [1, 1, 2, 2, 2, 1, 2] [1, 1, 2, 0, 2, 2, 1] [0, 2, 1, 1, 0, 2, 0] [0, 1, 2, 2, 0, 1, 0] demoR1_2110122 demoR2_2110122 demoC_2110122 demoM_2110122 demoMir_2110122

theorem demoR1_0210122 : invRung 7 5 20 [0, 2, 1, 0, 1, 2, 2] [0, 2, 1, 0, 1, 2, 2] 1 2 false = ([2, 2, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_0210122 : invRung 7 5 20 [0, 2, 1, 0, 1, 2, 2] [2, 2, 1, 2, 1, 2, 0] 3 1 true = ([2, 0, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0210122 : fieldCube 7 5 20 [2, 0, 1, 0, 2, 0, 1] = [2, 0, 2, 0, 1, 0, 1] := by
  decide

theorem demoM_0210122 : fieldMul 7 5 20 [2, 0, 2, 0, 1, 0, 1] [0, 2, 1, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0210122 : specInv 7 5 20 [0, 2, 1, 0, 1, 2, 2] = some [2, 0, 2, 0, 1, 0, 1] :=
  specInv_white_7 [0, 2, 1, 0, 1, 2, 2] [2, 2, 1, 2, 1, 2, 0] [2, 0, 1, 0, 2, 0, 1] [2, 0, 2, 0, 1, 0, 1] demoR1_0210122 demoR2_0210122 demoC_0210122 demoM_0210122

theorem demoR1_1210122 : invRung 7 5 20 [1, 2, 1, 0, 1, 2, 2] [1, 2, 1, 0, 1, 2, 2] 1 2 false = ([0, 1, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_1210122 : invRung 7 5 20 [1, 2, 1, 0, 1, 2, 2] [0, 1, 2, 0, 0, 0, 2] 3 1 true = ([2, 1, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_1210122 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 1, 0] = [2, 0, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_1210122 : fieldMul 7 5 20 [2, 0, 0, 0, 1, 2, 1] [1, 2, 1, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1210122 : specInv 7 5 20 [1, 2, 1, 0, 1, 2, 2] = some [2, 0, 0, 0, 1, 2, 1] :=
  specInv_white_7 [1, 2, 1, 0, 1, 2, 2] [0, 1, 2, 0, 0, 0, 2] [2, 1, 0, 2, 2, 1, 0] [2, 0, 0, 0, 1, 2, 1] demoR1_1210122 demoR2_1210122 demoC_1210122 demoM_1210122

theorem demoR1_2210122 : invRung 7 5 20 [2, 2, 1, 0, 1, 2, 2] [2, 2, 1, 0, 1, 2, 2] 1 2 false = ([2, 0, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_2210122 : invRung 7 5 20 [2, 2, 1, 0, 1, 2, 2] [2, 0, 0, 0, 2, 2, 2] 3 1 true = ([0, 1, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_2210122 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 0, 0] = [0, 2, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_2210122 : fieldMul 7 5 20 [0, 2, 0, 0, 0, 2, 1] [2, 2, 1, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2210122 : specInv 7 5 20 [2, 2, 1, 0, 1, 2, 2] = some [0, 2, 0, 0, 0, 2, 1] :=
  specInv_white_7 [2, 2, 1, 0, 1, 2, 2] [2, 0, 0, 0, 2, 2, 2] [0, 1, 2, 0, 2, 0, 0] [0, 2, 0, 0, 0, 2, 1] demoR1_2210122 demoR2_2210122 demoC_2210122 demoM_2210122

theorem demoR1_0020122 : invRung 7 5 20 [0, 0, 2, 0, 1, 2, 2] [0, 0, 2, 0, 1, 2, 2] 1 2 false = ([1, 1, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_0020122 : invRung 7 5 20 [0, 0, 2, 0, 1, 2, 2] [1, 1, 2, 2, 1, 0, 1] 3 1 true = ([2, 2, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0020122 : fieldCube 7 5 20 [2, 2, 2, 1, 1, 0, 0] = [0, 1, 1, 0, 0, 2, 0] := by
  decide

theorem demoM_0020122 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 2, 0] [0, 0, 2, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020122 : mirrorTrits [0, 1, 1, 0, 0, 2, 0] = [0, 2, 2, 0, 0, 1, 0] := by
  decide

theorem demoInv_0020122 : specInv 7 5 20 [0, 0, 2, 0, 1, 2, 2] = some [0, 2, 2, 0, 0, 1, 0] :=
  specInv_mirror_7 [0, 0, 2, 0, 1, 2, 2] [1, 1, 2, 2, 1, 0, 1] [2, 2, 2, 1, 1, 0, 0] [0, 1, 1, 0, 0, 2, 0] [0, 2, 2, 0, 0, 1, 0] demoR1_0020122 demoR2_0020122 demoC_0020122 demoM_0020122 demoMir_0020122

theorem demoR1_1020122 : invRung 7 5 20 [1, 0, 2, 0, 1, 2, 2] [1, 0, 2, 0, 1, 2, 2] 1 2 false = ([0, 0, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_1020122 : invRung 7 5 20 [1, 0, 2, 0, 1, 2, 2] [0, 0, 1, 1, 2, 0, 0] 3 1 true = ([0, 2, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_1020122 : fieldCube 7 5 20 [0, 2, 0, 0, 2, 1, 0] = [1, 0, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_1020122 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 0, 1] [1, 0, 2, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1020122 : specInv 7 5 20 [1, 0, 2, 0, 1, 2, 2] = some [1, 0, 1, 1, 1, 0, 1] :=
  specInv_white_7 [1, 0, 2, 0, 1, 2, 2] [0, 0, 1, 1, 2, 0, 0] [0, 2, 0, 0, 2, 1, 0] [1, 0, 1, 1, 1, 0, 1] demoR1_1020122 demoR2_1020122 demoC_1020122 demoM_1020122

theorem demoR1_2020122 : invRung 7 5 20 [2, 0, 2, 0, 1, 2, 2] [2, 0, 2, 0, 1, 2, 2] 1 2 false = ([2, 0, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_2020122 : invRung 7 5 20 [2, 0, 2, 0, 1, 2, 2] [2, 0, 2, 0, 2, 2, 1] 3 1 true = ([2, 2, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_2020122 : fieldCube 7 5 20 [2, 2, 1, 2, 0, 1, 2] = [2, 0, 1, 1, 0, 2, 2] := by
  decide

theorem demoM_2020122 : fieldMul 7 5 20 [2, 0, 1, 1, 0, 2, 2] [2, 0, 2, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020122 : mirrorTrits [2, 0, 1, 1, 0, 2, 2] = [1, 0, 2, 2, 0, 1, 1] := by
  decide

theorem demoInv_2020122 : specInv 7 5 20 [2, 0, 2, 0, 1, 2, 2] = some [1, 0, 2, 2, 0, 1, 1] :=
  specInv_mirror_7 [2, 0, 2, 0, 1, 2, 2] [2, 0, 2, 0, 2, 2, 1] [2, 2, 1, 2, 0, 1, 2] [2, 0, 1, 1, 0, 2, 2] [1, 0, 2, 2, 0, 1, 1] demoR1_2020122 demoR2_2020122 demoC_2020122 demoM_2020122 demoMir_2020122

theorem demoR1_0120122 : invRung 7 5 20 [0, 1, 2, 0, 1, 2, 2] [0, 1, 2, 0, 1, 2, 2] 1 2 false = ([1, 0, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_0120122 : invRung 7 5 20 [0, 1, 2, 0, 1, 2, 2] [1, 0, 0, 2, 0, 0, 2] 3 1 true = ([2, 1, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0120122 : fieldCube 7 5 20 [2, 1, 1, 0, 2, 1, 0] = [0, 0, 1, 0, 1, 0, 2] := by
  decide

theorem demoM_0120122 : fieldMul 7 5 20 [0, 0, 1, 0, 1, 0, 2] [0, 1, 2, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0120122 : specInv 7 5 20 [0, 1, 2, 0, 1, 2, 2] = some [0, 0, 1, 0, 1, 0, 2] :=
  specInv_white_7 [0, 1, 2, 0, 1, 2, 2] [1, 0, 0, 2, 0, 0, 2] [2, 1, 1, 0, 2, 1, 0] [0, 0, 1, 0, 1, 0, 2] demoR1_0120122 demoR2_0120122 demoC_0120122 demoM_0120122

theorem demoR1_1120122 : invRung 7 5 20 [1, 1, 2, 0, 1, 2, 2] [1, 1, 2, 0, 1, 2, 2] 1 2 false = ([1, 0, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_1120122 : invRung 7 5 20 [1, 1, 2, 0, 1, 2, 2] [1, 0, 2, 1, 2, 1, 1] 3 1 true = ([0, 0, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_1120122 : fieldCube 7 5 20 [0, 0, 0, 2, 2, 2, 2] = [1, 0, 2, 1, 1, 2, 2] := by
  decide

theorem demoM_1120122 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 2, 2] [1, 1, 2, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120122 : mirrorTrits [1, 0, 2, 1, 1, 2, 2] = [2, 0, 1, 2, 2, 1, 1] := by
  decide

theorem demoInv_1120122 : specInv 7 5 20 [1, 1, 2, 0, 1, 2, 2] = some [2, 0, 1, 2, 2, 1, 1] :=
  specInv_mirror_7 [1, 1, 2, 0, 1, 2, 2] [1, 0, 2, 1, 2, 1, 1] [0, 0, 0, 2, 2, 2, 2] [1, 0, 2, 1, 1, 2, 2] [2, 0, 1, 2, 2, 1, 1] demoR1_1120122 demoR2_1120122 demoC_1120122 demoM_1120122 demoMir_1120122

theorem demoR1_2120122 : invRung 7 5 20 [2, 1, 2, 0, 1, 2, 2] [2, 1, 2, 0, 1, 2, 2] 1 2 false = ([0, 0, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2120122 : invRung 7 5 20 [2, 1, 2, 0, 1, 2, 2] [0, 0, 2, 2, 0, 0, 2] 3 1 true = ([1, 1, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_2120122 : fieldCube 7 5 20 [1, 1, 0, 2, 2, 2, 2] = [2, 0, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_2120122 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 2, 2] [2, 1, 2, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120122 : mirrorTrits [2, 0, 2, 2, 1, 2, 2] = [1, 0, 1, 1, 2, 1, 1] := by
  decide

theorem demoInv_2120122 : specInv 7 5 20 [2, 1, 2, 0, 1, 2, 2] = some [1, 0, 1, 1, 2, 1, 1] :=
  specInv_mirror_7 [2, 1, 2, 0, 1, 2, 2] [0, 0, 2, 2, 0, 0, 2] [1, 1, 0, 2, 2, 2, 2] [2, 0, 2, 2, 1, 2, 2] [1, 0, 1, 1, 2, 1, 1] demoR1_2120122 demoR2_2120122 demoC_2120122 demoM_2120122 demoMir_2120122

theorem demoR1_0220122 : invRung 7 5 20 [0, 2, 2, 0, 1, 2, 2] [0, 2, 2, 0, 1, 2, 2] 1 2 false = ([2, 2, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_0220122 : invRung 7 5 20 [0, 2, 2, 0, 1, 2, 2] [2, 2, 2, 2, 2, 1, 0] 3 1 true = ([1, 1, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0220122 : fieldCube 7 5 20 [1, 1, 0, 2, 2, 0, 2] = [0, 1, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_0220122 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 0, 1] [0, 2, 2, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0220122 : specInv 7 5 20 [0, 2, 2, 0, 1, 2, 2] = some [0, 1, 0, 2, 2, 0, 1] :=
  specInv_white_7 [0, 2, 2, 0, 1, 2, 2] [2, 2, 2, 2, 2, 1, 0] [1, 1, 0, 2, 2, 0, 2] [0, 1, 0, 2, 2, 0, 1] demoR1_0220122 demoR2_0220122 demoC_0220122 demoM_0220122

theorem demoR1_1220122 : invRung 7 5 20 [1, 2, 2, 0, 1, 2, 2] [1, 2, 2, 0, 1, 2, 2] 1 2 false = ([0, 1, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_1220122 : invRung 7 5 20 [1, 2, 2, 0, 1, 2, 2] [0, 1, 1, 2, 1, 2, 0] 3 1 true = ([1, 2, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_1220122 : fieldCube 7 5 20 [1, 2, 0, 2, 2, 1, 1] = [1, 1, 2, 2, 2, 0, 2] := by
  decide

theorem demoM_1220122 : fieldMul 7 5 20 [1, 1, 2, 2, 2, 0, 2] [1, 2, 2, 0, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1220122 : specInv 7 5 20 [1, 2, 2, 0, 1, 2, 2] = some [1, 1, 2, 2, 2, 0, 2] :=
  specInv_white_7 [1, 2, 2, 0, 1, 2, 2] [0, 1, 1, 2, 1, 2, 0] [1, 2, 0, 2, 2, 1, 1] [1, 1, 2, 2, 2, 0, 2] demoR1_1220122 demoR2_1220122 demoC_1220122 demoM_1220122

theorem demoR1_2220122 : invRung 7 5 20 [2, 2, 2, 0, 1, 2, 2] [2, 2, 2, 0, 1, 2, 2] 1 2 false = ([2, 2, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2220122 : invRung 7 5 20 [2, 2, 2, 0, 1, 2, 2] [2, 2, 0, 0, 2, 0, 2] 3 1 true = ([1, 1, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_2220122 : fieldCube 7 5 20 [1, 1, 2, 1, 2, 0, 0] = [2, 2, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_2220122 : fieldMul 7 5 20 [2, 2, 1, 0, 0, 0, 1] [2, 2, 2, 0, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220122 : mirrorTrits [2, 2, 1, 0, 0, 0, 1] = [1, 1, 2, 0, 0, 0, 2] := by
  decide

theorem demoInv_2220122 : specInv 7 5 20 [2, 2, 2, 0, 1, 2, 2] = some [1, 1, 2, 0, 0, 0, 2] :=
  specInv_mirror_7 [2, 2, 2, 0, 1, 2, 2] [2, 2, 0, 0, 2, 0, 2] [1, 1, 2, 1, 2, 0, 0] [2, 2, 1, 0, 0, 0, 1] [1, 1, 2, 0, 0, 0, 2] demoR1_2220122 demoR2_2220122 demoC_2220122 demoM_2220122 demoMir_2220122

theorem demoR1_0001122 : invRung 7 5 20 [0, 0, 0, 1, 1, 2, 2] [0, 0, 0, 1, 1, 2, 2] 1 2 false = ([2, 2, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_0001122 : invRung 7 5 20 [0, 0, 0, 1, 1, 2, 2] [2, 2, 2, 1, 0, 0, 1] 3 1 true = ([0, 0, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_0001122 : fieldCube 7 5 20 [0, 0, 2, 1, 1, 1, 2] = [2, 1, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_0001122 : fieldMul 7 5 20 [2, 1, 0, 0, 0, 2, 1] [0, 0, 0, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001122 : mirrorTrits [2, 1, 0, 0, 0, 2, 1] = [1, 2, 0, 0, 0, 1, 2] := by
  decide

theorem demoInv_0001122 : specInv 7 5 20 [0, 0, 0, 1, 1, 2, 2] = some [1, 2, 0, 0, 0, 1, 2] :=
  specInv_mirror_7 [0, 0, 0, 1, 1, 2, 2] [2, 2, 2, 1, 0, 0, 1] [0, 0, 2, 1, 1, 1, 2] [2, 1, 0, 0, 0, 2, 1] [1, 2, 0, 0, 0, 1, 2] demoR1_0001122 demoR2_0001122 demoC_0001122 demoM_0001122 demoMir_0001122

theorem demoR1_1001122 : invRung 7 5 20 [1, 0, 0, 1, 1, 2, 2] [1, 0, 0, 1, 1, 2, 2] 1 2 false = ([0, 0, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_1001122 : invRung 7 5 20 [1, 0, 0, 1, 1, 2, 2] [0, 0, 2, 0, 1, 0, 2] 3 1 true = ([1, 2, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_1001122 : fieldCube 7 5 20 [1, 2, 2, 1, 2, 0, 0] = [2, 2, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_1001122 : fieldMul 7 5 20 [2, 2, 1, 1, 0, 0, 1] [1, 0, 0, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1001122 : mirrorTrits [2, 2, 1, 1, 0, 0, 1] = [1, 1, 2, 2, 0, 0, 2] := by
  decide

theorem demoInv_1001122 : specInv 7 5 20 [1, 0, 0, 1, 1, 2, 2] = some [1, 1, 2, 2, 0, 0, 2] :=
  specInv_mirror_7 [1, 0, 0, 1, 1, 2, 2] [0, 0, 2, 0, 1, 0, 2] [1, 2, 2, 1, 2, 0, 0] [2, 2, 1, 1, 0, 0, 1] [1, 1, 2, 2, 0, 0, 2] demoR1_1001122 demoR2_1001122 demoC_1001122 demoM_1001122 demoMir_1001122

theorem demoR1_2001122 : invRung 7 5 20 [2, 0, 0, 1, 1, 2, 2] [2, 0, 0, 1, 1, 2, 2] 1 2 false = ([1, 0, 2, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2001122 : invRung 7 5 20 [2, 0, 0, 1, 1, 2, 2] [1, 0, 2, 0, 2, 2, 0] 3 1 true = ([1, 2, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_2001122 : fieldCube 7 5 20 [1, 2, 0, 0, 0, 2, 0] = [0, 2, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_2001122 : fieldMul 7 5 20 [0, 2, 2, 2, 2, 2, 1] [2, 0, 0, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001122 : mirrorTrits [0, 2, 2, 2, 2, 2, 1] = [0, 1, 1, 1, 1, 1, 2] := by
  decide

theorem demoInv_2001122 : specInv 7 5 20 [2, 0, 0, 1, 1, 2, 2] = some [0, 1, 1, 1, 1, 1, 2] :=
  specInv_mirror_7 [2, 0, 0, 1, 1, 2, 2] [1, 0, 2, 0, 2, 2, 0] [1, 2, 0, 0, 0, 2, 0] [0, 2, 2, 2, 2, 2, 1] [0, 1, 1, 1, 1, 1, 2] demoR1_2001122 demoR2_2001122 demoC_2001122 demoM_2001122 demoMir_2001122

theorem demoR1_0101122 : invRung 7 5 20 [0, 1, 0, 1, 1, 2, 2] [0, 1, 0, 1, 1, 2, 2] 1 2 false = ([1, 1, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_0101122 : invRung 7 5 20 [0, 1, 0, 1, 1, 2, 2] [1, 1, 1, 2, 1, 0, 1] 3 1 true = ([0, 1, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0101122 : fieldCube 7 5 20 [0, 1, 1, 2, 2, 0, 2] = [2, 1, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_0101122 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 0, 2] [0, 1, 0, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0101122 : specInv 7 5 20 [0, 1, 0, 1, 1, 2, 2] = some [2, 1, 0, 2, 2, 0, 2] :=
  specInv_white_7 [0, 1, 0, 1, 1, 2, 2] [1, 1, 1, 2, 1, 0, 1] [0, 1, 1, 2, 2, 0, 2] [2, 1, 0, 2, 2, 0, 2] demoR1_0101122 demoR2_0101122 demoC_0101122 demoM_0101122

theorem demoR1_1101122 : invRung 7 5 20 [1, 1, 0, 1, 1, 2, 2] [1, 1, 0, 1, 1, 2, 2] 1 2 false = ([1, 2, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_1101122 : invRung 7 5 20 [1, 1, 0, 1, 1, 2, 2] [1, 2, 2, 0, 0, 1, 1] 3 1 true = ([1, 2, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_1101122 : fieldCube 7 5 20 [1, 2, 2, 1, 1, 2, 2] = [1, 2, 1, 2, 1, 0, 0] := by
  decide

theorem demoM_1101122 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 0, 0] [1, 1, 0, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1101122 : specInv 7 5 20 [1, 1, 0, 1, 1, 2, 2] = some [1, 2, 1, 2, 1, 0, 0] :=
  specInv_white_7 [1, 1, 0, 1, 1, 2, 2] [1, 2, 2, 0, 0, 1, 1] [1, 2, 2, 1, 1, 2, 2] [1, 2, 1, 2, 1, 0, 0] demoR1_1101122 demoR2_1101122 demoC_1101122 demoM_1101122

theorem demoR1_2101122 : invRung 7 5 20 [2, 1, 0, 1, 1, 2, 2] [2, 1, 0, 1, 1, 2, 2] 1 2 false = ([0, 1, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2101122 : invRung 7 5 20 [2, 1, 0, 1, 1, 2, 2] [0, 1, 2, 1, 2, 0, 1] 3 1 true = ([1, 0, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2101122 : fieldCube 7 5 20 [1, 0, 2, 2, 0, 1, 0] = [1, 1, 0, 0, 1, 0, 1] := by
  decide

theorem demoM_2101122 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 0, 1] [2, 1, 0, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101122 : mirrorTrits [1, 1, 0, 0, 1, 0, 1] = [2, 2, 0, 0, 2, 0, 2] := by
  decide

theorem demoInv_2101122 : specInv 7 5 20 [2, 1, 0, 1, 1, 2, 2] = some [2, 2, 0, 0, 2, 0, 2] :=
  specInv_mirror_7 [2, 1, 0, 1, 1, 2, 2] [0, 1, 2, 1, 2, 0, 1] [1, 0, 2, 2, 0, 1, 0] [1, 1, 0, 0, 1, 0, 1] [2, 2, 0, 0, 2, 0, 2] demoR1_2101122 demoR2_2101122 demoC_2101122 demoM_2101122 demoMir_2101122

theorem demoR1_0201122 : invRung 7 5 20 [0, 2, 0, 1, 1, 2, 2] [0, 2, 0, 1, 1, 2, 2] 1 2 false = ([2, 0, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_0201122 : invRung 7 5 20 [0, 2, 0, 1, 1, 2, 2] [2, 0, 2, 1, 1, 0, 2] 3 1 true = ([2, 1, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0201122 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 0, 0] = [0, 1, 1, 2, 0, 2, 0] := by
  decide

theorem demoM_0201122 : fieldMul 7 5 20 [0, 1, 1, 2, 0, 2, 0] [0, 2, 0, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0201122 : specInv 7 5 20 [0, 2, 0, 1, 1, 2, 2] = some [0, 1, 1, 2, 0, 2, 0] :=
  specInv_white_7 [0, 2, 0, 1, 1, 2, 2] [2, 0, 2, 1, 1, 0, 2] [2, 1, 2, 1, 1, 0, 0] [0, 1, 1, 2, 0, 2, 0] demoR1_0201122 demoR2_0201122 demoC_0201122 demoM_0201122

theorem demoR1_1201122 : invRung 7 5 20 [1, 2, 0, 1, 1, 2, 2] [1, 2, 0, 1, 1, 2, 2] 1 2 false = ([1, 2, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1201122 : invRung 7 5 20 [1, 2, 0, 1, 1, 2, 2] [1, 2, 1, 2, 0, 1, 2] 3 1 true = ([0, 2, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1201122 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 2, 0] = [0, 2, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_1201122 : fieldMul 7 5 20 [0, 2, 0, 2, 2, 0, 2] [1, 2, 0, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201122 : mirrorTrits [0, 2, 0, 2, 2, 0, 2] = [0, 1, 0, 1, 1, 0, 1] := by
  decide

theorem demoInv_1201122 : specInv 7 5 20 [1, 2, 0, 1, 1, 2, 2] = some [0, 1, 0, 1, 1, 0, 1] :=
  specInv_mirror_7 [1, 2, 0, 1, 1, 2, 2] [1, 2, 1, 2, 0, 1, 2] [0, 2, 1, 1, 0, 2, 0] [0, 2, 0, 2, 2, 0, 2] [0, 1, 0, 1, 1, 0, 1] demoR1_1201122 demoR2_1201122 demoC_1201122 demoM_1201122 demoMir_1201122

theorem demoR1_2201122 : invRung 7 5 20 [2, 2, 0, 1, 1, 2, 2] [2, 2, 0, 1, 1, 2, 2] 1 2 false = ([1, 1, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_2201122 : invRung 7 5 20 [2, 2, 0, 1, 1, 2, 2] [1, 1, 1, 2, 2, 2, 2] 3 1 true = ([0, 1, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2201122 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 0, 0] = [0, 1, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_2201122 : fieldMul 7 5 20 [0, 1, 0, 2, 0, 1, 1] [2, 2, 0, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2201122 : specInv 7 5 20 [2, 2, 0, 1, 1, 2, 2] = some [0, 1, 0, 2, 0, 1, 1] :=
  specInv_white_7 [2, 2, 0, 1, 1, 2, 2] [1, 1, 1, 2, 2, 2, 2] [0, 1, 0, 0, 1, 0, 0] [0, 1, 0, 2, 0, 1, 1] demoR1_2201122 demoR2_2201122 demoC_2201122 demoM_2201122

theorem demoR1_0011122 : invRung 7 5 20 [0, 0, 1, 1, 1, 2, 2] [0, 0, 1, 1, 1, 2, 2] 1 2 false = ([0, 2, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_0011122 : invRung 7 5 20 [0, 0, 1, 1, 1, 2, 2] [0, 2, 0, 2, 2, 2, 0] 3 1 true = ([1, 1, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0011122 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 2, 1] = [0, 1, 1, 0, 0, 1, 1] := by
  decide

theorem demoM_0011122 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 1, 1] [0, 0, 1, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011122 : mirrorTrits [0, 1, 1, 0, 0, 1, 1] = [0, 2, 2, 0, 0, 2, 2] := by
  decide

theorem demoInv_0011122 : specInv 7 5 20 [0, 0, 1, 1, 1, 2, 2] = some [0, 2, 2, 0, 0, 2, 2] :=
  specInv_mirror_7 [0, 0, 1, 1, 1, 2, 2] [0, 2, 0, 2, 2, 2, 0] [1, 1, 1, 0, 1, 2, 1] [0, 1, 1, 0, 0, 1, 1] [0, 2, 2, 0, 0, 2, 2] demoR1_0011122 demoR2_0011122 demoC_0011122 demoM_0011122 demoMir_0011122

theorem demoR1_1011122 : invRung 7 5 20 [1, 0, 1, 1, 1, 2, 2] [1, 0, 1, 1, 1, 2, 2] 1 2 false = ([2, 0, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_1011122 : invRung 7 5 20 [1, 0, 1, 1, 1, 2, 2] [2, 0, 2, 1, 0, 1, 0] 3 1 true = ([2, 1, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_1011122 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 0, 2] = [0, 2, 2, 0, 2, 0, 0] := by
  decide

theorem demoM_1011122 : fieldMul 7 5 20 [0, 2, 2, 0, 2, 0, 0] [1, 0, 1, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011122 : mirrorTrits [0, 2, 2, 0, 2, 0, 0] = [0, 1, 1, 0, 1, 0, 0] := by
  decide

theorem demoInv_1011122 : specInv 7 5 20 [1, 0, 1, 1, 1, 2, 2] = some [0, 1, 1, 0, 1, 0, 0] :=
  specInv_mirror_7 [1, 0, 1, 1, 1, 2, 2] [2, 0, 2, 1, 0, 1, 0] [2, 1, 1, 1, 0, 0, 2] [0, 2, 2, 0, 2, 0, 0] [0, 1, 1, 0, 1, 0, 0] demoR1_1011122 demoR2_1011122 demoC_1011122 demoM_1011122 demoMir_1011122

theorem demoR1_2011122 : invRung 7 5 20 [2, 0, 1, 1, 1, 2, 2] [2, 0, 1, 1, 1, 2, 2] 1 2 false = ([1, 2, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_2011122 : invRung 7 5 20 [2, 0, 1, 1, 1, 2, 2] [1, 2, 1, 0, 0, 1, 1] 3 1 true = ([0, 0, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_2011122 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 2, 2] = [1, 0, 2, 1, 1, 2, 0] := by
  decide

theorem demoM_2011122 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 2, 0] [2, 0, 1, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011122 : mirrorTrits [1, 0, 2, 1, 1, 2, 0] = [2, 0, 1, 2, 2, 1, 0] := by
  decide

theorem demoInv_2011122 : specInv 7 5 20 [2, 0, 1, 1, 1, 2, 2] = some [2, 0, 1, 2, 2, 1, 0] :=
  specInv_mirror_7 [2, 0, 1, 1, 1, 2, 2] [1, 2, 1, 0, 0, 1, 1] [0, 0, 1, 2, 2, 2, 2] [1, 0, 2, 1, 1, 2, 0] [2, 0, 1, 2, 2, 1, 0] demoR1_2011122 demoR2_2011122 demoC_2011122 demoM_2011122 demoMir_2011122

theorem demoR1_0111122 : invRung 7 5 20 [0, 1, 1, 1, 1, 2, 2] [0, 1, 1, 1, 1, 2, 2] 1 2 false = ([0, 1, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_0111122 : invRung 7 5 20 [0, 1, 1, 1, 1, 2, 2] [0, 1, 2, 1, 0, 1, 0] 3 1 true = ([1, 1, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0111122 : fieldCube 7 5 20 [1, 1, 2, 1, 0, 0, 1] = [2, 1, 0, 2, 1, 2, 0] := by
  decide

theorem demoM_0111122 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 2, 0] [0, 1, 1, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0111122 : specInv 7 5 20 [0, 1, 1, 1, 1, 2, 2] = some [2, 1, 0, 2, 1, 2, 0] :=
  specInv_white_7 [0, 1, 1, 1, 1, 2, 2] [0, 1, 2, 1, 0, 1, 0] [1, 1, 2, 1, 0, 0, 1] [2, 1, 0, 2, 1, 2, 0] demoR1_0111122 demoR2_0111122 demoC_0111122 demoM_0111122

theorem demoR1_1111122 : invRung 7 5 20 [1, 1, 1, 1, 1, 2, 2] [1, 1, 1, 1, 1, 2, 2] 1 2 false = ([1, 1, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_1111122 : invRung 7 5 20 [1, 1, 1, 1, 1, 2, 2] [1, 1, 0, 1, 0, 2, 1] 3 1 true = ([0, 0, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_1111122 : fieldCube 7 5 20 [0, 0, 2, 0, 0, 2, 2] = [2, 1, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_1111122 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 1, 2] [1, 1, 1, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1111122 : specInv 7 5 20 [1, 1, 1, 1, 1, 2, 2] = some [2, 1, 0, 2, 1, 1, 2] :=
  specInv_white_7 [1, 1, 1, 1, 1, 2, 2] [1, 1, 0, 1, 0, 2, 1] [0, 0, 2, 0, 0, 2, 2] [2, 1, 0, 2, 1, 1, 2] demoR1_1111122 demoR2_1111122 demoC_1111122 demoM_1111122

theorem demoR1_2111122 : invRung 7 5 20 [2, 1, 1, 1, 1, 2, 2] [2, 1, 1, 1, 1, 2, 2] 1 2 false = ([1, 1, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2111122 : invRung 7 5 20 [2, 1, 1, 1, 1, 2, 2] [1, 1, 0, 0, 2, 0, 0] 3 1 true = ([0, 0, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_2111122 : fieldCube 7 5 20 [0, 0, 1, 1, 1, 0, 0] = [1, 1, 1, 1, 0, 2, 2] := by
  decide

theorem demoM_2111122 : fieldMul 7 5 20 [1, 1, 1, 1, 0, 2, 2] [2, 1, 1, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2111122 : specInv 7 5 20 [2, 1, 1, 1, 1, 2, 2] = some [1, 1, 1, 1, 0, 2, 2] :=
  specInv_white_7 [2, 1, 1, 1, 1, 2, 2] [1, 1, 0, 0, 2, 0, 0] [0, 0, 1, 1, 1, 0, 0] [1, 1, 1, 1, 0, 2, 2] demoR1_2111122 demoR2_2111122 demoC_2111122 demoM_2111122

theorem demoR1_0211122 : invRung 7 5 20 [0, 2, 1, 1, 1, 2, 2] [0, 2, 1, 1, 1, 2, 2] 1 2 false = ([0, 2, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_0211122 : invRung 7 5 20 [0, 2, 1, 1, 1, 2, 2] [0, 2, 1, 1, 0, 1, 1] 3 1 true = ([1, 1, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_0211122 : fieldCube 7 5 20 [1, 1, 2, 2, 0, 2, 1] = [2, 0, 0, 2, 0, 2, 1] := by
  decide

theorem demoM_0211122 : fieldMul 7 5 20 [2, 0, 0, 2, 0, 2, 1] [0, 2, 1, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0211122 : specInv 7 5 20 [0, 2, 1, 1, 1, 2, 2] = some [2, 0, 0, 2, 0, 2, 1] :=
  specInv_white_7 [0, 2, 1, 1, 1, 2, 2] [0, 2, 1, 1, 0, 1, 1] [1, 1, 2, 2, 0, 2, 1] [2, 0, 0, 2, 0, 2, 1] demoR1_0211122 demoR2_0211122 demoC_0211122 demoM_0211122

theorem demoR1_1211122 : invRung 7 5 20 [1, 2, 1, 1, 1, 2, 2] [1, 2, 1, 1, 1, 2, 2] 1 2 false = ([0, 2, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1211122 : invRung 7 5 20 [1, 2, 1, 1, 1, 2, 2] [0, 2, 1, 0, 1, 0, 1] 3 1 true = ([2, 0, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_1211122 : fieldCube 7 5 20 [2, 0, 2, 1, 2, 0, 0] = [0, 2, 1, 2, 0, 0, 1] := by
  decide

theorem demoM_1211122 : fieldMul 7 5 20 [0, 2, 1, 2, 0, 0, 1] [1, 2, 1, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1211122 : mirrorTrits [0, 2, 1, 2, 0, 0, 1] = [0, 1, 2, 1, 0, 0, 2] := by
  decide

theorem demoInv_1211122 : specInv 7 5 20 [1, 2, 1, 1, 1, 2, 2] = some [0, 1, 2, 1, 0, 0, 2] :=
  specInv_mirror_7 [1, 2, 1, 1, 1, 2, 2] [0, 2, 1, 0, 1, 0, 1] [2, 0, 2, 1, 2, 0, 0] [0, 2, 1, 2, 0, 0, 1] [0, 1, 2, 1, 0, 0, 2] demoR1_1211122 demoR2_1211122 demoC_1211122 demoM_1211122 demoMir_1211122

theorem demoR1_2211122 : invRung 7 5 20 [2, 2, 1, 1, 1, 2, 2] [2, 2, 1, 1, 1, 2, 2] 1 2 false = ([1, 1, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2211122 : invRung 7 5 20 [2, 2, 1, 1, 1, 2, 2] [1, 1, 2, 0, 1, 1, 2] 3 1 true = ([2, 2, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_2211122 : fieldCube 7 5 20 [2, 2, 2, 0, 1, 0, 2] = [2, 0, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_2211122 : fieldMul 7 5 20 [2, 0, 1, 2, 2, 0, 2] [2, 2, 1, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2211122 : specInv 7 5 20 [2, 2, 1, 1, 1, 2, 2] = some [2, 0, 1, 2, 2, 0, 2] :=
  specInv_white_7 [2, 2, 1, 1, 1, 2, 2] [1, 1, 2, 0, 1, 1, 2] [2, 2, 2, 0, 1, 0, 2] [2, 0, 1, 2, 2, 0, 2] demoR1_2211122 demoR2_2211122 demoC_2211122 demoM_2211122

theorem demoR1_0021122 : invRung 7 5 20 [0, 0, 2, 1, 1, 2, 2] [0, 0, 2, 1, 1, 2, 2] 1 2 false = ([1, 0, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_0021122 : invRung 7 5 20 [0, 0, 2, 1, 1, 2, 2] [1, 0, 0, 1, 0, 2, 2] 3 1 true = ([2, 1, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_0021122 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 2, 2] = [0, 0, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_0021122 : fieldMul 7 5 20 [0, 0, 2, 2, 1, 2, 2] [0, 0, 2, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021122 : mirrorTrits [0, 0, 2, 2, 1, 2, 2] = [0, 0, 1, 1, 2, 1, 1] := by
  decide

theorem demoInv_0021122 : specInv 7 5 20 [0, 0, 2, 1, 1, 2, 2] = some [0, 0, 1, 1, 2, 1, 1] :=
  specInv_mirror_7 [0, 0, 2, 1, 1, 2, 2] [1, 0, 0, 1, 0, 2, 2] [2, 1, 0, 2, 2, 2, 2] [0, 0, 2, 2, 1, 2, 2] [0, 0, 1, 1, 2, 1, 1] demoR1_0021122 demoR2_0021122 demoC_0021122 demoM_0021122 demoMir_0021122

theorem demoR1_1021122 : invRung 7 5 20 [1, 0, 2, 1, 1, 2, 2] [1, 0, 2, 1, 1, 2, 2] 1 2 false = ([0, 1, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1021122 : invRung 7 5 20 [1, 0, 2, 1, 1, 2, 2] [0, 1, 2, 0, 1, 0, 0] 3 1 true = ([1, 0, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_1021122 : fieldCube 7 5 20 [1, 0, 0, 2, 0, 2, 0] = [2, 2, 1, 0, 2, 1, 1] := by
  decide

theorem demoM_1021122 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 1, 1] [1, 0, 2, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1021122 : specInv 7 5 20 [1, 0, 2, 1, 1, 2, 2] = some [2, 2, 1, 0, 2, 1, 1] :=
  specInv_white_7 [1, 0, 2, 1, 1, 2, 2] [0, 1, 2, 0, 1, 0, 0] [1, 0, 0, 2, 0, 2, 0] [2, 2, 1, 0, 2, 1, 1] demoR1_1021122 demoR2_1021122 demoC_1021122 demoM_1021122

theorem demoR1_2021122 : invRung 7 5 20 [2, 0, 2, 1, 1, 2, 2] [2, 0, 2, 1, 1, 2, 2] 1 2 false = ([2, 2, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_2021122 : invRung 7 5 20 [2, 0, 2, 1, 1, 2, 2] [2, 2, 1, 1, 0, 1, 0] 3 1 true = ([0, 2, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_2021122 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 2, 0] = [2, 0, 2, 0, 2, 0, 1] := by
  decide

theorem demoM_2021122 : fieldMul 7 5 20 [2, 0, 2, 0, 2, 0, 1] [2, 0, 2, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021122 : mirrorTrits [2, 0, 2, 0, 2, 0, 1] = [1, 0, 1, 0, 1, 0, 2] := by
  decide

theorem demoInv_2021122 : specInv 7 5 20 [2, 0, 2, 1, 1, 2, 2] = some [1, 0, 1, 0, 1, 0, 2] :=
  specInv_mirror_7 [2, 0, 2, 1, 1, 2, 2] [2, 2, 1, 1, 0, 1, 0] [0, 2, 2, 0, 1, 2, 0] [2, 0, 2, 0, 2, 0, 1] [1, 0, 1, 0, 1, 0, 2] demoR1_2021122 demoR2_2021122 demoC_2021122 demoM_2021122 demoMir_2021122

theorem demoR1_0121122 : invRung 7 5 20 [0, 1, 2, 1, 1, 2, 2] [0, 1, 2, 1, 1, 2, 2] 1 2 false = ([2, 1, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_0121122 : invRung 7 5 20 [0, 1, 2, 1, 1, 2, 2] [2, 1, 1, 0, 0, 2, 1] 3 1 true = ([1, 1, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0121122 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 0, 0] = [2, 1, 1, 2, 0, 2, 2] := by
  decide

theorem demoM_0121122 : fieldMul 7 5 20 [2, 1, 1, 2, 0, 2, 2] [0, 1, 2, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0121122 : specInv 7 5 20 [0, 1, 2, 1, 1, 2, 2] = some [2, 1, 1, 2, 0, 2, 2] :=
  specInv_white_7 [0, 1, 2, 1, 1, 2, 2] [2, 1, 1, 0, 0, 2, 1] [1, 1, 1, 1, 1, 0, 0] [2, 1, 1, 2, 0, 2, 2] demoR1_0121122 demoR2_0121122 demoC_0121122 demoM_0121122

theorem demoR1_1121122 : invRung 7 5 20 [1, 1, 2, 1, 1, 2, 2] [1, 1, 2, 1, 1, 2, 2] 1 2 false = ([0, 0, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1121122 : invRung 7 5 20 [1, 1, 2, 1, 1, 2, 2] [0, 0, 0, 2, 1, 0, 2] 3 1 true = ([2, 1, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1121122 : fieldCube 7 5 20 [2, 1, 0, 1, 2, 2, 0] = [2, 1, 0, 0, 2, 2, 0] := by
  decide

theorem demoM_1121122 : fieldMul 7 5 20 [2, 1, 0, 0, 2, 2, 0] [1, 1, 2, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121122 : mirrorTrits [2, 1, 0, 0, 2, 2, 0] = [1, 2, 0, 0, 1, 1, 0] := by
  decide

theorem demoInv_1121122 : specInv 7 5 20 [1, 1, 2, 1, 1, 2, 2] = some [1, 2, 0, 0, 1, 1, 0] :=
  specInv_mirror_7 [1, 1, 2, 1, 1, 2, 2] [0, 0, 0, 2, 1, 0, 2] [2, 1, 0, 1, 2, 2, 0] [2, 1, 0, 0, 2, 2, 0] [1, 2, 0, 0, 1, 1, 0] demoR1_1121122 demoR2_1121122 demoC_1121122 demoM_1121122 demoMir_1121122

theorem demoR1_2121122 : invRung 7 5 20 [2, 1, 2, 1, 1, 2, 2] [2, 1, 2, 1, 1, 2, 2] 1 2 false = ([0, 1, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2121122 : invRung 7 5 20 [2, 1, 2, 1, 1, 2, 2] [0, 1, 1, 2, 0, 0, 2] 3 1 true = ([1, 0, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2121122 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 1, 0] = [2, 1, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_2121122 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 1, 0] [2, 1, 2, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2121122 : specInv 7 5 20 [2, 1, 2, 1, 1, 2, 2] = some [2, 1, 1, 0, 1, 1, 0] :=
  specInv_white_7 [2, 1, 2, 1, 1, 2, 2] [0, 1, 1, 2, 0, 0, 2] [1, 0, 1, 0, 0, 1, 0] [2, 1, 1, 0, 1, 1, 0] demoR1_2121122 demoR2_2121122 demoC_2121122 demoM_2121122

theorem demoR1_0221122 : invRung 7 5 20 [0, 2, 2, 1, 1, 2, 2] [0, 2, 2, 1, 1, 2, 2] 1 2 false = ([1, 0, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_0221122 : invRung 7 5 20 [0, 2, 2, 1, 1, 2, 2] [1, 0, 0, 0, 2, 1, 1] 3 1 true = ([0, 0, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_0221122 : fieldCube 7 5 20 [0, 0, 2, 2, 2, 2, 0] = [1, 1, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_0221122 : fieldMul 7 5 20 [1, 1, 1, 2, 2, 0, 2] [0, 2, 2, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0221122 : mirrorTrits [1, 1, 1, 2, 2, 0, 2] = [2, 2, 2, 1, 1, 0, 1] := by
  decide

theorem demoInv_0221122 : specInv 7 5 20 [0, 2, 2, 1, 1, 2, 2] = some [2, 2, 2, 1, 1, 0, 1] :=
  specInv_mirror_7 [0, 2, 2, 1, 1, 2, 2] [1, 0, 0, 0, 2, 1, 1] [0, 0, 2, 2, 2, 2, 0] [1, 1, 1, 2, 2, 0, 2] [2, 2, 2, 1, 1, 0, 1] demoR1_0221122 demoR2_0221122 demoC_0221122 demoM_0221122 demoMir_0221122

theorem demoR1_1221122 : invRung 7 5 20 [1, 2, 2, 1, 1, 2, 2] [1, 2, 2, 1, 1, 2, 2] 1 2 false = ([1, 1, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_1221122 : invRung 7 5 20 [1, 2, 2, 1, 1, 2, 2] [1, 1, 2, 0, 2, 1, 0] 3 1 true = ([1, 0, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_1221122 : fieldCube 7 5 20 [1, 0, 2, 0, 0, 2, 1] = [0, 0, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_1221122 : fieldMul 7 5 20 [0, 0, 1, 1, 0, 0, 1] [1, 2, 2, 1, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1221122 : specInv 7 5 20 [1, 2, 2, 1, 1, 2, 2] = some [0, 0, 1, 1, 0, 0, 1] :=
  specInv_white_7 [1, 2, 2, 1, 1, 2, 2] [1, 1, 2, 0, 2, 1, 0] [1, 0, 2, 0, 0, 2, 1] [0, 0, 1, 1, 0, 0, 1] demoR1_1221122 demoR2_1221122 demoC_1221122 demoM_1221122

theorem demoR1_2221122 : invRung 7 5 20 [2, 2, 2, 1, 1, 2, 2] [2, 2, 2, 1, 1, 2, 2] 1 2 false = ([2, 0, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_2221122 : invRung 7 5 20 [2, 2, 2, 1, 1, 2, 2] [2, 0, 2, 0, 0, 2, 1] 3 1 true = ([1, 2, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_2221122 : fieldCube 7 5 20 [1, 2, 2, 2, 0, 1, 2] = [1, 0, 1, 1, 0, 2, 0] := by
  decide

theorem demoM_2221122 : fieldMul 7 5 20 [1, 0, 1, 1, 0, 2, 0] [2, 2, 2, 1, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221122 : mirrorTrits [1, 0, 1, 1, 0, 2, 0] = [2, 0, 2, 2, 0, 1, 0] := by
  decide

theorem demoInv_2221122 : specInv 7 5 20 [2, 2, 2, 1, 1, 2, 2] = some [2, 0, 2, 2, 0, 1, 0] :=
  specInv_mirror_7 [2, 2, 2, 1, 1, 2, 2] [2, 0, 2, 0, 0, 2, 1] [1, 2, 2, 2, 0, 1, 2] [1, 0, 1, 1, 0, 2, 0] [2, 0, 2, 2, 0, 1, 0] demoR1_2221122 demoR2_2221122 demoC_2221122 demoM_2221122 demoMir_2221122

theorem demoR1_0002122 : invRung 7 5 20 [0, 0, 0, 2, 1, 2, 2] [0, 0, 0, 2, 1, 2, 2] 1 2 false = ([1, 2, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_0002122 : invRung 7 5 20 [0, 0, 0, 2, 1, 2, 2] [1, 2, 2, 0, 1, 1, 0] 3 1 true = ([1, 1, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0002122 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 1, 1] = [2, 2, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_0002122 : fieldMul 7 5 20 [2, 2, 0, 2, 2, 2, 1] [0, 0, 0, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0002122 : specInv 7 5 20 [0, 0, 0, 2, 1, 2, 2] = some [2, 2, 0, 2, 2, 2, 1] :=
  specInv_white_7 [0, 0, 0, 2, 1, 2, 2] [1, 2, 2, 0, 1, 1, 0] [1, 1, 1, 0, 0, 1, 1] [2, 2, 0, 2, 2, 2, 1] demoR1_0002122 demoR2_0002122 demoC_0002122 demoM_0002122

theorem demoR1_1002122 : invRung 7 5 20 [1, 0, 0, 2, 1, 2, 2] [1, 0, 0, 2, 1, 2, 2] 1 2 false = ([2, 2, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1002122 : invRung 7 5 20 [1, 0, 0, 2, 1, 2, 2] [2, 2, 2, 2, 1, 0, 2] 3 1 true = ([1, 1, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1002122 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 0, 0] = [1, 1, 0, 2, 0, 1, 2] := by
  decide

theorem demoM_1002122 : fieldMul 7 5 20 [1, 1, 0, 2, 0, 1, 2] [1, 0, 0, 2, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002122 : mirrorTrits [1, 1, 0, 2, 0, 1, 2] = [2, 2, 0, 1, 0, 2, 1] := by
  decide

theorem demoInv_1002122 : specInv 7 5 20 [1, 0, 0, 2, 1, 2, 2] = some [2, 2, 0, 1, 0, 2, 1] :=
  specInv_mirror_7 [1, 0, 0, 2, 1, 2, 2] [2, 2, 2, 2, 1, 0, 2] [1, 1, 1, 0, 1, 0, 0] [1, 1, 0, 2, 0, 1, 2] [2, 2, 0, 1, 0, 2, 1] demoR1_1002122 demoR2_1002122 demoC_1002122 demoM_1002122 demoMir_1002122

theorem demoR1_2002122 : invRung 7 5 20 [2, 0, 0, 2, 1, 2, 2] [2, 0, 0, 2, 1, 2, 2] 1 2 false = ([0, 0, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2002122 : invRung 7 5 20 [2, 0, 0, 2, 1, 2, 2] [0, 0, 0, 1, 0, 2, 1] 3 1 true = ([1, 0, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_2002122 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 1, 1] = [1, 1, 2, 0, 2, 0, 1] := by
  decide

theorem demoM_2002122 : fieldMul 7 5 20 [1, 1, 2, 0, 2, 0, 1] [2, 0, 0, 2, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002122 : mirrorTrits [1, 1, 2, 0, 2, 0, 1] = [2, 2, 1, 0, 1, 0, 2] := by
  decide

theorem demoInv_2002122 : specInv 7 5 20 [2, 0, 0, 2, 1, 2, 2] = some [2, 2, 1, 0, 1, 0, 2] :=
  specInv_mirror_7 [2, 0, 0, 2, 1, 2, 2] [0, 0, 0, 1, 0, 2, 1] [1, 0, 2, 2, 2, 1, 1] [1, 1, 2, 0, 2, 0, 1] [2, 2, 1, 0, 1, 0, 2] demoR1_2002122 demoR2_2002122 demoC_2002122 demoM_2002122 demoMir_2002122

theorem demoR1_0102122 : invRung 7 5 20 [0, 1, 0, 2, 1, 2, 2] [0, 1, 0, 2, 1, 2, 2] 1 2 false = ([1, 0, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_0102122 : invRung 7 5 20 [0, 1, 0, 2, 1, 2, 2] [1, 0, 2, 2, 1, 1, 1] 3 1 true = ([0, 0, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_0102122 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 1, 2] = [1, 1, 2, 0, 0, 1, 2] := by
  decide

theorem demoM_0102122 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 1, 2] [0, 1, 0, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0102122 : specInv 7 5 20 [0, 1, 0, 2, 1, 2, 2] = some [1, 1, 2, 0, 0, 1, 2] :=
  specInv_white_7 [0, 1, 0, 2, 1, 2, 2] [1, 0, 2, 2, 1, 1, 1] [0, 0, 0, 0, 1, 1, 2] [1, 1, 2, 0, 0, 1, 2] demoR1_0102122 demoR2_0102122 demoC_0102122 demoM_0102122

theorem demoR1_1102122 : invRung 7 5 20 [1, 1, 0, 2, 1, 2, 2] [1, 1, 0, 2, 1, 2, 2] 1 2 false = ([2, 0, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_1102122 : invRung 7 5 20 [1, 1, 0, 2, 1, 2, 2] [2, 0, 0, 0, 1, 0, 2] 3 1 true = ([1, 0, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_1102122 : fieldCube 7 5 20 [1, 0, 0, 2, 0, 1, 2] = [1, 0, 1, 2, 0, 2, 1] := by
  decide

theorem demoM_1102122 : fieldMul 7 5 20 [1, 0, 1, 2, 0, 2, 1] [1, 1, 0, 2, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102122 : mirrorTrits [1, 0, 1, 2, 0, 2, 1] = [2, 0, 2, 1, 0, 1, 2] := by
  decide

theorem demoInv_1102122 : specInv 7 5 20 [1, 1, 0, 2, 1, 2, 2] = some [2, 0, 2, 1, 0, 1, 2] :=
  specInv_mirror_7 [1, 1, 0, 2, 1, 2, 2] [2, 0, 0, 0, 1, 0, 2] [1, 0, 0, 2, 0, 1, 2] [1, 0, 1, 2, 0, 2, 1] [2, 0, 2, 1, 0, 1, 2] demoR1_1102122 demoR2_1102122 demoC_1102122 demoM_1102122 demoMir_1102122

theorem demoR1_2102122 : invRung 7 5 20 [2, 1, 0, 2, 1, 2, 2] [2, 1, 0, 2, 1, 2, 2] 1 2 false = ([2, 0, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2102122 : invRung 7 5 20 [2, 1, 0, 2, 1, 2, 2] [2, 0, 1, 0, 0, 1, 0] 3 1 true = ([2, 1, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_2102122 : fieldCube 7 5 20 [2, 1, 0, 0, 1, 1, 2] = [0, 1, 2, 1, 0, 1, 2] := by
  decide

theorem demoM_2102122 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 1, 2] [2, 1, 0, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2102122 : specInv 7 5 20 [2, 1, 0, 2, 1, 2, 2] = some [0, 1, 2, 1, 0, 1, 2] :=
  specInv_white_7 [2, 1, 0, 2, 1, 2, 2] [2, 0, 1, 0, 0, 1, 0] [2, 1, 0, 0, 1, 1, 2] [0, 1, 2, 1, 0, 1, 2] demoR1_2102122 demoR2_2102122 demoC_2102122 demoM_2102122

theorem demoR1_0202122 : invRung 7 5 20 [0, 2, 0, 2, 1, 2, 2] [0, 2, 0, 2, 1, 2, 2] 1 2 false = ([0, 2, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_0202122 : invRung 7 5 20 [0, 2, 0, 2, 1, 2, 2] [0, 2, 1, 0, 2, 2, 1] 3 1 true = ([2, 0, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0202122 : fieldCube 7 5 20 [2, 0, 0, 0, 1, 2, 1] = [1, 1, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_0202122 : fieldMul 7 5 20 [1, 1, 1, 2, 0, 1, 0] [0, 2, 0, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0202122 : specInv 7 5 20 [0, 2, 0, 2, 1, 2, 2] = some [1, 1, 1, 2, 0, 1, 0] :=
  specInv_white_7 [0, 2, 0, 2, 1, 2, 2] [0, 2, 1, 0, 2, 2, 1] [2, 0, 0, 0, 1, 2, 1] [1, 1, 1, 2, 0, 1, 0] demoR1_0202122 demoR2_0202122 demoC_0202122 demoM_0202122

theorem demoR1_1202122 : invRung 7 5 20 [1, 2, 0, 2, 1, 2, 2] [1, 2, 0, 2, 1, 2, 2] 1 2 false = ([1, 0, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1202122 : invRung 7 5 20 [1, 2, 0, 2, 1, 2, 2] [1, 0, 0, 1, 1, 0, 2] 3 1 true = ([0, 2, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_1202122 : fieldCube 7 5 20 [0, 2, 0, 0, 0, 2, 1] = [2, 0, 1, 0, 0, 0, 2] := by
  decide

theorem demoM_1202122 : fieldMul 7 5 20 [2, 0, 1, 0, 0, 0, 2] [1, 2, 0, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1202122 : specInv 7 5 20 [1, 2, 0, 2, 1, 2, 2] = some [2, 0, 1, 0, 0, 0, 2] :=
  specInv_white_7 [1, 2, 0, 2, 1, 2, 2] [1, 0, 0, 1, 1, 0, 2] [0, 2, 0, 0, 0, 2, 1] [2, 0, 1, 0, 0, 0, 2] demoR1_1202122 demoR2_1202122 demoC_1202122 demoM_1202122

theorem demoR1_2202122 : invRung 7 5 20 [2, 2, 0, 2, 1, 2, 2] [2, 2, 0, 2, 1, 2, 2] 1 2 false = ([0, 0, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2202122 : invRung 7 5 20 [2, 2, 0, 2, 1, 2, 2] [0, 0, 1, 0, 2, 2, 0] 3 1 true = ([2, 0, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_2202122 : fieldCube 7 5 20 [2, 0, 2, 0, 1, 0, 1] = [2, 2, 2, 2, 1, 2, 1] := by
  decide

theorem demoM_2202122 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 2, 1] [2, 2, 0, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2202122 : specInv 7 5 20 [2, 2, 0, 2, 1, 2, 2] = some [2, 2, 2, 2, 1, 2, 1] :=
  specInv_white_7 [2, 2, 0, 2, 1, 2, 2] [0, 0, 1, 0, 2, 2, 0] [2, 0, 2, 0, 1, 0, 1] [2, 2, 2, 2, 1, 2, 1] demoR1_2202122 demoR2_2202122 demoC_2202122 demoM_2202122

theorem demoR1_0012122 : invRung 7 5 20 [0, 0, 1, 2, 1, 2, 2] [0, 0, 1, 2, 1, 2, 2] 1 2 false = ([0, 1, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0012122 : invRung 7 5 20 [0, 0, 1, 2, 1, 2, 2] [0, 1, 2, 1, 2, 1, 2] 3 1 true = ([1, 0, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0012122 : fieldCube 7 5 20 [1, 0, 2, 1, 2, 2, 2] = [1, 0, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_0012122 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 1, 1] [0, 0, 1, 2, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0012122 : mirrorTrits [1, 0, 1, 1, 1, 1, 1] = [2, 0, 2, 2, 2, 2, 2] := by
  decide

theorem demoInv_0012122 : specInv 7 5 20 [0, 0, 1, 2, 1, 2, 2] = some [2, 0, 2, 2, 2, 2, 2] :=
  specInv_mirror_7 [0, 0, 1, 2, 1, 2, 2] [0, 1, 2, 1, 2, 1, 2] [1, 0, 2, 1, 2, 2, 2] [1, 0, 1, 1, 1, 1, 1] [2, 0, 2, 2, 2, 2, 2] demoR1_0012122 demoR2_0012122 demoC_0012122 demoM_0012122 demoMir_0012122

theorem demoR1_1012122 : invRung 7 5 20 [1, 0, 1, 2, 1, 2, 2] [1, 0, 1, 2, 1, 2, 2] 1 2 false = ([2, 2, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_1012122 : invRung 7 5 20 [1, 0, 1, 2, 1, 2, 2] [2, 2, 2, 2, 1, 0, 1] 3 1 true = ([0, 0, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_1012122 : fieldCube 7 5 20 [0, 0, 2, 0, 2, 1, 1] = [1, 1, 0, 0, 2, 1, 1] := by
  decide

theorem demoM_1012122 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 1, 1] [1, 0, 1, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1012122 : specInv 7 5 20 [1, 0, 1, 2, 1, 2, 2] = some [1, 1, 0, 0, 2, 1, 1] :=
  specInv_white_7 [1, 0, 1, 2, 1, 2, 2] [2, 2, 2, 2, 1, 0, 1] [0, 0, 2, 0, 2, 1, 1] [1, 1, 0, 0, 2, 1, 1] demoR1_1012122 demoR2_1012122 demoC_1012122 demoM_1012122

theorem demoR1_2012122 : invRung 7 5 20 [2, 0, 1, 2, 1, 2, 2] [2, 0, 1, 2, 1, 2, 2] 1 2 false = ([1, 0, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_2012122 : invRung 7 5 20 [2, 0, 1, 2, 1, 2, 2] [1, 0, 0, 2, 1, 1, 1] 3 1 true = ([2, 1, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_2012122 : fieldCube 7 5 20 [2, 1, 0, 2, 0, 2, 2] = [0, 1, 2, 0, 1, 0, 0] := by
  decide

theorem demoM_2012122 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 0, 0] [2, 0, 1, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2012122 : specInv 7 5 20 [2, 0, 1, 2, 1, 2, 2] = some [0, 1, 2, 0, 1, 0, 0] :=
  specInv_white_7 [2, 0, 1, 2, 1, 2, 2] [1, 0, 0, 2, 1, 1, 1] [2, 1, 0, 2, 0, 2, 2] [0, 1, 2, 0, 1, 0, 0] demoR1_2012122 demoR2_2012122 demoC_2012122 demoM_2012122

theorem demoR1_0112122 : invRung 7 5 20 [0, 1, 1, 2, 1, 2, 2] [0, 1, 1, 2, 1, 2, 2] 1 2 false = ([2, 1, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_0112122 : invRung 7 5 20 [0, 1, 1, 2, 1, 2, 2] [2, 1, 1, 2, 1, 2, 0] 3 1 true = ([1, 1, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_0112122 : fieldCube 7 5 20 [1, 1, 1, 2, 0, 0, 0] = [0, 0, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_0112122 : fieldMul 7 5 20 [0, 0, 2, 1, 0, 2, 1] [0, 1, 1, 2, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112122 : mirrorTrits [0, 0, 2, 1, 0, 2, 1] = [0, 0, 1, 2, 0, 1, 2] := by
  decide

theorem demoInv_0112122 : specInv 7 5 20 [0, 1, 1, 2, 1, 2, 2] = some [0, 0, 1, 2, 0, 1, 2] :=
  specInv_mirror_7 [0, 1, 1, 2, 1, 2, 2] [2, 1, 1, 2, 1, 2, 0] [1, 1, 1, 2, 0, 0, 0] [0, 0, 2, 1, 0, 2, 1] [0, 0, 1, 2, 0, 1, 2] demoR1_0112122 demoR2_0112122 demoC_0112122 demoM_0112122 demoMir_0112122

theorem demoR1_1112122 : invRung 7 5 20 [1, 1, 1, 2, 1, 2, 2] [1, 1, 1, 2, 1, 2, 2] 1 2 false = ([1, 1, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_1112122 : invRung 7 5 20 [1, 1, 1, 2, 1, 2, 2] [1, 1, 0, 1, 1, 2, 0] 3 1 true = ([2, 0, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_1112122 : fieldCube 7 5 20 [2, 0, 1, 2, 1, 2, 1] = [0, 1, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_1112122 : fieldMul 7 5 20 [0, 1, 0, 2, 0, 0, 1] [1, 1, 1, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1112122 : specInv 7 5 20 [1, 1, 1, 2, 1, 2, 2] = some [0, 1, 0, 2, 0, 0, 1] :=
  specInv_white_7 [1, 1, 1, 2, 1, 2, 2] [1, 1, 0, 1, 1, 2, 0] [2, 0, 1, 2, 1, 2, 1] [0, 1, 0, 2, 0, 0, 1] demoR1_1112122 demoR2_1112122 demoC_1112122 demoM_1112122

theorem demoR1_2112122 : invRung 7 5 20 [2, 1, 1, 2, 1, 2, 2] [2, 1, 1, 2, 1, 2, 2] 1 2 false = ([2, 0, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2112122 : invRung 7 5 20 [2, 1, 1, 2, 1, 2, 2] [2, 0, 2, 1, 2, 0, 1] 3 1 true = ([1, 2, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_2112122 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 2, 2] = [2, 0, 2, 0, 1, 2, 1] := by
  decide

theorem demoM_2112122 : fieldMul 7 5 20 [2, 0, 2, 0, 1, 2, 1] [2, 1, 1, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2112122 : specInv 7 5 20 [2, 1, 1, 2, 1, 2, 2] = some [2, 0, 2, 0, 1, 2, 1] :=
  specInv_white_7 [2, 1, 1, 2, 1, 2, 2] [2, 0, 2, 1, 2, 0, 1] [1, 2, 2, 2, 2, 2, 2] [2, 0, 2, 0, 1, 2, 1] demoR1_2112122 demoR2_2112122 demoC_2112122 demoM_2112122

theorem demoR1_0212122 : invRung 7 5 20 [0, 2, 1, 2, 1, 2, 2] [0, 2, 1, 2, 1, 2, 2] 1 2 false = ([1, 1, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_0212122 : invRung 7 5 20 [0, 2, 1, 2, 1, 2, 2] [1, 1, 0, 2, 1, 2, 0] 3 1 true = ([0, 0, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0212122 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 0, 1] = [1, 0, 0, 0, 1, 1, 0] := by
  decide

theorem demoM_0212122 : fieldMul 7 5 20 [1, 0, 0, 0, 1, 1, 0] [0, 2, 1, 2, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212122 : mirrorTrits [1, 0, 0, 0, 1, 1, 0] = [2, 0, 0, 0, 2, 2, 0] := by
  decide

theorem demoInv_0212122 : specInv 7 5 20 [0, 2, 1, 2, 1, 2, 2] = some [2, 0, 0, 0, 2, 2, 0] :=
  specInv_mirror_7 [0, 2, 1, 2, 1, 2, 2] [1, 1, 0, 2, 1, 2, 0] [0, 0, 0, 1, 2, 0, 1] [1, 0, 0, 0, 1, 1, 0] [2, 0, 0, 0, 2, 2, 0] demoR1_0212122 demoR2_0212122 demoC_0212122 demoM_0212122 demoMir_0212122

theorem demoR1_1212122 : invRung 7 5 20 [1, 2, 1, 2, 1, 2, 2] [1, 2, 1, 2, 1, 2, 2] 1 2 false = ([0, 1, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_1212122 : invRung 7 5 20 [1, 2, 1, 2, 1, 2, 2] [0, 1, 1, 0, 1, 2, 2] 3 1 true = ([0, 1, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_1212122 : fieldCube 7 5 20 [0, 1, 1, 1, 2, 0, 0] = [1, 2, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_1212122 : fieldMul 7 5 20 [1, 2, 1, 0, 0, 0, 0] [1, 2, 1, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1212122 : specInv 7 5 20 [1, 2, 1, 2, 1, 2, 2] = some [1, 2, 1, 0, 0, 0, 0] :=
  specInv_white_7 [1, 2, 1, 2, 1, 2, 2] [0, 1, 1, 0, 1, 2, 2] [0, 1, 1, 1, 2, 0, 0] [1, 2, 1, 0, 0, 0, 0] demoR1_1212122 demoR2_1212122 demoC_1212122 demoM_1212122

theorem demoR1_2212122 : invRung 7 5 20 [2, 2, 1, 2, 1, 2, 2] [2, 2, 1, 2, 1, 2, 2] 1 2 false = ([0, 2, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_2212122 : invRung 7 5 20 [2, 2, 1, 2, 1, 2, 2] [0, 2, 1, 1, 2, 2, 2] 3 1 true = ([1, 1, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_2212122 : fieldCube 7 5 20 [1, 1, 1, 2, 1, 1, 0] = [1, 2, 0, 2, 1, 1, 1] := by
  decide

theorem demoM_2212122 : fieldMul 7 5 20 [1, 2, 0, 2, 1, 1, 1] [2, 2, 1, 2, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212122 : mirrorTrits [1, 2, 0, 2, 1, 1, 1] = [2, 1, 0, 1, 2, 2, 2] := by
  decide

theorem demoInv_2212122 : specInv 7 5 20 [2, 2, 1, 2, 1, 2, 2] = some [2, 1, 0, 1, 2, 2, 2] :=
  specInv_mirror_7 [2, 2, 1, 2, 1, 2, 2] [0, 2, 1, 1, 2, 2, 2] [1, 1, 1, 2, 1, 1, 0] [1, 2, 0, 2, 1, 1, 1] [2, 1, 0, 1, 2, 2, 2] demoR1_2212122 demoR2_2212122 demoC_2212122 demoM_2212122 demoMir_2212122

theorem demoR1_0022122 : invRung 7 5 20 [0, 0, 2, 2, 1, 2, 2] [0, 0, 2, 2, 1, 2, 2] 1 2 false = ([0, 2, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_0022122 : invRung 7 5 20 [0, 0, 2, 2, 1, 2, 2] [0, 2, 2, 0, 2, 0, 1] 3 1 true = ([1, 0, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_0022122 : fieldCube 7 5 20 [1, 0, 0, 1, 1, 1, 1] = [0, 0, 1, 2, 2, 1, 1] := by
  decide

theorem demoM_0022122 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 1, 1] [0, 0, 2, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0022122 : specInv 7 5 20 [0, 0, 2, 2, 1, 2, 2] = some [0, 0, 1, 2, 2, 1, 1] :=
  specInv_white_7 [0, 0, 2, 2, 1, 2, 2] [0, 2, 2, 0, 2, 0, 1] [1, 0, 0, 1, 1, 1, 1] [0, 0, 1, 2, 2, 1, 1] demoR1_0022122 demoR2_0022122 demoC_0022122 demoM_0022122

theorem demoR1_1022122 : invRung 7 5 20 [1, 0, 2, 2, 1, 2, 2] [1, 0, 2, 2, 1, 2, 2] 1 2 false = ([2, 1, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_1022122 : invRung 7 5 20 [1, 0, 2, 2, 1, 2, 2] [2, 1, 0, 0, 0, 2, 2] 3 1 true = ([1, 1, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_1022122 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 1, 0] = [2, 0, 1, 0, 1, 0, 2] := by
  decide

theorem demoM_1022122 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 0, 2] [1, 0, 2, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1022122 : specInv 7 5 20 [1, 0, 2, 2, 1, 2, 2] = some [2, 0, 1, 0, 1, 0, 2] :=
  specInv_white_7 [1, 0, 2, 2, 1, 2, 2] [2, 1, 0, 0, 0, 2, 2] [1, 1, 1, 0, 2, 1, 0] [2, 0, 1, 0, 1, 0, 2] demoR1_1022122 demoR2_1022122 demoC_1022122 demoM_1022122

theorem demoR1_2022122 : invRung 7 5 20 [2, 0, 2, 2, 1, 2, 2] [2, 0, 2, 2, 1, 2, 2] 1 2 false = ([1, 2, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2022122 : invRung 7 5 20 [2, 0, 2, 2, 1, 2, 2] [1, 2, 2, 1, 1, 2, 2] 3 1 true = ([0, 0, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_2022122 : fieldCube 7 5 20 [0, 0, 0, 2, 0, 2, 0] = [1, 2, 1, 0, 2, 1, 1] := by
  decide

theorem demoM_2022122 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 1, 1] [2, 0, 2, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2022122 : specInv 7 5 20 [2, 0, 2, 2, 1, 2, 2] = some [1, 2, 1, 0, 2, 1, 1] :=
  specInv_white_7 [2, 0, 2, 2, 1, 2, 2] [1, 2, 2, 1, 1, 2, 2] [0, 0, 0, 2, 0, 2, 0] [1, 2, 1, 0, 2, 1, 1] demoR1_2022122 demoR2_2022122 demoC_2022122 demoM_2022122

theorem demoR1_0122122 : invRung 7 5 20 [0, 1, 2, 2, 1, 2, 2] [0, 1, 2, 2, 1, 2, 2] 1 2 false = ([1, 0, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_0122122 : invRung 7 5 20 [0, 1, 2, 2, 1, 2, 2] [1, 0, 2, 2, 2, 1, 1] 3 1 true = ([0, 0, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_0122122 : fieldCube 7 5 20 [0, 0, 2, 1, 1, 1, 0] = [2, 2, 2, 1, 1, 0, 2] := by
  decide

theorem demoM_0122122 : fieldMul 7 5 20 [2, 2, 2, 1, 1, 0, 2] [0, 1, 2, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0122122 : specInv 7 5 20 [0, 1, 2, 2, 1, 2, 2] = some [2, 2, 2, 1, 1, 0, 2] :=
  specInv_white_7 [0, 1, 2, 2, 1, 2, 2] [1, 0, 2, 2, 2, 1, 1] [0, 0, 2, 1, 1, 1, 0] [2, 2, 2, 1, 1, 0, 2] demoR1_0122122 demoR2_0122122 demoC_0122122 demoM_0122122

theorem demoR1_1122122 : invRung 7 5 20 [1, 1, 2, 2, 1, 2, 2] [1, 1, 2, 2, 1, 2, 2] 1 2 false = ([0, 0, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_1122122 : invRung 7 5 20 [1, 1, 2, 2, 1, 2, 2] [0, 0, 0, 2, 2, 2, 2] 3 1 true = ([2, 0, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1122122 : fieldCube 7 5 20 [2, 0, 0, 0, 1, 1, 1] = [0, 0, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_1122122 : fieldMul 7 5 20 [0, 0, 0, 2, 2, 0, 1] [1, 1, 2, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1122122 : specInv 7 5 20 [1, 1, 2, 2, 1, 2, 2] = some [0, 0, 0, 2, 2, 0, 1] :=
  specInv_white_7 [1, 1, 2, 2, 1, 2, 2] [0, 0, 0, 2, 2, 2, 2] [2, 0, 0, 0, 1, 1, 1] [0, 0, 0, 2, 2, 0, 1] demoR1_1122122 demoR2_1122122 demoC_1122122 demoM_1122122

theorem demoR1_2122122 : invRung 7 5 20 [2, 1, 2, 2, 1, 2, 2] [2, 1, 2, 2, 1, 2, 2] 1 2 false = ([1, 1, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_2122122 : invRung 7 5 20 [2, 1, 2, 2, 1, 2, 2] [1, 1, 1, 2, 2, 0, 2] 3 1 true = ([2, 2, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_2122122 : fieldCube 7 5 20 [2, 2, 0, 0, 0, 1, 1] = [0, 2, 0, 0, 2, 2, 0] := by
  decide

theorem demoM_2122122 : fieldMul 7 5 20 [0, 2, 0, 0, 2, 2, 0] [2, 1, 2, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2122122 : specInv 7 5 20 [2, 1, 2, 2, 1, 2, 2] = some [0, 2, 0, 0, 2, 2, 0] :=
  specInv_white_7 [2, 1, 2, 2, 1, 2, 2] [1, 1, 1, 2, 2, 0, 2] [2, 2, 0, 0, 0, 1, 1] [0, 2, 0, 0, 2, 2, 0] demoR1_2122122 demoR2_2122122 demoC_2122122 demoM_2122122

theorem demoR1_0222122 : invRung 7 5 20 [0, 2, 2, 2, 1, 2, 2] [0, 2, 2, 2, 1, 2, 2] 1 2 false = ([0, 0, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_0222122 : invRung 7 5 20 [0, 2, 2, 2, 1, 2, 2] [0, 0, 0, 0, 0, 2, 0] 3 1 true = ([1, 0, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0222122 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 2, 1] = [2, 1, 0, 2, 0, 0, 2] := by
  decide

theorem demoM_0222122 : fieldMul 7 5 20 [2, 1, 0, 2, 0, 0, 2] [0, 2, 2, 2, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222122 : mirrorTrits [2, 1, 0, 2, 0, 0, 2] = [1, 2, 0, 1, 0, 0, 1] := by
  decide

theorem demoInv_0222122 : specInv 7 5 20 [0, 2, 2, 2, 1, 2, 2] = some [1, 2, 0, 1, 0, 0, 1] :=
  specInv_mirror_7 [0, 2, 2, 2, 1, 2, 2] [0, 0, 0, 0, 0, 2, 0] [1, 0, 2, 2, 1, 2, 1] [2, 1, 0, 2, 0, 0, 2] [1, 2, 0, 1, 0, 0, 1] demoR1_0222122 demoR2_0222122 demoC_0222122 demoM_0222122 demoMir_0222122

theorem demoR1_1222122 : invRung 7 5 20 [1, 2, 2, 2, 1, 2, 2] [1, 2, 2, 2, 1, 2, 2] 1 2 false = ([2, 2, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_1222122 : invRung 7 5 20 [1, 2, 2, 2, 1, 2, 2] [2, 2, 1, 1, 1, 1, 2] 3 1 true = ([2, 0, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_1222122 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 1, 2] = [2, 0, 1, 2, 0, 2, 0] := by
  decide

theorem demoM_1222122 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 2, 0] [1, 2, 2, 2, 1, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222122 : mirrorTrits [2, 0, 1, 2, 0, 2, 0] = [1, 0, 2, 1, 0, 1, 0] := by
  decide

theorem demoInv_1222122 : specInv 7 5 20 [1, 2, 2, 2, 1, 2, 2] = some [1, 0, 2, 1, 0, 1, 0] :=
  specInv_mirror_7 [1, 2, 2, 2, 1, 2, 2] [2, 2, 1, 1, 1, 1, 2] [2, 0, 2, 2, 0, 1, 2] [2, 0, 1, 2, 0, 2, 0] [1, 0, 2, 1, 0, 1, 0] demoR1_1222122 demoR2_1222122 demoC_1222122 demoM_1222122 demoMir_1222122

theorem demoR1_2222122 : invRung 7 5 20 [2, 2, 2, 2, 1, 2, 2] [2, 2, 2, 2, 1, 2, 2] 1 2 false = ([2, 1, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_2222122 : invRung 7 5 20 [2, 2, 2, 2, 1, 2, 2] [2, 1, 1, 1, 2, 2, 0] 3 1 true = ([0, 1, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_2222122 : fieldCube 7 5 20 [0, 1, 1, 2, 1, 1, 2] = [0, 1, 1, 1, 0, 0, 0] := by
  decide

theorem demoM_2222122 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 0, 0] [2, 2, 2, 2, 1, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2222122 : specInv 7 5 20 [2, 2, 2, 2, 1, 2, 2] = some [0, 1, 1, 1, 0, 0, 0] :=
  specInv_white_7 [2, 2, 2, 2, 1, 2, 2] [2, 1, 1, 1, 2, 2, 0] [0, 1, 1, 2, 1, 1, 2] [0, 1, 1, 1, 0, 0, 0] demoR1_2222122 demoR2_2222122 demoC_2222122 demoM_2222122

theorem demoR1_0000222 : invRung 7 5 20 [0, 0, 0, 0, 2, 2, 2] [0, 0, 0, 0, 2, 2, 2] 1 2 false = ([0, 2, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_0000222 : invRung 7 5 20 [0, 0, 0, 0, 2, 2, 2] [0, 2, 1, 1, 0, 1, 0] 3 1 true = ([0, 0, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_0000222 : fieldCube 7 5 20 [0, 0, 0, 1, 1, 1, 2] = [2, 1, 0, 0, 0, 2, 2] := by
  decide

theorem demoM_0000222 : fieldMul 7 5 20 [2, 1, 0, 0, 0, 2, 2] [0, 0, 0, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000222 : mirrorTrits [2, 1, 0, 0, 0, 2, 2] = [1, 2, 0, 0, 0, 1, 1] := by
  decide

theorem demoInv_0000222 : specInv 7 5 20 [0, 0, 0, 0, 2, 2, 2] = some [1, 2, 0, 0, 0, 1, 1] :=
  specInv_mirror_7 [0, 0, 0, 0, 2, 2, 2] [0, 2, 1, 1, 0, 1, 0] [0, 0, 0, 1, 1, 1, 2] [2, 1, 0, 0, 0, 2, 2] [1, 2, 0, 0, 0, 1, 1] demoR1_0000222 demoR2_0000222 demoC_0000222 demoM_0000222 demoMir_0000222

theorem demoR1_1000222 : invRung 7 5 20 [1, 0, 0, 0, 2, 2, 2] [1, 0, 0, 0, 2, 2, 2] 1 2 false = ([0, 2, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_1000222 : invRung 7 5 20 [1, 0, 0, 0, 2, 2, 2] [0, 2, 2, 1, 0, 1, 2] 3 1 true = ([1, 1, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_1000222 : fieldCube 7 5 20 [1, 1, 2, 2, 2, 2, 1] = [2, 2, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_1000222 : fieldMul 7 5 20 [2, 2, 0, 1, 0, 1, 0] [1, 0, 0, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000222 : mirrorTrits [2, 2, 0, 1, 0, 1, 0] = [1, 1, 0, 2, 0, 2, 0] := by
  decide

theorem demoInv_1000222 : specInv 7 5 20 [1, 0, 0, 0, 2, 2, 2] = some [1, 1, 0, 2, 0, 2, 0] :=
  specInv_mirror_7 [1, 0, 0, 0, 2, 2, 2] [0, 2, 2, 1, 0, 1, 2] [1, 1, 2, 2, 2, 2, 1] [2, 2, 0, 1, 0, 1, 0] [1, 1, 0, 2, 0, 2, 0] demoR1_1000222 demoR2_1000222 demoC_1000222 demoM_1000222 demoMir_1000222

theorem demoR1_2000222 : invRung 7 5 20 [2, 0, 0, 0, 2, 2, 2] [2, 0, 0, 0, 2, 2, 2] 1 2 false = ([1, 2, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_2000222 : invRung 7 5 20 [2, 0, 0, 0, 2, 2, 2] [1, 2, 1, 0, 1, 1, 0] 3 1 true = ([2, 2, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2000222 : fieldCube 7 5 20 [2, 2, 2, 1, 2, 1, 0] = [1, 0, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_2000222 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 1, 0] [2, 0, 0, 0, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2000222 : specInv 7 5 20 [2, 0, 0, 0, 2, 2, 2] = some [1, 0, 2, 1, 1, 1, 0] :=
  specInv_white_7 [2, 0, 0, 0, 2, 2, 2] [1, 2, 1, 0, 1, 1, 0] [2, 2, 2, 1, 2, 1, 0] [1, 0, 2, 1, 1, 1, 0] demoR1_2000222 demoR2_2000222 demoC_2000222 demoM_2000222

theorem demoR1_0100222 : invRung 7 5 20 [0, 1, 0, 0, 2, 2, 2] [0, 1, 0, 0, 2, 2, 2] 1 2 false = ([1, 1, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_0100222 : invRung 7 5 20 [0, 1, 0, 0, 2, 2, 2] [1, 1, 0, 1, 1, 0, 2] 3 1 true = ([1, 1, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_0100222 : fieldCube 7 5 20 [1, 1, 0, 1, 1, 2, 1] = [1, 1, 2, 0, 0, 2, 0] := by
  decide

theorem demoM_0100222 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 2, 0] [0, 1, 0, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100222 : mirrorTrits [1, 1, 2, 0, 0, 2, 0] = [2, 2, 1, 0, 0, 1, 0] := by
  decide

theorem demoInv_0100222 : specInv 7 5 20 [0, 1, 0, 0, 2, 2, 2] = some [2, 2, 1, 0, 0, 1, 0] :=
  specInv_mirror_7 [0, 1, 0, 0, 2, 2, 2] [1, 1, 0, 1, 1, 0, 2] [1, 1, 0, 1, 1, 2, 1] [1, 1, 2, 0, 0, 2, 0] [2, 2, 1, 0, 0, 1, 0] demoR1_0100222 demoR2_0100222 demoC_0100222 demoM_0100222 demoMir_0100222

theorem demoR1_1100222 : invRung 7 5 20 [1, 1, 0, 0, 2, 2, 2] [1, 1, 0, 0, 2, 2, 2] 1 2 false = ([0, 1, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_1100222 : invRung 7 5 20 [1, 1, 0, 0, 2, 2, 2] [0, 1, 1, 0, 1, 2, 0] 3 1 true = ([1, 0, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_1100222 : fieldCube 7 5 20 [1, 0, 0, 2, 1, 1, 2] = [1, 1, 1, 0, 0, 0, 2] := by
  decide

theorem demoM_1100222 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 0, 2] [1, 1, 0, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1100222 : mirrorTrits [1, 1, 1, 0, 0, 0, 2] = [2, 2, 2, 0, 0, 0, 1] := by
  decide

theorem demoInv_1100222 : specInv 7 5 20 [1, 1, 0, 0, 2, 2, 2] = some [2, 2, 2, 0, 0, 0, 1] :=
  specInv_mirror_7 [1, 1, 0, 0, 2, 2, 2] [0, 1, 1, 0, 1, 2, 0] [1, 0, 0, 2, 1, 1, 2] [1, 1, 1, 0, 0, 0, 2] [2, 2, 2, 0, 0, 0, 1] demoR1_1100222 demoR2_1100222 demoC_1100222 demoM_1100222 demoMir_1100222

theorem demoR1_2100222 : invRung 7 5 20 [2, 1, 0, 0, 2, 2, 2] [2, 1, 0, 0, 2, 2, 2] 1 2 false = ([2, 0, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2100222 : invRung 7 5 20 [2, 1, 0, 0, 2, 2, 2] [2, 0, 2, 0, 2, 0, 0] 3 1 true = ([0, 1, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_2100222 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 1, 1] = [1, 2, 0, 2, 2, 2, 0] := by
  decide

theorem demoM_2100222 : fieldMul 7 5 20 [1, 2, 0, 2, 2, 2, 0] [2, 1, 0, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100222 : mirrorTrits [1, 2, 0, 2, 2, 2, 0] = [2, 1, 0, 1, 1, 1, 0] := by
  decide

theorem demoInv_2100222 : specInv 7 5 20 [2, 1, 0, 0, 2, 2, 2] = some [2, 1, 0, 1, 1, 1, 0] :=
  specInv_mirror_7 [2, 1, 0, 0, 2, 2, 2] [2, 0, 2, 0, 2, 0, 0] [0, 1, 0, 0, 0, 1, 1] [1, 2, 0, 2, 2, 2, 0] [2, 1, 0, 1, 1, 1, 0] demoR1_2100222 demoR2_2100222 demoC_2100222 demoM_2100222 demoMir_2100222

theorem demoR1_0200222 : invRung 7 5 20 [0, 2, 0, 0, 2, 2, 2] [0, 2, 0, 0, 2, 2, 2] 1 2 false = ([1, 0, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_0200222 : invRung 7 5 20 [0, 2, 0, 0, 2, 2, 2] [1, 0, 2, 2, 0, 0, 2] 3 1 true = ([0, 2, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0200222 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 2, 1] = [2, 1, 1, 1, 0, 1, 2] := by
  decide

theorem demoM_0200222 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 1, 2] [0, 2, 0, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200222 : mirrorTrits [2, 1, 1, 1, 0, 1, 2] = [1, 2, 2, 2, 0, 2, 1] := by
  decide

theorem demoInv_0200222 : specInv 7 5 20 [0, 2, 0, 0, 2, 2, 2] = some [1, 2, 2, 2, 0, 2, 1] :=
  specInv_mirror_7 [0, 2, 0, 0, 2, 2, 2] [1, 0, 2, 2, 0, 0, 2] [0, 2, 2, 0, 1, 2, 1] [2, 1, 1, 1, 0, 1, 2] [1, 2, 2, 2, 0, 2, 1] demoR1_0200222 demoR2_0200222 demoC_0200222 demoM_0200222 demoMir_0200222

theorem demoR1_1200222 : invRung 7 5 20 [1, 2, 0, 0, 2, 2, 2] [1, 2, 0, 0, 2, 2, 2] 1 2 false = ([2, 1, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_1200222 : invRung 7 5 20 [1, 2, 0, 0, 2, 2, 2] [2, 1, 0, 1, 2, 0, 0] 3 1 true = ([1, 1, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_1200222 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 0, 1] = [2, 1, 0, 2, 1, 2, 1] := by
  decide

theorem demoM_1200222 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 2, 1] [1, 2, 0, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200222 : mirrorTrits [2, 1, 0, 2, 1, 2, 1] = [1, 2, 0, 1, 2, 1, 2] := by
  decide

theorem demoInv_1200222 : specInv 7 5 20 [1, 2, 0, 0, 2, 2, 2] = some [1, 2, 0, 1, 2, 1, 2] :=
  specInv_mirror_7 [1, 2, 0, 0, 2, 2, 2] [2, 1, 0, 1, 2, 0, 0] [1, 1, 0, 1, 0, 0, 1] [2, 1, 0, 2, 1, 2, 1] [1, 2, 0, 1, 2, 1, 2] demoR1_1200222 demoR2_1200222 demoC_1200222 demoM_1200222 demoMir_1200222

theorem demoR1_2200222 : invRung 7 5 20 [2, 2, 0, 0, 2, 2, 2] [2, 2, 0, 0, 2, 2, 2] 1 2 false = ([2, 0, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_2200222 : invRung 7 5 20 [2, 2, 0, 0, 2, 2, 2] [2, 0, 0, 0, 2, 1, 0] 3 1 true = ([2, 0, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2200222 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 0, 0] = [2, 1, 0, 1, 0, 1, 2] := by
  decide

theorem demoM_2200222 : fieldMul 7 5 20 [2, 1, 0, 1, 0, 1, 2] [2, 2, 0, 0, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2200222 : specInv 7 5 20 [2, 2, 0, 0, 2, 2, 2] = some [2, 1, 0, 1, 0, 1, 2] :=
  specInv_white_7 [2, 2, 0, 0, 2, 2, 2] [2, 0, 0, 0, 2, 1, 0] [2, 0, 1, 0, 1, 0, 0] [2, 1, 0, 1, 0, 1, 2] demoR1_2200222 demoR2_2200222 demoC_2200222 demoM_2200222

theorem demoR1_0010222 : invRung 7 5 20 [0, 0, 1, 0, 2, 2, 2] [0, 0, 1, 0, 2, 2, 2] 1 2 false = ([2, 0, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0010222 : invRung 7 5 20 [0, 0, 1, 0, 2, 2, 2] [2, 0, 0, 1, 2, 1, 2] 3 1 true = ([2, 0, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0010222 : fieldCube 7 5 20 [2, 0, 1, 1, 1, 2, 0] = [2, 0, 0, 1, 2, 1, 0] := by
  decide

theorem demoM_0010222 : fieldMul 7 5 20 [2, 0, 0, 1, 2, 1, 0] [0, 0, 1, 0, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0010222 : specInv 7 5 20 [0, 0, 1, 0, 2, 2, 2] = some [2, 0, 0, 1, 2, 1, 0] :=
  specInv_white_7 [0, 0, 1, 0, 2, 2, 2] [2, 0, 0, 1, 2, 1, 2] [2, 0, 1, 1, 1, 2, 0] [2, 0, 0, 1, 2, 1, 0] demoR1_0010222 demoR2_0010222 demoC_0010222 demoM_0010222

theorem demoR1_1010222 : invRung 7 5 20 [1, 0, 1, 0, 2, 2, 2] [1, 0, 1, 0, 2, 2, 2] 1 2 false = ([2, 1, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_1010222 : invRung 7 5 20 [1, 0, 1, 0, 2, 2, 2] [2, 1, 1, 2, 2, 0, 1] 3 1 true = ([0, 1, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_1010222 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 0, 0] = [2, 2, 2, 0, 0, 1, 2] := by
  decide

theorem demoM_1010222 : fieldMul 7 5 20 [2, 2, 2, 0, 0, 1, 2] [1, 0, 1, 0, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1010222 : specInv 7 5 20 [1, 0, 1, 0, 2, 2, 2] = some [2, 2, 2, 0, 0, 1, 2] :=
  specInv_white_7 [1, 0, 1, 0, 2, 2, 2] [2, 1, 1, 2, 2, 0, 1] [0, 1, 0, 2, 2, 0, 0] [2, 2, 2, 0, 0, 1, 2] demoR1_1010222 demoR2_1010222 demoC_1010222 demoM_1010222

theorem demoR1_2010222 : invRung 7 5 20 [2, 0, 1, 0, 2, 2, 2] [2, 0, 1, 0, 2, 2, 2] 1 2 false = ([0, 1, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_2010222 : invRung 7 5 20 [2, 0, 1, 0, 2, 2, 2] [0, 1, 0, 1, 2, 1, 0] 3 1 true = ([2, 1, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_2010222 : fieldCube 7 5 20 [2, 1, 2, 0, 1, 1, 2] = [0, 1, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_2010222 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 1, 1] [2, 0, 1, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010222 : mirrorTrits [0, 1, 2, 1, 0, 1, 1] = [0, 2, 1, 2, 0, 2, 2] := by
  decide

theorem demoInv_2010222 : specInv 7 5 20 [2, 0, 1, 0, 2, 2, 2] = some [0, 2, 1, 2, 0, 2, 2] :=
  specInv_mirror_7 [2, 0, 1, 0, 2, 2, 2] [0, 1, 0, 1, 2, 1, 0] [2, 1, 2, 0, 1, 1, 2] [0, 1, 2, 1, 0, 1, 1] [0, 2, 1, 2, 0, 2, 2] demoR1_2010222 demoR2_2010222 demoC_2010222 demoM_2010222 demoMir_2010222

theorem demoR1_0110222 : invRung 7 5 20 [0, 1, 1, 0, 2, 2, 2] [0, 1, 1, 0, 2, 2, 2] 1 2 false = ([0, 0, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_0110222 : invRung 7 5 20 [0, 1, 1, 0, 2, 2, 2] [0, 0, 1, 2, 0, 2, 1] 3 1 true = ([1, 1, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0110222 : fieldCube 7 5 20 [1, 1, 2, 0, 2, 0, 1] = [1, 0, 2, 1, 1, 0, 2] := by
  decide

theorem demoM_0110222 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 0, 2] [0, 1, 1, 0, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0110222 : specInv 7 5 20 [0, 1, 1, 0, 2, 2, 2] = some [1, 0, 2, 1, 1, 0, 2] :=
  specInv_white_7 [0, 1, 1, 0, 2, 2, 2] [0, 0, 1, 2, 0, 2, 1] [1, 1, 2, 0, 2, 0, 1] [1, 0, 2, 1, 1, 0, 2] demoR1_0110222 demoR2_0110222 demoC_0110222 demoM_0110222

theorem demoR1_1110222 : invRung 7 5 20 [1, 1, 1, 0, 2, 2, 2] [1, 1, 1, 0, 2, 2, 2] 1 2 false = ([2, 0, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_1110222 : invRung 7 5 20 [1, 1, 1, 0, 2, 2, 2] [2, 0, 0, 1, 1, 1, 1] 3 1 true = ([1, 1, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_1110222 : fieldCube 7 5 20 [1, 1, 0, 2, 0, 1, 2] = [1, 0, 1, 0, 0, 2, 1] := by
  decide

theorem demoM_1110222 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 2, 1] [1, 1, 1, 0, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1110222 : specInv 7 5 20 [1, 1, 1, 0, 2, 2, 2] = some [1, 0, 1, 0, 0, 2, 1] :=
  specInv_white_7 [1, 1, 1, 0, 2, 2, 2] [2, 0, 0, 1, 1, 1, 1] [1, 1, 0, 2, 0, 1, 2] [1, 0, 1, 0, 0, 2, 1] demoR1_1110222 demoR2_1110222 demoC_1110222 demoM_1110222

theorem demoR1_2110222 : invRung 7 5 20 [2, 1, 1, 0, 2, 2, 2] [2, 1, 1, 0, 2, 2, 2] 1 2 false = ([1, 1, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_2110222 : invRung 7 5 20 [2, 1, 1, 0, 2, 2, 2] [1, 1, 2, 0, 2, 1, 1] 3 1 true = ([2, 2, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_2110222 : fieldCube 7 5 20 [2, 2, 0, 2, 2, 2, 1] = [0, 2, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_2110222 : fieldMul 7 5 20 [0, 2, 0, 2, 0, 1, 1] [2, 1, 1, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110222 : mirrorTrits [0, 2, 0, 2, 0, 1, 1] = [0, 1, 0, 1, 0, 2, 2] := by
  decide

theorem demoInv_2110222 : specInv 7 5 20 [2, 1, 1, 0, 2, 2, 2] = some [0, 1, 0, 1, 0, 2, 2] :=
  specInv_mirror_7 [2, 1, 1, 0, 2, 2, 2] [1, 1, 2, 0, 2, 1, 1] [2, 2, 0, 2, 2, 2, 1] [0, 2, 0, 2, 0, 1, 1] [0, 1, 0, 1, 0, 2, 2] demoR1_2110222 demoR2_2110222 demoC_2110222 demoM_2110222 demoMir_2110222

theorem demoR1_0210222 : invRung 7 5 20 [0, 2, 1, 0, 2, 2, 2] [0, 2, 1, 0, 2, 2, 2] 1 2 false = ([1, 2, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_0210222 : invRung 7 5 20 [0, 2, 1, 0, 2, 2, 2] [1, 2, 0, 1, 2, 2, 1] 3 1 true = ([2, 2, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_0210222 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 1, 0] = [1, 2, 2, 0, 1, 0, 1] := by
  decide

theorem demoM_0210222 : fieldMul 7 5 20 [1, 2, 2, 0, 1, 0, 1] [0, 2, 1, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210222 : mirrorTrits [1, 2, 2, 0, 1, 0, 1] = [2, 1, 1, 0, 2, 0, 2] := by
  decide

theorem demoInv_0210222 : specInv 7 5 20 [0, 2, 1, 0, 2, 2, 2] = some [2, 1, 1, 0, 2, 0, 2] :=
  specInv_mirror_7 [0, 2, 1, 0, 2, 2, 2] [1, 2, 0, 1, 2, 2, 1] [2, 2, 1, 1, 1, 1, 0] [1, 2, 2, 0, 1, 0, 1] [2, 1, 1, 0, 2, 0, 2] demoR1_0210222 demoR2_0210222 demoC_0210222 demoM_0210222 demoMir_0210222

theorem demoR1_1210222 : invRung 7 5 20 [1, 2, 1, 0, 2, 2, 2] [1, 2, 1, 0, 2, 2, 2] 1 2 false = ([2, 2, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_1210222 : invRung 7 5 20 [1, 2, 1, 0, 2, 2, 2] [2, 2, 0, 2, 0, 0, 0] 3 1 true = ([1, 0, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_1210222 : fieldCube 7 5 20 [1, 0, 0, 1, 1, 2, 0] = [1, 0, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_1210222 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 1, 2] [1, 2, 1, 0, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1210222 : specInv 7 5 20 [1, 2, 1, 0, 2, 2, 2] = some [1, 0, 0, 1, 2, 1, 2] :=
  specInv_white_7 [1, 2, 1, 0, 2, 2, 2] [2, 2, 0, 2, 0, 0, 0] [1, 0, 0, 1, 1, 2, 0] [1, 0, 0, 1, 2, 1, 2] demoR1_1210222 demoR2_1210222 demoC_1210222 demoM_1210222

theorem demoR1_2210222 : invRung 7 5 20 [2, 2, 1, 0, 2, 2, 2] [2, 2, 1, 0, 2, 2, 2] 1 2 false = ([2, 2, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2210222 : invRung 7 5 20 [2, 2, 1, 0, 2, 2, 2] [2, 2, 2, 2, 1, 1, 2] 3 1 true = ([0, 0, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_2210222 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 0, 0] = [2, 2, 2, 2, 0, 1, 0] := by
  decide

theorem demoM_2210222 : fieldMul 7 5 20 [2, 2, 2, 2, 0, 1, 0] [2, 2, 1, 0, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2210222 : specInv 7 5 20 [2, 2, 1, 0, 2, 2, 2] = some [2, 2, 2, 2, 0, 1, 0] :=
  specInv_white_7 [2, 2, 1, 0, 2, 2, 2] [2, 2, 2, 2, 1, 1, 2] [0, 0, 1, 2, 2, 0, 0] [2, 2, 2, 2, 0, 1, 0] demoR1_2210222 demoR2_2210222 demoC_2210222 demoM_2210222

theorem demoR1_0020222 : invRung 7 5 20 [0, 0, 2, 0, 2, 2, 2] [0, 0, 2, 0, 2, 2, 2] 1 2 false = ([0, 2, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_0020222 : invRung 7 5 20 [0, 0, 2, 0, 2, 2, 2] [0, 2, 0, 0, 1, 2, 2] 3 1 true = ([2, 2, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0020222 : fieldCube 7 5 20 [2, 2, 2, 1, 2, 1, 2] = [1, 2, 0, 0, 0, 0, 2] := by
  decide

theorem demoM_0020222 : fieldMul 7 5 20 [1, 2, 0, 0, 0, 0, 2] [0, 0, 2, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020222 : mirrorTrits [1, 2, 0, 0, 0, 0, 2] = [2, 1, 0, 0, 0, 0, 1] := by
  decide

theorem demoInv_0020222 : specInv 7 5 20 [0, 0, 2, 0, 2, 2, 2] = some [2, 1, 0, 0, 0, 0, 1] :=
  specInv_mirror_7 [0, 0, 2, 0, 2, 2, 2] [0, 2, 0, 0, 1, 2, 2] [2, 2, 2, 1, 2, 1, 2] [1, 2, 0, 0, 0, 0, 2] [2, 1, 0, 0, 0, 0, 1] demoR1_0020222 demoR2_0020222 demoC_0020222 demoM_0020222 demoMir_0020222

theorem demoR1_1020222 : invRung 7 5 20 [1, 0, 2, 0, 2, 2, 2] [1, 0, 2, 0, 2, 2, 2] 1 2 false = ([2, 1, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_1020222 : invRung 7 5 20 [1, 0, 2, 0, 2, 2, 2] [2, 1, 2, 2, 1, 0, 0] 3 1 true = ([1, 1, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_1020222 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 1, 0] = [2, 0, 1, 0, 1, 0, 1] := by
  decide

theorem demoM_1020222 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 0, 1] [1, 0, 2, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020222 : mirrorTrits [2, 0, 1, 0, 1, 0, 1] = [1, 0, 2, 0, 2, 0, 2] := by
  decide

theorem demoInv_1020222 : specInv 7 5 20 [1, 0, 2, 0, 2, 2, 2] = some [1, 0, 2, 0, 2, 0, 2] :=
  specInv_mirror_7 [1, 0, 2, 0, 2, 2, 2] [2, 1, 2, 2, 1, 0, 0] [1, 1, 0, 0, 2, 1, 0] [2, 0, 1, 0, 1, 0, 1] [1, 0, 2, 0, 2, 0, 2] demoR1_1020222 demoR2_1020222 demoC_1020222 demoM_1020222 demoMir_1020222

theorem demoR1_2020222 : invRung 7 5 20 [2, 0, 2, 0, 2, 2, 2] [2, 0, 2, 0, 2, 2, 2] 1 2 false = ([2, 1, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_2020222 : invRung 7 5 20 [2, 0, 2, 0, 2, 2, 2] [2, 1, 2, 1, 0, 2, 2] 3 1 true = ([1, 2, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_2020222 : fieldCube 7 5 20 [1, 2, 0, 2, 1, 0, 0] = [0, 1, 2, 0, 0, 0, 1] := by
  decide

theorem demoM_2020222 : fieldMul 7 5 20 [0, 1, 2, 0, 0, 0, 1] [2, 0, 2, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020222 : mirrorTrits [0, 1, 2, 0, 0, 0, 1] = [0, 2, 1, 0, 0, 0, 2] := by
  decide

theorem demoInv_2020222 : specInv 7 5 20 [2, 0, 2, 0, 2, 2, 2] = some [0, 2, 1, 0, 0, 0, 2] :=
  specInv_mirror_7 [2, 0, 2, 0, 2, 2, 2] [2, 1, 2, 1, 0, 2, 2] [1, 2, 0, 2, 1, 0, 0] [0, 1, 2, 0, 0, 0, 1] [0, 2, 1, 0, 0, 0, 2] demoR1_2020222 demoR2_2020222 demoC_2020222 demoM_2020222 demoMir_2020222

theorem demoR1_0120222 : invRung 7 5 20 [0, 1, 2, 0, 2, 2, 2] [0, 1, 2, 0, 2, 2, 2] 1 2 false = ([1, 2, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_0120222 : invRung 7 5 20 [0, 1, 2, 0, 2, 2, 2] [1, 2, 2, 1, 1, 1, 0] 3 1 true = ([0, 2, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0120222 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 1, 2] = [2, 0, 0, 1, 0, 1, 1] := by
  decide

theorem demoM_0120222 : fieldMul 7 5 20 [2, 0, 0, 1, 0, 1, 1] [0, 1, 2, 0, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0120222 : specInv 7 5 20 [0, 1, 2, 0, 2, 2, 2] = some [2, 0, 0, 1, 0, 1, 1] :=
  specInv_white_7 [0, 1, 2, 0, 2, 2, 2] [1, 2, 2, 1, 1, 1, 0] [0, 2, 0, 1, 0, 1, 2] [2, 0, 0, 1, 0, 1, 1] demoR1_0120222 demoR2_0120222 demoC_0120222 demoM_0120222

theorem demoR1_1120222 : invRung 7 5 20 [1, 1, 2, 0, 2, 2, 2] [1, 1, 2, 0, 2, 2, 2] 1 2 false = ([2, 2, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_1120222 : invRung 7 5 20 [1, 1, 2, 0, 2, 2, 2] [2, 2, 0, 0, 0, 0, 1] 3 1 true = ([1, 0, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_1120222 : fieldCube 7 5 20 [1, 0, 2, 0, 0, 1, 1] = [2, 2, 0, 1, 2, 2, 2] := by
  decide

theorem demoM_1120222 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 2, 2] [1, 1, 2, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120222 : mirrorTrits [2, 2, 0, 1, 2, 2, 2] = [1, 1, 0, 2, 1, 1, 1] := by
  decide

theorem demoInv_1120222 : specInv 7 5 20 [1, 1, 2, 0, 2, 2, 2] = some [1, 1, 0, 2, 1, 1, 1] :=
  specInv_mirror_7 [1, 1, 2, 0, 2, 2, 2] [2, 2, 0, 0, 0, 0, 1] [1, 0, 2, 0, 0, 1, 1] [2, 2, 0, 1, 2, 2, 2] [1, 1, 0, 2, 1, 1, 1] demoR1_1120222 demoR2_1120222 demoC_1120222 demoM_1120222 demoMir_1120222

theorem demoR1_2120222 : invRung 7 5 20 [2, 1, 2, 0, 2, 2, 2] [2, 1, 2, 0, 2, 2, 2] 1 2 false = ([0, 2, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2120222 : invRung 7 5 20 [2, 1, 2, 0, 2, 2, 2] [0, 2, 1, 1, 1, 2, 0] 3 1 true = ([0, 2, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2120222 : fieldCube 7 5 20 [0, 2, 1, 0, 1, 1, 0] = [1, 2, 1, 0, 1, 2, 1] := by
  decide

theorem demoM_2120222 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 2, 1] [2, 1, 2, 0, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2120222 : specInv 7 5 20 [2, 1, 2, 0, 2, 2, 2] = some [1, 2, 1, 0, 1, 2, 1] :=
  specInv_white_7 [2, 1, 2, 0, 2, 2, 2] [0, 2, 1, 1, 1, 2, 0] [0, 2, 1, 0, 1, 1, 0] [1, 2, 1, 0, 1, 2, 1] demoR1_2120222 demoR2_2120222 demoC_2120222 demoM_2120222

theorem demoR1_0220222 : invRung 7 5 20 [0, 2, 2, 0, 2, 2, 2] [0, 2, 2, 0, 2, 2, 2] 1 2 false = ([0, 0, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_0220222 : invRung 7 5 20 [0, 2, 2, 0, 2, 2, 2] [0, 0, 0, 0, 2, 0, 2] 3 1 true = ([1, 0, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_0220222 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 2, 1] = [2, 2, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_0220222 : fieldMul 7 5 20 [2, 2, 0, 0, 0, 1, 0] [0, 2, 2, 0, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0220222 : specInv 7 5 20 [0, 2, 2, 0, 2, 2, 2] = some [2, 2, 0, 0, 0, 1, 0] :=
  specInv_white_7 [0, 2, 2, 0, 2, 2, 2] [0, 0, 0, 0, 2, 0, 2] [1, 0, 2, 2, 2, 2, 1] [2, 2, 0, 0, 0, 1, 0] demoR1_0220222 demoR2_0220222 demoC_0220222 demoM_0220222

theorem demoR1_1220222 : invRung 7 5 20 [1, 2, 2, 0, 2, 2, 2] [1, 2, 2, 0, 2, 2, 2] 1 2 false = ([0, 2, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1220222 : invRung 7 5 20 [1, 2, 2, 0, 2, 2, 2] [0, 2, 0, 0, 2, 2, 1] 3 1 true = ([2, 1, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_1220222 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 0, 2] = [0, 1, 2, 2, 2, 2, 2] := by
  decide

theorem demoM_1220222 : fieldMul 7 5 20 [0, 1, 2, 2, 2, 2, 2] [1, 2, 2, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220222 : mirrorTrits [0, 1, 2, 2, 2, 2, 2] = [0, 2, 1, 1, 1, 1, 1] := by
  decide

theorem demoInv_1220222 : specInv 7 5 20 [1, 2, 2, 0, 2, 2, 2] = some [0, 2, 1, 1, 1, 1, 1] :=
  specInv_mirror_7 [1, 2, 2, 0, 2, 2, 2] [0, 2, 0, 0, 2, 2, 1] [2, 1, 1, 1, 2, 0, 2] [0, 1, 2, 2, 2, 2, 2] [0, 2, 1, 1, 1, 1, 1] demoR1_1220222 demoR2_1220222 demoC_1220222 demoM_1220222 demoMir_1220222

theorem demoR1_2220222 : invRung 7 5 20 [2, 2, 2, 0, 2, 2, 2] [2, 2, 2, 0, 2, 2, 2] 1 2 false = ([2, 0, 2, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_2220222 : invRung 7 5 20 [2, 2, 2, 0, 2, 2, 2] [2, 0, 2, 1, 1, 0, 1] 3 1 true = ([0, 1, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_2220222 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 1, 2] = [2, 1, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_2220222 : fieldMul 7 5 20 [2, 1, 0, 1, 0, 2, 1] [2, 2, 2, 0, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220222 : mirrorTrits [2, 1, 0, 1, 0, 2, 1] = [1, 2, 0, 2, 0, 1, 2] := by
  decide

theorem demoInv_2220222 : specInv 7 5 20 [2, 2, 2, 0, 2, 2, 2] = some [1, 2, 0, 2, 0, 1, 2] :=
  specInv_mirror_7 [2, 2, 2, 0, 2, 2, 2] [2, 0, 2, 1, 1, 0, 1] [0, 1, 2, 1, 1, 1, 2] [2, 1, 0, 1, 0, 2, 1] [1, 2, 0, 2, 0, 1, 2] demoR1_2220222 demoR2_2220222 demoC_2220222 demoM_2220222 demoMir_2220222

theorem demoR1_0001222 : invRung 7 5 20 [0, 0, 0, 1, 2, 2, 2] [0, 0, 0, 1, 2, 2, 2] 1 2 false = ([0, 0, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_0001222 : invRung 7 5 20 [0, 0, 0, 1, 2, 2, 2] [0, 0, 1, 2, 2, 0, 1] 3 1 true = ([0, 2, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0001222 : fieldCube 7 5 20 [0, 2, 2, 0, 0, 2, 1] = [2, 0, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_0001222 : fieldMul 7 5 20 [2, 0, 1, 0, 0, 0, 1] [0, 0, 0, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001222 : mirrorTrits [2, 0, 1, 0, 0, 0, 1] = [1, 0, 2, 0, 0, 0, 2] := by
  decide

theorem demoInv_0001222 : specInv 7 5 20 [0, 0, 0, 1, 2, 2, 2] = some [1, 0, 2, 0, 0, 0, 2] :=
  specInv_mirror_7 [0, 0, 0, 1, 2, 2, 2] [0, 0, 1, 2, 2, 0, 1] [0, 2, 2, 0, 0, 2, 1] [2, 0, 1, 0, 0, 0, 1] [1, 0, 2, 0, 0, 0, 2] demoR1_0001222 demoR2_0001222 demoC_0001222 demoM_0001222 demoMir_0001222

theorem demoR1_1001222 : invRung 7 5 20 [1, 0, 0, 1, 2, 2, 2] [1, 0, 0, 1, 2, 2, 2] 1 2 false = ([0, 0, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_1001222 : invRung 7 5 20 [1, 0, 0, 1, 2, 2, 2] [0, 0, 2, 0, 0, 1, 0] 3 1 true = ([0, 1, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1001222 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 1, 0] = [1, 1, 1, 1, 1, 1, 0] := by
  decide

theorem demoM_1001222 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 1, 0] [1, 0, 0, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1001222 : specInv 7 5 20 [1, 0, 0, 1, 2, 2, 2] = some [1, 1, 1, 1, 1, 1, 0] :=
  specInv_white_7 [1, 0, 0, 1, 2, 2, 2] [0, 0, 2, 0, 0, 1, 0] [0, 1, 1, 0, 0, 1, 0] [1, 1, 1, 1, 1, 1, 0] demoR1_1001222 demoR2_1001222 demoC_1001222 demoM_1001222

theorem demoR1_2001222 : invRung 7 5 20 [2, 0, 0, 1, 2, 2, 2] [2, 0, 0, 1, 2, 2, 2] 1 2 false = ([1, 2, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_2001222 : invRung 7 5 20 [2, 0, 0, 1, 2, 2, 2] [1, 2, 2, 2, 1, 0, 1] 3 1 true = ([0, 2, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_2001222 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 1, 2] = [1, 1, 2, 2, 0, 1, 2] := by
  decide

theorem demoM_2001222 : fieldMul 7 5 20 [1, 1, 2, 2, 0, 1, 2] [2, 0, 0, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001222 : mirrorTrits [1, 1, 2, 2, 0, 1, 2] = [2, 2, 1, 1, 0, 2, 1] := by
  decide

theorem demoInv_2001222 : specInv 7 5 20 [2, 0, 0, 1, 2, 2, 2] = some [2, 2, 1, 1, 0, 2, 1] :=
  specInv_mirror_7 [2, 0, 0, 1, 2, 2, 2] [1, 2, 2, 2, 1, 0, 1] [0, 2, 0, 0, 1, 1, 2] [1, 1, 2, 2, 0, 1, 2] [2, 2, 1, 1, 0, 2, 1] demoR1_2001222 demoR2_2001222 demoC_2001222 demoM_2001222 demoMir_2001222

theorem demoR1_0101222 : invRung 7 5 20 [0, 1, 0, 1, 2, 2, 2] [0, 1, 0, 1, 2, 2, 2] 1 2 false = ([0, 0, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_0101222 : invRung 7 5 20 [0, 1, 0, 1, 2, 2, 2] [0, 0, 1, 1, 2, 0, 2] 3 1 true = ([1, 0, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0101222 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 0, 1] = [2, 0, 0, 0, 1, 1, 0] := by
  decide

theorem demoM_0101222 : fieldMul 7 5 20 [2, 0, 0, 0, 1, 1, 0] [0, 1, 0, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0101222 : specInv 7 5 20 [0, 1, 0, 1, 2, 2, 2] = some [2, 0, 0, 0, 1, 1, 0] :=
  specInv_white_7 [0, 1, 0, 1, 2, 2, 2] [0, 0, 1, 1, 2, 0, 2] [1, 0, 0, 1, 2, 0, 1] [2, 0, 0, 0, 1, 1, 0] demoR1_0101222 demoR2_0101222 demoC_0101222 demoM_0101222

theorem demoR1_1101222 : invRung 7 5 20 [1, 1, 0, 1, 2, 2, 2] [1, 1, 0, 1, 2, 2, 2] 1 2 false = ([0, 0, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_1101222 : invRung 7 5 20 [1, 1, 0, 1, 2, 2, 2] [0, 0, 2, 1, 2, 2, 0] 3 1 true = ([2, 2, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_1101222 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 0, 0] = [1, 1, 2, 0, 0, 0, 0] := by
  decide

theorem demoM_1101222 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 0, 0] [1, 1, 0, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1101222 : specInv 7 5 20 [1, 1, 0, 1, 2, 2, 2] = some [1, 1, 2, 0, 0, 0, 0] :=
  specInv_white_7 [1, 1, 0, 1, 2, 2, 2] [0, 0, 2, 1, 2, 2, 0] [2, 2, 2, 2, 1, 0, 0] [1, 1, 2, 0, 0, 0, 0] demoR1_1101222 demoR2_1101222 demoC_1101222 demoM_1101222

theorem demoR1_2101222 : invRung 7 5 20 [2, 1, 0, 1, 2, 2, 2] [2, 1, 0, 1, 2, 2, 2] 1 2 false = ([0, 1, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_2101222 : invRung 7 5 20 [2, 1, 0, 1, 2, 2, 2] [0, 1, 1, 1, 2, 1, 0] 3 1 true = ([2, 2, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_2101222 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 2, 0] = [1, 1, 2, 1, 2, 1, 1] := by
  decide

theorem demoM_2101222 : fieldMul 7 5 20 [1, 1, 2, 1, 2, 1, 1] [2, 1, 0, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101222 : mirrorTrits [1, 1, 2, 1, 2, 1, 1] = [2, 2, 1, 2, 1, 2, 2] := by
  decide

theorem demoInv_2101222 : specInv 7 5 20 [2, 1, 0, 1, 2, 2, 2] = some [2, 2, 1, 2, 1, 2, 2] :=
  specInv_mirror_7 [2, 1, 0, 1, 2, 2, 2] [0, 1, 1, 1, 2, 1, 0] [2, 2, 1, 0, 2, 2, 0] [1, 1, 2, 1, 2, 1, 1] [2, 2, 1, 2, 1, 2, 2] demoR1_2101222 demoR2_2101222 demoC_2101222 demoM_2101222 demoMir_2101222

theorem demoR1_0201222 : invRung 7 5 20 [0, 2, 0, 1, 2, 2, 2] [0, 2, 0, 1, 2, 2, 2] 1 2 false = ([2, 1, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_0201222 : invRung 7 5 20 [0, 2, 0, 1, 2, 2, 2] [2, 1, 1, 2, 2, 2, 2] 3 1 true = ([2, 1, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_0201222 : fieldCube 7 5 20 [2, 1, 0, 2, 0, 2, 1] = [0, 0, 0, 2, 0, 2, 2] := by
  decide

theorem demoM_0201222 : fieldMul 7 5 20 [0, 0, 0, 2, 0, 2, 2] [0, 2, 0, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201222 : mirrorTrits [0, 0, 0, 2, 0, 2, 2] = [0, 0, 0, 1, 0, 1, 1] := by
  decide

theorem demoInv_0201222 : specInv 7 5 20 [0, 2, 0, 1, 2, 2, 2] = some [0, 0, 0, 1, 0, 1, 1] :=
  specInv_mirror_7 [0, 2, 0, 1, 2, 2, 2] [2, 1, 1, 2, 2, 2, 2] [2, 1, 0, 2, 0, 2, 1] [0, 0, 0, 2, 0, 2, 2] [0, 0, 0, 1, 0, 1, 1] demoR1_0201222 demoR2_0201222 demoC_0201222 demoM_0201222 demoMir_0201222

theorem demoR1_1201222 : invRung 7 5 20 [1, 2, 0, 1, 2, 2, 2] [1, 2, 0, 1, 2, 2, 2] 1 2 false = ([2, 2, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_1201222 : invRung 7 5 20 [1, 2, 0, 1, 2, 2, 2] [2, 2, 2, 2, 0, 1, 0] 3 1 true = ([2, 2, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1201222 : fieldCube 7 5 20 [2, 2, 1, 0, 1, 1, 0] = [0, 2, 1, 0, 1, 2, 1] := by
  decide

theorem demoM_1201222 : fieldMul 7 5 20 [0, 2, 1, 0, 1, 2, 1] [1, 2, 0, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1201222 : specInv 7 5 20 [1, 2, 0, 1, 2, 2, 2] = some [0, 2, 1, 0, 1, 2, 1] :=
  specInv_white_7 [1, 2, 0, 1, 2, 2, 2] [2, 2, 2, 2, 0, 1, 0] [2, 2, 1, 0, 1, 1, 0] [0, 2, 1, 0, 1, 2, 1] demoR1_1201222 demoR2_1201222 demoC_1201222 demoM_1201222

theorem demoR1_2201222 : invRung 7 5 20 [2, 2, 0, 1, 2, 2, 2] [2, 2, 0, 1, 2, 2, 2] 1 2 false = ([1, 0, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2201222 : invRung 7 5 20 [2, 2, 0, 1, 2, 2, 2] [1, 0, 0, 1, 1, 2, 0] 3 1 true = ([0, 1, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_2201222 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 0, 1] = [2, 2, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_2201222 : fieldMul 7 5 20 [2, 2, 1, 0, 1, 1, 1] [2, 2, 0, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2201222 : specInv 7 5 20 [2, 2, 0, 1, 2, 2, 2] = some [2, 2, 1, 0, 1, 1, 1] :=
  specInv_white_7 [2, 2, 0, 1, 2, 2, 2] [1, 0, 0, 1, 1, 2, 0] [0, 1, 2, 2, 1, 0, 1] [2, 2, 1, 0, 1, 1, 1] demoR1_2201222 demoR2_2201222 demoC_2201222 demoM_2201222

theorem demoR1_0011222 : invRung 7 5 20 [0, 0, 1, 1, 2, 2, 2] [0, 0, 1, 1, 2, 2, 2] 1 2 false = ([0, 2, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_0011222 : invRung 7 5 20 [0, 0, 1, 1, 2, 2, 2] [0, 2, 0, 0, 2, 1, 1] 3 1 true = ([2, 1, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0011222 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 1, 1] = [1, 2, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_0011222 : fieldMul 7 5 20 [1, 2, 1, 2, 2, 0, 2] [0, 0, 1, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011222 : mirrorTrits [1, 2, 1, 2, 2, 0, 2] = [2, 1, 2, 1, 1, 0, 1] := by
  decide

theorem demoInv_0011222 : specInv 7 5 20 [0, 0, 1, 1, 2, 2, 2] = some [2, 1, 2, 1, 1, 0, 1] :=
  specInv_mirror_7 [0, 0, 1, 1, 2, 2, 2] [0, 2, 0, 0, 2, 1, 1] [2, 1, 2, 1, 0, 1, 1] [1, 2, 1, 2, 2, 0, 2] [2, 1, 2, 1, 1, 0, 1] demoR1_0011222 demoR2_0011222 demoC_0011222 demoM_0011222 demoMir_0011222

theorem demoR1_1011222 : invRung 7 5 20 [1, 0, 1, 1, 2, 2, 2] [1, 0, 1, 1, 2, 2, 2] 1 2 false = ([0, 1, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1011222 : invRung 7 5 20 [1, 0, 1, 1, 2, 2, 2] [0, 1, 2, 1, 2, 2, 1] 3 1 true = ([2, 1, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_1011222 : fieldCube 7 5 20 [2, 1, 1, 0, 0, 2, 1] = [1, 0, 1, 2, 0, 0, 0] := by
  decide

theorem demoM_1011222 : fieldMul 7 5 20 [1, 0, 1, 2, 0, 0, 0] [1, 0, 1, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011222 : mirrorTrits [1, 0, 1, 2, 0, 0, 0] = [2, 0, 2, 1, 0, 0, 0] := by
  decide

theorem demoInv_1011222 : specInv 7 5 20 [1, 0, 1, 1, 2, 2, 2] = some [2, 0, 2, 1, 0, 0, 0] :=
  specInv_mirror_7 [1, 0, 1, 1, 2, 2, 2] [0, 1, 2, 1, 2, 2, 1] [2, 1, 1, 0, 0, 2, 1] [1, 0, 1, 2, 0, 0, 0] [2, 0, 2, 1, 0, 0, 0] demoR1_1011222 demoR2_1011222 demoC_1011222 demoM_1011222 demoMir_1011222

theorem demoR1_2011222 : invRung 7 5 20 [2, 0, 1, 1, 2, 2, 2] [2, 0, 1, 1, 2, 2, 2] 1 2 false = ([1, 1, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_2011222 : invRung 7 5 20 [2, 0, 1, 1, 2, 2, 2] [1, 1, 0, 2, 1, 0, 1] 3 1 true = ([0, 0, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_2011222 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 2, 2] = [2, 0, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_2011222 : fieldMul 7 5 20 [2, 0, 0, 1, 1, 0, 0] [2, 0, 1, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011222 : mirrorTrits [2, 0, 0, 1, 1, 0, 0] = [1, 0, 0, 2, 2, 0, 0] := by
  decide

theorem demoInv_2011222 : specInv 7 5 20 [2, 0, 1, 1, 2, 2, 2] = some [1, 0, 0, 2, 2, 0, 0] :=
  specInv_mirror_7 [2, 0, 1, 1, 2, 2, 2] [1, 1, 0, 2, 1, 0, 1] [0, 0, 1, 0, 2, 2, 2] [2, 0, 0, 1, 1, 0, 0] [1, 0, 0, 2, 2, 0, 0] demoR1_2011222 demoR2_2011222 demoC_2011222 demoM_2011222 demoMir_2011222

theorem demoR1_0111222 : invRung 7 5 20 [0, 1, 1, 1, 2, 2, 2] [0, 1, 1, 1, 2, 2, 2] 1 2 false = ([1, 2, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_0111222 : invRung 7 5 20 [0, 1, 1, 1, 2, 2, 2] [1, 2, 1, 1, 1, 2, 2] 3 1 true = ([2, 2, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0111222 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 2, 1] = [0, 1, 0, 1, 0, 0, 2] := by
  decide

theorem demoM_0111222 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 0, 2] [0, 1, 1, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111222 : mirrorTrits [0, 1, 0, 1, 0, 0, 2] = [0, 2, 0, 2, 0, 0, 1] := by
  decide

theorem demoInv_0111222 : specInv 7 5 20 [0, 1, 1, 1, 2, 2, 2] = some [0, 2, 0, 2, 0, 0, 1] :=
  specInv_mirror_7 [0, 1, 1, 1, 2, 2, 2] [1, 2, 1, 1, 1, 2, 2] [2, 2, 2, 2, 1, 2, 1] [0, 1, 0, 1, 0, 0, 2] [0, 2, 0, 2, 0, 0, 1] demoR1_0111222 demoR2_0111222 demoC_0111222 demoM_0111222 demoMir_0111222

theorem demoR1_1111222 : invRung 7 5 20 [1, 1, 1, 1, 2, 2, 2] [1, 1, 1, 1, 2, 2, 2] 1 2 false = ([1, 0, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_1111222 : invRung 7 5 20 [1, 1, 1, 1, 2, 2, 2] [1, 0, 1, 0, 1, 2, 0] 3 1 true = ([2, 0, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_1111222 : fieldCube 7 5 20 [2, 0, 1, 0, 0, 0, 2] = [2, 2, 1, 2, 2, 2, 0] := by
  decide

theorem demoM_1111222 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 2, 0] [1, 1, 1, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111222 : mirrorTrits [2, 2, 1, 2, 2, 2, 0] = [1, 1, 2, 1, 1, 1, 0] := by
  decide

theorem demoInv_1111222 : specInv 7 5 20 [1, 1, 1, 1, 2, 2, 2] = some [1, 1, 2, 1, 1, 1, 0] :=
  specInv_mirror_7 [1, 1, 1, 1, 2, 2, 2] [1, 0, 1, 0, 1, 2, 0] [2, 0, 1, 0, 0, 0, 2] [2, 2, 1, 2, 2, 2, 0] [1, 1, 2, 1, 1, 1, 0] demoR1_1111222 demoR2_1111222 demoC_1111222 demoM_1111222 demoMir_1111222

theorem demoR1_2111222 : invRung 7 5 20 [2, 1, 1, 1, 2, 2, 2] [2, 1, 1, 1, 2, 2, 2] 1 2 false = ([1, 1, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_2111222 : invRung 7 5 20 [2, 1, 1, 1, 2, 2, 2] [1, 1, 2, 1, 0, 1, 1] 3 1 true = ([1, 1, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2111222 : fieldCube 7 5 20 [1, 1, 1, 2, 0, 1, 0] = [1, 1, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_2111222 : fieldMul 7 5 20 [1, 1, 0, 1, 1, 0, 0] [2, 1, 1, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2111222 : mirrorTrits [1, 1, 0, 1, 1, 0, 0] = [2, 2, 0, 2, 2, 0, 0] := by
  decide

theorem demoInv_2111222 : specInv 7 5 20 [2, 1, 1, 1, 2, 2, 2] = some [2, 2, 0, 2, 2, 0, 0] :=
  specInv_mirror_7 [2, 1, 1, 1, 2, 2, 2] [1, 1, 2, 1, 0, 1, 1] [1, 1, 1, 2, 0, 1, 0] [1, 1, 0, 1, 1, 0, 0] [2, 2, 0, 2, 2, 0, 0] demoR1_2111222 demoR2_2111222 demoC_2111222 demoM_2111222 demoMir_2111222

theorem demoR1_0211222 : invRung 7 5 20 [0, 2, 1, 1, 2, 2, 2] [0, 2, 1, 1, 2, 2, 2] 1 2 false = ([2, 2, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_0211222 : invRung 7 5 20 [0, 2, 1, 1, 2, 2, 2] [2, 2, 0, 1, 0, 0, 2] 3 1 true = ([0, 0, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0211222 : fieldCube 7 5 20 [0, 0, 1, 0, 1, 0, 1] = [0, 2, 2, 2, 1, 2, 0] := by
  decide

theorem demoM_0211222 : fieldMul 7 5 20 [0, 2, 2, 2, 1, 2, 0] [0, 2, 1, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211222 : mirrorTrits [0, 2, 2, 2, 1, 2, 0] = [0, 1, 1, 1, 2, 1, 0] := by
  decide

theorem demoInv_0211222 : specInv 7 5 20 [0, 2, 1, 1, 2, 2, 2] = some [0, 1, 1, 1, 2, 1, 0] :=
  specInv_mirror_7 [0, 2, 1, 1, 2, 2, 2] [2, 2, 0, 1, 0, 0, 2] [0, 0, 1, 0, 1, 0, 1] [0, 2, 2, 2, 1, 2, 0] [0, 1, 1, 1, 2, 1, 0] demoR1_0211222 demoR2_0211222 demoC_0211222 demoM_0211222 demoMir_0211222

theorem demoR1_1211222 : invRung 7 5 20 [1, 2, 1, 1, 2, 2, 2] [1, 2, 1, 1, 2, 2, 2] 1 2 false = ([2, 0, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_1211222 : invRung 7 5 20 [1, 2, 1, 1, 2, 2, 2] [2, 0, 1, 2, 2, 1, 2] 3 1 true = ([0, 0, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1211222 : fieldCube 7 5 20 [0, 0, 1, 0, 1, 1, 1] = [1, 0, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_1211222 : fieldMul 7 5 20 [1, 0, 0, 2, 2, 0, 2] [1, 2, 1, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1211222 : specInv 7 5 20 [1, 2, 1, 1, 2, 2, 2] = some [1, 0, 0, 2, 2, 0, 2] :=
  specInv_white_7 [1, 2, 1, 1, 2, 2, 2] [2, 0, 1, 2, 2, 1, 2] [0, 0, 1, 0, 1, 1, 1] [1, 0, 0, 2, 2, 0, 2] demoR1_1211222 demoR2_1211222 demoC_1211222 demoM_1211222

theorem demoR1_2211222 : invRung 7 5 20 [2, 2, 1, 1, 2, 2, 2] [2, 2, 1, 1, 2, 2, 2] 1 2 false = ([1, 0, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2211222 : invRung 7 5 20 [2, 2, 1, 1, 2, 2, 2] [1, 0, 2, 1, 0, 0, 2] 3 1 true = ([1, 2, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_2211222 : fieldCube 7 5 20 [1, 2, 1, 0, 0, 0, 2] = [1, 2, 1, 1, 2, 2, 0] := by
  decide

theorem demoM_2211222 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 2, 0] [2, 2, 1, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2211222 : specInv 7 5 20 [2, 2, 1, 1, 2, 2, 2] = some [1, 2, 1, 1, 2, 2, 0] :=
  specInv_white_7 [2, 2, 1, 1, 2, 2, 2] [1, 0, 2, 1, 0, 0, 2] [1, 2, 1, 0, 0, 0, 2] [1, 2, 1, 1, 2, 2, 0] demoR1_2211222 demoR2_2211222 demoC_2211222 demoM_2211222

theorem demoR1_0021222 : invRung 7 5 20 [0, 0, 2, 1, 2, 2, 2] [0, 0, 2, 1, 2, 2, 2] 1 2 false = ([0, 0, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0021222 : invRung 7 5 20 [0, 0, 2, 1, 2, 2, 2] [0, 0, 1, 0, 2, 1, 2] 3 1 true = ([1, 0, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_0021222 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 0, 2] = [2, 0, 2, 0, 2, 1, 1] := by
  decide

theorem demoM_0021222 : fieldMul 7 5 20 [2, 0, 2, 0, 2, 1, 1] [0, 0, 2, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0021222 : specInv 7 5 20 [0, 0, 2, 1, 2, 2, 2] = some [2, 0, 2, 0, 2, 1, 1] :=
  specInv_white_7 [0, 0, 2, 1, 2, 2, 2] [0, 0, 1, 0, 2, 1, 2] [1, 0, 1, 1, 1, 0, 2] [2, 0, 2, 0, 2, 1, 1] demoR1_0021222 demoR2_0021222 demoC_0021222 demoM_0021222

theorem demoR1_1021222 : invRung 7 5 20 [1, 0, 2, 1, 2, 2, 2] [1, 0, 2, 1, 2, 2, 2] 1 2 false = ([2, 1, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_1021222 : invRung 7 5 20 [1, 0, 2, 1, 2, 2, 2] [2, 1, 2, 1, 1, 2, 2] 3 1 true = ([0, 0, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_1021222 : fieldCube 7 5 20 [0, 0, 1, 2, 0, 0, 1] = [2, 1, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_1021222 : fieldMul 7 5 20 [2, 1, 1, 1, 1, 0, 2] [1, 0, 2, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1021222 : specInv 7 5 20 [1, 0, 2, 1, 2, 2, 2] = some [2, 1, 1, 1, 1, 0, 2] :=
  specInv_white_7 [1, 0, 2, 1, 2, 2, 2] [2, 1, 2, 1, 1, 2, 2] [0, 0, 1, 2, 0, 0, 1] [2, 1, 1, 1, 1, 0, 2] demoR1_1021222 demoR2_1021222 demoC_1021222 demoM_1021222

theorem demoR1_2021222 : invRung 7 5 20 [2, 0, 2, 1, 2, 2, 2] [2, 0, 2, 1, 2, 2, 2] 1 2 false = ([2, 2, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2021222 : invRung 7 5 20 [2, 0, 2, 1, 2, 2, 2] [2, 2, 2, 1, 1, 2, 0] 3 1 true = ([2, 1, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_2021222 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 2, 1] = [0, 2, 0, 1, 0, 1, 1] := by
  decide

theorem demoM_2021222 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 1, 1] [2, 0, 2, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021222 : mirrorTrits [0, 2, 0, 1, 0, 1, 1] = [0, 1, 0, 2, 0, 2, 2] := by
  decide

theorem demoInv_2021222 : specInv 7 5 20 [2, 0, 2, 1, 2, 2, 2] = some [0, 1, 0, 2, 0, 2, 2] :=
  specInv_mirror_7 [2, 0, 2, 1, 2, 2, 2] [2, 2, 2, 1, 1, 2, 0] [2, 1, 0, 2, 2, 2, 1] [0, 2, 0, 1, 0, 1, 1] [0, 1, 0, 2, 0, 2, 2] demoR1_2021222 demoR2_2021222 demoC_2021222 demoM_2021222 demoMir_2021222

theorem demoR1_0121222 : invRung 7 5 20 [0, 1, 2, 1, 2, 2, 2] [0, 1, 2, 1, 2, 2, 2] 1 2 false = ([2, 2, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_0121222 : invRung 7 5 20 [0, 1, 2, 1, 2, 2, 2] [2, 2, 2, 2, 2, 2, 2] 3 1 true = ([0, 2, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0121222 : fieldCube 7 5 20 [0, 2, 1, 0, 2, 1, 0] = [1, 0, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_0121222 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 0, 2] [0, 1, 2, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0121222 : mirrorTrits [1, 0, 1, 1, 1, 0, 2] = [2, 0, 2, 2, 2, 0, 1] := by
  decide

theorem demoInv_0121222 : specInv 7 5 20 [0, 1, 2, 1, 2, 2, 2] = some [2, 0, 2, 2, 2, 0, 1] :=
  specInv_mirror_7 [0, 1, 2, 1, 2, 2, 2] [2, 2, 2, 2, 2, 2, 2] [0, 2, 1, 0, 2, 1, 0] [1, 0, 1, 1, 1, 0, 2] [2, 0, 2, 2, 2, 0, 1] demoR1_0121222 demoR2_0121222 demoC_0121222 demoM_0121222 demoMir_0121222

theorem demoR1_1121222 : invRung 7 5 20 [1, 1, 2, 1, 2, 2, 2] [1, 1, 2, 1, 2, 2, 2] 1 2 false = ([1, 1, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_1121222 : invRung 7 5 20 [1, 1, 2, 1, 2, 2, 2] [1, 1, 2, 0, 2, 0, 2] 3 1 true = ([2, 0, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1121222 : fieldCube 7 5 20 [2, 0, 1, 1, 2, 2, 0] = [2, 1, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_1121222 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 2, 1] [1, 1, 2, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1121222 : specInv 7 5 20 [1, 1, 2, 1, 2, 2, 2] = some [2, 1, 0, 2, 2, 2, 1] :=
  specInv_white_7 [1, 1, 2, 1, 2, 2, 2] [1, 1, 2, 0, 2, 0, 2] [2, 0, 1, 1, 2, 2, 0] [2, 1, 0, 2, 2, 2, 1] demoR1_1121222 demoR2_1121222 demoC_1121222 demoM_1121222

theorem demoR1_2121222 : invRung 7 5 20 [2, 1, 2, 1, 2, 2, 2] [2, 1, 2, 1, 2, 2, 2] 1 2 false = ([0, 2, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_2121222 : invRung 7 5 20 [2, 1, 2, 1, 2, 2, 2] [0, 2, 0, 2, 0, 2, 0] 3 1 true = ([1, 1, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_2121222 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 2, 1] = [0, 0, 1, 2, 0, 0, 1] := by
  decide

theorem demoM_2121222 : fieldMul 7 5 20 [0, 0, 1, 2, 0, 0, 1] [2, 1, 2, 1, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2121222 : mirrorTrits [0, 0, 1, 2, 0, 0, 1] = [0, 0, 2, 1, 0, 0, 2] := by
  decide

theorem demoInv_2121222 : specInv 7 5 20 [2, 1, 2, 1, 2, 2, 2] = some [0, 0, 2, 1, 0, 0, 2] :=
  specInv_mirror_7 [2, 1, 2, 1, 2, 2, 2] [0, 2, 0, 2, 0, 2, 0] [1, 1, 2, 0, 0, 2, 1] [0, 0, 1, 2, 0, 0, 1] [0, 0, 2, 1, 0, 0, 2] demoR1_2121222 demoR2_2121222 demoC_2121222 demoM_2121222 demoMir_2121222

theorem demoR1_0221222 : invRung 7 5 20 [0, 2, 2, 1, 2, 2, 2] [0, 2, 2, 1, 2, 2, 2] 1 2 false = ([2, 0, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_0221222 : invRung 7 5 20 [0, 2, 2, 1, 2, 2, 2] [2, 0, 2, 0, 2, 1, 1] 3 1 true = ([2, 0, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0221222 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 1, 1] = [2, 2, 2, 1, 2, 1, 2] := by
  decide

theorem demoM_0221222 : fieldMul 7 5 20 [2, 2, 2, 1, 2, 1, 2] [0, 2, 2, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0221222 : specInv 7 5 20 [0, 2, 2, 1, 2, 2, 2] = some [2, 2, 2, 1, 2, 1, 2] :=
  specInv_white_7 [0, 2, 2, 1, 2, 2, 2] [2, 0, 2, 0, 2, 1, 1] [2, 0, 2, 2, 0, 1, 1] [2, 2, 2, 1, 2, 1, 2] demoR1_0221222 demoR2_0221222 demoC_0221222 demoM_0221222

theorem demoR1_1221222 : invRung 7 5 20 [1, 2, 2, 1, 2, 2, 2] [1, 2, 2, 1, 2, 2, 2] 1 2 false = ([1, 1, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_1221222 : invRung 7 5 20 [1, 2, 2, 1, 2, 2, 2] [1, 1, 1, 2, 2, 1, 2] 3 1 true = ([0, 0, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_1221222 : fieldCube 7 5 20 [0, 0, 1, 1, 1, 0, 1] = [1, 2, 0, 2, 1, 0, 0] := by
  decide

theorem demoM_1221222 : fieldMul 7 5 20 [1, 2, 0, 2, 1, 0, 0] [1, 2, 2, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1221222 : specInv 7 5 20 [1, 2, 2, 1, 2, 2, 2] = some [1, 2, 0, 2, 1, 0, 0] :=
  specInv_white_7 [1, 2, 2, 1, 2, 2, 2] [1, 1, 1, 2, 2, 1, 2] [0, 0, 1, 1, 1, 0, 1] [1, 2, 0, 2, 1, 0, 0] demoR1_1221222 demoR2_1221222 demoC_1221222 demoM_1221222

theorem demoR1_2221222 : invRung 7 5 20 [2, 2, 2, 1, 2, 2, 2] [2, 2, 2, 1, 2, 2, 2] 1 2 false = ([2, 0, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_2221222 : invRung 7 5 20 [2, 2, 2, 1, 2, 2, 2] [2, 0, 0, 1, 0, 1, 1] 3 1 true = ([0, 0, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_2221222 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 1, 1] = [1, 1, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_2221222 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 1, 0] [2, 2, 2, 1, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2221222 : specInv 7 5 20 [2, 2, 2, 1, 2, 2, 2] = some [1, 1, 0, 0, 2, 1, 0] :=
  specInv_white_7 [2, 2, 2, 1, 2, 2, 2] [2, 0, 0, 1, 0, 1, 1] [0, 0, 1, 0, 2, 1, 1] [1, 1, 0, 0, 2, 1, 0] demoR1_2221222 demoR2_2221222 demoC_2221222 demoM_2221222

theorem demoR1_0002222 : invRung 7 5 20 [0, 0, 0, 2, 2, 2, 2] [0, 0, 0, 2, 2, 2, 2] 1 2 false = ([2, 1, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_0002222 : invRung 7 5 20 [0, 0, 0, 2, 2, 2, 2] [2, 1, 0, 2, 0, 2, 2] 3 1 true = ([0, 1, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_0002222 : fieldCube 7 5 20 [0, 1, 1, 2, 0, 2, 1] = [1, 0, 0, 2, 0, 2, 0] := by
  decide

theorem demoM_0002222 : fieldMul 7 5 20 [1, 0, 0, 2, 0, 2, 0] [0, 0, 0, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0002222 : specInv 7 5 20 [0, 0, 0, 2, 2, 2, 2] = some [1, 0, 0, 2, 0, 2, 0] :=
  specInv_white_7 [0, 0, 0, 2, 2, 2, 2] [2, 1, 0, 2, 0, 2, 2] [0, 1, 1, 2, 0, 2, 1] [1, 0, 0, 2, 0, 2, 0] demoR1_0002222 demoR2_0002222 demoC_0002222 demoM_0002222

theorem demoR1_1002222 : invRung 7 5 20 [1, 0, 0, 2, 2, 2, 2] [1, 0, 0, 2, 2, 2, 2] 1 2 false = ([2, 0, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_1002222 : invRung 7 5 20 [1, 0, 0, 2, 2, 2, 2] [2, 0, 0, 2, 2, 1, 2] 3 1 true = ([0, 1, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_1002222 : fieldCube 7 5 20 [0, 1, 1, 0, 1, 0, 1] = [0, 2, 2, 0, 1, 2, 0] := by
  decide

theorem demoM_1002222 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 2, 0] [1, 0, 0, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002222 : mirrorTrits [0, 2, 2, 0, 1, 2, 0] = [0, 1, 1, 0, 2, 1, 0] := by
  decide

theorem demoInv_1002222 : specInv 7 5 20 [1, 0, 0, 2, 2, 2, 2] = some [0, 1, 1, 0, 2, 1, 0] :=
  specInv_mirror_7 [1, 0, 0, 2, 2, 2, 2] [2, 0, 0, 2, 2, 1, 2] [0, 1, 1, 0, 1, 0, 1] [0, 2, 2, 0, 1, 2, 0] [0, 1, 1, 0, 2, 1, 0] demoR1_1002222 demoR2_1002222 demoC_1002222 demoM_1002222 demoMir_1002222

theorem demoR1_2002222 : invRung 7 5 20 [2, 0, 0, 2, 2, 2, 2] [2, 0, 0, 2, 2, 2, 2] 1 2 false = ([0, 0, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_2002222 : invRung 7 5 20 [2, 0, 0, 2, 2, 2, 2] [0, 0, 0, 2, 0, 2, 1] 3 1 true = ([2, 0, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2002222 : fieldCube 7 5 20 [2, 0, 2, 1, 2, 2, 0] = [2, 1, 0, 2, 2, 2, 2] := by
  decide

theorem demoM_2002222 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 2, 2] [2, 0, 0, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002222 : mirrorTrits [2, 1, 0, 2, 2, 2, 2] = [1, 2, 0, 1, 1, 1, 1] := by
  decide

theorem demoInv_2002222 : specInv 7 5 20 [2, 0, 0, 2, 2, 2, 2] = some [1, 2, 0, 1, 1, 1, 1] :=
  specInv_mirror_7 [2, 0, 0, 2, 2, 2, 2] [0, 0, 0, 2, 0, 2, 1] [2, 0, 2, 1, 2, 2, 0] [2, 1, 0, 2, 2, 2, 2] [1, 2, 0, 1, 1, 1, 1] demoR1_2002222 demoR2_2002222 demoC_2002222 demoM_2002222 demoMir_2002222

theorem demoR1_0102222 : invRung 7 5 20 [0, 1, 0, 2, 2, 2, 2] [0, 1, 0, 2, 2, 2, 2] 1 2 false = ([0, 0, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0102222 : invRung 7 5 20 [0, 1, 0, 2, 2, 2, 2] [0, 0, 0, 1, 1, 1, 2] 3 1 true = ([1, 2, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_0102222 : fieldCube 7 5 20 [1, 2, 2, 0, 2, 0, 2] = [1, 1, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_0102222 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 1, 0] [0, 1, 0, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0102222 : specInv 7 5 20 [0, 1, 0, 2, 2, 2, 2] = some [1, 1, 1, 0, 2, 1, 0] :=
  specInv_white_7 [0, 1, 0, 2, 2, 2, 2] [0, 0, 0, 1, 1, 1, 2] [1, 2, 2, 0, 2, 0, 2] [1, 1, 1, 0, 2, 1, 0] demoR1_0102222 demoR2_0102222 demoC_0102222 demoM_0102222

theorem demoR1_1102222 : invRung 7 5 20 [1, 1, 0, 2, 2, 2, 2] [1, 1, 0, 2, 2, 2, 2] 1 2 false = ([1, 2, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1102222 : invRung 7 5 20 [1, 1, 0, 2, 2, 2, 2] [1, 2, 0, 0, 1, 0, 1] 3 1 true = ([2, 1, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_1102222 : fieldCube 7 5 20 [2, 1, 1, 2, 0, 2, 1] = [0, 0, 0, 2, 0, 2, 0] := by
  decide

theorem demoM_1102222 : fieldMul 7 5 20 [0, 0, 0, 2, 0, 2, 0] [1, 1, 0, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1102222 : specInv 7 5 20 [1, 1, 0, 2, 2, 2, 2] = some [0, 0, 0, 2, 0, 2, 0] :=
  specInv_white_7 [1, 1, 0, 2, 2, 2, 2] [1, 2, 0, 0, 1, 0, 1] [2, 1, 1, 2, 0, 2, 1] [0, 0, 0, 2, 0, 2, 0] demoR1_1102222 demoR2_1102222 demoC_1102222 demoM_1102222

theorem demoR1_2102222 : invRung 7 5 20 [2, 1, 0, 2, 2, 2, 2] [2, 1, 0, 2, 2, 2, 2] 1 2 false = ([2, 1, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2102222 : invRung 7 5 20 [2, 1, 0, 2, 2, 2, 2] [2, 1, 2, 1, 0, 0, 2] 3 1 true = ([0, 1, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_2102222 : fieldCube 7 5 20 [0, 1, 1, 1, 2, 0, 1] = [1, 0, 0, 1, 1, 1, 1] := by
  decide

theorem demoM_2102222 : fieldMul 7 5 20 [1, 0, 0, 1, 1, 1, 1] [2, 1, 0, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2102222 : specInv 7 5 20 [2, 1, 0, 2, 2, 2, 2] = some [1, 0, 0, 1, 1, 1, 1] :=
  specInv_white_7 [2, 1, 0, 2, 2, 2, 2] [2, 1, 2, 1, 0, 0, 2] [0, 1, 1, 1, 2, 0, 1] [1, 0, 0, 1, 1, 1, 1] demoR1_2102222 demoR2_2102222 demoC_2102222 demoM_2102222

theorem demoR1_0202222 : invRung 7 5 20 [0, 2, 0, 2, 2, 2, 2] [0, 2, 0, 2, 2, 2, 2] 1 2 false = ([0, 1, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_0202222 : invRung 7 5 20 [0, 2, 0, 2, 2, 2, 2] [0, 1, 0, 0, 1, 0, 2] 3 1 true = ([1, 1, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_0202222 : fieldCube 7 5 20 [1, 1, 1, 2, 0, 0, 2] = [0, 2, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_0202222 : fieldMul 7 5 20 [0, 2, 0, 0, 2, 1, 0] [0, 2, 0, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0202222 : specInv 7 5 20 [0, 2, 0, 2, 2, 2, 2] = some [0, 2, 0, 0, 2, 1, 0] :=
  specInv_white_7 [0, 2, 0, 2, 2, 2, 2] [0, 1, 0, 0, 1, 0, 2] [1, 1, 1, 2, 0, 0, 2] [0, 2, 0, 0, 2, 1, 0] demoR1_0202222 demoR2_0202222 demoC_0202222 demoM_0202222

theorem demoR1_1202222 : invRung 7 5 20 [1, 2, 0, 2, 2, 2, 2] [1, 2, 0, 2, 2, 2, 2] 1 2 false = ([2, 1, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_1202222 : invRung 7 5 20 [1, 2, 0, 2, 2, 2, 2] [2, 1, 0, 2, 1, 1, 1] 3 1 true = ([2, 1, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_1202222 : fieldCube 7 5 20 [2, 1, 2, 2, 2, 1, 2] = [2, 2, 1, 2, 0, 1, 2] := by
  decide

theorem demoM_1202222 : fieldMul 7 5 20 [2, 2, 1, 2, 0, 1, 2] [1, 2, 0, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202222 : mirrorTrits [2, 2, 1, 2, 0, 1, 2] = [1, 1, 2, 1, 0, 2, 1] := by
  decide

theorem demoInv_1202222 : specInv 7 5 20 [1, 2, 0, 2, 2, 2, 2] = some [1, 1, 2, 1, 0, 2, 1] :=
  specInv_mirror_7 [1, 2, 0, 2, 2, 2, 2] [2, 1, 0, 2, 1, 1, 1] [2, 1, 2, 2, 2, 1, 2] [2, 2, 1, 2, 0, 1, 2] [1, 1, 2, 1, 0, 2, 1] demoR1_1202222 demoR2_1202222 demoC_1202222 demoM_1202222 demoMir_1202222

theorem demoR1_2202222 : invRung 7 5 20 [2, 2, 0, 2, 2, 2, 2] [2, 2, 0, 2, 2, 2, 2] 1 2 false = ([0, 0, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_2202222 : invRung 7 5 20 [2, 2, 0, 2, 2, 2, 2] [0, 0, 1, 2, 0, 2, 2] 3 1 true = ([0, 0, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_2202222 : fieldCube 7 5 20 [0, 0, 0, 1, 1, 1, 0] = [2, 2, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_2202222 : fieldMul 7 5 20 [2, 2, 2, 1, 1, 0, 0] [2, 2, 0, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202222 : mirrorTrits [2, 2, 2, 1, 1, 0, 0] = [1, 1, 1, 2, 2, 0, 0] := by
  decide

theorem demoInv_2202222 : specInv 7 5 20 [2, 2, 0, 2, 2, 2, 2] = some [1, 1, 1, 2, 2, 0, 0] :=
  specInv_mirror_7 [2, 2, 0, 2, 2, 2, 2] [0, 0, 1, 2, 0, 2, 2] [0, 0, 0, 1, 1, 1, 0] [2, 2, 2, 1, 1, 0, 0] [1, 1, 1, 2, 2, 0, 0] demoR1_2202222 demoR2_2202222 demoC_2202222 demoM_2202222 demoMir_2202222

theorem demoR1_0012222 : invRung 7 5 20 [0, 0, 1, 2, 2, 2, 2] [0, 0, 1, 2, 2, 2, 2] 1 2 false = ([0, 1, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0012222 : invRung 7 5 20 [0, 0, 1, 2, 2, 2, 2] [0, 1, 2, 1, 0, 0, 0] 3 1 true = ([0, 1, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0012222 : fieldCube 7 5 20 [0, 1, 1, 1, 1, 2, 2] = [0, 2, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_0012222 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 0, 2] [0, 0, 1, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0012222 : specInv 7 5 20 [0, 0, 1, 2, 2, 2, 2] = some [0, 2, 1, 1, 1, 0, 2] :=
  specInv_white_7 [0, 0, 1, 2, 2, 2, 2] [0, 1, 2, 1, 0, 0, 0] [0, 1, 1, 1, 1, 2, 2] [0, 2, 1, 1, 1, 0, 2] demoR1_0012222 demoR2_0012222 demoC_0012222 demoM_0012222

theorem demoR1_1012222 : invRung 7 5 20 [1, 0, 1, 2, 2, 2, 2] [1, 0, 1, 2, 2, 2, 2] 1 2 false = ([0, 0, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_1012222 : invRung 7 5 20 [1, 0, 1, 2, 2, 2, 2] [0, 0, 1, 0, 0, 0, 2] 3 1 true = ([2, 2, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_1012222 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 2, 1] = [2, 2, 2, 2, 0, 0, 1] := by
  decide

theorem demoM_1012222 : fieldMul 7 5 20 [2, 2, 2, 2, 0, 0, 1] [1, 0, 1, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1012222 : specInv 7 5 20 [1, 0, 1, 2, 2, 2, 2] = some [2, 2, 2, 2, 0, 0, 1] :=
  specInv_white_7 [1, 0, 1, 2, 2, 2, 2] [0, 0, 1, 0, 0, 0, 2] [2, 2, 0, 1, 2, 2, 1] [2, 2, 2, 2, 0, 0, 1] demoR1_1012222 demoR2_1012222 demoC_1012222 demoM_1012222

theorem demoR1_2012222 : invRung 7 5 20 [2, 0, 1, 2, 2, 2, 2] [2, 0, 1, 2, 2, 2, 2] 1 2 false = ([1, 2, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_2012222 : invRung 7 5 20 [2, 0, 1, 2, 2, 2, 2] [1, 2, 0, 1, 1, 1, 1] 3 1 true = ([2, 1, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_2012222 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 2, 2] = [2, 1, 1, 0, 1, 2, 1] := by
  decide

theorem demoM_2012222 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 2, 1] [2, 0, 1, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012222 : mirrorTrits [2, 1, 1, 0, 1, 2, 1] = [1, 2, 2, 0, 2, 1, 2] := by
  decide

theorem demoInv_2012222 : specInv 7 5 20 [2, 0, 1, 2, 2, 2, 2] = some [1, 2, 2, 0, 2, 1, 2] :=
  specInv_mirror_7 [2, 0, 1, 2, 2, 2, 2] [1, 2, 0, 1, 1, 1, 1] [2, 1, 1, 1, 0, 2, 2] [2, 1, 1, 0, 1, 2, 1] [1, 2, 2, 0, 2, 1, 2] demoR1_2012222 demoR2_2012222 demoC_2012222 demoM_2012222 demoMir_2012222

theorem demoR1_0112222 : invRung 7 5 20 [0, 1, 1, 2, 2, 2, 2] [0, 1, 1, 2, 2, 2, 2] 1 2 false = ([0, 2, 2, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_0112222 : invRung 7 5 20 [0, 1, 1, 2, 2, 2, 2] [0, 2, 2, 0, 2, 2, 0] 3 1 true = ([0, 1, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0112222 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 1, 2] = [2, 0, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_0112222 : fieldMul 7 5 20 [2, 0, 0, 0, 0, 1, 0] [0, 1, 1, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112222 : mirrorTrits [2, 0, 0, 0, 0, 1, 0] = [1, 0, 0, 0, 0, 2, 0] := by
  decide

theorem demoInv_0112222 : specInv 7 5 20 [0, 1, 1, 2, 2, 2, 2] = some [1, 0, 0, 0, 0, 2, 0] :=
  specInv_mirror_7 [0, 1, 1, 2, 2, 2, 2] [0, 2, 2, 0, 2, 2, 0] [0, 1, 2, 1, 0, 1, 2] [2, 0, 0, 0, 0, 1, 0] [1, 0, 0, 0, 0, 2, 0] demoR1_0112222 demoR2_0112222 demoC_0112222 demoM_0112222 demoMir_0112222

theorem demoR1_1112222 : invRung 7 5 20 [1, 1, 1, 2, 2, 2, 2] [1, 1, 1, 2, 2, 2, 2] 1 2 false = ([1, 0, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1112222 : invRung 7 5 20 [1, 1, 1, 2, 2, 2, 2] [1, 0, 2, 0, 1, 0, 0] 3 1 true = ([1, 0, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_1112222 : fieldCube 7 5 20 [1, 0, 1, 2, 0, 2, 1] = [2, 0, 0, 1, 0, 2, 0] := by
  decide

theorem demoM_1112222 : fieldMul 7 5 20 [2, 0, 0, 1, 0, 2, 0] [1, 1, 1, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1112222 : specInv 7 5 20 [1, 1, 1, 2, 2, 2, 2] = some [2, 0, 0, 1, 0, 2, 0] :=
  specInv_white_7 [1, 1, 1, 2, 2, 2, 2] [1, 0, 2, 0, 1, 0, 0] [1, 0, 1, 2, 0, 2, 1] [2, 0, 0, 1, 0, 2, 0] demoR1_1112222 demoR2_1112222 demoC_1112222 demoM_1112222

theorem demoR1_2112222 : invRung 7 5 20 [2, 1, 1, 2, 2, 2, 2] [2, 1, 1, 2, 2, 2, 2] 1 2 false = ([2, 0, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_2112222 : invRung 7 5 20 [2, 1, 1, 2, 2, 2, 2] [2, 0, 1, 1, 1, 1, 0] 3 1 true = ([1, 1, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_2112222 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 1, 2] = [2, 0, 2, 0, 0, 0, 0] := by
  decide

theorem demoM_2112222 : fieldMul 7 5 20 [2, 0, 2, 0, 0, 0, 0] [2, 1, 1, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112222 : mirrorTrits [2, 0, 2, 0, 0, 0, 0] = [1, 0, 1, 0, 0, 0, 0] := by
  decide

theorem demoInv_2112222 : specInv 7 5 20 [2, 1, 1, 2, 2, 2, 2] = some [1, 0, 1, 0, 0, 0, 0] :=
  specInv_mirror_7 [2, 1, 1, 2, 2, 2, 2] [2, 0, 1, 1, 1, 1, 0] [1, 1, 2, 0, 0, 1, 2] [2, 0, 2, 0, 0, 0, 0] [1, 0, 1, 0, 0, 0, 0] demoR1_2112222 demoR2_2112222 demoC_2112222 demoM_2112222 demoMir_2112222

theorem demoR1_0212222 : invRung 7 5 20 [0, 2, 1, 2, 2, 2, 2] [0, 2, 1, 2, 2, 2, 2] 1 2 false = ([0, 1, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_0212222 : invRung 7 5 20 [0, 2, 1, 2, 2, 2, 2] [0, 1, 0, 2, 0, 2, 0] 3 1 true = ([0, 1, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_0212222 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 0, 2] = [0, 0, 1, 1, 2, 0, 0] := by
  decide

theorem demoM_0212222 : fieldMul 7 5 20 [0, 0, 1, 1, 2, 0, 0] [0, 2, 1, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212222 : mirrorTrits [0, 0, 1, 1, 2, 0, 0] = [0, 0, 2, 2, 1, 0, 0] := by
  decide

theorem demoInv_0212222 : specInv 7 5 20 [0, 2, 1, 2, 2, 2, 2] = some [0, 0, 2, 2, 1, 0, 0] :=
  specInv_mirror_7 [0, 2, 1, 2, 2, 2, 2] [0, 1, 0, 2, 0, 2, 0] [0, 1, 0, 0, 1, 0, 2] [0, 0, 1, 1, 2, 0, 0] [0, 0, 2, 2, 1, 0, 0] demoR1_0212222 demoR2_0212222 demoC_0212222 demoM_0212222 demoMir_0212222

theorem demoR1_1212222 : invRung 7 5 20 [1, 2, 1, 2, 2, 2, 2] [1, 2, 1, 2, 2, 2, 2] 1 2 false = ([2, 2, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_1212222 : invRung 7 5 20 [1, 2, 1, 2, 2, 2, 2] [2, 2, 1, 1, 0, 0, 2] 3 1 true = ([1, 1, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_1212222 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 1, 2] = [2, 1, 2, 1, 0, 1, 0] := by
  decide

theorem demoM_1212222 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 1, 0] [1, 2, 1, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212222 : mirrorTrits [2, 1, 2, 1, 0, 1, 0] = [1, 2, 1, 2, 0, 2, 0] := by
  decide

theorem demoInv_1212222 : specInv 7 5 20 [1, 2, 1, 2, 2, 2, 2] = some [1, 2, 1, 2, 0, 2, 0] :=
  specInv_mirror_7 [1, 2, 1, 2, 2, 2, 2] [2, 2, 1, 1, 0, 0, 2] [1, 1, 1, 0, 1, 1, 2] [2, 1, 2, 1, 0, 1, 0] [1, 2, 1, 2, 0, 2, 0] demoR1_1212222 demoR2_1212222 demoC_1212222 demoM_1212222 demoMir_1212222

theorem demoR1_2212222 : invRung 7 5 20 [2, 2, 1, 2, 2, 2, 2] [2, 2, 1, 2, 2, 2, 2] 1 2 false = ([0, 1, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_2212222 : invRung 7 5 20 [2, 2, 1, 2, 2, 2, 2] [0, 1, 0, 0, 1, 0, 1] 3 1 true = ([0, 0, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2212222 : fieldCube 7 5 20 [0, 0, 1, 1, 2, 1, 0] = [2, 0, 2, 2, 1, 1, 2] := by
  decide

theorem demoM_2212222 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 1, 2] [2, 2, 1, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2212222 : specInv 7 5 20 [2, 2, 1, 2, 2, 2, 2] = some [2, 0, 2, 2, 1, 1, 2] :=
  specInv_white_7 [2, 2, 1, 2, 2, 2, 2] [0, 1, 0, 0, 1, 0, 1] [0, 0, 1, 1, 2, 1, 0] [2, 0, 2, 2, 1, 1, 2] demoR1_2212222 demoR2_2212222 demoC_2212222 demoM_2212222

theorem demoR1_0022222 : invRung 7 5 20 [0, 0, 2, 2, 2, 2, 2] [0, 0, 2, 2, 2, 2, 2] 1 2 false = ([2, 1, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_0022222 : invRung 7 5 20 [0, 0, 2, 2, 2, 2, 2] [2, 1, 1, 2, 0, 1, 2] 3 1 true = ([2, 0, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_0022222 : fieldCube 7 5 20 [2, 0, 2, 0, 2, 1, 1] = [0, 1, 0, 0, 2, 1, 1] := by
  decide

theorem demoM_0022222 : fieldMul 7 5 20 [0, 1, 0, 0, 2, 1, 1] [0, 0, 2, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022222 : mirrorTrits [0, 1, 0, 0, 2, 1, 1] = [0, 2, 0, 0, 1, 2, 2] := by
  decide

theorem demoInv_0022222 : specInv 7 5 20 [0, 0, 2, 2, 2, 2, 2] = some [0, 2, 0, 0, 1, 2, 2] :=
  specInv_mirror_7 [0, 0, 2, 2, 2, 2, 2] [2, 1, 1, 2, 0, 1, 2] [2, 0, 2, 0, 2, 1, 1] [0, 1, 0, 0, 2, 1, 1] [0, 2, 0, 0, 1, 2, 2] demoR1_0022222 demoR2_0022222 demoC_0022222 demoM_0022222 demoMir_0022222

theorem demoR1_1022222 : invRung 7 5 20 [1, 0, 2, 2, 2, 2, 2] [1, 0, 2, 2, 2, 2, 2] 1 2 false = ([1, 0, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_1022222 : invRung 7 5 20 [1, 0, 2, 2, 2, 2, 2] [1, 0, 0, 0, 1, 2, 2] 3 1 true = ([0, 2, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1022222 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 1, 1] = [2, 2, 1, 0, 2, 0, 0] := by
  decide

theorem demoM_1022222 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 0, 0] [1, 0, 2, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1022222 : specInv 7 5 20 [1, 0, 2, 2, 2, 2, 2] = some [2, 2, 1, 0, 2, 0, 0] :=
  specInv_white_7 [1, 0, 2, 2, 2, 2, 2] [1, 0, 0, 0, 1, 2, 2] [0, 2, 0, 1, 0, 1, 1] [2, 2, 1, 0, 2, 0, 0] demoR1_1022222 demoR2_1022222 demoC_1022222 demoM_1022222

theorem demoR1_2022222 : invRung 7 5 20 [2, 0, 2, 2, 2, 2, 2] [2, 0, 2, 2, 2, 2, 2] 1 2 false = ([1, 1, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2022222 : invRung 7 5 20 [2, 0, 2, 2, 2, 2, 2] [1, 1, 2, 2, 2, 0, 0] 3 1 true = ([2, 1, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_2022222 : fieldCube 7 5 20 [2, 1, 1, 1, 1, 0, 2] = [0, 0, 2, 1, 2, 1, 1] := by
  decide

theorem demoM_2022222 : fieldMul 7 5 20 [0, 0, 2, 1, 2, 1, 1] [2, 0, 2, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022222 : mirrorTrits [0, 0, 2, 1, 2, 1, 1] = [0, 0, 1, 2, 1, 2, 2] := by
  decide

theorem demoInv_2022222 : specInv 7 5 20 [2, 0, 2, 2, 2, 2, 2] = some [0, 0, 1, 2, 1, 2, 2] :=
  specInv_mirror_7 [2, 0, 2, 2, 2, 2, 2] [1, 1, 2, 2, 2, 0, 0] [2, 1, 1, 1, 1, 0, 2] [0, 0, 2, 1, 2, 1, 1] [0, 0, 1, 2, 1, 2, 2] demoR1_2022222 demoR2_2022222 demoC_2022222 demoM_2022222 demoMir_2022222

theorem demoR1_0122222 : invRung 7 5 20 [0, 1, 2, 2, 2, 2, 2] [0, 1, 2, 2, 2, 2, 2] 1 2 false = ([1, 0, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_0122222 : invRung 7 5 20 [0, 1, 2, 2, 2, 2, 2] [1, 0, 0, 0, 2, 2, 1] 3 1 true = ([1, 0, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_0122222 : fieldCube 7 5 20 [1, 0, 2, 0, 0, 1, 0] = [2, 1, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_0122222 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 1, 1] [0, 1, 2, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0122222 : specInv 7 5 20 [0, 1, 2, 2, 2, 2, 2] = some [2, 1, 1, 0, 1, 1, 1] :=
  specInv_white_7 [0, 1, 2, 2, 2, 2, 2] [1, 0, 0, 0, 2, 2, 1] [1, 0, 2, 0, 0, 1, 0] [2, 1, 1, 0, 1, 1, 1] demoR1_0122222 demoR2_0122222 demoC_0122222 demoM_0122222

theorem demoR1_1122222 : invRung 7 5 20 [1, 1, 2, 2, 2, 2, 2] [1, 1, 2, 2, 2, 2, 2] 1 2 false = ([1, 0, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_1122222 : invRung 7 5 20 [1, 1, 2, 2, 2, 2, 2] [1, 0, 1, 1, 0, 2, 1] 3 1 true = ([1, 0, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_1122222 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 1, 2] = [0, 1, 0, 0, 0, 2, 0] := by
  decide

theorem demoM_1122222 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 2, 0] [1, 1, 2, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122222 : mirrorTrits [0, 1, 0, 0, 0, 2, 0] = [0, 2, 0, 0, 0, 1, 0] := by
  decide

theorem demoInv_1122222 : specInv 7 5 20 [1, 1, 2, 2, 2, 2, 2] = some [0, 2, 0, 0, 0, 1, 0] :=
  specInv_mirror_7 [1, 1, 2, 2, 2, 2, 2] [1, 0, 1, 1, 0, 2, 1] [1, 0, 1, 1, 1, 1, 2] [0, 1, 0, 0, 0, 2, 0] [0, 2, 0, 0, 0, 1, 0] demoR1_1122222 demoR2_1122222 demoC_1122222 demoM_1122222 demoMir_1122222

theorem demoR1_2122222 : invRung 7 5 20 [2, 1, 2, 2, 2, 2, 2] [2, 1, 2, 2, 2, 2, 2] 1 2 false = ([1, 1, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2122222 : invRung 7 5 20 [2, 1, 2, 2, 2, 2, 2] [1, 1, 1, 2, 1, 1, 2] 3 1 true = ([1, 1, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_2122222 : fieldCube 7 5 20 [1, 1, 2, 1, 1, 1, 2] = [0, 1, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_2122222 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 2, 1] [2, 1, 2, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122222 : mirrorTrits [0, 1, 0, 1, 0, 2, 1] = [0, 2, 0, 2, 0, 1, 2] := by
  decide

theorem demoInv_2122222 : specInv 7 5 20 [2, 1, 2, 2, 2, 2, 2] = some [0, 2, 0, 2, 0, 1, 2] :=
  specInv_mirror_7 [2, 1, 2, 2, 2, 2, 2] [1, 1, 1, 2, 1, 1, 2] [1, 1, 2, 1, 1, 1, 2] [0, 1, 0, 1, 0, 2, 1] [0, 2, 0, 2, 0, 1, 2] demoR1_2122222 demoR2_2122222 demoC_2122222 demoM_2122222 demoMir_2122222

theorem demoR1_0222222 : invRung 7 5 20 [0, 2, 2, 2, 2, 2, 2] [0, 2, 2, 2, 2, 2, 2] 1 2 false = ([1, 2, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_0222222 : invRung 7 5 20 [0, 2, 2, 2, 2, 2, 2] [1, 2, 1, 1, 0, 2, 0] 3 1 true = ([1, 2, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_0222222 : fieldCube 7 5 20 [1, 2, 1, 2, 2, 0, 1] = [0, 0, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_0222222 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 2, 1] [0, 2, 2, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222222 : mirrorTrits [0, 0, 1, 2, 1, 2, 1] = [0, 0, 2, 1, 2, 1, 2] := by
  decide

theorem demoInv_0222222 : specInv 7 5 20 [0, 2, 2, 2, 2, 2, 2] = some [0, 0, 2, 1, 2, 1, 2] :=
  specInv_mirror_7 [0, 2, 2, 2, 2, 2, 2] [1, 2, 1, 1, 0, 2, 0] [1, 2, 1, 2, 2, 0, 1] [0, 0, 1, 2, 1, 2, 1] [0, 0, 2, 1, 2, 1, 2] demoR1_0222222 demoR2_0222222 demoC_0222222 demoM_0222222 demoMir_0222222

theorem demoR1_1222222 : invRung 7 5 20 [1, 2, 2, 2, 2, 2, 2] [1, 2, 2, 2, 2, 2, 2] 1 2 false = ([2, 1, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_1222222 : invRung 7 5 20 [1, 2, 2, 2, 2, 2, 2] [2, 1, 1, 0, 0, 0, 1] 3 1 true = ([0, 1, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_1222222 : fieldCube 7 5 20 [0, 1, 2, 2, 0, 0, 0] = [2, 0, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_1222222 : fieldMul 7 5 20 [2, 0, 2, 1, 0, 2, 2] [1, 2, 2, 2, 2, 2, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1222222 : specInv 7 5 20 [1, 2, 2, 2, 2, 2, 2] = some [2, 0, 2, 1, 0, 2, 2] :=
  specInv_white_7 [1, 2, 2, 2, 2, 2, 2] [2, 1, 1, 0, 0, 0, 1] [0, 1, 2, 2, 0, 0, 0] [2, 0, 2, 1, 0, 2, 2] demoR1_1222222 demoR2_1222222 demoC_1222222 demoM_1222222

theorem demoR1_2222222 : invRung 7 5 20 [2, 2, 2, 2, 2, 2, 2] [2, 2, 2, 2, 2, 2, 2] 1 2 false = ([2, 0, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_2222222 : invRung 7 5 20 [2, 2, 2, 2, 2, 2, 2] [2, 0, 2, 1, 0, 2, 0] 3 1 true = ([1, 1, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_2222222 : fieldCube 7 5 20 [1, 1, 2, 1, 2, 2, 1] = [1, 2, 2, 1, 0, 0, 0] := by
  decide

theorem demoM_2222222 : fieldMul 7 5 20 [1, 2, 2, 1, 0, 0, 0] [2, 2, 2, 2, 2, 2, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222222 : mirrorTrits [1, 2, 2, 1, 0, 0, 0] = [2, 1, 1, 2, 0, 0, 0] := by
  decide

theorem demoInv_2222222 : specInv 7 5 20 [2, 2, 2, 2, 2, 2, 2] = some [2, 1, 1, 2, 0, 0, 0] :=
  specInv_mirror_7 [2, 2, 2, 2, 2, 2, 2] [2, 0, 2, 1, 0, 2, 0] [1, 1, 2, 1, 2, 2, 1] [1, 2, 2, 1, 0, 0, 0] [2, 1, 1, 2, 0, 0, 0] demoR1_2222222 demoR2_2222222 demoC_2222222 demoM_2222222 demoMir_2222222

end EcbsLink2.Link2
