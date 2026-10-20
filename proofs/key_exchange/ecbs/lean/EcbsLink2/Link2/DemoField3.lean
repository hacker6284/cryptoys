/-
  One quarter of Demo's nonzero trit lists. Each kernel `decide` is one rung,
  one cube, or one multiply.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldOk

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem demoR1_2111111 : invRung 7 5 20 [2, 1, 1, 1, 1, 1, 1] [2, 1, 1, 1, 1, 1, 1] 1 2 false = ([1, 2, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_2111111 : invRung 7 5 20 [2, 1, 1, 1, 1, 1, 1] [1, 2, 2, 0, 0, 0, 2] 3 1 true = ([0, 1, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_2111111 : fieldCube 7 5 20 [0, 1, 2, 2, 0, 0, 0] = [2, 0, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_2111111 : fieldMul 7 5 20 [2, 0, 2, 1, 0, 2, 2] [2, 1, 1, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2111111 : mirrorTrits [2, 0, 2, 1, 0, 2, 2] = [1, 0, 1, 2, 0, 1, 1] := by
  decide

theorem demoInv_2111111 : specInv 7 5 20 [2, 1, 1, 1, 1, 1, 1] = some [1, 0, 1, 2, 0, 1, 1] :=
  specInv_mirror_7 [2, 1, 1, 1, 1, 1, 1] [1, 2, 2, 0, 0, 0, 2] [0, 1, 2, 2, 0, 0, 0] [2, 0, 2, 1, 0, 2, 2] [1, 0, 1, 2, 0, 1, 1] demoR1_2111111 demoR2_2111111 demoC_2111111 demoM_2111111 demoMir_2111111

theorem demoR1_0211111 : invRung 7 5 20 [0, 2, 1, 1, 1, 1, 1] [0, 2, 1, 1, 1, 1, 1] 1 2 false = ([2, 0, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_0211111 : invRung 7 5 20 [0, 2, 1, 1, 1, 1, 1] [2, 0, 0, 0, 1, 1, 2] 3 1 true = ([1, 0, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_0211111 : fieldCube 7 5 20 [1, 0, 2, 0, 0, 1, 0] = [2, 1, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_0211111 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 1, 1] [0, 2, 1, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211111 : mirrorTrits [2, 1, 1, 0, 1, 1, 1] = [1, 2, 2, 0, 2, 2, 2] := by
  decide

theorem demoInv_0211111 : specInv 7 5 20 [0, 2, 1, 1, 1, 1, 1] = some [1, 2, 2, 0, 2, 2, 2] :=
  specInv_mirror_7 [0, 2, 1, 1, 1, 1, 1] [2, 0, 0, 0, 1, 1, 2] [1, 0, 2, 0, 0, 1, 0] [2, 1, 1, 0, 1, 1, 1] [1, 2, 2, 0, 2, 2, 2] demoR1_0211111 demoR2_0211111 demoC_0211111 demoM_0211111 demoMir_0211111

theorem demoR1_1211111 : invRung 7 5 20 [1, 2, 1, 1, 1, 1, 1] [1, 2, 1, 1, 1, 1, 1] 1 2 false = ([2, 2, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1211111 : invRung 7 5 20 [1, 2, 1, 1, 1, 1, 1] [2, 2, 2, 1, 2, 2, 1] 3 1 true = ([1, 1, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_1211111 : fieldCube 7 5 20 [1, 1, 2, 1, 1, 1, 2] = [0, 1, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_1211111 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 2, 1] [1, 2, 1, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1211111 : specInv 7 5 20 [1, 2, 1, 1, 1, 1, 1] = some [0, 1, 0, 1, 0, 2, 1] :=
  specInv_white_7 [1, 2, 1, 1, 1, 1, 1] [2, 2, 2, 1, 2, 2, 1] [1, 1, 2, 1, 1, 1, 2] [0, 1, 0, 1, 0, 2, 1] demoR1_1211111 demoR2_1211111 demoC_1211111 demoM_1211111

theorem demoR1_2211111 : invRung 7 5 20 [2, 2, 1, 1, 1, 1, 1] [2, 2, 1, 1, 1, 1, 1] 1 2 false = ([2, 0, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_2211111 : invRung 7 5 20 [2, 2, 1, 1, 1, 1, 1] [2, 0, 2, 2, 0, 1, 2] 3 1 true = ([1, 0, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_2211111 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 1, 2] = [0, 1, 0, 0, 0, 2, 0] := by
  decide

theorem demoM_2211111 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 2, 0] [2, 2, 1, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2211111 : specInv 7 5 20 [2, 2, 1, 1, 1, 1, 1] = some [0, 1, 0, 0, 0, 2, 0] :=
  specInv_white_7 [2, 2, 1, 1, 1, 1, 1] [2, 0, 2, 2, 0, 1, 2] [1, 0, 1, 1, 1, 1, 2] [0, 1, 0, 0, 0, 2, 0] demoR1_2211111 demoR2_2211111 demoC_2211111 demoM_2211111

theorem demoR1_0021111 : invRung 7 5 20 [0, 0, 2, 1, 1, 1, 1] [0, 0, 2, 1, 1, 1, 1] 1 2 false = ([0, 2, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0021111 : invRung 7 5 20 [0, 0, 2, 1, 1, 1, 1] [0, 2, 1, 2, 0, 0, 0] 3 1 true = ([0, 1, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0021111 : fieldCube 7 5 20 [0, 1, 1, 1, 1, 2, 2] = [0, 2, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_0021111 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 0, 2] [0, 0, 2, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021111 : mirrorTrits [0, 2, 1, 1, 1, 0, 2] = [0, 1, 2, 2, 2, 0, 1] := by
  decide

theorem demoInv_0021111 : specInv 7 5 20 [0, 0, 2, 1, 1, 1, 1] = some [0, 1, 2, 2, 2, 0, 1] :=
  specInv_mirror_7 [0, 0, 2, 1, 1, 1, 1] [0, 2, 1, 2, 0, 0, 0] [0, 1, 1, 1, 1, 2, 2] [0, 2, 1, 1, 1, 0, 2] [0, 1, 2, 2, 2, 0, 1] demoR1_0021111 demoR2_0021111 demoC_0021111 demoM_0021111 demoMir_0021111

theorem demoR1_1021111 : invRung 7 5 20 [1, 0, 2, 1, 1, 1, 1] [1, 0, 2, 1, 1, 1, 1] 1 2 false = ([2, 1, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_1021111 : invRung 7 5 20 [1, 0, 2, 1, 1, 1, 1] [2, 1, 0, 2, 2, 2, 2] 3 1 true = ([2, 1, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_1021111 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 2, 2] = [2, 1, 1, 0, 1, 2, 1] := by
  decide

theorem demoM_1021111 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 2, 1] [1, 0, 2, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1021111 : specInv 7 5 20 [1, 0, 2, 1, 1, 1, 1] = some [2, 1, 1, 0, 1, 2, 1] :=
  specInv_white_7 [1, 0, 2, 1, 1, 1, 1] [2, 1, 0, 2, 2, 2, 2] [2, 1, 1, 1, 0, 2, 2] [2, 1, 1, 0, 1, 2, 1] demoR1_1021111 demoR2_1021111 demoC_1021111 demoM_1021111

theorem demoR1_2021111 : invRung 7 5 20 [2, 0, 2, 1, 1, 1, 1] [2, 0, 2, 1, 1, 1, 1] 1 2 false = ([0, 0, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_2021111 : invRung 7 5 20 [2, 0, 2, 1, 1, 1, 1] [0, 0, 2, 0, 0, 0, 1] 3 1 true = ([2, 2, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_2021111 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 2, 1] = [2, 2, 2, 2, 0, 0, 1] := by
  decide

theorem demoM_2021111 : fieldMul 7 5 20 [2, 2, 2, 2, 0, 0, 1] [2, 0, 2, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021111 : mirrorTrits [2, 2, 2, 2, 0, 0, 1] = [1, 1, 1, 1, 0, 0, 2] := by
  decide

theorem demoInv_2021111 : specInv 7 5 20 [2, 0, 2, 1, 1, 1, 1] = some [1, 1, 1, 1, 0, 0, 2] :=
  specInv_mirror_7 [2, 0, 2, 1, 1, 1, 1] [0, 0, 2, 0, 0, 0, 1] [2, 2, 0, 1, 2, 2, 1] [2, 2, 2, 2, 0, 0, 1] [1, 1, 1, 1, 0, 0, 2] demoR1_2021111 demoR2_2021111 demoC_2021111 demoM_2021111 demoMir_2021111

theorem demoR1_0121111 : invRung 7 5 20 [0, 1, 2, 1, 1, 1, 1] [0, 1, 2, 1, 1, 1, 1] 1 2 false = ([0, 2, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_0121111 : invRung 7 5 20 [0, 1, 2, 1, 1, 1, 1] [0, 2, 0, 1, 0, 1, 0] 3 1 true = ([0, 1, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_0121111 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 0, 2] = [0, 0, 1, 1, 2, 0, 0] := by
  decide

theorem demoM_0121111 : fieldMul 7 5 20 [0, 0, 1, 1, 2, 0, 0] [0, 1, 2, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0121111 : specInv 7 5 20 [0, 1, 2, 1, 1, 1, 1] = some [0, 0, 1, 1, 2, 0, 0] :=
  specInv_white_7 [0, 1, 2, 1, 1, 1, 1] [0, 2, 0, 1, 0, 1, 0] [0, 1, 0, 0, 1, 0, 2] [0, 0, 1, 1, 2, 0, 0] demoR1_0121111 demoR2_0121111 demoC_0121111 demoM_0121111

theorem demoR1_1121111 : invRung 7 5 20 [1, 1, 2, 1, 1, 1, 1] [1, 1, 2, 1, 1, 1, 1] 1 2 false = ([0, 2, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_1121111 : invRung 7 5 20 [1, 1, 2, 1, 1, 1, 1] [0, 2, 0, 0, 2, 0, 2] 3 1 true = ([0, 0, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1121111 : fieldCube 7 5 20 [0, 0, 1, 1, 2, 1, 0] = [2, 0, 2, 2, 1, 1, 2] := by
  decide

theorem demoM_1121111 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 1, 2] [1, 1, 2, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121111 : mirrorTrits [2, 0, 2, 2, 1, 1, 2] = [1, 0, 1, 1, 2, 2, 1] := by
  decide

theorem demoInv_1121111 : specInv 7 5 20 [1, 1, 2, 1, 1, 1, 1] = some [1, 0, 1, 1, 2, 2, 1] :=
  specInv_mirror_7 [1, 1, 2, 1, 1, 1, 1] [0, 2, 0, 0, 2, 0, 2] [0, 0, 1, 1, 2, 1, 0] [2, 0, 2, 2, 1, 1, 2] [1, 0, 1, 1, 2, 2, 1] demoR1_1121111 demoR2_1121111 demoC_1121111 demoM_1121111 demoMir_1121111

theorem demoR1_2121111 : invRung 7 5 20 [2, 1, 2, 1, 1, 1, 1] [2, 1, 2, 1, 1, 1, 1] 1 2 false = ([1, 1, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_2121111 : invRung 7 5 20 [2, 1, 2, 1, 1, 1, 1] [1, 1, 2, 2, 0, 0, 1] 3 1 true = ([1, 1, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_2121111 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 1, 2] = [2, 1, 2, 1, 0, 1, 0] := by
  decide

theorem demoM_2121111 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 1, 0] [2, 1, 2, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2121111 : specInv 7 5 20 [2, 1, 2, 1, 1, 1, 1] = some [2, 1, 2, 1, 0, 1, 0] :=
  specInv_white_7 [2, 1, 2, 1, 1, 1, 1] [1, 1, 2, 2, 0, 0, 1] [1, 1, 1, 0, 1, 1, 2] [2, 1, 2, 1, 0, 1, 0] demoR1_2121111 demoR2_2121111 demoC_2121111 demoM_2121111

theorem demoR1_0221111 : invRung 7 5 20 [0, 2, 2, 1, 1, 1, 1] [0, 2, 2, 1, 1, 1, 1] 1 2 false = ([0, 1, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_0221111 : invRung 7 5 20 [0, 2, 2, 1, 1, 1, 1] [0, 1, 1, 0, 1, 1, 0] 3 1 true = ([0, 1, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0221111 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 1, 2] = [2, 0, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_0221111 : fieldMul 7 5 20 [2, 0, 0, 0, 0, 1, 0] [0, 2, 2, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0221111 : specInv 7 5 20 [0, 2, 2, 1, 1, 1, 1] = some [2, 0, 0, 0, 0, 1, 0] :=
  specInv_white_7 [0, 2, 2, 1, 1, 1, 1] [0, 1, 1, 0, 1, 1, 0] [0, 1, 2, 1, 0, 1, 2] [2, 0, 0, 0, 0, 1, 0] demoR1_0221111 demoR2_0221111 demoC_0221111 demoM_0221111

theorem demoR1_1221111 : invRung 7 5 20 [1, 2, 2, 1, 1, 1, 1] [1, 2, 2, 1, 1, 1, 1] 1 2 false = ([1, 0, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_1221111 : invRung 7 5 20 [1, 2, 2, 1, 1, 1, 1] [1, 0, 2, 2, 2, 2, 0] 3 1 true = ([1, 1, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_1221111 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 1, 2] = [2, 0, 2, 0, 0, 0, 0] := by
  decide

theorem demoM_1221111 : fieldMul 7 5 20 [2, 0, 2, 0, 0, 0, 0] [1, 2, 2, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1221111 : specInv 7 5 20 [1, 2, 2, 1, 1, 1, 1] = some [2, 0, 2, 0, 0, 0, 0] :=
  specInv_white_7 [1, 2, 2, 1, 1, 1, 1] [1, 0, 2, 2, 2, 2, 0] [1, 1, 2, 0, 0, 1, 2] [2, 0, 2, 0, 0, 0, 0] demoR1_1221111 demoR2_1221111 demoC_1221111 demoM_1221111

theorem demoR1_2221111 : invRung 7 5 20 [2, 2, 2, 1, 1, 1, 1] [2, 2, 2, 1, 1, 1, 1] 1 2 false = ([2, 0, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2221111 : invRung 7 5 20 [2, 2, 2, 1, 1, 1, 1] [2, 0, 1, 0, 2, 0, 0] 3 1 true = ([1, 0, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_2221111 : fieldCube 7 5 20 [1, 0, 1, 2, 0, 2, 1] = [2, 0, 0, 1, 0, 2, 0] := by
  decide

theorem demoM_2221111 : fieldMul 7 5 20 [2, 0, 0, 1, 0, 2, 0] [2, 2, 2, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221111 : mirrorTrits [2, 0, 0, 1, 0, 2, 0] = [1, 0, 0, 2, 0, 1, 0] := by
  decide

theorem demoInv_2221111 : specInv 7 5 20 [2, 2, 2, 1, 1, 1, 1] = some [1, 0, 0, 2, 0, 1, 0] :=
  specInv_mirror_7 [2, 2, 2, 1, 1, 1, 1] [2, 0, 1, 0, 2, 0, 0] [1, 0, 1, 2, 0, 2, 1] [2, 0, 0, 1, 0, 2, 0] [1, 0, 0, 2, 0, 1, 0] demoR1_2221111 demoR2_2221111 demoC_2221111 demoM_2221111 demoMir_2221111

theorem demoR1_0002111 : invRung 7 5 20 [0, 0, 0, 2, 1, 1, 1] [0, 0, 0, 2, 1, 1, 1] 1 2 false = ([0, 0, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_0002111 : invRung 7 5 20 [0, 0, 0, 2, 1, 1, 1] [0, 0, 2, 1, 1, 0, 2] 3 1 true = ([0, 2, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0002111 : fieldCube 7 5 20 [0, 2, 2, 0, 0, 2, 1] = [2, 0, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_0002111 : fieldMul 7 5 20 [2, 0, 1, 0, 0, 0, 1] [0, 0, 0, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0002111 : specInv 7 5 20 [0, 0, 0, 2, 1, 1, 1] = some [2, 0, 1, 0, 0, 0, 1] :=
  specInv_white_7 [0, 0, 0, 2, 1, 1, 1] [0, 0, 2, 1, 1, 0, 2] [0, 2, 2, 0, 0, 2, 1] [2, 0, 1, 0, 0, 0, 1] demoR1_0002111 demoR2_0002111 demoC_0002111 demoM_0002111

theorem demoR1_1002111 : invRung 7 5 20 [1, 0, 0, 2, 1, 1, 1] [1, 0, 0, 2, 1, 1, 1] 1 2 false = ([2, 1, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_1002111 : invRung 7 5 20 [1, 0, 0, 2, 1, 1, 1] [2, 1, 1, 1, 2, 0, 2] 3 1 true = ([0, 2, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_1002111 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 1, 2] = [1, 1, 2, 2, 0, 1, 2] := by
  decide

theorem demoM_1002111 : fieldMul 7 5 20 [1, 1, 2, 2, 0, 1, 2] [1, 0, 0, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1002111 : specInv 7 5 20 [1, 0, 0, 2, 1, 1, 1] = some [1, 1, 2, 2, 0, 1, 2] :=
  specInv_white_7 [1, 0, 0, 2, 1, 1, 1] [2, 1, 1, 1, 2, 0, 2] [0, 2, 0, 0, 1, 1, 2] [1, 1, 2, 2, 0, 1, 2] demoR1_1002111 demoR2_1002111 demoC_1002111 demoM_1002111

theorem demoR1_2002111 : invRung 7 5 20 [2, 0, 0, 2, 1, 1, 1] [2, 0, 0, 2, 1, 1, 1] 1 2 false = ([0, 0, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_2002111 : invRung 7 5 20 [2, 0, 0, 2, 1, 1, 1] [0, 0, 1, 0, 0, 2, 0] 3 1 true = ([0, 1, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2002111 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 1, 0] = [1, 1, 1, 1, 1, 1, 0] := by
  decide

theorem demoM_2002111 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 1, 0] [2, 0, 0, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002111 : mirrorTrits [1, 1, 1, 1, 1, 1, 0] = [2, 2, 2, 2, 2, 2, 0] := by
  decide

theorem demoInv_2002111 : specInv 7 5 20 [2, 0, 0, 2, 1, 1, 1] = some [2, 2, 2, 2, 2, 2, 0] :=
  specInv_mirror_7 [2, 0, 0, 2, 1, 1, 1] [0, 0, 1, 0, 0, 2, 0] [0, 1, 1, 0, 0, 1, 0] [1, 1, 1, 1, 1, 1, 0] [2, 2, 2, 2, 2, 2, 0] demoR1_2002111 demoR2_2002111 demoC_2002111 demoM_2002111 demoMir_2002111

theorem demoR1_0102111 : invRung 7 5 20 [0, 1, 0, 2, 1, 1, 1] [0, 1, 0, 2, 1, 1, 1] 1 2 false = ([1, 2, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_0102111 : invRung 7 5 20 [0, 1, 0, 2, 1, 1, 1] [1, 2, 2, 1, 1, 1, 1] 3 1 true = ([2, 1, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_0102111 : fieldCube 7 5 20 [2, 1, 0, 2, 0, 2, 1] = [0, 0, 0, 2, 0, 2, 2] := by
  decide

theorem demoM_0102111 : fieldMul 7 5 20 [0, 0, 0, 2, 0, 2, 2] [0, 1, 0, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0102111 : specInv 7 5 20 [0, 1, 0, 2, 1, 1, 1] = some [0, 0, 0, 2, 0, 2, 2] :=
  specInv_white_7 [0, 1, 0, 2, 1, 1, 1] [1, 2, 2, 1, 1, 1, 1] [2, 1, 0, 2, 0, 2, 1] [0, 0, 0, 2, 0, 2, 2] demoR1_0102111 demoR2_0102111 demoC_0102111 demoM_0102111

theorem demoR1_1102111 : invRung 7 5 20 [1, 1, 0, 2, 1, 1, 1] [1, 1, 0, 2, 1, 1, 1] 1 2 false = ([2, 0, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1102111 : invRung 7 5 20 [1, 1, 0, 2, 1, 1, 1] [2, 0, 0, 2, 2, 1, 0] 3 1 true = ([0, 1, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_1102111 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 0, 1] = [2, 2, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_1102111 : fieldMul 7 5 20 [2, 2, 1, 0, 1, 1, 1] [1, 1, 0, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102111 : mirrorTrits [2, 2, 1, 0, 1, 1, 1] = [1, 1, 2, 0, 2, 2, 2] := by
  decide

theorem demoInv_1102111 : specInv 7 5 20 [1, 1, 0, 2, 1, 1, 1] = some [1, 1, 2, 0, 2, 2, 2] :=
  specInv_mirror_7 [1, 1, 0, 2, 1, 1, 1] [2, 0, 0, 2, 2, 1, 0] [0, 1, 2, 2, 1, 0, 1] [2, 2, 1, 0, 1, 1, 1] [1, 1, 2, 0, 2, 2, 2] demoR1_1102111 demoR2_1102111 demoC_1102111 demoM_1102111 demoMir_1102111

theorem demoR1_2102111 : invRung 7 5 20 [2, 1, 0, 2, 1, 1, 1] [2, 1, 0, 2, 1, 1, 1] 1 2 false = ([1, 1, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_2102111 : invRung 7 5 20 [2, 1, 0, 2, 1, 1, 1] [1, 1, 1, 1, 0, 2, 0] 3 1 true = ([2, 2, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2102111 : fieldCube 7 5 20 [2, 2, 1, 0, 1, 1, 0] = [0, 2, 1, 0, 1, 2, 1] := by
  decide

theorem demoM_2102111 : fieldMul 7 5 20 [0, 2, 1, 0, 1, 2, 1] [2, 1, 0, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2102111 : mirrorTrits [0, 2, 1, 0, 1, 2, 1] = [0, 1, 2, 0, 2, 1, 2] := by
  decide

theorem demoInv_2102111 : specInv 7 5 20 [2, 1, 0, 2, 1, 1, 1] = some [0, 1, 2, 0, 2, 1, 2] :=
  specInv_mirror_7 [2, 1, 0, 2, 1, 1, 1] [1, 1, 1, 1, 0, 2, 0] [2, 2, 1, 0, 1, 1, 0] [0, 2, 1, 0, 1, 2, 1] [0, 1, 2, 0, 2, 1, 2] demoR1_2102111 demoR2_2102111 demoC_2102111 demoM_2102111 demoMir_2102111

theorem demoR1_0202111 : invRung 7 5 20 [0, 2, 0, 2, 1, 1, 1] [0, 2, 0, 2, 1, 1, 1] 1 2 false = ([0, 0, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_0202111 : invRung 7 5 20 [0, 2, 0, 2, 1, 1, 1] [0, 0, 2, 2, 1, 0, 1] 3 1 true = ([1, 0, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0202111 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 0, 1] = [2, 0, 0, 0, 1, 1, 0] := by
  decide

theorem demoM_0202111 : fieldMul 7 5 20 [2, 0, 0, 0, 1, 1, 0] [0, 2, 0, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202111 : mirrorTrits [2, 0, 0, 0, 1, 1, 0] = [1, 0, 0, 0, 2, 2, 0] := by
  decide

theorem demoInv_0202111 : specInv 7 5 20 [0, 2, 0, 2, 1, 1, 1] = some [1, 0, 0, 0, 2, 2, 0] :=
  specInv_mirror_7 [0, 2, 0, 2, 1, 1, 1] [0, 0, 2, 2, 1, 0, 1] [1, 0, 0, 1, 2, 0, 1] [2, 0, 0, 0, 1, 1, 0] [1, 0, 0, 0, 2, 2, 0] demoR1_0202111 demoR2_0202111 demoC_0202111 demoM_0202111 demoMir_0202111

theorem demoR1_1202111 : invRung 7 5 20 [1, 2, 0, 2, 1, 1, 1] [1, 2, 0, 2, 1, 1, 1] 1 2 false = ([0, 2, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_1202111 : invRung 7 5 20 [1, 2, 0, 2, 1, 1, 1] [0, 2, 2, 2, 1, 2, 0] 3 1 true = ([2, 2, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_1202111 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 2, 0] = [1, 1, 2, 1, 2, 1, 1] := by
  decide

theorem demoM_1202111 : fieldMul 7 5 20 [1, 1, 2, 1, 2, 1, 1] [1, 2, 0, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1202111 : specInv 7 5 20 [1, 2, 0, 2, 1, 1, 1] = some [1, 1, 2, 1, 2, 1, 1] :=
  specInv_white_7 [1, 2, 0, 2, 1, 1, 1] [0, 2, 2, 2, 1, 2, 0] [2, 2, 1, 0, 2, 2, 0] [1, 1, 2, 1, 2, 1, 1] demoR1_1202111 demoR2_1202111 demoC_1202111 demoM_1202111

theorem demoR1_2202111 : invRung 7 5 20 [2, 2, 0, 2, 1, 1, 1] [2, 2, 0, 2, 1, 1, 1] 1 2 false = ([0, 0, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_2202111 : invRung 7 5 20 [2, 2, 0, 2, 1, 1, 1] [0, 0, 1, 2, 1, 1, 0] 3 1 true = ([2, 2, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_2202111 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 0, 0] = [1, 1, 2, 0, 0, 0, 0] := by
  decide

theorem demoM_2202111 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 0, 0] [2, 2, 0, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202111 : mirrorTrits [1, 1, 2, 0, 0, 0, 0] = [2, 2, 1, 0, 0, 0, 0] := by
  decide

theorem demoInv_2202111 : specInv 7 5 20 [2, 2, 0, 2, 1, 1, 1] = some [2, 2, 1, 0, 0, 0, 0] :=
  specInv_mirror_7 [2, 2, 0, 2, 1, 1, 1] [0, 0, 1, 2, 1, 1, 0] [2, 2, 2, 2, 1, 0, 0] [1, 1, 2, 0, 0, 0, 0] [2, 2, 1, 0, 0, 0, 0] demoR1_2202111 demoR2_2202111 demoC_2202111 demoM_2202111 demoMir_2202111

theorem demoR1_0012111 : invRung 7 5 20 [0, 0, 1, 2, 1, 1, 1] [0, 0, 1, 2, 1, 1, 1] 1 2 false = ([0, 0, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0012111 : invRung 7 5 20 [0, 0, 1, 2, 1, 1, 1] [0, 0, 2, 0, 1, 2, 1] 3 1 true = ([1, 0, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_0012111 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 0, 2] = [2, 0, 2, 0, 2, 1, 1] := by
  decide

theorem demoM_0012111 : fieldMul 7 5 20 [2, 0, 2, 0, 2, 1, 1] [0, 0, 1, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0012111 : mirrorTrits [2, 0, 2, 0, 2, 1, 1] = [1, 0, 1, 0, 1, 2, 2] := by
  decide

theorem demoInv_0012111 : specInv 7 5 20 [0, 0, 1, 2, 1, 1, 1] = some [1, 0, 1, 0, 1, 2, 2] :=
  specInv_mirror_7 [0, 0, 1, 2, 1, 1, 1] [0, 0, 2, 0, 1, 2, 1] [1, 0, 1, 1, 1, 0, 2] [2, 0, 2, 0, 2, 1, 1] [1, 0, 1, 0, 1, 2, 2] demoR1_0012111 demoR2_0012111 demoC_0012111 demoM_0012111 demoMir_0012111

theorem demoR1_1012111 : invRung 7 5 20 [1, 0, 1, 2, 1, 1, 1] [1, 0, 1, 2, 1, 1, 1] 1 2 false = ([1, 1, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1012111 : invRung 7 5 20 [1, 0, 1, 2, 1, 1, 1] [1, 1, 1, 2, 2, 1, 0] 3 1 true = ([2, 1, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_1012111 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 2, 1] = [0, 2, 0, 1, 0, 1, 1] := by
  decide

theorem demoM_1012111 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 1, 1] [1, 0, 1, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1012111 : specInv 7 5 20 [1, 0, 1, 2, 1, 1, 1] = some [0, 2, 0, 1, 0, 1, 1] :=
  specInv_white_7 [1, 0, 1, 2, 1, 1, 1] [1, 1, 1, 2, 2, 1, 0] [2, 1, 0, 2, 2, 2, 1] [0, 2, 0, 1, 0, 1, 1] demoR1_1012111 demoR2_1012111 demoC_1012111 demoM_1012111

theorem demoR1_2012111 : invRung 7 5 20 [2, 0, 1, 2, 1, 1, 1] [2, 0, 1, 2, 1, 1, 1] 1 2 false = ([1, 2, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_2012111 : invRung 7 5 20 [2, 0, 1, 2, 1, 1, 1] [1, 2, 1, 2, 2, 1, 1] 3 1 true = ([0, 0, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_2012111 : fieldCube 7 5 20 [0, 0, 1, 2, 0, 0, 1] = [2, 1, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_2012111 : fieldMul 7 5 20 [2, 1, 1, 1, 1, 0, 2] [2, 0, 1, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012111 : mirrorTrits [2, 1, 1, 1, 1, 0, 2] = [1, 2, 2, 2, 2, 0, 1] := by
  decide

theorem demoInv_2012111 : specInv 7 5 20 [2, 0, 1, 2, 1, 1, 1] = some [1, 2, 2, 2, 2, 0, 1] :=
  specInv_mirror_7 [2, 0, 1, 2, 1, 1, 1] [1, 2, 1, 2, 2, 1, 1] [0, 0, 1, 2, 0, 0, 1] [2, 1, 1, 1, 1, 0, 2] [1, 2, 2, 2, 2, 0, 1] demoR1_2012111 demoR2_2012111 demoC_2012111 demoM_2012111 demoMir_2012111

theorem demoR1_0112111 : invRung 7 5 20 [0, 1, 1, 2, 1, 1, 1] [0, 1, 1, 2, 1, 1, 1] 1 2 false = ([1, 0, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_0112111 : invRung 7 5 20 [0, 1, 1, 2, 1, 1, 1] [1, 0, 1, 0, 1, 2, 2] 3 1 true = ([2, 0, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0112111 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 1, 1] = [2, 2, 2, 1, 2, 1, 2] := by
  decide

theorem demoM_0112111 : fieldMul 7 5 20 [2, 2, 2, 1, 2, 1, 2] [0, 1, 1, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112111 : mirrorTrits [2, 2, 2, 1, 2, 1, 2] = [1, 1, 1, 2, 1, 2, 1] := by
  decide

theorem demoInv_0112111 : specInv 7 5 20 [0, 1, 1, 2, 1, 1, 1] = some [1, 1, 1, 2, 1, 2, 1] :=
  specInv_mirror_7 [0, 1, 1, 2, 1, 1, 1] [1, 0, 1, 0, 1, 2, 2] [2, 0, 2, 2, 0, 1, 1] [2, 2, 2, 1, 2, 1, 2] [1, 1, 1, 2, 1, 2, 1] demoR1_0112111 demoR2_0112111 demoC_0112111 demoM_0112111 demoMir_0112111

theorem demoR1_1112111 : invRung 7 5 20 [1, 1, 1, 2, 1, 1, 1] [1, 1, 1, 2, 1, 1, 1] 1 2 false = ([1, 0, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_1112111 : invRung 7 5 20 [1, 1, 1, 2, 1, 1, 1] [1, 0, 0, 2, 0, 2, 2] 3 1 true = ([0, 0, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_1112111 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 1, 1] = [1, 1, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_1112111 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 1, 0] [1, 1, 1, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112111 : mirrorTrits [1, 1, 0, 0, 2, 1, 0] = [2, 2, 0, 0, 1, 2, 0] := by
  decide

theorem demoInv_1112111 : specInv 7 5 20 [1, 1, 1, 2, 1, 1, 1] = some [2, 2, 0, 0, 1, 2, 0] :=
  specInv_mirror_7 [1, 1, 1, 2, 1, 1, 1] [1, 0, 0, 2, 0, 2, 2] [0, 0, 1, 0, 2, 1, 1] [1, 1, 0, 0, 2, 1, 0] [2, 2, 0, 0, 1, 2, 0] demoR1_1112111 demoR2_1112111 demoC_1112111 demoM_1112111 demoMir_1112111

theorem demoR1_2112111 : invRung 7 5 20 [2, 1, 1, 2, 1, 1, 1] [2, 1, 1, 2, 1, 1, 1] 1 2 false = ([2, 2, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_2112111 : invRung 7 5 20 [2, 1, 1, 2, 1, 1, 1] [2, 2, 2, 1, 1, 2, 1] 3 1 true = ([0, 0, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_2112111 : fieldCube 7 5 20 [0, 0, 1, 1, 1, 0, 1] = [1, 2, 0, 2, 1, 0, 0] := by
  decide

theorem demoM_2112111 : fieldMul 7 5 20 [1, 2, 0, 2, 1, 0, 0] [2, 1, 1, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112111 : mirrorTrits [1, 2, 0, 2, 1, 0, 0] = [2, 1, 0, 1, 2, 0, 0] := by
  decide

theorem demoInv_2112111 : specInv 7 5 20 [2, 1, 1, 2, 1, 1, 1] = some [2, 1, 0, 1, 2, 0, 0] :=
  specInv_mirror_7 [2, 1, 1, 2, 1, 1, 1] [2, 2, 2, 1, 1, 2, 1] [0, 0, 1, 1, 1, 0, 1] [1, 2, 0, 2, 1, 0, 0] [2, 1, 0, 1, 2, 0, 0] demoR1_2112111 demoR2_2112111 demoC_2112111 demoM_2112111 demoMir_2112111

theorem demoR1_0212111 : invRung 7 5 20 [0, 2, 1, 2, 1, 1, 1] [0, 2, 1, 2, 1, 1, 1] 1 2 false = ([1, 1, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_0212111 : invRung 7 5 20 [0, 2, 1, 2, 1, 1, 1] [1, 1, 1, 1, 1, 1, 1] 3 1 true = ([0, 2, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0212111 : fieldCube 7 5 20 [0, 2, 1, 0, 2, 1, 0] = [1, 0, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_0212111 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 0, 2] [0, 2, 1, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0212111 : specInv 7 5 20 [0, 2, 1, 2, 1, 1, 1] = some [1, 0, 1, 1, 1, 0, 2] :=
  specInv_white_7 [0, 2, 1, 2, 1, 1, 1] [1, 1, 1, 1, 1, 1, 1] [0, 2, 1, 0, 2, 1, 0] [1, 0, 1, 1, 1, 0, 2] demoR1_0212111 demoR2_0212111 demoC_0212111 demoM_0212111

theorem demoR1_1212111 : invRung 7 5 20 [1, 2, 1, 2, 1, 1, 1] [1, 2, 1, 2, 1, 1, 1] 1 2 false = ([0, 1, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_1212111 : invRung 7 5 20 [1, 2, 1, 2, 1, 1, 1] [0, 1, 0, 1, 0, 1, 0] 3 1 true = ([1, 1, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_1212111 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 2, 1] = [0, 0, 1, 2, 0, 0, 1] := by
  decide

theorem demoM_1212111 : fieldMul 7 5 20 [0, 0, 1, 2, 0, 0, 1] [1, 2, 1, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1212111 : specInv 7 5 20 [1, 2, 1, 2, 1, 1, 1] = some [0, 0, 1, 2, 0, 0, 1] :=
  specInv_white_7 [1, 2, 1, 2, 1, 1, 1] [0, 1, 0, 1, 0, 1, 0] [1, 1, 2, 0, 0, 2, 1] [0, 0, 1, 2, 0, 0, 1] demoR1_1212111 demoR2_1212111 demoC_1212111 demoM_1212111

theorem demoR1_2212111 : invRung 7 5 20 [2, 2, 1, 2, 1, 1, 1] [2, 2, 1, 2, 1, 1, 1] 1 2 false = ([2, 2, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_2212111 : invRung 7 5 20 [2, 2, 1, 2, 1, 1, 1] [2, 2, 1, 0, 1, 0, 1] 3 1 true = ([2, 0, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2212111 : fieldCube 7 5 20 [2, 0, 1, 1, 2, 2, 0] = [2, 1, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_2212111 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 2, 1] [2, 2, 1, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212111 : mirrorTrits [2, 1, 0, 2, 2, 2, 1] = [1, 2, 0, 1, 1, 1, 2] := by
  decide

theorem demoInv_2212111 : specInv 7 5 20 [2, 2, 1, 2, 1, 1, 1] = some [1, 2, 0, 1, 1, 1, 2] :=
  specInv_mirror_7 [2, 2, 1, 2, 1, 1, 1] [2, 2, 1, 0, 1, 0, 1] [2, 0, 1, 1, 2, 2, 0] [2, 1, 0, 2, 2, 2, 1] [1, 2, 0, 1, 1, 1, 2] demoR1_2212111 demoR2_2212111 demoC_2212111 demoM_2212111 demoMir_2212111

theorem demoR1_0022111 : invRung 7 5 20 [0, 0, 2, 2, 1, 1, 1] [0, 0, 2, 2, 1, 1, 1] 1 2 false = ([0, 1, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_0022111 : invRung 7 5 20 [0, 0, 2, 2, 1, 1, 1] [0, 1, 0, 0, 1, 2, 2] 3 1 true = ([2, 1, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0022111 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 1, 1] = [1, 2, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_0022111 : fieldMul 7 5 20 [1, 2, 1, 2, 2, 0, 2] [0, 0, 2, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0022111 : specInv 7 5 20 [0, 0, 2, 2, 1, 1, 1] = some [1, 2, 1, 2, 2, 0, 2] :=
  specInv_white_7 [0, 0, 2, 2, 1, 1, 1] [0, 1, 0, 0, 1, 2, 2] [2, 1, 2, 1, 0, 1, 1] [1, 2, 1, 2, 2, 0, 2] demoR1_0022111 demoR2_0022111 demoC_0022111 demoM_0022111

theorem demoR1_1022111 : invRung 7 5 20 [1, 0, 2, 2, 1, 1, 1] [1, 0, 2, 2, 1, 1, 1] 1 2 false = ([2, 2, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_1022111 : invRung 7 5 20 [1, 0, 2, 2, 1, 1, 1] [2, 2, 0, 1, 2, 0, 2] 3 1 true = ([0, 0, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_1022111 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 2, 2] = [2, 0, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_1022111 : fieldMul 7 5 20 [2, 0, 0, 1, 1, 0, 0] [1, 0, 2, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1022111 : specInv 7 5 20 [1, 0, 2, 2, 1, 1, 1] = some [2, 0, 0, 1, 1, 0, 0] :=
  specInv_white_7 [1, 0, 2, 2, 1, 1, 1] [2, 2, 0, 1, 2, 0, 2] [0, 0, 1, 0, 2, 2, 2] [2, 0, 0, 1, 1, 0, 0] demoR1_1022111 demoR2_1022111 demoC_1022111 demoM_1022111

theorem demoR1_2022111 : invRung 7 5 20 [2, 0, 2, 2, 1, 1, 1] [2, 0, 2, 2, 1, 1, 1] 1 2 false = ([0, 2, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2022111 : invRung 7 5 20 [2, 0, 2, 2, 1, 1, 1] [0, 2, 1, 2, 1, 1, 2] 3 1 true = ([2, 1, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_2022111 : fieldCube 7 5 20 [2, 1, 1, 0, 0, 2, 1] = [1, 0, 1, 2, 0, 0, 0] := by
  decide

theorem demoM_2022111 : fieldMul 7 5 20 [1, 0, 1, 2, 0, 0, 0] [2, 0, 2, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2022111 : specInv 7 5 20 [2, 0, 2, 2, 1, 1, 1] = some [1, 0, 1, 2, 0, 0, 0] :=
  specInv_white_7 [2, 0, 2, 2, 1, 1, 1] [0, 2, 1, 2, 1, 1, 2] [2, 1, 1, 0, 0, 2, 1] [1, 0, 1, 2, 0, 0, 0] demoR1_2022111 demoR2_2022111 demoC_2022111 demoM_2022111

theorem demoR1_0122111 : invRung 7 5 20 [0, 1, 2, 2, 1, 1, 1] [0, 1, 2, 2, 1, 1, 1] 1 2 false = ([1, 1, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_0122111 : invRung 7 5 20 [0, 1, 2, 2, 1, 1, 1] [1, 1, 0, 2, 0, 0, 1] 3 1 true = ([0, 0, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0122111 : fieldCube 7 5 20 [0, 0, 1, 0, 1, 0, 1] = [0, 2, 2, 2, 1, 2, 0] := by
  decide

theorem demoM_0122111 : fieldMul 7 5 20 [0, 2, 2, 2, 1, 2, 0] [0, 1, 2, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0122111 : specInv 7 5 20 [0, 1, 2, 2, 1, 1, 1] = some [0, 2, 2, 2, 1, 2, 0] :=
  specInv_white_7 [0, 1, 2, 2, 1, 1, 1] [1, 1, 0, 2, 0, 0, 1] [0, 0, 1, 0, 1, 0, 1] [0, 2, 2, 2, 1, 2, 0] demoR1_0122111 demoR2_0122111 demoC_0122111 demoM_0122111

theorem demoR1_1122111 : invRung 7 5 20 [1, 1, 2, 2, 1, 1, 1] [1, 1, 2, 2, 1, 1, 1] 1 2 false = ([2, 0, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1122111 : invRung 7 5 20 [1, 1, 2, 2, 1, 1, 1] [2, 0, 1, 2, 0, 0, 1] 3 1 true = ([1, 2, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_1122111 : fieldCube 7 5 20 [1, 2, 1, 0, 0, 0, 2] = [1, 2, 1, 1, 2, 2, 0] := by
  decide

theorem demoM_1122111 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 2, 0] [1, 1, 2, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122111 : mirrorTrits [1, 2, 1, 1, 2, 2, 0] = [2, 1, 2, 2, 1, 1, 0] := by
  decide

theorem demoInv_1122111 : specInv 7 5 20 [1, 1, 2, 2, 1, 1, 1] = some [2, 1, 2, 2, 1, 1, 0] :=
  specInv_mirror_7 [1, 1, 2, 2, 1, 1, 1] [2, 0, 1, 2, 0, 0, 1] [1, 2, 1, 0, 0, 0, 2] [1, 2, 1, 1, 2, 2, 0] [2, 1, 2, 2, 1, 1, 0] demoR1_1122111 demoR2_1122111 demoC_1122111 demoM_1122111 demoMir_1122111

theorem demoR1_2122111 : invRung 7 5 20 [2, 1, 2, 2, 1, 1, 1] [2, 1, 2, 2, 1, 1, 1] 1 2 false = ([1, 0, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_2122111 : invRung 7 5 20 [2, 1, 2, 2, 1, 1, 1] [1, 0, 2, 1, 1, 2, 1] 3 1 true = ([0, 0, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2122111 : fieldCube 7 5 20 [0, 0, 1, 0, 1, 1, 1] = [1, 0, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_2122111 : fieldMul 7 5 20 [1, 0, 0, 2, 2, 0, 2] [2, 1, 2, 2, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122111 : mirrorTrits [1, 0, 0, 2, 2, 0, 2] = [2, 0, 0, 1, 1, 0, 1] := by
  decide

theorem demoInv_2122111 : specInv 7 5 20 [2, 1, 2, 2, 1, 1, 1] = some [2, 0, 0, 1, 1, 0, 1] :=
  specInv_mirror_7 [2, 1, 2, 2, 1, 1, 1] [1, 0, 2, 1, 1, 2, 1] [0, 0, 1, 0, 1, 1, 1] [1, 0, 0, 2, 2, 0, 2] [2, 0, 0, 1, 1, 0, 1] demoR1_2122111 demoR2_2122111 demoC_2122111 demoM_2122111 demoMir_2122111

theorem demoR1_0222111 : invRung 7 5 20 [0, 2, 2, 2, 1, 1, 1] [0, 2, 2, 2, 1, 1, 1] 1 2 false = ([2, 1, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_0222111 : invRung 7 5 20 [0, 2, 2, 2, 1, 1, 1] [2, 1, 2, 2, 2, 1, 1] 3 1 true = ([2, 2, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0222111 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 2, 1] = [0, 1, 0, 1, 0, 0, 2] := by
  decide

theorem demoM_0222111 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 0, 2] [0, 2, 2, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0222111 : specInv 7 5 20 [0, 2, 2, 2, 1, 1, 1] = some [0, 1, 0, 1, 0, 0, 2] :=
  specInv_white_7 [0, 2, 2, 2, 1, 1, 1] [2, 1, 2, 2, 2, 1, 1] [2, 2, 2, 2, 1, 2, 1] [0, 1, 0, 1, 0, 0, 2] demoR1_0222111 demoR2_0222111 demoC_0222111 demoM_0222111

theorem demoR1_1222111 : invRung 7 5 20 [1, 2, 2, 2, 1, 1, 1] [1, 2, 2, 2, 1, 1, 1] 1 2 false = ([2, 2, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_1222111 : invRung 7 5 20 [1, 2, 2, 2, 1, 1, 1] [2, 2, 1, 2, 0, 2, 2] 3 1 true = ([1, 1, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1222111 : fieldCube 7 5 20 [1, 1, 1, 2, 0, 1, 0] = [1, 1, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_1222111 : fieldMul 7 5 20 [1, 1, 0, 1, 1, 0, 0] [1, 2, 2, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1222111 : specInv 7 5 20 [1, 2, 2, 2, 1, 1, 1] = some [1, 1, 0, 1, 1, 0, 0] :=
  specInv_white_7 [1, 2, 2, 2, 1, 1, 1] [2, 2, 1, 2, 0, 2, 2] [1, 1, 1, 2, 0, 1, 0] [1, 1, 0, 1, 1, 0, 0] demoR1_1222111 demoR2_1222111 demoC_1222111 demoM_1222111

theorem demoR1_2222111 : invRung 7 5 20 [2, 2, 2, 2, 1, 1, 1] [2, 2, 2, 2, 1, 1, 1] 1 2 false = ([2, 0, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_2222111 : invRung 7 5 20 [2, 2, 2, 2, 1, 1, 1] [2, 0, 2, 0, 2, 1, 0] 3 1 true = ([2, 0, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_2222111 : fieldCube 7 5 20 [2, 0, 1, 0, 0, 0, 2] = [2, 2, 1, 2, 2, 2, 0] := by
  decide

theorem demoM_2222111 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 2, 0] [2, 2, 2, 2, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2222111 : specInv 7 5 20 [2, 2, 2, 2, 1, 1, 1] = some [2, 2, 1, 2, 2, 2, 0] :=
  specInv_white_7 [2, 2, 2, 2, 1, 1, 1] [2, 0, 2, 0, 2, 1, 0] [2, 0, 1, 0, 0, 0, 2] [2, 2, 1, 2, 2, 2, 0] demoR1_2222111 demoR2_2222111 demoC_2222111 demoM_2222111

theorem demoR1_0000211 : invRung 7 5 20 [0, 0, 0, 0, 2, 1, 1] [0, 0, 0, 0, 2, 1, 1] 1 2 false = ([1, 1, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_0000211 : invRung 7 5 20 [0, 0, 0, 0, 2, 1, 1] [1, 1, 0, 1, 2, 0, 0] 3 1 true = ([0, 2, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_0000211 : fieldCube 7 5 20 [0, 2, 0, 2, 2, 1, 0] = [0, 0, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_0000211 : fieldMul 7 5 20 [0, 0, 0, 1, 1, 2, 1] [0, 0, 0, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000211 : mirrorTrits [0, 0, 0, 1, 1, 2, 1] = [0, 0, 0, 2, 2, 1, 2] := by
  decide

theorem demoInv_0000211 : specInv 7 5 20 [0, 0, 0, 0, 2, 1, 1] = some [0, 0, 0, 2, 2, 1, 2] :=
  specInv_mirror_7 [0, 0, 0, 0, 2, 1, 1] [1, 1, 0, 1, 2, 0, 0] [0, 2, 0, 2, 2, 1, 0] [0, 0, 0, 1, 1, 2, 1] [0, 0, 0, 2, 2, 1, 2] demoR1_0000211 demoR2_0000211 demoC_0000211 demoM_0000211 demoMir_0000211

theorem demoR1_1000211 : invRung 7 5 20 [1, 0, 0, 0, 2, 1, 1] [1, 0, 0, 0, 2, 1, 1] 1 2 false = ([2, 2, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1000211 : invRung 7 5 20 [1, 0, 0, 0, 2, 1, 1] [2, 2, 0, 2, 0, 0, 1] 3 1 true = ([2, 2, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1000211 : fieldCube 7 5 20 [2, 2, 0, 1, 1, 2, 1] = [2, 1, 2, 1, 0, 2, 0] := by
  decide

theorem demoM_1000211 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 2, 0] [1, 0, 0, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000211 : mirrorTrits [2, 1, 2, 1, 0, 2, 0] = [1, 2, 1, 2, 0, 1, 0] := by
  decide

theorem demoInv_1000211 : specInv 7 5 20 [1, 0, 0, 0, 2, 1, 1] = some [1, 2, 1, 2, 0, 1, 0] :=
  specInv_mirror_7 [1, 0, 0, 0, 2, 1, 1] [2, 2, 0, 2, 0, 0, 1] [2, 2, 0, 1, 1, 2, 1] [2, 1, 2, 1, 0, 2, 0] [1, 2, 1, 2, 0, 1, 0] demoR1_1000211 demoR2_1000211 demoC_1000211 demoM_1000211 demoMir_1000211

theorem demoR1_2000211 : invRung 7 5 20 [2, 0, 0, 0, 2, 1, 1] [2, 0, 0, 0, 2, 1, 1] 1 2 false = ([0, 0, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_2000211 : invRung 7 5 20 [2, 0, 0, 0, 2, 1, 1] [0, 0, 1, 1, 0, 2, 2] 3 1 true = ([1, 1, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_2000211 : fieldCube 7 5 20 [1, 1, 0, 2, 1, 0, 2] = [0, 0, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_2000211 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 2, 0] [2, 0, 0, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000211 : mirrorTrits [0, 0, 0, 1, 2, 2, 0] = [0, 0, 0, 2, 1, 1, 0] := by
  decide

theorem demoInv_2000211 : specInv 7 5 20 [2, 0, 0, 0, 2, 1, 1] = some [0, 0, 0, 2, 1, 1, 0] :=
  specInv_mirror_7 [2, 0, 0, 0, 2, 1, 1] [0, 0, 1, 1, 0, 2, 2] [1, 1, 0, 2, 1, 0, 2] [0, 0, 0, 1, 2, 2, 0] [0, 0, 0, 2, 1, 1, 0] demoR1_2000211 demoR2_2000211 demoC_2000211 demoM_2000211 demoMir_2000211

theorem demoR1_0100211 : invRung 7 5 20 [0, 1, 0, 0, 2, 1, 1] [0, 1, 0, 0, 2, 1, 1] 1 2 false = ([2, 0, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_0100211 : invRung 7 5 20 [0, 1, 0, 0, 2, 1, 1] [2, 0, 1, 2, 0, 2, 2] 3 1 true = ([0, 0, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0100211 : fieldCube 7 5 20 [0, 0, 2, 1, 2, 2, 2] = [0, 0, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_0100211 : fieldMul 7 5 20 [0, 0, 1, 1, 1, 1, 1] [0, 1, 0, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0100211 : specInv 7 5 20 [0, 1, 0, 0, 2, 1, 1] = some [0, 0, 1, 1, 1, 1, 1] :=
  specInv_white_7 [0, 1, 0, 0, 2, 1, 1] [2, 0, 1, 2, 0, 2, 2] [0, 0, 2, 1, 2, 2, 2] [0, 0, 1, 1, 1, 1, 1] demoR1_0100211 demoR2_0100211 demoC_0100211 demoM_0100211

theorem demoR1_1100211 : invRung 7 5 20 [1, 1, 0, 0, 2, 1, 1] [1, 1, 0, 0, 2, 1, 1] 1 2 false = ([1, 1, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_1100211 : invRung 7 5 20 [1, 1, 0, 0, 2, 1, 1] [1, 1, 2, 1, 1, 1, 2] 3 1 true = ([2, 2, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_1100211 : fieldCube 7 5 20 [2, 2, 2, 2, 2, 0, 1] = [1, 0, 1, 2, 1, 2, 2] := by
  decide

theorem demoM_1100211 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 2, 2] [1, 1, 0, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1100211 : specInv 7 5 20 [1, 1, 0, 0, 2, 1, 1] = some [1, 0, 1, 2, 1, 2, 2] :=
  specInv_white_7 [1, 1, 0, 0, 2, 1, 1] [1, 1, 2, 1, 1, 1, 2] [2, 2, 2, 2, 2, 0, 1] [1, 0, 1, 2, 1, 2, 2] demoR1_1100211 demoR2_1100211 demoC_1100211 demoM_1100211

theorem demoR1_2100211 : invRung 7 5 20 [2, 1, 0, 0, 2, 1, 1] [2, 1, 0, 0, 2, 1, 1] 1 2 false = ([2, 1, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2100211 : invRung 7 5 20 [2, 1, 0, 0, 2, 1, 1] [2, 1, 0, 0, 1, 1, 2] 3 1 true = ([2, 2, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2100211 : fieldCube 7 5 20 [2, 2, 0, 1, 0, 1, 1] = [1, 2, 1, 0, 2, 0, 0] := by
  decide

theorem demoM_2100211 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 0, 0] [2, 1, 0, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2100211 : specInv 7 5 20 [2, 1, 0, 0, 2, 1, 1] = some [1, 2, 1, 0, 2, 0, 0] :=
  specInv_white_7 [2, 1, 0, 0, 2, 1, 1] [2, 1, 0, 0, 1, 1, 2] [2, 2, 0, 1, 0, 1, 1] [1, 2, 1, 0, 2, 0, 0] demoR1_2100211 demoR2_2100211 demoC_2100211 demoM_2100211

theorem demoR1_0200211 : invRung 7 5 20 [0, 2, 0, 0, 2, 1, 1] [0, 2, 0, 0, 2, 1, 1] 1 2 false = ([1, 0, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0200211 : invRung 7 5 20 [0, 2, 0, 0, 2, 1, 1] [1, 0, 0, 0, 1, 2, 1] 3 1 true = ([2, 0, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_0200211 : fieldCube 7 5 20 [2, 0, 0, 2, 2, 1, 1] = [2, 1, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_0200211 : fieldMul 7 5 20 [2, 1, 2, 0, 2, 0, 2] [0, 2, 0, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200211 : mirrorTrits [2, 1, 2, 0, 2, 0, 2] = [1, 2, 1, 0, 1, 0, 1] := by
  decide

theorem demoInv_0200211 : specInv 7 5 20 [0, 2, 0, 0, 2, 1, 1] = some [1, 2, 1, 0, 1, 0, 1] :=
  specInv_mirror_7 [0, 2, 0, 0, 2, 1, 1] [1, 0, 0, 0, 1, 2, 1] [2, 0, 0, 2, 2, 1, 1] [2, 1, 2, 0, 2, 0, 2] [1, 2, 1, 0, 1, 0, 1] demoR1_0200211 demoR2_0200211 demoC_0200211 demoM_0200211 demoMir_0200211

theorem demoR1_1200211 : invRung 7 5 20 [1, 2, 0, 0, 2, 1, 1] [1, 2, 0, 0, 2, 1, 1] 1 2 false = ([1, 2, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1200211 : invRung 7 5 20 [1, 2, 0, 0, 2, 1, 1] [1, 2, 2, 1, 1, 2, 1] 3 1 true = ([1, 2, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_1200211 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 2, 1] = [2, 2, 0, 2, 0, 1, 0] := by
  decide

theorem demoM_1200211 : fieldMul 7 5 20 [2, 2, 0, 2, 0, 1, 0] [1, 2, 0, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1200211 : specInv 7 5 20 [1, 2, 0, 0, 2, 1, 1] = some [2, 2, 0, 2, 0, 1, 0] :=
  specInv_white_7 [1, 2, 0, 0, 2, 1, 1] [1, 2, 2, 1, 1, 2, 1] [1, 2, 2, 2, 2, 2, 1] [2, 2, 0, 2, 0, 1, 0] demoR1_1200211 demoR2_1200211 demoC_1200211 demoM_1200211

theorem demoR1_2200211 : invRung 7 5 20 [2, 2, 0, 0, 2, 1, 1] [2, 2, 0, 0, 2, 1, 1] 1 2 false = ([2, 2, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2200211 : invRung 7 5 20 [2, 2, 0, 0, 2, 1, 1] [2, 2, 0, 1, 0, 2, 1] 3 1 true = ([2, 2, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_2200211 : fieldCube 7 5 20 [2, 2, 0, 0, 0, 1, 2] = [0, 0, 2, 1, 0, 0, 1] := by
  decide

theorem demoM_2200211 : fieldMul 7 5 20 [0, 0, 2, 1, 0, 0, 1] [2, 2, 0, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200211 : mirrorTrits [0, 0, 2, 1, 0, 0, 1] = [0, 0, 1, 2, 0, 0, 2] := by
  decide

theorem demoInv_2200211 : specInv 7 5 20 [2, 2, 0, 0, 2, 1, 1] = some [0, 0, 1, 2, 0, 0, 2] :=
  specInv_mirror_7 [2, 2, 0, 0, 2, 1, 1] [2, 2, 0, 1, 0, 2, 1] [2, 2, 0, 0, 0, 1, 2] [0, 0, 2, 1, 0, 0, 1] [0, 0, 1, 2, 0, 0, 2] demoR1_2200211 demoR2_2200211 demoC_2200211 demoM_2200211 demoMir_2200211

theorem demoR1_0010211 : invRung 7 5 20 [0, 0, 1, 0, 2, 1, 1] [0, 0, 1, 0, 2, 1, 1] 1 2 false = ([2, 2, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_0010211 : invRung 7 5 20 [0, 0, 1, 0, 2, 1, 1] [2, 2, 1, 1, 2, 0, 2] 3 1 true = ([2, 2, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0010211 : fieldCube 7 5 20 [2, 2, 2, 1, 1, 0, 0] = [0, 1, 1, 0, 0, 2, 0] := by
  decide

theorem demoM_0010211 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 2, 0] [0, 0, 1, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0010211 : specInv 7 5 20 [0, 0, 1, 0, 2, 1, 1] = some [0, 1, 1, 0, 0, 2, 0] :=
  specInv_white_7 [0, 0, 1, 0, 2, 1, 1] [2, 2, 1, 1, 2, 0, 2] [2, 2, 2, 1, 1, 0, 0] [0, 1, 1, 0, 0, 2, 0] demoR1_0010211 demoR2_0010211 demoC_0010211 demoM_0010211

theorem demoR1_1010211 : invRung 7 5 20 [1, 0, 1, 0, 2, 1, 1] [1, 0, 1, 0, 2, 1, 1] 1 2 false = ([1, 0, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_1010211 : invRung 7 5 20 [1, 0, 1, 0, 2, 1, 1] [1, 0, 1, 0, 1, 1, 2] 3 1 true = ([2, 2, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_1010211 : fieldCube 7 5 20 [2, 2, 1, 2, 0, 1, 2] = [2, 0, 1, 1, 0, 2, 2] := by
  decide

theorem demoM_1010211 : fieldMul 7 5 20 [2, 0, 1, 1, 0, 2, 2] [1, 0, 1, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1010211 : specInv 7 5 20 [1, 0, 1, 0, 2, 1, 1] = some [2, 0, 1, 1, 0, 2, 2] :=
  specInv_white_7 [1, 0, 1, 0, 2, 1, 1] [1, 0, 1, 0, 1, 1, 2] [2, 2, 1, 2, 0, 1, 2] [2, 0, 1, 1, 0, 2, 2] demoR1_1010211 demoR2_1010211 demoC_1010211 demoM_1010211

theorem demoR1_2010211 : invRung 7 5 20 [2, 0, 1, 0, 2, 1, 1] [2, 0, 1, 0, 2, 1, 1] 1 2 false = ([0, 0, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_2010211 : invRung 7 5 20 [2, 0, 1, 0, 2, 1, 1] [0, 0, 2, 2, 1, 0, 0] 3 1 true = ([0, 2, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_2010211 : fieldCube 7 5 20 [0, 2, 0, 0, 2, 1, 0] = [1, 0, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_2010211 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 0, 1] [2, 0, 1, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010211 : mirrorTrits [1, 0, 1, 1, 1, 0, 1] = [2, 0, 2, 2, 2, 0, 2] := by
  decide

theorem demoInv_2010211 : specInv 7 5 20 [2, 0, 1, 0, 2, 1, 1] = some [2, 0, 2, 2, 2, 0, 2] :=
  specInv_mirror_7 [2, 0, 1, 0, 2, 1, 1] [0, 0, 2, 2, 1, 0, 0] [0, 2, 0, 0, 2, 1, 0] [1, 0, 1, 1, 1, 0, 1] [2, 0, 2, 2, 2, 0, 2] demoR1_2010211 demoR2_2010211 demoC_2010211 demoM_2010211 demoMir_2010211

theorem demoR1_0110211 : invRung 7 5 20 [0, 1, 1, 0, 2, 1, 1] [0, 1, 1, 0, 2, 1, 1] 1 2 false = ([1, 1, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_0110211 : invRung 7 5 20 [0, 1, 1, 0, 2, 1, 1] [1, 1, 1, 1, 1, 2, 0] 3 1 true = ([1, 1, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0110211 : fieldCube 7 5 20 [1, 1, 0, 2, 2, 0, 2] = [0, 1, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_0110211 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 0, 1] [0, 1, 1, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110211 : mirrorTrits [0, 1, 0, 2, 2, 0, 1] = [0, 2, 0, 1, 1, 0, 2] := by
  decide

theorem demoInv_0110211 : specInv 7 5 20 [0, 1, 1, 0, 2, 1, 1] = some [0, 2, 0, 1, 1, 0, 2] :=
  specInv_mirror_7 [0, 1, 1, 0, 2, 1, 1] [1, 1, 1, 1, 1, 2, 0] [1, 1, 0, 2, 2, 0, 2] [0, 1, 0, 2, 2, 0, 1] [0, 2, 0, 1, 1, 0, 2] demoR1_0110211 demoR2_0110211 demoC_0110211 demoM_0110211 demoMir_0110211

theorem demoR1_1110211 : invRung 7 5 20 [1, 1, 1, 0, 2, 1, 1] [1, 1, 1, 0, 2, 1, 1] 1 2 false = ([1, 1, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_1110211 : invRung 7 5 20 [1, 1, 1, 0, 2, 1, 1] [1, 1, 0, 0, 1, 0, 1] 3 1 true = ([1, 1, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_1110211 : fieldCube 7 5 20 [1, 1, 2, 1, 2, 0, 0] = [2, 2, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_1110211 : fieldMul 7 5 20 [2, 2, 1, 0, 0, 0, 1] [1, 1, 1, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1110211 : specInv 7 5 20 [1, 1, 1, 0, 2, 1, 1] = some [2, 2, 1, 0, 0, 0, 1] :=
  specInv_white_7 [1, 1, 1, 0, 2, 1, 1] [1, 1, 0, 0, 1, 0, 1] [1, 1, 2, 1, 2, 0, 0] [2, 2, 1, 0, 0, 0, 1] demoR1_1110211 demoR2_1110211 demoC_1110211 demoM_1110211

theorem demoR1_2110211 : invRung 7 5 20 [2, 1, 1, 0, 2, 1, 1] [2, 1, 1, 0, 2, 1, 1] 1 2 false = ([0, 2, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_2110211 : invRung 7 5 20 [2, 1, 1, 0, 2, 1, 1] [0, 2, 2, 1, 2, 1, 0] 3 1 true = ([1, 2, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_2110211 : fieldCube 7 5 20 [1, 2, 0, 2, 2, 1, 1] = [1, 1, 2, 2, 2, 0, 2] := by
  decide

theorem demoM_2110211 : fieldMul 7 5 20 [1, 1, 2, 2, 2, 0, 2] [2, 1, 1, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110211 : mirrorTrits [1, 1, 2, 2, 2, 0, 2] = [2, 2, 1, 1, 1, 0, 1] := by
  decide

theorem demoInv_2110211 : specInv 7 5 20 [2, 1, 1, 0, 2, 1, 1] = some [2, 2, 1, 1, 1, 0, 1] :=
  specInv_mirror_7 [2, 1, 1, 0, 2, 1, 1] [0, 2, 2, 1, 2, 1, 0] [1, 2, 0, 2, 2, 1, 1] [1, 1, 2, 2, 2, 0, 2] [2, 2, 1, 1, 1, 0, 1] demoR1_2110211 demoR2_2110211 demoC_2110211 demoM_2110211 demoMir_2110211

theorem demoR1_0210211 : invRung 7 5 20 [0, 2, 1, 0, 2, 1, 1] [0, 2, 1, 0, 2, 1, 1] 1 2 false = ([2, 0, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_0210211 : invRung 7 5 20 [0, 2, 1, 0, 2, 1, 1] [2, 0, 0, 1, 0, 0, 1] 3 1 true = ([2, 1, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0210211 : fieldCube 7 5 20 [2, 1, 1, 0, 2, 1, 0] = [0, 0, 1, 0, 1, 0, 2] := by
  decide

theorem demoM_0210211 : fieldMul 7 5 20 [0, 0, 1, 0, 1, 0, 2] [0, 2, 1, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210211 : mirrorTrits [0, 0, 1, 0, 1, 0, 2] = [0, 0, 2, 0, 2, 0, 1] := by
  decide

theorem demoInv_0210211 : specInv 7 5 20 [0, 2, 1, 0, 2, 1, 1] = some [0, 0, 2, 0, 2, 0, 1] :=
  specInv_mirror_7 [0, 2, 1, 0, 2, 1, 1] [2, 0, 0, 1, 0, 0, 1] [2, 1, 1, 0, 2, 1, 0] [0, 0, 1, 0, 1, 0, 2] [0, 0, 2, 0, 2, 0, 1] demoR1_0210211 demoR2_0210211 demoC_0210211 demoM_0210211 demoMir_0210211

theorem demoR1_1210211 : invRung 7 5 20 [1, 2, 1, 0, 2, 1, 1] [1, 2, 1, 0, 2, 1, 1] 1 2 false = ([0, 0, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1210211 : invRung 7 5 20 [1, 2, 1, 0, 2, 1, 1] [0, 0, 1, 1, 0, 0, 1] 3 1 true = ([1, 1, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_1210211 : fieldCube 7 5 20 [1, 1, 0, 2, 2, 2, 2] = [2, 0, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_1210211 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 2, 2] [1, 2, 1, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1210211 : specInv 7 5 20 [1, 2, 1, 0, 2, 1, 1] = some [2, 0, 2, 2, 1, 2, 2] :=
  specInv_white_7 [1, 2, 1, 0, 2, 1, 1] [0, 0, 1, 1, 0, 0, 1] [1, 1, 0, 2, 2, 2, 2] [2, 0, 2, 2, 1, 2, 2] demoR1_1210211 demoR2_1210211 demoC_1210211 demoM_1210211

theorem demoR1_2210211 : invRung 7 5 20 [2, 2, 1, 0, 2, 1, 1] [2, 2, 1, 0, 2, 1, 1] 1 2 false = ([2, 0, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_2210211 : invRung 7 5 20 [2, 2, 1, 0, 2, 1, 1] [2, 0, 1, 2, 1, 2, 2] 3 1 true = ([0, 0, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_2210211 : fieldCube 7 5 20 [0, 0, 0, 2, 2, 2, 2] = [1, 0, 2, 1, 1, 2, 2] := by
  decide

theorem demoM_2210211 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 2, 2] [2, 2, 1, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2210211 : specInv 7 5 20 [2, 2, 1, 0, 2, 1, 1] = some [1, 0, 2, 1, 1, 2, 2] :=
  specInv_white_7 [2, 2, 1, 0, 2, 1, 1] [2, 0, 1, 2, 1, 2, 2] [0, 0, 0, 2, 2, 2, 2] [1, 0, 2, 1, 1, 2, 2] demoR1_2210211 demoR2_2210211 demoC_2210211 demoM_2210211

theorem demoR1_0020211 : invRung 7 5 20 [0, 0, 2, 0, 2, 1, 1] [0, 0, 2, 0, 2, 1, 1] 1 2 false = ([1, 0, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_0020211 : invRung 7 5 20 [0, 0, 2, 0, 2, 1, 1] [1, 0, 1, 0, 0, 0, 1] 3 1 true = ([1, 0, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_0020211 : fieldCube 7 5 20 [1, 0, 2, 1, 0, 0, 2] = [2, 2, 2, 2, 2, 0, 1] := by
  decide

theorem demoM_0020211 : fieldMul 7 5 20 [2, 2, 2, 2, 2, 0, 1] [0, 0, 2, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0020211 : specInv 7 5 20 [0, 0, 2, 0, 2, 1, 1] = some [2, 2, 2, 2, 2, 0, 1] :=
  specInv_white_7 [0, 0, 2, 0, 2, 1, 1] [1, 0, 1, 0, 0, 0, 1] [1, 0, 2, 1, 0, 0, 2] [2, 2, 2, 2, 2, 0, 1] demoR1_0020211 demoR2_0020211 demoC_0020211 demoM_0020211

theorem demoR1_1020211 : invRung 7 5 20 [1, 0, 2, 0, 2, 1, 1] [1, 0, 2, 0, 2, 1, 1] 1 2 false = ([0, 1, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_1020211 : invRung 7 5 20 [1, 0, 2, 0, 2, 1, 1] [0, 1, 2, 0, 0, 2, 2] 3 1 true = ([1, 1, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_1020211 : fieldCube 7 5 20 [1, 1, 0, 2, 2, 2, 1] = [2, 2, 0, 1, 0, 1, 1] := by
  decide

theorem demoM_1020211 : fieldMul 7 5 20 [2, 2, 0, 1, 0, 1, 1] [1, 0, 2, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1020211 : specInv 7 5 20 [1, 0, 2, 0, 2, 1, 1] = some [2, 2, 0, 1, 0, 1, 1] :=
  specInv_white_7 [1, 0, 2, 0, 2, 1, 1] [0, 1, 2, 0, 0, 2, 2] [1, 1, 0, 2, 2, 2, 1] [2, 2, 0, 1, 0, 1, 1] demoR1_1020211 demoR2_1020211 demoC_1020211 demoM_1020211

theorem demoR1_2020211 : invRung 7 5 20 [2, 0, 2, 0, 2, 1, 1] [2, 0, 2, 0, 2, 1, 1] 1 2 false = ([2, 0, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_2020211 : invRung 7 5 20 [2, 0, 2, 0, 2, 1, 1] [2, 0, 1, 2, 0, 1, 2] 3 1 true = ([0, 2, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_2020211 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 1, 1] = [0, 0, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_2020211 : fieldMul 7 5 20 [0, 0, 2, 1, 2, 2, 2] [2, 0, 2, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2020211 : specInv 7 5 20 [2, 0, 2, 0, 2, 1, 1] = some [0, 0, 2, 1, 2, 2, 2] :=
  specInv_white_7 [2, 0, 2, 0, 2, 1, 1] [2, 0, 1, 2, 0, 1, 2] [0, 2, 1, 2, 1, 1, 1] [0, 0, 2, 1, 2, 2, 2] demoR1_2020211 demoR2_2020211 demoC_2020211 demoM_2020211

theorem demoR1_0120211 : invRung 7 5 20 [0, 1, 2, 0, 2, 1, 1] [0, 1, 2, 0, 2, 1, 1] 1 2 false = ([1, 1, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_0120211 : invRung 7 5 20 [0, 1, 2, 0, 2, 1, 1] [1, 1, 2, 1, 2, 1, 0] 3 1 true = ([2, 0, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0120211 : fieldCube 7 5 20 [2, 0, 1, 0, 2, 0, 1] = [2, 0, 2, 0, 1, 0, 1] := by
  decide

theorem demoM_0120211 : fieldMul 7 5 20 [2, 0, 2, 0, 1, 0, 1] [0, 1, 2, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0120211 : mirrorTrits [2, 0, 2, 0, 1, 0, 1] = [1, 0, 1, 0, 2, 0, 2] := by
  decide

theorem demoInv_0120211 : specInv 7 5 20 [0, 1, 2, 0, 2, 1, 1] = some [1, 0, 1, 0, 2, 0, 2] :=
  specInv_mirror_7 [0, 1, 2, 0, 2, 1, 1] [1, 1, 2, 1, 2, 1, 0] [2, 0, 1, 0, 2, 0, 1] [2, 0, 2, 0, 1, 0, 1] [1, 0, 1, 0, 2, 0, 2] demoR1_0120211 demoR2_0120211 demoC_0120211 demoM_0120211 demoMir_0120211

theorem demoR1_1120211 : invRung 7 5 20 [1, 1, 2, 0, 2, 1, 1] [1, 1, 2, 0, 2, 1, 1] 1 2 false = ([1, 0, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_1120211 : invRung 7 5 20 [1, 1, 2, 0, 2, 1, 1] [1, 0, 0, 0, 1, 1, 1] 3 1 true = ([0, 1, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_1120211 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 0, 0] = [0, 2, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_1120211 : fieldMul 7 5 20 [0, 2, 0, 0, 0, 2, 1] [1, 1, 2, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120211 : mirrorTrits [0, 2, 0, 0, 0, 2, 1] = [0, 1, 0, 0, 0, 1, 2] := by
  decide

theorem demoInv_1120211 : specInv 7 5 20 [1, 1, 2, 0, 2, 1, 1] = some [0, 1, 0, 0, 0, 1, 2] :=
  specInv_mirror_7 [1, 1, 2, 0, 2, 1, 1] [1, 0, 0, 0, 1, 1, 1] [0, 1, 2, 0, 2, 0, 0] [0, 2, 0, 0, 0, 2, 1] [0, 1, 0, 0, 0, 1, 2] demoR1_1120211 demoR2_1120211 demoC_1120211 demoM_1120211 demoMir_1120211

theorem demoR1_2120211 : invRung 7 5 20 [2, 1, 2, 0, 2, 1, 1] [2, 1, 2, 0, 2, 1, 1] 1 2 false = ([0, 2, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_2120211 : invRung 7 5 20 [2, 1, 2, 0, 2, 1, 1] [0, 2, 1, 0, 0, 0, 1] 3 1 true = ([2, 1, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_2120211 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 1, 0] = [2, 0, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_2120211 : fieldMul 7 5 20 [2, 0, 0, 0, 1, 2, 1] [2, 1, 2, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120211 : mirrorTrits [2, 0, 0, 0, 1, 2, 1] = [1, 0, 0, 0, 2, 1, 2] := by
  decide

theorem demoInv_2120211 : specInv 7 5 20 [2, 1, 2, 0, 2, 1, 1] = some [1, 0, 0, 0, 2, 1, 2] :=
  specInv_mirror_7 [2, 1, 2, 0, 2, 1, 1] [0, 2, 1, 0, 0, 0, 1] [2, 1, 0, 2, 2, 1, 0] [2, 0, 0, 0, 1, 2, 1] [1, 0, 0, 0, 2, 1, 2] demoR1_2120211 demoR2_2120211 demoC_2120211 demoM_2120211 demoMir_2120211

theorem demoR1_0220211 : invRung 7 5 20 [0, 2, 2, 0, 2, 1, 1] [0, 2, 2, 0, 2, 1, 1] 1 2 false = ([1, 1, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_0220211 : invRung 7 5 20 [0, 2, 2, 0, 2, 1, 1] [1, 1, 0, 2, 1, 2, 2] 3 1 true = ([0, 0, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_0220211 : fieldCube 7 5 20 [0, 0, 1, 2, 0, 1, 0] = [0, 1, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_0220211 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 0, 0] [0, 2, 2, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0220211 : mirrorTrits [0, 1, 0, 0, 1, 0, 0] = [0, 2, 0, 0, 2, 0, 0] := by
  decide

theorem demoInv_0220211 : specInv 7 5 20 [0, 2, 2, 0, 2, 1, 1] = some [0, 2, 0, 0, 2, 0, 0] :=
  specInv_mirror_7 [0, 2, 2, 0, 2, 1, 1] [1, 1, 0, 2, 1, 2, 2] [0, 0, 1, 2, 0, 1, 0] [0, 1, 0, 0, 1, 0, 0] [0, 2, 0, 0, 2, 0, 0] demoR1_0220211 demoR2_0220211 demoC_0220211 demoM_0220211 demoMir_0220211

theorem demoR1_1220211 : invRung 7 5 20 [1, 2, 2, 0, 2, 1, 1] [1, 2, 2, 0, 2, 1, 1] 1 2 false = ([2, 2, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1220211 : invRung 7 5 20 [1, 2, 2, 0, 2, 1, 1] [2, 2, 1, 1, 1, 2, 1] 3 1 true = ([1, 1, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_1220211 : fieldCube 7 5 20 [1, 1, 2, 0, 2, 2, 1] = [0, 2, 1, 1, 0, 2, 0] := by
  decide

theorem demoM_1220211 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 2, 0] [1, 2, 2, 0, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1220211 : specInv 7 5 20 [1, 2, 2, 0, 2, 1, 1] = some [0, 2, 1, 1, 0, 2, 0] :=
  specInv_white_7 [1, 2, 2, 0, 2, 1, 1] [2, 2, 1, 1, 1, 2, 1] [1, 1, 2, 0, 2, 2, 1] [0, 2, 1, 1, 0, 2, 0] demoR1_1220211 demoR2_1220211 demoC_1220211 demoM_1220211

theorem demoR1_2220211 : invRung 7 5 20 [2, 2, 2, 0, 2, 1, 1] [2, 2, 2, 0, 2, 1, 1] 1 2 false = ([1, 2, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_2220211 : invRung 7 5 20 [2, 2, 2, 0, 2, 1, 1] [1, 2, 1, 0, 1, 0, 2] 3 1 true = ([1, 2, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_2220211 : fieldCube 7 5 20 [1, 2, 0, 2, 0, 2, 2] = [2, 1, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_2220211 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 0, 0] [2, 2, 2, 0, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220211 : mirrorTrits [2, 1, 2, 1, 1, 0, 0] = [1, 2, 1, 2, 2, 0, 0] := by
  decide

theorem demoInv_2220211 : specInv 7 5 20 [2, 2, 2, 0, 2, 1, 1] = some [1, 2, 1, 2, 2, 0, 0] :=
  specInv_mirror_7 [2, 2, 2, 0, 2, 1, 1] [1, 2, 1, 0, 1, 0, 2] [1, 2, 0, 2, 0, 2, 2] [2, 1, 2, 1, 1, 0, 0] [1, 2, 1, 2, 2, 0, 0] demoR1_2220211 demoR2_2220211 demoC_2220211 demoM_2220211 demoMir_2220211

theorem demoR1_0001211 : invRung 7 5 20 [0, 0, 0, 1, 2, 1, 1] [0, 0, 0, 1, 2, 1, 1] 1 2 false = ([2, 1, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_0001211 : invRung 7 5 20 [0, 0, 0, 1, 2, 1, 1] [2, 1, 1, 0, 2, 2, 0] 3 1 true = ([1, 1, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0001211 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 1, 1] = [2, 2, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_0001211 : fieldMul 7 5 20 [2, 2, 0, 2, 2, 2, 1] [0, 0, 0, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001211 : mirrorTrits [2, 2, 0, 2, 2, 2, 1] = [1, 1, 0, 1, 1, 1, 2] := by
  decide

theorem demoInv_0001211 : specInv 7 5 20 [0, 0, 0, 1, 2, 1, 1] = some [1, 1, 0, 1, 1, 1, 2] :=
  specInv_mirror_7 [0, 0, 0, 1, 2, 1, 1] [2, 1, 1, 0, 2, 2, 0] [1, 1, 1, 0, 0, 1, 1] [2, 2, 0, 2, 2, 2, 1] [1, 1, 0, 1, 1, 1, 2] demoR1_0001211 demoR2_0001211 demoC_0001211 demoM_0001211 demoMir_0001211

theorem demoR1_1001211 : invRung 7 5 20 [1, 0, 0, 1, 2, 1, 1] [1, 0, 0, 1, 2, 1, 1] 1 2 false = ([0, 0, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1001211 : invRung 7 5 20 [1, 0, 0, 1, 2, 1, 1] [0, 0, 0, 2, 0, 1, 2] 3 1 true = ([1, 0, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_1001211 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 1, 1] = [1, 1, 2, 0, 2, 0, 1] := by
  decide

theorem demoM_1001211 : fieldMul 7 5 20 [1, 1, 2, 0, 2, 0, 1] [1, 0, 0, 1, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1001211 : specInv 7 5 20 [1, 0, 0, 1, 2, 1, 1] = some [1, 1, 2, 0, 2, 0, 1] :=
  specInv_white_7 [1, 0, 0, 1, 2, 1, 1] [0, 0, 0, 2, 0, 1, 2] [1, 0, 2, 2, 2, 1, 1] [1, 1, 2, 0, 2, 0, 1] demoR1_1001211 demoR2_1001211 demoC_1001211 demoM_1001211

theorem demoR1_2001211 : invRung 7 5 20 [2, 0, 0, 1, 2, 1, 1] [2, 0, 0, 1, 2, 1, 1] 1 2 false = ([1, 1, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2001211 : invRung 7 5 20 [2, 0, 0, 1, 2, 1, 1] [1, 1, 1, 1, 2, 0, 1] 3 1 true = ([1, 1, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2001211 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 0, 0] = [1, 1, 0, 2, 0, 1, 2] := by
  decide

theorem demoM_2001211 : fieldMul 7 5 20 [1, 1, 0, 2, 0, 1, 2] [2, 0, 0, 1, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2001211 : specInv 7 5 20 [2, 0, 0, 1, 2, 1, 1] = some [1, 1, 0, 2, 0, 1, 2] :=
  specInv_white_7 [2, 0, 0, 1, 2, 1, 1] [1, 1, 1, 1, 2, 0, 1] [1, 1, 1, 0, 1, 0, 0] [1, 1, 0, 2, 0, 1, 2] demoR1_2001211 demoR2_2001211 demoC_2001211 demoM_2001211

theorem demoR1_0101211 : invRung 7 5 20 [0, 1, 0, 1, 2, 1, 1] [0, 1, 0, 1, 2, 1, 1] 1 2 false = ([0, 1, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_0101211 : invRung 7 5 20 [0, 1, 0, 1, 2, 1, 1] [0, 1, 2, 0, 1, 1, 2] 3 1 true = ([2, 0, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0101211 : fieldCube 7 5 20 [2, 0, 0, 0, 1, 2, 1] = [1, 1, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_0101211 : fieldMul 7 5 20 [1, 1, 1, 2, 0, 1, 0] [0, 1, 0, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101211 : mirrorTrits [1, 1, 1, 2, 0, 1, 0] = [2, 2, 2, 1, 0, 2, 0] := by
  decide

theorem demoInv_0101211 : specInv 7 5 20 [0, 1, 0, 1, 2, 1, 1] = some [2, 2, 2, 1, 0, 2, 0] :=
  specInv_mirror_7 [0, 1, 0, 1, 2, 1, 1] [0, 1, 2, 0, 1, 1, 2] [2, 0, 0, 0, 1, 2, 1] [1, 1, 1, 2, 0, 1, 0] [2, 2, 2, 1, 0, 2, 0] demoR1_0101211 demoR2_0101211 demoC_0101211 demoM_0101211 demoMir_0101211

theorem demoR1_1101211 : invRung 7 5 20 [1, 1, 0, 1, 2, 1, 1] [1, 1, 0, 1, 2, 1, 1] 1 2 false = ([0, 0, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1101211 : invRung 7 5 20 [1, 1, 0, 1, 2, 1, 1] [0, 0, 2, 0, 1, 1, 0] 3 1 true = ([2, 0, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_1101211 : fieldCube 7 5 20 [2, 0, 2, 0, 1, 0, 1] = [2, 2, 2, 2, 1, 2, 1] := by
  decide

theorem demoM_1101211 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 2, 1] [1, 1, 0, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1101211 : mirrorTrits [2, 2, 2, 2, 1, 2, 1] = [1, 1, 1, 1, 2, 1, 2] := by
  decide

theorem demoInv_1101211 : specInv 7 5 20 [1, 1, 0, 1, 2, 1, 1] = some [1, 1, 1, 1, 2, 1, 2] :=
  specInv_mirror_7 [1, 1, 0, 1, 2, 1, 1] [0, 0, 2, 0, 1, 1, 0] [2, 0, 2, 0, 1, 0, 1] [2, 2, 2, 2, 1, 2, 1] [1, 1, 1, 1, 2, 1, 2] demoR1_1101211 demoR2_1101211 demoC_1101211 demoM_1101211 demoMir_1101211

theorem demoR1_2101211 : invRung 7 5 20 [2, 1, 0, 1, 2, 1, 1] [2, 1, 0, 1, 2, 1, 1] 1 2 false = ([2, 0, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2101211 : invRung 7 5 20 [2, 1, 0, 1, 2, 1, 1] [2, 0, 0, 2, 2, 0, 1] 3 1 true = ([0, 2, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_2101211 : fieldCube 7 5 20 [0, 2, 0, 0, 0, 2, 1] = [2, 0, 1, 0, 0, 0, 2] := by
  decide

theorem demoM_2101211 : fieldMul 7 5 20 [2, 0, 1, 0, 0, 0, 2] [2, 1, 0, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101211 : mirrorTrits [2, 0, 1, 0, 0, 0, 2] = [1, 0, 2, 0, 0, 0, 1] := by
  decide

theorem demoInv_2101211 : specInv 7 5 20 [2, 1, 0, 1, 2, 1, 1] = some [1, 0, 2, 0, 0, 0, 1] :=
  specInv_mirror_7 [2, 1, 0, 1, 2, 1, 1] [2, 0, 0, 2, 2, 0, 1] [0, 2, 0, 0, 0, 2, 1] [2, 0, 1, 0, 0, 0, 2] [1, 0, 2, 0, 0, 0, 1] demoR1_2101211 demoR2_2101211 demoC_2101211 demoM_2101211 demoMir_2101211

theorem demoR1_0201211 : invRung 7 5 20 [0, 2, 0, 1, 2, 1, 1] [0, 2, 0, 1, 2, 1, 1] 1 2 false = ([2, 0, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_0201211 : invRung 7 5 20 [0, 2, 0, 1, 2, 1, 1] [2, 0, 1, 1, 2, 2, 2] 3 1 true = ([0, 0, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_0201211 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 1, 2] = [1, 1, 2, 0, 0, 1, 2] := by
  decide

theorem demoM_0201211 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 1, 2] [0, 2, 0, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201211 : mirrorTrits [1, 1, 2, 0, 0, 1, 2] = [2, 2, 1, 0, 0, 2, 1] := by
  decide

theorem demoInv_0201211 : specInv 7 5 20 [0, 2, 0, 1, 2, 1, 1] = some [2, 2, 1, 0, 0, 2, 1] :=
  specInv_mirror_7 [0, 2, 0, 1, 2, 1, 1] [2, 0, 1, 1, 2, 2, 2] [0, 0, 0, 0, 1, 1, 2] [1, 1, 2, 0, 0, 1, 2] [2, 2, 1, 0, 0, 2, 1] demoR1_0201211 demoR2_0201211 demoC_0201211 demoM_0201211 demoMir_0201211

theorem demoR1_1201211 : invRung 7 5 20 [1, 2, 0, 1, 2, 1, 1] [1, 2, 0, 1, 2, 1, 1] 1 2 false = ([1, 0, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1201211 : invRung 7 5 20 [1, 2, 0, 1, 2, 1, 1] [1, 0, 2, 0, 0, 2, 0] 3 1 true = ([2, 1, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_1201211 : fieldCube 7 5 20 [2, 1, 0, 0, 1, 1, 2] = [0, 1, 2, 1, 0, 1, 2] := by
  decide

theorem demoM_1201211 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 1, 2] [1, 2, 0, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201211 : mirrorTrits [0, 1, 2, 1, 0, 1, 2] = [0, 2, 1, 2, 0, 2, 1] := by
  decide

theorem demoInv_1201211 : specInv 7 5 20 [1, 2, 0, 1, 2, 1, 1] = some [0, 2, 1, 2, 0, 2, 1] :=
  specInv_mirror_7 [1, 2, 0, 1, 2, 1, 1] [1, 0, 2, 0, 0, 2, 0] [2, 1, 0, 0, 1, 1, 2] [0, 1, 2, 1, 0, 1, 2] [0, 2, 1, 2, 0, 2, 1] demoR1_1201211 demoR2_1201211 demoC_1201211 demoM_1201211 demoMir_1201211

theorem demoR1_2201211 : invRung 7 5 20 [2, 2, 0, 1, 2, 1, 1] [2, 2, 0, 1, 2, 1, 1] 1 2 false = ([1, 0, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_2201211 : invRung 7 5 20 [2, 2, 0, 1, 2, 1, 1] [1, 0, 0, 0, 2, 0, 1] 3 1 true = ([1, 0, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_2201211 : fieldCube 7 5 20 [1, 0, 0, 2, 0, 1, 2] = [1, 0, 1, 2, 0, 2, 1] := by
  decide

theorem demoM_2201211 : fieldMul 7 5 20 [1, 0, 1, 2, 0, 2, 1] [2, 2, 0, 1, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2201211 : specInv 7 5 20 [2, 2, 0, 1, 2, 1, 1] = some [1, 0, 1, 2, 0, 2, 1] :=
  specInv_white_7 [2, 2, 0, 1, 2, 1, 1] [1, 0, 0, 0, 2, 0, 1] [1, 0, 0, 2, 0, 1, 2] [1, 0, 1, 2, 0, 2, 1] demoR1_2201211 demoR2_2201211 demoC_2201211 demoM_2201211

theorem demoR1_0011211 : invRung 7 5 20 [0, 0, 1, 1, 2, 1, 1] [0, 0, 1, 1, 2, 1, 1] 1 2 false = ([0, 1, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_0011211 : invRung 7 5 20 [0, 0, 1, 1, 2, 1, 1] [0, 1, 1, 0, 1, 0, 2] 3 1 true = ([1, 0, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_0011211 : fieldCube 7 5 20 [1, 0, 0, 1, 1, 1, 1] = [0, 0, 1, 2, 2, 1, 1] := by
  decide

theorem demoM_0011211 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 1, 1] [0, 0, 1, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011211 : mirrorTrits [0, 0, 1, 2, 2, 1, 1] = [0, 0, 2, 1, 1, 2, 2] := by
  decide

theorem demoInv_0011211 : specInv 7 5 20 [0, 0, 1, 1, 2, 1, 1] = some [0, 0, 2, 1, 1, 2, 2] :=
  specInv_mirror_7 [0, 0, 1, 1, 2, 1, 1] [0, 1, 1, 0, 1, 0, 2] [1, 0, 0, 1, 1, 1, 1] [0, 0, 1, 2, 2, 1, 1] [0, 0, 2, 1, 1, 2, 2] demoR1_0011211 demoR2_0011211 demoC_0011211 demoM_0011211 demoMir_0011211

theorem demoR1_1011211 : invRung 7 5 20 [1, 0, 1, 1, 2, 1, 1] [1, 0, 1, 1, 2, 1, 1] 1 2 false = ([2, 1, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1011211 : invRung 7 5 20 [1, 0, 1, 1, 2, 1, 1] [2, 1, 1, 2, 2, 1, 1] 3 1 true = ([0, 0, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_1011211 : fieldCube 7 5 20 [0, 0, 0, 2, 0, 2, 0] = [1, 2, 1, 0, 2, 1, 1] := by
  decide

theorem demoM_1011211 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 1, 1] [1, 0, 1, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011211 : mirrorTrits [1, 2, 1, 0, 2, 1, 1] = [2, 1, 2, 0, 1, 2, 2] := by
  decide

theorem demoInv_1011211 : specInv 7 5 20 [1, 0, 1, 1, 2, 1, 1] = some [2, 1, 2, 0, 1, 2, 2] :=
  specInv_mirror_7 [1, 0, 1, 1, 2, 1, 1] [2, 1, 1, 2, 2, 1, 1] [0, 0, 0, 2, 0, 2, 0] [1, 2, 1, 0, 2, 1, 1] [2, 1, 2, 0, 1, 2, 2] demoR1_1011211 demoR2_1011211 demoC_1011211 demoM_1011211 demoMir_1011211

theorem demoR1_2011211 : invRung 7 5 20 [2, 0, 1, 1, 2, 1, 1] [2, 0, 1, 1, 2, 1, 1] 1 2 false = ([1, 2, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_2011211 : invRung 7 5 20 [2, 0, 1, 1, 2, 1, 1] [1, 2, 0, 0, 0, 1, 1] 3 1 true = ([1, 1, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_2011211 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 1, 0] = [2, 0, 1, 0, 1, 0, 2] := by
  decide

theorem demoM_2011211 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 0, 2] [2, 0, 1, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011211 : mirrorTrits [2, 0, 1, 0, 1, 0, 2] = [1, 0, 2, 0, 2, 0, 1] := by
  decide

theorem demoInv_2011211 : specInv 7 5 20 [2, 0, 1, 1, 2, 1, 1] = some [1, 0, 2, 0, 2, 0, 1] :=
  specInv_mirror_7 [2, 0, 1, 1, 2, 1, 1] [1, 2, 0, 0, 0, 1, 1] [1, 1, 1, 0, 2, 1, 0] [2, 0, 1, 0, 1, 0, 2] [1, 0, 2, 0, 2, 0, 1] demoR1_2011211 demoR2_2011211 demoC_2011211 demoM_2011211 demoMir_2011211

theorem demoR1_0111211 : invRung 7 5 20 [0, 1, 1, 1, 2, 1, 1] [0, 1, 1, 1, 2, 1, 1] 1 2 false = ([0, 0, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_0111211 : invRung 7 5 20 [0, 1, 1, 1, 2, 1, 1] [0, 0, 0, 0, 0, 1, 0] 3 1 true = ([1, 0, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0111211 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 2, 1] = [2, 1, 0, 2, 0, 0, 2] := by
  decide

theorem demoM_0111211 : fieldMul 7 5 20 [2, 1, 0, 2, 0, 0, 2] [0, 1, 1, 1, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0111211 : specInv 7 5 20 [0, 1, 1, 1, 2, 1, 1] = some [2, 1, 0, 2, 0, 0, 2] :=
  specInv_white_7 [0, 1, 1, 1, 2, 1, 1] [0, 0, 0, 0, 0, 1, 0] [1, 0, 2, 2, 1, 2, 1] [2, 1, 0, 2, 0, 0, 2] demoR1_0111211 demoR2_0111211 demoC_0111211 demoM_0111211

theorem demoR1_1111211 : invRung 7 5 20 [1, 1, 1, 1, 2, 1, 1] [1, 1, 1, 1, 2, 1, 1] 1 2 false = ([1, 2, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_1111211 : invRung 7 5 20 [1, 1, 1, 1, 2, 1, 1] [1, 2, 2, 2, 1, 1, 0] 3 1 true = ([0, 1, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_1111211 : fieldCube 7 5 20 [0, 1, 1, 2, 1, 1, 2] = [0, 1, 1, 1, 0, 0, 0] := by
  decide

theorem demoM_1111211 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 0, 0] [1, 1, 1, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111211 : mirrorTrits [0, 1, 1, 1, 0, 0, 0] = [0, 2, 2, 2, 0, 0, 0] := by
  decide

theorem demoInv_1111211 : specInv 7 5 20 [1, 1, 1, 1, 2, 1, 1] = some [0, 2, 2, 2, 0, 0, 0] :=
  specInv_mirror_7 [1, 1, 1, 1, 2, 1, 1] [1, 2, 2, 2, 1, 1, 0] [0, 1, 1, 2, 1, 1, 2] [0, 1, 1, 1, 0, 0, 0] [0, 2, 2, 2, 0, 0, 0] demoR1_1111211 demoR2_1111211 demoC_1111211 demoM_1111211 demoMir_1111211

theorem demoR1_2111211 : invRung 7 5 20 [2, 1, 1, 1, 2, 1, 1] [2, 1, 1, 1, 2, 1, 1] 1 2 false = ([1, 1, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_2111211 : invRung 7 5 20 [2, 1, 1, 1, 2, 1, 1] [1, 1, 2, 2, 2, 2, 1] 3 1 true = ([2, 0, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_2111211 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 1, 2] = [2, 0, 1, 2, 0, 2, 0] := by
  decide

theorem demoM_2111211 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 2, 0] [2, 1, 1, 1, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2111211 : specInv 7 5 20 [2, 1, 1, 1, 2, 1, 1] = some [2, 0, 1, 2, 0, 2, 0] :=
  specInv_white_7 [2, 1, 1, 1, 2, 1, 1] [1, 1, 2, 2, 2, 2, 1] [2, 0, 2, 2, 0, 1, 2] [2, 0, 1, 2, 0, 2, 0] demoR1_2111211 demoR2_2111211 demoC_2111211 demoM_2111211

theorem demoR1_0211211 : invRung 7 5 20 [0, 2, 1, 1, 2, 1, 1] [0, 2, 1, 1, 2, 1, 1] 1 2 false = ([2, 0, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_0211211 : invRung 7 5 20 [0, 2, 1, 1, 2, 1, 1] [2, 0, 1, 1, 1, 2, 2] 3 1 true = ([0, 0, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_0211211 : fieldCube 7 5 20 [0, 0, 2, 1, 1, 1, 0] = [2, 2, 2, 1, 1, 0, 2] := by
  decide

theorem demoM_0211211 : fieldMul 7 5 20 [2, 2, 2, 1, 1, 0, 2] [0, 2, 1, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211211 : mirrorTrits [2, 2, 2, 1, 1, 0, 2] = [1, 1, 1, 2, 2, 0, 1] := by
  decide

theorem demoInv_0211211 : specInv 7 5 20 [0, 2, 1, 1, 2, 1, 1] = some [1, 1, 1, 2, 2, 0, 1] :=
  specInv_mirror_7 [0, 2, 1, 1, 2, 1, 1] [2, 0, 1, 1, 1, 2, 2] [0, 0, 2, 1, 1, 1, 0] [2, 2, 2, 1, 1, 0, 2] [1, 1, 1, 2, 2, 0, 1] demoR1_0211211 demoR2_0211211 demoC_0211211 demoM_0211211 demoMir_0211211

theorem demoR1_1211211 : invRung 7 5 20 [1, 2, 1, 1, 2, 1, 1] [1, 2, 1, 1, 2, 1, 1] 1 2 false = ([2, 2, 2, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_1211211 : invRung 7 5 20 [1, 2, 1, 1, 2, 1, 1] [2, 2, 2, 1, 1, 0, 1] 3 1 true = ([2, 2, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_1211211 : fieldCube 7 5 20 [2, 2, 0, 0, 0, 1, 1] = [0, 2, 0, 0, 2, 2, 0] := by
  decide

theorem demoM_1211211 : fieldMul 7 5 20 [0, 2, 0, 0, 2, 2, 0] [1, 2, 1, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1211211 : mirrorTrits [0, 2, 0, 0, 2, 2, 0] = [0, 1, 0, 0, 1, 1, 0] := by
  decide

theorem demoInv_1211211 : specInv 7 5 20 [1, 2, 1, 1, 2, 1, 1] = some [0, 1, 0, 0, 1, 1, 0] :=
  specInv_mirror_7 [1, 2, 1, 1, 2, 1, 1] [2, 2, 2, 1, 1, 0, 1] [2, 2, 0, 0, 0, 1, 1] [0, 2, 0, 0, 2, 2, 0] [0, 1, 0, 0, 1, 1, 0] demoR1_1211211 demoR2_1211211 demoC_1211211 demoM_1211211 demoMir_1211211

theorem demoR1_2211211 : invRung 7 5 20 [2, 2, 1, 1, 2, 1, 1] [2, 2, 1, 1, 2, 1, 1] 1 2 false = ([0, 0, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_2211211 : invRung 7 5 20 [2, 2, 1, 1, 2, 1, 1] [0, 0, 0, 1, 1, 1, 1] 3 1 true = ([2, 0, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2211211 : fieldCube 7 5 20 [2, 0, 0, 0, 1, 1, 1] = [0, 0, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_2211211 : fieldMul 7 5 20 [0, 0, 0, 2, 2, 0, 1] [2, 2, 1, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211211 : mirrorTrits [0, 0, 0, 2, 2, 0, 1] = [0, 0, 0, 1, 1, 0, 2] := by
  decide

theorem demoInv_2211211 : specInv 7 5 20 [2, 2, 1, 1, 2, 1, 1] = some [0, 0, 0, 1, 1, 0, 2] :=
  specInv_mirror_7 [2, 2, 1, 1, 2, 1, 1] [0, 0, 0, 1, 1, 1, 1] [2, 0, 0, 0, 1, 1, 1] [0, 0, 0, 2, 2, 0, 1] [0, 0, 0, 1, 1, 0, 2] demoR1_2211211 demoR2_2211211 demoC_2211211 demoM_2211211 demoMir_2211211

theorem demoR1_0021211 : invRung 7 5 20 [0, 0, 2, 1, 2, 1, 1] [0, 0, 2, 1, 2, 1, 1] 1 2 false = ([0, 2, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0021211 : invRung 7 5 20 [0, 0, 2, 1, 2, 1, 1] [0, 2, 1, 2, 1, 2, 1] 3 1 true = ([1, 0, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0021211 : fieldCube 7 5 20 [1, 0, 2, 1, 2, 2, 2] = [1, 0, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_0021211 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 1, 1] [0, 0, 2, 1, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0021211 : specInv 7 5 20 [0, 0, 2, 1, 2, 1, 1] = some [1, 0, 1, 1, 1, 1, 1] :=
  specInv_white_7 [0, 0, 2, 1, 2, 1, 1] [0, 2, 1, 2, 1, 2, 1] [1, 0, 2, 1, 2, 2, 2] [1, 0, 1, 1, 1, 1, 1] demoR1_0021211 demoR2_0021211 demoC_0021211 demoM_0021211

theorem demoR1_1021211 : invRung 7 5 20 [1, 0, 2, 1, 2, 1, 1] [1, 0, 2, 1, 2, 1, 1] 1 2 false = ([2, 0, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_1021211 : invRung 7 5 20 [1, 0, 2, 1, 2, 1, 1] [2, 0, 0, 1, 2, 2, 2] 3 1 true = ([2, 1, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_1021211 : fieldCube 7 5 20 [2, 1, 0, 2, 0, 2, 2] = [0, 1, 2, 0, 1, 0, 0] := by
  decide

theorem demoM_1021211 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 0, 0] [1, 0, 2, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021211 : mirrorTrits [0, 1, 2, 0, 1, 0, 0] = [0, 2, 1, 0, 2, 0, 0] := by
  decide

theorem demoInv_1021211 : specInv 7 5 20 [1, 0, 2, 1, 2, 1, 1] = some [0, 2, 1, 0, 2, 0, 0] :=
  specInv_mirror_7 [1, 0, 2, 1, 2, 1, 1] [2, 0, 0, 1, 2, 2, 2] [2, 1, 0, 2, 0, 2, 2] [0, 1, 2, 0, 1, 0, 0] [0, 2, 1, 0, 2, 0, 0] demoR1_1021211 demoR2_1021211 demoC_1021211 demoM_1021211 demoMir_1021211

theorem demoR1_2021211 : invRung 7 5 20 [2, 0, 2, 1, 2, 1, 1] [2, 0, 2, 1, 2, 1, 1] 1 2 false = ([1, 1, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_2021211 : invRung 7 5 20 [2, 0, 2, 1, 2, 1, 1] [1, 1, 1, 1, 2, 0, 2] 3 1 true = ([0, 0, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_2021211 : fieldCube 7 5 20 [0, 0, 2, 0, 2, 1, 1] = [1, 1, 0, 0, 2, 1, 1] := by
  decide

theorem demoM_2021211 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 1, 1] [2, 0, 2, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021211 : mirrorTrits [1, 1, 0, 0, 2, 1, 1] = [2, 2, 0, 0, 1, 2, 2] := by
  decide

theorem demoInv_2021211 : specInv 7 5 20 [2, 0, 2, 1, 2, 1, 1] = some [2, 2, 0, 0, 1, 2, 2] :=
  specInv_mirror_7 [2, 0, 2, 1, 2, 1, 1] [1, 1, 1, 1, 2, 0, 2] [0, 0, 2, 0, 2, 1, 1] [1, 1, 0, 0, 2, 1, 1] [2, 2, 0, 0, 1, 2, 2] demoR1_2021211 demoR2_2021211 demoC_2021211 demoM_2021211 demoMir_2021211

theorem demoR1_0121211 : invRung 7 5 20 [0, 1, 2, 1, 2, 1, 1] [0, 1, 2, 1, 2, 1, 1] 1 2 false = ([2, 2, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_0121211 : invRung 7 5 20 [0, 1, 2, 1, 2, 1, 1] [2, 2, 0, 1, 2, 1, 0] 3 1 true = ([0, 0, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0121211 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 0, 1] = [1, 0, 0, 0, 1, 1, 0] := by
  decide

theorem demoM_0121211 : fieldMul 7 5 20 [1, 0, 0, 0, 1, 1, 0] [0, 1, 2, 1, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0121211 : specInv 7 5 20 [0, 1, 2, 1, 2, 1, 1] = some [1, 0, 0, 0, 1, 1, 0] :=
  specInv_white_7 [0, 1, 2, 1, 2, 1, 1] [2, 2, 0, 1, 2, 1, 0] [0, 0, 0, 1, 2, 0, 1] [1, 0, 0, 0, 1, 1, 0] demoR1_0121211 demoR2_0121211 demoC_0121211 demoM_0121211

theorem demoR1_1121211 : invRung 7 5 20 [1, 1, 2, 1, 2, 1, 1] [1, 1, 2, 1, 2, 1, 1] 1 2 false = ([0, 1, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_1121211 : invRung 7 5 20 [1, 1, 2, 1, 2, 1, 1] [0, 1, 2, 2, 1, 1, 1] 3 1 true = ([1, 1, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_1121211 : fieldCube 7 5 20 [1, 1, 1, 2, 1, 1, 0] = [1, 2, 0, 2, 1, 1, 1] := by
  decide

theorem demoM_1121211 : fieldMul 7 5 20 [1, 2, 0, 2, 1, 1, 1] [1, 1, 2, 1, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1121211 : specInv 7 5 20 [1, 1, 2, 1, 2, 1, 1] = some [1, 2, 0, 2, 1, 1, 1] :=
  specInv_white_7 [1, 1, 2, 1, 2, 1, 1] [0, 1, 2, 2, 1, 1, 1] [1, 1, 1, 2, 1, 1, 0] [1, 2, 0, 2, 1, 1, 1] demoR1_1121211 demoR2_1121211 demoC_1121211 demoM_1121211

theorem demoR1_2121211 : invRung 7 5 20 [2, 1, 2, 1, 2, 1, 1] [2, 1, 2, 1, 2, 1, 1] 1 2 false = ([0, 2, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_2121211 : invRung 7 5 20 [2, 1, 2, 1, 2, 1, 1] [0, 2, 2, 0, 2, 1, 1] 3 1 true = ([0, 1, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_2121211 : fieldCube 7 5 20 [0, 1, 1, 1, 2, 0, 0] = [1, 2, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_2121211 : fieldMul 7 5 20 [1, 2, 1, 0, 0, 0, 0] [2, 1, 2, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2121211 : mirrorTrits [1, 2, 1, 0, 0, 0, 0] = [2, 1, 2, 0, 0, 0, 0] := by
  decide

theorem demoInv_2121211 : specInv 7 5 20 [2, 1, 2, 1, 2, 1, 1] = some [2, 1, 2, 0, 0, 0, 0] :=
  specInv_mirror_7 [2, 1, 2, 1, 2, 1, 1] [0, 2, 2, 0, 2, 1, 1] [0, 1, 1, 1, 2, 0, 0] [1, 2, 1, 0, 0, 0, 0] [2, 1, 2, 0, 0, 0, 0] demoR1_2121211 demoR2_2121211 demoC_2121211 demoM_2121211 demoMir_2121211

theorem demoR1_0221211 : invRung 7 5 20 [0, 2, 2, 1, 2, 1, 1] [0, 2, 2, 1, 2, 1, 1] 1 2 false = ([1, 2, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_0221211 : invRung 7 5 20 [0, 2, 2, 1, 2, 1, 1] [1, 2, 2, 1, 2, 1, 0] 3 1 true = ([1, 1, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_0221211 : fieldCube 7 5 20 [1, 1, 1, 2, 0, 0, 0] = [0, 0, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_0221211 : fieldMul 7 5 20 [0, 0, 2, 1, 0, 2, 1] [0, 2, 2, 1, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0221211 : specInv 7 5 20 [0, 2, 2, 1, 2, 1, 1] = some [0, 0, 2, 1, 0, 2, 1] :=
  specInv_white_7 [0, 2, 2, 1, 2, 1, 1] [1, 2, 2, 1, 2, 1, 0] [1, 1, 1, 2, 0, 0, 0] [0, 0, 2, 1, 0, 2, 1] demoR1_0221211 demoR2_0221211 demoC_0221211 demoM_0221211

theorem demoR1_1221211 : invRung 7 5 20 [1, 2, 2, 1, 2, 1, 1] [1, 2, 2, 1, 2, 1, 1] 1 2 false = ([1, 0, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1221211 : invRung 7 5 20 [1, 2, 2, 1, 2, 1, 1] [1, 0, 1, 2, 1, 0, 2] 3 1 true = ([1, 2, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_1221211 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 2, 2] = [2, 0, 2, 0, 1, 2, 1] := by
  decide

theorem demoM_1221211 : fieldMul 7 5 20 [2, 0, 2, 0, 1, 2, 1] [1, 2, 2, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221211 : mirrorTrits [2, 0, 2, 0, 1, 2, 1] = [1, 0, 1, 0, 2, 1, 2] := by
  decide

theorem demoInv_1221211 : specInv 7 5 20 [1, 2, 2, 1, 2, 1, 1] = some [1, 0, 1, 0, 2, 1, 2] :=
  specInv_mirror_7 [1, 2, 2, 1, 2, 1, 1] [1, 0, 1, 2, 1, 0, 2] [1, 2, 2, 2, 2, 2, 2] [2, 0, 2, 0, 1, 2, 1] [1, 0, 1, 0, 2, 1, 2] demoR1_1221211 demoR2_1221211 demoC_1221211 demoM_1221211 demoMir_1221211

theorem demoR1_2221211 : invRung 7 5 20 [2, 2, 2, 1, 2, 1, 1] [2, 2, 2, 1, 2, 1, 1] 1 2 false = ([2, 2, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_2221211 : invRung 7 5 20 [2, 2, 2, 1, 2, 1, 1] [2, 2, 0, 2, 2, 1, 0] 3 1 true = ([2, 0, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_2221211 : fieldCube 7 5 20 [2, 0, 1, 2, 1, 2, 1] = [0, 1, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_2221211 : fieldMul 7 5 20 [0, 1, 0, 2, 0, 0, 1] [2, 2, 2, 1, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221211 : mirrorTrits [0, 1, 0, 2, 0, 0, 1] = [0, 2, 0, 1, 0, 0, 2] := by
  decide

theorem demoInv_2221211 : specInv 7 5 20 [2, 2, 2, 1, 2, 1, 1] = some [0, 2, 0, 1, 0, 0, 2] :=
  specInv_mirror_7 [2, 2, 2, 1, 2, 1, 1] [2, 2, 0, 2, 2, 1, 0] [2, 0, 1, 2, 1, 2, 1] [0, 1, 0, 2, 0, 0, 1] [0, 2, 0, 1, 0, 0, 2] demoR1_2221211 demoR2_2221211 demoC_2221211 demoM_2221211 demoMir_2221211

theorem demoR1_0002211 : invRung 7 5 20 [0, 0, 0, 2, 2, 1, 1] [0, 0, 0, 2, 2, 1, 1] 1 2 false = ([1, 1, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_0002211 : invRung 7 5 20 [0, 0, 0, 2, 2, 1, 1] [1, 1, 1, 2, 0, 0, 2] 3 1 true = ([0, 0, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_0002211 : fieldCube 7 5 20 [0, 0, 2, 1, 1, 1, 2] = [2, 1, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_0002211 : fieldMul 7 5 20 [2, 1, 0, 0, 0, 2, 1] [0, 0, 0, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0002211 : specInv 7 5 20 [0, 0, 0, 2, 2, 1, 1] = some [2, 1, 0, 0, 0, 2, 1] :=
  specInv_white_7 [0, 0, 0, 2, 2, 1, 1] [1, 1, 1, 2, 0, 0, 2] [0, 0, 2, 1, 1, 1, 2] [2, 1, 0, 0, 0, 2, 1] demoR1_0002211 demoR2_0002211 demoC_0002211 demoM_0002211

theorem demoR1_1002211 : invRung 7 5 20 [1, 0, 0, 2, 2, 1, 1] [1, 0, 0, 2, 2, 1, 1] 1 2 false = ([2, 0, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1002211 : invRung 7 5 20 [1, 0, 0, 2, 2, 1, 1] [2, 0, 1, 0, 1, 1, 0] 3 1 true = ([1, 2, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_1002211 : fieldCube 7 5 20 [1, 2, 0, 0, 0, 2, 0] = [0, 2, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_1002211 : fieldMul 7 5 20 [0, 2, 2, 2, 2, 2, 1] [1, 0, 0, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1002211 : specInv 7 5 20 [1, 0, 0, 2, 2, 1, 1] = some [0, 2, 2, 2, 2, 2, 1] :=
  specInv_white_7 [1, 0, 0, 2, 2, 1, 1] [2, 0, 1, 0, 1, 1, 0] [1, 2, 0, 0, 0, 2, 0] [0, 2, 2, 2, 2, 2, 1] demoR1_1002211 demoR2_1002211 demoC_1002211 demoM_1002211

theorem demoR1_2002211 : invRung 7 5 20 [2, 0, 0, 2, 2, 1, 1] [2, 0, 0, 2, 2, 1, 1] 1 2 false = ([0, 0, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_2002211 : invRung 7 5 20 [2, 0, 0, 2, 2, 1, 1] [0, 0, 1, 0, 2, 0, 1] 3 1 true = ([1, 2, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_2002211 : fieldCube 7 5 20 [1, 2, 2, 1, 2, 0, 0] = [2, 2, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_2002211 : fieldMul 7 5 20 [2, 2, 1, 1, 0, 0, 1] [2, 0, 0, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2002211 : specInv 7 5 20 [2, 0, 0, 2, 2, 1, 1] = some [2, 2, 1, 1, 0, 0, 1] :=
  specInv_white_7 [2, 0, 0, 2, 2, 1, 1] [0, 0, 1, 0, 2, 0, 1] [1, 2, 2, 1, 2, 0, 0] [2, 2, 1, 1, 0, 0, 1] demoR1_2002211 demoR2_2002211 demoC_2002211 demoM_2002211

theorem demoR1_0102211 : invRung 7 5 20 [0, 1, 0, 2, 2, 1, 1] [0, 1, 0, 2, 2, 1, 1] 1 2 false = ([1, 0, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_0102211 : invRung 7 5 20 [0, 1, 0, 2, 2, 1, 1] [1, 0, 1, 2, 2, 0, 1] 3 1 true = ([2, 1, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0102211 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 0, 0] = [0, 1, 1, 2, 0, 2, 0] := by
  decide

theorem demoM_0102211 : fieldMul 7 5 20 [0, 1, 1, 2, 0, 2, 0] [0, 1, 0, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102211 : mirrorTrits [0, 1, 1, 2, 0, 2, 0] = [0, 2, 2, 1, 0, 1, 0] := by
  decide

theorem demoInv_0102211 : specInv 7 5 20 [0, 1, 0, 2, 2, 1, 1] = some [0, 2, 2, 1, 0, 1, 0] :=
  specInv_mirror_7 [0, 1, 0, 2, 2, 1, 1] [1, 0, 1, 2, 2, 0, 1] [2, 1, 2, 1, 1, 0, 0] [0, 1, 1, 2, 0, 2, 0] [0, 2, 2, 1, 0, 1, 0] demoR1_0102211 demoR2_0102211 demoC_0102211 demoM_0102211 demoMir_0102211

theorem demoR1_1102211 : invRung 7 5 20 [1, 1, 0, 2, 2, 1, 1] [1, 1, 0, 2, 2, 1, 1] 1 2 false = ([2, 2, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_1102211 : invRung 7 5 20 [1, 1, 0, 2, 2, 1, 1] [2, 2, 2, 1, 1, 1, 1] 3 1 true = ([0, 1, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1102211 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 0, 0] = [0, 1, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_1102211 : fieldMul 7 5 20 [0, 1, 0, 2, 0, 1, 1] [1, 1, 0, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102211 : mirrorTrits [0, 1, 0, 2, 0, 1, 1] = [0, 2, 0, 1, 0, 2, 2] := by
  decide

theorem demoInv_1102211 : specInv 7 5 20 [1, 1, 0, 2, 2, 1, 1] = some [0, 2, 0, 1, 0, 2, 2] :=
  specInv_mirror_7 [1, 1, 0, 2, 2, 1, 1] [2, 2, 2, 1, 1, 1, 1] [0, 1, 0, 0, 1, 0, 0] [0, 1, 0, 2, 0, 1, 1] [0, 2, 0, 1, 0, 2, 2] demoR1_1102211 demoR2_1102211 demoC_1102211 demoM_1102211 demoMir_1102211

theorem demoR1_2102211 : invRung 7 5 20 [2, 1, 0, 2, 2, 1, 1] [2, 1, 0, 2, 2, 1, 1] 1 2 false = ([2, 1, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2102211 : invRung 7 5 20 [2, 1, 0, 2, 2, 1, 1] [2, 1, 2, 1, 0, 2, 1] 3 1 true = ([0, 2, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2102211 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 2, 0] = [0, 2, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_2102211 : fieldMul 7 5 20 [0, 2, 0, 2, 2, 0, 2] [2, 1, 0, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2102211 : specInv 7 5 20 [2, 1, 0, 2, 2, 1, 1] = some [0, 2, 0, 2, 2, 0, 2] :=
  specInv_white_7 [2, 1, 0, 2, 2, 1, 1] [2, 1, 2, 1, 0, 2, 1] [0, 2, 1, 1, 0, 2, 0] [0, 2, 0, 2, 2, 0, 2] demoR1_2102211 demoR2_2102211 demoC_2102211 demoM_2102211

theorem demoR1_0202211 : invRung 7 5 20 [0, 2, 0, 2, 2, 1, 1] [0, 2, 0, 2, 2, 1, 1] 1 2 false = ([2, 2, 2, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_0202211 : invRung 7 5 20 [0, 2, 0, 2, 2, 1, 1] [2, 2, 2, 1, 2, 0, 2] 3 1 true = ([0, 1, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0202211 : fieldCube 7 5 20 [0, 1, 1, 2, 2, 0, 2] = [2, 1, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_0202211 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 0, 2] [0, 2, 0, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202211 : mirrorTrits [2, 1, 0, 2, 2, 0, 2] = [1, 2, 0, 1, 1, 0, 1] := by
  decide

theorem demoInv_0202211 : specInv 7 5 20 [0, 2, 0, 2, 2, 1, 1] = some [1, 2, 0, 1, 1, 0, 1] :=
  specInv_mirror_7 [0, 2, 0, 2, 2, 1, 1] [2, 2, 2, 1, 2, 0, 2] [0, 1, 1, 2, 2, 0, 2] [2, 1, 0, 2, 2, 0, 2] [1, 2, 0, 1, 1, 0, 1] demoR1_0202211 demoR2_0202211 demoC_0202211 demoM_0202211 demoMir_0202211

theorem demoR1_1202211 : invRung 7 5 20 [1, 2, 0, 2, 2, 1, 1] [1, 2, 0, 2, 2, 1, 1] 1 2 false = ([0, 2, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1202211 : invRung 7 5 20 [1, 2, 0, 2, 2, 1, 1] [0, 2, 1, 2, 1, 0, 2] 3 1 true = ([1, 0, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1202211 : fieldCube 7 5 20 [1, 0, 2, 2, 0, 1, 0] = [1, 1, 0, 0, 1, 0, 1] := by
  decide

theorem demoM_1202211 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 0, 1] [1, 2, 0, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1202211 : specInv 7 5 20 [1, 2, 0, 2, 2, 1, 1] = some [1, 1, 0, 0, 1, 0, 1] :=
  specInv_white_7 [1, 2, 0, 2, 2, 1, 1] [0, 2, 1, 2, 1, 0, 2] [1, 0, 2, 2, 0, 1, 0] [1, 1, 0, 0, 1, 0, 1] demoR1_1202211 demoR2_1202211 demoC_1202211 demoM_1202211

theorem demoR1_2202211 : invRung 7 5 20 [2, 2, 0, 2, 2, 1, 1] [2, 2, 0, 2, 2, 1, 1] 1 2 false = ([2, 1, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_2202211 : invRung 7 5 20 [2, 2, 0, 2, 2, 1, 1] [2, 1, 1, 0, 0, 2, 2] 3 1 true = ([1, 2, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_2202211 : fieldCube 7 5 20 [1, 2, 2, 1, 1, 2, 2] = [1, 2, 1, 2, 1, 0, 0] := by
  decide

theorem demoM_2202211 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 0, 0] [2, 2, 0, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202211 : mirrorTrits [1, 2, 1, 2, 1, 0, 0] = [2, 1, 2, 1, 2, 0, 0] := by
  decide

theorem demoInv_2202211 : specInv 7 5 20 [2, 2, 0, 2, 2, 1, 1] = some [2, 1, 2, 1, 2, 0, 0] :=
  specInv_mirror_7 [2, 2, 0, 2, 2, 1, 1] [2, 1, 1, 0, 0, 2, 2] [1, 2, 2, 1, 1, 2, 2] [1, 2, 1, 2, 1, 0, 0] [2, 1, 2, 1, 2, 0, 0] demoR1_2202211 demoR2_2202211 demoC_2202211 demoM_2202211 demoMir_2202211

theorem demoR1_0012211 : invRung 7 5 20 [0, 0, 1, 2, 2, 1, 1] [0, 0, 1, 2, 2, 1, 1] 1 2 false = ([2, 0, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_0012211 : invRung 7 5 20 [0, 0, 1, 2, 2, 1, 1] [2, 0, 0, 2, 0, 1, 1] 3 1 true = ([2, 1, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_0012211 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 2, 2] = [0, 0, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_0012211 : fieldMul 7 5 20 [0, 0, 2, 2, 1, 2, 2] [0, 0, 1, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0012211 : specInv 7 5 20 [0, 0, 1, 2, 2, 1, 1] = some [0, 0, 2, 2, 1, 2, 2] :=
  specInv_white_7 [0, 0, 1, 2, 2, 1, 1] [2, 0, 0, 2, 0, 1, 1] [2, 1, 0, 2, 2, 2, 2] [0, 0, 2, 2, 1, 2, 2] demoR1_0012211 demoR2_0012211 demoC_0012211 demoM_0012211

theorem demoR1_1012211 : invRung 7 5 20 [1, 0, 1, 2, 2, 1, 1] [1, 0, 1, 2, 2, 1, 1] 1 2 false = ([1, 1, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_1012211 : invRung 7 5 20 [1, 0, 1, 2, 2, 1, 1] [1, 1, 2, 2, 0, 2, 0] 3 1 true = ([0, 2, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_1012211 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 2, 0] = [2, 0, 2, 0, 2, 0, 1] := by
  decide

theorem demoM_1012211 : fieldMul 7 5 20 [2, 0, 2, 0, 2, 0, 1] [1, 0, 1, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1012211 : specInv 7 5 20 [1, 0, 1, 2, 2, 1, 1] = some [2, 0, 2, 0, 2, 0, 1] :=
  specInv_white_7 [1, 0, 1, 2, 2, 1, 1] [1, 1, 2, 2, 0, 2, 0] [0, 2, 2, 0, 1, 2, 0] [2, 0, 2, 0, 2, 0, 1] demoR1_1012211 demoR2_1012211 demoC_1012211 demoM_1012211

theorem demoR1_2012211 : invRung 7 5 20 [2, 0, 1, 2, 2, 1, 1] [2, 0, 1, 2, 2, 1, 1] 1 2 false = ([0, 2, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2012211 : invRung 7 5 20 [2, 0, 1, 2, 2, 1, 1] [0, 2, 1, 0, 2, 0, 0] 3 1 true = ([1, 0, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_2012211 : fieldCube 7 5 20 [1, 0, 0, 2, 0, 2, 0] = [2, 2, 1, 0, 2, 1, 1] := by
  decide

theorem demoM_2012211 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 1, 1] [2, 0, 1, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012211 : mirrorTrits [2, 2, 1, 0, 2, 1, 1] = [1, 1, 2, 0, 1, 2, 2] := by
  decide

theorem demoInv_2012211 : specInv 7 5 20 [2, 0, 1, 2, 2, 1, 1] = some [1, 1, 2, 0, 1, 2, 2] :=
  specInv_mirror_7 [2, 0, 1, 2, 2, 1, 1] [0, 2, 1, 0, 2, 0, 0] [1, 0, 0, 2, 0, 2, 0] [2, 2, 1, 0, 2, 1, 1] [1, 1, 2, 0, 1, 2, 2] demoR1_2012211 demoR2_2012211 demoC_2012211 demoM_2012211 demoMir_2012211

theorem demoR1_0112211 : invRung 7 5 20 [0, 1, 1, 2, 2, 1, 1] [0, 1, 1, 2, 2, 1, 1] 1 2 false = ([2, 0, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_0112211 : invRung 7 5 20 [0, 1, 1, 2, 2, 1, 1] [2, 0, 0, 0, 1, 2, 2] 3 1 true = ([0, 0, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_0112211 : fieldCube 7 5 20 [0, 0, 2, 2, 2, 2, 0] = [1, 1, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_0112211 : fieldMul 7 5 20 [1, 1, 1, 2, 2, 0, 2] [0, 1, 1, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0112211 : specInv 7 5 20 [0, 1, 1, 2, 2, 1, 1] = some [1, 1, 1, 2, 2, 0, 2] :=
  specInv_white_7 [0, 1, 1, 2, 2, 1, 1] [2, 0, 0, 0, 1, 2, 2] [0, 0, 2, 2, 2, 2, 0] [1, 1, 1, 2, 2, 0, 2] demoR1_0112211 demoR2_0112211 demoC_0112211 demoM_0112211

theorem demoR1_1112211 : invRung 7 5 20 [1, 1, 1, 2, 2, 1, 1] [1, 1, 1, 2, 2, 1, 1] 1 2 false = ([1, 0, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_1112211 : invRung 7 5 20 [1, 1, 1, 2, 2, 1, 1] [1, 0, 1, 0, 0, 1, 2] 3 1 true = ([1, 2, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_1112211 : fieldCube 7 5 20 [1, 2, 2, 2, 0, 1, 2] = [1, 0, 1, 1, 0, 2, 0] := by
  decide

theorem demoM_1112211 : fieldMul 7 5 20 [1, 0, 1, 1, 0, 2, 0] [1, 1, 1, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1112211 : specInv 7 5 20 [1, 1, 1, 2, 2, 1, 1] = some [1, 0, 1, 1, 0, 2, 0] :=
  specInv_white_7 [1, 1, 1, 2, 2, 1, 1] [1, 0, 1, 0, 0, 1, 2] [1, 2, 2, 2, 0, 1, 2] [1, 0, 1, 1, 0, 2, 0] demoR1_1112211 demoR2_1112211 demoC_1112211 demoM_1112211

theorem demoR1_2112211 : invRung 7 5 20 [2, 1, 1, 2, 2, 1, 1] [2, 1, 1, 2, 2, 1, 1] 1 2 false = ([2, 2, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_2112211 : invRung 7 5 20 [2, 1, 1, 2, 2, 1, 1] [2, 2, 1, 0, 1, 2, 0] 3 1 true = ([1, 0, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_2112211 : fieldCube 7 5 20 [1, 0, 2, 0, 0, 2, 1] = [0, 0, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_2112211 : fieldMul 7 5 20 [0, 0, 1, 1, 0, 0, 1] [2, 1, 1, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112211 : mirrorTrits [0, 0, 1, 1, 0, 0, 1] = [0, 0, 2, 2, 0, 0, 2] := by
  decide

theorem demoInv_2112211 : specInv 7 5 20 [2, 1, 1, 2, 2, 1, 1] = some [0, 0, 2, 2, 0, 0, 2] :=
  specInv_mirror_7 [2, 1, 1, 2, 2, 1, 1] [2, 2, 1, 0, 1, 2, 0] [1, 0, 2, 0, 0, 2, 1] [0, 0, 1, 1, 0, 0, 1] [0, 0, 2, 2, 0, 0, 2] demoR1_2112211 demoR2_2112211 demoC_2112211 demoM_2112211 demoMir_2112211

theorem demoR1_0212211 : invRung 7 5 20 [0, 2, 1, 2, 2, 1, 1] [0, 2, 1, 2, 2, 1, 1] 1 2 false = ([1, 2, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_0212211 : invRung 7 5 20 [0, 2, 1, 2, 2, 1, 1] [1, 2, 2, 0, 0, 1, 2] 3 1 true = ([1, 1, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0212211 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 0, 0] = [2, 1, 1, 2, 0, 2, 2] := by
  decide

theorem demoM_0212211 : fieldMul 7 5 20 [2, 1, 1, 2, 0, 2, 2] [0, 2, 1, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212211 : mirrorTrits [2, 1, 1, 2, 0, 2, 2] = [1, 2, 2, 1, 0, 1, 1] := by
  decide

theorem demoInv_0212211 : specInv 7 5 20 [0, 2, 1, 2, 2, 1, 1] = some [1, 2, 2, 1, 0, 1, 1] :=
  specInv_mirror_7 [0, 2, 1, 2, 2, 1, 1] [1, 2, 2, 0, 0, 1, 2] [1, 1, 1, 1, 1, 0, 0] [2, 1, 1, 2, 0, 2, 2] [1, 2, 2, 1, 0, 1, 1] demoR1_0212211 demoR2_0212211 demoC_0212211 demoM_0212211 demoMir_0212211

theorem demoR1_1212211 : invRung 7 5 20 [1, 2, 1, 2, 2, 1, 1] [1, 2, 1, 2, 2, 1, 1] 1 2 false = ([0, 2, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1212211 : invRung 7 5 20 [1, 2, 1, 2, 2, 1, 1] [0, 2, 2, 1, 0, 0, 1] 3 1 true = ([1, 0, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1212211 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 1, 0] = [2, 1, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_1212211 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 1, 0] [1, 2, 1, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212211 : mirrorTrits [2, 1, 1, 0, 1, 1, 0] = [1, 2, 2, 0, 2, 2, 0] := by
  decide

theorem demoInv_1212211 : specInv 7 5 20 [1, 2, 1, 2, 2, 1, 1] = some [1, 2, 2, 0, 2, 2, 0] :=
  specInv_mirror_7 [1, 2, 1, 2, 2, 1, 1] [0, 2, 2, 1, 0, 0, 1] [1, 0, 1, 0, 0, 1, 0] [2, 1, 1, 0, 1, 1, 0] [1, 2, 2, 0, 2, 2, 0] demoR1_1212211 demoR2_1212211 demoC_1212211 demoM_1212211 demoMir_1212211

theorem demoR1_2212211 : invRung 7 5 20 [2, 2, 1, 2, 2, 1, 1] [2, 2, 1, 2, 2, 1, 1] 1 2 false = ([0, 0, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2212211 : invRung 7 5 20 [2, 2, 1, 2, 2, 1, 1] [0, 0, 0, 1, 2, 0, 1] 3 1 true = ([2, 1, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2212211 : fieldCube 7 5 20 [2, 1, 0, 1, 2, 2, 0] = [2, 1, 0, 0, 2, 2, 0] := by
  decide

theorem demoM_2212211 : fieldMul 7 5 20 [2, 1, 0, 0, 2, 2, 0] [2, 2, 1, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2212211 : specInv 7 5 20 [2, 2, 1, 2, 2, 1, 1] = some [2, 1, 0, 0, 2, 2, 0] :=
  specInv_white_7 [2, 2, 1, 2, 2, 1, 1] [0, 0, 0, 1, 2, 0, 1] [2, 1, 0, 1, 2, 2, 0] [2, 1, 0, 0, 2, 2, 0] demoR1_2212211 demoR2_2212211 demoC_2212211 demoM_2212211

theorem demoR1_0022211 : invRung 7 5 20 [0, 0, 2, 2, 2, 1, 1] [0, 0, 2, 2, 2, 1, 1] 1 2 false = ([0, 1, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_0022211 : invRung 7 5 20 [0, 0, 2, 2, 2, 1, 1] [0, 1, 0, 1, 1, 1, 0] 3 1 true = ([1, 1, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0022211 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 2, 1] = [0, 1, 1, 0, 0, 1, 1] := by
  decide

theorem demoM_0022211 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 1, 1] [0, 0, 2, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0022211 : specInv 7 5 20 [0, 0, 2, 2, 2, 1, 1] = some [0, 1, 1, 0, 0, 1, 1] :=
  specInv_white_7 [0, 0, 2, 2, 2, 1, 1] [0, 1, 0, 1, 1, 1, 0] [1, 1, 1, 0, 1, 2, 1] [0, 1, 1, 0, 0, 1, 1] demoR1_0022211 demoR2_0022211 demoC_0022211 demoM_0022211

theorem demoR1_1022211 : invRung 7 5 20 [1, 0, 2, 2, 2, 1, 1] [1, 0, 2, 2, 2, 1, 1] 1 2 false = ([2, 1, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_1022211 : invRung 7 5 20 [1, 0, 2, 2, 2, 1, 1] [2, 1, 2, 0, 0, 2, 2] 3 1 true = ([0, 0, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_1022211 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 2, 2] = [1, 0, 2, 1, 1, 2, 0] := by
  decide

theorem demoM_1022211 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 2, 0] [1, 0, 2, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1022211 : specInv 7 5 20 [1, 0, 2, 2, 2, 1, 1] = some [1, 0, 2, 1, 1, 2, 0] :=
  specInv_white_7 [1, 0, 2, 2, 2, 1, 1] [2, 1, 2, 0, 0, 2, 2] [0, 0, 1, 2, 2, 2, 2] [1, 0, 2, 1, 1, 2, 0] demoR1_1022211 demoR2_1022211 demoC_1022211 demoM_1022211

theorem demoR1_2022211 : invRung 7 5 20 [2, 0, 2, 2, 2, 1, 1] [2, 0, 2, 2, 2, 1, 1] 1 2 false = ([1, 0, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_2022211 : invRung 7 5 20 [2, 0, 2, 2, 2, 1, 1] [1, 0, 1, 2, 0, 2, 0] 3 1 true = ([2, 1, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_2022211 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 0, 2] = [0, 2, 2, 0, 2, 0, 0] := by
  decide

theorem demoM_2022211 : fieldMul 7 5 20 [0, 2, 2, 0, 2, 0, 0] [2, 0, 2, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2022211 : specInv 7 5 20 [2, 0, 2, 2, 2, 1, 1] = some [0, 2, 2, 0, 2, 0, 0] :=
  specInv_white_7 [2, 0, 2, 2, 2, 1, 1] [1, 0, 1, 2, 0, 2, 0] [2, 1, 1, 1, 0, 0, 2] [0, 2, 2, 0, 2, 0, 0] demoR1_2022211 demoR2_2022211 demoC_2022211 demoM_2022211

theorem demoR1_0122211 : invRung 7 5 20 [0, 1, 2, 2, 2, 1, 1] [0, 1, 2, 2, 2, 1, 1] 1 2 false = ([0, 1, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_0122211 : invRung 7 5 20 [0, 1, 2, 2, 2, 1, 1] [0, 1, 2, 2, 0, 2, 2] 3 1 true = ([1, 1, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_0122211 : fieldCube 7 5 20 [1, 1, 2, 2, 0, 2, 1] = [2, 0, 0, 2, 0, 2, 1] := by
  decide

theorem demoM_0122211 : fieldMul 7 5 20 [2, 0, 0, 2, 0, 2, 1] [0, 1, 2, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122211 : mirrorTrits [2, 0, 0, 2, 0, 2, 1] = [1, 0, 0, 1, 0, 1, 2] := by
  decide

theorem demoInv_0122211 : specInv 7 5 20 [0, 1, 2, 2, 2, 1, 1] = some [1, 0, 0, 1, 0, 1, 2] :=
  specInv_mirror_7 [0, 1, 2, 2, 2, 1, 1] [0, 1, 2, 2, 0, 2, 2] [1, 1, 2, 2, 0, 2, 1] [2, 0, 0, 2, 0, 2, 1] [1, 0, 0, 1, 0, 1, 2] demoR1_0122211 demoR2_0122211 demoC_0122211 demoM_0122211 demoMir_0122211

theorem demoR1_1122211 : invRung 7 5 20 [1, 1, 2, 2, 2, 1, 1] [1, 1, 2, 2, 2, 1, 1] 1 2 false = ([2, 2, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1122211 : invRung 7 5 20 [1, 1, 2, 2, 2, 1, 1] [2, 2, 1, 0, 2, 2, 1] 3 1 true = ([2, 2, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_1122211 : fieldCube 7 5 20 [2, 2, 2, 0, 1, 0, 2] = [2, 0, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_1122211 : fieldMul 7 5 20 [2, 0, 1, 2, 2, 0, 2] [1, 1, 2, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122211 : mirrorTrits [2, 0, 1, 2, 2, 0, 2] = [1, 0, 2, 1, 1, 0, 1] := by
  decide

theorem demoInv_1122211 : specInv 7 5 20 [1, 1, 2, 2, 2, 1, 1] = some [1, 0, 2, 1, 1, 0, 1] :=
  specInv_mirror_7 [1, 1, 2, 2, 2, 1, 1] [2, 2, 1, 0, 2, 2, 1] [2, 2, 2, 0, 1, 0, 2] [2, 0, 1, 2, 2, 0, 2] [1, 0, 2, 1, 1, 0, 1] demoR1_1122211 demoR2_1122211 demoC_1122211 demoM_1122211 demoMir_1122211

theorem demoR1_2122211 : invRung 7 5 20 [2, 1, 2, 2, 2, 1, 1] [2, 1, 2, 2, 2, 1, 1] 1 2 false = ([0, 1, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2122211 : invRung 7 5 20 [2, 1, 2, 2, 2, 1, 1] [0, 1, 2, 0, 2, 0, 2] 3 1 true = ([2, 0, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_2122211 : fieldCube 7 5 20 [2, 0, 2, 1, 2, 0, 0] = [0, 2, 1, 2, 0, 0, 1] := by
  decide

theorem demoM_2122211 : fieldMul 7 5 20 [0, 2, 1, 2, 0, 0, 1] [2, 1, 2, 2, 2, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2122211 : specInv 7 5 20 [2, 1, 2, 2, 2, 1, 1] = some [0, 2, 1, 2, 0, 0, 1] :=
  specInv_white_7 [2, 1, 2, 2, 2, 1, 1] [0, 1, 2, 0, 2, 0, 2] [2, 0, 2, 1, 2, 0, 0] [0, 2, 1, 2, 0, 0, 1] demoR1_2122211 demoR2_2122211 demoC_2122211 demoM_2122211

theorem demoR1_0222211 : invRung 7 5 20 [0, 2, 2, 2, 2, 1, 1] [0, 2, 2, 2, 2, 1, 1] 1 2 false = ([0, 2, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_0222211 : invRung 7 5 20 [0, 2, 2, 2, 2, 1, 1] [0, 2, 1, 2, 0, 2, 0] 3 1 true = ([1, 1, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0222211 : fieldCube 7 5 20 [1, 1, 2, 1, 0, 0, 1] = [2, 1, 0, 2, 1, 2, 0] := by
  decide

theorem demoM_0222211 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 2, 0] [0, 2, 2, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222211 : mirrorTrits [2, 1, 0, 2, 1, 2, 0] = [1, 2, 0, 1, 2, 1, 0] := by
  decide

theorem demoInv_0222211 : specInv 7 5 20 [0, 2, 2, 2, 2, 1, 1] = some [1, 2, 0, 1, 2, 1, 0] :=
  specInv_mirror_7 [0, 2, 2, 2, 2, 1, 1] [0, 2, 1, 2, 0, 2, 0] [1, 1, 2, 1, 0, 0, 1] [2, 1, 0, 2, 1, 2, 0] [1, 2, 0, 1, 2, 1, 0] demoR1_0222211 demoR2_0222211 demoC_0222211 demoM_0222211 demoMir_0222211

theorem demoR1_1222211 : invRung 7 5 20 [1, 2, 2, 2, 2, 1, 1] [1, 2, 2, 2, 2, 1, 1] 1 2 false = ([2, 2, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1222211 : invRung 7 5 20 [1, 2, 2, 2, 2, 1, 1] [2, 2, 0, 0, 1, 0, 0] 3 1 true = ([0, 0, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_1222211 : fieldCube 7 5 20 [0, 0, 1, 1, 1, 0, 0] = [1, 1, 1, 1, 0, 2, 2] := by
  decide

theorem demoM_1222211 : fieldMul 7 5 20 [1, 1, 1, 1, 0, 2, 2] [1, 2, 2, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222211 : mirrorTrits [1, 1, 1, 1, 0, 2, 2] = [2, 2, 2, 2, 0, 1, 1] := by
  decide

theorem demoInv_1222211 : specInv 7 5 20 [1, 2, 2, 2, 2, 1, 1] = some [2, 2, 2, 2, 0, 1, 1] :=
  specInv_mirror_7 [1, 2, 2, 2, 2, 1, 1] [2, 2, 0, 0, 1, 0, 0] [0, 0, 1, 1, 1, 0, 0] [1, 1, 1, 1, 0, 2, 2] [2, 2, 2, 2, 0, 1, 1] demoR1_1222211 demoR2_1222211 demoC_1222211 demoM_1222211 demoMir_1222211

theorem demoR1_2222211 : invRung 7 5 20 [2, 2, 2, 2, 2, 1, 1] [2, 2, 2, 2, 2, 1, 1] 1 2 false = ([2, 2, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_2222211 : invRung 7 5 20 [2, 2, 2, 2, 2, 1, 1] [2, 2, 0, 2, 0, 1, 2] 3 1 true = ([0, 0, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_2222211 : fieldCube 7 5 20 [0, 0, 2, 0, 0, 2, 2] = [2, 1, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_2222211 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 1, 2] [2, 2, 2, 2, 2, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222211 : mirrorTrits [2, 1, 0, 2, 1, 1, 2] = [1, 2, 0, 1, 2, 2, 1] := by
  decide

theorem demoInv_2222211 : specInv 7 5 20 [2, 2, 2, 2, 2, 1, 1] = some [1, 2, 0, 1, 2, 2, 1] :=
  specInv_mirror_7 [2, 2, 2, 2, 2, 1, 1] [2, 2, 0, 2, 0, 1, 2] [0, 0, 2, 0, 0, 2, 2] [2, 1, 0, 2, 1, 1, 2] [1, 2, 0, 1, 2, 2, 1] demoR1_2222211 demoR2_2222211 demoC_2222211 demoM_2222211 demoMir_2222211

theorem demoR1_0000021 : invRung 7 5 20 [0, 0, 0, 0, 0, 2, 1] [0, 0, 0, 0, 0, 2, 1] 1 2 false = ([2, 1, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0000021 : invRung 7 5 20 [0, 0, 0, 0, 0, 2, 1] [2, 1, 1, 0, 2, 1, 2] 3 1 true = ([0, 1, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0000021 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 2, 1] = [1, 1, 0, 0, 0, 0, 0] := by
  decide

theorem demoM_0000021 : fieldMul 7 5 20 [1, 1, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0000021 : specInv 7 5 20 [0, 0, 0, 0, 0, 2, 1] = some [1, 1, 0, 0, 0, 0, 0] :=
  specInv_white_7 [0, 0, 0, 0, 0, 2, 1] [2, 1, 1, 0, 2, 1, 2] [0, 1, 0, 2, 1, 2, 1] [1, 1, 0, 0, 0, 0, 0] demoR1_0000021 demoR2_0000021 demoC_0000021 demoM_0000021

theorem demoR1_1000021 : invRung 7 5 20 [1, 0, 0, 0, 0, 2, 1] [1, 0, 0, 0, 0, 2, 1] 1 2 false = ([1, 1, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_1000021 : invRung 7 5 20 [1, 0, 0, 0, 0, 2, 1] [1, 1, 2, 2, 1, 0, 0] 3 1 true = ([0, 2, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_1000021 : fieldCube 7 5 20 [0, 2, 0, 2, 0, 2, 1] = [1, 0, 0, 0, 0, 2, 2] := by
  decide

theorem demoM_1000021 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 2, 2] [1, 0, 0, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1000021 : specInv 7 5 20 [1, 0, 0, 0, 0, 2, 1] = some [1, 0, 0, 0, 0, 2, 2] :=
  specInv_white_7 [1, 0, 0, 0, 0, 2, 1] [1, 1, 2, 2, 1, 0, 0] [0, 2, 0, 2, 0, 2, 1] [1, 0, 0, 0, 0, 2, 2] demoR1_1000021 demoR2_1000021 demoC_1000021 demoM_1000021

theorem demoR1_2000021 : invRung 7 5 20 [2, 0, 0, 0, 0, 2, 1] [2, 0, 0, 0, 0, 2, 1] 1 2 false = ([1, 2, 0, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_2000021 : invRung 7 5 20 [2, 0, 0, 0, 0, 2, 1] [1, 2, 0, 1, 1, 0, 1] 3 1 true = ([0, 1, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2000021 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 1, 1] = [1, 0, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_2000021 : fieldMul 7 5 20 [1, 0, 0, 0, 2, 0, 1] [2, 0, 0, 0, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000021 : mirrorTrits [1, 0, 0, 0, 2, 0, 1] = [2, 0, 0, 0, 1, 0, 2] := by
  decide

theorem demoInv_2000021 : specInv 7 5 20 [2, 0, 0, 0, 0, 2, 1] = some [2, 0, 0, 0, 1, 0, 2] :=
  specInv_mirror_7 [2, 0, 0, 0, 0, 2, 1] [1, 2, 0, 1, 1, 0, 1] [0, 1, 0, 0, 1, 1, 1] [1, 0, 0, 0, 2, 0, 1] [2, 0, 0, 0, 1, 0, 2] demoR1_2000021 demoR2_2000021 demoC_2000021 demoM_2000021 demoMir_2000021

theorem demoR1_0100021 : invRung 7 5 20 [0, 1, 0, 0, 0, 2, 1] [0, 1, 0, 0, 0, 2, 1] 1 2 false = ([0, 2, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0100021 : invRung 7 5 20 [0, 1, 0, 0, 0, 2, 1] [0, 2, 2, 0, 2, 1, 2] 3 1 true = ([0, 1, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_0100021 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 1, 0] = [1, 1, 1, 1, 1, 1, 2] := by
  decide

theorem demoM_0100021 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 1, 2] [0, 1, 0, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0100021 : specInv 7 5 20 [0, 1, 0, 0, 0, 2, 1] = some [1, 1, 1, 1, 1, 1, 2] :=
  specInv_white_7 [0, 1, 0, 0, 0, 2, 1] [0, 2, 2, 0, 2, 1, 2] [0, 1, 0, 0, 0, 1, 0] [1, 1, 1, 1, 1, 1, 2] demoR1_0100021 demoR2_0100021 demoC_0100021 demoM_0100021

theorem demoR1_1100021 : invRung 7 5 20 [1, 1, 0, 0, 0, 2, 1] [1, 1, 0, 0, 0, 2, 1] 1 2 false = ([1, 0, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1100021 : invRung 7 5 20 [1, 1, 0, 0, 0, 2, 1] [1, 0, 1, 2, 2, 1, 0] 3 1 true = ([2, 2, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_1100021 : fieldCube 7 5 20 [2, 2, 2, 1, 2, 0, 0] = [0, 2, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_1100021 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 0, 1] [1, 1, 0, 0, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1100021 : mirrorTrits [0, 2, 1, 1, 0, 0, 1] = [0, 1, 2, 2, 0, 0, 2] := by
  decide

theorem demoInv_1100021 : specInv 7 5 20 [1, 1, 0, 0, 0, 2, 1] = some [0, 1, 2, 2, 0, 0, 2] :=
  specInv_mirror_7 [1, 1, 0, 0, 0, 2, 1] [1, 0, 1, 2, 2, 1, 0] [2, 2, 2, 1, 2, 0, 0] [0, 2, 1, 1, 0, 0, 1] [0, 1, 2, 2, 0, 0, 2] demoR1_1100021 demoR2_1100021 demoC_1100021 demoM_1100021 demoMir_1100021

theorem demoR1_2100021 : invRung 7 5 20 [2, 1, 0, 0, 0, 2, 1] [2, 1, 0, 0, 0, 2, 1] 1 2 false = ([2, 1, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_2100021 : invRung 7 5 20 [2, 1, 0, 0, 0, 2, 1] [2, 1, 2, 0, 0, 1, 1] 3 1 true = ([0, 1, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_2100021 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 2, 0] = [0, 0, 0, 2, 2, 1, 1] := by
  decide

theorem demoM_2100021 : fieldMul 7 5 20 [0, 0, 0, 2, 2, 1, 1] [2, 1, 0, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2100021 : specInv 7 5 20 [2, 1, 0, 0, 0, 2, 1] = some [0, 0, 0, 2, 2, 1, 1] :=
  specInv_white_7 [2, 1, 0, 0, 0, 2, 1] [2, 1, 2, 0, 0, 1, 1] [0, 1, 2, 1, 1, 2, 0] [0, 0, 0, 2, 2, 1, 1] demoR1_2100021 demoR2_2100021 demoC_2100021 demoM_2100021

theorem demoR1_0200021 : invRung 7 5 20 [0, 2, 0, 0, 0, 2, 1] [0, 2, 0, 0, 0, 2, 1] 1 2 false = ([1, 0, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_0200021 : invRung 7 5 20 [0, 2, 0, 0, 0, 2, 1] [1, 0, 2, 1, 1, 1, 0] 3 1 true = ([1, 2, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_0200021 : fieldCube 7 5 20 [1, 2, 2, 0, 1, 1, 0] = [2, 2, 1, 0, 1, 2, 2] := by
  decide

theorem demoM_0200021 : fieldMul 7 5 20 [2, 2, 1, 0, 1, 2, 2] [0, 2, 0, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0200021 : specInv 7 5 20 [0, 2, 0, 0, 0, 2, 1] = some [2, 2, 1, 0, 1, 2, 2] :=
  specInv_white_7 [0, 2, 0, 0, 0, 2, 1] [1, 0, 2, 1, 1, 1, 0] [1, 2, 2, 0, 1, 1, 0] [2, 2, 1, 0, 1, 2, 2] demoR1_0200021 demoR2_0200021 demoC_0200021 demoM_0200021

theorem demoR1_1200021 : invRung 7 5 20 [1, 2, 0, 0, 0, 2, 1] [1, 2, 0, 0, 0, 2, 1] 1 2 false = ([1, 0, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_1200021 : invRung 7 5 20 [1, 2, 0, 0, 0, 2, 1] [1, 0, 2, 1, 1, 1, 2] 3 1 true = ([2, 0, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_1200021 : fieldCube 7 5 20 [2, 0, 2, 0, 1, 0, 2] = [2, 0, 1, 0, 2, 0, 2] := by
  decide

theorem demoM_1200021 : fieldMul 7 5 20 [2, 0, 1, 0, 2, 0, 2] [1, 2, 0, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1200021 : specInv 7 5 20 [1, 2, 0, 0, 0, 2, 1] = some [2, 0, 1, 0, 2, 0, 2] :=
  specInv_white_7 [1, 2, 0, 0, 0, 2, 1] [1, 0, 2, 1, 1, 1, 2] [2, 0, 2, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0, 2] demoR1_1200021 demoR2_1200021 demoC_1200021 demoM_1200021

theorem demoR1_2200021 : invRung 7 5 20 [2, 2, 0, 0, 0, 2, 1] [2, 2, 0, 0, 0, 2, 1] 1 2 false = ([0, 2, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2200021 : invRung 7 5 20 [2, 2, 0, 0, 0, 2, 1] [0, 2, 0, 2, 2, 0, 1] 3 1 true = ([0, 1, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_2200021 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 1, 0] = [0, 0, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_2200021 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 2, 1] [2, 2, 0, 0, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200021 : mirrorTrits [0, 0, 0, 0, 1, 2, 1] = [0, 0, 0, 0, 2, 1, 2] := by
  decide

theorem demoInv_2200021 : specInv 7 5 20 [2, 2, 0, 0, 0, 2, 1] = some [0, 0, 0, 0, 2, 1, 2] :=
  specInv_mirror_7 [2, 2, 0, 0, 0, 2, 1] [0, 2, 0, 2, 2, 0, 1] [0, 1, 0, 2, 2, 1, 0] [0, 0, 0, 0, 1, 2, 1] [0, 0, 0, 0, 2, 1, 2] demoR1_2200021 demoR2_2200021 demoC_2200021 demoM_2200021 demoMir_2200021

theorem demoR1_0010021 : invRung 7 5 20 [0, 0, 1, 0, 0, 2, 1] [0, 0, 1, 0, 0, 2, 1] 1 2 false = ([1, 1, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_0010021 : invRung 7 5 20 [0, 0, 1, 0, 0, 2, 1] [1, 1, 2, 2, 1, 0, 2] 3 1 true = ([2, 1, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0010021 : fieldCube 7 5 20 [2, 1, 2, 0, 2, 0, 1] = [2, 0, 2, 1, 1, 0, 2] := by
  decide

theorem demoM_0010021 : fieldMul 7 5 20 [2, 0, 2, 1, 1, 0, 2] [0, 0, 1, 0, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010021 : mirrorTrits [2, 0, 2, 1, 1, 0, 2] = [1, 0, 1, 2, 2, 0, 1] := by
  decide

theorem demoInv_0010021 : specInv 7 5 20 [0, 0, 1, 0, 0, 2, 1] = some [1, 0, 1, 2, 2, 0, 1] :=
  specInv_mirror_7 [0, 0, 1, 0, 0, 2, 1] [1, 1, 2, 2, 1, 0, 2] [2, 1, 2, 0, 2, 0, 1] [2, 0, 2, 1, 1, 0, 2] [1, 0, 1, 2, 2, 0, 1] demoR1_0010021 demoR2_0010021 demoC_0010021 demoM_0010021 demoMir_0010021

theorem demoR1_1010021 : invRung 7 5 20 [1, 0, 1, 0, 0, 2, 1] [1, 0, 1, 0, 0, 2, 1] 1 2 false = ([0, 2, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_1010021 : invRung 7 5 20 [1, 0, 1, 0, 0, 2, 1] [0, 2, 2, 0, 1, 2, 0] 3 1 true = ([2, 0, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_1010021 : fieldCube 7 5 20 [2, 0, 0, 1, 2, 1, 1] = [1, 1, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_1010021 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 2, 2] [1, 0, 1, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1010021 : specInv 7 5 20 [1, 0, 1, 0, 0, 2, 1] = some [1, 1, 1, 0, 2, 2, 2] :=
  specInv_white_7 [1, 0, 1, 0, 0, 2, 1] [0, 2, 2, 0, 1, 2, 0] [2, 0, 0, 1, 2, 1, 1] [1, 1, 1, 0, 2, 2, 2] demoR1_1010021 demoR2_1010021 demoC_1010021 demoM_1010021

theorem demoR1_2010021 : invRung 7 5 20 [2, 0, 1, 0, 0, 2, 1] [2, 0, 1, 0, 0, 2, 1] 1 2 false = ([0, 0, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2010021 : invRung 7 5 20 [2, 0, 1, 0, 0, 2, 1] [0, 0, 2, 0, 1, 1, 2] 3 1 true = ([0, 1, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_2010021 : fieldCube 7 5 20 [0, 1, 0, 1, 1, 1, 2] = [2, 1, 0, 1, 0, 2, 2] := by
  decide

theorem demoM_2010021 : fieldMul 7 5 20 [2, 1, 0, 1, 0, 2, 2] [2, 0, 1, 0, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010021 : mirrorTrits [2, 1, 0, 1, 0, 2, 2] = [1, 2, 0, 2, 0, 1, 1] := by
  decide

theorem demoInv_2010021 : specInv 7 5 20 [2, 0, 1, 0, 0, 2, 1] = some [1, 2, 0, 2, 0, 1, 1] :=
  specInv_mirror_7 [2, 0, 1, 0, 0, 2, 1] [0, 0, 2, 0, 1, 1, 2] [0, 1, 0, 1, 1, 1, 2] [2, 1, 0, 1, 0, 2, 2] [1, 2, 0, 2, 0, 1, 1] demoR1_2010021 demoR2_2010021 demoC_2010021 demoM_2010021 demoMir_2010021

theorem demoR1_0110021 : invRung 7 5 20 [0, 1, 1, 0, 0, 2, 1] [0, 1, 1, 0, 0, 2, 1] 1 2 false = ([1, 0, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_0110021 : invRung 7 5 20 [0, 1, 1, 0, 0, 2, 1] [1, 0, 1, 0, 2, 0, 0] 3 1 true = ([0, 2, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_0110021 : fieldCube 7 5 20 [0, 2, 1, 0, 2, 2, 1] = [2, 2, 1, 2, 0, 2, 2] := by
  decide

theorem demoM_0110021 : fieldMul 7 5 20 [2, 2, 1, 2, 0, 2, 2] [0, 1, 1, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0110021 : specInv 7 5 20 [0, 1, 1, 0, 0, 2, 1] = some [2, 2, 1, 2, 0, 2, 2] :=
  specInv_white_7 [0, 1, 1, 0, 0, 2, 1] [1, 0, 1, 0, 2, 0, 0] [0, 2, 1, 0, 2, 2, 1] [2, 2, 1, 2, 0, 2, 2] demoR1_0110021 demoR2_0110021 demoC_0110021 demoM_0110021

theorem demoR1_1110021 : invRung 7 5 20 [1, 1, 1, 0, 0, 2, 1] [1, 1, 1, 0, 0, 2, 1] 1 2 false = ([2, 1, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1110021 : invRung 7 5 20 [1, 1, 1, 0, 0, 2, 1] [2, 1, 0, 0, 1, 1, 0] 3 1 true = ([0, 2, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_1110021 : fieldCube 7 5 20 [0, 2, 0, 2, 1, 2, 0] = [1, 0, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_1110021 : fieldMul 7 5 20 [1, 0, 1, 0, 2, 2, 2] [1, 1, 1, 0, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1110021 : mirrorTrits [1, 0, 1, 0, 2, 2, 2] = [2, 0, 2, 0, 1, 1, 1] := by
  decide

theorem demoInv_1110021 : specInv 7 5 20 [1, 1, 1, 0, 0, 2, 1] = some [2, 0, 2, 0, 1, 1, 1] :=
  specInv_mirror_7 [1, 1, 1, 0, 0, 2, 1] [2, 1, 0, 0, 1, 1, 0] [0, 2, 0, 2, 1, 2, 0] [1, 0, 1, 0, 2, 2, 2] [2, 0, 2, 0, 1, 1, 1] demoR1_1110021 demoR2_1110021 demoC_1110021 demoM_1110021 demoMir_1110021

theorem demoR1_2110021 : invRung 7 5 20 [2, 1, 1, 0, 0, 2, 1] [2, 1, 1, 0, 0, 2, 1] 1 2 false = ([0, 1, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_2110021 : invRung 7 5 20 [2, 1, 1, 0, 0, 2, 1] [0, 1, 1, 1, 0, 1, 1] 3 1 true = ([0, 0, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_2110021 : fieldCube 7 5 20 [0, 0, 1, 1, 1, 2, 0] = [0, 0, 0, 1, 2, 1, 0] := by
  decide

theorem demoM_2110021 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 1, 0] [2, 1, 1, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2110021 : specInv 7 5 20 [2, 1, 1, 0, 0, 2, 1] = some [0, 0, 0, 1, 2, 1, 0] :=
  specInv_white_7 [2, 1, 1, 0, 0, 2, 1] [0, 1, 1, 1, 0, 1, 1] [0, 0, 1, 1, 1, 2, 0] [0, 0, 0, 1, 2, 1, 0] demoR1_2110021 demoR2_2110021 demoC_2110021 demoM_2110021

theorem demoR1_0210021 : invRung 7 5 20 [0, 2, 1, 0, 0, 2, 1] [0, 2, 1, 0, 0, 2, 1] 1 2 false = ([2, 1, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_0210021 : invRung 7 5 20 [0, 2, 1, 0, 0, 2, 1] [2, 1, 0, 2, 2, 1, 2] 3 1 true = ([0, 1, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_0210021 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 1, 2] = [1, 1, 2, 1, 0, 1, 2] := by
  decide

theorem demoM_0210021 : fieldMul 7 5 20 [1, 1, 2, 1, 0, 1, 2] [0, 2, 1, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0210021 : specInv 7 5 20 [0, 2, 1, 0, 0, 2, 1] = some [1, 1, 2, 1, 0, 1, 2] :=
  specInv_white_7 [0, 2, 1, 0, 0, 2, 1] [2, 1, 0, 2, 2, 1, 2] [0, 1, 0, 0, 1, 1, 2] [1, 1, 2, 1, 0, 1, 2] demoR1_0210021 demoR2_0210021 demoC_0210021 demoM_0210021

theorem demoR1_1210021 : invRung 7 5 20 [1, 2, 1, 0, 0, 2, 1] [1, 2, 1, 0, 0, 2, 1] 1 2 false = ([2, 0, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_1210021 : invRung 7 5 20 [1, 2, 1, 0, 0, 2, 1] [2, 0, 1, 2, 2, 0, 2] 3 1 true = ([1, 0, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1210021 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 2, 1] = [1, 0, 2, 1, 0, 1, 2] := by
  decide

theorem demoM_1210021 : fieldMul 7 5 20 [1, 0, 2, 1, 0, 1, 2] [1, 2, 1, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1210021 : specInv 7 5 20 [1, 2, 1, 0, 0, 2, 1] = some [1, 0, 2, 1, 0, 1, 2] :=
  specInv_white_7 [1, 2, 1, 0, 0, 2, 1] [2, 0, 1, 2, 2, 0, 2] [1, 0, 0, 1, 0, 2, 1] [1, 0, 2, 1, 0, 1, 2] demoR1_1210021 demoR2_1210021 demoC_1210021 demoM_1210021

theorem demoR1_2210021 : invRung 7 5 20 [2, 2, 1, 0, 0, 2, 1] [2, 2, 1, 0, 0, 2, 1] 1 2 false = ([1, 0, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2210021 : invRung 7 5 20 [2, 2, 1, 0, 0, 2, 1] [1, 0, 0, 2, 2, 0, 0] 3 1 true = ([2, 1, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_2210021 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 0, 1] = [0, 1, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_2210021 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 2, 2] [2, 2, 1, 0, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210021 : mirrorTrits [0, 1, 0, 2, 1, 2, 2] = [0, 2, 0, 1, 2, 1, 1] := by
  decide

theorem demoInv_2210021 : specInv 7 5 20 [2, 2, 1, 0, 0, 2, 1] = some [0, 2, 0, 1, 2, 1, 1] :=
  specInv_mirror_7 [2, 2, 1, 0, 0, 2, 1] [1, 0, 0, 2, 2, 0, 0] [2, 1, 1, 1, 0, 0, 1] [0, 1, 0, 2, 1, 2, 2] [0, 2, 0, 1, 2, 1, 1] demoR1_2210021 demoR2_2210021 demoC_2210021 demoM_2210021 demoMir_2210021

theorem demoR1_0020021 : invRung 7 5 20 [0, 0, 2, 0, 0, 2, 1] [0, 0, 2, 0, 0, 2, 1] 1 2 false = ([1, 0, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0020021 : invRung 7 5 20 [0, 0, 2, 0, 0, 2, 1] [1, 0, 1, 2, 1, 2, 1] 3 1 true = ([2, 0, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_0020021 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 1, 1] = [2, 0, 2, 2, 2, 2, 0] := by
  decide

theorem demoM_0020021 : fieldMul 7 5 20 [2, 0, 2, 2, 2, 2, 0] [0, 0, 2, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0020021 : specInv 7 5 20 [0, 0, 2, 0, 0, 2, 1] = some [2, 0, 2, 2, 2, 2, 0] :=
  specInv_white_7 [0, 0, 2, 0, 0, 2, 1] [1, 0, 1, 2, 1, 2, 1] [2, 0, 2, 2, 1, 1, 1] [2, 0, 2, 2, 2, 2, 0] demoR1_0020021 demoR2_0020021 demoC_0020021 demoM_0020021

theorem demoR1_1020021 : invRung 7 5 20 [1, 0, 2, 0, 0, 2, 1] [1, 0, 2, 0, 0, 2, 1] 1 2 false = ([2, 2, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1020021 : invRung 7 5 20 [1, 0, 2, 0, 0, 2, 1] [2, 2, 1, 2, 2, 1, 1] 3 1 true = ([0, 1, 2, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_1020021 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 0, 1] = [1, 2, 0, 0, 1, 0, 1] := by
  decide

theorem demoM_1020021 : fieldMul 7 5 20 [1, 2, 0, 0, 1, 0, 1] [1, 0, 2, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1020021 : specInv 7 5 20 [1, 0, 2, 0, 0, 2, 1] = some [1, 2, 0, 0, 1, 0, 1] :=
  specInv_white_7 [1, 0, 2, 0, 0, 2, 1] [2, 2, 1, 2, 2, 1, 1] [0, 1, 2, 1, 1, 0, 1] [1, 2, 0, 0, 1, 0, 1] demoR1_1020021 demoR2_1020021 demoC_1020021 demoM_1020021

theorem demoR1_2020021 : invRung 7 5 20 [2, 0, 2, 0, 0, 2, 1] [2, 0, 2, 0, 0, 2, 1] 1 2 false = ([1, 0, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2020021 : invRung 7 5 20 [2, 0, 2, 0, 0, 2, 1] [1, 0, 1, 0, 2, 2, 0] 3 1 true = ([0, 0, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_2020021 : fieldCube 7 5 20 [0, 0, 0, 1, 1, 0, 0] = [1, 1, 1, 1, 0, 2, 1] := by
  decide

theorem demoM_2020021 : fieldMul 7 5 20 [1, 1, 1, 1, 0, 2, 1] [2, 0, 2, 0, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020021 : mirrorTrits [1, 1, 1, 1, 0, 2, 1] = [2, 2, 2, 2, 0, 1, 2] := by
  decide

theorem demoInv_2020021 : specInv 7 5 20 [2, 0, 2, 0, 0, 2, 1] = some [2, 2, 2, 2, 0, 1, 2] :=
  specInv_mirror_7 [2, 0, 2, 0, 0, 2, 1] [1, 0, 1, 0, 2, 2, 0] [0, 0, 0, 1, 1, 0, 0] [1, 1, 1, 1, 0, 2, 1] [2, 2, 2, 2, 0, 1, 2] demoR1_2020021 demoR2_2020021 demoC_2020021 demoM_2020021 demoMir_2020021

theorem demoR1_0120021 : invRung 7 5 20 [0, 1, 2, 0, 0, 2, 1] [0, 1, 2, 0, 0, 2, 1] 1 2 false = ([0, 2, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0120021 : invRung 7 5 20 [0, 1, 2, 0, 0, 2, 1] [0, 2, 0, 0, 2, 1, 2] 3 1 true = ([0, 0, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_0120021 : fieldCube 7 5 20 [0, 0, 2, 2, 0, 2, 0] = [1, 2, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_0120021 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 1, 0] [0, 1, 2, 0, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0120021 : mirrorTrits [1, 2, 1, 0, 2, 1, 0] = [2, 1, 2, 0, 1, 2, 0] := by
  decide

theorem demoInv_0120021 : specInv 7 5 20 [0, 1, 2, 0, 0, 2, 1] = some [2, 1, 2, 0, 1, 2, 0] :=
  specInv_mirror_7 [0, 1, 2, 0, 0, 2, 1] [0, 2, 0, 0, 2, 1, 2] [0, 0, 2, 2, 0, 2, 0] [1, 2, 1, 0, 2, 1, 0] [2, 1, 2, 0, 1, 2, 0] demoR1_0120021 demoR2_0120021 demoC_0120021 demoM_0120021 demoMir_0120021

theorem demoR1_1120021 : invRung 7 5 20 [1, 1, 2, 0, 0, 2, 1] [1, 1, 2, 0, 0, 2, 1] 1 2 false = ([0, 0, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_1120021 : invRung 7 5 20 [1, 1, 2, 0, 0, 2, 1] [0, 0, 0, 1, 0, 0, 0] 3 1 true = ([2, 2, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_1120021 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 0, 1] = [2, 0, 2, 2, 1, 0, 1] := by
  decide

theorem demoM_1120021 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 0, 1] [1, 1, 2, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1120021 : specInv 7 5 20 [1, 1, 2, 0, 0, 2, 1] = some [2, 0, 2, 2, 1, 0, 1] :=
  specInv_white_7 [1, 1, 2, 0, 0, 2, 1] [0, 0, 0, 1, 0, 0, 0] [2, 2, 1, 0, 2, 0, 1] [2, 0, 2, 2, 1, 0, 1] demoR1_1120021 demoR2_1120021 demoC_1120021 demoM_1120021

theorem demoR1_2120021 : invRung 7 5 20 [2, 1, 2, 0, 0, 2, 1] [2, 1, 2, 0, 0, 2, 1] 1 2 false = ([0, 2, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_2120021 : invRung 7 5 20 [2, 1, 2, 0, 0, 2, 1] [0, 2, 2, 2, 0, 0, 0] 3 1 true = ([1, 0, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2120021 : fieldCube 7 5 20 [1, 0, 2, 1, 2, 1, 0] = [0, 0, 2, 2, 1, 1, 0] := by
  decide

theorem demoM_2120021 : fieldMul 7 5 20 [0, 0, 2, 2, 1, 1, 0] [2, 1, 2, 0, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120021 : mirrorTrits [0, 0, 2, 2, 1, 1, 0] = [0, 0, 1, 1, 2, 2, 0] := by
  decide

theorem demoInv_2120021 : specInv 7 5 20 [2, 1, 2, 0, 0, 2, 1] = some [0, 0, 1, 1, 2, 2, 0] :=
  specInv_mirror_7 [2, 1, 2, 0, 0, 2, 1] [0, 2, 2, 2, 0, 0, 0] [1, 0, 2, 1, 2, 1, 0] [0, 0, 2, 2, 1, 1, 0] [0, 0, 1, 1, 2, 2, 0] demoR1_2120021 demoR2_2120021 demoC_2120021 demoM_2120021 demoMir_2120021

theorem demoR1_0220021 : invRung 7 5 20 [0, 2, 2, 0, 0, 2, 1] [0, 2, 2, 0, 0, 2, 1] 1 2 false = ([1, 2, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0220021 : invRung 7 5 20 [0, 2, 2, 0, 0, 2, 1] [1, 2, 0, 2, 2, 2, 1] 3 1 true = ([0, 0, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0220021 : fieldCube 7 5 20 [0, 0, 1, 1, 0, 1, 1] = [2, 2, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_0220021 : fieldMul 7 5 20 [2, 2, 1, 1, 2, 0, 1] [0, 2, 2, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0220021 : specInv 7 5 20 [0, 2, 2, 0, 0, 2, 1] = some [2, 2, 1, 1, 2, 0, 1] :=
  specInv_white_7 [0, 2, 2, 0, 0, 2, 1] [1, 2, 0, 2, 2, 2, 1] [0, 0, 1, 1, 0, 1, 1] [2, 2, 1, 1, 2, 0, 1] demoR1_0220021 demoR2_0220021 demoC_0220021 demoM_0220021

theorem demoR1_1220021 : invRung 7 5 20 [1, 2, 2, 0, 0, 2, 1] [1, 2, 2, 0, 0, 2, 1] 1 2 false = ([0, 0, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_1220021 : invRung 7 5 20 [1, 2, 2, 0, 0, 2, 1] [0, 0, 0, 2, 2, 0, 1] 3 1 true = ([1, 1, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1220021 : fieldCube 7 5 20 [1, 1, 1, 1, 2, 2, 0] = [1, 1, 0, 0, 2, 2, 1] := by
  decide

theorem demoM_1220021 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 2, 1] [1, 2, 2, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1220021 : specInv 7 5 20 [1, 2, 2, 0, 0, 2, 1] = some [1, 1, 0, 0, 2, 2, 1] :=
  specInv_white_7 [1, 2, 2, 0, 0, 2, 1] [0, 0, 0, 2, 2, 0, 1] [1, 1, 1, 1, 2, 2, 0] [1, 1, 0, 0, 2, 2, 1] demoR1_1220021 demoR2_1220021 demoC_1220021 demoM_1220021

theorem demoR1_2220021 : invRung 7 5 20 [2, 2, 2, 0, 0, 2, 1] [2, 2, 2, 0, 0, 2, 1] 1 2 false = ([1, 1, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_2220021 : invRung 7 5 20 [2, 2, 2, 0, 0, 2, 1] [1, 1, 1, 1, 1, 1, 0] 3 1 true = ([0, 1, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_2220021 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 2, 1] = [2, 1, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_2220021 : fieldMul 7 5 20 [2, 1, 1, 0, 0, 1, 0] [2, 2, 2, 0, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2220021 : specInv 7 5 20 [2, 2, 2, 0, 0, 2, 1] = some [2, 1, 1, 0, 0, 1, 0] :=
  specInv_white_7 [2, 2, 2, 0, 0, 2, 1] [1, 1, 1, 1, 1, 1, 0] [0, 1, 0, 0, 1, 2, 1] [2, 1, 1, 0, 0, 1, 0] demoR1_2220021 demoR2_2220021 demoC_2220021 demoM_2220021

theorem demoR1_0001021 : invRung 7 5 20 [0, 0, 0, 1, 0, 2, 1] [0, 0, 0, 1, 0, 2, 1] 1 2 false = ([2, 1, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0001021 : invRung 7 5 20 [0, 0, 0, 1, 0, 2, 1] [2, 1, 0, 0, 2, 2, 2] 3 1 true = ([2, 1, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_0001021 : fieldCube 7 5 20 [2, 1, 2, 0, 0, 2, 2] = [1, 1, 0, 0, 1, 1, 2] := by
  decide

theorem demoM_0001021 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 1, 2] [0, 0, 0, 1, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001021 : mirrorTrits [1, 1, 0, 0, 1, 1, 2] = [2, 2, 0, 0, 2, 2, 1] := by
  decide

theorem demoInv_0001021 : specInv 7 5 20 [0, 0, 0, 1, 0, 2, 1] = some [2, 2, 0, 0, 2, 2, 1] :=
  specInv_mirror_7 [0, 0, 0, 1, 0, 2, 1] [2, 1, 0, 0, 2, 2, 2] [2, 1, 2, 0, 0, 2, 2] [1, 1, 0, 0, 1, 1, 2] [2, 2, 0, 0, 2, 2, 1] demoR1_0001021 demoR2_0001021 demoC_0001021 demoM_0001021 demoMir_0001021

theorem demoR1_1001021 : invRung 7 5 20 [1, 0, 0, 1, 0, 2, 1] [1, 0, 0, 1, 0, 2, 1] 1 2 false = ([1, 0, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1001021 : invRung 7 5 20 [1, 0, 0, 1, 0, 2, 1] [1, 0, 2, 0, 1, 1, 0] 3 1 true = ([0, 0, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_1001021 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 0, 2] = [2, 0, 0, 0, 2, 2, 1] := by
  decide

theorem demoM_1001021 : fieldMul 7 5 20 [2, 0, 0, 0, 2, 2, 1] [1, 0, 0, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1001021 : specInv 7 5 20 [1, 0, 0, 1, 0, 2, 1] = some [2, 0, 0, 0, 2, 2, 1] :=
  specInv_white_7 [1, 0, 0, 1, 0, 2, 1] [1, 0, 2, 0, 1, 1, 0] [0, 0, 1, 2, 1, 0, 2] [2, 0, 0, 0, 2, 2, 1] demoR1_1001021 demoR2_1001021 demoC_1001021 demoM_1001021

theorem demoR1_2001021 : invRung 7 5 20 [2, 0, 0, 1, 0, 2, 1] [2, 0, 0, 1, 0, 2, 1] 1 2 false = ([1, 2, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_2001021 : invRung 7 5 20 [2, 0, 0, 1, 0, 2, 1] [1, 2, 2, 2, 0, 2, 1] 3 1 true = ([0, 2, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_2001021 : fieldCube 7 5 20 [0, 2, 1, 1, 2, 2, 1] = [0, 2, 2, 2, 0, 0, 2] := by
  decide

theorem demoM_2001021 : fieldMul 7 5 20 [0, 2, 2, 2, 0, 0, 2] [2, 0, 0, 1, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001021 : mirrorTrits [0, 2, 2, 2, 0, 0, 2] = [0, 1, 1, 1, 0, 0, 1] := by
  decide

theorem demoInv_2001021 : specInv 7 5 20 [2, 0, 0, 1, 0, 2, 1] = some [0, 1, 1, 1, 0, 0, 1] :=
  specInv_mirror_7 [2, 0, 0, 1, 0, 2, 1] [1, 2, 2, 2, 0, 2, 1] [0, 2, 1, 1, 2, 2, 1] [0, 2, 2, 2, 0, 0, 2] [0, 1, 1, 1, 0, 0, 1] demoR1_2001021 demoR2_2001021 demoC_2001021 demoM_2001021 demoMir_2001021

theorem demoR1_0101021 : invRung 7 5 20 [0, 1, 0, 1, 0, 2, 1] [0, 1, 0, 1, 0, 2, 1] 1 2 false = ([1, 0, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0101021 : invRung 7 5 20 [0, 1, 0, 1, 0, 2, 1] [1, 0, 1, 1, 2, 1, 2] 3 1 true = ([2, 2, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0101021 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 0, 1] = [1, 2, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_0101021 : fieldMul 7 5 20 [1, 2, 1, 1, 1, 1, 1] [0, 1, 0, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0101021 : specInv 7 5 20 [0, 1, 0, 1, 0, 2, 1] = some [1, 2, 1, 1, 1, 1, 1] :=
  specInv_white_7 [0, 1, 0, 1, 0, 2, 1] [1, 0, 1, 1, 2, 1, 2] [2, 2, 2, 2, 1, 0, 1] [1, 2, 1, 1, 1, 1, 1] demoR1_0101021 demoR2_0101021 demoC_0101021 demoM_0101021

theorem demoR1_1101021 : invRung 7 5 20 [1, 1, 0, 1, 0, 2, 1] [1, 1, 0, 1, 0, 2, 1] 1 2 false = ([0, 0, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1101021 : invRung 7 5 20 [1, 1, 0, 1, 0, 2, 1] [0, 0, 1, 1, 1, 0, 0] 3 1 true = ([0, 0, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_1101021 : fieldCube 7 5 20 [0, 0, 2, 2, 2, 2, 1] = [1, 2, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_1101021 : fieldMul 7 5 20 [1, 2, 0, 0, 0, 1, 0] [1, 1, 0, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1101021 : specInv 7 5 20 [1, 1, 0, 1, 0, 2, 1] = some [1, 2, 0, 0, 0, 1, 0] :=
  specInv_white_7 [1, 1, 0, 1, 0, 2, 1] [0, 0, 1, 1, 1, 0, 0] [0, 0, 2, 2, 2, 2, 1] [1, 2, 0, 0, 0, 1, 0] demoR1_1101021 demoR2_1101021 demoC_1101021 demoM_1101021

theorem demoR1_2101021 : invRung 7 5 20 [2, 1, 0, 1, 0, 2, 1] [2, 1, 0, 1, 0, 2, 1] 1 2 false = ([2, 2, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_2101021 : invRung 7 5 20 [2, 1, 0, 1, 0, 2, 1] [2, 2, 1, 2, 0, 0, 1] 3 1 true = ([0, 0, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2101021 : fieldCube 7 5 20 [0, 0, 2, 0, 0, 1, 0] = [1, 1, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_2101021 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 1, 1] [2, 1, 0, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2101021 : specInv 7 5 20 [2, 1, 0, 1, 0, 2, 1] = some [1, 1, 1, 0, 1, 1, 1] :=
  specInv_white_7 [2, 1, 0, 1, 0, 2, 1] [2, 2, 1, 2, 0, 0, 1] [0, 0, 2, 0, 0, 1, 0] [1, 1, 1, 0, 1, 1, 1] demoR1_2101021 demoR2_2101021 demoC_2101021 demoM_2101021

theorem demoR1_0201021 : invRung 7 5 20 [0, 2, 0, 1, 0, 2, 1] [0, 2, 0, 1, 0, 2, 1] 1 2 false = ([0, 0, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_0201021 : invRung 7 5 20 [0, 2, 0, 1, 0, 2, 1] [0, 0, 1, 1, 0, 1, 1] 3 1 true = ([2, 0, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_0201021 : fieldCube 7 5 20 [2, 0, 2, 2, 2, 1, 1] = [2, 1, 2, 0, 2, 0, 1] := by
  decide

theorem demoM_0201021 : fieldMul 7 5 20 [2, 1, 2, 0, 2, 0, 1] [0, 2, 0, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0201021 : specInv 7 5 20 [0, 2, 0, 1, 0, 2, 1] = some [2, 1, 2, 0, 2, 0, 1] :=
  specInv_white_7 [0, 2, 0, 1, 0, 2, 1] [0, 0, 1, 1, 0, 1, 1] [2, 0, 2, 2, 2, 1, 1] [2, 1, 2, 0, 2, 0, 1] demoR1_0201021 demoR2_0201021 demoC_0201021 demoM_0201021

theorem demoR1_1201021 : invRung 7 5 20 [1, 2, 0, 1, 0, 2, 1] [1, 2, 0, 1, 0, 2, 1] 1 2 false = ([2, 2, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_1201021 : invRung 7 5 20 [1, 2, 0, 1, 0, 2, 1] [2, 2, 2, 2, 1, 2, 0] 3 1 true = ([1, 2, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_1201021 : fieldCube 7 5 20 [1, 2, 2, 0, 0, 2, 2] = [0, 1, 0, 1, 1, 1, 2] := by
  decide

theorem demoM_1201021 : fieldMul 7 5 20 [0, 1, 0, 1, 1, 1, 2] [1, 2, 0, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1201021 : specInv 7 5 20 [1, 2, 0, 1, 0, 2, 1] = some [0, 1, 0, 1, 1, 1, 2] :=
  specInv_white_7 [1, 2, 0, 1, 0, 2, 1] [2, 2, 2, 2, 1, 2, 0] [1, 2, 2, 0, 0, 2, 2] [0, 1, 0, 1, 1, 1, 2] demoR1_1201021 demoR2_1201021 demoC_1201021 demoM_1201021

theorem demoR1_2201021 : invRung 7 5 20 [2, 2, 0, 1, 0, 2, 1] [2, 2, 0, 1, 0, 2, 1] 1 2 false = ([0, 2, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2201021 : invRung 7 5 20 [2, 2, 0, 1, 0, 2, 1] [0, 2, 2, 0, 2, 0, 2] 3 1 true = ([2, 0, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_2201021 : fieldCube 7 5 20 [2, 0, 2, 1, 1, 2, 0] = [2, 0, 0, 1, 2, 1, 1] := by
  decide

theorem demoM_2201021 : fieldMul 7 5 20 [2, 0, 0, 1, 2, 1, 1] [2, 2, 0, 1, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2201021 : mirrorTrits [2, 0, 0, 1, 2, 1, 1] = [1, 0, 0, 2, 1, 2, 2] := by
  decide

theorem demoInv_2201021 : specInv 7 5 20 [2, 2, 0, 1, 0, 2, 1] = some [1, 0, 0, 2, 1, 2, 2] :=
  specInv_mirror_7 [2, 2, 0, 1, 0, 2, 1] [0, 2, 2, 0, 2, 0, 2] [2, 0, 2, 1, 1, 2, 0] [2, 0, 0, 1, 2, 1, 1] [1, 0, 0, 2, 1, 2, 2] demoR1_2201021 demoR2_2201021 demoC_2201021 demoM_2201021 demoMir_2201021

theorem demoR1_0011021 : invRung 7 5 20 [0, 0, 1, 1, 0, 2, 1] [0, 0, 1, 1, 0, 2, 1] 1 2 false = ([0, 1, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_0011021 : invRung 7 5 20 [0, 0, 1, 1, 0, 2, 1] [0, 1, 0, 2, 0, 0, 2] 3 1 true = ([1, 2, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_0011021 : fieldCube 7 5 20 [1, 2, 1, 1, 1, 1, 1] = [0, 0, 1, 1, 2, 1, 2] := by
  decide

theorem demoM_0011021 : fieldMul 7 5 20 [0, 0, 1, 1, 2, 1, 2] [0, 0, 1, 1, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011021 : mirrorTrits [0, 0, 1, 1, 2, 1, 2] = [0, 0, 2, 2, 1, 2, 1] := by
  decide

theorem demoInv_0011021 : specInv 7 5 20 [0, 0, 1, 1, 0, 2, 1] = some [0, 0, 2, 2, 1, 2, 1] :=
  specInv_mirror_7 [0, 0, 1, 1, 0, 2, 1] [0, 1, 0, 2, 0, 0, 2] [1, 2, 1, 1, 1, 1, 1] [0, 0, 1, 1, 2, 1, 2] [0, 0, 2, 2, 1, 2, 1] demoR1_0011021 demoR2_0011021 demoC_0011021 demoM_0011021 demoMir_0011021

theorem demoR1_1011021 : invRung 7 5 20 [1, 0, 1, 1, 0, 2, 1] [1, 0, 1, 1, 0, 2, 1] 1 2 false = ([2, 2, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_1011021 : invRung 7 5 20 [1, 0, 1, 1, 0, 2, 1] [2, 2, 2, 0, 2, 0, 1] 3 1 true = ([1, 1, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1011021 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 1, 1] = [2, 0, 0, 0, 2, 0, 2] := by
  decide

theorem demoM_1011021 : fieldMul 7 5 20 [2, 0, 0, 0, 2, 0, 2] [1, 0, 1, 1, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011021 : mirrorTrits [2, 0, 0, 0, 2, 0, 2] = [1, 0, 0, 0, 1, 0, 1] := by
  decide

theorem demoInv_1011021 : specInv 7 5 20 [1, 0, 1, 1, 0, 2, 1] = some [1, 0, 0, 0, 1, 0, 1] :=
  specInv_mirror_7 [1, 0, 1, 1, 0, 2, 1] [2, 2, 2, 0, 2, 0, 1] [1, 1, 1, 0, 1, 1, 1] [2, 0, 0, 0, 2, 0, 2] [1, 0, 0, 0, 1, 0, 1] demoR1_1011021 demoR2_1011021 demoC_1011021 demoM_1011021 demoMir_1011021

theorem demoR1_2011021 : invRung 7 5 20 [2, 0, 1, 1, 0, 2, 1] [2, 0, 1, 1, 0, 2, 1] 1 2 false = ([2, 2, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_2011021 : invRung 7 5 20 [2, 0, 1, 1, 0, 2, 1] [2, 2, 2, 2, 0, 1, 1] 3 1 true = ([1, 2, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2011021 : fieldCube 7 5 20 [1, 2, 0, 0, 0, 1, 0] = [2, 1, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_2011021 : fieldMul 7 5 20 [2, 1, 1, 2, 1, 1, 2] [2, 0, 1, 1, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011021 : mirrorTrits [2, 1, 1, 2, 1, 1, 2] = [1, 2, 2, 1, 2, 2, 1] := by
  decide

theorem demoInv_2011021 : specInv 7 5 20 [2, 0, 1, 1, 0, 2, 1] = some [1, 2, 2, 1, 2, 2, 1] :=
  specInv_mirror_7 [2, 0, 1, 1, 0, 2, 1] [2, 2, 2, 2, 0, 1, 1] [1, 2, 0, 0, 0, 1, 0] [2, 1, 1, 2, 1, 1, 2] [1, 2, 2, 1, 2, 2, 1] demoR1_2011021 demoR2_2011021 demoC_2011021 demoM_2011021 demoMir_2011021

theorem demoR1_0111021 : invRung 7 5 20 [0, 1, 1, 1, 0, 2, 1] [0, 1, 1, 1, 0, 2, 1] 1 2 false = ([2, 0, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_0111021 : invRung 7 5 20 [0, 1, 1, 1, 0, 2, 1] [2, 0, 1, 2, 0, 1, 0] 3 1 true = ([1, 0, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_0111021 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 1, 1] = [1, 0, 2, 2, 2, 2, 0] := by
  decide

theorem demoM_0111021 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 2, 0] [0, 1, 1, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0111021 : specInv 7 5 20 [0, 1, 1, 1, 0, 2, 1] = some [1, 0, 2, 2, 2, 2, 0] :=
  specInv_white_7 [0, 1, 1, 1, 0, 2, 1] [2, 0, 1, 2, 0, 1, 0] [1, 0, 2, 2, 1, 1, 1] [1, 0, 2, 2, 2, 2, 0] demoR1_0111021 demoR2_0111021 demoC_0111021 demoM_0111021

theorem demoR1_1111021 : invRung 7 5 20 [1, 1, 1, 1, 0, 2, 1] [1, 1, 1, 1, 0, 2, 1] 1 2 false = ([1, 1, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_1111021 : invRung 7 5 20 [1, 1, 1, 1, 0, 2, 1] [1, 1, 2, 2, 0, 2, 1] 3 1 true = ([0, 0, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_1111021 : fieldCube 7 5 20 [0, 0, 2, 1, 0, 0, 0] = [1, 0, 1, 0, 0, 1, 2] := by
  decide

theorem demoM_1111021 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 1, 2] [1, 1, 1, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1111021 : specInv 7 5 20 [1, 1, 1, 1, 0, 2, 1] = some [1, 0, 1, 0, 0, 1, 2] :=
  specInv_white_7 [1, 1, 1, 1, 0, 2, 1] [1, 1, 2, 2, 0, 2, 1] [0, 0, 2, 1, 0, 0, 0] [1, 0, 1, 0, 0, 1, 2] demoR1_1111021 demoR2_1111021 demoC_1111021 demoM_1111021

theorem demoR1_2111021 : invRung 7 5 20 [2, 1, 1, 1, 0, 2, 1] [2, 1, 1, 1, 0, 2, 1] 1 2 false = ([0, 0, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2111021 : invRung 7 5 20 [2, 1, 1, 1, 0, 2, 1] [0, 0, 0, 2, 2, 0, 0] 3 1 true = ([2, 2, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_2111021 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 0, 2] = [1, 1, 0, 0, 2, 0, 2] := by
  decide

theorem demoM_2111021 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 0, 2] [2, 1, 1, 1, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2111021 : mirrorTrits [1, 1, 0, 0, 2, 0, 2] = [2, 2, 0, 0, 1, 0, 1] := by
  decide

theorem demoInv_2111021 : specInv 7 5 20 [2, 1, 1, 1, 0, 2, 1] = some [2, 2, 0, 0, 1, 0, 1] :=
  specInv_mirror_7 [2, 1, 1, 1, 0, 2, 1] [0, 0, 0, 2, 2, 0, 0] [2, 2, 1, 2, 2, 0, 2] [1, 1, 0, 0, 2, 0, 2] [2, 2, 0, 0, 1, 0, 1] demoR1_2111021 demoR2_2111021 demoC_2111021 demoM_2111021 demoMir_2111021

theorem demoR1_0211021 : invRung 7 5 20 [0, 2, 1, 1, 0, 2, 1] [0, 2, 1, 1, 0, 2, 1] 1 2 false = ([2, 2, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_0211021 : invRung 7 5 20 [0, 2, 1, 1, 0, 2, 1] [2, 2, 2, 1, 1, 1, 0] 3 1 true = ([1, 2, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0211021 : fieldCube 7 5 20 [1, 2, 2, 0, 0, 2, 1] = [0, 0, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_0211021 : fieldMul 7 5 20 [0, 0, 1, 0, 0, 0, 1] [0, 2, 1, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0211021 : specInv 7 5 20 [0, 2, 1, 1, 0, 2, 1] = some [0, 0, 1, 0, 0, 0, 1] :=
  specInv_white_7 [0, 2, 1, 1, 0, 2, 1] [2, 2, 2, 1, 1, 1, 0] [1, 2, 2, 0, 0, 2, 1] [0, 0, 1, 0, 0, 0, 1] demoR1_0211021 demoR2_0211021 demoC_0211021 demoM_0211021

theorem demoR1_1211021 : invRung 7 5 20 [1, 2, 1, 1, 0, 2, 1] [1, 2, 1, 1, 0, 2, 1] 1 2 false = ([1, 1, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1211021 : invRung 7 5 20 [1, 2, 1, 1, 0, 2, 1] [1, 1, 2, 1, 1, 2, 1] 3 1 true = ([2, 2, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_1211021 : fieldCube 7 5 20 [2, 2, 2, 0, 0, 2, 0] = [1, 2, 2, 2, 2, 2, 0] := by
  decide

theorem demoM_1211021 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 2, 0] [1, 2, 1, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1211021 : specInv 7 5 20 [1, 2, 1, 1, 0, 2, 1] = some [1, 2, 2, 2, 2, 2, 0] :=
  specInv_white_7 [1, 2, 1, 1, 0, 2, 1] [1, 1, 2, 1, 1, 2, 1] [2, 2, 2, 0, 0, 2, 0] [1, 2, 2, 2, 2, 2, 0] demoR1_1211021 demoR2_1211021 demoC_1211021 demoM_1211021

theorem demoR1_2211021 : invRung 7 5 20 [2, 2, 1, 1, 0, 2, 1] [2, 2, 1, 1, 0, 2, 1] 1 2 false = ([2, 0, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_2211021 : invRung 7 5 20 [2, 2, 1, 1, 0, 2, 1] [2, 0, 1, 0, 0, 2, 0] 3 1 true = ([0, 2, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_2211021 : fieldCube 7 5 20 [0, 2, 1, 1, 2, 0, 1] = [1, 0, 0, 2, 1, 1, 1] := by
  decide

theorem demoM_2211021 : fieldMul 7 5 20 [1, 0, 0, 2, 1, 1, 1] [2, 2, 1, 1, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211021 : mirrorTrits [1, 0, 0, 2, 1, 1, 1] = [2, 0, 0, 1, 2, 2, 2] := by
  decide

theorem demoInv_2211021 : specInv 7 5 20 [2, 2, 1, 1, 0, 2, 1] = some [2, 0, 0, 1, 2, 2, 2] :=
  specInv_mirror_7 [2, 2, 1, 1, 0, 2, 1] [2, 0, 1, 0, 0, 2, 0] [0, 2, 1, 1, 2, 0, 1] [1, 0, 0, 2, 1, 1, 1] [2, 0, 0, 1, 2, 2, 2] demoR1_2211021 demoR2_2211021 demoC_2211021 demoM_2211021 demoMir_2211021

theorem demoR1_0021021 : invRung 7 5 20 [0, 0, 2, 1, 0, 2, 1] [0, 0, 2, 1, 0, 2, 1] 1 2 false = ([0, 1, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0021021 : invRung 7 5 20 [0, 0, 2, 1, 0, 2, 1] [0, 1, 2, 2, 2, 2, 1] 3 1 true = ([0, 0, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0021021 : fieldCube 7 5 20 [0, 0, 1, 2, 0, 1, 1] = [0, 2, 2, 1, 2, 1, 1] := by
  decide

theorem demoM_0021021 : fieldMul 7 5 20 [0, 2, 2, 1, 2, 1, 1] [0, 0, 2, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0021021 : specInv 7 5 20 [0, 0, 2, 1, 0, 2, 1] = some [0, 2, 2, 1, 2, 1, 1] :=
  specInv_white_7 [0, 0, 2, 1, 0, 2, 1] [0, 1, 2, 2, 2, 2, 1] [0, 0, 1, 2, 0, 1, 1] [0, 2, 2, 1, 2, 1, 1] demoR1_0021021 demoR2_0021021 demoC_0021021 demoM_0021021

theorem demoR1_1021021 : invRung 7 5 20 [1, 0, 2, 1, 0, 2, 1] [1, 0, 2, 1, 0, 2, 1] 1 2 false = ([1, 1, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1021021 : invRung 7 5 20 [1, 0, 2, 1, 0, 2, 1] [1, 1, 2, 1, 1, 0, 0] 3 1 true = ([1, 1, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_1021021 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 1, 1] = [0, 0, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_1021021 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 1, 2] [1, 0, 2, 1, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021021 : mirrorTrits [0, 0, 1, 0, 2, 1, 2] = [0, 0, 2, 0, 1, 2, 1] := by
  decide

theorem demoInv_1021021 : specInv 7 5 20 [1, 0, 2, 1, 0, 2, 1] = some [0, 0, 2, 0, 1, 2, 1] :=
  specInv_mirror_7 [1, 0, 2, 1, 0, 2, 1] [1, 1, 2, 1, 1, 0, 0] [1, 1, 1, 1, 1, 1, 1] [0, 0, 1, 0, 2, 1, 2] [0, 0, 2, 0, 1, 2, 1] demoR1_1021021 demoR2_1021021 demoC_1021021 demoM_1021021 demoMir_1021021

theorem demoR1_2021021 : invRung 7 5 20 [2, 0, 2, 1, 0, 2, 1] [2, 0, 2, 1, 0, 2, 1] 1 2 false = ([0, 2, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_2021021 : invRung 7 5 20 [2, 0, 2, 1, 0, 2, 1] [0, 2, 0, 0, 1, 1, 1] 3 1 true = ([1, 0, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_2021021 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 2, 1] = [2, 1, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_2021021 : fieldMul 7 5 20 [2, 1, 0, 2, 0, 0, 1] [2, 0, 2, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2021021 : specInv 7 5 20 [2, 0, 2, 1, 0, 2, 1] = some [2, 1, 0, 2, 0, 0, 1] :=
  specInv_white_7 [2, 0, 2, 1, 0, 2, 1] [0, 2, 0, 0, 1, 1, 1] [1, 0, 1, 2, 1, 2, 1] [2, 1, 0, 2, 0, 0, 1] demoR1_2021021 demoR2_2021021 demoC_2021021 demoM_2021021

theorem demoR1_0121021 : invRung 7 5 20 [0, 1, 2, 1, 0, 2, 1] [0, 1, 2, 1, 0, 2, 1] 1 2 false = ([2, 2, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_0121021 : invRung 7 5 20 [0, 1, 2, 1, 0, 2, 1] [2, 2, 2, 0, 1, 1, 2] 3 1 true = ([1, 2, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0121021 : fieldCube 7 5 20 [1, 2, 2, 1, 0, 0, 1] = [2, 1, 0, 0, 1, 2, 0] := by
  decide

theorem demoM_0121021 : fieldMul 7 5 20 [2, 1, 0, 0, 1, 2, 0] [0, 1, 2, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0121021 : specInv 7 5 20 [0, 1, 2, 1, 0, 2, 1] = some [2, 1, 0, 0, 1, 2, 0] :=
  specInv_white_7 [0, 1, 2, 1, 0, 2, 1] [2, 2, 2, 0, 1, 1, 2] [1, 2, 2, 1, 0, 0, 1] [2, 1, 0, 0, 1, 2, 0] demoR1_0121021 demoR2_0121021 demoC_0121021 demoM_0121021

theorem demoR1_1121021 : invRung 7 5 20 [1, 1, 2, 1, 0, 2, 1] [1, 1, 2, 1, 0, 2, 1] 1 2 false = ([0, 1, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_1121021 : invRung 7 5 20 [1, 1, 2, 1, 0, 2, 1] [0, 1, 2, 0, 2, 1, 2] 3 1 true = ([0, 2, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_1121021 : fieldCube 7 5 20 [0, 2, 1, 0, 0, 2, 2] = [2, 1, 0, 1, 1, 1, 1] := by
  decide

theorem demoM_1121021 : fieldMul 7 5 20 [2, 1, 0, 1, 1, 1, 1] [1, 1, 2, 1, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121021 : mirrorTrits [2, 1, 0, 1, 1, 1, 1] = [1, 2, 0, 2, 2, 2, 2] := by
  decide

theorem demoInv_1121021 : specInv 7 5 20 [1, 1, 2, 1, 0, 2, 1] = some [1, 2, 0, 2, 2, 2, 2] :=
  specInv_mirror_7 [1, 1, 2, 1, 0, 2, 1] [0, 1, 2, 0, 2, 1, 2] [0, 2, 1, 0, 0, 2, 2] [2, 1, 0, 1, 1, 1, 1] [1, 2, 0, 2, 2, 2, 2] demoR1_1121021 demoR2_1121021 demoC_1121021 demoM_1121021 demoMir_1121021

theorem demoR1_2121021 : invRung 7 5 20 [2, 1, 2, 1, 0, 2, 1] [2, 1, 2, 1, 0, 2, 1] 1 2 false = ([1, 0, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_2121021 : invRung 7 5 20 [2, 1, 2, 1, 0, 2, 1] [1, 0, 2, 2, 1, 0, 1] 3 1 true = ([1, 0, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_2121021 : fieldCube 7 5 20 [1, 0, 0, 1, 1, 1, 0] = [0, 2, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_2121021 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 0, 0] [2, 1, 2, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2121021 : specInv 7 5 20 [2, 1, 2, 1, 0, 2, 1] = some [0, 2, 2, 1, 1, 0, 0] :=
  specInv_white_7 [2, 1, 2, 1, 0, 2, 1] [1, 0, 2, 2, 1, 0, 1] [1, 0, 0, 1, 1, 1, 0] [0, 2, 2, 1, 1, 0, 0] demoR1_2121021 demoR2_2121021 demoC_2121021 demoM_2121021

theorem demoR1_0221021 : invRung 7 5 20 [0, 2, 2, 1, 0, 2, 1] [0, 2, 2, 1, 0, 2, 1] 1 2 false = ([0, 2, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_0221021 : invRung 7 5 20 [0, 2, 2, 1, 0, 2, 1] [0, 2, 0, 0, 1, 0, 2] 3 1 true = ([1, 1, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_0221021 : fieldCube 7 5 20 [1, 1, 0, 2, 0, 0, 1] = [0, 1, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_0221021 : fieldMul 7 5 20 [0, 1, 1, 2, 1, 0, 1] [0, 2, 2, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0221021 : specInv 7 5 20 [0, 2, 2, 1, 0, 2, 1] = some [0, 1, 1, 2, 1, 0, 1] :=
  specInv_white_7 [0, 2, 2, 1, 0, 2, 1] [0, 2, 0, 0, 1, 0, 2] [1, 1, 0, 2, 0, 0, 1] [0, 1, 1, 2, 1, 0, 1] demoR1_0221021 demoR2_0221021 demoC_0221021 demoM_0221021

theorem demoR1_1221021 : invRung 7 5 20 [1, 2, 2, 1, 0, 2, 1] [1, 2, 2, 1, 0, 2, 1] 1 2 false = ([1, 1, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_1221021 : invRung 7 5 20 [1, 2, 2, 1, 0, 2, 1] [1, 1, 0, 2, 0, 1, 1] 3 1 true = ([2, 0, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_1221021 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 1, 2] = [2, 0, 1, 2, 0, 2, 2] := by
  decide

theorem demoM_1221021 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 2, 2] [1, 2, 2, 1, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1221021 : specInv 7 5 20 [1, 2, 2, 1, 0, 2, 1] = some [2, 0, 1, 2, 0, 2, 2] :=
  specInv_white_7 [1, 2, 2, 1, 0, 2, 1] [1, 1, 0, 2, 0, 1, 1] [2, 0, 1, 2, 0, 1, 2] [2, 0, 1, 2, 0, 2, 2] demoR1_1221021 demoR2_1221021 demoC_1221021 demoM_1221021

theorem demoR1_2221021 : invRung 7 5 20 [2, 2, 2, 1, 0, 2, 1] [2, 2, 2, 1, 0, 2, 1] 1 2 false = ([1, 2, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2221021 : invRung 7 5 20 [2, 2, 2, 1, 0, 2, 1] [1, 2, 2, 2, 0, 0, 2] 3 1 true = ([2, 1, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2221021 : fieldCube 7 5 20 [2, 1, 1, 2, 1, 2, 2] = [0, 2, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_2221021 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 1, 2] [2, 2, 2, 1, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221021 : mirrorTrits [0, 2, 2, 1, 1, 1, 2] = [0, 1, 1, 2, 2, 2, 1] := by
  decide

theorem demoInv_2221021 : specInv 7 5 20 [2, 2, 2, 1, 0, 2, 1] = some [0, 1, 1, 2, 2, 2, 1] :=
  specInv_mirror_7 [2, 2, 2, 1, 0, 2, 1] [1, 2, 2, 2, 0, 0, 2] [2, 1, 1, 2, 1, 2, 2] [0, 2, 2, 1, 1, 1, 2] [0, 1, 1, 2, 2, 2, 1] demoR1_2221021 demoR2_2221021 demoC_2221021 demoM_2221021 demoMir_2221021

theorem demoR1_0002021 : invRung 7 5 20 [0, 0, 0, 2, 0, 2, 1] [0, 0, 0, 2, 0, 2, 1] 1 2 false = ([2, 0, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_0002021 : invRung 7 5 20 [0, 0, 0, 2, 0, 2, 1] [2, 0, 1, 2, 0, 1, 1] 3 1 true = ([0, 0, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_0002021 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 0, 0] = [2, 1, 2, 1, 0, 0, 2] := by
  decide

theorem demoM_0002021 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 0, 2] [0, 0, 0, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002021 : mirrorTrits [2, 1, 2, 1, 0, 0, 2] = [1, 2, 1, 2, 0, 0, 1] := by
  decide

theorem demoInv_0002021 : specInv 7 5 20 [0, 0, 0, 2, 0, 2, 1] = some [1, 2, 1, 2, 0, 0, 1] :=
  specInv_mirror_7 [0, 0, 0, 2, 0, 2, 1] [2, 0, 1, 2, 0, 1, 1] [0, 0, 1, 2, 1, 0, 0] [2, 1, 2, 1, 0, 0, 2] [1, 2, 1, 2, 0, 0, 1] demoR1_0002021 demoR2_0002021 demoC_0002021 demoM_0002021 demoMir_0002021

theorem demoR1_1002021 : invRung 7 5 20 [1, 0, 0, 2, 0, 2, 1] [1, 0, 0, 2, 0, 2, 1] 1 2 false = ([1, 0, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_1002021 : invRung 7 5 20 [1, 0, 0, 2, 0, 2, 1] [1, 0, 0, 1, 2, 0, 0] 3 1 true = ([0, 2, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_1002021 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 0, 2] = [0, 0, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_1002021 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 0, 2] [1, 0, 0, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002021 : mirrorTrits [0, 0, 1, 2, 2, 0, 2] = [0, 0, 2, 1, 1, 0, 1] := by
  decide

theorem demoInv_1002021 : specInv 7 5 20 [1, 0, 0, 2, 0, 2, 1] = some [0, 0, 2, 1, 1, 0, 1] :=
  specInv_mirror_7 [1, 0, 0, 2, 0, 2, 1] [1, 0, 0, 1, 2, 0, 0] [0, 2, 2, 0, 1, 0, 2] [0, 0, 1, 2, 2, 0, 2] [0, 0, 2, 1, 1, 0, 1] demoR1_1002021 demoR2_1002021 demoC_1002021 demoM_1002021 demoMir_1002021

theorem demoR1_2002021 : invRung 7 5 20 [2, 0, 0, 2, 0, 2, 1] [2, 0, 0, 2, 0, 2, 1] 1 2 false = ([1, 2, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_2002021 : invRung 7 5 20 [2, 0, 0, 2, 0, 2, 1] [1, 2, 1, 1, 0, 2, 2] 3 1 true = ([2, 0, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2002021 : fieldCube 7 5 20 [2, 0, 2, 0, 1, 1, 0] = [0, 2, 1, 1, 1, 2, 2] := by
  decide

theorem demoM_2002021 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 2, 2] [2, 0, 0, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2002021 : specInv 7 5 20 [2, 0, 0, 2, 0, 2, 1] = some [0, 2, 1, 1, 1, 2, 2] :=
  specInv_white_7 [2, 0, 0, 2, 0, 2, 1] [1, 2, 1, 1, 0, 2, 2] [2, 0, 2, 0, 1, 1, 0] [0, 2, 1, 1, 1, 2, 2] demoR1_2002021 demoR2_2002021 demoC_2002021 demoM_2002021

theorem demoR1_0102021 : invRung 7 5 20 [0, 1, 0, 2, 0, 2, 1] [0, 1, 0, 2, 0, 2, 1] 1 2 false = ([1, 1, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_0102021 : invRung 7 5 20 [0, 1, 0, 2, 0, 2, 1] [1, 1, 1, 2, 2, 0, 1] 3 1 true = ([0, 0, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0102021 : fieldCube 7 5 20 [0, 0, 2, 1, 0, 1, 1] = [2, 2, 1, 1, 2, 0, 2] := by
  decide

theorem demoM_0102021 : fieldMul 7 5 20 [2, 2, 1, 1, 2, 0, 2] [0, 1, 0, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102021 : mirrorTrits [2, 2, 1, 1, 2, 0, 2] = [1, 1, 2, 2, 1, 0, 1] := by
  decide

theorem demoInv_0102021 : specInv 7 5 20 [0, 1, 0, 2, 0, 2, 1] = some [1, 1, 2, 2, 1, 0, 1] :=
  specInv_mirror_7 [0, 1, 0, 2, 0, 2, 1] [1, 1, 1, 2, 2, 0, 1] [0, 0, 2, 1, 0, 1, 1] [2, 2, 1, 1, 2, 0, 2] [1, 1, 2, 2, 1, 0, 1] demoR1_0102021 demoR2_0102021 demoC_0102021 demoM_0102021 demoMir_0102021

theorem demoR1_1102021 : invRung 7 5 20 [1, 1, 0, 2, 0, 2, 1] [1, 1, 0, 2, 0, 2, 1] 1 2 false = ([1, 2, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_1102021 : invRung 7 5 20 [1, 1, 0, 2, 0, 2, 1] [1, 2, 1, 1, 0, 1, 0] 3 1 true = ([2, 1, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_1102021 : fieldCube 7 5 20 [2, 1, 1, 2, 1, 0, 1] = [1, 2, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_1102021 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 1, 0] [1, 1, 0, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1102021 : specInv 7 5 20 [1, 1, 0, 2, 0, 2, 1] = some [1, 2, 1, 0, 1, 1, 0] :=
  specInv_white_7 [1, 1, 0, 2, 0, 2, 1] [1, 2, 1, 1, 0, 1, 0] [2, 1, 1, 2, 1, 0, 1] [1, 2, 1, 0, 1, 1, 0] demoR1_1102021 demoR2_1102021 demoC_1102021 demoM_1102021

theorem demoR1_2102021 : invRung 7 5 20 [2, 1, 0, 2, 0, 2, 1] [2, 1, 0, 2, 0, 2, 1] 1 2 false = ([1, 1, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_2102021 : invRung 7 5 20 [2, 1, 0, 2, 0, 2, 1] [1, 1, 2, 0, 0, 1, 2] 3 1 true = ([1, 1, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_2102021 : fieldCube 7 5 20 [1, 1, 1, 2, 0, 1, 2] = [1, 0, 1, 0, 0, 2, 2] := by
  decide

theorem demoM_2102021 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 2, 2] [2, 1, 0, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2102021 : specInv 7 5 20 [2, 1, 0, 2, 0, 2, 1] = some [1, 0, 1, 0, 0, 2, 2] :=
  specInv_white_7 [2, 1, 0, 2, 0, 2, 1] [1, 1, 2, 0, 0, 1, 2] [1, 1, 1, 2, 0, 1, 2] [1, 0, 1, 0, 0, 2, 2] demoR1_2102021 demoR2_2102021 demoC_2102021 demoM_2102021

theorem demoR1_0202021 : invRung 7 5 20 [0, 2, 0, 2, 0, 2, 1] [0, 2, 0, 2, 0, 2, 1] 1 2 false = ([0, 1, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_0202021 : invRung 7 5 20 [0, 2, 0, 2, 0, 2, 1] [0, 1, 0, 2, 1, 1, 1] 3 1 true = ([2, 1, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0202021 : fieldCube 7 5 20 [2, 1, 1, 0, 2, 1, 2] = [0, 2, 2, 2, 0, 2, 1] := by
  decide

theorem demoM_0202021 : fieldMul 7 5 20 [0, 2, 2, 2, 0, 2, 1] [0, 2, 0, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0202021 : specInv 7 5 20 [0, 2, 0, 2, 0, 2, 1] = some [0, 2, 2, 2, 0, 2, 1] :=
  specInv_white_7 [0, 2, 0, 2, 0, 2, 1] [0, 1, 0, 2, 1, 1, 1] [2, 1, 1, 0, 2, 1, 2] [0, 2, 2, 2, 0, 2, 1] demoR1_0202021 demoR2_0202021 demoC_0202021 demoM_0202021

theorem demoR1_1202021 : invRung 7 5 20 [1, 2, 0, 2, 0, 2, 1] [1, 2, 0, 2, 0, 2, 1] 1 2 false = ([1, 1, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1202021 : invRung 7 5 20 [1, 2, 0, 2, 0, 2, 1] [1, 1, 1, 2, 0, 0, 1] 3 1 true = ([1, 2, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_1202021 : fieldCube 7 5 20 [1, 2, 2, 0, 0, 1, 1] = [2, 2, 0, 0, 2, 2, 2] := by
  decide

theorem demoM_1202021 : fieldMul 7 5 20 [2, 2, 0, 0, 2, 2, 2] [1, 2, 0, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202021 : mirrorTrits [2, 2, 0, 0, 2, 2, 2] = [1, 1, 0, 0, 1, 1, 1] := by
  decide

theorem demoInv_1202021 : specInv 7 5 20 [1, 2, 0, 2, 0, 2, 1] = some [1, 1, 0, 0, 1, 1, 1] :=
  specInv_mirror_7 [1, 2, 0, 2, 0, 2, 1] [1, 1, 1, 2, 0, 0, 1] [1, 2, 2, 0, 0, 1, 1] [2, 2, 0, 0, 2, 2, 2] [1, 1, 0, 0, 1, 1, 1] demoR1_1202021 demoR2_1202021 demoC_1202021 demoM_1202021 demoMir_1202021

theorem demoR1_2202021 : invRung 7 5 20 [2, 2, 0, 2, 0, 2, 1] [2, 2, 0, 2, 0, 2, 1] 1 2 false = ([1, 1, 2, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_2202021 : invRung 7 5 20 [2, 2, 0, 2, 0, 2, 1] [1, 1, 2, 1, 1, 0, 1] 3 1 true = ([0, 1, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_2202021 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 0, 1] = [1, 1, 0, 2, 1, 2, 1] := by
  decide

theorem demoM_2202021 : fieldMul 7 5 20 [1, 1, 0, 2, 1, 2, 1] [2, 2, 0, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202021 : mirrorTrits [1, 1, 0, 2, 1, 2, 1] = [2, 2, 0, 1, 2, 1, 2] := by
  decide

theorem demoInv_2202021 : specInv 7 5 20 [2, 2, 0, 2, 0, 2, 1] = some [2, 2, 0, 1, 2, 1, 2] :=
  specInv_mirror_7 [2, 2, 0, 2, 0, 2, 1] [1, 1, 2, 1, 1, 0, 1] [0, 1, 0, 1, 0, 0, 1] [1, 1, 0, 2, 1, 2, 1] [2, 2, 0, 1, 2, 1, 2] demoR1_2202021 demoR2_2202021 demoC_2202021 demoM_2202021 demoMir_2202021

theorem demoR1_0012021 : invRung 7 5 20 [0, 0, 1, 2, 0, 2, 1] [0, 0, 1, 2, 0, 2, 1] 1 2 false = ([2, 0, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_0012021 : invRung 7 5 20 [0, 0, 1, 2, 0, 2, 1] [2, 0, 0, 1, 2, 0, 1] 3 1 true = ([1, 1, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_0012021 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 1, 2] = [2, 1, 2, 1, 0, 1, 2] := by
  decide

theorem demoM_0012021 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 1, 2] [0, 0, 1, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0012021 : specInv 7 5 20 [0, 0, 1, 2, 0, 2, 1] = some [2, 1, 2, 1, 0, 1, 2] :=
  specInv_white_7 [0, 0, 1, 2, 0, 2, 1] [2, 0, 0, 1, 2, 0, 1] [1, 1, 0, 0, 1, 1, 2] [2, 1, 2, 1, 0, 1, 2] demoR1_0012021 demoR2_0012021 demoC_0012021 demoM_0012021

theorem demoR1_1012021 : invRung 7 5 20 [1, 0, 1, 2, 0, 2, 1] [1, 0, 1, 2, 0, 2, 1] 1 2 false = ([1, 0, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_1012021 : invRung 7 5 20 [1, 0, 1, 2, 0, 2, 1] [1, 0, 0, 0, 0, 1, 2] 3 1 true = ([0, 2, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_1012021 : fieldCube 7 5 20 [0, 2, 2, 2, 0, 0, 2] = [2, 2, 0, 1, 2, 1, 1] := by
  decide

theorem demoM_1012021 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 1, 1] [1, 0, 1, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1012021 : specInv 7 5 20 [1, 0, 1, 2, 0, 2, 1] = some [2, 2, 0, 1, 2, 1, 1] :=
  specInv_white_7 [1, 0, 1, 2, 0, 2, 1] [1, 0, 0, 0, 0, 1, 2] [0, 2, 2, 2, 0, 0, 2] [2, 2, 0, 1, 2, 1, 1] demoR1_1012021 demoR2_1012021 demoC_1012021 demoM_1012021

theorem demoR1_2012021 : invRung 7 5 20 [2, 0, 1, 2, 0, 2, 1] [2, 0, 1, 2, 0, 2, 1] 1 2 false = ([1, 1, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_2012021 : invRung 7 5 20 [2, 0, 1, 2, 0, 2, 1] [1, 1, 2, 2, 2, 1, 1] 3 1 true = ([2, 0, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_2012021 : fieldCube 7 5 20 [2, 0, 0, 0, 2, 2, 1] = [1, 2, 1, 0, 0, 2, 1] := by
  decide

theorem demoM_2012021 : fieldMul 7 5 20 [1, 2, 1, 0, 0, 2, 1] [2, 0, 1, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012021 : mirrorTrits [1, 2, 1, 0, 0, 2, 1] = [2, 1, 2, 0, 0, 1, 2] := by
  decide

theorem demoInv_2012021 : specInv 7 5 20 [2, 0, 1, 2, 0, 2, 1] = some [2, 1, 2, 0, 0, 1, 2] :=
  specInv_mirror_7 [2, 0, 1, 2, 0, 2, 1] [1, 1, 2, 2, 2, 1, 1] [2, 0, 0, 0, 2, 2, 1] [1, 2, 1, 0, 0, 2, 1] [2, 1, 2, 0, 0, 1, 2] demoR1_2012021 demoR2_2012021 demoC_2012021 demoM_2012021 demoMir_2012021

theorem demoR1_0112021 : invRung 7 5 20 [0, 1, 1, 2, 0, 2, 1] [0, 1, 1, 2, 0, 2, 1] 1 2 false = ([2, 0, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_0112021 : invRung 7 5 20 [0, 1, 1, 2, 0, 2, 1] [2, 0, 2, 1, 0, 0, 2] 3 1 true = ([2, 1, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_0112021 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 1, 0] = [1, 2, 2, 2, 1, 0, 2] := by
  decide

theorem demoM_0112021 : fieldMul 7 5 20 [1, 2, 2, 2, 1, 0, 2] [0, 1, 1, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0112021 : specInv 7 5 20 [0, 1, 1, 2, 0, 2, 1] = some [1, 2, 2, 2, 1, 0, 2] :=
  specInv_white_7 [0, 1, 1, 2, 0, 2, 1] [2, 0, 2, 1, 0, 0, 2] [2, 1, 2, 1, 1, 1, 0] [1, 2, 2, 2, 1, 0, 2] demoR1_0112021 demoR2_0112021 demoC_0112021 demoM_0112021

theorem demoR1_1112021 : invRung 7 5 20 [1, 1, 1, 2, 0, 2, 1] [1, 1, 1, 2, 0, 2, 1] 1 2 false = ([2, 0, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_1112021 : invRung 7 5 20 [1, 1, 1, 2, 0, 2, 1] [2, 0, 1, 2, 1, 1, 2] 3 1 true = ([1, 1, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_1112021 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 0, 2] = [2, 2, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_1112021 : fieldMul 7 5 20 [2, 2, 2, 0, 2, 0, 2] [1, 1, 1, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112021 : mirrorTrits [2, 2, 2, 0, 2, 0, 2] = [1, 1, 1, 0, 1, 0, 1] := by
  decide

theorem demoInv_1112021 : specInv 7 5 20 [1, 1, 1, 2, 0, 2, 1] = some [1, 1, 1, 0, 1, 0, 1] :=
  specInv_mirror_7 [1, 1, 1, 2, 0, 2, 1] [2, 0, 1, 2, 1, 1, 2] [1, 1, 0, 1, 0, 0, 2] [2, 2, 2, 0, 2, 0, 2] [1, 1, 1, 0, 1, 0, 1] demoR1_1112021 demoR2_1112021 demoC_1112021 demoM_1112021 demoMir_1112021

theorem demoR1_2112021 : invRung 7 5 20 [2, 1, 1, 2, 0, 2, 1] [2, 1, 1, 2, 0, 2, 1] 1 2 false = ([2, 0, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_2112021 : invRung 7 5 20 [2, 1, 1, 2, 0, 2, 1] [2, 0, 1, 2, 0, 0, 0] 3 1 true = ([1, 2, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_2112021 : fieldCube 7 5 20 [1, 2, 2, 2, 1, 1, 1] = [1, 0, 2, 1, 2, 2, 0] := by
  decide

theorem demoM_2112021 : fieldMul 7 5 20 [1, 0, 2, 1, 2, 2, 0] [2, 1, 1, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2112021 : specInv 7 5 20 [2, 1, 1, 2, 0, 2, 1] = some [1, 0, 2, 1, 2, 2, 0] :=
  specInv_white_7 [2, 1, 1, 2, 0, 2, 1] [2, 0, 1, 2, 0, 0, 0] [1, 2, 2, 2, 1, 1, 1] [1, 0, 2, 1, 2, 2, 0] demoR1_2112021 demoR2_2112021 demoC_2112021 demoM_2112021

theorem demoR1_0212021 : invRung 7 5 20 [0, 2, 1, 2, 0, 2, 1] [0, 2, 1, 2, 0, 2, 1] 1 2 false = ([0, 1, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_0212021 : invRung 7 5 20 [0, 2, 1, 2, 0, 2, 1] [0, 1, 1, 1, 1, 0, 0] 3 1 true = ([1, 1, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0212021 : fieldCube 7 5 20 [1, 1, 1, 1, 0, 0, 1] = [2, 1, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_0212021 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 2, 2] [0, 2, 1, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212021 : mirrorTrits [2, 1, 0, 2, 1, 2, 2] = [1, 2, 0, 1, 2, 1, 1] := by
  decide

theorem demoInv_0212021 : specInv 7 5 20 [0, 2, 1, 2, 0, 2, 1] = some [1, 2, 0, 1, 2, 1, 1] :=
  specInv_mirror_7 [0, 2, 1, 2, 0, 2, 1] [0, 1, 1, 1, 1, 0, 0] [1, 1, 1, 1, 0, 0, 1] [2, 1, 0, 2, 1, 2, 2] [1, 2, 0, 1, 2, 1, 1] demoR1_0212021 demoR2_0212021 demoC_0212021 demoM_0212021 demoMir_0212021

theorem demoR1_1212021 : invRung 7 5 20 [1, 2, 1, 2, 0, 2, 1] [1, 2, 1, 2, 0, 2, 1] 1 2 false = ([1, 2, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_1212021 : invRung 7 5 20 [1, 2, 1, 2, 0, 2, 1] [1, 2, 2, 2, 1, 0, 0] 3 1 true = ([0, 0, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_1212021 : fieldCube 7 5 20 [0, 0, 0, 2, 0, 1, 2] = [0, 0, 1, 2, 0, 2, 1] := by
  decide

theorem demoM_1212021 : fieldMul 7 5 20 [0, 0, 1, 2, 0, 2, 1] [1, 2, 1, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212021 : mirrorTrits [0, 0, 1, 2, 0, 2, 1] = [0, 0, 2, 1, 0, 1, 2] := by
  decide

theorem demoInv_1212021 : specInv 7 5 20 [1, 2, 1, 2, 0, 2, 1] = some [0, 0, 2, 1, 0, 1, 2] :=
  specInv_mirror_7 [1, 2, 1, 2, 0, 2, 1] [1, 2, 2, 2, 1, 0, 0] [0, 0, 0, 2, 0, 1, 2] [0, 0, 1, 2, 0, 2, 1] [0, 0, 2, 1, 0, 1, 2] demoR1_1212021 demoR2_1212021 demoC_1212021 demoM_1212021 demoMir_1212021

theorem demoR1_2212021 : invRung 7 5 20 [2, 2, 1, 2, 0, 2, 1] [2, 2, 1, 2, 0, 2, 1] 1 2 false = ([1, 2, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2212021 : invRung 7 5 20 [2, 2, 1, 2, 0, 2, 1] [1, 2, 0, 1, 2, 0, 1] 3 1 true = ([1, 0, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_2212021 : fieldCube 7 5 20 [1, 0, 0, 0, 2, 2, 1] = [0, 2, 1, 0, 0, 2, 1] := by
  decide

theorem demoM_2212021 : fieldMul 7 5 20 [0, 2, 1, 0, 0, 2, 1] [2, 2, 1, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212021 : mirrorTrits [0, 2, 1, 0, 0, 2, 1] = [0, 1, 2, 0, 0, 1, 2] := by
  decide

theorem demoInv_2212021 : specInv 7 5 20 [2, 2, 1, 2, 0, 2, 1] = some [0, 1, 2, 0, 0, 1, 2] :=
  specInv_mirror_7 [2, 2, 1, 2, 0, 2, 1] [1, 2, 0, 1, 2, 0, 1] [1, 0, 0, 0, 2, 2, 1] [0, 2, 1, 0, 0, 2, 1] [0, 1, 2, 0, 0, 1, 2] demoR1_2212021 demoR2_2212021 demoC_2212021 demoM_2212021 demoMir_2212021

theorem demoR1_0022021 : invRung 7 5 20 [0, 0, 2, 2, 0, 2, 1] [0, 0, 2, 2, 0, 2, 1] 1 2 false = ([2, 1, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_0022021 : invRung 7 5 20 [0, 0, 2, 2, 0, 2, 1] [2, 1, 2, 1, 2, 1, 0] 3 1 true = ([2, 0, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0022021 : fieldCube 7 5 20 [2, 0, 1, 0, 2, 1, 0] = [0, 0, 1, 2, 1, 0, 2] := by
  decide

theorem demoM_0022021 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 0, 2] [0, 0, 2, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0022021 : specInv 7 5 20 [0, 0, 2, 2, 0, 2, 1] = some [0, 0, 1, 2, 1, 0, 2] :=
  specInv_white_7 [0, 0, 2, 2, 0, 2, 1] [2, 1, 2, 1, 2, 1, 0] [2, 0, 1, 0, 2, 1, 0] [0, 0, 1, 2, 1, 0, 2] demoR1_0022021 demoR2_0022021 demoC_0022021 demoM_0022021

theorem demoR1_1022021 : invRung 7 5 20 [1, 0, 2, 2, 0, 2, 1] [1, 0, 2, 2, 0, 2, 1] 1 2 false = ([0, 1, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_1022021 : invRung 7 5 20 [1, 0, 2, 2, 0, 2, 1] [0, 1, 1, 0, 2, 1, 2] 3 1 true = ([0, 2, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_1022021 : fieldCube 7 5 20 [0, 2, 2, 0, 0, 0, 2] = [0, 2, 1, 1, 2, 2, 1] := by
  decide

theorem demoM_1022021 : fieldMul 7 5 20 [0, 2, 1, 1, 2, 2, 1] [1, 0, 2, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1022021 : mirrorTrits [0, 2, 1, 1, 2, 2, 1] = [0, 1, 2, 2, 1, 1, 2] := by
  decide

theorem demoInv_1022021 : specInv 7 5 20 [1, 0, 2, 2, 0, 2, 1] = some [0, 1, 2, 2, 1, 1, 2] :=
  specInv_mirror_7 [1, 0, 2, 2, 0, 2, 1] [0, 1, 1, 0, 2, 1, 2] [0, 2, 2, 0, 0, 0, 2] [0, 2, 1, 1, 2, 2, 1] [0, 1, 2, 2, 1, 1, 2] demoR1_1022021 demoR2_1022021 demoC_1022021 demoM_1022021 demoMir_1022021

theorem demoR1_2022021 : invRung 7 5 20 [2, 0, 2, 2, 0, 2, 1] [2, 0, 2, 2, 0, 2, 1] 1 2 false = ([2, 1, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_2022021 : invRung 7 5 20 [2, 0, 2, 2, 0, 2, 1] [2, 1, 2, 1, 2, 2, 0] 3 1 true = ([2, 1, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2022021 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 2, 1] = [2, 1, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_2022021 : fieldMul 7 5 20 [2, 1, 2, 0, 0, 2, 2] [2, 0, 2, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022021 : mirrorTrits [2, 1, 2, 0, 0, 2, 2] = [1, 2, 1, 0, 0, 1, 1] := by
  decide

theorem demoInv_2022021 : specInv 7 5 20 [2, 0, 2, 2, 0, 2, 1] = some [1, 2, 1, 0, 0, 1, 1] :=
  specInv_mirror_7 [2, 0, 2, 2, 0, 2, 1] [2, 1, 2, 1, 2, 2, 0] [2, 1, 2, 1, 1, 2, 1] [2, 1, 2, 0, 0, 2, 2] [1, 2, 1, 0, 0, 1, 1] demoR1_2022021 demoR2_2022021 demoC_2022021 demoM_2022021 demoMir_2022021

theorem demoR1_0122021 : invRung 7 5 20 [0, 1, 2, 2, 0, 2, 1] [0, 1, 2, 2, 0, 2, 1] 1 2 false = ([0, 2, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0122021 : invRung 7 5 20 [0, 1, 2, 2, 0, 2, 1] [0, 2, 2, 0, 1, 1, 1] 3 1 true = ([1, 2, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_0122021 : fieldCube 7 5 20 [1, 2, 2, 1, 1, 1, 0] = [0, 2, 2, 0, 1, 0, 2] := by
  decide

theorem demoM_0122021 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 0, 2] [0, 1, 2, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122021 : mirrorTrits [0, 2, 2, 0, 1, 0, 2] = [0, 1, 1, 0, 2, 0, 1] := by
  decide

theorem demoInv_0122021 : specInv 7 5 20 [0, 1, 2, 2, 0, 2, 1] = some [0, 1, 1, 0, 2, 0, 1] :=
  specInv_mirror_7 [0, 1, 2, 2, 0, 2, 1] [0, 2, 2, 0, 1, 1, 1] [1, 2, 2, 1, 1, 1, 0] [0, 2, 2, 0, 1, 0, 2] [0, 1, 1, 0, 2, 0, 1] demoR1_0122021 demoR2_0122021 demoC_0122021 demoM_0122021 demoMir_0122021

theorem demoR1_1122021 : invRung 7 5 20 [1, 1, 2, 2, 0, 2, 1] [1, 1, 2, 2, 0, 2, 1] 1 2 false = ([2, 1, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1122021 : invRung 7 5 20 [1, 1, 2, 2, 0, 2, 1] [2, 1, 1, 0, 2, 2, 1] 3 1 true = ([0, 1, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1122021 : fieldCube 7 5 20 [0, 1, 2, 1, 2, 1, 0] = [2, 0, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_1122021 : fieldMul 7 5 20 [2, 0, 2, 0, 1, 1, 0] [1, 1, 2, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1122021 : specInv 7 5 20 [1, 1, 2, 2, 0, 2, 1] = some [2, 0, 2, 0, 1, 1, 0] :=
  specInv_white_7 [1, 1, 2, 2, 0, 2, 1] [2, 1, 1, 0, 2, 2, 1] [0, 1, 2, 1, 2, 1, 0] [2, 0, 2, 0, 1, 1, 0] demoR1_1122021 demoR2_1122021 demoC_1122021 demoM_1122021

theorem demoR1_2122021 : invRung 7 5 20 [2, 1, 2, 2, 0, 2, 1] [2, 1, 2, 2, 0, 2, 1] 1 2 false = ([1, 2, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_2122021 : invRung 7 5 20 [2, 1, 2, 2, 0, 2, 1] [1, 2, 1, 1, 0, 0, 0] 3 1 true = ([2, 0, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_2122021 : fieldCube 7 5 20 [2, 0, 2, 0, 2, 1, 0] = [0, 0, 1, 2, 1, 0, 0] := by
  decide

theorem demoM_2122021 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 0, 0] [2, 1, 2, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122021 : mirrorTrits [0, 0, 1, 2, 1, 0, 0] = [0, 0, 2, 1, 2, 0, 0] := by
  decide

theorem demoInv_2122021 : specInv 7 5 20 [2, 1, 2, 2, 0, 2, 1] = some [0, 0, 2, 1, 2, 0, 0] :=
  specInv_mirror_7 [2, 1, 2, 2, 0, 2, 1] [1, 2, 1, 1, 0, 0, 0] [2, 0, 2, 0, 2, 1, 0] [0, 0, 1, 2, 1, 0, 0] [0, 0, 2, 1, 2, 0, 0] demoR1_2122021 demoR2_2122021 demoC_2122021 demoM_2122021 demoMir_2122021

theorem demoR1_0222021 : invRung 7 5 20 [0, 2, 2, 2, 0, 2, 1] [0, 2, 2, 2, 0, 2, 1] 1 2 false = ([0, 0, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_0222021 : invRung 7 5 20 [0, 2, 2, 2, 0, 2, 1] [0, 0, 0, 2, 0, 2, 2] 3 1 true = ([0, 0, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_0222021 : fieldCube 7 5 20 [0, 0, 2, 0, 2, 0, 0] = [0, 2, 0, 2, 0, 2, 1] := by
  decide

theorem demoM_0222021 : fieldMul 7 5 20 [0, 2, 0, 2, 0, 2, 1] [0, 2, 2, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0222021 : specInv 7 5 20 [0, 2, 2, 2, 0, 2, 1] = some [0, 2, 0, 2, 0, 2, 1] :=
  specInv_white_7 [0, 2, 2, 2, 0, 2, 1] [0, 0, 0, 2, 0, 2, 2] [0, 0, 2, 0, 2, 0, 0] [0, 2, 0, 2, 0, 2, 1] demoR1_0222021 demoR2_0222021 demoC_0222021 demoM_0222021

theorem demoR1_1222021 : invRung 7 5 20 [1, 2, 2, 2, 0, 2, 1] [1, 2, 2, 2, 0, 2, 1] 1 2 false = ([0, 2, 2, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_1222021 : invRung 7 5 20 [1, 2, 2, 2, 0, 2, 1] [0, 2, 2, 1, 1, 0, 1] 3 1 true = ([1, 1, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_1222021 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 2, 2] = [0, 1, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_1222021 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 1, 1] [1, 2, 2, 2, 0, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222021 : mirrorTrits [0, 1, 0, 0, 1, 1, 1] = [0, 2, 0, 0, 2, 2, 2] := by
  decide

theorem demoInv_1222021 : specInv 7 5 20 [1, 2, 2, 2, 0, 2, 1] = some [0, 2, 0, 0, 2, 2, 2] :=
  specInv_mirror_7 [1, 2, 2, 2, 0, 2, 1] [0, 2, 2, 1, 1, 0, 1] [1, 1, 1, 0, 0, 2, 2] [0, 1, 0, 0, 1, 1, 1] [0, 2, 0, 0, 2, 2, 2] demoR1_1222021 demoR2_1222021 demoC_1222021 demoM_1222021 demoMir_1222021

theorem demoR1_2222021 : invRung 7 5 20 [2, 2, 2, 2, 0, 2, 1] [2, 2, 2, 2, 0, 2, 1] 1 2 false = ([2, 2, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2222021 : invRung 7 5 20 [2, 2, 2, 2, 0, 2, 1] [2, 2, 1, 0, 2, 0, 2] 3 1 true = ([2, 1, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_2222021 : fieldCube 7 5 20 [2, 1, 0, 1, 0, 0, 1] = [0, 1, 0, 2, 1, 2, 1] := by
  decide

theorem demoM_2222021 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 2, 1] [2, 2, 2, 2, 0, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2222021 : specInv 7 5 20 [2, 2, 2, 2, 0, 2, 1] = some [0, 1, 0, 2, 1, 2, 1] :=
  specInv_white_7 [2, 2, 2, 2, 0, 2, 1] [2, 2, 1, 0, 2, 0, 2] [2, 1, 0, 1, 0, 0, 1] [0, 1, 0, 2, 1, 2, 1] demoR1_2222021 demoR2_2222021 demoC_2222021 demoM_2222021

theorem demoR1_0000121 : invRung 7 5 20 [0, 0, 0, 0, 1, 2, 1] [0, 0, 0, 0, 1, 2, 1] 1 2 false = ([1, 1, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_0000121 : invRung 7 5 20 [0, 0, 0, 0, 1, 2, 1] [1, 1, 2, 2, 0, 1, 1] 3 1 true = ([1, 2, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_0000121 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 0, 0] = [1, 1, 0, 0, 0, 1, 2] := by
  decide

theorem demoM_0000121 : fieldMul 7 5 20 [1, 1, 0, 0, 0, 1, 2] [0, 0, 0, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0000121 : specInv 7 5 20 [0, 0, 0, 0, 1, 2, 1] = some [1, 1, 0, 0, 0, 1, 2] :=
  specInv_white_7 [0, 0, 0, 0, 1, 2, 1] [1, 1, 2, 2, 0, 1, 1] [1, 2, 1, 0, 1, 0, 0] [1, 1, 0, 0, 0, 1, 2] demoR1_0000121 demoR2_0000121 demoC_0000121 demoM_0000121

theorem demoR1_1000121 : invRung 7 5 20 [1, 0, 0, 0, 1, 2, 1] [1, 0, 0, 0, 1, 2, 1] 1 2 false = ([0, 1, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1000121 : invRung 7 5 20 [1, 0, 0, 0, 1, 2, 1] [0, 1, 2, 0, 0, 2, 0] 3 1 true = ([0, 0, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_1000121 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 0, 1] = [0, 0, 2, 0, 1, 0, 1] := by
  decide

theorem demoM_1000121 : fieldMul 7 5 20 [0, 0, 2, 0, 1, 0, 1] [1, 0, 0, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000121 : mirrorTrits [0, 0, 2, 0, 1, 0, 1] = [0, 0, 1, 0, 2, 0, 2] := by
  decide

theorem demoInv_1000121 : specInv 7 5 20 [1, 0, 0, 0, 1, 2, 1] = some [0, 0, 1, 0, 2, 0, 2] :=
  specInv_mirror_7 [1, 0, 0, 0, 1, 2, 1] [0, 1, 2, 0, 0, 2, 0] [0, 0, 1, 0, 2, 0, 1] [0, 0, 2, 0, 1, 0, 1] [0, 0, 1, 0, 2, 0, 2] demoR1_1000121 demoR2_1000121 demoC_1000121 demoM_1000121 demoMir_1000121

theorem demoR1_2000121 : invRung 7 5 20 [2, 0, 0, 0, 1, 2, 1] [2, 0, 0, 0, 1, 2, 1] 1 2 false = ([1, 2, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_2000121 : invRung 7 5 20 [2, 0, 0, 0, 1, 2, 1] [1, 2, 1, 1, 1, 0, 1] 3 1 true = ([0, 2, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2000121 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 1, 0] = [1, 2, 1, 0, 1, 2, 2] := by
  decide

theorem demoM_2000121 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 2, 2] [2, 0, 0, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2000121 : specInv 7 5 20 [2, 0, 0, 0, 1, 2, 1] = some [1, 2, 1, 0, 1, 2, 2] :=
  specInv_white_7 [2, 0, 0, 0, 1, 2, 1] [1, 2, 1, 1, 1, 0, 1] [0, 2, 2, 0, 1, 1, 0] [1, 2, 1, 0, 1, 2, 2] demoR1_2000121 demoR2_2000121 demoC_2000121 demoM_2000121

theorem demoR1_0100121 : invRung 7 5 20 [0, 1, 0, 0, 1, 2, 1] [0, 1, 0, 0, 1, 2, 1] 1 2 false = ([2, 1, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_0100121 : invRung 7 5 20 [0, 1, 0, 0, 1, 2, 1] [2, 1, 2, 2, 1, 0, 2] 3 1 true = ([0, 0, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_0100121 : fieldCube 7 5 20 [0, 0, 1, 2, 0, 2, 0] = [1, 2, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_0100121 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 1, 2] [0, 1, 0, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0100121 : specInv 7 5 20 [0, 1, 0, 0, 1, 2, 1] = some [1, 2, 1, 0, 2, 1, 2] :=
  specInv_white_7 [0, 1, 0, 0, 1, 2, 1] [2, 1, 2, 2, 1, 0, 2] [0, 0, 1, 2, 0, 2, 0] [1, 2, 1, 0, 2, 1, 2] demoR1_0100121 demoR2_0100121 demoC_0100121 demoM_0100121

theorem demoR1_1100121 : invRung 7 5 20 [1, 1, 0, 0, 1, 2, 1] [1, 1, 0, 0, 1, 2, 1] 1 2 false = ([1, 2, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_1100121 : invRung 7 5 20 [1, 1, 0, 0, 1, 2, 1] [1, 2, 2, 0, 0, 2, 1] 3 1 true = ([2, 2, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_1100121 : fieldCube 7 5 20 [2, 2, 2, 2, 0, 0, 0] = [1, 0, 2, 2, 0, 2, 2] := by
  decide

theorem demoM_1100121 : fieldMul 7 5 20 [1, 0, 2, 2, 0, 2, 2] [1, 1, 0, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1100121 : specInv 7 5 20 [1, 1, 0, 0, 1, 2, 1] = some [1, 0, 2, 2, 0, 2, 2] :=
  specInv_white_7 [1, 1, 0, 0, 1, 2, 1] [1, 2, 2, 0, 0, 2, 1] [2, 2, 2, 2, 0, 0, 0] [1, 0, 2, 2, 0, 2, 2] demoR1_1100121 demoR2_1100121 demoC_1100121 demoM_1100121

theorem demoR1_2100121 : invRung 7 5 20 [2, 1, 0, 0, 1, 2, 1] [2, 1, 0, 0, 1, 2, 1] 1 2 false = ([1, 0, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_2100121 : invRung 7 5 20 [2, 1, 0, 0, 1, 2, 1] [1, 0, 0, 0, 0, 0, 2] 3 1 true = ([0, 1, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_2100121 : fieldCube 7 5 20 [0, 1, 1, 1, 2, 1, 1] = [2, 1, 1, 1, 2, 2, 0] := by
  decide

theorem demoM_2100121 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 2, 0] [2, 1, 0, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100121 : mirrorTrits [2, 1, 1, 1, 2, 2, 0] = [1, 2, 2, 2, 1, 1, 0] := by
  decide

theorem demoInv_2100121 : specInv 7 5 20 [2, 1, 0, 0, 1, 2, 1] = some [1, 2, 2, 2, 1, 1, 0] :=
  specInv_mirror_7 [2, 1, 0, 0, 1, 2, 1] [1, 0, 0, 0, 0, 0, 2] [0, 1, 1, 1, 2, 1, 1] [2, 1, 1, 1, 2, 2, 0] [1, 2, 2, 2, 1, 1, 0] demoR1_2100121 demoR2_2100121 demoC_2100121 demoM_2100121 demoMir_2100121

theorem demoR1_0200121 : invRung 7 5 20 [0, 2, 0, 0, 1, 2, 1] [0, 2, 0, 0, 1, 2, 1] 1 2 false = ([0, 2, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0200121 : invRung 7 5 20 [0, 2, 0, 0, 1, 2, 1] [0, 2, 2, 1, 2, 1, 2] 3 1 true = ([0, 0, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_0200121 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 2, 0] = [0, 1, 0, 2, 2, 2, 0] := by
  decide

theorem demoM_0200121 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 2, 0] [0, 2, 0, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0200121 : specInv 7 5 20 [0, 2, 0, 0, 1, 2, 1] = some [0, 1, 0, 2, 2, 2, 0] :=
  specInv_white_7 [0, 2, 0, 0, 1, 2, 1] [0, 2, 2, 1, 2, 1, 2] [0, 0, 0, 1, 2, 2, 0] [0, 1, 0, 2, 2, 2, 0] demoR1_0200121 demoR2_0200121 demoC_0200121 demoM_0200121

theorem demoR1_1200121 : invRung 7 5 20 [1, 2, 0, 0, 1, 2, 1] [1, 2, 0, 0, 1, 2, 1] 1 2 false = ([2, 2, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_1200121 : invRung 7 5 20 [1, 2, 0, 0, 1, 2, 1] [2, 2, 2, 0, 2, 0, 2] 3 1 true = ([2, 1, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1200121 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 2, 0] = [2, 2, 0, 1, 2, 0, 0] := by
  decide

theorem demoM_1200121 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 0, 0] [1, 2, 0, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1200121 : specInv 7 5 20 [1, 2, 0, 0, 1, 2, 1] = some [2, 2, 0, 1, 2, 0, 0] :=
  specInv_white_7 [1, 2, 0, 0, 1, 2, 1] [2, 2, 2, 0, 2, 0, 2] [2, 1, 2, 1, 0, 2, 0] [2, 2, 0, 1, 2, 0, 0] demoR1_1200121 demoR2_1200121 demoC_1200121 demoM_1200121

theorem demoR1_2200121 : invRung 7 5 20 [2, 2, 0, 0, 1, 2, 1] [2, 2, 0, 0, 1, 2, 1] 1 2 false = ([1, 1, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_2200121 : invRung 7 5 20 [2, 2, 0, 0, 1, 2, 1] [1, 1, 2, 0, 0, 0, 1] 3 1 true = ([0, 0, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2200121 : fieldCube 7 5 20 [0, 0, 0, 1, 1, 2, 1] = [0, 1, 2, 2, 0, 2, 0] := by
  decide

theorem demoM_2200121 : fieldMul 7 5 20 [0, 1, 2, 2, 0, 2, 0] [2, 2, 0, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2200121 : specInv 7 5 20 [2, 2, 0, 0, 1, 2, 1] = some [0, 1, 2, 2, 0, 2, 0] :=
  specInv_white_7 [2, 2, 0, 0, 1, 2, 1] [1, 1, 2, 0, 0, 0, 1] [0, 0, 0, 1, 1, 2, 1] [0, 1, 2, 2, 0, 2, 0] demoR1_2200121 demoR2_2200121 demoC_2200121 demoM_2200121

theorem demoR1_0010121 : invRung 7 5 20 [0, 0, 1, 0, 1, 2, 1] [0, 0, 1, 0, 1, 2, 1] 1 2 false = ([1, 0, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_0010121 : invRung 7 5 20 [0, 0, 1, 0, 1, 2, 1] [1, 0, 2, 0, 0, 0, 2] 3 1 true = ([0, 0, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_0010121 : fieldCube 7 5 20 [0, 0, 2, 0, 0, 1, 2] = [1, 0, 2, 2, 0, 0, 0] := by
  decide

theorem demoM_0010121 : fieldMul 7 5 20 [1, 0, 2, 2, 0, 0, 0] [0, 0, 1, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010121 : mirrorTrits [1, 0, 2, 2, 0, 0, 0] = [2, 0, 1, 1, 0, 0, 0] := by
  decide

theorem demoInv_0010121 : specInv 7 5 20 [0, 0, 1, 0, 1, 2, 1] = some [2, 0, 1, 1, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 1, 0, 1, 2, 1] [1, 0, 2, 0, 0, 0, 2] [0, 0, 2, 0, 0, 1, 2] [1, 0, 2, 2, 0, 0, 0] [2, 0, 1, 1, 0, 0, 0] demoR1_0010121 demoR2_0010121 demoC_0010121 demoM_0010121 demoMir_0010121

theorem demoR1_1010121 : invRung 7 5 20 [1, 0, 1, 0, 1, 2, 1] [1, 0, 1, 0, 1, 2, 1] 1 2 false = ([2, 0, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1010121 : invRung 7 5 20 [1, 0, 1, 0, 1, 2, 1] [2, 0, 0, 0, 0, 2, 0] 3 1 true = ([0, 1, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_1010121 : fieldCube 7 5 20 [0, 1, 1, 0, 2, 2, 2] = [2, 0, 0, 2, 1, 0, 0] := by
  decide

theorem demoM_1010121 : fieldMul 7 5 20 [2, 0, 0, 2, 1, 0, 0] [1, 0, 1, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1010121 : mirrorTrits [2, 0, 0, 2, 1, 0, 0] = [1, 0, 0, 1, 2, 0, 0] := by
  decide

theorem demoInv_1010121 : specInv 7 5 20 [1, 0, 1, 0, 1, 2, 1] = some [1, 0, 0, 1, 2, 0, 0] :=
  specInv_mirror_7 [1, 0, 1, 0, 1, 2, 1] [2, 0, 0, 0, 0, 2, 0] [0, 1, 1, 0, 2, 2, 2] [2, 0, 0, 2, 1, 0, 0] [1, 0, 0, 1, 2, 0, 0] demoR1_1010121 demoR2_1010121 demoC_1010121 demoM_1010121 demoMir_1010121

theorem demoR1_2010121 : invRung 7 5 20 [2, 0, 1, 0, 1, 2, 1] [2, 0, 1, 0, 1, 2, 1] 1 2 false = ([2, 0, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_2010121 : invRung 7 5 20 [2, 0, 1, 0, 1, 2, 1] [2, 0, 0, 2, 0, 0, 1] 3 1 true = ([2, 2, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_2010121 : fieldCube 7 5 20 [2, 2, 0, 2, 0, 1, 1] = [2, 2, 2, 0, 2, 1, 0] := by
  decide

theorem demoM_2010121 : fieldMul 7 5 20 [2, 2, 2, 0, 2, 1, 0] [2, 0, 1, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010121 : mirrorTrits [2, 2, 2, 0, 2, 1, 0] = [1, 1, 1, 0, 1, 2, 0] := by
  decide

theorem demoInv_2010121 : specInv 7 5 20 [2, 0, 1, 0, 1, 2, 1] = some [1, 1, 1, 0, 1, 2, 0] :=
  specInv_mirror_7 [2, 0, 1, 0, 1, 2, 1] [2, 0, 0, 2, 0, 0, 1] [2, 2, 0, 2, 0, 1, 1] [2, 2, 2, 0, 2, 1, 0] [1, 1, 1, 0, 1, 2, 0] demoR1_2010121 demoR2_2010121 demoC_2010121 demoM_2010121 demoMir_2010121

theorem demoR1_0110121 : invRung 7 5 20 [0, 1, 1, 0, 1, 2, 1] [0, 1, 1, 0, 1, 2, 1] 1 2 false = ([1, 1, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_0110121 : invRung 7 5 20 [0, 1, 1, 0, 1, 2, 1] [1, 1, 1, 2, 1, 1, 1] 3 1 true = ([0, 1, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0110121 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 1, 2] = [0, 1, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_0110121 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 0, 2] [0, 1, 1, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110121 : mirrorTrits [0, 1, 1, 1, 0, 0, 2] = [0, 2, 2, 2, 0, 0, 1] := by
  decide

theorem demoInv_0110121 : specInv 7 5 20 [0, 1, 1, 0, 1, 2, 1] = some [0, 2, 2, 2, 0, 0, 1] :=
  specInv_mirror_7 [0, 1, 1, 0, 1, 2, 1] [1, 1, 1, 2, 1, 1, 1] [0, 1, 0, 2, 1, 1, 2] [0, 1, 1, 1, 0, 0, 2] [0, 2, 2, 2, 0, 0, 1] demoR1_0110121 demoR2_0110121 demoC_0110121 demoM_0110121 demoMir_0110121

theorem demoR1_1110121 : invRung 7 5 20 [1, 1, 1, 0, 1, 2, 1] [1, 1, 1, 0, 1, 2, 1] 1 2 false = ([2, 1, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1110121 : invRung 7 5 20 [1, 1, 1, 0, 1, 2, 1] [2, 1, 0, 1, 1, 2, 1] 3 1 true = ([2, 1, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_1110121 : fieldCube 7 5 20 [2, 1, 1, 1, 1, 2, 2] = [2, 2, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_1110121 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 0, 2] [1, 1, 1, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1110121 : specInv 7 5 20 [1, 1, 1, 0, 1, 2, 1] = some [2, 2, 1, 1, 1, 0, 2] :=
  specInv_white_7 [1, 1, 1, 0, 1, 2, 1] [2, 1, 0, 1, 1, 2, 1] [2, 1, 1, 1, 1, 2, 2] [2, 2, 1, 1, 1, 0, 2] demoR1_1110121 demoR2_1110121 demoC_1110121 demoM_1110121

theorem demoR1_2110121 : invRung 7 5 20 [2, 1, 1, 0, 1, 2, 1] [2, 1, 1, 0, 1, 2, 1] 1 2 false = ([1, 0, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_2110121 : invRung 7 5 20 [2, 1, 1, 0, 1, 2, 1] [1, 0, 0, 1, 1, 1, 1] 3 1 true = ([2, 2, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2110121 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 1, 0] = [1, 0, 2, 1, 1, 1, 1] := by
  decide

theorem demoM_2110121 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 1, 1] [2, 1, 1, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2110121 : specInv 7 5 20 [2, 1, 1, 0, 1, 2, 1] = some [1, 0, 2, 1, 1, 1, 1] :=
  specInv_white_7 [2, 1, 1, 0, 1, 2, 1] [1, 0, 0, 1, 1, 1, 1] [2, 2, 0, 1, 2, 1, 0] [1, 0, 2, 1, 1, 1, 1] demoR1_2110121 demoR2_2110121 demoC_2110121 demoM_2110121

theorem demoR1_0210121 : invRung 7 5 20 [0, 2, 1, 0, 1, 2, 1] [0, 2, 1, 0, 1, 2, 1] 1 2 false = ([2, 2, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0210121 : invRung 7 5 20 [0, 2, 1, 0, 1, 2, 1] [2, 2, 1, 0, 2, 2, 2] 3 1 true = ([0, 0, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0210121 : fieldCube 7 5 20 [0, 0, 2, 0, 0, 1, 1] = [1, 2, 0, 1, 2, 2, 2] := by
  decide

theorem demoM_0210121 : fieldMul 7 5 20 [1, 2, 0, 1, 2, 2, 2] [0, 2, 1, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0210121 : specInv 7 5 20 [0, 2, 1, 0, 1, 2, 1] = some [1, 2, 0, 1, 2, 2, 2] :=
  specInv_white_7 [0, 2, 1, 0, 1, 2, 1] [2, 2, 1, 0, 2, 2, 2] [0, 0, 2, 0, 0, 1, 1] [1, 2, 0, 1, 2, 2, 2] demoR1_0210121 demoR2_0210121 demoC_0210121 demoM_0210121

theorem demoR1_1210121 : invRung 7 5 20 [1, 2, 1, 0, 1, 2, 1] [1, 2, 1, 0, 1, 2, 1] 1 2 false = ([0, 0, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_1210121 : invRung 7 5 20 [1, 2, 1, 0, 1, 2, 1] [0, 0, 1, 2, 1, 1, 2] 3 1 true = ([1, 2, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_1210121 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 0, 2] = [2, 1, 2, 0, 2, 2, 2] := by
  decide

theorem demoM_1210121 : fieldMul 7 5 20 [2, 1, 2, 0, 2, 2, 2] [1, 2, 1, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1210121 : specInv 7 5 20 [1, 2, 1, 0, 1, 2, 1] = some [2, 1, 2, 0, 2, 2, 2] :=
  specInv_white_7 [1, 2, 1, 0, 1, 2, 1] [0, 0, 1, 2, 1, 1, 2] [1, 2, 1, 1, 2, 0, 2] [2, 1, 2, 0, 2, 2, 2] demoR1_1210121 demoR2_1210121 demoC_1210121 demoM_1210121

theorem demoR1_2210121 : invRung 7 5 20 [2, 2, 1, 0, 1, 2, 1] [2, 2, 1, 0, 1, 2, 1] 1 2 false = ([1, 2, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2210121 : invRung 7 5 20 [2, 2, 1, 0, 1, 2, 1] [1, 2, 1, 1, 0, 0, 2] 3 1 true = ([1, 1, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_2210121 : fieldCube 7 5 20 [1, 1, 0, 2, 0, 2, 1] = [2, 0, 0, 2, 0, 2, 2] := by
  decide

theorem demoM_2210121 : fieldMul 7 5 20 [2, 0, 0, 2, 0, 2, 2] [2, 2, 1, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2210121 : specInv 7 5 20 [2, 2, 1, 0, 1, 2, 1] = some [2, 0, 0, 2, 0, 2, 2] :=
  specInv_white_7 [2, 2, 1, 0, 1, 2, 1] [1, 2, 1, 1, 0, 0, 2] [1, 1, 0, 2, 0, 2, 1] [2, 0, 0, 2, 0, 2, 2] demoR1_2210121 demoR2_2210121 demoC_2210121 demoM_2210121

theorem demoR1_0020121 : invRung 7 5 20 [0, 0, 2, 0, 1, 2, 1] [0, 0, 2, 0, 1, 2, 1] 1 2 false = ([2, 2, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_0020121 : invRung 7 5 20 [0, 0, 2, 0, 1, 2, 1] [2, 2, 0, 0, 2, 0, 0] 3 1 true = ([1, 2, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0020121 : fieldCube 7 5 20 [1, 2, 2, 1, 0, 0, 0] = [2, 0, 1, 2, 0, 1, 2] := by
  decide

theorem demoM_0020121 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 1, 2] [0, 0, 2, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020121 : mirrorTrits [2, 0, 1, 2, 0, 1, 2] = [1, 0, 2, 1, 0, 2, 1] := by
  decide

theorem demoInv_0020121 : specInv 7 5 20 [0, 0, 2, 0, 1, 2, 1] = some [1, 0, 2, 1, 0, 2, 1] :=
  specInv_mirror_7 [0, 0, 2, 0, 1, 2, 1] [2, 2, 0, 0, 2, 0, 0] [1, 2, 2, 1, 0, 0, 0] [2, 0, 1, 2, 0, 1, 2] [1, 0, 2, 1, 0, 2, 1] demoR1_0020121 demoR2_0020121 demoC_0020121 demoM_0020121 demoMir_0020121

theorem demoR1_1020121 : invRung 7 5 20 [1, 0, 2, 0, 1, 2, 1] [1, 0, 2, 0, 1, 2, 1] 1 2 false = ([1, 2, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_1020121 : invRung 7 5 20 [1, 0, 2, 0, 1, 2, 1] [1, 2, 0, 2, 2, 0, 2] 3 1 true = ([0, 0, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_1020121 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 2, 1] = [1, 1, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_1020121 : fieldMul 7 5 20 [1, 1, 0, 2, 0, 0, 1] [1, 0, 2, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020121 : mirrorTrits [1, 1, 0, 2, 0, 0, 1] = [2, 2, 0, 1, 0, 0, 2] := by
  decide

theorem demoInv_1020121 : specInv 7 5 20 [1, 0, 2, 0, 1, 2, 1] = some [2, 2, 0, 1, 0, 0, 2] :=
  specInv_mirror_7 [1, 0, 2, 0, 1, 2, 1] [1, 2, 0, 2, 2, 0, 2] [0, 0, 1, 2, 1, 2, 1] [1, 1, 0, 2, 0, 0, 1] [2, 2, 0, 1, 0, 0, 2] demoR1_1020121 demoR2_1020121 demoC_1020121 demoM_1020121 demoMir_1020121

theorem demoR1_2020121 : invRung 7 5 20 [2, 0, 2, 0, 1, 2, 1] [2, 0, 2, 0, 1, 2, 1] 1 2 false = ([2, 1, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2020121 : invRung 7 5 20 [2, 0, 2, 0, 1, 2, 1] [2, 1, 2, 2, 1, 1, 2] 3 1 true = ([2, 0, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_2020121 : fieldCube 7 5 20 [2, 0, 2, 1, 0, 2, 2] = [2, 1, 1, 2, 1, 2, 2] := by
  decide

theorem demoM_2020121 : fieldMul 7 5 20 [2, 1, 1, 2, 1, 2, 2] [2, 0, 2, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2020121 : specInv 7 5 20 [2, 0, 2, 0, 1, 2, 1] = some [2, 1, 1, 2, 1, 2, 2] :=
  specInv_white_7 [2, 0, 2, 0, 1, 2, 1] [2, 1, 2, 2, 1, 1, 2] [2, 0, 2, 1, 0, 2, 2] [2, 1, 1, 2, 1, 2, 2] demoR1_2020121 demoR2_2020121 demoC_2020121 demoM_2020121

theorem demoR1_0120121 : invRung 7 5 20 [0, 1, 2, 0, 1, 2, 1] [0, 1, 2, 0, 1, 2, 1] 1 2 false = ([1, 0, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0120121 : invRung 7 5 20 [0, 1, 2, 0, 1, 2, 1] [1, 0, 0, 0, 2, 2, 2] 3 1 true = ([2, 1, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_0120121 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 1, 1] = [1, 1, 1, 1, 2, 2, 0] := by
  decide

theorem demoM_0120121 : fieldMul 7 5 20 [1, 1, 1, 1, 2, 2, 0] [0, 1, 2, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0120121 : mirrorTrits [1, 1, 1, 1, 2, 2, 0] = [2, 2, 2, 2, 1, 1, 0] := by
  decide

theorem demoInv_0120121 : specInv 7 5 20 [0, 1, 2, 0, 1, 2, 1] = some [2, 2, 2, 2, 1, 1, 0] :=
  specInv_mirror_7 [0, 1, 2, 0, 1, 2, 1] [1, 0, 0, 0, 2, 2, 2] [2, 1, 1, 1, 2, 1, 1] [1, 1, 1, 1, 2, 2, 0] [2, 2, 2, 2, 1, 1, 0] demoR1_0120121 demoR2_0120121 demoC_0120121 demoM_0120121 demoMir_0120121

theorem demoR1_1120121 : invRung 7 5 20 [1, 1, 2, 0, 1, 2, 1] [1, 1, 2, 0, 1, 2, 1] 1 2 false = ([0, 2, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_1120121 : invRung 7 5 20 [1, 1, 2, 0, 1, 2, 1] [0, 2, 2, 0, 0, 2, 2] 3 1 true = ([2, 1, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_1120121 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 0, 0] = [0, 0, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_1120121 : fieldMul 7 5 20 [0, 0, 1, 1, 0, 1, 1] [1, 1, 2, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120121 : mirrorTrits [0, 0, 1, 1, 0, 1, 1] = [0, 0, 2, 2, 0, 2, 2] := by
  decide

theorem demoInv_1120121 : specInv 7 5 20 [1, 1, 2, 0, 1, 2, 1] = some [0, 0, 2, 2, 0, 2, 2] :=
  specInv_mirror_7 [1, 1, 2, 0, 1, 2, 1] [0, 2, 2, 0, 0, 2, 2] [2, 1, 1, 1, 0, 0, 0] [0, 0, 1, 1, 0, 1, 1] [0, 0, 2, 2, 0, 2, 2] demoR1_1120121 demoR2_1120121 demoC_1120121 demoM_1120121 demoMir_1120121

theorem demoR1_2120121 : invRung 7 5 20 [2, 1, 2, 0, 1, 2, 1] [2, 1, 2, 0, 1, 2, 1] 1 2 false = ([0, 2, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_2120121 : invRung 7 5 20 [2, 1, 2, 0, 1, 2, 1] [0, 2, 2, 0, 0, 2, 0] 3 1 true = ([2, 2, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_2120121 : fieldCube 7 5 20 [2, 2, 0, 1, 0, 0, 1] = [0, 1, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_2120121 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 2, 1] [2, 1, 2, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120121 : mirrorTrits [0, 1, 0, 0, 1, 2, 1] = [0, 2, 0, 0, 2, 1, 2] := by
  decide

theorem demoInv_2120121 : specInv 7 5 20 [2, 1, 2, 0, 1, 2, 1] = some [0, 2, 0, 0, 2, 1, 2] :=
  specInv_mirror_7 [2, 1, 2, 0, 1, 2, 1] [0, 2, 2, 0, 0, 2, 0] [2, 2, 0, 1, 0, 0, 1] [0, 1, 0, 0, 1, 2, 1] [0, 2, 0, 0, 2, 1, 2] demoR1_2120121 demoR2_2120121 demoC_2120121 demoM_2120121 demoMir_2120121

theorem demoR1_0220121 : invRung 7 5 20 [0, 2, 2, 0, 1, 2, 1] [0, 2, 2, 0, 1, 2, 1] 1 2 false = ([2, 0, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_0220121 : invRung 7 5 20 [0, 2, 2, 0, 1, 2, 1] [2, 0, 2, 2, 2, 2, 0] 3 1 true = ([0, 2, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0220121 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 0, 0] = [1, 1, 1, 0, 0, 2, 2] := by
  decide

theorem demoM_0220121 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 2, 2] [0, 2, 2, 0, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0220121 : specInv 7 5 20 [0, 2, 2, 0, 1, 2, 1] = some [1, 1, 1, 0, 0, 2, 2] :=
  specInv_white_7 [0, 2, 2, 0, 1, 2, 1] [2, 0, 2, 2, 2, 2, 0] [0, 2, 1, 1, 1, 0, 0] [1, 1, 1, 0, 0, 2, 2] demoR1_0220121 demoR2_0220121 demoC_0220121 demoM_0220121

theorem demoR1_1220121 : invRung 7 5 20 [1, 2, 2, 0, 1, 2, 1] [1, 2, 2, 0, 1, 2, 1] 1 2 false = ([1, 2, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_1220121 : invRung 7 5 20 [1, 2, 2, 0, 1, 2, 1] [1, 2, 0, 1, 0, 1, 2] 3 1 true = ([1, 2, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_1220121 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 2, 0] = [0, 0, 2, 0, 2, 0, 0] := by
  decide

theorem demoM_1220121 : fieldMul 7 5 20 [0, 0, 2, 0, 2, 0, 0] [1, 2, 2, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220121 : mirrorTrits [0, 0, 2, 0, 2, 0, 0] = [0, 0, 1, 0, 1, 0, 0] := by
  decide

theorem demoInv_1220121 : specInv 7 5 20 [1, 2, 2, 0, 1, 2, 1] = some [0, 0, 1, 0, 1, 0, 0] :=
  specInv_mirror_7 [1, 2, 2, 0, 1, 2, 1] [1, 2, 0, 1, 0, 1, 2] [1, 2, 1, 0, 1, 2, 0] [0, 0, 2, 0, 2, 0, 0] [0, 0, 1, 0, 1, 0, 0] demoR1_1220121 demoR2_1220121 demoC_1220121 demoM_1220121 demoMir_1220121

theorem demoR1_2220121 : invRung 7 5 20 [2, 2, 2, 0, 1, 2, 1] [2, 2, 2, 0, 1, 2, 1] 1 2 false = ([0, 1, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_2220121 : invRung 7 5 20 [2, 2, 2, 0, 1, 2, 1] [0, 1, 1, 2, 0, 2, 2] 3 1 true = ([1, 2, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_2220121 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 2, 1] = [2, 1, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_2220121 : fieldMul 7 5 20 [2, 1, 0, 1, 0, 0, 1] [2, 2, 2, 0, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220121 : mirrorTrits [2, 1, 0, 1, 0, 0, 1] = [1, 2, 0, 2, 0, 0, 2] := by
  decide

theorem demoInv_2220121 : specInv 7 5 20 [2, 2, 2, 0, 1, 2, 1] = some [1, 2, 0, 2, 0, 0, 2] :=
  specInv_mirror_7 [2, 2, 2, 0, 1, 2, 1] [0, 1, 1, 2, 0, 2, 2] [1, 2, 1, 2, 1, 2, 1] [2, 1, 0, 1, 0, 0, 1] [1, 2, 0, 2, 0, 0, 2] demoR1_2220121 demoR2_2220121 demoC_2220121 demoM_2220121 demoMir_2220121

theorem demoR1_0001121 : invRung 7 5 20 [0, 0, 0, 1, 1, 2, 1] [0, 0, 0, 1, 1, 2, 1] 1 2 false = ([0, 2, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_0001121 : invRung 7 5 20 [0, 0, 0, 1, 1, 2, 1] [0, 2, 0, 0, 1, 2, 0] 3 1 true = ([0, 1, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_0001121 : fieldCube 7 5 20 [0, 1, 1, 2, 2, 1, 0] = [0, 0, 0, 0, 1, 2, 2] := by
  decide

theorem demoM_0001121 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 2, 2] [0, 0, 0, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0001121 : specInv 7 5 20 [0, 0, 0, 1, 1, 2, 1] = some [0, 0, 0, 0, 1, 2, 2] :=
  specInv_white_7 [0, 0, 0, 1, 1, 2, 1] [0, 2, 0, 0, 1, 2, 0] [0, 1, 1, 2, 2, 1, 0] [0, 0, 0, 0, 1, 2, 2] demoR1_0001121 demoR2_0001121 demoC_0001121 demoM_0001121

theorem demoR1_1001121 : invRung 7 5 20 [1, 0, 0, 1, 1, 2, 1] [1, 0, 0, 1, 1, 2, 1] 1 2 false = ([2, 1, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_1001121 : invRung 7 5 20 [1, 0, 0, 1, 1, 2, 1] [2, 1, 0, 1, 0, 2, 2] 3 1 true = ([0, 2, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_1001121 : fieldCube 7 5 20 [0, 2, 0, 1, 2, 0, 1] = [1, 0, 0, 2, 1, 1, 0] := by
  decide

theorem demoM_1001121 : fieldMul 7 5 20 [1, 0, 0, 2, 1, 1, 0] [1, 0, 0, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1001121 : specInv 7 5 20 [1, 0, 0, 1, 1, 2, 1] = some [1, 0, 0, 2, 1, 1, 0] :=
  specInv_white_7 [1, 0, 0, 1, 1, 2, 1] [2, 1, 0, 1, 0, 2, 2] [0, 2, 0, 1, 2, 0, 1] [1, 0, 0, 2, 1, 1, 0] demoR1_1001121 demoR2_1001121 demoC_1001121 demoM_1001121

theorem demoR1_2001121 : invRung 7 5 20 [2, 0, 0, 1, 1, 2, 1] [2, 0, 0, 1, 1, 2, 1] 1 2 false = ([0, 0, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_2001121 : invRung 7 5 20 [2, 0, 0, 1, 1, 2, 1] [0, 0, 0, 1, 2, 0, 0] 3 1 true = ([0, 2, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2001121 : fieldCube 7 5 20 [0, 2, 0, 1, 1, 2, 1] = [0, 1, 2, 1, 0, 2, 0] := by
  decide

theorem demoM_2001121 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 2, 0] [2, 0, 0, 1, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001121 : mirrorTrits [0, 1, 2, 1, 0, 2, 0] = [0, 2, 1, 2, 0, 1, 0] := by
  decide

theorem demoInv_2001121 : specInv 7 5 20 [2, 0, 0, 1, 1, 2, 1] = some [0, 2, 1, 2, 0, 1, 0] :=
  specInv_mirror_7 [2, 0, 0, 1, 1, 2, 1] [0, 0, 0, 1, 2, 0, 0] [0, 2, 0, 1, 1, 2, 1] [0, 1, 2, 1, 0, 2, 0] [0, 2, 1, 2, 0, 1, 0] demoR1_2001121 demoR2_2001121 demoC_2001121 demoM_2001121 demoMir_2001121

theorem demoR1_0101121 : invRung 7 5 20 [0, 1, 0, 1, 1, 2, 1] [0, 1, 0, 1, 1, 2, 1] 1 2 false = ([2, 0, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_0101121 : invRung 7 5 20 [0, 1, 0, 1, 1, 2, 1] [2, 0, 2, 0, 1, 2, 2] 3 1 true = ([1, 2, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0101121 : fieldCube 7 5 20 [1, 2, 2, 1, 2, 0, 1] = [2, 0, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_0101121 : fieldMul 7 5 20 [2, 0, 0, 2, 1, 1, 2] [0, 1, 0, 1, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101121 : mirrorTrits [2, 0, 0, 2, 1, 1, 2] = [1, 0, 0, 1, 2, 2, 1] := by
  decide

theorem demoInv_0101121 : specInv 7 5 20 [0, 1, 0, 1, 1, 2, 1] = some [1, 0, 0, 1, 2, 2, 1] :=
  specInv_mirror_7 [0, 1, 0, 1, 1, 2, 1] [2, 0, 2, 0, 1, 2, 2] [1, 2, 2, 1, 2, 0, 1] [2, 0, 0, 2, 1, 1, 2] [1, 0, 0, 1, 2, 2, 1] demoR1_0101121 demoR2_0101121 demoC_0101121 demoM_0101121 demoMir_0101121

theorem demoR1_1101121 : invRung 7 5 20 [1, 1, 0, 1, 1, 2, 1] [1, 1, 0, 1, 1, 2, 1] 1 2 false = ([2, 0, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1101121 : invRung 7 5 20 [1, 1, 0, 1, 1, 2, 1] [2, 0, 2, 1, 1, 2, 1] 3 1 true = ([1, 0, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_1101121 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 0, 1] = [0, 2, 1, 2, 1, 1, 0] := by
  decide

theorem demoM_1101121 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 1, 0] [1, 1, 0, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1101121 : specInv 7 5 20 [1, 1, 0, 1, 1, 2, 1] = some [0, 2, 1, 2, 1, 1, 0] :=
  specInv_white_7 [1, 1, 0, 1, 1, 2, 1] [2, 0, 2, 1, 1, 2, 1] [1, 0, 1, 2, 1, 0, 1] [0, 2, 1, 2, 1, 1, 0] demoR1_1101121 demoR2_1101121 demoC_1101121 demoM_1101121

theorem demoR1_2101121 : invRung 7 5 20 [2, 1, 0, 1, 1, 2, 1] [2, 1, 0, 1, 1, 2, 1] 1 2 false = ([0, 2, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_2101121 : invRung 7 5 20 [2, 1, 0, 1, 1, 2, 1] [0, 2, 1, 0, 1, 2, 2] 3 1 true = ([1, 1, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_2101121 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 0, 0] = [1, 2, 0, 0, 0, 2, 2] := by
  decide

theorem demoM_2101121 : fieldMul 7 5 20 [1, 2, 0, 0, 0, 2, 2] [2, 1, 0, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2101121 : specInv 7 5 20 [2, 1, 0, 1, 1, 2, 1] = some [1, 2, 0, 0, 0, 2, 2] :=
  specInv_white_7 [2, 1, 0, 1, 1, 2, 1] [0, 2, 1, 0, 1, 2, 2] [1, 1, 0, 0, 2, 0, 0] [1, 2, 0, 0, 0, 2, 2] demoR1_2101121 demoR2_2101121 demoC_2101121 demoM_2101121

theorem demoR1_0201121 : invRung 7 5 20 [0, 2, 0, 1, 1, 2, 1] [0, 2, 0, 1, 1, 2, 1] 1 2 false = ([1, 0, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_0201121 : invRung 7 5 20 [0, 2, 0, 1, 1, 2, 1] [1, 0, 1, 0, 0, 2, 1] 3 1 true = ([0, 0, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0201121 : fieldCube 7 5 20 [0, 0, 2, 1, 0, 0, 1] = [1, 1, 0, 1, 1, 2, 0] := by
  decide

theorem demoM_0201121 : fieldMul 7 5 20 [1, 1, 0, 1, 1, 2, 0] [0, 2, 0, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0201121 : specInv 7 5 20 [0, 2, 0, 1, 1, 2, 1] = some [1, 1, 0, 1, 1, 2, 0] :=
  specInv_white_7 [0, 2, 0, 1, 1, 2, 1] [1, 0, 1, 0, 0, 2, 1] [0, 0, 2, 1, 0, 0, 1] [1, 1, 0, 1, 1, 2, 0] demoR1_0201121 demoR2_0201121 demoC_0201121 demoM_0201121

theorem demoR1_1201121 : invRung 7 5 20 [1, 2, 0, 1, 1, 2, 1] [1, 2, 0, 1, 1, 2, 1] 1 2 false = ([2, 2, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_1201121 : invRung 7 5 20 [1, 2, 0, 1, 1, 2, 1] [2, 2, 1, 2, 0, 1, 1] 3 1 true = ([2, 2, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1201121 : fieldCube 7 5 20 [2, 2, 0, 2, 0, 1, 0] = [2, 1, 0, 2, 1, 0, 2] := by
  decide

theorem demoM_1201121 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 0, 2] [1, 2, 0, 1, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201121 : mirrorTrits [2, 1, 0, 2, 1, 0, 2] = [1, 2, 0, 1, 2, 0, 1] := by
  decide

theorem demoInv_1201121 : specInv 7 5 20 [1, 2, 0, 1, 1, 2, 1] = some [1, 2, 0, 1, 2, 0, 1] :=
  specInv_mirror_7 [1, 2, 0, 1, 1, 2, 1] [2, 2, 1, 2, 0, 1, 1] [2, 2, 0, 2, 0, 1, 0] [2, 1, 0, 2, 1, 0, 2] [1, 2, 0, 1, 2, 0, 1] demoR1_1201121 demoR2_1201121 demoC_1201121 demoM_1201121 demoMir_1201121

theorem demoR1_2201121 : invRung 7 5 20 [2, 2, 0, 1, 1, 2, 1] [2, 2, 0, 1, 1, 2, 1] 1 2 false = ([0, 2, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_2201121 : invRung 7 5 20 [2, 2, 0, 1, 1, 2, 1] [0, 2, 2, 1, 0, 2, 0] 3 1 true = ([2, 1, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_2201121 : fieldCube 7 5 20 [2, 1, 2, 0, 2, 0, 2] = [2, 1, 1, 2, 2, 1, 0] := by
  decide

theorem demoM_2201121 : fieldMul 7 5 20 [2, 1, 1, 2, 2, 1, 0] [2, 2, 0, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2201121 : specInv 7 5 20 [2, 2, 0, 1, 1, 2, 1] = some [2, 1, 1, 2, 2, 1, 0] :=
  specInv_white_7 [2, 2, 0, 1, 1, 2, 1] [0, 2, 2, 1, 0, 2, 0] [2, 1, 2, 0, 2, 0, 2] [2, 1, 1, 2, 2, 1, 0] demoR1_2201121 demoR2_2201121 demoC_2201121 demoM_2201121

theorem demoR1_0011121 : invRung 7 5 20 [0, 0, 1, 1, 1, 2, 1] [0, 0, 1, 1, 1, 2, 1] 1 2 false = ([2, 0, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_0011121 : invRung 7 5 20 [0, 0, 1, 1, 1, 2, 1] [2, 0, 0, 2, 1, 2, 2] 3 1 true = ([0, 1, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_0011121 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 2, 2] = [1, 2, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_0011121 : fieldMul 7 5 20 [1, 2, 2, 1, 1, 1, 0] [0, 0, 1, 1, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011121 : mirrorTrits [1, 2, 2, 1, 1, 1, 0] = [2, 1, 1, 2, 2, 2, 0] := by
  decide

theorem demoInv_0011121 : specInv 7 5 20 [0, 0, 1, 1, 1, 2, 1] = some [2, 1, 1, 2, 2, 2, 0] :=
  specInv_mirror_7 [0, 0, 1, 1, 1, 2, 1] [2, 0, 0, 2, 1, 2, 2] [0, 1, 2, 2, 1, 2, 2] [1, 2, 2, 1, 1, 1, 0] [2, 1, 1, 2, 2, 2, 0] demoR1_0011121 demoR2_0011121 demoC_0011121 demoM_0011121 demoMir_0011121

theorem demoR1_1011121 : invRung 7 5 20 [1, 0, 1, 1, 1, 2, 1] [1, 0, 1, 1, 1, 2, 1] 1 2 false = ([0, 0, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_1011121 : invRung 7 5 20 [1, 0, 1, 1, 1, 2, 1] [0, 0, 2, 1, 2, 1, 1] 3 1 true = ([1, 2, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_1011121 : fieldCube 7 5 20 [1, 2, 0, 0, 2, 2, 0] = [0, 1, 2, 1, 2, 1, 0] := by
  decide

theorem demoM_1011121 : fieldMul 7 5 20 [0, 1, 2, 1, 2, 1, 0] [1, 0, 1, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1011121 : specInv 7 5 20 [1, 0, 1, 1, 1, 2, 1] = some [0, 1, 2, 1, 2, 1, 0] :=
  specInv_white_7 [1, 0, 1, 1, 1, 2, 1] [0, 0, 2, 1, 2, 1, 1] [1, 2, 0, 0, 2, 2, 0] [0, 1, 2, 1, 2, 1, 0] demoR1_1011121 demoR2_1011121 demoC_1011121 demoM_1011121

theorem demoR1_2011121 : invRung 7 5 20 [2, 0, 1, 1, 1, 2, 1] [2, 0, 1, 1, 1, 2, 1] 1 2 false = ([0, 2, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_2011121 : invRung 7 5 20 [2, 0, 1, 1, 1, 2, 1] [0, 2, 1, 1, 2, 0, 0] 3 1 true = ([1, 0, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_2011121 : fieldCube 7 5 20 [1, 0, 0, 1, 1, 0, 2] = [2, 0, 2, 0, 2, 1, 0] := by
  decide

theorem demoM_2011121 : fieldMul 7 5 20 [2, 0, 2, 0, 2, 1, 0] [2, 0, 1, 1, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011121 : mirrorTrits [2, 0, 2, 0, 2, 1, 0] = [1, 0, 1, 0, 1, 2, 0] := by
  decide

theorem demoInv_2011121 : specInv 7 5 20 [2, 0, 1, 1, 1, 2, 1] = some [1, 0, 1, 0, 1, 2, 0] :=
  specInv_mirror_7 [2, 0, 1, 1, 1, 2, 1] [0, 2, 1, 1, 2, 0, 0] [1, 0, 0, 1, 1, 0, 2] [2, 0, 2, 0, 2, 1, 0] [1, 0, 1, 0, 1, 2, 0] demoR1_2011121 demoR2_2011121 demoC_2011121 demoM_2011121 demoMir_2011121

theorem demoR1_0111121 : invRung 7 5 20 [0, 1, 1, 1, 1, 2, 1] [0, 1, 1, 1, 1, 2, 1] 1 2 false = ([1, 1, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_0111121 : invRung 7 5 20 [0, 1, 1, 1, 1, 2, 1] [1, 1, 0, 2, 0, 0, 2] 3 1 true = ([1, 2, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_0111121 : fieldCube 7 5 20 [1, 2, 0, 2, 0, 0, 0] = [0, 0, 2, 2, 0, 2, 0] := by
  decide

theorem demoM_0111121 : fieldMul 7 5 20 [0, 0, 2, 2, 0, 2, 0] [0, 1, 1, 1, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111121 : mirrorTrits [0, 0, 2, 2, 0, 2, 0] = [0, 0, 1, 1, 0, 1, 0] := by
  decide

theorem demoInv_0111121 : specInv 7 5 20 [0, 1, 1, 1, 1, 2, 1] = some [0, 0, 1, 1, 0, 1, 0] :=
  specInv_mirror_7 [0, 1, 1, 1, 1, 2, 1] [1, 1, 0, 2, 0, 0, 2] [1, 2, 0, 2, 0, 0, 0] [0, 0, 2, 2, 0, 2, 0] [0, 0, 1, 1, 0, 1, 0] demoR1_0111121 demoR2_0111121 demoC_0111121 demoM_0111121 demoMir_0111121

theorem demoR1_1111121 : invRung 7 5 20 [1, 1, 1, 1, 1, 2, 1] [1, 1, 1, 1, 1, 2, 1] 1 2 false = ([0, 1, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_1111121 : invRung 7 5 20 [1, 1, 1, 1, 1, 2, 1] [0, 1, 0, 0, 0, 0, 0] 3 1 true = ([0, 2, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1111121 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 1, 1] = [2, 2, 1, 0, 2, 0, 1] := by
  decide

theorem demoM_1111121 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 0, 1] [1, 1, 1, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1111121 : specInv 7 5 20 [1, 1, 1, 1, 1, 2, 1] = some [2, 2, 1, 0, 2, 0, 1] :=
  specInv_white_7 [1, 1, 1, 1, 1, 2, 1] [0, 1, 0, 0, 0, 0, 0] [0, 2, 1, 1, 0, 1, 1] [2, 2, 1, 0, 2, 0, 1] demoR1_1111121 demoR2_1111121 demoC_1111121 demoM_1111121

theorem demoR1_2111121 : invRung 7 5 20 [2, 1, 1, 1, 1, 2, 1] [2, 1, 1, 1, 1, 2, 1] 1 2 false = ([0, 2, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_2111121 : invRung 7 5 20 [2, 1, 1, 1, 1, 2, 1] [0, 2, 2, 1, 2, 2, 1] 3 1 true = ([0, 1, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_2111121 : fieldCube 7 5 20 [0, 1, 0, 1, 1, 0, 2] = [1, 0, 2, 1, 2, 1, 0] := by
  decide

theorem demoM_2111121 : fieldMul 7 5 20 [1, 0, 2, 1, 2, 1, 0] [2, 1, 1, 1, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2111121 : mirrorTrits [1, 0, 2, 1, 2, 1, 0] = [2, 0, 1, 2, 1, 2, 0] := by
  decide

theorem demoInv_2111121 : specInv 7 5 20 [2, 1, 1, 1, 1, 2, 1] = some [2, 0, 1, 2, 1, 2, 0] :=
  specInv_mirror_7 [2, 1, 1, 1, 1, 2, 1] [0, 2, 2, 1, 2, 2, 1] [0, 1, 0, 1, 1, 0, 2] [1, 0, 2, 1, 2, 1, 0] [2, 0, 1, 2, 1, 2, 0] demoR1_2111121 demoR2_2111121 demoC_2111121 demoM_2111121 demoMir_2111121

theorem demoR1_0211121 : invRung 7 5 20 [0, 2, 1, 1, 1, 2, 1] [0, 2, 1, 1, 1, 2, 1] 1 2 false = ([1, 0, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_0211121 : invRung 7 5 20 [0, 2, 1, 1, 1, 2, 1] [1, 0, 1, 2, 1, 2, 2] 3 1 true = ([1, 1, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_0211121 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 2, 1] = [1, 2, 2, 1, 0, 0, 1] := by
  decide

theorem demoM_0211121 : fieldMul 7 5 20 [1, 2, 2, 1, 0, 0, 1] [0, 2, 1, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0211121 : specInv 7 5 20 [0, 2, 1, 1, 1, 2, 1] = some [1, 2, 2, 1, 0, 0, 1] :=
  specInv_white_7 [0, 2, 1, 1, 1, 2, 1] [1, 0, 1, 2, 1, 2, 2] [1, 1, 0, 1, 2, 2, 1] [1, 2, 2, 1, 0, 0, 1] demoR1_0211121 demoR2_0211121 demoC_0211121 demoM_0211121

theorem demoR1_1211121 : invRung 7 5 20 [1, 2, 1, 1, 1, 2, 1] [1, 2, 1, 1, 1, 2, 1] 1 2 false = ([1, 1, 2, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_1211121 : invRung 7 5 20 [1, 2, 1, 1, 1, 2, 1] [1, 1, 2, 0, 2, 2, 0] 3 1 true = ([1, 0, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_1211121 : fieldCube 7 5 20 [1, 0, 1, 0, 2, 2, 1] = [0, 2, 1, 0, 0, 2, 2] := by
  decide

theorem demoM_1211121 : fieldMul 7 5 20 [0, 2, 1, 0, 0, 2, 2] [1, 2, 1, 1, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1211121 : mirrorTrits [0, 2, 1, 0, 0, 2, 2] = [0, 1, 2, 0, 0, 1, 1] := by
  decide

theorem demoInv_1211121 : specInv 7 5 20 [1, 2, 1, 1, 1, 2, 1] = some [0, 1, 2, 0, 0, 1, 1] :=
  specInv_mirror_7 [1, 2, 1, 1, 1, 2, 1] [1, 1, 2, 0, 2, 2, 0] [1, 0, 1, 0, 2, 2, 1] [0, 2, 1, 0, 0, 2, 2] [0, 1, 2, 0, 0, 1, 1] demoR1_1211121 demoR2_1211121 demoC_1211121 demoM_1211121 demoMir_1211121

theorem demoR1_2211121 : invRung 7 5 20 [2, 2, 1, 1, 1, 2, 1] [2, 2, 1, 1, 1, 2, 1] 1 2 false = ([1, 2, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_2211121 : invRung 7 5 20 [2, 2, 1, 1, 1, 2, 1] [1, 2, 1, 0, 2, 0, 1] 3 1 true = ([0, 1, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_2211121 : fieldCube 7 5 20 [0, 1, 0, 1, 2, 0, 1] = [1, 0, 0, 1, 1, 1, 0] := by
  decide

theorem demoM_2211121 : fieldMul 7 5 20 [1, 0, 0, 1, 1, 1, 0] [2, 2, 1, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2211121 : specInv 7 5 20 [2, 2, 1, 1, 1, 2, 1] = some [1, 0, 0, 1, 1, 1, 0] :=
  specInv_white_7 [2, 2, 1, 1, 1, 2, 1] [1, 2, 1, 0, 2, 0, 1] [0, 1, 0, 1, 2, 0, 1] [1, 0, 0, 1, 1, 1, 0] demoR1_2211121 demoR2_2211121 demoC_2211121 demoM_2211121

theorem demoR1_0021121 : invRung 7 5 20 [0, 0, 2, 1, 1, 2, 1] [0, 0, 2, 1, 1, 2, 1] 1 2 false = ([0, 2, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_0021121 : invRung 7 5 20 [0, 0, 2, 1, 1, 2, 1] [0, 2, 2, 0, 0, 1, 1] 3 1 true = ([0, 0, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_0021121 : fieldCube 7 5 20 [0, 0, 2, 1, 2, 1, 1] = [2, 1, 1, 0, 2, 2, 1] := by
  decide

theorem demoM_0021121 : fieldMul 7 5 20 [2, 1, 1, 0, 2, 2, 1] [0, 0, 2, 1, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021121 : mirrorTrits [2, 1, 1, 0, 2, 2, 1] = [1, 2, 2, 0, 1, 1, 2] := by
  decide

theorem demoInv_0021121 : specInv 7 5 20 [0, 0, 2, 1, 1, 2, 1] = some [1, 2, 2, 0, 1, 1, 2] :=
  specInv_mirror_7 [0, 0, 2, 1, 1, 2, 1] [0, 2, 2, 0, 0, 1, 1] [0, 0, 2, 1, 2, 1, 1] [2, 1, 1, 0, 2, 2, 1] [1, 2, 2, 0, 1, 1, 2] demoR1_0021121 demoR2_0021121 demoC_0021121 demoM_0021121 demoMir_0021121

theorem demoR1_1021121 : invRung 7 5 20 [1, 0, 2, 1, 1, 2, 1] [1, 0, 2, 1, 1, 2, 1] 1 2 false = ([2, 0, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_1021121 : invRung 7 5 20 [1, 0, 2, 1, 1, 2, 1] [2, 0, 1, 0, 0, 2, 2] 3 1 true = ([0, 1, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_1021121 : fieldCube 7 5 20 [0, 1, 0, 0, 2, 1, 1] = [1, 1, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_1021121 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 1, 2] [1, 0, 2, 1, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021121 : mirrorTrits [1, 1, 0, 1, 2, 1, 2] = [2, 2, 0, 2, 1, 2, 1] := by
  decide

theorem demoInv_1021121 : specInv 7 5 20 [1, 0, 2, 1, 1, 2, 1] = some [2, 2, 0, 2, 1, 2, 1] :=
  specInv_mirror_7 [1, 0, 2, 1, 1, 2, 1] [2, 0, 1, 0, 0, 2, 2] [0, 1, 0, 0, 2, 1, 1] [1, 1, 0, 1, 2, 1, 2] [2, 2, 0, 2, 1, 2, 1] demoR1_1021121 demoR2_1021121 demoC_1021121 demoM_1021121 demoMir_1021121

theorem demoR1_2021121 : invRung 7 5 20 [2, 0, 2, 1, 1, 2, 1] [2, 0, 2, 1, 1, 2, 1] 1 2 false = ([0, 2, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_2021121 : invRung 7 5 20 [2, 0, 2, 1, 1, 2, 1] [0, 2, 0, 0, 1, 2, 1] 3 1 true = ([2, 2, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_2021121 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 0, 0] = [2, 2, 0, 1, 0, 2, 0] := by
  decide

theorem demoM_2021121 : fieldMul 7 5 20 [2, 2, 0, 1, 0, 2, 0] [2, 0, 2, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2021121 : specInv 7 5 20 [2, 0, 2, 1, 1, 2, 1] = some [2, 2, 0, 1, 0, 2, 0] :=
  specInv_white_7 [2, 0, 2, 1, 1, 2, 1] [0, 2, 0, 0, 1, 2, 1] [2, 2, 1, 0, 2, 0, 0] [2, 2, 0, 1, 0, 2, 0] demoR1_2021121 demoR2_2021121 demoC_2021121 demoM_2021121

theorem demoR1_0121121 : invRung 7 5 20 [0, 1, 2, 1, 1, 2, 1] [0, 1, 2, 1, 1, 2, 1] 1 2 false = ([2, 2, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_0121121 : invRung 7 5 20 [0, 1, 2, 1, 1, 2, 1] [2, 2, 2, 2, 0, 2, 1] 3 1 true = ([1, 0, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0121121 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 1, 2] = [1, 1, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_0121121 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 0, 1] [0, 1, 2, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0121121 : specInv 7 5 20 [0, 1, 2, 1, 1, 2, 1] = some [1, 1, 1, 0, 0, 0, 1] :=
  specInv_white_7 [0, 1, 2, 1, 1, 2, 1] [2, 2, 2, 2, 0, 2, 1] [1, 0, 2, 2, 1, 1, 2] [1, 1, 1, 0, 0, 0, 1] demoR1_0121121 demoR2_0121121 demoC_0121121 demoM_0121121

theorem demoR1_1121121 : invRung 7 5 20 [1, 1, 2, 1, 1, 2, 1] [1, 1, 2, 1, 1, 2, 1] 1 2 false = ([2, 2, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1121121 : invRung 7 5 20 [1, 1, 2, 1, 1, 2, 1] [2, 2, 0, 0, 0, 2, 0] 3 1 true = ([2, 1, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_1121121 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 1, 1] = [1, 0, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_1121121 : fieldMul 7 5 20 [1, 0, 1, 0, 2, 1, 0] [1, 1, 2, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1121121 : specInv 7 5 20 [1, 1, 2, 1, 1, 2, 1] = some [1, 0, 1, 0, 2, 1, 0] :=
  specInv_white_7 [1, 1, 2, 1, 1, 2, 1] [2, 2, 0, 0, 0, 2, 0] [2, 1, 2, 1, 1, 1, 1] [1, 0, 1, 0, 2, 1, 0] demoR1_1121121 demoR2_1121121 demoC_1121121 demoM_1121121

theorem demoR1_2121121 : invRung 7 5 20 [2, 1, 2, 1, 1, 2, 1] [2, 1, 2, 1, 1, 2, 1] 1 2 false = ([0, 2, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_2121121 : invRung 7 5 20 [2, 1, 2, 1, 1, 2, 1] [0, 2, 0, 0, 1, 0, 0] 3 1 true = ([1, 0, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_2121121 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 0, 0] = [0, 1, 2, 1, 0, 0, 0] := by
  decide

theorem demoM_2121121 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 0, 0] [2, 1, 2, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2121121 : specInv 7 5 20 [2, 1, 2, 1, 1, 2, 1] = some [0, 1, 2, 1, 0, 0, 0] :=
  specInv_white_7 [2, 1, 2, 1, 1, 2, 1] [0, 2, 0, 0, 1, 0, 0] [1, 0, 2, 2, 1, 0, 0] [0, 1, 2, 1, 0, 0, 0] demoR1_2121121 demoR2_2121121 demoC_2121121 demoM_2121121

theorem demoR1_0221121 : invRung 7 5 20 [0, 2, 2, 1, 1, 2, 1] [0, 2, 2, 1, 1, 2, 1] 1 2 false = ([0, 2, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_0221121 : invRung 7 5 20 [0, 2, 2, 1, 1, 2, 1] [0, 2, 1, 1, 2, 2, 1] 3 1 true = ([0, 0, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0221121 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 1, 2] = [2, 2, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_0221121 : fieldMul 7 5 20 [2, 2, 0, 1, 0, 0, 0] [0, 2, 2, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0221121 : specInv 7 5 20 [0, 2, 2, 1, 1, 2, 1] = some [2, 2, 0, 1, 0, 0, 0] :=
  specInv_white_7 [0, 2, 2, 1, 1, 2, 1] [0, 2, 1, 1, 2, 2, 1] [0, 0, 0, 1, 2, 1, 2] [2, 2, 0, 1, 0, 0, 0] demoR1_0221121 demoR2_0221121 demoC_0221121 demoM_0221121

theorem demoR1_1221121 : invRung 7 5 20 [1, 2, 2, 1, 1, 2, 1] [1, 2, 2, 1, 1, 2, 1] 1 2 false = ([1, 2, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1221121 : invRung 7 5 20 [1, 2, 2, 1, 1, 2, 1] [1, 2, 1, 1, 1, 0, 2] 3 1 true = ([0, 1, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1221121 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 1, 1] = [1, 0, 0, 0, 2, 0, 0] := by
  decide

theorem demoM_1221121 : fieldMul 7 5 20 [1, 0, 0, 0, 2, 0, 0] [1, 2, 2, 1, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1221121 : specInv 7 5 20 [1, 2, 2, 1, 1, 2, 1] = some [1, 0, 0, 0, 2, 0, 0] :=
  specInv_white_7 [1, 2, 2, 1, 1, 2, 1] [1, 2, 1, 1, 1, 0, 2] [0, 1, 2, 0, 1, 1, 1] [1, 0, 0, 0, 2, 0, 0] demoR1_1221121 demoR2_1221121 demoC_1221121 demoM_1221121

theorem demoR1_2221121 : invRung 7 5 20 [2, 2, 2, 1, 1, 2, 1] [2, 2, 2, 1, 1, 2, 1] 1 2 false = ([2, 1, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_2221121 : invRung 7 5 20 [2, 2, 2, 1, 1, 2, 1] [2, 1, 2, 2, 1, 1, 1] 3 1 true = ([0, 1, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2221121 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 2, 0] = [0, 2, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_2221121 : fieldMul 7 5 20 [0, 2, 0, 1, 2, 0, 2] [2, 2, 2, 1, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221121 : mirrorTrits [0, 2, 0, 1, 2, 0, 2] = [0, 1, 0, 2, 1, 0, 1] := by
  decide

theorem demoInv_2221121 : specInv 7 5 20 [2, 2, 2, 1, 1, 2, 1] = some [0, 1, 0, 2, 1, 0, 1] :=
  specInv_mirror_7 [2, 2, 2, 1, 1, 2, 1] [2, 1, 2, 2, 1, 1, 1] [0, 1, 1, 1, 0, 2, 0] [0, 2, 0, 1, 2, 0, 2] [0, 1, 0, 2, 1, 0, 1] demoR1_2221121 demoR2_2221121 demoC_2221121 demoM_2221121 demoMir_2221121

theorem demoR1_0002121 : invRung 7 5 20 [0, 0, 0, 2, 1, 2, 1] [0, 0, 0, 2, 1, 2, 1] 1 2 false = ([2, 2, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0002121 : invRung 7 5 20 [0, 0, 0, 2, 1, 2, 1] [2, 2, 1, 2, 0, 0, 0] 3 1 true = ([1, 2, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_0002121 : fieldCube 7 5 20 [1, 2, 1, 1, 1, 1, 0] = [0, 2, 2, 0, 1, 0, 1] := by
  decide

theorem demoM_0002121 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 0, 1] [0, 0, 0, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002121 : mirrorTrits [0, 2, 2, 0, 1, 0, 1] = [0, 1, 1, 0, 2, 0, 2] := by
  decide

theorem demoInv_0002121 : specInv 7 5 20 [0, 0, 0, 2, 1, 2, 1] = some [0, 1, 1, 0, 2, 0, 2] :=
  specInv_mirror_7 [0, 0, 0, 2, 1, 2, 1] [2, 2, 1, 2, 0, 0, 0] [1, 2, 1, 1, 1, 1, 0] [0, 2, 2, 0, 1, 0, 1] [0, 1, 1, 0, 2, 0, 2] demoR1_0002121 demoR2_0002121 demoC_0002121 demoM_0002121 demoMir_0002121

theorem demoR1_1002121 : invRung 7 5 20 [1, 0, 0, 2, 1, 2, 1] [1, 0, 0, 2, 1, 2, 1] 1 2 false = ([1, 2, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_1002121 : invRung 7 5 20 [1, 0, 0, 2, 1, 2, 1] [1, 2, 0, 1, 1, 2, 0] 3 1 true = ([1, 0, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_1002121 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 0, 0] = [2, 1, 1, 1, 0, 2, 0] := by
  decide

theorem demoM_1002121 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 2, 0] [1, 0, 0, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002121 : mirrorTrits [2, 1, 1, 1, 0, 2, 0] = [1, 2, 2, 2, 0, 1, 0] := by
  decide

theorem demoInv_1002121 : specInv 7 5 20 [1, 0, 0, 2, 1, 2, 1] = some [1, 2, 2, 2, 0, 1, 0] :=
  specInv_mirror_7 [1, 0, 0, 2, 1, 2, 1] [1, 2, 0, 1, 1, 2, 0] [1, 0, 2, 1, 1, 0, 0] [2, 1, 1, 1, 0, 2, 0] [1, 2, 2, 2, 0, 1, 0] demoR1_1002121 demoR2_1002121 demoC_1002121 demoM_1002121 demoMir_1002121

theorem demoR1_2002121 : invRung 7 5 20 [2, 0, 0, 2, 1, 2, 1] [2, 0, 0, 2, 1, 2, 1] 1 2 false = ([2, 1, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_2002121 : invRung 7 5 20 [2, 0, 0, 2, 1, 2, 1] [2, 1, 0, 1, 1, 0, 2] 3 1 true = ([1, 1, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_2002121 : fieldCube 7 5 20 [1, 1, 0, 0, 0, 0, 2] = [1, 2, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_2002121 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 2, 2] [2, 0, 0, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002121 : mirrorTrits [1, 2, 1, 0, 2, 2, 2] = [2, 1, 2, 0, 1, 1, 1] := by
  decide

theorem demoInv_2002121 : specInv 7 5 20 [2, 0, 0, 2, 1, 2, 1] = some [2, 1, 2, 0, 1, 1, 1] :=
  specInv_mirror_7 [2, 0, 0, 2, 1, 2, 1] [2, 1, 0, 1, 1, 0, 2] [1, 1, 0, 0, 0, 0, 2] [1, 2, 1, 0, 2, 2, 2] [2, 1, 2, 0, 1, 1, 1] demoR1_2002121 demoR2_2002121 demoC_2002121 demoM_2002121 demoMir_2002121

theorem demoR1_0102121 : invRung 7 5 20 [0, 1, 0, 2, 1, 2, 1] [0, 1, 0, 2, 1, 2, 1] 1 2 false = ([1, 2, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_0102121 : invRung 7 5 20 [0, 1, 0, 2, 1, 2, 1] [1, 2, 1, 0, 1, 2, 0] 3 1 true = ([1, 1, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0102121 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 1, 2] = [2, 2, 2, 2, 0, 2, 1] := by
  decide

theorem demoM_0102121 : fieldMul 7 5 20 [2, 2, 2, 2, 0, 2, 1] [0, 1, 0, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0102121 : specInv 7 5 20 [0, 1, 0, 2, 1, 2, 1] = some [2, 2, 2, 2, 0, 2, 1] :=
  specInv_white_7 [0, 1, 0, 2, 1, 2, 1] [1, 2, 1, 0, 1, 2, 0] [1, 1, 1, 0, 2, 1, 2] [2, 2, 2, 2, 0, 2, 1] demoR1_0102121 demoR2_0102121 demoC_0102121 demoM_0102121

theorem demoR1_1102121 : invRung 7 5 20 [1, 1, 0, 2, 1, 2, 1] [1, 1, 0, 2, 1, 2, 1] 1 2 false = ([2, 0, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_1102121 : invRung 7 5 20 [1, 1, 0, 2, 1, 2, 1] [2, 0, 0, 2, 2, 0, 0] 3 1 true = ([1, 0, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1102121 : fieldCube 7 5 20 [1, 0, 1, 0, 1, 0, 0] = [1, 1, 0, 1, 0, 1, 2] := by
  decide

theorem demoM_1102121 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 1, 2] [1, 1, 0, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1102121 : specInv 7 5 20 [1, 1, 0, 2, 1, 2, 1] = some [1, 1, 0, 1, 0, 1, 2] :=
  specInv_white_7 [1, 1, 0, 2, 1, 2, 1] [2, 0, 0, 2, 2, 0, 0] [1, 0, 1, 0, 1, 0, 0] [1, 1, 0, 1, 0, 1, 2] demoR1_1102121 demoR2_1102121 demoC_1102121 demoM_1102121

theorem demoR1_2102121 : invRung 7 5 20 [2, 1, 0, 2, 1, 2, 1] [2, 1, 0, 2, 1, 2, 1] 1 2 false = ([1, 2, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_2102121 : invRung 7 5 20 [2, 1, 0, 2, 1, 2, 1] [1, 2, 2, 1, 2, 2, 2] 3 1 true = ([0, 1, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_2102121 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 2, 2] = [2, 1, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_2102121 : fieldMul 7 5 20 [2, 1, 0, 0, 1, 1, 1] [2, 1, 0, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2102121 : specInv 7 5 20 [2, 1, 0, 2, 1, 2, 1] = some [2, 1, 0, 0, 1, 1, 1] :=
  specInv_white_7 [2, 1, 0, 2, 1, 2, 1] [1, 2, 2, 1, 2, 2, 2] [0, 1, 1, 0, 0, 2, 2] [2, 1, 0, 0, 1, 1, 1] demoR1_2102121 demoR2_2102121 demoC_2102121 demoM_2102121

theorem demoR1_0202121 : invRung 7 5 20 [0, 2, 0, 2, 1, 2, 1] [0, 2, 0, 2, 1, 2, 1] 1 2 false = ([0, 2, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_0202121 : invRung 7 5 20 [0, 2, 0, 2, 1, 2, 1] [0, 2, 1, 2, 0, 2, 1] 3 1 true = ([1, 2, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_0202121 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 0, 0] = [1, 2, 0, 1, 0, 2, 0] := by
  decide

theorem demoM_0202121 : fieldMul 7 5 20 [1, 2, 0, 1, 0, 2, 0] [0, 2, 0, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202121 : mirrorTrits [1, 2, 0, 1, 0, 2, 0] = [2, 1, 0, 2, 0, 1, 0] := by
  decide

theorem demoInv_0202121 : specInv 7 5 20 [0, 2, 0, 2, 1, 2, 1] = some [2, 1, 0, 2, 0, 1, 0] :=
  specInv_mirror_7 [0, 2, 0, 2, 1, 2, 1] [0, 2, 1, 2, 0, 2, 1] [1, 2, 1, 0, 2, 0, 0] [1, 2, 0, 1, 0, 2, 0] [2, 1, 0, 2, 0, 1, 0] demoR1_0202121 demoR2_0202121 demoC_0202121 demoM_0202121 demoMir_0202121

theorem demoR1_1202121 : invRung 7 5 20 [1, 2, 0, 2, 1, 2, 1] [1, 2, 0, 2, 1, 2, 1] 1 2 false = ([0, 2, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1202121 : invRung 7 5 20 [1, 2, 0, 2, 1, 2, 1] [0, 2, 0, 2, 0, 1, 2] 3 1 true = ([1, 0, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1202121 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 2, 2] = [2, 2, 2, 0, 1, 1, 2] := by
  decide

theorem demoM_1202121 : fieldMul 7 5 20 [2, 2, 2, 0, 1, 1, 2] [1, 2, 0, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202121 : mirrorTrits [2, 2, 2, 0, 1, 1, 2] = [1, 1, 1, 0, 2, 2, 1] := by
  decide

theorem demoInv_1202121 : specInv 7 5 20 [1, 2, 0, 2, 1, 2, 1] = some [1, 1, 1, 0, 2, 2, 1] :=
  specInv_mirror_7 [1, 2, 0, 2, 1, 2, 1] [0, 2, 0, 2, 0, 1, 2] [1, 0, 1, 2, 1, 2, 2] [2, 2, 2, 0, 1, 1, 2] [1, 1, 1, 0, 2, 2, 1] demoR1_1202121 demoR2_1202121 demoC_1202121 demoM_1202121 demoMir_1202121

theorem demoR1_2202121 : invRung 7 5 20 [2, 2, 0, 2, 1, 2, 1] [2, 2, 0, 2, 1, 2, 1] 1 2 false = ([0, 2, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_2202121 : invRung 7 5 20 [2, 2, 0, 2, 1, 2, 1] [0, 2, 1, 1, 2, 0, 2] 3 1 true = ([0, 0, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_2202121 : fieldCube 7 5 20 [0, 0, 1, 1, 1, 1, 1] = [2, 0, 1, 2, 2, 1, 2] := by
  decide

theorem demoM_2202121 : fieldMul 7 5 20 [2, 0, 1, 2, 2, 1, 2] [2, 2, 0, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202121 : mirrorTrits [2, 0, 1, 2, 2, 1, 2] = [1, 0, 2, 1, 1, 2, 1] := by
  decide

theorem demoInv_2202121 : specInv 7 5 20 [2, 2, 0, 2, 1, 2, 1] = some [1, 0, 2, 1, 1, 2, 1] :=
  specInv_mirror_7 [2, 2, 0, 2, 1, 2, 1] [0, 2, 1, 1, 2, 0, 2] [0, 0, 1, 1, 1, 1, 1] [2, 0, 1, 2, 2, 1, 2] [1, 0, 2, 1, 1, 2, 1] demoR1_2202121 demoR2_2202121 demoC_2202121 demoM_2202121 demoMir_2202121

theorem demoR1_0012121 : invRung 7 5 20 [0, 0, 1, 2, 1, 2, 1] [0, 0, 1, 2, 1, 2, 1] 1 2 false = ([0, 2, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_0012121 : invRung 7 5 20 [0, 0, 1, 2, 1, 2, 1] [0, 2, 1, 2, 2, 0, 0] 3 1 true = ([2, 1, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_0012121 : fieldCube 7 5 20 [2, 1, 2, 0, 0, 1, 0] = [0, 1, 1, 1, 1, 1, 1] := by
  decide

theorem demoM_0012121 : fieldMul 7 5 20 [0, 1, 1, 1, 1, 1, 1] [0, 0, 1, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0012121 : specInv 7 5 20 [0, 0, 1, 2, 1, 2, 1] = some [0, 1, 1, 1, 1, 1, 1] :=
  specInv_white_7 [0, 0, 1, 2, 1, 2, 1] [0, 2, 1, 2, 2, 0, 0] [2, 1, 2, 0, 0, 1, 0] [0, 1, 1, 1, 1, 1, 1] demoR1_0012121 demoR2_0012121 demoC_0012121 demoM_0012121

theorem demoR1_1012121 : invRung 7 5 20 [1, 0, 1, 2, 1, 2, 1] [1, 0, 1, 2, 1, 2, 1] 1 2 false = ([1, 1, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1012121 : invRung 7 5 20 [1, 0, 1, 2, 1, 2, 1] [1, 1, 0, 1, 1, 2, 1] 3 1 true = ([0, 2, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_1012121 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 1, 2] = [0, 1, 1, 2, 0, 0, 0] := by
  decide

theorem demoM_1012121 : fieldMul 7 5 20 [0, 1, 1, 2, 0, 0, 0] [1, 0, 1, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1012121 : specInv 7 5 20 [1, 0, 1, 2, 1, 2, 1] = some [0, 1, 1, 2, 0, 0, 0] :=
  specInv_white_7 [1, 0, 1, 2, 1, 2, 1] [1, 1, 0, 1, 1, 2, 1] [0, 2, 1, 2, 1, 1, 2] [0, 1, 1, 2, 0, 0, 0] demoR1_1012121 demoR2_1012121 demoC_1012121 demoM_1012121

theorem demoR1_2012121 : invRung 7 5 20 [2, 0, 1, 2, 1, 2, 1] [2, 0, 1, 2, 1, 2, 1] 1 2 false = ([1, 1, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_2012121 : invRung 7 5 20 [2, 0, 1, 2, 1, 2, 1] [1, 1, 0, 0, 1, 2, 2] 3 1 true = ([2, 1, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_2012121 : fieldCube 7 5 20 [2, 1, 2, 2, 0, 0, 0] = [1, 0, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_2012121 : fieldMul 7 5 20 [1, 0, 2, 1, 0, 2, 2] [2, 0, 1, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2012121 : specInv 7 5 20 [2, 0, 1, 2, 1, 2, 1] = some [1, 0, 2, 1, 0, 2, 2] :=
  specInv_white_7 [2, 0, 1, 2, 1, 2, 1] [1, 1, 0, 0, 1, 2, 2] [2, 1, 2, 2, 0, 0, 0] [1, 0, 2, 1, 0, 2, 2] demoR1_2012121 demoR2_2012121 demoC_2012121 demoM_2012121

theorem demoR1_0112121 : invRung 7 5 20 [0, 1, 1, 2, 1, 2, 1] [0, 1, 1, 2, 1, 2, 1] 1 2 false = ([0, 1, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_0112121 : invRung 7 5 20 [0, 1, 1, 2, 1, 2, 1] [0, 1, 1, 1, 1, 2, 1] 3 1 true = ([1, 0, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0112121 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 0, 2] = [0, 1, 0, 1, 2, 0, 0] := by
  decide

theorem demoM_0112121 : fieldMul 7 5 20 [0, 1, 0, 1, 2, 0, 0] [0, 1, 1, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112121 : mirrorTrits [0, 1, 0, 1, 2, 0, 0] = [0, 2, 0, 2, 1, 0, 0] := by
  decide

theorem demoInv_0112121 : specInv 7 5 20 [0, 1, 1, 2, 1, 2, 1] = some [0, 2, 0, 2, 1, 0, 0] :=
  specInv_mirror_7 [0, 1, 1, 2, 1, 2, 1] [0, 1, 1, 1, 1, 2, 1] [1, 0, 2, 2, 2, 0, 2] [0, 1, 0, 1, 2, 0, 0] [0, 2, 0, 2, 1, 0, 0] demoR1_0112121 demoR2_0112121 demoC_0112121 demoM_0112121 demoMir_0112121

theorem demoR1_1112121 : invRung 7 5 20 [1, 1, 1, 2, 1, 2, 1] [1, 1, 1, 2, 1, 2, 1] 1 2 false = ([0, 0, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_1112121 : invRung 7 5 20 [1, 1, 1, 2, 1, 2, 1] [0, 0, 1, 2, 1, 1, 1] 3 1 true = ([1, 1, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_1112121 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 2, 0] = [0, 2, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_1112121 : fieldMul 7 5 20 [0, 2, 2, 1, 2, 2, 2] [1, 1, 1, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112121 : mirrorTrits [0, 2, 2, 1, 2, 2, 2] = [0, 1, 1, 2, 1, 1, 1] := by
  decide

theorem demoInv_1112121 : specInv 7 5 20 [1, 1, 1, 2, 1, 2, 1] = some [0, 1, 1, 2, 1, 1, 1] :=
  specInv_mirror_7 [1, 1, 1, 2, 1, 2, 1] [0, 0, 1, 2, 1, 1, 1] [1, 1, 1, 0, 0, 2, 0] [0, 2, 2, 1, 2, 2, 2] [0, 1, 1, 2, 1, 1, 1] demoR1_1112121 demoR2_1112121 demoC_1112121 demoM_1112121 demoMir_1112121

theorem demoR1_2112121 : invRung 7 5 20 [2, 1, 1, 2, 1, 2, 1] [2, 1, 1, 2, 1, 2, 1] 1 2 false = ([1, 2, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2112121 : invRung 7 5 20 [2, 1, 1, 2, 1, 2, 1] [1, 2, 1, 2, 2, 0, 1] 3 1 true = ([1, 0, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_2112121 : fieldCube 7 5 20 [1, 0, 1, 0, 2, 1, 1] = [2, 1, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_2112121 : fieldMul 7 5 20 [2, 1, 0, 0, 2, 1, 0] [2, 1, 1, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2112121 : specInv 7 5 20 [2, 1, 1, 2, 1, 2, 1] = some [2, 1, 0, 0, 2, 1, 0] :=
  specInv_white_7 [2, 1, 1, 2, 1, 2, 1] [1, 2, 1, 2, 2, 0, 1] [1, 0, 1, 0, 2, 1, 1] [2, 1, 0, 0, 2, 1, 0] demoR1_2112121 demoR2_2112121 demoC_2112121 demoM_2112121

theorem demoR1_0212121 : invRung 7 5 20 [0, 2, 1, 2, 1, 2, 1] [0, 2, 1, 2, 1, 2, 1] 1 2 false = ([1, 2, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_0212121 : invRung 7 5 20 [0, 2, 1, 2, 1, 2, 1] [1, 2, 2, 1, 1, 0, 0] 3 1 true = ([2, 1, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0212121 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 2, 2] = [2, 2, 1, 1, 1, 0, 0] := by
  decide

theorem demoM_0212121 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 0, 0] [0, 2, 1, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0212121 : specInv 7 5 20 [0, 2, 1, 2, 1, 2, 1] = some [2, 2, 1, 1, 1, 0, 0] :=
  specInv_white_7 [0, 2, 1, 2, 1, 2, 1] [1, 2, 2, 1, 1, 0, 0] [2, 1, 2, 1, 1, 2, 2] [2, 2, 1, 1, 1, 0, 0] demoR1_0212121 demoR2_0212121 demoC_0212121 demoM_0212121

theorem demoR1_1212121 : invRung 7 5 20 [1, 2, 1, 2, 1, 2, 1] [1, 2, 1, 2, 1, 2, 1] 1 2 false = ([0, 2, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_1212121 : invRung 7 5 20 [1, 2, 1, 2, 1, 2, 1] [0, 2, 0, 2, 1, 1, 0] 3 1 true = ([2, 2, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1212121 : fieldCube 7 5 20 [2, 2, 2, 1, 0, 1, 1] = [1, 2, 1, 0, 2, 0, 2] := by
  decide

theorem demoM_1212121 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 0, 2] [1, 2, 1, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1212121 : specInv 7 5 20 [1, 2, 1, 2, 1, 2, 1] = some [1, 2, 1, 0, 2, 0, 2] :=
  specInv_white_7 [1, 2, 1, 2, 1, 2, 1] [0, 2, 0, 2, 1, 1, 0] [2, 2, 2, 1, 0, 1, 1] [1, 2, 1, 0, 2, 0, 2] demoR1_1212121 demoR2_1212121 demoC_1212121 demoM_1212121

theorem demoR1_2212121 : invRung 7 5 20 [2, 2, 1, 2, 1, 2, 1] [2, 2, 1, 2, 1, 2, 1] 1 2 false = ([2, 1, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_2212121 : invRung 7 5 20 [2, 2, 1, 2, 1, 2, 1] [2, 1, 0, 1, 2, 1, 0] 3 1 true = ([1, 1, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_2212121 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 2, 0] = [0, 1, 2, 0, 2, 1, 0] := by
  decide

theorem demoM_2212121 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 1, 0] [2, 2, 1, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2212121 : specInv 7 5 20 [2, 2, 1, 2, 1, 2, 1] = some [0, 1, 2, 0, 2, 1, 0] :=
  specInv_white_7 [2, 2, 1, 2, 1, 2, 1] [2, 1, 0, 1, 2, 1, 0] [1, 1, 0, 0, 2, 2, 0] [0, 1, 2, 0, 2, 1, 0] demoR1_2212121 demoR2_2212121 demoC_2212121 demoM_2212121

theorem demoR1_0022121 : invRung 7 5 20 [0, 0, 2, 2, 1, 2, 1] [0, 0, 2, 2, 1, 2, 1] 1 2 false = ([1, 1, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0022121 : invRung 7 5 20 [0, 0, 2, 2, 1, 2, 1] [1, 1, 1, 1, 0, 0, 0] 3 1 true = ([0, 1, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_0022121 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 2, 1] = [0, 0, 2, 2, 0, 1, 2] := by
  decide

theorem demoM_0022121 : fieldMul 7 5 20 [0, 0, 2, 2, 0, 1, 2] [0, 0, 2, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022121 : mirrorTrits [0, 0, 2, 2, 0, 1, 2] = [0, 0, 1, 1, 0, 2, 1] := by
  decide

theorem demoInv_0022121 : specInv 7 5 20 [0, 0, 2, 2, 1, 2, 1] = some [0, 0, 1, 1, 0, 2, 1] :=
  specInv_mirror_7 [0, 0, 2, 2, 1, 2, 1] [1, 1, 1, 1, 0, 0, 0] [0, 1, 0, 1, 0, 2, 1] [0, 0, 2, 2, 0, 1, 2] [0, 0, 1, 1, 0, 2, 1] demoR1_0022121 demoR2_0022121 demoC_0022121 demoM_0022121 demoMir_0022121

theorem demoR1_1022121 : invRung 7 5 20 [1, 0, 2, 2, 1, 2, 1] [1, 0, 2, 2, 1, 2, 1] 1 2 false = ([0, 2, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_1022121 : invRung 7 5 20 [1, 0, 2, 2, 1, 2, 1] [0, 2, 1, 0, 0, 2, 1] 3 1 true = ([2, 1, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1022121 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 1, 1] = [0, 0, 0, 0, 2, 0, 2] := by
  decide

theorem demoM_1022121 : fieldMul 7 5 20 [0, 0, 0, 0, 2, 0, 2] [1, 0, 2, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1022121 : specInv 7 5 20 [1, 0, 2, 2, 1, 2, 1] = some [0, 0, 0, 0, 2, 0, 2] :=
  specInv_white_7 [1, 0, 2, 2, 1, 2, 1] [0, 2, 1, 0, 0, 2, 1] [2, 1, 1, 0, 1, 1, 1] [0, 0, 0, 0, 2, 0, 2] demoR1_1022121 demoR2_1022121 demoC_1022121 demoM_1022121

theorem demoR1_2022121 : invRung 7 5 20 [2, 0, 2, 2, 1, 2, 1] [2, 0, 2, 2, 1, 2, 1] 1 2 false = ([1, 0, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_2022121 : invRung 7 5 20 [2, 0, 2, 2, 1, 2, 1] [1, 0, 2, 1, 0, 1, 0] 3 1 true = ([0, 1, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_2022121 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 2, 0] = [2, 2, 2, 1, 2, 2, 1] := by
  decide

theorem demoM_2022121 : fieldMul 7 5 20 [2, 2, 2, 1, 2, 2, 1] [2, 0, 2, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022121 : mirrorTrits [2, 2, 2, 1, 2, 2, 1] = [1, 1, 1, 2, 1, 1, 2] := by
  decide

theorem demoInv_2022121 : specInv 7 5 20 [2, 0, 2, 2, 1, 2, 1] = some [1, 1, 1, 2, 1, 1, 2] :=
  specInv_mirror_7 [2, 0, 2, 2, 1, 2, 1] [1, 0, 2, 1, 0, 1, 0] [0, 1, 0, 0, 0, 2, 0] [2, 2, 2, 1, 2, 2, 1] [1, 1, 1, 2, 1, 1, 2] demoR1_2022121 demoR2_2022121 demoC_2022121 demoM_2022121 demoMir_2022121

theorem demoR1_0122121 : invRung 7 5 20 [0, 1, 2, 2, 1, 2, 1] [0, 1, 2, 2, 1, 2, 1] 1 2 false = ([2, 1, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_0122121 : invRung 7 5 20 [0, 1, 2, 2, 1, 2, 1] [2, 1, 0, 0, 2, 1, 1] 3 1 true = ([1, 1, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0122121 : fieldCube 7 5 20 [1, 1, 0, 2, 0, 1, 1] = [1, 2, 2, 2, 2, 1, 0] := by
  decide

theorem demoM_0122121 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 1, 0] [0, 1, 2, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0122121 : specInv 7 5 20 [0, 1, 2, 2, 1, 2, 1] = some [1, 2, 2, 2, 2, 1, 0] :=
  specInv_white_7 [0, 1, 2, 2, 1, 2, 1] [2, 1, 0, 0, 2, 1, 1] [1, 1, 0, 2, 0, 1, 1] [1, 2, 2, 2, 2, 1, 0] demoR1_0122121 demoR2_0122121 demoC_0122121 demoM_0122121

theorem demoR1_1122121 : invRung 7 5 20 [1, 1, 2, 2, 1, 2, 1] [1, 1, 2, 2, 1, 2, 1] 1 2 false = ([0, 1, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1122121 : invRung 7 5 20 [1, 1, 2, 2, 1, 2, 1] [0, 1, 2, 0, 1, 1, 0] 3 1 true = ([2, 1, 0, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_1122121 : fieldCube 7 5 20 [2, 1, 0, 1, 1, 0, 1] = [0, 2, 0, 0, 1, 0, 2] := by
  decide

theorem demoM_1122121 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 0, 2] [1, 1, 2, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1122121 : specInv 7 5 20 [1, 1, 2, 2, 1, 2, 1] = some [0, 2, 0, 0, 1, 0, 2] :=
  specInv_white_7 [1, 1, 2, 2, 1, 2, 1] [0, 1, 2, 0, 1, 1, 0] [2, 1, 0, 1, 1, 0, 1] [0, 2, 0, 0, 1, 0, 2] demoR1_1122121 demoR2_1122121 demoC_1122121 demoM_1122121

theorem demoR1_2122121 : invRung 7 5 20 [2, 1, 2, 2, 1, 2, 1] [2, 1, 2, 2, 1, 2, 1] 1 2 false = ([2, 0, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_2122121 : invRung 7 5 20 [2, 1, 2, 2, 1, 2, 1] [2, 0, 1, 1, 0, 0, 0] 3 1 true = ([0, 2, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_2122121 : fieldCube 7 5 20 [0, 2, 0, 1, 1, 2, 2] = [0, 2, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_2122121 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 0, 1] [2, 1, 2, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122121 : mirrorTrits [0, 2, 1, 2, 1, 0, 1] = [0, 1, 2, 1, 2, 0, 2] := by
  decide

theorem demoInv_2122121 : specInv 7 5 20 [2, 1, 2, 2, 1, 2, 1] = some [0, 1, 2, 1, 2, 0, 2] :=
  specInv_mirror_7 [2, 1, 2, 2, 1, 2, 1] [2, 0, 1, 1, 0, 0, 0] [0, 2, 0, 1, 1, 2, 2] [0, 2, 1, 2, 1, 0, 1] [0, 1, 2, 1, 2, 0, 2] demoR1_2122121 demoR2_2122121 demoC_2122121 demoM_2122121 demoMir_2122121

theorem demoR1_0222121 : invRung 7 5 20 [0, 2, 2, 2, 1, 2, 1] [0, 2, 2, 2, 1, 2, 1] 1 2 false = ([2, 2, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_0222121 : invRung 7 5 20 [0, 2, 2, 2, 1, 2, 1] [2, 2, 1, 0, 2, 2, 0] 3 1 true = ([2, 0, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0222121 : fieldCube 7 5 20 [2, 0, 0, 0, 2, 1, 2] = [0, 2, 2, 1, 0, 2, 0] := by
  decide

theorem demoM_0222121 : fieldMul 7 5 20 [0, 2, 2, 1, 0, 2, 0] [0, 2, 2, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0222121 : specInv 7 5 20 [0, 2, 2, 2, 1, 2, 1] = some [0, 2, 2, 1, 0, 2, 0] :=
  specInv_white_7 [0, 2, 2, 2, 1, 2, 1] [2, 2, 1, 0, 2, 2, 0] [2, 0, 0, 0, 2, 1, 2] [0, 2, 2, 1, 0, 2, 0] demoR1_0222121 demoR2_0222121 demoC_0222121 demoM_0222121

theorem demoR1_1222121 : invRung 7 5 20 [1, 2, 2, 2, 1, 2, 1] [1, 2, 2, 2, 1, 2, 1] 1 2 false = ([2, 2, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_1222121 : invRung 7 5 20 [1, 2, 2, 2, 1, 2, 1] [2, 2, 2, 2, 2, 2, 1] 3 1 true = ([1, 2, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_1222121 : fieldCube 7 5 20 [1, 2, 0, 0, 0, 2, 1] = [0, 0, 1, 0, 0, 0, 2] := by
  decide

theorem demoM_1222121 : fieldMul 7 5 20 [0, 0, 1, 0, 0, 0, 2] [1, 2, 2, 2, 1, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222121 : mirrorTrits [0, 0, 1, 0, 0, 0, 2] = [0, 0, 2, 0, 0, 0, 1] := by
  decide

theorem demoInv_1222121 : specInv 7 5 20 [1, 2, 2, 2, 1, 2, 1] = some [0, 0, 2, 0, 0, 0, 1] :=
  specInv_mirror_7 [1, 2, 2, 2, 1, 2, 1] [2, 2, 2, 2, 2, 2, 1] [1, 2, 0, 0, 0, 2, 1] [0, 0, 1, 0, 0, 0, 2] [0, 0, 2, 0, 0, 0, 1] demoR1_1222121 demoR2_1222121 demoC_1222121 demoM_1222121 demoMir_1222121

theorem demoR1_2222121 : invRung 7 5 20 [2, 2, 2, 2, 1, 2, 1] [2, 2, 2, 2, 1, 2, 1] 1 2 false = ([2, 0, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_2222121 : invRung 7 5 20 [2, 2, 2, 2, 1, 2, 1] [2, 0, 2, 1, 2, 0, 0] 3 1 true = ([0, 2, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_2222121 : fieldCube 7 5 20 [0, 2, 1, 0, 1, 2, 2] = [2, 2, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_2222121 : fieldMul 7 5 20 [2, 2, 0, 2, 1, 2, 2] [2, 2, 2, 2, 1, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2222121 : specInv 7 5 20 [2, 2, 2, 2, 1, 2, 1] = some [2, 2, 0, 2, 1, 2, 2] :=
  specInv_white_7 [2, 2, 2, 2, 1, 2, 1] [2, 0, 2, 1, 2, 0, 0] [0, 2, 1, 0, 1, 2, 2] [2, 2, 0, 2, 1, 2, 2] demoR1_2222121 demoR2_2222121 demoC_2222121 demoM_2222121

theorem demoR1_0000221 : invRung 7 5 20 [0, 0, 0, 0, 2, 2, 1] [0, 0, 0, 0, 2, 2, 1] 1 2 false = ([0, 0, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0000221 : invRung 7 5 20 [0, 0, 0, 0, 2, 2, 1] [0, 0, 2, 0, 1, 1, 1] 3 1 true = ([2, 1, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0000221 : fieldCube 7 5 20 [2, 1, 2, 2, 1, 1, 2] = [2, 1, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_0000221 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 0, 1] [0, 0, 0, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000221 : mirrorTrits [2, 1, 1, 1, 0, 0, 1] = [1, 2, 2, 2, 0, 0, 2] := by
  decide

theorem demoInv_0000221 : specInv 7 5 20 [0, 0, 0, 0, 2, 2, 1] = some [1, 2, 2, 2, 0, 0, 2] :=
  specInv_mirror_7 [0, 0, 0, 0, 2, 2, 1] [0, 0, 2, 0, 1, 1, 1] [2, 1, 2, 2, 1, 1, 2] [2, 1, 1, 1, 0, 0, 1] [1, 2, 2, 2, 0, 0, 2] demoR1_0000221 demoR2_0000221 demoC_0000221 demoM_0000221 demoMir_0000221

theorem demoR1_1000221 : invRung 7 5 20 [1, 0, 0, 0, 2, 2, 1] [1, 0, 0, 0, 2, 2, 1] 1 2 false = ([1, 2, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_1000221 : invRung 7 5 20 [1, 0, 0, 0, 2, 2, 1] [1, 2, 0, 0, 2, 1, 1] 3 1 true = ([1, 1, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_1000221 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 2, 2] = [0, 1, 0, 0, 1, 1, 2] := by
  decide

theorem demoM_1000221 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 1, 2] [1, 0, 0, 0, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1000221 : specInv 7 5 20 [1, 0, 0, 0, 2, 2, 1] = some [0, 1, 0, 0, 1, 1, 2] :=
  specInv_white_7 [1, 0, 0, 0, 2, 2, 1] [1, 2, 0, 0, 2, 1, 1] [1, 1, 2, 0, 0, 2, 2] [0, 1, 0, 0, 1, 1, 2] demoR1_1000221 demoR2_1000221 demoC_1000221 demoM_1000221

theorem demoR1_2000221 : invRung 7 5 20 [2, 0, 0, 0, 2, 2, 1] [2, 0, 0, 0, 2, 2, 1] 1 2 false = ([2, 2, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_2000221 : invRung 7 5 20 [2, 0, 0, 0, 2, 2, 1] [2, 2, 2, 0, 1, 0, 2] 3 1 true = ([0, 0, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_2000221 : fieldCube 7 5 20 [0, 0, 2, 2, 0, 2, 1] = [1, 0, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_2000221 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 2, 1] [2, 0, 0, 0, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2000221 : specInv 7 5 20 [2, 0, 0, 0, 2, 2, 1] = some [1, 0, 0, 1, 0, 2, 1] :=
  specInv_white_7 [2, 0, 0, 0, 2, 2, 1] [2, 2, 2, 0, 1, 0, 2] [0, 0, 2, 2, 0, 2, 1] [1, 0, 0, 1, 0, 2, 1] demoR1_2000221 demoR2_2000221 demoC_2000221 demoM_2000221

theorem demoR1_0100221 : invRung 7 5 20 [0, 1, 0, 0, 2, 2, 1] [0, 1, 0, 0, 2, 2, 1] 1 2 false = ([2, 1, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_0100221 : invRung 7 5 20 [0, 1, 0, 0, 2, 2, 1] [2, 1, 2, 2, 0, 1, 2] 3 1 true = ([1, 0, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0100221 : fieldCube 7 5 20 [1, 0, 1, 1, 0, 1, 1] = [0, 2, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_0100221 : fieldMul 7 5 20 [0, 2, 1, 1, 2, 0, 1] [0, 1, 0, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100221 : mirrorTrits [0, 2, 1, 1, 2, 0, 1] = [0, 1, 2, 2, 1, 0, 2] := by
  decide

theorem demoInv_0100221 : specInv 7 5 20 [0, 1, 0, 0, 2, 2, 1] = some [0, 1, 2, 2, 1, 0, 2] :=
  specInv_mirror_7 [0, 1, 0, 0, 2, 2, 1] [2, 1, 2, 2, 0, 1, 2] [1, 0, 1, 1, 0, 1, 1] [0, 2, 1, 1, 2, 0, 1] [0, 1, 2, 2, 1, 0, 2] demoR1_0100221 demoR2_0100221 demoC_0100221 demoM_0100221 demoMir_0100221

theorem demoR1_1100221 : invRung 7 5 20 [1, 1, 0, 0, 2, 2, 1] [1, 1, 0, 0, 2, 2, 1] 1 2 false = ([1, 1, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_1100221 : invRung 7 5 20 [1, 1, 0, 0, 2, 2, 1] [1, 1, 2, 2, 1, 2, 2] 3 1 true = ([0, 2, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_1100221 : fieldCube 7 5 20 [0, 2, 1, 0, 2, 1, 2] = [1, 2, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_1100221 : fieldMul 7 5 20 [1, 2, 2, 0, 0, 2, 1] [1, 1, 0, 0, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1100221 : specInv 7 5 20 [1, 1, 0, 0, 2, 2, 1] = some [1, 2, 2, 0, 0, 2, 1] :=
  specInv_white_7 [1, 1, 0, 0, 2, 2, 1] [1, 1, 2, 2, 1, 2, 2] [0, 2, 1, 0, 2, 1, 2] [1, 2, 2, 0, 0, 2, 1] demoR1_1100221 demoR2_1100221 demoC_1100221 demoM_1100221

theorem demoR1_2100221 : invRung 7 5 20 [2, 1, 0, 0, 2, 2, 1] [2, 1, 0, 0, 2, 2, 1] 1 2 false = ([2, 1, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_2100221 : invRung 7 5 20 [2, 1, 0, 0, 2, 2, 1] [2, 1, 2, 1, 0, 1, 0] 3 1 true = ([1, 2, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_2100221 : fieldCube 7 5 20 [1, 2, 0, 0, 2, 1, 2] = [2, 2, 2, 0, 0, 2, 0] := by
  decide

theorem demoM_2100221 : fieldMul 7 5 20 [2, 2, 2, 0, 0, 2, 0] [2, 1, 0, 0, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2100221 : specInv 7 5 20 [2, 1, 0, 0, 2, 2, 1] = some [2, 2, 2, 0, 0, 2, 0] :=
  specInv_white_7 [2, 1, 0, 0, 2, 2, 1] [2, 1, 2, 1, 0, 1, 0] [1, 2, 0, 0, 2, 1, 2] [2, 2, 2, 0, 0, 2, 0] demoR1_2100221 demoR2_2100221 demoC_2100221 demoM_2100221

theorem demoR1_0200221 : invRung 7 5 20 [0, 2, 0, 0, 2, 2, 1] [0, 2, 0, 0, 2, 2, 1] 1 2 false = ([1, 1, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_0200221 : invRung 7 5 20 [0, 2, 0, 0, 2, 2, 1] [1, 1, 0, 1, 0, 2, 0] 3 1 true = ([2, 0, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_0200221 : fieldCube 7 5 20 [2, 0, 1, 2, 1, 0, 2] = [1, 0, 0, 0, 2, 2, 1] := by
  decide

theorem demoM_0200221 : fieldMul 7 5 20 [1, 0, 0, 0, 2, 2, 1] [0, 2, 0, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200221 : mirrorTrits [1, 0, 0, 0, 2, 2, 1] = [2, 0, 0, 0, 1, 1, 2] := by
  decide

theorem demoInv_0200221 : specInv 7 5 20 [0, 2, 0, 0, 2, 2, 1] = some [2, 0, 0, 0, 1, 1, 2] :=
  specInv_mirror_7 [0, 2, 0, 0, 2, 2, 1] [1, 1, 0, 1, 0, 2, 0] [2, 0, 1, 2, 1, 0, 2] [1, 0, 0, 0, 2, 2, 1] [2, 0, 0, 0, 1, 1, 2] demoR1_0200221 demoR2_0200221 demoC_0200221 demoM_0200221 demoMir_0200221

theorem demoR1_1200221 : invRung 7 5 20 [1, 2, 0, 0, 2, 2, 1] [1, 2, 0, 0, 2, 2, 1] 1 2 false = ([1, 0, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1200221 : invRung 7 5 20 [1, 2, 0, 0, 2, 2, 1] [1, 0, 2, 2, 0, 0, 1] 3 1 true = ([1, 1, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_1200221 : fieldCube 7 5 20 [1, 1, 2, 2, 1, 1, 2] = [1, 1, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_1200221 : fieldMul 7 5 20 [1, 1, 1, 1, 0, 0, 1] [1, 2, 0, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200221 : mirrorTrits [1, 1, 1, 1, 0, 0, 1] = [2, 2, 2, 2, 0, 0, 2] := by
  decide

theorem demoInv_1200221 : specInv 7 5 20 [1, 2, 0, 0, 2, 2, 1] = some [2, 2, 2, 2, 0, 0, 2] :=
  specInv_mirror_7 [1, 2, 0, 0, 2, 2, 1] [1, 0, 2, 2, 0, 0, 1] [1, 1, 2, 2, 1, 1, 2] [1, 1, 1, 1, 0, 0, 1] [2, 2, 2, 2, 0, 0, 2] demoR1_1200221 demoR2_1200221 demoC_1200221 demoM_1200221 demoMir_1200221

theorem demoR1_2200221 : invRung 7 5 20 [2, 2, 0, 0, 2, 2, 1] [2, 2, 0, 0, 2, 2, 1] 1 2 false = ([2, 1, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_2200221 : invRung 7 5 20 [2, 2, 0, 0, 2, 2, 1] [2, 1, 0, 1, 1, 1, 0] 3 1 true = ([1, 0, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_2200221 : fieldCube 7 5 20 [1, 0, 1, 1, 0, 1, 2] = [0, 0, 0, 2, 0, 1, 2] := by
  decide

theorem demoM_2200221 : fieldMul 7 5 20 [0, 0, 0, 2, 0, 1, 2] [2, 2, 0, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200221 : mirrorTrits [0, 0, 0, 2, 0, 1, 2] = [0, 0, 0, 1, 0, 2, 1] := by
  decide

theorem demoInv_2200221 : specInv 7 5 20 [2, 2, 0, 0, 2, 2, 1] = some [0, 0, 0, 1, 0, 2, 1] :=
  specInv_mirror_7 [2, 2, 0, 0, 2, 2, 1] [2, 1, 0, 1, 1, 1, 0] [1, 0, 1, 1, 0, 1, 2] [0, 0, 0, 2, 0, 1, 2] [0, 0, 0, 1, 0, 2, 1] demoR1_2200221 demoR2_2200221 demoC_2200221 demoM_2200221 demoMir_2200221

theorem demoR1_0010221 : invRung 7 5 20 [0, 0, 1, 0, 2, 2, 1] [0, 0, 1, 0, 2, 2, 1] 1 2 false = ([1, 1, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0010221 : invRung 7 5 20 [0, 0, 1, 0, 2, 2, 1] [1, 1, 1, 2, 0, 0, 0] 3 1 true = ([0, 0, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0010221 : fieldCube 7 5 20 [0, 0, 0, 2, 2, 0, 2] = [2, 1, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_0010221 : fieldMul 7 5 20 [2, 1, 0, 1, 2, 0, 1] [0, 0, 1, 0, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0010221 : specInv 7 5 20 [0, 0, 1, 0, 2, 2, 1] = some [2, 1, 0, 1, 2, 0, 1] :=
  specInv_white_7 [0, 0, 1, 0, 2, 2, 1] [1, 1, 1, 2, 0, 0, 0] [0, 0, 0, 2, 2, 0, 2] [2, 1, 0, 1, 2, 0, 1] demoR1_0010221 demoR2_0010221 demoC_0010221 demoM_0010221

theorem demoR1_1010221 : invRung 7 5 20 [1, 0, 1, 0, 2, 2, 1] [1, 0, 1, 0, 2, 2, 1] 1 2 false = ([0, 2, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_1010221 : invRung 7 5 20 [1, 0, 1, 0, 2, 2, 1] [0, 2, 2, 1, 0, 2, 1] 3 1 true = ([0, 1, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_1010221 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 1, 1] = [0, 0, 2, 0, 2, 2, 0] := by
  decide

theorem demoM_1010221 : fieldMul 7 5 20 [0, 0, 2, 0, 2, 2, 0] [1, 0, 1, 0, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1010221 : specInv 7 5 20 [1, 0, 1, 0, 2, 2, 1] = some [0, 0, 2, 0, 2, 2, 0] :=
  specInv_white_7 [1, 0, 1, 0, 2, 2, 1] [0, 2, 2, 1, 0, 2, 1] [0, 1, 2, 2, 1, 1, 1] [0, 0, 2, 0, 2, 2, 0] demoR1_1010221 demoR2_1010221 demoC_1010221 demoM_1010221

theorem demoR1_2010221 : invRung 7 5 20 [2, 0, 1, 0, 2, 2, 1] [2, 0, 1, 0, 2, 2, 1] 1 2 false = ([2, 0, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_2010221 : invRung 7 5 20 [2, 0, 1, 0, 2, 2, 1] [2, 0, 1, 2, 0, 2, 1] 3 1 true = ([1, 1, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_2010221 : fieldCube 7 5 20 [1, 1, 2, 2, 1, 1, 0] = [1, 2, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_2010221 : fieldMul 7 5 20 [1, 2, 0, 2, 1, 1, 2] [2, 0, 1, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010221 : mirrorTrits [1, 2, 0, 2, 1, 1, 2] = [2, 1, 0, 1, 2, 2, 1] := by
  decide

theorem demoInv_2010221 : specInv 7 5 20 [2, 0, 1, 0, 2, 2, 1] = some [2, 1, 0, 1, 2, 2, 1] :=
  specInv_mirror_7 [2, 0, 1, 0, 2, 2, 1] [2, 0, 1, 2, 0, 2, 1] [1, 1, 2, 2, 1, 1, 0] [1, 2, 0, 2, 1, 1, 2] [2, 1, 0, 1, 2, 2, 1] demoR1_2010221 demoR2_2010221 demoC_2010221 demoM_2010221 demoMir_2010221

theorem demoR1_0110221 : invRung 7 5 20 [0, 1, 1, 0, 2, 2, 1] [0, 1, 1, 0, 2, 2, 1] 1 2 false = ([2, 0, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0110221 : invRung 7 5 20 [0, 1, 1, 0, 2, 2, 1] [2, 0, 1, 1, 1, 1, 2] 3 1 true = ([0, 1, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_0110221 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 0, 0] = [0, 1, 0, 2, 0, 1, 0] := by
  decide

theorem demoM_0110221 : fieldMul 7 5 20 [0, 1, 0, 2, 0, 1, 0] [0, 1, 1, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110221 : mirrorTrits [0, 1, 0, 2, 0, 1, 0] = [0, 2, 0, 1, 0, 2, 0] := by
  decide

theorem demoInv_0110221 : specInv 7 5 20 [0, 1, 1, 0, 2, 2, 1] = some [0, 2, 0, 1, 0, 2, 0] :=
  specInv_mirror_7 [0, 1, 1, 0, 2, 2, 1] [2, 0, 1, 1, 1, 1, 2] [0, 1, 2, 0, 1, 0, 0] [0, 1, 0, 2, 0, 1, 0] [0, 2, 0, 1, 0, 2, 0] demoR1_0110221 demoR2_0110221 demoC_0110221 demoM_0110221 demoMir_0110221

theorem demoR1_1110221 : invRung 7 5 20 [1, 1, 1, 0, 2, 2, 1] [1, 1, 1, 0, 2, 2, 1] 1 2 false = ([2, 1, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_1110221 : invRung 7 5 20 [1, 1, 1, 0, 2, 2, 1] [2, 1, 2, 2, 2, 2, 2] 3 1 true = ([1, 1, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_1110221 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 1, 1] = [2, 1, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_1110221 : fieldMul 7 5 20 [2, 1, 0, 1, 2, 1, 2] [1, 1, 1, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1110221 : mirrorTrits [2, 1, 0, 1, 2, 1, 2] = [1, 2, 0, 2, 1, 2, 1] := by
  decide

theorem demoInv_1110221 : specInv 7 5 20 [1, 1, 1, 0, 2, 2, 1] = some [1, 2, 0, 2, 1, 2, 1] :=
  specInv_mirror_7 [1, 1, 1, 0, 2, 2, 1] [2, 1, 2, 2, 2, 2, 2] [1, 1, 0, 0, 2, 1, 1] [2, 1, 0, 1, 2, 1, 2] [1, 2, 0, 2, 1, 2, 1] demoR1_1110221 demoR2_1110221 demoC_1110221 demoM_1110221 demoMir_1110221

theorem demoR1_2110221 : invRung 7 5 20 [2, 1, 1, 0, 2, 2, 1] [2, 1, 1, 0, 2, 2, 1] 1 2 false = ([1, 1, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_2110221 : invRung 7 5 20 [2, 1, 1, 0, 2, 2, 1] [1, 1, 0, 1, 0, 0, 1] 3 1 true = ([1, 0, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_2110221 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 1, 1] = [0, 0, 1, 2, 2, 1, 2] := by
  decide

theorem demoM_2110221 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 1, 2] [2, 1, 1, 0, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2110221 : specInv 7 5 20 [2, 1, 1, 0, 2, 2, 1] = some [0, 0, 1, 2, 2, 1, 2] :=
  specInv_white_7 [2, 1, 1, 0, 2, 2, 1] [1, 1, 0, 1, 0, 0, 1] [1, 0, 1, 1, 1, 1, 1] [0, 0, 1, 2, 2, 1, 2] demoR1_2110221 demoR2_2110221 demoC_2110221 demoM_2110221

theorem demoR1_0210221 : invRung 7 5 20 [0, 2, 1, 0, 2, 2, 1] [0, 2, 1, 0, 2, 2, 1] 1 2 false = ([1, 0, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_0210221 : invRung 7 5 20 [0, 2, 1, 0, 2, 2, 1] [1, 0, 0, 0, 0, 1, 1] 3 1 true = ([1, 2, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_0210221 : fieldCube 7 5 20 [1, 2, 1, 1, 1, 0, 1] = [2, 2, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_0210221 : fieldMul 7 5 20 [2, 2, 0, 1, 1, 0, 0] [0, 2, 1, 0, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0210221 : specInv 7 5 20 [0, 2, 1, 0, 2, 2, 1] = some [2, 2, 0, 1, 1, 0, 0] :=
  specInv_white_7 [0, 2, 1, 0, 2, 2, 1] [1, 0, 0, 0, 0, 1, 1] [1, 2, 1, 1, 1, 0, 1] [2, 2, 0, 1, 1, 0, 0] demoR1_0210221 demoR2_0210221 demoC_0210221 demoM_0210221

theorem demoR1_1210221 : invRung 7 5 20 [1, 2, 1, 0, 2, 2, 1] [1, 2, 1, 0, 2, 2, 1] 1 2 false = ([2, 2, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_1210221 : invRung 7 5 20 [1, 2, 1, 0, 2, 2, 1] [2, 2, 1, 1, 1, 0, 1] 3 1 true = ([1, 1, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_1210221 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 1, 1] = [2, 1, 0, 1, 2, 1, 0] := by
  decide

theorem demoM_1210221 : fieldMul 7 5 20 [2, 1, 0, 1, 2, 1, 0] [1, 2, 1, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1210221 : mirrorTrits [2, 1, 0, 1, 2, 1, 0] = [1, 2, 0, 2, 1, 2, 0] := by
  decide

theorem demoInv_1210221 : specInv 7 5 20 [1, 2, 1, 0, 2, 2, 1] = some [1, 2, 0, 2, 1, 2, 0] :=
  specInv_mirror_7 [1, 2, 1, 0, 2, 2, 1] [2, 2, 1, 1, 1, 0, 1] [1, 1, 1, 0, 2, 1, 1] [2, 1, 0, 1, 2, 1, 0] [1, 2, 0, 2, 1, 2, 0] demoR1_1210221 demoR2_1210221 demoC_1210221 demoM_1210221 demoMir_1210221

theorem demoR1_2210221 : invRung 7 5 20 [2, 2, 1, 0, 2, 2, 1] [2, 2, 1, 0, 2, 2, 1] 1 2 false = ([1, 2, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_2210221 : invRung 7 5 20 [2, 2, 1, 0, 2, 2, 1] [1, 2, 1, 2, 2, 1, 0] 3 1 true = ([2, 1, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_2210221 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 0, 1] = [1, 0, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_2210221 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 2, 0] [2, 2, 1, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210221 : mirrorTrits [1, 0, 1, 1, 1, 2, 0] = [2, 0, 2, 2, 2, 1, 0] := by
  decide

theorem demoInv_2210221 : specInv 7 5 20 [2, 2, 1, 0, 2, 2, 1] = some [2, 0, 2, 2, 2, 1, 0] :=
  specInv_mirror_7 [2, 2, 1, 0, 2, 2, 1] [1, 2, 1, 2, 2, 1, 0] [2, 1, 0, 2, 2, 0, 1] [1, 0, 1, 1, 1, 2, 0] [2, 0, 2, 2, 2, 1, 0] demoR1_2210221 demoR2_2210221 demoC_2210221 demoM_2210221 demoMir_2210221

theorem demoR1_0020221 : invRung 7 5 20 [0, 0, 2, 0, 2, 2, 1] [0, 0, 2, 0, 2, 2, 1] 1 2 false = ([0, 0, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_0020221 : invRung 7 5 20 [0, 0, 2, 0, 2, 2, 1] [0, 0, 1, 1, 2, 1, 0] 3 1 true = ([0, 0, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_0020221 : fieldCube 7 5 20 [0, 0, 0, 2, 0, 2, 2] = [1, 1, 2, 2, 1, 0, 0] := by
  decide

theorem demoM_0020221 : fieldMul 7 5 20 [1, 1, 2, 2, 1, 0, 0] [0, 0, 2, 0, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0020221 : specInv 7 5 20 [0, 0, 2, 0, 2, 2, 1] = some [1, 1, 2, 2, 1, 0, 0] :=
  specInv_white_7 [0, 0, 2, 0, 2, 2, 1] [0, 0, 1, 1, 2, 1, 0] [0, 0, 0, 2, 0, 2, 2] [1, 1, 2, 2, 1, 0, 0] demoR1_0020221 demoR2_0020221 demoC_0020221 demoM_0020221

theorem demoR1_1020221 : invRung 7 5 20 [1, 0, 2, 0, 2, 2, 1] [1, 0, 2, 0, 2, 2, 1] 1 2 false = ([2, 0, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_1020221 : invRung 7 5 20 [1, 0, 2, 0, 2, 2, 1] [2, 0, 0, 2, 1, 2, 1] 3 1 true = ([2, 2, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1020221 : fieldCube 7 5 20 [2, 2, 1, 0, 1, 1, 1] = [0, 0, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_1020221 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 0, 2] [1, 0, 2, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020221 : mirrorTrits [0, 0, 0, 1, 2, 0, 2] = [0, 0, 0, 2, 1, 0, 1] := by
  decide

theorem demoInv_1020221 : specInv 7 5 20 [1, 0, 2, 0, 2, 2, 1] = some [0, 0, 0, 2, 1, 0, 1] :=
  specInv_mirror_7 [1, 0, 2, 0, 2, 2, 1] [2, 0, 0, 2, 1, 2, 1] [2, 2, 1, 0, 1, 1, 1] [0, 0, 0, 1, 2, 0, 2] [0, 0, 0, 2, 1, 0, 1] demoR1_1020221 demoR2_1020221 demoC_1020221 demoM_1020221 demoMir_1020221

theorem demoR1_2020221 : invRung 7 5 20 [2, 0, 2, 0, 2, 2, 1] [2, 0, 2, 0, 2, 2, 1] 1 2 false = ([1, 2, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_2020221 : invRung 7 5 20 [2, 0, 2, 0, 2, 2, 1] [1, 2, 0, 1, 2, 0, 2] 3 1 true = ([0, 2, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_2020221 : fieldCube 7 5 20 [0, 2, 1, 0, 1, 2, 1] = [2, 1, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_2020221 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 1, 1] [2, 0, 2, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020221 : mirrorTrits [2, 1, 1, 1, 0, 1, 1] = [1, 2, 2, 2, 0, 2, 2] := by
  decide

theorem demoInv_2020221 : specInv 7 5 20 [2, 0, 2, 0, 2, 2, 1] = some [1, 2, 2, 2, 0, 2, 2] :=
  specInv_mirror_7 [2, 0, 2, 0, 2, 2, 1] [1, 2, 0, 1, 2, 0, 2] [0, 2, 1, 0, 1, 2, 1] [2, 1, 1, 1, 0, 1, 1] [1, 2, 2, 2, 0, 2, 2] demoR1_2020221 demoR2_2020221 demoC_2020221 demoM_2020221 demoMir_2020221

theorem demoR1_0120221 : invRung 7 5 20 [0, 1, 2, 0, 2, 2, 1] [0, 1, 2, 0, 2, 2, 1] 1 2 false = ([0, 2, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_0120221 : invRung 7 5 20 [0, 1, 2, 0, 2, 2, 1] [0, 2, 0, 2, 1, 2, 2] 3 1 true = ([1, 2, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0120221 : fieldCube 7 5 20 [1, 2, 0, 1, 0, 0, 0] = [2, 0, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_0120221 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 1, 0] [0, 1, 2, 0, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0120221 : specInv 7 5 20 [0, 1, 2, 0, 2, 2, 1] = some [2, 0, 1, 2, 0, 1, 0] :=
  specInv_white_7 [0, 1, 2, 0, 2, 2, 1] [0, 2, 0, 2, 1, 2, 2] [1, 2, 0, 1, 0, 0, 0] [2, 0, 1, 2, 0, 1, 0] demoR1_0120221 demoR2_0120221 demoC_0120221 demoM_0120221

theorem demoR1_1120221 : invRung 7 5 20 [1, 1, 2, 0, 2, 2, 1] [1, 1, 2, 0, 2, 2, 1] 1 2 false = ([0, 1, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_1120221 : invRung 7 5 20 [1, 1, 2, 0, 2, 2, 1] [0, 1, 0, 1, 2, 0, 1] 3 1 true = ([1, 1, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_1120221 : fieldCube 7 5 20 [1, 1, 1, 2, 2, 1, 2] = [1, 2, 1, 2, 0, 1, 1] := by
  decide

theorem demoM_1120221 : fieldMul 7 5 20 [1, 2, 1, 2, 0, 1, 1] [1, 1, 2, 0, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1120221 : specInv 7 5 20 [1, 1, 2, 0, 2, 2, 1] = some [1, 2, 1, 2, 0, 1, 1] :=
  specInv_white_7 [1, 1, 2, 0, 2, 2, 1] [0, 1, 0, 1, 2, 0, 1] [1, 1, 1, 2, 2, 1, 2] [1, 2, 1, 2, 0, 1, 1] demoR1_1120221 demoR2_1120221 demoC_1120221 demoM_1120221

theorem demoR1_2120221 : invRung 7 5 20 [2, 1, 2, 0, 2, 2, 1] [2, 1, 2, 0, 2, 2, 1] 1 2 false = ([2, 1, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2120221 : invRung 7 5 20 [2, 1, 2, 0, 2, 2, 1] [2, 1, 0, 0, 2, 0, 0] 3 1 true = ([1, 0, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2120221 : fieldCube 7 5 20 [1, 0, 0, 0, 1, 0, 0] = [1, 1, 0, 1, 0, 1, 1] := by
  decide

theorem demoM_2120221 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 1, 1] [2, 1, 2, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120221 : mirrorTrits [1, 1, 0, 1, 0, 1, 1] = [2, 2, 0, 2, 0, 2, 2] := by
  decide

theorem demoInv_2120221 : specInv 7 5 20 [2, 1, 2, 0, 2, 2, 1] = some [2, 2, 0, 2, 0, 2, 2] :=
  specInv_mirror_7 [2, 1, 2, 0, 2, 2, 1] [2, 1, 0, 0, 2, 0, 0] [1, 0, 0, 0, 1, 0, 0] [1, 1, 0, 1, 0, 1, 1] [2, 2, 0, 2, 0, 2, 2] demoR1_2120221 demoR2_2120221 demoC_2120221 demoM_2120221 demoMir_2120221

theorem demoR1_0220221 : invRung 7 5 20 [0, 2, 2, 0, 2, 2, 1] [0, 2, 2, 0, 2, 2, 1] 1 2 false = ([2, 1, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_0220221 : invRung 7 5 20 [0, 2, 2, 0, 2, 2, 1] [2, 1, 2, 0, 1, 0, 1] 3 1 true = ([0, 2, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_0220221 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 1, 1] = [2, 0, 1, 1, 2, 1, 0] := by
  decide

theorem demoM_0220221 : fieldMul 7 5 20 [2, 0, 1, 1, 2, 1, 0] [0, 2, 2, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0220221 : mirrorTrits [2, 0, 1, 1, 2, 1, 0] = [1, 0, 2, 2, 1, 2, 0] := by
  decide

theorem demoInv_0220221 : specInv 7 5 20 [0, 2, 2, 0, 2, 2, 1] = some [1, 0, 2, 2, 1, 2, 0] :=
  specInv_mirror_7 [0, 2, 2, 0, 2, 2, 1] [2, 1, 2, 0, 1, 0, 1] [0, 2, 2, 1, 1, 1, 1] [2, 0, 1, 1, 2, 1, 0] [1, 0, 2, 2, 1, 2, 0] demoR1_0220221 demoR2_0220221 demoC_0220221 demoM_0220221 demoMir_0220221

theorem demoR1_1220221 : invRung 7 5 20 [1, 2, 2, 0, 2, 2, 1] [1, 2, 2, 0, 2, 2, 1] 1 2 false = ([0, 0, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_1220221 : invRung 7 5 20 [1, 2, 2, 0, 2, 2, 1] [0, 0, 0, 1, 0, 0, 2] 3 1 true = ([1, 0, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1220221 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 2, 0] = [1, 2, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_1220221 : fieldMul 7 5 20 [1, 2, 0, 0, 2, 0, 1] [1, 2, 2, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220221 : mirrorTrits [1, 2, 0, 0, 2, 0, 1] = [2, 1, 0, 0, 1, 0, 2] := by
  decide

theorem demoInv_1220221 : specInv 7 5 20 [1, 2, 2, 0, 2, 2, 1] = some [2, 1, 0, 0, 1, 0, 2] :=
  specInv_mirror_7 [1, 2, 2, 0, 2, 2, 1] [0, 0, 0, 1, 0, 0, 2] [1, 0, 0, 1, 0, 2, 0] [1, 2, 0, 0, 2, 0, 1] [2, 1, 0, 0, 1, 0, 2] demoR1_1220221 demoR2_1220221 demoC_1220221 demoM_1220221 demoMir_1220221

theorem demoR1_2220221 : invRung 7 5 20 [2, 2, 2, 0, 2, 2, 1] [2, 2, 2, 0, 2, 2, 1] 1 2 false = ([2, 2, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_2220221 : invRung 7 5 20 [2, 2, 2, 0, 2, 2, 1] [2, 2, 0, 1, 1, 1, 0] 3 1 true = ([2, 0, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_2220221 : fieldCube 7 5 20 [2, 0, 1, 0, 0, 0, 0] = [2, 0, 0, 0, 0, 0, 1] := by
  decide

theorem demoM_2220221 : fieldMul 7 5 20 [2, 0, 0, 0, 0, 0, 1] [2, 2, 2, 0, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220221 : mirrorTrits [2, 0, 0, 0, 0, 0, 1] = [1, 0, 0, 0, 0, 0, 2] := by
  decide

theorem demoInv_2220221 : specInv 7 5 20 [2, 2, 2, 0, 2, 2, 1] = some [1, 0, 0, 0, 0, 0, 2] :=
  specInv_mirror_7 [2, 2, 2, 0, 2, 2, 1] [2, 2, 0, 1, 1, 1, 0] [2, 0, 1, 0, 0, 0, 0] [2, 0, 0, 0, 0, 0, 1] [1, 0, 0, 0, 0, 0, 2] demoR1_2220221 demoR2_2220221 demoC_2220221 demoM_2220221 demoMir_2220221

theorem demoR1_0001221 : invRung 7 5 20 [0, 0, 0, 1, 2, 2, 1] [0, 0, 0, 1, 2, 2, 1] 1 2 false = ([0, 2, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_0001221 : invRung 7 5 20 [0, 0, 0, 1, 2, 2, 1] [0, 2, 2, 0, 1, 0, 1] 3 1 true = ([1, 2, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_0001221 : fieldCube 7 5 20 [1, 2, 0, 0, 1, 0, 0] = [1, 1, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_0001221 : fieldMul 7 5 20 [1, 1, 0, 0, 0, 1, 1] [0, 0, 0, 1, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0001221 : specInv 7 5 20 [0, 0, 0, 1, 2, 2, 1] = some [1, 1, 0, 0, 0, 1, 1] :=
  specInv_white_7 [0, 0, 0, 1, 2, 2, 1] [0, 2, 2, 0, 1, 0, 1] [1, 2, 0, 0, 1, 0, 0] [1, 1, 0, 0, 0, 1, 1] demoR1_0001221 demoR2_0001221 demoC_0001221 demoM_0001221

theorem demoR1_1001221 : invRung 7 5 20 [1, 0, 0, 1, 2, 2, 1] [1, 0, 0, 1, 2, 2, 1] 1 2 false = ([1, 0, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_1001221 : invRung 7 5 20 [1, 0, 0, 1, 2, 2, 1] [1, 0, 2, 2, 0, 1, 1] 3 1 true = ([1, 0, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_1001221 : fieldCube 7 5 20 [1, 0, 0, 2, 0, 0, 2] = [0, 2, 0, 2, 2, 1, 2] := by
  decide

theorem demoM_1001221 : fieldMul 7 5 20 [0, 2, 0, 2, 2, 1, 2] [1, 0, 0, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1001221 : mirrorTrits [0, 2, 0, 2, 2, 1, 2] = [0, 1, 0, 1, 1, 2, 1] := by
  decide

theorem demoInv_1001221 : specInv 7 5 20 [1, 0, 0, 1, 2, 2, 1] = some [0, 1, 0, 1, 1, 2, 1] :=
  specInv_mirror_7 [1, 0, 0, 1, 2, 2, 1] [1, 0, 2, 2, 0, 1, 1] [1, 0, 0, 2, 0, 0, 2] [0, 2, 0, 2, 2, 1, 2] [0, 1, 0, 1, 1, 2, 1] demoR1_1001221 demoR2_1001221 demoC_1001221 demoM_1001221 demoMir_1001221

theorem demoR1_2001221 : invRung 7 5 20 [2, 0, 0, 1, 2, 2, 1] [2, 0, 0, 1, 2, 2, 1] 1 2 false = ([2, 1, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_2001221 : invRung 7 5 20 [2, 0, 0, 1, 2, 2, 1] [2, 1, 1, 0, 2, 2, 2] 3 1 true = ([0, 0, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_2001221 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 0, 1] = [2, 2, 1, 2, 1, 1, 0] := by
  decide

theorem demoM_2001221 : fieldMul 7 5 20 [2, 2, 1, 2, 1, 1, 0] [2, 0, 0, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001221 : mirrorTrits [2, 2, 1, 2, 1, 1, 0] = [1, 1, 2, 1, 2, 2, 0] := by
  decide

theorem demoInv_2001221 : specInv 7 5 20 [2, 0, 0, 1, 2, 2, 1] = some [1, 1, 2, 1, 2, 2, 0] :=
  specInv_mirror_7 [2, 0, 0, 1, 2, 2, 1] [2, 1, 1, 0, 2, 2, 2] [0, 0, 1, 2, 1, 0, 1] [2, 2, 1, 2, 1, 1, 0] [1, 1, 2, 1, 2, 2, 0] demoR1_2001221 demoR2_2001221 demoC_2001221 demoM_2001221 demoMir_2001221

theorem demoR1_0101221 : invRung 7 5 20 [0, 1, 0, 1, 2, 2, 1] [0, 1, 0, 1, 2, 2, 1] 1 2 false = ([0, 1, 0, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_0101221 : invRung 7 5 20 [0, 1, 0, 1, 2, 2, 1] [0, 1, 0, 1, 1, 0, 1] 3 1 true = ([2, 0, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0101221 : fieldCube 7 5 20 [2, 0, 0, 2, 2, 0, 2] = [1, 1, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_0101221 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 0, 1] [0, 1, 0, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101221 : mirrorTrits [1, 1, 0, 1, 2, 0, 1] = [2, 2, 0, 2, 1, 0, 2] := by
  decide

theorem demoInv_0101221 : specInv 7 5 20 [0, 1, 0, 1, 2, 2, 1] = some [2, 2, 0, 2, 1, 0, 2] :=
  specInv_mirror_7 [0, 1, 0, 1, 2, 2, 1] [0, 1, 0, 1, 1, 0, 1] [2, 0, 0, 2, 2, 0, 2] [1, 1, 0, 1, 2, 0, 1] [2, 2, 0, 2, 1, 0, 2] demoR1_0101221 demoR2_0101221 demoC_0101221 demoM_0101221 demoMir_0101221

theorem demoR1_1101221 : invRung 7 5 20 [1, 1, 0, 1, 2, 2, 1] [1, 1, 0, 1, 2, 2, 1] 1 2 false = ([0, 0, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_1101221 : invRung 7 5 20 [1, 1, 0, 1, 2, 2, 1] [0, 0, 2, 0, 2, 1, 1] 3 1 true = ([2, 2, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_1101221 : fieldCube 7 5 20 [2, 2, 1, 1, 2, 2, 2] = [2, 0, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_1101221 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 1, 0] [1, 1, 0, 1, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1101221 : specInv 7 5 20 [1, 1, 0, 1, 2, 2, 1] = some [2, 0, 1, 0, 1, 1, 0] :=
  specInv_white_7 [1, 1, 0, 1, 2, 2, 1] [0, 0, 2, 0, 2, 1, 1] [2, 2, 1, 1, 2, 2, 2] [2, 0, 1, 0, 1, 1, 0] demoR1_1101221 demoR2_1101221 demoC_1101221 demoM_1101221

theorem demoR1_2101221 : invRung 7 5 20 [2, 1, 0, 1, 2, 2, 1] [2, 1, 0, 1, 2, 2, 1] 1 2 false = ([2, 1, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_2101221 : invRung 7 5 20 [2, 1, 0, 1, 2, 2, 1] [2, 1, 2, 0, 0, 1, 2] 3 1 true = ([2, 1, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2101221 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 1, 0] = [1, 0, 2, 0, 1, 1, 2] := by
  decide

theorem demoM_2101221 : fieldMul 7 5 20 [1, 0, 2, 0, 1, 1, 2] [2, 1, 0, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101221 : mirrorTrits [1, 0, 2, 0, 1, 1, 2] = [2, 0, 1, 0, 2, 2, 1] := by
  decide

theorem demoInv_2101221 : specInv 7 5 20 [2, 1, 0, 1, 2, 2, 1] = some [2, 0, 1, 0, 2, 2, 1] :=
  specInv_mirror_7 [2, 1, 0, 1, 2, 2, 1] [2, 1, 2, 0, 0, 1, 2] [2, 1, 1, 1, 2, 1, 0] [1, 0, 2, 0, 1, 1, 2] [2, 0, 1, 0, 2, 2, 1] demoR1_2101221 demoR2_2101221 demoC_2101221 demoM_2101221 demoMir_2101221

theorem demoR1_0201221 : invRung 7 5 20 [0, 2, 0, 1, 2, 2, 1] [0, 2, 0, 1, 2, 2, 1] 1 2 false = ([0, 0, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_0201221 : invRung 7 5 20 [0, 2, 0, 1, 2, 2, 1] [0, 0, 2, 0, 1, 2, 2] 3 1 true = ([1, 0, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_0201221 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 0, 0] = [0, 2, 2, 2, 0, 1, 1] := by
  decide

theorem demoM_0201221 : fieldMul 7 5 20 [0, 2, 2, 2, 0, 1, 1] [0, 2, 0, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201221 : mirrorTrits [0, 2, 2, 2, 0, 1, 1] = [0, 1, 1, 1, 0, 2, 2] := by
  decide

theorem demoInv_0201221 : specInv 7 5 20 [0, 2, 0, 1, 2, 2, 1] = some [0, 1, 1, 1, 0, 2, 2] :=
  specInv_mirror_7 [0, 2, 0, 1, 2, 2, 1] [0, 0, 2, 0, 1, 2, 2] [1, 0, 2, 2, 2, 0, 0] [0, 2, 2, 2, 0, 1, 1] [0, 1, 1, 1, 0, 2, 2] demoR1_0201221 demoR2_0201221 demoC_0201221 demoM_0201221 demoMir_0201221

theorem demoR1_1201221 : invRung 7 5 20 [1, 2, 0, 1, 2, 2, 1] [1, 2, 0, 1, 2, 2, 1] 1 2 false = ([2, 1, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1201221 : invRung 7 5 20 [1, 2, 0, 1, 2, 2, 1] [2, 1, 0, 0, 0, 2, 0] 3 1 true = ([1, 2, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_1201221 : fieldCube 7 5 20 [1, 2, 2, 1, 0, 2, 2] = [1, 1, 1, 1, 1, 2, 2] := by
  decide

theorem demoM_1201221 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 2, 2] [1, 2, 0, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201221 : mirrorTrits [1, 1, 1, 1, 1, 2, 2] = [2, 2, 2, 2, 2, 1, 1] := by
  decide

theorem demoInv_1201221 : specInv 7 5 20 [1, 2, 0, 1, 2, 2, 1] = some [2, 2, 2, 2, 2, 1, 1] :=
  specInv_mirror_7 [1, 2, 0, 1, 2, 2, 1] [2, 1, 0, 0, 0, 2, 0] [1, 2, 2, 1, 0, 2, 2] [1, 1, 1, 1, 1, 2, 2] [2, 2, 2, 2, 2, 1, 1] demoR1_1201221 demoR2_1201221 demoC_1201221 demoM_1201221 demoMir_1201221

theorem demoR1_2201221 : invRung 7 5 20 [2, 2, 0, 1, 2, 2, 1] [2, 2, 0, 1, 2, 2, 1] 1 2 false = ([2, 0, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2201221 : invRung 7 5 20 [2, 2, 0, 1, 2, 2, 1] [2, 0, 1, 0, 2, 0, 2] 3 1 true = ([2, 1, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_2201221 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 0, 1] = [0, 1, 0, 2, 1, 2, 0] := by
  decide

theorem demoM_2201221 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 2, 0] [2, 2, 0, 1, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2201221 : specInv 7 5 20 [2, 2, 0, 1, 2, 2, 1] = some [0, 1, 0, 2, 1, 2, 0] :=
  specInv_white_7 [2, 2, 0, 1, 2, 2, 1] [2, 0, 1, 0, 2, 0, 2] [2, 1, 2, 1, 0, 0, 1] [0, 1, 0, 2, 1, 2, 0] demoR1_2201221 demoR2_2201221 demoC_2201221 demoM_2201221

theorem demoR1_0011221 : invRung 7 5 20 [0, 0, 1, 1, 2, 2, 1] [0, 0, 1, 1, 2, 2, 1] 1 2 false = ([0, 1, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_0011221 : invRung 7 5 20 [0, 0, 1, 1, 2, 2, 1] [0, 1, 2, 1, 1, 2, 2] 3 1 true = ([2, 2, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0011221 : fieldCube 7 5 20 [2, 2, 0, 0, 2, 0, 1] = [2, 0, 2, 2, 1, 0, 0] := by
  decide

theorem demoM_0011221 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 0, 0] [0, 0, 1, 1, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0011221 : specInv 7 5 20 [0, 0, 1, 1, 2, 2, 1] = some [2, 0, 2, 2, 1, 0, 0] :=
  specInv_white_7 [0, 0, 1, 1, 2, 2, 1] [0, 1, 2, 1, 1, 2, 2] [2, 2, 0, 0, 2, 0, 1] [2, 0, 2, 2, 1, 0, 0] demoR1_0011221 demoR2_0011221 demoC_0011221 demoM_0011221

theorem demoR1_1011221 : invRung 7 5 20 [1, 0, 1, 1, 2, 2, 1] [1, 0, 1, 1, 2, 2, 1] 1 2 false = ([2, 2, 0, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_1011221 : invRung 7 5 20 [1, 0, 1, 1, 2, 2, 1] [2, 2, 0, 1, 1, 0, 1] 3 1 true = ([2, 0, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_1011221 : fieldCube 7 5 20 [2, 0, 0, 0, 0, 0, 2] = [2, 2, 1, 2, 2, 2, 2] := by
  decide

theorem demoM_1011221 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 2, 2] [1, 0, 1, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011221 : mirrorTrits [2, 2, 1, 2, 2, 2, 2] = [1, 1, 2, 1, 1, 1, 1] := by
  decide

theorem demoInv_1011221 : specInv 7 5 20 [1, 0, 1, 1, 2, 2, 1] = some [1, 1, 2, 1, 1, 1, 1] :=
  specInv_mirror_7 [1, 0, 1, 1, 2, 2, 1] [2, 2, 0, 1, 1, 0, 1] [2, 0, 0, 0, 0, 0, 2] [2, 2, 1, 2, 2, 2, 2] [1, 1, 2, 1, 1, 1, 1] demoR1_1011221 demoR2_1011221 demoC_1011221 demoM_1011221 demoMir_1011221

theorem demoR1_2011221 : invRung 7 5 20 [2, 0, 1, 1, 2, 2, 1] [2, 0, 1, 1, 2, 2, 1] 1 2 false = ([1, 2, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2011221 : invRung 7 5 20 [2, 0, 1, 1, 2, 2, 1] [1, 2, 0, 2, 0, 0, 2] 3 1 true = ([0, 1, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_2011221 : fieldCube 7 5 20 [0, 1, 1, 0, 1, 1, 2] = [1, 1, 2, 1, 0, 1, 0] := by
  decide

theorem demoM_2011221 : fieldMul 7 5 20 [1, 1, 2, 1, 0, 1, 0] [2, 0, 1, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011221 : mirrorTrits [1, 1, 2, 1, 0, 1, 0] = [2, 2, 1, 2, 0, 2, 0] := by
  decide

theorem demoInv_2011221 : specInv 7 5 20 [2, 0, 1, 1, 2, 2, 1] = some [2, 2, 1, 2, 0, 2, 0] :=
  specInv_mirror_7 [2, 0, 1, 1, 2, 2, 1] [1, 2, 0, 2, 0, 0, 2] [0, 1, 1, 0, 1, 1, 2] [1, 1, 2, 1, 0, 1, 0] [2, 2, 1, 2, 0, 2, 0] demoR1_2011221 demoR2_2011221 demoC_2011221 demoM_2011221 demoMir_2011221

theorem demoR1_0111221 : invRung 7 5 20 [0, 1, 1, 1, 2, 2, 1] [0, 1, 1, 1, 2, 2, 1] 1 2 false = ([0, 0, 2, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_0111221 : invRung 7 5 20 [0, 1, 1, 1, 2, 2, 1] [0, 0, 2, 0, 2, 2, 0] 3 1 true = ([1, 2, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_0111221 : fieldCube 7 5 20 [1, 2, 0, 2, 1, 1, 1] = [1, 0, 2, 1, 2, 2, 1] := by
  decide

theorem demoM_0111221 : fieldMul 7 5 20 [1, 0, 2, 1, 2, 2, 1] [0, 1, 1, 1, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0111221 : specInv 7 5 20 [0, 1, 1, 1, 2, 2, 1] = some [1, 0, 2, 1, 2, 2, 1] :=
  specInv_white_7 [0, 1, 1, 1, 2, 2, 1] [0, 0, 2, 0, 2, 2, 0] [1, 2, 0, 2, 1, 1, 1] [1, 0, 2, 1, 2, 2, 1] demoR1_0111221 demoR2_0111221 demoC_0111221 demoM_0111221

theorem demoR1_1111221 : invRung 7 5 20 [1, 1, 1, 1, 2, 2, 1] [1, 1, 1, 1, 2, 2, 1] 1 2 false = ([1, 1, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1111221 : invRung 7 5 20 [1, 1, 1, 1, 2, 2, 1] [1, 1, 0, 2, 2, 1, 1] 3 1 true = ([1, 2, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_1111221 : fieldCube 7 5 20 [1, 2, 1, 0, 0, 0, 0] = [1, 0, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_1111221 : fieldMul 7 5 20 [1, 0, 0, 2, 0, 0, 1] [1, 1, 1, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111221 : mirrorTrits [1, 0, 0, 2, 0, 0, 1] = [2, 0, 0, 1, 0, 0, 2] := by
  decide

theorem demoInv_1111221 : specInv 7 5 20 [1, 1, 1, 1, 2, 2, 1] = some [2, 0, 0, 1, 0, 0, 2] :=
  specInv_mirror_7 [1, 1, 1, 1, 2, 2, 1] [1, 1, 0, 2, 2, 1, 1] [1, 2, 1, 0, 0, 0, 0] [1, 0, 0, 2, 0, 0, 1] [2, 0, 0, 1, 0, 0, 2] demoR1_1111221 demoR2_1111221 demoC_1111221 demoM_1111221 demoMir_1111221

theorem demoR1_2111221 : invRung 7 5 20 [2, 1, 1, 1, 2, 2, 1] [2, 1, 1, 1, 2, 2, 1] 1 2 false = ([1, 0, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_2111221 : invRung 7 5 20 [2, 1, 1, 1, 2, 2, 1] [1, 0, 2, 1, 1, 1, 1] 3 1 true = ([1, 0, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2111221 : fieldCube 7 5 20 [1, 0, 0, 0, 1, 1, 0] = [2, 2, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_2111221 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 2, 0] [2, 1, 1, 1, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2111221 : specInv 7 5 20 [2, 1, 1, 1, 2, 2, 1] = some [2, 2, 1, 1, 1, 2, 0] :=
  specInv_white_7 [2, 1, 1, 1, 2, 2, 1] [1, 0, 2, 1, 1, 1, 1] [1, 0, 0, 0, 1, 1, 0] [2, 2, 1, 1, 1, 2, 0] demoR1_2111221 demoR2_2111221 demoC_2111221 demoM_2111221

theorem demoR1_0211221 : invRung 7 5 20 [0, 2, 1, 1, 2, 2, 1] [0, 2, 1, 1, 2, 2, 1] 1 2 false = ([1, 1, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_0211221 : invRung 7 5 20 [0, 2, 1, 1, 2, 2, 1] [1, 1, 1, 0, 0, 2, 2] 3 1 true = ([1, 1, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0211221 : fieldCube 7 5 20 [1, 1, 2, 1, 0, 0, 0] = [2, 0, 1, 1, 0, 1, 2] := by
  decide

theorem demoM_0211221 : fieldMul 7 5 20 [2, 0, 1, 1, 0, 1, 2] [0, 2, 1, 1, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0211221 : specInv 7 5 20 [0, 2, 1, 1, 2, 2, 1] = some [2, 0, 1, 1, 0, 1, 2] :=
  specInv_white_7 [0, 2, 1, 1, 2, 2, 1] [1, 1, 1, 0, 0, 2, 2] [1, 1, 2, 1, 0, 0, 0] [2, 0, 1, 1, 0, 1, 2] demoR1_0211221 demoR2_0211221 demoC_0211221 demoM_0211221

theorem demoR1_1211221 : invRung 7 5 20 [1, 2, 1, 1, 2, 2, 1] [1, 2, 1, 1, 2, 2, 1] 1 2 false = ([1, 0, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1211221 : invRung 7 5 20 [1, 2, 1, 1, 2, 2, 1] [1, 0, 2, 2, 2, 1, 0] 3 1 true = ([0, 0, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_1211221 : fieldCube 7 5 20 [0, 0, 2, 0, 1, 2, 0] = [2, 0, 2, 1, 2, 0, 1] := by
  decide

theorem demoM_1211221 : fieldMul 7 5 20 [2, 0, 2, 1, 2, 0, 1] [1, 2, 1, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1211221 : mirrorTrits [2, 0, 2, 1, 2, 0, 1] = [1, 0, 1, 2, 1, 0, 2] := by
  decide

theorem demoInv_1211221 : specInv 7 5 20 [1, 2, 1, 1, 2, 2, 1] = some [1, 0, 1, 2, 1, 0, 2] :=
  specInv_mirror_7 [1, 2, 1, 1, 2, 2, 1] [1, 0, 2, 2, 2, 1, 0] [0, 0, 2, 0, 1, 2, 0] [2, 0, 2, 1, 2, 0, 1] [1, 0, 1, 2, 1, 0, 2] demoR1_1211221 demoR2_1211221 demoC_1211221 demoM_1211221 demoMir_1211221

theorem demoR1_2211221 : invRung 7 5 20 [2, 2, 1, 1, 2, 2, 1] [2, 2, 1, 1, 2, 2, 1] 1 2 false = ([2, 2, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_2211221 : invRung 7 5 20 [2, 2, 1, 1, 2, 2, 1] [2, 2, 0, 0, 0, 0, 0] 3 1 true = ([0, 1, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2211221 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 2, 1] = [0, 1, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_2211221 : fieldMul 7 5 20 [0, 1, 2, 0, 0, 2, 2] [2, 2, 1, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211221 : mirrorTrits [0, 1, 2, 0, 0, 2, 2] = [0, 2, 1, 0, 0, 1, 1] := by
  decide

theorem demoInv_2211221 : specInv 7 5 20 [2, 2, 1, 1, 2, 2, 1] = some [0, 2, 1, 0, 0, 1, 1] :=
  specInv_mirror_7 [2, 2, 1, 1, 2, 2, 1] [2, 2, 0, 0, 0, 0, 0] [0, 1, 2, 1, 1, 2, 1] [0, 1, 2, 0, 0, 2, 2] [0, 2, 1, 0, 0, 1, 1] demoR1_2211221 demoR2_2211221 demoC_2211221 demoM_2211221 demoMir_2211221

theorem demoR1_0021221 : invRung 7 5 20 [0, 0, 2, 1, 2, 2, 1] [0, 0, 2, 1, 2, 2, 1] 1 2 false = ([2, 2, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_0021221 : invRung 7 5 20 [0, 0, 2, 1, 2, 2, 1] [2, 2, 1, 2, 1, 1, 1] 3 1 true = ([2, 0, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_0021221 : fieldCube 7 5 20 [2, 0, 0, 0, 1, 1, 0] = [0, 2, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_0021221 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 2, 0] [0, 0, 2, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021221 : mirrorTrits [0, 2, 1, 1, 1, 2, 0] = [0, 1, 2, 2, 2, 1, 0] := by
  decide

theorem demoInv_0021221 : specInv 7 5 20 [0, 0, 2, 1, 2, 2, 1] = some [0, 1, 2, 2, 2, 1, 0] :=
  specInv_mirror_7 [0, 0, 2, 1, 2, 2, 1] [2, 2, 1, 2, 1, 1, 1] [2, 0, 0, 0, 1, 1, 0] [0, 2, 1, 1, 1, 2, 0] [0, 1, 2, 2, 2, 1, 0] demoR1_0021221 demoR2_0021221 demoC_0021221 demoM_0021221 demoMir_0021221

theorem demoR1_1021221 : invRung 7 5 20 [1, 0, 2, 1, 2, 2, 1] [1, 0, 2, 1, 2, 2, 1] 1 2 false = ([1, 0, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1021221 : invRung 7 5 20 [1, 0, 2, 1, 2, 2, 1] [1, 0, 1, 0, 2, 2, 1] 3 1 true = ([1, 1, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_1021221 : fieldCube 7 5 20 [1, 1, 2, 1, 2, 1, 1] = [0, 1, 1, 1, 2, 2, 1] := by
  decide

theorem demoM_1021221 : fieldMul 7 5 20 [0, 1, 1, 1, 2, 2, 1] [1, 0, 2, 1, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1021221 : specInv 7 5 20 [1, 0, 2, 1, 2, 2, 1] = some [0, 1, 1, 1, 2, 2, 1] :=
  specInv_white_7 [1, 0, 2, 1, 2, 2, 1] [1, 0, 1, 0, 2, 2, 1] [1, 1, 2, 1, 2, 1, 1] [0, 1, 1, 1, 2, 2, 1] demoR1_1021221 demoR2_1021221 demoC_1021221 demoM_1021221

theorem demoR1_2021221 : invRung 7 5 20 [2, 0, 2, 1, 2, 2, 1] [2, 0, 2, 1, 2, 2, 1] 1 2 false = ([0, 2, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_2021221 : invRung 7 5 20 [2, 0, 2, 1, 2, 2, 1] [0, 2, 0, 1, 1, 1, 1] 3 1 true = ([1, 1, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_2021221 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 0, 0] = [1, 0, 0, 1, 0, 0, 2] := by
  decide

theorem demoM_2021221 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 0, 2] [2, 0, 2, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021221 : mirrorTrits [1, 0, 0, 1, 0, 0, 2] = [2, 0, 0, 2, 0, 0, 1] := by
  decide

theorem demoInv_2021221 : specInv 7 5 20 [2, 0, 2, 1, 2, 2, 1] = some [2, 0, 0, 2, 0, 0, 1] :=
  specInv_mirror_7 [2, 0, 2, 1, 2, 2, 1] [0, 2, 0, 1, 1, 1, 1] [1, 1, 2, 0, 0, 0, 0] [1, 0, 0, 1, 0, 0, 2] [2, 0, 0, 2, 0, 0, 1] demoR1_2021221 demoR2_2021221 demoC_2021221 demoM_2021221 demoMir_2021221

theorem demoR1_0121221 : invRung 7 5 20 [0, 1, 2, 1, 2, 2, 1] [0, 1, 2, 1, 2, 2, 1] 1 2 false = ([2, 0, 2, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_0121221 : invRung 7 5 20 [0, 1, 2, 1, 2, 2, 1] [2, 0, 2, 1, 2, 0, 2] 3 1 true = ([0, 1, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0121221 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 1, 1] = [2, 2, 1, 2, 2, 0, 1] := by
  decide

theorem demoM_0121221 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 0, 1] [0, 1, 2, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0121221 : mirrorTrits [2, 2, 1, 2, 2, 0, 1] = [1, 1, 2, 1, 1, 0, 2] := by
  decide

theorem demoInv_0121221 : specInv 7 5 20 [0, 1, 2, 1, 2, 2, 1] = some [1, 1, 2, 1, 1, 0, 2] :=
  specInv_mirror_7 [0, 1, 2, 1, 2, 2, 1] [2, 0, 2, 1, 2, 0, 2] [0, 1, 1, 1, 0, 1, 1] [2, 2, 1, 2, 2, 0, 1] [1, 1, 2, 1, 1, 0, 2] demoR1_0121221 demoR2_0121221 demoC_0121221 demoM_0121221 demoMir_0121221

theorem demoR1_1121221 : invRung 7 5 20 [1, 1, 2, 1, 2, 2, 1] [1, 1, 2, 1, 2, 2, 1] 1 2 false = ([0, 0, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1121221 : invRung 7 5 20 [1, 1, 2, 1, 2, 2, 1] [0, 0, 0, 0, 1, 0, 0] 3 1 true = ([2, 0, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_1121221 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 1, 2] = [0, 1, 2, 0, 0, 1, 0] := by
  decide

theorem demoM_1121221 : fieldMul 7 5 20 [0, 1, 2, 0, 0, 1, 0] [1, 1, 2, 1, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1121221 : specInv 7 5 20 [1, 1, 2, 1, 2, 2, 1] = some [0, 1, 2, 0, 0, 1, 0] :=
  specInv_white_7 [1, 1, 2, 1, 2, 2, 1] [0, 0, 0, 0, 1, 0, 0] [2, 0, 1, 0, 1, 1, 2] [0, 1, 2, 0, 0, 1, 0] demoR1_1121221 demoR2_1121221 demoC_1121221 demoM_1121221

theorem demoR1_2121221 : invRung 7 5 20 [2, 1, 2, 1, 2, 2, 1] [2, 1, 2, 1, 2, 2, 1] 1 2 false = ([0, 0, 2, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_2121221 : invRung 7 5 20 [2, 1, 2, 1, 2, 2, 1] [0, 0, 2, 1, 1, 0, 1] 3 1 true = ([1, 2, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_2121221 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 0, 0] = [2, 2, 1, 1, 0, 0, 0] := by
  decide

theorem demoM_2121221 : fieldMul 7 5 20 [2, 2, 1, 1, 0, 0, 0] [2, 1, 2, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2121221 : mirrorTrits [2, 2, 1, 1, 0, 0, 0] = [1, 1, 2, 2, 0, 0, 0] := by
  decide

theorem demoInv_2121221 : specInv 7 5 20 [2, 1, 2, 1, 2, 2, 1] = some [1, 1, 2, 2, 0, 0, 0] :=
  specInv_mirror_7 [2, 1, 2, 1, 2, 2, 1] [0, 0, 2, 1, 1, 0, 1] [1, 2, 1, 1, 2, 0, 0] [2, 2, 1, 1, 0, 0, 0] [1, 1, 2, 2, 0, 0, 0] demoR1_2121221 demoR2_2121221 demoC_2121221 demoM_2121221 demoMir_2121221

theorem demoR1_0221221 : invRung 7 5 20 [0, 2, 2, 1, 2, 2, 1] [0, 2, 2, 1, 2, 2, 1] 1 2 false = ([1, 2, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_0221221 : invRung 7 5 20 [0, 2, 2, 1, 2, 2, 1] [1, 2, 0, 1, 0, 0, 1] 3 1 true = ([0, 2, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0221221 : fieldCube 7 5 20 [0, 2, 2, 0, 2, 2, 2] = [2, 0, 0, 0, 1, 0, 1] := by
  decide

theorem demoM_0221221 : fieldMul 7 5 20 [2, 0, 0, 0, 1, 0, 1] [0, 2, 2, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0221221 : mirrorTrits [2, 0, 0, 0, 1, 0, 1] = [1, 0, 0, 0, 2, 0, 2] := by
  decide

theorem demoInv_0221221 : specInv 7 5 20 [0, 2, 2, 1, 2, 2, 1] = some [1, 0, 0, 0, 2, 0, 2] :=
  specInv_mirror_7 [0, 2, 2, 1, 2, 2, 1] [1, 2, 0, 1, 0, 0, 1] [0, 2, 2, 0, 2, 2, 2] [2, 0, 0, 0, 1, 0, 1] [1, 0, 0, 0, 2, 0, 2] demoR1_0221221 demoR2_0221221 demoC_0221221 demoM_0221221 demoMir_0221221

theorem demoR1_1221221 : invRung 7 5 20 [1, 2, 2, 1, 2, 2, 1] [1, 2, 2, 1, 2, 2, 1] 1 2 false = ([1, 2, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1221221 : invRung 7 5 20 [1, 2, 2, 1, 2, 2, 1] [1, 2, 2, 2, 2, 1, 1] 3 1 true = ([1, 1, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1221221 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 2, 1] = [1, 0, 2, 2, 0, 1, 2] := by
  decide

theorem demoM_1221221 : fieldMul 7 5 20 [1, 0, 2, 2, 0, 1, 2] [1, 2, 2, 1, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221221 : mirrorTrits [1, 0, 2, 2, 0, 1, 2] = [2, 0, 1, 1, 0, 2, 1] := by
  decide

theorem demoInv_1221221 : specInv 7 5 20 [1, 2, 2, 1, 2, 2, 1] = some [2, 0, 1, 1, 0, 2, 1] :=
  specInv_mirror_7 [1, 2, 2, 1, 2, 2, 1] [1, 2, 2, 2, 2, 1, 1] [1, 1, 0, 1, 0, 2, 1] [1, 0, 2, 2, 0, 1, 2] [2, 0, 1, 1, 0, 2, 1] demoR1_1221221 demoR2_1221221 demoC_1221221 demoM_1221221 demoMir_1221221

theorem demoR1_2221221 : invRung 7 5 20 [2, 2, 2, 1, 2, 2, 1] [2, 2, 2, 1, 2, 2, 1] 1 2 false = ([2, 1, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_2221221 : invRung 7 5 20 [2, 2, 2, 1, 2, 2, 1] [2, 1, 1, 1, 2, 1, 1] 3 1 true = ([2, 2, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_2221221 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 1, 1] = [1, 0, 1, 1, 2, 1, 2] := by
  decide

theorem demoM_2221221 : fieldMul 7 5 20 [1, 0, 1, 1, 2, 1, 2] [2, 2, 2, 1, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2221221 : specInv 7 5 20 [2, 2, 2, 1, 2, 2, 1] = some [1, 0, 1, 1, 2, 1, 2] :=
  specInv_white_7 [2, 2, 2, 1, 2, 2, 1] [2, 1, 1, 1, 2, 1, 1] [2, 2, 1, 1, 1, 1, 1] [1, 0, 1, 1, 2, 1, 2] demoR1_2221221 demoR2_2221221 demoC_2221221 demoM_2221221

theorem demoR1_0002221 : invRung 7 5 20 [0, 0, 0, 2, 2, 2, 1] [0, 0, 0, 2, 2, 2, 1] 1 2 false = ([0, 0, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_0002221 : invRung 7 5 20 [0, 0, 0, 2, 2, 2, 1] [0, 0, 0, 0, 2, 1, 1] 3 1 true = ([2, 1, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_0002221 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 0, 2] = [2, 0, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_0002221 : fieldMul 7 5 20 [2, 0, 1, 1, 2, 0, 1] [0, 0, 0, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002221 : mirrorTrits [2, 0, 1, 1, 2, 0, 1] = [1, 0, 2, 2, 1, 0, 2] := by
  decide

theorem demoInv_0002221 : specInv 7 5 20 [0, 0, 0, 2, 2, 2, 1] = some [1, 0, 2, 2, 1, 0, 2] :=
  specInv_mirror_7 [0, 0, 0, 2, 2, 2, 1] [0, 0, 0, 0, 2, 1, 1] [2, 1, 1, 0, 1, 0, 2] [2, 0, 1, 1, 2, 0, 1] [1, 0, 2, 2, 1, 0, 2] demoR1_0002221 demoR2_0002221 demoC_0002221 demoM_0002221 demoMir_0002221

theorem demoR1_1002221 : invRung 7 5 20 [1, 0, 0, 2, 2, 2, 1] [1, 0, 0, 2, 2, 2, 1] 1 2 false = ([1, 2, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_1002221 : invRung 7 5 20 [1, 0, 0, 2, 2, 2, 1] [1, 2, 1, 2, 2, 0, 2] 3 1 true = ([1, 1, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_1002221 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 0, 2] = [2, 1, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_1002221 : fieldMul 7 5 20 [2, 1, 2, 2, 2, 2, 1] [1, 0, 0, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1002221 : specInv 7 5 20 [1, 0, 0, 2, 2, 2, 1] = some [2, 1, 2, 2, 2, 2, 1] :=
  specInv_white_7 [1, 0, 0, 2, 2, 2, 1] [1, 2, 1, 2, 2, 0, 2] [1, 1, 0, 1, 2, 0, 2] [2, 1, 2, 2, 2, 2, 1] demoR1_1002221 demoR2_1002221 demoC_1002221 demoM_1002221

theorem demoR1_2002221 : invRung 7 5 20 [2, 0, 0, 2, 2, 2, 1] [2, 0, 0, 2, 2, 2, 1] 1 2 false = ([2, 0, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_2002221 : invRung 7 5 20 [2, 0, 0, 2, 2, 2, 1] [2, 0, 2, 2, 1, 0, 1] 3 1 true = ([0, 0, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_2002221 : fieldCube 7 5 20 [0, 0, 0, 1, 0, 2, 2] = [0, 1, 1, 2, 1, 2, 0] := by
  decide

theorem demoM_2002221 : fieldMul 7 5 20 [0, 1, 1, 2, 1, 2, 0] [2, 0, 0, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2002221 : specInv 7 5 20 [2, 0, 0, 2, 2, 2, 1] = some [0, 1, 1, 2, 1, 2, 0] :=
  specInv_white_7 [2, 0, 0, 2, 2, 2, 1] [2, 0, 2, 2, 1, 0, 1] [0, 0, 0, 1, 0, 2, 2] [0, 1, 1, 2, 1, 2, 0] demoR1_2002221 demoR2_2002221 demoC_2002221 demoM_2002221

theorem demoR1_0102221 : invRung 7 5 20 [0, 1, 0, 2, 2, 2, 1] [0, 1, 0, 2, 2, 2, 1] 1 2 false = ([0, 1, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_0102221 : invRung 7 5 20 [0, 1, 0, 2, 2, 2, 1] [0, 1, 1, 1, 2, 2, 0] 3 1 true = ([1, 2, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_0102221 : fieldCube 7 5 20 [1, 2, 1, 0, 0, 1, 2] = [2, 0, 2, 1, 0, 0, 2] := by
  decide

theorem demoM_0102221 : fieldMul 7 5 20 [2, 0, 2, 1, 0, 0, 2] [0, 1, 0, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102221 : mirrorTrits [2, 0, 2, 1, 0, 0, 2] = [1, 0, 1, 2, 0, 0, 1] := by
  decide

theorem demoInv_0102221 : specInv 7 5 20 [0, 1, 0, 2, 2, 2, 1] = some [1, 0, 1, 2, 0, 0, 1] :=
  specInv_mirror_7 [0, 1, 0, 2, 2, 2, 1] [0, 1, 1, 1, 2, 2, 0] [1, 2, 1, 0, 0, 1, 2] [2, 0, 2, 1, 0, 0, 2] [1, 0, 1, 2, 0, 0, 1] demoR1_0102221 demoR2_0102221 demoC_0102221 demoM_0102221 demoMir_0102221

theorem demoR1_1102221 : invRung 7 5 20 [1, 1, 0, 2, 2, 2, 1] [1, 1, 0, 2, 2, 2, 1] 1 2 false = ([1, 1, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_1102221 : invRung 7 5 20 [1, 1, 0, 2, 2, 2, 1] [1, 1, 1, 0, 0, 0, 1] 3 1 true = ([2, 2, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_1102221 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 1, 0] = [0, 0, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_1102221 : fieldMul 7 5 20 [0, 0, 1, 1, 1, 0, 2] [1, 1, 0, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1102221 : specInv 7 5 20 [1, 1, 0, 2, 2, 2, 1] = some [0, 0, 1, 1, 1, 0, 2] :=
  specInv_white_7 [1, 1, 0, 2, 2, 2, 1] [1, 1, 1, 0, 0, 0, 1] [2, 2, 1, 0, 2, 1, 0] [0, 0, 1, 1, 1, 0, 2] demoR1_1102221 demoR2_1102221 demoC_1102221 demoM_1102221

theorem demoR1_2102221 : invRung 7 5 20 [2, 1, 0, 2, 2, 2, 1] [2, 1, 0, 2, 2, 2, 1] 1 2 false = ([1, 2, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_2102221 : invRung 7 5 20 [2, 1, 0, 2, 2, 2, 1] [1, 2, 0, 2, 0, 1, 0] 3 1 true = ([0, 0, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_2102221 : fieldCube 7 5 20 [0, 0, 1, 1, 2, 0, 2] = [1, 1, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_2102221 : fieldMul 7 5 20 [1, 1, 2, 1, 2, 2, 2] [2, 1, 0, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2102221 : specInv 7 5 20 [2, 1, 0, 2, 2, 2, 1] = some [1, 1, 2, 1, 2, 2, 2] :=
  specInv_white_7 [2, 1, 0, 2, 2, 2, 1] [1, 2, 0, 2, 0, 1, 0] [0, 0, 1, 1, 2, 0, 2] [1, 1, 2, 1, 2, 2, 2] demoR1_2102221 demoR2_2102221 demoC_2102221 demoM_2102221

theorem demoR1_0202221 : invRung 7 5 20 [0, 2, 0, 2, 2, 2, 1] [0, 2, 0, 2, 2, 2, 1] 1 2 false = ([0, 0, 0, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_0202221 : invRung 7 5 20 [0, 2, 0, 2, 2, 2, 1] [0, 0, 0, 1, 1, 0, 1] 3 1 true = ([1, 2, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_0202221 : fieldCube 7 5 20 [1, 2, 2, 0, 2, 0, 0] = [1, 2, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_0202221 : fieldMul 7 5 20 [1, 2, 0, 1, 0, 2, 1] [0, 2, 0, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202221 : mirrorTrits [1, 2, 0, 1, 0, 2, 1] = [2, 1, 0, 2, 0, 1, 2] := by
  decide

theorem demoInv_0202221 : specInv 7 5 20 [0, 2, 0, 2, 2, 2, 1] = some [2, 1, 0, 2, 0, 1, 2] :=
  specInv_mirror_7 [0, 2, 0, 2, 2, 2, 1] [0, 0, 0, 1, 1, 0, 1] [1, 2, 2, 0, 2, 0, 0] [1, 2, 0, 1, 0, 2, 1] [2, 1, 0, 2, 0, 1, 2] demoR1_0202221 demoR2_0202221 demoC_0202221 demoM_0202221 demoMir_0202221

theorem demoR1_1202221 : invRung 7 5 20 [1, 2, 0, 2, 2, 2, 1] [1, 2, 0, 2, 2, 2, 1] 1 2 false = ([1, 2, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_1202221 : invRung 7 5 20 [1, 2, 0, 2, 2, 2, 1] [1, 2, 2, 1, 2, 2, 0] 3 1 true = ([0, 0, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_1202221 : fieldCube 7 5 20 [0, 0, 2, 2, 2, 1, 1] = [0, 1, 2, 0, 2, 0, 1] := by
  decide

theorem demoM_1202221 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 0, 1] [1, 2, 0, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1202221 : specInv 7 5 20 [1, 2, 0, 2, 2, 2, 1] = some [0, 1, 2, 0, 2, 0, 1] :=
  specInv_white_7 [1, 2, 0, 2, 2, 2, 1] [1, 2, 2, 1, 2, 2, 0] [0, 0, 2, 2, 2, 1, 1] [0, 1, 2, 0, 2, 0, 1] demoR1_1202221 demoR2_1202221 demoC_1202221 demoM_1202221

theorem demoR1_2202221 : invRung 7 5 20 [2, 2, 0, 2, 2, 2, 1] [2, 2, 0, 2, 2, 2, 1] 1 2 false = ([0, 1, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2202221 : invRung 7 5 20 [2, 2, 0, 2, 2, 2, 1] [0, 1, 2, 0, 2, 0, 0] 3 1 true = ([0, 0, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_2202221 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 1, 0] = [0, 0, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_2202221 : fieldMul 7 5 20 [0, 0, 0, 2, 1, 2, 2] [2, 2, 0, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2202221 : specInv 7 5 20 [2, 2, 0, 2, 2, 2, 1] = some [0, 0, 0, 2, 1, 2, 2] :=
  specInv_white_7 [2, 2, 0, 2, 2, 2, 1] [0, 1, 2, 0, 2, 0, 0] [0, 0, 1, 2, 2, 1, 0] [0, 0, 0, 2, 1, 2, 2] demoR1_2202221 demoR2_2202221 demoC_2202221 demoM_2202221

theorem demoR1_0012221 : invRung 7 5 20 [0, 0, 1, 2, 2, 2, 1] [0, 0, 1, 2, 2, 2, 1] 1 2 false = ([2, 0, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_0012221 : invRung 7 5 20 [0, 0, 1, 2, 2, 2, 1] [2, 0, 1, 0, 2, 2, 1] 3 1 true = ([1, 1, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0012221 : fieldCube 7 5 20 [1, 1, 1, 1, 0, 1, 0] = [0, 1, 2, 1, 1, 2, 0] := by
  decide

theorem demoM_0012221 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 2, 0] [0, 0, 1, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0012221 : mirrorTrits [0, 1, 2, 1, 1, 2, 0] = [0, 2, 1, 2, 2, 1, 0] := by
  decide

theorem demoInv_0012221 : specInv 7 5 20 [0, 0, 1, 2, 2, 2, 1] = some [0, 2, 1, 2, 2, 1, 0] :=
  specInv_mirror_7 [0, 0, 1, 2, 2, 2, 1] [2, 0, 1, 0, 2, 2, 1] [1, 1, 1, 1, 0, 1, 0] [0, 1, 2, 1, 1, 2, 0] [0, 2, 1, 2, 2, 1, 0] demoR1_0012221 demoR2_0012221 demoC_0012221 demoM_0012221 demoMir_0012221

theorem demoR1_1012221 : invRung 7 5 20 [1, 0, 1, 2, 2, 2, 1] [1, 0, 1, 2, 2, 2, 1] 1 2 false = ([1, 0, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_1012221 : invRung 7 5 20 [1, 0, 1, 2, 2, 2, 1] [1, 0, 1, 2, 2, 2, 2] 3 1 true = ([1, 2, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_1012221 : fieldCube 7 5 20 [1, 2, 1, 1, 0, 0, 2] = [2, 2, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_1012221 : fieldMul 7 5 20 [2, 2, 2, 1, 2, 0, 0] [1, 0, 1, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1012221 : specInv 7 5 20 [1, 0, 1, 2, 2, 2, 1] = some [2, 2, 2, 1, 2, 0, 0] :=
  specInv_white_7 [1, 0, 1, 2, 2, 2, 1] [1, 0, 1, 2, 2, 2, 2] [1, 2, 1, 1, 0, 0, 2] [2, 2, 2, 1, 2, 0, 0] demoR1_1012221 demoR2_1012221 demoC_1012221 demoM_1012221

theorem demoR1_2012221 : invRung 7 5 20 [2, 0, 1, 2, 2, 2, 1] [2, 0, 1, 2, 2, 2, 1] 1 2 false = ([0, 1, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_2012221 : invRung 7 5 20 [2, 0, 1, 2, 2, 2, 1] [0, 1, 1, 1, 0, 2, 2] 3 1 true = ([0, 2, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2012221 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 0, 0] = [0, 1, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_2012221 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 1, 0] [2, 0, 1, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012221 : mirrorTrits [0, 1, 0, 0, 0, 1, 0] = [0, 2, 0, 0, 0, 2, 0] := by
  decide

theorem demoInv_2012221 : specInv 7 5 20 [2, 0, 1, 2, 2, 2, 1] = some [0, 2, 0, 0, 0, 2, 0] :=
  specInv_mirror_7 [2, 0, 1, 2, 2, 2, 1] [0, 1, 1, 1, 0, 2, 2] [0, 2, 2, 0, 1, 0, 0] [0, 1, 0, 0, 0, 1, 0] [0, 2, 0, 0, 0, 2, 0] demoR1_2012221 demoR2_2012221 demoC_2012221 demoM_2012221 demoMir_2012221

theorem demoR1_0112221 : invRung 7 5 20 [0, 1, 1, 2, 2, 2, 1] [0, 1, 1, 2, 2, 2, 1] 1 2 false = ([0, 0, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_0112221 : invRung 7 5 20 [0, 1, 1, 2, 2, 2, 1] [0, 0, 0, 0, 2, 2, 1] 3 1 true = ([2, 0, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0112221 : fieldCube 7 5 20 [2, 0, 2, 0, 1, 2, 1] = [1, 1, 1, 2, 0, 1, 2] := by
  decide

theorem demoM_0112221 : fieldMul 7 5 20 [1, 1, 1, 2, 0, 1, 2] [0, 1, 1, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112221 : mirrorTrits [1, 1, 1, 2, 0, 1, 2] = [2, 2, 2, 1, 0, 2, 1] := by
  decide

theorem demoInv_0112221 : specInv 7 5 20 [0, 1, 1, 2, 2, 2, 1] = some [2, 2, 2, 1, 0, 2, 1] :=
  specInv_mirror_7 [0, 1, 1, 2, 2, 2, 1] [0, 0, 0, 0, 2, 2, 1] [2, 0, 2, 0, 1, 2, 1] [1, 1, 1, 2, 0, 1, 2] [2, 2, 2, 1, 0, 2, 1] demoR1_0112221 demoR2_0112221 demoC_0112221 demoM_0112221 demoMir_0112221

theorem demoR1_1112221 : invRung 7 5 20 [1, 1, 1, 2, 2, 2, 1] [1, 1, 1, 2, 2, 2, 1] 1 2 false = ([2, 0, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1112221 : invRung 7 5 20 [1, 1, 1, 2, 2, 2, 1] [2, 0, 0, 1, 1, 2, 1] 3 1 true = ([0, 1, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_1112221 : fieldCube 7 5 20 [0, 1, 0, 2, 0, 0, 1] = [2, 1, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_1112221 : fieldMul 7 5 20 [2, 1, 1, 2, 1, 0, 1] [1, 1, 1, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112221 : mirrorTrits [2, 1, 1, 2, 1, 0, 1] = [1, 2, 2, 1, 2, 0, 2] := by
  decide

theorem demoInv_1112221 : specInv 7 5 20 [1, 1, 1, 2, 2, 2, 1] = some [1, 2, 2, 1, 2, 0, 2] :=
  specInv_mirror_7 [1, 1, 1, 2, 2, 2, 1] [2, 0, 0, 1, 1, 2, 1] [0, 1, 0, 2, 0, 0, 1] [2, 1, 1, 2, 1, 0, 1] [1, 2, 2, 1, 2, 0, 2] demoR1_1112221 demoR2_1112221 demoC_1112221 demoM_1112221 demoMir_1112221

theorem demoR1_2112221 : invRung 7 5 20 [2, 1, 1, 2, 2, 2, 1] [2, 1, 1, 2, 2, 2, 1] 1 2 false = ([0, 0, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_2112221 : invRung 7 5 20 [2, 1, 1, 2, 2, 2, 1] [0, 0, 2, 1, 1, 1, 0] 3 1 true = ([0, 0, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2112221 : fieldCube 7 5 20 [0, 0, 2, 1, 0, 2, 1] = [0, 0, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_2112221 : fieldMul 7 5 20 [0, 0, 2, 1, 0, 1, 1] [2, 1, 1, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2112221 : specInv 7 5 20 [2, 1, 1, 2, 2, 2, 1] = some [0, 0, 2, 1, 0, 1, 1] :=
  specInv_white_7 [2, 1, 1, 2, 2, 2, 1] [0, 0, 2, 1, 1, 1, 0] [0, 0, 2, 1, 0, 2, 1] [0, 0, 2, 1, 0, 1, 1] demoR1_2112221 demoR2_2112221 demoC_2112221 demoM_2112221

theorem demoR1_0212221 : invRung 7 5 20 [0, 2, 1, 2, 2, 2, 1] [0, 2, 1, 2, 2, 2, 1] 1 2 false = ([2, 0, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_0212221 : invRung 7 5 20 [0, 2, 1, 2, 2, 2, 1] [2, 0, 1, 2, 1, 0, 0] 3 1 true = ([0, 2, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_0212221 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 2, 1] = [0, 0, 2, 0, 0, 1, 0] := by
  decide

theorem demoM_0212221 : fieldMul 7 5 20 [0, 0, 2, 0, 0, 1, 0] [0, 2, 1, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212221 : mirrorTrits [0, 0, 2, 0, 0, 1, 0] = [0, 0, 1, 0, 0, 2, 0] := by
  decide

theorem demoInv_0212221 : specInv 7 5 20 [0, 2, 1, 2, 2, 2, 1] = some [0, 0, 1, 0, 0, 2, 0] :=
  specInv_mirror_7 [0, 2, 1, 2, 2, 2, 1] [2, 0, 1, 2, 1, 0, 0] [0, 2, 1, 1, 0, 2, 1] [0, 0, 2, 0, 0, 1, 0] [0, 0, 1, 0, 0, 2, 0] demoR1_0212221 demoR2_0212221 demoC_0212221 demoM_0212221 demoMir_0212221

theorem demoR1_1212221 : invRung 7 5 20 [1, 2, 1, 2, 2, 2, 1] [1, 2, 1, 2, 2, 2, 1] 1 2 false = ([1, 1, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_1212221 : invRung 7 5 20 [1, 2, 1, 2, 2, 2, 1] [1, 1, 1, 0, 1, 2, 0] 3 1 true = ([0, 0, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_1212221 : fieldCube 7 5 20 [0, 0, 0, 2, 1, 1, 1] = [0, 0, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_1212221 : fieldMul 7 5 20 [0, 0, 2, 2, 2, 2, 1] [1, 2, 1, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212221 : mirrorTrits [0, 0, 2, 2, 2, 2, 1] = [0, 0, 1, 1, 1, 1, 2] := by
  decide

theorem demoInv_1212221 : specInv 7 5 20 [1, 2, 1, 2, 2, 2, 1] = some [0, 0, 1, 1, 1, 1, 2] :=
  specInv_mirror_7 [1, 2, 1, 2, 2, 2, 1] [1, 1, 1, 0, 1, 2, 0] [0, 0, 0, 2, 1, 1, 1] [0, 0, 2, 2, 2, 2, 1] [0, 0, 1, 1, 1, 1, 2] demoR1_1212221 demoR2_1212221 demoC_1212221 demoM_1212221 demoMir_1212221

theorem demoR1_2212221 : invRung 7 5 20 [2, 2, 1, 2, 2, 2, 1] [2, 2, 1, 2, 2, 2, 1] 1 2 false = ([1, 1, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_2212221 : invRung 7 5 20 [2, 2, 1, 2, 2, 2, 1] [1, 1, 2, 2, 2, 2, 2] 3 1 true = ([0, 1, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_2212221 : fieldCube 7 5 20 [0, 1, 1, 1, 1, 1, 0] = [2, 2, 2, 2, 1, 0, 1] := by
  decide

theorem demoM_2212221 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 0, 1] [2, 2, 1, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212221 : mirrorTrits [2, 2, 2, 2, 1, 0, 1] = [1, 1, 1, 1, 2, 0, 2] := by
  decide

theorem demoInv_2212221 : specInv 7 5 20 [2, 2, 1, 2, 2, 2, 1] = some [1, 1, 1, 1, 2, 0, 2] :=
  specInv_mirror_7 [2, 2, 1, 2, 2, 2, 1] [1, 1, 2, 2, 2, 2, 2] [0, 1, 1, 1, 1, 1, 0] [2, 2, 2, 2, 1, 0, 1] [1, 1, 1, 1, 2, 0, 2] demoR1_2212221 demoR2_2212221 demoC_2212221 demoM_2212221 demoMir_2212221

theorem demoR1_0022221 : invRung 7 5 20 [0, 0, 2, 2, 2, 2, 1] [0, 0, 2, 2, 2, 2, 1] 1 2 false = ([1, 0, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0022221 : invRung 7 5 20 [0, 0, 2, 2, 2, 2, 1] [1, 0, 2, 0, 2, 1, 2] 3 1 true = ([2, 0, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0022221 : fieldCube 7 5 20 [2, 0, 1, 0, 0, 0, 1] = [2, 1, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_0022221 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 1, 2] [0, 0, 2, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0022221 : specInv 7 5 20 [0, 0, 2, 2, 2, 2, 1] = some [2, 1, 2, 1, 1, 1, 2] :=
  specInv_white_7 [0, 0, 2, 2, 2, 2, 1] [1, 0, 2, 0, 2, 1, 2] [2, 0, 1, 0, 0, 0, 1] [2, 1, 2, 1, 1, 1, 2] demoR1_0022221 demoR2_0022221 demoC_0022221 demoM_0022221

theorem demoR1_1022221 : invRung 7 5 20 [1, 0, 2, 2, 2, 2, 1] [1, 0, 2, 2, 2, 2, 1] 1 2 false = ([0, 1, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_1022221 : invRung 7 5 20 [1, 0, 2, 2, 2, 2, 1] [0, 1, 2, 2, 2, 2, 2] 3 1 true = ([1, 1, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_1022221 : fieldCube 7 5 20 [1, 1, 2, 2, 0, 1, 2] = [1, 0, 1, 0, 0, 2, 0] := by
  decide

theorem demoM_1022221 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 2, 0] [1, 0, 2, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1022221 : specInv 7 5 20 [1, 0, 2, 2, 2, 2, 1] = some [1, 0, 1, 0, 0, 2, 0] :=
  specInv_white_7 [1, 0, 2, 2, 2, 2, 1] [0, 1, 2, 2, 2, 2, 2] [1, 1, 2, 2, 0, 1, 2] [1, 0, 1, 0, 0, 2, 0] demoR1_1022221 demoR2_1022221 demoC_1022221 demoM_1022221

theorem demoR1_2022221 : invRung 7 5 20 [2, 0, 2, 2, 2, 2, 1] [2, 0, 2, 2, 2, 2, 1] 1 2 false = ([2, 2, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_2022221 : invRung 7 5 20 [2, 0, 2, 2, 2, 2, 1] [2, 2, 2, 0, 2, 2, 2] 3 1 true = ([1, 1, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_2022221 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 1, 0] = [0, 2, 2, 2, 1, 0, 1] := by
  decide

theorem demoM_2022221 : fieldMul 7 5 20 [0, 2, 2, 2, 1, 0, 1] [2, 0, 2, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022221 : mirrorTrits [0, 2, 2, 2, 1, 0, 1] = [0, 1, 1, 1, 2, 0, 2] := by
  decide

theorem demoInv_2022221 : specInv 7 5 20 [2, 0, 2, 2, 2, 2, 1] = some [0, 1, 1, 1, 2, 0, 2] :=
  specInv_mirror_7 [2, 0, 2, 2, 2, 2, 1] [2, 2, 2, 0, 2, 2, 2] [1, 1, 1, 1, 1, 1, 0] [0, 2, 2, 2, 1, 0, 1] [0, 1, 1, 1, 2, 0, 2] demoR1_2022221 demoR2_2022221 demoC_2022221 demoM_2022221 demoMir_2022221

theorem demoR1_0122221 : invRung 7 5 20 [0, 1, 2, 2, 2, 2, 1] [0, 1, 2, 2, 2, 2, 1] 1 2 false = ([0, 1, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_0122221 : invRung 7 5 20 [0, 1, 2, 2, 2, 2, 1] [0, 1, 1, 1, 1, 2, 2] 3 1 true = ([1, 0, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0122221 : fieldCube 7 5 20 [1, 0, 0, 2, 0, 1, 1] = [1, 2, 2, 1, 2, 1, 0] := by
  decide

theorem demoM_0122221 : fieldMul 7 5 20 [1, 2, 2, 1, 2, 1, 0] [0, 1, 2, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0122221 : specInv 7 5 20 [0, 1, 2, 2, 2, 2, 1] = some [1, 2, 2, 1, 2, 1, 0] :=
  specInv_white_7 [0, 1, 2, 2, 2, 2, 1] [0, 1, 1, 1, 1, 2, 2] [1, 0, 0, 2, 0, 1, 1] [1, 2, 2, 1, 2, 1, 0] demoR1_0122221 demoR2_0122221 demoC_0122221 demoM_0122221

theorem demoR1_1122221 : invRung 7 5 20 [1, 1, 2, 2, 2, 2, 1] [1, 1, 2, 2, 2, 2, 1] 1 2 false = ([2, 1, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_1122221 : invRung 7 5 20 [1, 1, 2, 2, 2, 2, 1] [2, 1, 2, 1, 1, 1, 0] 3 1 true = ([1, 1, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_1122221 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 0, 2] = [1, 0, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_1122221 : fieldMul 7 5 20 [1, 0, 1, 1, 2, 0, 1] [1, 1, 2, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1122221 : specInv 7 5 20 [1, 1, 2, 2, 2, 2, 1] = some [1, 0, 1, 1, 2, 0, 1] :=
  specInv_white_7 [1, 1, 2, 2, 2, 2, 1] [2, 1, 2, 1, 1, 1, 0] [1, 1, 1, 0, 1, 0, 2] [1, 0, 1, 1, 2, 0, 1] demoR1_1122221 demoR2_1122221 demoC_1122221 demoM_1122221

theorem demoR1_2122221 : invRung 7 5 20 [2, 1, 2, 2, 2, 2, 1] [2, 1, 2, 2, 2, 2, 1] 1 2 false = ([0, 0, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_2122221 : invRung 7 5 20 [2, 1, 2, 2, 2, 2, 1] [0, 0, 2, 2, 1, 1, 1] 3 1 true = ([2, 2, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_2122221 : fieldCube 7 5 20 [2, 2, 1, 2, 1, 0, 2] = [1, 0, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_2122221 : fieldMul 7 5 20 [1, 0, 0, 2, 2, 2, 1] [2, 1, 2, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2122221 : specInv 7 5 20 [2, 1, 2, 2, 2, 2, 1] = some [1, 0, 0, 2, 2, 2, 1] :=
  specInv_white_7 [2, 1, 2, 2, 2, 2, 1] [0, 0, 2, 2, 1, 1, 1] [2, 2, 1, 2, 1, 0, 2] [1, 0, 0, 2, 2, 2, 1] demoR1_2122221 demoR2_2122221 demoC_2122221 demoM_2122221

theorem demoR1_0222221 : invRung 7 5 20 [0, 2, 2, 2, 2, 2, 1] [0, 2, 2, 2, 2, 2, 1] 1 2 false = ([1, 1, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_0222221 : invRung 7 5 20 [0, 2, 2, 2, 2, 2, 1] [1, 1, 0, 1, 2, 2, 1] 3 1 true = ([1, 1, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0222221 : fieldCube 7 5 20 [1, 1, 2, 1, 1, 2, 0] = [1, 0, 0, 2, 2, 1, 1] := by
  decide

theorem demoM_0222221 : fieldMul 7 5 20 [1, 0, 0, 2, 2, 1, 1] [0, 2, 2, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0222221 : specInv 7 5 20 [0, 2, 2, 2, 2, 2, 1] = some [1, 0, 0, 2, 2, 1, 1] :=
  specInv_white_7 [0, 2, 2, 2, 2, 2, 1] [1, 1, 0, 1, 2, 2, 1] [1, 1, 2, 1, 1, 2, 0] [1, 0, 0, 2, 2, 1, 1] demoR1_0222221 demoR2_0222221 demoC_0222221 demoM_0222221

theorem demoR1_1222221 : invRung 7 5 20 [1, 2, 2, 2, 2, 2, 1] [1, 2, 2, 2, 2, 2, 1] 1 2 false = ([0, 1, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_1222221 : invRung 7 5 20 [1, 2, 2, 2, 2, 2, 1] [0, 1, 2, 0, 1, 1, 1] 3 1 true = ([0, 1, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_1222221 : fieldCube 7 5 20 [0, 1, 1, 2, 1, 0, 0] = [2, 1, 2, 2, 0, 0, 2] := by
  decide

theorem demoM_1222221 : fieldMul 7 5 20 [2, 1, 2, 2, 0, 0, 2] [1, 2, 2, 2, 2, 2, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1222221 : specInv 7 5 20 [1, 2, 2, 2, 2, 2, 1] = some [2, 1, 2, 2, 0, 0, 2] :=
  specInv_white_7 [1, 2, 2, 2, 2, 2, 1] [0, 1, 2, 0, 1, 1, 1] [0, 1, 1, 2, 1, 0, 0] [2, 1, 2, 2, 0, 0, 2] demoR1_1222221 demoR2_1222221 demoC_1222221 demoM_1222221

theorem demoR1_2222221 : invRung 7 5 20 [2, 2, 2, 2, 2, 2, 1] [2, 2, 2, 2, 2, 2, 1] 1 2 false = ([0, 2, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_2222221 : invRung 7 5 20 [2, 2, 2, 2, 2, 2, 1] [0, 2, 2, 2, 0, 0, 1] 3 1 true = ([1, 0, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_2222221 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 1, 2] = [0, 1, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_2222221 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 2, 1] [2, 2, 2, 2, 2, 2, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222221 : mirrorTrits [0, 1, 0, 0, 0, 2, 1] = [0, 2, 0, 0, 0, 1, 2] := by
  decide

theorem demoInv_2222221 : specInv 7 5 20 [2, 2, 2, 2, 2, 2, 1] = some [0, 2, 0, 0, 0, 1, 2] :=
  specInv_mirror_7 [2, 2, 2, 2, 2, 2, 1] [0, 2, 2, 2, 0, 0, 1] [1, 0, 2, 1, 1, 1, 2] [0, 1, 0, 0, 0, 2, 1] [0, 2, 0, 0, 0, 1, 2] demoR1_2222221 demoR2_2222221 demoC_2222221 demoM_2222221 demoMir_2222221

theorem demoR1_0000002 : invRung 7 5 20 [0, 0, 0, 0, 0, 0, 2] [0, 0, 0, 0, 0, 0, 2] 1 2 false = ([1, 2, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0000002 : invRung 7 5 20 [0, 0, 0, 0, 0, 0, 2] [1, 2, 1, 1, 1, 1, 2] 3 1 true = ([0, 0, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_0000002 : fieldCube 7 5 20 [0, 0, 0, 2, 0, 1, 0] = [0, 1, 0, 0, 1, 0, 2] := by
  decide

theorem demoM_0000002 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 0, 2] [0, 0, 0, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000002 : mirrorTrits [0, 1, 0, 0, 1, 0, 2] = [0, 2, 0, 0, 2, 0, 1] := by
  decide

theorem demoInv_0000002 : specInv 7 5 20 [0, 0, 0, 0, 0, 0, 2] = some [0, 2, 0, 0, 2, 0, 1] :=
  specInv_mirror_7 [0, 0, 0, 0, 0, 0, 2] [1, 2, 1, 1, 1, 1, 2] [0, 0, 0, 2, 0, 1, 0] [0, 1, 0, 0, 1, 0, 2] [0, 2, 0, 0, 2, 0, 1] demoR1_0000002 demoR2_0000002 demoC_0000002 demoM_0000002 demoMir_0000002

theorem demoR1_1000002 : invRung 7 5 20 [1, 0, 0, 0, 0, 0, 2] [1, 0, 0, 0, 0, 0, 2] 1 2 false = ([1, 2, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_1000002 : invRung 7 5 20 [1, 0, 0, 0, 0, 0, 2] [1, 2, 0, 1, 2, 0, 0] 3 1 true = ([0, 0, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1000002 : fieldCube 7 5 20 [0, 0, 0, 0, 0, 1, 0] = [1, 1, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_1000002 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 1, 2] [1, 0, 0, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000002 : mirrorTrits [1, 1, 1, 0, 1, 1, 2] = [2, 2, 2, 0, 2, 2, 1] := by
  decide

theorem demoInv_1000002 : specInv 7 5 20 [1, 0, 0, 0, 0, 0, 2] = some [2, 2, 2, 0, 2, 2, 1] :=
  specInv_mirror_7 [1, 0, 0, 0, 0, 0, 2] [1, 2, 0, 1, 2, 0, 0] [0, 0, 0, 0, 0, 1, 0] [1, 1, 1, 0, 1, 1, 2] [2, 2, 2, 0, 2, 2, 1] demoR1_1000002 demoR2_1000002 demoC_1000002 demoM_1000002 demoMir_1000002

theorem demoR1_2000002 : invRung 7 5 20 [2, 0, 0, 0, 0, 0, 2] [2, 0, 0, 0, 0, 0, 2] 1 2 false = ([0, 0, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_2000002 : invRung 7 5 20 [2, 0, 0, 0, 0, 0, 2] [0, 0, 2, 2, 0, 1, 0] 3 1 true = ([1, 2, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_2000002 : fieldCube 7 5 20 [1, 2, 2, 1, 1, 1, 1] = [0, 0, 1, 1, 2, 1, 0] := by
  decide

theorem demoM_2000002 : fieldMul 7 5 20 [0, 0, 1, 1, 2, 1, 0] [2, 0, 0, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2000002 : specInv 7 5 20 [2, 0, 0, 0, 0, 0, 2] = some [0, 0, 1, 1, 2, 1, 0] :=
  specInv_white_7 [2, 0, 0, 0, 0, 0, 2] [0, 0, 2, 2, 0, 1, 0] [1, 2, 2, 1, 1, 1, 1] [0, 0, 1, 1, 2, 1, 0] demoR1_2000002 demoR2_2000002 demoC_2000002 demoM_2000002

theorem demoR1_0100002 : invRung 7 5 20 [0, 1, 0, 0, 0, 0, 2] [0, 1, 0, 0, 0, 0, 2] 1 2 false = ([0, 0, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_0100002 : invRung 7 5 20 [0, 1, 0, 0, 0, 0, 2] [0, 0, 1, 0, 0, 1, 1] 3 1 true = ([0, 2, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0100002 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 0, 1] = [2, 2, 1, 1, 1, 1, 0] := by
  decide

theorem demoM_0100002 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 1, 0] [0, 1, 0, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100002 : mirrorTrits [2, 2, 1, 1, 1, 1, 0] = [1, 1, 2, 2, 2, 2, 0] := by
  decide

theorem demoInv_0100002 : specInv 7 5 20 [0, 1, 0, 0, 0, 0, 2] = some [1, 1, 2, 2, 2, 2, 0] :=
  specInv_mirror_7 [0, 1, 0, 0, 0, 0, 2] [0, 0, 1, 0, 0, 1, 1] [0, 2, 1, 2, 1, 0, 1] [2, 2, 1, 1, 1, 1, 0] [1, 1, 2, 2, 2, 2, 0] demoR1_0100002 demoR2_0100002 demoC_0100002 demoM_0100002 demoMir_0100002

theorem demoR1_1100002 : invRung 7 5 20 [1, 1, 0, 0, 0, 0, 2] [1, 1, 0, 0, 0, 0, 2] 1 2 false = ([0, 1, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_1100002 : invRung 7 5 20 [1, 1, 0, 0, 0, 0, 2] [0, 1, 0, 1, 2, 1, 2] 3 1 true = ([1, 2, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_1100002 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 1, 0] = [1, 0, 0, 1, 1, 2, 0] := by
  decide

theorem demoM_1100002 : fieldMul 7 5 20 [1, 0, 0, 1, 1, 2, 0] [1, 1, 0, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1100002 : specInv 7 5 20 [1, 1, 0, 0, 0, 0, 2] = some [1, 0, 0, 1, 1, 2, 0] :=
  specInv_white_7 [1, 1, 0, 0, 0, 0, 2] [0, 1, 0, 1, 2, 1, 2] [1, 2, 2, 2, 2, 1, 0] [1, 0, 0, 1, 1, 2, 0] demoR1_1100002 demoR2_1100002 demoC_1100002 demoM_1100002

theorem demoR1_2100002 : invRung 7 5 20 [2, 1, 0, 0, 0, 0, 2] [2, 1, 0, 0, 0, 0, 2] 1 2 false = ([1, 2, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_2100002 : invRung 7 5 20 [2, 1, 0, 0, 0, 0, 2] [1, 2, 1, 2, 1, 2, 2] 3 1 true = ([0, 2, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_2100002 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 0, 2] = [0, 0, 1, 2, 2, 0, 0] := by
  decide

theorem demoM_2100002 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 0, 0] [2, 1, 0, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2100002 : specInv 7 5 20 [2, 1, 0, 0, 0, 0, 2] = some [0, 0, 1, 2, 2, 0, 0] :=
  specInv_white_7 [2, 1, 0, 0, 0, 0, 2] [1, 2, 1, 2, 1, 2, 2] [0, 2, 0, 0, 1, 0, 2] [0, 0, 1, 2, 2, 0, 0] demoR1_2100002 demoR2_2100002 demoC_2100002 demoM_2100002

theorem demoR1_0200002 : invRung 7 5 20 [0, 2, 0, 0, 0, 0, 2] [0, 2, 0, 0, 0, 0, 2] 1 2 false = ([0, 0, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0200002 : invRung 7 5 20 [0, 2, 0, 0, 0, 0, 2] [0, 0, 2, 1, 2, 1, 2] 3 1 true = ([2, 1, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0200002 : fieldCube 7 5 20 [2, 1, 0, 0, 2, 1, 0] = [0, 0, 1, 0, 1, 0, 1] := by
  decide

theorem demoM_0200002 : fieldMul 7 5 20 [0, 0, 1, 0, 1, 0, 1] [0, 2, 0, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200002 : mirrorTrits [0, 0, 1, 0, 1, 0, 1] = [0, 0, 2, 0, 2, 0, 2] := by
  decide

theorem demoInv_0200002 : specInv 7 5 20 [0, 2, 0, 0, 0, 0, 2] = some [0, 0, 2, 0, 2, 0, 2] :=
  specInv_mirror_7 [0, 2, 0, 0, 0, 0, 2] [0, 0, 2, 1, 2, 1, 2] [2, 1, 0, 0, 2, 1, 0] [0, 0, 1, 0, 1, 0, 1] [0, 0, 2, 0, 2, 0, 2] demoR1_0200002 demoR2_0200002 demoC_0200002 demoM_0200002 demoMir_0200002

theorem demoR1_1200002 : invRung 7 5 20 [1, 2, 0, 0, 0, 0, 2] [1, 2, 0, 0, 0, 0, 2] 1 2 false = ([0, 0, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_1200002 : invRung 7 5 20 [1, 2, 0, 0, 0, 0, 2] [0, 0, 1, 1, 1, 1, 1] 3 1 true = ([0, 2, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_1200002 : fieldCube 7 5 20 [0, 2, 2, 1, 2, 2, 2] = [0, 0, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_1200002 : fieldMul 7 5 20 [0, 0, 1, 0, 1, 1, 1] [1, 2, 0, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1200002 : specInv 7 5 20 [1, 2, 0, 0, 0, 0, 2] = some [0, 0, 1, 0, 1, 1, 1] :=
  specInv_white_7 [1, 2, 0, 0, 0, 0, 2] [0, 0, 1, 1, 1, 1, 1] [0, 2, 2, 1, 2, 2, 2] [0, 0, 1, 0, 1, 1, 1] demoR1_1200002 demoR2_1200002 demoC_1200002 demoM_1200002

theorem demoR1_2200002 : invRung 7 5 20 [2, 2, 0, 0, 0, 0, 2] [2, 2, 0, 0, 0, 0, 2] 1 2 false = ([0, 2, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_2200002 : invRung 7 5 20 [2, 2, 0, 0, 0, 0, 2] [0, 2, 1, 0, 0, 1, 2] 3 1 true = ([0, 1, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_2200002 : fieldCube 7 5 20 [0, 1, 0, 1, 2, 0, 0] = [1, 2, 1, 0, 0, 0, 2] := by
  decide

theorem demoM_2200002 : fieldMul 7 5 20 [1, 2, 1, 0, 0, 0, 2] [2, 2, 0, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2200002 : specInv 7 5 20 [2, 2, 0, 0, 0, 0, 2] = some [1, 2, 1, 0, 0, 0, 2] :=
  specInv_white_7 [2, 2, 0, 0, 0, 0, 2] [0, 2, 1, 0, 0, 1, 2] [0, 1, 0, 1, 2, 0, 0] [1, 2, 1, 0, 0, 0, 2] demoR1_2200002 demoR2_2200002 demoC_2200002 demoM_2200002

theorem demoR1_0010002 : invRung 7 5 20 [0, 0, 1, 0, 0, 0, 2] [0, 0, 1, 0, 0, 0, 2] 1 2 false = ([0, 1, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_0010002 : invRung 7 5 20 [0, 0, 1, 0, 0, 0, 2] [0, 1, 0, 0, 0, 2, 1] 3 1 true = ([2, 0, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_0010002 : fieldCube 7 5 20 [2, 0, 1, 0, 2, 0, 2] = [2, 1, 1, 1, 2, 1, 2] := by
  decide

theorem demoM_0010002 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 1, 2] [0, 0, 1, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0010002 : specInv 7 5 20 [0, 0, 1, 0, 0, 0, 2] = some [2, 1, 1, 1, 2, 1, 2] :=
  specInv_white_7 [0, 0, 1, 0, 0, 0, 2] [0, 1, 0, 0, 0, 2, 1] [2, 0, 1, 0, 2, 0, 2] [2, 1, 1, 1, 2, 1, 2] demoR1_0010002 demoR2_0010002 demoC_0010002 demoM_0010002

theorem demoR1_1010002 : invRung 7 5 20 [1, 0, 1, 0, 0, 0, 2] [1, 0, 1, 0, 0, 0, 2] 1 2 false = ([2, 0, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_1010002 : invRung 7 5 20 [1, 0, 1, 0, 0, 0, 2] [2, 0, 1, 2, 1, 2, 0] 3 1 true = ([0, 0, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_1010002 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 2, 1] = [2, 1, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_1010002 : fieldMul 7 5 20 [2, 1, 1, 2, 0, 1, 0] [1, 0, 1, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1010002 : mirrorTrits [2, 1, 1, 2, 0, 1, 0] = [1, 2, 2, 1, 0, 2, 0] := by
  decide

theorem demoInv_1010002 : specInv 7 5 20 [1, 0, 1, 0, 0, 0, 2] = some [1, 2, 2, 1, 0, 2, 0] :=
  specInv_mirror_7 [1, 0, 1, 0, 0, 0, 2] [2, 0, 1, 2, 1, 2, 0] [0, 0, 0, 0, 1, 2, 1] [2, 1, 1, 2, 0, 1, 0] [1, 2, 2, 1, 0, 2, 0] demoR1_1010002 demoR2_1010002 demoC_1010002 demoM_1010002 demoMir_1010002

theorem demoR1_2010002 : invRung 7 5 20 [2, 0, 1, 0, 0, 0, 2] [2, 0, 1, 0, 0, 0, 2] 1 2 false = ([0, 2, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_2010002 : invRung 7 5 20 [2, 0, 1, 0, 0, 0, 2] [0, 2, 2, 1, 1, 0, 2] 3 1 true = ([2, 2, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_2010002 : fieldCube 7 5 20 [2, 2, 1, 0, 1, 2, 2] = [1, 2, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_2010002 : fieldMul 7 5 20 [1, 2, 0, 2, 1, 2, 2] [2, 0, 1, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2010002 : specInv 7 5 20 [2, 0, 1, 0, 0, 0, 2] = some [1, 2, 0, 2, 1, 2, 2] :=
  specInv_white_7 [2, 0, 1, 0, 0, 0, 2] [0, 2, 2, 1, 1, 0, 2] [2, 2, 1, 0, 1, 2, 2] [1, 2, 0, 2, 1, 2, 2] demoR1_2010002 demoR2_2010002 demoC_2010002 demoM_2010002

theorem demoR1_0110002 : invRung 7 5 20 [0, 1, 1, 0, 0, 0, 2] [0, 1, 1, 0, 0, 0, 2] 1 2 false = ([0, 1, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_0110002 : invRung 7 5 20 [0, 1, 1, 0, 0, 0, 2] [0, 1, 1, 2, 2, 1, 2] 3 1 true = ([1, 1, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0110002 : fieldCube 7 5 20 [1, 1, 0, 0, 0, 1, 1] = [2, 2, 0, 2, 2, 2, 0] := by
  decide

theorem demoM_0110002 : fieldMul 7 5 20 [2, 2, 0, 2, 2, 2, 0] [0, 1, 1, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110002 : mirrorTrits [2, 2, 0, 2, 2, 2, 0] = [1, 1, 0, 1, 1, 1, 0] := by
  decide

theorem demoInv_0110002 : specInv 7 5 20 [0, 1, 1, 0, 0, 0, 2] = some [1, 1, 0, 1, 1, 1, 0] :=
  specInv_mirror_7 [0, 1, 1, 0, 0, 0, 2] [0, 1, 1, 2, 2, 1, 2] [1, 1, 0, 0, 0, 1, 1] [2, 2, 0, 2, 2, 2, 0] [1, 1, 0, 1, 1, 1, 0] demoR1_0110002 demoR2_0110002 demoC_0110002 demoM_0110002 demoMir_0110002

theorem demoR1_1110002 : invRung 7 5 20 [1, 1, 1, 0, 0, 0, 2] [1, 1, 1, 0, 0, 0, 2] 1 2 false = ([2, 0, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_1110002 : invRung 7 5 20 [1, 1, 1, 0, 0, 0, 2] [2, 0, 0, 1, 2, 0, 0] 3 1 true = ([2, 2, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_1110002 : fieldCube 7 5 20 [2, 2, 1, 2, 1, 1, 0] = [2, 2, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_1110002 : fieldMul 7 5 20 [2, 2, 0, 0, 1, 1, 1] [1, 1, 1, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1110002 : specInv 7 5 20 [1, 1, 1, 0, 0, 0, 2] = some [2, 2, 0, 0, 1, 1, 1] :=
  specInv_white_7 [1, 1, 1, 0, 0, 0, 2] [2, 0, 0, 1, 2, 0, 0] [2, 2, 1, 2, 1, 1, 0] [2, 2, 0, 0, 1, 1, 1] demoR1_1110002 demoR2_1110002 demoC_1110002 demoM_1110002

theorem demoR1_2110002 : invRung 7 5 20 [2, 1, 1, 0, 0, 0, 2] [2, 1, 1, 0, 0, 0, 2] 1 2 false = ([2, 1, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_2110002 : invRung 7 5 20 [2, 1, 1, 0, 0, 0, 2] [2, 1, 1, 2, 1, 2, 1] 3 1 true = ([0, 2, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_2110002 : fieldCube 7 5 20 [0, 2, 0, 2, 2, 1, 2] = [0, 2, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_2110002 : fieldMul 7 5 20 [0, 2, 1, 0, 0, 1, 0] [2, 1, 1, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2110002 : specInv 7 5 20 [2, 1, 1, 0, 0, 0, 2] = some [0, 2, 1, 0, 0, 1, 0] :=
  specInv_white_7 [2, 1, 1, 0, 0, 0, 2] [2, 1, 1, 2, 1, 2, 1] [0, 2, 0, 2, 2, 1, 2] [0, 2, 1, 0, 0, 1, 0] demoR1_2110002 demoR2_2110002 demoC_2110002 demoM_2110002

theorem demoR1_0210002 : invRung 7 5 20 [0, 2, 1, 0, 0, 0, 2] [0, 2, 1, 0, 0, 0, 2] 1 2 false = ([2, 2, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_0210002 : invRung 7 5 20 [0, 2, 1, 0, 0, 0, 2] [2, 2, 1, 0, 1, 1, 2] 3 1 true = ([1, 2, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0210002 : fieldCube 7 5 20 [1, 2, 2, 1, 2, 2, 2] = [1, 0, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_0210002 : fieldMul 7 5 20 [1, 0, 1, 0, 1, 1, 1] [0, 2, 1, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210002 : mirrorTrits [1, 0, 1, 0, 1, 1, 1] = [2, 0, 2, 0, 2, 2, 2] := by
  decide

theorem demoInv_0210002 : specInv 7 5 20 [0, 2, 1, 0, 0, 0, 2] = some [2, 0, 2, 0, 2, 2, 2] :=
  specInv_mirror_7 [0, 2, 1, 0, 0, 0, 2] [2, 2, 1, 0, 1, 1, 2] [1, 2, 2, 1, 2, 2, 2] [1, 0, 1, 0, 1, 1, 1] [2, 0, 2, 0, 2, 2, 2] demoR1_0210002 demoR2_0210002 demoC_0210002 demoM_0210002 demoMir_0210002

theorem demoR1_1210002 : invRung 7 5 20 [1, 2, 1, 0, 0, 0, 2] [1, 2, 1, 0, 0, 0, 2] 1 2 false = ([1, 2, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_1210002 : invRung 7 5 20 [1, 2, 1, 0, 0, 0, 2] [1, 2, 1, 0, 2, 1, 0] 3 1 true = ([0, 2, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_1210002 : fieldCube 7 5 20 [0, 2, 2, 1, 2, 1, 2] = [2, 2, 0, 0, 0, 0, 2] := by
  decide

theorem demoM_1210002 : fieldMul 7 5 20 [2, 2, 0, 0, 0, 0, 2] [1, 2, 1, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1210002 : specInv 7 5 20 [1, 2, 1, 0, 0, 0, 2] = some [2, 2, 0, 0, 0, 0, 2] :=
  specInv_white_7 [1, 2, 1, 0, 0, 0, 2] [1, 2, 1, 0, 2, 1, 0] [0, 2, 2, 1, 2, 1, 2] [2, 2, 0, 0, 0, 0, 2] demoR1_1210002 demoR2_1210002 demoC_1210002 demoM_1210002

theorem demoR1_2210002 : invRung 7 5 20 [2, 2, 1, 0, 0, 0, 2] [2, 2, 1, 0, 0, 0, 2] 1 2 false = ([0, 0, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2210002 : invRung 7 5 20 [2, 2, 1, 0, 0, 0, 2] [0, 0, 2, 1, 2, 0, 1] 3 1 true = ([0, 2, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_2210002 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 2, 0] = [2, 0, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_2210002 : fieldMul 7 5 20 [2, 0, 2, 0, 2, 0, 2] [2, 2, 1, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210002 : mirrorTrits [2, 0, 2, 0, 2, 0, 2] = [1, 0, 1, 0, 1, 0, 1] := by
  decide

theorem demoInv_2210002 : specInv 7 5 20 [2, 2, 1, 0, 0, 0, 2] = some [1, 0, 1, 0, 1, 0, 1] :=
  specInv_mirror_7 [2, 2, 1, 0, 0, 0, 2] [0, 0, 2, 1, 2, 0, 1] [0, 2, 0, 0, 1, 2, 0] [2, 0, 2, 0, 2, 0, 2] [1, 0, 1, 0, 1, 0, 1] demoR1_2210002 demoR2_2210002 demoC_2210002 demoM_2210002 demoMir_2210002

theorem demoR1_0020002 : invRung 7 5 20 [0, 0, 2, 0, 0, 0, 2] [0, 0, 2, 0, 0, 0, 2] 1 2 false = ([1, 0, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_0020002 : invRung 7 5 20 [0, 0, 2, 0, 0, 0, 2] [1, 0, 2, 0, 2, 1, 0] 3 1 true = ([1, 1, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_0020002 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 2, 1] = [0, 2, 1, 1, 0, 2, 1] := by
  decide

theorem demoM_0020002 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 2, 1] [0, 0, 2, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020002 : mirrorTrits [0, 2, 1, 1, 0, 2, 1] = [0, 1, 2, 2, 0, 1, 2] := by
  decide

theorem demoInv_0020002 : specInv 7 5 20 [0, 0, 2, 0, 0, 0, 2] = some [0, 1, 2, 2, 0, 1, 2] :=
  specInv_mirror_7 [0, 0, 2, 0, 0, 0, 2] [1, 0, 2, 0, 2, 1, 0] [1, 1, 0, 0, 2, 2, 1] [0, 2, 1, 1, 0, 2, 1] [0, 1, 2, 2, 0, 1, 2] demoR1_0020002 demoR2_0020002 demoC_0020002 demoM_0020002 demoMir_0020002

theorem demoR1_1020002 : invRung 7 5 20 [1, 0, 2, 0, 0, 0, 2] [1, 0, 2, 0, 0, 0, 2] 1 2 false = ([1, 1, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_1020002 : invRung 7 5 20 [1, 0, 2, 0, 0, 0, 2] [1, 1, 0, 1, 0, 2, 2] 3 1 true = ([2, 2, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_1020002 : fieldCube 7 5 20 [2, 2, 1, 1, 2, 0, 1] = [0, 0, 0, 2, 1, 1, 1] := by
  decide

theorem demoM_1020002 : fieldMul 7 5 20 [0, 0, 0, 2, 1, 1, 1] [1, 0, 2, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020002 : mirrorTrits [0, 0, 0, 2, 1, 1, 1] = [0, 0, 0, 1, 2, 2, 2] := by
  decide

theorem demoInv_1020002 : specInv 7 5 20 [1, 0, 2, 0, 0, 0, 2] = some [0, 0, 0, 1, 2, 2, 2] :=
  specInv_mirror_7 [1, 0, 2, 0, 0, 0, 2] [1, 1, 0, 1, 0, 2, 2] [2, 2, 1, 1, 2, 0, 1] [0, 0, 0, 2, 1, 1, 1] [0, 0, 0, 1, 2, 2, 2] demoR1_1020002 demoR2_1020002 demoC_1020002 demoM_1020002 demoMir_1020002

theorem demoR1_2020002 : invRung 7 5 20 [2, 0, 2, 0, 0, 0, 2] [2, 0, 2, 0, 0, 0, 2] 1 2 false = ([0, 1, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_2020002 : invRung 7 5 20 [2, 0, 2, 0, 0, 0, 2] [0, 1, 1, 1, 2, 0, 2] 3 1 true = ([2, 1, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2020002 : fieldCube 7 5 20 [2, 1, 1, 0, 0, 1, 0] = [0, 1, 1, 1, 1, 1, 0] := by
  decide

theorem demoM_2020002 : fieldMul 7 5 20 [0, 1, 1, 1, 1, 1, 0] [2, 0, 2, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020002 : mirrorTrits [0, 1, 1, 1, 1, 1, 0] = [0, 2, 2, 2, 2, 2, 0] := by
  decide

theorem demoInv_2020002 : specInv 7 5 20 [2, 0, 2, 0, 0, 0, 2] = some [0, 2, 2, 2, 2, 2, 0] :=
  specInv_mirror_7 [2, 0, 2, 0, 0, 0, 2] [0, 1, 1, 1, 2, 0, 2] [2, 1, 1, 0, 0, 1, 0] [0, 1, 1, 1, 1, 1, 0] [0, 2, 2, 2, 2, 2, 0] demoR1_2020002 demoR2_2020002 demoC_2020002 demoM_2020002 demoMir_2020002

theorem demoR1_0120002 : invRung 7 5 20 [0, 1, 2, 0, 0, 0, 2] [0, 1, 2, 0, 0, 0, 2] 1 2 false = ([2, 1, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_0120002 : invRung 7 5 20 [0, 1, 2, 0, 0, 0, 2] [2, 1, 0, 1, 0, 1, 2] 3 1 true = ([1, 1, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0120002 : fieldCube 7 5 20 [1, 1, 0, 1, 1, 2, 2] = [1, 2, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_0120002 : fieldMul 7 5 20 [1, 2, 1, 1, 1, 0, 1] [0, 1, 2, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0120002 : specInv 7 5 20 [0, 1, 2, 0, 0, 0, 2] = some [1, 2, 1, 1, 1, 0, 1] :=
  specInv_white_7 [0, 1, 2, 0, 0, 0, 2] [2, 1, 0, 1, 0, 1, 2] [1, 1, 0, 1, 1, 2, 2] [1, 2, 1, 1, 1, 0, 1] demoR1_0120002 demoR2_0120002 demoC_0120002 demoM_0120002

theorem demoR1_1120002 : invRung 7 5 20 [1, 1, 2, 0, 0, 0, 2] [1, 1, 2, 0, 0, 0, 2] 1 2 false = ([2, 1, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_1120002 : invRung 7 5 20 [1, 1, 2, 0, 0, 0, 2] [2, 1, 0, 1, 1, 2, 2] 3 1 true = ([1, 2, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_1120002 : fieldCube 7 5 20 [1, 2, 0, 0, 2, 0, 2] = [1, 1, 1, 0, 2, 1, 1] := by
  decide

theorem demoM_1120002 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 1, 1] [1, 1, 2, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120002 : mirrorTrits [1, 1, 1, 0, 2, 1, 1] = [2, 2, 2, 0, 1, 2, 2] := by
  decide

theorem demoInv_1120002 : specInv 7 5 20 [1, 1, 2, 0, 0, 0, 2] = some [2, 2, 2, 0, 1, 2, 2] :=
  specInv_mirror_7 [1, 1, 2, 0, 0, 0, 2] [2, 1, 0, 1, 1, 2, 2] [1, 2, 0, 0, 2, 0, 2] [1, 1, 1, 0, 2, 1, 1] [2, 2, 2, 0, 1, 2, 2] demoR1_1120002 demoR2_1120002 demoC_1120002 demoM_1120002 demoMir_1120002

theorem demoR1_2120002 : invRung 7 5 20 [2, 1, 2, 0, 0, 0, 2] [2, 1, 2, 0, 0, 0, 2] 1 2 false = ([0, 2, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_2120002 : invRung 7 5 20 [2, 1, 2, 0, 0, 0, 2] [0, 2, 2, 2, 0, 2, 0] 3 1 true = ([0, 1, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_2120002 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 0, 2] = [2, 1, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_2120002 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 0, 1] [2, 1, 2, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120002 : mirrorTrits [2, 1, 0, 2, 2, 0, 1] = [1, 2, 0, 1, 1, 0, 2] := by
  decide

theorem demoInv_2120002 : specInv 7 5 20 [2, 1, 2, 0, 0, 0, 2] = some [1, 2, 0, 1, 1, 0, 2] :=
  specInv_mirror_7 [2, 1, 2, 0, 0, 0, 2] [0, 2, 2, 2, 0, 2, 0] [0, 1, 0, 2, 2, 0, 2] [2, 1, 0, 2, 2, 0, 1] [1, 2, 0, 1, 1, 0, 2] demoR1_2120002 demoR2_2120002 demoC_2120002 demoM_2120002 demoMir_2120002

theorem demoR1_0220002 : invRung 7 5 20 [0, 2, 2, 0, 0, 0, 2] [0, 2, 2, 0, 0, 0, 2] 1 2 false = ([0, 2, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_0220002 : invRung 7 5 20 [0, 2, 2, 0, 0, 0, 2] [0, 2, 1, 1, 1, 0, 0] 3 1 true = ([2, 0, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_0220002 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 0, 0] = [1, 1, 2, 1, 0, 0, 0] := by
  decide

theorem demoM_0220002 : fieldMul 7 5 20 [1, 1, 2, 1, 0, 0, 0] [0, 2, 2, 0, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0220002 : specInv 7 5 20 [0, 2, 2, 0, 0, 0, 2] = some [1, 1, 2, 1, 0, 0, 0] :=
  specInv_white_7 [0, 2, 2, 0, 0, 0, 2] [0, 2, 1, 1, 1, 0, 0] [2, 0, 2, 2, 1, 0, 0] [1, 1, 2, 1, 0, 0, 0] demoR1_0220002 demoR2_0220002 demoC_0220002 demoM_0220002

theorem demoR1_1220002 : invRung 7 5 20 [1, 2, 2, 0, 0, 0, 2] [1, 2, 2, 0, 0, 0, 2] 1 2 false = ([0, 2, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1220002 : invRung 7 5 20 [1, 2, 2, 0, 0, 0, 2] [0, 2, 0, 1, 1, 0, 2] 3 1 true = ([2, 2, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_1220002 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 2, 2] = [0, 0, 2, 0, 1, 2, 0] := by
  decide

theorem demoM_1220002 : fieldMul 7 5 20 [0, 0, 2, 0, 1, 2, 0] [1, 2, 2, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220002 : mirrorTrits [0, 0, 2, 0, 1, 2, 0] = [0, 0, 1, 0, 2, 1, 0] := by
  decide

theorem demoInv_1220002 : specInv 7 5 20 [1, 2, 2, 0, 0, 0, 2] = some [0, 0, 1, 0, 2, 1, 0] :=
  specInv_mirror_7 [1, 2, 2, 0, 0, 0, 2] [0, 2, 0, 1, 1, 0, 2] [2, 2, 1, 2, 2, 2, 2] [0, 0, 2, 0, 1, 2, 0] [0, 0, 1, 0, 2, 1, 0] demoR1_1220002 demoR2_1220002 demoC_1220002 demoM_1220002 demoMir_1220002

theorem demoR1_2220002 : invRung 7 5 20 [2, 2, 2, 0, 0, 0, 2] [2, 2, 2, 0, 0, 0, 2] 1 2 false = ([0, 2, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_2220002 : invRung 7 5 20 [2, 2, 2, 0, 0, 0, 2] [0, 2, 0, 1, 2, 1, 2] 3 1 true = ([1, 1, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_2220002 : fieldCube 7 5 20 [1, 1, 2, 1, 0, 1, 0] = [0, 1, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_2220002 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 2, 1] [2, 2, 2, 0, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220002 : mirrorTrits [0, 1, 2, 1, 1, 2, 1] = [0, 2, 1, 2, 2, 1, 2] := by
  decide

theorem demoInv_2220002 : specInv 7 5 20 [2, 2, 2, 0, 0, 0, 2] = some [0, 2, 1, 2, 2, 1, 2] :=
  specInv_mirror_7 [2, 2, 2, 0, 0, 0, 2] [0, 2, 0, 1, 2, 1, 2] [1, 1, 2, 1, 0, 1, 0] [0, 1, 2, 1, 1, 2, 1] [0, 2, 1, 2, 2, 1, 2] demoR1_2220002 demoR2_2220002 demoC_2220002 demoM_2220002 demoMir_2220002

theorem demoR1_0001002 : invRung 7 5 20 [0, 0, 0, 1, 0, 0, 2] [0, 0, 0, 1, 0, 0, 2] 1 2 false = ([1, 0, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0001002 : invRung 7 5 20 [0, 0, 0, 1, 0, 0, 2] [1, 0, 0, 2, 0, 0, 0] 3 1 true = ([0, 0, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_0001002 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 1, 0] = [1, 2, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_0001002 : fieldMul 7 5 20 [1, 2, 1, 1, 1, 2, 0] [0, 0, 0, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001002 : mirrorTrits [1, 2, 1, 1, 1, 2, 0] = [2, 1, 2, 2, 2, 1, 0] := by
  decide

theorem demoInv_0001002 : specInv 7 5 20 [0, 0, 0, 1, 0, 0, 2] = some [2, 1, 2, 2, 2, 1, 0] :=
  specInv_mirror_7 [0, 0, 0, 1, 0, 0, 2] [1, 0, 0, 2, 0, 0, 0] [0, 0, 0, 0, 1, 1, 0] [1, 2, 1, 1, 1, 2, 0] [2, 1, 2, 2, 2, 1, 0] demoR1_0001002 demoR2_0001002 demoC_0001002 demoM_0001002 demoMir_0001002

theorem demoR1_1001002 : invRung 7 5 20 [1, 0, 0, 1, 0, 0, 2] [1, 0, 0, 1, 0, 0, 2] 1 2 false = ([1, 1, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_1001002 : invRung 7 5 20 [1, 0, 0, 1, 0, 0, 2] [1, 1, 1, 0, 2, 1, 0] 3 1 true = ([1, 1, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_1001002 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 2, 2] = [1, 0, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_1001002 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 1, 2] [1, 0, 0, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1001002 : specInv 7 5 20 [1, 0, 0, 1, 0, 0, 2] = some [1, 0, 1, 2, 1, 1, 2] :=
  specInv_white_7 [1, 0, 0, 1, 0, 0, 2] [1, 1, 1, 0, 2, 1, 0] [1, 1, 0, 1, 2, 2, 2] [1, 0, 1, 2, 1, 1, 2] demoR1_1001002 demoR2_1001002 demoC_1001002 demoM_1001002

theorem demoR1_2001002 : invRung 7 5 20 [2, 0, 0, 1, 0, 0, 2] [2, 0, 0, 1, 0, 0, 2] 1 2 false = ([0, 2, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_2001002 : invRung 7 5 20 [2, 0, 0, 1, 0, 0, 2] [0, 2, 0, 1, 0, 2, 2] 3 1 true = ([1, 2, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2001002 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 2, 2] = [2, 2, 2, 2, 1, 1, 2] := by
  decide

theorem demoM_2001002 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 1, 2] [2, 0, 0, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001002 : mirrorTrits [2, 2, 2, 2, 1, 1, 2] = [1, 1, 1, 1, 2, 2, 1] := by
  decide

theorem demoInv_2001002 : specInv 7 5 20 [2, 0, 0, 1, 0, 0, 2] = some [1, 1, 1, 1, 2, 2, 1] :=
  specInv_mirror_7 [2, 0, 0, 1, 0, 0, 2] [0, 2, 0, 1, 0, 2, 2] [1, 2, 1, 2, 1, 2, 2] [2, 2, 2, 2, 1, 1, 2] [1, 1, 1, 1, 2, 2, 1] demoR1_2001002 demoR2_2001002 demoC_2001002 demoM_2001002 demoMir_2001002

theorem demoR1_0101002 : invRung 7 5 20 [0, 1, 0, 1, 0, 0, 2] [0, 1, 0, 1, 0, 0, 2] 1 2 false = ([0, 2, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_0101002 : invRung 7 5 20 [0, 1, 0, 1, 0, 0, 2] [0, 2, 1, 2, 0, 0, 1] 3 1 true = ([2, 2, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_0101002 : fieldCube 7 5 20 [2, 2, 0, 2, 1, 2, 2] = [0, 2, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_0101002 : fieldMul 7 5 20 [0, 2, 2, 2, 1, 1, 1] [0, 1, 0, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0101002 : specInv 7 5 20 [0, 1, 0, 1, 0, 0, 2] = some [0, 2, 2, 2, 1, 1, 1] :=
  specInv_white_7 [0, 1, 0, 1, 0, 0, 2] [0, 2, 1, 2, 0, 0, 1] [2, 2, 0, 2, 1, 2, 2] [0, 2, 2, 2, 1, 1, 1] demoR1_0101002 demoR2_0101002 demoC_0101002 demoM_0101002

theorem demoR1_1101002 : invRung 7 5 20 [1, 1, 0, 1, 0, 0, 2] [1, 1, 0, 1, 0, 0, 2] 1 2 false = ([1, 1, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_1101002 : invRung 7 5 20 [1, 1, 0, 1, 0, 0, 2] [1, 1, 2, 1, 2, 1, 1] 3 1 true = ([0, 2, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1101002 : fieldCube 7 5 20 [0, 2, 2, 1, 0, 2, 0] = [0, 2, 0, 2, 2, 0, 0] := by
  decide

theorem demoM_1101002 : fieldMul 7 5 20 [0, 2, 0, 2, 2, 0, 0] [1, 1, 0, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1101002 : specInv 7 5 20 [1, 1, 0, 1, 0, 0, 2] = some [0, 2, 0, 2, 2, 0, 0] :=
  specInv_white_7 [1, 1, 0, 1, 0, 0, 2] [1, 1, 2, 1, 2, 1, 1] [0, 2, 2, 1, 0, 2, 0] [0, 2, 0, 2, 2, 0, 0] demoR1_1101002 demoR2_1101002 demoC_1101002 demoM_1101002

theorem demoR1_2101002 : invRung 7 5 20 [2, 1, 0, 1, 0, 0, 2] [2, 1, 0, 1, 0, 0, 2] 1 2 false = ([0, 2, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_2101002 : invRung 7 5 20 [2, 1, 0, 1, 0, 0, 2] [0, 2, 0, 2, 0, 1, 0] 3 1 true = ([0, 0, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_2101002 : fieldCube 7 5 20 [0, 0, 1, 0, 0, 0, 2] = [0, 2, 1, 2, 2, 2, 0] := by
  decide

theorem demoM_2101002 : fieldMul 7 5 20 [0, 2, 1, 2, 2, 2, 0] [2, 1, 0, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101002 : mirrorTrits [0, 2, 1, 2, 2, 2, 0] = [0, 1, 2, 1, 1, 1, 0] := by
  decide

theorem demoInv_2101002 : specInv 7 5 20 [2, 1, 0, 1, 0, 0, 2] = some [0, 1, 2, 1, 1, 1, 0] :=
  specInv_mirror_7 [2, 1, 0, 1, 0, 0, 2] [0, 2, 0, 2, 0, 1, 0] [0, 0, 1, 0, 0, 0, 2] [0, 2, 1, 2, 2, 2, 0] [0, 1, 2, 1, 1, 1, 0] demoR1_2101002 demoR2_2101002 demoC_2101002 demoM_2101002 demoMir_2101002

theorem demoR1_0201002 : invRung 7 5 20 [0, 2, 0, 1, 0, 0, 2] [0, 2, 0, 1, 0, 0, 2] 1 2 false = ([0, 1, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_0201002 : invRung 7 5 20 [0, 2, 0, 1, 0, 0, 2] [0, 1, 0, 2, 2, 1, 2] 3 1 true = ([1, 0, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_0201002 : fieldCube 7 5 20 [1, 0, 2, 1, 0, 2, 2] = [1, 1, 1, 2, 1, 2, 2] := by
  decide

theorem demoM_0201002 : fieldMul 7 5 20 [1, 1, 1, 2, 1, 2, 2] [0, 2, 0, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201002 : mirrorTrits [1, 1, 1, 2, 1, 2, 2] = [2, 2, 2, 1, 2, 1, 1] := by
  decide

theorem demoInv_0201002 : specInv 7 5 20 [0, 2, 0, 1, 0, 0, 2] = some [2, 2, 2, 1, 2, 1, 1] :=
  specInv_mirror_7 [0, 2, 0, 1, 0, 0, 2] [0, 1, 0, 2, 2, 1, 2] [1, 0, 2, 1, 0, 2, 2] [1, 1, 1, 2, 1, 2, 2] [2, 2, 2, 1, 2, 1, 1] demoR1_0201002 demoR2_0201002 demoC_0201002 demoM_0201002 demoMir_0201002

theorem demoR1_1201002 : invRung 7 5 20 [1, 2, 0, 1, 0, 0, 2] [1, 2, 0, 1, 0, 0, 2] 1 2 false = ([2, 2, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_1201002 : invRung 7 5 20 [1, 2, 0, 1, 0, 0, 2] [2, 2, 1, 0, 0, 1, 0] 3 1 true = ([0, 1, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_1201002 : fieldCube 7 5 20 [0, 1, 1, 2, 0, 0, 0] = [2, 0, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_1201002 : fieldMul 7 5 20 [2, 0, 2, 1, 0, 2, 1] [1, 2, 0, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201002 : mirrorTrits [2, 0, 2, 1, 0, 2, 1] = [1, 0, 1, 2, 0, 1, 2] := by
  decide

theorem demoInv_1201002 : specInv 7 5 20 [1, 2, 0, 1, 0, 0, 2] = some [1, 0, 1, 2, 0, 1, 2] :=
  specInv_mirror_7 [1, 2, 0, 1, 0, 0, 2] [2, 2, 1, 0, 0, 1, 0] [0, 1, 1, 2, 0, 0, 0] [2, 0, 2, 1, 0, 2, 1] [1, 0, 1, 2, 0, 1, 2] demoR1_1201002 demoR2_1201002 demoC_1201002 demoM_1201002 demoMir_1201002

theorem demoR1_2201002 : invRung 7 5 20 [2, 2, 0, 1, 0, 0, 2] [2, 2, 0, 1, 0, 0, 2] 1 2 false = ([1, 1, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_2201002 : invRung 7 5 20 [2, 2, 0, 1, 0, 0, 2] [1, 1, 1, 2, 0, 2, 0] 3 1 true = ([0, 1, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_2201002 : fieldCube 7 5 20 [0, 1, 1, 1, 1, 1, 1] = [2, 0, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_2201002 : fieldMul 7 5 20 [2, 0, 1, 0, 2, 1, 2] [2, 2, 0, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2201002 : mirrorTrits [2, 0, 1, 0, 2, 1, 2] = [1, 0, 2, 0, 1, 2, 1] := by
  decide

theorem demoInv_2201002 : specInv 7 5 20 [2, 2, 0, 1, 0, 0, 2] = some [1, 0, 2, 0, 1, 2, 1] :=
  specInv_mirror_7 [2, 2, 0, 1, 0, 0, 2] [1, 1, 1, 2, 0, 2, 0] [0, 1, 1, 1, 1, 1, 1] [2, 0, 1, 0, 2, 1, 2] [1, 0, 2, 0, 1, 2, 1] demoR1_2201002 demoR2_2201002 demoC_2201002 demoM_2201002 demoMir_2201002

theorem demoR1_0011002 : invRung 7 5 20 [0, 0, 1, 1, 0, 0, 2] [0, 0, 1, 1, 0, 0, 2] 1 2 false = ([0, 1, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0011002 : invRung 7 5 20 [0, 0, 1, 1, 0, 0, 2] [0, 1, 2, 2, 0, 0, 0] 3 1 true = ([1, 0, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_0011002 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 2, 2] = [0, 1, 0, 2, 1, 1, 0] := by
  decide

theorem demoM_0011002 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 1, 0] [0, 0, 1, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0011002 : specInv 7 5 20 [0, 0, 1, 1, 0, 0, 2] = some [0, 1, 0, 2, 1, 1, 0] :=
  specInv_white_7 [0, 0, 1, 1, 0, 0, 2] [0, 1, 2, 2, 0, 0, 0] [1, 0, 0, 0, 0, 2, 2] [0, 1, 0, 2, 1, 1, 0] demoR1_0011002 demoR2_0011002 demoC_0011002 demoM_0011002

theorem demoR1_1011002 : invRung 7 5 20 [1, 0, 1, 1, 0, 0, 2] [1, 0, 1, 1, 0, 0, 2] 1 2 false = ([2, 2, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1011002 : invRung 7 5 20 [1, 0, 1, 1, 0, 0, 2] [2, 2, 0, 1, 1, 0, 2] 3 1 true = ([1, 0, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_1011002 : fieldCube 7 5 20 [1, 0, 0, 0, 2, 0, 1] = [1, 0, 2, 0, 1, 0, 0] := by
  decide

theorem demoM_1011002 : fieldMul 7 5 20 [1, 0, 2, 0, 1, 0, 0] [1, 0, 1, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011002 : mirrorTrits [1, 0, 2, 0, 1, 0, 0] = [2, 0, 1, 0, 2, 0, 0] := by
  decide

theorem demoInv_1011002 : specInv 7 5 20 [1, 0, 1, 1, 0, 0, 2] = some [2, 0, 1, 0, 2, 0, 0] :=
  specInv_mirror_7 [1, 0, 1, 1, 0, 0, 2] [2, 2, 0, 1, 1, 0, 2] [1, 0, 0, 0, 2, 0, 1] [1, 0, 2, 0, 1, 0, 0] [2, 0, 1, 0, 2, 0, 0] demoR1_1011002 demoR2_1011002 demoC_1011002 demoM_1011002 demoMir_1011002

theorem demoR1_2011002 : invRung 7 5 20 [2, 0, 1, 1, 0, 0, 2] [2, 0, 1, 1, 0, 0, 2] 1 2 false = ([0, 2, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_2011002 : invRung 7 5 20 [2, 0, 1, 1, 0, 0, 2] [0, 2, 2, 2, 0, 2, 1] 3 1 true = ([1, 1, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_2011002 : fieldCube 7 5 20 [1, 1, 0, 0, 0, 0, 0] = [1, 0, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_2011002 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 0, 0] [2, 0, 1, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2011002 : specInv 7 5 20 [2, 0, 1, 1, 0, 0, 2] = some [1, 0, 0, 1, 0, 0, 0] :=
  specInv_white_7 [2, 0, 1, 1, 0, 0, 2] [0, 2, 2, 2, 0, 2, 1] [1, 1, 0, 0, 0, 0, 0] [1, 0, 0, 1, 0, 0, 0] demoR1_2011002 demoR2_2011002 demoC_2011002 demoM_2011002

theorem demoR1_0111002 : invRung 7 5 20 [0, 1, 1, 1, 0, 0, 2] [0, 1, 1, 1, 0, 0, 2] 1 2 false = ([1, 1, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_0111002 : invRung 7 5 20 [0, 1, 1, 1, 0, 0, 2] [1, 1, 0, 0, 2, 1, 0] 3 1 true = ([0, 2, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0111002 : fieldCube 7 5 20 [0, 2, 2, 2, 0, 1, 1] = [0, 2, 2, 0, 2, 1, 2] := by
  decide

theorem demoM_0111002 : fieldMul 7 5 20 [0, 2, 2, 0, 2, 1, 2] [0, 1, 1, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0111002 : specInv 7 5 20 [0, 1, 1, 1, 0, 0, 2] = some [0, 2, 2, 0, 2, 1, 2] :=
  specInv_white_7 [0, 1, 1, 1, 0, 0, 2] [1, 1, 0, 0, 2, 1, 0] [0, 2, 2, 2, 0, 1, 1] [0, 2, 2, 0, 2, 1, 2] demoR1_0111002 demoR2_0111002 demoC_0111002 demoM_0111002

theorem demoR1_1111002 : invRung 7 5 20 [1, 1, 1, 1, 0, 0, 2] [1, 1, 1, 1, 0, 0, 2] 1 2 false = ([1, 2, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_1111002 : invRung 7 5 20 [1, 1, 1, 1, 0, 0, 2] [1, 2, 2, 2, 1, 2, 1] 3 1 true = ([0, 1, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_1111002 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 2, 0] = [1, 0, 1, 2, 2, 2, 2] := by
  decide

theorem demoM_1111002 : fieldMul 7 5 20 [1, 0, 1, 2, 2, 2, 2] [1, 1, 1, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111002 : mirrorTrits [1, 0, 1, 2, 2, 2, 2] = [2, 0, 2, 1, 1, 1, 1] := by
  decide

theorem demoInv_1111002 : specInv 7 5 20 [1, 1, 1, 1, 0, 0, 2] = some [2, 0, 2, 1, 1, 1, 1] :=
  specInv_mirror_7 [1, 1, 1, 1, 0, 0, 2] [1, 2, 2, 2, 1, 2, 1] [0, 1, 0, 2, 1, 2, 0] [1, 0, 1, 2, 2, 2, 2] [2, 0, 2, 1, 1, 1, 1] demoR1_1111002 demoR2_1111002 demoC_1111002 demoM_1111002 demoMir_1111002

theorem demoR1_2111002 : invRung 7 5 20 [2, 1, 1, 1, 0, 0, 2] [2, 1, 1, 1, 0, 0, 2] 1 2 false = ([2, 1, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2111002 : invRung 7 5 20 [2, 1, 1, 1, 0, 0, 2] [2, 1, 1, 2, 1, 1, 2] 3 1 true = ([1, 1, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_2111002 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 2, 2] = [1, 2, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_2111002 : fieldMul 7 5 20 [1, 2, 1, 1, 1, 0, 2] [2, 1, 1, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2111002 : specInv 7 5 20 [2, 1, 1, 1, 0, 0, 2] = some [1, 2, 1, 1, 1, 0, 2] :=
  specInv_white_7 [2, 1, 1, 1, 0, 0, 2] [2, 1, 1, 2, 1, 1, 2] [1, 1, 1, 1, 1, 2, 2] [1, 2, 1, 1, 1, 0, 2] demoR1_2111002 demoR2_2111002 demoC_2111002 demoM_2111002

theorem demoR1_0211002 : invRung 7 5 20 [0, 2, 1, 1, 0, 0, 2] [0, 2, 1, 1, 0, 0, 2] 1 2 false = ([1, 0, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_0211002 : invRung 7 5 20 [0, 2, 1, 1, 0, 0, 2] [1, 0, 0, 1, 0, 1, 0] 3 1 true = ([1, 2, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0211002 : fieldCube 7 5 20 [1, 2, 0, 0, 1, 2, 1] = [0, 1, 1, 1, 0, 1, 0] := by
  decide

theorem demoM_0211002 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 1, 0] [0, 2, 1, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0211002 : specInv 7 5 20 [0, 2, 1, 1, 0, 0, 2] = some [0, 1, 1, 1, 0, 1, 0] :=
  specInv_white_7 [0, 2, 1, 1, 0, 0, 2] [1, 0, 0, 1, 0, 1, 0] [1, 2, 0, 0, 1, 2, 1] [0, 1, 1, 1, 0, 1, 0] demoR1_0211002 demoR2_0211002 demoC_0211002 demoM_0211002

theorem demoR1_1211002 : invRung 7 5 20 [1, 2, 1, 1, 0, 0, 2] [1, 2, 1, 1, 0, 0, 2] 1 2 false = ([2, 2, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1211002 : invRung 7 5 20 [1, 2, 1, 1, 0, 0, 2] [2, 2, 0, 1, 2, 2, 1] 3 1 true = ([1, 2, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_1211002 : fieldCube 7 5 20 [1, 2, 1, 1, 0, 1, 0] = [0, 1, 2, 2, 1, 2, 0] := by
  decide

theorem demoM_1211002 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 2, 0] [1, 2, 1, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1211002 : specInv 7 5 20 [1, 2, 1, 1, 0, 0, 2] = some [0, 1, 2, 2, 1, 2, 0] :=
  specInv_white_7 [1, 2, 1, 1, 0, 0, 2] [2, 2, 0, 1, 2, 2, 1] [1, 2, 1, 1, 0, 1, 0] [0, 1, 2, 2, 1, 2, 0] demoR1_1211002 demoR2_1211002 demoC_1211002 demoM_1211002

theorem demoR1_2211002 : invRung 7 5 20 [2, 2, 1, 1, 0, 0, 2] [2, 2, 1, 1, 0, 0, 2] 1 2 false = ([0, 1, 2, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_2211002 : invRung 7 5 20 [2, 2, 1, 1, 0, 0, 2] [0, 1, 2, 1, 2, 0, 2] 3 1 true = ([1, 1, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_2211002 : fieldCube 7 5 20 [1, 1, 0, 2, 2, 2, 0] = [2, 1, 1, 0, 2, 0, 0] := by
  decide

theorem demoM_2211002 : fieldMul 7 5 20 [2, 1, 1, 0, 2, 0, 0] [2, 2, 1, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211002 : mirrorTrits [2, 1, 1, 0, 2, 0, 0] = [1, 2, 2, 0, 1, 0, 0] := by
  decide

theorem demoInv_2211002 : specInv 7 5 20 [2, 2, 1, 1, 0, 0, 2] = some [1, 2, 2, 0, 1, 0, 0] :=
  specInv_mirror_7 [2, 2, 1, 1, 0, 0, 2] [0, 1, 2, 1, 2, 0, 2] [1, 1, 0, 2, 2, 2, 0] [2, 1, 1, 0, 2, 0, 0] [1, 2, 2, 0, 1, 0, 0] demoR1_2211002 demoR2_2211002 demoC_2211002 demoM_2211002 demoMir_2211002

theorem demoR1_0021002 : invRung 7 5 20 [0, 0, 2, 1, 0, 0, 2] [0, 0, 2, 1, 0, 0, 2] 1 2 false = ([2, 0, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_0021002 : invRung 7 5 20 [0, 0, 2, 1, 0, 0, 2] [2, 0, 2, 0, 0, 2, 0] 3 1 true = ([2, 0, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0021002 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 0, 1] = [1, 2, 1, 2, 1, 1, 1] := by
  decide

theorem demoM_0021002 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 1, 1] [0, 0, 2, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021002 : mirrorTrits [1, 2, 1, 2, 1, 1, 1] = [2, 1, 2, 1, 2, 2, 2] := by
  decide

theorem demoInv_0021002 : specInv 7 5 20 [0, 0, 2, 1, 0, 0, 2] = some [2, 1, 2, 1, 2, 2, 2] :=
  specInv_mirror_7 [0, 0, 2, 1, 0, 0, 2] [2, 0, 2, 0, 0, 2, 0] [2, 0, 2, 2, 1, 0, 1] [1, 2, 1, 2, 1, 1, 1] [2, 1, 2, 1, 2, 2, 2] demoR1_0021002 demoR2_0021002 demoC_0021002 demoM_0021002 demoMir_0021002

theorem demoR1_1021002 : invRung 7 5 20 [1, 0, 2, 1, 0, 0, 2] [1, 0, 2, 1, 0, 0, 2] 1 2 false = ([2, 1, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_1021002 : invRung 7 5 20 [1, 0, 2, 1, 0, 0, 2] [2, 1, 1, 0, 0, 1, 0] 3 1 true = ([1, 2, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_1021002 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 1, 0] = [2, 0, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_1021002 : fieldMul 7 5 20 [2, 0, 1, 1, 1, 0, 2] [1, 0, 2, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1021002 : specInv 7 5 20 [1, 0, 2, 1, 0, 0, 2] = some [2, 0, 1, 1, 1, 0, 2] :=
  specInv_white_7 [1, 0, 2, 1, 0, 0, 2] [2, 1, 1, 0, 0, 1, 0] [1, 2, 1, 0, 2, 1, 0] [2, 0, 1, 1, 1, 0, 2] demoR1_1021002 demoR2_1021002 demoC_1021002 demoM_1021002

theorem demoR1_2021002 : invRung 7 5 20 [2, 0, 2, 1, 0, 0, 2] [2, 0, 2, 1, 0, 0, 2] 1 2 false = ([1, 0, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_2021002 : invRung 7 5 20 [2, 0, 2, 1, 0, 0, 2] [1, 0, 1, 1, 0, 1, 1] 3 1 true = ([0, 0, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_2021002 : fieldCube 7 5 20 [0, 0, 2, 2, 1, 1, 0] = [0, 2, 0, 1, 1, 1, 2] := by
  decide

theorem demoM_2021002 : fieldMul 7 5 20 [0, 2, 0, 1, 1, 1, 2] [2, 0, 2, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2021002 : specInv 7 5 20 [2, 0, 2, 1, 0, 0, 2] = some [0, 2, 0, 1, 1, 1, 2] :=
  specInv_white_7 [2, 0, 2, 1, 0, 0, 2] [1, 0, 1, 1, 0, 1, 1] [0, 0, 2, 2, 1, 1, 0] [0, 2, 0, 1, 1, 1, 2] demoR1_2021002 demoR2_2021002 demoC_2021002 demoM_2021002

theorem demoR1_0121002 : invRung 7 5 20 [0, 1, 2, 1, 0, 0, 2] [0, 1, 2, 1, 0, 0, 2] 1 2 false = ([2, 0, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_0121002 : invRung 7 5 20 [0, 1, 2, 1, 0, 0, 2] [2, 0, 2, 1, 0, 0, 1] 3 1 true = ([0, 0, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_0121002 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 2, 0] = [2, 1, 2, 2, 2, 1, 1] := by
  decide

theorem demoM_0121002 : fieldMul 7 5 20 [2, 1, 2, 2, 2, 1, 1] [0, 1, 2, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0121002 : mirrorTrits [2, 1, 2, 2, 2, 1, 1] = [1, 2, 1, 1, 1, 2, 2] := by
  decide

theorem demoInv_0121002 : specInv 7 5 20 [0, 1, 2, 1, 0, 0, 2] = some [1, 2, 1, 1, 1, 2, 2] :=
  specInv_mirror_7 [0, 1, 2, 1, 0, 0, 2] [2, 0, 2, 1, 0, 0, 1] [0, 0, 1, 0, 2, 2, 0] [2, 1, 2, 2, 2, 1, 1] [1, 2, 1, 1, 1, 2, 2] demoR1_0121002 demoR2_0121002 demoC_0121002 demoM_0121002 demoMir_0121002

theorem demoR1_1121002 : invRung 7 5 20 [1, 1, 2, 1, 0, 0, 2] [1, 1, 2, 1, 0, 0, 2] 1 2 false = ([0, 0, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_1121002 : invRung 7 5 20 [1, 1, 2, 1, 0, 0, 2] [0, 0, 0, 0, 2, 1, 2] 3 1 true = ([1, 2, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_1121002 : fieldCube 7 5 20 [1, 2, 2, 0, 1, 0, 2] = [1, 0, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_1121002 : fieldMul 7 5 20 [1, 0, 1, 2, 2, 0, 2] [1, 1, 2, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121002 : mirrorTrits [1, 0, 1, 2, 2, 0, 2] = [2, 0, 2, 1, 1, 0, 1] := by
  decide

theorem demoInv_1121002 : specInv 7 5 20 [1, 1, 2, 1, 0, 0, 2] = some [2, 0, 2, 1, 1, 0, 1] :=
  specInv_mirror_7 [1, 1, 2, 1, 0, 0, 2] [0, 0, 0, 0, 2, 1, 2] [1, 2, 2, 0, 1, 0, 2] [1, 0, 1, 2, 2, 0, 2] [2, 0, 2, 1, 1, 0, 1] demoR1_1121002 demoR2_1121002 demoC_1121002 demoM_1121002 demoMir_1121002

theorem demoR1_2121002 : invRung 7 5 20 [2, 1, 2, 1, 0, 0, 2] [2, 1, 2, 1, 0, 0, 2] 1 2 false = ([2, 0, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_2121002 : invRung 7 5 20 [2, 1, 2, 1, 0, 0, 2] [2, 0, 1, 2, 1, 2, 1] 3 1 true = ([1, 2, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_2121002 : fieldCube 7 5 20 [1, 2, 1, 1, 0, 1, 2] = [0, 0, 0, 1, 0, 1, 2] := by
  decide

theorem demoM_2121002 : fieldMul 7 5 20 [0, 0, 0, 1, 0, 1, 2] [2, 1, 2, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2121002 : specInv 7 5 20 [2, 1, 2, 1, 0, 0, 2] = some [0, 0, 0, 1, 0, 1, 2] :=
  specInv_white_7 [2, 1, 2, 1, 0, 0, 2] [2, 0, 1, 2, 1, 2, 1] [1, 2, 1, 1, 0, 1, 2] [0, 0, 0, 1, 0, 1, 2] demoR1_2121002 demoR2_2121002 demoC_2121002 demoM_2121002

theorem demoR1_0221002 : invRung 7 5 20 [0, 2, 2, 1, 0, 0, 2] [0, 2, 2, 1, 0, 0, 2] 1 2 false = ([2, 1, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_0221002 : invRung 7 5 20 [0, 2, 2, 1, 0, 0, 2] [2, 1, 2, 2, 2, 1, 2] 3 1 true = ([1, 0, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_0221002 : fieldCube 7 5 20 [1, 0, 2, 1, 2, 2, 1] = [1, 2, 2, 0, 0, 0, 0] := by
  decide

theorem demoM_0221002 : fieldMul 7 5 20 [1, 2, 2, 0, 0, 0, 0] [0, 2, 2, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0221002 : specInv 7 5 20 [0, 2, 2, 1, 0, 0, 2] = some [1, 2, 2, 0, 0, 0, 0] :=
  specInv_white_7 [0, 2, 2, 1, 0, 0, 2] [2, 1, 2, 2, 2, 1, 2] [1, 0, 2, 1, 2, 2, 1] [1, 2, 2, 0, 0, 0, 0] demoR1_0221002 demoR2_0221002 demoC_0221002 demoM_0221002

theorem demoR1_1221002 : invRung 7 5 20 [1, 2, 2, 1, 0, 0, 2] [1, 2, 2, 1, 0, 0, 2] 1 2 false = ([1, 1, 2, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_1221002 : invRung 7 5 20 [1, 2, 2, 1, 0, 0, 2] [1, 1, 2, 1, 2, 0, 2] 3 1 true = ([1, 0, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_1221002 : fieldCube 7 5 20 [1, 0, 0, 2, 0, 0, 1] = [0, 1, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_1221002 : fieldMul 7 5 20 [0, 1, 1, 1, 1, 0, 1] [1, 2, 2, 1, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221002 : mirrorTrits [0, 1, 1, 1, 1, 0, 1] = [0, 2, 2, 2, 2, 0, 2] := by
  decide

theorem demoInv_1221002 : specInv 7 5 20 [1, 2, 2, 1, 0, 0, 2] = some [0, 2, 2, 2, 2, 0, 2] :=
  specInv_mirror_7 [1, 2, 2, 1, 0, 0, 2] [1, 1, 2, 1, 2, 0, 2] [1, 0, 0, 2, 0, 0, 1] [0, 1, 1, 1, 1, 0, 1] [0, 2, 2, 2, 2, 0, 2] demoR1_1221002 demoR2_1221002 demoC_1221002 demoM_1221002 demoMir_1221002

theorem demoR1_2221002 : invRung 7 5 20 [2, 2, 2, 1, 0, 0, 2] [2, 2, 2, 1, 0, 0, 2] 1 2 false = ([0, 0, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_2221002 : invRung 7 5 20 [2, 2, 2, 1, 0, 0, 2] [0, 0, 1, 2, 2, 1, 0] 3 1 true = ([2, 2, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_2221002 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 2, 0] = [2, 0, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_2221002 : fieldMul 7 5 20 [2, 0, 0, 0, 2, 1, 0] [2, 2, 2, 1, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2221002 : specInv 7 5 20 [2, 2, 2, 1, 0, 0, 2] = some [2, 0, 0, 0, 2, 1, 0] :=
  specInv_white_7 [2, 2, 2, 1, 0, 0, 2] [0, 0, 1, 2, 2, 1, 0] [2, 2, 1, 1, 1, 2, 0] [2, 0, 0, 0, 2, 1, 0] demoR1_2221002 demoR2_2221002 demoC_2221002 demoM_2221002

theorem demoR1_0002002 : invRung 7 5 20 [0, 0, 0, 2, 0, 0, 2] [0, 0, 0, 2, 0, 0, 2] 1 2 false = ([2, 0, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_0002002 : invRung 7 5 20 [0, 0, 0, 2, 0, 0, 2] [2, 0, 1, 1, 1, 1, 1] 3 1 true = ([0, 0, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0002002 : fieldCube 7 5 20 [0, 0, 0, 0, 2, 1, 0] = [1, 0, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_0002002 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 0, 1] [0, 0, 0, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002002 : mirrorTrits [1, 0, 1, 2, 1, 0, 1] = [2, 0, 2, 1, 2, 0, 2] := by
  decide

theorem demoInv_0002002 : specInv 7 5 20 [0, 0, 0, 2, 0, 0, 2] = some [2, 0, 2, 1, 2, 0, 2] :=
  specInv_mirror_7 [0, 0, 0, 2, 0, 0, 2] [2, 0, 1, 1, 1, 1, 1] [0, 0, 0, 0, 2, 1, 0] [1, 0, 1, 2, 1, 0, 1] [2, 0, 2, 1, 2, 0, 2] demoR1_0002002 demoR2_0002002 demoC_0002002 demoM_0002002 demoMir_0002002

theorem demoR1_1002002 : invRung 7 5 20 [1, 0, 0, 2, 0, 0, 2] [1, 0, 0, 2, 0, 0, 2] 1 2 false = ([2, 1, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_1002002 : invRung 7 5 20 [1, 0, 0, 2, 0, 0, 2] [2, 1, 0, 1, 1, 1, 1] 3 1 true = ([0, 2, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_1002002 : fieldCube 7 5 20 [0, 2, 2, 1, 0, 0, 2] = [1, 2, 2, 1, 2, 0, 1] := by
  decide

theorem demoM_1002002 : fieldMul 7 5 20 [1, 2, 2, 1, 2, 0, 1] [1, 0, 0, 2, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1002002 : specInv 7 5 20 [1, 0, 0, 2, 0, 0, 2] = some [1, 2, 2, 1, 2, 0, 1] :=
  specInv_white_7 [1, 0, 0, 2, 0, 0, 2] [2, 1, 0, 1, 1, 1, 1] [0, 2, 2, 1, 0, 0, 2] [1, 2, 2, 1, 2, 0, 1] demoR1_1002002 demoR2_1002002 demoC_1002002 demoM_1002002

theorem demoR1_2002002 : invRung 7 5 20 [2, 0, 0, 2, 0, 0, 2] [2, 0, 0, 2, 0, 0, 2] 1 2 false = ([1, 1, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2002002 : invRung 7 5 20 [2, 0, 0, 2, 0, 0, 2] [1, 1, 1, 0, 2, 2, 0] 3 1 true = ([2, 2, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_2002002 : fieldCube 7 5 20 [2, 2, 2, 2, 2, 0, 2] = [1, 1, 0, 0, 2, 0, 0] := by
  decide

theorem demoM_2002002 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 0, 0] [2, 0, 0, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002002 : mirrorTrits [1, 1, 0, 0, 2, 0, 0] = [2, 2, 0, 0, 1, 0, 0] := by
  decide

theorem demoInv_2002002 : specInv 7 5 20 [2, 0, 0, 2, 0, 0, 2] = some [2, 2, 0, 0, 1, 0, 0] :=
  specInv_mirror_7 [2, 0, 0, 2, 0, 0, 2] [1, 1, 1, 0, 2, 2, 0] [2, 2, 2, 2, 2, 0, 2] [1, 1, 0, 0, 2, 0, 0] [2, 2, 0, 0, 1, 0, 0] demoR1_2002002 demoR2_2002002 demoC_2002002 demoM_2002002 demoMir_2002002

theorem demoR1_0102002 : invRung 7 5 20 [0, 1, 0, 2, 0, 0, 2] [0, 1, 0, 2, 0, 0, 2] 1 2 false = ([0, 1, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0102002 : invRung 7 5 20 [0, 1, 0, 2, 0, 0, 2] [0, 1, 2, 0, 1, 2, 1] 3 1 true = ([2, 2, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_0102002 : fieldCube 7 5 20 [2, 2, 2, 1, 2, 2, 1] = [2, 2, 2, 2, 0, 0, 0] := by
  decide

theorem demoM_0102002 : fieldMul 7 5 20 [2, 2, 2, 2, 0, 0, 0] [0, 1, 0, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102002 : mirrorTrits [2, 2, 2, 2, 0, 0, 0] = [1, 1, 1, 1, 0, 0, 0] := by
  decide

theorem demoInv_0102002 : specInv 7 5 20 [0, 1, 0, 2, 0, 0, 2] = some [1, 1, 1, 1, 0, 0, 0] :=
  specInv_mirror_7 [0, 1, 0, 2, 0, 0, 2] [0, 1, 2, 0, 1, 2, 1] [2, 2, 2, 1, 2, 2, 1] [2, 2, 2, 2, 0, 0, 0] [1, 1, 1, 1, 0, 0, 0] demoR1_0102002 demoR2_0102002 demoC_0102002 demoM_0102002 demoMir_0102002

theorem demoR1_1102002 : invRung 7 5 20 [1, 1, 0, 2, 0, 0, 2] [1, 1, 0, 2, 0, 0, 2] 1 2 false = ([2, 0, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_1102002 : invRung 7 5 20 [1, 1, 0, 2, 0, 0, 2] [2, 0, 1, 1, 0, 1, 1] 3 1 true = ([0, 0, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_1102002 : fieldCube 7 5 20 [0, 0, 2, 2, 0, 1, 2] = [0, 0, 1, 2, 0, 2, 0] := by
  decide

theorem demoM_1102002 : fieldMul 7 5 20 [0, 0, 1, 2, 0, 2, 0] [1, 1, 0, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102002 : mirrorTrits [0, 0, 1, 2, 0, 2, 0] = [0, 0, 2, 1, 0, 1, 0] := by
  decide

theorem demoInv_1102002 : specInv 7 5 20 [1, 1, 0, 2, 0, 0, 2] = some [0, 0, 2, 1, 0, 1, 0] :=
  specInv_mirror_7 [1, 1, 0, 2, 0, 0, 2] [2, 0, 1, 1, 0, 1, 1] [0, 0, 2, 2, 0, 1, 2] [0, 0, 1, 2, 0, 2, 0] [0, 0, 2, 1, 0, 1, 0] demoR1_1102002 demoR2_1102002 demoC_1102002 demoM_1102002 demoMir_1102002

theorem demoR1_2102002 : invRung 7 5 20 [2, 1, 0, 2, 0, 0, 2] [2, 1, 0, 2, 0, 0, 2] 1 2 false = ([2, 0, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_2102002 : invRung 7 5 20 [2, 1, 0, 2, 0, 0, 2] [2, 0, 1, 0, 0, 0, 0] 3 1 true = ([0, 0, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_2102002 : fieldCube 7 5 20 [0, 0, 0, 0, 2, 0, 2] = [0, 1, 1, 1, 2, 1, 1] := by
  decide

theorem demoM_2102002 : fieldMul 7 5 20 [0, 1, 1, 1, 2, 1, 1] [2, 1, 0, 2, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2102002 : specInv 7 5 20 [2, 1, 0, 2, 0, 0, 2] = some [0, 1, 1, 1, 2, 1, 1] :=
  specInv_white_7 [2, 1, 0, 2, 0, 0, 2] [2, 0, 1, 0, 0, 0, 0] [0, 0, 0, 0, 2, 0, 2] [0, 1, 1, 1, 2, 1, 1] demoR1_2102002 demoR2_2102002 demoC_2102002 demoM_2102002

theorem demoR1_0202002 : invRung 7 5 20 [0, 2, 0, 2, 0, 0, 2] [0, 2, 0, 2, 0, 0, 2] 1 2 false = ([2, 0, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0202002 : invRung 7 5 20 [0, 2, 0, 2, 0, 0, 2] [2, 0, 1, 0, 2, 2, 2] 3 1 true = ([0, 1, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0202002 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 1, 0] = [1, 0, 1, 0, 1, 0, 0] := by
  decide

theorem demoM_0202002 : fieldMul 7 5 20 [1, 0, 1, 0, 1, 0, 0] [0, 2, 0, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202002 : mirrorTrits [1, 0, 1, 0, 1, 0, 0] = [2, 0, 2, 0, 2, 0, 0] := by
  decide

theorem demoInv_0202002 : specInv 7 5 20 [0, 2, 0, 2, 0, 0, 2] = some [2, 0, 2, 0, 2, 0, 0] :=
  specInv_mirror_7 [0, 2, 0, 2, 0, 0, 2] [2, 0, 1, 0, 2, 2, 2] [0, 1, 2, 0, 2, 1, 0] [1, 0, 1, 0, 1, 0, 0] [2, 0, 2, 0, 2, 0, 0] demoR1_0202002 demoR2_0202002 demoC_0202002 demoM_0202002 demoMir_0202002

theorem demoR1_1202002 : invRung 7 5 20 [1, 2, 0, 2, 0, 0, 2] [1, 2, 0, 2, 0, 0, 2] 1 2 false = ([0, 1, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_1202002 : invRung 7 5 20 [1, 2, 0, 2, 0, 0, 2] [0, 1, 0, 0, 2, 2, 0] 3 1 true = ([1, 2, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_1202002 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 0, 2] = [1, 1, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_1202002 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 1, 2] [1, 2, 0, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202002 : mirrorTrits [1, 1, 1, 0, 2, 1, 2] = [2, 2, 2, 0, 1, 2, 1] := by
  decide

theorem demoInv_1202002 : specInv 7 5 20 [1, 2, 0, 2, 0, 0, 2] = some [2, 2, 2, 0, 1, 2, 1] :=
  specInv_mirror_7 [1, 2, 0, 2, 0, 0, 2] [0, 1, 0, 0, 2, 2, 0] [1, 2, 1, 0, 2, 0, 2] [1, 1, 1, 0, 2, 1, 2] [2, 2, 2, 0, 1, 2, 1] demoR1_1202002 demoR2_1202002 demoC_1202002 demoM_1202002 demoMir_1202002

theorem demoR1_2202002 : invRung 7 5 20 [2, 2, 0, 2, 0, 0, 2] [2, 2, 0, 2, 0, 0, 2] 1 2 false = ([1, 2, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2202002 : invRung 7 5 20 [2, 2, 0, 2, 0, 0, 2] [1, 2, 2, 0, 0, 1, 0] 3 1 true = ([2, 2, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_2202002 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 0, 0] = [0, 1, 1, 0, 0, 2, 2] := by
  decide

theorem demoM_2202002 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 2, 2] [2, 2, 0, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202002 : mirrorTrits [0, 1, 1, 0, 0, 2, 2] = [0, 2, 2, 0, 0, 1, 1] := by
  decide

theorem demoInv_2202002 : specInv 7 5 20 [2, 2, 0, 2, 0, 0, 2] = some [0, 2, 2, 0, 0, 1, 1] :=
  specInv_mirror_7 [2, 2, 0, 2, 0, 0, 2] [1, 2, 2, 0, 0, 1, 0] [2, 2, 1, 1, 1, 0, 0] [0, 1, 1, 0, 0, 2, 2] [0, 2, 2, 0, 0, 1, 1] demoR1_2202002 demoR2_2202002 demoC_2202002 demoM_2202002 demoMir_2202002

theorem demoR1_0012002 : invRung 7 5 20 [0, 0, 1, 2, 0, 0, 2] [0, 0, 1, 2, 0, 0, 2] 1 2 false = ([1, 0, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_0012002 : invRung 7 5 20 [0, 0, 1, 2, 0, 0, 2] [1, 0, 0, 2, 1, 2, 2] 3 1 true = ([0, 2, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0012002 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 0, 1] = [1, 1, 0, 0, 1, 2, 2] := by
  decide

theorem demoM_0012002 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 2, 2] [0, 0, 1, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0012002 : mirrorTrits [1, 1, 0, 0, 1, 2, 2] = [2, 2, 0, 0, 2, 1, 1] := by
  decide

theorem demoInv_0012002 : specInv 7 5 20 [0, 0, 1, 2, 0, 0, 2] = some [2, 2, 0, 0, 2, 1, 1] :=
  specInv_mirror_7 [0, 0, 1, 2, 0, 0, 2] [1, 0, 0, 2, 1, 2, 2] [0, 2, 1, 1, 0, 0, 1] [1, 1, 0, 0, 1, 2, 2] [2, 2, 0, 0, 2, 1, 1] demoR1_0012002 demoR2_0012002 demoC_0012002 demoM_0012002 demoMir_0012002

theorem demoR1_1012002 : invRung 7 5 20 [1, 0, 1, 2, 0, 0, 2] [1, 0, 1, 2, 0, 0, 2] 1 2 false = ([0, 2, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_1012002 : invRung 7 5 20 [1, 0, 1, 2, 0, 0, 2] [0, 2, 0, 2, 2, 2, 2] 3 1 true = ([0, 0, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_1012002 : fieldCube 7 5 20 [0, 0, 0, 2, 2, 1, 1] = [0, 1, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_1012002 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 0, 2] [1, 0, 1, 2, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1012002 : specInv 7 5 20 [1, 0, 1, 2, 0, 0, 2] = some [0, 1, 2, 0, 2, 0, 2] :=
  specInv_white_7 [1, 0, 1, 2, 0, 0, 2] [0, 2, 0, 2, 2, 2, 2] [0, 0, 0, 2, 2, 1, 1] [0, 1, 2, 0, 2, 0, 2] demoR1_1012002 demoR2_1012002 demoC_1012002 demoM_1012002

theorem demoR1_2012002 : invRung 7 5 20 [2, 0, 1, 2, 0, 0, 2] [2, 0, 1, 2, 0, 0, 2] 1 2 false = ([1, 2, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_2012002 : invRung 7 5 20 [2, 0, 1, 2, 0, 0, 2] [1, 2, 2, 0, 0, 2, 2] 3 1 true = ([1, 1, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_2012002 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 1, 2] = [0, 1, 0, 1, 0, 2, 0] := by
  decide

theorem demoM_2012002 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 2, 0] [2, 0, 1, 2, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2012002 : specInv 7 5 20 [2, 0, 1, 2, 0, 0, 2] = some [0, 1, 0, 1, 0, 2, 0] :=
  specInv_white_7 [2, 0, 1, 2, 0, 0, 2] [1, 2, 2, 0, 0, 2, 2] [1, 1, 1, 1, 1, 1, 2] [0, 1, 0, 1, 0, 2, 0] demoR1_2012002 demoR2_2012002 demoC_2012002 demoM_2012002

theorem demoR1_0112002 : invRung 7 5 20 [0, 1, 1, 2, 0, 0, 2] [0, 1, 1, 2, 0, 0, 2] 1 2 false = ([2, 1, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_0112002 : invRung 7 5 20 [0, 1, 1, 2, 0, 0, 2] [2, 1, 0, 0, 2, 0, 1] 3 1 true = ([1, 1, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0112002 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 0, 1] = [2, 0, 0, 1, 1, 1, 0] := by
  decide

theorem demoM_0112002 : fieldMul 7 5 20 [2, 0, 0, 1, 1, 1, 0] [0, 1, 1, 2, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0112002 : specInv 7 5 20 [0, 1, 1, 2, 0, 0, 2] = some [2, 0, 0, 1, 1, 1, 0] :=
  specInv_white_7 [0, 1, 1, 2, 0, 0, 2] [2, 1, 0, 0, 2, 0, 1] [1, 1, 0, 1, 2, 0, 1] [2, 0, 0, 1, 1, 1, 0] demoR1_0112002 demoR2_0112002 demoC_0112002 demoM_0112002

theorem demoR1_1112002 : invRung 7 5 20 [1, 1, 1, 2, 0, 0, 2] [1, 1, 1, 2, 0, 0, 2] 1 2 false = ([0, 0, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_1112002 : invRung 7 5 20 [1, 1, 1, 2, 0, 0, 2] [0, 0, 1, 0, 0, 0, 0] 3 1 true = ([1, 0, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_1112002 : fieldCube 7 5 20 [1, 0, 2, 0, 1, 1, 2] = [2, 1, 2, 0, 0, 1, 1] := by
  decide

theorem demoM_1112002 : fieldMul 7 5 20 [2, 1, 2, 0, 0, 1, 1] [1, 1, 1, 2, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1112002 : specInv 7 5 20 [1, 1, 1, 2, 0, 0, 2] = some [2, 1, 2, 0, 0, 1, 1] :=
  specInv_white_7 [1, 1, 1, 2, 0, 0, 2] [0, 0, 1, 0, 0, 0, 0] [1, 0, 2, 0, 1, 1, 2] [2, 1, 2, 0, 0, 1, 1] demoR1_1112002 demoR2_1112002 demoC_1112002 demoM_1112002

theorem demoR1_2112002 : invRung 7 5 20 [2, 1, 1, 2, 0, 0, 2] [2, 1, 1, 2, 0, 0, 2] 1 2 false = ([2, 2, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_2112002 : invRung 7 5 20 [2, 1, 1, 2, 0, 0, 2] [2, 2, 0, 0, 1, 2, 2] 3 1 true = ([2, 0, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2112002 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 1, 0] = [0, 2, 1, 1, 1, 2, 1] := by
  decide

theorem demoM_2112002 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 2, 1] [2, 1, 1, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112002 : mirrorTrits [0, 2, 1, 1, 1, 2, 1] = [0, 1, 2, 2, 2, 1, 2] := by
  decide

theorem demoInv_2112002 : specInv 7 5 20 [2, 1, 1, 2, 0, 0, 2] = some [0, 1, 2, 2, 2, 1, 2] :=
  specInv_mirror_7 [2, 1, 1, 2, 0, 0, 2] [2, 2, 0, 0, 1, 2, 2] [2, 0, 1, 0, 1, 1, 0] [0, 2, 1, 1, 1, 2, 1] [0, 1, 2, 2, 2, 1, 2] demoR1_2112002 demoR2_2112002 demoC_2112002 demoM_2112002 demoMir_2112002

theorem demoR1_0212002 : invRung 7 5 20 [0, 2, 1, 2, 0, 0, 2] [0, 2, 1, 2, 0, 0, 2] 1 2 false = ([2, 2, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_0212002 : invRung 7 5 20 [0, 2, 1, 2, 0, 0, 2] [2, 2, 2, 2, 1, 1, 1] 3 1 true = ([0, 2, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0212002 : fieldCube 7 5 20 [0, 2, 2, 0, 2, 1, 0] = [1, 0, 1, 1, 1, 0, 0] := by
  decide

theorem demoM_0212002 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 0, 0] [0, 2, 1, 2, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0212002 : specInv 7 5 20 [0, 2, 1, 2, 0, 0, 2] = some [1, 0, 1, 1, 1, 0, 0] :=
  specInv_white_7 [0, 2, 1, 2, 0, 0, 2] [2, 2, 2, 2, 1, 1, 1] [0, 2, 2, 0, 2, 1, 0] [1, 0, 1, 1, 1, 0, 0] demoR1_0212002 demoR2_0212002 demoC_0212002 demoM_0212002

theorem demoR1_1212002 : invRung 7 5 20 [1, 2, 1, 2, 0, 0, 2] [1, 2, 1, 2, 0, 0, 2] 1 2 false = ([2, 2, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1212002 : invRung 7 5 20 [1, 2, 1, 2, 0, 0, 2] [2, 2, 1, 0, 1, 0, 0] 3 1 true = ([0, 0, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_1212002 : fieldCube 7 5 20 [0, 0, 1, 1, 0, 0, 0] = [1, 0, 1, 0, 0, 1, 1] := by
  decide

theorem demoM_1212002 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 1, 1] [1, 2, 1, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212002 : mirrorTrits [1, 0, 1, 0, 0, 1, 1] = [2, 0, 2, 0, 0, 2, 2] := by
  decide

theorem demoInv_1212002 : specInv 7 5 20 [1, 2, 1, 2, 0, 0, 2] = some [2, 0, 2, 0, 0, 2, 2] :=
  specInv_mirror_7 [1, 2, 1, 2, 0, 0, 2] [2, 2, 1, 0, 1, 0, 0] [0, 0, 1, 1, 0, 0, 0] [1, 0, 1, 0, 0, 1, 1] [2, 0, 2, 0, 0, 2, 2] demoR1_1212002 demoR2_1212002 demoC_1212002 demoM_1212002 demoMir_1212002

theorem demoR1_2212002 : invRung 7 5 20 [2, 2, 1, 2, 0, 0, 2] [2, 2, 1, 2, 0, 0, 2] 1 2 false = ([2, 1, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_2212002 : invRung 7 5 20 [2, 2, 1, 2, 0, 0, 2] [2, 1, 0, 0, 1, 0, 2] 3 1 true = ([2, 0, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_2212002 : fieldCube 7 5 20 [2, 0, 2, 0, 2, 1, 2] = [0, 2, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_2212002 : fieldMul 7 5 20 [0, 2, 2, 1, 0, 2, 2] [2, 2, 1, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212002 : mirrorTrits [0, 2, 2, 1, 0, 2, 2] = [0, 1, 1, 2, 0, 1, 1] := by
  decide

theorem demoInv_2212002 : specInv 7 5 20 [2, 2, 1, 2, 0, 0, 2] = some [0, 1, 1, 2, 0, 1, 1] :=
  specInv_mirror_7 [2, 2, 1, 2, 0, 0, 2] [2, 1, 0, 0, 1, 0, 2] [2, 0, 2, 0, 2, 1, 2] [0, 2, 2, 1, 0, 2, 2] [0, 1, 1, 2, 0, 1, 1] demoR1_2212002 demoR2_2212002 demoC_2212002 demoM_2212002 demoMir_2212002

theorem demoR1_0022002 : invRung 7 5 20 [0, 0, 2, 2, 0, 0, 2] [0, 0, 2, 2, 0, 0, 2] 1 2 false = ([1, 2, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_0022002 : invRung 7 5 20 [0, 0, 2, 2, 0, 0, 2] [1, 2, 1, 1, 1, 0, 0] 3 1 true = ([1, 2, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0022002 : fieldCube 7 5 20 [1, 2, 0, 0, 1, 0, 1] = [1, 2, 2, 1, 1, 2, 2] := by
  decide

theorem demoM_0022002 : fieldMul 7 5 20 [1, 2, 2, 1, 1, 2, 2] [0, 0, 2, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022002 : mirrorTrits [1, 2, 2, 1, 1, 2, 2] = [2, 1, 1, 2, 2, 1, 1] := by
  decide

theorem demoInv_0022002 : specInv 7 5 20 [0, 0, 2, 2, 0, 0, 2] = some [2, 1, 1, 2, 2, 1, 1] :=
  specInv_mirror_7 [0, 0, 2, 2, 0, 0, 2] [1, 2, 1, 1, 1, 0, 0] [1, 2, 0, 0, 1, 0, 1] [1, 2, 2, 1, 1, 2, 2] [2, 1, 1, 2, 2, 1, 1] demoR1_0022002 demoR2_0022002 demoC_0022002 demoM_0022002 demoMir_0022002

theorem demoR1_1022002 : invRung 7 5 20 [1, 0, 2, 2, 0, 0, 2] [1, 0, 2, 2, 0, 0, 2] 1 2 false = ([1, 2, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_1022002 : invRung 7 5 20 [1, 0, 2, 2, 0, 0, 2] [1, 2, 0, 1, 0, 0, 2] 3 1 true = ([2, 0, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_1022002 : fieldCube 7 5 20 [2, 0, 2, 2, 2, 2, 0] = [0, 1, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_1022002 : fieldMul 7 5 20 [0, 1, 1, 2, 2, 0, 2] [1, 0, 2, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1022002 : mirrorTrits [0, 1, 1, 2, 2, 0, 2] = [0, 2, 2, 1, 1, 0, 1] := by
  decide

theorem demoInv_1022002 : specInv 7 5 20 [1, 0, 2, 2, 0, 0, 2] = some [0, 2, 2, 1, 1, 0, 1] :=
  specInv_mirror_7 [1, 0, 2, 2, 0, 0, 2] [1, 2, 0, 1, 0, 0, 2] [2, 0, 2, 2, 2, 2, 0] [0, 1, 1, 2, 2, 0, 2] [0, 2, 2, 1, 1, 0, 1] demoR1_1022002 demoR2_1022002 demoC_1022002 demoM_1022002 demoMir_1022002

theorem demoR1_2022002 : invRung 7 5 20 [2, 0, 2, 2, 0, 0, 2] [2, 0, 2, 2, 0, 0, 2] 1 2 false = ([0, 2, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2022002 : invRung 7 5 20 [2, 0, 2, 2, 0, 0, 2] [0, 2, 1, 1, 1, 2, 2] 3 1 true = ([1, 1, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2022002 : fieldCube 7 5 20 [1, 1, 1, 1, 0, 2, 1] = [1, 0, 2, 2, 0, 1, 0] := by
  decide

theorem demoM_2022002 : fieldMul 7 5 20 [1, 0, 2, 2, 0, 1, 0] [2, 0, 2, 2, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2022002 : specInv 7 5 20 [2, 0, 2, 2, 0, 0, 2] = some [1, 0, 2, 2, 0, 1, 0] :=
  specInv_white_7 [2, 0, 2, 2, 0, 0, 2] [0, 2, 1, 1, 1, 2, 2] [1, 1, 1, 1, 0, 2, 1] [1, 0, 2, 2, 0, 1, 0] demoR1_2022002 demoR2_2022002 demoC_2022002 demoM_2022002

theorem demoR1_0122002 : invRung 7 5 20 [0, 1, 2, 2, 0, 0, 2] [0, 1, 2, 2, 0, 0, 2] 1 2 false = ([2, 2, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_0122002 : invRung 7 5 20 [0, 1, 2, 2, 0, 0, 2] [2, 2, 2, 0, 2, 0, 0] 3 1 true = ([1, 0, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_0122002 : fieldCube 7 5 20 [1, 0, 1, 2, 2, 2, 1] = [2, 2, 0, 0, 0, 1, 2] := by
  decide

theorem demoM_0122002 : fieldMul 7 5 20 [2, 2, 0, 0, 0, 1, 2] [0, 1, 2, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122002 : mirrorTrits [2, 2, 0, 0, 0, 1, 2] = [1, 1, 0, 0, 0, 2, 1] := by
  decide

theorem demoInv_0122002 : specInv 7 5 20 [0, 1, 2, 2, 0, 0, 2] = some [1, 1, 0, 0, 0, 2, 1] :=
  specInv_mirror_7 [0, 1, 2, 2, 0, 0, 2] [2, 2, 2, 0, 2, 0, 0] [1, 0, 1, 2, 2, 2, 1] [2, 2, 0, 0, 0, 1, 2] [1, 1, 0, 0, 0, 2, 1] demoR1_0122002 demoR2_0122002 demoC_0122002 demoM_0122002 demoMir_0122002

theorem demoR1_1122002 : invRung 7 5 20 [1, 1, 2, 2, 0, 0, 2] [1, 1, 2, 2, 0, 0, 2] 1 2 false = ([1, 1, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1122002 : invRung 7 5 20 [1, 1, 2, 2, 0, 0, 2] [1, 1, 0, 2, 2, 1, 0] 3 1 true = ([2, 1, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_1122002 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 2, 0] = [2, 0, 0, 2, 2, 1, 1] := by
  decide

theorem demoM_1122002 : fieldMul 7 5 20 [2, 0, 0, 2, 2, 1, 1] [1, 1, 2, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122002 : mirrorTrits [2, 0, 0, 2, 2, 1, 1] = [1, 0, 0, 1, 1, 2, 2] := by
  decide

theorem demoInv_1122002 : specInv 7 5 20 [1, 1, 2, 2, 0, 0, 2] = some [1, 0, 0, 1, 1, 2, 2] :=
  specInv_mirror_7 [1, 1, 2, 2, 0, 0, 2] [1, 1, 0, 2, 2, 1, 0] [2, 1, 2, 1, 1, 2, 0] [2, 0, 0, 2, 2, 1, 1] [1, 0, 0, 1, 1, 2, 2] demoR1_1122002 demoR2_1122002 demoC_1122002 demoM_1122002 demoMir_1122002

theorem demoR1_2122002 : invRung 7 5 20 [2, 1, 2, 2, 0, 0, 2] [2, 1, 2, 2, 0, 0, 2] 1 2 false = ([1, 2, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_2122002 : invRung 7 5 20 [2, 1, 2, 2, 0, 0, 2] [1, 2, 2, 0, 1, 0, 1] 3 1 true = ([2, 2, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_2122002 : fieldCube 7 5 20 [2, 2, 0, 0, 0, 2, 0] = [1, 2, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_2122002 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 2, 1] [2, 1, 2, 2, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2122002 : specInv 7 5 20 [2, 1, 2, 2, 0, 0, 2] = some [1, 2, 2, 2, 2, 2, 1] :=
  specInv_white_7 [2, 1, 2, 2, 0, 0, 2] [1, 2, 2, 0, 1, 0, 1] [2, 2, 0, 0, 0, 2, 0] [1, 2, 2, 2, 2, 2, 1] demoR1_2122002 demoR2_2122002 demoC_2122002 demoM_2122002

theorem demoR1_0222002 : invRung 7 5 20 [0, 2, 2, 2, 0, 0, 2] [0, 2, 2, 2, 0, 0, 2] 1 2 false = ([0, 1, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0222002 : invRung 7 5 20 [0, 2, 2, 2, 0, 0, 2] [0, 1, 0, 0, 1, 1, 1] 3 1 true = ([2, 0, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0222002 : fieldCube 7 5 20 [2, 0, 1, 1, 0, 1, 2] = [1, 0, 0, 2, 0, 1, 2] := by
  decide

theorem demoM_0222002 : fieldMul 7 5 20 [1, 0, 0, 2, 0, 1, 2] [0, 2, 2, 2, 0, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0222002 : specInv 7 5 20 [0, 2, 2, 2, 0, 0, 2] = some [1, 0, 0, 2, 0, 1, 2] :=
  specInv_white_7 [0, 2, 2, 2, 0, 0, 2] [0, 1, 0, 0, 1, 1, 1] [2, 0, 1, 1, 0, 1, 2] [1, 0, 0, 2, 0, 1, 2] demoR1_0222002 demoR2_0222002 demoC_0222002 demoM_0222002

theorem demoR1_1222002 : invRung 7 5 20 [1, 2, 2, 2, 0, 0, 2] [1, 2, 2, 2, 0, 0, 2] 1 2 false = ([1, 0, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_1222002 : invRung 7 5 20 [1, 2, 2, 2, 0, 0, 2] [1, 0, 0, 2, 1, 2, 0] 3 1 true = ([2, 0, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_1222002 : fieldCube 7 5 20 [2, 0, 2, 1, 2, 0, 1] = [0, 0, 0, 0, 1, 1, 2] := by
  decide

theorem demoM_1222002 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 1, 2] [1, 2, 2, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222002 : mirrorTrits [0, 0, 0, 0, 1, 1, 2] = [0, 0, 0, 0, 2, 2, 1] := by
  decide

theorem demoInv_1222002 : specInv 7 5 20 [1, 2, 2, 2, 0, 0, 2] = some [0, 0, 0, 0, 2, 2, 1] :=
  specInv_mirror_7 [1, 2, 2, 2, 0, 0, 2] [1, 0, 0, 2, 1, 2, 0] [2, 0, 2, 1, 2, 0, 1] [0, 0, 0, 0, 1, 1, 2] [0, 0, 0, 0, 2, 2, 1] demoR1_1222002 demoR2_1222002 demoC_1222002 demoM_1222002 demoMir_1222002

theorem demoR1_2222002 : invRung 7 5 20 [2, 2, 2, 2, 0, 0, 2] [2, 2, 2, 2, 0, 0, 2] 1 2 false = ([2, 0, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_2222002 : invRung 7 5 20 [2, 2, 2, 2, 0, 0, 2] [2, 0, 0, 2, 0, 0, 0] 3 1 true = ([0, 1, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_2222002 : fieldCube 7 5 20 [0, 1, 2, 0, 0, 2, 2] = [2, 1, 0, 0, 1, 1, 2] := by
  decide

theorem demoM_2222002 : fieldMul 7 5 20 [2, 1, 0, 0, 1, 1, 2] [2, 2, 2, 2, 0, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222002 : mirrorTrits [2, 1, 0, 0, 1, 1, 2] = [1, 2, 0, 0, 2, 2, 1] := by
  decide

theorem demoInv_2222002 : specInv 7 5 20 [2, 2, 2, 2, 0, 0, 2] = some [1, 2, 0, 0, 2, 2, 1] :=
  specInv_mirror_7 [2, 2, 2, 2, 0, 0, 2] [2, 0, 0, 2, 0, 0, 0] [0, 1, 2, 0, 0, 2, 2] [2, 1, 0, 0, 1, 1, 2] [1, 2, 0, 0, 2, 2, 1] demoR1_2222002 demoR2_2222002 demoC_2222002 demoM_2222002 demoMir_2222002

theorem demoR1_0000102 : invRung 7 5 20 [0, 0, 0, 0, 1, 0, 2] [0, 0, 0, 0, 1, 0, 2] 1 2 false = ([0, 2, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_0000102 : invRung 7 5 20 [0, 0, 0, 0, 1, 0, 2] [0, 2, 1, 0, 0, 0, 2] 3 1 true = ([2, 1, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0000102 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 2, 1] = [0, 1, 0, 0, 0, 0, 0] := by
  decide

theorem demoM_0000102 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 0, 0] [0, 0, 0, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000102 : mirrorTrits [0, 1, 0, 0, 0, 0, 0] = [0, 2, 0, 0, 0, 0, 0] := by
  decide

theorem demoInv_0000102 : specInv 7 5 20 [0, 0, 0, 0, 1, 0, 2] = some [0, 2, 0, 0, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 0, 0, 1, 0, 2] [0, 2, 1, 0, 0, 0, 2] [2, 1, 0, 2, 1, 2, 1] [0, 1, 0, 0, 0, 0, 0] [0, 2, 0, 0, 0, 0, 0] demoR1_0000102 demoR2_0000102 demoC_0000102 demoM_0000102 demoMir_0000102

theorem demoR1_1000102 : invRung 7 5 20 [1, 0, 0, 0, 1, 0, 2] [1, 0, 0, 0, 1, 0, 2] 1 2 false = ([0, 0, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_1000102 : invRung 7 5 20 [1, 0, 0, 0, 1, 0, 2] [0, 0, 1, 2, 1, 0, 1] 3 1 true = ([2, 1, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_1000102 : fieldCube 7 5 20 [2, 1, 0, 1, 0, 1, 2] = [1, 0, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_1000102 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 1, 1] [1, 0, 0, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1000102 : specInv 7 5 20 [1, 0, 0, 0, 1, 0, 2] = some [1, 0, 0, 0, 0, 1, 1] :=
  specInv_white_7 [1, 0, 0, 0, 1, 0, 2] [0, 0, 1, 2, 1, 0, 1] [2, 1, 0, 1, 0, 1, 2] [1, 0, 0, 0, 0, 1, 1] demoR1_1000102 demoR2_1000102 demoC_1000102 demoM_1000102

theorem demoR1_2000102 : invRung 7 5 20 [2, 0, 0, 0, 1, 0, 2] [2, 0, 0, 0, 1, 0, 2] 1 2 false = ([0, 2, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_2000102 : invRung 7 5 20 [2, 0, 0, 0, 1, 0, 2] [0, 2, 0, 2, 2, 1, 1] 3 1 true = ([2, 1, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_2000102 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 1, 2] = [1, 0, 0, 0, 0, 1, 2] := by
  decide

theorem demoM_2000102 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 1, 2] [2, 0, 0, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000102 : mirrorTrits [1, 0, 0, 0, 0, 1, 2] = [2, 0, 0, 0, 0, 2, 1] := by
  decide

theorem demoInv_2000102 : specInv 7 5 20 [2, 0, 0, 0, 1, 0, 2] = some [2, 0, 0, 0, 0, 2, 1] :=
  specInv_mirror_7 [2, 0, 0, 0, 1, 0, 2] [0, 2, 0, 2, 2, 1, 1] [2, 1, 1, 1, 0, 1, 2] [1, 0, 0, 0, 0, 1, 2] [2, 0, 0, 0, 0, 2, 1] demoR1_2000102 demoR2_2000102 demoC_2000102 demoM_2000102 demoMir_2000102

theorem demoR1_0100102 : invRung 7 5 20 [0, 1, 0, 0, 1, 0, 2] [0, 1, 0, 0, 1, 0, 2] 1 2 false = ([1, 0, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0100102 : invRung 7 5 20 [0, 1, 0, 0, 1, 0, 2] [1, 0, 0, 2, 2, 2, 1] 3 1 true = ([0, 0, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_0100102 : fieldCube 7 5 20 [0, 0, 1, 0, 0, 0, 0] = [0, 0, 0, 0, 0, 0, 1] := by
  decide

theorem demoM_0100102 : fieldMul 7 5 20 [0, 0, 0, 0, 0, 0, 1] [0, 1, 0, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0100102 : specInv 7 5 20 [0, 1, 0, 0, 1, 0, 2] = some [0, 0, 0, 0, 0, 0, 1] :=
  specInv_white_7 [0, 1, 0, 0, 1, 0, 2] [1, 0, 0, 2, 2, 2, 1] [0, 0, 1, 0, 0, 0, 0] [0, 0, 0, 0, 0, 0, 1] demoR1_0100102 demoR2_0100102 demoC_0100102 demoM_0100102

theorem demoR1_1100102 : invRung 7 5 20 [1, 1, 0, 0, 1, 0, 2] [1, 1, 0, 0, 1, 0, 2] 1 2 false = ([2, 2, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_1100102 : invRung 7 5 20 [1, 1, 0, 0, 1, 0, 2] [2, 2, 2, 2, 2, 0, 0] 3 1 true = ([1, 1, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_1100102 : fieldCube 7 5 20 [1, 1, 1, 2, 2, 2, 2] = [2, 0, 2, 2, 1, 2, 0] := by
  decide

theorem demoM_1100102 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 2, 0] [1, 1, 0, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1100102 : mirrorTrits [2, 0, 2, 2, 1, 2, 0] = [1, 0, 1, 1, 2, 1, 0] := by
  decide

theorem demoInv_1100102 : specInv 7 5 20 [1, 1, 0, 0, 1, 0, 2] = some [1, 0, 1, 1, 2, 1, 0] :=
  specInv_mirror_7 [1, 1, 0, 0, 1, 0, 2] [2, 2, 2, 2, 2, 0, 0] [1, 1, 1, 2, 2, 2, 2] [2, 0, 2, 2, 1, 2, 0] [1, 0, 1, 1, 2, 1, 0] demoR1_1100102 demoR2_1100102 demoC_1100102 demoM_1100102 demoMir_1100102

theorem demoR1_2100102 : invRung 7 5 20 [2, 1, 0, 0, 1, 0, 2] [2, 1, 0, 0, 1, 0, 2] 1 2 false = ([2, 1, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_2100102 : invRung 7 5 20 [2, 1, 0, 0, 1, 0, 2] [2, 1, 2, 2, 2, 1, 0] 3 1 true = ([1, 0, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2100102 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 1, 0] = [2, 1, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_2100102 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 1, 2] [2, 1, 0, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100102 : mirrorTrits [2, 1, 1, 0, 1, 1, 2] = [1, 2, 2, 0, 2, 2, 1] := by
  decide

theorem demoInv_2100102 : specInv 7 5 20 [2, 1, 0, 0, 1, 0, 2] = some [1, 2, 2, 0, 2, 2, 1] :=
  specInv_mirror_7 [2, 1, 0, 0, 1, 0, 2] [2, 1, 2, 2, 2, 1, 0] [1, 0, 0, 0, 0, 1, 0] [2, 1, 1, 0, 1, 1, 2] [1, 2, 2, 0, 2, 2, 1] demoR1_2100102 demoR2_2100102 demoC_2100102 demoM_2100102 demoMir_2100102

theorem demoR1_0200102 : invRung 7 5 20 [0, 2, 0, 0, 1, 0, 2] [0, 2, 0, 0, 1, 0, 2] 1 2 false = ([0, 1, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_0200102 : invRung 7 5 20 [0, 2, 0, 0, 1, 0, 2] [0, 1, 1, 1, 2, 0, 0] 3 1 true = ([2, 2, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0200102 : fieldCube 7 5 20 [2, 2, 2, 1, 0, 1, 0] = [1, 1, 2, 2, 1, 2, 1] := by
  decide

theorem demoM_0200102 : fieldMul 7 5 20 [1, 1, 2, 2, 1, 2, 1] [0, 2, 0, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0200102 : specInv 7 5 20 [0, 2, 0, 0, 1, 0, 2] = some [1, 1, 2, 2, 1, 2, 1] :=
  specInv_white_7 [0, 2, 0, 0, 1, 0, 2] [0, 1, 1, 1, 2, 0, 0] [2, 2, 2, 1, 0, 1, 0] [1, 1, 2, 2, 1, 2, 1] demoR1_0200102 demoR2_0200102 demoC_0200102 demoM_0200102

theorem demoR1_1200102 : invRung 7 5 20 [1, 2, 0, 0, 1, 0, 2] [1, 2, 0, 0, 1, 0, 2] 1 2 false = ([2, 2, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_1200102 : invRung 7 5 20 [1, 2, 0, 0, 1, 0, 2] [2, 2, 2, 0, 0, 1, 0] 3 1 true = ([2, 1, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_1200102 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 1, 1] = [2, 1, 2, 1, 2, 0, 2] := by
  decide

theorem demoM_1200102 : fieldMul 7 5 20 [2, 1, 2, 1, 2, 0, 2] [1, 2, 0, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200102 : mirrorTrits [2, 1, 2, 1, 2, 0, 2] = [1, 2, 1, 2, 1, 0, 1] := by
  decide

theorem demoInv_1200102 : specInv 7 5 20 [1, 2, 0, 0, 1, 0, 2] = some [1, 2, 1, 2, 1, 0, 1] :=
  specInv_mirror_7 [1, 2, 0, 0, 1, 0, 2] [2, 2, 2, 0, 0, 1, 0] [2, 1, 0, 2, 2, 1, 1] [2, 1, 2, 1, 2, 0, 2] [1, 2, 1, 2, 1, 0, 1] demoR1_1200102 demoR2_1200102 demoC_1200102 demoM_1200102 demoMir_1200102

theorem demoR1_2200102 : invRung 7 5 20 [2, 2, 0, 0, 1, 0, 2] [2, 2, 0, 0, 1, 0, 2] 1 2 false = ([2, 2, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_2200102 : invRung 7 5 20 [2, 2, 0, 0, 1, 0, 2] [2, 2, 0, 1, 1, 1, 1] 3 1 true = ([2, 1, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_2200102 : fieldCube 7 5 20 [2, 1, 0, 2, 0, 1, 1] = [2, 2, 2, 2, 2, 1, 0] := by
  decide

theorem demoM_2200102 : fieldMul 7 5 20 [2, 2, 2, 2, 2, 1, 0] [2, 2, 0, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200102 : mirrorTrits [2, 2, 2, 2, 2, 1, 0] = [1, 1, 1, 1, 1, 2, 0] := by
  decide

theorem demoInv_2200102 : specInv 7 5 20 [2, 2, 0, 0, 1, 0, 2] = some [1, 1, 1, 1, 1, 2, 0] :=
  specInv_mirror_7 [2, 2, 0, 0, 1, 0, 2] [2, 2, 0, 1, 1, 1, 1] [2, 1, 0, 2, 0, 1, 1] [2, 2, 2, 2, 2, 1, 0] [1, 1, 1, 1, 1, 2, 0] demoR1_2200102 demoR2_2200102 demoC_2200102 demoM_2200102 demoMir_2200102

theorem demoR1_0010102 : invRung 7 5 20 [0, 0, 1, 0, 1, 0, 2] [0, 0, 1, 0, 1, 0, 2] 1 2 false = ([1, 2, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_0010102 : invRung 7 5 20 [0, 0, 1, 0, 1, 0, 2] [1, 2, 2, 1, 2, 0, 1] 3 1 true = ([1, 0, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0010102 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 1, 0] = [0, 1, 2, 0, 1, 2, 2] := by
  decide

theorem demoM_0010102 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 2, 2] [0, 0, 1, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0010102 : specInv 7 5 20 [0, 0, 1, 0, 1, 0, 2] = some [0, 1, 2, 0, 1, 2, 2] :=
  specInv_white_7 [0, 0, 1, 0, 1, 0, 2] [1, 2, 2, 1, 2, 0, 1] [1, 0, 0, 1, 0, 1, 0] [0, 1, 2, 0, 1, 2, 2] demoR1_0010102 demoR2_0010102 demoC_0010102 demoM_0010102

theorem demoR1_1010102 : invRung 7 5 20 [1, 0, 1, 0, 1, 0, 2] [1, 0, 1, 0, 1, 0, 2] 1 2 false = ([2, 1, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_1010102 : invRung 7 5 20 [1, 0, 1, 0, 1, 0, 2] [2, 1, 0, 2, 2, 2, 0] 3 1 true = ([2, 0, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_1010102 : fieldCube 7 5 20 [2, 0, 0, 1, 1, 1, 1] = [1, 0, 1, 2, 2, 1, 1] := by
  decide

theorem demoM_1010102 : fieldMul 7 5 20 [1, 0, 1, 2, 2, 1, 1] [1, 0, 1, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1010102 : mirrorTrits [1, 0, 1, 2, 2, 1, 1] = [2, 0, 2, 1, 1, 2, 2] := by
  decide

theorem demoInv_1010102 : specInv 7 5 20 [1, 0, 1, 0, 1, 0, 2] = some [2, 0, 2, 1, 1, 2, 2] :=
  specInv_mirror_7 [1, 0, 1, 0, 1, 0, 2] [2, 1, 0, 2, 2, 2, 0] [2, 0, 0, 1, 1, 1, 1] [1, 0, 1, 2, 2, 1, 1] [2, 0, 2, 1, 1, 2, 2] demoR1_1010102 demoR2_1010102 demoC_1010102 demoM_1010102 demoMir_1010102

theorem demoR1_2010102 : invRung 7 5 20 [2, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 1, 0, 2] 1 2 false = ([0, 0, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_2010102 : invRung 7 5 20 [2, 0, 1, 0, 1, 0, 2] [0, 0, 0, 0, 1, 1, 1] 3 1 true = ([0, 1, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_2010102 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 2, 2] = [1, 0, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_2010102 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 2, 2] [2, 0, 1, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2010102 : specInv 7 5 20 [2, 0, 1, 0, 1, 0, 2] = some [1, 0, 2, 2, 1, 2, 2] :=
  specInv_white_7 [2, 0, 1, 0, 1, 0, 2] [0, 0, 0, 0, 1, 1, 1] [0, 1, 0, 2, 2, 2, 2] [1, 0, 2, 2, 1, 2, 2] demoR1_2010102 demoR2_2010102 demoC_2010102 demoM_2010102

theorem demoR1_0110102 : invRung 7 5 20 [0, 1, 1, 0, 1, 0, 2] [0, 1, 1, 0, 1, 0, 2] 1 2 false = ([0, 2, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_0110102 : invRung 7 5 20 [0, 1, 1, 0, 1, 0, 2] [0, 2, 0, 1, 0, 0, 2] 3 1 true = ([0, 0, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0110102 : fieldCube 7 5 20 [0, 0, 0, 1, 0, 1, 2] = [2, 0, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_0110102 : fieldMul 7 5 20 [2, 0, 0, 2, 0, 1, 1] [0, 1, 1, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110102 : mirrorTrits [2, 0, 0, 2, 0, 1, 1] = [1, 0, 0, 1, 0, 2, 2] := by
  decide

theorem demoInv_0110102 : specInv 7 5 20 [0, 1, 1, 0, 1, 0, 2] = some [1, 0, 0, 1, 0, 2, 2] :=
  specInv_mirror_7 [0, 1, 1, 0, 1, 0, 2] [0, 2, 0, 1, 0, 0, 2] [0, 0, 0, 1, 0, 1, 2] [2, 0, 0, 2, 0, 1, 1] [1, 0, 0, 1, 0, 2, 2] demoR1_0110102 demoR2_0110102 demoC_0110102 demoM_0110102 demoMir_0110102

theorem demoR1_1110102 : invRung 7 5 20 [1, 1, 1, 0, 1, 0, 2] [1, 1, 1, 0, 1, 0, 2] 1 2 false = ([2, 1, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_1110102 : invRung 7 5 20 [1, 1, 1, 0, 1, 0, 2] [2, 1, 1, 2, 0, 1, 0] 3 1 true = ([1, 0, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_1110102 : fieldCube 7 5 20 [1, 0, 1, 2, 2, 0, 2] = [0, 1, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_1110102 : fieldMul 7 5 20 [0, 1, 0, 1, 2, 0, 2] [1, 1, 1, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1110102 : specInv 7 5 20 [1, 1, 1, 0, 1, 0, 2] = some [0, 1, 0, 1, 2, 0, 2] :=
  specInv_white_7 [1, 1, 1, 0, 1, 0, 2] [2, 1, 1, 2, 0, 1, 0] [1, 0, 1, 2, 2, 0, 2] [0, 1, 0, 1, 2, 0, 2] demoR1_1110102 demoR2_1110102 demoC_1110102 demoM_1110102

theorem demoR1_2110102 : invRung 7 5 20 [2, 1, 1, 0, 1, 0, 2] [2, 1, 1, 0, 1, 0, 2] 1 2 false = ([0, 2, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_2110102 : invRung 7 5 20 [2, 1, 1, 0, 1, 0, 2] [0, 2, 0, 2, 2, 1, 0] 3 1 true = ([2, 1, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_2110102 : fieldCube 7 5 20 [2, 1, 2, 2, 2, 1, 1] = [2, 1, 2, 1, 2, 0, 1] := by
  decide

theorem demoM_2110102 : fieldMul 7 5 20 [2, 1, 2, 1, 2, 0, 1] [2, 1, 1, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2110102 : specInv 7 5 20 [2, 1, 1, 0, 1, 0, 2] = some [2, 1, 2, 1, 2, 0, 1] :=
  specInv_white_7 [2, 1, 1, 0, 1, 0, 2] [0, 2, 0, 2, 2, 1, 0] [2, 1, 2, 2, 2, 1, 1] [2, 1, 2, 1, 2, 0, 1] demoR1_2110102 demoR2_2110102 demoC_2110102 demoM_2110102

theorem demoR1_0210102 : invRung 7 5 20 [0, 2, 1, 0, 1, 0, 2] [0, 2, 1, 0, 1, 0, 2] 1 2 false = ([1, 1, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_0210102 : invRung 7 5 20 [0, 2, 1, 0, 1, 0, 2] [1, 1, 1, 1, 2, 0, 0] 3 1 true = ([0, 1, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0210102 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 1, 1] = [1, 2, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_0210102 : fieldMul 7 5 20 [1, 2, 0, 2, 2, 2, 1] [0, 2, 1, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210102 : mirrorTrits [1, 2, 0, 2, 2, 2, 1] = [2, 1, 0, 1, 1, 1, 2] := by
  decide

theorem demoInv_0210102 : specInv 7 5 20 [0, 2, 1, 0, 1, 0, 2] = some [2, 1, 0, 1, 1, 1, 2] :=
  specInv_mirror_7 [0, 2, 1, 0, 1, 0, 2] [1, 1, 1, 1, 2, 0, 0] [0, 1, 1, 0, 0, 1, 1] [1, 2, 0, 2, 2, 2, 1] [2, 1, 0, 1, 1, 1, 2] demoR1_0210102 demoR2_0210102 demoC_0210102 demoM_0210102 demoMir_0210102

theorem demoR1_1210102 : invRung 7 5 20 [1, 2, 1, 0, 1, 0, 2] [1, 2, 1, 0, 1, 0, 2] 1 2 false = ([1, 1, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_1210102 : invRung 7 5 20 [1, 2, 1, 0, 1, 0, 2] [1, 1, 2, 0, 1, 2, 1] 3 1 true = ([0, 2, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_1210102 : fieldCube 7 5 20 [0, 2, 2, 0, 2, 0, 0] = [0, 2, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_1210102 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 2, 1] [1, 2, 1, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1210102 : mirrorTrits [0, 2, 0, 1, 0, 2, 1] = [0, 1, 0, 2, 0, 1, 2] := by
  decide

theorem demoInv_1210102 : specInv 7 5 20 [1, 2, 1, 0, 1, 0, 2] = some [0, 1, 0, 2, 0, 1, 2] :=
  specInv_mirror_7 [1, 2, 1, 0, 1, 0, 2] [1, 1, 2, 0, 1, 2, 1] [0, 2, 2, 0, 2, 0, 0] [0, 2, 0, 1, 0, 2, 1] [0, 1, 0, 2, 0, 1, 2] demoR1_1210102 demoR2_1210102 demoC_1210102 demoM_1210102 demoMir_1210102

theorem demoR1_2210102 : invRung 7 5 20 [2, 2, 1, 0, 1, 0, 2] [2, 2, 1, 0, 1, 0, 2] 1 2 false = ([2, 2, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_2210102 : invRung 7 5 20 [2, 2, 1, 0, 1, 0, 2] [2, 2, 0, 0, 2, 2, 1] 3 1 true = ([1, 0, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_2210102 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 2, 0] = [1, 0, 0, 1, 2, 1, 1] := by
  decide

theorem demoM_2210102 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 1, 1] [2, 2, 1, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210102 : mirrorTrits [1, 0, 0, 1, 2, 1, 1] = [2, 0, 0, 2, 1, 2, 2] := by
  decide

theorem demoInv_2210102 : specInv 7 5 20 [2, 2, 1, 0, 1, 0, 2] = some [2, 0, 0, 2, 1, 2, 2] :=
  specInv_mirror_7 [2, 2, 1, 0, 1, 0, 2] [2, 2, 0, 0, 2, 2, 1] [1, 0, 2, 1, 1, 2, 0] [1, 0, 0, 1, 2, 1, 1] [2, 0, 0, 2, 1, 2, 2] demoR1_2210102 demoR2_2210102 demoC_2210102 demoM_2210102 demoMir_2210102

theorem demoR1_0020102 : invRung 7 5 20 [0, 0, 2, 0, 1, 0, 2] [0, 0, 2, 0, 1, 0, 2] 1 2 false = ([1, 0, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_0020102 : invRung 7 5 20 [0, 0, 2, 0, 1, 0, 2] [1, 0, 0, 1, 2, 2, 1] 3 1 true = ([0, 1, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0020102 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 2, 2] = [2, 2, 0, 1, 1, 2, 0] := by
  decide

theorem demoM_0020102 : fieldMul 7 5 20 [2, 2, 0, 1, 1, 2, 0] [0, 0, 2, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020102 : mirrorTrits [2, 2, 0, 1, 1, 2, 0] = [1, 1, 0, 2, 2, 1, 0] := by
  decide

theorem demoInv_0020102 : specInv 7 5 20 [0, 0, 2, 0, 1, 0, 2] = some [1, 1, 0, 2, 2, 1, 0] :=
  specInv_mirror_7 [0, 0, 2, 0, 1, 0, 2] [1, 0, 0, 1, 2, 2, 1] [0, 1, 2, 0, 1, 2, 2] [2, 2, 0, 1, 1, 2, 0] [1, 1, 0, 2, 2, 1, 0] demoR1_0020102 demoR2_0020102 demoC_0020102 demoM_0020102 demoMir_0020102

theorem demoR1_1020102 : invRung 7 5 20 [1, 0, 2, 0, 1, 0, 2] [1, 0, 2, 0, 1, 0, 2] 1 2 false = ([2, 0, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1020102 : invRung 7 5 20 [1, 0, 2, 0, 1, 0, 2] [2, 0, 0, 1, 1, 0, 2] 3 1 true = ([1, 0, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1020102 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 2, 2] = [2, 2, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_1020102 : fieldMul 7 5 20 [2, 2, 2, 0, 1, 1, 0] [1, 0, 2, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020102 : mirrorTrits [2, 2, 2, 0, 1, 1, 0] = [1, 1, 1, 0, 2, 2, 0] := by
  decide

theorem demoInv_1020102 : specInv 7 5 20 [1, 0, 2, 0, 1, 0, 2] = some [1, 1, 1, 0, 2, 2, 0] :=
  specInv_mirror_7 [1, 0, 2, 0, 1, 0, 2] [2, 0, 0, 1, 1, 0, 2] [1, 0, 2, 2, 1, 2, 2] [2, 2, 2, 0, 1, 1, 0] [1, 1, 1, 0, 2, 2, 0] demoR1_1020102 demoR2_1020102 demoC_1020102 demoM_1020102 demoMir_1020102

theorem demoR1_2020102 : invRung 7 5 20 [2, 0, 2, 0, 1, 0, 2] [2, 0, 2, 0, 1, 0, 2] 1 2 false = ([0, 2, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_2020102 : invRung 7 5 20 [2, 0, 2, 0, 1, 0, 2] [0, 2, 2, 0, 1, 0, 0] 3 1 true = ([1, 0, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_2020102 : fieldCube 7 5 20 [1, 0, 1, 2, 2, 1, 1] = [1, 1, 2, 0, 2, 0, 0] := by
  decide

theorem demoM_2020102 : fieldMul 7 5 20 [1, 1, 2, 0, 2, 0, 0] [2, 0, 2, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2020102 : specInv 7 5 20 [2, 0, 2, 0, 1, 0, 2] = some [1, 1, 2, 0, 2, 0, 0] :=
  specInv_white_7 [2, 0, 2, 0, 1, 0, 2] [0, 2, 2, 0, 1, 0, 0] [1, 0, 1, 2, 2, 1, 1] [1, 1, 2, 0, 2, 0, 0] demoR1_2020102 demoR2_2020102 demoC_2020102 demoM_2020102

theorem demoR1_0120102 : invRung 7 5 20 [0, 1, 2, 0, 1, 0, 2] [0, 1, 2, 0, 1, 0, 2] 1 2 false = ([1, 1, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_0120102 : invRung 7 5 20 [0, 1, 2, 0, 1, 0, 2] [1, 1, 2, 1, 1, 2, 0] 3 1 true = ([2, 2, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_0120102 : fieldCube 7 5 20 [2, 2, 0, 2, 2, 0, 1] = [1, 0, 1, 2, 1, 2, 0] := by
  decide

theorem demoM_0120102 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 2, 0] [0, 1, 2, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0120102 : specInv 7 5 20 [0, 1, 2, 0, 1, 0, 2] = some [1, 0, 1, 2, 1, 2, 0] :=
  specInv_white_7 [0, 1, 2, 0, 1, 0, 2] [1, 1, 2, 1, 1, 2, 0] [2, 2, 0, 2, 2, 0, 1] [1, 0, 1, 2, 1, 2, 0] demoR1_0120102 demoR2_0120102 demoC_0120102 demoM_0120102

theorem demoR1_1120102 : invRung 7 5 20 [1, 1, 2, 0, 1, 0, 2] [1, 1, 2, 0, 1, 0, 2] 1 2 false = ([0, 0, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_1120102 : invRung 7 5 20 [1, 1, 2, 0, 1, 0, 2] [0, 0, 0, 0, 1, 0, 2] 3 1 true = ([1, 2, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_1120102 : fieldCube 7 5 20 [1, 2, 1, 1, 0, 2, 2] = [1, 1, 1, 1, 1, 2, 1] := by
  decide

theorem demoM_1120102 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 2, 1] [1, 1, 2, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120102 : mirrorTrits [1, 1, 1, 1, 1, 2, 1] = [2, 2, 2, 2, 2, 1, 2] := by
  decide

theorem demoInv_1120102 : specInv 7 5 20 [1, 1, 2, 0, 1, 0, 2] = some [2, 2, 2, 2, 2, 1, 2] :=
  specInv_mirror_7 [1, 1, 2, 0, 1, 0, 2] [0, 0, 0, 0, 1, 0, 2] [1, 2, 1, 1, 0, 2, 2] [1, 1, 1, 1, 1, 2, 1] [2, 2, 2, 2, 2, 1, 2] demoR1_1120102 demoR2_1120102 demoC_1120102 demoM_1120102 demoMir_1120102

theorem demoR1_2120102 : invRung 7 5 20 [2, 1, 2, 0, 1, 0, 2] [2, 1, 2, 0, 1, 0, 2] 1 2 false = ([1, 0, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_2120102 : invRung 7 5 20 [2, 1, 2, 0, 1, 0, 2] [1, 0, 2, 0, 2, 2, 1] 3 1 true = ([0, 2, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_2120102 : fieldCube 7 5 20 [0, 2, 0, 2, 0, 0, 0] = [2, 0, 2, 2, 0, 2, 0] := by
  decide

theorem demoM_2120102 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 2, 0] [2, 1, 2, 0, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120102 : mirrorTrits [2, 0, 2, 2, 0, 2, 0] = [1, 0, 1, 1, 0, 1, 0] := by
  decide

theorem demoInv_2120102 : specInv 7 5 20 [2, 1, 2, 0, 1, 0, 2] = some [1, 0, 1, 1, 0, 1, 0] :=
  specInv_mirror_7 [2, 1, 2, 0, 1, 0, 2] [1, 0, 2, 0, 2, 2, 1] [0, 2, 0, 2, 0, 0, 0] [2, 0, 2, 2, 0, 2, 0] [1, 0, 1, 1, 0, 1, 0] demoR1_2120102 demoR2_2120102 demoC_2120102 demoM_2120102 demoMir_2120102

theorem demoR1_0220102 : invRung 7 5 20 [0, 2, 2, 0, 1, 0, 2] [0, 2, 2, 0, 1, 0, 2] 1 2 false = ([1, 0, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_0220102 : invRung 7 5 20 [0, 2, 2, 0, 1, 0, 2] [1, 0, 2, 1, 1, 0, 2] 3 1 true = ([0, 0, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_0220102 : fieldCube 7 5 20 [0, 0, 2, 2, 2, 1, 2] = [0, 2, 1, 1, 0, 1, 2] := by
  decide

theorem demoM_0220102 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 1, 2] [0, 2, 2, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0220102 : specInv 7 5 20 [0, 2, 2, 0, 1, 0, 2] = some [0, 2, 1, 1, 0, 1, 2] :=
  specInv_white_7 [0, 2, 2, 0, 1, 0, 2] [1, 0, 2, 1, 1, 0, 2] [0, 0, 2, 2, 2, 1, 2] [0, 2, 1, 1, 0, 1, 2] demoR1_0220102 demoR2_0220102 demoC_0220102 demoM_0220102

theorem demoR1_1220102 : invRung 7 5 20 [1, 2, 2, 0, 1, 0, 2] [1, 2, 2, 0, 1, 0, 2] 1 2 false = ([1, 2, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1220102 : invRung 7 5 20 [1, 2, 2, 0, 1, 0, 2] [1, 2, 1, 0, 1, 0, 0] 3 1 true = ([2, 0, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_1220102 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 2, 0] = [1, 0, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_1220102 : fieldMul 7 5 20 [1, 0, 2, 1, 2, 0, 0] [1, 2, 2, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1220102 : specInv 7 5 20 [1, 2, 2, 0, 1, 0, 2] = some [1, 0, 2, 1, 2, 0, 0] :=
  specInv_white_7 [1, 2, 2, 0, 1, 0, 2] [1, 2, 1, 0, 1, 0, 0] [2, 0, 1, 0, 1, 2, 0] [1, 0, 2, 1, 2, 0, 0] demoR1_1220102 demoR2_1220102 demoC_1220102 demoM_1220102

theorem demoR1_2220102 : invRung 7 5 20 [2, 2, 2, 0, 1, 0, 2] [2, 2, 2, 0, 1, 0, 2] 1 2 false = ([2, 1, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2220102 : invRung 7 5 20 [2, 2, 2, 0, 1, 0, 2] [2, 1, 0, 2, 2, 0, 1] 3 1 true = ([2, 1, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2220102 : fieldCube 7 5 20 [2, 1, 2, 1, 2, 1, 0] = [1, 0, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_2220102 : fieldMul 7 5 20 [1, 0, 2, 0, 1, 1, 0] [2, 2, 2, 0, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2220102 : specInv 7 5 20 [2, 2, 2, 0, 1, 0, 2] = some [1, 0, 2, 0, 1, 1, 0] :=
  specInv_white_7 [2, 2, 2, 0, 1, 0, 2] [2, 1, 0, 2, 2, 0, 1] [2, 1, 2, 1, 2, 1, 0] [1, 0, 2, 0, 1, 1, 0] demoR1_2220102 demoR2_2220102 demoC_2220102 demoM_2220102

theorem demoR1_0001102 : invRung 7 5 20 [0, 0, 0, 1, 1, 0, 2] [0, 0, 0, 1, 1, 0, 2] 1 2 false = ([2, 0, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_0001102 : invRung 7 5 20 [0, 0, 0, 1, 1, 0, 2] [2, 0, 0, 1, 0, 1, 0] 3 1 true = ([2, 2, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0001102 : fieldCube 7 5 20 [2, 2, 0, 1, 0, 1, 0] = [1, 1, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_0001102 : fieldMul 7 5 20 [1, 1, 2, 2, 1, 2, 2] [0, 0, 0, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001102 : mirrorTrits [1, 1, 2, 2, 1, 2, 2] = [2, 2, 1, 1, 2, 1, 1] := by
  decide

theorem demoInv_0001102 : specInv 7 5 20 [0, 0, 0, 1, 1, 0, 2] = some [2, 2, 1, 1, 2, 1, 1] :=
  specInv_mirror_7 [0, 0, 0, 1, 1, 0, 2] [2, 0, 0, 1, 0, 1, 0] [2, 2, 0, 1, 0, 1, 0] [1, 1, 2, 2, 1, 2, 2] [2, 2, 1, 1, 2, 1, 1] demoR1_0001102 demoR2_0001102 demoC_0001102 demoM_0001102 demoMir_0001102

theorem demoR1_1001102 : invRung 7 5 20 [1, 0, 0, 1, 1, 0, 2] [1, 0, 0, 1, 1, 0, 2] 1 2 false = ([2, 2, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_1001102 : invRung 7 5 20 [1, 0, 0, 1, 1, 0, 2] [2, 2, 1, 0, 1, 2, 1] 3 1 true = ([1, 0, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_1001102 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 1, 0] = [0, 2, 2, 1, 1, 0, 2] := by
  decide

theorem demoM_1001102 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 0, 2] [1, 0, 0, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1001102 : specInv 7 5 20 [1, 0, 0, 1, 1, 0, 2] = some [0, 2, 2, 1, 1, 0, 2] :=
  specInv_white_7 [1, 0, 0, 1, 1, 0, 2] [2, 2, 1, 0, 1, 2, 1] [1, 0, 2, 1, 1, 1, 0] [0, 2, 2, 1, 1, 0, 2] demoR1_1001102 demoR2_1001102 demoC_1001102 demoM_1001102

theorem demoR1_2001102 : invRung 7 5 20 [2, 0, 0, 1, 1, 0, 2] [2, 0, 0, 1, 1, 0, 2] 1 2 false = ([2, 1, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_2001102 : invRung 7 5 20 [2, 0, 0, 1, 1, 0, 2] [2, 1, 2, 2, 1, 2, 0] 3 1 true = ([2, 1, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_2001102 : fieldCube 7 5 20 [2, 1, 0, 0, 0, 2, 2] = [1, 1, 0, 0, 1, 1, 0] := by
  decide

theorem demoM_2001102 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 1, 0] [2, 0, 0, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001102 : mirrorTrits [1, 1, 0, 0, 1, 1, 0] = [2, 2, 0, 0, 2, 2, 0] := by
  decide

theorem demoInv_2001102 : specInv 7 5 20 [2, 0, 0, 1, 1, 0, 2] = some [2, 2, 0, 0, 2, 2, 0] :=
  specInv_mirror_7 [2, 0, 0, 1, 1, 0, 2] [2, 1, 2, 2, 1, 2, 0] [2, 1, 0, 0, 0, 2, 2] [1, 1, 0, 0, 1, 1, 0] [2, 2, 0, 0, 2, 2, 0] demoR1_2001102 demoR2_2001102 demoC_2001102 demoM_2001102 demoMir_2001102

theorem demoR1_0101102 : invRung 7 5 20 [0, 1, 0, 1, 1, 0, 2] [0, 1, 0, 1, 1, 0, 2] 1 2 false = ([0, 2, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0101102 : invRung 7 5 20 [0, 1, 0, 1, 1, 0, 2] [0, 2, 2, 0, 2, 2, 2] 3 1 true = ([0, 2, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_0101102 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 1, 2] = [1, 1, 2, 2, 0, 1, 1] := by
  decide

theorem demoM_0101102 : fieldMul 7 5 20 [1, 1, 2, 2, 0, 1, 1] [0, 1, 0, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0101102 : specInv 7 5 20 [0, 1, 0, 1, 1, 0, 2] = some [1, 1, 2, 2, 0, 1, 1] :=
  specInv_white_7 [0, 1, 0, 1, 1, 0, 2] [0, 2, 2, 0, 2, 2, 2] [0, 2, 2, 0, 1, 1, 2] [1, 1, 2, 2, 0, 1, 1] demoR1_0101102 demoR2_0101102 demoC_0101102 demoM_0101102

theorem demoR1_1101102 : invRung 7 5 20 [1, 1, 0, 1, 1, 0, 2] [1, 1, 0, 1, 1, 0, 2] 1 2 false = ([2, 2, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1101102 : invRung 7 5 20 [1, 1, 0, 1, 1, 0, 2] [2, 2, 2, 0, 1, 0, 0] 3 1 true = ([2, 0, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1101102 : fieldCube 7 5 20 [2, 0, 2, 1, 1, 2, 1] = [2, 1, 2, 2, 0, 2, 2] := by
  decide

theorem demoM_1101102 : fieldMul 7 5 20 [2, 1, 2, 2, 0, 2, 2] [1, 1, 0, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1101102 : mirrorTrits [2, 1, 2, 2, 0, 2, 2] = [1, 2, 1, 1, 0, 1, 1] := by
  decide

theorem demoInv_1101102 : specInv 7 5 20 [1, 1, 0, 1, 1, 0, 2] = some [1, 2, 1, 1, 0, 1, 1] :=
  specInv_mirror_7 [1, 1, 0, 1, 1, 0, 2] [2, 2, 2, 0, 1, 0, 0] [2, 0, 2, 1, 1, 2, 1] [2, 1, 2, 2, 0, 2, 2] [1, 2, 1, 1, 0, 1, 1] demoR1_1101102 demoR2_1101102 demoC_1101102 demoM_1101102 demoMir_1101102

theorem demoR1_2101102 : invRung 7 5 20 [2, 1, 0, 1, 1, 0, 2] [2, 1, 0, 1, 1, 0, 2] 1 2 false = ([0, 1, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_2101102 : invRung 7 5 20 [2, 1, 0, 1, 1, 0, 2] [0, 1, 1, 2, 2, 2, 2] 3 1 true = ([0, 1, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_2101102 : fieldCube 7 5 20 [0, 1, 0, 1, 2, 1, 2] = [2, 2, 0, 2, 0, 0, 0] := by
  decide

theorem demoM_2101102 : fieldMul 7 5 20 [2, 2, 0, 2, 0, 0, 0] [2, 1, 0, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101102 : mirrorTrits [2, 2, 0, 2, 0, 0, 0] = [1, 1, 0, 1, 0, 0, 0] := by
  decide

theorem demoInv_2101102 : specInv 7 5 20 [2, 1, 0, 1, 1, 0, 2] = some [1, 1, 0, 1, 0, 0, 0] :=
  specInv_mirror_7 [2, 1, 0, 1, 1, 0, 2] [0, 1, 1, 2, 2, 2, 2] [0, 1, 0, 1, 2, 1, 2] [2, 2, 0, 2, 0, 0, 0] [1, 1, 0, 1, 0, 0, 0] demoR1_2101102 demoR2_2101102 demoC_2101102 demoM_2101102 demoMir_2101102

theorem demoR1_0201102 : invRung 7 5 20 [0, 2, 0, 1, 1, 0, 2] [0, 2, 0, 1, 1, 0, 2] 1 2 false = ([2, 2, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_0201102 : invRung 7 5 20 [0, 2, 0, 1, 1, 0, 2] [2, 2, 0, 0, 1, 0, 2] 3 1 true = ([0, 1, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0201102 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 0, 1] = [0, 2, 2, 0, 1, 2, 2] := by
  decide

theorem demoM_0201102 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 2, 2] [0, 2, 0, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201102 : mirrorTrits [0, 2, 2, 0, 1, 2, 2] = [0, 1, 1, 0, 2, 1, 1] := by
  decide

theorem demoInv_0201102 : specInv 7 5 20 [0, 2, 0, 1, 1, 0, 2] = some [0, 1, 1, 0, 2, 1, 1] :=
  specInv_mirror_7 [0, 2, 0, 1, 1, 0, 2] [2, 2, 0, 0, 1, 0, 2] [0, 1, 0, 0, 1, 0, 1] [0, 2, 2, 0, 1, 2, 2] [0, 1, 1, 0, 2, 1, 1] demoR1_0201102 demoR2_0201102 demoC_0201102 demoM_0201102 demoMir_0201102

theorem demoR1_1201102 : invRung 7 5 20 [1, 2, 0, 1, 1, 0, 2] [1, 2, 0, 1, 1, 0, 2] 1 2 false = ([0, 1, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1201102 : invRung 7 5 20 [1, 2, 0, 1, 1, 0, 2] [0, 1, 2, 2, 0, 0, 1] 3 1 true = ([0, 1, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_1201102 : fieldCube 7 5 20 [0, 1, 2, 1, 2, 0, 0] = [1, 2, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_1201102 : fieldMul 7 5 20 [1, 2, 1, 0, 0, 0, 1] [1, 2, 0, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201102 : mirrorTrits [1, 2, 1, 0, 0, 0, 1] = [2, 1, 2, 0, 0, 0, 2] := by
  decide

theorem demoInv_1201102 : specInv 7 5 20 [1, 2, 0, 1, 1, 0, 2] = some [2, 1, 2, 0, 0, 0, 2] :=
  specInv_mirror_7 [1, 2, 0, 1, 1, 0, 2] [0, 1, 2, 2, 0, 0, 1] [0, 1, 2, 1, 2, 0, 0] [1, 2, 1, 0, 0, 0, 1] [2, 1, 2, 0, 0, 0, 2] demoR1_1201102 demoR2_1201102 demoC_1201102 demoM_1201102 demoMir_1201102

theorem demoR1_2201102 : invRung 7 5 20 [2, 2, 0, 1, 1, 0, 2] [2, 2, 0, 1, 1, 0, 2] 1 2 false = ([2, 1, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_2201102 : invRung 7 5 20 [2, 2, 0, 1, 1, 0, 2] [2, 1, 2, 2, 1, 0, 1] 3 1 true = ([0, 1, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_2201102 : fieldCube 7 5 20 [0, 1, 0, 1, 1, 2, 2] = [0, 2, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_2201102 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 0, 1] [2, 2, 0, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2201102 : mirrorTrits [0, 2, 1, 1, 1, 0, 1] = [0, 1, 2, 2, 2, 0, 2] := by
  decide

theorem demoInv_2201102 : specInv 7 5 20 [2, 2, 0, 1, 1, 0, 2] = some [0, 1, 2, 2, 2, 0, 2] :=
  specInv_mirror_7 [2, 2, 0, 1, 1, 0, 2] [2, 1, 2, 2, 1, 0, 1] [0, 1, 0, 1, 1, 2, 2] [0, 2, 1, 1, 1, 0, 1] [0, 1, 2, 2, 2, 0, 2] demoR1_2201102 demoR2_2201102 demoC_2201102 demoM_2201102 demoMir_2201102

theorem demoR1_0011102 : invRung 7 5 20 [0, 0, 1, 1, 1, 0, 2] [0, 0, 1, 1, 1, 0, 2] 1 2 false = ([0, 1, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_0011102 : invRung 7 5 20 [0, 0, 1, 1, 1, 0, 2] [0, 1, 2, 1, 1, 2, 1] 3 1 true = ([1, 0, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_0011102 : fieldCube 7 5 20 [1, 0, 1, 1, 2, 2, 0] = [1, 1, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_0011102 : fieldMul 7 5 20 [1, 1, 0, 2, 2, 2, 1] [0, 0, 1, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0011102 : specInv 7 5 20 [0, 0, 1, 1, 1, 0, 2] = some [1, 1, 0, 2, 2, 2, 1] :=
  specInv_white_7 [0, 0, 1, 1, 1, 0, 2] [0, 1, 2, 1, 1, 2, 1] [1, 0, 1, 1, 2, 2, 0] [1, 1, 0, 2, 2, 2, 1] demoR1_0011102 demoR2_0011102 demoC_0011102 demoM_0011102

theorem demoR1_1011102 : invRung 7 5 20 [1, 0, 1, 1, 1, 0, 2] [1, 0, 1, 1, 1, 0, 2] 1 2 false = ([1, 2, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_1011102 : invRung 7 5 20 [1, 0, 1, 1, 1, 0, 2] [1, 2, 2, 1, 0, 0, 0] 3 1 true = ([1, 0, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_1011102 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 0, 1] = [0, 2, 1, 2, 1, 1, 1] := by
  decide

theorem demoM_1011102 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 1, 1] [1, 0, 1, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1011102 : specInv 7 5 20 [1, 0, 1, 1, 1, 0, 2] = some [0, 2, 1, 2, 1, 1, 1] :=
  specInv_white_7 [1, 0, 1, 1, 1, 0, 2] [1, 2, 2, 1, 0, 0, 0] [1, 0, 2, 2, 1, 0, 1] [0, 2, 1, 2, 1, 1, 1] demoR1_1011102 demoR2_1011102 demoC_1011102 demoM_1011102

theorem demoR1_2011102 : invRung 7 5 20 [2, 0, 1, 1, 1, 0, 2] [2, 0, 1, 1, 1, 0, 2] 1 2 false = ([2, 2, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_2011102 : invRung 7 5 20 [2, 0, 1, 1, 1, 0, 2] [2, 2, 2, 0, 0, 2, 1] 3 1 true = ([0, 2, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_2011102 : fieldCube 7 5 20 [0, 2, 1, 0, 0, 1, 2] = [1, 0, 2, 1, 0, 0, 2] := by
  decide

theorem demoM_2011102 : fieldMul 7 5 20 [1, 0, 2, 1, 0, 0, 2] [2, 0, 1, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2011102 : specInv 7 5 20 [2, 0, 1, 1, 1, 0, 2] = some [1, 0, 2, 1, 0, 0, 2] :=
  specInv_white_7 [2, 0, 1, 1, 1, 0, 2] [2, 2, 2, 0, 0, 2, 1] [0, 2, 1, 0, 0, 1, 2] [1, 0, 2, 1, 0, 0, 2] demoR1_2011102 demoR2_2011102 demoC_2011102 demoM_2011102

theorem demoR1_0111102 : invRung 7 5 20 [0, 1, 1, 1, 1, 0, 2] [0, 1, 1, 1, 1, 0, 2] 1 2 false = ([0, 1, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_0111102 : invRung 7 5 20 [0, 1, 1, 1, 1, 0, 2] [0, 1, 2, 2, 1, 0, 2] 3 1 true = ([0, 2, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_0111102 : fieldCube 7 5 20 [0, 2, 0, 1, 1, 1, 2] = [2, 1, 0, 2, 0, 2, 2] := by
  decide

theorem demoM_0111102 : fieldMul 7 5 20 [2, 1, 0, 2, 0, 2, 2] [0, 1, 1, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111102 : mirrorTrits [2, 1, 0, 2, 0, 2, 2] = [1, 2, 0, 1, 0, 1, 1] := by
  decide

theorem demoInv_0111102 : specInv 7 5 20 [0, 1, 1, 1, 1, 0, 2] = some [1, 2, 0, 1, 0, 1, 1] :=
  specInv_mirror_7 [0, 1, 1, 1, 1, 0, 2] [0, 1, 2, 2, 1, 0, 2] [0, 2, 0, 1, 1, 1, 2] [2, 1, 0, 2, 0, 2, 2] [1, 2, 0, 1, 0, 1, 1] demoR1_0111102 demoR2_0111102 demoC_0111102 demoM_0111102 demoMir_0111102

theorem demoR1_1111102 : invRung 7 5 20 [1, 1, 1, 1, 1, 0, 2] [1, 1, 1, 1, 1, 0, 2] 1 2 false = ([0, 2, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_1111102 : invRung 7 5 20 [1, 1, 1, 1, 1, 0, 2] [0, 2, 2, 2, 2, 2, 0] 3 1 true = ([2, 0, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_1111102 : fieldCube 7 5 20 [2, 0, 1, 1, 1, 0, 2] = [0, 0, 2, 0, 2, 1, 1] := by
  decide

theorem demoM_1111102 : fieldMul 7 5 20 [0, 0, 2, 0, 2, 1, 1] [1, 1, 1, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111102 : mirrorTrits [0, 0, 2, 0, 2, 1, 1] = [0, 0, 1, 0, 1, 2, 2] := by
  decide

theorem demoInv_1111102 : specInv 7 5 20 [1, 1, 1, 1, 1, 0, 2] = some [0, 0, 1, 0, 1, 2, 2] :=
  specInv_mirror_7 [1, 1, 1, 1, 1, 0, 2] [0, 2, 2, 2, 2, 2, 0] [2, 0, 1, 1, 1, 0, 2] [0, 0, 2, 0, 2, 1, 1] [0, 0, 1, 0, 1, 2, 2] demoR1_1111102 demoR2_1111102 demoC_1111102 demoM_1111102 demoMir_1111102

theorem demoR1_2111102 : invRung 7 5 20 [2, 1, 1, 1, 1, 0, 2] [2, 1, 1, 1, 1, 0, 2] 1 2 false = ([2, 1, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_2111102 : invRung 7 5 20 [2, 1, 1, 1, 1, 0, 2] [2, 1, 1, 0, 1, 1, 0] 3 1 true = ([1, 2, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_2111102 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 1, 1] = [1, 0, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_2111102 : fieldMul 7 5 20 [1, 0, 2, 1, 2, 2, 2] [2, 1, 1, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2111102 : specInv 7 5 20 [2, 1, 1, 1, 1, 0, 2] = some [1, 0, 2, 1, 2, 2, 2] :=
  specInv_white_7 [2, 1, 1, 1, 1, 0, 2] [2, 1, 1, 0, 1, 1, 0] [1, 2, 1, 2, 1, 1, 1] [1, 0, 2, 1, 2, 2, 2] demoR1_2111102 demoR2_2111102 demoC_2111102 demoM_2111102

theorem demoR1_0211102 : invRung 7 5 20 [0, 2, 1, 1, 1, 0, 2] [0, 2, 1, 1, 1, 0, 2] 1 2 false = ([2, 1, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_0211102 : invRung 7 5 20 [0, 2, 1, 1, 1, 0, 2] [2, 1, 2, 1, 1, 2, 1] 3 1 true = ([2, 1, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_0211102 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 2, 0] = [0, 0, 1, 2, 2, 2, 2] := by
  decide

theorem demoM_0211102 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 2, 2] [0, 2, 1, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0211102 : specInv 7 5 20 [0, 2, 1, 1, 1, 0, 2] = some [0, 0, 1, 2, 2, 2, 2] :=
  specInv_white_7 [0, 2, 1, 1, 1, 0, 2] [2, 1, 2, 1, 1, 2, 1] [2, 1, 0, 2, 1, 2, 0] [0, 0, 1, 2, 2, 2, 2] demoR1_0211102 demoR2_0211102 demoC_0211102 demoM_0211102

theorem demoR1_1211102 : invRung 7 5 20 [1, 2, 1, 1, 1, 0, 2] [1, 2, 1, 1, 1, 0, 2] 1 2 false = ([1, 0, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1211102 : invRung 7 5 20 [1, 2, 1, 1, 1, 0, 2] [1, 0, 2, 2, 0, 1, 2] 3 1 true = ([2, 1, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_1211102 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 1, 2] = [2, 1, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_1211102 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 0, 2] [1, 2, 1, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1211102 : specInv 7 5 20 [1, 2, 1, 1, 1, 0, 2] = some [2, 1, 1, 1, 0, 0, 2] :=
  specInv_white_7 [1, 2, 1, 1, 1, 0, 2] [1, 0, 2, 2, 0, 1, 2] [2, 1, 0, 2, 1, 1, 2] [2, 1, 1, 1, 0, 0, 2] demoR1_1211102 demoR2_1211102 demoC_1211102 demoM_1211102

theorem demoR1_2211102 : invRung 7 5 20 [2, 2, 1, 1, 1, 0, 2] [2, 2, 1, 1, 1, 0, 2] 1 2 false = ([1, 2, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_2211102 : invRung 7 5 20 [2, 2, 1, 1, 1, 0, 2] [1, 2, 0, 0, 0, 2, 2] 3 1 true = ([1, 1, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_2211102 : fieldCube 7 5 20 [1, 1, 1, 1, 0, 2, 2] = [1, 1, 1, 0, 1, 2, 1] := by
  decide

theorem demoM_2211102 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 2, 1] [2, 2, 1, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2211102 : specInv 7 5 20 [2, 2, 1, 1, 1, 0, 2] = some [1, 1, 1, 0, 1, 2, 1] :=
  specInv_white_7 [2, 2, 1, 1, 1, 0, 2] [1, 2, 0, 0, 0, 2, 2] [1, 1, 1, 1, 0, 2, 2] [1, 1, 1, 0, 1, 2, 1] demoR1_2211102 demoR2_2211102 demoC_2211102 demoM_2211102

theorem demoR1_0021102 : invRung 7 5 20 [0, 0, 2, 1, 1, 0, 2] [0, 0, 2, 1, 1, 0, 2] 1 2 false = ([1, 1, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0021102 : invRung 7 5 20 [0, 0, 2, 1, 1, 0, 2] [1, 1, 2, 0, 0, 0, 0] 3 1 true = ([1, 2, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_0021102 : fieldCube 7 5 20 [1, 2, 0, 2, 2, 2, 1] = [2, 2, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_0021102 : fieldMul 7 5 20 [2, 2, 0, 2, 0, 1, 1] [0, 0, 2, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0021102 : specInv 7 5 20 [0, 0, 2, 1, 1, 0, 2] = some [2, 2, 0, 2, 0, 1, 1] :=
  specInv_white_7 [0, 0, 2, 1, 1, 0, 2] [1, 1, 2, 0, 0, 0, 0] [1, 2, 0, 2, 2, 2, 1] [2, 2, 0, 2, 0, 1, 1] demoR1_0021102 demoR2_0021102 demoC_0021102 demoM_0021102

theorem demoR1_1021102 : invRung 7 5 20 [1, 0, 2, 1, 1, 0, 2] [1, 0, 2, 1, 1, 0, 2] 1 2 false = ([2, 1, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_1021102 : invRung 7 5 20 [1, 0, 2, 1, 1, 0, 2] [2, 1, 2, 1, 0, 1, 2] 3 1 true = ([1, 0, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_1021102 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 1, 1] = [0, 1, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_1021102 : fieldMul 7 5 20 [0, 1, 1, 0, 2, 2, 2] [1, 0, 2, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1021102 : specInv 7 5 20 [1, 0, 2, 1, 1, 0, 2] = some [0, 1, 1, 0, 2, 2, 2] :=
  specInv_white_7 [1, 0, 2, 1, 1, 0, 2] [2, 1, 2, 1, 0, 1, 2] [1, 0, 0, 1, 2, 1, 1] [0, 1, 1, 0, 2, 2, 2] demoR1_1021102 demoR2_1021102 demoC_1021102 demoM_1021102

theorem demoR1_2021102 : invRung 7 5 20 [2, 0, 2, 1, 1, 0, 2] [2, 0, 2, 1, 1, 0, 2] 1 2 false = ([0, 2, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_2021102 : invRung 7 5 20 [2, 0, 2, 1, 1, 0, 2] [0, 2, 2, 0, 0, 2, 1] 3 1 true = ([0, 2, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2021102 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 2, 1] = [0, 0, 2, 0, 0, 1, 2] := by
  decide

theorem demoM_2021102 : fieldMul 7 5 20 [0, 0, 2, 0, 0, 1, 2] [2, 0, 2, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2021102 : specInv 7 5 20 [2, 0, 2, 1, 1, 0, 2] = some [0, 0, 2, 0, 0, 1, 2] :=
  specInv_white_7 [2, 0, 2, 1, 1, 0, 2] [0, 2, 2, 0, 0, 2, 1] [0, 2, 0, 1, 0, 2, 1] [0, 0, 2, 0, 0, 1, 2] demoR1_2021102 demoR2_2021102 demoC_2021102 demoM_2021102

theorem demoR1_0121102 : invRung 7 5 20 [0, 1, 2, 1, 1, 0, 2] [0, 1, 2, 1, 1, 0, 2] 1 2 false = ([0, 1, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_0121102 : invRung 7 5 20 [0, 1, 2, 1, 1, 0, 2] [0, 1, 2, 2, 0, 0, 2] 3 1 true = ([0, 1, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_0121102 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 0, 0] = [2, 1, 2, 2, 0, 0, 0] := by
  decide

theorem demoM_0121102 : fieldMul 7 5 20 [2, 1, 2, 2, 0, 0, 0] [0, 1, 2, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0121102 : mirrorTrits [2, 1, 2, 2, 0, 0, 0] = [1, 2, 1, 1, 0, 0, 0] := by
  decide

theorem demoInv_0121102 : specInv 7 5 20 [0, 1, 2, 1, 1, 0, 2] = some [1, 2, 1, 1, 0, 0, 0] :=
  specInv_mirror_7 [0, 1, 2, 1, 1, 0, 2] [0, 1, 2, 2, 0, 0, 2] [0, 1, 2, 2, 1, 0, 0] [2, 1, 2, 2, 0, 0, 0] [1, 2, 1, 1, 0, 0, 0] demoR1_0121102 demoR2_0121102 demoC_0121102 demoM_0121102 demoMir_0121102

theorem demoR1_1121102 : invRung 7 5 20 [1, 1, 2, 1, 1, 0, 2] [1, 1, 2, 1, 1, 0, 2] 1 2 false = ([0, 0, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_1121102 : invRung 7 5 20 [1, 1, 2, 1, 1, 0, 2] [0, 0, 0, 2, 0, 0, 2] 3 1 true = ([1, 0, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_1121102 : fieldCube 7 5 20 [1, 0, 0, 2, 1, 0, 1] = [0, 2, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_1121102 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 1, 2] [1, 1, 2, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121102 : mirrorTrits [0, 2, 1, 2, 1, 1, 2] = [0, 1, 2, 1, 2, 2, 1] := by
  decide

theorem demoInv_1121102 : specInv 7 5 20 [1, 1, 2, 1, 1, 0, 2] = some [0, 1, 2, 1, 2, 2, 1] :=
  specInv_mirror_7 [1, 1, 2, 1, 1, 0, 2] [0, 0, 0, 2, 0, 0, 2] [1, 0, 0, 2, 1, 0, 1] [0, 2, 1, 2, 1, 1, 2] [0, 1, 2, 1, 2, 2, 1] demoR1_1121102 demoR2_1121102 demoC_1121102 demoM_1121102 demoMir_1121102

theorem demoR1_2121102 : invRung 7 5 20 [2, 1, 2, 1, 1, 0, 2] [2, 1, 2, 1, 1, 0, 2] 1 2 false = ([2, 2, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_2121102 : invRung 7 5 20 [2, 1, 2, 1, 1, 0, 2] [2, 2, 0, 2, 0, 2, 2] 3 1 true = ([1, 0, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_2121102 : fieldCube 7 5 20 [1, 0, 1, 0, 1, 1, 2] = [2, 1, 2, 0, 0, 1, 0] := by
  decide

theorem demoM_2121102 : fieldMul 7 5 20 [2, 1, 2, 0, 0, 1, 0] [2, 1, 2, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2121102 : mirrorTrits [2, 1, 2, 0, 0, 1, 0] = [1, 2, 1, 0, 0, 2, 0] := by
  decide

theorem demoInv_2121102 : specInv 7 5 20 [2, 1, 2, 1, 1, 0, 2] = some [1, 2, 1, 0, 0, 2, 0] :=
  specInv_mirror_7 [2, 1, 2, 1, 1, 0, 2] [2, 2, 0, 2, 0, 2, 2] [1, 0, 1, 0, 1, 1, 2] [2, 1, 2, 0, 0, 1, 0] [1, 2, 1, 0, 0, 2, 0] demoR1_2121102 demoR2_2121102 demoC_2121102 demoM_2121102 demoMir_2121102

theorem demoR1_0221102 : invRung 7 5 20 [0, 2, 2, 1, 1, 0, 2] [0, 2, 2, 1, 1, 0, 2] 1 2 false = ([2, 0, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_0221102 : invRung 7 5 20 [0, 2, 2, 1, 1, 0, 2] [2, 0, 0, 2, 0, 2, 2] 3 1 true = ([2, 0, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0221102 : fieldCube 7 5 20 [2, 0, 0, 0, 2, 2, 2] = [1, 0, 0, 1, 1, 0, 2] := by
  decide

theorem demoM_0221102 : fieldMul 7 5 20 [1, 0, 0, 1, 1, 0, 2] [0, 2, 2, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0221102 : specInv 7 5 20 [0, 2, 2, 1, 1, 0, 2] = some [1, 0, 0, 1, 1, 0, 2] :=
  specInv_white_7 [0, 2, 2, 1, 1, 0, 2] [2, 0, 0, 2, 0, 2, 2] [2, 0, 0, 0, 2, 2, 2] [1, 0, 0, 1, 1, 0, 2] demoR1_0221102 demoR2_0221102 demoC_0221102 demoM_0221102

theorem demoR1_1221102 : invRung 7 5 20 [1, 2, 2, 1, 1, 0, 2] [1, 2, 2, 1, 1, 0, 2] 1 2 false = ([1, 2, 2, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_1221102 : invRung 7 5 20 [1, 2, 2, 1, 1, 0, 2] [1, 2, 2, 2, 2, 0, 1] 3 1 true = ([0, 2, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_1221102 : fieldCube 7 5 20 [0, 2, 0, 0, 0, 1, 1] = [1, 2, 0, 0, 2, 2, 0] := by
  decide

theorem demoM_1221102 : fieldMul 7 5 20 [1, 2, 0, 0, 2, 2, 0] [1, 2, 2, 1, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221102 : mirrorTrits [1, 2, 0, 0, 2, 2, 0] = [2, 1, 0, 0, 1, 1, 0] := by
  decide

theorem demoInv_1221102 : specInv 7 5 20 [1, 2, 2, 1, 1, 0, 2] = some [2, 1, 0, 0, 1, 1, 0] :=
  specInv_mirror_7 [1, 2, 2, 1, 1, 0, 2] [1, 2, 2, 2, 2, 0, 1] [0, 2, 0, 0, 0, 1, 1] [1, 2, 0, 0, 2, 2, 0] [2, 1, 0, 0, 1, 1, 0] demoR1_1221102 demoR2_1221102 demoC_1221102 demoM_1221102 demoMir_1221102

theorem demoR1_2221102 : invRung 7 5 20 [2, 2, 2, 1, 1, 0, 2] [2, 2, 2, 1, 1, 0, 2] 1 2 false = ([1, 0, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2221102 : invRung 7 5 20 [2, 2, 2, 1, 1, 0, 2] [1, 0, 2, 1, 1, 2, 0] 3 1 true = ([1, 2, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_2221102 : fieldCube 7 5 20 [1, 2, 0, 1, 0, 1, 0] = [0, 1, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_2221102 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 2, 2] [2, 2, 2, 1, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2221102 : specInv 7 5 20 [2, 2, 2, 1, 1, 0, 2] = some [0, 1, 2, 2, 1, 2, 2] :=
  specInv_white_7 [2, 2, 2, 1, 1, 0, 2] [1, 0, 2, 1, 1, 2, 0] [1, 2, 0, 1, 0, 1, 0] [0, 1, 2, 2, 1, 2, 2] demoR1_2221102 demoR2_2221102 demoC_2221102 demoM_2221102

theorem demoR1_0002102 : invRung 7 5 20 [0, 0, 0, 2, 1, 0, 2] [0, 0, 0, 2, 1, 0, 2] 1 2 false = ([2, 0, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_0002102 : invRung 7 5 20 [0, 0, 0, 2, 1, 0, 2] [2, 0, 2, 2, 2, 0, 0] 3 1 true = ([1, 1, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_0002102 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 0, 2] = [1, 2, 1, 0, 2, 2, 0] := by
  decide

theorem demoM_0002102 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 2, 0] [0, 0, 0, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002102 : mirrorTrits [1, 2, 1, 0, 2, 2, 0] = [2, 1, 2, 0, 1, 1, 0] := by
  decide

theorem demoInv_0002102 : specInv 7 5 20 [0, 0, 0, 2, 1, 0, 2] = some [2, 1, 2, 0, 1, 1, 0] :=
  specInv_mirror_7 [0, 0, 0, 2, 1, 0, 2] [2, 0, 2, 2, 2, 0, 0] [1, 1, 1, 0, 0, 0, 2] [1, 2, 1, 0, 2, 2, 0] [2, 1, 2, 0, 1, 1, 0] demoR1_0002102 demoR2_0002102 demoC_0002102 demoM_0002102 demoMir_0002102

theorem demoR1_1002102 : invRung 7 5 20 [1, 0, 0, 2, 1, 0, 2] [1, 0, 0, 2, 1, 0, 2] 1 2 false = ([2, 2, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_1002102 : invRung 7 5 20 [1, 0, 0, 2, 1, 0, 2] [2, 2, 0, 2, 0, 2, 1] 3 1 true = ([1, 2, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_1002102 : fieldCube 7 5 20 [1, 2, 0, 2, 2, 2, 0] = [2, 1, 1, 1, 2, 0, 0] := by
  decide

theorem demoM_1002102 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 0, 0] [1, 0, 0, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002102 : mirrorTrits [2, 1, 1, 1, 2, 0, 0] = [1, 2, 2, 2, 1, 0, 0] := by
  decide

theorem demoInv_1002102 : specInv 7 5 20 [1, 0, 0, 2, 1, 0, 2] = some [1, 2, 2, 2, 1, 0, 0] :=
  specInv_mirror_7 [1, 0, 0, 2, 1, 0, 2] [2, 2, 0, 2, 0, 2, 1] [1, 2, 0, 2, 2, 2, 0] [2, 1, 1, 1, 2, 0, 0] [1, 2, 2, 2, 1, 0, 0] demoR1_1002102 demoR2_1002102 demoC_1002102 demoM_1002102 demoMir_1002102

theorem demoR1_2002102 : invRung 7 5 20 [2, 0, 0, 2, 1, 0, 2] [2, 0, 0, 2, 1, 0, 2] 1 2 false = ([2, 0, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_2002102 : invRung 7 5 20 [2, 0, 0, 2, 1, 0, 2] [2, 0, 2, 1, 2, 1, 0] 3 1 true = ([1, 1, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_2002102 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 2, 0] = [0, 2, 2, 1, 2, 2, 0] := by
  decide

theorem demoM_2002102 : fieldMul 7 5 20 [0, 2, 2, 1, 2, 2, 0] [2, 0, 0, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002102 : mirrorTrits [0, 2, 2, 1, 2, 2, 0] = [0, 1, 1, 2, 1, 1, 0] := by
  decide

theorem demoInv_2002102 : specInv 7 5 20 [2, 0, 0, 2, 1, 0, 2] = some [0, 1, 1, 2, 1, 1, 0] :=
  specInv_mirror_7 [2, 0, 0, 2, 1, 0, 2] [2, 0, 2, 1, 2, 1, 0] [1, 1, 2, 0, 0, 2, 0] [0, 2, 2, 1, 2, 2, 0] [0, 1, 1, 2, 1, 1, 0] demoR1_2002102 demoR2_2002102 demoC_2002102 demoM_2002102 demoMir_2002102

theorem demoR1_0102102 : invRung 7 5 20 [0, 1, 0, 2, 1, 0, 2] [0, 1, 0, 2, 1, 0, 2] 1 2 false = ([2, 1, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_0102102 : invRung 7 5 20 [0, 1, 0, 2, 1, 0, 2] [2, 1, 0, 2, 0, 1, 2] 3 1 true = ([2, 0, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_0102102 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 0, 2] = [1, 2, 0, 2, 2, 1, 0] := by
  decide

theorem demoM_0102102 : fieldMul 7 5 20 [1, 2, 0, 2, 2, 1, 0] [0, 1, 0, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102102 : mirrorTrits [1, 2, 0, 2, 2, 1, 0] = [2, 1, 0, 1, 1, 2, 0] := by
  decide

theorem demoInv_0102102 : specInv 7 5 20 [0, 1, 0, 2, 1, 0, 2] = some [2, 1, 0, 1, 1, 2, 0] :=
  specInv_mirror_7 [0, 1, 0, 2, 1, 0, 2] [2, 1, 0, 2, 0, 1, 2] [2, 0, 1, 2, 0, 0, 2] [1, 2, 0, 2, 2, 1, 0] [2, 1, 0, 1, 1, 2, 0] demoR1_0102102 demoR2_0102102 demoC_0102102 demoM_0102102 demoMir_0102102

theorem demoR1_1102102 : invRung 7 5 20 [1, 1, 0, 2, 1, 0, 2] [1, 1, 0, 2, 1, 0, 2] 1 2 false = ([2, 1, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_1102102 : invRung 7 5 20 [1, 1, 0, 2, 1, 0, 2] [2, 1, 0, 0, 1, 2, 0] 3 1 true = ([1, 1, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_1102102 : fieldCube 7 5 20 [1, 1, 2, 0, 2, 0, 2] = [1, 1, 1, 2, 2, 1, 0] := by
  decide

theorem demoM_1102102 : fieldMul 7 5 20 [1, 1, 1, 2, 2, 1, 0] [1, 1, 0, 2, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1102102 : specInv 7 5 20 [1, 1, 0, 2, 1, 0, 2] = some [1, 1, 1, 2, 2, 1, 0] :=
  specInv_white_7 [1, 1, 0, 2, 1, 0, 2] [2, 1, 0, 0, 1, 2, 0] [1, 1, 2, 0, 2, 0, 2] [1, 1, 1, 2, 2, 1, 0] demoR1_1102102 demoR2_1102102 demoC_1102102 demoM_1102102

theorem demoR1_2102102 : invRung 7 5 20 [2, 1, 0, 2, 1, 0, 2] [2, 1, 0, 2, 1, 0, 2] 1 2 false = ([1, 2, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_2102102 : invRung 7 5 20 [2, 1, 0, 2, 1, 0, 2] [1, 2, 0, 2, 0, 2, 2] 3 1 true = ([1, 2, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_2102102 : fieldCube 7 5 20 [1, 2, 0, 0, 2, 1, 1] = [2, 1, 0, 2, 2, 1, 2] := by
  decide

theorem demoM_2102102 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 1, 2] [2, 1, 0, 2, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2102102 : specInv 7 5 20 [2, 1, 0, 2, 1, 0, 2] = some [2, 1, 0, 2, 2, 1, 2] :=
  specInv_white_7 [2, 1, 0, 2, 1, 0, 2] [1, 2, 0, 2, 0, 2, 2] [1, 2, 0, 0, 2, 1, 1] [2, 1, 0, 2, 2, 1, 2] demoR1_2102102 demoR2_2102102 demoC_2102102 demoM_2102102

theorem demoR1_0202102 : invRung 7 5 20 [0, 2, 0, 2, 1, 0, 2] [0, 2, 0, 2, 1, 0, 2] 1 2 false = ([0, 1, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0202102 : invRung 7 5 20 [0, 2, 0, 2, 1, 0, 2] [0, 1, 0, 1, 0, 0, 0] 3 1 true = ([1, 2, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0202102 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 2, 2] = [1, 0, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_0202102 : fieldMul 7 5 20 [1, 0, 1, 0, 1, 1, 0] [0, 2, 0, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202102 : mirrorTrits [1, 0, 1, 0, 1, 1, 0] = [2, 0, 2, 0, 2, 2, 0] := by
  decide

theorem demoInv_0202102 : specInv 7 5 20 [0, 2, 0, 2, 1, 0, 2] = some [2, 0, 2, 0, 2, 2, 0] :=
  specInv_mirror_7 [0, 2, 0, 2, 1, 0, 2] [0, 1, 0, 1, 0, 0, 0] [1, 2, 1, 1, 2, 2, 2] [1, 0, 1, 0, 1, 1, 0] [2, 0, 2, 0, 2, 2, 0] demoR1_0202102 demoR2_0202102 demoC_0202102 demoM_0202102 demoMir_0202102

theorem demoR1_1202102 : invRung 7 5 20 [1, 2, 0, 2, 1, 0, 2] [1, 2, 0, 2, 1, 0, 2] 1 2 false = ([0, 0, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_1202102 : invRung 7 5 20 [1, 2, 0, 2, 1, 0, 2] [0, 0, 2, 1, 0, 2, 2] 3 1 true = ([2, 2, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_1202102 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 2, 0] = [0, 0, 1, 0, 2, 2, 1] := by
  decide

theorem demoM_1202102 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 2, 1] [1, 2, 0, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202102 : mirrorTrits [0, 0, 1, 0, 2, 2, 1] = [0, 0, 2, 0, 1, 1, 2] := by
  decide

theorem demoInv_1202102 : specInv 7 5 20 [1, 2, 0, 2, 1, 0, 2] = some [0, 0, 2, 0, 1, 1, 2] :=
  specInv_mirror_7 [1, 2, 0, 2, 1, 0, 2] [0, 0, 2, 1, 0, 2, 2] [2, 2, 2, 2, 1, 2, 0] [0, 0, 1, 0, 2, 2, 1] [0, 0, 2, 0, 1, 1, 2] demoR1_1202102 demoR2_1202102 demoC_1202102 demoM_1202102 demoMir_1202102

theorem demoR1_2202102 : invRung 7 5 20 [2, 2, 0, 2, 1, 0, 2] [2, 2, 0, 2, 1, 0, 2] 1 2 false = ([1, 2, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2202102 : invRung 7 5 20 [2, 2, 0, 2, 1, 0, 2] [1, 2, 0, 1, 1, 2, 2] 3 1 true = ([0, 1, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_2202102 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 1, 0] = [0, 2, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_2202102 : fieldMul 7 5 20 [0, 2, 0, 2, 1, 1, 2] [2, 2, 0, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202102 : mirrorTrits [0, 2, 0, 2, 1, 1, 2] = [0, 1, 0, 1, 2, 2, 1] := by
  decide

theorem demoInv_2202102 : specInv 7 5 20 [2, 2, 0, 2, 1, 0, 2] = some [0, 1, 0, 1, 2, 2, 1] :=
  specInv_mirror_7 [2, 2, 0, 2, 1, 0, 2] [1, 2, 0, 1, 1, 2, 2] [0, 1, 2, 2, 1, 1, 0] [0, 2, 0, 2, 1, 1, 2] [0, 1, 0, 1, 2, 2, 1] demoR1_2202102 demoR2_2202102 demoC_2202102 demoM_2202102 demoMir_2202102

theorem demoR1_0012102 : invRung 7 5 20 [0, 0, 1, 2, 1, 0, 2] [0, 0, 1, 2, 1, 0, 2] 1 2 false = ([0, 2, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_0012102 : invRung 7 5 20 [0, 0, 1, 2, 1, 0, 2] [0, 2, 2, 1, 1, 1, 0] 3 1 true = ([1, 2, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_0012102 : fieldCube 7 5 20 [1, 2, 1, 2, 0, 0, 0] = [0, 0, 2, 2, 0, 2, 1] := by
  decide

theorem demoM_0012102 : fieldMul 7 5 20 [0, 0, 2, 2, 0, 2, 1] [0, 0, 1, 2, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0012102 : specInv 7 5 20 [0, 0, 1, 2, 1, 0, 2] = some [0, 0, 2, 2, 0, 2, 1] :=
  specInv_white_7 [0, 0, 1, 2, 1, 0, 2] [0, 2, 2, 1, 1, 1, 0] [1, 2, 1, 2, 0, 0, 0] [0, 0, 2, 2, 0, 2, 1] demoR1_0012102 demoR2_0012102 demoC_0012102 demoM_0012102

theorem demoR1_1012102 : invRung 7 5 20 [1, 0, 1, 2, 1, 0, 2] [1, 0, 1, 2, 1, 0, 2] 1 2 false = ([1, 1, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_1012102 : invRung 7 5 20 [1, 0, 1, 2, 1, 0, 2] [1, 1, 0, 1, 2, 1, 0] 3 1 true = ([2, 1, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_1012102 : fieldCube 7 5 20 [2, 1, 1, 0, 0, 0, 1] = [2, 1, 2, 2, 1, 1, 2] := by
  decide

theorem demoM_1012102 : fieldMul 7 5 20 [2, 1, 2, 2, 1, 1, 2] [1, 0, 1, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1012102 : mirrorTrits [2, 1, 2, 2, 1, 1, 2] = [1, 2, 1, 1, 2, 2, 1] := by
  decide

theorem demoInv_1012102 : specInv 7 5 20 [1, 0, 1, 2, 1, 0, 2] = some [1, 2, 1, 1, 2, 2, 1] :=
  specInv_mirror_7 [1, 0, 1, 2, 1, 0, 2] [1, 1, 0, 1, 2, 1, 0] [2, 1, 1, 0, 0, 0, 1] [2, 1, 2, 2, 1, 1, 2] [1, 2, 1, 1, 2, 2, 1] demoR1_1012102 demoR2_1012102 demoC_1012102 demoM_1012102 demoMir_1012102

theorem demoR1_2012102 : invRung 7 5 20 [2, 0, 1, 2, 1, 0, 2] [2, 0, 1, 2, 1, 0, 2] 1 2 false = ([2, 1, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2012102 : invRung 7 5 20 [2, 0, 1, 2, 1, 0, 2] [2, 1, 2, 2, 0, 0, 2] 3 1 true = ([1, 1, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2012102 : fieldCube 7 5 20 [1, 1, 2, 1, 1, 2, 1] = [1, 1, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_2012102 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 2, 2] [2, 0, 1, 2, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2012102 : specInv 7 5 20 [2, 0, 1, 2, 1, 0, 2] = some [1, 1, 2, 0, 0, 2, 2] :=
  specInv_white_7 [2, 0, 1, 2, 1, 0, 2] [2, 1, 2, 2, 0, 0, 2] [1, 1, 2, 1, 1, 2, 1] [1, 1, 2, 0, 0, 2, 2] demoR1_2012102 demoR2_2012102 demoC_2012102 demoM_2012102

theorem demoR1_0112102 : invRung 7 5 20 [0, 1, 1, 2, 1, 0, 2] [0, 1, 1, 2, 1, 0, 2] 1 2 false = ([0, 0, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_0112102 : invRung 7 5 20 [0, 1, 1, 2, 1, 0, 2] [0, 0, 0, 1, 2, 1, 1] 3 1 true = ([2, 0, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0112102 : fieldCube 7 5 20 [2, 0, 0, 0, 2, 1, 0] = [0, 0, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_0112102 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 0, 1] [0, 1, 1, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112102 : mirrorTrits [0, 0, 1, 2, 1, 0, 1] = [0, 0, 2, 1, 2, 0, 2] := by
  decide

theorem demoInv_0112102 : specInv 7 5 20 [0, 1, 1, 2, 1, 0, 2] = some [0, 0, 2, 1, 2, 0, 2] :=
  specInv_mirror_7 [0, 1, 1, 2, 1, 0, 2] [0, 0, 0, 1, 2, 1, 1] [2, 0, 0, 0, 2, 1, 0] [0, 0, 1, 2, 1, 0, 1] [0, 0, 2, 1, 2, 0, 2] demoR1_0112102 demoR2_0112102 demoC_0112102 demoM_0112102 demoMir_0112102

theorem demoR1_1112102 : invRung 7 5 20 [1, 1, 1, 2, 1, 0, 2] [1, 1, 1, 2, 1, 0, 2] 1 2 false = ([1, 2, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_1112102 : invRung 7 5 20 [1, 1, 1, 2, 1, 0, 2] [1, 2, 1, 1, 1, 1, 0] 3 1 true = ([0, 1, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_1112102 : fieldCube 7 5 20 [0, 1, 1, 1, 1, 0, 1] = [1, 2, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_1112102 : fieldMul 7 5 20 [1, 2, 0, 0, 1, 0, 0] [1, 1, 1, 2, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1112102 : specInv 7 5 20 [1, 1, 1, 2, 1, 0, 2] = some [1, 2, 0, 0, 1, 0, 0] :=
  specInv_white_7 [1, 1, 1, 2, 1, 0, 2] [1, 2, 1, 1, 1, 1, 0] [0, 1, 1, 1, 1, 0, 1] [1, 2, 0, 0, 1, 0, 0] demoR1_1112102 demoR2_1112102 demoC_1112102 demoM_1112102

theorem demoR1_2112102 : invRung 7 5 20 [2, 1, 1, 2, 1, 0, 2] [2, 1, 1, 2, 1, 0, 2] 1 2 false = ([1, 1, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2112102 : invRung 7 5 20 [2, 1, 1, 2, 1, 0, 2] [1, 1, 2, 1, 0, 2, 1] 3 1 true = ([1, 2, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_2112102 : fieldCube 7 5 20 [1, 2, 2, 0, 0, 0, 0] = [1, 0, 0, 2, 0, 0, 2] := by
  decide

theorem demoM_2112102 : fieldMul 7 5 20 [1, 0, 0, 2, 0, 0, 2] [2, 1, 1, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112102 : mirrorTrits [1, 0, 0, 2, 0, 0, 2] = [2, 0, 0, 1, 0, 0, 1] := by
  decide

theorem demoInv_2112102 : specInv 7 5 20 [2, 1, 1, 2, 1, 0, 2] = some [2, 0, 0, 1, 0, 0, 1] :=
  specInv_mirror_7 [2, 1, 1, 2, 1, 0, 2] [1, 1, 2, 1, 0, 2, 1] [1, 2, 2, 0, 0, 0, 0] [1, 0, 0, 2, 0, 0, 2] [2, 0, 0, 1, 0, 0, 1] demoR1_2112102 demoR2_2112102 demoC_2112102 demoM_2112102 demoMir_2112102

theorem demoR1_0212102 : invRung 7 5 20 [0, 2, 1, 2, 1, 0, 2] [0, 2, 1, 2, 1, 0, 2] 1 2 false = ([2, 2, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_0212102 : invRung 7 5 20 [0, 2, 1, 2, 1, 0, 2] [2, 2, 1, 0, 2, 0, 1] 3 1 true = ([2, 0, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_0212102 : fieldCube 7 5 20 [2, 0, 0, 2, 0, 2, 1] = [0, 0, 0, 1, 0, 2, 2] := by
  decide

theorem demoM_0212102 : fieldMul 7 5 20 [0, 0, 0, 1, 0, 2, 2] [0, 2, 1, 2, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0212102 : specInv 7 5 20 [0, 2, 1, 2, 1, 0, 2] = some [0, 0, 0, 1, 0, 2, 2] :=
  specInv_white_7 [0, 2, 1, 2, 1, 0, 2] [2, 2, 1, 0, 2, 0, 1] [2, 0, 0, 2, 0, 2, 1] [0, 0, 0, 1, 0, 2, 2] demoR1_0212102 demoR2_0212102 demoC_0212102 demoM_0212102

theorem demoR1_1212102 : invRung 7 5 20 [1, 2, 1, 2, 1, 0, 2] [1, 2, 1, 2, 1, 0, 2] 1 2 false = ([0, 2, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_1212102 : invRung 7 5 20 [1, 2, 1, 2, 1, 0, 2] [0, 2, 2, 1, 1, 2, 0] 3 1 true = ([0, 2, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_1212102 : fieldCube 7 5 20 [0, 2, 1, 2, 0, 0, 1] = [2, 1, 1, 0, 1, 0, 2] := by
  decide

theorem demoM_1212102 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 0, 2] [1, 2, 1, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212102 : mirrorTrits [2, 1, 1, 0, 1, 0, 2] = [1, 2, 2, 0, 2, 0, 1] := by
  decide

theorem demoInv_1212102 : specInv 7 5 20 [1, 2, 1, 2, 1, 0, 2] = some [1, 2, 2, 0, 2, 0, 1] :=
  specInv_mirror_7 [1, 2, 1, 2, 1, 0, 2] [0, 2, 2, 1, 1, 2, 0] [0, 2, 1, 2, 0, 0, 1] [2, 1, 1, 0, 1, 0, 2] [1, 2, 2, 0, 2, 0, 1] demoR1_1212102 demoR2_1212102 demoC_1212102 demoM_1212102 demoMir_1212102

theorem demoR1_2212102 : invRung 7 5 20 [2, 2, 1, 2, 1, 0, 2] [2, 2, 1, 2, 1, 0, 2] 1 2 false = ([2, 1, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_2212102 : invRung 7 5 20 [2, 2, 1, 2, 1, 0, 2] [2, 1, 2, 1, 0, 1, 1] 3 1 true = ([2, 0, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_2212102 : fieldCube 7 5 20 [2, 0, 1, 2, 2, 0, 2] = [1, 1, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_2212102 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 0, 2] [2, 2, 1, 2, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2212102 : specInv 7 5 20 [2, 2, 1, 2, 1, 0, 2] = some [1, 1, 0, 1, 2, 0, 2] :=
  specInv_white_7 [2, 2, 1, 2, 1, 0, 2] [2, 1, 2, 1, 0, 1, 1] [2, 0, 1, 2, 2, 0, 2] [1, 1, 0, 1, 2, 0, 2] demoR1_2212102 demoR2_2212102 demoC_2212102 demoM_2212102

theorem demoR1_0022102 : invRung 7 5 20 [0, 0, 2, 2, 1, 0, 2] [0, 0, 2, 2, 1, 0, 2] 1 2 false = ([2, 1, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_0022102 : invRung 7 5 20 [0, 0, 2, 2, 1, 0, 2] [2, 1, 1, 2, 1, 0, 1] 3 1 true = ([2, 0, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0022102 : fieldCube 7 5 20 [2, 0, 0, 2, 0, 1, 1] = [2, 2, 2, 1, 2, 1, 0] := by
  decide

theorem demoM_0022102 : fieldMul 7 5 20 [2, 2, 2, 1, 2, 1, 0] [0, 0, 2, 2, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0022102 : specInv 7 5 20 [0, 0, 2, 2, 1, 0, 2] = some [2, 2, 2, 1, 2, 1, 0] :=
  specInv_white_7 [0, 0, 2, 2, 1, 0, 2] [2, 1, 1, 2, 1, 0, 1] [2, 0, 0, 2, 0, 1, 1] [2, 2, 2, 1, 2, 1, 0] demoR1_0022102 demoR2_0022102 demoC_0022102 demoM_0022102

theorem demoR1_1022102 : invRung 7 5 20 [1, 0, 2, 2, 1, 0, 2] [1, 0, 2, 2, 1, 0, 2] 1 2 false = ([0, 0, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_1022102 : invRung 7 5 20 [1, 0, 2, 2, 1, 0, 2] [0, 0, 0, 2, 2, 1, 2] 3 1 true = ([2, 1, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_1022102 : fieldCube 7 5 20 [2, 1, 2, 1, 2, 0, 1] = [0, 0, 0, 1, 1, 1, 2] := by
  decide

theorem demoM_1022102 : fieldMul 7 5 20 [0, 0, 0, 1, 1, 1, 2] [1, 0, 2, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1022102 : mirrorTrits [0, 0, 0, 1, 1, 1, 2] = [0, 0, 0, 2, 2, 2, 1] := by
  decide

theorem demoInv_1022102 : specInv 7 5 20 [1, 0, 2, 2, 1, 0, 2] = some [0, 0, 0, 2, 2, 2, 1] :=
  specInv_mirror_7 [1, 0, 2, 2, 1, 0, 2] [0, 0, 0, 2, 2, 1, 2] [2, 1, 2, 1, 2, 0, 1] [0, 0, 0, 1, 1, 1, 2] [0, 0, 0, 2, 2, 2, 1] demoR1_1022102 demoR2_1022102 demoC_1022102 demoM_1022102 demoMir_1022102

theorem demoR1_2022102 : invRung 7 5 20 [2, 0, 2, 2, 1, 0, 2] [2, 0, 2, 2, 1, 0, 2] 1 2 false = ([1, 2, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2022102 : invRung 7 5 20 [2, 0, 2, 2, 1, 0, 2] [1, 2, 0, 2, 2, 0, 0] 3 1 true = ([0, 1, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_2022102 : fieldCube 7 5 20 [0, 1, 0, 1, 2, 0, 2] = [1, 1, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_2022102 : fieldMul 7 5 20 [1, 1, 2, 2, 2, 2, 1] [2, 0, 2, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022102 : mirrorTrits [1, 1, 2, 2, 2, 2, 1] = [2, 2, 1, 1, 1, 1, 2] := by
  decide

theorem demoInv_2022102 : specInv 7 5 20 [2, 0, 2, 2, 1, 0, 2] = some [2, 2, 1, 1, 1, 1, 2] :=
  specInv_mirror_7 [2, 0, 2, 2, 1, 0, 2] [1, 2, 0, 2, 2, 0, 0] [0, 1, 0, 1, 2, 0, 2] [1, 1, 2, 2, 2, 2, 1] [2, 2, 1, 1, 1, 1, 2] demoR1_2022102 demoR2_2022102 demoC_2022102 demoM_2022102 demoMir_2022102

theorem demoR1_0122102 : invRung 7 5 20 [0, 1, 2, 2, 1, 0, 2] [0, 1, 2, 2, 1, 0, 2] 1 2 false = ([2, 1, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_0122102 : invRung 7 5 20 [0, 1, 2, 2, 1, 0, 2] [2, 1, 1, 1, 1, 1, 0] 3 1 true = ([0, 2, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_0122102 : fieldCube 7 5 20 [0, 2, 2, 2, 1, 1, 0] = [0, 2, 0, 0, 1, 1, 2] := by
  decide

theorem demoM_0122102 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 1, 2] [0, 1, 2, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122102 : mirrorTrits [0, 2, 0, 0, 1, 1, 2] = [0, 1, 0, 0, 2, 2, 1] := by
  decide

theorem demoInv_0122102 : specInv 7 5 20 [0, 1, 2, 2, 1, 0, 2] = some [0, 1, 0, 0, 2, 2, 1] :=
  specInv_mirror_7 [0, 1, 2, 2, 1, 0, 2] [2, 1, 1, 1, 1, 1, 0] [0, 2, 2, 2, 1, 1, 0] [0, 2, 0, 0, 1, 1, 2] [0, 1, 0, 0, 2, 2, 1] demoR1_0122102 demoR2_0122102 demoC_0122102 demoM_0122102 demoMir_0122102

theorem demoR1_1122102 : invRung 7 5 20 [1, 1, 2, 2, 1, 0, 2] [1, 1, 2, 2, 1, 0, 2] 1 2 false = ([0, 2, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_1122102 : invRung 7 5 20 [1, 1, 2, 2, 1, 0, 2] [0, 2, 1, 0, 1, 0, 2] 3 1 true = ([2, 2, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_1122102 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 1, 2] = [0, 2, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_1122102 : fieldMul 7 5 20 [0, 2, 2, 0, 0, 2, 1] [1, 1, 2, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122102 : mirrorTrits [0, 2, 2, 0, 0, 2, 1] = [0, 1, 1, 0, 0, 1, 2] := by
  decide

theorem demoInv_1122102 : specInv 7 5 20 [1, 1, 2, 2, 1, 0, 2] = some [0, 1, 1, 0, 0, 1, 2] :=
  specInv_mirror_7 [1, 1, 2, 2, 1, 0, 2] [0, 2, 1, 0, 1, 0, 2] [2, 2, 1, 0, 2, 1, 2] [0, 2, 2, 0, 0, 2, 1] [0, 1, 1, 0, 0, 1, 2] demoR1_1122102 demoR2_1122102 demoC_1122102 demoM_1122102 demoMir_1122102

theorem demoR1_2122102 : invRung 7 5 20 [2, 1, 2, 2, 1, 0, 2] [2, 1, 2, 2, 1, 0, 2] 1 2 false = ([0, 2, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2122102 : invRung 7 5 20 [2, 1, 2, 2, 1, 0, 2] [0, 2, 1, 1, 0, 2, 1] 3 1 true = ([1, 1, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_2122102 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 2, 1] = [0, 1, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_2122102 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 1, 0] [2, 1, 2, 2, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2122102 : specInv 7 5 20 [2, 1, 2, 2, 1, 0, 2] = some [0, 1, 1, 0, 0, 1, 0] :=
  specInv_white_7 [2, 1, 2, 2, 1, 0, 2] [0, 2, 1, 1, 0, 2, 1] [1, 1, 0, 0, 1, 2, 1] [0, 1, 1, 0, 0, 1, 0] demoR1_2122102 demoR2_2122102 demoC_2122102 demoM_2122102

theorem demoR1_0222102 : invRung 7 5 20 [0, 2, 2, 2, 1, 0, 2] [0, 2, 2, 2, 1, 0, 2] 1 2 false = ([2, 1, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_0222102 : invRung 7 5 20 [0, 2, 2, 2, 1, 0, 2] [2, 1, 2, 2, 0, 2, 1] 3 1 true = ([2, 2, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_0222102 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 1, 1] = [2, 0, 2, 1, 2, 2, 0] := by
  decide

theorem demoM_0222102 : fieldMul 7 5 20 [2, 0, 2, 1, 2, 2, 0] [0, 2, 2, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222102 : mirrorTrits [2, 0, 2, 1, 2, 2, 0] = [1, 0, 1, 2, 1, 1, 0] := by
  decide

theorem demoInv_0222102 : specInv 7 5 20 [0, 2, 2, 2, 1, 0, 2] = some [1, 0, 1, 2, 1, 1, 0] :=
  specInv_mirror_7 [0, 2, 2, 2, 1, 0, 2] [2, 1, 2, 2, 0, 2, 1] [2, 2, 2, 2, 1, 1, 1] [2, 0, 2, 1, 2, 2, 0] [1, 0, 1, 2, 1, 1, 0] demoR1_0222102 demoR2_0222102 demoC_0222102 demoM_0222102 demoMir_0222102

theorem demoR1_1222102 : invRung 7 5 20 [1, 2, 2, 2, 1, 0, 2] [1, 2, 2, 2, 1, 0, 2] 1 2 false = ([0, 2, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_1222102 : invRung 7 5 20 [1, 2, 2, 2, 1, 0, 2] [0, 2, 0, 1, 1, 1, 2] 3 1 true = ([2, 1, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_1222102 : fieldCube 7 5 20 [2, 1, 0, 1, 1, 0, 0] = [0, 1, 1, 2, 0, 2, 1] := by
  decide

theorem demoM_1222102 : fieldMul 7 5 20 [0, 1, 1, 2, 0, 2, 1] [1, 2, 2, 2, 1, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1222102 : specInv 7 5 20 [1, 2, 2, 2, 1, 0, 2] = some [0, 1, 1, 2, 0, 2, 1] :=
  specInv_white_7 [1, 2, 2, 2, 1, 0, 2] [0, 2, 0, 1, 1, 1, 2] [2, 1, 0, 1, 1, 0, 0] [0, 1, 1, 2, 0, 2, 1] demoR1_1222102 demoR2_1222102 demoC_1222102 demoM_1222102

theorem demoR1_2222102 : invRung 7 5 20 [2, 2, 2, 2, 1, 0, 2] [2, 2, 2, 2, 1, 0, 2] 1 2 false = ([2, 1, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2222102 : invRung 7 5 20 [2, 2, 2, 2, 1, 0, 2] [2, 1, 0, 1, 1, 2, 0] 3 1 true = ([1, 2, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_2222102 : fieldCube 7 5 20 [1, 2, 0, 2, 0, 0, 1] = [0, 1, 1, 0, 1, 0, 1] := by
  decide

theorem demoM_2222102 : fieldMul 7 5 20 [0, 1, 1, 0, 1, 0, 1] [2, 2, 2, 2, 1, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222102 : mirrorTrits [0, 1, 1, 0, 1, 0, 1] = [0, 2, 2, 0, 2, 0, 2] := by
  decide

theorem demoInv_2222102 : specInv 7 5 20 [2, 2, 2, 2, 1, 0, 2] = some [0, 2, 2, 0, 2, 0, 2] :=
  specInv_mirror_7 [2, 2, 2, 2, 1, 0, 2] [2, 1, 0, 1, 1, 2, 0] [1, 2, 0, 2, 0, 0, 1] [0, 1, 1, 0, 1, 0, 1] [0, 2, 2, 0, 2, 0, 2] demoR1_2222102 demoR2_2222102 demoC_2222102 demoM_2222102 demoMir_2222102

theorem demoR1_0000202 : invRung 7 5 20 [0, 0, 0, 0, 2, 0, 2] [0, 0, 0, 0, 2, 0, 2] 1 2 false = ([1, 1, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_0000202 : invRung 7 5 20 [0, 0, 0, 0, 2, 0, 2] [1, 1, 2, 1, 0, 1, 2] 3 1 true = ([0, 1, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_0000202 : fieldCube 7 5 20 [0, 1, 2, 2, 2, 2, 2] = [1, 0, 2, 2, 1, 2, 1] := by
  decide

theorem demoM_0000202 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 2, 1] [0, 0, 0, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0000202 : specInv 7 5 20 [0, 0, 0, 0, 2, 0, 2] = some [1, 0, 2, 2, 1, 2, 1] :=
  specInv_white_7 [0, 0, 0, 0, 2, 0, 2] [1, 1, 2, 1, 0, 1, 2] [0, 1, 2, 2, 2, 2, 2] [1, 0, 2, 2, 1, 2, 1] demoR1_0000202 demoR2_0000202 demoC_0000202 demoM_0000202

theorem demoR1_1000202 : invRung 7 5 20 [1, 0, 0, 0, 2, 0, 2] [1, 0, 0, 0, 2, 0, 2] 1 2 false = ([0, 2, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_1000202 : invRung 7 5 20 [1, 0, 0, 0, 2, 0, 2] [0, 2, 2, 2, 1, 2, 2] 3 1 true = ([2, 2, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1000202 : fieldCube 7 5 20 [2, 2, 0, 0, 0, 1, 0] = [0, 1, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_1000202 : fieldMul 7 5 20 [0, 1, 1, 2, 1, 1, 2] [1, 0, 0, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000202 : mirrorTrits [0, 1, 1, 2, 1, 1, 2] = [0, 2, 2, 1, 2, 2, 1] := by
  decide

theorem demoInv_1000202 : specInv 7 5 20 [1, 0, 0, 0, 2, 0, 2] = some [0, 2, 2, 1, 2, 2, 1] :=
  specInv_mirror_7 [1, 0, 0, 0, 2, 0, 2] [0, 2, 2, 2, 1, 2, 2] [2, 2, 0, 0, 0, 1, 0] [0, 1, 1, 2, 1, 1, 2] [0, 2, 2, 1, 2, 2, 1] demoR1_1000202 demoR2_1000202 demoC_1000202 demoM_1000202 demoMir_1000202

theorem demoR1_2000202 : invRung 7 5 20 [2, 0, 0, 0, 2, 0, 2] [2, 0, 0, 0, 2, 0, 2] 1 2 false = ([0, 1, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_2000202 : invRung 7 5 20 [2, 0, 0, 0, 2, 0, 2] [0, 1, 0, 1, 2, 0, 2] 3 1 true = ([2, 1, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2000202 : fieldCube 7 5 20 [2, 1, 0, 1, 0, 2, 1] = [2, 0, 2, 2, 0, 1, 2] := by
  decide

theorem demoM_2000202 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 1, 2] [2, 0, 0, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2000202 : specInv 7 5 20 [2, 0, 0, 0, 2, 0, 2] = some [2, 0, 2, 2, 0, 1, 2] :=
  specInv_white_7 [2, 0, 0, 0, 2, 0, 2] [0, 1, 0, 1, 2, 0, 2] [2, 1, 0, 1, 0, 2, 1] [2, 0, 2, 2, 0, 1, 2] demoR1_2000202 demoR2_2000202 demoC_2000202 demoM_2000202

theorem demoR1_0100202 : invRung 7 5 20 [0, 1, 0, 0, 2, 0, 2] [0, 1, 0, 0, 2, 0, 2] 1 2 false = ([2, 1, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_0100202 : invRung 7 5 20 [0, 1, 0, 0, 2, 0, 2] [2, 1, 1, 2, 2, 1, 0] 3 1 true = ([0, 0, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_0100202 : fieldCube 7 5 20 [0, 0, 2, 2, 1, 1, 1] = [0, 0, 2, 2, 2, 2, 0] := by
  decide

theorem demoM_0100202 : fieldMul 7 5 20 [0, 0, 2, 2, 2, 2, 0] [0, 1, 0, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_0100202 : specInv 7 5 20 [0, 1, 0, 0, 2, 0, 2] = some [0, 0, 2, 2, 2, 2, 0] :=
  specInv_white_7 [0, 1, 0, 0, 2, 0, 2] [2, 1, 1, 2, 2, 1, 0] [0, 0, 2, 2, 1, 1, 1] [0, 0, 2, 2, 2, 2, 0] demoR1_0100202 demoR2_0100202 demoC_0100202 demoM_0100202

theorem demoR1_1100202 : invRung 7 5 20 [1, 1, 0, 0, 2, 0, 2] [1, 1, 0, 0, 2, 0, 2] 1 2 false = ([0, 0, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_1100202 : invRung 7 5 20 [1, 1, 0, 0, 2, 0, 2] [0, 0, 2, 1, 0, 0, 0] 3 1 true = ([2, 0, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_1100202 : fieldCube 7 5 20 [2, 0, 0, 2, 2, 0, 0] = [1, 2, 2, 2, 0, 1, 2] := by
  decide

theorem demoM_1100202 : fieldMul 7 5 20 [1, 2, 2, 2, 0, 1, 2] [1, 1, 0, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1100202 : specInv 7 5 20 [1, 1, 0, 0, 2, 0, 2] = some [1, 2, 2, 2, 0, 1, 2] :=
  specInv_white_7 [1, 1, 0, 0, 2, 0, 2] [0, 0, 2, 1, 0, 0, 0] [2, 0, 0, 2, 2, 0, 0] [1, 2, 2, 2, 0, 1, 2] demoR1_1100202 demoR2_1100202 demoC_1100202 demoM_1100202

theorem demoR1_2100202 : invRung 7 5 20 [2, 1, 0, 0, 2, 0, 2] [2, 1, 0, 0, 2, 0, 2] 1 2 false = ([1, 2, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_2100202 : invRung 7 5 20 [2, 1, 0, 0, 2, 0, 2] [1, 2, 0, 0, 1, 1, 0] 3 1 true = ([2, 0, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_2100202 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 0, 0] = [1, 0, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_2100202 : fieldMul 7 5 20 [1, 0, 2, 0, 0, 2, 1] [2, 1, 0, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100202 : mirrorTrits [1, 0, 2, 0, 0, 2, 1] = [2, 0, 1, 0, 0, 1, 2] := by
  decide

theorem demoInv_2100202 : specInv 7 5 20 [2, 1, 0, 0, 2, 0, 2] = some [2, 0, 1, 0, 0, 1, 2] :=
  specInv_mirror_7 [2, 1, 0, 0, 2, 0, 2] [1, 2, 0, 0, 1, 1, 0] [2, 0, 1, 2, 0, 0, 0] [1, 0, 2, 0, 0, 2, 1] [2, 0, 1, 0, 0, 1, 2] demoR1_2100202 demoR2_2100202 demoC_2100202 demoM_2100202 demoMir_2100202

theorem demoR1_0200202 : invRung 7 5 20 [0, 2, 0, 0, 2, 0, 2] [0, 2, 0, 0, 2, 0, 2] 1 2 false = ([1, 2, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_0200202 : invRung 7 5 20 [0, 2, 0, 0, 2, 0, 2] [1, 2, 0, 1, 0, 2, 2] 3 1 true = ([2, 1, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0200202 : fieldCube 7 5 20 [2, 1, 1, 2, 2, 0, 2] = [1, 1, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_0200202 : fieldMul 7 5 20 [1, 1, 0, 2, 2, 0, 2] [0, 2, 0, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200202 : mirrorTrits [1, 1, 0, 2, 2, 0, 2] = [2, 2, 0, 1, 1, 0, 1] := by
  decide

theorem demoInv_0200202 : specInv 7 5 20 [0, 2, 0, 0, 2, 0, 2] = some [2, 2, 0, 1, 1, 0, 1] :=
  specInv_mirror_7 [0, 2, 0, 0, 2, 0, 2] [1, 2, 0, 1, 0, 2, 2] [2, 1, 1, 2, 2, 0, 2] [1, 1, 0, 2, 2, 0, 2] [2, 2, 0, 1, 1, 0, 1] demoR1_0200202 demoR2_0200202 demoC_0200202 demoM_0200202 demoMir_0200202

theorem demoR1_1200202 : invRung 7 5 20 [1, 2, 0, 0, 2, 0, 2] [1, 2, 0, 0, 2, 0, 2] 1 2 false = ([1, 0, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_1200202 : invRung 7 5 20 [1, 2, 0, 0, 2, 0, 2] [1, 0, 2, 2, 0, 1, 0] 3 1 true = ([1, 1, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_1200202 : fieldCube 7 5 20 [1, 1, 1, 2, 2, 1, 1] = [1, 1, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_1200202 : fieldMul 7 5 20 [1, 1, 2, 1, 2, 0, 0] [1, 2, 0, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1200202 : specInv 7 5 20 [1, 2, 0, 0, 2, 0, 2] = some [1, 1, 2, 1, 2, 0, 0] :=
  specInv_white_7 [1, 2, 0, 0, 2, 0, 2] [1, 0, 2, 2, 0, 1, 0] [1, 1, 1, 2, 2, 1, 1] [1, 1, 2, 1, 2, 0, 0] demoR1_1200202 demoR2_1200202 demoC_1200202 demoM_1200202

theorem demoR1_2200202 : invRung 7 5 20 [2, 2, 0, 0, 2, 0, 2] [2, 2, 0, 0, 2, 0, 2] 1 2 false = ([0, 0, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_2200202 : invRung 7 5 20 [2, 2, 0, 0, 2, 0, 2] [0, 0, 0, 2, 0, 1, 1] 3 1 true = ([2, 0, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_2200202 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 0, 2] = [1, 2, 0, 2, 2, 1, 1] := by
  decide

theorem demoM_2200202 : fieldMul 7 5 20 [1, 2, 0, 2, 2, 1, 1] [2, 2, 0, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200202 : mirrorTrits [1, 2, 0, 2, 2, 1, 1] = [2, 1, 0, 1, 1, 2, 2] := by
  decide

theorem demoInv_2200202 : specInv 7 5 20 [2, 2, 0, 0, 2, 0, 2] = some [2, 1, 0, 1, 1, 2, 2] :=
  specInv_mirror_7 [2, 2, 0, 0, 2, 0, 2] [0, 0, 0, 2, 0, 1, 1] [2, 0, 2, 2, 0, 0, 2] [1, 2, 0, 2, 2, 1, 1] [2, 1, 0, 1, 1, 2, 2] demoR1_2200202 demoR2_2200202 demoC_2200202 demoM_2200202 demoMir_2200202

theorem demoR1_0010202 : invRung 7 5 20 [0, 0, 1, 0, 2, 0, 2] [0, 0, 1, 0, 2, 0, 2] 1 2 false = ([1, 2, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_0010202 : invRung 7 5 20 [0, 0, 1, 0, 2, 0, 2] [1, 2, 2, 0, 0, 0, 1] 3 1 true = ([2, 2, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0010202 : fieldCube 7 5 20 [2, 2, 0, 1, 1, 2, 0] = [2, 0, 0, 0, 2, 1, 2] := by
  decide

theorem demoM_0010202 : fieldMul 7 5 20 [2, 0, 0, 0, 2, 1, 2] [0, 0, 1, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010202 : mirrorTrits [2, 0, 0, 0, 2, 1, 2] = [1, 0, 0, 0, 1, 2, 1] := by
  decide

theorem demoInv_0010202 : specInv 7 5 20 [0, 0, 1, 0, 2, 0, 2] = some [1, 0, 0, 0, 1, 2, 1] :=
  specInv_mirror_7 [0, 0, 1, 0, 2, 0, 2] [1, 2, 2, 0, 0, 0, 1] [2, 2, 0, 1, 1, 2, 0] [2, 0, 0, 0, 2, 1, 2] [1, 0, 0, 0, 1, 2, 1] demoR1_0010202 demoR2_0010202 demoC_0010202 demoM_0010202 demoMir_0010202

theorem demoR1_1010202 : invRung 7 5 20 [1, 0, 1, 0, 2, 0, 2] [1, 0, 1, 0, 2, 0, 2] 1 2 false = ([0, 0, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_1010202 : invRung 7 5 20 [1, 0, 1, 0, 2, 0, 2] [0, 0, 2, 0, 2, 1, 0] 3 1 true = ([2, 2, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1010202 : fieldCube 7 5 20 [2, 2, 2, 0, 1, 1, 0] = [0, 2, 1, 0, 1, 2, 2] := by
  decide

theorem demoM_1010202 : fieldMul 7 5 20 [0, 2, 1, 0, 1, 2, 2] [1, 0, 1, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1010202 : mirrorTrits [0, 2, 1, 0, 1, 2, 2] = [0, 1, 2, 0, 2, 1, 1] := by
  decide

theorem demoInv_1010202 : specInv 7 5 20 [1, 0, 1, 0, 2, 0, 2] = some [0, 1, 2, 0, 2, 1, 1] :=
  specInv_mirror_7 [1, 0, 1, 0, 2, 0, 2] [0, 0, 2, 0, 2, 1, 0] [2, 2, 2, 0, 1, 1, 0] [0, 2, 1, 0, 1, 2, 2] [0, 1, 2, 0, 2, 1, 1] demoR1_1010202 demoR2_1010202 demoC_1010202 demoM_1010202 demoMir_1010202

theorem demoR1_2010202 : invRung 7 5 20 [2, 0, 1, 0, 2, 0, 2] [2, 0, 1, 0, 2, 0, 2] 1 2 false = ([0, 1, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2010202 : invRung 7 5 20 [2, 0, 1, 0, 2, 0, 2] [0, 1, 0, 0, 0, 1, 0] 3 1 true = ([1, 1, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_2010202 : fieldCube 7 5 20 [1, 1, 2, 0, 2, 0, 0] = [1, 2, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_2010202 : fieldMul 7 5 20 [1, 2, 0, 0, 0, 2, 1] [2, 0, 1, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2010202 : specInv 7 5 20 [2, 0, 1, 0, 2, 0, 2] = some [1, 2, 0, 0, 0, 2, 1] :=
  specInv_white_7 [2, 0, 1, 0, 2, 0, 2] [0, 1, 0, 0, 0, 1, 0] [1, 1, 2, 0, 2, 0, 0] [1, 2, 0, 0, 0, 2, 1] demoR1_2010202 demoR2_2010202 demoC_2010202 demoM_2010202

theorem demoR1_0110202 : invRung 7 5 20 [0, 1, 1, 0, 2, 0, 2] [0, 1, 1, 0, 2, 0, 2] 1 2 false = ([0, 1, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_0110202 : invRung 7 5 20 [0, 1, 1, 0, 2, 0, 2] [0, 1, 1, 0, 0, 0, 1] 3 1 true = ([0, 0, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0110202 : fieldCube 7 5 20 [0, 0, 0, 1, 1, 2, 0] = [0, 0, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_0110202 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 1, 2] [0, 1, 1, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110202 : mirrorTrits [0, 0, 0, 1, 2, 1, 2] = [0, 0, 0, 2, 1, 2, 1] := by
  decide

theorem demoInv_0110202 : specInv 7 5 20 [0, 1, 1, 0, 2, 0, 2] = some [0, 0, 0, 2, 1, 2, 1] :=
  specInv_mirror_7 [0, 1, 1, 0, 2, 0, 2] [0, 1, 1, 0, 0, 0, 1] [0, 0, 0, 1, 1, 2, 0] [0, 0, 0, 1, 2, 1, 2] [0, 0, 0, 2, 1, 2, 1] demoR1_0110202 demoR2_0110202 demoC_0110202 demoM_0110202 demoMir_0110202

theorem demoR1_1110202 : invRung 7 5 20 [1, 1, 1, 0, 2, 0, 2] [1, 1, 1, 0, 2, 0, 2] 1 2 false = ([1, 2, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_1110202 : invRung 7 5 20 [1, 1, 1, 0, 2, 0, 2] [1, 2, 0, 0, 0, 0, 2] 3 1 true = ([2, 0, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_1110202 : fieldCube 7 5 20 [2, 0, 2, 1, 1, 0, 0] = [0, 1, 1, 1, 0, 2, 0] := by
  decide

theorem demoM_1110202 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 2, 0] [1, 1, 1, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1110202 : specInv 7 5 20 [1, 1, 1, 0, 2, 0, 2] = some [0, 1, 1, 1, 0, 2, 0] :=
  specInv_white_7 [1, 1, 1, 0, 2, 0, 2] [1, 2, 0, 0, 0, 0, 2] [2, 0, 2, 1, 1, 0, 0] [0, 1, 1, 1, 0, 2, 0] demoR1_1110202 demoR2_1110202 demoC_1110202 demoM_1110202

theorem demoR1_2110202 : invRung 7 5 20 [2, 1, 1, 0, 2, 0, 2] [2, 1, 1, 0, 2, 0, 2] 1 2 false = ([2, 2, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_2110202 : invRung 7 5 20 [2, 1, 1, 0, 2, 0, 2] [2, 2, 2, 2, 2, 1, 1] 3 1 true = ([0, 2, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_2110202 : fieldCube 7 5 20 [0, 2, 0, 0, 0, 0, 1] = [0, 1, 2, 0, 1, 1, 1] := by
  decide

theorem demoM_2110202 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 1, 1] [2, 1, 1, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110202 : mirrorTrits [0, 1, 2, 0, 1, 1, 1] = [0, 2, 1, 0, 2, 2, 2] := by
  decide

theorem demoInv_2110202 : specInv 7 5 20 [2, 1, 1, 0, 2, 0, 2] = some [0, 2, 1, 0, 2, 2, 2] :=
  specInv_mirror_7 [2, 1, 1, 0, 2, 0, 2] [2, 2, 2, 2, 2, 1, 1] [0, 2, 0, 0, 0, 0, 1] [0, 1, 2, 0, 1, 1, 1] [0, 2, 1, 0, 2, 2, 2] demoR1_2110202 demoR2_2110202 demoC_2110202 demoM_2110202 demoMir_2110202

theorem demoR1_0210202 : invRung 7 5 20 [0, 2, 1, 0, 2, 0, 2] [0, 2, 1, 0, 2, 0, 2] 1 2 false = ([1, 0, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_0210202 : invRung 7 5 20 [0, 2, 1, 0, 2, 0, 2] [1, 0, 1, 1, 2, 2, 2] 3 1 true = ([0, 1, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0210202 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 2, 2] = [0, 2, 1, 1, 1, 0, 0] := by
  decide

theorem demoM_0210202 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 0, 0] [0, 2, 1, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210202 : mirrorTrits [0, 2, 1, 1, 1, 0, 0] = [0, 1, 2, 2, 2, 0, 0] := by
  decide

theorem demoInv_0210202 : specInv 7 5 20 [0, 2, 1, 0, 2, 0, 2] = some [0, 1, 2, 2, 2, 0, 0] :=
  specInv_mirror_7 [0, 2, 1, 0, 2, 0, 2] [1, 0, 1, 1, 2, 2, 2] [0, 1, 2, 1, 1, 2, 2] [0, 2, 1, 1, 1, 0, 0] [0, 1, 2, 2, 2, 0, 0] demoR1_0210202 demoR2_0210202 demoC_0210202 demoM_0210202 demoMir_0210202

theorem demoR1_1210202 : invRung 7 5 20 [1, 2, 1, 0, 2, 0, 2] [1, 2, 1, 0, 2, 0, 2] 1 2 false = ([1, 2, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_1210202 : invRung 7 5 20 [1, 2, 1, 0, 2, 0, 2] [1, 2, 2, 2, 2, 0, 0] 3 1 true = ([0, 1, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1210202 : fieldCube 7 5 20 [0, 1, 1, 0, 1, 1, 0] = [1, 2, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_1210202 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 2, 1] [1, 2, 1, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_1210202 : specInv 7 5 20 [1, 2, 1, 0, 2, 0, 2] = some [1, 2, 1, 2, 1, 2, 1] :=
  specInv_white_7 [1, 2, 1, 0, 2, 0, 2] [1, 2, 2, 2, 2, 0, 0] [0, 1, 1, 0, 1, 1, 0] [1, 2, 1, 2, 1, 2, 1] demoR1_1210202 demoR2_1210202 demoC_1210202 demoM_1210202

theorem demoR1_2210202 : invRung 7 5 20 [2, 2, 1, 0, 2, 0, 2] [2, 2, 1, 0, 2, 0, 2] 1 2 false = ([0, 2, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_2210202 : invRung 7 5 20 [2, 2, 1, 0, 2, 0, 2] [0, 2, 2, 1, 1, 1, 2] 3 1 true = ([0, 2, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2210202 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 1, 0] = [1, 2, 1, 0, 1, 2, 0] := by
  decide

theorem demoM_2210202 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 2, 0] [2, 2, 1, 0, 2, 0, 2] = whiteHole0 7 := by
  decide

theorem demoInv_2210202 : specInv 7 5 20 [2, 2, 1, 0, 2, 0, 2] = some [1, 2, 1, 0, 1, 2, 0] :=
  specInv_white_7 [2, 2, 1, 0, 2, 0, 2] [0, 2, 2, 1, 1, 1, 2] [0, 2, 0, 0, 1, 1, 0] [1, 2, 1, 0, 1, 2, 0] demoR1_2210202 demoR2_2210202 demoC_2210202 demoM_2210202

theorem demoR1_0020202 : invRung 7 5 20 [0, 0, 2, 0, 2, 0, 2] [0, 0, 2, 0, 2, 0, 2] 1 2 false = ([0, 2, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_0020202 : invRung 7 5 20 [0, 0, 2, 0, 2, 0, 2] [0, 2, 2, 2, 2, 2, 2] 3 1 true = ([2, 1, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0020202 : fieldCube 7 5 20 [2, 1, 1, 2, 1, 2, 1] = [0, 1, 0, 0, 0, 0, 1] := by
  decide

theorem demoM_0020202 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 0, 1] [0, 0, 2, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020202 : mirrorTrits [0, 1, 0, 0, 0, 0, 1] = [0, 2, 0, 0, 0, 0, 2] := by
  decide

theorem demoInv_0020202 : specInv 7 5 20 [0, 0, 2, 0, 2, 0, 2] = some [0, 2, 0, 0, 0, 0, 2] :=
  specInv_mirror_7 [0, 0, 2, 0, 2, 0, 2] [0, 2, 2, 2, 2, 2, 2] [2, 1, 1, 2, 1, 2, 1] [0, 1, 0, 0, 0, 0, 1] [0, 2, 0, 0, 0, 0, 2] demoR1_0020202 demoR2_0020202 demoC_0020202 demoM_0020202 demoMir_0020202

theorem demoR1_1020202 : invRung 7 5 20 [1, 0, 2, 0, 2, 0, 2] [1, 0, 2, 0, 2, 0, 2] 1 2 false = ([1, 0, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_1020202 : invRung 7 5 20 [1, 0, 2, 0, 2, 0, 2] [1, 0, 0, 1, 2, 0, 2] 3 1 true = ([2, 2, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_1020202 : fieldCube 7 5 20 [2, 2, 2, 1, 2, 2, 2] = [2, 0, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_1020202 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 1, 1] [1, 0, 2, 0, 2, 0, 2] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020202 : mirrorTrits [2, 0, 1, 0, 1, 1, 1] = [1, 0, 2, 0, 2, 2, 2] := by
  decide

theorem demoInv_1020202 : specInv 7 5 20 [1, 0, 2, 0, 2, 0, 2] = some [1, 0, 2, 0, 2, 2, 2] :=
  specInv_mirror_7 [1, 0, 2, 0, 2, 0, 2] [1, 0, 0, 1, 2, 0, 2] [2, 2, 2, 1, 2, 2, 2] [2, 0, 1, 0, 1, 1, 1] [1, 0, 2, 0, 2, 2, 2] demoR1_1020202 demoR2_1020202 demoC_1020202 demoM_1020202 demoMir_1020202

end EcbsLink2.Link2
