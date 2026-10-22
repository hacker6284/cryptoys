/-
  One quarter of Demo's nonzero trit lists. Each kernel `decide` is one rung,
  one cube, or one multiply.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldOk

namespace EcbsLink2.Link2

open EcbsLink2.Spec

theorem demoR1_1202020 : invRung 7 5 20 [1, 2, 0, 2, 0, 2, 0] [1, 2, 0, 2, 0, 2, 0] 1 2 false = ([2, 2, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_1202020 : invRung 7 5 20 [1, 2, 0, 2, 0, 2, 0] [2, 2, 0, 0, 1, 1, 1] 3 1 true = ([2, 2, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1202020 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 2, 0] = [2, 1, 0, 1, 2, 2, 0] := by
  decide

theorem demoM_1202020 : fieldMul 7 5 20 [2, 1, 0, 1, 2, 2, 0] [1, 2, 0, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1202020 : specInv 7 5 20 [1, 2, 0, 2, 0, 2, 0] = some [2, 1, 0, 1, 2, 2, 0] :=
  specInv_white_7 [1, 2, 0, 2, 0, 2, 0] [2, 2, 0, 0, 1, 1, 1] [2, 2, 0, 1, 2, 2, 0] [2, 1, 0, 1, 2, 2, 0] demoR1_1202020 demoR2_1202020 demoC_1202020 demoM_1202020

theorem demoR1_2202020 : invRung 7 5 20 [2, 2, 0, 2, 0, 2, 0] [2, 2, 0, 2, 0, 2, 0] 1 2 false = ([2, 1, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_2202020 : invRung 7 5 20 [2, 2, 0, 2, 0, 2, 0] [2, 1, 0, 2, 2, 0, 0] 3 1 true = ([2, 0, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_2202020 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 0, 1] = [1, 1, 1, 1, 1, 0, 0] := by
  decide

theorem demoM_2202020 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 0, 0] [2, 2, 0, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202020 : mirrorTrits [1, 1, 1, 1, 1, 0, 0] = [2, 2, 2, 2, 2, 0, 0] := by
  decide

theorem demoInv_2202020 : specInv 7 5 20 [2, 2, 0, 2, 0, 2, 0] = some [2, 2, 2, 2, 2, 0, 0] :=
  specInv_mirror_7 [2, 2, 0, 2, 0, 2, 0] [2, 1, 0, 2, 2, 0, 0] [2, 0, 2, 2, 0, 0, 1] [1, 1, 1, 1, 1, 0, 0] [2, 2, 2, 2, 2, 0, 0] demoR1_2202020 demoR2_2202020 demoC_2202020 demoM_2202020 demoMir_2202020

theorem demoR1_0012020 : invRung 7 5 20 [0, 0, 1, 2, 0, 2, 0] [0, 0, 1, 2, 0, 2, 0] 1 2 false = ([1, 1, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0012020 : invRung 7 5 20 [0, 0, 1, 2, 0, 2, 0] [1, 1, 0, 0, 1, 2, 1] 3 1 true = ([0, 0, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0012020 : fieldCube 7 5 20 [0, 0, 1, 1, 2, 1, 2] = [2, 2, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_0012020 : fieldMul 7 5 20 [2, 2, 0, 1, 0, 0, 1] [0, 0, 1, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0012020 : specInv 7 5 20 [0, 0, 1, 2, 0, 2, 0] = some [2, 2, 0, 1, 0, 0, 1] :=
  specInv_white_7 [0, 0, 1, 2, 0, 2, 0] [1, 1, 0, 0, 1, 2, 1] [0, 0, 1, 1, 2, 1, 2] [2, 2, 0, 1, 0, 0, 1] demoR1_0012020 demoR2_0012020 demoC_0012020 demoM_0012020

theorem demoR1_1012020 : invRung 7 5 20 [1, 0, 1, 2, 0, 2, 0] [1, 0, 1, 2, 0, 2, 0] 1 2 false = ([1, 1, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_1012020 : invRung 7 5 20 [1, 0, 1, 2, 0, 2, 0] [1, 1, 1, 0, 1, 2, 1] 3 1 true = ([2, 1, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_1012020 : fieldCube 7 5 20 [2, 1, 1, 2, 1, 1, 2] = [2, 1, 1, 1, 0, 0, 0] := by
  decide

theorem demoM_1012020 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 0, 0] [1, 0, 1, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1012020 : specInv 7 5 20 [1, 0, 1, 2, 0, 2, 0] = some [2, 1, 1, 1, 0, 0, 0] :=
  specInv_white_7 [1, 0, 1, 2, 0, 2, 0] [1, 1, 1, 0, 1, 2, 1] [2, 1, 1, 2, 1, 1, 2] [2, 1, 1, 1, 0, 0, 0] demoR1_1012020 demoR2_1012020 demoC_1012020 demoM_1012020

theorem demoR1_2012020 : invRung 7 5 20 [2, 0, 1, 2, 0, 2, 0] [2, 0, 1, 2, 0, 2, 0] 1 2 false = ([1, 0, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2012020 : invRung 7 5 20 [2, 0, 1, 2, 0, 2, 0] [1, 0, 1, 1, 2, 0, 1] 3 1 true = ([2, 0, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_2012020 : fieldCube 7 5 20 [2, 0, 0, 0, 2, 0, 2] = [2, 1, 1, 1, 2, 1, 1] := by
  decide

theorem demoM_2012020 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 1, 1] [2, 0, 1, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2012020 : specInv 7 5 20 [2, 0, 1, 2, 0, 2, 0] = some [2, 1, 1, 1, 2, 1, 1] :=
  specInv_white_7 [2, 0, 1, 2, 0, 2, 0] [1, 0, 1, 1, 2, 0, 1] [2, 0, 0, 0, 2, 0, 2] [2, 1, 1, 1, 2, 1, 1] demoR1_2012020 demoR2_2012020 demoC_2012020 demoM_2012020

theorem demoR1_0112020 : invRung 7 5 20 [0, 1, 1, 2, 0, 2, 0] [0, 1, 1, 2, 0, 2, 0] 1 2 false = ([0, 0, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_0112020 : invRung 7 5 20 [0, 1, 1, 2, 0, 2, 0] [0, 0, 2, 0, 0, 1, 2] 3 1 true = ([1, 1, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0112020 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 2, 2] = [0, 2, 0, 1, 1, 2, 2] := by
  decide

theorem demoM_0112020 : fieldMul 7 5 20 [0, 2, 0, 1, 1, 2, 2] [0, 1, 1, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0112020 : specInv 7 5 20 [0, 1, 1, 2, 0, 2, 0] = some [0, 2, 0, 1, 1, 2, 2] :=
  specInv_white_7 [0, 1, 1, 2, 0, 2, 0] [0, 0, 2, 0, 0, 1, 2] [1, 1, 1, 0, 1, 2, 2] [0, 2, 0, 1, 1, 2, 2] demoR1_0112020 demoR2_0112020 demoC_0112020 demoM_0112020

theorem demoR1_1112020 : invRung 7 5 20 [1, 1, 1, 2, 0, 2, 0] [1, 1, 1, 2, 0, 2, 0] 1 2 false = ([0, 1, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_1112020 : invRung 7 5 20 [1, 1, 1, 2, 0, 2, 0] [0, 1, 1, 0, 0, 0, 2] 3 1 true = ([2, 1, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1112020 : fieldCube 7 5 20 [2, 1, 2, 2, 0, 1, 0] = [2, 1, 0, 1, 1, 0, 1] := by
  decide

theorem demoM_1112020 : fieldMul 7 5 20 [2, 1, 0, 1, 1, 0, 1] [1, 1, 1, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112020 : mirrorTrits [2, 1, 0, 1, 1, 0, 1] = [1, 2, 0, 2, 2, 0, 2] := by
  decide

theorem demoInv_1112020 : specInv 7 5 20 [1, 1, 1, 2, 0, 2, 0] = some [1, 2, 0, 2, 2, 0, 2] :=
  specInv_mirror_7 [1, 1, 1, 2, 0, 2, 0] [0, 1, 1, 0, 0, 0, 2] [2, 1, 2, 2, 0, 1, 0] [2, 1, 0, 1, 1, 0, 1] [1, 2, 0, 2, 2, 0, 2] demoR1_1112020 demoR2_1112020 demoC_1112020 demoM_1112020 demoMir_1112020

theorem demoR1_2112020 : invRung 7 5 20 [2, 1, 1, 2, 0, 2, 0] [2, 1, 1, 2, 0, 2, 0] 1 2 false = ([2, 0, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_2112020 : invRung 7 5 20 [2, 1, 1, 2, 0, 2, 0] [2, 0, 1, 0, 1, 2, 2] 3 1 true = ([1, 1, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2112020 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 0, 0] = [1, 1, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_2112020 : fieldMul 7 5 20 [1, 1, 0, 2, 0, 1, 1] [2, 1, 1, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112020 : mirrorTrits [1, 1, 0, 2, 0, 1, 1] = [2, 2, 0, 1, 0, 2, 2] := by
  decide

theorem demoInv_2112020 : specInv 7 5 20 [2, 1, 1, 2, 0, 2, 0] = some [2, 2, 0, 1, 0, 2, 2] :=
  specInv_mirror_7 [2, 1, 1, 2, 0, 2, 0] [2, 0, 1, 0, 1, 2, 2] [1, 1, 0, 0, 1, 0, 0] [1, 1, 0, 2, 0, 1, 1] [2, 2, 0, 1, 0, 2, 2] demoR1_2112020 demoR2_2112020 demoC_2112020 demoM_2112020 demoMir_2112020

theorem demoR1_0212020 : invRung 7 5 20 [0, 2, 1, 2, 0, 2, 0] [0, 2, 1, 2, 0, 2, 0] 1 2 false = ([1, 2, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_0212020 : invRung 7 5 20 [0, 2, 1, 2, 0, 2, 0] [1, 2, 2, 2, 2, 0, 2] 3 1 true = ([1, 2, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0212020 : fieldCube 7 5 20 [1, 2, 0, 0, 2, 0, 1] = [1, 0, 2, 2, 1, 0, 0] := by
  decide

theorem demoM_0212020 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 0, 0] [0, 2, 1, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212020 : mirrorTrits [1, 0, 2, 2, 1, 0, 0] = [2, 0, 1, 1, 2, 0, 0] := by
  decide

theorem demoInv_0212020 : specInv 7 5 20 [0, 2, 1, 2, 0, 2, 0] = some [2, 0, 1, 1, 2, 0, 0] :=
  specInv_mirror_7 [0, 2, 1, 2, 0, 2, 0] [1, 2, 2, 2, 2, 0, 2] [1, 2, 0, 0, 2, 0, 1] [1, 0, 2, 2, 1, 0, 0] [2, 0, 1, 1, 2, 0, 0] demoR1_0212020 demoR2_0212020 demoC_0212020 demoM_0212020 demoMir_0212020

theorem demoR1_1212020 : invRung 7 5 20 [1, 2, 1, 2, 0, 2, 0] [1, 2, 1, 2, 0, 2, 0] 1 2 false = ([1, 2, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1212020 : invRung 7 5 20 [1, 2, 1, 2, 0, 2, 0] [1, 2, 2, 0, 1, 0, 0] 3 1 true = ([2, 0, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_1212020 : fieldCube 7 5 20 [2, 0, 0, 0, 0, 0, 1] = [2, 1, 2, 1, 1, 1, 1] := by
  decide

theorem demoM_1212020 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 1, 1] [1, 2, 1, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212020 : mirrorTrits [2, 1, 2, 1, 1, 1, 1] = [1, 2, 1, 2, 2, 2, 2] := by
  decide

theorem demoInv_1212020 : specInv 7 5 20 [1, 2, 1, 2, 0, 2, 0] = some [1, 2, 1, 2, 2, 2, 2] :=
  specInv_mirror_7 [1, 2, 1, 2, 0, 2, 0] [1, 2, 2, 0, 1, 0, 0] [2, 0, 0, 0, 0, 0, 1] [2, 1, 2, 1, 1, 1, 1] [1, 2, 1, 2, 2, 2, 2] demoR1_1212020 demoR2_1212020 demoC_1212020 demoM_1212020 demoMir_1212020

theorem demoR1_2212020 : invRung 7 5 20 [2, 2, 1, 2, 0, 2, 0] [2, 2, 1, 2, 0, 2, 0] 1 2 false = ([2, 2, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_2212020 : invRung 7 5 20 [2, 2, 1, 2, 0, 2, 0] [2, 2, 2, 0, 1, 2, 1] 3 1 true = ([2, 0, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2212020 : fieldCube 7 5 20 [2, 0, 1, 1, 2, 1, 0] = [1, 0, 2, 2, 1, 1, 2] := by
  decide

theorem demoM_2212020 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 1, 2] [2, 2, 1, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212020 : mirrorTrits [1, 0, 2, 2, 1, 1, 2] = [2, 0, 1, 1, 2, 2, 1] := by
  decide

theorem demoInv_2212020 : specInv 7 5 20 [2, 2, 1, 2, 0, 2, 0] = some [2, 0, 1, 1, 2, 2, 1] :=
  specInv_mirror_7 [2, 2, 1, 2, 0, 2, 0] [2, 2, 2, 0, 1, 2, 1] [2, 0, 1, 1, 2, 1, 0] [1, 0, 2, 2, 1, 1, 2] [2, 0, 1, 1, 2, 2, 1] demoR1_2212020 demoR2_2212020 demoC_2212020 demoM_2212020 demoMir_2212020

theorem demoR1_0022020 : invRung 7 5 20 [0, 0, 2, 2, 0, 2, 0] [0, 0, 2, 2, 0, 2, 0] 1 2 false = ([0, 0, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_0022020 : invRung 7 5 20 [0, 0, 2, 2, 0, 2, 0] [0, 0, 1, 2, 0, 2, 0] 3 1 true = ([0, 1, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0022020 : fieldCube 7 5 20 [0, 1, 2, 2, 0, 1, 1] = [0, 2, 2, 2, 2, 1, 2] := by
  decide

theorem demoM_0022020 : fieldMul 7 5 20 [0, 2, 2, 2, 2, 1, 2] [0, 0, 2, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0022020 : specInv 7 5 20 [0, 0, 2, 2, 0, 2, 0] = some [0, 2, 2, 2, 2, 1, 2] :=
  specInv_white_7 [0, 0, 2, 2, 0, 2, 0] [0, 0, 1, 2, 0, 2, 0] [0, 1, 2, 2, 0, 1, 1] [0, 2, 2, 2, 2, 1, 2] demoR1_0022020 demoR2_0022020 demoC_0022020 demoM_0022020

theorem demoR1_1022020 : invRung 7 5 20 [1, 0, 2, 2, 0, 2, 0] [1, 0, 2, 2, 0, 2, 0] 1 2 false = ([0, 1, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_1022020 : invRung 7 5 20 [1, 0, 2, 2, 0, 2, 0] [0, 1, 1, 0, 1, 1, 2] 3 1 true = ([1, 2, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_1022020 : fieldCube 7 5 20 [1, 2, 0, 2, 2, 0, 1] = [0, 0, 1, 2, 1, 2, 0] := by
  decide

theorem demoM_1022020 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 2, 0] [1, 0, 2, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1022020 : specInv 7 5 20 [1, 0, 2, 2, 0, 2, 0] = some [0, 0, 1, 2, 1, 2, 0] :=
  specInv_white_7 [1, 0, 2, 2, 0, 2, 0] [0, 1, 1, 0, 1, 1, 2] [1, 2, 0, 2, 2, 0, 1] [0, 0, 1, 2, 1, 2, 0] demoR1_1022020 demoR2_1022020 demoC_1022020 demoM_1022020

theorem demoR1_2022020 : invRung 7 5 20 [2, 0, 2, 2, 0, 2, 0] [2, 0, 2, 2, 0, 2, 0] 1 2 false = ([0, 0, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_2022020 : invRung 7 5 20 [2, 0, 2, 2, 0, 2, 0] [0, 0, 0, 1, 2, 0, 2] 3 1 true = ([2, 2, 1, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2022020 : fieldCube 7 5 20 [2, 2, 1, 1, 0, 1, 1] = [1, 2, 1, 0, 2, 0, 1] := by
  decide

theorem demoM_2022020 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 0, 1] [2, 0, 2, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2022020 : specInv 7 5 20 [2, 0, 2, 2, 0, 2, 0] = some [1, 2, 1, 0, 2, 0, 1] :=
  specInv_white_7 [2, 0, 2, 2, 0, 2, 0] [0, 0, 0, 1, 2, 0, 2] [2, 2, 1, 1, 0, 1, 1] [1, 2, 1, 0, 2, 0, 1] demoR1_2022020 demoR2_2022020 demoC_2022020 demoM_2022020

theorem demoR1_0122020 : invRung 7 5 20 [0, 1, 2, 2, 0, 2, 0] [0, 1, 2, 2, 0, 2, 0] 1 2 false = ([2, 0, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_0122020 : invRung 7 5 20 [0, 1, 2, 2, 0, 2, 0] [2, 0, 2, 0, 2, 0, 2] 3 1 true = ([0, 0, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0122020 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 2, 2] = [2, 2, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_0122020 : fieldMul 7 5 20 [2, 2, 0, 0, 1, 2, 1] [0, 1, 2, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0122020 : specInv 7 5 20 [0, 1, 2, 2, 0, 2, 0] = some [2, 2, 0, 0, 1, 2, 1] :=
  specInv_white_7 [0, 1, 2, 2, 0, 2, 0] [2, 0, 2, 0, 2, 0, 2] [0, 0, 0, 0, 1, 2, 2] [2, 2, 0, 0, 1, 2, 1] demoR1_0122020 demoR2_0122020 demoC_0122020 demoM_0122020

theorem demoR1_1122020 : invRung 7 5 20 [1, 1, 2, 2, 0, 2, 0] [1, 1, 2, 2, 0, 2, 0] 1 2 false = ([2, 1, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_1122020 : invRung 7 5 20 [1, 1, 2, 2, 0, 2, 0] [2, 1, 1, 0, 1, 2, 0] 3 1 true = ([1, 0, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_1122020 : fieldCube 7 5 20 [1, 0, 0, 2, 1, 1, 0] = [1, 2, 0, 1, 1, 1, 0] := by
  decide

theorem demoM_1122020 : fieldMul 7 5 20 [1, 2, 0, 1, 1, 1, 0] [1, 1, 2, 2, 0, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1122020 : specInv 7 5 20 [1, 1, 2, 2, 0, 2, 0] = some [1, 2, 0, 1, 1, 1, 0] :=
  specInv_white_7 [1, 1, 2, 2, 0, 2, 0] [2, 1, 1, 0, 1, 2, 0] [1, 0, 0, 2, 1, 1, 0] [1, 2, 0, 1, 1, 1, 0] demoR1_1122020 demoR2_1122020 demoC_1122020 demoM_1122020

theorem demoR1_2122020 : invRung 7 5 20 [2, 1, 2, 2, 0, 2, 0] [2, 1, 2, 2, 0, 2, 0] 1 2 false = ([1, 2, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2122020 : invRung 7 5 20 [2, 1, 2, 2, 0, 2, 0] [1, 2, 1, 2, 0, 0, 2] 3 1 true = ([0, 1, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2122020 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 2, 0] = [0, 2, 0, 1, 2, 0, 0] := by
  decide

theorem demoM_2122020 : fieldMul 7 5 20 [0, 2, 0, 1, 2, 0, 0] [2, 1, 2, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122020 : mirrorTrits [0, 2, 0, 1, 2, 0, 0] = [0, 1, 0, 2, 1, 0, 0] := by
  decide

theorem demoInv_2122020 : specInv 7 5 20 [2, 1, 2, 2, 0, 2, 0] = some [0, 1, 0, 2, 1, 0, 0] :=
  specInv_mirror_7 [2, 1, 2, 2, 0, 2, 0] [1, 2, 1, 2, 0, 0, 2] [0, 1, 2, 1, 0, 2, 0] [0, 2, 0, 1, 2, 0, 0] [0, 1, 0, 2, 1, 0, 0] demoR1_2122020 demoR2_2122020 demoC_2122020 demoM_2122020 demoMir_2122020

theorem demoR1_0222020 : invRung 7 5 20 [0, 2, 2, 2, 0, 2, 0] [0, 2, 2, 2, 0, 2, 0] 1 2 false = ([1, 2, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_0222020 : invRung 7 5 20 [0, 2, 2, 2, 0, 2, 0] [1, 2, 2, 0, 1, 2, 0] 3 1 true = ([2, 2, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_0222020 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 0, 0] = [0, 2, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_0222020 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 0, 2] [0, 2, 2, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222020 : mirrorTrits [0, 2, 1, 1, 0, 0, 2] = [0, 1, 2, 2, 0, 0, 1] := by
  decide

theorem demoInv_0222020 : specInv 7 5 20 [0, 2, 2, 2, 0, 2, 0] = some [0, 1, 2, 2, 0, 0, 1] :=
  specInv_mirror_7 [0, 2, 2, 2, 0, 2, 0] [1, 2, 2, 0, 1, 2, 0] [2, 2, 0, 1, 2, 0, 0] [0, 2, 1, 1, 0, 0, 2] [0, 1, 2, 2, 0, 0, 1] demoR1_0222020 demoR2_0222020 demoC_0222020 demoM_0222020 demoMir_0222020

theorem demoR1_1222020 : invRung 7 5 20 [1, 2, 2, 2, 0, 2, 0] [1, 2, 2, 2, 0, 2, 0] 1 2 false = ([1, 1, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_1222020 : invRung 7 5 20 [1, 2, 2, 2, 0, 2, 0] [1, 1, 0, 0, 0, 0, 1] 3 1 true = ([0, 1, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_1222020 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 2, 0] = [1, 1, 1, 0, 2, 0, 0] := by
  decide

theorem demoM_1222020 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 0, 0] [1, 2, 2, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222020 : mirrorTrits [1, 1, 1, 0, 2, 0, 0] = [2, 2, 2, 0, 1, 0, 0] := by
  decide

theorem demoInv_1222020 : specInv 7 5 20 [1, 2, 2, 2, 0, 2, 0] = some [2, 2, 2, 0, 1, 0, 0] :=
  specInv_mirror_7 [1, 2, 2, 2, 0, 2, 0] [1, 1, 0, 0, 0, 0, 1] [0, 1, 0, 2, 2, 2, 0] [1, 1, 1, 0, 2, 0, 0] [2, 2, 2, 0, 1, 0, 0] demoR1_1222020 demoR2_1222020 demoC_1222020 demoM_1222020 demoMir_1222020

theorem demoR1_2222020 : invRung 7 5 20 [2, 2, 2, 2, 0, 2, 0] [2, 2, 2, 2, 0, 2, 0] 1 2 false = ([2, 2, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_2222020 : invRung 7 5 20 [2, 2, 2, 2, 0, 2, 0] [2, 2, 1, 1, 2, 2, 0] 3 1 true = ([0, 1, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_2222020 : fieldCube 7 5 20 [0, 1, 2, 2, 0, 2, 0] = [1, 2, 1, 1, 2, 1, 0] := by
  decide

theorem demoM_2222020 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 1, 0] [2, 2, 2, 2, 0, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222020 : mirrorTrits [1, 2, 1, 1, 2, 1, 0] = [2, 1, 2, 2, 1, 2, 0] := by
  decide

theorem demoInv_2222020 : specInv 7 5 20 [2, 2, 2, 2, 0, 2, 0] = some [2, 1, 2, 2, 1, 2, 0] :=
  specInv_mirror_7 [2, 2, 2, 2, 0, 2, 0] [2, 2, 1, 1, 2, 2, 0] [0, 1, 2, 2, 0, 2, 0] [1, 2, 1, 1, 2, 1, 0] [2, 1, 2, 2, 1, 2, 0] demoR1_2222020 demoR2_2222020 demoC_2222020 demoM_2222020 demoMir_2222020

theorem demoR1_0000120 : invRung 7 5 20 [0, 0, 0, 0, 1, 2, 0] [0, 0, 0, 0, 1, 2, 0] 1 2 false = ([0, 1, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_0000120 : invRung 7 5 20 [0, 0, 0, 0, 1, 2, 0] [0, 1, 0, 2, 0, 2, 2] 3 1 true = ([0, 0, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0000120 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 1, 2] = [0, 1, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_0000120 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 0, 0] [0, 0, 0, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000120 : mirrorTrits [0, 1, 1, 0, 0, 0, 0] = [0, 2, 2, 0, 0, 0, 0] := by
  decide

theorem demoInv_0000120 : specInv 7 5 20 [0, 0, 0, 0, 1, 2, 0] = some [0, 2, 2, 0, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 0, 0, 1, 2, 0] [0, 1, 0, 2, 0, 2, 2] [0, 0, 1, 2, 1, 1, 2] [0, 1, 1, 0, 0, 0, 0] [0, 2, 2, 0, 0, 0, 0] demoR1_0000120 demoR2_0000120 demoC_0000120 demoM_0000120 demoMir_0000120

theorem demoR1_1000120 : invRung 7 5 20 [1, 0, 0, 0, 1, 2, 0] [1, 0, 0, 0, 1, 2, 0] 1 2 false = ([2, 2, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_1000120 : invRung 7 5 20 [1, 0, 0, 0, 1, 2, 0] [2, 2, 2, 0, 0, 2, 2] 3 1 true = ([2, 1, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_1000120 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 2, 1] = [2, 2, 2, 1, 0, 0, 2] := by
  decide

theorem demoM_1000120 : fieldMul 7 5 20 [2, 2, 2, 1, 0, 0, 2] [1, 0, 0, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000120 : mirrorTrits [2, 2, 2, 1, 0, 0, 2] = [1, 1, 1, 2, 0, 0, 1] := by
  decide

theorem demoInv_1000120 : specInv 7 5 20 [1, 0, 0, 0, 1, 2, 0] = some [1, 1, 1, 2, 0, 0, 1] :=
  specInv_mirror_7 [1, 0, 0, 0, 1, 2, 0] [2, 2, 2, 0, 0, 2, 2] [2, 1, 1, 1, 2, 2, 1] [2, 2, 2, 1, 0, 0, 2] [1, 1, 1, 2, 0, 0, 1] demoR1_1000120 demoR2_1000120 demoC_1000120 demoM_1000120 demoMir_1000120

theorem demoR1_2000120 : invRung 7 5 20 [2, 0, 0, 0, 1, 2, 0] [2, 0, 0, 0, 1, 2, 0] 1 2 false = ([2, 2, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_2000120 : invRung 7 5 20 [2, 0, 0, 0, 1, 2, 0] [2, 2, 0, 2, 1, 1, 0] 3 1 true = ([0, 0, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_2000120 : fieldCube 7 5 20 [0, 0, 0, 2, 0, 0, 1] = [2, 1, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_2000120 : fieldMul 7 5 20 [2, 1, 1, 1, 1, 0, 1] [2, 0, 0, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000120 : mirrorTrits [2, 1, 1, 1, 1, 0, 1] = [1, 2, 2, 2, 2, 0, 2] := by
  decide

theorem demoInv_2000120 : specInv 7 5 20 [2, 0, 0, 0, 1, 2, 0] = some [1, 2, 2, 2, 2, 0, 2] :=
  specInv_mirror_7 [2, 0, 0, 0, 1, 2, 0] [2, 2, 0, 2, 1, 1, 0] [0, 0, 0, 2, 0, 0, 1] [2, 1, 1, 1, 1, 0, 1] [1, 2, 2, 2, 2, 0, 2] demoR1_2000120 demoR2_2000120 demoC_2000120 demoM_2000120 demoMir_2000120

theorem demoR1_0100120 : invRung 7 5 20 [0, 1, 0, 0, 1, 2, 0] [0, 1, 0, 0, 1, 2, 0] 1 2 false = ([0, 0, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_0100120 : invRung 7 5 20 [0, 1, 0, 0, 1, 2, 0] [0, 0, 0, 0, 0, 0, 2] 3 1 true = ([2, 1, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0100120 : fieldCube 7 5 20 [2, 1, 2, 0, 0, 1, 1] = [0, 2, 0, 2, 2, 2, 2] := by
  decide

theorem demoM_0100120 : fieldMul 7 5 20 [0, 2, 0, 2, 2, 2, 2] [0, 1, 0, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100120 : mirrorTrits [0, 2, 0, 2, 2, 2, 2] = [0, 1, 0, 1, 1, 1, 1] := by
  decide

theorem demoInv_0100120 : specInv 7 5 20 [0, 1, 0, 0, 1, 2, 0] = some [0, 1, 0, 1, 1, 1, 1] :=
  specInv_mirror_7 [0, 1, 0, 0, 1, 2, 0] [0, 0, 0, 0, 0, 0, 2] [2, 1, 2, 0, 0, 1, 1] [0, 2, 0, 2, 2, 2, 2] [0, 1, 0, 1, 1, 1, 1] demoR1_0100120 demoR2_0100120 demoC_0100120 demoM_0100120 demoMir_0100120

theorem demoR1_1100120 : invRung 7 5 20 [1, 1, 0, 0, 1, 2, 0] [1, 1, 0, 0, 1, 2, 0] 1 2 false = ([1, 0, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_1100120 : invRung 7 5 20 [1, 1, 0, 0, 1, 2, 0] [1, 0, 1, 2, 2, 0, 0] 3 1 true = ([2, 0, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_1100120 : fieldCube 7 5 20 [2, 0, 0, 1, 1, 1, 0] = [1, 2, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_1100120 : fieldMul 7 5 20 [1, 2, 2, 1, 1, 0, 0] [1, 1, 0, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1100120 : mirrorTrits [1, 2, 2, 1, 1, 0, 0] = [2, 1, 1, 2, 2, 0, 0] := by
  decide

theorem demoInv_1100120 : specInv 7 5 20 [1, 1, 0, 0, 1, 2, 0] = some [2, 1, 1, 2, 2, 0, 0] :=
  specInv_mirror_7 [1, 1, 0, 0, 1, 2, 0] [1, 0, 1, 2, 2, 0, 0] [2, 0, 0, 1, 1, 1, 0] [1, 2, 2, 1, 1, 0, 0] [2, 1, 1, 2, 2, 0, 0] demoR1_1100120 demoR2_1100120 demoC_1100120 demoM_1100120 demoMir_1100120

theorem demoR1_2100120 : invRung 7 5 20 [2, 1, 0, 0, 1, 2, 0] [2, 1, 0, 0, 1, 2, 0] 1 2 false = ([2, 1, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_2100120 : invRung 7 5 20 [2, 1, 0, 0, 1, 2, 0] [2, 1, 0, 1, 2, 1, 2] 3 1 true = ([0, 2, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2100120 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 2, 1] = [0, 1, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_2100120 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 2, 1] [2, 1, 0, 0, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2100120 : specInv 7 5 20 [2, 1, 0, 0, 1, 2, 0] = some [0, 1, 2, 1, 0, 2, 1] :=
  specInv_white_7 [2, 1, 0, 0, 1, 2, 0] [2, 1, 0, 1, 2, 1, 2] [0, 2, 1, 1, 1, 2, 1] [0, 1, 2, 1, 0, 2, 1] demoR1_2100120 demoR2_2100120 demoC_2100120 demoM_2100120

theorem demoR1_0200120 : invRung 7 5 20 [0, 2, 0, 0, 1, 2, 0] [0, 2, 0, 0, 1, 2, 0] 1 2 false = ([1, 2, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0200120 : invRung 7 5 20 [0, 2, 0, 0, 1, 2, 0] [1, 2, 1, 2, 0, 0, 0] 3 1 true = ([1, 0, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_0200120 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 0, 1] = [2, 2, 0, 2, 1, 0, 0] := by
  decide

theorem demoM_0200120 : fieldMul 7 5 20 [2, 2, 0, 2, 1, 0, 0] [0, 2, 0, 0, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0200120 : specInv 7 5 20 [0, 2, 0, 0, 1, 2, 0] = some [2, 2, 0, 2, 1, 0, 0] :=
  specInv_white_7 [0, 2, 0, 0, 1, 2, 0] [1, 2, 1, 2, 0, 0, 0] [1, 0, 1, 1, 1, 0, 1] [2, 2, 0, 2, 1, 0, 0] demoR1_0200120 demoR2_0200120 demoC_0200120 demoM_0200120

theorem demoR1_1200120 : invRung 7 5 20 [1, 2, 0, 0, 1, 2, 0] [1, 2, 0, 0, 1, 2, 0] 1 2 false = ([1, 2, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1200120 : invRung 7 5 20 [1, 2, 0, 0, 1, 2, 0] [1, 2, 1, 0, 0, 2, 0] 3 1 true = ([2, 0, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_1200120 : fieldCube 7 5 20 [2, 0, 1, 1, 0, 2, 2] = [2, 1, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_1200120 : fieldMul 7 5 20 [2, 1, 1, 2, 1, 2, 1] [1, 2, 0, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200120 : mirrorTrits [2, 1, 1, 2, 1, 2, 1] = [1, 2, 2, 1, 2, 1, 2] := by
  decide

theorem demoInv_1200120 : specInv 7 5 20 [1, 2, 0, 0, 1, 2, 0] = some [1, 2, 2, 1, 2, 1, 2] :=
  specInv_mirror_7 [1, 2, 0, 0, 1, 2, 0] [1, 2, 1, 0, 0, 2, 0] [2, 0, 1, 1, 0, 2, 2] [2, 1, 1, 2, 1, 2, 1] [1, 2, 2, 1, 2, 1, 2] demoR1_1200120 demoR2_1200120 demoC_1200120 demoM_1200120 demoMir_1200120

theorem demoR1_2200120 : invRung 7 5 20 [2, 2, 0, 0, 1, 2, 0] [2, 2, 0, 0, 1, 2, 0] 1 2 false = ([0, 2, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_2200120 : invRung 7 5 20 [2, 2, 0, 0, 1, 2, 0] [0, 2, 1, 0, 1, 1, 1] 3 1 true = ([0, 1, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_2200120 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 2, 0] = [2, 2, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_2200120 : fieldMul 7 5 20 [2, 2, 2, 1, 2, 2, 2] [2, 2, 0, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200120 : mirrorTrits [2, 2, 2, 1, 2, 2, 2] = [1, 1, 1, 2, 1, 1, 1] := by
  decide

theorem demoInv_2200120 : specInv 7 5 20 [2, 2, 0, 0, 1, 2, 0] = some [1, 1, 1, 2, 1, 1, 1] :=
  specInv_mirror_7 [2, 2, 0, 0, 1, 2, 0] [0, 2, 1, 0, 1, 1, 1] [0, 1, 1, 0, 0, 2, 0] [2, 2, 2, 1, 2, 2, 2] [1, 1, 1, 2, 1, 1, 1] demoR1_2200120 demoR2_2200120 demoC_2200120 demoM_2200120 demoMir_2200120

theorem demoR1_0010120 : invRung 7 5 20 [0, 0, 1, 0, 1, 2, 0] [0, 0, 1, 0, 1, 2, 0] 1 2 false = ([0, 0, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0010120 : invRung 7 5 20 [0, 0, 1, 0, 1, 2, 0] [0, 0, 2, 1, 1, 1, 2] 3 1 true = ([1, 1, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_0010120 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 1, 0] = [2, 2, 1, 2, 1, 2, 0] := by
  decide

theorem demoM_0010120 : fieldMul 7 5 20 [2, 2, 1, 2, 1, 2, 0] [0, 0, 1, 0, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0010120 : specInv 7 5 20 [0, 0, 1, 0, 1, 2, 0] = some [2, 2, 1, 2, 1, 2, 0] :=
  specInv_white_7 [0, 0, 1, 0, 1, 2, 0] [0, 0, 2, 1, 1, 1, 2] [1, 1, 0, 0, 1, 1, 0] [2, 2, 1, 2, 1, 2, 0] demoR1_0010120 demoR2_0010120 demoC_0010120 demoM_0010120

theorem demoR1_1010120 : invRung 7 5 20 [1, 0, 1, 0, 1, 2, 0] [1, 0, 1, 0, 1, 2, 0] 1 2 false = ([2, 2, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_1010120 : invRung 7 5 20 [1, 0, 1, 0, 1, 2, 0] [2, 2, 2, 2, 0, 2, 2] 3 1 true = ([0, 2, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_1010120 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 0, 2] = [1, 0, 2, 2, 2, 1, 2] := by
  decide

theorem demoM_1010120 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 1, 2] [1, 0, 1, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1010120 : mirrorTrits [1, 0, 2, 2, 2, 1, 2] = [2, 0, 1, 1, 1, 2, 1] := by
  decide

theorem demoInv_1010120 : specInv 7 5 20 [1, 0, 1, 0, 1, 2, 0] = some [2, 0, 1, 1, 1, 2, 1] :=
  specInv_mirror_7 [1, 0, 1, 0, 1, 2, 0] [2, 2, 2, 2, 0, 2, 2] [0, 2, 2, 1, 1, 0, 2] [1, 0, 2, 2, 2, 1, 2] [2, 0, 1, 1, 1, 2, 1] demoR1_1010120 demoR2_1010120 demoC_1010120 demoM_1010120 demoMir_1010120

theorem demoR1_2010120 : invRung 7 5 20 [2, 0, 1, 0, 1, 2, 0] [2, 0, 1, 0, 1, 2, 0] 1 2 false = ([2, 2, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_2010120 : invRung 7 5 20 [2, 0, 1, 0, 1, 2, 0] [2, 2, 1, 0, 2, 1, 1] 3 1 true = ([1, 1, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2010120 : fieldCube 7 5 20 [1, 1, 2, 2, 1, 2, 2] = [2, 2, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_2010120 : fieldMul 7 5 20 [2, 2, 2, 1, 1, 1, 0] [2, 0, 1, 0, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2010120 : specInv 7 5 20 [2, 0, 1, 0, 1, 2, 0] = some [2, 2, 2, 1, 1, 1, 0] :=
  specInv_white_7 [2, 0, 1, 0, 1, 2, 0] [2, 2, 1, 0, 2, 1, 1] [1, 1, 2, 2, 1, 2, 2] [2, 2, 2, 1, 1, 1, 0] demoR1_2010120 demoR2_2010120 demoC_2010120 demoM_2010120

theorem demoR1_0110120 : invRung 7 5 20 [0, 1, 1, 0, 1, 2, 0] [0, 1, 1, 0, 1, 2, 0] 1 2 false = ([1, 0, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_0110120 : invRung 7 5 20 [0, 1, 1, 0, 1, 2, 0] [1, 0, 2, 0, 0, 0, 1] 3 1 true = ([1, 2, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_0110120 : fieldCube 7 5 20 [1, 2, 2, 0, 1, 1, 1] = [2, 0, 0, 1, 2, 0, 0] := by
  decide

theorem demoM_0110120 : fieldMul 7 5 20 [2, 0, 0, 1, 2, 0, 0] [0, 1, 1, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110120 : mirrorTrits [2, 0, 0, 1, 2, 0, 0] = [1, 0, 0, 2, 1, 0, 0] := by
  decide

theorem demoInv_0110120 : specInv 7 5 20 [0, 1, 1, 0, 1, 2, 0] = some [1, 0, 0, 2, 1, 0, 0] :=
  specInv_mirror_7 [0, 1, 1, 0, 1, 2, 0] [1, 0, 2, 0, 0, 0, 1] [1, 2, 2, 0, 1, 1, 1] [2, 0, 0, 1, 2, 0, 0] [1, 0, 0, 2, 1, 0, 0] demoR1_0110120 demoR2_0110120 demoC_0110120 demoM_0110120 demoMir_0110120

theorem demoR1_1110120 : invRung 7 5 20 [1, 1, 1, 0, 1, 2, 0] [1, 1, 1, 0, 1, 2, 0] 1 2 false = ([2, 0, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1110120 : invRung 7 5 20 [1, 1, 1, 0, 1, 2, 0] [2, 0, 2, 1, 2, 2, 1] 3 1 true = ([0, 0, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_1110120 : fieldCube 7 5 20 [0, 0, 2, 1, 1, 0, 2] = [1, 0, 2, 0, 2, 1, 2] := by
  decide

theorem demoM_1110120 : fieldMul 7 5 20 [1, 0, 2, 0, 2, 1, 2] [1, 1, 1, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1110120 : mirrorTrits [1, 0, 2, 0, 2, 1, 2] = [2, 0, 1, 0, 1, 2, 1] := by
  decide

theorem demoInv_1110120 : specInv 7 5 20 [1, 1, 1, 0, 1, 2, 0] = some [2, 0, 1, 0, 1, 2, 1] :=
  specInv_mirror_7 [1, 1, 1, 0, 1, 2, 0] [2, 0, 2, 1, 2, 2, 1] [0, 0, 2, 1, 1, 0, 2] [1, 0, 2, 0, 2, 1, 2] [2, 0, 1, 0, 1, 2, 1] demoR1_1110120 demoR2_1110120 demoC_1110120 demoM_1110120 demoMir_1110120

theorem demoR1_2110120 : invRung 7 5 20 [2, 1, 1, 0, 1, 2, 0] [2, 1, 1, 0, 1, 2, 0] 1 2 false = ([0, 0, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_2110120 : invRung 7 5 20 [2, 1, 1, 0, 1, 2, 0] [0, 0, 0, 1, 1, 1, 0] 3 1 true = ([1, 0, 2, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_2110120 : fieldCube 7 5 20 [1, 0, 2, 0, 0, 1, 2] = [2, 0, 2, 2, 0, 0, 0] := by
  decide

theorem demoM_2110120 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 0, 0] [2, 1, 1, 0, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2110120 : specInv 7 5 20 [2, 1, 1, 0, 1, 2, 0] = some [2, 0, 2, 2, 0, 0, 0] :=
  specInv_white_7 [2, 1, 1, 0, 1, 2, 0] [0, 0, 0, 1, 1, 1, 0] [1, 0, 2, 0, 0, 1, 2] [2, 0, 2, 2, 0, 0, 0] demoR1_2110120 demoR2_2110120 demoC_2110120 demoM_2110120

theorem demoR1_0210120 : invRung 7 5 20 [0, 2, 1, 0, 1, 2, 0] [0, 2, 1, 0, 1, 2, 0] 1 2 false = ([1, 2, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_0210120 : invRung 7 5 20 [0, 2, 1, 0, 1, 2, 0] [1, 2, 1, 0, 2, 2, 1] 3 1 true = ([1, 1, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_0210120 : fieldCube 7 5 20 [1, 1, 1, 0, 1, 1, 0] = [2, 2, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_0210120 : fieldMul 7 5 20 [2, 2, 1, 2, 1, 2, 1] [0, 2, 1, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210120 : mirrorTrits [2, 2, 1, 2, 1, 2, 1] = [1, 1, 2, 1, 2, 1, 2] := by
  decide

theorem demoInv_0210120 : specInv 7 5 20 [0, 2, 1, 0, 1, 2, 0] = some [1, 1, 2, 1, 2, 1, 2] :=
  specInv_mirror_7 [0, 2, 1, 0, 1, 2, 0] [1, 2, 1, 0, 2, 2, 1] [1, 1, 1, 0, 1, 1, 0] [2, 2, 1, 2, 1, 2, 1] [1, 1, 2, 1, 2, 1, 2] demoR1_0210120 demoR2_0210120 demoC_0210120 demoM_0210120 demoMir_0210120

theorem demoR1_1210120 : invRung 7 5 20 [1, 2, 1, 0, 1, 2, 0] [1, 2, 1, 0, 1, 2, 0] 1 2 false = ([1, 1, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1210120 : invRung 7 5 20 [1, 2, 1, 0, 1, 2, 0] [1, 1, 1, 2, 0, 1, 2] 3 1 true = ([0, 2, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_1210120 : fieldCube 7 5 20 [0, 2, 2, 1, 0, 1, 1] = [2, 2, 1, 0, 2, 0, 2] := by
  decide

theorem demoM_1210120 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 0, 2] [1, 2, 1, 0, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1210120 : specInv 7 5 20 [1, 2, 1, 0, 1, 2, 0] = some [2, 2, 1, 0, 2, 0, 2] :=
  specInv_white_7 [1, 2, 1, 0, 1, 2, 0] [1, 1, 1, 2, 0, 1, 2] [0, 2, 2, 1, 0, 1, 1] [2, 2, 1, 0, 2, 0, 2] demoR1_1210120 demoR2_1210120 demoC_1210120 demoM_1210120

theorem demoR1_2210120 : invRung 7 5 20 [2, 2, 1, 0, 1, 2, 0] [2, 2, 1, 0, 1, 2, 0] 1 2 false = ([0, 2, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_2210120 : invRung 7 5 20 [2, 2, 1, 0, 1, 2, 0] [0, 2, 1, 2, 1, 2, 2] 3 1 true = ([2, 2, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_2210120 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 1, 1] = [2, 1, 2, 2, 2, 0, 0] := by
  decide

theorem demoM_2210120 : fieldMul 7 5 20 [2, 1, 2, 2, 2, 0, 0] [2, 2, 1, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210120 : mirrorTrits [2, 1, 2, 2, 2, 0, 0] = [1, 2, 1, 1, 1, 0, 0] := by
  decide

theorem demoInv_2210120 : specInv 7 5 20 [2, 2, 1, 0, 1, 2, 0] = some [1, 2, 1, 1, 1, 0, 0] :=
  specInv_mirror_7 [2, 2, 1, 0, 1, 2, 0] [0, 2, 1, 2, 1, 2, 2] [2, 2, 1, 2, 2, 1, 1] [2, 1, 2, 2, 2, 0, 0] [1, 2, 1, 1, 1, 0, 0] demoR1_2210120 demoR2_2210120 demoC_2210120 demoM_2210120 demoMir_2210120

theorem demoR1_0020120 : invRung 7 5 20 [0, 0, 2, 0, 1, 2, 0] [0, 0, 2, 0, 1, 2, 0] 1 2 false = ([0, 2, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_0020120 : invRung 7 5 20 [0, 0, 2, 0, 1, 2, 0] [0, 2, 2, 0, 1, 2, 2] 3 1 true = ([2, 0, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0020120 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 1, 2] = [2, 1, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_0020120 : fieldMul 7 5 20 [2, 1, 1, 0, 0, 0, 1] [0, 0, 2, 0, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0020120 : specInv 7 5 20 [0, 0, 2, 0, 1, 2, 0] = some [2, 1, 1, 0, 0, 0, 1] :=
  specInv_white_7 [0, 0, 2, 0, 1, 2, 0] [0, 2, 2, 0, 1, 2, 2] [2, 0, 2, 2, 1, 1, 2] [2, 1, 1, 0, 0, 0, 1] demoR1_0020120 demoR2_0020120 demoC_0020120 demoM_0020120

theorem demoR1_1020120 : invRung 7 5 20 [1, 0, 2, 0, 1, 2, 0] [1, 0, 2, 0, 1, 2, 0] 1 2 false = ([1, 2, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_1020120 : invRung 7 5 20 [1, 0, 2, 0, 1, 2, 0] [1, 2, 1, 1, 2, 1, 1] 3 1 true = ([0, 0, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_1020120 : fieldCube 7 5 20 [0, 0, 1, 1, 2, 0, 0] = [1, 2, 1, 2, 0, 0, 0] := by
  decide

theorem demoM_1020120 : fieldMul 7 5 20 [1, 2, 1, 2, 0, 0, 0] [1, 0, 2, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020120 : mirrorTrits [1, 2, 1, 2, 0, 0, 0] = [2, 1, 2, 1, 0, 0, 0] := by
  decide

theorem demoInv_1020120 : specInv 7 5 20 [1, 0, 2, 0, 1, 2, 0] = some [2, 1, 2, 1, 0, 0, 0] :=
  specInv_mirror_7 [1, 0, 2, 0, 1, 2, 0] [1, 2, 1, 1, 2, 1, 1] [0, 0, 1, 1, 2, 0, 0] [1, 2, 1, 2, 0, 0, 0] [2, 1, 2, 1, 0, 0, 0] demoR1_1020120 demoR2_1020120 demoC_1020120 demoM_1020120 demoMir_1020120

theorem demoR1_2020120 : invRung 7 5 20 [2, 0, 2, 0, 1, 2, 0] [2, 0, 2, 0, 1, 2, 0] 1 2 false = ([0, 2, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_2020120 : invRung 7 5 20 [2, 0, 2, 0, 1, 2, 0] [0, 2, 2, 1, 2, 0, 0] 3 1 true = ([2, 1, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_2020120 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 1, 0] = [1, 1, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_2020120 : fieldMul 7 5 20 [1, 1, 2, 1, 1, 2, 1] [2, 0, 2, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020120 : mirrorTrits [1, 1, 2, 1, 1, 2, 1] = [2, 2, 1, 2, 2, 1, 2] := by
  decide

theorem demoInv_2020120 : specInv 7 5 20 [2, 0, 2, 0, 1, 2, 0] = some [2, 2, 1, 2, 2, 1, 2] :=
  specInv_mirror_7 [2, 0, 2, 0, 1, 2, 0] [0, 2, 2, 1, 2, 0, 0] [2, 1, 2, 1, 0, 1, 0] [1, 1, 2, 1, 1, 2, 1] [2, 2, 1, 2, 2, 1, 2] demoR1_2020120 demoR2_2020120 demoC_2020120 demoM_2020120 demoMir_2020120

theorem demoR1_0120120 : invRung 7 5 20 [0, 1, 2, 0, 1, 2, 0] [0, 1, 2, 0, 1, 2, 0] 1 2 false = ([2, 2, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_0120120 : invRung 7 5 20 [0, 1, 2, 0, 1, 2, 0] [2, 2, 1, 2, 1, 1, 2] 3 1 true = ([1, 2, 1, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0120120 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 0, 1] = [1, 0, 2, 2, 1, 0, 1] := by
  decide

theorem demoM_0120120 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 0, 1] [0, 1, 2, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0120120 : mirrorTrits [1, 0, 2, 2, 1, 0, 1] = [2, 0, 1, 1, 2, 0, 2] := by
  decide

theorem demoInv_0120120 : specInv 7 5 20 [0, 1, 2, 0, 1, 2, 0] = some [2, 0, 1, 1, 2, 0, 2] :=
  specInv_mirror_7 [0, 1, 2, 0, 1, 2, 0] [2, 2, 1, 2, 1, 1, 2] [1, 2, 1, 0, 2, 0, 1] [1, 0, 2, 2, 1, 0, 1] [2, 0, 1, 1, 2, 0, 2] demoR1_0120120 demoR2_0120120 demoC_0120120 demoM_0120120 demoMir_0120120

theorem demoR1_1120120 : invRung 7 5 20 [1, 1, 2, 0, 1, 2, 0] [1, 1, 2, 0, 1, 2, 0] 1 2 false = ([2, 2, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_1120120 : invRung 7 5 20 [1, 1, 2, 0, 1, 2, 0] [2, 2, 1, 2, 0, 2, 0] 3 1 true = ([0, 0, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_1120120 : fieldCube 7 5 20 [0, 0, 1, 2, 1, 2, 0] = [1, 0, 1, 1, 2, 2, 0] := by
  decide

theorem demoM_1120120 : fieldMul 7 5 20 [1, 0, 1, 1, 2, 2, 0] [1, 1, 2, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120120 : mirrorTrits [1, 0, 1, 1, 2, 2, 0] = [2, 0, 2, 2, 1, 1, 0] := by
  decide

theorem demoInv_1120120 : specInv 7 5 20 [1, 1, 2, 0, 1, 2, 0] = some [2, 0, 2, 2, 1, 1, 0] :=
  specInv_mirror_7 [1, 1, 2, 0, 1, 2, 0] [2, 2, 1, 2, 0, 2, 0] [0, 0, 1, 2, 1, 2, 0] [1, 0, 1, 1, 2, 2, 0] [2, 0, 2, 2, 1, 1, 0] demoR1_1120120 demoR2_1120120 demoC_1120120 demoM_1120120 demoMir_1120120

theorem demoR1_2120120 : invRung 7 5 20 [2, 1, 2, 0, 1, 2, 0] [2, 1, 2, 0, 1, 2, 0] 1 2 false = ([2, 1, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_2120120 : invRung 7 5 20 [2, 1, 2, 0, 1, 2, 0] [2, 1, 2, 0, 1, 2, 1] 3 1 true = ([0, 2, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_2120120 : fieldCube 7 5 20 [0, 2, 2, 2, 2, 1, 2] = [0, 2, 1, 0, 0, 1, 2] := by
  decide

theorem demoM_2120120 : fieldMul 7 5 20 [0, 2, 1, 0, 0, 1, 2] [2, 1, 2, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120120 : mirrorTrits [0, 2, 1, 0, 0, 1, 2] = [0, 1, 2, 0, 0, 2, 1] := by
  decide

theorem demoInv_2120120 : specInv 7 5 20 [2, 1, 2, 0, 1, 2, 0] = some [0, 1, 2, 0, 0, 2, 1] :=
  specInv_mirror_7 [2, 1, 2, 0, 1, 2, 0] [2, 1, 2, 0, 1, 2, 1] [0, 2, 2, 2, 2, 1, 2] [0, 2, 1, 0, 0, 1, 2] [0, 1, 2, 0, 0, 2, 1] demoR1_2120120 demoR2_2120120 demoC_2120120 demoM_2120120 demoMir_2120120

theorem demoR1_0220120 : invRung 7 5 20 [0, 2, 2, 0, 1, 2, 0] [0, 2, 2, 0, 1, 2, 0] 1 2 false = ([1, 0, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_0220120 : invRung 7 5 20 [0, 2, 2, 0, 1, 2, 0] [1, 0, 0, 2, 1, 1, 0] 3 1 true = ([1, 1, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0220120 : fieldCube 7 5 20 [1, 1, 1, 1, 2, 0, 1] = [2, 0, 0, 1, 1, 1, 1] := by
  decide

theorem demoM_0220120 : fieldMul 7 5 20 [2, 0, 0, 1, 1, 1, 1] [0, 2, 2, 0, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0220120 : specInv 7 5 20 [0, 2, 2, 0, 1, 2, 0] = some [2, 0, 0, 1, 1, 1, 1] :=
  specInv_white_7 [0, 2, 2, 0, 1, 2, 0] [1, 0, 0, 2, 1, 1, 0] [1, 1, 1, 1, 2, 0, 1] [2, 0, 0, 1, 1, 1, 1] demoR1_0220120 demoR2_0220120 demoC_0220120 demoM_0220120

theorem demoR1_1220120 : invRung 7 5 20 [1, 2, 2, 0, 1, 2, 0] [1, 2, 2, 0, 1, 2, 0] 1 2 false = ([0, 1, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1220120 : invRung 7 5 20 [1, 2, 2, 0, 1, 2, 0] [0, 1, 1, 2, 0, 0, 1] 3 1 true = ([2, 2, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_1220120 : fieldCube 7 5 20 [2, 2, 2, 1, 0, 1, 2] = [1, 0, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_1220120 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 1, 0] [1, 2, 2, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220120 : mirrorTrits [1, 0, 0, 1, 0, 1, 0] = [2, 0, 0, 2, 0, 2, 0] := by
  decide

theorem demoInv_1220120 : specInv 7 5 20 [1, 2, 2, 0, 1, 2, 0] = some [2, 0, 0, 2, 0, 2, 0] :=
  specInv_mirror_7 [1, 2, 2, 0, 1, 2, 0] [0, 1, 1, 2, 0, 0, 1] [2, 2, 2, 1, 0, 1, 2] [1, 0, 0, 1, 0, 1, 0] [2, 0, 0, 2, 0, 2, 0] demoR1_1220120 demoR2_1220120 demoC_1220120 demoM_1220120 demoMir_1220120

theorem demoR1_2220120 : invRung 7 5 20 [2, 2, 2, 0, 1, 2, 0] [2, 2, 2, 0, 1, 2, 0] 1 2 false = ([1, 0, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_2220120 : invRung 7 5 20 [2, 2, 2, 0, 1, 2, 0] [1, 0, 2, 2, 1, 0, 2] 3 1 true = ([0, 0, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2220120 : fieldCube 7 5 20 [0, 0, 2, 1, 2, 2, 0] = [0, 1, 0, 2, 2, 2, 2] := by
  decide

theorem demoM_2220120 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 2, 2] [2, 2, 2, 0, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220120 : mirrorTrits [0, 1, 0, 2, 2, 2, 2] = [0, 2, 0, 1, 1, 1, 1] := by
  decide

theorem demoInv_2220120 : specInv 7 5 20 [2, 2, 2, 0, 1, 2, 0] = some [0, 2, 0, 1, 1, 1, 1] :=
  specInv_mirror_7 [2, 2, 2, 0, 1, 2, 0] [1, 0, 2, 2, 1, 0, 2] [0, 0, 2, 1, 2, 2, 0] [0, 1, 0, 2, 2, 2, 2] [0, 2, 0, 1, 1, 1, 1] demoR1_2220120 demoR2_2220120 demoC_2220120 demoM_2220120 demoMir_2220120

theorem demoR1_0001120 : invRung 7 5 20 [0, 0, 0, 1, 1, 2, 0] [0, 0, 0, 1, 1, 2, 0] 1 2 false = ([2, 0, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_0001120 : invRung 7 5 20 [0, 0, 0, 1, 1, 2, 0] [2, 0, 2, 2, 1, 0, 0] 3 1 true = ([2, 2, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0001120 : fieldCube 7 5 20 [2, 2, 1, 2, 1, 0, 1] = [1, 2, 1, 1, 1, 1, 0] := by
  decide

theorem demoM_0001120 : fieldMul 7 5 20 [1, 2, 1, 1, 1, 1, 0] [0, 0, 0, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0001120 : specInv 7 5 20 [0, 0, 0, 1, 1, 2, 0] = some [1, 2, 1, 1, 1, 1, 0] :=
  specInv_white_7 [0, 0, 0, 1, 1, 2, 0] [2, 0, 2, 2, 1, 0, 0] [2, 2, 1, 2, 1, 0, 1] [1, 2, 1, 1, 1, 1, 0] demoR1_0001120 demoR2_0001120 demoC_0001120 demoM_0001120

theorem demoR1_1001120 : invRung 7 5 20 [1, 0, 0, 1, 1, 2, 0] [1, 0, 0, 1, 1, 2, 0] 1 2 false = ([1, 2, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_1001120 : invRung 7 5 20 [1, 0, 0, 1, 1, 2, 0] [1, 2, 0, 1, 0, 2, 0] 3 1 true = ([0, 1, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_1001120 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 2, 1] = [1, 1, 0, 0, 0, 0, 2] := by
  decide

theorem demoM_1001120 : fieldMul 7 5 20 [1, 1, 0, 0, 0, 0, 2] [1, 0, 0, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1001120 : specInv 7 5 20 [1, 0, 0, 1, 1, 2, 0] = some [1, 1, 0, 0, 0, 0, 2] :=
  specInv_white_7 [1, 0, 0, 1, 1, 2, 0] [1, 2, 0, 1, 0, 2, 0] [0, 1, 2, 2, 1, 2, 1] [1, 1, 0, 0, 0, 0, 2] demoR1_1001120 demoR2_1001120 demoC_1001120 demoM_1001120

theorem demoR1_2001120 : invRung 7 5 20 [2, 0, 0, 1, 1, 2, 0] [2, 0, 0, 1, 1, 2, 0] 1 2 false = ([1, 2, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_2001120 : invRung 7 5 20 [2, 0, 0, 1, 1, 2, 0] [1, 2, 1, 0, 2, 1, 1] 3 1 true = ([1, 1, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_2001120 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 0, 1] = [1, 0, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_2001120 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 0, 0] [2, 0, 0, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2001120 : specInv 7 5 20 [2, 0, 0, 1, 1, 2, 0] = some [1, 0, 2, 1, 1, 0, 0] :=
  specInv_white_7 [2, 0, 0, 1, 1, 2, 0] [1, 2, 1, 0, 2, 1, 1] [1, 1, 0, 0, 2, 0, 1] [1, 0, 2, 1, 1, 0, 0] demoR1_2001120 demoR2_2001120 demoC_2001120 demoM_2001120

theorem demoR1_0101120 : invRung 7 5 20 [0, 1, 0, 1, 1, 2, 0] [0, 1, 0, 1, 1, 2, 0] 1 2 false = ([2, 0, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_0101120 : invRung 7 5 20 [0, 1, 0, 1, 1, 2, 0] [2, 0, 1, 0, 2, 1, 1] 3 1 true = ([0, 1, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_0101120 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 0, 2] = [0, 1, 1, 2, 2, 1, 0] := by
  decide

theorem demoM_0101120 : fieldMul 7 5 20 [0, 1, 1, 2, 2, 1, 0] [0, 1, 0, 1, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101120 : mirrorTrits [0, 1, 1, 2, 2, 1, 0] = [0, 2, 2, 1, 1, 2, 0] := by
  decide

theorem demoInv_0101120 : specInv 7 5 20 [0, 1, 0, 1, 1, 2, 0] = some [0, 2, 2, 1, 1, 2, 0] :=
  specInv_mirror_7 [0, 1, 0, 1, 1, 2, 0] [2, 0, 1, 0, 2, 1, 1] [0, 1, 2, 0, 2, 0, 2] [0, 1, 1, 2, 2, 1, 0] [0, 2, 2, 1, 1, 2, 0] demoR1_0101120 demoR2_0101120 demoC_0101120 demoM_0101120 demoMir_0101120

theorem demoR1_1101120 : invRung 7 5 20 [1, 1, 0, 1, 1, 2, 0] [1, 1, 0, 1, 1, 2, 0] 1 2 false = ([1, 1, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_1101120 : invRung 7 5 20 [1, 1, 0, 1, 1, 2, 0] [1, 1, 1, 0, 2, 2, 2] 3 1 true = ([1, 1, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_1101120 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 2, 2] = [0, 2, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_1101120 : fieldMul 7 5 20 [0, 2, 0, 1, 1, 2, 1] [1, 1, 0, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1101120 : specInv 7 5 20 [1, 1, 0, 1, 1, 2, 0] = some [0, 2, 0, 1, 1, 2, 1] :=
  specInv_white_7 [1, 1, 0, 1, 1, 2, 0] [1, 1, 1, 0, 2, 2, 2] [1, 1, 0, 0, 1, 2, 2] [0, 2, 0, 1, 1, 2, 1] demoR1_1101120 demoR2_1101120 demoC_1101120 demoM_1101120

theorem demoR1_2101120 : invRung 7 5 20 [2, 1, 0, 1, 1, 2, 0] [2, 1, 0, 1, 1, 2, 0] 1 2 false = ([0, 2, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_2101120 : invRung 7 5 20 [2, 1, 0, 1, 1, 2, 0] [0, 2, 0, 2, 2, 2, 1] 3 1 true = ([0, 1, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2101120 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 2, 0] = [0, 2, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_2101120 : fieldMul 7 5 20 [0, 2, 0, 1, 2, 0, 1] [2, 1, 0, 1, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101120 : mirrorTrits [0, 2, 0, 1, 2, 0, 1] = [0, 1, 0, 2, 1, 0, 2] := by
  decide

theorem demoInv_2101120 : specInv 7 5 20 [2, 1, 0, 1, 1, 2, 0] = some [0, 1, 0, 2, 1, 0, 2] :=
  specInv_mirror_7 [2, 1, 0, 1, 1, 2, 0] [0, 2, 0, 2, 2, 2, 1] [0, 1, 0, 1, 0, 2, 0] [0, 2, 0, 1, 2, 0, 1] [0, 1, 0, 2, 1, 0, 2] demoR1_2101120 demoR2_2101120 demoC_2101120 demoM_2101120 demoMir_2101120

theorem demoR1_0201120 : invRung 7 5 20 [0, 2, 0, 1, 1, 2, 0] [0, 2, 0, 1, 1, 2, 0] 1 2 false = ([0, 1, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_0201120 : invRung 7 5 20 [0, 2, 0, 1, 1, 2, 0] [0, 1, 1, 0, 2, 2, 1] 3 1 true = ([1, 0, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0201120 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 2, 2] = [1, 2, 1, 0, 1, 0, 0] := by
  decide

theorem demoM_0201120 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 0, 0] [0, 2, 0, 1, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201120 : mirrorTrits [1, 2, 1, 0, 1, 0, 0] = [2, 1, 2, 0, 2, 0, 0] := by
  decide

theorem demoInv_0201120 : specInv 7 5 20 [0, 2, 0, 1, 1, 2, 0] = some [2, 1, 2, 0, 2, 0, 0] :=
  specInv_mirror_7 [0, 2, 0, 1, 1, 2, 0] [0, 1, 1, 0, 2, 2, 1] [1, 0, 2, 1, 1, 2, 2] [1, 2, 1, 0, 1, 0, 0] [2, 1, 2, 0, 2, 0, 0] demoR1_0201120 demoR2_0201120 demoC_0201120 demoM_0201120 demoMir_0201120

theorem demoR1_1201120 : invRung 7 5 20 [1, 2, 0, 1, 1, 2, 0] [1, 2, 0, 1, 1, 2, 0] 1 2 false = ([2, 2, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1201120 : invRung 7 5 20 [1, 2, 0, 1, 1, 2, 0] [2, 2, 0, 2, 2, 1, 1] 3 1 true = ([2, 0, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1201120 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 2, 2] = [0, 2, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_1201120 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 1, 0] [1, 2, 0, 1, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201120 : mirrorTrits [0, 2, 2, 0, 1, 1, 0] = [0, 1, 1, 0, 2, 2, 0] := by
  decide

theorem demoInv_1201120 : specInv 7 5 20 [1, 2, 0, 1, 1, 2, 0] = some [0, 1, 1, 0, 2, 2, 0] :=
  specInv_mirror_7 [1, 2, 0, 1, 1, 2, 0] [2, 2, 0, 2, 2, 1, 1] [2, 0, 2, 2, 1, 2, 2] [0, 2, 2, 0, 1, 1, 0] [0, 1, 1, 0, 2, 2, 0] demoR1_1201120 demoR2_1201120 demoC_1201120 demoM_1201120 demoMir_1201120

theorem demoR1_2201120 : invRung 7 5 20 [2, 2, 0, 1, 1, 2, 0] [2, 2, 0, 1, 1, 2, 0] 1 2 false = ([0, 2, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2201120 : invRung 7 5 20 [2, 2, 0, 1, 1, 2, 0] [0, 2, 0, 2, 2, 1, 2] 3 1 true = ([0, 0, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_2201120 : fieldCube 7 5 20 [0, 0, 1, 0, 1, 0, 2] = [0, 0, 1, 0, 2, 0, 1] := by
  decide

theorem demoM_2201120 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 0, 1] [2, 2, 0, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2201120 : specInv 7 5 20 [2, 2, 0, 1, 1, 2, 0] = some [0, 0, 1, 0, 2, 0, 1] :=
  specInv_white_7 [2, 2, 0, 1, 1, 2, 0] [0, 2, 0, 2, 2, 1, 2] [0, 0, 1, 0, 1, 0, 2] [0, 0, 1, 0, 2, 0, 1] demoR1_2201120 demoR2_2201120 demoC_2201120 demoM_2201120

theorem demoR1_0011120 : invRung 7 5 20 [0, 0, 1, 1, 1, 2, 0] [0, 0, 1, 1, 1, 2, 0] 1 2 false = ([2, 1, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0011120 : invRung 7 5 20 [0, 0, 1, 1, 1, 2, 0] [2, 1, 2, 0, 2, 2, 2] 3 1 true = ([0, 2, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_0011120 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 0, 1] = [1, 2, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_0011120 : fieldMul 7 5 20 [1, 2, 0, 1, 1, 0, 0] [0, 0, 1, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0011120 : specInv 7 5 20 [0, 0, 1, 1, 1, 2, 0] = some [1, 2, 0, 1, 1, 0, 0] :=
  specInv_white_7 [0, 0, 1, 1, 1, 2, 0] [2, 1, 2, 0, 2, 2, 2] [0, 2, 1, 1, 1, 0, 1] [1, 2, 0, 1, 1, 0, 0] demoR1_0011120 demoR2_0011120 demoC_0011120 demoM_0011120

theorem demoR1_1011120 : invRung 7 5 20 [1, 0, 1, 1, 1, 2, 0] [1, 0, 1, 1, 1, 2, 0] 1 2 false = ([1, 2, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_1011120 : invRung 7 5 20 [1, 0, 1, 1, 1, 2, 0] [1, 2, 2, 1, 2, 0, 0] 3 1 true = ([1, 2, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_1011120 : fieldCube 7 5 20 [1, 2, 1, 0, 0, 0, 1] = [1, 1, 2, 0, 1, 1, 2] := by
  decide

theorem demoM_1011120 : fieldMul 7 5 20 [1, 1, 2, 0, 1, 1, 2] [1, 0, 1, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1011120 : specInv 7 5 20 [1, 0, 1, 1, 1, 2, 0] = some [1, 1, 2, 0, 1, 1, 2] :=
  specInv_white_7 [1, 0, 1, 1, 1, 2, 0] [1, 2, 2, 1, 2, 0, 0] [1, 2, 1, 0, 0, 0, 1] [1, 1, 2, 0, 1, 1, 2] demoR1_1011120 demoR2_1011120 demoC_1011120 demoM_1011120

theorem demoR1_2011120 : invRung 7 5 20 [2, 0, 1, 1, 1, 2, 0] [2, 0, 1, 1, 1, 2, 0] 1 2 false = ([1, 0, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_2011120 : invRung 7 5 20 [2, 0, 1, 1, 1, 2, 0] [1, 0, 2, 1, 1, 0, 0] 3 1 true = ([0, 2, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_2011120 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 2, 2] = [2, 2, 0, 2, 1, 2, 0] := by
  decide

theorem demoM_2011120 : fieldMul 7 5 20 [2, 2, 0, 2, 1, 2, 0] [2, 0, 1, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2011120 : specInv 7 5 20 [2, 0, 1, 1, 1, 2, 0] = some [2, 2, 0, 2, 1, 2, 0] :=
  specInv_white_7 [2, 0, 1, 1, 1, 2, 0] [1, 0, 2, 1, 1, 0, 0] [0, 2, 2, 0, 1, 2, 2] [2, 2, 0, 2, 1, 2, 0] demoR1_2011120 demoR2_2011120 demoC_2011120 demoM_2011120

theorem demoR1_0111120 : invRung 7 5 20 [0, 1, 1, 1, 1, 2, 0] [0, 1, 1, 1, 1, 2, 0] 1 2 false = ([1, 1, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_0111120 : invRung 7 5 20 [0, 1, 1, 1, 1, 2, 0] [1, 1, 0, 0, 1, 0, 2] 3 1 true = ([2, 2, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0111120 : fieldCube 7 5 20 [2, 2, 0, 1, 1, 2, 2] = [2, 2, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_0111120 : fieldMul 7 5 20 [2, 2, 1, 2, 1, 0, 1] [0, 1, 1, 1, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111120 : mirrorTrits [2, 2, 1, 2, 1, 0, 1] = [1, 1, 2, 1, 2, 0, 2] := by
  decide

theorem demoInv_0111120 : specInv 7 5 20 [0, 1, 1, 1, 1, 2, 0] = some [1, 1, 2, 1, 2, 0, 2] :=
  specInv_mirror_7 [0, 1, 1, 1, 1, 2, 0] [1, 1, 0, 0, 1, 0, 2] [2, 2, 0, 1, 1, 2, 2] [2, 2, 1, 2, 1, 0, 1] [1, 1, 2, 1, 2, 0, 2] demoR1_0111120 demoR2_0111120 demoC_0111120 demoM_0111120 demoMir_0111120

theorem demoR1_1111120 : invRung 7 5 20 [1, 1, 1, 1, 1, 2, 0] [1, 1, 1, 1, 1, 2, 0] 1 2 false = ([0, 0, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_1111120 : invRung 7 5 20 [1, 1, 1, 1, 1, 2, 0] [0, 0, 0, 1, 0, 1, 0] 3 1 true = ([2, 2, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_1111120 : fieldCube 7 5 20 [2, 2, 0, 2, 2, 0, 2] = [1, 1, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_1111120 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 0, 1] [1, 1, 1, 1, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111120 : mirrorTrits [1, 1, 0, 0, 2, 0, 1] = [2, 2, 0, 0, 1, 0, 2] := by
  decide

theorem demoInv_1111120 : specInv 7 5 20 [1, 1, 1, 1, 1, 2, 0] = some [2, 2, 0, 0, 1, 0, 2] :=
  specInv_mirror_7 [1, 1, 1, 1, 1, 2, 0] [0, 0, 0, 1, 0, 1, 0] [2, 2, 0, 2, 2, 0, 2] [1, 1, 0, 0, 2, 0, 1] [2, 2, 0, 0, 1, 0, 2] demoR1_1111120 demoR2_1111120 demoC_1111120 demoM_1111120 demoMir_1111120

theorem demoR1_2111120 : invRung 7 5 20 [2, 1, 1, 1, 1, 2, 0] [2, 1, 1, 1, 1, 2, 0] 1 2 false = ([2, 1, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_2111120 : invRung 7 5 20 [2, 1, 1, 1, 1, 2, 0] [2, 1, 2, 0, 1, 0, 0] 3 1 true = ([1, 2, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_2111120 : fieldCube 7 5 20 [1, 2, 2, 1, 0, 1, 0] = [0, 1, 2, 2, 1, 2, 1] := by
  decide

theorem demoM_2111120 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 2, 1] [2, 1, 1, 1, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2111120 : mirrorTrits [0, 1, 2, 2, 1, 2, 1] = [0, 2, 1, 1, 2, 1, 2] := by
  decide

theorem demoInv_2111120 : specInv 7 5 20 [2, 1, 1, 1, 1, 2, 0] = some [0, 2, 1, 1, 2, 1, 2] :=
  specInv_mirror_7 [2, 1, 1, 1, 1, 2, 0] [2, 1, 2, 0, 1, 0, 0] [1, 2, 2, 1, 0, 1, 0] [0, 1, 2, 2, 1, 2, 1] [0, 2, 1, 1, 2, 1, 2] demoR1_2111120 demoR2_2111120 demoC_2111120 demoM_2111120 demoMir_2111120

theorem demoR1_0211120 : invRung 7 5 20 [0, 2, 1, 1, 1, 2, 0] [0, 2, 1, 1, 1, 2, 0] 1 2 false = ([2, 1, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0211120 : invRung 7 5 20 [0, 2, 1, 1, 1, 2, 0] [2, 1, 0, 2, 2, 2, 1] 3 1 true = ([0, 1, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0211120 : fieldCube 7 5 20 [0, 1, 0, 1, 2, 2, 2] = [0, 0, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_0211120 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 1, 2] [0, 2, 1, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0211120 : specInv 7 5 20 [0, 2, 1, 1, 1, 2, 0] = some [0, 0, 1, 2, 1, 1, 2] :=
  specInv_white_7 [0, 2, 1, 1, 1, 2, 0] [2, 1, 0, 2, 2, 2, 1] [0, 1, 0, 1, 2, 2, 2] [0, 0, 1, 2, 1, 1, 2] demoR1_0211120 demoR2_0211120 demoC_0211120 demoM_0211120

theorem demoR1_1211120 : invRung 7 5 20 [1, 2, 1, 1, 1, 2, 0] [1, 2, 1, 1, 1, 2, 0] 1 2 false = ([1, 2, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_1211120 : invRung 7 5 20 [1, 2, 1, 1, 1, 2, 0] [1, 2, 0, 1, 2, 2, 0] 3 1 true = ([0, 2, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_1211120 : fieldCube 7 5 20 [0, 2, 1, 0, 0, 0, 0] = [0, 0, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_1211120 : fieldMul 7 5 20 [0, 0, 0, 2, 0, 0, 1] [1, 2, 1, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1211120 : specInv 7 5 20 [1, 2, 1, 1, 1, 2, 0] = some [0, 0, 0, 2, 0, 0, 1] :=
  specInv_white_7 [1, 2, 1, 1, 1, 2, 0] [1, 2, 0, 1, 2, 2, 0] [0, 2, 1, 0, 0, 0, 0] [0, 0, 0, 2, 0, 0, 1] demoR1_1211120 demoR2_1211120 demoC_1211120 demoM_1211120

theorem demoR1_2211120 : invRung 7 5 20 [2, 2, 1, 1, 1, 2, 0] [2, 2, 1, 1, 1, 2, 0] 1 2 false = ([2, 1, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_2211120 : invRung 7 5 20 [2, 2, 1, 1, 1, 2, 0] [2, 1, 1, 0, 1, 2, 1] 3 1 true = ([0, 1, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_2211120 : fieldCube 7 5 20 [0, 1, 2, 1, 2, 1, 1] = [2, 1, 1, 1, 2, 2, 1] := by
  decide

theorem demoM_2211120 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 2, 1] [2, 2, 1, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2211120 : specInv 7 5 20 [2, 2, 1, 1, 1, 2, 0] = some [2, 1, 1, 1, 2, 2, 1] :=
  specInv_white_7 [2, 2, 1, 1, 1, 2, 0] [2, 1, 1, 0, 1, 2, 1] [0, 1, 2, 1, 2, 1, 1] [2, 1, 1, 1, 2, 2, 1] demoR1_2211120 demoR2_2211120 demoC_2211120 demoM_2211120

theorem demoR1_0021120 : invRung 7 5 20 [0, 0, 2, 1, 1, 2, 0] [0, 0, 2, 1, 1, 2, 0] 1 2 false = ([0, 0, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_0021120 : invRung 7 5 20 [0, 0, 2, 1, 1, 2, 0] [0, 0, 1, 1, 2, 1, 1] 3 1 true = ([2, 1, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0021120 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 2, 1] = [1, 1, 1, 0, 0, 1, 1] := by
  decide

theorem demoM_0021120 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 1, 1] [0, 0, 2, 1, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021120 : mirrorTrits [1, 1, 1, 0, 0, 1, 1] = [2, 2, 2, 0, 0, 2, 2] := by
  decide

theorem demoInv_0021120 : specInv 7 5 20 [0, 0, 2, 1, 1, 2, 0] = some [2, 2, 2, 0, 0, 2, 2] :=
  specInv_mirror_7 [0, 0, 2, 1, 1, 2, 0] [0, 0, 1, 1, 2, 1, 1] [2, 1, 1, 0, 1, 2, 1] [1, 1, 1, 0, 0, 1, 1] [2, 2, 2, 0, 0, 2, 2] demoR1_0021120 demoR2_0021120 demoC_0021120 demoM_0021120 demoMir_0021120

theorem demoR1_1021120 : invRung 7 5 20 [1, 0, 2, 1, 1, 2, 0] [1, 0, 2, 1, 1, 2, 0] 1 2 false = ([1, 0, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_1021120 : invRung 7 5 20 [1, 0, 2, 1, 1, 2, 0] [1, 0, 1, 1, 0, 1, 2] 3 1 true = ([0, 2, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_1021120 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 0, 2] = [1, 0, 2, 2, 2, 1, 1] := by
  decide

theorem demoM_1021120 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 1, 1] [1, 0, 2, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1021120 : specInv 7 5 20 [1, 0, 2, 1, 1, 2, 0] = some [1, 0, 2, 2, 2, 1, 1] :=
  specInv_white_7 [1, 0, 2, 1, 1, 2, 0] [1, 0, 1, 1, 0, 1, 2] [0, 2, 1, 1, 1, 0, 2] [1, 0, 2, 2, 2, 1, 1] demoR1_1021120 demoR2_1021120 demoC_1021120 demoM_1021120

theorem demoR1_2021120 : invRung 7 5 20 [2, 0, 2, 1, 1, 2, 0] [2, 0, 2, 1, 1, 2, 0] 1 2 false = ([0, 2, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_2021120 : invRung 7 5 20 [2, 0, 2, 1, 1, 2, 0] [0, 2, 1, 2, 2, 2, 0] 3 1 true = ([2, 2, 2, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_2021120 : fieldCube 7 5 20 [2, 2, 2, 2, 0, 0, 1] = [1, 1, 1, 0, 1, 0, 0] := by
  decide

theorem demoM_2021120 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 0, 0] [2, 0, 2, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2021120 : specInv 7 5 20 [2, 0, 2, 1, 1, 2, 0] = some [1, 1, 1, 0, 1, 0, 0] :=
  specInv_white_7 [2, 0, 2, 1, 1, 2, 0] [0, 2, 1, 2, 2, 2, 0] [2, 2, 2, 2, 0, 0, 1] [1, 1, 1, 0, 1, 0, 0] demoR1_2021120 demoR2_2021120 demoC_2021120 demoM_2021120

theorem demoR1_0121120 : invRung 7 5 20 [0, 1, 2, 1, 1, 2, 0] [0, 1, 2, 1, 1, 2, 0] 1 2 false = ([1, 2, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_0121120 : invRung 7 5 20 [0, 1, 2, 1, 1, 2, 0] [1, 2, 0, 2, 1, 1, 2] 3 1 true = ([1, 2, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_0121120 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 1, 0] = [0, 0, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_0121120 : fieldMul 7 5 20 [0, 0, 2, 1, 1, 1, 2] [0, 1, 2, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0121120 : specInv 7 5 20 [0, 1, 2, 1, 1, 2, 0] = some [0, 0, 2, 1, 1, 1, 2] :=
  specInv_white_7 [0, 1, 2, 1, 1, 2, 0] [1, 2, 0, 2, 1, 1, 2] [1, 2, 1, 1, 2, 1, 0] [0, 0, 2, 1, 1, 1, 2] demoR1_0121120 demoR2_0121120 demoC_0121120 demoM_0121120

theorem demoR1_1121120 : invRung 7 5 20 [1, 1, 2, 1, 1, 2, 0] [1, 1, 2, 1, 1, 2, 0] 1 2 false = ([2, 2, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_1121120 : invRung 7 5 20 [1, 1, 2, 1, 1, 2, 0] [2, 2, 1, 1, 2, 2, 2] 3 1 true = ([1, 1, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_1121120 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 0, 0] = [1, 2, 0, 0, 0, 2, 0] := by
  decide

theorem demoM_1121120 : fieldMul 7 5 20 [1, 2, 0, 0, 0, 2, 0] [1, 1, 2, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1121120 : specInv 7 5 20 [1, 1, 2, 1, 1, 2, 0] = some [1, 2, 0, 0, 0, 2, 0] :=
  specInv_white_7 [1, 1, 2, 1, 1, 2, 0] [2, 2, 1, 1, 2, 2, 2] [1, 1, 1, 0, 2, 0, 0] [1, 2, 0, 0, 0, 2, 0] demoR1_1121120 demoR2_1121120 demoC_1121120 demoM_1121120

theorem demoR1_2121120 : invRung 7 5 20 [2, 1, 2, 1, 1, 2, 0] [2, 1, 2, 1, 1, 2, 0] 1 2 false = ([0, 0, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_2121120 : invRung 7 5 20 [2, 1, 2, 1, 1, 2, 0] [0, 0, 1, 0, 1, 0, 2] 3 1 true = ([0, 2, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_2121120 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 0, 2] = [1, 2, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_2121120 : fieldMul 7 5 20 [1, 2, 2, 1, 2, 0, 0] [2, 1, 2, 1, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2121120 : specInv 7 5 20 [2, 1, 2, 1, 1, 2, 0] = some [1, 2, 2, 1, 2, 0, 0] :=
  specInv_white_7 [2, 1, 2, 1, 1, 2, 0] [0, 0, 1, 0, 1, 0, 2] [0, 2, 1, 1, 0, 0, 2] [1, 2, 2, 1, 2, 0, 0] demoR1_2121120 demoR2_2121120 demoC_2121120 demoM_2121120

theorem demoR1_0221120 : invRung 7 5 20 [0, 2, 2, 1, 1, 2, 0] [0, 2, 2, 1, 1, 2, 0] 1 2 false = ([2, 0, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_0221120 : invRung 7 5 20 [0, 2, 2, 1, 1, 2, 0] [2, 0, 2, 2, 2, 0, 2] 3 1 true = ([1, 0, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_0221120 : fieldCube 7 5 20 [1, 0, 1, 2, 0, 0, 2] = [0, 2, 0, 2, 2, 1, 0] := by
  decide

theorem demoM_0221120 : fieldMul 7 5 20 [0, 2, 0, 2, 2, 1, 0] [0, 2, 2, 1, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0221120 : mirrorTrits [0, 2, 0, 2, 2, 1, 0] = [0, 1, 0, 1, 1, 2, 0] := by
  decide

theorem demoInv_0221120 : specInv 7 5 20 [0, 2, 2, 1, 1, 2, 0] = some [0, 1, 0, 1, 1, 2, 0] :=
  specInv_mirror_7 [0, 2, 2, 1, 1, 2, 0] [2, 0, 2, 2, 2, 0, 2] [1, 0, 1, 2, 0, 0, 2] [0, 2, 0, 2, 2, 1, 0] [0, 1, 0, 1, 1, 2, 0] demoR1_0221120 demoR2_0221120 demoC_0221120 demoM_0221120 demoMir_0221120

theorem demoR1_1221120 : invRung 7 5 20 [1, 2, 2, 1, 1, 2, 0] [1, 2, 2, 1, 1, 2, 0] 1 2 false = ([0, 1, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_1221120 : invRung 7 5 20 [1, 2, 2, 1, 1, 2, 0] [0, 1, 1, 1, 2, 1, 2] 3 1 true = ([0, 1, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_1221120 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 2, 2] = [2, 2, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_1221120 : fieldMul 7 5 20 [2, 2, 0, 1, 1, 2, 1] [1, 2, 2, 1, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221120 : mirrorTrits [2, 2, 0, 1, 1, 2, 1] = [1, 1, 0, 2, 2, 1, 2] := by
  decide

theorem demoInv_1221120 : specInv 7 5 20 [1, 2, 2, 1, 1, 2, 0] = some [1, 1, 0, 2, 2, 1, 2] :=
  specInv_mirror_7 [1, 2, 2, 1, 1, 2, 0] [0, 1, 1, 1, 2, 1, 2] [0, 1, 0, 0, 1, 2, 2] [2, 2, 0, 1, 1, 2, 1] [1, 1, 0, 2, 2, 1, 2] demoR1_1221120 demoR2_1221120 demoC_1221120 demoM_1221120 demoMir_1221120

theorem demoR1_2221120 : invRung 7 5 20 [2, 2, 2, 1, 1, 2, 0] [2, 2, 2, 1, 1, 2, 0] 1 2 false = ([0, 2, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_2221120 : invRung 7 5 20 [2, 2, 2, 1, 1, 2, 0] [0, 2, 1, 2, 0, 1, 2] 3 1 true = ([1, 2, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2221120 : fieldCube 7 5 20 [1, 2, 0, 2, 0, 1, 0] = [1, 1, 0, 2, 1, 0, 2] := by
  decide

theorem demoM_2221120 : fieldMul 7 5 20 [1, 1, 0, 2, 1, 0, 2] [2, 2, 2, 1, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221120 : mirrorTrits [1, 1, 0, 2, 1, 0, 2] = [2, 2, 0, 1, 2, 0, 1] := by
  decide

theorem demoInv_2221120 : specInv 7 5 20 [2, 2, 2, 1, 1, 2, 0] = some [2, 2, 0, 1, 2, 0, 1] :=
  specInv_mirror_7 [2, 2, 2, 1, 1, 2, 0] [0, 2, 1, 2, 0, 1, 2] [1, 2, 0, 2, 0, 1, 0] [1, 1, 0, 2, 1, 0, 2] [2, 2, 0, 1, 2, 0, 1] demoR1_2221120 demoR2_2221120 demoC_2221120 demoM_2221120 demoMir_2221120

theorem demoR1_0002120 : invRung 7 5 20 [0, 0, 0, 2, 1, 2, 0] [0, 0, 0, 2, 1, 2, 0] 1 2 false = ([2, 0, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_0002120 : invRung 7 5 20 [0, 0, 0, 2, 1, 2, 0] [2, 0, 0, 1, 2, 0, 2] 3 1 true = ([1, 2, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0002120 : fieldCube 7 5 20 [1, 2, 0, 1, 1, 0, 0] = [2, 1, 1, 0, 0, 2, 1] := by
  decide

theorem demoM_0002120 : fieldMul 7 5 20 [2, 1, 1, 0, 0, 2, 1] [0, 0, 0, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002120 : mirrorTrits [2, 1, 1, 0, 0, 2, 1] = [1, 2, 2, 0, 0, 1, 2] := by
  decide

theorem demoInv_0002120 : specInv 7 5 20 [0, 0, 0, 2, 1, 2, 0] = some [1, 2, 2, 0, 0, 1, 2] :=
  specInv_mirror_7 [0, 0, 0, 2, 1, 2, 0] [2, 0, 0, 1, 2, 0, 2] [1, 2, 0, 1, 1, 0, 0] [2, 1, 1, 0, 0, 2, 1] [1, 2, 2, 0, 0, 1, 2] demoR1_0002120 demoR2_0002120 demoC_0002120 demoM_0002120 demoMir_0002120

theorem demoR1_1002120 : invRung 7 5 20 [1, 0, 0, 2, 1, 2, 0] [1, 0, 0, 2, 1, 2, 0] 1 2 false = ([1, 2, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_1002120 : invRung 7 5 20 [1, 0, 0, 2, 1, 2, 0] [1, 2, 2, 2, 0, 1, 0] 3 1 true = ([2, 2, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_1002120 : fieldCube 7 5 20 [2, 2, 0, 2, 1, 2, 0] = [0, 0, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_1002120 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 2, 2] [1, 0, 0, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002120 : mirrorTrits [0, 0, 1, 0, 2, 2, 2] = [0, 0, 2, 0, 1, 1, 1] := by
  decide

theorem demoInv_1002120 : specInv 7 5 20 [1, 0, 0, 2, 1, 2, 0] = some [0, 0, 2, 0, 1, 1, 1] :=
  specInv_mirror_7 [1, 0, 0, 2, 1, 2, 0] [1, 2, 2, 2, 0, 1, 0] [2, 2, 0, 2, 1, 2, 0] [0, 0, 1, 0, 2, 2, 2] [0, 0, 2, 0, 1, 1, 1] demoR1_1002120 demoR2_1002120 demoC_1002120 demoM_1002120 demoMir_1002120

theorem demoR1_2002120 : invRung 7 5 20 [2, 0, 0, 2, 1, 2, 0] [2, 0, 0, 2, 1, 2, 0] 1 2 false = ([1, 1, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2002120 : invRung 7 5 20 [2, 0, 0, 2, 1, 2, 0] [1, 1, 2, 2, 0, 0, 2] 3 1 true = ([1, 1, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_2002120 : fieldCube 7 5 20 [1, 1, 2, 0, 1, 1, 2] = [2, 1, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_2002120 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 1, 1] [2, 0, 0, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002120 : mirrorTrits [2, 1, 2, 1, 0, 1, 1] = [1, 2, 1, 2, 0, 2, 2] := by
  decide

theorem demoInv_2002120 : specInv 7 5 20 [2, 0, 0, 2, 1, 2, 0] = some [1, 2, 1, 2, 0, 2, 2] :=
  specInv_mirror_7 [2, 0, 0, 2, 1, 2, 0] [1, 1, 2, 2, 0, 0, 2] [1, 1, 2, 0, 1, 1, 2] [2, 1, 2, 1, 0, 1, 1] [1, 2, 1, 2, 0, 2, 2] demoR1_2002120 demoR2_2002120 demoC_2002120 demoM_2002120 demoMir_2002120

theorem demoR1_0102120 : invRung 7 5 20 [0, 1, 0, 2, 1, 2, 0] [0, 1, 0, 2, 1, 2, 0] 1 2 false = ([1, 2, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_0102120 : invRung 7 5 20 [0, 1, 0, 2, 1, 2, 0] [1, 2, 0, 0, 0, 2, 1] 3 1 true = ([1, 0, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0102120 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 1, 1] = [2, 2, 0, 1, 2, 2, 1] := by
  decide

theorem demoM_0102120 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 2, 1] [0, 1, 0, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0102120 : specInv 7 5 20 [0, 1, 0, 2, 1, 2, 0] = some [2, 2, 0, 1, 2, 2, 1] :=
  specInv_white_7 [0, 1, 0, 2, 1, 2, 0] [1, 2, 0, 0, 0, 2, 1] [1, 0, 1, 0, 0, 1, 1] [2, 2, 0, 1, 2, 2, 1] demoR1_0102120 demoR2_0102120 demoC_0102120 demoM_0102120

theorem demoR1_1102120 : invRung 7 5 20 [1, 1, 0, 2, 1, 2, 0] [1, 1, 0, 2, 1, 2, 0] 1 2 false = ([1, 0, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_1102120 : invRung 7 5 20 [1, 1, 0, 2, 1, 2, 0] [1, 0, 1, 2, 1, 1, 0] 3 1 true = ([1, 0, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_1102120 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 0, 0] = [2, 1, 1, 1, 0, 2, 2] := by
  decide

theorem demoM_1102120 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 2, 2] [1, 1, 0, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102120 : mirrorTrits [2, 1, 1, 1, 0, 2, 2] = [1, 2, 2, 2, 0, 1, 1] := by
  decide

theorem demoInv_1102120 : specInv 7 5 20 [1, 1, 0, 2, 1, 2, 0] = some [1, 2, 2, 2, 0, 1, 1] :=
  specInv_mirror_7 [1, 1, 0, 2, 1, 2, 0] [1, 0, 1, 2, 1, 1, 0] [1, 0, 1, 1, 1, 0, 0] [2, 1, 1, 1, 0, 2, 2] [1, 2, 2, 2, 0, 1, 1] demoR1_1102120 demoR2_1102120 demoC_1102120 demoM_1102120 demoMir_1102120

theorem demoR1_2102120 : invRung 7 5 20 [2, 1, 0, 2, 1, 2, 0] [2, 1, 0, 2, 1, 2, 0] 1 2 false = ([1, 0, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_2102120 : invRung 7 5 20 [2, 1, 0, 2, 1, 2, 0] [1, 0, 2, 2, 1, 0, 0] 3 1 true = ([0, 2, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_2102120 : fieldCube 7 5 20 [0, 2, 2, 1, 0, 2, 2] = [0, 1, 1, 1, 1, 2, 2] := by
  decide

theorem demoM_2102120 : fieldMul 7 5 20 [0, 1, 1, 1, 1, 2, 2] [2, 1, 0, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2102120 : specInv 7 5 20 [2, 1, 0, 2, 1, 2, 0] = some [0, 1, 1, 1, 1, 2, 2] :=
  specInv_white_7 [2, 1, 0, 2, 1, 2, 0] [1, 0, 2, 2, 1, 0, 0] [0, 2, 2, 1, 0, 2, 2] [0, 1, 1, 1, 1, 2, 2] demoR1_2102120 demoR2_2102120 demoC_2102120 demoM_2102120

theorem demoR1_0202120 : invRung 7 5 20 [0, 2, 0, 2, 1, 2, 0] [0, 2, 0, 2, 1, 2, 0] 1 2 false = ([1, 0, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_0202120 : invRung 7 5 20 [0, 2, 0, 2, 1, 2, 0] [1, 0, 1, 2, 2, 2, 0] 3 1 true = ([1, 1, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0202120 : fieldCube 7 5 20 [1, 1, 2, 2, 2, 0, 2] = [0, 1, 0, 2, 2, 0, 0] := by
  decide

theorem demoM_0202120 : fieldMul 7 5 20 [0, 1, 0, 2, 2, 0, 0] [0, 2, 0, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0202120 : specInv 7 5 20 [0, 2, 0, 2, 1, 2, 0] = some [0, 1, 0, 2, 2, 0, 0] :=
  specInv_white_7 [0, 2, 0, 2, 1, 2, 0] [1, 0, 1, 2, 2, 2, 0] [1, 1, 2, 2, 2, 0, 2] [0, 1, 0, 2, 2, 0, 0] demoR1_0202120 demoR2_0202120 demoC_0202120 demoM_0202120

theorem demoR1_1202120 : invRung 7 5 20 [1, 2, 0, 2, 1, 2, 0] [1, 2, 0, 2, 1, 2, 0] 1 2 false = ([2, 1, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_1202120 : invRung 7 5 20 [1, 2, 0, 2, 1, 2, 0] [2, 1, 1, 0, 2, 1, 1] 3 1 true = ([2, 2, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_1202120 : fieldCube 7 5 20 [2, 2, 1, 0, 0, 0, 1] = [2, 1, 2, 0, 1, 1, 2] := by
  decide

theorem demoM_1202120 : fieldMul 7 5 20 [2, 1, 2, 0, 1, 1, 2] [1, 2, 0, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202120 : mirrorTrits [2, 1, 2, 0, 1, 1, 2] = [1, 2, 1, 0, 2, 2, 1] := by
  decide

theorem demoInv_1202120 : specInv 7 5 20 [1, 2, 0, 2, 1, 2, 0] = some [1, 2, 1, 0, 2, 2, 1] :=
  specInv_mirror_7 [1, 2, 0, 2, 1, 2, 0] [2, 1, 1, 0, 2, 1, 1] [2, 2, 1, 0, 0, 0, 1] [2, 1, 2, 0, 1, 1, 2] [1, 2, 1, 0, 2, 2, 1] demoR1_1202120 demoR2_1202120 demoC_1202120 demoM_1202120 demoMir_1202120

theorem demoR1_2202120 : invRung 7 5 20 [2, 2, 0, 2, 1, 2, 0] [2, 2, 0, 2, 1, 2, 0] 1 2 false = ([2, 0, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2202120 : invRung 7 5 20 [2, 2, 0, 2, 1, 2, 0] [2, 0, 0, 1, 1, 2, 0] 3 1 true = ([0, 1, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_2202120 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 0, 1] = [2, 0, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_2202120 : fieldMul 7 5 20 [2, 0, 1, 1, 1, 2, 0] [2, 2, 0, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2202120 : specInv 7 5 20 [2, 2, 0, 2, 1, 2, 0] = some [2, 0, 1, 1, 1, 2, 0] :=
  specInv_white_7 [2, 2, 0, 2, 1, 2, 0] [2, 0, 0, 1, 1, 2, 0] [0, 1, 0, 2, 2, 0, 1] [2, 0, 1, 1, 1, 2, 0] demoR1_2202120 demoR2_2202120 demoC_2202120 demoM_2202120

theorem demoR1_0012120 : invRung 7 5 20 [0, 0, 1, 2, 1, 2, 0] [0, 0, 1, 2, 1, 2, 0] 1 2 false = ([2, 0, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_0012120 : invRung 7 5 20 [0, 0, 1, 2, 1, 2, 0] [2, 0, 1, 1, 2, 1, 0] 3 1 true = ([2, 2, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_0012120 : fieldCube 7 5 20 [2, 2, 0, 2, 0, 0, 0] = [1, 0, 2, 2, 0, 2, 0] := by
  decide

theorem demoM_0012120 : fieldMul 7 5 20 [1, 0, 2, 2, 0, 2, 0] [0, 0, 1, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0012120 : specInv 7 5 20 [0, 0, 1, 2, 1, 2, 0] = some [1, 0, 2, 2, 0, 2, 0] :=
  specInv_white_7 [0, 0, 1, 2, 1, 2, 0] [2, 0, 1, 1, 2, 1, 0] [2, 2, 0, 2, 0, 0, 0] [1, 0, 2, 2, 0, 2, 0] demoR1_0012120 demoR2_0012120 demoC_0012120 demoM_0012120

theorem demoR1_1012120 : invRung 7 5 20 [1, 0, 1, 2, 1, 2, 0] [1, 0, 1, 2, 1, 2, 0] 1 2 false = ([1, 2, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1012120 : invRung 7 5 20 [1, 0, 1, 2, 1, 2, 0] [1, 2, 0, 0, 0, 2, 0] 3 1 true = ([2, 1, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_1012120 : fieldCube 7 5 20 [2, 1, 2, 2, 0, 2, 2] = [0, 1, 2, 0, 1, 0, 2] := by
  decide

theorem demoM_1012120 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 0, 2] [1, 0, 1, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1012120 : specInv 7 5 20 [1, 0, 1, 2, 1, 2, 0] = some [0, 1, 2, 0, 1, 0, 2] :=
  specInv_white_7 [1, 0, 1, 2, 1, 2, 0] [1, 2, 0, 0, 0, 2, 0] [2, 1, 2, 2, 0, 2, 2] [0, 1, 2, 0, 1, 0, 2] demoR1_1012120 demoR2_1012120 demoC_1012120 demoM_1012120

theorem demoR1_2012120 : invRung 7 5 20 [2, 0, 1, 2, 1, 2, 0] [2, 0, 1, 2, 1, 2, 0] 1 2 false = ([1, 0, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2012120 : invRung 7 5 20 [2, 0, 1, 2, 1, 2, 0] [1, 0, 0, 0, 2, 0, 2] 3 1 true = ([1, 1, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_2012120 : fieldCube 7 5 20 [1, 1, 2, 2, 0, 1, 1] = [1, 2, 2, 2, 2, 1, 2] := by
  decide

theorem demoM_2012120 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 1, 2] [2, 0, 1, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012120 : mirrorTrits [1, 2, 2, 2, 2, 1, 2] = [2, 1, 1, 1, 1, 2, 1] := by
  decide

theorem demoInv_2012120 : specInv 7 5 20 [2, 0, 1, 2, 1, 2, 0] = some [2, 1, 1, 1, 1, 2, 1] :=
  specInv_mirror_7 [2, 0, 1, 2, 1, 2, 0] [1, 0, 0, 0, 2, 0, 2] [1, 1, 2, 2, 0, 1, 1] [1, 2, 2, 2, 2, 1, 2] [2, 1, 1, 1, 1, 2, 1] demoR1_2012120 demoR2_2012120 demoC_2012120 demoM_2012120 demoMir_2012120

theorem demoR1_0112120 : invRung 7 5 20 [0, 1, 1, 2, 1, 2, 0] [0, 1, 1, 2, 1, 2, 0] 1 2 false = ([1, 1, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_0112120 : invRung 7 5 20 [0, 1, 1, 2, 1, 2, 0] [1, 1, 2, 0, 0, 2, 1] 3 1 true = ([0, 2, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_0112120 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 0, 2] = [2, 0, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_0112120 : fieldMul 7 5 20 [2, 0, 0, 2, 2, 2, 1] [0, 1, 1, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0112120 : specInv 7 5 20 [0, 1, 1, 2, 1, 2, 0] = some [2, 0, 0, 2, 2, 2, 1] :=
  specInv_white_7 [0, 1, 1, 2, 1, 2, 0] [1, 1, 2, 0, 0, 2, 1] [0, 2, 1, 2, 1, 0, 2] [2, 0, 0, 2, 2, 2, 1] demoR1_0112120 demoR2_0112120 demoC_0112120 demoM_0112120

theorem demoR1_1112120 : invRung 7 5 20 [1, 1, 1, 2, 1, 2, 0] [1, 1, 1, 2, 1, 2, 0] 1 2 false = ([1, 1, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_1112120 : invRung 7 5 20 [1, 1, 1, 2, 1, 2, 0] [1, 1, 1, 2, 2, 2, 1] 3 1 true = ([0, 2, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_1112120 : fieldCube 7 5 20 [0, 2, 2, 0, 2, 0, 1] = [0, 0, 2, 2, 1, 0, 2] := by
  decide

theorem demoM_1112120 : fieldMul 7 5 20 [0, 0, 2, 2, 1, 0, 2] [1, 1, 1, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112120 : mirrorTrits [0, 0, 2, 2, 1, 0, 2] = [0, 0, 1, 1, 2, 0, 1] := by
  decide

theorem demoInv_1112120 : specInv 7 5 20 [1, 1, 1, 2, 1, 2, 0] = some [0, 0, 1, 1, 2, 0, 1] :=
  specInv_mirror_7 [1, 1, 1, 2, 1, 2, 0] [1, 1, 1, 2, 2, 2, 1] [0, 2, 2, 0, 2, 0, 1] [0, 0, 2, 2, 1, 0, 2] [0, 0, 1, 1, 2, 0, 1] demoR1_1112120 demoR2_1112120 demoC_1112120 demoM_1112120 demoMir_1112120

theorem demoR1_2112120 : invRung 7 5 20 [2, 1, 1, 2, 1, 2, 0] [2, 1, 1, 2, 1, 2, 0] 1 2 false = ([1, 2, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_2112120 : invRung 7 5 20 [2, 1, 1, 2, 1, 2, 0] [1, 2, 0, 1, 2, 1, 0] 3 1 true = ([2, 1, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_2112120 : fieldCube 7 5 20 [2, 1, 0, 1, 2, 0, 2] = [0, 1, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_2112120 : fieldMul 7 5 20 [0, 1, 2, 2, 2, 2, 1] [2, 1, 1, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112120 : mirrorTrits [0, 1, 2, 2, 2, 2, 1] = [0, 2, 1, 1, 1, 1, 2] := by
  decide

theorem demoInv_2112120 : specInv 7 5 20 [2, 1, 1, 2, 1, 2, 0] = some [0, 2, 1, 1, 1, 1, 2] :=
  specInv_mirror_7 [2, 1, 1, 2, 1, 2, 0] [1, 2, 0, 1, 2, 1, 0] [2, 1, 0, 1, 2, 0, 2] [0, 1, 2, 2, 2, 2, 1] [0, 2, 1, 1, 1, 1, 2] demoR1_2112120 demoR2_2112120 demoC_2112120 demoM_2112120 demoMir_2112120

theorem demoR1_0212120 : invRung 7 5 20 [0, 2, 1, 2, 1, 2, 0] [0, 2, 1, 2, 1, 2, 0] 1 2 false = ([2, 0, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_0212120 : invRung 7 5 20 [0, 2, 1, 2, 1, 2, 0] [2, 0, 2, 2, 2, 2, 2] 3 1 true = ([2, 1, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_0212120 : fieldCube 7 5 20 [2, 1, 1, 2, 2, 0, 1] = [1, 0, 1, 1, 1, 2, 1] := by
  decide

theorem demoM_0212120 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 2, 1] [0, 2, 1, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212120 : mirrorTrits [1, 0, 1, 1, 1, 2, 1] = [2, 0, 2, 2, 2, 1, 2] := by
  decide

theorem demoInv_0212120 : specInv 7 5 20 [0, 2, 1, 2, 1, 2, 0] = some [2, 0, 2, 2, 2, 1, 2] :=
  specInv_mirror_7 [0, 2, 1, 2, 1, 2, 0] [2, 0, 2, 2, 2, 2, 2] [2, 1, 1, 2, 2, 0, 1] [1, 0, 1, 1, 1, 2, 1] [2, 0, 2, 2, 2, 1, 2] demoR1_0212120 demoR2_0212120 demoC_0212120 demoM_0212120 demoMir_0212120

theorem demoR1_1212120 : invRung 7 5 20 [1, 2, 1, 2, 1, 2, 0] [1, 2, 1, 2, 1, 2, 0] 1 2 false = ([0, 2, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_1212120 : invRung 7 5 20 [1, 2, 1, 2, 1, 2, 0] [0, 2, 1, 2, 1, 0, 0] 3 1 true = ([2, 1, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1212120 : fieldCube 7 5 20 [2, 1, 2, 2, 1, 2, 2] = [0, 2, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_1212120 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 1, 0] [1, 2, 1, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212120 : mirrorTrits [0, 2, 2, 1, 1, 1, 0] = [0, 1, 1, 2, 2, 2, 0] := by
  decide

theorem demoInv_1212120 : specInv 7 5 20 [1, 2, 1, 2, 1, 2, 0] = some [0, 1, 1, 2, 2, 2, 0] :=
  specInv_mirror_7 [1, 2, 1, 2, 1, 2, 0] [0, 2, 1, 2, 1, 0, 0] [2, 1, 2, 2, 1, 2, 2] [0, 2, 2, 1, 1, 1, 0] [0, 1, 1, 2, 2, 2, 0] demoR1_1212120 demoR2_1212120 demoC_1212120 demoM_1212120 demoMir_1212120

theorem demoR1_2212120 : invRung 7 5 20 [2, 2, 1, 2, 1, 2, 0] [2, 2, 1, 2, 1, 2, 0] 1 2 false = ([0, 1, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2212120 : invRung 7 5 20 [2, 2, 1, 2, 1, 2, 0] [0, 1, 2, 1, 1, 2, 0] 3 1 true = ([1, 0, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_2212120 : fieldCube 7 5 20 [1, 0, 0, 2, 2, 0, 1] = [0, 0, 1, 0, 1, 2, 0] := by
  decide

theorem demoM_2212120 : fieldMul 7 5 20 [0, 0, 1, 0, 1, 2, 0] [2, 2, 1, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2212120 : specInv 7 5 20 [2, 2, 1, 2, 1, 2, 0] = some [0, 0, 1, 0, 1, 2, 0] :=
  specInv_white_7 [2, 2, 1, 2, 1, 2, 0] [0, 1, 2, 1, 1, 2, 0] [1, 0, 0, 2, 2, 0, 1] [0, 0, 1, 0, 1, 2, 0] demoR1_2212120 demoR2_2212120 demoC_2212120 demoM_2212120

theorem demoR1_0022120 : invRung 7 5 20 [0, 0, 2, 2, 1, 2, 0] [0, 0, 2, 2, 1, 2, 0] 1 2 false = ([1, 2, 2, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_0022120 : invRung 7 5 20 [0, 0, 2, 2, 1, 2, 0] [1, 2, 2, 1, 1, 0, 1] 3 1 true = ([2, 0, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_0022120 : fieldCube 7 5 20 [2, 0, 2, 0, 0, 0, 0] = [2, 0, 0, 0, 0, 0, 2] := by
  decide

theorem demoM_0022120 : fieldMul 7 5 20 [2, 0, 0, 0, 0, 0, 2] [0, 0, 2, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022120 : mirrorTrits [2, 0, 0, 0, 0, 0, 2] = [1, 0, 0, 0, 0, 0, 1] := by
  decide

theorem demoInv_0022120 : specInv 7 5 20 [0, 0, 2, 2, 1, 2, 0] = some [1, 0, 0, 0, 0, 0, 1] :=
  specInv_mirror_7 [0, 0, 2, 2, 1, 2, 0] [1, 2, 2, 1, 1, 0, 1] [2, 0, 2, 0, 0, 0, 0] [2, 0, 0, 0, 0, 0, 2] [1, 0, 0, 0, 0, 0, 1] demoR1_0022120 demoR2_0022120 demoC_0022120 demoM_0022120 demoMir_0022120

theorem demoR1_1022120 : invRung 7 5 20 [1, 0, 2, 2, 1, 2, 0] [1, 0, 2, 2, 1, 2, 0] 1 2 false = ([2, 1, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_1022120 : invRung 7 5 20 [1, 0, 2, 2, 1, 2, 0] [2, 1, 2, 1, 2, 1, 2] 3 1 true = ([2, 0, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1022120 : fieldCube 7 5 20 [2, 0, 0, 0, 0, 1, 0] = [0, 1, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_1022120 : fieldMul 7 5 20 [0, 1, 1, 0, 1, 1, 2] [1, 0, 2, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1022120 : mirrorTrits [0, 1, 1, 0, 1, 1, 2] = [0, 2, 2, 0, 2, 2, 1] := by
  decide

theorem demoInv_1022120 : specInv 7 5 20 [1, 0, 2, 2, 1, 2, 0] = some [0, 2, 2, 0, 2, 2, 1] :=
  specInv_mirror_7 [1, 0, 2, 2, 1, 2, 0] [2, 1, 2, 1, 2, 1, 2] [2, 0, 0, 0, 0, 1, 0] [0, 1, 1, 0, 1, 1, 2] [0, 2, 2, 0, 2, 2, 1] demoR1_1022120 demoR2_1022120 demoC_1022120 demoM_1022120 demoMir_1022120

theorem demoR1_2022120 : invRung 7 5 20 [2, 0, 2, 2, 1, 2, 0] [2, 0, 2, 2, 1, 2, 0] 1 2 false = ([1, 1, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_2022120 : invRung 7 5 20 [2, 0, 2, 2, 1, 2, 0] [1, 1, 0, 1, 0, 1, 0] 3 1 true = ([2, 0, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2022120 : fieldCube 7 5 20 [2, 0, 0, 1, 0, 2, 0] = [2, 2, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_2022120 : fieldMul 7 5 20 [2, 2, 0, 0, 2, 0, 1] [2, 0, 2, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2022120 : specInv 7 5 20 [2, 0, 2, 2, 1, 2, 0] = some [2, 2, 0, 0, 2, 0, 1] :=
  specInv_white_7 [2, 0, 2, 2, 1, 2, 0] [1, 1, 0, 1, 0, 1, 0] [2, 0, 0, 1, 0, 2, 0] [2, 2, 0, 0, 2, 0, 1] demoR1_2022120 demoR2_2022120 demoC_2022120 demoM_2022120

theorem demoR1_0122120 : invRung 7 5 20 [0, 1, 2, 2, 1, 2, 0] [0, 1, 2, 2, 1, 2, 0] 1 2 false = ([0, 1, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_0122120 : invRung 7 5 20 [0, 1, 2, 2, 1, 2, 0] [0, 1, 0, 2, 1, 2, 0] 3 1 true = ([0, 2, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_0122120 : fieldCube 7 5 20 [0, 2, 0, 1, 2, 0, 0] = [1, 2, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_0122120 : fieldMul 7 5 20 [1, 2, 1, 1, 0, 0, 2] [0, 1, 2, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0122120 : specInv 7 5 20 [0, 1, 2, 2, 1, 2, 0] = some [1, 2, 1, 1, 0, 0, 2] :=
  specInv_white_7 [0, 1, 2, 2, 1, 2, 0] [0, 1, 0, 2, 1, 2, 0] [0, 2, 0, 1, 2, 0, 0] [1, 2, 1, 1, 0, 0, 2] demoR1_0122120 demoR2_0122120 demoC_0122120 demoM_0122120

theorem demoR1_1122120 : invRung 7 5 20 [1, 1, 2, 2, 1, 2, 0] [1, 1, 2, 2, 1, 2, 0] 1 2 false = ([2, 0, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1122120 : invRung 7 5 20 [1, 1, 2, 2, 1, 2, 0] [2, 0, 1, 1, 1, 0, 0] 3 1 true = ([1, 2, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_1122120 : fieldCube 7 5 20 [1, 2, 0, 1, 1, 1, 0] = [0, 2, 2, 0, 1, 0, 0] := by
  decide

theorem demoM_1122120 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 0, 0] [1, 1, 2, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122120 : mirrorTrits [0, 2, 2, 0, 1, 0, 0] = [0, 1, 1, 0, 2, 0, 0] := by
  decide

theorem demoInv_1122120 : specInv 7 5 20 [1, 1, 2, 2, 1, 2, 0] = some [0, 1, 1, 0, 2, 0, 0] :=
  specInv_mirror_7 [1, 1, 2, 2, 1, 2, 0] [2, 0, 1, 1, 1, 0, 0] [1, 2, 0, 1, 1, 1, 0] [0, 2, 2, 0, 1, 0, 0] [0, 1, 1, 0, 2, 0, 0] demoR1_1122120 demoR2_1122120 demoC_1122120 demoM_1122120 demoMir_1122120

theorem demoR1_2122120 : invRung 7 5 20 [2, 1, 2, 2, 1, 2, 0] [2, 1, 2, 2, 1, 2, 0] 1 2 false = ([1, 2, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_2122120 : invRung 7 5 20 [2, 1, 2, 2, 1, 2, 0] [1, 2, 2, 2, 1, 2, 0] 3 1 true = ([2, 2, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_2122120 : fieldCube 7 5 20 [2, 2, 0, 0, 1, 2, 1] = [1, 1, 1, 1, 0, 1, 0] := by
  decide

theorem demoM_2122120 : fieldMul 7 5 20 [1, 1, 1, 1, 0, 1, 0] [2, 1, 2, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122120 : mirrorTrits [1, 1, 1, 1, 0, 1, 0] = [2, 2, 2, 2, 0, 2, 0] := by
  decide

theorem demoInv_2122120 : specInv 7 5 20 [2, 1, 2, 2, 1, 2, 0] = some [2, 2, 2, 2, 0, 2, 0] :=
  specInv_mirror_7 [2, 1, 2, 2, 1, 2, 0] [1, 2, 2, 2, 1, 2, 0] [2, 2, 0, 0, 1, 2, 1] [1, 1, 1, 1, 0, 1, 0] [2, 2, 2, 2, 0, 2, 0] demoR1_2122120 demoR2_2122120 demoC_2122120 demoM_2122120 demoMir_2122120

theorem demoR1_0222120 : invRung 7 5 20 [0, 2, 2, 2, 1, 2, 0] [0, 2, 2, 2, 1, 2, 0] 1 2 false = ([2, 0, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0222120 : invRung 7 5 20 [0, 2, 2, 2, 1, 2, 0] [2, 0, 1, 0, 2, 1, 2] 3 1 true = ([0, 1, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0222120 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 0, 1] = [0, 1, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_0222120 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 1, 1] [0, 2, 2, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0222120 : specInv 7 5 20 [0, 2, 2, 2, 1, 2, 0] = some [0, 1, 2, 2, 1, 1, 1] :=
  specInv_white_7 [0, 2, 2, 2, 1, 2, 0] [2, 0, 1, 0, 2, 1, 2] [0, 1, 0, 0, 0, 0, 1] [0, 1, 2, 2, 1, 1, 1] demoR1_0222120 demoR2_0222120 demoC_0222120 demoM_0222120

theorem demoR1_1222120 : invRung 7 5 20 [1, 2, 2, 2, 1, 2, 0] [1, 2, 2, 2, 1, 2, 0] 1 2 false = ([2, 0, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1222120 : invRung 7 5 20 [1, 2, 2, 2, 1, 2, 0] [2, 0, 0, 2, 0, 1, 2] 3 1 true = ([1, 1, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_1222120 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 0, 1] = [1, 1, 2, 2, 1, 1, 0] := by
  decide

theorem demoM_1222120 : fieldMul 7 5 20 [1, 1, 2, 2, 1, 1, 0] [1, 2, 2, 2, 1, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222120 : mirrorTrits [1, 1, 2, 2, 1, 1, 0] = [2, 2, 1, 1, 2, 2, 0] := by
  decide

theorem demoInv_1222120 : specInv 7 5 20 [1, 2, 2, 2, 1, 2, 0] = some [2, 2, 1, 1, 2, 2, 0] :=
  specInv_mirror_7 [1, 2, 2, 2, 1, 2, 0] [2, 0, 0, 2, 0, 1, 2] [1, 1, 2, 0, 0, 0, 1] [1, 1, 2, 2, 1, 1, 0] [2, 2, 1, 1, 2, 2, 0] demoR1_1222120 demoR2_1222120 demoC_1222120 demoM_1222120 demoMir_1222120

theorem demoR1_2222120 : invRung 7 5 20 [2, 2, 2, 2, 1, 2, 0] [2, 2, 2, 2, 1, 2, 0] 1 2 false = ([1, 2, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2222120 : invRung 7 5 20 [2, 2, 2, 2, 1, 2, 0] [1, 2, 1, 2, 1, 1, 2] 3 1 true = ([2, 0, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2222120 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 1, 1] = [0, 0, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_2222120 : fieldMul 7 5 20 [0, 0, 0, 2, 2, 0, 2] [2, 2, 2, 2, 1, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2222120 : specInv 7 5 20 [2, 2, 2, 2, 1, 2, 0] = some [0, 0, 0, 2, 2, 0, 2] :=
  specInv_white_7 [2, 2, 2, 2, 1, 2, 0] [1, 2, 1, 2, 1, 1, 2] [2, 0, 1, 0, 1, 1, 1] [0, 0, 0, 2, 2, 0, 2] demoR1_2222120 demoR2_2222120 demoC_2222120 demoM_2222120

theorem demoR1_0000220 : invRung 7 5 20 [0, 0, 0, 0, 2, 2, 0] [0, 0, 0, 0, 2, 2, 0] 1 2 false = ([0, 0, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_0000220 : invRung 7 5 20 [0, 0, 0, 0, 2, 2, 0] [0, 0, 0, 0, 0, 2, 2] 3 1 true = ([2, 1, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_0000220 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 0, 0] = [0, 2, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_0000220 : fieldMul 7 5 20 [0, 2, 1, 0, 0, 0, 0] [0, 0, 0, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000220 : mirrorTrits [0, 2, 1, 0, 0, 0, 0] = [0, 1, 2, 0, 0, 0, 0] := by
  decide

theorem demoInv_0000220 : specInv 7 5 20 [0, 0, 0, 0, 2, 2, 0] = some [0, 1, 2, 0, 0, 0, 0] :=
  specInv_mirror_7 [0, 0, 0, 0, 2, 2, 0] [0, 0, 0, 0, 0, 2, 2] [2, 1, 1, 1, 2, 0, 0] [0, 2, 1, 0, 0, 0, 0] [0, 1, 2, 0, 0, 0, 0] demoR1_0000220 demoR2_0000220 demoC_0000220 demoM_0000220 demoMir_0000220

theorem demoR1_1000220 : invRung 7 5 20 [1, 0, 0, 0, 2, 2, 0] [1, 0, 0, 0, 2, 2, 0] 1 2 false = ([1, 0, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_1000220 : invRung 7 5 20 [1, 0, 0, 0, 2, 2, 0] [1, 0, 2, 2, 1, 1, 0] 3 1 true = ([0, 2, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1000220 : fieldCube 7 5 20 [0, 2, 2, 1, 2, 2, 0] = [0, 1, 0, 1, 2, 2, 2] := by
  decide

theorem demoM_1000220 : fieldMul 7 5 20 [0, 1, 0, 1, 2, 2, 2] [1, 0, 0, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000220 : mirrorTrits [0, 1, 0, 1, 2, 2, 2] = [0, 2, 0, 2, 1, 1, 1] := by
  decide

theorem demoInv_1000220 : specInv 7 5 20 [1, 0, 0, 0, 2, 2, 0] = some [0, 2, 0, 2, 1, 1, 1] :=
  specInv_mirror_7 [1, 0, 0, 0, 2, 2, 0] [1, 0, 2, 2, 1, 1, 0] [0, 2, 2, 1, 2, 2, 0] [0, 1, 0, 1, 2, 2, 2] [0, 2, 0, 2, 1, 1, 1] demoR1_1000220 demoR2_1000220 demoC_1000220 demoM_1000220 demoMir_1000220

theorem demoR1_2000220 : invRung 7 5 20 [2, 0, 0, 0, 2, 2, 0] [2, 0, 0, 0, 2, 2, 0] 1 2 false = ([1, 2, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_2000220 : invRung 7 5 20 [2, 0, 0, 0, 2, 2, 0] [1, 2, 2, 2, 0, 1, 1] 3 1 true = ([1, 2, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_2000220 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 2, 0] = [0, 1, 2, 1, 2, 1, 1] := by
  decide

theorem demoM_2000220 : fieldMul 7 5 20 [0, 1, 2, 1, 2, 1, 1] [2, 0, 0, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000220 : mirrorTrits [0, 1, 2, 1, 2, 1, 1] = [0, 2, 1, 2, 1, 2, 2] := by
  decide

theorem demoInv_2000220 : specInv 7 5 20 [2, 0, 0, 0, 2, 2, 0] = some [0, 2, 1, 2, 1, 2, 2] :=
  specInv_mirror_7 [2, 0, 0, 0, 2, 2, 0] [1, 2, 2, 2, 0, 1, 1] [1, 2, 1, 0, 2, 2, 0] [0, 1, 2, 1, 2, 1, 1] [0, 2, 1, 2, 1, 2, 2] demoR1_2000220 demoR2_2000220 demoC_2000220 demoM_2000220 demoMir_2000220

theorem demoR1_0100220 : invRung 7 5 20 [0, 1, 0, 0, 2, 2, 0] [0, 1, 0, 0, 2, 2, 0] 1 2 false = ([1, 0, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0100220 : invRung 7 5 20 [0, 1, 0, 0, 2, 2, 0] [1, 0, 1, 0, 2, 1, 2] 3 1 true = ([1, 2, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_0100220 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 0, 0] = [0, 2, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_0100220 : fieldMul 7 5 20 [0, 2, 2, 1, 0, 1, 1] [0, 1, 0, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100220 : mirrorTrits [0, 2, 2, 1, 0, 1, 1] = [0, 1, 1, 2, 0, 2, 2] := by
  decide

theorem demoInv_0100220 : specInv 7 5 20 [0, 1, 0, 0, 2, 2, 0] = some [0, 1, 1, 2, 0, 2, 2] :=
  specInv_mirror_7 [0, 1, 0, 0, 2, 2, 0] [1, 0, 1, 0, 2, 1, 2] [1, 2, 2, 2, 2, 0, 0] [0, 2, 2, 1, 0, 1, 1] [0, 1, 1, 2, 0, 2, 2] demoR1_0100220 demoR2_0100220 demoC_0100220 demoM_0100220 demoMir_0100220

theorem demoR1_1100220 : invRung 7 5 20 [1, 1, 0, 0, 2, 2, 0] [1, 1, 0, 0, 2, 2, 0] 1 2 false = ([2, 2, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_1100220 : invRung 7 5 20 [1, 1, 0, 0, 2, 2, 0] [2, 2, 1, 0, 0, 0, 1] 3 1 true = ([0, 0, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1100220 : fieldCube 7 5 20 [0, 0, 1, 0, 0, 1, 0] = [1, 1, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_1100220 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 1, 0] [1, 1, 0, 0, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1100220 : specInv 7 5 20 [1, 1, 0, 0, 2, 2, 0] = some [1, 1, 1, 0, 1, 1, 0] :=
  specInv_white_7 [1, 1, 0, 0, 2, 2, 0] [2, 2, 1, 0, 0, 0, 1] [0, 0, 1, 0, 0, 1, 0] [1, 1, 1, 0, 1, 1, 0] demoR1_1100220 demoR2_1100220 demoC_1100220 demoM_1100220

theorem demoR1_2100220 : invRung 7 5 20 [2, 1, 0, 0, 2, 2, 0] [2, 1, 0, 0, 2, 2, 0] 1 2 false = ([1, 2, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2100220 : invRung 7 5 20 [2, 1, 0, 0, 2, 2, 0] [1, 2, 1, 0, 2, 2, 0] 3 1 true = ([1, 2, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_2100220 : fieldCube 7 5 20 [1, 2, 0, 2, 0, 2, 0] = [2, 2, 1, 2, 2, 1, 1] := by
  decide

theorem demoM_2100220 : fieldMul 7 5 20 [2, 2, 1, 2, 2, 1, 1] [2, 1, 0, 0, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2100220 : specInv 7 5 20 [2, 1, 0, 0, 2, 2, 0] = some [2, 2, 1, 2, 2, 1, 1] :=
  specInv_white_7 [2, 1, 0, 0, 2, 2, 0] [1, 2, 1, 0, 2, 2, 0] [1, 2, 0, 2, 0, 2, 0] [2, 2, 1, 2, 2, 1, 1] demoR1_2100220 demoR2_2100220 demoC_2100220 demoM_2100220

theorem demoR1_0200220 : invRung 7 5 20 [0, 2, 0, 0, 2, 2, 0] [0, 2, 0, 0, 2, 2, 0] 1 2 false = ([0, 1, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_0200220 : invRung 7 5 20 [0, 2, 0, 0, 2, 2, 0] [0, 1, 1, 2, 2, 1, 1] 3 1 true = ([0, 2, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0200220 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 1, 0] = [2, 1, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_0200220 : fieldMul 7 5 20 [2, 1, 2, 2, 1, 2, 2] [0, 2, 0, 0, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0200220 : specInv 7 5 20 [0, 2, 0, 0, 2, 2, 0] = some [2, 1, 2, 2, 1, 2, 2] :=
  specInv_white_7 [0, 2, 0, 0, 2, 2, 0] [0, 1, 1, 2, 2, 1, 1] [0, 2, 0, 1, 0, 1, 0] [2, 1, 2, 2, 1, 2, 2] demoR1_0200220 demoR2_0200220 demoC_0200220 demoM_0200220

theorem demoR1_1200220 : invRung 7 5 20 [1, 2, 0, 0, 2, 2, 0] [1, 2, 0, 0, 2, 2, 0] 1 2 false = ([1, 0, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_1200220 : invRung 7 5 20 [1, 2, 0, 0, 2, 2, 0] [1, 0, 2, 1, 2, 2, 2] 3 1 true = ([1, 0, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_1200220 : fieldCube 7 5 20 [1, 0, 1, 2, 2, 2, 0] = [2, 1, 1, 2, 2, 0, 1] := by
  decide

theorem demoM_1200220 : fieldMul 7 5 20 [2, 1, 1, 2, 2, 0, 1] [1, 2, 0, 0, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1200220 : specInv 7 5 20 [1, 2, 0, 0, 2, 2, 0] = some [2, 1, 1, 2, 2, 0, 1] :=
  specInv_white_7 [1, 2, 0, 0, 2, 2, 0] [1, 0, 2, 1, 2, 2, 2] [1, 0, 1, 2, 2, 2, 0] [2, 1, 1, 2, 2, 0, 1] demoR1_1200220 demoR2_1200220 demoC_1200220 demoM_1200220

theorem demoR1_2200220 : invRung 7 5 20 [2, 2, 0, 0, 2, 2, 0] [2, 2, 0, 0, 2, 2, 0] 1 2 false = ([2, 2, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_2200220 : invRung 7 5 20 [2, 2, 0, 0, 2, 2, 0] [2, 2, 2, 2, 0, 2, 0] 3 1 true = ([0, 0, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_2200220 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 1, 1] = [1, 0, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_2200220 : fieldMul 7 5 20 [1, 0, 0, 2, 2, 0, 1] [2, 2, 0, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200220 : mirrorTrits [1, 0, 0, 2, 2, 0, 1] = [2, 0, 0, 1, 1, 0, 2] := by
  decide

theorem demoInv_2200220 : specInv 7 5 20 [2, 2, 0, 0, 2, 2, 0] = some [2, 0, 0, 1, 1, 0, 2] :=
  specInv_mirror_7 [2, 2, 0, 0, 2, 2, 0] [2, 2, 2, 2, 0, 2, 0] [0, 0, 0, 0, 1, 1, 1] [1, 0, 0, 2, 2, 0, 1] [2, 0, 0, 1, 1, 0, 2] demoR1_2200220 demoR2_2200220 demoC_2200220 demoM_2200220 demoMir_2200220

theorem demoR1_0010220 : invRung 7 5 20 [0, 0, 1, 0, 2, 2, 0] [0, 0, 1, 0, 2, 2, 0] 1 2 false = ([0, 0, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_0010220 : invRung 7 5 20 [0, 0, 1, 0, 2, 2, 0] [0, 0, 0, 2, 2, 1, 1] 3 1 true = ([0, 0, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_0010220 : fieldCube 7 5 20 [0, 0, 1, 0, 1, 2, 0] = [2, 0, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_0010220 : fieldMul 7 5 20 [2, 0, 2, 1, 2, 0, 0] [0, 0, 1, 0, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0010220 : specInv 7 5 20 [0, 0, 1, 0, 2, 2, 0] = some [2, 0, 2, 1, 2, 0, 0] :=
  specInv_white_7 [0, 0, 1, 0, 2, 2, 0] [0, 0, 0, 2, 2, 1, 1] [0, 0, 1, 0, 1, 2, 0] [2, 0, 2, 1, 2, 0, 0] demoR1_0010220 demoR2_0010220 demoC_0010220 demoM_0010220

theorem demoR1_1010220 : invRung 7 5 20 [1, 0, 1, 0, 2, 2, 0] [1, 0, 1, 0, 2, 2, 0] 1 2 false = ([0, 0, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_1010220 : invRung 7 5 20 [1, 0, 1, 0, 2, 2, 0] [0, 0, 2, 1, 1, 2, 1] 3 1 true = ([1, 0, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1010220 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 2, 1] = [1, 1, 2, 2, 0, 2, 1] := by
  decide

theorem demoM_1010220 : fieldMul 7 5 20 [1, 1, 2, 2, 0, 2, 1] [1, 0, 1, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1010220 : mirrorTrits [1, 1, 2, 2, 0, 2, 1] = [2, 2, 1, 1, 0, 1, 2] := by
  decide

theorem demoInv_1010220 : specInv 7 5 20 [1, 0, 1, 0, 2, 2, 0] = some [2, 2, 1, 1, 0, 1, 2] :=
  specInv_mirror_7 [1, 0, 1, 0, 2, 2, 0] [0, 0, 2, 1, 1, 2, 1] [1, 0, 1, 1, 1, 2, 1] [1, 1, 2, 2, 0, 2, 1] [2, 2, 1, 1, 0, 1, 2] demoR1_1010220 demoR2_1010220 demoC_1010220 demoM_1010220 demoMir_1010220

theorem demoR1_2010220 : invRung 7 5 20 [2, 0, 1, 0, 2, 2, 0] [2, 0, 1, 0, 2, 2, 0] 1 2 false = ([2, 1, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_2010220 : invRung 7 5 20 [2, 0, 1, 0, 2, 2, 0] [2, 1, 2, 0, 0, 0, 2] 3 1 true = ([0, 2, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_2010220 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 1, 0] = [2, 2, 2, 0, 1, 0, 2] := by
  decide

theorem demoM_2010220 : fieldMul 7 5 20 [2, 2, 2, 0, 1, 0, 2] [2, 0, 1, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010220 : mirrorTrits [2, 2, 2, 0, 1, 0, 2] = [1, 1, 1, 0, 2, 0, 1] := by
  decide

theorem demoInv_2010220 : specInv 7 5 20 [2, 0, 1, 0, 2, 2, 0] = some [1, 1, 1, 0, 2, 0, 1] :=
  specInv_mirror_7 [2, 0, 1, 0, 2, 2, 0] [2, 1, 2, 0, 0, 0, 2] [0, 2, 2, 1, 1, 1, 0] [2, 2, 2, 0, 1, 0, 2] [1, 1, 1, 0, 2, 0, 1] demoR1_2010220 demoR2_2010220 demoC_2010220 demoM_2010220 demoMir_2010220

theorem demoR1_0110220 : invRung 7 5 20 [0, 1, 1, 0, 2, 2, 0] [0, 1, 1, 0, 2, 2, 0] 1 2 false = ([2, 1, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_0110220 : invRung 7 5 20 [0, 1, 1, 0, 2, 2, 0] [2, 1, 2, 1, 2, 0, 0] 3 1 true = ([1, 2, 1, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_0110220 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 1, 1] = [2, 1, 0, 2, 2, 1, 0] := by
  decide

theorem demoM_0110220 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 1, 0] [0, 1, 1, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110220 : mirrorTrits [2, 1, 0, 2, 2, 1, 0] = [1, 2, 0, 1, 1, 2, 0] := by
  decide

theorem demoInv_0110220 : specInv 7 5 20 [0, 1, 1, 0, 2, 2, 0] = some [1, 2, 0, 1, 1, 2, 0] :=
  specInv_mirror_7 [0, 1, 1, 0, 2, 2, 0] [2, 1, 2, 1, 2, 0, 0] [1, 2, 1, 0, 2, 1, 1] [2, 1, 0, 2, 2, 1, 0] [1, 2, 0, 1, 1, 2, 0] demoR1_0110220 demoR2_0110220 demoC_0110220 demoM_0110220 demoMir_0110220

theorem demoR1_1110220 : invRung 7 5 20 [1, 1, 1, 0, 2, 2, 0] [1, 1, 1, 0, 2, 2, 0] 1 2 false = ([2, 2, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_1110220 : invRung 7 5 20 [1, 1, 1, 0, 2, 2, 0] [2, 2, 0, 0, 2, 2, 0] 3 1 true = ([2, 0, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_1110220 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 0, 2] = [2, 0, 1, 0, 2, 0, 1] := by
  decide

theorem demoM_1110220 : fieldMul 7 5 20 [2, 0, 1, 0, 2, 0, 1] [1, 1, 1, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1110220 : mirrorTrits [2, 0, 1, 0, 2, 0, 1] = [1, 0, 2, 0, 1, 0, 2] := by
  decide

theorem demoInv_1110220 : specInv 7 5 20 [1, 1, 1, 0, 2, 2, 0] = some [1, 0, 2, 0, 1, 0, 2] :=
  specInv_mirror_7 [1, 1, 1, 0, 2, 2, 0] [2, 2, 0, 0, 2, 2, 0] [2, 0, 1, 0, 1, 0, 2] [2, 0, 1, 0, 2, 0, 1] [1, 0, 2, 0, 1, 0, 2] demoR1_1110220 demoR2_1110220 demoC_1110220 demoM_1110220 demoMir_1110220

theorem demoR1_2110220 : invRung 7 5 20 [2, 1, 1, 0, 2, 2, 0] [2, 1, 1, 0, 2, 2, 0] 1 2 false = ([0, 0, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2110220 : invRung 7 5 20 [2, 1, 1, 0, 2, 2, 0] [0, 0, 1, 1, 2, 0, 1] 3 1 true = ([0, 0, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_2110220 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 1, 1] = [0, 1, 2, 0, 2, 0, 0] := by
  decide

theorem demoM_2110220 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 0, 0] [2, 1, 1, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110220 : mirrorTrits [0, 1, 2, 0, 2, 0, 0] = [0, 2, 1, 0, 1, 0, 0] := by
  decide

theorem demoInv_2110220 : specInv 7 5 20 [2, 1, 1, 0, 2, 2, 0] = some [0, 2, 1, 0, 1, 0, 0] :=
  specInv_mirror_7 [2, 1, 1, 0, 2, 2, 0] [0, 0, 1, 1, 2, 0, 1] [0, 0, 1, 2, 2, 1, 1] [0, 1, 2, 0, 2, 0, 0] [0, 2, 1, 0, 1, 0, 0] demoR1_2110220 demoR2_2110220 demoC_2110220 demoM_2110220 demoMir_2110220

theorem demoR1_0210220 : invRung 7 5 20 [0, 2, 1, 0, 2, 2, 0] [0, 2, 1, 0, 2, 2, 0] 1 2 false = ([0, 2, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_0210220 : invRung 7 5 20 [0, 2, 1, 0, 2, 2, 0] [0, 2, 1, 2, 0, 1, 1] 3 1 true = ([2, 2, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_0210220 : fieldCube 7 5 20 [2, 2, 0, 2, 2, 2, 0] = [0, 1, 1, 1, 2, 0, 0] := by
  decide

theorem demoM_0210220 : fieldMul 7 5 20 [0, 1, 1, 1, 2, 0, 0] [0, 2, 1, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210220 : mirrorTrits [0, 1, 1, 1, 2, 0, 0] = [0, 2, 2, 2, 1, 0, 0] := by
  decide

theorem demoInv_0210220 : specInv 7 5 20 [0, 2, 1, 0, 2, 2, 0] = some [0, 2, 2, 2, 1, 0, 0] :=
  specInv_mirror_7 [0, 2, 1, 0, 2, 2, 0] [0, 2, 1, 2, 0, 1, 1] [2, 2, 0, 2, 2, 2, 0] [0, 1, 1, 1, 2, 0, 0] [0, 2, 2, 2, 1, 0, 0] demoR1_0210220 demoR2_0210220 demoC_0210220 demoM_0210220 demoMir_0210220

theorem demoR1_1210220 : invRung 7 5 20 [1, 2, 1, 0, 2, 2, 0] [1, 2, 1, 0, 2, 2, 0] 1 2 false = ([0, 2, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_1210220 : invRung 7 5 20 [1, 2, 1, 0, 2, 2, 0] [0, 2, 1, 2, 0, 0, 2] 3 1 true = ([2, 2, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1210220 : fieldCube 7 5 20 [2, 2, 0, 0, 1, 1, 1] = [0, 0, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_1210220 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 0, 1] [1, 2, 1, 0, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1210220 : specInv 7 5 20 [1, 2, 1, 0, 2, 2, 0] = some [0, 0, 0, 1, 2, 0, 1] :=
  specInv_white_7 [1, 2, 1, 0, 2, 2, 0] [0, 2, 1, 2, 0, 0, 2] [2, 2, 0, 0, 1, 1, 1] [0, 0, 0, 1, 2, 0, 1] demoR1_1210220 demoR2_1210220 demoC_1210220 demoM_1210220

theorem demoR1_2210220 : invRung 7 5 20 [2, 2, 1, 0, 2, 2, 0] [2, 2, 1, 0, 2, 2, 0] 1 2 false = ([0, 1, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_2210220 : invRung 7 5 20 [2, 2, 1, 0, 2, 2, 0] [0, 1, 0, 0, 0, 0, 1] 3 1 true = ([0, 2, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2210220 : fieldCube 7 5 20 [0, 2, 1, 0, 0, 1, 0] = [1, 1, 1, 2, 1, 1, 0] := by
  decide

theorem demoM_2210220 : fieldMul 7 5 20 [1, 1, 1, 2, 1, 1, 0] [2, 2, 1, 0, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2210220 : specInv 7 5 20 [2, 2, 1, 0, 2, 2, 0] = some [1, 1, 1, 2, 1, 1, 0] :=
  specInv_white_7 [2, 2, 1, 0, 2, 2, 0] [0, 1, 0, 0, 0, 0, 1] [0, 2, 1, 0, 0, 1, 0] [1, 1, 1, 2, 1, 1, 0] demoR1_2210220 demoR2_2210220 demoC_2210220 demoM_2210220

theorem demoR1_0020220 : invRung 7 5 20 [0, 0, 2, 0, 2, 2, 0] [0, 0, 2, 0, 2, 2, 0] 1 2 false = ([0, 1, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_0020220 : invRung 7 5 20 [0, 0, 2, 0, 2, 2, 0] [0, 1, 1, 2, 1, 0, 1] 3 1 true = ([0, 2, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_0020220 : fieldCube 7 5 20 [0, 2, 2, 2, 1, 2, 0] = [1, 0, 1, 0, 2, 2, 1] := by
  decide

theorem demoM_0020220 : fieldMul 7 5 20 [1, 0, 1, 0, 2, 2, 1] [0, 0, 2, 0, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0020220 : specInv 7 5 20 [0, 0, 2, 0, 2, 2, 0] = some [1, 0, 1, 0, 2, 2, 1] :=
  specInv_white_7 [0, 0, 2, 0, 2, 2, 0] [0, 1, 1, 2, 1, 0, 1] [0, 2, 2, 2, 1, 2, 0] [1, 0, 1, 0, 2, 2, 1] demoR1_0020220 demoR2_0020220 demoC_0020220 demoM_0020220

theorem demoR1_1020220 : invRung 7 5 20 [1, 0, 2, 0, 2, 2, 0] [1, 0, 2, 0, 2, 2, 0] 1 2 false = ([1, 1, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1020220 : invRung 7 5 20 [1, 0, 2, 0, 2, 2, 0] [1, 1, 1, 1, 1, 0, 2] 3 1 true = ([1, 2, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1020220 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 2, 0] = [1, 1, 0, 1, 2, 2, 1] := by
  decide

theorem demoM_1020220 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 2, 1] [1, 0, 2, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020220 : mirrorTrits [1, 1, 0, 1, 2, 2, 1] = [2, 2, 0, 2, 1, 1, 2] := by
  decide

theorem demoInv_1020220 : specInv 7 5 20 [1, 0, 2, 0, 2, 2, 0] = some [2, 2, 0, 2, 1, 1, 2] :=
  specInv_mirror_7 [1, 0, 2, 0, 2, 2, 0] [1, 1, 1, 1, 1, 0, 2] [1, 2, 1, 1, 2, 2, 0] [1, 1, 0, 1, 2, 2, 1] [2, 2, 0, 2, 1, 1, 2] demoR1_1020220 demoR2_1020220 demoC_1020220 demoM_1020220 demoMir_1020220

theorem demoR1_2020220 : invRung 7 5 20 [2, 0, 2, 0, 2, 2, 0] [2, 0, 2, 0, 2, 2, 0] 1 2 false = ([1, 1, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_2020220 : invRung 7 5 20 [2, 0, 2, 0, 2, 2, 0] [1, 1, 2, 2, 0, 2, 2] 3 1 true = ([1, 0, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_2020220 : fieldCube 7 5 20 [1, 0, 0, 2, 2, 0, 2] = [0, 1, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_2020220 : fieldMul 7 5 20 [0, 1, 0, 1, 2, 0, 1] [2, 0, 2, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020220 : mirrorTrits [0, 1, 0, 1, 2, 0, 1] = [0, 2, 0, 2, 1, 0, 2] := by
  decide

theorem demoInv_2020220 : specInv 7 5 20 [2, 0, 2, 0, 2, 2, 0] = some [0, 2, 0, 2, 1, 0, 2] :=
  specInv_mirror_7 [2, 0, 2, 0, 2, 2, 0] [1, 1, 2, 2, 0, 2, 2] [1, 0, 0, 2, 2, 0, 2] [0, 1, 0, 1, 2, 0, 1] [0, 2, 0, 2, 1, 0, 2] demoR1_2020220 demoR2_2020220 demoC_2020220 demoM_2020220 demoMir_2020220

theorem demoR1_0120220 : invRung 7 5 20 [0, 1, 2, 0, 2, 2, 0] [0, 1, 2, 0, 2, 2, 0] 1 2 false = ([0, 2, 0, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_0120220 : invRung 7 5 20 [0, 1, 2, 0, 2, 2, 0] [0, 2, 0, 2, 1, 1, 1] 3 1 true = ([2, 0, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_0120220 : fieldCube 7 5 20 [2, 0, 2, 1, 0, 1, 1] = [1, 2, 1, 1, 2, 0, 2] := by
  decide

theorem demoM_0120220 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 0, 2] [0, 1, 2, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0120220 : mirrorTrits [1, 2, 1, 1, 2, 0, 2] = [2, 1, 2, 2, 1, 0, 1] := by
  decide

theorem demoInv_0120220 : specInv 7 5 20 [0, 1, 2, 0, 2, 2, 0] = some [2, 1, 2, 2, 1, 0, 1] :=
  specInv_mirror_7 [0, 1, 2, 0, 2, 2, 0] [0, 2, 0, 2, 1, 1, 1] [2, 0, 2, 1, 0, 1, 1] [1, 2, 1, 1, 2, 0, 2] [2, 1, 2, 2, 1, 0, 1] demoR1_0120220 demoR2_0120220 demoC_0120220 demoM_0120220 demoMir_0120220

theorem demoR1_1120220 : invRung 7 5 20 [1, 1, 2, 0, 2, 2, 0] [1, 1, 2, 0, 2, 2, 0] 1 2 false = ([1, 2, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_1120220 : invRung 7 5 20 [1, 1, 2, 0, 2, 2, 0] [1, 2, 0, 0, 0, 0, 1] 3 1 true = ([0, 2, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1120220 : fieldCube 7 5 20 [0, 2, 2, 1, 0, 2, 1] = [0, 0, 2, 0, 0, 1, 1] := by
  decide

theorem demoM_1120220 : fieldMul 7 5 20 [0, 0, 2, 0, 0, 1, 1] [1, 1, 2, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120220 : mirrorTrits [0, 0, 2, 0, 0, 1, 1] = [0, 0, 1, 0, 0, 2, 2] := by
  decide

theorem demoInv_1120220 : specInv 7 5 20 [1, 1, 2, 0, 2, 2, 0] = some [0, 0, 1, 0, 0, 2, 2] :=
  specInv_mirror_7 [1, 1, 2, 0, 2, 2, 0] [1, 2, 0, 0, 0, 0, 1] [0, 2, 2, 1, 0, 2, 1] [0, 0, 2, 0, 0, 1, 1] [0, 0, 1, 0, 0, 2, 2] demoR1_1120220 demoR2_1120220 demoC_1120220 demoM_1120220 demoMir_1120220

theorem demoR1_2120220 : invRung 7 5 20 [2, 1, 2, 0, 2, 2, 0] [2, 1, 2, 0, 2, 2, 0] 1 2 false = ([0, 1, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_2120220 : invRung 7 5 20 [2, 1, 2, 0, 2, 2, 0] [0, 1, 0, 2, 1, 0, 0] 3 1 true = ([2, 2, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_2120220 : fieldCube 7 5 20 [2, 2, 2, 1, 1, 1, 2] = [1, 1, 0, 2, 0, 2, 1] := by
  decide

theorem demoM_2120220 : fieldMul 7 5 20 [1, 1, 0, 2, 0, 2, 1] [2, 1, 2, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120220 : mirrorTrits [1, 1, 0, 2, 0, 2, 1] = [2, 2, 0, 1, 0, 1, 2] := by
  decide

theorem demoInv_2120220 : specInv 7 5 20 [2, 1, 2, 0, 2, 2, 0] = some [2, 2, 0, 1, 0, 1, 2] :=
  specInv_mirror_7 [2, 1, 2, 0, 2, 2, 0] [0, 1, 0, 2, 1, 0, 0] [2, 2, 2, 1, 1, 1, 2] [1, 1, 0, 2, 0, 2, 1] [2, 2, 0, 1, 0, 1, 2] demoR1_2120220 demoR2_2120220 demoC_2120220 demoM_2120220 demoMir_2120220

theorem demoR1_0220220 : invRung 7 5 20 [0, 2, 2, 0, 2, 2, 0] [0, 2, 2, 0, 2, 2, 0] 1 2 false = ([0, 2, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_0220220 : invRung 7 5 20 [0, 2, 2, 0, 2, 2, 0] [0, 2, 0, 1, 2, 2, 0] 3 1 true = ([0, 2, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_0220220 : fieldCube 7 5 20 [0, 2, 2, 2, 2, 0, 0] = [2, 2, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_0220220 : fieldMul 7 5 20 [2, 2, 2, 1, 0, 1, 1] [0, 2, 2, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0220220 : mirrorTrits [2, 2, 2, 1, 0, 1, 1] = [1, 1, 1, 2, 0, 2, 2] := by
  decide

theorem demoInv_0220220 : specInv 7 5 20 [0, 2, 2, 0, 2, 2, 0] = some [1, 1, 1, 2, 0, 2, 2] :=
  specInv_mirror_7 [0, 2, 2, 0, 2, 2, 0] [0, 2, 0, 1, 2, 2, 0] [0, 2, 2, 2, 2, 0, 0] [2, 2, 2, 1, 0, 1, 1] [1, 1, 1, 2, 0, 2, 2] demoR1_0220220 demoR2_0220220 demoC_0220220 demoM_0220220 demoMir_0220220

theorem demoR1_1220220 : invRung 7 5 20 [1, 2, 2, 0, 2, 2, 0] [1, 2, 2, 0, 2, 2, 0] 1 2 false = ([1, 0, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_1220220 : invRung 7 5 20 [1, 2, 2, 0, 2, 2, 0] [1, 0, 0, 2, 2, 2, 0] 3 1 true = ([0, 1, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_1220220 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 1, 0] = [2, 1, 2, 1, 1, 2, 2] := by
  decide

theorem demoM_1220220 : fieldMul 7 5 20 [2, 1, 2, 1, 1, 2, 2] [1, 2, 2, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220220 : mirrorTrits [2, 1, 2, 1, 1, 2, 2] = [1, 2, 1, 2, 2, 1, 1] := by
  decide

theorem demoInv_1220220 : specInv 7 5 20 [1, 2, 2, 0, 2, 2, 0] = some [1, 2, 1, 2, 2, 1, 1] :=
  specInv_mirror_7 [1, 2, 2, 0, 2, 2, 0] [1, 0, 0, 2, 2, 2, 0] [0, 1, 0, 1, 0, 1, 0] [2, 1, 2, 1, 1, 2, 2] [1, 2, 1, 2, 2, 1, 1] demoR1_1220220 demoR2_1220220 demoC_1220220 demoM_1220220 demoMir_1220220

theorem demoR1_2220220 : invRung 7 5 20 [2, 2, 2, 0, 2, 2, 0] [2, 2, 2, 0, 2, 2, 0] 1 2 false = ([2, 2, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_2220220 : invRung 7 5 20 [2, 2, 2, 0, 2, 2, 0] [2, 2, 2, 0, 1, 2, 2] 3 1 true = ([1, 1, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_2220220 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 2, 0] = [1, 1, 0, 0, 2, 2, 0] := by
  decide

theorem demoM_2220220 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 2, 0] [2, 2, 2, 0, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220220 : mirrorTrits [1, 1, 0, 0, 2, 2, 0] = [2, 2, 0, 0, 1, 1, 0] := by
  decide

theorem demoInv_2220220 : specInv 7 5 20 [2, 2, 2, 0, 2, 2, 0] = some [2, 2, 0, 0, 1, 1, 0] :=
  specInv_mirror_7 [2, 2, 2, 0, 2, 2, 0] [2, 2, 2, 0, 1, 2, 2] [1, 1, 0, 1, 2, 2, 0] [1, 1, 0, 0, 2, 2, 0] [2, 2, 0, 0, 1, 1, 0] demoR1_2220220 demoR2_2220220 demoC_2220220 demoM_2220220 demoMir_2220220

theorem demoR1_0001220 : invRung 7 5 20 [0, 0, 0, 1, 2, 2, 0] [0, 0, 0, 1, 2, 2, 0] 1 2 false = ([1, 0, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_0001220 : invRung 7 5 20 [0, 0, 0, 1, 2, 2, 0] [1, 0, 2, 2, 2, 0, 2] 3 1 true = ([1, 1, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_0001220 : fieldCube 7 5 20 [1, 1, 1, 2, 2, 1, 0] = [1, 0, 0, 0, 1, 2, 2] := by
  decide

theorem demoM_0001220 : fieldMul 7 5 20 [1, 0, 0, 0, 1, 2, 2] [0, 0, 0, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0001220 : specInv 7 5 20 [0, 0, 0, 1, 2, 2, 0] = some [1, 0, 0, 0, 1, 2, 2] :=
  specInv_white_7 [0, 0, 0, 1, 2, 2, 0] [1, 0, 2, 2, 2, 0, 2] [1, 1, 1, 2, 2, 1, 0] [1, 0, 0, 0, 1, 2, 2] demoR1_0001220 demoR2_0001220 demoC_0001220 demoM_0001220

theorem demoR1_1001220 : invRung 7 5 20 [1, 0, 0, 1, 2, 2, 0] [1, 0, 0, 1, 2, 2, 0] 1 2 false = ([2, 1, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1001220 : invRung 7 5 20 [1, 0, 0, 1, 2, 2, 0] [2, 1, 2, 1, 1, 0, 0] 3 1 true = ([2, 1, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_1001220 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 1, 2] = [2, 2, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_1001220 : fieldMul 7 5 20 [2, 2, 1, 2, 0, 1, 0] [1, 0, 0, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1001220 : specInv 7 5 20 [1, 0, 0, 1, 2, 2, 0] = some [2, 2, 1, 2, 0, 1, 0] :=
  specInv_white_7 [1, 0, 0, 1, 2, 2, 0] [2, 1, 2, 1, 1, 0, 0] [2, 1, 0, 2, 2, 1, 2] [2, 2, 1, 2, 0, 1, 0] demoR1_1001220 demoR2_1001220 demoC_1001220 demoM_1001220

theorem demoR1_2001220 : invRung 7 5 20 [2, 0, 0, 1, 2, 2, 0] [2, 0, 0, 1, 2, 2, 0] 1 2 false = ([2, 0, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_2001220 : invRung 7 5 20 [2, 0, 0, 1, 2, 2, 0] [2, 0, 1, 0, 0, 2, 1] 3 1 true = ([1, 2, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_2001220 : fieldCube 7 5 20 [1, 2, 0, 2, 2, 1, 0] = [1, 0, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_2001220 : fieldMul 7 5 20 [1, 0, 0, 1, 1, 2, 1] [2, 0, 0, 1, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001220 : mirrorTrits [1, 0, 0, 1, 1, 2, 1] = [2, 0, 0, 2, 2, 1, 2] := by
  decide

theorem demoInv_2001220 : specInv 7 5 20 [2, 0, 0, 1, 2, 2, 0] = some [2, 0, 0, 2, 2, 1, 2] :=
  specInv_mirror_7 [2, 0, 0, 1, 2, 2, 0] [2, 0, 1, 0, 0, 2, 1] [1, 2, 0, 2, 2, 1, 0] [1, 0, 0, 1, 1, 2, 1] [2, 0, 0, 2, 2, 1, 2] demoR1_2001220 demoR2_2001220 demoC_2001220 demoM_2001220 demoMir_2001220

theorem demoR1_0101220 : invRung 7 5 20 [0, 1, 0, 1, 2, 2, 0] [0, 1, 0, 1, 2, 2, 0] 1 2 false = ([2, 1, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_0101220 : invRung 7 5 20 [0, 1, 0, 1, 2, 2, 0] [2, 1, 1, 1, 1, 1, 1] 3 1 true = ([0, 0, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_0101220 : fieldCube 7 5 20 [0, 0, 1, 1, 0, 0, 2] = [1, 2, 2, 2, 2, 0, 0] := by
  decide

theorem demoM_0101220 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 0, 0] [0, 1, 0, 1, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101220 : mirrorTrits [1, 2, 2, 2, 2, 0, 0] = [2, 1, 1, 1, 1, 0, 0] := by
  decide

theorem demoInv_0101220 : specInv 7 5 20 [0, 1, 0, 1, 2, 2, 0] = some [2, 1, 1, 1, 1, 0, 0] :=
  specInv_mirror_7 [0, 1, 0, 1, 2, 2, 0] [2, 1, 1, 1, 1, 1, 1] [0, 0, 1, 1, 0, 0, 2] [1, 2, 2, 2, 2, 0, 0] [2, 1, 1, 1, 1, 0, 0] demoR1_0101220 demoR2_0101220 demoC_0101220 demoM_0101220 demoMir_0101220

theorem demoR1_1101220 : invRung 7 5 20 [1, 1, 0, 1, 2, 2, 0] [1, 1, 0, 1, 2, 2, 0] 1 2 false = ([1, 1, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_1101220 : invRung 7 5 20 [1, 1, 0, 1, 2, 2, 0] [1, 1, 2, 1, 2, 0, 0] 3 1 true = ([2, 0, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_1101220 : fieldCube 7 5 20 [2, 0, 0, 1, 0, 0, 0] = [0, 0, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_1101220 : fieldMul 7 5 20 [0, 0, 1, 0, 0, 1, 0] [1, 1, 0, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1101220 : specInv 7 5 20 [1, 1, 0, 1, 2, 2, 0] = some [0, 0, 1, 0, 0, 1, 0] :=
  specInv_white_7 [1, 1, 0, 1, 2, 2, 0] [1, 1, 2, 1, 2, 0, 0] [2, 0, 0, 1, 0, 0, 0] [0, 0, 1, 0, 0, 1, 0] demoR1_1101220 demoR2_1101220 demoC_1101220 demoM_1101220

theorem demoR1_2101220 : invRung 7 5 20 [2, 1, 0, 1, 2, 2, 0] [2, 1, 0, 1, 2, 2, 0] 1 2 false = ([1, 1, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_2101220 : invRung 7 5 20 [2, 1, 0, 1, 2, 2, 0] [1, 1, 1, 0, 0, 0, 2] 3 1 true = ([1, 0, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_2101220 : fieldCube 7 5 20 [1, 0, 1, 0, 2, 0, 0] = [1, 2, 0, 2, 0, 2, 0] := by
  decide

theorem demoM_2101220 : fieldMul 7 5 20 [1, 2, 0, 2, 0, 2, 0] [2, 1, 0, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2101220 : specInv 7 5 20 [2, 1, 0, 1, 2, 2, 0] = some [1, 2, 0, 2, 0, 2, 0] :=
  specInv_white_7 [2, 1, 0, 1, 2, 2, 0] [1, 1, 1, 0, 0, 0, 2] [1, 0, 1, 0, 2, 0, 0] [1, 2, 0, 2, 0, 2, 0] demoR1_2101220 demoR2_2101220 demoC_2101220 demoM_2101220

theorem demoR1_0201220 : invRung 7 5 20 [0, 2, 0, 1, 2, 2, 0] [0, 2, 0, 1, 2, 2, 0] 1 2 false = ([1, 1, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_0201220 : invRung 7 5 20 [0, 2, 0, 1, 2, 2, 0] [1, 1, 2, 0, 0, 1, 0] 3 1 true = ([1, 0, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0201220 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 2, 1] = [0, 0, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_0201220 : fieldMul 7 5 20 [0, 0, 1, 1, 0, 0, 2] [0, 2, 0, 1, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201220 : mirrorTrits [0, 0, 1, 1, 0, 0, 2] = [0, 0, 2, 2, 0, 0, 1] := by
  decide

theorem demoInv_0201220 : specInv 7 5 20 [0, 2, 0, 1, 2, 2, 0] = some [0, 0, 2, 2, 0, 0, 1] :=
  specInv_mirror_7 [0, 2, 0, 1, 2, 2, 0] [1, 1, 2, 0, 0, 1, 0] [1, 0, 0, 0, 0, 2, 1] [0, 0, 1, 1, 0, 0, 2] [0, 0, 2, 2, 0, 0, 1] demoR1_0201220 demoR2_0201220 demoC_0201220 demoM_0201220 demoMir_0201220

theorem demoR1_1201220 : invRung 7 5 20 [1, 2, 0, 1, 2, 2, 0] [1, 2, 0, 1, 2, 2, 0] 1 2 false = ([1, 1, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1201220 : invRung 7 5 20 [1, 2, 0, 1, 2, 2, 0] [1, 1, 1, 2, 2, 1, 1] 3 1 true = ([2, 1, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_1201220 : fieldCube 7 5 20 [2, 1, 0, 0, 0, 0, 0] = [2, 0, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_1201220 : fieldMul 7 5 20 [2, 0, 0, 1, 0, 0, 0] [1, 2, 0, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1201220 : specInv 7 5 20 [1, 2, 0, 1, 2, 2, 0] = some [2, 0, 0, 1, 0, 0, 0] :=
  specInv_white_7 [1, 2, 0, 1, 2, 2, 0] [1, 1, 1, 2, 2, 1, 1] [2, 1, 0, 0, 0, 0, 0] [2, 0, 0, 1, 0, 0, 0] demoR1_1201220 demoR2_1201220 demoC_1201220 demoM_1201220

theorem demoR1_2201220 : invRung 7 5 20 [2, 2, 0, 1, 2, 2, 0] [2, 2, 0, 1, 2, 2, 0] 1 2 false = ([1, 0, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2201220 : invRung 7 5 20 [2, 2, 0, 1, 2, 2, 0] [1, 0, 0, 2, 1, 1, 2] 3 1 true = ([1, 0, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_2201220 : fieldCube 7 5 20 [1, 0, 0, 0, 1, 0, 2] = [1, 0, 1, 0, 2, 0, 0] := by
  decide

theorem demoM_2201220 : fieldMul 7 5 20 [1, 0, 1, 0, 2, 0, 0] [2, 2, 0, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2201220 : specInv 7 5 20 [2, 2, 0, 1, 2, 2, 0] = some [1, 0, 1, 0, 2, 0, 0] :=
  specInv_white_7 [2, 2, 0, 1, 2, 2, 0] [1, 0, 0, 2, 1, 1, 2] [1, 0, 0, 0, 1, 0, 2] [1, 0, 1, 0, 2, 0, 0] demoR1_2201220 demoR2_2201220 demoC_2201220 demoM_2201220

theorem demoR1_0011220 : invRung 7 5 20 [0, 0, 1, 1, 2, 2, 0] [0, 0, 1, 1, 2, 2, 0] 1 2 false = ([1, 1, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_0011220 : invRung 7 5 20 [0, 0, 1, 1, 2, 2, 0] [1, 1, 1, 1, 2, 1, 1] 3 1 true = ([1, 2, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_0011220 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 1, 2] = [1, 2, 1, 0, 0, 1, 2] := by
  decide

theorem demoM_0011220 : fieldMul 7 5 20 [1, 2, 1, 0, 0, 1, 2] [0, 0, 1, 1, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011220 : mirrorTrits [1, 2, 1, 0, 0, 1, 2] = [2, 1, 2, 0, 0, 2, 1] := by
  decide

theorem demoInv_0011220 : specInv 7 5 20 [0, 0, 1, 1, 2, 2, 0] = some [2, 1, 2, 0, 0, 2, 1] :=
  specInv_mirror_7 [0, 0, 1, 1, 2, 2, 0] [1, 1, 1, 1, 2, 1, 1] [1, 2, 2, 2, 2, 1, 2] [1, 2, 1, 0, 0, 1, 2] [2, 1, 2, 0, 0, 2, 1] demoR1_0011220 demoR2_0011220 demoC_0011220 demoM_0011220 demoMir_0011220

theorem demoR1_1011220 : invRung 7 5 20 [1, 0, 1, 1, 2, 2, 0] [1, 0, 1, 1, 2, 2, 0] 1 2 false = ([1, 0, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_1011220 : invRung 7 5 20 [1, 0, 1, 1, 2, 2, 0] [1, 0, 2, 2, 1, 1, 2] 3 1 true = ([1, 0, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_1011220 : fieldCube 7 5 20 [1, 0, 2, 2, 0, 2, 0] = [2, 2, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_1011220 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 1, 0] [1, 0, 1, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1011220 : specInv 7 5 20 [1, 0, 1, 1, 2, 2, 0] = some [2, 2, 1, 0, 2, 1, 0] :=
  specInv_white_7 [1, 0, 1, 1, 2, 2, 0] [1, 0, 2, 2, 1, 1, 2] [1, 0, 2, 2, 0, 2, 0] [2, 2, 1, 0, 2, 1, 0] demoR1_1011220 demoR2_1011220 demoC_1011220 demoM_1011220

theorem demoR1_2011220 : invRung 7 5 20 [2, 0, 1, 1, 2, 2, 0] [2, 0, 1, 1, 2, 2, 0] 1 2 false = ([0, 2, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_2011220 : invRung 7 5 20 [2, 0, 1, 1, 2, 2, 0] [0, 2, 2, 2, 2, 2, 1] 3 1 true = ([0, 1, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_2011220 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 0, 2] = [0, 0, 1, 1, 2, 0, 2] := by
  decide

theorem demoM_2011220 : fieldMul 7 5 20 [0, 0, 1, 1, 2, 0, 2] [2, 0, 1, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2011220 : specInv 7 5 20 [2, 0, 1, 1, 2, 2, 0] = some [0, 0, 1, 1, 2, 0, 2] :=
  specInv_white_7 [2, 0, 1, 1, 2, 2, 0] [0, 2, 2, 2, 2, 2, 1] [0, 1, 2, 0, 1, 0, 2] [0, 0, 1, 1, 2, 0, 2] demoR1_2011220 demoR2_2011220 demoC_2011220 demoM_2011220

theorem demoR1_0111220 : invRung 7 5 20 [0, 1, 1, 1, 2, 2, 0] [0, 1, 1, 1, 2, 2, 0] 1 2 false = ([1, 2, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_0111220 : invRung 7 5 20 [0, 1, 1, 1, 2, 2, 0] [1, 2, 0, 0, 1, 1, 2] 3 1 true = ([0, 1, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0111220 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 0, 0] = [1, 0, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_0111220 : fieldMul 7 5 20 [1, 0, 1, 1, 0, 1, 1] [0, 1, 1, 1, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111220 : mirrorTrits [1, 0, 1, 1, 0, 1, 1] = [2, 0, 2, 2, 0, 2, 2] := by
  decide

theorem demoInv_0111220 : specInv 7 5 20 [0, 1, 1, 1, 2, 2, 0] = some [2, 0, 2, 2, 0, 2, 2] :=
  specInv_mirror_7 [0, 1, 1, 1, 2, 2, 0] [1, 2, 0, 0, 1, 1, 2] [0, 1, 1, 1, 0, 0, 0] [1, 0, 1, 1, 0, 1, 1] [2, 0, 2, 2, 0, 2, 2] demoR1_0111220 demoR2_0111220 demoC_0111220 demoM_0111220 demoMir_0111220

theorem demoR1_1111220 : invRung 7 5 20 [1, 1, 1, 1, 2, 2, 0] [1, 1, 1, 1, 2, 2, 0] 1 2 false = ([2, 2, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_1111220 : invRung 7 5 20 [1, 1, 1, 1, 2, 2, 0] [2, 2, 0, 1, 0, 1, 0] 3 1 true = ([2, 0, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_1111220 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 2, 0] = [0, 2, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_1111220 : fieldMul 7 5 20 [0, 2, 1, 0, 2, 1, 2] [1, 1, 1, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1111220 : specInv 7 5 20 [1, 1, 1, 1, 2, 2, 0] = some [0, 2, 1, 0, 2, 1, 2] :=
  specInv_white_7 [1, 1, 1, 1, 2, 2, 0] [2, 2, 0, 1, 0, 1, 0] [2, 0, 1, 2, 0, 2, 0] [0, 2, 1, 0, 2, 1, 2] demoR1_1111220 demoR2_1111220 demoC_1111220 demoM_1111220

theorem demoR1_2111220 : invRung 7 5 20 [2, 1, 1, 1, 2, 2, 0] [2, 1, 1, 1, 2, 2, 0] 1 2 false = ([1, 1, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2111220 : invRung 7 5 20 [2, 1, 1, 1, 2, 2, 0] [1, 1, 1, 0, 1, 1, 2] 3 1 true = ([2, 1, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_2111220 : fieldCube 7 5 20 [2, 1, 0, 2, 0, 0, 2] = [1, 2, 0, 0, 2, 1, 2] := by
  decide

theorem demoM_2111220 : fieldMul 7 5 20 [1, 2, 0, 0, 2, 1, 2] [2, 1, 1, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2111220 : specInv 7 5 20 [2, 1, 1, 1, 2, 2, 0] = some [1, 2, 0, 0, 2, 1, 2] :=
  specInv_white_7 [2, 1, 1, 1, 2, 2, 0] [1, 1, 1, 0, 1, 1, 2] [2, 1, 0, 2, 0, 0, 2] [1, 2, 0, 0, 2, 1, 2] demoR1_2111220 demoR2_2111220 demoC_2111220 demoM_2111220

theorem demoR1_0211220 : invRung 7 5 20 [0, 2, 1, 1, 2, 2, 0] [0, 2, 1, 1, 2, 2, 0] 1 2 false = ([0, 1, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_0211220 : invRung 7 5 20 [0, 2, 1, 1, 2, 2, 0] [0, 1, 2, 2, 0, 1, 0] 3 1 true = ([1, 0, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_0211220 : fieldCube 7 5 20 [1, 0, 1, 0, 1, 1, 1] = [2, 0, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_0211220 : fieldMul 7 5 20 [2, 0, 0, 2, 2, 0, 2] [0, 2, 1, 1, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0211220 : mirrorTrits [2, 0, 0, 2, 2, 0, 2] = [1, 0, 0, 1, 1, 0, 1] := by
  decide

theorem demoInv_0211220 : specInv 7 5 20 [0, 2, 1, 1, 2, 2, 0] = some [1, 0, 0, 1, 1, 0, 1] :=
  specInv_mirror_7 [0, 2, 1, 1, 2, 2, 0] [0, 1, 2, 2, 0, 1, 0] [1, 0, 1, 0, 1, 1, 1] [2, 0, 0, 2, 2, 0, 2] [1, 0, 0, 1, 1, 0, 1] demoR1_0211220 demoR2_0211220 demoC_0211220 demoM_0211220 demoMir_0211220

theorem demoR1_1211220 : invRung 7 5 20 [1, 2, 1, 1, 2, 2, 0] [1, 2, 1, 1, 2, 2, 0] 1 2 false = ([2, 0, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1211220 : invRung 7 5 20 [1, 2, 1, 1, 2, 2, 0] [2, 0, 1, 1, 1, 0, 2] 3 1 true = ([2, 2, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_1211220 : fieldCube 7 5 20 [2, 2, 0, 0, 0, 0, 2] = [2, 2, 1, 1, 2, 2, 2] := by
  decide

theorem demoM_1211220 : fieldMul 7 5 20 [2, 2, 1, 1, 2, 2, 2] [1, 2, 1, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1211220 : specInv 7 5 20 [1, 2, 1, 1, 2, 2, 0] = some [2, 2, 1, 1, 2, 2, 2] :=
  specInv_white_7 [1, 2, 1, 1, 2, 2, 0] [2, 0, 1, 1, 1, 0, 2] [2, 2, 0, 0, 0, 0, 2] [2, 2, 1, 1, 2, 2, 2] demoR1_1211220 demoR2_1211220 demoC_1211220 demoM_1211220

theorem demoR1_2211220 : invRung 7 5 20 [2, 2, 1, 1, 2, 2, 0] [2, 2, 1, 1, 2, 2, 0] 1 2 false = ([1, 0, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2211220 : invRung 7 5 20 [2, 2, 1, 1, 2, 2, 0] [1, 0, 0, 0, 1, 1, 2] 3 1 true = ([2, 0, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_2211220 : fieldCube 7 5 20 [2, 0, 2, 0, 2, 0, 2] = [2, 1, 1, 1, 2, 1, 0] := by
  decide

theorem demoM_2211220 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 1, 0] [2, 2, 1, 1, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211220 : mirrorTrits [2, 1, 1, 1, 2, 1, 0] = [1, 2, 2, 2, 1, 2, 0] := by
  decide

theorem demoInv_2211220 : specInv 7 5 20 [2, 2, 1, 1, 2, 2, 0] = some [1, 2, 2, 2, 1, 2, 0] :=
  specInv_mirror_7 [2, 2, 1, 1, 2, 2, 0] [1, 0, 0, 0, 1, 1, 2] [2, 0, 2, 0, 2, 0, 2] [2, 1, 1, 1, 2, 1, 0] [1, 2, 2, 2, 1, 2, 0] demoR1_2211220 demoR2_2211220 demoC_2211220 demoM_2211220 demoMir_2211220

theorem demoR1_0021220 : invRung 7 5 20 [0, 0, 2, 1, 2, 2, 0] [0, 0, 2, 1, 2, 2, 0] 1 2 false = ([2, 1, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_0021220 : invRung 7 5 20 [0, 0, 2, 1, 2, 2, 0] [2, 1, 2, 1, 2, 0, 1] 3 1 true = ([0, 1, 0, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_0021220 : fieldCube 7 5 20 [0, 1, 0, 1, 0, 0, 2] = [1, 2, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_0021220 : fieldMul 7 5 20 [1, 2, 2, 0, 2, 0, 2] [0, 0, 2, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0021220 : specInv 7 5 20 [0, 0, 2, 1, 2, 2, 0] = some [1, 2, 2, 0, 2, 0, 2] :=
  specInv_white_7 [0, 0, 2, 1, 2, 2, 0] [2, 1, 2, 1, 2, 0, 1] [0, 1, 0, 1, 0, 0, 2] [1, 2, 2, 0, 2, 0, 2] demoR1_0021220 demoR2_0021220 demoC_0021220 demoM_0021220

theorem demoR1_1021220 : invRung 7 5 20 [1, 0, 2, 1, 2, 2, 0] [1, 0, 2, 1, 2, 2, 0] 1 2 false = ([0, 1, 2, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_1021220 : invRung 7 5 20 [1, 0, 2, 1, 2, 2, 0] [0, 1, 2, 1, 1, 0, 1] 3 1 true = ([1, 1, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_1021220 : fieldCube 7 5 20 [1, 1, 0, 1, 1, 0, 0] = [2, 1, 1, 2, 0, 2, 1] := by
  decide

theorem demoM_1021220 : fieldMul 7 5 20 [2, 1, 1, 2, 0, 2, 1] [1, 0, 2, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1021220 : specInv 7 5 20 [1, 0, 2, 1, 2, 2, 0] = some [2, 1, 1, 2, 0, 2, 1] :=
  specInv_white_7 [1, 0, 2, 1, 2, 2, 0] [0, 1, 2, 1, 1, 0, 1] [1, 1, 0, 1, 1, 0, 0] [2, 1, 1, 2, 0, 2, 1] demoR1_1021220 demoR2_1021220 demoC_1021220 demoM_1021220

theorem demoR1_2021220 : invRung 7 5 20 [2, 0, 2, 1, 2, 2, 0] [2, 0, 2, 1, 2, 2, 0] 1 2 false = ([0, 0, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_2021220 : invRung 7 5 20 [2, 0, 2, 1, 2, 2, 0] [0, 0, 1, 2, 1, 0, 0] 3 1 true = ([2, 2, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_2021220 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 2, 0] = [0, 1, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_2021220 : fieldMul 7 5 20 [0, 1, 1, 1, 2, 0, 1] [2, 0, 2, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2021220 : specInv 7 5 20 [2, 0, 2, 1, 2, 2, 0] = some [0, 1, 1, 1, 2, 0, 1] :=
  specInv_white_7 [2, 0, 2, 1, 2, 2, 0] [0, 0, 1, 2, 1, 0, 0] [2, 2, 1, 2, 2, 2, 0] [0, 1, 1, 1, 2, 0, 1] demoR1_2021220 demoR2_2021220 demoC_2021220 demoM_2021220

theorem demoR1_0121220 : invRung 7 5 20 [0, 1, 2, 1, 2, 2, 0] [0, 1, 2, 1, 2, 2, 0] 1 2 false = ([1, 1, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_0121220 : invRung 7 5 20 [0, 1, 2, 1, 2, 2, 0] [1, 1, 0, 2, 0, 1, 0] 3 1 true = ([0, 0, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0121220 : fieldCube 7 5 20 [0, 0, 0, 1, 0, 0, 1] = [1, 1, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_0121220 : fieldMul 7 5 20 [1, 1, 0, 1, 1, 2, 1] [0, 1, 2, 1, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0121220 : mirrorTrits [1, 1, 0, 1, 1, 2, 1] = [2, 2, 0, 2, 2, 1, 2] := by
  decide

theorem demoInv_0121220 : specInv 7 5 20 [0, 1, 2, 1, 2, 2, 0] = some [2, 2, 0, 2, 2, 1, 2] :=
  specInv_mirror_7 [0, 1, 2, 1, 2, 2, 0] [1, 1, 0, 2, 0, 1, 0] [0, 0, 0, 1, 0, 0, 1] [1, 1, 0, 1, 1, 2, 1] [2, 2, 0, 2, 2, 1, 2] demoR1_0121220 demoR2_0121220 demoC_0121220 demoM_0121220 demoMir_0121220

theorem demoR1_1121220 : invRung 7 5 20 [1, 1, 2, 1, 2, 2, 0] [1, 1, 2, 1, 2, 2, 0] 1 2 false = ([0, 1, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_1121220 : invRung 7 5 20 [1, 1, 2, 1, 2, 2, 0] [0, 1, 0, 1, 0, 2, 2] 3 1 true = ([0, 2, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_1121220 : fieldCube 7 5 20 [0, 2, 2, 1, 2, 0, 1] = [1, 0, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_1121220 : fieldMul 7 5 20 [1, 0, 0, 2, 1, 1, 2] [1, 1, 2, 1, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121220 : mirrorTrits [1, 0, 0, 2, 1, 1, 2] = [2, 0, 0, 1, 2, 2, 1] := by
  decide

theorem demoInv_1121220 : specInv 7 5 20 [1, 1, 2, 1, 2, 2, 0] = some [2, 0, 0, 1, 2, 2, 1] :=
  specInv_mirror_7 [1, 1, 2, 1, 2, 2, 0] [0, 1, 0, 1, 0, 2, 2] [0, 2, 2, 1, 2, 0, 1] [1, 0, 0, 2, 1, 1, 2] [2, 0, 0, 1, 2, 2, 1] demoR1_1121220 demoR2_1121220 demoC_1121220 demoM_1121220 demoMir_1121220

theorem demoR1_2121220 : invRung 7 5 20 [2, 1, 2, 1, 2, 2, 0] [2, 1, 2, 1, 2, 2, 0] 1 2 false = ([0, 2, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_2121220 : invRung 7 5 20 [2, 1, 2, 1, 2, 2, 0] [0, 2, 1, 0, 1, 2, 0] 3 1 true = ([0, 2, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_2121220 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 0, 0] = [0, 1, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_2121220 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 1, 1] [2, 1, 2, 1, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2121220 : mirrorTrits [0, 1, 0, 0, 0, 1, 1] = [0, 2, 0, 0, 0, 2, 2] := by
  decide

theorem demoInv_2121220 : specInv 7 5 20 [2, 1, 2, 1, 2, 2, 0] = some [0, 2, 0, 0, 0, 2, 2] :=
  specInv_mirror_7 [2, 1, 2, 1, 2, 2, 0] [0, 2, 1, 0, 1, 2, 0] [0, 2, 0, 0, 1, 0, 0] [0, 1, 0, 0, 0, 1, 1] [0, 2, 0, 0, 0, 2, 2] demoR1_2121220 demoR2_2121220 demoC_2121220 demoM_2121220 demoMir_2121220

theorem demoR1_0221220 : invRung 7 5 20 [0, 2, 2, 1, 2, 2, 0] [0, 2, 2, 1, 2, 2, 0] 1 2 false = ([0, 1, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_0221220 : invRung 7 5 20 [0, 2, 2, 1, 2, 2, 0] [0, 1, 2, 0, 1, 0, 2] 3 1 true = ([0, 2, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_0221220 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 1, 1] = [1, 0, 0, 1, 2, 0, 1] := by
  decide

theorem demoM_0221220 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 0, 1] [0, 2, 2, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0221220 : specInv 7 5 20 [0, 2, 2, 1, 2, 2, 0] = some [1, 0, 0, 1, 2, 0, 1] :=
  specInv_white_7 [0, 2, 2, 1, 2, 2, 0] [0, 1, 2, 0, 1, 0, 2] [0, 2, 0, 0, 1, 1, 1] [1, 0, 0, 1, 2, 0, 1] demoR1_0221220 demoR2_0221220 demoC_0221220 demoM_0221220

theorem demoR1_1221220 : invRung 7 5 20 [1, 2, 2, 1, 2, 2, 0] [1, 2, 2, 1, 2, 2, 0] 1 2 false = ([0, 2, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_1221220 : invRung 7 5 20 [1, 2, 2, 1, 2, 2, 0] [0, 2, 2, 2, 1, 1, 1] 3 1 true = ([0, 1, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_1221220 : fieldCube 7 5 20 [0, 1, 0, 1, 1, 1, 0] = [2, 2, 2, 2, 1, 0, 0] := by
  decide

theorem demoM_1221220 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 0, 0] [1, 2, 2, 1, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1221220 : specInv 7 5 20 [1, 2, 2, 1, 2, 2, 0] = some [2, 2, 2, 2, 1, 0, 0] :=
  specInv_white_7 [1, 2, 2, 1, 2, 2, 0] [0, 2, 2, 2, 1, 1, 1] [0, 1, 0, 1, 1, 1, 0] [2, 2, 2, 2, 1, 0, 0] demoR1_1221220 demoR2_1221220 demoC_1221220 demoM_1221220

theorem demoR1_2221220 : invRung 7 5 20 [2, 2, 2, 1, 2, 2, 0] [2, 2, 2, 1, 2, 2, 0] 1 2 false = ([0, 0, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2221220 : invRung 7 5 20 [2, 2, 2, 1, 2, 2, 0] [0, 0, 2, 0, 2, 0, 2] 3 1 true = ([2, 1, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_2221220 : fieldCube 7 5 20 [2, 1, 1, 0, 0, 0, 2] = [2, 2, 1, 0, 2, 2, 0] := by
  decide

theorem demoM_2221220 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 2, 0] [2, 2, 2, 1, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221220 : mirrorTrits [2, 2, 1, 0, 2, 2, 0] = [1, 1, 2, 0, 1, 1, 0] := by
  decide

theorem demoInv_2221220 : specInv 7 5 20 [2, 2, 2, 1, 2, 2, 0] = some [1, 1, 2, 0, 1, 1, 0] :=
  specInv_mirror_7 [2, 2, 2, 1, 2, 2, 0] [0, 0, 2, 0, 2, 0, 2] [2, 1, 1, 0, 0, 0, 2] [2, 2, 1, 0, 2, 2, 0] [1, 1, 2, 0, 1, 1, 0] demoR1_2221220 demoR2_2221220 demoC_2221220 demoM_2221220 demoMir_2221220

theorem demoR1_0002220 : invRung 7 5 20 [0, 0, 0, 2, 2, 2, 0] [0, 0, 0, 2, 2, 2, 0] 1 2 false = ([0, 1, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_0002220 : invRung 7 5 20 [0, 0, 0, 2, 2, 2, 0] [0, 1, 1, 2, 1, 2, 2] 3 1 true = ([0, 0, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_0002220 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 2, 1] = [2, 2, 1, 0, 0, 2, 2] := by
  decide

theorem demoM_0002220 : fieldMul 7 5 20 [2, 2, 1, 0, 0, 2, 2] [0, 0, 0, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002220 : mirrorTrits [2, 2, 1, 0, 0, 2, 2] = [1, 1, 2, 0, 0, 1, 1] := by
  decide

theorem demoInv_0002220 : specInv 7 5 20 [0, 0, 0, 2, 2, 2, 0] = some [1, 1, 2, 0, 0, 1, 1] :=
  specInv_mirror_7 [0, 0, 0, 2, 2, 2, 0] [0, 1, 1, 2, 1, 2, 2] [0, 0, 1, 0, 2, 2, 1] [2, 2, 1, 0, 0, 2, 2] [1, 1, 2, 0, 0, 1, 1] demoR1_0002220 demoR2_0002220 demoC_0002220 demoM_0002220 demoMir_0002220

theorem demoR1_1002220 : invRung 7 5 20 [1, 0, 0, 2, 2, 2, 0] [1, 0, 0, 2, 2, 2, 0] 1 2 false = ([1, 2, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_1002220 : invRung 7 5 20 [1, 0, 0, 2, 2, 2, 0] [1, 2, 1, 2, 1, 0, 1] 3 1 true = ([0, 2, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_1002220 : fieldCube 7 5 20 [0, 2, 0, 2, 1, 1, 2] = [0, 1, 1, 2, 0, 0, 2] := by
  decide

theorem demoM_1002220 : fieldMul 7 5 20 [0, 1, 1, 2, 0, 0, 2] [1, 0, 0, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1002220 : mirrorTrits [0, 1, 1, 2, 0, 0, 2] = [0, 2, 2, 1, 0, 0, 1] := by
  decide

theorem demoInv_1002220 : specInv 7 5 20 [1, 0, 0, 2, 2, 2, 0] = some [0, 2, 2, 1, 0, 0, 1] :=
  specInv_mirror_7 [1, 0, 0, 2, 2, 2, 0] [1, 2, 1, 2, 1, 0, 1] [0, 2, 0, 2, 1, 1, 2] [0, 1, 1, 2, 0, 0, 2] [0, 2, 2, 1, 0, 0, 1] demoR1_1002220 demoR2_1002220 demoC_1002220 demoM_1002220 demoMir_1002220

theorem demoR1_2002220 : invRung 7 5 20 [2, 0, 0, 2, 2, 2, 0] [2, 0, 0, 2, 2, 2, 0] 1 2 false = ([1, 0, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_2002220 : invRung 7 5 20 [2, 0, 0, 2, 2, 2, 0] [1, 0, 1, 1, 0, 1, 0] 3 1 true = ([1, 0, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2002220 : fieldCube 7 5 20 [1, 0, 1, 0, 1, 1, 0] = [2, 2, 1, 1, 1, 2, 1] := by
  decide

theorem demoM_2002220 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 2, 1] [2, 0, 0, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002220 : mirrorTrits [2, 2, 1, 1, 1, 2, 1] = [1, 1, 2, 2, 2, 1, 2] := by
  decide

theorem demoInv_2002220 : specInv 7 5 20 [2, 0, 0, 2, 2, 2, 0] = some [1, 1, 2, 2, 2, 1, 2] :=
  specInv_mirror_7 [2, 0, 0, 2, 2, 2, 0] [1, 0, 1, 1, 0, 1, 0] [1, 0, 1, 0, 1, 1, 0] [2, 2, 1, 1, 1, 2, 1] [1, 1, 2, 2, 2, 1, 2] demoR1_2002220 demoR2_2002220 demoC_2002220 demoM_2002220 demoMir_2002220

theorem demoR1_0102220 : invRung 7 5 20 [0, 1, 0, 2, 2, 2, 0] [0, 1, 0, 2, 2, 2, 0] 1 2 false = ([0, 1, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_0102220 : invRung 7 5 20 [0, 1, 0, 2, 2, 2, 0] [0, 1, 0, 1, 2, 0, 0] 3 1 true = ([1, 0, 0, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0102220 : fieldCube 7 5 20 [1, 0, 0, 0, 1, 2, 2] = [0, 2, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_0102220 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 2, 1] [0, 1, 0, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0102220 : specInv 7 5 20 [0, 1, 0, 2, 2, 2, 0] = some [0, 2, 0, 0, 1, 2, 1] :=
  specInv_white_7 [0, 1, 0, 2, 2, 2, 0] [0, 1, 0, 1, 2, 0, 0] [1, 0, 0, 0, 1, 2, 2] [0, 2, 0, 0, 1, 2, 1] demoR1_0102220 demoR2_0102220 demoC_0102220 demoM_0102220

theorem demoR1_1102220 : invRung 7 5 20 [1, 1, 0, 2, 2, 2, 0] [1, 1, 0, 2, 2, 2, 0] 1 2 false = ([0, 1, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_1102220 : invRung 7 5 20 [1, 1, 0, 2, 2, 2, 0] [0, 1, 1, 2, 0, 2, 0] 3 1 true = ([2, 2, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1102220 : fieldCube 7 5 20 [2, 2, 1, 2, 0, 1, 0] = [2, 1, 0, 2, 1, 0, 0] := by
  decide

theorem demoM_1102220 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 0, 0] [1, 1, 0, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1102220 : specInv 7 5 20 [1, 1, 0, 2, 2, 2, 0] = some [2, 1, 0, 2, 1, 0, 0] :=
  specInv_white_7 [1, 1, 0, 2, 2, 2, 0] [0, 1, 1, 2, 0, 2, 0] [2, 2, 1, 2, 0, 1, 0] [2, 1, 0, 2, 1, 0, 0] demoR1_1102220 demoR2_1102220 demoC_1102220 demoM_1102220

theorem demoR1_2102220 : invRung 7 5 20 [2, 1, 0, 2, 2, 2, 0] [2, 1, 0, 2, 2, 2, 0] 1 2 false = ([1, 0, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_2102220 : invRung 7 5 20 [2, 1, 0, 2, 2, 2, 0] [1, 0, 1, 1, 0, 0, 0] 3 1 true = ([1, 0, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2102220 : fieldCube 7 5 20 [1, 0, 0, 1, 1, 2, 1] = [1, 1, 2, 2, 0, 2, 0] := by
  decide

theorem demoM_2102220 : fieldMul 7 5 20 [1, 1, 2, 2, 0, 2, 0] [2, 1, 0, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2102220 : mirrorTrits [1, 1, 2, 2, 0, 2, 0] = [2, 2, 1, 1, 0, 1, 0] := by
  decide

theorem demoInv_2102220 : specInv 7 5 20 [2, 1, 0, 2, 2, 2, 0] = some [2, 2, 1, 1, 0, 1, 0] :=
  specInv_mirror_7 [2, 1, 0, 2, 2, 2, 0] [1, 0, 1, 1, 0, 0, 0] [1, 0, 0, 1, 1, 2, 1] [1, 1, 2, 2, 0, 2, 0] [2, 2, 1, 1, 0, 1, 0] demoR1_2102220 demoR2_2102220 demoC_2102220 demoM_2102220 demoMir_2102220

theorem demoR1_0202220 : invRung 7 5 20 [0, 2, 0, 2, 2, 2, 0] [0, 2, 0, 2, 2, 2, 0] 1 2 false = ([1, 1, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0202220 : invRung 7 5 20 [0, 2, 0, 2, 2, 2, 0] [1, 1, 1, 1, 2, 1, 2] 3 1 true = ([2, 1, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_0202220 : fieldCube 7 5 20 [2, 1, 0, 1, 1, 2, 1] = [2, 1, 2, 0, 0, 2, 0] := by
  decide

theorem demoM_0202220 : fieldMul 7 5 20 [2, 1, 2, 0, 0, 2, 0] [0, 2, 0, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202220 : mirrorTrits [2, 1, 2, 0, 0, 2, 0] = [1, 2, 1, 0, 0, 1, 0] := by
  decide

theorem demoInv_0202220 : specInv 7 5 20 [0, 2, 0, 2, 2, 2, 0] = some [1, 2, 1, 0, 0, 1, 0] :=
  specInv_mirror_7 [0, 2, 0, 2, 2, 2, 0] [1, 1, 1, 1, 2, 1, 2] [2, 1, 0, 1, 1, 2, 1] [2, 1, 2, 0, 0, 2, 0] [1, 2, 1, 0, 0, 1, 0] demoR1_0202220 demoR2_0202220 demoC_0202220 demoM_0202220 demoMir_0202220

theorem demoR1_1202220 : invRung 7 5 20 [1, 2, 0, 2, 2, 2, 0] [1, 2, 0, 2, 2, 2, 0] 1 2 false = ([0, 1, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1202220 : invRung 7 5 20 [1, 2, 0, 2, 2, 2, 0] [0, 1, 0, 1, 0, 0, 1] 3 1 true = ([1, 2, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_1202220 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 1, 0] = [1, 2, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_1202220 : fieldMul 7 5 20 [1, 2, 0, 0, 1, 1, 1] [1, 2, 0, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1202220 : specInv 7 5 20 [1, 2, 0, 2, 2, 2, 0] = some [1, 2, 0, 0, 1, 1, 1] :=
  specInv_white_7 [1, 2, 0, 2, 2, 2, 0] [0, 1, 0, 1, 0, 0, 1] [1, 2, 1, 2, 1, 1, 0] [1, 2, 0, 0, 1, 1, 1] demoR1_1202220 demoR2_1202220 demoC_1202220 demoM_1202220

theorem demoR1_2202220 : invRung 7 5 20 [2, 2, 0, 2, 2, 2, 0] [2, 2, 0, 2, 2, 2, 0] 1 2 false = ([2, 2, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_2202220 : invRung 7 5 20 [2, 2, 0, 2, 2, 2, 0] [2, 2, 0, 1, 0, 0, 0] 3 1 true = ([0, 0, 0, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_2202220 : fieldCube 7 5 20 [0, 0, 0, 1, 2, 2, 1] = [0, 2, 2, 0, 0, 0, 1] := by
  decide

theorem demoM_2202220 : fieldMul 7 5 20 [0, 2, 2, 0, 0, 0, 1] [2, 2, 0, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2202220 : specInv 7 5 20 [2, 2, 0, 2, 2, 2, 0] = some [0, 2, 2, 0, 0, 0, 1] :=
  specInv_white_7 [2, 2, 0, 2, 2, 2, 0] [2, 2, 0, 1, 0, 0, 0] [0, 0, 0, 1, 2, 2, 1] [0, 2, 2, 0, 0, 0, 1] demoR1_2202220 demoR2_2202220 demoC_2202220 demoM_2202220

theorem demoR1_0012220 : invRung 7 5 20 [0, 0, 1, 2, 2, 2, 0] [0, 0, 1, 2, 2, 2, 0] 1 2 false = ([0, 0, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_0012220 : invRung 7 5 20 [0, 0, 1, 2, 2, 2, 0] [0, 0, 2, 1, 1, 1, 1] 3 1 true = ([0, 1, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_0012220 : fieldCube 7 5 20 [0, 1, 2, 2, 2, 2, 1] = [1, 2, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_0012220 : fieldMul 7 5 20 [1, 2, 0, 1, 0, 1, 0] [0, 0, 1, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0012220 : mirrorTrits [1, 2, 0, 1, 0, 1, 0] = [2, 1, 0, 2, 0, 2, 0] := by
  decide

theorem demoInv_0012220 : specInv 7 5 20 [0, 0, 1, 2, 2, 2, 0] = some [2, 1, 0, 2, 0, 2, 0] :=
  specInv_mirror_7 [0, 0, 1, 2, 2, 2, 0] [0, 0, 2, 1, 1, 1, 1] [0, 1, 2, 2, 2, 2, 1] [1, 2, 0, 1, 0, 1, 0] [2, 1, 0, 2, 0, 2, 0] demoR1_0012220 demoR2_0012220 demoC_0012220 demoM_0012220 demoMir_0012220

theorem demoR1_1012220 : invRung 7 5 20 [1, 0, 1, 2, 2, 2, 0] [1, 0, 1, 2, 2, 2, 0] 1 2 false = ([0, 0, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1012220 : invRung 7 5 20 [1, 0, 1, 2, 2, 2, 0] [0, 0, 1, 2, 0, 0, 1] 3 1 true = ([2, 0, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_1012220 : fieldCube 7 5 20 [2, 0, 0, 2, 2, 2, 1] = [0, 2, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_1012220 : fieldMul 7 5 20 [0, 2, 0, 0, 0, 1, 1] [1, 0, 1, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1012220 : specInv 7 5 20 [1, 0, 1, 2, 2, 2, 0] = some [0, 2, 0, 0, 0, 1, 1] :=
  specInv_white_7 [1, 0, 1, 2, 2, 2, 0] [0, 0, 1, 2, 0, 0, 1] [2, 0, 0, 2, 2, 2, 1] [0, 2, 0, 0, 0, 1, 1] demoR1_1012220 demoR2_1012220 demoC_1012220 demoM_1012220

theorem demoR1_2012220 : invRung 7 5 20 [2, 0, 1, 2, 2, 2, 0] [2, 0, 1, 2, 2, 2, 0] 1 2 false = ([2, 2, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_2012220 : invRung 7 5 20 [2, 0, 1, 2, 2, 2, 0] [2, 2, 0, 1, 0, 1, 2] 3 1 true = ([0, 0, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_2012220 : fieldCube 7 5 20 [0, 0, 2, 2, 1, 0, 2] = [2, 0, 0, 0, 2, 2, 2] := by
  decide

theorem demoM_2012220 : fieldMul 7 5 20 [2, 0, 0, 0, 2, 2, 2] [2, 0, 1, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012220 : mirrorTrits [2, 0, 0, 0, 2, 2, 2] = [1, 0, 0, 0, 1, 1, 1] := by
  decide

theorem demoInv_2012220 : specInv 7 5 20 [2, 0, 1, 2, 2, 2, 0] = some [1, 0, 0, 0, 1, 1, 1] :=
  specInv_mirror_7 [2, 0, 1, 2, 2, 2, 0] [2, 2, 0, 1, 0, 1, 2] [0, 0, 2, 2, 1, 0, 2] [2, 0, 0, 0, 2, 2, 2] [1, 0, 0, 0, 1, 1, 1] demoR1_2012220 demoR2_2012220 demoC_2012220 demoM_2012220 demoMir_2012220

theorem demoR1_0112220 : invRung 7 5 20 [0, 1, 1, 2, 2, 2, 0] [0, 1, 1, 2, 2, 2, 0] 1 2 false = ([0, 2, 0, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_0112220 : invRung 7 5 20 [0, 1, 1, 2, 2, 2, 0] [0, 2, 0, 1, 1, 0, 1] 3 1 true = ([0, 2, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_0112220 : fieldCube 7 5 20 [0, 2, 0, 0, 2, 2, 0] = [2, 1, 2, 1, 2, 1, 0] := by
  decide

theorem demoM_0112220 : fieldMul 7 5 20 [2, 1, 2, 1, 2, 1, 0] [0, 1, 1, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112220 : mirrorTrits [2, 1, 2, 1, 2, 1, 0] = [1, 2, 1, 2, 1, 2, 0] := by
  decide

theorem demoInv_0112220 : specInv 7 5 20 [0, 1, 1, 2, 2, 2, 0] = some [1, 2, 1, 2, 1, 2, 0] :=
  specInv_mirror_7 [0, 1, 1, 2, 2, 2, 0] [0, 2, 0, 1, 1, 0, 1] [0, 2, 0, 0, 2, 2, 0] [2, 1, 2, 1, 2, 1, 0] [1, 2, 1, 2, 1, 2, 0] demoR1_0112220 demoR2_0112220 demoC_0112220 demoM_0112220 demoMir_0112220

theorem demoR1_1112220 : invRung 7 5 20 [1, 1, 1, 2, 2, 2, 0] [1, 1, 1, 2, 2, 2, 0] 1 2 false = ([2, 0, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1112220 : invRung 7 5 20 [1, 1, 1, 2, 2, 2, 0] [2, 0, 1, 2, 2, 1, 1] 3 1 true = ([0, 0, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_1112220 : fieldCube 7 5 20 [0, 0, 0, 2, 2, 0, 1] = [2, 0, 1, 0, 1, 2, 0] := by
  decide

theorem demoM_1112220 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 2, 0] [1, 1, 1, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112220 : mirrorTrits [2, 0, 1, 0, 1, 2, 0] = [1, 0, 2, 0, 2, 1, 0] := by
  decide

theorem demoInv_1112220 : specInv 7 5 20 [1, 1, 1, 2, 2, 2, 0] = some [1, 0, 2, 0, 2, 1, 0] :=
  specInv_mirror_7 [1, 1, 1, 2, 2, 2, 0] [2, 0, 1, 2, 2, 1, 1] [0, 0, 0, 2, 2, 0, 1] [2, 0, 1, 0, 1, 2, 0] [1, 0, 2, 0, 2, 1, 0] demoR1_1112220 demoR2_1112220 demoC_1112220 demoM_1112220 demoMir_1112220

theorem demoR1_2112220 : invRung 7 5 20 [2, 1, 1, 2, 2, 2, 0] [2, 1, 1, 2, 2, 2, 0] 1 2 false = ([2, 2, 1, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_2112220 : invRung 7 5 20 [2, 1, 1, 2, 2, 2, 0] [2, 2, 1, 0, 1, 0, 2] 3 1 true = ([2, 2, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_2112220 : fieldCube 7 5 20 [2, 2, 2, 1, 1, 0, 2] = [0, 0, 2, 2, 2, 1, 2] := by
  decide

theorem demoM_2112220 : fieldMul 7 5 20 [0, 0, 2, 2, 2, 1, 2] [2, 1, 1, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112220 : mirrorTrits [0, 0, 2, 2, 2, 1, 2] = [0, 0, 1, 1, 1, 2, 1] := by
  decide

theorem demoInv_2112220 : specInv 7 5 20 [2, 1, 1, 2, 2, 2, 0] = some [0, 0, 1, 1, 1, 2, 1] :=
  specInv_mirror_7 [2, 1, 1, 2, 2, 2, 0] [2, 2, 1, 0, 1, 0, 2] [2, 2, 2, 1, 1, 0, 2] [0, 0, 2, 2, 2, 1, 2] [0, 0, 1, 1, 1, 2, 1] demoR1_2112220 demoR2_2112220 demoC_2112220 demoM_2112220 demoMir_2112220

theorem demoR1_0212220 : invRung 7 5 20 [0, 2, 1, 2, 2, 2, 0] [0, 2, 1, 2, 2, 2, 0] 1 2 false = ([2, 0, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_0212220 : invRung 7 5 20 [0, 2, 1, 2, 2, 2, 0] [2, 0, 1, 2, 0, 0, 2] 3 1 true = ([2, 1, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0212220 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 1, 2] = [1, 2, 0, 2, 0, 0, 1] := by
  decide

theorem demoM_0212220 : fieldMul 7 5 20 [1, 2, 0, 2, 0, 0, 1] [0, 2, 1, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0212220 : specInv 7 5 20 [0, 2, 1, 2, 2, 2, 0] = some [1, 2, 0, 2, 0, 0, 1] :=
  specInv_white_7 [0, 2, 1, 2, 2, 2, 0] [2, 0, 1, 2, 0, 0, 2] [2, 1, 1, 1, 2, 1, 2] [1, 2, 0, 2, 0, 0, 1] demoR1_0212220 demoR2_0212220 demoC_0212220 demoM_0212220

theorem demoR1_1212220 : invRung 7 5 20 [1, 2, 1, 2, 2, 2, 0] [1, 2, 1, 2, 2, 2, 0] 1 2 false = ([0, 0, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_1212220 : invRung 7 5 20 [1, 2, 1, 2, 2, 2, 0] [0, 0, 1, 1, 2, 2, 0] 3 1 true = ([2, 1, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1212220 : fieldCube 7 5 20 [2, 1, 1, 2, 0, 1, 0] = [2, 1, 0, 1, 1, 0, 0] := by
  decide

theorem demoM_1212220 : fieldMul 7 5 20 [2, 1, 0, 1, 1, 0, 0] [1, 2, 1, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212220 : mirrorTrits [2, 1, 0, 1, 1, 0, 0] = [1, 2, 0, 2, 2, 0, 0] := by
  decide

theorem demoInv_1212220 : specInv 7 5 20 [1, 2, 1, 2, 2, 2, 0] = some [1, 2, 0, 2, 2, 0, 0] :=
  specInv_mirror_7 [1, 2, 1, 2, 2, 2, 0] [0, 0, 1, 1, 2, 2, 0] [2, 1, 1, 2, 0, 1, 0] [2, 1, 0, 1, 1, 0, 0] [1, 2, 0, 2, 2, 0, 0] demoR1_1212220 demoR2_1212220 demoC_1212220 demoM_1212220 demoMir_1212220

theorem demoR1_2212220 : invRung 7 5 20 [2, 2, 1, 2, 2, 2, 0] [2, 2, 1, 2, 2, 2, 0] 1 2 false = ([1, 0, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2212220 : invRung 7 5 20 [2, 2, 1, 2, 2, 2, 0] [1, 0, 2, 2, 2, 1, 2] 3 1 true = ([1, 2, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2212220 : fieldCube 7 5 20 [1, 2, 0, 2, 1, 2, 2] = [2, 2, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_2212220 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 1, 1] [2, 2, 1, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2212220 : specInv 7 5 20 [2, 2, 1, 2, 2, 2, 0] = some [2, 2, 2, 2, 1, 1, 1] :=
  specInv_white_7 [2, 2, 1, 2, 2, 2, 0] [1, 0, 2, 2, 2, 1, 2] [1, 2, 0, 2, 1, 2, 2] [2, 2, 2, 2, 1, 1, 1] demoR1_2212220 demoR2_2212220 demoC_2212220 demoM_2212220

theorem demoR1_0022220 : invRung 7 5 20 [0, 0, 2, 2, 2, 2, 0] [0, 0, 2, 2, 2, 2, 0] 1 2 false = ([2, 2, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_0022220 : invRung 7 5 20 [0, 0, 2, 2, 2, 2, 0] [2, 2, 0, 1, 1, 2, 1] 3 1 true = ([1, 2, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0022220 : fieldCube 7 5 20 [1, 2, 1, 2, 2, 0, 2] = [0, 1, 0, 0, 2, 0, 2] := by
  decide

theorem demoM_0022220 : fieldMul 7 5 20 [0, 1, 0, 0, 2, 0, 2] [0, 0, 2, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0022220 : specInv 7 5 20 [0, 0, 2, 2, 2, 2, 0] = some [0, 1, 0, 0, 2, 0, 2] :=
  specInv_white_7 [0, 0, 2, 2, 2, 2, 0] [2, 2, 0, 1, 1, 2, 1] [1, 2, 1, 2, 2, 0, 2] [0, 1, 0, 0, 2, 0, 2] demoR1_0022220 demoR2_0022220 demoC_0022220 demoM_0022220

theorem demoR1_1022220 : invRung 7 5 20 [1, 0, 2, 2, 2, 2, 0] [1, 0, 2, 2, 2, 2, 0] 1 2 false = ([0, 1, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1022220 : invRung 7 5 20 [1, 0, 2, 2, 2, 2, 0] [0, 1, 2, 0, 2, 2, 1] 3 1 true = ([2, 0, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_1022220 : fieldCube 7 5 20 [2, 0, 0, 1, 1, 0, 0] = [0, 1, 1, 1, 0, 2, 1] := by
  decide

theorem demoM_1022220 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 2, 1] [1, 0, 2, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1022220 : specInv 7 5 20 [1, 0, 2, 2, 2, 2, 0] = some [0, 1, 1, 1, 0, 2, 1] :=
  specInv_white_7 [1, 0, 2, 2, 2, 2, 0] [0, 1, 2, 0, 2, 2, 1] [2, 0, 0, 1, 1, 0, 0] [0, 1, 1, 1, 0, 2, 1] demoR1_1022220 demoR2_1022220 demoC_1022220 demoM_1022220

theorem demoR1_2022220 : invRung 7 5 20 [2, 0, 2, 2, 2, 2, 0] [2, 0, 2, 2, 2, 2, 0] 1 2 false = ([0, 1, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_2022220 : invRung 7 5 20 [2, 0, 2, 2, 2, 2, 0] [0, 1, 1, 2, 0, 0, 0] 3 1 true = ([1, 0, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_2022220 : fieldCube 7 5 20 [1, 0, 1, 2, 0, 0, 0] = [0, 0, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_2022220 : fieldMul 7 5 20 [0, 0, 2, 0, 0, 2, 1] [2, 0, 2, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_2022220 : specInv 7 5 20 [2, 0, 2, 2, 2, 2, 0] = some [0, 0, 2, 0, 0, 2, 1] :=
  specInv_white_7 [2, 0, 2, 2, 2, 2, 0] [0, 1, 1, 2, 0, 0, 0] [1, 0, 1, 2, 0, 0, 0] [0, 0, 2, 0, 0, 2, 1] demoR1_2022220 demoR2_2022220 demoC_2022220 demoM_2022220

theorem demoR1_0122220 : invRung 7 5 20 [0, 1, 2, 2, 2, 2, 0] [0, 1, 2, 2, 2, 2, 0] 1 2 false = ([2, 2, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0122220 : invRung 7 5 20 [0, 1, 2, 2, 2, 2, 0] [2, 2, 2, 1, 2, 1, 2] 3 1 true = ([2, 1, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0122220 : fieldCube 7 5 20 [2, 1, 0, 0, 2, 0, 1] = [2, 0, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_0122220 : fieldMul 7 5 20 [2, 0, 2, 1, 1, 0, 0] [0, 1, 2, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_0122220 : specInv 7 5 20 [0, 1, 2, 2, 2, 2, 0] = some [2, 0, 2, 1, 1, 0, 0] :=
  specInv_white_7 [0, 1, 2, 2, 2, 2, 0] [2, 2, 2, 1, 2, 1, 2] [2, 1, 0, 0, 2, 0, 1] [2, 0, 2, 1, 1, 0, 0] demoR1_0122220 demoR2_0122220 demoC_0122220 demoM_0122220

theorem demoR1_1122220 : invRung 7 5 20 [1, 1, 2, 2, 2, 2, 0] [1, 1, 2, 2, 2, 2, 0] 1 2 false = ([2, 1, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_1122220 : invRung 7 5 20 [1, 1, 2, 2, 2, 2, 0] [2, 1, 1, 2, 0, 1, 1] 3 1 true = ([1, 2, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_1122220 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 1, 2] = [0, 2, 0, 0, 0, 0, 1] := by
  decide

theorem demoM_1122220 : fieldMul 7 5 20 [0, 2, 0, 0, 0, 0, 1] [1, 1, 2, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122220 : mirrorTrits [0, 2, 0, 0, 0, 0, 1] = [0, 1, 0, 0, 0, 0, 2] := by
  decide

theorem demoInv_1122220 : specInv 7 5 20 [1, 1, 2, 2, 2, 2, 0] = some [0, 1, 0, 0, 0, 0, 2] :=
  specInv_mirror_7 [1, 1, 2, 2, 2, 2, 0] [2, 1, 1, 2, 0, 1, 1] [1, 2, 1, 1, 2, 1, 2] [0, 2, 0, 0, 0, 0, 1] [0, 1, 0, 0, 0, 0, 2] demoR1_1122220 demoR2_1122220 demoC_1122220 demoM_1122220 demoMir_1122220

theorem demoR1_2122220 : invRung 7 5 20 [2, 1, 2, 2, 2, 2, 0] [2, 1, 2, 2, 2, 2, 0] 1 2 false = ([0, 0, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2122220 : invRung 7 5 20 [2, 1, 2, 2, 2, 2, 0] [0, 0, 2, 2, 1, 1, 2] 3 1 true = ([0, 2, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_2122220 : fieldCube 7 5 20 [0, 2, 2, 2, 2, 1, 0] = [0, 0, 0, 1, 1, 2, 0] := by
  decide

theorem demoM_2122220 : fieldMul 7 5 20 [0, 0, 0, 1, 1, 2, 0] [2, 1, 2, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122220 : mirrorTrits [0, 0, 0, 1, 1, 2, 0] = [0, 0, 0, 2, 2, 1, 0] := by
  decide

theorem demoInv_2122220 : specInv 7 5 20 [2, 1, 2, 2, 2, 2, 0] = some [0, 0, 0, 2, 2, 1, 0] :=
  specInv_mirror_7 [2, 1, 2, 2, 2, 2, 0] [0, 0, 2, 2, 1, 1, 2] [0, 2, 2, 2, 2, 1, 0] [0, 0, 0, 1, 1, 2, 0] [0, 0, 0, 2, 2, 1, 0] demoR1_2122220 demoR2_2122220 demoC_2122220 demoM_2122220 demoMir_2122220

theorem demoR1_0222220 : invRung 7 5 20 [0, 2, 2, 2, 2, 2, 0] [0, 2, 2, 2, 2, 2, 0] 1 2 false = ([2, 0, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0222220 : invRung 7 5 20 [0, 2, 2, 2, 2, 2, 0] [2, 0, 2, 2, 2, 2, 1] 3 1 true = ([2, 2, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0222220 : fieldCube 7 5 20 [2, 2, 2, 0, 0, 2, 1] = [1, 0, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_0222220 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 0, 1] [0, 2, 2, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222220 : mirrorTrits [1, 0, 1, 0, 0, 0, 1] = [2, 0, 2, 0, 0, 0, 2] := by
  decide

theorem demoInv_0222220 : specInv 7 5 20 [0, 2, 2, 2, 2, 2, 0] = some [2, 0, 2, 0, 0, 0, 2] :=
  specInv_mirror_7 [0, 2, 2, 2, 2, 2, 0] [2, 0, 2, 2, 2, 2, 1] [2, 2, 2, 0, 0, 2, 1] [1, 0, 1, 0, 0, 0, 1] [2, 0, 2, 0, 0, 0, 2] demoR1_0222220 demoR2_0222220 demoC_0222220 demoM_0222220 demoMir_0222220

theorem demoR1_1222220 : invRung 7 5 20 [1, 2, 2, 2, 2, 2, 0] [1, 2, 2, 2, 2, 2, 0] 1 2 false = ([1, 0, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_1222220 : invRung 7 5 20 [1, 2, 2, 2, 2, 2, 0] [1, 0, 1, 0, 2, 1, 0] 3 1 true = ([2, 1, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_1222220 : fieldCube 7 5 20 [2, 1, 0, 0, 2, 2, 1] = [1, 2, 1, 1, 0, 2, 1] := by
  decide

theorem demoM_1222220 : fieldMul 7 5 20 [1, 2, 1, 1, 0, 2, 1] [1, 2, 2, 2, 2, 2, 0] = whiteHole0 7 := by
  decide

theorem demoInv_1222220 : specInv 7 5 20 [1, 2, 2, 2, 2, 2, 0] = some [1, 2, 1, 1, 0, 2, 1] :=
  specInv_white_7 [1, 2, 2, 2, 2, 2, 0] [1, 0, 1, 0, 2, 1, 0] [2, 1, 0, 0, 2, 2, 1] [1, 2, 1, 1, 0, 2, 1] demoR1_1222220 demoR2_1222220 demoC_1222220 demoM_1222220

theorem demoR1_2222220 : invRung 7 5 20 [2, 2, 2, 2, 2, 2, 0] [2, 2, 2, 2, 2, 2, 0] 1 2 false = ([0, 2, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_2222220 : invRung 7 5 20 [2, 2, 2, 2, 2, 2, 0] [0, 2, 1, 2, 2, 2, 1] 3 1 true = ([2, 1, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_2222220 : fieldCube 7 5 20 [2, 1, 2, 2, 1, 0, 2] = [1, 0, 0, 1, 2, 2, 2] := by
  decide

theorem demoM_2222220 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 2, 2] [2, 2, 2, 2, 2, 2, 0] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222220 : mirrorTrits [1, 0, 0, 1, 2, 2, 2] = [2, 0, 0, 2, 1, 1, 1] := by
  decide

theorem demoInv_2222220 : specInv 7 5 20 [2, 2, 2, 2, 2, 2, 0] = some [2, 0, 0, 2, 1, 1, 1] :=
  specInv_mirror_7 [2, 2, 2, 2, 2, 2, 0] [0, 2, 1, 2, 2, 2, 1] [2, 1, 2, 2, 1, 0, 2] [1, 0, 0, 1, 2, 2, 2] [2, 0, 0, 2, 1, 1, 1] demoR1_2222220 demoR2_2222220 demoC_2222220 demoM_2222220 demoMir_2222220

theorem demoR1_0000001 : invRung 7 5 20 [0, 0, 0, 0, 0, 0, 1] [0, 0, 0, 0, 0, 0, 1] 1 2 false = ([2, 1, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0000001 : invRung 7 5 20 [0, 0, 0, 0, 0, 0, 1] [2, 1, 2, 2, 2, 2, 1] 3 1 true = ([0, 0, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_0000001 : fieldCube 7 5 20 [0, 0, 0, 2, 0, 1, 0] = [0, 1, 0, 0, 1, 0, 2] := by
  decide

theorem demoM_0000001 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 0, 2] [0, 0, 0, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0000001 : specInv 7 5 20 [0, 0, 0, 0, 0, 0, 1] = some [0, 1, 0, 0, 1, 0, 2] :=
  specInv_white_7 [0, 0, 0, 0, 0, 0, 1] [2, 1, 2, 2, 2, 2, 1] [0, 0, 0, 2, 0, 1, 0] [0, 1, 0, 0, 1, 0, 2] demoR1_0000001 demoR2_0000001 demoC_0000001 demoM_0000001

theorem demoR1_1000001 : invRung 7 5 20 [1, 0, 0, 0, 0, 0, 1] [1, 0, 0, 0, 0, 0, 1] 1 2 false = ([0, 0, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_1000001 : invRung 7 5 20 [1, 0, 0, 0, 0, 0, 1] [0, 0, 1, 1, 0, 2, 0] 3 1 true = ([1, 2, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_1000001 : fieldCube 7 5 20 [1, 2, 2, 1, 1, 1, 1] = [0, 0, 1, 1, 2, 1, 0] := by
  decide

theorem demoM_1000001 : fieldMul 7 5 20 [0, 0, 1, 1, 2, 1, 0] [1, 0, 0, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000001 : mirrorTrits [0, 0, 1, 1, 2, 1, 0] = [0, 0, 2, 2, 1, 2, 0] := by
  decide

theorem demoInv_1000001 : specInv 7 5 20 [1, 0, 0, 0, 0, 0, 1] = some [0, 0, 2, 2, 1, 2, 0] :=
  specInv_mirror_7 [1, 0, 0, 0, 0, 0, 1] [0, 0, 1, 1, 0, 2, 0] [1, 2, 2, 1, 1, 1, 1] [0, 0, 1, 1, 2, 1, 0] [0, 0, 2, 2, 1, 2, 0] demoR1_1000001 demoR2_1000001 demoC_1000001 demoM_1000001 demoMir_1000001

theorem demoR1_2000001 : invRung 7 5 20 [2, 0, 0, 0, 0, 0, 1] [2, 0, 0, 0, 0, 0, 1] 1 2 false = ([2, 1, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_2000001 : invRung 7 5 20 [2, 0, 0, 0, 0, 0, 1] [2, 1, 0, 2, 1, 0, 0] 3 1 true = ([0, 0, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2000001 : fieldCube 7 5 20 [0, 0, 0, 0, 0, 1, 0] = [1, 1, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_2000001 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 1, 2] [2, 0, 0, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2000001 : specInv 7 5 20 [2, 0, 0, 0, 0, 0, 1] = some [1, 1, 1, 0, 1, 1, 2] :=
  specInv_white_7 [2, 0, 0, 0, 0, 0, 1] [2, 1, 0, 2, 1, 0, 0] [0, 0, 0, 0, 0, 1, 0] [1, 1, 1, 0, 1, 1, 2] demoR1_2000001 demoR2_2000001 demoC_2000001 demoM_2000001

theorem demoR1_0100001 : invRung 7 5 20 [0, 1, 0, 0, 0, 0, 1] [0, 1, 0, 0, 0, 0, 1] 1 2 false = ([0, 0, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0100001 : invRung 7 5 20 [0, 1, 0, 0, 0, 0, 1] [0, 0, 1, 2, 1, 2, 1] 3 1 true = ([2, 1, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0100001 : fieldCube 7 5 20 [2, 1, 0, 0, 2, 1, 0] = [0, 0, 1, 0, 1, 0, 1] := by
  decide

theorem demoM_0100001 : fieldMul 7 5 20 [0, 0, 1, 0, 1, 0, 1] [0, 1, 0, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0100001 : specInv 7 5 20 [0, 1, 0, 0, 0, 0, 1] = some [0, 0, 1, 0, 1, 0, 1] :=
  specInv_white_7 [0, 1, 0, 0, 0, 0, 1] [0, 0, 1, 2, 1, 2, 1] [2, 1, 0, 0, 2, 1, 0] [0, 0, 1, 0, 1, 0, 1] demoR1_0100001 demoR2_0100001 demoC_0100001 demoM_0100001

theorem demoR1_1100001 : invRung 7 5 20 [1, 1, 0, 0, 0, 0, 1] [1, 1, 0, 0, 0, 0, 1] 1 2 false = ([0, 1, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_1100001 : invRung 7 5 20 [1, 1, 0, 0, 0, 0, 1] [0, 1, 2, 0, 0, 2, 1] 3 1 true = ([0, 1, 0, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_1100001 : fieldCube 7 5 20 [0, 1, 0, 1, 2, 0, 0] = [1, 2, 1, 0, 0, 0, 2] := by
  decide

theorem demoM_1100001 : fieldMul 7 5 20 [1, 2, 1, 0, 0, 0, 2] [1, 1, 0, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1100001 : mirrorTrits [1, 2, 1, 0, 0, 0, 2] = [2, 1, 2, 0, 0, 0, 1] := by
  decide

theorem demoInv_1100001 : specInv 7 5 20 [1, 1, 0, 0, 0, 0, 1] = some [2, 1, 2, 0, 0, 0, 1] :=
  specInv_mirror_7 [1, 1, 0, 0, 0, 0, 1] [0, 1, 2, 0, 0, 2, 1] [0, 1, 0, 1, 2, 0, 0] [1, 2, 1, 0, 0, 0, 2] [2, 1, 2, 0, 0, 0, 1] demoR1_1100001 demoR2_1100001 demoC_1100001 demoM_1100001 demoMir_1100001

theorem demoR1_2100001 : invRung 7 5 20 [2, 1, 0, 0, 0, 0, 1] [2, 1, 0, 0, 0, 0, 1] 1 2 false = ([0, 0, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_2100001 : invRung 7 5 20 [2, 1, 0, 0, 0, 0, 1] [0, 0, 2, 2, 2, 2, 2] 3 1 true = ([0, 2, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_2100001 : fieldCube 7 5 20 [0, 2, 2, 1, 2, 2, 2] = [0, 0, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_2100001 : fieldMul 7 5 20 [0, 0, 1, 0, 1, 1, 1] [2, 1, 0, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100001 : mirrorTrits [0, 0, 1, 0, 1, 1, 1] = [0, 0, 2, 0, 2, 2, 2] := by
  decide

theorem demoInv_2100001 : specInv 7 5 20 [2, 1, 0, 0, 0, 0, 1] = some [0, 0, 2, 0, 2, 2, 2] :=
  specInv_mirror_7 [2, 1, 0, 0, 0, 0, 1] [0, 0, 2, 2, 2, 2, 2] [0, 2, 2, 1, 2, 2, 2] [0, 0, 1, 0, 1, 1, 1] [0, 0, 2, 0, 2, 2, 2] demoR1_2100001 demoR2_2100001 demoC_2100001 demoM_2100001 demoMir_2100001

theorem demoR1_0200001 : invRung 7 5 20 [0, 2, 0, 0, 0, 0, 1] [0, 2, 0, 0, 0, 0, 1] 1 2 false = ([0, 0, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_0200001 : invRung 7 5 20 [0, 2, 0, 0, 0, 0, 1] [0, 0, 2, 0, 0, 2, 2] 3 1 true = ([0, 2, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0200001 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 0, 1] = [2, 2, 1, 1, 1, 1, 0] := by
  decide

theorem demoM_0200001 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 1, 0] [0, 2, 0, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0200001 : specInv 7 5 20 [0, 2, 0, 0, 0, 0, 1] = some [2, 2, 1, 1, 1, 1, 0] :=
  specInv_white_7 [0, 2, 0, 0, 0, 0, 1] [0, 0, 2, 0, 0, 2, 2] [0, 2, 1, 2, 1, 0, 1] [2, 2, 1, 1, 1, 1, 0] demoR1_0200001 demoR2_0200001 demoC_0200001 demoM_0200001

theorem demoR1_1200001 : invRung 7 5 20 [1, 2, 0, 0, 0, 0, 1] [1, 2, 0, 0, 0, 0, 1] 1 2 false = ([2, 1, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_1200001 : invRung 7 5 20 [1, 2, 0, 0, 0, 0, 1] [2, 1, 2, 1, 2, 1, 1] 3 1 true = ([0, 2, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_1200001 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 0, 2] = [0, 0, 1, 2, 2, 0, 0] := by
  decide

theorem demoM_1200001 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 0, 0] [1, 2, 0, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200001 : mirrorTrits [0, 0, 1, 2, 2, 0, 0] = [0, 0, 2, 1, 1, 0, 0] := by
  decide

theorem demoInv_1200001 : specInv 7 5 20 [1, 2, 0, 0, 0, 0, 1] = some [0, 0, 2, 1, 1, 0, 0] :=
  specInv_mirror_7 [1, 2, 0, 0, 0, 0, 1] [2, 1, 2, 1, 2, 1, 1] [0, 2, 0, 0, 1, 0, 2] [0, 0, 1, 2, 2, 0, 0] [0, 0, 2, 1, 1, 0, 0] demoR1_1200001 demoR2_1200001 demoC_1200001 demoM_1200001 demoMir_1200001

theorem demoR1_2200001 : invRung 7 5 20 [2, 2, 0, 0, 0, 0, 1] [2, 2, 0, 0, 0, 0, 1] 1 2 false = ([0, 2, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_2200001 : invRung 7 5 20 [2, 2, 0, 0, 0, 0, 1] [0, 2, 0, 2, 1, 2, 1] 3 1 true = ([1, 2, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoC_2200001 : fieldCube 7 5 20 [1, 2, 2, 2, 2, 1, 0] = [1, 0, 0, 1, 1, 2, 0] := by
  decide

theorem demoM_2200001 : fieldMul 7 5 20 [1, 0, 0, 1, 1, 2, 0] [2, 2, 0, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200001 : mirrorTrits [1, 0, 0, 1, 1, 2, 0] = [2, 0, 0, 2, 2, 1, 0] := by
  decide

theorem demoInv_2200001 : specInv 7 5 20 [2, 2, 0, 0, 0, 0, 1] = some [2, 0, 0, 2, 2, 1, 0] :=
  specInv_mirror_7 [2, 2, 0, 0, 0, 0, 1] [0, 2, 0, 2, 1, 2, 1] [1, 2, 2, 2, 2, 1, 0] [1, 0, 0, 1, 1, 2, 0] [2, 0, 0, 2, 2, 1, 0] demoR1_2200001 demoR2_2200001 demoC_2200001 demoM_2200001 demoMir_2200001

theorem demoR1_0010001 : invRung 7 5 20 [0, 0, 1, 0, 0, 0, 1] [0, 0, 1, 0, 0, 0, 1] 1 2 false = ([2, 0, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_0010001 : invRung 7 5 20 [0, 0, 1, 0, 0, 0, 1] [2, 0, 1, 0, 1, 2, 0] 3 1 true = ([1, 1, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_0010001 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 2, 1] = [0, 2, 1, 1, 0, 2, 1] := by
  decide

theorem demoM_0010001 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 2, 1] [0, 0, 1, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0010001 : specInv 7 5 20 [0, 0, 1, 0, 0, 0, 1] = some [0, 2, 1, 1, 0, 2, 1] :=
  specInv_white_7 [0, 0, 1, 0, 0, 0, 1] [2, 0, 1, 0, 1, 2, 0] [1, 1, 0, 0, 2, 2, 1] [0, 2, 1, 1, 0, 2, 1] demoR1_0010001 demoR2_0010001 demoC_0010001 demoM_0010001

theorem demoR1_1010001 : invRung 7 5 20 [1, 0, 1, 0, 0, 0, 1] [1, 0, 1, 0, 0, 0, 1] 1 2 false = ([0, 2, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_1010001 : invRung 7 5 20 [1, 0, 1, 0, 0, 0, 1] [0, 2, 2, 2, 1, 0, 1] 3 1 true = ([2, 1, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1010001 : fieldCube 7 5 20 [2, 1, 1, 0, 0, 1, 0] = [0, 1, 1, 1, 1, 1, 0] := by
  decide

theorem demoM_1010001 : fieldMul 7 5 20 [0, 1, 1, 1, 1, 1, 0] [1, 0, 1, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1010001 : specInv 7 5 20 [1, 0, 1, 0, 0, 0, 1] = some [0, 1, 1, 1, 1, 1, 0] :=
  specInv_white_7 [1, 0, 1, 0, 0, 0, 1] [0, 2, 2, 2, 1, 0, 1] [2, 1, 1, 0, 0, 1, 0] [0, 1, 1, 1, 1, 1, 0] demoR1_1010001 demoR2_1010001 demoC_1010001 demoM_1010001

theorem demoR1_2010001 : invRung 7 5 20 [2, 0, 1, 0, 0, 0, 1] [2, 0, 1, 0, 0, 0, 1] 1 2 false = ([2, 2, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_2010001 : invRung 7 5 20 [2, 0, 1, 0, 0, 0, 1] [2, 2, 0, 2, 0, 1, 1] 3 1 true = ([2, 2, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_2010001 : fieldCube 7 5 20 [2, 2, 1, 1, 2, 0, 1] = [0, 0, 0, 2, 1, 1, 1] := by
  decide

theorem demoM_2010001 : fieldMul 7 5 20 [0, 0, 0, 2, 1, 1, 1] [2, 0, 1, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2010001 : specInv 7 5 20 [2, 0, 1, 0, 0, 0, 1] = some [0, 0, 0, 2, 1, 1, 1] :=
  specInv_white_7 [2, 0, 1, 0, 0, 0, 1] [2, 2, 0, 2, 0, 1, 1] [2, 2, 1, 1, 2, 0, 1] [0, 0, 0, 2, 1, 1, 1] demoR1_2010001 demoR2_2010001 demoC_2010001 demoM_2010001

theorem demoR1_0110001 : invRung 7 5 20 [0, 1, 1, 0, 0, 0, 1] [0, 1, 1, 0, 0, 0, 1] 1 2 false = ([0, 1, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_0110001 : invRung 7 5 20 [0, 1, 1, 0, 0, 0, 1] [0, 1, 2, 2, 2, 0, 0] 3 1 true = ([2, 0, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_0110001 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 0, 0] = [1, 1, 2, 1, 0, 0, 0] := by
  decide

theorem demoM_0110001 : fieldMul 7 5 20 [1, 1, 2, 1, 0, 0, 0] [0, 1, 1, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110001 : mirrorTrits [1, 1, 2, 1, 0, 0, 0] = [2, 2, 1, 2, 0, 0, 0] := by
  decide

theorem demoInv_0110001 : specInv 7 5 20 [0, 1, 1, 0, 0, 0, 1] = some [2, 2, 1, 2, 0, 0, 0] :=
  specInv_mirror_7 [0, 1, 1, 0, 0, 0, 1] [0, 1, 2, 2, 2, 0, 0] [2, 0, 2, 2, 1, 0, 0] [1, 1, 2, 1, 0, 0, 0] [2, 2, 1, 2, 0, 0, 0] demoR1_0110001 demoR2_0110001 demoC_0110001 demoM_0110001 demoMir_0110001

theorem demoR1_1110001 : invRung 7 5 20 [1, 1, 1, 0, 0, 0, 1] [1, 1, 1, 0, 0, 0, 1] 1 2 false = ([0, 1, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_1110001 : invRung 7 5 20 [1, 1, 1, 0, 0, 0, 1] [0, 1, 0, 2, 1, 2, 1] 3 1 true = ([1, 1, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_1110001 : fieldCube 7 5 20 [1, 1, 2, 1, 0, 1, 0] = [0, 1, 2, 1, 1, 2, 1] := by
  decide

theorem demoM_1110001 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 2, 1] [1, 1, 1, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1110001 : specInv 7 5 20 [1, 1, 1, 0, 0, 0, 1] = some [0, 1, 2, 1, 1, 2, 1] :=
  specInv_white_7 [1, 1, 1, 0, 0, 0, 1] [0, 1, 0, 2, 1, 2, 1] [1, 1, 2, 1, 0, 1, 0] [0, 1, 2, 1, 1, 2, 1] demoR1_1110001 demoR2_1110001 demoC_1110001 demoM_1110001

theorem demoR1_2110001 : invRung 7 5 20 [2, 1, 1, 0, 0, 0, 1] [2, 1, 1, 0, 0, 0, 1] 1 2 false = ([0, 1, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2110001 : invRung 7 5 20 [2, 1, 1, 0, 0, 0, 1] [0, 1, 0, 2, 2, 0, 1] 3 1 true = ([2, 2, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_2110001 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 2, 2] = [0, 0, 2, 0, 1, 2, 0] := by
  decide

theorem demoM_2110001 : fieldMul 7 5 20 [0, 0, 2, 0, 1, 2, 0] [2, 1, 1, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2110001 : specInv 7 5 20 [2, 1, 1, 0, 0, 0, 1] = some [0, 0, 2, 0, 1, 2, 0] :=
  specInv_white_7 [2, 1, 1, 0, 0, 0, 1] [0, 1, 0, 2, 2, 0, 1] [2, 2, 1, 2, 2, 2, 2] [0, 0, 2, 0, 1, 2, 0] demoR1_2110001 demoR2_2110001 demoC_2110001 demoM_2110001

theorem demoR1_0210001 : invRung 7 5 20 [0, 2, 1, 0, 0, 0, 1] [0, 2, 1, 0, 0, 0, 1] 1 2 false = ([1, 2, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_0210001 : invRung 7 5 20 [0, 2, 1, 0, 0, 0, 1] [1, 2, 0, 2, 0, 2, 1] 3 1 true = ([1, 1, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0210001 : fieldCube 7 5 20 [1, 1, 0, 1, 1, 2, 2] = [1, 2, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_0210001 : fieldMul 7 5 20 [1, 2, 1, 1, 1, 0, 1] [0, 2, 1, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210001 : mirrorTrits [1, 2, 1, 1, 1, 0, 1] = [2, 1, 2, 2, 2, 0, 2] := by
  decide

theorem demoInv_0210001 : specInv 7 5 20 [0, 2, 1, 0, 0, 0, 1] = some [2, 1, 2, 2, 2, 0, 2] :=
  specInv_mirror_7 [0, 2, 1, 0, 0, 0, 1] [1, 2, 0, 2, 0, 2, 1] [1, 1, 0, 1, 1, 2, 2] [1, 2, 1, 1, 1, 0, 1] [2, 1, 2, 2, 2, 0, 2] demoR1_0210001 demoR2_0210001 demoC_0210001 demoM_0210001 demoMir_0210001

theorem demoR1_1210001 : invRung 7 5 20 [1, 2, 1, 0, 0, 0, 1] [1, 2, 1, 0, 0, 0, 1] 1 2 false = ([0, 1, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_1210001 : invRung 7 5 20 [1, 2, 1, 0, 0, 0, 1] [0, 1, 1, 1, 0, 1, 0] 3 1 true = ([0, 1, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_1210001 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 0, 2] = [2, 1, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_1210001 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 0, 1] [1, 2, 1, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1210001 : specInv 7 5 20 [1, 2, 1, 0, 0, 0, 1] = some [2, 1, 0, 2, 2, 0, 1] :=
  specInv_white_7 [1, 2, 1, 0, 0, 0, 1] [0, 1, 1, 1, 0, 1, 0] [0, 1, 0, 2, 2, 0, 2] [2, 1, 0, 2, 2, 0, 1] demoR1_1210001 demoR2_1210001 demoC_1210001 demoM_1210001

theorem demoR1_2210001 : invRung 7 5 20 [2, 2, 1, 0, 0, 0, 1] [2, 2, 1, 0, 0, 0, 1] 1 2 false = ([1, 2, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_2210001 : invRung 7 5 20 [2, 2, 1, 0, 0, 0, 1] [1, 2, 0, 2, 2, 1, 1] 3 1 true = ([1, 2, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_2210001 : fieldCube 7 5 20 [1, 2, 0, 0, 2, 0, 2] = [1, 1, 1, 0, 2, 1, 1] := by
  decide

theorem demoM_2210001 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 1, 1] [2, 2, 1, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2210001 : specInv 7 5 20 [2, 2, 1, 0, 0, 0, 1] = some [1, 1, 1, 0, 2, 1, 1] :=
  specInv_white_7 [2, 2, 1, 0, 0, 0, 1] [1, 2, 0, 2, 2, 1, 1] [1, 2, 0, 0, 2, 0, 2] [1, 1, 1, 0, 2, 1, 1] demoR1_2210001 demoR2_2210001 demoC_2210001 demoM_2210001

theorem demoR1_0020001 : invRung 7 5 20 [0, 0, 2, 0, 0, 0, 1] [0, 0, 2, 0, 0, 0, 1] 1 2 false = ([0, 2, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_0020001 : invRung 7 5 20 [0, 0, 2, 0, 0, 0, 1] [0, 2, 0, 0, 0, 1, 2] 3 1 true = ([2, 0, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_0020001 : fieldCube 7 5 20 [2, 0, 1, 0, 2, 0, 2] = [2, 1, 1, 1, 2, 1, 2] := by
  decide

theorem demoM_0020001 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 1, 2] [0, 0, 2, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020001 : mirrorTrits [2, 1, 1, 1, 2, 1, 2] = [1, 2, 2, 2, 1, 2, 1] := by
  decide

theorem demoInv_0020001 : specInv 7 5 20 [0, 0, 2, 0, 0, 0, 1] = some [1, 2, 2, 2, 1, 2, 1] :=
  specInv_mirror_7 [0, 0, 2, 0, 0, 0, 1] [0, 2, 0, 0, 0, 1, 2] [2, 0, 1, 0, 2, 0, 2] [2, 1, 1, 1, 2, 1, 2] [1, 2, 2, 2, 1, 2, 1] demoR1_0020001 demoR2_0020001 demoC_0020001 demoM_0020001 demoMir_0020001

theorem demoR1_1020001 : invRung 7 5 20 [1, 0, 2, 0, 0, 0, 1] [1, 0, 2, 0, 0, 0, 1] 1 2 false = ([0, 1, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_1020001 : invRung 7 5 20 [1, 0, 2, 0, 0, 0, 1] [0, 1, 1, 2, 2, 0, 1] 3 1 true = ([2, 2, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_1020001 : fieldCube 7 5 20 [2, 2, 1, 0, 1, 2, 2] = [1, 2, 0, 2, 1, 2, 2] := by
  decide

theorem demoM_1020001 : fieldMul 7 5 20 [1, 2, 0, 2, 1, 2, 2] [1, 0, 2, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020001 : mirrorTrits [1, 2, 0, 2, 1, 2, 2] = [2, 1, 0, 1, 2, 1, 1] := by
  decide

theorem demoInv_1020001 : specInv 7 5 20 [1, 0, 2, 0, 0, 0, 1] = some [2, 1, 0, 1, 2, 1, 1] :=
  specInv_mirror_7 [1, 0, 2, 0, 0, 0, 1] [0, 1, 1, 2, 2, 0, 1] [2, 2, 1, 0, 1, 2, 2] [1, 2, 0, 2, 1, 2, 2] [2, 1, 0, 1, 2, 1, 1] demoR1_1020001 demoR2_1020001 demoC_1020001 demoM_1020001 demoMir_1020001

theorem demoR1_2020001 : invRung 7 5 20 [2, 0, 2, 0, 0, 0, 1] [2, 0, 2, 0, 0, 0, 1] 1 2 false = ([1, 0, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_2020001 : invRung 7 5 20 [2, 0, 2, 0, 0, 0, 1] [1, 0, 2, 1, 2, 1, 0] 3 1 true = ([0, 0, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_2020001 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 2, 1] = [2, 1, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_2020001 : fieldMul 7 5 20 [2, 1, 1, 2, 0, 1, 0] [2, 0, 2, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2020001 : specInv 7 5 20 [2, 0, 2, 0, 0, 0, 1] = some [2, 1, 1, 2, 0, 1, 0] :=
  specInv_white_7 [2, 0, 2, 0, 0, 0, 1] [1, 0, 2, 1, 2, 1, 0] [0, 0, 0, 0, 1, 2, 1] [2, 1, 1, 2, 0, 1, 0] demoR1_2020001 demoR2_2020001 demoC_2020001 demoM_2020001

theorem demoR1_0120001 : invRung 7 5 20 [0, 1, 2, 0, 0, 0, 1] [0, 1, 2, 0, 0, 0, 1] 1 2 false = ([1, 1, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_0120001 : invRung 7 5 20 [0, 1, 2, 0, 0, 0, 1] [1, 1, 2, 0, 2, 2, 1] 3 1 true = ([1, 2, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0120001 : fieldCube 7 5 20 [1, 2, 2, 1, 2, 2, 2] = [1, 0, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_0120001 : fieldMul 7 5 20 [1, 0, 1, 0, 1, 1, 1] [0, 1, 2, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0120001 : specInv 7 5 20 [0, 1, 2, 0, 0, 0, 1] = some [1, 0, 1, 0, 1, 1, 1] :=
  specInv_white_7 [0, 1, 2, 0, 0, 0, 1] [1, 1, 2, 0, 2, 2, 1] [1, 2, 2, 1, 2, 2, 2] [1, 0, 1, 0, 1, 1, 1] demoR1_0120001 demoR2_0120001 demoC_0120001 demoM_0120001

theorem demoR1_1120001 : invRung 7 5 20 [1, 1, 2, 0, 0, 0, 1] [1, 1, 2, 0, 0, 0, 1] 1 2 false = ([0, 0, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1120001 : invRung 7 5 20 [1, 1, 2, 0, 0, 0, 1] [0, 0, 1, 2, 1, 0, 2] 3 1 true = ([0, 2, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_1120001 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 2, 0] = [2, 0, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_1120001 : fieldMul 7 5 20 [2, 0, 2, 0, 2, 0, 2] [1, 1, 2, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1120001 : specInv 7 5 20 [1, 1, 2, 0, 0, 0, 1] = some [2, 0, 2, 0, 2, 0, 2] :=
  specInv_white_7 [1, 1, 2, 0, 0, 0, 1] [0, 0, 1, 2, 1, 0, 2] [0, 2, 0, 0, 1, 2, 0] [2, 0, 2, 0, 2, 0, 2] demoR1_1120001 demoR2_1120001 demoC_1120001 demoM_1120001

theorem demoR1_2120001 : invRung 7 5 20 [2, 1, 2, 0, 0, 0, 1] [2, 1, 2, 0, 0, 0, 1] 1 2 false = ([2, 1, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_2120001 : invRung 7 5 20 [2, 1, 2, 0, 0, 0, 1] [2, 1, 2, 0, 1, 2, 0] 3 1 true = ([0, 2, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_2120001 : fieldCube 7 5 20 [0, 2, 2, 1, 2, 1, 2] = [2, 2, 0, 0, 0, 0, 2] := by
  decide

theorem demoM_2120001 : fieldMul 7 5 20 [2, 2, 0, 0, 0, 0, 2] [2, 1, 2, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120001 : mirrorTrits [2, 2, 0, 0, 0, 0, 2] = [1, 1, 0, 0, 0, 0, 1] := by
  decide

theorem demoInv_2120001 : specInv 7 5 20 [2, 1, 2, 0, 0, 0, 1] = some [1, 1, 0, 0, 0, 0, 1] :=
  specInv_mirror_7 [2, 1, 2, 0, 0, 0, 1] [2, 1, 2, 0, 1, 2, 0] [0, 2, 2, 1, 2, 1, 2] [2, 2, 0, 0, 0, 0, 2] [1, 1, 0, 0, 0, 0, 1] demoR1_2120001 demoR2_2120001 demoC_2120001 demoM_2120001 demoMir_2120001

theorem demoR1_0220001 : invRung 7 5 20 [0, 2, 2, 0, 0, 0, 1] [0, 2, 2, 0, 0, 0, 1] 1 2 false = ([0, 2, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_0220001 : invRung 7 5 20 [0, 2, 2, 0, 0, 0, 1] [0, 2, 2, 1, 1, 2, 1] 3 1 true = ([1, 1, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0220001 : fieldCube 7 5 20 [1, 1, 0, 0, 0, 1, 1] = [2, 2, 0, 2, 2, 2, 0] := by
  decide

theorem demoM_0220001 : fieldMul 7 5 20 [2, 2, 0, 2, 2, 2, 0] [0, 2, 2, 0, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0220001 : specInv 7 5 20 [0, 2, 2, 0, 0, 0, 1] = some [2, 2, 0, 2, 2, 2, 0] :=
  specInv_white_7 [0, 2, 2, 0, 0, 0, 1] [0, 2, 2, 1, 1, 2, 1] [1, 1, 0, 0, 0, 1, 1] [2, 2, 0, 2, 2, 2, 0] demoR1_0220001 demoR2_0220001 demoC_0220001 demoM_0220001

theorem demoR1_1220001 : invRung 7 5 20 [1, 2, 2, 0, 0, 0, 1] [1, 2, 2, 0, 0, 0, 1] 1 2 false = ([1, 2, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_1220001 : invRung 7 5 20 [1, 2, 2, 0, 0, 0, 1] [1, 2, 2, 1, 2, 1, 2] 3 1 true = ([0, 2, 0, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_1220001 : fieldCube 7 5 20 [0, 2, 0, 2, 2, 1, 2] = [0, 2, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_1220001 : fieldMul 7 5 20 [0, 2, 1, 0, 0, 1, 0] [1, 2, 2, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220001 : mirrorTrits [0, 2, 1, 0, 0, 1, 0] = [0, 1, 2, 0, 0, 2, 0] := by
  decide

theorem demoInv_1220001 : specInv 7 5 20 [1, 2, 2, 0, 0, 0, 1] = some [0, 1, 2, 0, 0, 2, 0] :=
  specInv_mirror_7 [1, 2, 2, 0, 0, 0, 1] [1, 2, 2, 1, 2, 1, 2] [0, 2, 0, 2, 2, 1, 2] [0, 2, 1, 0, 0, 1, 0] [0, 1, 2, 0, 0, 2, 0] demoR1_1220001 demoR2_1220001 demoC_1220001 demoM_1220001 demoMir_1220001

theorem demoR1_2220001 : invRung 7 5 20 [2, 2, 2, 0, 0, 0, 1] [2, 2, 2, 0, 0, 0, 1] 1 2 false = ([1, 0, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_2220001 : invRung 7 5 20 [2, 2, 2, 0, 0, 0, 1] [1, 0, 0, 2, 1, 0, 0] 3 1 true = ([2, 2, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_2220001 : fieldCube 7 5 20 [2, 2, 1, 2, 1, 1, 0] = [2, 2, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_2220001 : fieldMul 7 5 20 [2, 2, 0, 0, 1, 1, 1] [2, 2, 2, 0, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220001 : mirrorTrits [2, 2, 0, 0, 1, 1, 1] = [1, 1, 0, 0, 2, 2, 2] := by
  decide

theorem demoInv_2220001 : specInv 7 5 20 [2, 2, 2, 0, 0, 0, 1] = some [1, 1, 0, 0, 2, 2, 2] :=
  specInv_mirror_7 [2, 2, 2, 0, 0, 0, 1] [1, 0, 0, 2, 1, 0, 0] [2, 2, 1, 2, 1, 1, 0] [2, 2, 0, 0, 1, 1, 1] [1, 1, 0, 0, 2, 2, 2] demoR1_2220001 demoR2_2220001 demoC_2220001 demoM_2220001 demoMir_2220001

theorem demoR1_0001001 : invRung 7 5 20 [0, 0, 0, 1, 0, 0, 1] [0, 0, 0, 1, 0, 0, 1] 1 2 false = ([1, 0, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_0001001 : invRung 7 5 20 [0, 0, 0, 1, 0, 0, 1] [1, 0, 2, 2, 2, 2, 2] 3 1 true = ([0, 0, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0001001 : fieldCube 7 5 20 [0, 0, 0, 0, 2, 1, 0] = [1, 0, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_0001001 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 0, 1] [0, 0, 0, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0001001 : specInv 7 5 20 [0, 0, 0, 1, 0, 0, 1] = some [1, 0, 1, 2, 1, 0, 1] :=
  specInv_white_7 [0, 0, 0, 1, 0, 0, 1] [1, 0, 2, 2, 2, 2, 2] [0, 0, 0, 0, 2, 1, 0] [1, 0, 1, 2, 1, 0, 1] demoR1_0001001 demoR2_0001001 demoC_0001001 demoM_0001001

theorem demoR1_1001001 : invRung 7 5 20 [1, 0, 0, 1, 0, 0, 1] [1, 0, 0, 1, 0, 0, 1] 1 2 false = ([2, 2, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1001001 : invRung 7 5 20 [1, 0, 0, 1, 0, 0, 1] [2, 2, 2, 0, 1, 1, 0] 3 1 true = ([2, 2, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_1001001 : fieldCube 7 5 20 [2, 2, 2, 2, 2, 0, 2] = [1, 1, 0, 0, 2, 0, 0] := by
  decide

theorem demoM_1001001 : fieldMul 7 5 20 [1, 1, 0, 0, 2, 0, 0] [1, 0, 0, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1001001 : specInv 7 5 20 [1, 0, 0, 1, 0, 0, 1] = some [1, 1, 0, 0, 2, 0, 0] :=
  specInv_white_7 [1, 0, 0, 1, 0, 0, 1] [2, 2, 2, 0, 1, 1, 0] [2, 2, 2, 2, 2, 0, 2] [1, 1, 0, 0, 2, 0, 0] demoR1_1001001 demoR2_1001001 demoC_1001001 demoM_1001001

theorem demoR1_2001001 : invRung 7 5 20 [2, 0, 0, 1, 0, 0, 1] [2, 0, 0, 1, 0, 0, 1] 1 2 false = ([1, 2, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_2001001 : invRung 7 5 20 [2, 0, 0, 1, 0, 0, 1] [1, 2, 0, 2, 2, 2, 2] 3 1 true = ([0, 2, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_2001001 : fieldCube 7 5 20 [0, 2, 2, 1, 0, 0, 2] = [1, 2, 2, 1, 2, 0, 1] := by
  decide

theorem demoM_2001001 : fieldMul 7 5 20 [1, 2, 2, 1, 2, 0, 1] [2, 0, 0, 1, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001001 : mirrorTrits [1, 2, 2, 1, 2, 0, 1] = [2, 1, 1, 2, 1, 0, 2] := by
  decide

theorem demoInv_2001001 : specInv 7 5 20 [2, 0, 0, 1, 0, 0, 1] = some [2, 1, 1, 2, 1, 0, 2] :=
  specInv_mirror_7 [2, 0, 0, 1, 0, 0, 1] [1, 2, 0, 2, 2, 2, 2] [0, 2, 2, 1, 0, 0, 2] [1, 2, 2, 1, 2, 0, 1] [2, 1, 1, 2, 1, 0, 2] demoR1_2001001 demoR2_2001001 demoC_2001001 demoM_2001001 demoMir_2001001

theorem demoR1_0101001 : invRung 7 5 20 [0, 1, 0, 1, 0, 0, 1] [0, 1, 0, 1, 0, 0, 1] 1 2 false = ([1, 0, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0101001 : invRung 7 5 20 [0, 1, 0, 1, 0, 0, 1] [1, 0, 2, 0, 1, 1, 1] 3 1 true = ([0, 1, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0101001 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 1, 0] = [1, 0, 1, 0, 1, 0, 0] := by
  decide

theorem demoM_0101001 : fieldMul 7 5 20 [1, 0, 1, 0, 1, 0, 0] [0, 1, 0, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0101001 : specInv 7 5 20 [0, 1, 0, 1, 0, 0, 1] = some [1, 0, 1, 0, 1, 0, 0] :=
  specInv_white_7 [0, 1, 0, 1, 0, 0, 1] [1, 0, 2, 0, 1, 1, 1] [0, 1, 2, 0, 2, 1, 0] [1, 0, 1, 0, 1, 0, 0] demoR1_0101001 demoR2_0101001 demoC_0101001 demoM_0101001

theorem demoR1_1101001 : invRung 7 5 20 [1, 1, 0, 1, 0, 0, 1] [1, 1, 0, 1, 0, 0, 1] 1 2 false = ([2, 1, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1101001 : invRung 7 5 20 [1, 1, 0, 1, 0, 0, 1] [2, 1, 1, 0, 0, 2, 0] 3 1 true = ([2, 2, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_1101001 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 0, 0] = [0, 1, 1, 0, 0, 2, 2] := by
  decide

theorem demoM_1101001 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 2, 2] [1, 1, 0, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1101001 : specInv 7 5 20 [1, 1, 0, 1, 0, 0, 1] = some [0, 1, 1, 0, 0, 2, 2] :=
  specInv_white_7 [1, 1, 0, 1, 0, 0, 1] [2, 1, 1, 0, 0, 2, 0] [2, 2, 1, 1, 1, 0, 0] [0, 1, 1, 0, 0, 2, 2] demoR1_1101001 demoR2_1101001 demoC_1101001 demoM_1101001

theorem demoR1_2101001 : invRung 7 5 20 [2, 1, 0, 1, 0, 0, 1] [2, 1, 0, 1, 0, 0, 1] 1 2 false = ([0, 2, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_2101001 : invRung 7 5 20 [2, 1, 0, 1, 0, 0, 1] [0, 2, 0, 0, 1, 1, 0] 3 1 true = ([1, 2, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_2101001 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 0, 2] = [1, 1, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_2101001 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 1, 2] [2, 1, 0, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2101001 : specInv 7 5 20 [2, 1, 0, 1, 0, 0, 1] = some [1, 1, 1, 0, 2, 1, 2] :=
  specInv_white_7 [2, 1, 0, 1, 0, 0, 1] [0, 2, 0, 0, 1, 1, 0] [1, 2, 1, 0, 2, 0, 2] [1, 1, 1, 0, 2, 1, 2] demoR1_2101001 demoR2_2101001 demoC_2101001 demoM_2101001

theorem demoR1_0201001 : invRung 7 5 20 [0, 2, 0, 1, 0, 0, 1] [0, 2, 0, 1, 0, 0, 1] 1 2 false = ([0, 2, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0201001 : invRung 7 5 20 [0, 2, 0, 1, 0, 0, 1] [0, 2, 1, 0, 2, 1, 2] 3 1 true = ([2, 2, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_0201001 : fieldCube 7 5 20 [2, 2, 2, 1, 2, 2, 1] = [2, 2, 2, 2, 0, 0, 0] := by
  decide

theorem demoM_0201001 : fieldMul 7 5 20 [2, 2, 2, 2, 0, 0, 0] [0, 2, 0, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0201001 : specInv 7 5 20 [0, 2, 0, 1, 0, 0, 1] = some [2, 2, 2, 2, 0, 0, 0] :=
  specInv_white_7 [0, 2, 0, 1, 0, 0, 1] [0, 2, 1, 0, 2, 1, 2] [2, 2, 2, 1, 2, 2, 1] [2, 2, 2, 2, 0, 0, 0] demoR1_0201001 demoR2_0201001 demoC_0201001 demoM_0201001

theorem demoR1_1201001 : invRung 7 5 20 [1, 2, 0, 1, 0, 0, 1] [1, 2, 0, 1, 0, 0, 1] 1 2 false = ([1, 0, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_1201001 : invRung 7 5 20 [1, 2, 0, 1, 0, 0, 1] [1, 0, 2, 0, 0, 0, 0] 3 1 true = ([0, 0, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_1201001 : fieldCube 7 5 20 [0, 0, 0, 0, 2, 0, 2] = [0, 1, 1, 1, 2, 1, 1] := by
  decide

theorem demoM_1201001 : fieldMul 7 5 20 [0, 1, 1, 1, 2, 1, 1] [1, 2, 0, 1, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201001 : mirrorTrits [0, 1, 1, 1, 2, 1, 1] = [0, 2, 2, 2, 1, 2, 2] := by
  decide

theorem demoInv_1201001 : specInv 7 5 20 [1, 2, 0, 1, 0, 0, 1] = some [0, 2, 2, 2, 1, 2, 2] :=
  specInv_mirror_7 [1, 2, 0, 1, 0, 0, 1] [1, 0, 2, 0, 0, 0, 0] [0, 0, 0, 0, 2, 0, 2] [0, 1, 1, 1, 2, 1, 1] [0, 2, 2, 2, 1, 2, 2] demoR1_1201001 demoR2_1201001 demoC_1201001 demoM_1201001 demoMir_1201001

theorem demoR1_2201001 : invRung 7 5 20 [2, 2, 0, 1, 0, 0, 1] [2, 2, 0, 1, 0, 0, 1] 1 2 false = ([1, 0, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_2201001 : invRung 7 5 20 [2, 2, 0, 1, 0, 0, 1] [1, 0, 2, 2, 0, 2, 2] 3 1 true = ([0, 0, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_2201001 : fieldCube 7 5 20 [0, 0, 2, 2, 0, 1, 2] = [0, 0, 1, 2, 0, 2, 0] := by
  decide

theorem demoM_2201001 : fieldMul 7 5 20 [0, 0, 1, 2, 0, 2, 0] [2, 2, 0, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2201001 : specInv 7 5 20 [2, 2, 0, 1, 0, 0, 1] = some [0, 0, 1, 2, 0, 2, 0] :=
  specInv_white_7 [2, 2, 0, 1, 0, 0, 1] [1, 0, 2, 2, 0, 2, 2] [0, 0, 2, 2, 0, 1, 2] [0, 0, 1, 2, 0, 2, 0] demoR1_2201001 demoR2_2201001 demoC_2201001 demoM_2201001

theorem demoR1_0011001 : invRung 7 5 20 [0, 0, 1, 1, 0, 0, 1] [0, 0, 1, 1, 0, 0, 1] 1 2 false = ([2, 1, 2, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_0011001 : invRung 7 5 20 [0, 0, 1, 1, 0, 0, 1] [2, 1, 2, 2, 2, 0, 0] 3 1 true = ([1, 2, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0011001 : fieldCube 7 5 20 [1, 2, 0, 0, 1, 0, 1] = [1, 2, 2, 1, 1, 2, 2] := by
  decide

theorem demoM_0011001 : fieldMul 7 5 20 [1, 2, 2, 1, 1, 2, 2] [0, 0, 1, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0011001 : specInv 7 5 20 [0, 0, 1, 1, 0, 0, 1] = some [1, 2, 2, 1, 1, 2, 2] :=
  specInv_white_7 [0, 0, 1, 1, 0, 0, 1] [2, 1, 2, 2, 2, 0, 0] [1, 2, 0, 0, 1, 0, 1] [1, 2, 2, 1, 1, 2, 2] demoR1_0011001 demoR2_0011001 demoC_0011001 demoM_0011001

theorem demoR1_1011001 : invRung 7 5 20 [1, 0, 1, 1, 0, 0, 1] [1, 0, 1, 1, 0, 0, 1] 1 2 false = ([0, 1, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1011001 : invRung 7 5 20 [1, 0, 1, 1, 0, 0, 1] [0, 1, 2, 2, 2, 1, 1] 3 1 true = ([1, 1, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1011001 : fieldCube 7 5 20 [1, 1, 1, 1, 0, 2, 1] = [1, 0, 2, 2, 0, 1, 0] := by
  decide

theorem demoM_1011001 : fieldMul 7 5 20 [1, 0, 2, 2, 0, 1, 0] [1, 0, 1, 1, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1011001 : mirrorTrits [1, 0, 2, 2, 0, 1, 0] = [2, 0, 1, 1, 0, 2, 0] := by
  decide

theorem demoInv_1011001 : specInv 7 5 20 [1, 0, 1, 1, 0, 0, 1] = some [2, 0, 1, 1, 0, 2, 0] :=
  specInv_mirror_7 [1, 0, 1, 1, 0, 0, 1] [0, 1, 2, 2, 2, 1, 1] [1, 1, 1, 1, 0, 2, 1] [1, 0, 2, 2, 0, 1, 0] [2, 0, 1, 1, 0, 2, 0] demoR1_1011001 demoR2_1011001 demoC_1011001 demoM_1011001 demoMir_1011001

theorem demoR1_2011001 : invRung 7 5 20 [2, 0, 1, 1, 0, 0, 1] [2, 0, 1, 1, 0, 0, 1] 1 2 false = ([2, 1, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_2011001 : invRung 7 5 20 [2, 0, 1, 1, 0, 0, 1] [2, 1, 0, 2, 0, 0, 1] 3 1 true = ([2, 0, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_2011001 : fieldCube 7 5 20 [2, 0, 2, 2, 2, 2, 0] = [0, 1, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_2011001 : fieldMul 7 5 20 [0, 1, 1, 2, 2, 0, 2] [2, 0, 1, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2011001 : specInv 7 5 20 [2, 0, 1, 1, 0, 0, 1] = some [0, 1, 1, 2, 2, 0, 2] :=
  specInv_white_7 [2, 0, 1, 1, 0, 0, 1] [2, 1, 0, 2, 0, 0, 1] [2, 0, 2, 2, 2, 2, 0] [0, 1, 1, 2, 2, 0, 2] demoR1_2011001 demoR2_2011001 demoC_2011001 demoM_2011001

theorem demoR1_0111001 : invRung 7 5 20 [0, 1, 1, 1, 0, 0, 1] [0, 1, 1, 1, 0, 0, 1] 1 2 false = ([0, 2, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_0111001 : invRung 7 5 20 [0, 1, 1, 1, 0, 0, 1] [0, 2, 0, 0, 2, 2, 2] 3 1 true = ([2, 0, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0111001 : fieldCube 7 5 20 [2, 0, 1, 1, 0, 1, 2] = [1, 0, 0, 2, 0, 1, 2] := by
  decide

theorem demoM_0111001 : fieldMul 7 5 20 [1, 0, 0, 2, 0, 1, 2] [0, 1, 1, 1, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0111001 : mirrorTrits [1, 0, 0, 2, 0, 1, 2] = [2, 0, 0, 1, 0, 2, 1] := by
  decide

theorem demoInv_0111001 : specInv 7 5 20 [0, 1, 1, 1, 0, 0, 1] = some [2, 0, 0, 1, 0, 2, 1] :=
  specInv_mirror_7 [0, 1, 1, 1, 0, 0, 1] [0, 2, 0, 0, 2, 2, 2] [2, 0, 1, 1, 0, 1, 2] [1, 0, 0, 2, 0, 1, 2] [2, 0, 0, 1, 0, 2, 1] demoR1_0111001 demoR2_0111001 demoC_0111001 demoM_0111001 demoMir_0111001

theorem demoR1_1111001 : invRung 7 5 20 [1, 1, 1, 1, 0, 0, 1] [1, 1, 1, 1, 0, 0, 1] 1 2 false = ([1, 0, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_1111001 : invRung 7 5 20 [1, 1, 1, 1, 0, 0, 1] [1, 0, 0, 1, 0, 0, 0] 3 1 true = ([0, 1, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_1111001 : fieldCube 7 5 20 [0, 1, 2, 0, 0, 2, 2] = [2, 1, 0, 0, 1, 1, 2] := by
  decide

theorem demoM_1111001 : fieldMul 7 5 20 [2, 1, 0, 0, 1, 1, 2] [1, 1, 1, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1111001 : specInv 7 5 20 [1, 1, 1, 1, 0, 0, 1] = some [2, 1, 0, 0, 1, 1, 2] :=
  specInv_white_7 [1, 1, 1, 1, 0, 0, 1] [1, 0, 0, 1, 0, 0, 0] [0, 1, 2, 0, 0, 2, 2] [2, 1, 0, 0, 1, 1, 2] demoR1_1111001 demoR2_1111001 demoC_1111001 demoM_1111001

theorem demoR1_2111001 : invRung 7 5 20 [2, 1, 1, 1, 0, 0, 1] [2, 1, 1, 1, 0, 0, 1] 1 2 false = ([2, 0, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_2111001 : invRung 7 5 20 [2, 1, 1, 1, 0, 0, 1] [2, 0, 0, 1, 2, 1, 0] 3 1 true = ([2, 0, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_2111001 : fieldCube 7 5 20 [2, 0, 2, 1, 2, 0, 1] = [0, 0, 0, 0, 1, 1, 2] := by
  decide

theorem demoM_2111001 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 1, 2] [2, 1, 1, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2111001 : specInv 7 5 20 [2, 1, 1, 1, 0, 0, 1] = some [0, 0, 0, 0, 1, 1, 2] :=
  specInv_white_7 [2, 1, 1, 1, 0, 0, 1] [2, 0, 0, 1, 2, 1, 0] [2, 0, 2, 1, 2, 0, 1] [0, 0, 0, 0, 1, 1, 2] demoR1_2111001 demoR2_2111001 demoC_2111001 demoM_2111001

theorem demoR1_0211001 : invRung 7 5 20 [0, 2, 1, 1, 0, 0, 1] [0, 2, 1, 1, 0, 0, 1] 1 2 false = ([1, 1, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_0211001 : invRung 7 5 20 [0, 2, 1, 1, 0, 0, 1] [1, 1, 1, 0, 1, 0, 0] 3 1 true = ([1, 0, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_0211001 : fieldCube 7 5 20 [1, 0, 1, 2, 2, 2, 1] = [2, 2, 0, 0, 0, 1, 2] := by
  decide

theorem demoM_0211001 : fieldMul 7 5 20 [2, 2, 0, 0, 0, 1, 2] [0, 2, 1, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0211001 : specInv 7 5 20 [0, 2, 1, 1, 0, 0, 1] = some [2, 2, 0, 0, 0, 1, 2] :=
  specInv_white_7 [0, 2, 1, 1, 0, 0, 1] [1, 1, 1, 0, 1, 0, 0] [1, 0, 1, 2, 2, 2, 1] [2, 2, 0, 0, 0, 1, 2] demoR1_0211001 demoR2_0211001 demoC_0211001 demoM_0211001

theorem demoR1_1211001 : invRung 7 5 20 [1, 2, 1, 1, 0, 0, 1] [1, 2, 1, 1, 0, 0, 1] 1 2 false = ([2, 1, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_1211001 : invRung 7 5 20 [1, 2, 1, 1, 0, 0, 1] [2, 1, 1, 0, 2, 0, 2] 3 1 true = ([2, 2, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_1211001 : fieldCube 7 5 20 [2, 2, 0, 0, 0, 2, 0] = [1, 2, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_1211001 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 2, 1] [1, 2, 1, 1, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1211001 : mirrorTrits [1, 2, 2, 2, 2, 2, 1] = [2, 1, 1, 1, 1, 1, 2] := by
  decide

theorem demoInv_1211001 : specInv 7 5 20 [1, 2, 1, 1, 0, 0, 1] = some [2, 1, 1, 1, 1, 1, 2] :=
  specInv_mirror_7 [1, 2, 1, 1, 0, 0, 1] [2, 1, 1, 0, 2, 0, 2] [2, 2, 0, 0, 0, 2, 0] [1, 2, 2, 2, 2, 2, 1] [2, 1, 1, 1, 1, 1, 2] demoR1_1211001 demoR2_1211001 demoC_1211001 demoM_1211001 demoMir_1211001

theorem demoR1_2211001 : invRung 7 5 20 [2, 2, 1, 1, 0, 0, 1] [2, 2, 1, 1, 0, 0, 1] 1 2 false = ([2, 2, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_2211001 : invRung 7 5 20 [2, 2, 1, 1, 0, 0, 1] [2, 2, 0, 1, 1, 2, 0] 3 1 true = ([2, 1, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_2211001 : fieldCube 7 5 20 [2, 1, 2, 1, 1, 2, 0] = [2, 0, 0, 2, 2, 1, 1] := by
  decide

theorem demoM_2211001 : fieldMul 7 5 20 [2, 0, 0, 2, 2, 1, 1] [2, 2, 1, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2211001 : specInv 7 5 20 [2, 2, 1, 1, 0, 0, 1] = some [2, 0, 0, 2, 2, 1, 1] :=
  specInv_white_7 [2, 2, 1, 1, 0, 0, 1] [2, 2, 0, 1, 1, 2, 0] [2, 1, 2, 1, 1, 2, 0] [2, 0, 0, 2, 2, 1, 1] demoR1_2211001 demoR2_2211001 demoC_2211001 demoM_2211001

theorem demoR1_0021001 : invRung 7 5 20 [0, 0, 2, 1, 0, 0, 1] [0, 0, 2, 1, 0, 0, 1] 1 2 false = ([2, 0, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_0021001 : invRung 7 5 20 [0, 0, 2, 1, 0, 0, 1] [2, 0, 0, 1, 2, 1, 1] 3 1 true = ([0, 2, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_0021001 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 0, 1] = [1, 1, 0, 0, 1, 2, 2] := by
  decide

theorem demoM_0021001 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 2, 2] [0, 0, 2, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0021001 : specInv 7 5 20 [0, 0, 2, 1, 0, 0, 1] = some [1, 1, 0, 0, 1, 2, 2] :=
  specInv_white_7 [0, 0, 2, 1, 0, 0, 1] [2, 0, 0, 1, 2, 1, 1] [0, 2, 1, 1, 0, 0, 1] [1, 1, 0, 0, 1, 2, 2] demoR1_0021001 demoR2_0021001 demoC_0021001 demoM_0021001

theorem demoR1_1021001 : invRung 7 5 20 [1, 0, 2, 1, 0, 0, 1] [1, 0, 2, 1, 0, 0, 1] 1 2 false = ([2, 1, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_1021001 : invRung 7 5 20 [1, 0, 2, 1, 0, 0, 1] [2, 1, 1, 0, 0, 1, 1] 3 1 true = ([1, 1, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_1021001 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 1, 2] = [0, 1, 0, 1, 0, 2, 0] := by
  decide

theorem demoM_1021001 : fieldMul 7 5 20 [0, 1, 0, 1, 0, 2, 0] [1, 0, 2, 1, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021001 : mirrorTrits [0, 1, 0, 1, 0, 2, 0] = [0, 2, 0, 2, 0, 1, 0] := by
  decide

theorem demoInv_1021001 : specInv 7 5 20 [1, 0, 2, 1, 0, 0, 1] = some [0, 2, 0, 2, 0, 1, 0] :=
  specInv_mirror_7 [1, 0, 2, 1, 0, 0, 1] [2, 1, 1, 0, 0, 1, 1] [1, 1, 1, 1, 1, 1, 2] [0, 1, 0, 1, 0, 2, 0] [0, 2, 0, 2, 0, 1, 0] demoR1_1021001 demoR2_1021001 demoC_1021001 demoM_1021001 demoMir_1021001

theorem demoR1_2021001 : invRung 7 5 20 [2, 0, 2, 1, 0, 0, 1] [2, 0, 2, 1, 0, 0, 1] 1 2 false = ([0, 1, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_2021001 : invRung 7 5 20 [2, 0, 2, 1, 0, 0, 1] [0, 1, 0, 1, 1, 1, 1] 3 1 true = ([0, 0, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_2021001 : fieldCube 7 5 20 [0, 0, 0, 2, 2, 1, 1] = [0, 1, 2, 0, 2, 0, 2] := by
  decide

theorem demoM_2021001 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 0, 2] [2, 0, 2, 1, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021001 : mirrorTrits [0, 1, 2, 0, 2, 0, 2] = [0, 2, 1, 0, 1, 0, 1] := by
  decide

theorem demoInv_2021001 : specInv 7 5 20 [2, 0, 2, 1, 0, 0, 1] = some [0, 2, 1, 0, 1, 0, 1] :=
  specInv_mirror_7 [2, 0, 2, 1, 0, 0, 1] [0, 1, 0, 1, 1, 1, 1] [0, 0, 0, 2, 2, 1, 1] [0, 1, 2, 0, 2, 0, 2] [0, 2, 1, 0, 1, 0, 1] demoR1_2021001 demoR2_2021001 demoC_2021001 demoM_2021001 demoMir_2021001

theorem demoR1_0121001 : invRung 7 5 20 [0, 1, 2, 1, 0, 0, 1] [0, 1, 2, 1, 0, 0, 1] 1 2 false = ([1, 1, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_0121001 : invRung 7 5 20 [0, 1, 2, 1, 0, 0, 1] [1, 1, 1, 1, 2, 2, 2] 3 1 true = ([0, 2, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0121001 : fieldCube 7 5 20 [0, 2, 2, 0, 2, 1, 0] = [1, 0, 1, 1, 1, 0, 0] := by
  decide

theorem demoM_0121001 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 0, 0] [0, 1, 2, 1, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0121001 : mirrorTrits [1, 0, 1, 1, 1, 0, 0] = [2, 0, 2, 2, 2, 0, 0] := by
  decide

theorem demoInv_0121001 : specInv 7 5 20 [0, 1, 2, 1, 0, 0, 1] = some [2, 0, 2, 2, 2, 0, 0] :=
  specInv_mirror_7 [0, 1, 2, 1, 0, 0, 1] [1, 1, 1, 1, 2, 2, 2] [0, 2, 2, 0, 2, 1, 0] [1, 0, 1, 1, 1, 0, 0] [2, 0, 2, 2, 2, 0, 0] demoR1_0121001 demoR2_0121001 demoC_0121001 demoM_0121001 demoMir_0121001

theorem demoR1_1121001 : invRung 7 5 20 [1, 1, 2, 1, 0, 0, 1] [1, 1, 2, 1, 0, 0, 1] 1 2 false = ([1, 2, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_1121001 : invRung 7 5 20 [1, 1, 2, 1, 0, 0, 1] [1, 2, 0, 0, 2, 0, 1] 3 1 true = ([2, 0, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_1121001 : fieldCube 7 5 20 [2, 0, 2, 0, 2, 1, 2] = [0, 2, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_1121001 : fieldMul 7 5 20 [0, 2, 2, 1, 0, 2, 2] [1, 1, 2, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1121001 : specInv 7 5 20 [1, 1, 2, 1, 0, 0, 1] = some [0, 2, 2, 1, 0, 2, 2] :=
  specInv_white_7 [1, 1, 2, 1, 0, 0, 1] [1, 2, 0, 0, 2, 0, 1] [2, 0, 2, 0, 2, 1, 2] [0, 2, 2, 1, 0, 2, 2] demoR1_1121001 demoR2_1121001 demoC_1121001 demoM_1121001

theorem demoR1_2121001 : invRung 7 5 20 [2, 1, 2, 1, 0, 0, 1] [2, 1, 2, 1, 0, 0, 1] 1 2 false = ([1, 1, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2121001 : invRung 7 5 20 [2, 1, 2, 1, 0, 0, 1] [1, 1, 2, 0, 2, 0, 0] 3 1 true = ([0, 0, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_2121001 : fieldCube 7 5 20 [0, 0, 1, 1, 0, 0, 0] = [1, 0, 1, 0, 0, 1, 1] := by
  decide

theorem demoM_2121001 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 1, 1] [2, 1, 2, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2121001 : specInv 7 5 20 [2, 1, 2, 1, 0, 0, 1] = some [1, 0, 1, 0, 0, 1, 1] :=
  specInv_white_7 [2, 1, 2, 1, 0, 0, 1] [1, 1, 2, 0, 2, 0, 0] [0, 0, 1, 1, 0, 0, 0] [1, 0, 1, 0, 0, 1, 1] demoR1_2121001 demoR2_2121001 demoC_2121001 demoM_2121001

theorem demoR1_0221001 : invRung 7 5 20 [0, 2, 2, 1, 0, 0, 1] [0, 2, 2, 1, 0, 0, 1] 1 2 false = ([1, 2, 0, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_0221001 : invRung 7 5 20 [0, 2, 2, 1, 0, 0, 1] [1, 2, 0, 0, 1, 0, 2] 3 1 true = ([1, 1, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_0221001 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 0, 1] = [2, 0, 0, 1, 1, 1, 0] := by
  decide

theorem demoM_0221001 : fieldMul 7 5 20 [2, 0, 0, 1, 1, 1, 0] [0, 2, 2, 1, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0221001 : mirrorTrits [2, 0, 0, 1, 1, 1, 0] = [1, 0, 0, 2, 2, 2, 0] := by
  decide

theorem demoInv_0221001 : specInv 7 5 20 [0, 2, 2, 1, 0, 0, 1] = some [1, 0, 0, 2, 2, 2, 0] :=
  specInv_mirror_7 [0, 2, 2, 1, 0, 0, 1] [1, 2, 0, 0, 1, 0, 2] [1, 1, 0, 1, 2, 0, 1] [2, 0, 0, 1, 1, 1, 0] [1, 0, 0, 2, 2, 2, 0] demoR1_0221001 demoR2_0221001 demoC_0221001 demoM_0221001 demoMir_0221001

theorem demoR1_1221001 : invRung 7 5 20 [1, 2, 2, 1, 0, 0, 1] [1, 2, 2, 1, 0, 0, 1] 1 2 false = ([1, 1, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_1221001 : invRung 7 5 20 [1, 2, 2, 1, 0, 0, 1] [1, 1, 0, 0, 2, 1, 1] 3 1 true = ([2, 0, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1221001 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 1, 0] = [0, 2, 1, 1, 1, 2, 1] := by
  decide

theorem demoM_1221001 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 2, 1] [1, 2, 2, 1, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1221001 : specInv 7 5 20 [1, 2, 2, 1, 0, 0, 1] = some [0, 2, 1, 1, 1, 2, 1] :=
  specInv_white_7 [1, 2, 2, 1, 0, 0, 1] [1, 1, 0, 0, 2, 1, 1] [2, 0, 1, 0, 1, 1, 0] [0, 2, 1, 1, 1, 2, 1] demoR1_1221001 demoR2_1221001 demoC_1221001 demoM_1221001

theorem demoR1_2221001 : invRung 7 5 20 [2, 2, 2, 1, 0, 0, 1] [2, 2, 2, 1, 0, 0, 1] 1 2 false = ([0, 0, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_2221001 : invRung 7 5 20 [2, 2, 2, 1, 0, 0, 1] [0, 0, 2, 0, 0, 0, 0] 3 1 true = ([1, 0, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_2221001 : fieldCube 7 5 20 [1, 0, 2, 0, 1, 1, 2] = [2, 1, 2, 0, 0, 1, 1] := by
  decide

theorem demoM_2221001 : fieldMul 7 5 20 [2, 1, 2, 0, 0, 1, 1] [2, 2, 2, 1, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221001 : mirrorTrits [2, 1, 2, 0, 0, 1, 1] = [1, 2, 1, 0, 0, 2, 2] := by
  decide

theorem demoInv_2221001 : specInv 7 5 20 [2, 2, 2, 1, 0, 0, 1] = some [1, 2, 1, 0, 0, 2, 2] :=
  specInv_mirror_7 [2, 2, 2, 1, 0, 0, 1] [0, 0, 2, 0, 0, 0, 0] [1, 0, 2, 0, 1, 1, 2] [2, 1, 2, 0, 0, 1, 1] [1, 2, 1, 0, 0, 2, 2] demoR1_2221001 demoR2_2221001 demoC_2221001 demoM_2221001 demoMir_2221001

theorem demoR1_0002001 : invRung 7 5 20 [0, 0, 0, 2, 0, 0, 1] [0, 0, 0, 2, 0, 0, 1] 1 2 false = ([2, 0, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0002001 : invRung 7 5 20 [0, 0, 0, 2, 0, 0, 1] [2, 0, 0, 1, 0, 0, 0] 3 1 true = ([0, 0, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_0002001 : fieldCube 7 5 20 [0, 0, 0, 0, 1, 1, 0] = [1, 2, 1, 1, 1, 2, 0] := by
  decide

theorem demoM_0002001 : fieldMul 7 5 20 [1, 2, 1, 1, 1, 2, 0] [0, 0, 0, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0002001 : specInv 7 5 20 [0, 0, 0, 2, 0, 0, 1] = some [1, 2, 1, 1, 1, 2, 0] :=
  specInv_white_7 [0, 0, 0, 2, 0, 0, 1] [2, 0, 0, 1, 0, 0, 0] [0, 0, 0, 0, 1, 1, 0] [1, 2, 1, 1, 1, 2, 0] demoR1_0002001 demoR2_0002001 demoC_0002001 demoM_0002001

theorem demoR1_1002001 : invRung 7 5 20 [1, 0, 0, 2, 0, 0, 1] [1, 0, 0, 2, 0, 0, 1] 1 2 false = ([0, 1, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_1002001 : invRung 7 5 20 [1, 0, 0, 2, 0, 0, 1] [0, 1, 0, 2, 0, 1, 1] 3 1 true = ([1, 2, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1002001 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 2, 2] = [2, 2, 2, 2, 1, 1, 2] := by
  decide

theorem demoM_1002001 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 1, 2] [1, 0, 0, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1002001 : specInv 7 5 20 [1, 0, 0, 2, 0, 0, 1] = some [2, 2, 2, 2, 1, 1, 2] :=
  specInv_white_7 [1, 0, 0, 2, 0, 0, 1] [0, 1, 0, 2, 0, 1, 1] [1, 2, 1, 2, 1, 2, 2] [2, 2, 2, 2, 1, 1, 2] demoR1_1002001 demoR2_1002001 demoC_1002001 demoM_1002001

theorem demoR1_2002001 : invRung 7 5 20 [2, 0, 0, 2, 0, 0, 1] [2, 0, 0, 2, 0, 0, 1] 1 2 false = ([2, 2, 2, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_2002001 : invRung 7 5 20 [2, 0, 0, 2, 0, 0, 1] [2, 2, 2, 0, 1, 2, 0] 3 1 true = ([1, 1, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_2002001 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 2, 2] = [1, 0, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_2002001 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 1, 2] [2, 0, 0, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002001 : mirrorTrits [1, 0, 1, 2, 1, 1, 2] = [2, 0, 2, 1, 2, 2, 1] := by
  decide

theorem demoInv_2002001 : specInv 7 5 20 [2, 0, 0, 2, 0, 0, 1] = some [2, 0, 2, 1, 2, 2, 1] :=
  specInv_mirror_7 [2, 0, 0, 2, 0, 0, 1] [2, 2, 2, 0, 1, 2, 0] [1, 1, 0, 1, 2, 2, 2] [1, 0, 1, 2, 1, 1, 2] [2, 0, 2, 1, 2, 2, 1] demoR1_2002001 demoR2_2002001 demoC_2002001 demoM_2002001 demoMir_2002001

theorem demoR1_0102001 : invRung 7 5 20 [0, 1, 0, 2, 0, 0, 1] [0, 1, 0, 2, 0, 0, 1] 1 2 false = ([0, 2, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_0102001 : invRung 7 5 20 [0, 1, 0, 2, 0, 0, 1] [0, 2, 0, 1, 1, 2, 1] 3 1 true = ([1, 0, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_0102001 : fieldCube 7 5 20 [1, 0, 2, 1, 0, 2, 2] = [1, 1, 1, 2, 1, 2, 2] := by
  decide

theorem demoM_0102001 : fieldMul 7 5 20 [1, 1, 1, 2, 1, 2, 2] [0, 1, 0, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0102001 : specInv 7 5 20 [0, 1, 0, 2, 0, 0, 1] = some [1, 1, 1, 2, 1, 2, 2] :=
  specInv_white_7 [0, 1, 0, 2, 0, 0, 1] [0, 2, 0, 1, 1, 2, 1] [1, 0, 2, 1, 0, 2, 2] [1, 1, 1, 2, 1, 2, 2] demoR1_0102001 demoR2_0102001 demoC_0102001 demoM_0102001

theorem demoR1_1102001 : invRung 7 5 20 [1, 1, 0, 2, 0, 0, 1] [1, 1, 0, 2, 0, 0, 1] 1 2 false = ([2, 2, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_1102001 : invRung 7 5 20 [1, 1, 0, 2, 0, 0, 1] [2, 2, 2, 1, 0, 1, 0] 3 1 true = ([0, 1, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_1102001 : fieldCube 7 5 20 [0, 1, 1, 1, 1, 1, 1] = [2, 0, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_1102001 : fieldMul 7 5 20 [2, 0, 1, 0, 2, 1, 2] [1, 1, 0, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1102001 : specInv 7 5 20 [1, 1, 0, 2, 0, 0, 1] = some [2, 0, 1, 0, 2, 1, 2] :=
  specInv_white_7 [1, 1, 0, 2, 0, 0, 1] [2, 2, 2, 1, 0, 1, 0] [0, 1, 1, 1, 1, 1, 1] [2, 0, 1, 0, 2, 1, 2] demoR1_1102001 demoR2_1102001 demoC_1102001 demoM_1102001

theorem demoR1_2102001 : invRung 7 5 20 [2, 1, 0, 2, 0, 0, 1] [2, 1, 0, 2, 0, 0, 1] 1 2 false = ([1, 1, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_2102001 : invRung 7 5 20 [2, 1, 0, 2, 0, 0, 1] [1, 1, 2, 0, 0, 2, 0] 3 1 true = ([0, 1, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_2102001 : fieldCube 7 5 20 [0, 1, 1, 2, 0, 0, 0] = [2, 0, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_2102001 : fieldMul 7 5 20 [2, 0, 2, 1, 0, 2, 1] [2, 1, 0, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2102001 : specInv 7 5 20 [2, 1, 0, 2, 0, 0, 1] = some [2, 0, 2, 1, 0, 2, 1] :=
  specInv_white_7 [2, 1, 0, 2, 0, 0, 1] [1, 1, 2, 0, 0, 2, 0] [0, 1, 1, 2, 0, 0, 0] [2, 0, 2, 1, 0, 2, 1] demoR1_2102001 demoR2_2102001 demoC_2102001 demoM_2102001

theorem demoR1_0202001 : invRung 7 5 20 [0, 2, 0, 2, 0, 0, 1] [0, 2, 0, 2, 0, 0, 1] 1 2 false = ([0, 1, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_0202001 : invRung 7 5 20 [0, 2, 0, 2, 0, 0, 1] [0, 1, 2, 1, 0, 0, 2] 3 1 true = ([2, 2, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_0202001 : fieldCube 7 5 20 [2, 2, 0, 2, 1, 2, 2] = [0, 2, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_0202001 : fieldMul 7 5 20 [0, 2, 2, 2, 1, 1, 1] [0, 2, 0, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202001 : mirrorTrits [0, 2, 2, 2, 1, 1, 1] = [0, 1, 1, 1, 2, 2, 2] := by
  decide

theorem demoInv_0202001 : specInv 7 5 20 [0, 2, 0, 2, 0, 0, 1] = some [0, 1, 1, 1, 2, 2, 2] :=
  specInv_mirror_7 [0, 2, 0, 2, 0, 0, 1] [0, 1, 2, 1, 0, 0, 2] [2, 2, 0, 2, 1, 2, 2] [0, 2, 2, 2, 1, 1, 1] [0, 1, 1, 1, 2, 2, 2] demoR1_0202001 demoR2_0202001 demoC_0202001 demoM_0202001 demoMir_0202001

theorem demoR1_1202001 : invRung 7 5 20 [1, 2, 0, 2, 0, 0, 1] [1, 2, 0, 2, 0, 0, 1] 1 2 false = ([0, 1, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_1202001 : invRung 7 5 20 [1, 2, 0, 2, 0, 0, 1] [0, 1, 0, 1, 0, 2, 0] 3 1 true = ([0, 0, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_1202001 : fieldCube 7 5 20 [0, 0, 1, 0, 0, 0, 2] = [0, 2, 1, 2, 2, 2, 0] := by
  decide

theorem demoM_1202001 : fieldMul 7 5 20 [0, 2, 1, 2, 2, 2, 0] [1, 2, 0, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1202001 : specInv 7 5 20 [1, 2, 0, 2, 0, 0, 1] = some [0, 2, 1, 2, 2, 2, 0] :=
  specInv_white_7 [1, 2, 0, 2, 0, 0, 1] [0, 1, 0, 1, 0, 2, 0] [0, 0, 1, 0, 0, 0, 2] [0, 2, 1, 2, 2, 2, 0] demoR1_1202001 demoR2_1202001 demoC_1202001 demoM_1202001

theorem demoR1_2202001 : invRung 7 5 20 [2, 2, 0, 2, 0, 0, 1] [2, 2, 0, 2, 0, 0, 1] 1 2 false = ([2, 2, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_2202001 : invRung 7 5 20 [2, 2, 0, 2, 0, 0, 1] [2, 2, 1, 2, 1, 2, 2] 3 1 true = ([0, 2, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2202001 : fieldCube 7 5 20 [0, 2, 2, 1, 0, 2, 0] = [0, 2, 0, 2, 2, 0, 0] := by
  decide

theorem demoM_2202001 : fieldMul 7 5 20 [0, 2, 0, 2, 2, 0, 0] [2, 2, 0, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202001 : mirrorTrits [0, 2, 0, 2, 2, 0, 0] = [0, 1, 0, 1, 1, 0, 0] := by
  decide

theorem demoInv_2202001 : specInv 7 5 20 [2, 2, 0, 2, 0, 0, 1] = some [0, 1, 0, 1, 1, 0, 0] :=
  specInv_mirror_7 [2, 2, 0, 2, 0, 0, 1] [2, 2, 1, 2, 1, 2, 2] [0, 2, 2, 1, 0, 2, 0] [0, 2, 0, 2, 2, 0, 0] [0, 1, 0, 1, 1, 0, 0] demoR1_2202001 demoR2_2202001 demoC_2202001 demoM_2202001 demoMir_2202001

theorem demoR1_0012001 : invRung 7 5 20 [0, 0, 1, 2, 0, 0, 1] [0, 0, 1, 2, 0, 0, 1] 1 2 false = ([1, 0, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_0012001 : invRung 7 5 20 [0, 0, 1, 2, 0, 0, 1] [1, 0, 1, 0, 0, 1, 0] 3 1 true = ([2, 0, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0012001 : fieldCube 7 5 20 [2, 0, 2, 2, 1, 0, 1] = [1, 2, 1, 2, 1, 1, 1] := by
  decide

theorem demoM_0012001 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 1, 1] [0, 0, 1, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0012001 : specInv 7 5 20 [0, 0, 1, 2, 0, 0, 1] = some [1, 2, 1, 2, 1, 1, 1] :=
  specInv_white_7 [0, 0, 1, 2, 0, 0, 1] [1, 0, 1, 0, 0, 1, 0] [2, 0, 2, 2, 1, 0, 1] [1, 2, 1, 2, 1, 1, 1] demoR1_0012001 demoR2_0012001 demoC_0012001 demoM_0012001

theorem demoR1_1012001 : invRung 7 5 20 [1, 0, 1, 2, 0, 0, 1] [1, 0, 1, 2, 0, 0, 1] 1 2 false = ([2, 0, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_1012001 : invRung 7 5 20 [1, 0, 1, 2, 0, 0, 1] [2, 0, 2, 2, 0, 2, 2] 3 1 true = ([0, 0, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_1012001 : fieldCube 7 5 20 [0, 0, 2, 2, 1, 1, 0] = [0, 2, 0, 1, 1, 1, 2] := by
  decide

theorem demoM_1012001 : fieldMul 7 5 20 [0, 2, 0, 1, 1, 1, 2] [1, 0, 1, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1012001 : mirrorTrits [0, 2, 0, 1, 1, 1, 2] = [0, 1, 0, 2, 2, 2, 1] := by
  decide

theorem demoInv_1012001 : specInv 7 5 20 [1, 0, 1, 2, 0, 0, 1] = some [0, 1, 0, 2, 2, 2, 1] :=
  specInv_mirror_7 [1, 0, 1, 2, 0, 0, 1] [2, 0, 2, 2, 0, 2, 2] [0, 0, 2, 2, 1, 1, 0] [0, 2, 0, 1, 1, 1, 2] [0, 1, 0, 2, 2, 2, 1] demoR1_1012001 demoR2_1012001 demoC_1012001 demoM_1012001 demoMir_1012001

theorem demoR1_2012001 : invRung 7 5 20 [2, 0, 1, 2, 0, 0, 1] [2, 0, 1, 2, 0, 0, 1] 1 2 false = ([1, 2, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_2012001 : invRung 7 5 20 [2, 0, 1, 2, 0, 0, 1] [1, 2, 2, 0, 0, 2, 0] 3 1 true = ([1, 2, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_2012001 : fieldCube 7 5 20 [1, 2, 1, 0, 2, 1, 0] = [2, 0, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_2012001 : fieldMul 7 5 20 [2, 0, 1, 1, 1, 0, 2] [2, 0, 1, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012001 : mirrorTrits [2, 0, 1, 1, 1, 0, 2] = [1, 0, 2, 2, 2, 0, 1] := by
  decide

theorem demoInv_2012001 : specInv 7 5 20 [2, 0, 1, 2, 0, 0, 1] = some [1, 0, 2, 2, 2, 0, 1] :=
  specInv_mirror_7 [2, 0, 1, 2, 0, 0, 1] [1, 2, 2, 0, 0, 2, 0] [1, 2, 1, 0, 2, 1, 0] [2, 0, 1, 1, 1, 0, 2] [1, 0, 2, 2, 2, 0, 1] demoR1_2012001 demoR2_2012001 demoC_2012001 demoM_2012001 demoMir_2012001

theorem demoR1_0112001 : invRung 7 5 20 [0, 1, 1, 2, 0, 0, 1] [0, 1, 1, 2, 0, 0, 1] 1 2 false = ([1, 2, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_0112001 : invRung 7 5 20 [0, 1, 1, 2, 0, 0, 1] [1, 2, 1, 1, 1, 2, 1] 3 1 true = ([1, 0, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_0112001 : fieldCube 7 5 20 [1, 0, 2, 1, 2, 2, 1] = [1, 2, 2, 0, 0, 0, 0] := by
  decide

theorem demoM_0112001 : fieldMul 7 5 20 [1, 2, 2, 0, 0, 0, 0] [0, 1, 1, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112001 : mirrorTrits [1, 2, 2, 0, 0, 0, 0] = [2, 1, 1, 0, 0, 0, 0] := by
  decide

theorem demoInv_0112001 : specInv 7 5 20 [0, 1, 1, 2, 0, 0, 1] = some [2, 1, 1, 0, 0, 0, 0] :=
  specInv_mirror_7 [0, 1, 1, 2, 0, 0, 1] [1, 2, 1, 1, 1, 2, 1] [1, 0, 2, 1, 2, 2, 1] [1, 2, 2, 0, 0, 0, 0] [2, 1, 1, 0, 0, 0, 0] demoR1_0112001 demoR2_0112001 demoC_0112001 demoM_0112001 demoMir_0112001

theorem demoR1_1112001 : invRung 7 5 20 [1, 1, 1, 2, 0, 0, 1] [1, 1, 1, 2, 0, 0, 1] 1 2 false = ([0, 0, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_1112001 : invRung 7 5 20 [1, 1, 1, 2, 0, 0, 1] [0, 0, 2, 1, 1, 2, 0] 3 1 true = ([2, 2, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_1112001 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 2, 0] = [2, 0, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_1112001 : fieldMul 7 5 20 [2, 0, 0, 0, 2, 1, 0] [1, 1, 1, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112001 : mirrorTrits [2, 0, 0, 0, 2, 1, 0] = [1, 0, 0, 0, 1, 2, 0] := by
  decide

theorem demoInv_1112001 : specInv 7 5 20 [1, 1, 1, 2, 0, 0, 1] = some [1, 0, 0, 0, 1, 2, 0] :=
  specInv_mirror_7 [1, 1, 1, 2, 0, 0, 1] [0, 0, 2, 1, 1, 2, 0] [2, 2, 1, 1, 1, 2, 0] [2, 0, 0, 0, 2, 1, 0] [1, 0, 0, 0, 1, 2, 0] demoR1_1112001 demoR2_1112001 demoC_1112001 demoM_1112001 demoMir_1112001

theorem demoR1_2112001 : invRung 7 5 20 [2, 1, 1, 2, 0, 0, 1] [2, 1, 1, 2, 0, 0, 1] 1 2 false = ([2, 2, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_2112001 : invRung 7 5 20 [2, 1, 1, 2, 0, 0, 1] [2, 2, 1, 2, 1, 0, 1] 3 1 true = ([1, 0, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_2112001 : fieldCube 7 5 20 [1, 0, 0, 2, 0, 0, 1] = [0, 1, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_2112001 : fieldMul 7 5 20 [0, 1, 1, 1, 1, 0, 1] [2, 1, 1, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2112001 : specInv 7 5 20 [2, 1, 1, 2, 0, 0, 1] = some [0, 1, 1, 1, 1, 0, 1] :=
  specInv_white_7 [2, 1, 1, 2, 0, 0, 1] [2, 2, 1, 2, 1, 0, 1] [1, 0, 0, 2, 0, 0, 1] [0, 1, 1, 1, 1, 0, 1] demoR1_2112001 demoR2_2112001 demoC_2112001 demoM_2112001

theorem demoR1_0212001 : invRung 7 5 20 [0, 2, 1, 2, 0, 0, 1] [0, 2, 1, 2, 0, 0, 1] 1 2 false = ([1, 0, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_0212001 : invRung 7 5 20 [0, 2, 1, 2, 0, 0, 1] [1, 0, 1, 2, 0, 0, 2] 3 1 true = ([0, 0, 1, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_0212001 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 2, 0] = [2, 1, 2, 2, 2, 1, 1] := by
  decide

theorem demoM_0212001 : fieldMul 7 5 20 [2, 1, 2, 2, 2, 1, 1] [0, 2, 1, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0212001 : specInv 7 5 20 [0, 2, 1, 2, 0, 0, 1] = some [2, 1, 2, 2, 2, 1, 1] :=
  specInv_white_7 [0, 2, 1, 2, 0, 0, 1] [1, 0, 1, 2, 0, 0, 2] [0, 0, 1, 0, 2, 2, 0] [2, 1, 2, 2, 2, 1, 1] demoR1_0212001 demoR2_0212001 demoC_0212001 demoM_0212001

theorem demoR1_1212001 : invRung 7 5 20 [1, 2, 1, 2, 0, 0, 1] [1, 2, 1, 2, 0, 0, 1] 1 2 false = ([1, 0, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_1212001 : invRung 7 5 20 [1, 2, 1, 2, 0, 0, 1] [1, 0, 2, 1, 2, 1, 2] 3 1 true = ([1, 2, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_1212001 : fieldCube 7 5 20 [1, 2, 1, 1, 0, 1, 2] = [0, 0, 0, 1, 0, 1, 2] := by
  decide

theorem demoM_1212001 : fieldMul 7 5 20 [0, 0, 0, 1, 0, 1, 2] [1, 2, 1, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212001 : mirrorTrits [0, 0, 0, 1, 0, 1, 2] = [0, 0, 0, 2, 0, 2, 1] := by
  decide

theorem demoInv_1212001 : specInv 7 5 20 [1, 2, 1, 2, 0, 0, 1] = some [0, 0, 0, 2, 0, 2, 1] :=
  specInv_mirror_7 [1, 2, 1, 2, 0, 0, 1] [1, 0, 2, 1, 2, 1, 2] [1, 2, 1, 1, 0, 1, 2] [0, 0, 0, 1, 0, 1, 2] [0, 0, 0, 2, 0, 2, 1] demoR1_1212001 demoR2_1212001 demoC_1212001 demoM_1212001 demoMir_1212001

theorem demoR1_2212001 : invRung 7 5 20 [2, 2, 1, 2, 0, 0, 1] [2, 2, 1, 2, 0, 0, 1] 1 2 false = ([0, 0, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_2212001 : invRung 7 5 20 [2, 2, 1, 2, 0, 0, 1] [0, 0, 0, 0, 1, 2, 1] 3 1 true = ([1, 2, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoC_2212001 : fieldCube 7 5 20 [1, 2, 2, 0, 1, 0, 2] = [1, 0, 1, 2, 2, 0, 2] := by
  decide

theorem demoM_2212001 : fieldMul 7 5 20 [1, 0, 1, 2, 2, 0, 2] [2, 2, 1, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2212001 : specInv 7 5 20 [2, 2, 1, 2, 0, 0, 1] = some [1, 0, 1, 2, 2, 0, 2] :=
  specInv_white_7 [2, 2, 1, 2, 0, 0, 1] [0, 0, 0, 0, 1, 2, 1] [1, 2, 2, 0, 1, 0, 2] [1, 0, 1, 2, 2, 0, 2] demoR1_2212001 demoR2_2212001 demoC_2212001 demoM_2212001

theorem demoR1_0022001 : invRung 7 5 20 [0, 0, 2, 2, 0, 0, 1] [0, 0, 2, 2, 0, 0, 1] 1 2 false = ([0, 2, 1, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_0022001 : invRung 7 5 20 [0, 0, 2, 2, 0, 0, 1] [0, 2, 1, 1, 0, 0, 0] 3 1 true = ([1, 0, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_0022001 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 2, 2] = [0, 1, 0, 2, 1, 1, 0] := by
  decide

theorem demoM_0022001 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 1, 0] [0, 0, 2, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022001 : mirrorTrits [0, 1, 0, 2, 1, 1, 0] = [0, 2, 0, 1, 2, 2, 0] := by
  decide

theorem demoInv_0022001 : specInv 7 5 20 [0, 0, 2, 2, 0, 0, 1] = some [0, 2, 0, 1, 2, 2, 0] :=
  specInv_mirror_7 [0, 0, 2, 2, 0, 0, 1] [0, 2, 1, 1, 0, 0, 0] [1, 0, 0, 0, 0, 2, 2] [0, 1, 0, 2, 1, 1, 0] [0, 2, 0, 1, 2, 2, 0] demoR1_0022001 demoR2_0022001 demoC_0022001 demoM_0022001 demoMir_0022001

theorem demoR1_1022001 : invRung 7 5 20 [1, 0, 2, 2, 0, 0, 1] [1, 0, 2, 2, 0, 0, 1] 1 2 false = ([0, 1, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_1022001 : invRung 7 5 20 [1, 0, 2, 2, 0, 0, 1] [0, 1, 1, 1, 0, 1, 2] 3 1 true = ([1, 1, 0, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_1022001 : fieldCube 7 5 20 [1, 1, 0, 0, 0, 0, 0] = [1, 0, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_1022001 : fieldMul 7 5 20 [1, 0, 0, 1, 0, 0, 0] [1, 0, 2, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1022001 : mirrorTrits [1, 0, 0, 1, 0, 0, 0] = [2, 0, 0, 2, 0, 0, 0] := by
  decide

theorem demoInv_1022001 : specInv 7 5 20 [1, 0, 2, 2, 0, 0, 1] = some [2, 0, 0, 2, 0, 0, 0] :=
  specInv_mirror_7 [1, 0, 2, 2, 0, 0, 1] [0, 1, 1, 1, 0, 1, 2] [1, 1, 0, 0, 0, 0, 0] [1, 0, 0, 1, 0, 0, 0] [2, 0, 0, 2, 0, 0, 0] demoR1_1022001 demoR2_1022001 demoC_1022001 demoM_1022001 demoMir_1022001

theorem demoR1_2022001 : invRung 7 5 20 [2, 0, 2, 2, 0, 0, 1] [2, 0, 2, 2, 0, 0, 1] 1 2 false = ([1, 1, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2022001 : invRung 7 5 20 [2, 0, 2, 2, 0, 0, 1] [1, 1, 0, 2, 2, 0, 1] 3 1 true = ([1, 0, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_2022001 : fieldCube 7 5 20 [1, 0, 0, 0, 2, 0, 1] = [1, 0, 2, 0, 1, 0, 0] := by
  decide

theorem demoM_2022001 : fieldMul 7 5 20 [1, 0, 2, 0, 1, 0, 0] [2, 0, 2, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2022001 : specInv 7 5 20 [2, 0, 2, 2, 0, 0, 1] = some [1, 0, 2, 0, 1, 0, 0] :=
  specInv_white_7 [2, 0, 2, 2, 0, 0, 1] [1, 1, 0, 2, 2, 0, 1] [1, 0, 0, 0, 2, 0, 1] [1, 0, 2, 0, 1, 0, 0] demoR1_2022001 demoR2_2022001 demoC_2022001 demoM_2022001

theorem demoR1_0122001 : invRung 7 5 20 [0, 1, 2, 2, 0, 0, 1] [0, 1, 2, 2, 0, 0, 1] 1 2 false = ([2, 0, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_0122001 : invRung 7 5 20 [0, 1, 2, 2, 0, 0, 1] [2, 0, 0, 2, 0, 2, 0] 3 1 true = ([1, 2, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0122001 : fieldCube 7 5 20 [1, 2, 0, 0, 1, 2, 1] = [0, 1, 1, 1, 0, 1, 0] := by
  decide

theorem demoM_0122001 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 1, 0] [0, 1, 2, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122001 : mirrorTrits [0, 1, 1, 1, 0, 1, 0] = [0, 2, 2, 2, 0, 2, 0] := by
  decide

theorem demoInv_0122001 : specInv 7 5 20 [0, 1, 2, 2, 0, 0, 1] = some [0, 2, 2, 2, 0, 2, 0] :=
  specInv_mirror_7 [0, 1, 2, 2, 0, 0, 1] [2, 0, 0, 2, 0, 2, 0] [1, 2, 0, 0, 1, 2, 1] [0, 1, 1, 1, 0, 1, 0] [0, 2, 2, 2, 0, 2, 0] demoR1_0122001 demoR2_0122001 demoC_0122001 demoM_0122001 demoMir_0122001

theorem demoR1_1122001 : invRung 7 5 20 [1, 1, 2, 2, 0, 0, 1] [1, 1, 2, 2, 0, 0, 1] 1 2 false = ([0, 2, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_1122001 : invRung 7 5 20 [1, 1, 2, 2, 0, 0, 1] [0, 2, 1, 2, 1, 0, 1] 3 1 true = ([1, 1, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_1122001 : fieldCube 7 5 20 [1, 1, 0, 2, 2, 2, 0] = [2, 1, 1, 0, 2, 0, 0] := by
  decide

theorem demoM_1122001 : fieldMul 7 5 20 [2, 1, 1, 0, 2, 0, 0] [1, 1, 2, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1122001 : specInv 7 5 20 [1, 1, 2, 2, 0, 0, 1] = some [2, 1, 1, 0, 2, 0, 0] :=
  specInv_white_7 [1, 1, 2, 2, 0, 0, 1] [0, 2, 1, 2, 1, 0, 1] [1, 1, 0, 2, 2, 2, 0] [2, 1, 1, 0, 2, 0, 0] demoR1_1122001 demoR2_1122001 demoC_1122001 demoM_1122001

theorem demoR1_2122001 : invRung 7 5 20 [2, 1, 2, 2, 0, 0, 1] [2, 1, 2, 2, 0, 0, 1] 1 2 false = ([1, 1, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2122001 : invRung 7 5 20 [2, 1, 2, 2, 0, 0, 1] [1, 1, 0, 2, 1, 1, 2] 3 1 true = ([1, 2, 1, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_2122001 : fieldCube 7 5 20 [1, 2, 1, 1, 0, 1, 0] = [0, 1, 2, 2, 1, 2, 0] := by
  decide

theorem demoM_2122001 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 2, 0] [2, 1, 2, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122001 : mirrorTrits [0, 1, 2, 2, 1, 2, 0] = [0, 2, 1, 1, 2, 1, 0] := by
  decide

theorem demoInv_2122001 : specInv 7 5 20 [2, 1, 2, 2, 0, 0, 1] = some [0, 2, 1, 1, 2, 1, 0] :=
  specInv_mirror_7 [2, 1, 2, 2, 0, 0, 1] [1, 1, 0, 2, 1, 1, 2] [1, 2, 1, 1, 0, 1, 0] [0, 1, 2, 2, 1, 2, 0] [0, 2, 1, 1, 2, 1, 0] demoR1_2122001 demoR2_2122001 demoC_2122001 demoM_2122001 demoMir_2122001

theorem demoR1_0222001 : invRung 7 5 20 [0, 2, 2, 2, 0, 0, 1] [0, 2, 2, 2, 0, 0, 1] 1 2 false = ([2, 2, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_0222001 : invRung 7 5 20 [0, 2, 2, 2, 0, 0, 1] [2, 2, 0, 0, 1, 2, 0] 3 1 true = ([0, 2, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0222001 : fieldCube 7 5 20 [0, 2, 2, 2, 0, 1, 1] = [0, 2, 2, 0, 2, 1, 2] := by
  decide

theorem demoM_0222001 : fieldMul 7 5 20 [0, 2, 2, 0, 2, 1, 2] [0, 2, 2, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0222001 : mirrorTrits [0, 2, 2, 0, 2, 1, 2] = [0, 1, 1, 0, 1, 2, 1] := by
  decide

theorem demoInv_0222001 : specInv 7 5 20 [0, 2, 2, 2, 0, 0, 1] = some [0, 1, 1, 0, 1, 2, 1] :=
  specInv_mirror_7 [0, 2, 2, 2, 0, 0, 1] [2, 2, 0, 0, 1, 2, 0] [0, 2, 2, 2, 0, 1, 1] [0, 2, 2, 0, 2, 1, 2] [0, 1, 1, 0, 1, 2, 1] demoR1_0222001 demoR2_0222001 demoC_0222001 demoM_0222001 demoMir_0222001

theorem demoR1_1222001 : invRung 7 5 20 [1, 2, 2, 2, 0, 0, 1] [1, 2, 2, 2, 0, 0, 1] 1 2 false = ([1, 2, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1222001 : invRung 7 5 20 [1, 2, 2, 2, 0, 0, 1] [1, 2, 2, 1, 2, 2, 1] 3 1 true = ([1, 1, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_1222001 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 2, 2] = [1, 2, 1, 1, 1, 0, 2] := by
  decide

theorem demoM_1222001 : fieldMul 7 5 20 [1, 2, 1, 1, 1, 0, 2] [1, 2, 2, 2, 0, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222001 : mirrorTrits [1, 2, 1, 1, 1, 0, 2] = [2, 1, 2, 2, 2, 0, 1] := by
  decide

theorem demoInv_1222001 : specInv 7 5 20 [1, 2, 2, 2, 0, 0, 1] = some [2, 1, 2, 2, 2, 0, 1] :=
  specInv_mirror_7 [1, 2, 2, 2, 0, 0, 1] [1, 2, 2, 1, 2, 2, 1] [1, 1, 1, 1, 1, 2, 2] [1, 2, 1, 1, 1, 0, 2] [2, 1, 2, 2, 2, 0, 1] demoR1_1222001 demoR2_1222001 demoC_1222001 demoM_1222001 demoMir_1222001

theorem demoR1_2222001 : invRung 7 5 20 [2, 2, 2, 2, 0, 0, 1] [2, 2, 2, 2, 0, 0, 1] 1 2 false = ([2, 1, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_2222001 : invRung 7 5 20 [2, 2, 2, 2, 0, 0, 1] [2, 1, 1, 1, 2, 1, 2] 3 1 true = ([0, 1, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_2222001 : fieldCube 7 5 20 [0, 1, 0, 2, 1, 2, 0] = [1, 0, 1, 2, 2, 2, 2] := by
  decide

theorem demoM_2222001 : fieldMul 7 5 20 [1, 0, 1, 2, 2, 2, 2] [2, 2, 2, 2, 0, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2222001 : specInv 7 5 20 [2, 2, 2, 2, 0, 0, 1] = some [1, 0, 1, 2, 2, 2, 2] :=
  specInv_white_7 [2, 2, 2, 2, 0, 0, 1] [2, 1, 1, 1, 2, 1, 2] [0, 1, 0, 2, 1, 2, 0] [1, 0, 1, 2, 2, 2, 2] demoR1_2222001 demoR2_2222001 demoC_2222001 demoM_2222001

theorem demoR1_0000101 : invRung 7 5 20 [0, 0, 0, 0, 1, 0, 1] [0, 0, 0, 0, 1, 0, 1] 1 2 false = ([2, 2, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_0000101 : invRung 7 5 20 [0, 0, 0, 0, 1, 0, 1] [2, 2, 1, 2, 0, 2, 1] 3 1 true = ([0, 1, 2, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_0000101 : fieldCube 7 5 20 [0, 1, 2, 2, 2, 2, 2] = [1, 0, 2, 2, 1, 2, 1] := by
  decide

theorem demoM_0000101 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 2, 1] [0, 0, 0, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0000101 : mirrorTrits [1, 0, 2, 2, 1, 2, 1] = [2, 0, 1, 1, 2, 1, 2] := by
  decide

theorem demoInv_0000101 : specInv 7 5 20 [0, 0, 0, 0, 1, 0, 1] = some [2, 0, 1, 1, 2, 1, 2] :=
  specInv_mirror_7 [0, 0, 0, 0, 1, 0, 1] [2, 2, 1, 2, 0, 2, 1] [0, 1, 2, 2, 2, 2, 2] [1, 0, 2, 2, 1, 2, 1] [2, 0, 1, 1, 2, 1, 2] demoR1_0000101 demoR2_0000101 demoC_0000101 demoM_0000101 demoMir_0000101

theorem demoR1_1000101 : invRung 7 5 20 [1, 0, 0, 0, 1, 0, 1] [1, 0, 0, 0, 1, 0, 1] 1 2 false = ([0, 2, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_1000101 : invRung 7 5 20 [1, 0, 0, 0, 1, 0, 1] [0, 2, 0, 2, 1, 0, 1] 3 1 true = ([2, 1, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1000101 : fieldCube 7 5 20 [2, 1, 0, 1, 0, 2, 1] = [2, 0, 2, 2, 0, 1, 2] := by
  decide

theorem demoM_1000101 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 1, 2] [1, 0, 0, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000101 : mirrorTrits [2, 0, 2, 2, 0, 1, 2] = [1, 0, 1, 1, 0, 2, 1] := by
  decide

theorem demoInv_1000101 : specInv 7 5 20 [1, 0, 0, 0, 1, 0, 1] = some [1, 0, 1, 1, 0, 2, 1] :=
  specInv_mirror_7 [1, 0, 0, 0, 1, 0, 1] [0, 2, 0, 2, 1, 0, 1] [2, 1, 0, 1, 0, 2, 1] [2, 0, 2, 2, 0, 1, 2] [1, 0, 1, 1, 0, 2, 1] demoR1_1000101 demoR2_1000101 demoC_1000101 demoM_1000101 demoMir_1000101

theorem demoR1_2000101 : invRung 7 5 20 [2, 0, 0, 0, 1, 0, 1] [2, 0, 0, 0, 1, 0, 1] 1 2 false = ([0, 1, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_2000101 : invRung 7 5 20 [2, 0, 0, 0, 1, 0, 1] [0, 1, 1, 1, 2, 1, 1] 3 1 true = ([2, 2, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2000101 : fieldCube 7 5 20 [2, 2, 0, 0, 0, 1, 0] = [0, 1, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_2000101 : fieldMul 7 5 20 [0, 1, 1, 2, 1, 1, 2] [2, 0, 0, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2000101 : specInv 7 5 20 [2, 0, 0, 0, 1, 0, 1] = some [0, 1, 1, 2, 1, 1, 2] :=
  specInv_white_7 [2, 0, 0, 0, 1, 0, 1] [0, 1, 1, 1, 2, 1, 1] [2, 2, 0, 0, 0, 1, 0] [0, 1, 1, 2, 1, 1, 2] demoR1_2000101 demoR2_2000101 demoC_2000101 demoM_2000101

theorem demoR1_0100101 : invRung 7 5 20 [0, 1, 0, 0, 1, 0, 1] [0, 1, 0, 0, 1, 0, 1] 1 2 false = ([2, 1, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_0100101 : invRung 7 5 20 [0, 1, 0, 0, 1, 0, 1] [2, 1, 0, 2, 0, 1, 1] 3 1 true = ([2, 1, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0100101 : fieldCube 7 5 20 [2, 1, 1, 2, 2, 0, 2] = [1, 1, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_0100101 : fieldMul 7 5 20 [1, 1, 0, 2, 2, 0, 2] [0, 1, 0, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0100101 : specInv 7 5 20 [0, 1, 0, 0, 1, 0, 1] = some [1, 1, 0, 2, 2, 0, 2] :=
  specInv_white_7 [0, 1, 0, 0, 1, 0, 1] [2, 1, 0, 2, 0, 1, 1] [2, 1, 1, 2, 2, 0, 2] [1, 1, 0, 2, 2, 0, 2] demoR1_0100101 demoR2_0100101 demoC_0100101 demoM_0100101

theorem demoR1_1100101 : invRung 7 5 20 [1, 1, 0, 0, 1, 0, 1] [1, 1, 0, 0, 1, 0, 1] 1 2 false = ([0, 0, 0, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_1100101 : invRung 7 5 20 [1, 1, 0, 0, 1, 0, 1] [0, 0, 0, 1, 0, 2, 2] 3 1 true = ([2, 0, 2, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_1100101 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 0, 2] = [1, 2, 0, 2, 2, 1, 1] := by
  decide

theorem demoM_1100101 : fieldMul 7 5 20 [1, 2, 0, 2, 2, 1, 1] [1, 1, 0, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1100101 : specInv 7 5 20 [1, 1, 0, 0, 1, 0, 1] = some [1, 2, 0, 2, 2, 1, 1] :=
  specInv_white_7 [1, 1, 0, 0, 1, 0, 1] [0, 0, 0, 1, 0, 2, 2] [2, 0, 2, 2, 0, 0, 2] [1, 2, 0, 2, 2, 1, 1] demoR1_1100101 demoR2_1100101 demoC_1100101 demoM_1100101

theorem demoR1_2100101 : invRung 7 5 20 [2, 1, 0, 0, 1, 0, 1] [2, 1, 0, 0, 1, 0, 1] 1 2 false = ([2, 0, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_2100101 : invRung 7 5 20 [2, 1, 0, 0, 1, 0, 1] [2, 0, 1, 1, 0, 2, 0] 3 1 true = ([1, 1, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_2100101 : fieldCube 7 5 20 [1, 1, 1, 2, 2, 1, 1] = [1, 1, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_2100101 : fieldMul 7 5 20 [1, 1, 2, 1, 2, 0, 0] [2, 1, 0, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100101 : mirrorTrits [1, 1, 2, 1, 2, 0, 0] = [2, 2, 1, 2, 1, 0, 0] := by
  decide

theorem demoInv_2100101 : specInv 7 5 20 [2, 1, 0, 0, 1, 0, 1] = some [2, 2, 1, 2, 1, 0, 0] :=
  specInv_mirror_7 [2, 1, 0, 0, 1, 0, 1] [2, 0, 1, 1, 0, 2, 0] [1, 1, 1, 2, 2, 1, 1] [1, 1, 2, 1, 2, 0, 0] [2, 2, 1, 2, 1, 0, 0] demoR1_2100101 demoR2_2100101 demoC_2100101 demoM_2100101 demoMir_2100101

theorem demoR1_0200101 : invRung 7 5 20 [0, 2, 0, 0, 1, 0, 1] [0, 2, 0, 0, 1, 0, 1] 1 2 false = ([1, 2, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_0200101 : invRung 7 5 20 [0, 2, 0, 0, 1, 0, 1] [1, 2, 2, 1, 1, 2, 0] 3 1 true = ([0, 0, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_0200101 : fieldCube 7 5 20 [0, 0, 2, 2, 1, 1, 1] = [0, 0, 2, 2, 2, 2, 0] := by
  decide

theorem demoM_0200101 : fieldMul 7 5 20 [0, 0, 2, 2, 2, 2, 0] [0, 2, 0, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200101 : mirrorTrits [0, 0, 2, 2, 2, 2, 0] = [0, 0, 1, 1, 1, 1, 0] := by
  decide

theorem demoInv_0200101 : specInv 7 5 20 [0, 2, 0, 0, 1, 0, 1] = some [0, 0, 1, 1, 1, 1, 0] :=
  specInv_mirror_7 [0, 2, 0, 0, 1, 0, 1] [1, 2, 2, 1, 1, 2, 0] [0, 0, 2, 2, 1, 1, 1] [0, 0, 2, 2, 2, 2, 0] [0, 0, 1, 1, 1, 1, 0] demoR1_0200101 demoR2_0200101 demoC_0200101 demoM_0200101 demoMir_0200101

theorem demoR1_1200101 : invRung 7 5 20 [1, 2, 0, 0, 1, 0, 1] [1, 2, 0, 0, 1, 0, 1] 1 2 false = ([2, 1, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_1200101 : invRung 7 5 20 [1, 2, 0, 0, 1, 0, 1] [2, 1, 0, 0, 2, 2, 0] 3 1 true = ([2, 0, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_1200101 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 0, 0] = [1, 0, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_1200101 : fieldMul 7 5 20 [1, 0, 2, 0, 0, 2, 1] [1, 2, 0, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1200101 : specInv 7 5 20 [1, 2, 0, 0, 1, 0, 1] = some [1, 0, 2, 0, 0, 2, 1] :=
  specInv_white_7 [1, 2, 0, 0, 1, 0, 1] [2, 1, 0, 0, 2, 2, 0] [2, 0, 1, 2, 0, 0, 0] [1, 0, 2, 0, 0, 2, 1] demoR1_1200101 demoR2_1200101 demoC_1200101 demoM_1200101

theorem demoR1_2200101 : invRung 7 5 20 [2, 2, 0, 0, 1, 0, 1] [2, 2, 0, 0, 1, 0, 1] 1 2 false = ([0, 0, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_2200101 : invRung 7 5 20 [2, 2, 0, 0, 1, 0, 1] [0, 0, 1, 2, 0, 0, 0] 3 1 true = ([2, 0, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_2200101 : fieldCube 7 5 20 [2, 0, 0, 2, 2, 0, 0] = [1, 2, 2, 2, 0, 1, 2] := by
  decide

theorem demoM_2200101 : fieldMul 7 5 20 [1, 2, 2, 2, 0, 1, 2] [2, 2, 0, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2200101 : mirrorTrits [1, 2, 2, 2, 0, 1, 2] = [2, 1, 1, 1, 0, 2, 1] := by
  decide

theorem demoInv_2200101 : specInv 7 5 20 [2, 2, 0, 0, 1, 0, 1] = some [2, 1, 1, 1, 0, 2, 1] :=
  specInv_mirror_7 [2, 2, 0, 0, 1, 0, 1] [0, 0, 1, 2, 0, 0, 0] [2, 0, 0, 2, 2, 0, 0] [1, 2, 2, 2, 0, 1, 2] [2, 1, 1, 1, 0, 2, 1] demoR1_2200101 demoR2_2200101 demoC_2200101 demoM_2200101 demoMir_2200101

theorem demoR1_0010101 : invRung 7 5 20 [0, 0, 1, 0, 1, 0, 1] [0, 0, 1, 0, 1, 0, 1] 1 2 false = ([0, 1, 1, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_0010101 : invRung 7 5 20 [0, 0, 1, 0, 1, 0, 1] [0, 1, 1, 1, 1, 1, 1] 3 1 true = ([2, 1, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0010101 : fieldCube 7 5 20 [2, 1, 1, 2, 1, 2, 1] = [0, 1, 0, 0, 0, 0, 1] := by
  decide

theorem demoM_0010101 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 0, 1] [0, 0, 1, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0010101 : specInv 7 5 20 [0, 0, 1, 0, 1, 0, 1] = some [0, 1, 0, 0, 0, 0, 1] :=
  specInv_white_7 [0, 0, 1, 0, 1, 0, 1] [0, 1, 1, 1, 1, 1, 1] [2, 1, 1, 2, 1, 2, 1] [0, 1, 0, 0, 0, 0, 1] demoR1_0010101 demoR2_0010101 demoC_0010101 demoM_0010101

theorem demoR1_1010101 : invRung 7 5 20 [1, 0, 1, 0, 1, 0, 1] [1, 0, 1, 0, 1, 0, 1] 1 2 false = ([0, 0, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_1010101 : invRung 7 5 20 [1, 0, 1, 0, 1, 0, 1] [0, 0, 1, 1, 0, 1, 2] 3 1 true = ([2, 2, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_1010101 : fieldCube 7 5 20 [2, 2, 0, 2, 1, 0, 0] = [1, 1, 2, 0, 0, 0, 1] := by
  decide

theorem demoM_1010101 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 0, 1] [1, 0, 1, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1010101 : mirrorTrits [1, 1, 2, 0, 0, 0, 1] = [2, 2, 1, 0, 0, 0, 2] := by
  decide

theorem demoInv_1010101 : specInv 7 5 20 [1, 0, 1, 0, 1, 0, 1] = some [2, 2, 1, 0, 0, 0, 2] :=
  specInv_mirror_7 [1, 0, 1, 0, 1, 0, 1] [0, 0, 1, 1, 0, 1, 2] [2, 2, 0, 2, 1, 0, 0] [1, 1, 2, 0, 0, 0, 1] [2, 2, 1, 0, 0, 0, 2] demoR1_1010101 demoR2_1010101 demoC_1010101 demoM_1010101 demoMir_1010101

theorem demoR1_2010101 : invRung 7 5 20 [2, 0, 1, 0, 1, 0, 1] [2, 0, 1, 0, 1, 0, 1] 1 2 false = ([2, 0, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoR2_2010101 : invRung 7 5 20 [2, 0, 1, 0, 1, 0, 1] [2, 0, 0, 2, 1, 0, 1] 3 1 true = ([2, 2, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_2010101 : fieldCube 7 5 20 [2, 2, 2, 1, 2, 2, 2] = [2, 0, 1, 0, 1, 1, 1] := by
  decide

theorem demoM_2010101 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 1, 1] [2, 0, 1, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2010101 : specInv 7 5 20 [2, 0, 1, 0, 1, 0, 1] = some [2, 0, 1, 0, 1, 1, 1] :=
  specInv_white_7 [2, 0, 1, 0, 1, 0, 1] [2, 0, 0, 2, 1, 0, 1] [2, 2, 2, 1, 2, 2, 2] [2, 0, 1, 0, 1, 1, 1] demoR1_2010101 demoR2_2010101 demoC_2010101 demoM_2010101

theorem demoR1_0110101 : invRung 7 5 20 [0, 1, 1, 0, 1, 0, 1] [0, 1, 1, 0, 1, 0, 1] 1 2 false = ([0, 2, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_0110101 : invRung 7 5 20 [0, 1, 1, 0, 1, 0, 1] [0, 2, 0, 1, 2, 0, 1] 3 1 true = ([0, 2, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_0110101 : fieldCube 7 5 20 [0, 2, 1, 2, 2, 2, 0] = [1, 1, 1, 1, 2, 0, 1] := by
  decide

theorem demoM_0110101 : fieldMul 7 5 20 [1, 1, 1, 1, 2, 0, 1] [0, 1, 1, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0110101 : specInv 7 5 20 [0, 1, 1, 0, 1, 0, 1] = some [1, 1, 1, 1, 2, 0, 1] :=
  specInv_white_7 [0, 1, 1, 0, 1, 0, 1] [0, 2, 0, 1, 2, 0, 1] [0, 2, 1, 2, 2, 2, 0] [1, 1, 1, 1, 2, 0, 1] demoR1_0110101 demoR2_0110101 demoC_0110101 demoM_0110101

theorem demoR1_1110101 : invRung 7 5 20 [1, 1, 1, 0, 1, 0, 1] [1, 1, 1, 0, 1, 0, 1] 1 2 false = ([0, 2, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_1110101 : invRung 7 5 20 [1, 1, 1, 0, 1, 0, 1] [0, 2, 2, 2, 1, 1, 2] 3 1 true = ([0, 2, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_1110101 : fieldCube 7 5 20 [0, 2, 0, 2, 2, 0, 0] = [2, 2, 2, 1, 0, 1, 2] := by
  decide

theorem demoM_1110101 : fieldMul 7 5 20 [2, 2, 2, 1, 0, 1, 2] [1, 1, 1, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1110101 : mirrorTrits [2, 2, 2, 1, 0, 1, 2] = [1, 1, 1, 2, 0, 2, 1] := by
  decide

theorem demoInv_1110101 : specInv 7 5 20 [1, 1, 1, 0, 1, 0, 1] = some [1, 1, 1, 2, 0, 2, 1] :=
  specInv_mirror_7 [1, 1, 1, 0, 1, 0, 1] [0, 2, 2, 2, 1, 1, 2] [0, 2, 0, 2, 2, 0, 0] [2, 2, 2, 1, 0, 1, 2] [1, 1, 1, 2, 0, 2, 1] demoR1_1110101 demoR2_1110101 demoC_1110101 demoM_1110101 demoMir_1110101

theorem demoR1_2110101 : invRung 7 5 20 [2, 1, 1, 0, 1, 0, 1] [2, 1, 1, 0, 1, 0, 1] 1 2 false = ([1, 2, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_2110101 : invRung 7 5 20 [2, 1, 1, 0, 1, 0, 1] [1, 2, 2, 0, 2, 0, 1] 3 1 true = ([0, 2, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_2110101 : fieldCube 7 5 20 [0, 2, 2, 2, 1, 1, 1] = [0, 0, 2, 1, 2, 2, 0] := by
  decide

theorem demoM_2110101 : fieldMul 7 5 20 [0, 0, 2, 1, 2, 2, 0] [2, 1, 1, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110101 : mirrorTrits [0, 0, 2, 1, 2, 2, 0] = [0, 0, 1, 2, 1, 1, 0] := by
  decide

theorem demoInv_2110101 : specInv 7 5 20 [2, 1, 1, 0, 1, 0, 1] = some [0, 0, 1, 2, 1, 1, 0] :=
  specInv_mirror_7 [2, 1, 1, 0, 1, 0, 1] [1, 2, 2, 0, 2, 0, 1] [0, 2, 2, 2, 1, 1, 1] [0, 0, 2, 1, 2, 2, 0] [0, 0, 1, 2, 1, 1, 0] demoR1_2110101 demoR2_2110101 demoC_2110101 demoM_2110101 demoMir_2110101

theorem demoR1_0210101 : invRung 7 5 20 [0, 2, 1, 0, 1, 0, 1] [0, 2, 1, 0, 1, 0, 1] 1 2 false = ([0, 1, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_0210101 : invRung 7 5 20 [0, 2, 1, 0, 1, 0, 1] [0, 1, 0, 0, 1, 2, 0] 3 1 true = ([2, 1, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0210101 : fieldCube 7 5 20 [2, 1, 0, 0, 0, 2, 1] = [1, 0, 1, 2, 0, 0, 2] := by
  decide

theorem demoM_0210101 : fieldMul 7 5 20 [1, 0, 1, 2, 0, 0, 2] [0, 2, 1, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210101 : mirrorTrits [1, 0, 1, 2, 0, 0, 2] = [2, 0, 2, 1, 0, 0, 1] := by
  decide

theorem demoInv_0210101 : specInv 7 5 20 [0, 2, 1, 0, 1, 0, 1] = some [2, 0, 2, 1, 0, 0, 1] :=
  specInv_mirror_7 [0, 2, 1, 0, 1, 0, 1] [0, 1, 0, 0, 1, 2, 0] [2, 1, 0, 0, 0, 2, 1] [1, 0, 1, 2, 0, 0, 2] [2, 0, 2, 1, 0, 0, 1] demoR1_0210101 demoR2_0210101 demoC_0210101 demoM_0210101 demoMir_0210101

theorem demoR1_1210101 : invRung 7 5 20 [1, 2, 1, 0, 1, 0, 1] [1, 2, 1, 0, 1, 0, 1] 1 2 false = ([0, 0, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_1210101 : invRung 7 5 20 [1, 2, 1, 0, 1, 0, 1] [0, 0, 1, 0, 2, 0, 2] 3 1 true = ([2, 2, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_1210101 : fieldCube 7 5 20 [2, 2, 1, 1, 0, 0, 1] = [0, 1, 0, 0, 1, 2, 2] := by
  decide

theorem demoM_1210101 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 2, 2] [1, 2, 1, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1210101 : mirrorTrits [0, 1, 0, 0, 1, 2, 2] = [0, 2, 0, 0, 2, 1, 1] := by
  decide

theorem demoInv_1210101 : specInv 7 5 20 [1, 2, 1, 0, 1, 0, 1] = some [0, 2, 0, 0, 2, 1, 1] :=
  specInv_mirror_7 [1, 2, 1, 0, 1, 0, 1] [0, 0, 1, 0, 2, 0, 2] [2, 2, 1, 1, 0, 0, 1] [0, 1, 0, 0, 1, 2, 2] [0, 2, 0, 0, 2, 1, 1] demoR1_1210101 demoR2_1210101 demoC_1210101 demoM_1210101 demoMir_1210101

theorem demoR1_2210101 : invRung 7 5 20 [2, 2, 1, 0, 1, 0, 1] [2, 2, 1, 0, 1, 0, 1] 1 2 false = ([0, 1, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2210101 : invRung 7 5 20 [2, 2, 1, 0, 1, 0, 1] [0, 1, 2, 2, 2, 1, 2] 3 1 true = ([0, 2, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_2210101 : fieldCube 7 5 20 [0, 2, 2, 2, 2, 2, 1] = [1, 2, 0, 2, 0, 1, 0] := by
  decide

theorem demoM_2210101 : fieldMul 7 5 20 [1, 2, 0, 2, 0, 1, 0] [2, 2, 1, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210101 : mirrorTrits [1, 2, 0, 2, 0, 1, 0] = [2, 1, 0, 1, 0, 2, 0] := by
  decide

theorem demoInv_2210101 : specInv 7 5 20 [2, 2, 1, 0, 1, 0, 1] = some [2, 1, 0, 1, 0, 2, 0] :=
  specInv_mirror_7 [2, 2, 1, 0, 1, 0, 1] [0, 1, 2, 2, 2, 1, 2] [0, 2, 2, 2, 2, 2, 1] [1, 2, 0, 2, 0, 1, 0] [2, 1, 0, 1, 0, 2, 0] demoR1_2210101 demoR2_2210101 demoC_2210101 demoM_2210101 demoMir_2210101

theorem demoR1_0020101 : invRung 7 5 20 [0, 0, 2, 0, 1, 0, 1] [0, 0, 2, 0, 1, 0, 1] 1 2 false = ([2, 1, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_0020101 : invRung 7 5 20 [0, 0, 2, 0, 1, 0, 1] [2, 1, 1, 0, 0, 0, 2] 3 1 true = ([2, 2, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0020101 : fieldCube 7 5 20 [2, 2, 0, 1, 1, 2, 0] = [2, 0, 0, 0, 2, 1, 2] := by
  decide

theorem demoM_0020101 : fieldMul 7 5 20 [2, 0, 0, 0, 2, 1, 2] [0, 0, 2, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0020101 : specInv 7 5 20 [0, 0, 2, 0, 1, 0, 1] = some [2, 0, 0, 0, 2, 1, 2] :=
  specInv_white_7 [0, 0, 2, 0, 1, 0, 1] [2, 1, 1, 0, 0, 0, 2] [2, 2, 0, 1, 1, 2, 0] [2, 0, 0, 0, 2, 1, 2] demoR1_0020101 demoR2_0020101 demoC_0020101 demoM_0020101

theorem demoR1_1020101 : invRung 7 5 20 [1, 0, 2, 0, 1, 0, 1] [1, 0, 2, 0, 1, 0, 1] 1 2 false = ([0, 2, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1020101 : invRung 7 5 20 [1, 0, 2, 0, 1, 0, 1] [0, 2, 0, 0, 0, 2, 0] 3 1 true = ([1, 1, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_1020101 : fieldCube 7 5 20 [1, 1, 2, 0, 2, 0, 0] = [1, 2, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_1020101 : fieldMul 7 5 20 [1, 2, 0, 0, 0, 2, 1] [1, 0, 2, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020101 : mirrorTrits [1, 2, 0, 0, 0, 2, 1] = [2, 1, 0, 0, 0, 1, 2] := by
  decide

theorem demoInv_1020101 : specInv 7 5 20 [1, 0, 2, 0, 1, 0, 1] = some [2, 1, 0, 0, 0, 1, 2] :=
  specInv_mirror_7 [1, 0, 2, 0, 1, 0, 1] [0, 2, 0, 0, 0, 2, 0] [1, 1, 2, 0, 2, 0, 0] [1, 2, 0, 0, 0, 2, 1] [2, 1, 0, 0, 0, 1, 2] demoR1_1020101 demoR2_1020101 demoC_1020101 demoM_1020101 demoMir_1020101

theorem demoR1_2020101 : invRung 7 5 20 [2, 0, 2, 0, 1, 0, 1] [2, 0, 2, 0, 1, 0, 1] 1 2 false = ([0, 0, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_2020101 : invRung 7 5 20 [2, 0, 2, 0, 1, 0, 1] [0, 0, 1, 0, 1, 2, 0] 3 1 true = ([2, 2, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2020101 : fieldCube 7 5 20 [2, 2, 2, 0, 1, 1, 0] = [0, 2, 1, 0, 1, 2, 2] := by
  decide

theorem demoM_2020101 : fieldMul 7 5 20 [0, 2, 1, 0, 1, 2, 2] [2, 0, 2, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2020101 : specInv 7 5 20 [2, 0, 2, 0, 1, 0, 1] = some [0, 2, 1, 0, 1, 2, 2] :=
  specInv_white_7 [2, 0, 2, 0, 1, 0, 1] [0, 0, 1, 0, 1, 2, 0] [2, 2, 2, 0, 1, 1, 0] [0, 2, 1, 0, 1, 2, 2] demoR1_2020101 demoR2_2020101 demoC_2020101 demoM_2020101

theorem demoR1_0120101 : invRung 7 5 20 [0, 1, 2, 0, 1, 0, 1] [0, 1, 2, 0, 1, 0, 1] 1 2 false = ([2, 0, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_0120101 : invRung 7 5 20 [0, 1, 2, 0, 1, 0, 1] [2, 0, 2, 2, 1, 1, 1] 3 1 true = ([0, 1, 2, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0120101 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 2, 2] = [0, 2, 1, 1, 1, 0, 0] := by
  decide

theorem demoM_0120101 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 0, 0] [0, 1, 2, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0120101 : specInv 7 5 20 [0, 1, 2, 0, 1, 0, 1] = some [0, 2, 1, 1, 1, 0, 0] :=
  specInv_white_7 [0, 1, 2, 0, 1, 0, 1] [2, 0, 2, 2, 1, 1, 1] [0, 1, 2, 1, 1, 2, 2] [0, 2, 1, 1, 1, 0, 0] demoR1_0120101 demoR2_0120101 demoC_0120101 demoM_0120101

theorem demoR1_1120101 : invRung 7 5 20 [1, 1, 2, 0, 1, 0, 1] [1, 1, 2, 0, 1, 0, 1] 1 2 false = ([0, 1, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_1120101 : invRung 7 5 20 [1, 1, 2, 0, 1, 0, 1] [0, 1, 1, 2, 2, 2, 1] 3 1 true = ([0, 2, 0, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1120101 : fieldCube 7 5 20 [0, 2, 0, 0, 1, 1, 0] = [1, 2, 1, 0, 1, 2, 0] := by
  decide

theorem demoM_1120101 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 2, 0] [1, 1, 2, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120101 : mirrorTrits [1, 2, 1, 0, 1, 2, 0] = [2, 1, 2, 0, 2, 1, 0] := by
  decide

theorem demoInv_1120101 : specInv 7 5 20 [1, 1, 2, 0, 1, 0, 1] = some [2, 1, 2, 0, 2, 1, 0] :=
  specInv_mirror_7 [1, 1, 2, 0, 1, 0, 1] [0, 1, 1, 2, 2, 2, 1] [0, 2, 0, 0, 1, 1, 0] [1, 2, 1, 0, 1, 2, 0] [2, 1, 2, 0, 2, 1, 0] demoR1_1120101 demoR2_1120101 demoC_1120101 demoM_1120101 demoMir_1120101

theorem demoR1_2120101 : invRung 7 5 20 [2, 1, 2, 0, 1, 0, 1] [2, 1, 2, 0, 1, 0, 1] 1 2 false = ([2, 1, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_2120101 : invRung 7 5 20 [2, 1, 2, 0, 1, 0, 1] [2, 1, 1, 1, 1, 0, 0] 3 1 true = ([0, 1, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_2120101 : fieldCube 7 5 20 [0, 1, 1, 0, 1, 1, 0] = [1, 2, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_2120101 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 2, 1] [2, 1, 2, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120101 : mirrorTrits [1, 2, 1, 2, 1, 2, 1] = [2, 1, 2, 1, 2, 1, 2] := by
  decide

theorem demoInv_2120101 : specInv 7 5 20 [2, 1, 2, 0, 1, 0, 1] = some [2, 1, 2, 1, 2, 1, 2] :=
  specInv_mirror_7 [2, 1, 2, 0, 1, 0, 1] [2, 1, 1, 1, 1, 0, 0] [0, 1, 1, 0, 1, 1, 0] [1, 2, 1, 2, 1, 2, 1] [2, 1, 2, 1, 2, 1, 2] demoR1_2120101 demoR2_2120101 demoC_2120101 demoM_2120101 demoMir_2120101

theorem demoR1_0220101 : invRung 7 5 20 [0, 2, 2, 0, 1, 0, 1] [0, 2, 2, 0, 1, 0, 1] 1 2 false = ([0, 2, 2, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_0220101 : invRung 7 5 20 [0, 2, 2, 0, 1, 0, 1] [0, 2, 2, 0, 0, 0, 2] 3 1 true = ([0, 0, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0220101 : fieldCube 7 5 20 [0, 0, 0, 1, 1, 2, 0] = [0, 0, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_0220101 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 1, 2] [0, 2, 2, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0220101 : specInv 7 5 20 [0, 2, 2, 0, 1, 0, 1] = some [0, 0, 0, 1, 2, 1, 2] :=
  specInv_white_7 [0, 2, 2, 0, 1, 0, 1] [0, 2, 2, 0, 0, 0, 2] [0, 0, 0, 1, 1, 2, 0] [0, 0, 0, 1, 2, 1, 2] demoR1_0220101 demoR2_0220101 demoC_0220101 demoM_0220101

theorem demoR1_1220101 : invRung 7 5 20 [1, 2, 2, 0, 1, 0, 1] [1, 2, 2, 0, 1, 0, 1] 1 2 false = ([1, 1, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_1220101 : invRung 7 5 20 [1, 2, 2, 0, 1, 0, 1] [1, 1, 1, 1, 1, 2, 2] 3 1 true = ([0, 2, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_1220101 : fieldCube 7 5 20 [0, 2, 0, 0, 0, 0, 1] = [0, 1, 2, 0, 1, 1, 1] := by
  decide

theorem demoM_1220101 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 1, 1] [1, 2, 2, 0, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1220101 : specInv 7 5 20 [1, 2, 2, 0, 1, 0, 1] = some [0, 1, 2, 0, 1, 1, 1] :=
  specInv_white_7 [1, 2, 2, 0, 1, 0, 1] [1, 1, 1, 1, 1, 2, 2] [0, 2, 0, 0, 0, 0, 1] [0, 1, 2, 0, 1, 1, 1] demoR1_1220101 demoR2_1220101 demoC_1220101 demoM_1220101

theorem demoR1_2220101 : invRung 7 5 20 [2, 2, 2, 0, 1, 0, 1] [2, 2, 2, 0, 1, 0, 1] 1 2 false = ([2, 1, 0, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_2220101 : invRung 7 5 20 [2, 2, 2, 0, 1, 0, 1] [2, 1, 0, 0, 0, 0, 1] 3 1 true = ([2, 0, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_2220101 : fieldCube 7 5 20 [2, 0, 2, 1, 1, 0, 0] = [0, 1, 1, 1, 0, 2, 0] := by
  decide

theorem demoM_2220101 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 2, 0] [2, 2, 2, 0, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220101 : mirrorTrits [0, 1, 1, 1, 0, 2, 0] = [0, 2, 2, 2, 0, 1, 0] := by
  decide

theorem demoInv_2220101 : specInv 7 5 20 [2, 2, 2, 0, 1, 0, 1] = some [0, 2, 2, 2, 0, 1, 0] :=
  specInv_mirror_7 [2, 2, 2, 0, 1, 0, 1] [2, 1, 0, 0, 0, 0, 1] [2, 0, 2, 1, 1, 0, 0] [0, 1, 1, 1, 0, 2, 0] [0, 2, 2, 2, 0, 1, 0] demoR1_2220101 demoR2_2220101 demoC_2220101 demoM_2220101 demoMir_2220101

theorem demoR1_0001101 : invRung 7 5 20 [0, 0, 0, 1, 1, 0, 1] [0, 0, 0, 1, 1, 0, 1] 1 2 false = ([1, 1, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0001101 : invRung 7 5 20 [0, 0, 0, 1, 1, 0, 1] [1, 1, 2, 2, 0, 0, 0] 3 1 true = ([2, 0, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0001101 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 0, 1] = [2, 2, 2, 2, 1, 2, 0] := by
  decide

theorem demoM_0001101 : fieldMul 7 5 20 [2, 2, 2, 2, 1, 2, 0] [0, 0, 0, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001101 : mirrorTrits [2, 2, 2, 2, 1, 2, 0] = [1, 1, 1, 1, 2, 1, 0] := by
  decide

theorem demoInv_0001101 : specInv 7 5 20 [0, 0, 0, 1, 1, 0, 1] = some [1, 1, 1, 1, 2, 1, 0] :=
  specInv_mirror_7 [0, 0, 0, 1, 1, 0, 1] [1, 1, 2, 2, 0, 0, 0] [2, 0, 1, 0, 1, 0, 1] [2, 2, 2, 2, 1, 2, 0] [1, 1, 1, 1, 2, 1, 0] demoR1_0001101 demoR2_0001101 demoC_0001101 demoM_0001101 demoMir_0001101

theorem demoR1_1001101 : invRung 7 5 20 [1, 0, 0, 1, 1, 0, 1] [1, 0, 0, 1, 1, 0, 1] 1 2 false = ([2, 1, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_1001101 : invRung 7 5 20 [1, 0, 0, 1, 1, 0, 1] [2, 1, 1, 0, 1, 2, 2] 3 1 true = ([0, 1, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_1001101 : fieldCube 7 5 20 [0, 1, 2, 0, 0, 0, 1] = [0, 1, 2, 2, 1, 1, 0] := by
  decide

theorem demoM_1001101 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 1, 0] [1, 0, 0, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1001101 : mirrorTrits [0, 1, 2, 2, 1, 1, 0] = [0, 2, 1, 1, 2, 2, 0] := by
  decide

theorem demoInv_1001101 : specInv 7 5 20 [1, 0, 0, 1, 1, 0, 1] = some [0, 2, 1, 1, 2, 2, 0] :=
  specInv_mirror_7 [1, 0, 0, 1, 1, 0, 1] [2, 1, 1, 0, 1, 2, 2] [0, 1, 2, 0, 0, 0, 1] [0, 1, 2, 2, 1, 1, 0] [0, 2, 1, 1, 2, 2, 0] demoR1_1001101 demoR2_1001101 demoC_1001101 demoM_1001101 demoMir_1001101

theorem demoR1_2001101 : invRung 7 5 20 [2, 0, 0, 1, 1, 0, 1] [2, 0, 0, 1, 1, 0, 1] 1 2 false = ([2, 2, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_2001101 : invRung 7 5 20 [2, 0, 0, 1, 1, 0, 1] [2, 2, 0, 2, 1, 2, 1] 3 1 true = ([1, 2, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_2001101 : fieldCube 7 5 20 [1, 2, 0, 0, 0, 0, 2] = [1, 2, 1, 1, 2, 2, 2] := by
  decide

theorem demoM_2001101 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 2, 2] [2, 0, 0, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2001101 : mirrorTrits [1, 2, 1, 1, 2, 2, 2] = [2, 1, 2, 2, 1, 1, 1] := by
  decide

theorem demoInv_2001101 : specInv 7 5 20 [2, 0, 0, 1, 1, 0, 1] = some [2, 1, 2, 2, 1, 1, 1] :=
  specInv_mirror_7 [2, 0, 0, 1, 1, 0, 1] [2, 2, 0, 2, 1, 2, 1] [1, 2, 0, 0, 0, 0, 2] [1, 2, 1, 1, 2, 2, 2] [2, 1, 2, 2, 1, 1, 1] demoR1_2001101 demoR2_2001101 demoC_2001101 demoM_2001101 demoMir_2001101

theorem demoR1_0101101 : invRung 7 5 20 [0, 1, 0, 1, 1, 0, 1] [0, 1, 0, 1, 1, 0, 1] 1 2 false = ([0, 1, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_0101101 : invRung 7 5 20 [0, 1, 0, 1, 1, 0, 1] [0, 1, 1, 2, 2, 0, 0] 3 1 true = ([1, 2, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_0101101 : fieldCube 7 5 20 [1, 2, 2, 0, 2, 1, 1] = [2, 1, 0, 2, 2, 1, 1] := by
  decide

theorem demoM_0101101 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 1, 1] [0, 1, 0, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101101 : mirrorTrits [2, 1, 0, 2, 2, 1, 1] = [1, 2, 0, 1, 1, 2, 2] := by
  decide

theorem demoInv_0101101 : specInv 7 5 20 [0, 1, 0, 1, 1, 0, 1] = some [1, 2, 0, 1, 1, 2, 2] :=
  specInv_mirror_7 [0, 1, 0, 1, 1, 0, 1] [0, 1, 1, 2, 2, 0, 0] [1, 2, 2, 0, 2, 1, 1] [2, 1, 0, 2, 2, 1, 1] [1, 2, 0, 1, 1, 2, 2] demoR1_0101101 demoR2_0101101 demoC_0101101 demoM_0101101 demoMir_0101101

theorem demoR1_1101101 : invRung 7 5 20 [1, 1, 0, 1, 1, 0, 1] [1, 1, 0, 1, 1, 0, 1] 1 2 false = ([2, 0, 1, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_1101101 : invRung 7 5 20 [1, 1, 0, 1, 1, 0, 1] [2, 0, 1, 2, 1, 1, 0] 3 1 true = ([2, 1, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1101101 : fieldCube 7 5 20 [2, 1, 0, 0, 1, 0, 0] = [2, 1, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_1101101 : fieldMul 7 5 20 [2, 1, 0, 2, 0, 1, 1] [1, 1, 0, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1101101 : mirrorTrits [2, 1, 0, 2, 0, 1, 1] = [1, 2, 0, 1, 0, 2, 2] := by
  decide

theorem demoInv_1101101 : specInv 7 5 20 [1, 1, 0, 1, 1, 0, 1] = some [1, 2, 0, 1, 0, 2, 2] :=
  specInv_mirror_7 [1, 1, 0, 1, 1, 0, 1] [2, 0, 1, 2, 1, 1, 0] [2, 1, 0, 0, 1, 0, 0] [2, 1, 0, 2, 0, 1, 1] [1, 2, 0, 1, 0, 2, 2] demoR1_1101101 demoR2_1101101 demoC_1101101 demoM_1101101 demoMir_1101101

theorem demoR1_2101101 : invRung 7 5 20 [2, 1, 0, 1, 1, 0, 1] [2, 1, 0, 1, 1, 0, 1] 1 2 false = ([2, 2, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_2101101 : invRung 7 5 20 [2, 1, 0, 1, 1, 0, 1] [2, 2, 0, 2, 2, 2, 0] 3 1 true = ([0, 2, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_2101101 : fieldCube 7 5 20 [0, 2, 1, 2, 2, 0, 0] = [2, 2, 2, 1, 0, 1, 0] := by
  decide

theorem demoM_2101101 : fieldMul 7 5 20 [2, 2, 2, 1, 0, 1, 0] [2, 1, 0, 1, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2101101 : specInv 7 5 20 [2, 1, 0, 1, 1, 0, 1] = some [2, 2, 2, 1, 0, 1, 0] :=
  specInv_white_7 [2, 1, 0, 1, 1, 0, 1] [2, 2, 0, 2, 2, 2, 0] [0, 2, 1, 2, 2, 0, 0] [2, 2, 2, 1, 0, 1, 0] demoR1_2101101 demoR2_2101101 demoC_2101101 demoM_2101101

theorem demoR1_0201101 : invRung 7 5 20 [0, 2, 0, 1, 1, 0, 1] [0, 2, 0, 1, 1, 0, 1] 1 2 false = ([1, 1, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_0201101 : invRung 7 5 20 [0, 2, 0, 1, 1, 0, 1] [1, 1, 0, 2, 1, 0, 0] 3 1 true = ([0, 1, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_0201101 : fieldCube 7 5 20 [0, 1, 1, 2, 2, 1, 1] = [0, 1, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_0201101 : fieldMul 7 5 20 [0, 1, 2, 1, 2, 0, 0] [0, 2, 0, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201101 : mirrorTrits [0, 1, 2, 1, 2, 0, 0] = [0, 2, 1, 2, 1, 0, 0] := by
  decide

theorem demoInv_0201101 : specInv 7 5 20 [0, 2, 0, 1, 1, 0, 1] = some [0, 2, 1, 2, 1, 0, 0] :=
  specInv_mirror_7 [0, 2, 0, 1, 1, 0, 1] [1, 1, 0, 2, 1, 0, 0] [0, 1, 1, 2, 2, 1, 1] [0, 1, 2, 1, 2, 0, 0] [0, 2, 1, 2, 1, 0, 0] demoR1_0201101 demoR2_0201101 demoC_0201101 demoM_0201101 demoMir_0201101

theorem demoR1_1201101 : invRung 7 5 20 [1, 2, 0, 1, 1, 0, 1] [1, 2, 0, 1, 1, 0, 1] 1 2 false = ([1, 0, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_1201101 : invRung 7 5 20 [1, 2, 0, 1, 1, 0, 1] [1, 0, 1, 2, 0, 2, 2] 3 1 true = ([2, 0, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_1201101 : fieldCube 7 5 20 [2, 0, 1, 1, 0, 0, 1] = [0, 1, 0, 1, 1, 2, 2] := by
  decide

theorem demoM_1201101 : fieldMul 7 5 20 [0, 1, 0, 1, 1, 2, 2] [1, 2, 0, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201101 : mirrorTrits [0, 1, 0, 1, 1, 2, 2] = [0, 2, 0, 2, 2, 1, 1] := by
  decide

theorem demoInv_1201101 : specInv 7 5 20 [1, 2, 0, 1, 1, 0, 1] = some [0, 2, 0, 2, 2, 1, 1] :=
  specInv_mirror_7 [1, 2, 0, 1, 1, 0, 1] [1, 0, 1, 2, 0, 2, 2] [2, 0, 1, 1, 0, 0, 1] [0, 1, 0, 1, 1, 2, 2] [0, 2, 0, 2, 2, 1, 1] demoR1_1201101 demoR2_1201101 demoC_1201101 demoM_1201101 demoMir_1201101

theorem demoR1_2201101 : invRung 7 5 20 [2, 2, 0, 1, 1, 0, 1] [2, 2, 0, 1, 1, 0, 1] 1 2 false = ([1, 1, 0, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_2201101 : invRung 7 5 20 [2, 2, 0, 1, 1, 0, 1] [1, 1, 0, 1, 1, 0, 1] 3 1 true = ([0, 0, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_2201101 : fieldCube 7 5 20 [0, 0, 2, 2, 0, 1, 0] = [0, 1, 0, 0, 1, 0, 1] := by
  decide

theorem demoM_2201101 : fieldMul 7 5 20 [0, 1, 0, 0, 1, 0, 1] [2, 2, 0, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2201101 : mirrorTrits [0, 1, 0, 0, 1, 0, 1] = [0, 2, 0, 0, 2, 0, 2] := by
  decide

theorem demoInv_2201101 : specInv 7 5 20 [2, 2, 0, 1, 1, 0, 1] = some [0, 2, 0, 0, 2, 0, 2] :=
  specInv_mirror_7 [2, 2, 0, 1, 1, 0, 1] [1, 1, 0, 1, 1, 0, 1] [0, 0, 2, 2, 0, 1, 0] [0, 1, 0, 0, 1, 0, 1] [0, 2, 0, 0, 2, 0, 2] demoR1_2201101 demoR2_2201101 demoC_2201101 demoM_2201101 demoMir_2201101

theorem demoR1_0011101 : invRung 7 5 20 [0, 0, 1, 1, 1, 0, 1] [0, 0, 1, 1, 1, 0, 1] 1 2 false = ([0, 1, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_0011101 : invRung 7 5 20 [0, 0, 1, 1, 1, 0, 1] [0, 1, 1, 1, 0, 2, 0] 3 1 true = ([1, 2, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_0011101 : fieldCube 7 5 20 [1, 2, 2, 1, 1, 0, 0] = [2, 1, 1, 0, 0, 2, 0] := by
  decide

theorem demoM_0011101 : fieldMul 7 5 20 [2, 1, 1, 0, 0, 2, 0] [0, 0, 1, 1, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0011101 : specInv 7 5 20 [0, 0, 1, 1, 1, 0, 1] = some [2, 1, 1, 0, 0, 2, 0] :=
  specInv_white_7 [0, 0, 1, 1, 1, 0, 1] [0, 1, 1, 1, 0, 2, 0] [1, 2, 2, 1, 1, 0, 0] [2, 1, 1, 0, 0, 2, 0] demoR1_0011101 demoR2_0011101 demoC_0011101 demoM_0011101

theorem demoR1_1011101 : invRung 7 5 20 [1, 0, 1, 1, 1, 0, 1] [1, 0, 1, 1, 1, 0, 1] 1 2 false = ([0, 1, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_1011101 : invRung 7 5 20 [1, 0, 1, 1, 1, 0, 1] [0, 1, 2, 1, 1, 1, 1] 3 1 true = ([0, 2, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_1011101 : fieldCube 7 5 20 [0, 2, 0, 2, 2, 2, 2] = [1, 0, 2, 0, 1, 2, 2] := by
  decide

theorem demoM_1011101 : fieldMul 7 5 20 [1, 0, 2, 0, 1, 2, 2] [1, 0, 1, 1, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1011101 : specInv 7 5 20 [1, 0, 1, 1, 1, 0, 1] = some [1, 0, 2, 0, 1, 2, 2] :=
  specInv_white_7 [1, 0, 1, 1, 1, 0, 1] [0, 1, 2, 1, 1, 1, 1] [0, 2, 0, 2, 2, 2, 2] [1, 0, 2, 0, 1, 2, 2] demoR1_1011101 demoR2_1011101 demoC_1011101 demoM_1011101

theorem demoR1_2011101 : invRung 7 5 20 [2, 0, 1, 1, 1, 0, 1] [2, 0, 1, 1, 1, 0, 1] 1 2 false = ([2, 1, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_2011101 : invRung 7 5 20 [2, 0, 1, 1, 1, 0, 1] [2, 1, 0, 1, 0, 0, 0] 3 1 true = ([0, 1, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_2011101 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 2, 1] = [0, 0, 2, 2, 0, 1, 1] := by
  decide

theorem demoM_2011101 : fieldMul 7 5 20 [0, 0, 2, 2, 0, 1, 1] [2, 0, 1, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011101 : mirrorTrits [0, 0, 2, 2, 0, 1, 1] = [0, 0, 1, 1, 0, 2, 2] := by
  decide

theorem demoInv_2011101 : specInv 7 5 20 [2, 0, 1, 1, 1, 0, 1] = some [0, 0, 1, 1, 0, 2, 2] :=
  specInv_mirror_7 [2, 0, 1, 1, 1, 0, 1] [2, 1, 0, 1, 0, 0, 0] [0, 1, 2, 1, 0, 2, 1] [0, 0, 2, 2, 0, 1, 1] [0, 0, 1, 1, 0, 2, 2] demoR1_2011101 demoR2_2011101 demoC_2011101 demoM_2011101 demoMir_2011101

theorem demoR1_0111101 : invRung 7 5 20 [0, 1, 1, 1, 1, 0, 1] [0, 1, 1, 1, 1, 0, 1] 1 2 false = ([0, 2, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_0111101 : invRung 7 5 20 [0, 1, 1, 1, 1, 0, 1] [0, 2, 2, 2, 2, 1, 0] 3 1 true = ([2, 2, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0111101 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 1, 2] = [2, 1, 1, 2, 0, 0, 1] := by
  decide

theorem demoM_0111101 : fieldMul 7 5 20 [2, 1, 1, 2, 0, 0, 1] [0, 1, 1, 1, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0111101 : specInv 7 5 20 [0, 1, 1, 1, 1, 0, 1] = some [2, 1, 1, 2, 0, 0, 1] :=
  specInv_white_7 [0, 1, 1, 1, 1, 0, 1] [0, 2, 2, 2, 2, 1, 0] [2, 2, 2, 2, 1, 1, 2] [2, 1, 1, 2, 0, 0, 1] demoR1_0111101 demoR2_0111101 demoC_0111101 demoM_0111101

theorem demoR1_1111101 : invRung 7 5 20 [1, 1, 1, 1, 1, 0, 1] [1, 1, 1, 1, 1, 0, 1] 1 2 false = ([1, 0, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_1111101 : invRung 7 5 20 [1, 1, 1, 1, 1, 0, 1] [1, 0, 2, 0, 2, 0, 1] 3 1 true = ([1, 0, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_1111101 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 1, 2] = [1, 1, 1, 0, 0, 0, 0] := by
  decide

theorem demoM_1111101 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 0, 0] [1, 1, 1, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1111101 : mirrorTrits [1, 1, 1, 0, 0, 0, 0] = [2, 2, 2, 0, 0, 0, 0] := by
  decide

theorem demoInv_1111101 : specInv 7 5 20 [1, 1, 1, 1, 1, 0, 1] = some [2, 2, 2, 0, 0, 0, 0] :=
  specInv_mirror_7 [1, 1, 1, 1, 1, 0, 1] [1, 0, 2, 0, 2, 0, 1] [1, 0, 1, 2, 1, 1, 2] [1, 1, 1, 0, 0, 0, 0] [2, 2, 2, 0, 0, 0, 0] demoR1_1111101 demoR2_1111101 demoC_1111101 demoM_1111101 demoMir_1111101

theorem demoR1_2111101 : invRung 7 5 20 [2, 1, 1, 1, 1, 0, 1] [2, 1, 1, 1, 1, 0, 1] 1 2 false = ([0, 0, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_2111101 : invRung 7 5 20 [2, 1, 1, 1, 1, 0, 1] [0, 0, 1, 0, 0, 1, 0] 3 1 true = ([1, 2, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_2111101 : fieldCube 7 5 20 [1, 2, 1, 1, 1, 2, 0] = [1, 0, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_2111101 : fieldMul 7 5 20 [1, 0, 0, 0, 2, 1, 0] [2, 1, 1, 1, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2111101 : specInv 7 5 20 [2, 1, 1, 1, 1, 0, 1] = some [1, 0, 0, 0, 2, 1, 0] :=
  specInv_white_7 [2, 1, 1, 1, 1, 0, 1] [0, 0, 1, 0, 0, 1, 0] [1, 2, 1, 1, 1, 2, 0] [1, 0, 0, 0, 2, 1, 0] demoR1_2111101 demoR2_2111101 demoC_2111101 demoM_2111101

theorem demoR1_0211101 : invRung 7 5 20 [0, 2, 1, 1, 1, 0, 1] [0, 2, 1, 1, 1, 0, 1] 1 2 false = ([0, 2, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_0211101 : invRung 7 5 20 [0, 2, 1, 1, 1, 0, 1] [0, 2, 1, 0, 1, 1, 0] 3 1 true = ([2, 1, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_0211101 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 0, 2] = [1, 1, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_0211101 : fieldMul 7 5 20 [1, 1, 0, 2, 2, 0, 1] [0, 2, 1, 1, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0211101 : specInv 7 5 20 [0, 2, 1, 1, 1, 0, 1] = some [1, 1, 0, 2, 2, 0, 1] :=
  specInv_white_7 [0, 2, 1, 1, 1, 0, 1] [0, 2, 1, 0, 1, 1, 0] [2, 1, 0, 2, 2, 0, 2] [1, 1, 0, 2, 2, 0, 1] demoR1_0211101 demoR2_0211101 demoC_0211101 demoM_0211101

theorem demoR1_1211101 : invRung 7 5 20 [1, 2, 1, 1, 1, 0, 1] [1, 2, 1, 1, 1, 0, 1] 1 2 false = ([2, 2, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_1211101 : invRung 7 5 20 [1, 2, 1, 1, 1, 0, 1] [2, 2, 0, 0, 2, 2, 2] 3 1 true = ([1, 2, 1, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_1211101 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 0, 0] = [0, 1, 2, 0, 0, 0, 2] := by
  decide

theorem demoM_1211101 : fieldMul 7 5 20 [0, 1, 2, 0, 0, 0, 2] [1, 2, 1, 1, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1211101 : specInv 7 5 20 [1, 2, 1, 1, 1, 0, 1] = some [0, 1, 2, 0, 0, 0, 2] :=
  specInv_white_7 [1, 2, 1, 1, 1, 0, 1] [2, 2, 0, 0, 2, 2, 2] [1, 2, 1, 2, 1, 0, 0] [0, 1, 2, 0, 0, 0, 2] demoR1_1211101 demoR2_1211101 demoC_1211101 demoM_1211101

theorem demoR1_2211101 : invRung 7 5 20 [2, 2, 1, 1, 1, 0, 1] [2, 2, 1, 1, 1, 0, 1] 1 2 false = ([1, 0, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_2211101 : invRung 7 5 20 [2, 2, 1, 1, 1, 0, 1] [1, 0, 0, 1, 1, 1, 2] 3 1 true = ([1, 1, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_2211101 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 0, 1] = [1, 2, 2, 0, 1, 2, 2] := by
  decide

theorem demoM_2211101 : fieldMul 7 5 20 [1, 2, 2, 0, 1, 2, 2] [2, 2, 1, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2211101 : mirrorTrits [1, 2, 2, 0, 1, 2, 2] = [2, 1, 1, 0, 2, 1, 1] := by
  decide

theorem demoInv_2211101 : specInv 7 5 20 [2, 2, 1, 1, 1, 0, 1] = some [2, 1, 1, 0, 2, 1, 1] :=
  specInv_mirror_7 [2, 2, 1, 1, 1, 0, 1] [1, 0, 0, 1, 1, 1, 2] [1, 1, 0, 0, 1, 0, 1] [1, 2, 2, 0, 1, 2, 2] [2, 1, 1, 0, 2, 1, 1] demoR1_2211101 demoR2_2211101 demoC_2211101 demoM_2211101 demoMir_2211101

theorem demoR1_0021101 : invRung 7 5 20 [0, 0, 2, 1, 1, 0, 1] [0, 0, 2, 1, 1, 0, 1] 1 2 false = ([1, 0, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoR2_0021101 : invRung 7 5 20 [0, 0, 2, 1, 1, 0, 1] [1, 0, 1, 0, 1, 2, 1] 3 1 true = ([0, 2, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0021101 : fieldCube 7 5 20 [0, 2, 1, 1, 0, 1, 2] = [2, 0, 0, 1, 0, 1, 2] := by
  decide

theorem demoM_0021101 : fieldMul 7 5 20 [2, 0, 0, 1, 0, 1, 2] [0, 0, 2, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021101 : mirrorTrits [2, 0, 0, 1, 0, 1, 2] = [1, 0, 0, 2, 0, 2, 1] := by
  decide

theorem demoInv_0021101 : specInv 7 5 20 [0, 0, 2, 1, 1, 0, 1] = some [1, 0, 0, 2, 0, 2, 1] :=
  specInv_mirror_7 [0, 0, 2, 1, 1, 0, 1] [1, 0, 1, 0, 1, 2, 1] [0, 2, 1, 1, 0, 1, 2] [2, 0, 0, 1, 0, 1, 2] [1, 0, 0, 2, 0, 2, 1] demoR1_0021101 demoR2_0021101 demoC_0021101 demoM_0021101 demoMir_0021101

theorem demoR1_1021101 : invRung 7 5 20 [1, 0, 2, 1, 1, 0, 1] [1, 0, 2, 1, 1, 0, 1] 1 2 false = ([2, 0, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1021101 : invRung 7 5 20 [1, 0, 2, 1, 1, 0, 1] [2, 0, 2, 2, 2, 1, 0] 3 1 true = ([1, 0, 2, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1021101 : fieldCube 7 5 20 [1, 0, 2, 0, 1, 1, 0] = [2, 2, 1, 1, 1, 2, 2] := by
  decide

theorem demoM_1021101 : fieldMul 7 5 20 [2, 2, 1, 1, 1, 2, 2] [1, 0, 2, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021101 : mirrorTrits [2, 2, 1, 1, 1, 2, 2] = [1, 1, 2, 2, 2, 1, 1] := by
  decide

theorem demoInv_1021101 : specInv 7 5 20 [1, 0, 2, 1, 1, 0, 1] = some [1, 1, 2, 2, 2, 1, 1] :=
  specInv_mirror_7 [1, 0, 2, 1, 1, 0, 1] [2, 0, 2, 2, 2, 1, 0] [1, 0, 2, 0, 1, 1, 0] [2, 2, 1, 1, 1, 2, 2] [1, 1, 2, 2, 2, 1, 1] demoR1_1021101 demoR2_1021101 demoC_1021101 demoM_1021101 demoMir_1021101

theorem demoR1_2021101 : invRung 7 5 20 [2, 0, 2, 1, 1, 0, 1] [2, 0, 2, 1, 1, 0, 1] 1 2 false = ([2, 2, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_2021101 : invRung 7 5 20 [2, 0, 2, 1, 1, 0, 1] [2, 2, 0, 0, 0, 2, 1] 3 1 true = ([1, 0, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_2021101 : fieldCube 7 5 20 [1, 0, 2, 1, 2, 0, 0] = [2, 2, 1, 2, 0, 0, 1] := by
  decide

theorem demoM_2021101 : fieldMul 7 5 20 [2, 2, 1, 2, 0, 0, 1] [2, 0, 2, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2021101 : mirrorTrits [2, 2, 1, 2, 0, 0, 1] = [1, 1, 2, 1, 0, 0, 2] := by
  decide

theorem demoInv_2021101 : specInv 7 5 20 [2, 0, 2, 1, 1, 0, 1] = some [1, 1, 2, 1, 0, 0, 2] :=
  specInv_mirror_7 [2, 0, 2, 1, 1, 0, 1] [2, 2, 0, 0, 0, 2, 1] [1, 0, 2, 1, 2, 0, 0] [2, 2, 1, 2, 0, 0, 1] [1, 1, 2, 1, 0, 0, 2] demoR1_2021101 demoR2_2021101 demoC_2021101 demoM_2021101 demoMir_2021101

theorem demoR1_0121101 : invRung 7 5 20 [0, 1, 2, 1, 1, 0, 1] [0, 1, 2, 1, 1, 0, 1] 1 2 false = ([2, 1, 0, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_0121101 : invRung 7 5 20 [0, 1, 2, 1, 1, 0, 1] [2, 1, 0, 1, 2, 2, 0] 3 1 true = ([0, 1, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0121101 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 2, 1] = [2, 0, 1, 2, 0, 0, 0] := by
  decide

theorem demoM_0121101 : fieldMul 7 5 20 [2, 0, 1, 2, 0, 0, 0] [0, 1, 2, 1, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0121101 : specInv 7 5 20 [0, 1, 2, 1, 1, 0, 1] = some [2, 0, 1, 2, 0, 0, 0] :=
  specInv_white_7 [0, 1, 2, 1, 1, 0, 1] [2, 1, 0, 1, 2, 2, 0] [0, 1, 1, 0, 0, 2, 1] [2, 0, 1, 2, 0, 0, 0] demoR1_0121101 demoR2_0121101 demoC_0121101 demoM_0121101

theorem demoR1_1121101 : invRung 7 5 20 [1, 1, 2, 1, 1, 0, 1] [1, 1, 2, 1, 1, 0, 1] 1 2 false = ([1, 1, 1, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_1121101 : invRung 7 5 20 [1, 1, 2, 1, 1, 0, 1] [1, 1, 1, 0, 0, 2, 1] 3 1 true = ([1, 0, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoC_1121101 : fieldCube 7 5 20 [1, 0, 2, 0, 1, 1, 1] = [2, 0, 0, 2, 2, 0, 0] := by
  decide

theorem demoM_1121101 : fieldMul 7 5 20 [2, 0, 0, 2, 2, 0, 0] [1, 1, 2, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121101 : mirrorTrits [2, 0, 0, 2, 2, 0, 0] = [1, 0, 0, 1, 1, 0, 0] := by
  decide

theorem demoInv_1121101 : specInv 7 5 20 [1, 1, 2, 1, 1, 0, 1] = some [1, 0, 0, 1, 1, 0, 0] :=
  specInv_mirror_7 [1, 1, 2, 1, 1, 0, 1] [1, 1, 1, 0, 0, 2, 1] [1, 0, 2, 0, 1, 1, 1] [2, 0, 0, 2, 2, 0, 0] [1, 0, 0, 1, 1, 0, 0] demoR1_1121101 demoR2_1121101 demoC_1121101 demoM_1121101 demoMir_1121101

theorem demoR1_2121101 : invRung 7 5 20 [2, 1, 2, 1, 1, 0, 1] [2, 1, 2, 1, 1, 0, 1] 1 2 false = ([1, 2, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_2121101 : invRung 7 5 20 [2, 1, 2, 1, 1, 0, 1] [1, 2, 1, 0, 1, 0, 1] 3 1 true = ([1, 0, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_2121101 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 1, 0] = [0, 0, 2, 2, 1, 1, 1] := by
  decide

theorem demoM_2121101 : fieldMul 7 5 20 [0, 0, 2, 2, 1, 1, 1] [2, 1, 2, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2121101 : mirrorTrits [0, 0, 2, 2, 1, 1, 1] = [0, 0, 1, 1, 2, 2, 2] := by
  decide

theorem demoInv_2121101 : specInv 7 5 20 [2, 1, 2, 1, 1, 0, 1] = some [0, 0, 1, 1, 2, 2, 2] :=
  specInv_mirror_7 [2, 1, 2, 1, 1, 0, 1] [1, 2, 1, 0, 1, 0, 1] [1, 0, 0, 1, 2, 1, 0] [0, 0, 2, 2, 1, 1, 1] [0, 0, 1, 1, 2, 2, 2] demoR1_2121101 demoR2_2121101 demoC_2121101 demoM_2121101 demoMir_2121101

theorem demoR1_0221101 : invRung 7 5 20 [0, 2, 2, 1, 1, 0, 1] [0, 2, 2, 1, 1, 0, 1] 1 2 false = ([1, 0, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_0221101 : invRung 7 5 20 [0, 2, 2, 1, 1, 0, 1] [1, 0, 1, 2, 0, 1, 2] 3 1 true = ([0, 0, 2, 0, 0, 2, 1], 3) := by
  decide

theorem demoC_0221101 : fieldCube 7 5 20 [0, 0, 2, 0, 0, 2, 1] = [2, 0, 1, 1, 0, 0, 1] := by
  decide

theorem demoM_0221101 : fieldMul 7 5 20 [2, 0, 1, 1, 0, 0, 1] [0, 2, 2, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0221101 : mirrorTrits [2, 0, 1, 1, 0, 0, 1] = [1, 0, 2, 2, 0, 0, 2] := by
  decide

theorem demoInv_0221101 : specInv 7 5 20 [0, 2, 2, 1, 1, 0, 1] = some [1, 0, 2, 2, 0, 0, 2] :=
  specInv_mirror_7 [0, 2, 2, 1, 1, 0, 1] [1, 0, 1, 2, 0, 1, 2] [0, 0, 2, 0, 0, 2, 1] [2, 0, 1, 1, 0, 0, 1] [1, 0, 2, 2, 0, 0, 2] demoR1_0221101 demoR2_0221101 demoC_0221101 demoM_0221101 demoMir_0221101

theorem demoR1_1221101 : invRung 7 5 20 [1, 2, 2, 1, 1, 0, 1] [1, 2, 2, 1, 1, 0, 1] 1 2 false = ([1, 1, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_1221101 : invRung 7 5 20 [1, 2, 2, 1, 1, 0, 1] [1, 1, 2, 2, 0, 1, 0] 3 1 true = ([0, 1, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1221101 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 2, 1] = [0, 0, 2, 2, 0, 1, 0] := by
  decide

theorem demoM_1221101 : fieldMul 7 5 20 [0, 0, 2, 2, 0, 1, 0] [1, 2, 2, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221101 : mirrorTrits [0, 0, 2, 2, 0, 1, 0] = [0, 0, 1, 1, 0, 2, 0] := by
  decide

theorem demoInv_1221101 : specInv 7 5 20 [1, 2, 2, 1, 1, 0, 1] = some [0, 0, 1, 1, 0, 2, 0] :=
  specInv_mirror_7 [1, 2, 2, 1, 1, 0, 1] [1, 1, 2, 2, 0, 1, 0] [0, 1, 1, 1, 0, 2, 1] [0, 0, 2, 2, 0, 1, 0] [0, 0, 1, 1, 0, 2, 0] demoR1_1221101 demoR2_1221101 demoC_1221101 demoM_1221101 demoMir_1221101

theorem demoR1_2221101 : invRung 7 5 20 [2, 2, 2, 1, 1, 0, 1] [2, 2, 2, 1, 1, 0, 1] 1 2 false = ([1, 2, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_2221101 : invRung 7 5 20 [2, 2, 2, 1, 1, 0, 1] [1, 2, 1, 2, 0, 1, 0] 3 1 true = ([0, 1, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_2221101 : fieldCube 7 5 20 [0, 1, 0, 0, 2, 0, 2] = [0, 1, 1, 2, 2, 1, 1] := by
  decide

theorem demoM_2221101 : fieldMul 7 5 20 [0, 1, 1, 2, 2, 1, 1] [2, 2, 2, 1, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221101 : mirrorTrits [0, 1, 1, 2, 2, 1, 1] = [0, 2, 2, 1, 1, 2, 2] := by
  decide

theorem demoInv_2221101 : specInv 7 5 20 [2, 2, 2, 1, 1, 0, 1] = some [0, 2, 2, 1, 1, 2, 2] :=
  specInv_mirror_7 [2, 2, 2, 1, 1, 0, 1] [1, 2, 1, 2, 0, 1, 0] [0, 1, 0, 0, 2, 0, 2] [0, 1, 1, 2, 2, 1, 1] [0, 2, 2, 1, 1, 2, 2] demoR1_2221101 demoR2_2221101 demoC_2221101 demoM_2221101 demoMir_2221101

theorem demoR1_0002101 : invRung 7 5 20 [0, 0, 0, 2, 1, 0, 1] [0, 0, 0, 2, 1, 0, 1] 1 2 false = ([2, 1, 2, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0002101 : invRung 7 5 20 [0, 0, 0, 2, 1, 0, 1] [2, 1, 2, 0, 1, 1, 1] 3 1 true = ([2, 2, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0002101 : fieldCube 7 5 20 [2, 2, 0, 1, 2, 2, 2] = [2, 0, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_0002101 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 1, 2] [0, 0, 0, 2, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002101 : mirrorTrits [2, 0, 1, 0, 1, 1, 2] = [1, 0, 2, 0, 2, 2, 1] := by
  decide

theorem demoInv_0002101 : specInv 7 5 20 [0, 0, 0, 2, 1, 0, 1] = some [1, 0, 2, 0, 2, 2, 1] :=
  specInv_mirror_7 [0, 0, 0, 2, 1, 0, 1] [2, 1, 2, 0, 1, 1, 1] [2, 2, 0, 1, 2, 2, 2] [2, 0, 1, 0, 1, 1, 2] [1, 0, 2, 0, 2, 2, 1] demoR1_0002101 demoR2_0002101 demoC_0002101 demoM_0002101 demoMir_0002101

theorem demoR1_1002101 : invRung 7 5 20 [1, 0, 0, 2, 1, 0, 1] [1, 0, 0, 2, 1, 0, 1] 1 2 false = ([0, 0, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_1002101 : invRung 7 5 20 [1, 0, 0, 2, 1, 0, 1] [0, 0, 0, 0, 2, 1, 0] 3 1 true = ([1, 2, 1, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_1002101 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 2, 1] = [0, 1, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_1002101 : fieldMul 7 5 20 [0, 1, 1, 1, 0, 1, 1] [1, 0, 0, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1002101 : specInv 7 5 20 [1, 0, 0, 2, 1, 0, 1] = some [0, 1, 1, 1, 0, 1, 1] :=
  specInv_white_7 [1, 0, 0, 2, 1, 0, 1] [0, 0, 0, 0, 2, 1, 0] [1, 2, 1, 0, 1, 2, 1] [0, 1, 1, 1, 0, 1, 1] demoR1_1002101 demoR2_1002101 demoC_1002101 demoM_1002101

theorem demoR1_2002101 : invRung 7 5 20 [2, 0, 0, 2, 1, 0, 1] [2, 0, 0, 2, 1, 0, 1] 1 2 false = ([0, 2, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_2002101 : invRung 7 5 20 [2, 0, 0, 2, 1, 0, 1] [0, 2, 2, 0, 1, 0, 2] 3 1 true = ([2, 0, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2002101 : fieldCube 7 5 20 [2, 0, 0, 1, 0, 1, 1] = [1, 2, 1, 1, 2, 0, 0] := by
  decide

theorem demoM_2002101 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 0, 0] [2, 0, 0, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2002101 : specInv 7 5 20 [2, 0, 0, 2, 1, 0, 1] = some [1, 2, 1, 1, 2, 0, 0] :=
  specInv_white_7 [2, 0, 0, 2, 1, 0, 1] [0, 2, 2, 0, 1, 0, 2] [2, 0, 0, 1, 0, 1, 1] [1, 2, 1, 1, 2, 0, 0] demoR1_2002101 demoR2_2002101 demoC_2002101 demoM_2002101

theorem demoR1_0102101 : invRung 7 5 20 [0, 1, 0, 2, 1, 0, 1] [0, 1, 0, 2, 1, 0, 1] 1 2 false = ([2, 0, 0, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_0102101 : invRung 7 5 20 [0, 1, 0, 2, 1, 0, 1] [2, 0, 0, 1, 1, 0, 1] 3 1 true = ([1, 1, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_0102101 : fieldCube 7 5 20 [1, 1, 1, 0, 2, 0, 2] = [1, 1, 1, 2, 2, 1, 2] := by
  decide

theorem demoM_0102101 : fieldMul 7 5 20 [1, 1, 1, 2, 2, 1, 2] [0, 1, 0, 2, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0102101 : mirrorTrits [1, 1, 1, 2, 2, 1, 2] = [2, 2, 2, 1, 1, 2, 1] := by
  decide

theorem demoInv_0102101 : specInv 7 5 20 [0, 1, 0, 2, 1, 0, 1] = some [2, 2, 2, 1, 1, 2, 1] :=
  specInv_mirror_7 [0, 1, 0, 2, 1, 0, 1] [2, 0, 0, 1, 1, 0, 1] [1, 1, 1, 0, 2, 0, 2] [1, 1, 1, 2, 2, 1, 2] [2, 2, 2, 1, 1, 2, 1] demoR1_0102101 demoR2_0102101 demoC_0102101 demoM_0102101 demoMir_0102101

theorem demoR1_1102101 : invRung 7 5 20 [1, 1, 0, 2, 1, 0, 1] [1, 1, 0, 2, 1, 0, 1] 1 2 false = ([2, 1, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_1102101 : invRung 7 5 20 [1, 1, 0, 2, 1, 0, 1] [2, 1, 2, 0, 2, 1, 1] 3 1 true = ([2, 0, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_1102101 : fieldCube 7 5 20 [2, 0, 0, 1, 2, 1, 2] = [1, 2, 0, 1, 0, 0, 0] := by
  decide

theorem demoM_1102101 : fieldMul 7 5 20 [1, 2, 0, 1, 0, 0, 0] [1, 1, 0, 2, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1102101 : mirrorTrits [1, 2, 0, 1, 0, 0, 0] = [2, 1, 0, 2, 0, 0, 0] := by
  decide

theorem demoInv_1102101 : specInv 7 5 20 [1, 1, 0, 2, 1, 0, 1] = some [2, 1, 0, 2, 0, 0, 0] :=
  specInv_mirror_7 [1, 1, 0, 2, 1, 0, 1] [2, 1, 2, 0, 2, 1, 1] [2, 0, 0, 1, 2, 1, 2] [1, 2, 0, 1, 0, 0, 0] [2, 1, 0, 2, 0, 0, 0] demoR1_1102101 demoR2_1102101 demoC_1102101 demoM_1102101 demoMir_1102101

theorem demoR1_2102101 : invRung 7 5 20 [2, 1, 0, 2, 1, 0, 1] [2, 1, 0, 2, 1, 0, 1] 1 2 false = ([0, 1, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_2102101 : invRung 7 5 20 [2, 1, 0, 2, 1, 0, 1] [0, 1, 1, 1, 1, 0, 1] 3 1 true = ([2, 2, 1, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_2102101 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 2, 2] = [1, 0, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_2102101 : fieldMul 7 5 20 [1, 0, 0, 0, 1, 0, 0] [2, 1, 0, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2102101 : specInv 7 5 20 [2, 1, 0, 2, 1, 0, 1] = some [1, 0, 0, 0, 1, 0, 0] :=
  specInv_white_7 [2, 1, 0, 2, 1, 0, 1] [0, 1, 1, 1, 1, 0, 1] [2, 2, 1, 0, 2, 2, 2] [1, 0, 0, 0, 1, 0, 0] demoR1_2102101 demoR2_2102101 demoC_2102101 demoM_2102101

theorem demoR1_0202101 : invRung 7 5 20 [0, 2, 0, 2, 1, 0, 1] [0, 2, 0, 2, 1, 0, 1] 1 2 false = ([1, 0, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_0202101 : invRung 7 5 20 [0, 2, 0, 2, 1, 0, 1] [1, 0, 1, 0, 0, 0, 2] 3 1 true = ([2, 2, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_0202101 : fieldCube 7 5 20 [2, 2, 1, 2, 0, 0, 1] = [1, 1, 1, 0, 1, 0, 2] := by
  decide

theorem demoM_0202101 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 0, 2] [0, 2, 0, 2, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202101 : mirrorTrits [1, 1, 1, 0, 1, 0, 2] = [2, 2, 2, 0, 2, 0, 1] := by
  decide

theorem demoInv_0202101 : specInv 7 5 20 [0, 2, 0, 2, 1, 0, 1] = some [2, 2, 2, 0, 2, 0, 1] :=
  specInv_mirror_7 [0, 2, 0, 2, 1, 0, 1] [1, 0, 1, 0, 0, 0, 2] [2, 2, 1, 2, 0, 0, 1] [1, 1, 1, 0, 1, 0, 2] [2, 2, 2, 0, 2, 0, 1] demoR1_0202101 demoR2_0202101 demoC_0202101 demoM_0202101 demoMir_0202101

theorem demoR1_1202101 : invRung 7 5 20 [1, 2, 0, 2, 1, 0, 1] [1, 2, 0, 2, 1, 0, 1] 1 2 false = ([0, 1, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_1202101 : invRung 7 5 20 [1, 2, 0, 2, 1, 0, 1] [0, 1, 1, 2, 0, 1, 1] 3 1 true = ([2, 0, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_1202101 : fieldCube 7 5 20 [2, 0, 0, 1, 0, 1, 2] = [1, 0, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_1202101 : fieldMul 7 5 20 [1, 0, 0, 2, 0, 1, 1] [1, 2, 0, 2, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202101 : mirrorTrits [1, 0, 0, 2, 0, 1, 1] = [2, 0, 0, 1, 0, 2, 2] := by
  decide

theorem demoInv_1202101 : specInv 7 5 20 [1, 2, 0, 2, 1, 0, 1] = some [2, 0, 0, 1, 0, 2, 2] :=
  specInv_mirror_7 [1, 2, 0, 2, 1, 0, 1] [0, 1, 1, 2, 0, 1, 1] [2, 0, 0, 1, 0, 1, 2] [1, 0, 0, 2, 0, 1, 1] [2, 0, 0, 1, 0, 2, 2] demoR1_1202101 demoR2_1202101 demoC_1202101 demoM_1202101 demoMir_1202101

theorem demoR1_2202101 : invRung 7 5 20 [2, 2, 0, 2, 1, 0, 1] [2, 2, 0, 2, 1, 0, 1] 1 2 false = ([2, 0, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_2202101 : invRung 7 5 20 [2, 2, 0, 2, 1, 0, 1] [2, 0, 0, 2, 1, 2, 0] 3 1 true = ([2, 2, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_2202101 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 2, 2] = [2, 2, 1, 2, 1, 0, 2] := by
  decide

theorem demoM_2202101 : fieldMul 7 5 20 [2, 2, 1, 2, 1, 0, 2] [2, 2, 0, 2, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2202101 : mirrorTrits [2, 2, 1, 2, 1, 0, 2] = [1, 1, 2, 1, 2, 0, 1] := by
  decide

theorem demoInv_2202101 : specInv 7 5 20 [2, 2, 0, 2, 1, 0, 1] = some [1, 1, 2, 1, 2, 0, 1] :=
  specInv_mirror_7 [2, 2, 0, 2, 1, 0, 1] [2, 0, 0, 2, 1, 2, 0] [2, 2, 1, 1, 1, 2, 2] [2, 2, 1, 2, 1, 0, 2] [1, 1, 2, 1, 2, 0, 1] demoR1_2202101 demoR2_2202101 demoC_2202101 demoM_2202101 demoMir_2202101

theorem demoR1_0012101 : invRung 7 5 20 [0, 0, 1, 2, 1, 0, 1] [0, 0, 1, 2, 1, 0, 1] 1 2 false = ([2, 2, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0012101 : invRung 7 5 20 [0, 0, 1, 2, 1, 0, 1] [2, 2, 0, 2, 2, 2, 1] 3 1 true = ([2, 2, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_0012101 : fieldCube 7 5 20 [2, 2, 2, 1, 0, 0, 2] = [0, 2, 2, 1, 2, 0, 1] := by
  decide

theorem demoM_0012101 : fieldMul 7 5 20 [0, 2, 2, 1, 2, 0, 1] [0, 0, 1, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0012101 : specInv 7 5 20 [0, 0, 1, 2, 1, 0, 1] = some [0, 2, 2, 1, 2, 0, 1] :=
  specInv_white_7 [0, 0, 1, 2, 1, 0, 1] [2, 2, 0, 2, 2, 2, 1] [2, 2, 2, 1, 0, 0, 2] [0, 2, 2, 1, 2, 0, 1] demoR1_0012101 demoR2_0012101 demoC_0012101 demoM_0012101

theorem demoR1_1012101 : invRung 7 5 20 [1, 0, 1, 2, 1, 0, 1] [1, 0, 1, 2, 1, 0, 1] 1 2 false = ([2, 2, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_1012101 : invRung 7 5 20 [1, 0, 1, 2, 1, 0, 1] [2, 2, 1, 0, 2, 0, 0] 3 1 true = ([0, 1, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_1012101 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 0, 0] = [0, 0, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_1012101 : fieldMul 7 5 20 [0, 0, 0, 1, 0, 0, 1] [1, 0, 1, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1012101 : specInv 7 5 20 [1, 0, 1, 2, 1, 0, 1] = some [0, 0, 0, 1, 0, 0, 1] :=
  specInv_white_7 [1, 0, 1, 2, 1, 0, 1] [2, 2, 1, 0, 2, 0, 0] [0, 1, 1, 0, 0, 0, 0] [0, 0, 0, 1, 0, 0, 1] demoR1_1012101 demoR2_1012101 demoC_1012101 demoM_1012101

theorem demoR1_2012101 : invRung 7 5 20 [2, 0, 1, 2, 1, 0, 1] [2, 0, 1, 2, 1, 0, 1] 1 2 false = ([1, 1, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2012101 : invRung 7 5 20 [2, 0, 1, 2, 1, 0, 1] [1, 1, 0, 0, 2, 2, 0] 3 1 true = ([2, 1, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_2012101 : fieldCube 7 5 20 [2, 1, 1, 1, 1, 0, 1] = [0, 2, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_2012101 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 0, 0] [2, 0, 1, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2012101 : specInv 7 5 20 [2, 0, 1, 2, 1, 0, 1] = some [0, 2, 0, 0, 1, 0, 0] :=
  specInv_white_7 [2, 0, 1, 2, 1, 0, 1] [1, 1, 0, 0, 2, 2, 0] [2, 1, 1, 1, 1, 0, 1] [0, 2, 0, 0, 1, 0, 0] demoR1_2012101 demoR2_2012101 demoC_2012101 demoM_2012101

theorem demoR1_0112101 : invRung 7 5 20 [0, 1, 1, 2, 1, 0, 1] [0, 1, 1, 2, 1, 0, 1] 1 2 false = ([1, 1, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0112101 : invRung 7 5 20 [0, 1, 1, 2, 1, 0, 1] [1, 1, 2, 2, 1, 2, 1] 3 1 true = ([2, 0, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0112101 : fieldCube 7 5 20 [2, 0, 1, 0, 2, 1, 2] = [0, 2, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_0112101 : fieldMul 7 5 20 [0, 2, 2, 1, 0, 2, 1] [0, 1, 1, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0112101 : specInv 7 5 20 [0, 1, 1, 2, 1, 0, 1] = some [0, 2, 2, 1, 0, 2, 1] :=
  specInv_white_7 [0, 1, 1, 2, 1, 0, 1] [1, 1, 2, 2, 1, 2, 1] [2, 0, 1, 0, 2, 1, 2] [0, 2, 2, 1, 0, 2, 1] demoR1_0112101 demoR2_0112101 demoC_0112101 demoM_0112101

theorem demoR1_1112101 : invRung 7 5 20 [1, 1, 1, 2, 1, 0, 1] [1, 1, 1, 2, 1, 0, 1] 1 2 false = ([0, 2, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoR2_1112101 : invRung 7 5 20 [1, 1, 1, 2, 1, 0, 1] [0, 2, 2, 1, 2, 2, 0] 3 1 true = ([2, 0, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1112101 : fieldCube 7 5 20 [2, 0, 2, 1, 0, 2, 1] = [2, 0, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_1112101 : fieldMul 7 5 20 [2, 0, 2, 1, 0, 1, 1] [1, 1, 1, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1112101 : specInv 7 5 20 [1, 1, 1, 2, 1, 0, 1] = some [2, 0, 2, 1, 0, 1, 1] :=
  specInv_white_7 [1, 1, 1, 2, 1, 0, 1] [0, 2, 2, 1, 2, 2, 0] [2, 0, 2, 1, 0, 2, 1] [2, 0, 2, 1, 0, 1, 1] demoR1_1112101 demoR2_1112101 demoC_1112101 demoM_1112101

theorem demoR1_2112101 : invRung 7 5 20 [2, 1, 1, 2, 1, 0, 1] [2, 1, 1, 2, 1, 0, 1] 1 2 false = ([0, 1, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_2112101 : invRung 7 5 20 [2, 1, 1, 2, 1, 0, 1] [0, 1, 2, 1, 0, 2, 0] 3 1 true = ([1, 1, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2112101 : fieldCube 7 5 20 [1, 1, 1, 2, 1, 2, 2] = [2, 2, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_2112101 : fieldMul 7 5 20 [2, 2, 2, 1, 1, 1, 2] [2, 1, 1, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2112101 : specInv 7 5 20 [2, 1, 1, 2, 1, 0, 1] = some [2, 2, 2, 1, 1, 1, 2] :=
  specInv_white_7 [2, 1, 1, 2, 1, 0, 1] [0, 1, 2, 1, 0, 2, 0] [1, 1, 1, 2, 1, 2, 2] [2, 2, 2, 1, 1, 1, 2] demoR1_2112101 demoR2_2112101 demoC_2112101 demoM_2112101

theorem demoR1_0212101 : invRung 7 5 20 [0, 2, 1, 2, 1, 0, 1] [0, 2, 1, 2, 1, 0, 1] 1 2 false = ([0, 0, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_0212101 : invRung 7 5 20 [0, 2, 1, 2, 1, 0, 1] [0, 0, 2, 0, 2, 1, 2] 3 1 true = ([0, 1, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_0212101 : fieldCube 7 5 20 [0, 1, 1, 2, 0, 2, 0] = [1, 2, 1, 1, 2, 1, 2] := by
  decide

theorem demoM_0212101 : fieldMul 7 5 20 [1, 2, 1, 1, 2, 1, 2] [0, 2, 1, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0212101 : specInv 7 5 20 [0, 2, 1, 2, 1, 0, 1] = some [1, 2, 1, 1, 2, 1, 2] :=
  specInv_white_7 [0, 2, 1, 2, 1, 0, 1] [0, 0, 2, 0, 2, 1, 2] [0, 1, 1, 2, 0, 2, 0] [1, 2, 1, 1, 2, 1, 2] demoR1_0212101 demoR2_0212101 demoC_0212101 demoM_0212101

theorem demoR1_1212101 : invRung 7 5 20 [1, 2, 1, 2, 1, 0, 1] [1, 2, 1, 2, 1, 0, 1] 1 2 false = ([1, 0, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoR2_1212101 : invRung 7 5 20 [1, 2, 1, 2, 1, 0, 1] [1, 0, 1, 1, 0, 2, 2] 3 1 true = ([0, 2, 0, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_1212101 : fieldCube 7 5 20 [0, 2, 0, 2, 2, 0, 2] = [2, 1, 0, 0, 2, 0, 1] := by
  decide

theorem demoM_1212101 : fieldMul 7 5 20 [2, 1, 0, 0, 2, 0, 1] [1, 2, 1, 2, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1212101 : mirrorTrits [2, 1, 0, 0, 2, 0, 1] = [1, 2, 0, 0, 1, 0, 2] := by
  decide

theorem demoInv_1212101 : specInv 7 5 20 [1, 2, 1, 2, 1, 0, 1] = some [1, 2, 0, 0, 1, 0, 2] :=
  specInv_mirror_7 [1, 2, 1, 2, 1, 0, 1] [1, 0, 1, 1, 0, 2, 2] [0, 2, 0, 2, 2, 0, 2] [2, 1, 0, 0, 2, 0, 1] [1, 2, 0, 0, 1, 0, 2] demoR1_1212101 demoR2_1212101 demoC_1212101 demoM_1212101 demoMir_1212101

theorem demoR1_2212101 : invRung 7 5 20 [2, 2, 1, 2, 1, 0, 1] [2, 2, 1, 2, 1, 0, 1] 1 2 false = ([2, 0, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_2212101 : invRung 7 5 20 [2, 2, 1, 2, 1, 0, 1] [2, 0, 2, 2, 1, 2, 0] 3 1 true = ([0, 1, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_2212101 : fieldCube 7 5 20 [0, 1, 0, 2, 0, 1, 1] = [0, 2, 2, 2, 2, 1, 0] := by
  decide

theorem demoM_2212101 : fieldMul 7 5 20 [0, 2, 2, 2, 2, 1, 0] [2, 2, 1, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2212101 : specInv 7 5 20 [2, 2, 1, 2, 1, 0, 1] = some [0, 2, 2, 2, 2, 1, 0] :=
  specInv_white_7 [2, 2, 1, 2, 1, 0, 1] [2, 0, 2, 2, 1, 2, 0] [0, 1, 0, 2, 0, 1, 1] [0, 2, 2, 2, 2, 1, 0] demoR1_2212101 demoR2_2212101 demoC_2212101 demoM_2212101

theorem demoR1_0022101 : invRung 7 5 20 [0, 0, 2, 2, 1, 0, 1] [0, 0, 2, 2, 1, 0, 1] 1 2 false = ([2, 0, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_0022101 : invRung 7 5 20 [0, 0, 2, 2, 1, 0, 1] [2, 0, 0, 1, 1, 2, 2] 3 1 true = ([1, 0, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_0022101 : fieldCube 7 5 20 [1, 0, 1, 2, 1, 2, 0] = [2, 0, 1, 1, 2, 2, 0] := by
  decide

theorem demoM_0022101 : fieldMul 7 5 20 [2, 0, 1, 1, 2, 2, 0] [0, 0, 2, 2, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022101 : mirrorTrits [2, 0, 1, 1, 2, 2, 0] = [1, 0, 2, 2, 1, 1, 0] := by
  decide

theorem demoInv_0022101 : specInv 7 5 20 [0, 0, 2, 2, 1, 0, 1] = some [1, 0, 2, 2, 1, 1, 0] :=
  specInv_mirror_7 [0, 0, 2, 2, 1, 0, 1] [2, 0, 0, 1, 1, 2, 2] [1, 0, 1, 2, 1, 2, 0] [2, 0, 1, 1, 2, 2, 0] [1, 0, 2, 2, 1, 1, 0] demoR1_0022101 demoR2_0022101 demoC_0022101 demoM_0022101 demoMir_0022101

theorem demoR1_1022101 : invRung 7 5 20 [1, 0, 2, 2, 1, 0, 1] [1, 0, 2, 2, 1, 0, 1] 1 2 false = ([0, 1, 2, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_1022101 : invRung 7 5 20 [1, 0, 2, 2, 1, 0, 1] [0, 1, 2, 0, 0, 1, 0] 3 1 true = ([2, 0, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_1022101 : fieldCube 7 5 20 [2, 0, 2, 2, 0, 2, 0] = [0, 2, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_1022101 : fieldMul 7 5 20 [0, 2, 1, 0, 2, 1, 0] [1, 0, 2, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1022101 : specInv 7 5 20 [1, 0, 2, 2, 1, 0, 1] = some [0, 2, 1, 0, 2, 1, 0] :=
  specInv_white_7 [1, 0, 2, 2, 1, 0, 1] [0, 1, 2, 0, 0, 1, 0] [2, 0, 2, 2, 0, 2, 0] [0, 2, 1, 0, 2, 1, 0] demoR1_1022101 demoR2_1022101 demoC_1022101 demoM_1022101

theorem demoR1_2022101 : invRung 7 5 20 [2, 0, 2, 2, 1, 0, 1] [2, 0, 2, 2, 1, 0, 1] 1 2 false = ([0, 0, 2, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_2022101 : invRung 7 5 20 [2, 0, 2, 2, 1, 0, 1] [0, 0, 2, 0, 1, 0, 0] 3 1 true = ([1, 1, 1, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2022101 : fieldCube 7 5 20 [1, 1, 1, 1, 1, 2, 1] = [1, 1, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_2022101 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 2, 1] [2, 0, 2, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2022101 : specInv 7 5 20 [2, 0, 2, 2, 1, 0, 1] = some [1, 1, 2, 0, 0, 2, 1] :=
  specInv_white_7 [2, 0, 2, 2, 1, 0, 1] [0, 0, 2, 0, 1, 0, 0] [1, 1, 1, 1, 1, 2, 1] [1, 1, 2, 0, 0, 2, 1] demoR1_2022101 demoR2_2022101 demoC_2022101 demoM_2022101

theorem demoR1_0122101 : invRung 7 5 20 [0, 1, 2, 2, 1, 0, 1] [0, 1, 2, 2, 1, 0, 1] 1 2 false = ([0, 1, 2, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0122101 : invRung 7 5 20 [0, 1, 2, 2, 1, 0, 1] [0, 1, 2, 2, 1, 2, 1] 3 1 true = ([1, 2, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_0122101 : fieldCube 7 5 20 [1, 2, 2, 1, 0, 2, 1] = [1, 0, 2, 0, 0, 1, 1] := by
  decide

theorem demoM_0122101 : fieldMul 7 5 20 [1, 0, 2, 0, 0, 1, 1] [0, 1, 2, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0122101 : specInv 7 5 20 [0, 1, 2, 2, 1, 0, 1] = some [1, 0, 2, 0, 0, 1, 1] :=
  specInv_white_7 [0, 1, 2, 2, 1, 0, 1] [0, 1, 2, 2, 1, 2, 1] [1, 2, 2, 1, 0, 2, 1] [1, 0, 2, 0, 0, 1, 1] demoR1_0122101 demoR2_0122101 demoC_0122101 demoM_0122101

theorem demoR1_1122101 : invRung 7 5 20 [1, 1, 2, 2, 1, 0, 1] [1, 1, 2, 2, 1, 0, 1] 1 2 false = ([0, 2, 1, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_1122101 : invRung 7 5 20 [1, 1, 2, 2, 1, 0, 1] [0, 2, 1, 1, 2, 1, 1] 3 1 true = ([2, 1, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_1122101 : fieldCube 7 5 20 [2, 1, 1, 2, 2, 2, 1] = [0, 2, 0, 1, 0, 1, 2] := by
  decide

theorem demoM_1122101 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 1, 2] [1, 1, 2, 2, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122101 : mirrorTrits [0, 2, 0, 1, 0, 1, 2] = [0, 1, 0, 2, 0, 2, 1] := by
  decide

theorem demoInv_1122101 : specInv 7 5 20 [1, 1, 2, 2, 1, 0, 1] = some [0, 1, 0, 2, 0, 2, 1] :=
  specInv_mirror_7 [1, 1, 2, 2, 1, 0, 1] [0, 2, 1, 1, 2, 1, 1] [2, 1, 1, 2, 2, 2, 1] [0, 2, 0, 1, 0, 1, 2] [0, 1, 0, 2, 0, 2, 1] demoR1_1122101 demoR2_1122101 demoC_1122101 demoM_1122101 demoMir_1122101

theorem demoR1_2122101 : invRung 7 5 20 [2, 1, 2, 2, 1, 0, 1] [2, 1, 2, 2, 1, 0, 1] 1 2 false = ([1, 0, 0, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_2122101 : invRung 7 5 20 [2, 1, 2, 2, 1, 0, 1] [1, 0, 0, 0, 2, 2, 0] 3 1 true = ([1, 1, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_2122101 : fieldCube 7 5 20 [1, 1, 1, 2, 1, 0, 1] = [0, 2, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_2122101 : fieldMul 7 5 20 [0, 2, 1, 0, 1, 1, 0] [2, 1, 2, 2, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122101 : mirrorTrits [0, 2, 1, 0, 1, 1, 0] = [0, 1, 2, 0, 2, 2, 0] := by
  decide

theorem demoInv_2122101 : specInv 7 5 20 [2, 1, 2, 2, 1, 0, 1] = some [0, 1, 2, 0, 2, 2, 0] :=
  specInv_mirror_7 [2, 1, 2, 2, 1, 0, 1] [1, 0, 0, 0, 2, 2, 0] [1, 1, 1, 2, 1, 0, 1] [0, 2, 1, 0, 1, 1, 0] [0, 1, 2, 0, 2, 2, 0] demoR1_2122101 demoR2_2122101 demoC_2122101 demoM_2122101 demoMir_2122101

theorem demoR1_0222101 : invRung 7 5 20 [0, 2, 2, 2, 1, 0, 1] [0, 2, 2, 2, 1, 0, 1] 1 2 false = ([2, 1, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_0222101 : invRung 7 5 20 [0, 2, 2, 2, 1, 0, 1] [2, 1, 0, 1, 0, 2, 1] 3 1 true = ([1, 0, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0222101 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 2, 2] = [1, 0, 1, 1, 1, 1, 2] := by
  decide

theorem demoM_0222101 : fieldMul 7 5 20 [1, 0, 1, 1, 1, 1, 2] [0, 2, 2, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0222101 : specInv 7 5 20 [0, 2, 2, 2, 1, 0, 1] = some [1, 0, 1, 1, 1, 1, 2] :=
  specInv_white_7 [0, 2, 2, 2, 1, 0, 1] [2, 1, 0, 1, 0, 2, 1] [1, 0, 0, 1, 2, 2, 2] [1, 0, 1, 1, 1, 1, 2] demoR1_0222101 demoR2_0222101 demoC_0222101 demoM_0222101

theorem demoR1_1222101 : invRung 7 5 20 [1, 2, 2, 2, 1, 0, 1] [1, 2, 2, 2, 1, 0, 1] 1 2 false = ([1, 0, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_1222101 : invRung 7 5 20 [1, 2, 2, 2, 1, 0, 1] [1, 0, 2, 1, 2, 0, 1] 3 1 true = ([1, 2, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1222101 : fieldCube 7 5 20 [1, 2, 1, 1, 0, 2, 1] = [1, 0, 2, 0, 0, 1, 0] := by
  decide

theorem demoM_1222101 : fieldMul 7 5 20 [1, 0, 2, 0, 0, 1, 0] [1, 2, 2, 2, 1, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222101 : mirrorTrits [1, 0, 2, 0, 0, 1, 0] = [2, 0, 1, 0, 0, 2, 0] := by
  decide

theorem demoInv_1222101 : specInv 7 5 20 [1, 2, 2, 2, 1, 0, 1] = some [2, 0, 1, 0, 0, 2, 0] :=
  specInv_mirror_7 [1, 2, 2, 2, 1, 0, 1] [1, 0, 2, 1, 2, 0, 1] [1, 2, 1, 1, 0, 2, 1] [1, 0, 2, 0, 0, 1, 0] [2, 0, 1, 0, 0, 2, 0] demoR1_1222101 demoR2_1222101 demoC_1222101 demoM_1222101 demoMir_1222101

theorem demoR1_2222101 : invRung 7 5 20 [2, 2, 2, 2, 1, 0, 1] [2, 2, 2, 2, 1, 0, 1] 1 2 false = ([0, 1, 0, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_2222101 : invRung 7 5 20 [2, 2, 2, 2, 1, 0, 1] [0, 1, 0, 0, 0, 2, 0] 3 1 true = ([1, 0, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_2222101 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 0, 1] = [1, 1, 2, 1, 1, 1, 2] := by
  decide

theorem demoM_2222101 : fieldMul 7 5 20 [1, 1, 2, 1, 1, 1, 2] [2, 2, 2, 2, 1, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2222101 : specInv 7 5 20 [2, 2, 2, 2, 1, 0, 1] = some [1, 1, 2, 1, 1, 1, 2] :=
  specInv_white_7 [2, 2, 2, 2, 1, 0, 1] [0, 1, 0, 0, 0, 2, 0] [1, 0, 1, 0, 0, 0, 1] [1, 1, 2, 1, 1, 1, 2] demoR1_2222101 demoR2_2222101 demoC_2222101 demoM_2222101

theorem demoR1_0000201 : invRung 7 5 20 [0, 0, 0, 0, 2, 0, 1] [0, 0, 0, 0, 2, 0, 1] 1 2 false = ([0, 1, 2, 0, 0, 0, 1], 3) := by
  decide

theorem demoR2_0000201 : invRung 7 5 20 [0, 0, 0, 0, 2, 0, 1] [0, 1, 2, 0, 0, 0, 1] 3 1 true = ([2, 1, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0000201 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 2, 1] = [0, 1, 0, 0, 0, 0, 0] := by
  decide

theorem demoM_0000201 : fieldMul 7 5 20 [0, 1, 0, 0, 0, 0, 0] [0, 0, 0, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0000201 : specInv 7 5 20 [0, 0, 0, 0, 2, 0, 1] = some [0, 1, 0, 0, 0, 0, 0] :=
  specInv_white_7 [0, 0, 0, 0, 2, 0, 1] [0, 1, 2, 0, 0, 0, 1] [2, 1, 0, 2, 1, 2, 1] [0, 1, 0, 0, 0, 0, 0] demoR1_0000201 demoR2_0000201 demoC_0000201 demoM_0000201

theorem demoR1_1000201 : invRung 7 5 20 [1, 0, 0, 0, 2, 0, 1] [1, 0, 0, 0, 2, 0, 1] 1 2 false = ([0, 1, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_1000201 : invRung 7 5 20 [1, 0, 0, 0, 2, 0, 1] [0, 1, 0, 1, 1, 2, 2] 3 1 true = ([2, 1, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_1000201 : fieldCube 7 5 20 [2, 1, 1, 1, 0, 1, 2] = [1, 0, 0, 0, 0, 1, 2] := by
  decide

theorem demoM_1000201 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 1, 2] [1, 0, 0, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1000201 : specInv 7 5 20 [1, 0, 0, 0, 2, 0, 1] = some [1, 0, 0, 0, 0, 1, 2] :=
  specInv_white_7 [1, 0, 0, 0, 2, 0, 1] [0, 1, 0, 1, 1, 2, 2] [2, 1, 1, 1, 0, 1, 2] [1, 0, 0, 0, 0, 1, 2] demoR1_1000201 demoR2_1000201 demoC_1000201 demoM_1000201

theorem demoR1_2000201 : invRung 7 5 20 [2, 0, 0, 0, 2, 0, 1] [2, 0, 0, 0, 2, 0, 1] 1 2 false = ([0, 0, 2, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_2000201 : invRung 7 5 20 [2, 0, 0, 0, 2, 0, 1] [0, 0, 2, 1, 2, 0, 2] 3 1 true = ([2, 1, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_2000201 : fieldCube 7 5 20 [2, 1, 0, 1, 0, 1, 2] = [1, 0, 0, 0, 0, 1, 1] := by
  decide

theorem demoM_2000201 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 1, 1] [2, 0, 0, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000201 : mirrorTrits [1, 0, 0, 0, 0, 1, 1] = [2, 0, 0, 0, 0, 2, 2] := by
  decide

theorem demoInv_2000201 : specInv 7 5 20 [2, 0, 0, 0, 2, 0, 1] = some [2, 0, 0, 0, 0, 2, 2] :=
  specInv_mirror_7 [2, 0, 0, 0, 2, 0, 1] [0, 0, 2, 1, 2, 0, 2] [2, 1, 0, 1, 0, 1, 2] [1, 0, 0, 0, 0, 1, 1] [2, 0, 0, 0, 0, 2, 2] demoR1_2000201 demoR2_2000201 demoC_2000201 demoM_2000201 demoMir_2000201

theorem demoR1_0100201 : invRung 7 5 20 [0, 1, 0, 0, 2, 0, 1] [0, 1, 0, 0, 2, 0, 1] 1 2 false = ([0, 2, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_0100201 : invRung 7 5 20 [0, 1, 0, 0, 2, 0, 1] [0, 2, 2, 2, 1, 0, 0] 3 1 true = ([2, 2, 2, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0100201 : fieldCube 7 5 20 [2, 2, 2, 1, 0, 1, 0] = [1, 1, 2, 2, 1, 2, 1] := by
  decide

theorem demoM_0100201 : fieldMul 7 5 20 [1, 1, 2, 2, 1, 2, 1] [0, 1, 0, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0100201 : mirrorTrits [1, 1, 2, 2, 1, 2, 1] = [2, 2, 1, 1, 2, 1, 2] := by
  decide

theorem demoInv_0100201 : specInv 7 5 20 [0, 1, 0, 0, 2, 0, 1] = some [2, 2, 1, 1, 2, 1, 2] :=
  specInv_mirror_7 [0, 1, 0, 0, 2, 0, 1] [0, 2, 2, 2, 1, 0, 0] [2, 2, 2, 1, 0, 1, 0] [1, 1, 2, 2, 1, 2, 1] [2, 2, 1, 1, 2, 1, 2] demoR1_0100201 demoR2_0100201 demoC_0100201 demoM_0100201 demoMir_0100201

theorem demoR1_1100201 : invRung 7 5 20 [1, 1, 0, 0, 2, 0, 1] [1, 1, 0, 0, 2, 0, 1] 1 2 false = ([1, 1, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_1100201 : invRung 7 5 20 [1, 1, 0, 0, 2, 0, 1] [1, 1, 0, 2, 2, 2, 2] 3 1 true = ([2, 1, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_1100201 : fieldCube 7 5 20 [2, 1, 0, 2, 0, 1, 1] = [2, 2, 2, 2, 2, 1, 0] := by
  decide

theorem demoM_1100201 : fieldMul 7 5 20 [2, 2, 2, 2, 2, 1, 0] [1, 1, 0, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1100201 : specInv 7 5 20 [1, 1, 0, 0, 2, 0, 1] = some [2, 2, 2, 2, 2, 1, 0] :=
  specInv_white_7 [1, 1, 0, 0, 2, 0, 1] [1, 1, 0, 2, 2, 2, 2] [2, 1, 0, 2, 0, 1, 1] [2, 2, 2, 2, 2, 1, 0] demoR1_1100201 demoR2_1100201 demoC_1100201 demoM_1100201

theorem demoR1_2100201 : invRung 7 5 20 [2, 1, 0, 0, 2, 0, 1] [2, 1, 0, 0, 2, 0, 1] 1 2 false = ([1, 1, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_2100201 : invRung 7 5 20 [2, 1, 0, 0, 2, 0, 1] [1, 1, 1, 0, 0, 2, 0] 3 1 true = ([2, 1, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_2100201 : fieldCube 7 5 20 [2, 1, 0, 2, 2, 1, 1] = [2, 1, 2, 1, 2, 0, 2] := by
  decide

theorem demoM_2100201 : fieldMul 7 5 20 [2, 1, 2, 1, 2, 0, 2] [2, 1, 0, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2100201 : specInv 7 5 20 [2, 1, 0, 0, 2, 0, 1] = some [2, 1, 2, 1, 2, 0, 2] :=
  specInv_white_7 [2, 1, 0, 0, 2, 0, 1] [1, 1, 1, 0, 0, 2, 0] [2, 1, 0, 2, 2, 1, 1] [2, 1, 2, 1, 2, 0, 2] demoR1_2100201 demoR2_2100201 demoC_2100201 demoM_2100201

theorem demoR1_0200201 : invRung 7 5 20 [0, 2, 0, 0, 2, 0, 1] [0, 2, 0, 0, 2, 0, 1] 1 2 false = ([2, 0, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0200201 : invRung 7 5 20 [0, 2, 0, 0, 2, 0, 1] [2, 0, 0, 1, 1, 1, 2] 3 1 true = ([0, 0, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_0200201 : fieldCube 7 5 20 [0, 0, 1, 0, 0, 0, 0] = [0, 0, 0, 0, 0, 0, 1] := by
  decide

theorem demoM_0200201 : fieldMul 7 5 20 [0, 0, 0, 0, 0, 0, 1] [0, 2, 0, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0200201 : mirrorTrits [0, 0, 0, 0, 0, 0, 1] = [0, 0, 0, 0, 0, 0, 2] := by
  decide

theorem demoInv_0200201 : specInv 7 5 20 [0, 2, 0, 0, 2, 0, 1] = some [0, 0, 0, 0, 0, 0, 2] :=
  specInv_mirror_7 [0, 2, 0, 0, 2, 0, 1] [2, 0, 0, 1, 1, 1, 2] [0, 0, 1, 0, 0, 0, 0] [0, 0, 0, 0, 0, 0, 1] [0, 0, 0, 0, 0, 0, 2] demoR1_0200201 demoR2_0200201 demoC_0200201 demoM_0200201 demoMir_0200201

theorem demoR1_1200201 : invRung 7 5 20 [1, 2, 0, 0, 2, 0, 1] [1, 2, 0, 0, 2, 0, 1] 1 2 false = ([1, 2, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_1200201 : invRung 7 5 20 [1, 2, 0, 0, 2, 0, 1] [1, 2, 1, 1, 1, 2, 0] 3 1 true = ([1, 0, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_1200201 : fieldCube 7 5 20 [1, 0, 0, 0, 0, 1, 0] = [2, 1, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_1200201 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 1, 2] [1, 2, 0, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1200201 : specInv 7 5 20 [1, 2, 0, 0, 2, 0, 1] = some [2, 1, 1, 0, 1, 1, 2] :=
  specInv_white_7 [1, 2, 0, 0, 2, 0, 1] [1, 2, 1, 1, 1, 2, 0] [1, 0, 0, 0, 0, 1, 0] [2, 1, 1, 0, 1, 1, 2] demoR1_1200201 demoR2_1200201 demoC_1200201 demoM_1200201

theorem demoR1_2200201 : invRung 7 5 20 [2, 2, 0, 0, 2, 0, 1] [2, 2, 0, 0, 2, 0, 1] 1 2 false = ([1, 1, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_2200201 : invRung 7 5 20 [2, 2, 0, 0, 2, 0, 1] [1, 1, 1, 1, 1, 0, 0] 3 1 true = ([1, 1, 1, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_2200201 : fieldCube 7 5 20 [1, 1, 1, 2, 2, 2, 2] = [2, 0, 2, 2, 1, 2, 0] := by
  decide

theorem demoM_2200201 : fieldMul 7 5 20 [2, 0, 2, 2, 1, 2, 0] [2, 2, 0, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2200201 : specInv 7 5 20 [2, 2, 0, 0, 2, 0, 1] = some [2, 0, 2, 2, 1, 2, 0] :=
  specInv_white_7 [2, 2, 0, 0, 2, 0, 1] [1, 1, 1, 1, 1, 0, 0] [1, 1, 1, 2, 2, 2, 2] [2, 0, 2, 2, 1, 2, 0] demoR1_2200201 demoR2_2200201 demoC_2200201 demoM_2200201

theorem demoR1_0010201 : invRung 7 5 20 [0, 0, 1, 0, 2, 0, 1] [0, 0, 1, 0, 2, 0, 1] 1 2 false = ([2, 0, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_0010201 : invRung 7 5 20 [0, 0, 1, 0, 2, 0, 1] [2, 0, 0, 2, 1, 1, 2] 3 1 true = ([0, 1, 2, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0010201 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 2, 2] = [2, 2, 0, 1, 1, 2, 0] := by
  decide

theorem demoM_0010201 : fieldMul 7 5 20 [2, 2, 0, 1, 1, 2, 0] [0, 0, 1, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0010201 : specInv 7 5 20 [0, 0, 1, 0, 2, 0, 1] = some [2, 2, 0, 1, 1, 2, 0] :=
  specInv_white_7 [0, 0, 1, 0, 2, 0, 1] [2, 0, 0, 2, 1, 1, 2] [0, 1, 2, 0, 1, 2, 2] [2, 2, 0, 1, 1, 2, 0] demoR1_0010201 demoR2_0010201 demoC_0010201 demoM_0010201

theorem demoR1_1010201 : invRung 7 5 20 [1, 0, 1, 0, 2, 0, 1] [1, 0, 1, 0, 2, 0, 1] 1 2 false = ([0, 1, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_1010201 : invRung 7 5 20 [1, 0, 1, 0, 2, 0, 1] [0, 1, 1, 0, 2, 0, 0] 3 1 true = ([1, 0, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_1010201 : fieldCube 7 5 20 [1, 0, 1, 2, 2, 1, 1] = [1, 1, 2, 0, 2, 0, 0] := by
  decide

theorem demoM_1010201 : fieldMul 7 5 20 [1, 1, 2, 0, 2, 0, 0] [1, 0, 1, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1010201 : mirrorTrits [1, 1, 2, 0, 2, 0, 0] = [2, 2, 1, 0, 1, 0, 0] := by
  decide

theorem demoInv_1010201 : specInv 7 5 20 [1, 0, 1, 0, 2, 0, 1] = some [2, 2, 1, 0, 1, 0, 0] :=
  specInv_mirror_7 [1, 0, 1, 0, 2, 0, 1] [0, 1, 1, 0, 2, 0, 0] [1, 0, 1, 2, 2, 1, 1] [1, 1, 2, 0, 2, 0, 0] [2, 2, 1, 0, 1, 0, 0] demoR1_1010201 demoR2_1010201 demoC_1010201 demoM_1010201 demoMir_1010201

theorem demoR1_2010201 : invRung 7 5 20 [2, 0, 1, 0, 2, 0, 1] [2, 0, 1, 0, 2, 0, 1] 1 2 false = ([1, 0, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_2010201 : invRung 7 5 20 [2, 0, 1, 0, 2, 0, 1] [1, 0, 0, 2, 2, 0, 1] 3 1 true = ([1, 0, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_2010201 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 2, 2] = [2, 2, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_2010201 : fieldMul 7 5 20 [2, 2, 2, 0, 1, 1, 0] [2, 0, 1, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2010201 : specInv 7 5 20 [2, 0, 1, 0, 2, 0, 1] = some [2, 2, 2, 0, 1, 1, 0] :=
  specInv_white_7 [2, 0, 1, 0, 2, 0, 1] [1, 0, 0, 2, 2, 0, 1] [1, 0, 2, 2, 1, 2, 2] [2, 2, 2, 0, 1, 1, 0] demoR1_2010201 demoR2_2010201 demoC_2010201 demoM_2010201

theorem demoR1_0110201 : invRung 7 5 20 [0, 1, 1, 0, 2, 0, 1] [0, 1, 1, 0, 2, 0, 1] 1 2 false = ([2, 0, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_0110201 : invRung 7 5 20 [0, 1, 1, 0, 2, 0, 1] [2, 0, 1, 2, 2, 0, 1] 3 1 true = ([0, 0, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_0110201 : fieldCube 7 5 20 [0, 0, 2, 2, 2, 1, 2] = [0, 2, 1, 1, 0, 1, 2] := by
  decide

theorem demoM_0110201 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 1, 2] [0, 1, 1, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110201 : mirrorTrits [0, 2, 1, 1, 0, 1, 2] = [0, 1, 2, 2, 0, 2, 1] := by
  decide

theorem demoInv_0110201 : specInv 7 5 20 [0, 1, 1, 0, 2, 0, 1] = some [0, 1, 2, 2, 0, 2, 1] :=
  specInv_mirror_7 [0, 1, 1, 0, 2, 0, 1] [2, 0, 1, 2, 2, 0, 1] [0, 0, 2, 2, 2, 1, 2] [0, 2, 1, 1, 0, 1, 2] [0, 1, 2, 2, 0, 2, 1] demoR1_0110201 demoR2_0110201 demoC_0110201 demoM_0110201 demoMir_0110201

theorem demoR1_1110201 : invRung 7 5 20 [1, 1, 1, 0, 2, 0, 1] [1, 1, 1, 0, 2, 0, 1] 1 2 false = ([1, 2, 0, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_1110201 : invRung 7 5 20 [1, 1, 1, 0, 2, 0, 1] [1, 2, 0, 1, 1, 0, 2] 3 1 true = ([2, 1, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1110201 : fieldCube 7 5 20 [2, 1, 2, 1, 2, 1, 0] = [1, 0, 2, 0, 1, 1, 0] := by
  decide

theorem demoM_1110201 : fieldMul 7 5 20 [1, 0, 2, 0, 1, 1, 0] [1, 1, 1, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1110201 : mirrorTrits [1, 0, 2, 0, 1, 1, 0] = [2, 0, 1, 0, 2, 2, 0] := by
  decide

theorem demoInv_1110201 : specInv 7 5 20 [1, 1, 1, 0, 2, 0, 1] = some [2, 0, 1, 0, 2, 2, 0] :=
  specInv_mirror_7 [1, 1, 1, 0, 2, 0, 1] [1, 2, 0, 1, 1, 0, 2] [2, 1, 2, 1, 2, 1, 0] [1, 0, 2, 0, 1, 1, 0] [2, 0, 1, 0, 2, 2, 0] demoR1_1110201 demoR2_1110201 demoC_1110201 demoM_1110201 demoMir_1110201

theorem demoR1_2110201 : invRung 7 5 20 [2, 1, 1, 0, 2, 0, 1] [2, 1, 1, 0, 2, 0, 1] 1 2 false = ([2, 1, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2110201 : invRung 7 5 20 [2, 1, 1, 0, 2, 0, 1] [2, 1, 2, 0, 2, 0, 0] 3 1 true = ([2, 0, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_2110201 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 2, 0] = [1, 0, 2, 1, 2, 0, 0] := by
  decide

theorem demoM_2110201 : fieldMul 7 5 20 [1, 0, 2, 1, 2, 0, 0] [2, 1, 1, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110201 : mirrorTrits [1, 0, 2, 1, 2, 0, 0] = [2, 0, 1, 2, 1, 0, 0] := by
  decide

theorem demoInv_2110201 : specInv 7 5 20 [2, 1, 1, 0, 2, 0, 1] = some [2, 0, 1, 2, 1, 0, 0] :=
  specInv_mirror_7 [2, 1, 1, 0, 2, 0, 1] [2, 1, 2, 0, 2, 0, 0] [2, 0, 1, 0, 1, 2, 0] [1, 0, 2, 1, 2, 0, 0] [2, 0, 1, 2, 1, 0, 0] demoR1_2110201 demoR2_2110201 demoC_2110201 demoM_2110201 demoMir_2110201

theorem demoR1_0210201 : invRung 7 5 20 [0, 2, 1, 0, 2, 0, 1] [0, 2, 1, 0, 2, 0, 1] 1 2 false = ([2, 2, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_0210201 : invRung 7 5 20 [0, 2, 1, 0, 2, 0, 1] [2, 2, 1, 2, 2, 1, 0] 3 1 true = ([2, 2, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_0210201 : fieldCube 7 5 20 [2, 2, 0, 2, 2, 0, 1] = [1, 0, 1, 2, 1, 2, 0] := by
  decide

theorem demoM_0210201 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 2, 0] [0, 2, 1, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210201 : mirrorTrits [1, 0, 1, 2, 1, 2, 0] = [2, 0, 2, 1, 2, 1, 0] := by
  decide

theorem demoInv_0210201 : specInv 7 5 20 [0, 2, 1, 0, 2, 0, 1] = some [2, 0, 2, 1, 2, 1, 0] :=
  specInv_mirror_7 [0, 2, 1, 0, 2, 0, 1] [2, 2, 1, 2, 2, 1, 0] [2, 2, 0, 2, 2, 0, 1] [1, 0, 1, 2, 1, 2, 0] [2, 0, 2, 1, 2, 1, 0] demoR1_0210201 demoR2_0210201 demoC_0210201 demoM_0210201 demoMir_0210201

theorem demoR1_1210201 : invRung 7 5 20 [1, 2, 1, 0, 2, 0, 1] [1, 2, 1, 0, 2, 0, 1] 1 2 false = ([2, 0, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_1210201 : invRung 7 5 20 [1, 2, 1, 0, 2, 0, 1] [2, 0, 1, 0, 1, 1, 2] 3 1 true = ([0, 2, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_1210201 : fieldCube 7 5 20 [0, 2, 0, 2, 0, 0, 0] = [2, 0, 2, 2, 0, 2, 0] := by
  decide

theorem demoM_1210201 : fieldMul 7 5 20 [2, 0, 2, 2, 0, 2, 0] [1, 2, 1, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1210201 : specInv 7 5 20 [1, 2, 1, 0, 2, 0, 1] = some [2, 0, 2, 2, 0, 2, 0] :=
  specInv_white_7 [1, 2, 1, 0, 2, 0, 1] [2, 0, 1, 0, 1, 1, 2] [0, 2, 0, 2, 0, 0, 0] [2, 0, 2, 2, 0, 2, 0] demoR1_1210201 demoR2_1210201 demoC_1210201 demoM_1210201

theorem demoR1_2210201 : invRung 7 5 20 [2, 2, 1, 0, 2, 0, 1] [2, 2, 1, 0, 2, 0, 1] 1 2 false = ([0, 0, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_2210201 : invRung 7 5 20 [2, 2, 1, 0, 2, 0, 1] [0, 0, 0, 0, 2, 0, 1] 3 1 true = ([1, 2, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_2210201 : fieldCube 7 5 20 [1, 2, 1, 1, 0, 2, 2] = [1, 1, 1, 1, 1, 2, 1] := by
  decide

theorem demoM_2210201 : fieldMul 7 5 20 [1, 1, 1, 1, 1, 2, 1] [2, 2, 1, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2210201 : specInv 7 5 20 [2, 2, 1, 0, 2, 0, 1] = some [1, 1, 1, 1, 1, 2, 1] :=
  specInv_white_7 [2, 2, 1, 0, 2, 0, 1] [0, 0, 0, 0, 2, 0, 1] [1, 2, 1, 1, 0, 2, 2] [1, 1, 1, 1, 1, 2, 1] demoR1_2210201 demoR2_2210201 demoC_2210201 demoM_2210201

theorem demoR1_0020201 : invRung 7 5 20 [0, 0, 2, 0, 2, 0, 1] [0, 0, 2, 0, 2, 0, 1] 1 2 false = ([2, 1, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_0020201 : invRung 7 5 20 [0, 0, 2, 0, 2, 0, 1] [2, 1, 1, 2, 1, 0, 2] 3 1 true = ([1, 0, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0020201 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 1, 0] = [0, 1, 2, 0, 1, 2, 2] := by
  decide

theorem demoM_0020201 : fieldMul 7 5 20 [0, 1, 2, 0, 1, 2, 2] [0, 0, 2, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020201 : mirrorTrits [0, 1, 2, 0, 1, 2, 2] = [0, 2, 1, 0, 2, 1, 1] := by
  decide

theorem demoInv_0020201 : specInv 7 5 20 [0, 0, 2, 0, 2, 0, 1] = some [0, 2, 1, 0, 2, 1, 1] :=
  specInv_mirror_7 [0, 0, 2, 0, 2, 0, 1] [2, 1, 1, 2, 1, 0, 2] [1, 0, 0, 1, 0, 1, 0] [0, 1, 2, 0, 1, 2, 2] [0, 2, 1, 0, 2, 1, 1] demoR1_0020201 demoR2_0020201 demoC_0020201 demoM_0020201 demoMir_0020201

theorem demoR1_1020201 : invRung 7 5 20 [1, 0, 2, 0, 2, 0, 1] [1, 0, 2, 0, 2, 0, 1] 1 2 false = ([0, 0, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_1020201 : invRung 7 5 20 [1, 0, 2, 0, 2, 0, 1] [0, 0, 0, 0, 2, 2, 2] 3 1 true = ([0, 1, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoC_1020201 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 2, 2] = [1, 0, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_1020201 : fieldMul 7 5 20 [1, 0, 2, 2, 1, 2, 2] [1, 0, 2, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1020201 : mirrorTrits [1, 0, 2, 2, 1, 2, 2] = [2, 0, 1, 1, 2, 1, 1] := by
  decide

theorem demoInv_1020201 : specInv 7 5 20 [1, 0, 2, 0, 2, 0, 1] = some [2, 0, 1, 1, 2, 1, 1] :=
  specInv_mirror_7 [1, 0, 2, 0, 2, 0, 1] [0, 0, 0, 0, 2, 2, 2] [0, 1, 0, 2, 2, 2, 2] [1, 0, 2, 2, 1, 2, 2] [2, 0, 1, 1, 2, 1, 1] demoR1_1020201 demoR2_1020201 demoC_1020201 demoM_1020201 demoMir_1020201

theorem demoR1_2020201 : invRung 7 5 20 [2, 0, 2, 0, 2, 0, 1] [2, 0, 2, 0, 2, 0, 1] 1 2 false = ([1, 2, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_2020201 : invRung 7 5 20 [2, 0, 2, 0, 2, 0, 1] [1, 2, 0, 1, 1, 1, 0] 3 1 true = ([2, 0, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_2020201 : fieldCube 7 5 20 [2, 0, 0, 1, 1, 1, 1] = [1, 0, 1, 2, 2, 1, 1] := by
  decide

theorem demoM_2020201 : fieldMul 7 5 20 [1, 0, 1, 2, 2, 1, 1] [2, 0, 2, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2020201 : specInv 7 5 20 [2, 0, 2, 0, 2, 0, 1] = some [1, 0, 1, 2, 2, 1, 1] :=
  specInv_white_7 [2, 0, 2, 0, 2, 0, 1] [1, 2, 0, 1, 1, 1, 0] [2, 0, 0, 1, 1, 1, 1] [1, 0, 1, 2, 2, 1, 1] demoR1_2020201 demoR2_2020201 demoC_2020201 demoM_2020201

theorem demoR1_0120201 : invRung 7 5 20 [0, 1, 2, 0, 2, 0, 1] [0, 1, 2, 0, 2, 0, 1] 1 2 false = ([2, 2, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_0120201 : invRung 7 5 20 [0, 1, 2, 0, 2, 0, 1] [2, 2, 2, 2, 1, 0, 0] 3 1 true = ([0, 1, 1, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_0120201 : fieldCube 7 5 20 [0, 1, 1, 0, 0, 1, 1] = [1, 2, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_0120201 : fieldMul 7 5 20 [1, 2, 0, 2, 2, 2, 1] [0, 1, 2, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0120201 : specInv 7 5 20 [0, 1, 2, 0, 2, 0, 1] = some [1, 2, 0, 2, 2, 2, 1] :=
  specInv_white_7 [0, 1, 2, 0, 2, 0, 1] [2, 2, 2, 2, 1, 0, 0] [0, 1, 1, 0, 0, 1, 1] [1, 2, 0, 2, 2, 2, 1] demoR1_0120201 demoR2_0120201 demoC_0120201 demoM_0120201

theorem demoR1_1120201 : invRung 7 5 20 [1, 1, 2, 0, 2, 0, 1] [1, 1, 2, 0, 2, 0, 1] 1 2 false = ([1, 1, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_1120201 : invRung 7 5 20 [1, 1, 2, 0, 2, 0, 1] [1, 1, 0, 0, 1, 1, 2] 3 1 true = ([1, 0, 2, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_1120201 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 2, 0] = [1, 0, 0, 1, 2, 1, 1] := by
  decide

theorem demoM_1120201 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 1, 1] [1, 1, 2, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1120201 : specInv 7 5 20 [1, 1, 2, 0, 2, 0, 1] = some [1, 0, 0, 1, 2, 1, 1] :=
  specInv_white_7 [1, 1, 2, 0, 2, 0, 1] [1, 1, 0, 0, 1, 1, 2] [1, 0, 2, 1, 1, 2, 0] [1, 0, 0, 1, 2, 1, 1] demoR1_1120201 demoR2_1120201 demoC_1120201 demoM_1120201

theorem demoR1_2120201 : invRung 7 5 20 [2, 1, 2, 0, 2, 0, 1] [2, 1, 2, 0, 2, 0, 1] 1 2 false = ([2, 2, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_2120201 : invRung 7 5 20 [2, 1, 2, 0, 2, 0, 1] [2, 2, 1, 0, 2, 1, 2] 3 1 true = ([0, 2, 2, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_2120201 : fieldCube 7 5 20 [0, 2, 2, 0, 2, 0, 0] = [0, 2, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_2120201 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 2, 1] [2, 1, 2, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2120201 : specInv 7 5 20 [2, 1, 2, 0, 2, 0, 1] = some [0, 2, 0, 1, 0, 2, 1] :=
  specInv_white_7 [2, 1, 2, 0, 2, 0, 1] [2, 2, 1, 0, 2, 1, 2] [0, 2, 2, 0, 2, 0, 0] [0, 2, 0, 1, 0, 2, 1] demoR1_2120201 demoR2_2120201 demoC_2120201 demoM_2120201

theorem demoR1_0220201 : invRung 7 5 20 [0, 2, 2, 0, 2, 0, 1] [0, 2, 2, 0, 2, 0, 1] 1 2 false = ([0, 1, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_0220201 : invRung 7 5 20 [0, 2, 2, 0, 2, 0, 1] [0, 1, 0, 2, 0, 0, 1] 3 1 true = ([0, 0, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0220201 : fieldCube 7 5 20 [0, 0, 0, 1, 0, 1, 2] = [2, 0, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_0220201 : fieldMul 7 5 20 [2, 0, 0, 2, 0, 1, 1] [0, 2, 2, 0, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0220201 : specInv 7 5 20 [0, 2, 2, 0, 2, 0, 1] = some [2, 0, 0, 2, 0, 1, 1] :=
  specInv_white_7 [0, 2, 2, 0, 2, 0, 1] [0, 1, 0, 2, 0, 0, 1] [0, 0, 0, 1, 0, 1, 2] [2, 0, 0, 2, 0, 1, 1] demoR1_0220201 demoR2_0220201 demoC_0220201 demoM_0220201

theorem demoR1_1220201 : invRung 7 5 20 [1, 2, 2, 0, 2, 0, 1] [1, 2, 2, 0, 2, 0, 1] 1 2 false = ([0, 1, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_1220201 : invRung 7 5 20 [1, 2, 2, 0, 2, 0, 1] [0, 1, 0, 1, 1, 2, 0] 3 1 true = ([2, 1, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoC_1220201 : fieldCube 7 5 20 [2, 1, 2, 2, 2, 1, 1] = [2, 1, 2, 1, 2, 0, 1] := by
  decide

theorem demoM_1220201 : fieldMul 7 5 20 [2, 1, 2, 1, 2, 0, 1] [1, 2, 2, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1220201 : mirrorTrits [2, 1, 2, 1, 2, 0, 1] = [1, 2, 1, 2, 1, 0, 2] := by
  decide

theorem demoInv_1220201 : specInv 7 5 20 [1, 2, 2, 0, 2, 0, 1] = some [1, 2, 1, 2, 1, 0, 2] :=
  specInv_mirror_7 [1, 2, 2, 0, 2, 0, 1] [0, 1, 0, 1, 1, 2, 0] [2, 1, 2, 2, 2, 1, 1] [2, 1, 2, 1, 2, 0, 1] [1, 2, 1, 2, 1, 0, 2] demoR1_1220201 demoR2_1220201 demoC_1220201 demoM_1220201 demoMir_1220201

theorem demoR1_2220201 : invRung 7 5 20 [2, 2, 2, 0, 2, 0, 1] [2, 2, 2, 0, 2, 0, 1] 1 2 false = ([1, 2, 2, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_2220201 : invRung 7 5 20 [2, 2, 2, 0, 2, 0, 1] [1, 2, 2, 1, 0, 2, 0] 3 1 true = ([1, 0, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_2220201 : fieldCube 7 5 20 [1, 0, 1, 2, 2, 0, 2] = [0, 1, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_2220201 : fieldMul 7 5 20 [0, 1, 0, 1, 2, 0, 2] [2, 2, 2, 0, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220201 : mirrorTrits [0, 1, 0, 1, 2, 0, 2] = [0, 2, 0, 2, 1, 0, 1] := by
  decide

theorem demoInv_2220201 : specInv 7 5 20 [2, 2, 2, 0, 2, 0, 1] = some [0, 2, 0, 2, 1, 0, 1] :=
  specInv_mirror_7 [2, 2, 2, 0, 2, 0, 1] [1, 2, 2, 1, 0, 2, 0] [1, 0, 1, 2, 2, 0, 2] [0, 1, 0, 1, 2, 0, 2] [0, 2, 0, 2, 1, 0, 1] demoR1_2220201 demoR2_2220201 demoC_2220201 demoM_2220201 demoMir_2220201

theorem demoR1_0001201 : invRung 7 5 20 [0, 0, 0, 1, 2, 0, 1] [0, 0, 0, 1, 2, 0, 1] 1 2 false = ([1, 0, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_0001201 : invRung 7 5 20 [0, 0, 0, 1, 2, 0, 1] [1, 0, 1, 1, 1, 0, 0] 3 1 true = ([1, 1, 1, 0, 0, 0, 2], 3) := by
  decide

theorem demoC_0001201 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 0, 2] = [1, 2, 1, 0, 2, 2, 0] := by
  decide

theorem demoM_0001201 : fieldMul 7 5 20 [1, 2, 1, 0, 2, 2, 0] [0, 0, 0, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0001201 : specInv 7 5 20 [0, 0, 0, 1, 2, 0, 1] = some [1, 2, 1, 0, 2, 2, 0] :=
  specInv_white_7 [0, 0, 0, 1, 2, 0, 1] [1, 0, 1, 1, 1, 0, 0] [1, 1, 1, 0, 0, 0, 2] [1, 2, 1, 0, 2, 2, 0] demoR1_0001201 demoR2_0001201 demoC_0001201 demoM_0001201

theorem demoR1_1001201 : invRung 7 5 20 [1, 0, 0, 1, 2, 0, 1] [1, 0, 0, 1, 2, 0, 1] 1 2 false = ([1, 0, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_1001201 : invRung 7 5 20 [1, 0, 0, 1, 2, 0, 1] [1, 0, 1, 2, 1, 2, 0] 3 1 true = ([1, 1, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_1001201 : fieldCube 7 5 20 [1, 1, 2, 0, 0, 2, 0] = [0, 2, 2, 1, 2, 2, 0] := by
  decide

theorem demoM_1001201 : fieldMul 7 5 20 [0, 2, 2, 1, 2, 2, 0] [1, 0, 0, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1001201 : specInv 7 5 20 [1, 0, 0, 1, 2, 0, 1] = some [0, 2, 2, 1, 2, 2, 0] :=
  specInv_white_7 [1, 0, 0, 1, 2, 0, 1] [1, 0, 1, 2, 1, 2, 0] [1, 1, 2, 0, 0, 2, 0] [0, 2, 2, 1, 2, 2, 0] demoR1_1001201 demoR2_1001201 demoC_1001201 demoM_1001201

theorem demoR1_2001201 : invRung 7 5 20 [2, 0, 0, 1, 2, 0, 1] [2, 0, 0, 1, 2, 0, 1] 1 2 false = ([1, 1, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_2001201 : invRung 7 5 20 [2, 0, 0, 1, 2, 0, 1] [1, 1, 0, 1, 0, 1, 2] 3 1 true = ([1, 2, 0, 2, 2, 2, 0], 3) := by
  decide

theorem demoC_2001201 : fieldCube 7 5 20 [1, 2, 0, 2, 2, 2, 0] = [2, 1, 1, 1, 2, 0, 0] := by
  decide

theorem demoM_2001201 : fieldMul 7 5 20 [2, 1, 1, 1, 2, 0, 0] [2, 0, 0, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2001201 : specInv 7 5 20 [2, 0, 0, 1, 2, 0, 1] = some [2, 1, 1, 1, 2, 0, 0] :=
  specInv_white_7 [2, 0, 0, 1, 2, 0, 1] [1, 1, 0, 1, 0, 1, 2] [1, 2, 0, 2, 2, 2, 0] [2, 1, 1, 1, 2, 0, 0] demoR1_2001201 demoR2_2001201 demoC_2001201 demoM_2001201

theorem demoR1_0101201 : invRung 7 5 20 [0, 1, 0, 1, 2, 0, 1] [0, 1, 0, 1, 2, 0, 1] 1 2 false = ([0, 2, 0, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_0101201 : invRung 7 5 20 [0, 1, 0, 1, 2, 0, 1] [0, 2, 0, 2, 0, 0, 0] 3 1 true = ([1, 2, 1, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0101201 : fieldCube 7 5 20 [1, 2, 1, 1, 2, 2, 2] = [1, 0, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_0101201 : fieldMul 7 5 20 [1, 0, 1, 0, 1, 1, 0] [0, 1, 0, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0101201 : specInv 7 5 20 [0, 1, 0, 1, 2, 0, 1] = some [1, 0, 1, 0, 1, 1, 0] :=
  specInv_white_7 [0, 1, 0, 1, 2, 0, 1] [0, 2, 0, 2, 0, 0, 0] [1, 2, 1, 1, 2, 2, 2] [1, 0, 1, 0, 1, 1, 0] demoR1_0101201 demoR2_0101201 demoC_0101201 demoM_0101201

theorem demoR1_1101201 : invRung 7 5 20 [1, 1, 0, 1, 2, 0, 1] [1, 1, 0, 1, 2, 0, 1] 1 2 false = ([2, 1, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1101201 : invRung 7 5 20 [1, 1, 0, 1, 2, 0, 1] [2, 1, 0, 2, 2, 1, 1] 3 1 true = ([0, 1, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_1101201 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 1, 0] = [0, 2, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_1101201 : fieldMul 7 5 20 [0, 2, 0, 2, 1, 1, 2] [1, 1, 0, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1101201 : specInv 7 5 20 [1, 1, 0, 1, 2, 0, 1] = some [0, 2, 0, 2, 1, 1, 2] :=
  specInv_white_7 [1, 1, 0, 1, 2, 0, 1] [2, 1, 0, 2, 2, 1, 1] [0, 1, 2, 2, 1, 1, 0] [0, 2, 0, 2, 1, 1, 2] demoR1_1101201 demoR2_1101201 demoC_1101201 demoM_1101201

theorem demoR1_2101201 : invRung 7 5 20 [2, 1, 0, 1, 2, 0, 1] [2, 1, 0, 1, 2, 0, 1] 1 2 false = ([0, 0, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_2101201 : invRung 7 5 20 [2, 1, 0, 1, 2, 0, 1] [0, 0, 1, 2, 0, 1, 1] 3 1 true = ([2, 2, 2, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_2101201 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 2, 0] = [0, 0, 1, 0, 2, 2, 1] := by
  decide

theorem demoM_2101201 : fieldMul 7 5 20 [0, 0, 1, 0, 2, 2, 1] [2, 1, 0, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2101201 : specInv 7 5 20 [2, 1, 0, 1, 2, 0, 1] = some [0, 0, 1, 0, 2, 2, 1] :=
  specInv_white_7 [2, 1, 0, 1, 2, 0, 1] [0, 0, 1, 2, 0, 1, 1] [2, 2, 2, 2, 1, 2, 0] [0, 0, 1, 0, 2, 2, 1] demoR1_2101201 demoR2_2101201 demoC_2101201 demoM_2101201

theorem demoR1_0201201 : invRung 7 5 20 [0, 2, 0, 1, 2, 0, 1] [0, 2, 0, 1, 2, 0, 1] 1 2 false = ([1, 2, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_0201201 : invRung 7 5 20 [0, 2, 0, 1, 2, 0, 1] [1, 2, 0, 1, 0, 2, 1] 3 1 true = ([2, 0, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_0201201 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 0, 2] = [1, 2, 0, 2, 2, 1, 0] := by
  decide

theorem demoM_0201201 : fieldMul 7 5 20 [1, 2, 0, 2, 2, 1, 0] [0, 2, 0, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0201201 : specInv 7 5 20 [0, 2, 0, 1, 2, 0, 1] = some [1, 2, 0, 2, 2, 1, 0] :=
  specInv_white_7 [0, 2, 0, 1, 2, 0, 1] [1, 2, 0, 1, 0, 2, 1] [2, 0, 1, 2, 0, 0, 2] [1, 2, 0, 2, 2, 1, 0] demoR1_0201201 demoR2_0201201 demoC_0201201 demoM_0201201

theorem demoR1_1201201 : invRung 7 5 20 [1, 2, 0, 1, 2, 0, 1] [1, 2, 0, 1, 2, 0, 1] 1 2 false = ([2, 1, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_1201201 : invRung 7 5 20 [1, 2, 0, 1, 2, 0, 1] [2, 1, 0, 1, 0, 1, 1] 3 1 true = ([1, 2, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_1201201 : fieldCube 7 5 20 [1, 2, 0, 0, 2, 1, 1] = [2, 1, 0, 2, 2, 1, 2] := by
  decide

theorem demoM_1201201 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 1, 2] [1, 2, 0, 1, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201201 : mirrorTrits [2, 1, 0, 2, 2, 1, 2] = [1, 2, 0, 1, 1, 2, 1] := by
  decide

theorem demoInv_1201201 : specInv 7 5 20 [1, 2, 0, 1, 2, 0, 1] = some [1, 2, 0, 1, 1, 2, 1] :=
  specInv_mirror_7 [1, 2, 0, 1, 2, 0, 1] [2, 1, 0, 1, 0, 1, 1] [1, 2, 0, 0, 2, 1, 1] [2, 1, 0, 2, 2, 1, 2] [1, 2, 0, 1, 1, 2, 1] demoR1_1201201 demoR2_1201201 demoC_1201201 demoM_1201201 demoMir_1201201

theorem demoR1_2201201 : invRung 7 5 20 [2, 2, 0, 1, 2, 0, 1] [2, 2, 0, 1, 2, 0, 1] 1 2 false = ([1, 2, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_2201201 : invRung 7 5 20 [2, 2, 0, 1, 2, 0, 1] [1, 2, 0, 0, 2, 1, 0] 3 1 true = ([1, 1, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_2201201 : fieldCube 7 5 20 [1, 1, 2, 0, 2, 0, 2] = [1, 1, 1, 2, 2, 1, 0] := by
  decide

theorem demoM_2201201 : fieldMul 7 5 20 [1, 1, 1, 2, 2, 1, 0] [2, 2, 0, 1, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2201201 : mirrorTrits [1, 1, 1, 2, 2, 1, 0] = [2, 2, 2, 1, 1, 2, 0] := by
  decide

theorem demoInv_2201201 : specInv 7 5 20 [2, 2, 0, 1, 2, 0, 1] = some [2, 2, 2, 1, 1, 2, 0] :=
  specInv_mirror_7 [2, 2, 0, 1, 2, 0, 1] [1, 2, 0, 0, 2, 1, 0] [1, 1, 2, 0, 2, 0, 2] [1, 1, 1, 2, 2, 1, 0] [2, 2, 2, 1, 1, 2, 0] demoR1_2201201 demoR2_2201201 demoC_2201201 demoM_2201201 demoMir_2201201

theorem demoR1_0011201 : invRung 7 5 20 [0, 0, 1, 1, 2, 0, 1] [0, 0, 1, 1, 2, 0, 1] 1 2 false = ([1, 2, 2, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_0011201 : invRung 7 5 20 [0, 0, 1, 1, 2, 0, 1] [1, 2, 2, 1, 2, 0, 2] 3 1 true = ([2, 0, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoC_0011201 : fieldCube 7 5 20 [2, 0, 0, 2, 0, 1, 1] = [2, 2, 2, 1, 2, 1, 0] := by
  decide

theorem demoM_0011201 : fieldMul 7 5 20 [2, 2, 2, 1, 2, 1, 0] [0, 0, 1, 1, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0011201 : mirrorTrits [2, 2, 2, 1, 2, 1, 0] = [1, 1, 1, 2, 1, 2, 0] := by
  decide

theorem demoInv_0011201 : specInv 7 5 20 [0, 0, 1, 1, 2, 0, 1] = some [1, 1, 1, 2, 1, 2, 0] :=
  specInv_mirror_7 [0, 0, 1, 1, 2, 0, 1] [1, 2, 2, 1, 2, 0, 2] [2, 0, 0, 2, 0, 1, 1] [2, 2, 2, 1, 2, 1, 0] [1, 1, 1, 2, 1, 2, 0] demoR1_0011201 demoR2_0011201 demoC_0011201 demoM_0011201 demoMir_0011201

theorem demoR1_1011201 : invRung 7 5 20 [1, 0, 1, 1, 2, 0, 1] [1, 0, 1, 1, 2, 0, 1] 1 2 false = ([2, 1, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1011201 : invRung 7 5 20 [1, 0, 1, 1, 2, 0, 1] [2, 1, 0, 1, 1, 0, 0] 3 1 true = ([0, 1, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_1011201 : fieldCube 7 5 20 [0, 1, 0, 1, 2, 0, 2] = [1, 1, 2, 2, 2, 2, 1] := by
  decide

theorem demoM_1011201 : fieldMul 7 5 20 [1, 1, 2, 2, 2, 2, 1] [1, 0, 1, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1011201 : specInv 7 5 20 [1, 0, 1, 1, 2, 0, 1] = some [1, 1, 2, 2, 2, 2, 1] :=
  specInv_white_7 [1, 0, 1, 1, 2, 0, 1] [2, 1, 0, 1, 1, 0, 0] [0, 1, 0, 1, 2, 0, 2] [1, 1, 2, 2, 2, 2, 1] demoR1_1011201 demoR2_1011201 demoC_1011201 demoM_1011201

theorem demoR1_2011201 : invRung 7 5 20 [2, 0, 1, 1, 2, 0, 1] [2, 0, 1, 1, 2, 0, 1] 1 2 false = ([0, 0, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_2011201 : invRung 7 5 20 [2, 0, 1, 1, 2, 0, 1] [0, 0, 0, 1, 1, 2, 1] 3 1 true = ([2, 1, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_2011201 : fieldCube 7 5 20 [2, 1, 2, 1, 2, 0, 1] = [0, 0, 0, 1, 1, 1, 2] := by
  decide

theorem demoM_2011201 : fieldMul 7 5 20 [0, 0, 0, 1, 1, 1, 2] [2, 0, 1, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2011201 : specInv 7 5 20 [2, 0, 1, 1, 2, 0, 1] = some [0, 0, 0, 1, 1, 1, 2] :=
  specInv_white_7 [2, 0, 1, 1, 2, 0, 1] [0, 0, 0, 1, 1, 2, 1] [2, 1, 2, 1, 2, 0, 1] [0, 0, 0, 1, 1, 1, 2] demoR1_2011201 demoR2_2011201 demoC_2011201 demoM_2011201

theorem demoR1_0111201 : invRung 7 5 20 [0, 1, 1, 1, 2, 0, 1] [0, 1, 1, 1, 2, 0, 1] 1 2 false = ([1, 2, 1, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_0111201 : invRung 7 5 20 [0, 1, 1, 1, 2, 0, 1] [1, 2, 1, 1, 0, 1, 2] 3 1 true = ([2, 2, 2, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_0111201 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 1, 1] = [2, 0, 2, 1, 2, 2, 0] := by
  decide

theorem demoM_0111201 : fieldMul 7 5 20 [2, 0, 2, 1, 2, 2, 0] [0, 1, 1, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0111201 : specInv 7 5 20 [0, 1, 1, 1, 2, 0, 1] = some [2, 0, 2, 1, 2, 2, 0] :=
  specInv_white_7 [0, 1, 1, 1, 2, 0, 1] [1, 2, 1, 1, 0, 1, 2] [2, 2, 2, 2, 1, 1, 1] [2, 0, 2, 1, 2, 2, 0] demoR1_0111201 demoR2_0111201 demoC_0111201 demoM_0111201

theorem demoR1_1111201 : invRung 7 5 20 [1, 1, 1, 1, 2, 0, 1] [1, 1, 1, 1, 2, 0, 1] 1 2 false = ([1, 2, 0, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1111201 : invRung 7 5 20 [1, 1, 1, 1, 2, 0, 1] [1, 2, 0, 2, 2, 1, 0] 3 1 true = ([1, 2, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_1111201 : fieldCube 7 5 20 [1, 2, 0, 2, 0, 0, 1] = [0, 1, 1, 0, 1, 0, 1] := by
  decide

theorem demoM_1111201 : fieldMul 7 5 20 [0, 1, 1, 0, 1, 0, 1] [1, 1, 1, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1111201 : specInv 7 5 20 [1, 1, 1, 1, 2, 0, 1] = some [0, 1, 1, 0, 1, 0, 1] :=
  specInv_white_7 [1, 1, 1, 1, 2, 0, 1] [1, 2, 0, 2, 2, 1, 0] [1, 2, 0, 2, 0, 0, 1] [0, 1, 1, 0, 1, 0, 1] demoR1_1111201 demoR2_1111201 demoC_1111201 demoM_1111201

theorem demoR1_2111201 : invRung 7 5 20 [2, 1, 1, 1, 2, 0, 1] [2, 1, 1, 1, 2, 0, 1] 1 2 false = ([0, 1, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_2111201 : invRung 7 5 20 [2, 1, 1, 1, 2, 0, 1] [0, 1, 0, 2, 2, 2, 1] 3 1 true = ([2, 1, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_2111201 : fieldCube 7 5 20 [2, 1, 0, 1, 1, 0, 0] = [0, 1, 1, 2, 0, 2, 1] := by
  decide

theorem demoM_2111201 : fieldMul 7 5 20 [0, 1, 1, 2, 0, 2, 1] [2, 1, 1, 1, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2111201 : mirrorTrits [0, 1, 1, 2, 0, 2, 1] = [0, 2, 2, 1, 0, 1, 2] := by
  decide

theorem demoInv_2111201 : specInv 7 5 20 [2, 1, 1, 1, 2, 0, 1] = some [0, 2, 2, 1, 0, 1, 2] :=
  specInv_mirror_7 [2, 1, 1, 1, 2, 0, 1] [0, 1, 0, 2, 2, 2, 1] [2, 1, 0, 1, 1, 0, 0] [0, 1, 1, 2, 0, 2, 1] [0, 2, 2, 1, 0, 1, 2] demoR1_2111201 demoR2_2111201 demoC_2111201 demoM_2111201 demoMir_2111201

theorem demoR1_0211201 : invRung 7 5 20 [0, 2, 1, 1, 2, 0, 1] [0, 2, 1, 1, 2, 0, 1] 1 2 false = ([1, 2, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_0211201 : invRung 7 5 20 [0, 2, 1, 1, 2, 0, 1] [1, 2, 2, 2, 2, 2, 0] 3 1 true = ([0, 2, 2, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_0211201 : fieldCube 7 5 20 [0, 2, 2, 2, 1, 1, 0] = [0, 2, 0, 0, 1, 1, 2] := by
  decide

theorem demoM_0211201 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 1, 2] [0, 2, 1, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0211201 : specInv 7 5 20 [0, 2, 1, 1, 2, 0, 1] = some [0, 2, 0, 0, 1, 1, 2] :=
  specInv_white_7 [0, 2, 1, 1, 2, 0, 1] [1, 2, 2, 2, 2, 2, 0] [0, 2, 2, 2, 1, 1, 0] [0, 2, 0, 0, 1, 1, 2] demoR1_0211201 demoR2_0211201 demoC_0211201 demoM_0211201

theorem demoR1_1211201 : invRung 7 5 20 [1, 2, 1, 1, 2, 0, 1] [1, 2, 1, 1, 2, 0, 1] 1 2 false = ([0, 1, 2, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1211201 : invRung 7 5 20 [1, 2, 1, 1, 2, 0, 1] [0, 1, 2, 2, 0, 1, 2] 3 1 true = ([1, 1, 0, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_1211201 : fieldCube 7 5 20 [1, 1, 0, 0, 1, 2, 1] = [0, 1, 1, 0, 0, 1, 0] := by
  decide

theorem demoM_1211201 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 1, 0] [1, 2, 1, 1, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1211201 : mirrorTrits [0, 1, 1, 0, 0, 1, 0] = [0, 2, 2, 0, 0, 2, 0] := by
  decide

theorem demoInv_1211201 : specInv 7 5 20 [1, 2, 1, 1, 2, 0, 1] = some [0, 2, 2, 0, 0, 2, 0] :=
  specInv_mirror_7 [1, 2, 1, 1, 2, 0, 1] [0, 1, 2, 2, 0, 1, 2] [1, 1, 0, 0, 1, 2, 1] [0, 1, 1, 0, 0, 1, 0] [0, 2, 2, 0, 0, 2, 0] demoR1_1211201 demoR2_1211201 demoC_1211201 demoM_1211201 demoMir_1211201

theorem demoR1_2211201 : invRung 7 5 20 [2, 2, 1, 1, 2, 0, 1] [2, 2, 1, 1, 2, 0, 1] 1 2 false = ([0, 1, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_2211201 : invRung 7 5 20 [2, 2, 1, 1, 2, 0, 1] [0, 1, 2, 0, 2, 0, 1] 3 1 true = ([2, 2, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_2211201 : fieldCube 7 5 20 [2, 2, 1, 0, 2, 1, 2] = [0, 2, 2, 0, 0, 2, 1] := by
  decide

theorem demoM_2211201 : fieldMul 7 5 20 [0, 2, 2, 0, 0, 2, 1] [2, 2, 1, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2211201 : specInv 7 5 20 [2, 2, 1, 1, 2, 0, 1] = some [0, 2, 2, 0, 0, 2, 1] :=
  specInv_white_7 [2, 2, 1, 1, 2, 0, 1] [0, 1, 2, 0, 2, 0, 1] [2, 2, 1, 0, 2, 1, 2] [0, 2, 2, 0, 0, 2, 1] demoR1_2211201 demoR2_2211201 demoC_2211201 demoM_2211201

theorem demoR1_0021201 : invRung 7 5 20 [0, 0, 2, 1, 2, 0, 1] [0, 0, 2, 1, 2, 0, 1] 1 2 false = ([0, 1, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_0021201 : invRung 7 5 20 [0, 0, 2, 1, 2, 0, 1] [0, 1, 1, 2, 2, 2, 0] 3 1 true = ([1, 2, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_0021201 : fieldCube 7 5 20 [1, 2, 1, 2, 0, 0, 0] = [0, 0, 2, 2, 0, 2, 1] := by
  decide

theorem demoM_0021201 : fieldMul 7 5 20 [0, 0, 2, 2, 0, 2, 1] [0, 0, 2, 1, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0021201 : mirrorTrits [0, 0, 2, 2, 0, 2, 1] = [0, 0, 1, 1, 0, 1, 2] := by
  decide

theorem demoInv_0021201 : specInv 7 5 20 [0, 0, 2, 1, 2, 0, 1] = some [0, 0, 1, 1, 0, 1, 2] :=
  specInv_mirror_7 [0, 0, 2, 1, 2, 0, 1] [0, 1, 1, 2, 2, 2, 0] [1, 2, 1, 2, 0, 0, 0] [0, 0, 2, 2, 0, 2, 1] [0, 0, 1, 1, 0, 1, 2] demoR1_0021201 demoR2_0021201 demoC_0021201 demoM_0021201 demoMir_0021201

theorem demoR1_1021201 : invRung 7 5 20 [1, 0, 2, 1, 2, 0, 1] [1, 0, 2, 1, 2, 0, 1] 1 2 false = ([1, 2, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1021201 : invRung 7 5 20 [1, 0, 2, 1, 2, 0, 1] [1, 2, 1, 1, 0, 0, 1] 3 1 true = ([1, 1, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_1021201 : fieldCube 7 5 20 [1, 1, 2, 1, 1, 2, 1] = [1, 1, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_1021201 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 2, 2] [1, 0, 2, 1, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021201 : mirrorTrits [1, 1, 2, 0, 0, 2, 2] = [2, 2, 1, 0, 0, 1, 1] := by
  decide

theorem demoInv_1021201 : specInv 7 5 20 [1, 0, 2, 1, 2, 0, 1] = some [2, 2, 1, 0, 0, 1, 1] :=
  specInv_mirror_7 [1, 0, 2, 1, 2, 0, 1] [1, 2, 1, 1, 0, 0, 1] [1, 1, 2, 1, 1, 2, 1] [1, 1, 2, 0, 0, 2, 2] [2, 2, 1, 0, 0, 1, 1] demoR1_1021201 demoR2_1021201 demoC_1021201 demoM_1021201 demoMir_1021201

theorem demoR1_2021201 : invRung 7 5 20 [2, 0, 2, 1, 2, 0, 1] [2, 0, 2, 1, 2, 0, 1] 1 2 false = ([2, 2, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_2021201 : invRung 7 5 20 [2, 0, 2, 1, 2, 0, 1] [2, 2, 0, 2, 1, 2, 0] 3 1 true = ([2, 1, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_2021201 : fieldCube 7 5 20 [2, 1, 1, 0, 0, 0, 1] = [2, 1, 2, 2, 1, 1, 2] := by
  decide

theorem demoM_2021201 : fieldMul 7 5 20 [2, 1, 2, 2, 1, 1, 2] [2, 0, 2, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2021201 : specInv 7 5 20 [2, 0, 2, 1, 2, 0, 1] = some [2, 1, 2, 2, 1, 1, 2] :=
  specInv_white_7 [2, 0, 2, 1, 2, 0, 1] [2, 2, 0, 2, 1, 2, 0] [2, 1, 1, 0, 0, 0, 1] [2, 1, 2, 2, 1, 1, 2] demoR1_2021201 demoR2_2021201 demoC_2021201 demoM_2021201

theorem demoR1_0121201 : invRung 7 5 20 [0, 1, 2, 1, 2, 0, 1] [0, 1, 2, 1, 2, 0, 1] 1 2 false = ([1, 1, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_0121201 : invRung 7 5 20 [0, 1, 2, 1, 2, 0, 1] [1, 1, 2, 0, 1, 0, 2] 3 1 true = ([2, 0, 0, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_0121201 : fieldCube 7 5 20 [2, 0, 0, 2, 0, 2, 1] = [0, 0, 0, 1, 0, 2, 2] := by
  decide

theorem demoM_0121201 : fieldMul 7 5 20 [0, 0, 0, 1, 0, 2, 2] [0, 1, 2, 1, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0121201 : mirrorTrits [0, 0, 0, 1, 0, 2, 2] = [0, 0, 0, 2, 0, 1, 1] := by
  decide

theorem demoInv_0121201 : specInv 7 5 20 [0, 1, 2, 1, 2, 0, 1] = some [0, 0, 0, 2, 0, 1, 1] :=
  specInv_mirror_7 [0, 1, 2, 1, 2, 0, 1] [1, 1, 2, 0, 1, 0, 2] [2, 0, 0, 2, 0, 2, 1] [0, 0, 0, 1, 0, 2, 2] [0, 0, 0, 2, 0, 1, 1] demoR1_0121201 demoR2_0121201 demoC_0121201 demoM_0121201 demoMir_0121201

theorem demoR1_1121201 : invRung 7 5 20 [1, 1, 2, 1, 2, 0, 1] [1, 1, 2, 1, 2, 0, 1] 1 2 false = ([1, 2, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_1121201 : invRung 7 5 20 [1, 1, 2, 1, 2, 0, 1] [1, 2, 1, 2, 0, 2, 2] 3 1 true = ([2, 0, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_1121201 : fieldCube 7 5 20 [2, 0, 1, 2, 2, 0, 2] = [1, 1, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_1121201 : fieldMul 7 5 20 [1, 1, 0, 1, 2, 0, 2] [1, 1, 2, 1, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121201 : mirrorTrits [1, 1, 0, 1, 2, 0, 2] = [2, 2, 0, 2, 1, 0, 1] := by
  decide

theorem demoInv_1121201 : specInv 7 5 20 [1, 1, 2, 1, 2, 0, 1] = some [2, 2, 0, 2, 1, 0, 1] :=
  specInv_mirror_7 [1, 1, 2, 1, 2, 0, 1] [1, 2, 1, 2, 0, 2, 2] [2, 0, 1, 2, 2, 0, 2] [1, 1, 0, 1, 2, 0, 2] [2, 2, 0, 2, 1, 0, 1] demoR1_1121201 demoR2_1121201 demoC_1121201 demoM_1121201 demoMir_1121201

theorem demoR1_2121201 : invRung 7 5 20 [2, 1, 2, 1, 2, 0, 1] [2, 1, 2, 1, 2, 0, 1] 1 2 false = ([0, 1, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_2121201 : invRung 7 5 20 [2, 1, 2, 1, 2, 0, 1] [0, 1, 1, 2, 2, 1, 0] 3 1 true = ([0, 2, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_2121201 : fieldCube 7 5 20 [0, 2, 1, 2, 0, 0, 1] = [2, 1, 1, 0, 1, 0, 2] := by
  decide

theorem demoM_2121201 : fieldMul 7 5 20 [2, 1, 1, 0, 1, 0, 2] [2, 1, 2, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2121201 : specInv 7 5 20 [2, 1, 2, 1, 2, 0, 1] = some [2, 1, 1, 0, 1, 0, 2] :=
  specInv_white_7 [2, 1, 2, 1, 2, 0, 1] [0, 1, 1, 2, 2, 1, 0] [0, 2, 1, 2, 0, 0, 1] [2, 1, 1, 0, 1, 0, 2] demoR1_2121201 demoR2_2121201 demoC_2121201 demoM_2121201

theorem demoR1_0221201 : invRung 7 5 20 [0, 2, 2, 1, 2, 0, 1] [0, 2, 2, 1, 2, 0, 1] 1 2 false = ([0, 0, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_0221201 : invRung 7 5 20 [0, 2, 2, 1, 2, 0, 1] [0, 0, 0, 2, 1, 2, 2] 3 1 true = ([2, 0, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_0221201 : fieldCube 7 5 20 [2, 0, 0, 0, 2, 1, 0] = [0, 0, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_0221201 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 0, 1] [0, 2, 2, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0221201 : specInv 7 5 20 [0, 2, 2, 1, 2, 0, 1] = some [0, 0, 1, 2, 1, 0, 1] :=
  specInv_white_7 [0, 2, 2, 1, 2, 0, 1] [0, 0, 0, 2, 1, 2, 2] [2, 0, 0, 0, 2, 1, 0] [0, 0, 1, 2, 1, 0, 1] demoR1_0221201 demoR2_0221201 demoC_0221201 demoM_0221201

theorem demoR1_1221201 : invRung 7 5 20 [1, 2, 2, 1, 2, 0, 1] [1, 2, 2, 1, 2, 0, 1] 1 2 false = ([2, 2, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1221201 : invRung 7 5 20 [1, 2, 2, 1, 2, 0, 1] [2, 2, 1, 2, 0, 1, 2] 3 1 true = ([1, 2, 2, 0, 0, 0, 0], 3) := by
  decide

theorem demoC_1221201 : fieldCube 7 5 20 [1, 2, 2, 0, 0, 0, 0] = [1, 0, 0, 2, 0, 0, 2] := by
  decide

theorem demoM_1221201 : fieldMul 7 5 20 [1, 0, 0, 2, 0, 0, 2] [1, 2, 2, 1, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1221201 : specInv 7 5 20 [1, 2, 2, 1, 2, 0, 1] = some [1, 0, 0, 2, 0, 0, 2] :=
  specInv_white_7 [1, 2, 2, 1, 2, 0, 1] [2, 2, 1, 2, 0, 1, 2] [1, 2, 2, 0, 0, 0, 0] [1, 0, 0, 2, 0, 0, 2] demoR1_1221201 demoR2_1221201 demoC_1221201 demoM_1221201

theorem demoR1_2221201 : invRung 7 5 20 [2, 2, 2, 1, 2, 0, 1] [2, 2, 2, 1, 2, 0, 1] 1 2 false = ([2, 1, 2, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_2221201 : invRung 7 5 20 [2, 2, 2, 1, 2, 0, 1] [2, 1, 2, 2, 2, 2, 0] 3 1 true = ([0, 1, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoC_2221201 : fieldCube 7 5 20 [0, 1, 1, 1, 1, 0, 1] = [1, 2, 0, 0, 1, 0, 0] := by
  decide

theorem demoM_2221201 : fieldMul 7 5 20 [1, 2, 0, 0, 1, 0, 0] [2, 2, 2, 1, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2221201 : mirrorTrits [1, 2, 0, 0, 1, 0, 0] = [2, 1, 0, 0, 2, 0, 0] := by
  decide

theorem demoInv_2221201 : specInv 7 5 20 [2, 2, 2, 1, 2, 0, 1] = some [2, 1, 0, 0, 2, 0, 0] :=
  specInv_mirror_7 [2, 2, 2, 1, 2, 0, 1] [2, 1, 2, 2, 2, 2, 0] [0, 1, 1, 1, 1, 0, 1] [1, 2, 0, 0, 1, 0, 0] [2, 1, 0, 0, 2, 0, 0] demoR1_2221201 demoR2_2221201 demoC_2221201 demoM_2221201 demoMir_2221201

theorem demoR1_0002201 : invRung 7 5 20 [0, 0, 0, 2, 2, 0, 1] [0, 0, 0, 2, 2, 0, 1] 1 2 false = ([1, 0, 0, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_0002201 : invRung 7 5 20 [0, 0, 0, 2, 2, 0, 1] [1, 0, 0, 2, 0, 2, 0] 3 1 true = ([2, 2, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_0002201 : fieldCube 7 5 20 [2, 2, 0, 1, 0, 1, 0] = [1, 1, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_0002201 : fieldMul 7 5 20 [1, 1, 2, 2, 1, 2, 2] [0, 0, 0, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0002201 : specInv 7 5 20 [0, 0, 0, 2, 2, 0, 1] = some [1, 1, 2, 2, 1, 2, 2] :=
  specInv_white_7 [0, 0, 0, 2, 2, 0, 1] [1, 0, 0, 2, 0, 2, 0] [2, 2, 0, 1, 0, 1, 0] [1, 1, 2, 2, 1, 2, 2] demoR1_0002201 demoR2_0002201 demoC_0002201 demoM_0002201

theorem demoR1_1002201 : invRung 7 5 20 [1, 0, 0, 2, 2, 0, 1] [1, 0, 0, 2, 2, 0, 1] 1 2 false = ([1, 2, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_1002201 : invRung 7 5 20 [1, 0, 0, 2, 2, 0, 1] [1, 2, 1, 1, 2, 1, 0] 3 1 true = ([2, 1, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_1002201 : fieldCube 7 5 20 [2, 1, 0, 0, 0, 2, 2] = [1, 1, 0, 0, 1, 1, 0] := by
  decide

theorem demoM_1002201 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 1, 0] [1, 0, 0, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1002201 : specInv 7 5 20 [1, 0, 0, 2, 2, 0, 1] = some [1, 1, 0, 0, 1, 1, 0] :=
  specInv_white_7 [1, 0, 0, 2, 2, 0, 1] [1, 2, 1, 1, 2, 1, 0] [2, 1, 0, 0, 0, 2, 2] [1, 1, 0, 0, 1, 1, 0] demoR1_1002201 demoR2_1002201 demoC_1002201 demoM_1002201

theorem demoR1_2002201 : invRung 7 5 20 [2, 0, 0, 2, 2, 0, 1] [2, 0, 0, 2, 2, 0, 1] 1 2 false = ([1, 1, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_2002201 : invRung 7 5 20 [2, 0, 0, 2, 2, 0, 1] [1, 1, 2, 0, 2, 1, 2] 3 1 true = ([1, 0, 2, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_2002201 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 1, 0] = [0, 2, 2, 1, 1, 0, 2] := by
  decide

theorem demoM_2002201 : fieldMul 7 5 20 [0, 2, 2, 1, 1, 0, 2] [2, 0, 0, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2002201 : mirrorTrits [0, 2, 2, 1, 1, 0, 2] = [0, 1, 1, 2, 2, 0, 1] := by
  decide

theorem demoInv_2002201 : specInv 7 5 20 [2, 0, 0, 2, 2, 0, 1] = some [0, 1, 1, 2, 2, 0, 1] :=
  specInv_mirror_7 [2, 0, 0, 2, 2, 0, 1] [1, 1, 2, 0, 2, 1, 2] [1, 0, 2, 1, 1, 1, 0] [0, 2, 2, 1, 1, 0, 2] [0, 1, 1, 2, 2, 0, 1] demoR1_2002201 demoR2_2002201 demoC_2002201 demoM_2002201 demoMir_2002201

theorem demoR1_0102201 : invRung 7 5 20 [0, 1, 0, 2, 2, 0, 1] [0, 1, 0, 2, 2, 0, 1] 1 2 false = ([1, 1, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_0102201 : invRung 7 5 20 [0, 1, 0, 2, 2, 0, 1] [1, 1, 0, 0, 2, 0, 1] 3 1 true = ([0, 1, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_0102201 : fieldCube 7 5 20 [0, 1, 0, 0, 1, 0, 1] = [0, 2, 2, 0, 1, 2, 2] := by
  decide

theorem demoM_0102201 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 2, 2] [0, 1, 0, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0102201 : specInv 7 5 20 [0, 1, 0, 2, 2, 0, 1] = some [0, 2, 2, 0, 1, 2, 2] :=
  specInv_white_7 [0, 1, 0, 2, 2, 0, 1] [1, 1, 0, 0, 2, 0, 1] [0, 1, 0, 0, 1, 0, 1] [0, 2, 2, 0, 1, 2, 2] demoR1_0102201 demoR2_0102201 demoC_0102201 demoM_0102201

theorem demoR1_1102201 : invRung 7 5 20 [1, 1, 0, 2, 2, 0, 1] [1, 1, 0, 2, 2, 0, 1] 1 2 false = ([1, 2, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoR2_1102201 : invRung 7 5 20 [1, 1, 0, 2, 2, 0, 1] [1, 2, 1, 1, 2, 0, 2] 3 1 true = ([0, 1, 0, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_1102201 : fieldCube 7 5 20 [0, 1, 0, 1, 1, 2, 2] = [0, 2, 1, 1, 1, 0, 1] := by
  decide

theorem demoM_1102201 : fieldMul 7 5 20 [0, 2, 1, 1, 1, 0, 1] [1, 1, 0, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1102201 : specInv 7 5 20 [1, 1, 0, 2, 2, 0, 1] = some [0, 2, 1, 1, 1, 0, 1] :=
  specInv_white_7 [1, 1, 0, 2, 2, 0, 1] [1, 2, 1, 1, 2, 0, 2] [0, 1, 0, 1, 1, 2, 2] [0, 2, 1, 1, 1, 0, 1] demoR1_1102201 demoR2_1102201 demoC_1102201 demoM_1102201

theorem demoR1_2102201 : invRung 7 5 20 [2, 1, 0, 2, 2, 0, 1] [2, 1, 0, 2, 2, 0, 1] 1 2 false = ([0, 2, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2102201 : invRung 7 5 20 [2, 1, 0, 2, 2, 0, 1] [0, 2, 1, 1, 0, 0, 2] 3 1 true = ([0, 1, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoC_2102201 : fieldCube 7 5 20 [0, 1, 2, 1, 2, 0, 0] = [1, 2, 1, 0, 0, 0, 1] := by
  decide

theorem demoM_2102201 : fieldMul 7 5 20 [1, 2, 1, 0, 0, 0, 1] [2, 1, 0, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2102201 : specInv 7 5 20 [2, 1, 0, 2, 2, 0, 1] = some [1, 2, 1, 0, 0, 0, 1] :=
  specInv_white_7 [2, 1, 0, 2, 2, 0, 1] [0, 2, 1, 1, 0, 0, 2] [0, 1, 2, 1, 2, 0, 0] [1, 2, 1, 0, 0, 0, 1] demoR1_2102201 demoR2_2102201 demoC_2102201 demoM_2102201

theorem demoR1_0202201 : invRung 7 5 20 [0, 2, 0, 2, 2, 0, 1] [0, 2, 0, 2, 2, 0, 1] 1 2 false = ([0, 1, 1, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0202201 : invRung 7 5 20 [0, 2, 0, 2, 2, 0, 1] [0, 1, 1, 0, 1, 1, 1] 3 1 true = ([0, 2, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_0202201 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 1, 2] = [1, 1, 2, 2, 0, 1, 1] := by
  decide

theorem demoM_0202201 : fieldMul 7 5 20 [1, 1, 2, 2, 0, 1, 1] [0, 2, 0, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0202201 : mirrorTrits [1, 1, 2, 2, 0, 1, 1] = [2, 2, 1, 1, 0, 2, 2] := by
  decide

theorem demoInv_0202201 : specInv 7 5 20 [0, 2, 0, 2, 2, 0, 1] = some [2, 2, 1, 1, 0, 2, 2] :=
  specInv_mirror_7 [0, 2, 0, 2, 2, 0, 1] [0, 1, 1, 0, 1, 1, 1] [0, 2, 2, 0, 1, 1, 2] [1, 1, 2, 2, 0, 1, 1] [2, 2, 1, 1, 0, 2, 2] demoR1_0202201 demoR2_0202201 demoC_0202201 demoM_0202201 demoMir_0202201

theorem demoR1_1202201 : invRung 7 5 20 [1, 2, 0, 2, 2, 0, 1] [1, 2, 0, 2, 2, 0, 1] 1 2 false = ([0, 2, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoR2_1202201 : invRung 7 5 20 [1, 2, 0, 2, 2, 0, 1] [0, 2, 2, 1, 1, 1, 1] 3 1 true = ([0, 1, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_1202201 : fieldCube 7 5 20 [0, 1, 0, 1, 2, 1, 2] = [2, 2, 0, 2, 0, 0, 0] := by
  decide

theorem demoM_1202201 : fieldMul 7 5 20 [2, 2, 0, 2, 0, 0, 0] [1, 2, 0, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1202201 : specInv 7 5 20 [1, 2, 0, 2, 2, 0, 1] = some [2, 2, 0, 2, 0, 0, 0] :=
  specInv_white_7 [1, 2, 0, 2, 2, 0, 1] [0, 2, 2, 1, 1, 1, 1] [0, 1, 0, 1, 2, 1, 2] [2, 2, 0, 2, 0, 0, 0] demoR1_1202201 demoR2_1202201 demoC_1202201 demoM_1202201

theorem demoR1_2202201 : invRung 7 5 20 [2, 2, 0, 2, 2, 0, 1] [2, 2, 0, 2, 2, 0, 1] 1 2 false = ([1, 1, 1, 0, 2, 0, 0], 3) := by
  decide

theorem demoR2_2202201 : invRung 7 5 20 [2, 2, 0, 2, 2, 0, 1] [1, 1, 1, 0, 2, 0, 0] 3 1 true = ([2, 0, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2202201 : fieldCube 7 5 20 [2, 0, 2, 1, 1, 2, 1] = [2, 1, 2, 2, 0, 2, 2] := by
  decide

theorem demoM_2202201 : fieldMul 7 5 20 [2, 1, 2, 2, 0, 2, 2] [2, 2, 0, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2202201 : specInv 7 5 20 [2, 2, 0, 2, 2, 0, 1] = some [2, 1, 2, 2, 0, 2, 2] :=
  specInv_white_7 [2, 2, 0, 2, 2, 0, 1] [1, 1, 1, 0, 2, 0, 0] [2, 0, 2, 1, 1, 2, 1] [2, 1, 2, 2, 0, 2, 2] demoR1_2202201 demoR2_2202201 demoC_2202201 demoM_2202201

theorem demoR1_0012201 : invRung 7 5 20 [0, 0, 1, 2, 2, 0, 1] [0, 0, 1, 2, 2, 0, 1] 1 2 false = ([2, 2, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0012201 : invRung 7 5 20 [0, 0, 1, 2, 2, 0, 1] [2, 2, 1, 0, 0, 0, 0] 3 1 true = ([1, 2, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_0012201 : fieldCube 7 5 20 [1, 2, 0, 2, 2, 2, 1] = [2, 2, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_0012201 : fieldMul 7 5 20 [2, 2, 0, 2, 0, 1, 1] [0, 0, 1, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0012201 : mirrorTrits [2, 2, 0, 2, 0, 1, 1] = [1, 1, 0, 1, 0, 2, 2] := by
  decide

theorem demoInv_0012201 : specInv 7 5 20 [0, 0, 1, 2, 2, 0, 1] = some [1, 1, 0, 1, 0, 2, 2] :=
  specInv_mirror_7 [0, 0, 1, 2, 2, 0, 1] [2, 2, 1, 0, 0, 0, 0] [1, 2, 0, 2, 2, 2, 1] [2, 2, 0, 2, 0, 1, 1] [1, 1, 0, 1, 0, 2, 2] demoR1_0012201 demoR2_0012201 demoC_0012201 demoM_0012201 demoMir_0012201

theorem demoR1_1012201 : invRung 7 5 20 [1, 0, 1, 2, 2, 0, 1] [1, 0, 1, 2, 2, 0, 1] 1 2 false = ([0, 1, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_1012201 : invRung 7 5 20 [1, 0, 1, 2, 2, 0, 1] [0, 1, 1, 0, 0, 1, 2] 3 1 true = ([0, 2, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1012201 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 2, 1] = [0, 0, 2, 0, 0, 1, 2] := by
  decide

theorem demoM_1012201 : fieldMul 7 5 20 [0, 0, 2, 0, 0, 1, 2] [1, 0, 1, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1012201 : mirrorTrits [0, 0, 2, 0, 0, 1, 2] = [0, 0, 1, 0, 0, 2, 1] := by
  decide

theorem demoInv_1012201 : specInv 7 5 20 [1, 0, 1, 2, 2, 0, 1] = some [0, 0, 1, 0, 0, 2, 1] :=
  specInv_mirror_7 [1, 0, 1, 2, 2, 0, 1] [0, 1, 1, 0, 0, 1, 2] [0, 2, 0, 1, 0, 2, 1] [0, 0, 2, 0, 0, 1, 2] [0, 0, 1, 0, 0, 2, 1] demoR1_1012201 demoR2_1012201 demoC_1012201 demoM_1012201 demoMir_1012201

theorem demoR1_2012201 : invRung 7 5 20 [2, 0, 1, 2, 2, 0, 1] [2, 0, 1, 2, 2, 0, 1] 1 2 false = ([1, 2, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_2012201 : invRung 7 5 20 [2, 0, 1, 2, 2, 0, 1] [1, 2, 1, 2, 0, 2, 1] 3 1 true = ([1, 0, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_2012201 : fieldCube 7 5 20 [1, 0, 0, 1, 2, 1, 1] = [0, 1, 1, 0, 2, 2, 2] := by
  decide

theorem demoM_2012201 : fieldMul 7 5 20 [0, 1, 1, 0, 2, 2, 2] [2, 0, 1, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012201 : mirrorTrits [0, 1, 1, 0, 2, 2, 2] = [0, 2, 2, 0, 1, 1, 1] := by
  decide

theorem demoInv_2012201 : specInv 7 5 20 [2, 0, 1, 2, 2, 0, 1] = some [0, 2, 2, 0, 1, 1, 1] :=
  specInv_mirror_7 [2, 0, 1, 2, 2, 0, 1] [1, 2, 1, 2, 0, 2, 1] [1, 0, 0, 1, 2, 1, 1] [0, 1, 1, 0, 2, 2, 2] [0, 2, 2, 0, 1, 1, 1] demoR1_2012201 demoR2_2012201 demoC_2012201 demoM_2012201 demoMir_2012201

theorem demoR1_0112201 : invRung 7 5 20 [0, 1, 1, 2, 2, 0, 1] [0, 1, 1, 2, 2, 0, 1] 1 2 false = ([1, 0, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_0112201 : invRung 7 5 20 [0, 1, 1, 2, 2, 0, 1] [1, 0, 0, 1, 0, 1, 1] 3 1 true = ([2, 0, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0112201 : fieldCube 7 5 20 [2, 0, 0, 0, 2, 2, 2] = [1, 0, 0, 1, 1, 0, 2] := by
  decide

theorem demoM_0112201 : fieldMul 7 5 20 [1, 0, 0, 1, 1, 0, 2] [0, 1, 1, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112201 : mirrorTrits [1, 0, 0, 1, 1, 0, 2] = [2, 0, 0, 2, 2, 0, 1] := by
  decide

theorem demoInv_0112201 : specInv 7 5 20 [0, 1, 1, 2, 2, 0, 1] = some [2, 0, 0, 2, 2, 0, 1] :=
  specInv_mirror_7 [0, 1, 1, 2, 2, 0, 1] [1, 0, 0, 1, 0, 1, 1] [2, 0, 0, 0, 2, 2, 2] [1, 0, 0, 1, 1, 0, 2] [2, 0, 0, 2, 2, 0, 1] demoR1_0112201 demoR2_0112201 demoC_0112201 demoM_0112201 demoMir_0112201

theorem demoR1_1112201 : invRung 7 5 20 [1, 1, 1, 2, 2, 0, 1] [1, 1, 1, 2, 2, 0, 1] 1 2 false = ([2, 0, 1, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1112201 : invRung 7 5 20 [1, 1, 1, 2, 2, 0, 1] [2, 0, 1, 2, 2, 1, 0] 3 1 true = ([1, 2, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_1112201 : fieldCube 7 5 20 [1, 2, 0, 1, 0, 1, 0] = [0, 1, 2, 2, 1, 2, 2] := by
  decide

theorem demoM_1112201 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 2, 2] [1, 1, 1, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112201 : mirrorTrits [0, 1, 2, 2, 1, 2, 2] = [0, 2, 1, 1, 2, 1, 1] := by
  decide

theorem demoInv_1112201 : specInv 7 5 20 [1, 1, 1, 2, 2, 0, 1] = some [0, 2, 1, 1, 2, 1, 1] :=
  specInv_mirror_7 [1, 1, 1, 2, 2, 0, 1] [2, 0, 1, 2, 2, 1, 0] [1, 2, 0, 1, 0, 1, 0] [0, 1, 2, 2, 1, 2, 2] [0, 2, 1, 1, 2, 1, 1] demoR1_1112201 demoR2_1112201 demoC_1112201 demoM_1112201 demoMir_1112201

theorem demoR1_2112201 : invRung 7 5 20 [2, 1, 1, 2, 2, 0, 1] [2, 1, 1, 2, 2, 0, 1] 1 2 false = ([2, 1, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_2112201 : invRung 7 5 20 [2, 1, 1, 2, 2, 0, 1] [2, 1, 1, 1, 1, 0, 2] 3 1 true = ([0, 2, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_2112201 : fieldCube 7 5 20 [0, 2, 0, 0, 0, 1, 1] = [1, 2, 0, 0, 2, 2, 0] := by
  decide

theorem demoM_2112201 : fieldMul 7 5 20 [1, 2, 0, 0, 2, 2, 0] [2, 1, 1, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2112201 : specInv 7 5 20 [2, 1, 1, 2, 2, 0, 1] = some [1, 2, 0, 0, 2, 2, 0] :=
  specInv_white_7 [2, 1, 1, 2, 2, 0, 1] [2, 1, 1, 1, 1, 0, 2] [0, 2, 0, 0, 0, 1, 1] [1, 2, 0, 0, 2, 2, 0] demoR1_2112201 demoR2_2112201 demoC_2112201 demoM_2112201

theorem demoR1_0212201 : invRung 7 5 20 [0, 2, 1, 2, 2, 0, 1] [0, 2, 1, 2, 2, 0, 1] 1 2 false = ([0, 2, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_0212201 : invRung 7 5 20 [0, 2, 1, 2, 2, 0, 1] [0, 2, 1, 1, 0, 0, 1] 3 1 true = ([0, 1, 2, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_0212201 : fieldCube 7 5 20 [0, 1, 2, 2, 1, 0, 0] = [2, 1, 2, 2, 0, 0, 0] := by
  decide

theorem demoM_0212201 : fieldMul 7 5 20 [2, 1, 2, 2, 0, 0, 0] [0, 2, 1, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0212201 : specInv 7 5 20 [0, 2, 1, 2, 2, 0, 1] = some [2, 1, 2, 2, 0, 0, 0] :=
  specInv_white_7 [0, 2, 1, 2, 2, 0, 1] [0, 2, 1, 1, 0, 0, 1] [0, 1, 2, 2, 1, 0, 0] [2, 1, 2, 2, 0, 0, 0] demoR1_0212201 demoR2_0212201 demoC_0212201 demoM_0212201

theorem demoR1_1212201 : invRung 7 5 20 [1, 2, 1, 2, 2, 0, 1] [1, 2, 1, 2, 2, 0, 1] 1 2 false = ([1, 1, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_1212201 : invRung 7 5 20 [1, 2, 1, 2, 2, 0, 1] [1, 1, 0, 1, 0, 1, 1] 3 1 true = ([1, 0, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_1212201 : fieldCube 7 5 20 [1, 0, 1, 0, 1, 1, 2] = [2, 1, 2, 0, 0, 1, 0] := by
  decide

theorem demoM_1212201 : fieldMul 7 5 20 [2, 1, 2, 0, 0, 1, 0] [1, 2, 1, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1212201 : specInv 7 5 20 [1, 2, 1, 2, 2, 0, 1] = some [2, 1, 2, 0, 0, 1, 0] :=
  specInv_white_7 [1, 2, 1, 2, 2, 0, 1] [1, 1, 0, 1, 0, 1, 1] [1, 0, 1, 0, 1, 1, 2] [2, 1, 2, 0, 0, 1, 0] demoR1_1212201 demoR2_1212201 demoC_1212201 demoM_1212201

theorem demoR1_2212201 : invRung 7 5 20 [2, 2, 1, 2, 2, 0, 1] [2, 2, 1, 2, 2, 0, 1] 1 2 false = ([0, 0, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_2212201 : invRung 7 5 20 [2, 2, 1, 2, 2, 0, 1] [0, 0, 0, 1, 0, 0, 1] 3 1 true = ([1, 0, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_2212201 : fieldCube 7 5 20 [1, 0, 0, 2, 1, 0, 1] = [0, 2, 1, 2, 1, 1, 2] := by
  decide

theorem demoM_2212201 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 1, 2] [2, 2, 1, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2212201 : specInv 7 5 20 [2, 2, 1, 2, 2, 0, 1] = some [0, 2, 1, 2, 1, 1, 2] :=
  specInv_white_7 [2, 2, 1, 2, 2, 0, 1] [0, 0, 0, 1, 0, 0, 1] [1, 0, 0, 2, 1, 0, 1] [0, 2, 1, 2, 1, 1, 2] demoR1_2212201 demoR2_2212201 demoC_2212201 demoM_2212201

theorem demoR1_0022201 : invRung 7 5 20 [0, 0, 2, 2, 2, 0, 1] [0, 0, 2, 2, 2, 0, 1] 1 2 false = ([0, 2, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_0022201 : invRung 7 5 20 [0, 0, 2, 2, 2, 0, 1] [0, 2, 1, 2, 2, 1, 2] 3 1 true = ([1, 0, 1, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_0022201 : fieldCube 7 5 20 [1, 0, 1, 1, 2, 2, 0] = [1, 1, 0, 2, 2, 2, 1] := by
  decide

theorem demoM_0022201 : fieldMul 7 5 20 [1, 1, 0, 2, 2, 2, 1] [0, 0, 2, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0022201 : mirrorTrits [1, 1, 0, 2, 2, 2, 1] = [2, 2, 0, 1, 1, 1, 2] := by
  decide

theorem demoInv_0022201 : specInv 7 5 20 [0, 0, 2, 2, 2, 0, 1] = some [2, 2, 0, 1, 1, 1, 2] :=
  specInv_mirror_7 [0, 0, 2, 2, 2, 0, 1] [0, 2, 1, 2, 2, 1, 2] [1, 0, 1, 1, 2, 2, 0] [1, 1, 0, 2, 2, 2, 1] [2, 2, 0, 1, 1, 1, 2] demoR1_0022201 demoR2_0022201 demoC_0022201 demoM_0022201 demoMir_0022201

theorem demoR1_1022201 : invRung 7 5 20 [1, 0, 2, 2, 2, 0, 1] [1, 0, 2, 2, 2, 0, 1] 1 2 false = ([1, 1, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_1022201 : invRung 7 5 20 [1, 0, 2, 2, 2, 0, 1] [1, 1, 1, 0, 0, 1, 2] 3 1 true = ([0, 2, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoC_1022201 : fieldCube 7 5 20 [0, 2, 1, 0, 0, 1, 2] = [1, 0, 2, 1, 0, 0, 2] := by
  decide

theorem demoM_1022201 : fieldMul 7 5 20 [1, 0, 2, 1, 0, 0, 2] [1, 0, 2, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1022201 : mirrorTrits [1, 0, 2, 1, 0, 0, 2] = [2, 0, 1, 2, 0, 0, 1] := by
  decide

theorem demoInv_1022201 : specInv 7 5 20 [1, 0, 2, 2, 2, 0, 1] = some [2, 0, 1, 2, 0, 0, 1] :=
  specInv_mirror_7 [1, 0, 2, 2, 2, 0, 1] [1, 1, 1, 0, 0, 1, 2] [0, 2, 1, 0, 0, 1, 2] [1, 0, 2, 1, 0, 0, 2] [2, 0, 1, 2, 0, 0, 1] demoR1_1022201 demoR2_1022201 demoC_1022201 demoM_1022201 demoMir_1022201

theorem demoR1_2022201 : invRung 7 5 20 [2, 0, 2, 2, 2, 0, 1] [2, 0, 2, 2, 2, 0, 1] 1 2 false = ([2, 1, 1, 2, 0, 0, 0], 3) := by
  decide

theorem demoR2_2022201 : invRung 7 5 20 [2, 0, 2, 2, 2, 0, 1] [2, 1, 1, 2, 0, 0, 0] 3 1 true = ([1, 0, 2, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_2022201 : fieldCube 7 5 20 [1, 0, 2, 2, 1, 0, 1] = [0, 2, 1, 2, 1, 1, 1] := by
  decide

theorem demoM_2022201 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 1, 1] [2, 0, 2, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2022201 : mirrorTrits [0, 2, 1, 2, 1, 1, 1] = [0, 1, 2, 1, 2, 2, 2] := by
  decide

theorem demoInv_2022201 : specInv 7 5 20 [2, 0, 2, 2, 2, 0, 1] = some [0, 1, 2, 1, 2, 2, 2] :=
  specInv_mirror_7 [2, 0, 2, 2, 2, 0, 1] [2, 1, 1, 2, 0, 0, 0] [1, 0, 2, 2, 1, 0, 1] [0, 2, 1, 2, 1, 1, 1] [0, 1, 2, 1, 2, 2, 2] demoR1_2022201 demoR2_2022201 demoC_2022201 demoM_2022201 demoMir_2022201

theorem demoR1_0122201 : invRung 7 5 20 [0, 1, 2, 2, 2, 0, 1] [0, 1, 2, 2, 2, 0, 1] 1 2 false = ([1, 2, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_0122201 : invRung 7 5 20 [0, 1, 2, 2, 2, 0, 1] [1, 2, 1, 2, 2, 1, 2] 3 1 true = ([2, 1, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_0122201 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 2, 0] = [0, 0, 1, 2, 2, 2, 2] := by
  decide

theorem demoM_0122201 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 2, 2] [0, 1, 2, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0122201 : mirrorTrits [0, 0, 1, 2, 2, 2, 2] = [0, 0, 2, 1, 1, 1, 1] := by
  decide

theorem demoInv_0122201 : specInv 7 5 20 [0, 1, 2, 2, 2, 0, 1] = some [0, 0, 2, 1, 1, 1, 1] :=
  specInv_mirror_7 [0, 1, 2, 2, 2, 0, 1] [1, 2, 1, 2, 2, 1, 2] [2, 1, 0, 2, 1, 2, 0] [0, 0, 1, 2, 2, 2, 2] [0, 0, 2, 1, 1, 1, 1] demoR1_0122201 demoR2_0122201 demoC_0122201 demoM_0122201 demoMir_0122201

theorem demoR1_1122201 : invRung 7 5 20 [1, 1, 2, 2, 2, 0, 1] [1, 1, 2, 2, 2, 0, 1] 1 2 false = ([2, 1, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoR2_1122201 : invRung 7 5 20 [1, 1, 2, 2, 2, 0, 1] [2, 1, 0, 0, 0, 1, 1] 3 1 true = ([1, 1, 1, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_1122201 : fieldCube 7 5 20 [1, 1, 1, 1, 0, 2, 2] = [1, 1, 1, 0, 1, 2, 1] := by
  decide

theorem demoM_1122201 : fieldMul 7 5 20 [1, 1, 1, 0, 1, 2, 1] [1, 1, 2, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1122201 : mirrorTrits [1, 1, 1, 0, 1, 2, 1] = [2, 2, 2, 0, 2, 1, 2] := by
  decide

theorem demoInv_1122201 : specInv 7 5 20 [1, 1, 2, 2, 2, 0, 1] = some [2, 2, 2, 0, 2, 1, 2] :=
  specInv_mirror_7 [1, 1, 2, 2, 2, 0, 1] [2, 1, 0, 0, 0, 1, 1] [1, 1, 1, 1, 0, 2, 2] [1, 1, 1, 0, 1, 2, 1] [2, 2, 2, 0, 2, 1, 2] demoR1_1122201 demoR2_1122201 demoC_1122201 demoM_1122201 demoMir_1122201

theorem demoR1_2122201 : invRung 7 5 20 [2, 1, 2, 2, 2, 0, 1] [2, 1, 2, 2, 2, 0, 1] 1 2 false = ([2, 0, 1, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_2122201 : invRung 7 5 20 [2, 1, 2, 2, 2, 0, 1] [2, 0, 1, 1, 0, 2, 1] 3 1 true = ([2, 1, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_2122201 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 1, 2] = [2, 1, 1, 1, 0, 0, 2] := by
  decide

theorem demoM_2122201 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 0, 2] [2, 1, 2, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122201 : mirrorTrits [2, 1, 1, 1, 0, 0, 2] = [1, 2, 2, 2, 0, 0, 1] := by
  decide

theorem demoInv_2122201 : specInv 7 5 20 [2, 1, 2, 2, 2, 0, 1] = some [1, 2, 2, 2, 0, 0, 1] :=
  specInv_mirror_7 [2, 1, 2, 2, 2, 0, 1] [2, 0, 1, 1, 0, 2, 1] [2, 1, 0, 2, 1, 1, 2] [2, 1, 1, 1, 0, 0, 2] [1, 2, 2, 2, 0, 0, 1] demoR1_2122201 demoR2_2122201 demoC_2122201 demoM_2122201 demoMir_2122201

theorem demoR1_0222201 : invRung 7 5 20 [0, 2, 2, 2, 2, 0, 1] [0, 2, 2, 2, 2, 0, 1] 1 2 false = ([0, 2, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_0222201 : invRung 7 5 20 [0, 2, 2, 2, 2, 0, 1] [0, 2, 1, 1, 2, 0, 1] 3 1 true = ([0, 2, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_0222201 : fieldCube 7 5 20 [0, 2, 0, 1, 1, 1, 2] = [2, 1, 0, 2, 0, 2, 2] := by
  decide

theorem demoM_0222201 : fieldMul 7 5 20 [2, 1, 0, 2, 0, 2, 2] [0, 2, 2, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0222201 : specInv 7 5 20 [0, 2, 2, 2, 2, 0, 1] = some [2, 1, 0, 2, 0, 2, 2] :=
  specInv_white_7 [0, 2, 2, 2, 2, 0, 1] [0, 2, 1, 1, 2, 0, 1] [0, 2, 0, 1, 1, 1, 2] [2, 1, 0, 2, 0, 2, 2] demoR1_0222201 demoR2_0222201 demoC_0222201 demoM_0222201

theorem demoR1_1222201 : invRung 7 5 20 [1, 2, 2, 2, 2, 0, 1] [1, 2, 2, 2, 2, 0, 1] 1 2 false = ([1, 2, 2, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_1222201 : invRung 7 5 20 [1, 2, 2, 2, 2, 0, 1] [1, 2, 2, 0, 2, 2, 0] 3 1 true = ([1, 2, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoC_1222201 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 1, 1] = [1, 0, 2, 1, 2, 2, 2] := by
  decide

theorem demoM_1222201 : fieldMul 7 5 20 [1, 0, 2, 1, 2, 2, 2] [1, 2, 2, 2, 2, 0, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222201 : mirrorTrits [1, 0, 2, 1, 2, 2, 2] = [2, 0, 1, 2, 1, 1, 1] := by
  decide

theorem demoInv_1222201 : specInv 7 5 20 [1, 2, 2, 2, 2, 0, 1] = some [2, 0, 1, 2, 1, 1, 1] :=
  specInv_mirror_7 [1, 2, 2, 2, 2, 0, 1] [1, 2, 2, 0, 2, 2, 0] [1, 2, 1, 2, 1, 1, 1] [1, 0, 2, 1, 2, 2, 2] [2, 0, 1, 2, 1, 1, 1] demoR1_1222201 demoR2_1222201 demoC_1222201 demoM_1222201 demoMir_1222201

theorem demoR1_2222201 : invRung 7 5 20 [2, 2, 2, 2, 2, 0, 1] [2, 2, 2, 2, 2, 0, 1] 1 2 false = ([0, 1, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoR2_2222201 : invRung 7 5 20 [2, 2, 2, 2, 2, 0, 1] [0, 1, 1, 1, 1, 1, 0] 3 1 true = ([2, 0, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_2222201 : fieldCube 7 5 20 [2, 0, 1, 1, 1, 0, 2] = [0, 0, 2, 0, 2, 1, 1] := by
  decide

theorem demoM_2222201 : fieldMul 7 5 20 [0, 0, 2, 0, 2, 1, 1] [2, 2, 2, 2, 2, 0, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2222201 : specInv 7 5 20 [2, 2, 2, 2, 2, 0, 1] = some [0, 0, 2, 0, 2, 1, 1] :=
  specInv_white_7 [2, 2, 2, 2, 2, 0, 1] [0, 1, 1, 1, 1, 1, 0] [2, 0, 1, 1, 1, 0, 2] [0, 0, 2, 0, 2, 1, 1] demoR1_2222201 demoR2_2222201 demoC_2222201 demoM_2222201

theorem demoR1_0000011 : invRung 7 5 20 [0, 0, 0, 0, 0, 1, 1] [0, 0, 0, 0, 0, 1, 1] 1 2 false = ([1, 1, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_0000011 : invRung 7 5 20 [0, 0, 0, 0, 0, 1, 1] [1, 1, 0, 0, 2, 0, 2] 3 1 true = ([1, 1, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0000011 : fieldCube 7 5 20 [1, 1, 0, 2, 1, 2, 1] = [2, 1, 0, 0, 0, 0, 0] := by
  decide

theorem demoM_0000011 : fieldMul 7 5 20 [2, 1, 0, 0, 0, 0, 0] [0, 0, 0, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0000011 : specInv 7 5 20 [0, 0, 0, 0, 0, 1, 1] = some [2, 1, 0, 0, 0, 0, 0] :=
  specInv_white_7 [0, 0, 0, 0, 0, 1, 1] [1, 1, 0, 0, 2, 0, 2] [1, 1, 0, 2, 1, 2, 1] [2, 1, 0, 0, 0, 0, 0] demoR1_0000011 demoR2_0000011 demoC_0000011 demoM_0000011

theorem demoR1_1000011 : invRung 7 5 20 [1, 0, 0, 0, 0, 1, 1] [1, 0, 0, 0, 0, 1, 1] 1 2 false = ([0, 2, 2, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_1000011 : invRung 7 5 20 [1, 0, 0, 0, 0, 1, 1] [0, 2, 2, 1, 2, 0, 1] 3 1 true = ([2, 2, 0, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_1000011 : fieldCube 7 5 20 [2, 2, 0, 0, 2, 2, 2] = [1, 0, 0, 0, 1, 0, 2] := by
  decide

theorem demoM_1000011 : fieldMul 7 5 20 [1, 0, 0, 0, 1, 0, 2] [1, 0, 0, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1000011 : specInv 7 5 20 [1, 0, 0, 0, 0, 1, 1] = some [1, 0, 0, 0, 1, 0, 2] :=
  specInv_white_7 [1, 0, 0, 0, 0, 1, 1] [0, 2, 2, 1, 2, 0, 1] [2, 2, 0, 0, 2, 2, 2] [1, 0, 0, 0, 1, 0, 2] demoR1_1000011 demoR2_1000011 demoC_1000011 demoM_1000011

theorem demoR1_2000011 : invRung 7 5 20 [2, 0, 0, 0, 0, 1, 1] [2, 0, 0, 0, 0, 1, 1] 1 2 false = ([0, 0, 1, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2000011 : invRung 7 5 20 [2, 0, 0, 0, 0, 1, 1] [0, 0, 1, 0, 1, 1, 2] 3 1 true = ([0, 2, 2, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_2000011 : fieldCube 7 5 20 [0, 2, 2, 2, 0, 2, 1] = [1, 0, 0, 0, 0, 2, 1] := by
  decide

theorem demoM_2000011 : fieldMul 7 5 20 [1, 0, 0, 0, 0, 2, 1] [2, 0, 0, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2000011 : mirrorTrits [1, 0, 0, 0, 0, 2, 1] = [2, 0, 0, 0, 0, 1, 2] := by
  decide

theorem demoInv_2000011 : specInv 7 5 20 [2, 0, 0, 0, 0, 1, 1] = some [2, 0, 0, 0, 0, 1, 2] :=
  specInv_mirror_7 [2, 0, 0, 0, 0, 1, 1] [0, 0, 1, 0, 1, 1, 2] [0, 2, 2, 2, 0, 2, 1] [1, 0, 0, 0, 0, 2, 1] [2, 0, 0, 0, 0, 1, 2] demoR1_2000011 demoR2_2000011 demoC_2000011 demoM_2000011 demoMir_2000011

theorem demoR1_0100011 : invRung 7 5 20 [0, 1, 0, 0, 0, 1, 1] [0, 1, 0, 0, 0, 1, 1] 1 2 false = ([2, 2, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0100011 : invRung 7 5 20 [0, 1, 0, 0, 0, 1, 1] [2, 2, 1, 2, 1, 2, 1] 3 1 true = ([2, 0, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0100011 : fieldCube 7 5 20 [2, 0, 1, 2, 1, 0, 1] = [1, 2, 1, 2, 1, 1, 0] := by
  decide

theorem demoM_0100011 : fieldMul 7 5 20 [1, 2, 1, 2, 1, 1, 0] [0, 1, 0, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0100011 : specInv 7 5 20 [0, 1, 0, 0, 0, 1, 1] = some [1, 2, 1, 2, 1, 1, 0] :=
  specInv_white_7 [0, 1, 0, 0, 0, 1, 1] [2, 2, 1, 2, 1, 2, 1] [2, 0, 1, 2, 1, 0, 1] [1, 2, 1, 2, 1, 1, 0] demoR1_0100011 demoR2_0100011 demoC_0100011 demoM_0100011

theorem demoR1_1100011 : invRung 7 5 20 [1, 1, 0, 0, 0, 1, 1] [1, 1, 0, 0, 0, 1, 1] 1 2 false = ([0, 0, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_1100011 : invRung 7 5 20 [1, 1, 0, 0, 0, 1, 1] [0, 0, 0, 1, 2, 1, 2] 3 1 true = ([1, 1, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoC_1100011 : fieldCube 7 5 20 [1, 1, 1, 2, 1, 0, 2] = [0, 0, 0, 1, 2, 2, 1] := by
  decide

theorem demoM_1100011 : fieldMul 7 5 20 [0, 0, 0, 1, 2, 2, 1] [1, 1, 0, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1100011 : specInv 7 5 20 [1, 1, 0, 0, 0, 1, 1] = some [0, 0, 0, 1, 2, 2, 1] :=
  specInv_white_7 [1, 1, 0, 0, 0, 1, 1] [0, 0, 0, 1, 2, 1, 2] [1, 1, 1, 2, 1, 0, 2] [0, 0, 0, 1, 2, 2, 1] demoR1_1100011 demoR2_1100011 demoC_1100011 demoM_1100011

theorem demoR1_2100011 : invRung 7 5 20 [2, 1, 0, 0, 0, 1, 1] [2, 1, 0, 0, 0, 1, 1] 1 2 false = ([1, 0, 1, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2100011 : invRung 7 5 20 [2, 1, 0, 0, 0, 1, 1] [1, 0, 1, 0, 2, 0, 2] 3 1 true = ([1, 0, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_2100011 : fieldCube 7 5 20 [1, 0, 0, 1, 0, 0, 1] = [2, 1, 0, 1, 1, 2, 1] := by
  decide

theorem demoM_2100011 : fieldMul 7 5 20 [2, 1, 0, 1, 1, 2, 1] [2, 1, 0, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2100011 : mirrorTrits [2, 1, 0, 1, 1, 2, 1] = [1, 2, 0, 2, 2, 1, 2] := by
  decide

theorem demoInv_2100011 : specInv 7 5 20 [2, 1, 0, 0, 0, 1, 1] = some [1, 2, 0, 2, 2, 1, 2] :=
  specInv_mirror_7 [2, 1, 0, 0, 0, 1, 1] [1, 0, 1, 0, 2, 0, 2] [1, 0, 0, 1, 0, 0, 1] [2, 1, 0, 1, 1, 2, 1] [1, 2, 0, 2, 2, 1, 2] demoR1_2100011 demoR2_2100011 demoC_2100011 demoM_2100011 demoMir_2100011

theorem demoR1_0200011 : invRung 7 5 20 [0, 2, 0, 0, 0, 1, 1] [0, 2, 0, 0, 0, 1, 1] 1 2 false = ([1, 2, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_0200011 : invRung 7 5 20 [0, 2, 0, 0, 0, 1, 1] [1, 2, 1, 2, 1, 1, 1] 3 1 true = ([0, 1, 1, 2, 1, 2, 0], 3) := by
  decide

theorem demoC_0200011 : fieldCube 7 5 20 [0, 1, 1, 2, 1, 2, 0] = [1, 0, 1, 2, 2, 2, 0] := by
  decide

theorem demoM_0200011 : fieldMul 7 5 20 [1, 0, 1, 2, 2, 2, 0] [0, 2, 0, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0200011 : specInv 7 5 20 [0, 2, 0, 0, 0, 1, 1] = some [1, 0, 1, 2, 2, 2, 0] :=
  specInv_white_7 [0, 2, 0, 0, 0, 1, 1] [1, 2, 1, 2, 1, 1, 1] [0, 1, 1, 2, 1, 2, 0] [1, 0, 1, 2, 2, 2, 0] demoR1_0200011 demoR2_0200011 demoC_0200011 demoM_0200011

theorem demoR1_1200011 : invRung 7 5 20 [1, 2, 0, 0, 0, 1, 1] [1, 2, 0, 0, 0, 1, 1] 1 2 false = ([1, 1, 0, 0, 2, 1, 2], 3) := by
  decide

theorem demoR2_1200011 : invRung 7 5 20 [1, 2, 0, 0, 0, 1, 1] [1, 1, 0, 0, 2, 1, 2] 3 1 true = ([2, 0, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_1200011 : fieldCube 7 5 20 [2, 0, 1, 1, 2, 0, 1] = [0, 0, 0, 0, 1, 1, 1] := by
  decide

theorem demoM_1200011 : fieldMul 7 5 20 [0, 0, 0, 0, 1, 1, 1] [1, 2, 0, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1200011 : mirrorTrits [0, 0, 0, 0, 1, 1, 1] = [0, 0, 0, 0, 2, 2, 2] := by
  decide

theorem demoInv_1200011 : specInv 7 5 20 [1, 2, 0, 0, 0, 1, 1] = some [0, 0, 0, 0, 2, 2, 2] :=
  specInv_mirror_7 [1, 2, 0, 0, 0, 1, 1] [1, 1, 0, 0, 2, 1, 2] [2, 0, 1, 1, 2, 0, 1] [0, 0, 0, 0, 1, 1, 1] [0, 0, 0, 0, 2, 2, 2] demoR1_1200011 demoR2_1200011 demoC_1200011 demoM_1200011 demoMir_1200011

theorem demoR1_2200011 : invRung 7 5 20 [2, 2, 0, 0, 0, 1, 1] [2, 2, 0, 0, 0, 1, 1] 1 2 false = ([0, 1, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2200011 : invRung 7 5 20 [2, 2, 0, 0, 0, 1, 1] [0, 1, 0, 0, 2, 0, 2] 3 1 true = ([2, 1, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_2200011 : fieldCube 7 5 20 [2, 1, 2, 2, 2, 2, 1] = [0, 2, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_2200011 : fieldMul 7 5 20 [0, 2, 0, 1, 0, 1, 0] [2, 2, 0, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2200011 : specInv 7 5 20 [2, 2, 0, 0, 0, 1, 1] = some [0, 2, 0, 1, 0, 1, 0] :=
  specInv_white_7 [2, 2, 0, 0, 0, 1, 1] [0, 1, 0, 0, 2, 0, 2] [2, 1, 2, 2, 2, 2, 1] [0, 2, 0, 1, 0, 1, 0] demoR1_2200011 demoR2_2200011 demoC_2200011 demoM_2200011

theorem demoR1_0010011 : invRung 7 5 20 [0, 0, 1, 0, 0, 1, 1] [0, 0, 1, 0, 0, 1, 1] 1 2 false = ([0, 0, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_0010011 : invRung 7 5 20 [0, 0, 1, 0, 0, 1, 1] [0, 0, 1, 1, 1, 1, 2] 3 1 true = ([0, 0, 2, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_0010011 : fieldCube 7 5 20 [0, 0, 2, 0, 2, 1, 2] = [1, 2, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_0010011 : fieldMul 7 5 20 [1, 2, 2, 1, 0, 2, 2] [0, 0, 1, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0010011 : mirrorTrits [1, 2, 2, 1, 0, 2, 2] = [2, 1, 1, 2, 0, 1, 1] := by
  decide

theorem demoInv_0010011 : specInv 7 5 20 [0, 0, 1, 0, 0, 1, 1] = some [2, 1, 1, 2, 0, 1, 1] :=
  specInv_mirror_7 [0, 0, 1, 0, 0, 1, 1] [0, 0, 1, 1, 1, 1, 2] [0, 0, 2, 0, 2, 1, 2] [1, 2, 2, 1, 0, 2, 2] [2, 1, 1, 2, 0, 1, 1] demoR1_0010011 demoR2_0010011 demoC_0010011 demoM_0010011 demoMir_0010011

theorem demoR1_1010011 : invRung 7 5 20 [1, 0, 1, 0, 0, 1, 1] [1, 0, 1, 0, 0, 1, 1] 1 2 false = ([2, 0, 2, 0, 1, 0, 2], 3) := by
  decide

theorem demoR2_1010011 : invRung 7 5 20 [1, 0, 1, 0, 0, 1, 1] [2, 0, 2, 0, 1, 0, 2] 3 1 true = ([0, 0, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_1010011 : fieldCube 7 5 20 [0, 0, 0, 2, 1, 0, 0] = [2, 1, 2, 1, 0, 0, 1] := by
  decide

theorem demoM_1010011 : fieldMul 7 5 20 [2, 1, 2, 1, 0, 0, 1] [1, 0, 1, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1010011 : specInv 7 5 20 [1, 0, 1, 0, 0, 1, 1] = some [2, 1, 2, 1, 0, 0, 1] :=
  specInv_white_7 [1, 0, 1, 0, 0, 1, 1] [2, 0, 2, 0, 1, 0, 2] [0, 0, 0, 2, 1, 0, 0] [2, 1, 2, 1, 0, 0, 1] demoR1_1010011 demoR2_1010011 demoC_1010011 demoM_1010011

theorem demoR1_2010011 : invRung 7 5 20 [2, 0, 1, 0, 0, 1, 1] [2, 0, 1, 0, 0, 1, 1] 1 2 false = ([2, 2, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_2010011 : invRung 7 5 20 [2, 0, 1, 0, 0, 1, 1] [2, 2, 0, 2, 2, 2, 2] 3 1 true = ([2, 1, 1, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_2010011 : fieldCube 7 5 20 [2, 1, 1, 0, 1, 2, 0] = [1, 0, 2, 2, 2, 0, 0] := by
  decide

theorem demoM_2010011 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 0, 0] [2, 0, 1, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2010011 : mirrorTrits [1, 0, 2, 2, 2, 0, 0] = [2, 0, 1, 1, 1, 0, 0] := by
  decide

theorem demoInv_2010011 : specInv 7 5 20 [2, 0, 1, 0, 0, 1, 1] = some [2, 0, 1, 1, 1, 0, 0] :=
  specInv_mirror_7 [2, 0, 1, 0, 0, 1, 1] [2, 2, 0, 2, 2, 2, 2] [2, 1, 1, 0, 1, 2, 0] [1, 0, 2, 2, 2, 0, 0] [2, 0, 1, 1, 1, 0, 0] demoR1_2010011 demoR2_2010011 demoC_2010011 demoM_2010011 demoMir_2010011

theorem demoR1_0110011 : invRung 7 5 20 [0, 1, 1, 0, 0, 1, 1] [0, 1, 1, 0, 0, 1, 1] 1 2 false = ([2, 1, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_0110011 : invRung 7 5 20 [0, 1, 1, 0, 0, 1, 1] [2, 1, 2, 0, 0, 2, 0] 3 1 true = ([2, 2, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_0110011 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 0, 2] = [0, 0, 2, 2, 2, 1, 1] := by
  decide

theorem demoM_0110011 : fieldMul 7 5 20 [0, 0, 2, 2, 2, 1, 1] [0, 1, 1, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0110011 : specInv 7 5 20 [0, 1, 1, 0, 0, 1, 1] = some [0, 0, 2, 2, 2, 1, 1] :=
  specInv_white_7 [0, 1, 1, 0, 0, 1, 1] [2, 1, 2, 0, 0, 2, 0] [2, 2, 1, 1, 1, 0, 2] [0, 0, 2, 2, 2, 1, 1] demoR1_0110011 demoR2_0110011 demoC_0110011 demoM_0110011

theorem demoR1_1110011 : invRung 7 5 20 [1, 1, 1, 0, 0, 1, 1] [1, 1, 1, 0, 0, 1, 1] 1 2 false = ([0, 0, 1, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_1110011 : invRung 7 5 20 [1, 1, 1, 0, 0, 1, 1] [0, 0, 1, 2, 2, 1, 1] 3 1 true = ([1, 0, 2, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_1110011 : fieldCube 7 5 20 [1, 0, 2, 1, 1, 1, 1] = [0, 0, 1, 2, 2, 1, 0] := by
  decide

theorem demoM_1110011 : fieldMul 7 5 20 [0, 0, 1, 2, 2, 1, 0] [1, 1, 1, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1110011 : specInv 7 5 20 [1, 1, 1, 0, 0, 1, 1] = some [0, 0, 1, 2, 2, 1, 0] :=
  specInv_white_7 [1, 1, 1, 0, 0, 1, 1] [0, 0, 1, 2, 2, 1, 1] [1, 0, 2, 1, 1, 1, 1] [0, 0, 1, 2, 2, 1, 0] demoR1_1110011 demoR2_1110011 demoC_1110011 demoM_1110011

theorem demoR1_2110011 : invRung 7 5 20 [2, 1, 1, 0, 0, 1, 1] [2, 1, 1, 0, 0, 1, 1] 1 2 false = ([1, 0, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoR2_2110011 : invRung 7 5 20 [2, 1, 1, 0, 0, 1, 1] [1, 0, 2, 0, 2, 2, 2] 3 1 true = ([0, 1, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_2110011 : fieldCube 7 5 20 [0, 1, 1, 1, 0, 0, 2] = [1, 2, 2, 0, 2, 0, 0] := by
  decide

theorem demoM_2110011 : fieldMul 7 5 20 [1, 2, 2, 0, 2, 0, 0] [2, 1, 1, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2110011 : mirrorTrits [1, 2, 2, 0, 2, 0, 0] = [2, 1, 1, 0, 1, 0, 0] := by
  decide

theorem demoInv_2110011 : specInv 7 5 20 [2, 1, 1, 0, 0, 1, 1] = some [2, 1, 1, 0, 1, 0, 0] :=
  specInv_mirror_7 [2, 1, 1, 0, 0, 1, 1] [1, 0, 2, 0, 2, 2, 2] [0, 1, 1, 1, 0, 0, 2] [1, 2, 2, 0, 2, 0, 0] [2, 1, 1, 0, 1, 0, 0] demoR1_2110011 demoR2_2110011 demoC_2110011 demoM_2110011 demoMir_2110011

theorem demoR1_0210011 : invRung 7 5 20 [0, 2, 1, 0, 0, 1, 1] [0, 2, 1, 0, 0, 1, 1] 1 2 false = ([0, 0, 0, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_0210011 : invRung 7 5 20 [0, 2, 1, 0, 0, 1, 1] [0, 0, 0, 0, 0, 1, 2] 3 1 true = ([1, 1, 1, 0, 0, 0, 1], 3) := by
  decide

theorem demoC_0210011 : fieldCube 7 5 20 [1, 1, 1, 0, 0, 0, 1] = [1, 1, 2, 2, 1, 1, 2] := by
  decide

theorem demoM_0210011 : fieldMul 7 5 20 [1, 1, 2, 2, 1, 1, 2] [0, 2, 1, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210011 : mirrorTrits [1, 1, 2, 2, 1, 1, 2] = [2, 2, 1, 1, 2, 2, 1] := by
  decide

theorem demoInv_0210011 : specInv 7 5 20 [0, 2, 1, 0, 0, 1, 1] = some [2, 2, 1, 1, 2, 2, 1] :=
  specInv_mirror_7 [0, 2, 1, 0, 0, 1, 1] [0, 0, 0, 0, 0, 1, 2] [1, 1, 1, 0, 0, 0, 1] [1, 1, 2, 2, 1, 1, 2] [2, 2, 1, 1, 2, 2, 1] demoR1_0210011 demoR2_0210011 demoC_0210011 demoM_0210011 demoMir_0210011

theorem demoR1_1210011 : invRung 7 5 20 [1, 2, 1, 0, 0, 1, 1] [1, 2, 1, 0, 0, 1, 1] 1 2 false = ([0, 2, 0, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_1210011 : invRung 7 5 20 [1, 2, 1, 0, 0, 1, 1] [0, 2, 0, 0, 0, 2, 2] 3 1 true = ([0, 1, 2, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_1210011 : fieldCube 7 5 20 [0, 1, 2, 1, 0, 0, 0] = [1, 0, 1, 1, 0, 1, 2] := by
  decide

theorem demoM_1210011 : fieldMul 7 5 20 [1, 0, 1, 1, 0, 1, 2] [1, 2, 1, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1210011 : mirrorTrits [1, 0, 1, 1, 0, 1, 2] = [2, 0, 2, 2, 0, 2, 1] := by
  decide

theorem demoInv_1210011 : specInv 7 5 20 [1, 2, 1, 0, 0, 1, 1] = some [2, 0, 2, 2, 0, 2, 1] :=
  specInv_mirror_7 [1, 2, 1, 0, 0, 1, 1] [0, 2, 0, 0, 0, 2, 2] [0, 1, 2, 1, 0, 0, 0] [1, 0, 1, 1, 0, 1, 2] [2, 0, 2, 2, 0, 2, 1] demoR1_1210011 demoR2_1210011 demoC_1210011 demoM_1210011 demoMir_1210011

theorem demoR1_2210011 : invRung 7 5 20 [2, 2, 1, 0, 0, 1, 1] [2, 2, 1, 0, 0, 1, 1] 1 2 false = ([2, 1, 1, 1, 1, 1, 2], 3) := by
  decide

theorem demoR2_2210011 : invRung 7 5 20 [2, 2, 1, 0, 0, 1, 1] [2, 1, 1, 1, 1, 1, 2] 3 1 true = ([1, 0, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_2210011 : fieldCube 7 5 20 [1, 0, 1, 0, 2, 1, 0] = [2, 0, 1, 2, 1, 0, 2] := by
  decide

theorem demoM_2210011 : fieldMul 7 5 20 [2, 0, 1, 2, 1, 0, 2] [2, 2, 1, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2210011 : mirrorTrits [2, 0, 1, 2, 1, 0, 2] = [1, 0, 2, 1, 2, 0, 1] := by
  decide

theorem demoInv_2210011 : specInv 7 5 20 [2, 2, 1, 0, 0, 1, 1] = some [1, 0, 2, 1, 2, 0, 1] :=
  specInv_mirror_7 [2, 2, 1, 0, 0, 1, 1] [2, 1, 1, 1, 1, 1, 2] [1, 0, 1, 0, 2, 1, 0] [2, 0, 1, 2, 1, 0, 2] [1, 0, 2, 1, 2, 0, 1] demoR1_2210011 demoR2_2210011 demoC_2210011 demoM_2210011 demoMir_2210011

theorem demoR1_0020011 : invRung 7 5 20 [0, 0, 2, 0, 0, 1, 1] [0, 0, 2, 0, 0, 1, 1] 1 2 false = ([0, 0, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_0020011 : invRung 7 5 20 [0, 0, 2, 0, 0, 1, 1] [0, 0, 1, 2, 2, 0, 0] 3 1 true = ([0, 1, 1, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_0020011 : fieldCube 7 5 20 [0, 1, 1, 2, 1, 0, 1] = [2, 2, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_0020011 : fieldMul 7 5 20 [2, 2, 1, 0, 1, 1, 0] [0, 0, 2, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0020011 : specInv 7 5 20 [0, 0, 2, 0, 0, 1, 1] = some [2, 2, 1, 0, 1, 1, 0] :=
  specInv_white_7 [0, 0, 2, 0, 0, 1, 1] [0, 0, 1, 2, 2, 0, 0] [0, 1, 1, 2, 1, 0, 1] [2, 2, 1, 0, 1, 1, 0] demoR1_0020011 demoR2_0020011 demoC_0020011 demoM_0020011

theorem demoR1_1020011 : invRung 7 5 20 [1, 0, 2, 0, 0, 1, 1] [1, 0, 2, 0, 0, 1, 1] 1 2 false = ([1, 2, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1020011 : invRung 7 5 20 [1, 0, 2, 0, 0, 1, 1] [1, 2, 2, 2, 2, 1, 0] 3 1 true = ([2, 0, 1, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_1020011 : fieldCube 7 5 20 [2, 0, 1, 2, 0, 2, 2] = [0, 1, 2, 2, 1, 0, 1] := by
  decide

theorem demoM_1020011 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 0, 1] [1, 0, 2, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1020011 : specInv 7 5 20 [1, 0, 2, 0, 0, 1, 1] = some [0, 1, 2, 2, 1, 0, 1] :=
  specInv_white_7 [1, 0, 2, 0, 0, 1, 1] [1, 2, 2, 2, 2, 1, 0] [2, 0, 1, 2, 0, 2, 2] [0, 1, 2, 2, 1, 0, 1] demoR1_1020011 demoR2_1020011 demoC_1020011 demoM_1020011

theorem demoR1_2020011 : invRung 7 5 20 [2, 0, 2, 0, 0, 1, 1] [2, 0, 2, 0, 0, 1, 1] 1 2 false = ([0, 2, 0, 1, 2, 1, 1], 3) := by
  decide

theorem demoR2_2020011 : invRung 7 5 20 [2, 0, 2, 0, 0, 1, 1] [0, 2, 0, 1, 2, 1, 1] 3 1 true = ([0, 2, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_2020011 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 1, 2] = [2, 1, 0, 2, 0, 2, 1] := by
  decide

theorem demoM_2020011 : fieldMul 7 5 20 [2, 1, 0, 2, 0, 2, 1] [2, 0, 2, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020011 : mirrorTrits [2, 1, 0, 2, 0, 2, 1] = [1, 2, 0, 1, 0, 1, 2] := by
  decide

theorem demoInv_2020011 : specInv 7 5 20 [2, 0, 2, 0, 0, 1, 1] = some [1, 2, 0, 1, 0, 1, 2] :=
  specInv_mirror_7 [2, 0, 2, 0, 0, 1, 1] [0, 2, 0, 1, 2, 1, 1] [0, 2, 2, 1, 1, 1, 2] [2, 1, 0, 2, 0, 2, 1] [1, 2, 0, 1, 0, 1, 2] demoR1_2020011 demoR2_2020011 demoC_2020011 demoM_2020011 demoMir_2020011

theorem demoR1_0120011 : invRung 7 5 20 [0, 1, 2, 0, 0, 1, 1] [0, 1, 2, 0, 0, 1, 1] 1 2 false = ([0, 0, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoR2_0120011 : invRung 7 5 20 [0, 1, 2, 0, 0, 1, 1] [0, 0, 1, 0, 0, 2, 2] 3 1 true = ([0, 0, 2, 0, 2, 2, 0], 3) := by
  decide

theorem demoC_0120011 : fieldCube 7 5 20 [0, 0, 2, 0, 2, 2, 0] = [2, 1, 2, 2, 2, 1, 2] := by
  decide

theorem demoM_0120011 : fieldMul 7 5 20 [2, 1, 2, 2, 2, 1, 2] [0, 1, 2, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0120011 : mirrorTrits [2, 1, 2, 2, 2, 1, 2] = [1, 2, 1, 1, 1, 2, 1] := by
  decide

theorem demoInv_0120011 : specInv 7 5 20 [0, 1, 2, 0, 0, 1, 1] = some [1, 2, 1, 1, 1, 2, 1] :=
  specInv_mirror_7 [0, 1, 2, 0, 0, 1, 1] [0, 0, 1, 0, 0, 2, 2] [0, 0, 2, 0, 2, 2, 0] [2, 1, 2, 2, 2, 1, 2] [1, 2, 1, 1, 1, 2, 1] demoR1_0120011 demoR2_0120011 demoC_0120011 demoM_0120011 demoMir_0120011

theorem demoR1_1120011 : invRung 7 5 20 [1, 1, 2, 0, 0, 1, 1] [1, 1, 2, 0, 0, 1, 1] 1 2 false = ([0, 0, 1, 2, 0, 1, 2], 3) := by
  decide

theorem demoR2_1120011 : invRung 7 5 20 [1, 1, 2, 0, 0, 1, 1] [0, 0, 1, 2, 0, 1, 2] 3 1 true = ([2, 1, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_1120011 : fieldCube 7 5 20 [2, 1, 0, 1, 2, 0, 1] = [0, 0, 0, 1, 1, 1, 0] := by
  decide

theorem demoM_1120011 : fieldMul 7 5 20 [0, 0, 0, 1, 1, 1, 0] [1, 1, 2, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120011 : mirrorTrits [0, 0, 0, 1, 1, 1, 0] = [0, 0, 0, 2, 2, 2, 0] := by
  decide

theorem demoInv_1120011 : specInv 7 5 20 [1, 1, 2, 0, 0, 1, 1] = some [0, 0, 0, 2, 2, 2, 0] :=
  specInv_mirror_7 [1, 1, 2, 0, 0, 1, 1] [0, 0, 1, 2, 0, 1, 2] [2, 1, 0, 1, 2, 0, 1] [0, 0, 0, 1, 1, 1, 0] [0, 0, 0, 2, 2, 2, 0] demoR1_1120011 demoR2_1120011 demoC_1120011 demoM_1120011 demoMir_1120011

theorem demoR1_2120011 : invRung 7 5 20 [2, 1, 2, 0, 0, 1, 1] [2, 1, 2, 0, 0, 1, 1] 1 2 false = ([0, 0, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_2120011 : invRung 7 5 20 [2, 1, 2, 0, 0, 1, 1] [0, 0, 0, 2, 0, 1, 0] 3 1 true = ([1, 2, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_2120011 : fieldCube 7 5 20 [1, 2, 0, 2, 1, 1, 2] = [1, 1, 1, 2, 0, 0, 2] := by
  decide

theorem demoM_2120011 : fieldMul 7 5 20 [1, 1, 1, 2, 0, 0, 2] [2, 1, 2, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2120011 : specInv 7 5 20 [2, 1, 2, 0, 0, 1, 1] = some [1, 1, 1, 2, 0, 0, 2] :=
  specInv_white_7 [2, 1, 2, 0, 0, 1, 1] [0, 0, 0, 2, 0, 1, 0] [1, 2, 0, 2, 1, 1, 2] [1, 1, 1, 2, 0, 0, 2] demoR1_2120011 demoR2_2120011 demoC_2120011 demoM_2120011

theorem demoR1_0220011 : invRung 7 5 20 [0, 2, 2, 0, 0, 1, 1] [0, 2, 2, 0, 0, 1, 1] 1 2 false = ([0, 0, 2, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_0220011 : invRung 7 5 20 [0, 2, 2, 0, 0, 1, 1] [0, 0, 2, 2, 2, 0, 2] 3 1 true = ([0, 2, 1, 2, 1, 2, 1], 3) := by
  decide

theorem demoC_0220011 : fieldCube 7 5 20 [0, 2, 1, 2, 1, 2, 1] = [1, 1, 0, 1, 0, 0, 1] := by
  decide

theorem demoM_0220011 : fieldMul 7 5 20 [1, 1, 0, 1, 0, 0, 1] [0, 2, 2, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0220011 : mirrorTrits [1, 1, 0, 1, 0, 0, 1] = [2, 2, 0, 2, 0, 0, 2] := by
  decide

theorem demoInv_0220011 : specInv 7 5 20 [0, 2, 2, 0, 0, 1, 1] = some [2, 2, 0, 2, 0, 0, 2] :=
  specInv_mirror_7 [0, 2, 2, 0, 0, 1, 1] [0, 0, 2, 2, 2, 0, 2] [0, 2, 1, 2, 1, 2, 1] [1, 1, 0, 1, 0, 0, 1] [2, 2, 0, 2, 0, 0, 2] demoR1_0220011 demoR2_0220011 demoC_0220011 demoM_0220011 demoMir_0220011

theorem demoR1_1220011 : invRung 7 5 20 [1, 2, 2, 0, 0, 1, 1] [1, 2, 2, 0, 0, 1, 1] 1 2 false = ([2, 2, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoR2_1220011 : invRung 7 5 20 [1, 2, 2, 0, 0, 1, 1] [2, 2, 1, 1, 1, 2, 0] 3 1 true = ([1, 1, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_1220011 : fieldCube 7 5 20 [1, 1, 2, 0, 2, 1, 0] = [2, 0, 1, 0, 1, 0, 0] := by
  decide

theorem demoM_1220011 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 0, 0] [1, 2, 2, 0, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1220011 : specInv 7 5 20 [1, 2, 2, 0, 0, 1, 1] = some [2, 0, 1, 0, 1, 0, 0] :=
  specInv_white_7 [1, 2, 2, 0, 0, 1, 1] [2, 2, 1, 1, 1, 2, 0] [1, 1, 2, 0, 2, 1, 0] [2, 0, 1, 0, 1, 0, 0] demoR1_1220011 demoR2_1220011 demoC_1220011 demoM_1220011

theorem demoR1_2220011 : invRung 7 5 20 [2, 2, 2, 0, 0, 1, 1] [2, 2, 2, 0, 0, 1, 1] 1 2 false = ([0, 0, 1, 0, 0, 1, 2], 3) := by
  decide

theorem demoR2_2220011 : invRung 7 5 20 [2, 2, 2, 0, 0, 1, 1] [0, 0, 1, 0, 0, 1, 2] 3 1 true = ([0, 1, 2, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_2220011 : fieldCube 7 5 20 [0, 1, 2, 0, 1, 0, 1] = [0, 2, 2, 0, 1, 2, 1] := by
  decide

theorem demoM_2220011 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 2, 1] [2, 2, 2, 0, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220011 : mirrorTrits [0, 2, 2, 0, 1, 2, 1] = [0, 1, 1, 0, 2, 1, 2] := by
  decide

theorem demoInv_2220011 : specInv 7 5 20 [2, 2, 2, 0, 0, 1, 1] = some [0, 1, 1, 0, 2, 1, 2] :=
  specInv_mirror_7 [2, 2, 2, 0, 0, 1, 1] [0, 0, 1, 0, 0, 1, 2] [0, 1, 2, 0, 1, 0, 1] [0, 2, 2, 0, 1, 2, 1] [0, 1, 1, 0, 2, 1, 2] demoR1_2220011 demoR2_2220011 demoC_2220011 demoM_2220011 demoMir_2220011

theorem demoR1_0001011 : invRung 7 5 20 [0, 0, 0, 1, 0, 1, 1] [0, 0, 0, 1, 0, 1, 1] 1 2 false = ([1, 0, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0001011 : invRung 7 5 20 [0, 0, 0, 1, 0, 1, 1] [1, 0, 1, 0, 0, 0, 0] 3 1 true = ([1, 0, 1, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_0001011 : fieldCube 7 5 20 [1, 0, 1, 0, 0, 2, 2] = [0, 1, 0, 2, 1, 1, 1] := by
  decide

theorem demoM_0001011 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 1, 1] [0, 0, 0, 1, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001011 : mirrorTrits [0, 1, 0, 2, 1, 1, 1] = [0, 2, 0, 1, 2, 2, 2] := by
  decide

theorem demoInv_0001011 : specInv 7 5 20 [0, 0, 0, 1, 0, 1, 1] = some [0, 2, 0, 1, 2, 2, 2] :=
  specInv_mirror_7 [0, 0, 0, 1, 0, 1, 1] [1, 0, 1, 0, 0, 0, 0] [1, 0, 1, 0, 0, 2, 2] [0, 1, 0, 2, 1, 1, 1] [0, 2, 0, 1, 2, 2, 2] demoR1_0001011 demoR2_0001011 demoC_0001011 demoM_0001011 demoMir_0001011

theorem demoR1_1001011 : invRung 7 5 20 [1, 0, 0, 1, 0, 1, 1] [1, 0, 0, 1, 0, 1, 1] 1 2 false = ([0, 2, 1, 1, 2, 1, 0], 3) := by
  decide

theorem demoR2_1001011 : invRung 7 5 20 [1, 0, 0, 1, 0, 1, 1] [0, 2, 1, 1, 2, 1, 0] 3 1 true = ([1, 2, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1001011 : fieldCube 7 5 20 [1, 2, 1, 0, 1, 1, 0] = [2, 2, 1, 0, 1, 2, 1] := by
  decide

theorem demoM_1001011 : fieldMul 7 5 20 [2, 2, 1, 0, 1, 2, 1] [1, 0, 0, 1, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1001011 : mirrorTrits [2, 2, 1, 0, 1, 2, 1] = [1, 1, 2, 0, 2, 1, 2] := by
  decide

theorem demoInv_1001011 : specInv 7 5 20 [1, 0, 0, 1, 0, 1, 1] = some [1, 1, 2, 0, 2, 1, 2] :=
  specInv_mirror_7 [1, 0, 0, 1, 0, 1, 1] [0, 2, 1, 1, 2, 1, 0] [1, 2, 1, 0, 1, 1, 0] [2, 2, 1, 0, 1, 2, 1] [1, 1, 2, 0, 2, 1, 2] demoR1_1001011 demoR2_1001011 demoC_1001011 demoM_1001011 demoMir_1001011

theorem demoR1_2001011 : invRung 7 5 20 [2, 0, 0, 1, 0, 1, 1] [2, 0, 0, 1, 0, 1, 1] 1 2 false = ([0, 0, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_2001011 : invRung 7 5 20 [2, 0, 0, 1, 0, 1, 1] [0, 0, 2, 2, 2, 1, 2] 3 1 true = ([2, 2, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_2001011 : fieldCube 7 5 20 [2, 2, 1, 1, 2, 0, 2] = [0, 1, 2, 0, 2, 2, 2] := by
  decide

theorem demoM_2001011 : fieldMul 7 5 20 [0, 1, 2, 0, 2, 2, 2] [2, 0, 0, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2001011 : specInv 7 5 20 [2, 0, 0, 1, 0, 1, 1] = some [0, 1, 2, 0, 2, 2, 2] :=
  specInv_white_7 [2, 0, 0, 1, 0, 1, 1] [0, 0, 2, 2, 2, 1, 2] [2, 2, 1, 1, 2, 0, 2] [0, 1, 2, 0, 2, 2, 2] demoR1_2001011 demoR2_2001011 demoC_2001011 demoM_2001011

theorem demoR1_0101011 : invRung 7 5 20 [0, 1, 0, 1, 0, 1, 1] [0, 1, 0, 1, 0, 1, 1] 1 2 false = ([2, 2, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_0101011 : invRung 7 5 20 [0, 1, 0, 1, 0, 1, 1] [2, 2, 1, 0, 2, 1, 0] 3 1 true = ([0, 2, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0101011 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 0, 0] = [1, 0, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_0101011 : fieldMul 7 5 20 [1, 0, 1, 2, 0, 1, 0] [0, 1, 0, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0101011 : specInv 7 5 20 [0, 1, 0, 1, 0, 1, 1] = some [1, 0, 1, 2, 0, 1, 0] :=
  specInv_white_7 [0, 1, 0, 1, 0, 1, 1] [2, 2, 1, 0, 2, 1, 0] [0, 2, 0, 1, 0, 0, 0] [1, 0, 1, 2, 0, 1, 0] demoR1_0101011 demoR2_0101011 demoC_0101011 demoM_0101011

theorem demoR1_1101011 : invRung 7 5 20 [1, 1, 0, 1, 0, 1, 1] [1, 1, 0, 1, 0, 1, 1] 1 2 false = ([1, 1, 1, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1101011 : invRung 7 5 20 [1, 1, 0, 1, 0, 1, 1] [1, 1, 1, 2, 1, 0, 2] 3 1 true = ([2, 1, 0, 2, 1, 0, 1], 3) := by
  decide

theorem demoC_1101011 : fieldCube 7 5 20 [2, 1, 0, 2, 1, 0, 1] = [1, 2, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_1101011 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 1, 2] [1, 1, 0, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1101011 : specInv 7 5 20 [1, 1, 0, 1, 0, 1, 1] = some [1, 2, 1, 0, 1, 1, 2] :=
  specInv_white_7 [1, 1, 0, 1, 0, 1, 1] [1, 1, 1, 2, 1, 0, 2] [2, 1, 0, 2, 1, 0, 1] [1, 2, 1, 0, 1, 1, 2] demoR1_1101011 demoR2_1101011 demoC_1101011 demoM_1101011

theorem demoR1_2101011 : invRung 7 5 20 [2, 1, 0, 1, 0, 1, 1] [2, 1, 0, 1, 0, 1, 1] 1 2 false = ([0, 1, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_2101011 : invRung 7 5 20 [2, 1, 0, 1, 0, 1, 1] [0, 1, 1, 0, 1, 0, 0] 3 1 true = ([1, 2, 2, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_2101011 : fieldCube 7 5 20 [1, 2, 2, 1, 1, 2, 1] = [1, 1, 2, 1, 0, 2, 2] := by
  decide

theorem demoM_2101011 : fieldMul 7 5 20 [1, 1, 2, 1, 0, 2, 2] [2, 1, 0, 1, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2101011 : mirrorTrits [1, 1, 2, 1, 0, 2, 2] = [2, 2, 1, 2, 0, 1, 1] := by
  decide

theorem demoInv_2101011 : specInv 7 5 20 [2, 1, 0, 1, 0, 1, 1] = some [2, 2, 1, 2, 0, 1, 1] :=
  specInv_mirror_7 [2, 1, 0, 1, 0, 1, 1] [0, 1, 1, 0, 1, 0, 0] [1, 2, 2, 1, 1, 2, 1] [1, 1, 2, 1, 0, 2, 2] [2, 2, 1, 2, 0, 1, 1] demoR1_2101011 demoR2_2101011 demoC_2101011 demoM_2101011 demoMir_2101011

theorem demoR1_0201011 : invRung 7 5 20 [0, 2, 0, 1, 0, 1, 1] [0, 2, 0, 1, 0, 1, 1] 1 2 false = ([1, 1, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_0201011 : invRung 7 5 20 [0, 2, 0, 1, 0, 1, 1] [1, 1, 0, 2, 1, 0, 2] 3 1 true = ([1, 1, 2, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_0201011 : fieldCube 7 5 20 [1, 1, 2, 1, 2, 2, 2] = [1, 0, 1, 2, 1, 1, 1] := by
  decide

theorem demoM_0201011 : fieldMul 7 5 20 [1, 0, 1, 2, 1, 1, 1] [0, 2, 0, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0201011 : specInv 7 5 20 [0, 2, 0, 1, 0, 1, 1] = some [1, 0, 1, 2, 1, 1, 1] :=
  specInv_white_7 [0, 2, 0, 1, 0, 1, 1] [1, 1, 0, 2, 1, 0, 2] [1, 1, 2, 1, 2, 2, 2] [1, 0, 1, 2, 1, 1, 1] demoR1_0201011 demoR2_0201011 demoC_0201011 demoM_0201011

theorem demoR1_1201011 : invRung 7 5 20 [1, 2, 0, 1, 0, 1, 1] [1, 2, 0, 1, 0, 1, 1] 1 2 false = ([0, 1, 0, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_1201011 : invRung 7 5 20 [1, 2, 0, 1, 0, 1, 1] [0, 1, 0, 0, 2, 2, 1] 3 1 true = ([2, 0, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_1201011 : fieldCube 7 5 20 [2, 0, 2, 1, 0, 0, 2] = [0, 2, 2, 2, 2, 0, 1] := by
  decide

theorem demoM_1201011 : fieldMul 7 5 20 [0, 2, 2, 2, 2, 0, 1] [1, 2, 0, 1, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201011 : mirrorTrits [0, 2, 2, 2, 2, 0, 1] = [0, 1, 1, 1, 1, 0, 2] := by
  decide

theorem demoInv_1201011 : specInv 7 5 20 [1, 2, 0, 1, 0, 1, 1] = some [0, 1, 1, 1, 1, 0, 2] :=
  specInv_mirror_7 [1, 2, 0, 1, 0, 1, 1] [0, 1, 0, 0, 2, 2, 1] [2, 0, 2, 1, 0, 0, 2] [0, 2, 2, 2, 2, 0, 1] [0, 1, 1, 1, 1, 0, 2] demoR1_1201011 demoR2_1201011 demoC_1201011 demoM_1201011 demoMir_1201011

theorem demoR1_2201011 : invRung 7 5 20 [2, 2, 0, 1, 0, 1, 1] [2, 2, 0, 1, 0, 1, 1] 1 2 false = ([1, 1, 2, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_2201011 : invRung 7 5 20 [2, 2, 0, 1, 0, 1, 1] [1, 1, 2, 2, 1, 1, 2] 3 1 true = ([0, 0, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_2201011 : fieldCube 7 5 20 [0, 0, 1, 1, 1, 0, 2] = [1, 0, 2, 0, 2, 1, 1] := by
  decide

theorem demoM_2201011 : fieldMul 7 5 20 [1, 0, 2, 0, 2, 1, 1] [2, 2, 0, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2201011 : specInv 7 5 20 [2, 2, 0, 1, 0, 1, 1] = some [1, 0, 2, 0, 2, 1, 1] :=
  specInv_white_7 [2, 2, 0, 1, 0, 1, 1] [1, 1, 2, 2, 1, 1, 2] [0, 0, 1, 1, 1, 0, 2] [1, 0, 2, 0, 2, 1, 1] demoR1_2201011 demoR2_2201011 demoC_2201011 demoM_2201011

theorem demoR1_0011011 : invRung 7 5 20 [0, 0, 1, 1, 0, 1, 1] [0, 0, 1, 1, 0, 1, 1] 1 2 false = ([0, 0, 2, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_0011011 : invRung 7 5 20 [0, 0, 1, 1, 0, 1, 1] [0, 0, 2, 2, 2, 1, 1] 3 1 true = ([1, 0, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoC_0011011 : fieldCube 7 5 20 [1, 0, 1, 2, 0, 2, 0] = [2, 2, 1, 0, 2, 1, 2] := by
  decide

theorem demoM_0011011 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 1, 2] [0, 0, 1, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0011011 : specInv 7 5 20 [0, 0, 1, 1, 0, 1, 1] = some [2, 2, 1, 0, 2, 1, 2] :=
  specInv_white_7 [0, 0, 1, 1, 0, 1, 1] [0, 0, 2, 2, 2, 1, 1] [1, 0, 1, 2, 0, 2, 0] [2, 2, 1, 0, 2, 1, 2] demoR1_0011011 demoR2_0011011 demoC_0011011 demoM_0011011

theorem demoR1_1011011 : invRung 7 5 20 [1, 0, 1, 1, 0, 1, 1] [1, 0, 1, 1, 0, 1, 1] 1 2 false = ([2, 2, 2, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_1011011 : invRung 7 5 20 [1, 0, 1, 1, 0, 1, 1] [2, 2, 2, 0, 0, 2, 0] 3 1 true = ([2, 2, 2, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_1011011 : fieldCube 7 5 20 [2, 2, 2, 2, 1, 2, 2] = [0, 2, 2, 2, 1, 1, 0] := by
  decide

theorem demoM_1011011 : fieldMul 7 5 20 [0, 2, 2, 2, 1, 1, 0] [1, 0, 1, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1011011 : specInv 7 5 20 [1, 0, 1, 1, 0, 1, 1] = some [0, 2, 2, 2, 1, 1, 0] :=
  specInv_white_7 [1, 0, 1, 1, 0, 1, 1] [2, 2, 2, 0, 0, 2, 0] [2, 2, 2, 2, 1, 2, 2] [0, 2, 2, 2, 1, 1, 0] demoR1_1011011 demoR2_1011011 demoC_1011011 demoM_1011011

theorem demoR1_2011011 : invRung 7 5 20 [2, 0, 1, 1, 0, 1, 1] [2, 0, 1, 1, 0, 1, 1] 1 2 false = ([2, 2, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2011011 : invRung 7 5 20 [2, 0, 1, 1, 0, 1, 1] [2, 2, 0, 0, 1, 1, 2] 3 1 true = ([0, 2, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_2011011 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 0, 1] = [1, 1, 0, 0, 1, 2, 1] := by
  decide

theorem demoM_2011011 : fieldMul 7 5 20 [1, 1, 0, 0, 1, 2, 1] [2, 0, 1, 1, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011011 : mirrorTrits [1, 1, 0, 0, 1, 2, 1] = [2, 2, 0, 0, 2, 1, 2] := by
  decide

theorem demoInv_2011011 : specInv 7 5 20 [2, 0, 1, 1, 0, 1, 1] = some [2, 2, 0, 0, 2, 1, 2] :=
  specInv_mirror_7 [2, 0, 1, 1, 0, 1, 1] [2, 2, 0, 0, 1, 1, 2] [0, 2, 0, 1, 0, 0, 1] [1, 1, 0, 0, 1, 2, 1] [2, 2, 0, 0, 2, 1, 2] demoR1_2011011 demoR2_2011011 demoC_2011011 demoM_2011011 demoMir_2011011

theorem demoR1_0111011 : invRung 7 5 20 [0, 1, 1, 1, 0, 1, 1] [0, 1, 1, 1, 0, 1, 1] 1 2 false = ([0, 1, 1, 0, 0, 0, 0], 3) := by
  decide

theorem demoR2_0111011 : invRung 7 5 20 [0, 1, 1, 1, 0, 1, 1] [0, 1, 1, 0, 0, 0, 0] 3 1 true = ([2, 1, 2, 0, 2, 2, 2], 3) := by
  decide

theorem demoC_0111011 : fieldCube 7 5 20 [2, 1, 2, 0, 2, 2, 2] = [1, 0, 0, 2, 1, 0, 1] := by
  decide

theorem demoM_0111011 : fieldMul 7 5 20 [1, 0, 0, 2, 1, 0, 1] [0, 1, 1, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0111011 : specInv 7 5 20 [0, 1, 1, 1, 0, 1, 1] = some [1, 0, 0, 2, 1, 0, 1] :=
  specInv_white_7 [0, 1, 1, 1, 0, 1, 1] [0, 1, 1, 0, 0, 0, 0] [2, 1, 2, 0, 2, 2, 2] [1, 0, 0, 2, 1, 0, 1] demoR1_0111011 demoR2_0111011 demoC_0111011 demoM_0111011

theorem demoR1_1111011 : invRung 7 5 20 [1, 1, 1, 1, 0, 1, 1] [1, 1, 1, 1, 0, 1, 1] 1 2 false = ([2, 2, 2, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_1111011 : invRung 7 5 20 [1, 1, 1, 1, 0, 1, 1] [2, 2, 2, 1, 2, 0, 0] 3 1 true = ([2, 0, 0, 2, 0, 2, 2], 3) := by
  decide

theorem demoC_1111011 : fieldCube 7 5 20 [2, 0, 0, 2, 0, 2, 2] = [0, 1, 2, 2, 1, 0, 0] := by
  decide

theorem demoM_1111011 : fieldMul 7 5 20 [0, 1, 2, 2, 1, 0, 0] [1, 1, 1, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1111011 : specInv 7 5 20 [1, 1, 1, 1, 0, 1, 1] = some [0, 1, 2, 2, 1, 0, 0] :=
  specInv_white_7 [1, 1, 1, 1, 0, 1, 1] [2, 2, 2, 1, 2, 0, 0] [2, 0, 0, 2, 0, 2, 2] [0, 1, 2, 2, 1, 0, 0] demoR1_1111011 demoR2_1111011 demoC_1111011 demoM_1111011

theorem demoR1_2111011 : invRung 7 5 20 [2, 1, 1, 1, 0, 1, 1] [2, 1, 1, 1, 0, 1, 1] 1 2 false = ([1, 0, 0, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_2111011 : invRung 7 5 20 [2, 1, 1, 1, 0, 1, 1] [1, 0, 0, 0, 1, 0, 0] 3 1 true = ([1, 2, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoC_2111011 : fieldCube 7 5 20 [1, 2, 0, 1, 2, 2, 2] = [1, 0, 1, 0, 1, 1, 2] := by
  decide

theorem demoM_2111011 : fieldMul 7 5 20 [1, 0, 1, 0, 1, 1, 2] [2, 1, 1, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2111011 : specInv 7 5 20 [2, 1, 1, 1, 0, 1, 1] = some [1, 0, 1, 0, 1, 1, 2] :=
  specInv_white_7 [2, 1, 1, 1, 0, 1, 1] [1, 0, 0, 0, 1, 0, 0] [1, 2, 0, 1, 2, 2, 2] [1, 0, 1, 0, 1, 1, 2] demoR1_2111011 demoR2_2111011 demoC_2111011 demoM_2111011

theorem demoR1_0211011 : invRung 7 5 20 [0, 2, 1, 1, 0, 1, 1] [0, 2, 1, 1, 0, 1, 1] 1 2 false = ([2, 1, 0, 0, 1, 1, 1], 3) := by
  decide

theorem demoR2_0211011 : invRung 7 5 20 [0, 2, 1, 1, 0, 1, 1] [2, 1, 0, 0, 1, 1, 1] 3 1 true = ([2, 1, 1, 0, 2, 2, 1], 3) := by
  decide

theorem demoC_0211011 : fieldCube 7 5 20 [2, 1, 1, 0, 2, 2, 1] = [1, 2, 1, 1, 0, 2, 2] := by
  decide

theorem demoM_0211011 : fieldMul 7 5 20 [1, 2, 1, 1, 0, 2, 2] [0, 2, 1, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0211011 : specInv 7 5 20 [0, 2, 1, 1, 0, 1, 1] = some [1, 2, 1, 1, 0, 2, 2] :=
  specInv_white_7 [0, 2, 1, 1, 0, 1, 1] [2, 1, 0, 0, 1, 1, 1] [2, 1, 1, 0, 2, 2, 1] [1, 2, 1, 1, 0, 2, 2] demoR1_0211011 demoR2_0211011 demoC_0211011 demoM_0211011

theorem demoR1_1211011 : invRung 7 5 20 [1, 2, 1, 1, 0, 1, 1] [1, 2, 1, 1, 0, 1, 1] 1 2 false = ([1, 2, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_1211011 : invRung 7 5 20 [1, 2, 1, 1, 0, 1, 1] [1, 2, 2, 2, 0, 2, 0] 3 1 true = ([2, 2, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_1211011 : fieldCube 7 5 20 [2, 2, 0, 1, 0, 2, 0] = [2, 2, 0, 2, 2, 0, 1] := by
  decide

theorem demoM_1211011 : fieldMul 7 5 20 [2, 2, 0, 2, 2, 0, 1] [1, 2, 1, 1, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1211011 : mirrorTrits [2, 2, 0, 2, 2, 0, 1] = [1, 1, 0, 1, 1, 0, 2] := by
  decide

theorem demoInv_1211011 : specInv 7 5 20 [1, 2, 1, 1, 0, 1, 1] = some [1, 1, 0, 1, 1, 0, 2] :=
  specInv_mirror_7 [1, 2, 1, 1, 0, 1, 1] [1, 2, 2, 2, 0, 2, 0] [2, 2, 0, 1, 0, 2, 0] [2, 2, 0, 2, 2, 0, 1] [1, 1, 0, 1, 1, 0, 2] demoR1_1211011 demoR2_1211011 demoC_1211011 demoM_1211011 demoMir_1211011

theorem demoR1_2211011 : invRung 7 5 20 [2, 2, 1, 1, 0, 1, 1] [2, 2, 1, 1, 0, 1, 1] 1 2 false = ([2, 2, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_2211011 : invRung 7 5 20 [2, 2, 1, 1, 0, 1, 1] [2, 2, 0, 1, 2, 2, 2] 3 1 true = ([1, 1, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_2211011 : fieldCube 7 5 20 [1, 1, 0, 1, 2, 1, 2] = [0, 2, 0, 2, 0, 0, 0] := by
  decide

theorem demoM_2211011 : fieldMul 7 5 20 [0, 2, 0, 2, 0, 0, 0] [2, 2, 1, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2211011 : specInv 7 5 20 [2, 2, 1, 1, 0, 1, 1] = some [0, 2, 0, 2, 0, 0, 0] :=
  specInv_white_7 [2, 2, 1, 1, 0, 1, 1] [2, 2, 0, 1, 2, 2, 2] [1, 1, 0, 1, 2, 1, 2] [0, 2, 0, 2, 0, 0, 0] demoR1_2211011 demoR2_2211011 demoC_2211011 demoM_2211011

theorem demoR1_0021011 : invRung 7 5 20 [0, 0, 2, 1, 0, 1, 1] [0, 0, 2, 1, 0, 1, 1] 1 2 false = ([1, 2, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoR2_0021011 : invRung 7 5 20 [0, 0, 2, 1, 0, 1, 1] [1, 2, 0, 1, 0, 1, 0] 3 1 true = ([0, 2, 2, 1, 2, 1, 1], 3) := by
  decide

theorem demoC_0021011 : fieldCube 7 5 20 [0, 2, 2, 1, 2, 1, 1] = [2, 1, 1, 2, 2, 2, 1] := by
  decide

theorem demoM_0021011 : fieldMul 7 5 20 [2, 1, 1, 2, 2, 2, 1] [0, 0, 2, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0021011 : specInv 7 5 20 [0, 0, 2, 1, 0, 1, 1] = some [2, 1, 1, 2, 2, 2, 1] :=
  specInv_white_7 [0, 0, 2, 1, 0, 1, 1] [1, 2, 0, 1, 0, 1, 0] [0, 2, 2, 1, 2, 1, 1] [2, 1, 1, 2, 2, 2, 1] demoR1_0021011 demoR2_0021011 demoC_0021011 demoM_0021011

theorem demoR1_1021011 : invRung 7 5 20 [1, 0, 2, 1, 0, 1, 1] [1, 0, 2, 1, 0, 1, 1] 1 2 false = ([2, 1, 1, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_1021011 : invRung 7 5 20 [1, 0, 2, 1, 0, 1, 1] [2, 1, 1, 2, 0, 2, 0] 3 1 true = ([0, 0, 1, 0, 2, 1, 2], 3) := by
  decide

theorem demoC_1021011 : fieldCube 7 5 20 [0, 0, 1, 0, 2, 1, 2] = [1, 2, 2, 1, 0, 2, 1] := by
  decide

theorem demoM_1021011 : fieldMul 7 5 20 [1, 2, 2, 1, 0, 2, 1] [1, 0, 2, 1, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1021011 : mirrorTrits [1, 2, 2, 1, 0, 2, 1] = [2, 1, 1, 2, 0, 1, 2] := by
  decide

theorem demoInv_1021011 : specInv 7 5 20 [1, 0, 2, 1, 0, 1, 1] = some [2, 1, 1, 2, 0, 1, 2] :=
  specInv_mirror_7 [1, 0, 2, 1, 0, 1, 1] [2, 1, 1, 2, 0, 2, 0] [0, 0, 1, 0, 2, 1, 2] [1, 2, 2, 1, 0, 2, 1] [2, 1, 1, 2, 0, 1, 2] demoR1_1021011 demoR2_1021011 demoC_1021011 demoM_1021011 demoMir_1021011

theorem demoR1_2021011 : invRung 7 5 20 [2, 0, 2, 1, 0, 1, 1] [2, 0, 2, 1, 0, 1, 1] 1 2 false = ([1, 0, 0, 1, 2, 0, 1], 3) := by
  decide

theorem demoR2_2021011 : invRung 7 5 20 [2, 0, 2, 1, 0, 1, 1] [1, 0, 0, 1, 2, 0, 1] 3 1 true = ([2, 1, 0, 2, 0, 0, 1], 3) := by
  decide

theorem demoC_2021011 : fieldCube 7 5 20 [2, 1, 0, 2, 0, 0, 1] = [1, 1, 1, 2, 1, 0, 1] := by
  decide

theorem demoM_2021011 : fieldMul 7 5 20 [1, 1, 1, 2, 1, 0, 1] [2, 0, 2, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2021011 : specInv 7 5 20 [2, 0, 2, 1, 0, 1, 1] = some [1, 1, 1, 2, 1, 0, 1] :=
  specInv_white_7 [2, 0, 2, 1, 0, 1, 1] [1, 0, 0, 1, 2, 0, 1] [2, 1, 0, 2, 0, 0, 1] [1, 1, 1, 2, 1, 0, 1] demoR1_2021011 demoR2_2021011 demoC_2021011 demoM_2021011

theorem demoR1_0121011 : invRung 7 5 20 [0, 1, 2, 1, 0, 1, 1] [0, 1, 2, 1, 0, 1, 1] 1 2 false = ([0, 1, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoR2_0121011 : invRung 7 5 20 [0, 1, 2, 1, 0, 1, 1] [0, 1, 0, 2, 2, 0, 0] 3 1 true = ([2, 1, 0, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_0121011 : fieldCube 7 5 20 [2, 1, 0, 1, 2, 1, 0] = [1, 0, 2, 0, 1, 1, 1] := by
  decide

theorem demoM_0121011 : fieldMul 7 5 20 [1, 0, 2, 0, 1, 1, 1] [0, 1, 2, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0121011 : specInv 7 5 20 [0, 1, 2, 1, 0, 1, 1] = some [1, 0, 2, 0, 1, 1, 1] :=
  specInv_white_7 [0, 1, 2, 1, 0, 1, 1] [0, 1, 0, 2, 2, 0, 0] [2, 1, 0, 1, 2, 1, 0] [1, 0, 2, 0, 1, 1, 1] demoR1_0121011 demoR2_0121011 demoC_0121011 demoM_0121011

theorem demoR1_1121011 : invRung 7 5 20 [1, 1, 2, 1, 0, 1, 1] [1, 1, 2, 1, 0, 1, 1] 1 2 false = ([1, 1, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoR2_1121011 : invRung 7 5 20 [1, 1, 2, 1, 0, 1, 1] [1, 1, 0, 2, 1, 1, 0] 3 1 true = ([2, 2, 0, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_1121011 : fieldCube 7 5 20 [2, 2, 0, 1, 1, 0, 0] = [0, 1, 1, 0, 0, 2, 1] := by
  decide

theorem demoM_1121011 : fieldMul 7 5 20 [0, 1, 1, 0, 0, 2, 1] [1, 1, 2, 1, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1121011 : mirrorTrits [0, 1, 1, 0, 0, 2, 1] = [0, 2, 2, 0, 0, 1, 2] := by
  decide

theorem demoInv_1121011 : specInv 7 5 20 [1, 1, 2, 1, 0, 1, 1] = some [0, 2, 2, 0, 0, 1, 2] :=
  specInv_mirror_7 [1, 1, 2, 1, 0, 1, 1] [1, 1, 0, 2, 1, 1, 0] [2, 2, 0, 1, 1, 0, 0] [0, 1, 1, 0, 0, 2, 1] [0, 2, 2, 0, 0, 1, 2] demoR1_1121011 demoR2_1121011 demoC_1121011 demoM_1121011 demoMir_1121011

theorem demoR1_2121011 : invRung 7 5 20 [2, 1, 2, 1, 0, 1, 1] [2, 1, 2, 1, 0, 1, 1] 1 2 false = ([2, 0, 0, 2, 2, 1, 1], 3) := by
  decide

theorem demoR2_2121011 : invRung 7 5 20 [2, 1, 2, 1, 0, 1, 1] [2, 0, 0, 2, 2, 1, 1] 3 1 true = ([1, 0, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_2121011 : fieldCube 7 5 20 [1, 0, 1, 1, 1, 2, 0] = [1, 0, 0, 1, 2, 1, 0] := by
  decide

theorem demoM_2121011 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 1, 0] [2, 1, 2, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2121011 : specInv 7 5 20 [2, 1, 2, 1, 0, 1, 1] = some [1, 0, 0, 1, 2, 1, 0] :=
  specInv_white_7 [2, 1, 2, 1, 0, 1, 1] [2, 0, 0, 2, 2, 1, 1] [1, 0, 1, 1, 1, 2, 0] [1, 0, 0, 1, 2, 1, 0] demoR1_2121011 demoR2_2121011 demoC_2121011 demoM_2121011

theorem demoR1_0221011 : invRung 7 5 20 [0, 2, 2, 1, 0, 1, 1] [0, 2, 2, 1, 0, 1, 1] 1 2 false = ([2, 1, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_0221011 : invRung 7 5 20 [0, 2, 2, 1, 0, 1, 1] [2, 1, 1, 2, 1, 2, 2] 3 1 true = ([0, 2, 0, 2, 1, 1, 0], 3) := by
  decide

theorem demoC_0221011 : fieldCube 7 5 20 [0, 2, 0, 2, 1, 1, 0] = [0, 2, 0, 0, 1, 1, 0] := by
  decide

theorem demoM_0221011 : fieldMul 7 5 20 [0, 2, 0, 0, 1, 1, 0] [0, 2, 2, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0221011 : specInv 7 5 20 [0, 2, 2, 1, 0, 1, 1] = some [0, 2, 0, 0, 1, 1, 0] :=
  specInv_white_7 [0, 2, 2, 1, 0, 1, 1] [2, 1, 1, 2, 1, 2, 2] [0, 2, 0, 2, 1, 1, 0] [0, 2, 0, 0, 1, 1, 0] demoR1_0221011 demoR2_0221011 demoC_0221011 demoM_0221011

theorem demoR1_1221011 : invRung 7 5 20 [1, 2, 2, 1, 0, 1, 1] [1, 2, 2, 1, 0, 1, 1] 1 2 false = ([0, 0, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_1221011 : invRung 7 5 20 [1, 2, 2, 1, 0, 1, 1] [0, 0, 0, 2, 1, 2, 0] 3 1 true = ([1, 1, 0, 1, 0, 1, 0], 3) := by
  decide

theorem demoC_1221011 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 1, 0] = [0, 1, 2, 1, 1, 2, 2] := by
  decide

theorem demoM_1221011 : fieldMul 7 5 20 [0, 1, 2, 1, 1, 2, 2] [1, 2, 2, 1, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1221011 : mirrorTrits [0, 1, 2, 1, 1, 2, 2] = [0, 2, 1, 2, 2, 1, 1] := by
  decide

theorem demoInv_1221011 : specInv 7 5 20 [1, 2, 2, 1, 0, 1, 1] = some [0, 2, 1, 2, 2, 1, 1] :=
  specInv_mirror_7 [1, 2, 2, 1, 0, 1, 1] [0, 0, 0, 2, 1, 2, 0] [1, 1, 0, 1, 0, 1, 0] [0, 1, 2, 1, 1, 2, 2] [0, 2, 1, 2, 2, 1, 1] demoR1_1221011 demoR2_1221011 demoC_1221011 demoM_1221011 demoMir_1221011

theorem demoR1_2221011 : invRung 7 5 20 [2, 2, 2, 1, 0, 1, 1] [2, 2, 2, 1, 0, 1, 1] 1 2 false = ([0, 0, 1, 1, 0, 0, 2], 3) := by
  decide

theorem demoR2_2221011 : invRung 7 5 20 [2, 2, 2, 1, 0, 1, 1] [0, 0, 1, 1, 0, 0, 2] 3 1 true = ([2, 0, 1, 0, 0, 1, 0], 3) := by
  decide

theorem demoC_2221011 : fieldCube 7 5 20 [2, 0, 1, 0, 0, 1, 0] = [0, 1, 1, 0, 1, 1, 0] := by
  decide

theorem demoM_2221011 : fieldMul 7 5 20 [0, 1, 1, 0, 1, 1, 0] [2, 2, 2, 1, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2221011 : specInv 7 5 20 [2, 2, 2, 1, 0, 1, 1] = some [0, 1, 1, 0, 1, 1, 0] :=
  specInv_white_7 [2, 2, 2, 1, 0, 1, 1] [0, 0, 1, 1, 0, 0, 2] [2, 0, 1, 0, 0, 1, 0] [0, 1, 1, 0, 1, 1, 0] demoR1_2221011 demoR2_2221011 demoC_2221011 demoM_2221011

theorem demoR1_0002011 : invRung 7 5 20 [0, 0, 0, 2, 0, 1, 1] [0, 0, 0, 2, 0, 1, 1] 1 2 false = ([2, 2, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoR2_0002011 : invRung 7 5 20 [0, 0, 0, 2, 0, 1, 1] [2, 2, 2, 2, 2, 1, 2] 3 1 true = ([0, 2, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoC_0002011 : fieldCube 7 5 20 [0, 2, 1, 1, 1, 2, 2] = [0, 2, 1, 2, 1, 0, 2] := by
  decide

theorem demoM_0002011 : fieldMul 7 5 20 [0, 2, 1, 2, 1, 0, 2] [0, 0, 0, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0002011 : mirrorTrits [0, 2, 1, 2, 1, 0, 2] = [0, 1, 2, 1, 2, 0, 1] := by
  decide

theorem demoInv_0002011 : specInv 7 5 20 [0, 0, 0, 2, 0, 1, 1] = some [0, 1, 2, 1, 2, 0, 1] :=
  specInv_mirror_7 [0, 0, 0, 2, 0, 1, 1] [2, 2, 2, 2, 2, 1, 2] [0, 2, 1, 1, 1, 2, 2] [0, 2, 1, 2, 1, 0, 2] [0, 1, 2, 1, 2, 0, 1] demoR1_0002011 demoR2_0002011 demoC_0002011 demoM_0002011 demoMir_0002011

theorem demoR1_1002011 : invRung 7 5 20 [1, 0, 0, 2, 0, 1, 1] [1, 0, 0, 2, 0, 1, 1] 1 2 false = ([1, 1, 2, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_1002011 : invRung 7 5 20 [1, 0, 0, 2, 0, 1, 1] [1, 1, 2, 1, 0, 0, 1] 3 1 true = ([0, 0, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoC_1002011 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 0, 2] = [2, 1, 0, 1, 2, 0, 2] := by
  decide

theorem demoM_1002011 : fieldMul 7 5 20 [2, 1, 0, 1, 2, 0, 2] [1, 0, 0, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1002011 : specInv 7 5 20 [1, 0, 0, 2, 0, 1, 1] = some [2, 1, 0, 1, 2, 0, 2] :=
  specInv_white_7 [1, 0, 0, 2, 0, 1, 1] [1, 1, 2, 1, 0, 0, 1] [0, 0, 1, 2, 2, 0, 2] [2, 1, 0, 1, 2, 0, 2] demoR1_1002011 demoR2_1002011 demoC_1002011 demoM_1002011

theorem demoR1_2002011 : invRung 7 5 20 [2, 0, 0, 2, 0, 1, 1] [2, 0, 0, 2, 0, 1, 1] 1 2 false = ([1, 1, 1, 2, 1, 2, 2], 3) := by
  decide

theorem demoR2_2002011 : invRung 7 5 20 [2, 0, 0, 2, 0, 1, 1] [1, 1, 1, 2, 1, 2, 2] 3 1 true = ([2, 1, 2, 1, 0, 0, 2], 3) := by
  decide

theorem demoC_2002011 : fieldCube 7 5 20 [2, 1, 2, 1, 0, 0, 2] = [0, 2, 2, 0, 2, 0, 1] := by
  decide

theorem demoM_2002011 : fieldMul 7 5 20 [0, 2, 2, 0, 2, 0, 1] [2, 0, 0, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2002011 : specInv 7 5 20 [2, 0, 0, 2, 0, 1, 1] = some [0, 2, 2, 0, 2, 0, 1] :=
  specInv_white_7 [2, 0, 0, 2, 0, 1, 1] [1, 1, 1, 2, 1, 2, 2] [2, 1, 2, 1, 0, 0, 2] [0, 2, 2, 0, 2, 0, 1] demoR1_2002011 demoR2_2002011 demoC_2002011 demoM_2002011

theorem demoR1_0102011 : invRung 7 5 20 [0, 1, 0, 2, 0, 1, 1] [0, 1, 0, 2, 0, 1, 1] 1 2 false = ([2, 0, 0, 1, 0, 2, 0], 3) := by
  decide

theorem demoR2_0102011 : invRung 7 5 20 [0, 1, 0, 2, 0, 1, 1] [2, 0, 0, 1, 0, 2, 0] 3 1 true = ([0, 1, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoC_0102011 : fieldCube 7 5 20 [0, 1, 1, 0, 1, 2, 2] = [2, 2, 0, 1, 1, 2, 2] := by
  decide

theorem demoM_0102011 : fieldMul 7 5 20 [2, 2, 0, 1, 1, 2, 2] [0, 1, 0, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0102011 : specInv 7 5 20 [0, 1, 0, 2, 0, 1, 1] = some [2, 2, 0, 1, 1, 2, 2] :=
  specInv_white_7 [0, 1, 0, 2, 0, 1, 1] [2, 0, 0, 1, 0, 2, 0] [0, 1, 1, 0, 1, 2, 2] [2, 2, 0, 1, 1, 2, 2] demoR1_0102011 demoR2_0102011 demoC_0102011 demoM_0102011

theorem demoR1_1102011 : invRung 7 5 20 [1, 1, 0, 2, 0, 1, 1] [1, 1, 0, 2, 0, 1, 1] 1 2 false = ([2, 2, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_1102011 : invRung 7 5 20 [1, 1, 0, 2, 0, 1, 1] [2, 2, 0, 1, 0, 1, 1] 3 1 true = ([2, 2, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_1102011 : fieldCube 7 5 20 [2, 2, 1, 2, 2, 0, 0] = [1, 2, 2, 1, 0, 1, 0] := by
  decide

theorem demoM_1102011 : fieldMul 7 5 20 [1, 2, 2, 1, 0, 1, 0] [1, 1, 0, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1102011 : specInv 7 5 20 [1, 1, 0, 2, 0, 1, 1] = some [1, 2, 2, 1, 0, 1, 0] :=
  specInv_white_7 [1, 1, 0, 2, 0, 1, 1] [2, 2, 0, 1, 0, 1, 1] [2, 2, 1, 2, 2, 0, 0] [1, 2, 2, 1, 0, 1, 0] demoR1_1102011 demoR2_1102011 demoC_1102011 demoM_1102011

theorem demoR1_2102011 : invRung 7 5 20 [2, 1, 0, 2, 0, 1, 1] [2, 1, 0, 2, 0, 1, 1] 1 2 false = ([2, 1, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_2102011 : invRung 7 5 20 [2, 1, 0, 2, 0, 1, 1] [2, 1, 1, 2, 0, 2, 1] 3 1 true = ([2, 2, 1, 1, 0, 2, 0], 3) := by
  decide

theorem demoC_2102011 : fieldCube 7 5 20 [2, 2, 1, 1, 0, 2, 0] = [2, 2, 0, 2, 2, 0, 2] := by
  decide

theorem demoM_2102011 : fieldMul 7 5 20 [2, 2, 0, 2, 2, 0, 2] [2, 1, 0, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2102011 : specInv 7 5 20 [2, 1, 0, 2, 0, 1, 1] = some [2, 2, 0, 2, 2, 0, 2] :=
  specInv_white_7 [2, 1, 0, 2, 0, 1, 1] [2, 1, 1, 2, 0, 2, 1] [2, 2, 1, 1, 0, 2, 0] [2, 2, 0, 2, 2, 0, 2] demoR1_2102011 demoR2_2102011 demoC_2102011 demoM_2102011

theorem demoR1_0202011 : invRung 7 5 20 [0, 2, 0, 2, 0, 1, 1] [0, 2, 0, 2, 0, 1, 1] 1 2 false = ([0, 2, 0, 0, 0, 2, 1], 3) := by
  decide

theorem demoR2_0202011 : invRung 7 5 20 [0, 2, 0, 2, 0, 1, 1] [0, 2, 0, 0, 0, 2, 1] 3 1 true = ([0, 0, 0, 2, 1, 2, 2], 3) := by
  decide

theorem demoC_0202011 : fieldCube 7 5 20 [0, 0, 0, 2, 1, 2, 2] = [1, 2, 2, 0, 1, 1, 1] := by
  decide

theorem demoM_0202011 : fieldMul 7 5 20 [1, 2, 2, 0, 1, 1, 1] [0, 2, 0, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0202011 : specInv 7 5 20 [0, 2, 0, 2, 0, 1, 1] = some [1, 2, 2, 0, 1, 1, 1] :=
  specInv_white_7 [0, 2, 0, 2, 0, 1, 1] [0, 2, 0, 0, 0, 2, 1] [0, 0, 0, 2, 1, 2, 2] [1, 2, 2, 0, 1, 1, 1] demoR1_0202011 demoR2_0202011 demoC_0202011 demoM_0202011

theorem demoR1_1202011 : invRung 7 5 20 [1, 2, 0, 2, 0, 1, 1] [1, 2, 0, 2, 0, 1, 1] 1 2 false = ([1, 2, 0, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1202011 : invRung 7 5 20 [1, 2, 0, 2, 0, 1, 1] [1, 2, 0, 2, 1, 0, 2] 3 1 true = ([1, 2, 0, 1, 0, 2, 1], 3) := by
  decide

theorem demoC_1202011 : fieldCube 7 5 20 [1, 2, 0, 1, 0, 2, 1] = [1, 0, 2, 0, 0, 1, 2] := by
  decide

theorem demoM_1202011 : fieldMul 7 5 20 [1, 0, 2, 0, 0, 1, 2] [1, 2, 0, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1202011 : mirrorTrits [1, 0, 2, 0, 0, 1, 2] = [2, 0, 1, 0, 0, 2, 1] := by
  decide

theorem demoInv_1202011 : specInv 7 5 20 [1, 2, 0, 2, 0, 1, 1] = some [2, 0, 1, 0, 0, 2, 1] :=
  specInv_mirror_7 [1, 2, 0, 2, 0, 1, 1] [1, 2, 0, 2, 1, 0, 2] [1, 2, 0, 1, 0, 2, 1] [1, 0, 2, 0, 0, 1, 2] [2, 0, 1, 0, 0, 2, 1] demoR1_1202011 demoR2_1202011 demoC_1202011 demoM_1202011 demoMir_1202011

theorem demoR1_2202011 : invRung 7 5 20 [2, 2, 0, 2, 0, 1, 1] [2, 2, 0, 2, 0, 1, 1] 1 2 false = ([1, 1, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_2202011 : invRung 7 5 20 [2, 2, 0, 2, 0, 1, 1] [1, 1, 0, 1, 2, 2, 2] 3 1 true = ([0, 1, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_2202011 : fieldCube 7 5 20 [0, 1, 2, 0, 2, 0, 1] = [0, 0, 2, 1, 1, 0, 2] := by
  decide

theorem demoM_2202011 : fieldMul 7 5 20 [0, 0, 2, 1, 1, 0, 2] [2, 2, 0, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2202011 : specInv 7 5 20 [2, 2, 0, 2, 0, 1, 1] = some [0, 0, 2, 1, 1, 0, 2] :=
  specInv_white_7 [2, 2, 0, 2, 0, 1, 1] [1, 1, 0, 1, 2, 2, 2] [0, 1, 2, 0, 2, 0, 1] [0, 0, 2, 1, 1, 0, 2] demoR1_2202011 demoR2_2202011 demoC_2202011 demoM_2202011

theorem demoR1_0012011 : invRung 7 5 20 [0, 0, 1, 2, 0, 1, 1] [0, 0, 1, 2, 0, 1, 1] 1 2 false = ([1, 0, 0, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_0012011 : invRung 7 5 20 [0, 0, 1, 2, 0, 1, 1] [1, 0, 0, 2, 0, 1, 1] 3 1 true = ([1, 2, 1, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_0012011 : fieldCube 7 5 20 [1, 2, 1, 2, 1, 1, 2] = [1, 1, 1, 2, 0, 0, 0] := by
  decide

theorem demoM_0012011 : fieldMul 7 5 20 [1, 1, 1, 2, 0, 0, 0] [0, 0, 1, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0012011 : specInv 7 5 20 [0, 0, 1, 2, 0, 1, 1] = some [1, 1, 1, 2, 0, 0, 0] :=
  specInv_white_7 [0, 0, 1, 2, 0, 1, 1] [1, 0, 0, 2, 0, 1, 1] [1, 2, 1, 2, 1, 1, 2] [1, 1, 1, 2, 0, 0, 0] demoR1_0012011 demoR2_0012011 demoC_0012011 demoM_0012011

theorem demoR1_1012011 : invRung 7 5 20 [1, 0, 1, 2, 0, 1, 1] [1, 0, 1, 2, 0, 1, 1] 1 2 false = ([0, 0, 1, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_1012011 : invRung 7 5 20 [1, 0, 1, 2, 0, 1, 1] [0, 0, 1, 0, 2, 1, 0] 3 1 true = ([2, 2, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoC_1012011 : fieldCube 7 5 20 [2, 2, 1, 0, 0, 2, 0] = [1, 2, 2, 2, 2, 2, 2] := by
  decide

theorem demoM_1012011 : fieldMul 7 5 20 [1, 2, 2, 2, 2, 2, 2] [1, 0, 1, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1012011 : mirrorTrits [1, 2, 2, 2, 2, 2, 2] = [2, 1, 1, 1, 1, 1, 1] := by
  decide

theorem demoInv_1012011 : specInv 7 5 20 [1, 0, 1, 2, 0, 1, 1] = some [2, 1, 1, 1, 1, 1, 1] :=
  specInv_mirror_7 [1, 0, 1, 2, 0, 1, 1] [0, 0, 1, 0, 2, 1, 0] [2, 2, 1, 0, 0, 2, 0] [1, 2, 2, 2, 2, 2, 2] [2, 1, 1, 1, 1, 1, 1] demoR1_1012011 demoR2_1012011 demoC_1012011 demoM_1012011 demoMir_1012011

theorem demoR1_2012011 : invRung 7 5 20 [2, 0, 1, 2, 0, 1, 1] [2, 0, 1, 2, 0, 1, 1] 1 2 false = ([0, 0, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2012011 : invRung 7 5 20 [2, 0, 1, 2, 0, 1, 1] [0, 0, 1, 2, 0, 0, 2] 3 1 true = ([0, 2, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_2012011 : fieldCube 7 5 20 [0, 2, 1, 2, 2, 0, 1] = [2, 0, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_2012011 : fieldMul 7 5 20 [2, 0, 1, 2, 1, 2, 1] [2, 0, 1, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2012011 : mirrorTrits [2, 0, 1, 2, 1, 2, 1] = [1, 0, 2, 1, 2, 1, 2] := by
  decide

theorem demoInv_2012011 : specInv 7 5 20 [2, 0, 1, 2, 0, 1, 1] = some [1, 0, 2, 1, 2, 1, 2] :=
  specInv_mirror_7 [2, 0, 1, 2, 0, 1, 1] [0, 0, 1, 2, 0, 0, 2] [0, 2, 1, 2, 2, 0, 1] [2, 0, 1, 2, 1, 2, 1] [1, 0, 2, 1, 2, 1, 2] demoR1_2012011 demoR2_2012011 demoC_2012011 demoM_2012011 demoMir_2012011

theorem demoR1_0112011 : invRung 7 5 20 [0, 1, 1, 2, 0, 1, 1] [0, 1, 1, 2, 0, 1, 1] 1 2 false = ([1, 2, 2, 0, 2, 2, 1], 3) := by
  decide

theorem demoR2_0112011 : invRung 7 5 20 [0, 1, 1, 2, 0, 1, 1] [1, 2, 2, 0, 2, 2, 1] 3 1 true = ([2, 0, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_0112011 : fieldCube 7 5 20 [2, 0, 0, 2, 1, 0, 0] = [1, 1, 2, 1, 0, 0, 1] := by
  decide

theorem demoM_0112011 : fieldMul 7 5 20 [1, 1, 2, 1, 0, 0, 1] [0, 1, 1, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0112011 : mirrorTrits [1, 1, 2, 1, 0, 0, 1] = [2, 2, 1, 2, 0, 0, 2] := by
  decide

theorem demoInv_0112011 : specInv 7 5 20 [0, 1, 1, 2, 0, 1, 1] = some [2, 2, 1, 2, 0, 0, 2] :=
  specInv_mirror_7 [0, 1, 1, 2, 0, 1, 1] [1, 2, 2, 0, 2, 2, 1] [2, 0, 0, 2, 1, 0, 0] [1, 1, 2, 1, 0, 0, 1] [2, 2, 1, 2, 0, 0, 2] demoR1_0112011 demoR2_0112011 demoC_0112011 demoM_0112011 demoMir_0112011

theorem demoR1_1112011 : invRung 7 5 20 [1, 1, 1, 2, 0, 1, 1] [1, 1, 1, 2, 0, 1, 1] 1 2 false = ([1, 1, 1, 1, 1, 0, 1], 3) := by
  decide

theorem demoR2_1112011 : invRung 7 5 20 [1, 1, 1, 2, 0, 1, 1] [1, 1, 1, 1, 1, 0, 1] 3 1 true = ([2, 2, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_1112011 : fieldCube 7 5 20 [2, 2, 2, 0, 2, 1, 0] = [0, 0, 1, 1, 1, 0, 0] := by
  decide

theorem demoM_1112011 : fieldMul 7 5 20 [0, 0, 1, 1, 1, 0, 0] [1, 1, 1, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1112011 : mirrorTrits [0, 0, 1, 1, 1, 0, 0] = [0, 0, 2, 2, 2, 0, 0] := by
  decide

theorem demoInv_1112011 : specInv 7 5 20 [1, 1, 1, 2, 0, 1, 1] = some [0, 0, 2, 2, 2, 0, 0] :=
  specInv_mirror_7 [1, 1, 1, 2, 0, 1, 1] [1, 1, 1, 1, 1, 0, 1] [2, 2, 2, 0, 2, 1, 0] [0, 0, 1, 1, 1, 0, 0] [0, 0, 2, 2, 2, 0, 0] demoR1_1112011 demoR2_1112011 demoC_1112011 demoM_1112011 demoMir_1112011

theorem demoR1_2112011 : invRung 7 5 20 [2, 1, 1, 2, 0, 1, 1] [2, 1, 1, 2, 0, 1, 1] 1 2 false = ([1, 2, 1, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_2112011 : invRung 7 5 20 [2, 1, 1, 2, 0, 1, 1] [1, 2, 1, 2, 2, 2, 1] 3 1 true = ([1, 0, 2, 2, 0, 0, 0], 3) := by
  decide

theorem demoC_2112011 : fieldCube 7 5 20 [1, 0, 2, 2, 0, 0, 0] = [0, 0, 2, 0, 0, 2, 2] := by
  decide

theorem demoM_2112011 : fieldMul 7 5 20 [0, 0, 2, 0, 0, 2, 2] [2, 1, 1, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2112011 : mirrorTrits [0, 0, 2, 0, 0, 2, 2] = [0, 0, 1, 0, 0, 1, 1] := by
  decide

theorem demoInv_2112011 : specInv 7 5 20 [2, 1, 1, 2, 0, 1, 1] = some [0, 0, 1, 0, 0, 1, 1] :=
  specInv_mirror_7 [2, 1, 1, 2, 0, 1, 1] [1, 2, 1, 2, 2, 2, 1] [1, 0, 2, 2, 0, 0, 0] [0, 0, 2, 0, 0, 2, 2] [0, 0, 1, 0, 0, 1, 1] demoR1_2112011 demoR2_2112011 demoC_2112011 demoM_2112011 demoMir_2112011

theorem demoR1_0212011 : invRung 7 5 20 [0, 2, 1, 2, 0, 1, 1] [0, 2, 1, 2, 0, 1, 1] 1 2 false = ([0, 1, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_0212011 : invRung 7 5 20 [0, 2, 1, 2, 0, 1, 1] [0, 1, 1, 1, 0, 0, 1] 3 1 true = ([2, 2, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoC_0212011 : fieldCube 7 5 20 [2, 2, 0, 1, 0, 0, 0] = [0, 0, 1, 2, 0, 1, 0] := by
  decide

theorem demoM_0212011 : fieldMul 7 5 20 [0, 0, 1, 2, 0, 1, 0] [0, 2, 1, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0212011 : mirrorTrits [0, 0, 1, 2, 0, 1, 0] = [0, 0, 2, 1, 0, 2, 0] := by
  decide

theorem demoInv_0212011 : specInv 7 5 20 [0, 2, 1, 2, 0, 1, 1] = some [0, 0, 2, 1, 0, 2, 0] :=
  specInv_mirror_7 [0, 2, 1, 2, 0, 1, 1] [0, 1, 1, 1, 0, 0, 1] [2, 2, 0, 1, 0, 0, 0] [0, 0, 1, 2, 0, 1, 0] [0, 0, 2, 1, 0, 2, 0] demoR1_0212011 demoR2_0212011 demoC_0212011 demoM_0212011 demoMir_0212011

theorem demoR1_1212011 : invRung 7 5 20 [1, 2, 1, 2, 0, 1, 1] [1, 2, 1, 2, 0, 1, 1] 1 2 false = ([1, 0, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoR2_1212011 : invRung 7 5 20 [1, 2, 1, 2, 0, 1, 1] [1, 0, 1, 0, 1, 1, 0] 3 1 true = ([0, 2, 0, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_1212011 : fieldCube 7 5 20 [0, 2, 0, 1, 2, 0, 2] = [1, 1, 2, 0, 2, 2, 1] := by
  decide

theorem demoM_1212011 : fieldMul 7 5 20 [1, 1, 2, 0, 2, 2, 1] [1, 2, 1, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1212011 : specInv 7 5 20 [1, 2, 1, 2, 0, 1, 1] = some [1, 1, 2, 0, 2, 2, 1] :=
  specInv_white_7 [1, 2, 1, 2, 0, 1, 1] [1, 0, 1, 0, 1, 1, 0] [0, 2, 0, 1, 2, 0, 2] [1, 1, 2, 0, 2, 2, 1] demoR1_1212011 demoR2_1212011 demoC_1212011 demoM_1212011

theorem demoR1_2212011 : invRung 7 5 20 [2, 2, 1, 2, 0, 1, 1] [2, 2, 1, 2, 0, 1, 1] 1 2 false = ([1, 0, 1, 1, 1, 2, 2], 3) := by
  decide

theorem demoR2_2212011 : invRung 7 5 20 [2, 2, 1, 2, 0, 1, 1] [1, 0, 1, 1, 1, 2, 2] 3 1 true = ([1, 0, 0, 0, 2, 0, 0], 3) := by
  decide

theorem demoC_2212011 : fieldCube 7 5 20 [1, 0, 0, 0, 2, 0, 0] = [1, 2, 0, 2, 0, 2, 2] := by
  decide

theorem demoM_2212011 : fieldMul 7 5 20 [1, 2, 0, 2, 0, 2, 2] [2, 2, 1, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2212011 : mirrorTrits [1, 2, 0, 2, 0, 2, 2] = [2, 1, 0, 1, 0, 1, 1] := by
  decide

theorem demoInv_2212011 : specInv 7 5 20 [2, 2, 1, 2, 0, 1, 1] = some [2, 1, 0, 1, 0, 1, 1] :=
  specInv_mirror_7 [2, 2, 1, 2, 0, 1, 1] [1, 0, 1, 1, 1, 2, 2] [1, 0, 0, 0, 2, 0, 0] [1, 2, 0, 2, 0, 2, 2] [2, 1, 0, 1, 0, 1, 1] demoR1_2212011 demoR2_2212011 demoC_2212011 demoM_2212011 demoMir_2212011

theorem demoR1_0022011 : invRung 7 5 20 [0, 0, 2, 2, 0, 1, 1] [0, 0, 2, 2, 0, 1, 1] 1 2 false = ([0, 1, 2, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_0022011 : invRung 7 5 20 [0, 0, 2, 2, 0, 1, 1] [0, 1, 2, 2, 0, 1, 1] 3 1 true = ([2, 1, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoC_0022011 : fieldCube 7 5 20 [2, 1, 0, 0, 1, 2, 0] = [1, 0, 2, 2, 2, 0, 2] := by
  decide

theorem demoM_0022011 : fieldMul 7 5 20 [1, 0, 2, 2, 2, 0, 2] [0, 0, 2, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0022011 : specInv 7 5 20 [0, 0, 2, 2, 0, 1, 1] = some [1, 0, 2, 2, 2, 0, 2] :=
  specInv_white_7 [0, 0, 2, 2, 0, 1, 1] [0, 1, 2, 2, 0, 1, 1] [2, 1, 0, 0, 1, 2, 0] [1, 0, 2, 2, 2, 0, 2] demoR1_0022011 demoR2_0022011 demoC_0022011 demoM_0022011

theorem demoR1_1022011 : invRung 7 5 20 [1, 0, 2, 2, 0, 1, 1] [1, 0, 2, 2, 0, 1, 1] 1 2 false = ([1, 2, 2, 2, 0, 2, 2], 3) := by
  decide

theorem demoR2_1022011 : invRung 7 5 20 [1, 0, 2, 2, 0, 1, 1] [1, 2, 2, 2, 0, 2, 2] 3 1 true = ([2, 1, 0, 1, 1, 1, 1], 3) := by
  decide

theorem demoC_1022011 : fieldCube 7 5 20 [2, 1, 0, 1, 1, 1, 1] = [1, 0, 1, 0, 2, 1, 1] := by
  decide

theorem demoM_1022011 : fieldMul 7 5 20 [1, 0, 1, 0, 2, 1, 1] [1, 0, 2, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1022011 : mirrorTrits [1, 0, 1, 0, 2, 1, 1] = [2, 0, 2, 0, 1, 2, 2] := by
  decide

theorem demoInv_1022011 : specInv 7 5 20 [1, 0, 2, 2, 0, 1, 1] = some [2, 0, 2, 0, 1, 2, 2] :=
  specInv_mirror_7 [1, 0, 2, 2, 0, 1, 1] [1, 2, 2, 2, 0, 2, 2] [2, 1, 0, 1, 1, 1, 1] [1, 0, 1, 0, 2, 1, 1] [2, 0, 2, 0, 1, 2, 2] demoR1_1022011 demoR2_1022011 demoC_1022011 demoM_1022011 demoMir_1022011

theorem demoR1_2022011 : invRung 7 5 20 [2, 0, 2, 2, 0, 1, 1] [2, 0, 2, 2, 0, 1, 1] 1 2 false = ([0, 2, 1, 2, 1, 1, 1], 3) := by
  decide

theorem demoR2_2022011 : invRung 7 5 20 [2, 0, 2, 2, 0, 1, 1] [0, 2, 1, 2, 1, 1, 1] 3 1 true = ([0, 2, 2, 1, 1, 0, 0], 3) := by
  decide

theorem demoC_2022011 : fieldCube 7 5 20 [0, 2, 2, 1, 1, 0, 0] = [1, 1, 1, 0, 0, 2, 0] := by
  decide

theorem demoM_2022011 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 2, 0] [2, 0, 2, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2022011 : specInv 7 5 20 [2, 0, 2, 2, 0, 1, 1] = some [1, 1, 1, 0, 0, 2, 0] :=
  specInv_white_7 [2, 0, 2, 2, 0, 1, 1] [0, 2, 1, 2, 1, 1, 1] [0, 2, 2, 1, 1, 0, 0] [1, 1, 1, 0, 0, 2, 0] demoR1_2022011 demoR2_2022011 demoC_2022011 demoM_2022011

theorem demoR1_0122011 : invRung 7 5 20 [0, 1, 2, 2, 0, 1, 1] [0, 1, 2, 2, 0, 1, 1] 1 2 false = ([0, 0, 1, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_0122011 : invRung 7 5 20 [0, 1, 2, 2, 0, 1, 1] [0, 0, 1, 1, 2, 1, 2] 3 1 true = ([2, 1, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0122011 : fieldCube 7 5 20 [2, 1, 0, 1, 2, 1, 2] = [1, 2, 0, 2, 0, 0, 0] := by
  decide

theorem demoM_0122011 : fieldMul 7 5 20 [1, 2, 0, 2, 0, 0, 0] [0, 1, 2, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0122011 : specInv 7 5 20 [0, 1, 2, 2, 0, 1, 1] = some [1, 2, 0, 2, 0, 0, 0] :=
  specInv_white_7 [0, 1, 2, 2, 0, 1, 1] [0, 0, 1, 1, 2, 1, 2] [2, 1, 0, 1, 2, 1, 2] [1, 2, 0, 2, 0, 0, 0] demoR1_0122011 demoR2_0122011 demoC_0122011 demoM_0122011

theorem demoR1_1122011 : invRung 7 5 20 [1, 1, 2, 2, 0, 1, 1] [1, 1, 2, 2, 0, 1, 1] 1 2 false = ([2, 2, 0, 0, 0, 1, 0], 3) := by
  decide

theorem demoR2_1122011 : invRung 7 5 20 [1, 1, 2, 2, 0, 1, 1] [2, 2, 0, 0, 0, 1, 0] 3 1 true = ([0, 1, 0, 2, 0, 1, 0], 3) := by
  decide

theorem demoC_1122011 : fieldCube 7 5 20 [0, 1, 0, 2, 0, 1, 0] = [0, 1, 0, 1, 1, 0, 2] := by
  decide

theorem demoM_1122011 : fieldMul 7 5 20 [0, 1, 0, 1, 1, 0, 2] [1, 1, 2, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1122011 : specInv 7 5 20 [1, 1, 2, 2, 0, 1, 1] = some [0, 1, 0, 1, 1, 0, 2] :=
  specInv_white_7 [1, 1, 2, 2, 0, 1, 1] [2, 2, 0, 0, 0, 1, 0] [0, 1, 0, 2, 0, 1, 0] [0, 1, 0, 1, 1, 0, 2] demoR1_1122011 demoR2_1122011 demoC_1122011 demoM_1122011

theorem demoR1_2122011 : invRung 7 5 20 [2, 1, 2, 2, 0, 1, 1] [2, 1, 2, 2, 0, 1, 1] 1 2 false = ([1, 2, 0, 1, 2, 1, 2], 3) := by
  decide

theorem demoR2_2122011 : invRung 7 5 20 [2, 1, 2, 2, 0, 1, 1] [1, 2, 0, 1, 2, 1, 2] 3 1 true = ([0, 0, 1, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_2122011 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 1, 2] = [0, 2, 1, 1, 0, 1, 1] := by
  decide

theorem demoM_2122011 : fieldMul 7 5 20 [0, 2, 1, 1, 0, 1, 1] [2, 1, 2, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2122011 : mirrorTrits [0, 2, 1, 1, 0, 1, 1] = [0, 1, 2, 2, 0, 2, 2] := by
  decide

theorem demoInv_2122011 : specInv 7 5 20 [2, 1, 2, 2, 0, 1, 1] = some [0, 1, 2, 2, 0, 2, 2] :=
  specInv_mirror_7 [2, 1, 2, 2, 0, 1, 1] [1, 2, 0, 1, 2, 1, 2] [0, 0, 1, 2, 2, 1, 2] [0, 2, 1, 1, 0, 1, 1] [0, 1, 2, 2, 0, 2, 2] demoR1_2122011 demoR2_2122011 demoC_2122011 demoM_2122011 demoMir_2122011

theorem demoR1_0222011 : invRung 7 5 20 [0, 2, 2, 2, 0, 1, 1] [0, 2, 2, 2, 0, 1, 1] 1 2 false = ([0, 1, 1, 0, 0, 2, 0], 3) := by
  decide

theorem demoR2_0222011 : invRung 7 5 20 [0, 2, 2, 2, 0, 1, 1] [0, 1, 1, 0, 0, 2, 0] 3 1 true = ([1, 0, 2, 0, 0, 2, 2], 3) := by
  decide

theorem demoC_0222011 : fieldCube 7 5 20 [1, 0, 2, 0, 0, 2, 2] = [0, 1, 0, 2, 1, 1, 2] := by
  decide

theorem demoM_0222011 : fieldMul 7 5 20 [0, 1, 0, 2, 1, 1, 2] [0, 2, 2, 2, 0, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0222011 : specInv 7 5 20 [0, 2, 2, 2, 0, 1, 1] = some [0, 1, 0, 2, 1, 1, 2] :=
  specInv_white_7 [0, 2, 2, 2, 0, 1, 1] [0, 1, 1, 0, 0, 2, 0] [1, 0, 2, 0, 0, 2, 2] [0, 1, 0, 2, 1, 1, 2] demoR1_0222011 demoR2_0222011 demoC_0222011 demoM_0222011

theorem demoR1_1222011 : invRung 7 5 20 [1, 2, 2, 2, 0, 1, 1] [1, 2, 2, 2, 0, 1, 1] 1 2 false = ([0, 2, 2, 2, 1, 0, 2], 3) := by
  decide

theorem demoR2_1222011 : invRung 7 5 20 [1, 2, 2, 2, 0, 1, 1] [0, 2, 2, 2, 1, 0, 2] 3 1 true = ([0, 2, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_1222011 : fieldCube 7 5 20 [0, 2, 1, 2, 0, 0, 2] = [2, 2, 0, 1, 2, 1, 0] := by
  decide

theorem demoM_1222011 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 1, 0] [1, 2, 2, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1222011 : mirrorTrits [2, 2, 0, 1, 2, 1, 0] = [1, 1, 0, 2, 1, 2, 0] := by
  decide

theorem demoInv_1222011 : specInv 7 5 20 [1, 2, 2, 2, 0, 1, 1] = some [1, 1, 0, 2, 1, 2, 0] :=
  specInv_mirror_7 [1, 2, 2, 2, 0, 1, 1] [0, 2, 2, 2, 1, 0, 2] [0, 2, 1, 2, 0, 0, 2] [2, 2, 0, 1, 2, 1, 0] [1, 1, 0, 2, 1, 2, 0] demoR1_1222011 demoR2_1222011 demoC_1222011 demoM_1222011 demoMir_1222011

theorem demoR1_2222011 : invRung 7 5 20 [2, 2, 2, 2, 0, 1, 1] [2, 2, 2, 2, 0, 1, 1] 1 2 false = ([2, 0, 0, 2, 0, 0, 2], 3) := by
  decide

theorem demoR2_2222011 : invRung 7 5 20 [2, 2, 2, 2, 0, 1, 1] [2, 0, 0, 2, 0, 0, 2] 3 1 true = ([2, 2, 2, 1, 0, 2, 2], 3) := by
  decide

theorem demoC_2222011 : fieldCube 7 5 20 [2, 2, 2, 1, 0, 2, 2] = [2, 1, 1, 1, 1, 2, 2] := by
  decide

theorem demoM_2222011 : fieldMul 7 5 20 [2, 1, 1, 1, 1, 2, 2] [2, 2, 2, 2, 0, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2222011 : mirrorTrits [2, 1, 1, 1, 1, 2, 2] = [1, 2, 2, 2, 2, 1, 1] := by
  decide

theorem demoInv_2222011 : specInv 7 5 20 [2, 2, 2, 2, 0, 1, 1] = some [1, 2, 2, 2, 2, 1, 1] :=
  specInv_mirror_7 [2, 2, 2, 2, 0, 1, 1] [2, 0, 0, 2, 0, 0, 2] [2, 2, 2, 1, 0, 2, 2] [2, 1, 1, 1, 1, 2, 2] [1, 2, 2, 2, 2, 1, 1] demoR1_2222011 demoR2_2222011 demoC_2222011 demoM_2222011 demoMir_2222011

theorem demoR1_0000111 : invRung 7 5 20 [0, 0, 0, 0, 1, 1, 1] [0, 0, 0, 0, 1, 1, 1] 1 2 false = ([0, 1, 2, 2, 0, 2, 0], 3) := by
  decide

theorem demoR2_0000111 : invRung 7 5 20 [0, 0, 0, 0, 1, 1, 1] [0, 1, 2, 2, 0, 2, 0] 3 1 true = ([0, 0, 0, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_0000111 : fieldCube 7 5 20 [0, 0, 0, 1, 1, 1, 2] = [2, 1, 0, 0, 0, 2, 2] := by
  decide

theorem demoM_0000111 : fieldMul 7 5 20 [2, 1, 0, 0, 0, 2, 2] [0, 0, 0, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0000111 : specInv 7 5 20 [0, 0, 0, 0, 1, 1, 1] = some [2, 1, 0, 0, 0, 2, 2] :=
  specInv_white_7 [0, 0, 0, 0, 1, 1, 1] [0, 1, 2, 2, 0, 2, 0] [0, 0, 0, 1, 1, 1, 2] [2, 1, 0, 0, 0, 2, 2] demoR1_0000111 demoR2_0000111 demoC_0000111 demoM_0000111

theorem demoR1_1000111 : invRung 7 5 20 [1, 0, 0, 0, 1, 1, 1] [1, 0, 0, 0, 1, 1, 1] 1 2 false = ([2, 1, 2, 0, 2, 2, 0], 3) := by
  decide

theorem demoR2_1000111 : invRung 7 5 20 [1, 0, 0, 0, 1, 1, 1] [2, 1, 2, 0, 2, 2, 0] 3 1 true = ([2, 2, 2, 1, 2, 1, 0], 3) := by
  decide

theorem demoC_1000111 : fieldCube 7 5 20 [2, 2, 2, 1, 2, 1, 0] = [1, 0, 2, 1, 1, 1, 0] := by
  decide

theorem demoM_1000111 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 1, 0] [1, 0, 0, 0, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1000111 : mirrorTrits [1, 0, 2, 1, 1, 1, 0] = [2, 0, 1, 2, 2, 2, 0] := by
  decide

theorem demoInv_1000111 : specInv 7 5 20 [1, 0, 0, 0, 1, 1, 1] = some [2, 0, 1, 2, 2, 2, 0] :=
  specInv_mirror_7 [1, 0, 0, 0, 1, 1, 1] [2, 1, 2, 0, 2, 2, 0] [2, 2, 2, 1, 2, 1, 0] [1, 0, 2, 1, 1, 1, 0] [2, 0, 1, 2, 2, 2, 0] demoR1_1000111 demoR2_1000111 demoC_1000111 demoM_1000111 demoMir_1000111

theorem demoR1_2000111 : invRung 7 5 20 [2, 0, 0, 0, 1, 1, 1] [2, 0, 0, 0, 1, 1, 1] 1 2 false = ([0, 1, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoR2_2000111 : invRung 7 5 20 [2, 0, 0, 0, 1, 1, 1] [0, 1, 1, 2, 0, 2, 1] 3 1 true = ([1, 1, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_2000111 : fieldCube 7 5 20 [1, 1, 2, 2, 2, 2, 1] = [2, 2, 0, 1, 0, 1, 0] := by
  decide

theorem demoM_2000111 : fieldMul 7 5 20 [2, 2, 0, 1, 0, 1, 0] [2, 0, 0, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2000111 : specInv 7 5 20 [2, 0, 0, 0, 1, 1, 1] = some [2, 2, 0, 1, 0, 1, 0] :=
  specInv_white_7 [2, 0, 0, 0, 1, 1, 1] [0, 1, 1, 2, 0, 2, 1] [1, 1, 2, 2, 2, 2, 1] [2, 2, 0, 1, 0, 1, 0] demoR1_2000111 demoR2_2000111 demoC_2000111 demoM_2000111

theorem demoR1_0100111 : invRung 7 5 20 [0, 1, 0, 0, 1, 1, 1] [0, 1, 0, 0, 1, 1, 1] 1 2 false = ([2, 0, 1, 1, 0, 0, 1], 3) := by
  decide

theorem demoR2_0100111 : invRung 7 5 20 [0, 1, 0, 0, 1, 1, 1] [2, 0, 1, 1, 0, 0, 1] 3 1 true = ([0, 2, 2, 0, 1, 2, 1], 3) := by
  decide

theorem demoC_0100111 : fieldCube 7 5 20 [0, 2, 2, 0, 1, 2, 1] = [2, 1, 1, 1, 0, 1, 2] := by
  decide

theorem demoM_0100111 : fieldMul 7 5 20 [2, 1, 1, 1, 0, 1, 2] [0, 1, 0, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0100111 : specInv 7 5 20 [0, 1, 0, 0, 1, 1, 1] = some [2, 1, 1, 1, 0, 1, 2] :=
  specInv_white_7 [0, 1, 0, 0, 1, 1, 1] [2, 0, 1, 1, 0, 0, 1] [0, 2, 2, 0, 1, 2, 1] [2, 1, 1, 1, 0, 1, 2] demoR1_0100111 demoR2_0100111 demoC_0100111 demoM_0100111

theorem demoR1_1100111 : invRung 7 5 20 [1, 1, 0, 0, 1, 1, 1] [1, 1, 0, 0, 1, 1, 1] 1 2 false = ([1, 0, 0, 0, 1, 2, 0], 3) := by
  decide

theorem demoR2_1100111 : invRung 7 5 20 [1, 1, 0, 0, 1, 1, 1] [1, 0, 0, 0, 1, 2, 0] 3 1 true = ([2, 0, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoC_1100111 : fieldCube 7 5 20 [2, 0, 1, 0, 1, 0, 0] = [2, 1, 0, 1, 0, 1, 2] := by
  decide

theorem demoM_1100111 : fieldMul 7 5 20 [2, 1, 0, 1, 0, 1, 2] [1, 1, 0, 0, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1100111 : mirrorTrits [2, 1, 0, 1, 0, 1, 2] = [1, 2, 0, 2, 0, 2, 1] := by
  decide

theorem demoInv_1100111 : specInv 7 5 20 [1, 1, 0, 0, 1, 1, 1] = some [1, 2, 0, 2, 0, 2, 1] :=
  specInv_mirror_7 [1, 1, 0, 0, 1, 1, 1] [1, 0, 0, 0, 1, 2, 0] [2, 0, 1, 0, 1, 0, 0] [2, 1, 0, 1, 0, 1, 2] [1, 2, 0, 2, 0, 2, 1] demoR1_1100111 demoR2_1100111 demoC_1100111 demoM_1100111 demoMir_1100111

theorem demoR1_2100111 : invRung 7 5 20 [2, 1, 0, 0, 1, 1, 1] [2, 1, 0, 0, 1, 1, 1] 1 2 false = ([1, 2, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoR2_2100111 : invRung 7 5 20 [2, 1, 0, 0, 1, 1, 1] [1, 2, 0, 2, 1, 0, 0] 3 1 true = ([1, 1, 0, 1, 0, 0, 1], 3) := by
  decide

theorem demoC_2100111 : fieldCube 7 5 20 [1, 1, 0, 1, 0, 0, 1] = [2, 1, 0, 2, 1, 2, 1] := by
  decide

theorem demoM_2100111 : fieldMul 7 5 20 [2, 1, 0, 2, 1, 2, 1] [2, 1, 0, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2100111 : specInv 7 5 20 [2, 1, 0, 0, 1, 1, 1] = some [2, 1, 0, 2, 1, 2, 1] :=
  specInv_white_7 [2, 1, 0, 0, 1, 1, 1] [1, 2, 0, 2, 1, 0, 0] [1, 1, 0, 1, 0, 0, 1] [2, 1, 0, 2, 1, 2, 1] demoR1_2100111 demoR2_2100111 demoC_2100111 demoM_2100111

theorem demoR1_0200111 : invRung 7 5 20 [0, 2, 0, 0, 1, 1, 1] [0, 2, 0, 0, 1, 1, 1] 1 2 false = ([2, 2, 0, 2, 2, 0, 1], 3) := by
  decide

theorem demoR2_0200111 : invRung 7 5 20 [0, 2, 0, 0, 1, 1, 1] [2, 2, 0, 2, 2, 0, 1] 3 1 true = ([1, 1, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoC_0200111 : fieldCube 7 5 20 [1, 1, 0, 1, 1, 2, 1] = [1, 1, 2, 0, 0, 2, 0] := by
  decide

theorem demoM_0200111 : fieldMul 7 5 20 [1, 1, 2, 0, 0, 2, 0] [0, 2, 0, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0200111 : specInv 7 5 20 [0, 2, 0, 0, 1, 1, 1] = some [1, 1, 2, 0, 0, 2, 0] :=
  specInv_white_7 [0, 2, 0, 0, 1, 1, 1] [2, 2, 0, 2, 2, 0, 1] [1, 1, 0, 1, 1, 2, 1] [1, 1, 2, 0, 0, 2, 0] demoR1_0200111 demoR2_0200111 demoC_0200111 demoM_0200111

theorem demoR1_1200111 : invRung 7 5 20 [1, 2, 0, 0, 1, 1, 1] [1, 2, 0, 0, 1, 1, 1] 1 2 false = ([1, 0, 1, 0, 1, 0, 0], 3) := by
  decide

theorem demoR2_1200111 : invRung 7 5 20 [1, 2, 0, 0, 1, 1, 1] [1, 0, 1, 0, 1, 0, 0] 3 1 true = ([0, 1, 0, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_1200111 : fieldCube 7 5 20 [0, 1, 0, 0, 0, 1, 1] = [1, 2, 0, 2, 2, 2, 0] := by
  decide

theorem demoM_1200111 : fieldMul 7 5 20 [1, 2, 0, 2, 2, 2, 0] [1, 2, 0, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1200111 : specInv 7 5 20 [1, 2, 0, 0, 1, 1, 1] = some [1, 2, 0, 2, 2, 2, 0] :=
  specInv_white_7 [1, 2, 0, 0, 1, 1, 1] [1, 0, 1, 0, 1, 0, 0] [0, 1, 0, 0, 0, 1, 1] [1, 2, 0, 2, 2, 2, 0] demoR1_1200111 demoR2_1200111 demoC_1200111 demoM_1200111

theorem demoR1_2200111 : invRung 7 5 20 [2, 2, 0, 0, 1, 1, 1] [2, 2, 0, 0, 1, 1, 1] 1 2 false = ([0, 2, 2, 0, 2, 1, 0], 3) := by
  decide

theorem demoR2_2200111 : invRung 7 5 20 [2, 2, 0, 0, 1, 1, 1] [0, 2, 2, 0, 2, 1, 0] 3 1 true = ([1, 0, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoC_2200111 : fieldCube 7 5 20 [1, 0, 0, 2, 1, 1, 2] = [1, 1, 1, 0, 0, 0, 2] := by
  decide

theorem demoM_2200111 : fieldMul 7 5 20 [1, 1, 1, 0, 0, 0, 2] [2, 2, 0, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2200111 : specInv 7 5 20 [2, 2, 0, 0, 1, 1, 1] = some [1, 1, 1, 0, 0, 0, 2] :=
  specInv_white_7 [2, 2, 0, 0, 1, 1, 1] [0, 2, 2, 0, 2, 1, 0] [1, 0, 0, 2, 1, 1, 2] [1, 1, 1, 0, 0, 0, 2] demoR1_2200111 demoR2_2200111 demoC_2200111 demoM_2200111

theorem demoR1_0010111 : invRung 7 5 20 [0, 0, 1, 0, 1, 1, 1] [0, 0, 1, 0, 1, 1, 1] 1 2 false = ([0, 1, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_0010111 : invRung 7 5 20 [0, 0, 1, 0, 1, 1, 1] [0, 1, 0, 0, 2, 1, 1] 3 1 true = ([2, 2, 2, 1, 2, 1, 2], 3) := by
  decide

theorem demoC_0010111 : fieldCube 7 5 20 [2, 2, 2, 1, 2, 1, 2] = [1, 2, 0, 0, 0, 0, 2] := by
  decide

theorem demoM_0010111 : fieldMul 7 5 20 [1, 2, 0, 0, 0, 0, 2] [0, 0, 1, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0010111 : specInv 7 5 20 [0, 0, 1, 0, 1, 1, 1] = some [1, 2, 0, 0, 0, 0, 2] :=
  specInv_white_7 [0, 0, 1, 0, 1, 1, 1] [0, 1, 0, 0, 2, 1, 1] [2, 2, 2, 1, 2, 1, 2] [1, 2, 0, 0, 0, 0, 2] demoR1_0010111 demoR2_0010111 demoC_0010111 demoM_0010111

theorem demoR1_1010111 : invRung 7 5 20 [1, 0, 1, 0, 1, 1, 1] [1, 0, 1, 0, 1, 1, 1] 1 2 false = ([1, 2, 1, 2, 0, 1, 1], 3) := by
  decide

theorem demoR2_1010111 : invRung 7 5 20 [1, 0, 1, 0, 1, 1, 1] [1, 2, 1, 2, 0, 1, 1] 3 1 true = ([1, 2, 0, 2, 1, 0, 0], 3) := by
  decide

theorem demoC_1010111 : fieldCube 7 5 20 [1, 2, 0, 2, 1, 0, 0] = [0, 1, 2, 0, 0, 0, 1] := by
  decide

theorem demoM_1010111 : fieldMul 7 5 20 [0, 1, 2, 0, 0, 0, 1] [1, 0, 1, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1010111 : specInv 7 5 20 [1, 0, 1, 0, 1, 1, 1] = some [0, 1, 2, 0, 0, 0, 1] :=
  specInv_white_7 [1, 0, 1, 0, 1, 1, 1] [1, 2, 1, 2, 0, 1, 1] [1, 2, 0, 2, 1, 0, 0] [0, 1, 2, 0, 0, 0, 1] demoR1_1010111 demoR2_1010111 demoC_1010111 demoM_1010111

theorem demoR1_2010111 : invRung 7 5 20 [2, 0, 1, 0, 1, 1, 1] [2, 0, 1, 0, 1, 1, 1] 1 2 false = ([1, 2, 1, 1, 2, 0, 0], 3) := by
  decide

theorem demoR2_2010111 : invRung 7 5 20 [2, 0, 1, 0, 1, 1, 1] [1, 2, 1, 1, 2, 0, 0] 3 1 true = ([1, 1, 0, 0, 2, 1, 0], 3) := by
  decide

theorem demoC_2010111 : fieldCube 7 5 20 [1, 1, 0, 0, 2, 1, 0] = [2, 0, 1, 0, 1, 0, 1] := by
  decide

theorem demoM_2010111 : fieldMul 7 5 20 [2, 0, 1, 0, 1, 0, 1] [2, 0, 1, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2010111 : specInv 7 5 20 [2, 0, 1, 0, 1, 1, 1] = some [2, 0, 1, 0, 1, 0, 1] :=
  specInv_white_7 [2, 0, 1, 0, 1, 1, 1] [1, 2, 1, 1, 2, 0, 0] [1, 1, 0, 0, 2, 1, 0] [2, 0, 1, 0, 1, 0, 1] demoR1_2010111 demoR2_2010111 demoC_2010111 demoM_2010111

theorem demoR1_0110111 : invRung 7 5 20 [0, 1, 1, 0, 1, 1, 1] [0, 1, 1, 0, 1, 1, 1] 1 2 false = ([0, 0, 0, 0, 1, 0, 1], 3) := by
  decide

theorem demoR2_0110111 : invRung 7 5 20 [0, 1, 1, 0, 1, 1, 1] [0, 0, 0, 0, 1, 0, 1] 3 1 true = ([1, 0, 2, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_0110111 : fieldCube 7 5 20 [1, 0, 2, 2, 2, 2, 1] = [2, 2, 0, 0, 0, 1, 0] := by
  decide

theorem demoM_0110111 : fieldMul 7 5 20 [2, 2, 0, 0, 0, 1, 0] [0, 1, 1, 0, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0110111 : mirrorTrits [2, 2, 0, 0, 0, 1, 0] = [1, 1, 0, 0, 0, 2, 0] := by
  decide

theorem demoInv_0110111 : specInv 7 5 20 [0, 1, 1, 0, 1, 1, 1] = some [1, 1, 0, 0, 0, 2, 0] :=
  specInv_mirror_7 [0, 1, 1, 0, 1, 1, 1] [0, 0, 0, 0, 1, 0, 1] [1, 0, 2, 2, 2, 2, 1] [2, 2, 0, 0, 0, 1, 0] [1, 1, 0, 0, 0, 2, 0] demoR1_0110111 demoR2_0110111 demoC_0110111 demoM_0110111 demoMir_0110111

theorem demoR1_1110111 : invRung 7 5 20 [1, 1, 1, 0, 1, 1, 1] [1, 1, 1, 0, 1, 1, 1] 1 2 false = ([1, 0, 1, 2, 2, 0, 2], 3) := by
  decide

theorem demoR2_1110111 : invRung 7 5 20 [1, 1, 1, 0, 1, 1, 1] [1, 0, 1, 2, 2, 0, 2] 3 1 true = ([0, 1, 2, 1, 1, 1, 2], 3) := by
  decide

theorem demoC_1110111 : fieldCube 7 5 20 [0, 1, 2, 1, 1, 1, 2] = [2, 1, 0, 1, 0, 2, 1] := by
  decide

theorem demoM_1110111 : fieldMul 7 5 20 [2, 1, 0, 1, 0, 2, 1] [1, 1, 1, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1110111 : specInv 7 5 20 [1, 1, 1, 0, 1, 1, 1] = some [2, 1, 0, 1, 0, 2, 1] :=
  specInv_white_7 [1, 1, 1, 0, 1, 1, 1] [1, 0, 1, 2, 2, 0, 2] [0, 1, 2, 1, 1, 1, 2] [2, 1, 0, 1, 0, 2, 1] demoR1_1110111 demoR2_1110111 demoC_1110111 demoM_1110111

theorem demoR1_2110111 : invRung 7 5 20 [2, 1, 1, 0, 1, 1, 1] [2, 1, 1, 0, 1, 1, 1] 1 2 false = ([0, 1, 0, 0, 1, 1, 2], 3) := by
  decide

theorem demoR2_2110111 : invRung 7 5 20 [2, 1, 1, 0, 1, 1, 1] [0, 1, 0, 0, 1, 1, 2] 3 1 true = ([2, 1, 1, 1, 2, 0, 2], 3) := by
  decide

theorem demoC_2110111 : fieldCube 7 5 20 [2, 1, 1, 1, 2, 0, 2] = [0, 1, 2, 2, 2, 2, 2] := by
  decide

theorem demoM_2110111 : fieldMul 7 5 20 [0, 1, 2, 2, 2, 2, 2] [2, 1, 1, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2110111 : specInv 7 5 20 [2, 1, 1, 0, 1, 1, 1] = some [0, 1, 2, 2, 2, 2, 2] :=
  specInv_white_7 [2, 1, 1, 0, 1, 1, 1] [0, 1, 0, 0, 1, 1, 2] [2, 1, 1, 1, 2, 0, 2] [0, 1, 2, 2, 2, 2, 2] demoR1_2110111 demoR2_2110111 demoC_2110111 demoM_2110111

theorem demoR1_0210111 : invRung 7 5 20 [0, 2, 1, 0, 1, 1, 1] [0, 2, 1, 0, 1, 1, 1] 1 2 false = ([2, 1, 1, 2, 2, 2, 0], 3) := by
  decide

theorem demoR2_0210111 : invRung 7 5 20 [0, 2, 1, 0, 1, 1, 1] [2, 1, 1, 2, 2, 2, 0] 3 1 true = ([0, 2, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoC_0210111 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 1, 2] = [2, 0, 0, 1, 0, 1, 1] := by
  decide

theorem demoM_0210111 : fieldMul 7 5 20 [2, 0, 0, 1, 0, 1, 1] [0, 2, 1, 0, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0210111 : mirrorTrits [2, 0, 0, 1, 0, 1, 1] = [1, 0, 0, 2, 0, 2, 2] := by
  decide

theorem demoInv_0210111 : specInv 7 5 20 [0, 2, 1, 0, 1, 1, 1] = some [1, 0, 0, 2, 0, 2, 2] :=
  specInv_mirror_7 [0, 2, 1, 0, 1, 1, 1] [2, 1, 1, 2, 2, 2, 0] [0, 2, 0, 1, 0, 1, 2] [2, 0, 0, 1, 0, 1, 1] [1, 0, 0, 2, 0, 2, 2] demoR1_0210111 demoR2_0210111 demoC_0210111 demoM_0210111 demoMir_0210111

theorem demoR1_1210111 : invRung 7 5 20 [1, 2, 1, 0, 1, 1, 1] [1, 2, 1, 0, 1, 1, 1] 1 2 false = ([0, 1, 2, 2, 2, 1, 0], 3) := by
  decide

theorem demoR2_1210111 : invRung 7 5 20 [1, 2, 1, 0, 1, 1, 1] [0, 1, 2, 2, 2, 1, 0] 3 1 true = ([0, 2, 1, 0, 1, 1, 0], 3) := by
  decide

theorem demoC_1210111 : fieldCube 7 5 20 [0, 2, 1, 0, 1, 1, 0] = [1, 2, 1, 0, 1, 2, 1] := by
  decide

theorem demoM_1210111 : fieldMul 7 5 20 [1, 2, 1, 0, 1, 2, 1] [1, 2, 1, 0, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1210111 : mirrorTrits [1, 2, 1, 0, 1, 2, 1] = [2, 1, 2, 0, 2, 1, 2] := by
  decide

theorem demoInv_1210111 : specInv 7 5 20 [1, 2, 1, 0, 1, 1, 1] = some [2, 1, 2, 0, 2, 1, 2] :=
  specInv_mirror_7 [1, 2, 1, 0, 1, 1, 1] [0, 1, 2, 2, 2, 1, 0] [0, 2, 1, 0, 1, 1, 0] [1, 2, 1, 0, 1, 2, 1] [2, 1, 2, 0, 2, 1, 2] demoR1_1210111 demoR2_1210111 demoC_1210111 demoM_1210111 demoMir_1210111

theorem demoR1_2210111 : invRung 7 5 20 [2, 2, 1, 0, 1, 1, 1] [2, 2, 1, 0, 1, 1, 1] 1 2 false = ([1, 1, 0, 0, 0, 0, 2], 3) := by
  decide

theorem demoR2_2210111 : invRung 7 5 20 [2, 2, 1, 0, 1, 1, 1] [1, 1, 0, 0, 0, 0, 2] 3 1 true = ([1, 0, 2, 0, 0, 1, 1], 3) := by
  decide

theorem demoC_2210111 : fieldCube 7 5 20 [1, 0, 2, 0, 0, 1, 1] = [2, 2, 0, 1, 2, 2, 2] := by
  decide

theorem demoM_2210111 : fieldMul 7 5 20 [2, 2, 0, 1, 2, 2, 2] [2, 2, 1, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2210111 : specInv 7 5 20 [2, 2, 1, 0, 1, 1, 1] = some [2, 2, 0, 1, 2, 2, 2] :=
  specInv_white_7 [2, 2, 1, 0, 1, 1, 1] [1, 1, 0, 0, 0, 0, 2] [1, 0, 2, 0, 0, 1, 1] [2, 2, 0, 1, 2, 2, 2] demoR1_2210111 demoR2_2210111 demoC_2210111 demoM_2210111

theorem demoR1_0020111 : invRung 7 5 20 [0, 0, 2, 0, 1, 1, 1] [0, 0, 2, 0, 1, 1, 1] 1 2 false = ([1, 0, 0, 2, 1, 2, 1], 3) := by
  decide

theorem demoR2_0020111 : invRung 7 5 20 [0, 0, 2, 0, 1, 1, 1] [1, 0, 0, 2, 1, 2, 1] 3 1 true = ([2, 0, 1, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_0020111 : fieldCube 7 5 20 [2, 0, 1, 1, 1, 2, 0] = [2, 0, 0, 1, 2, 1, 0] := by
  decide

theorem demoM_0020111 : fieldMul 7 5 20 [2, 0, 0, 1, 2, 1, 0] [0, 0, 2, 0, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0020111 : mirrorTrits [2, 0, 0, 1, 2, 1, 0] = [1, 0, 0, 2, 1, 2, 0] := by
  decide

theorem demoInv_0020111 : specInv 7 5 20 [0, 0, 2, 0, 1, 1, 1] = some [1, 0, 0, 2, 1, 2, 0] :=
  specInv_mirror_7 [0, 0, 2, 0, 1, 1, 1] [1, 0, 0, 2, 1, 2, 1] [2, 0, 1, 1, 1, 2, 0] [2, 0, 0, 1, 2, 1, 0] [1, 0, 0, 2, 1, 2, 0] demoR1_0020111 demoR2_0020111 demoC_0020111 demoM_0020111 demoMir_0020111

theorem demoR1_1020111 : invRung 7 5 20 [1, 0, 2, 0, 1, 1, 1] [1, 0, 2, 0, 1, 1, 1] 1 2 false = ([0, 2, 0, 2, 1, 2, 0], 3) := by
  decide

theorem demoR2_1020111 : invRung 7 5 20 [1, 0, 2, 0, 1, 1, 1] [0, 2, 0, 2, 1, 2, 0] 3 1 true = ([2, 1, 2, 0, 1, 1, 2], 3) := by
  decide

theorem demoC_1020111 : fieldCube 7 5 20 [2, 1, 2, 0, 1, 1, 2] = [0, 1, 2, 1, 0, 1, 1] := by
  decide

theorem demoM_1020111 : fieldMul 7 5 20 [0, 1, 2, 1, 0, 1, 1] [1, 0, 2, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1020111 : specInv 7 5 20 [1, 0, 2, 0, 1, 1, 1] = some [0, 1, 2, 1, 0, 1, 1] :=
  specInv_white_7 [1, 0, 2, 0, 1, 1, 1] [0, 2, 0, 2, 1, 2, 0] [2, 1, 2, 0, 1, 1, 2] [0, 1, 2, 1, 0, 1, 1] demoR1_1020111 demoR2_1020111 demoC_1020111 demoM_1020111

theorem demoR1_2020111 : invRung 7 5 20 [2, 0, 2, 0, 1, 1, 1] [2, 0, 2, 0, 1, 1, 1] 1 2 false = ([1, 2, 2, 1, 1, 0, 2], 3) := by
  decide

theorem demoR2_2020111 : invRung 7 5 20 [2, 0, 2, 0, 1, 1, 1] [1, 2, 2, 1, 1, 0, 2] 3 1 true = ([0, 1, 0, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_2020111 : fieldCube 7 5 20 [0, 1, 0, 2, 2, 0, 0] = [2, 2, 2, 0, 0, 1, 2] := by
  decide

theorem demoM_2020111 : fieldMul 7 5 20 [2, 2, 2, 0, 0, 1, 2] [2, 0, 2, 0, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2020111 : mirrorTrits [2, 2, 2, 0, 0, 1, 2] = [1, 1, 1, 0, 0, 2, 1] := by
  decide

theorem demoInv_2020111 : specInv 7 5 20 [2, 0, 2, 0, 1, 1, 1] = some [1, 1, 1, 0, 0, 2, 1] :=
  specInv_mirror_7 [2, 0, 2, 0, 1, 1, 1] [1, 2, 2, 1, 1, 0, 2] [0, 1, 0, 2, 2, 0, 0] [2, 2, 2, 0, 0, 1, 2] [1, 1, 1, 0, 0, 2, 1] demoR1_2020111 demoR2_2020111 demoC_2020111 demoM_2020111 demoMir_2020111

theorem demoR1_0120111 : invRung 7 5 20 [0, 1, 2, 0, 1, 1, 1] [0, 1, 2, 0, 1, 1, 1] 1 2 false = ([2, 1, 0, 2, 1, 1, 2], 3) := by
  decide

theorem demoR2_0120111 : invRung 7 5 20 [0, 1, 2, 0, 1, 1, 1] [2, 1, 0, 2, 1, 1, 2] 3 1 true = ([2, 2, 1, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_0120111 : fieldCube 7 5 20 [2, 2, 1, 1, 1, 1, 0] = [1, 2, 2, 0, 1, 0, 1] := by
  decide

theorem demoM_0120111 : fieldMul 7 5 20 [1, 2, 2, 0, 1, 0, 1] [0, 1, 2, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0120111 : specInv 7 5 20 [0, 1, 2, 0, 1, 1, 1] = some [1, 2, 2, 0, 1, 0, 1] :=
  specInv_white_7 [0, 1, 2, 0, 1, 1, 1] [2, 1, 0, 2, 1, 1, 2] [2, 2, 1, 1, 1, 1, 0] [1, 2, 2, 0, 1, 0, 1] demoR1_0120111 demoR2_0120111 demoC_0120111 demoM_0120111

theorem demoR1_1120111 : invRung 7 5 20 [1, 1, 2, 0, 1, 1, 1] [1, 1, 2, 0, 1, 1, 1] 1 2 false = ([1, 1, 1, 1, 2, 2, 1], 3) := by
  decide

theorem demoR2_1120111 : invRung 7 5 20 [1, 1, 2, 0, 1, 1, 1] [1, 1, 1, 1, 2, 2, 1] 3 1 true = ([0, 0, 1, 2, 2, 0, 0], 3) := by
  decide

theorem demoC_1120111 : fieldCube 7 5 20 [0, 0, 1, 2, 2, 0, 0] = [2, 2, 2, 2, 0, 1, 0] := by
  decide

theorem demoM_1120111 : fieldMul 7 5 20 [2, 2, 2, 2, 0, 1, 0] [1, 1, 2, 0, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1120111 : mirrorTrits [2, 2, 2, 2, 0, 1, 0] = [1, 1, 1, 1, 0, 2, 0] := by
  decide

theorem demoInv_1120111 : specInv 7 5 20 [1, 1, 2, 0, 1, 1, 1] = some [1, 1, 1, 1, 0, 2, 0] :=
  specInv_mirror_7 [1, 1, 2, 0, 1, 1, 1] [1, 1, 1, 1, 2, 2, 1] [0, 0, 1, 2, 2, 0, 0] [2, 2, 2, 2, 0, 1, 0] [1, 1, 1, 1, 0, 2, 0] demoR1_1120111 demoR2_1120111 demoC_1120111 demoM_1120111 demoMir_1120111

theorem demoR1_2120111 : invRung 7 5 20 [2, 1, 2, 0, 1, 1, 1] [2, 1, 2, 0, 1, 1, 1] 1 2 false = ([1, 1, 0, 1, 0, 0, 0], 3) := by
  decide

theorem demoR2_2120111 : invRung 7 5 20 [2, 1, 2, 0, 1, 1, 1] [1, 1, 0, 1, 0, 0, 0] 3 1 true = ([1, 0, 0, 1, 1, 2, 0], 3) := by
  decide

theorem demoC_2120111 : fieldCube 7 5 20 [1, 0, 0, 1, 1, 2, 0] = [1, 0, 0, 1, 2, 1, 2] := by
  decide

theorem demoM_2120111 : fieldMul 7 5 20 [1, 0, 0, 1, 2, 1, 2] [2, 1, 2, 0, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2120111 : mirrorTrits [1, 0, 0, 1, 2, 1, 2] = [2, 0, 0, 2, 1, 2, 1] := by
  decide

theorem demoInv_2120111 : specInv 7 5 20 [2, 1, 2, 0, 1, 1, 1] = some [2, 0, 0, 2, 1, 2, 1] :=
  specInv_mirror_7 [2, 1, 2, 0, 1, 1, 1] [1, 1, 0, 1, 0, 0, 0] [1, 0, 0, 1, 1, 2, 0] [1, 0, 0, 1, 2, 1, 2] [2, 0, 0, 2, 1, 2, 1] demoR1_2120111 demoR2_2120111 demoC_2120111 demoM_2120111 demoMir_2120111

theorem demoR1_0220111 : invRung 7 5 20 [0, 2, 2, 0, 1, 1, 1] [0, 2, 2, 0, 1, 1, 1] 1 2 false = ([0, 0, 2, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_0220111 : invRung 7 5 20 [0, 2, 2, 0, 1, 1, 1] [0, 0, 2, 1, 0, 1, 2] 3 1 true = ([1, 1, 2, 0, 2, 0, 1], 3) := by
  decide

theorem demoC_0220111 : fieldCube 7 5 20 [1, 1, 2, 0, 2, 0, 1] = [1, 0, 2, 1, 1, 0, 2] := by
  decide

theorem demoM_0220111 : fieldMul 7 5 20 [1, 0, 2, 1, 1, 0, 2] [0, 2, 2, 0, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0220111 : mirrorTrits [1, 0, 2, 1, 1, 0, 2] = [2, 0, 1, 2, 2, 0, 1] := by
  decide

theorem demoInv_0220111 : specInv 7 5 20 [0, 2, 2, 0, 1, 1, 1] = some [2, 0, 1, 2, 2, 0, 1] :=
  specInv_mirror_7 [0, 2, 2, 0, 1, 1, 1] [0, 0, 2, 1, 0, 1, 2] [1, 1, 2, 0, 2, 0, 1] [1, 0, 2, 1, 1, 0, 2] [2, 0, 1, 2, 2, 0, 1] demoR1_0220111 demoR2_0220111 demoC_0220111 demoM_0220111 demoMir_0220111

theorem demoR1_1220111 : invRung 7 5 20 [1, 2, 2, 0, 1, 1, 1] [1, 2, 2, 0, 1, 1, 1] 1 2 false = ([2, 2, 1, 0, 1, 2, 2], 3) := by
  decide

theorem demoR2_1220111 : invRung 7 5 20 [1, 2, 2, 0, 1, 1, 1] [2, 2, 1, 0, 1, 2, 2] 3 1 true = ([2, 2, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoC_1220111 : fieldCube 7 5 20 [2, 2, 0, 2, 2, 2, 1] = [0, 2, 0, 2, 0, 1, 1] := by
  decide

theorem demoM_1220111 : fieldMul 7 5 20 [0, 2, 0, 2, 0, 1, 1] [1, 2, 2, 0, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1220111 : specInv 7 5 20 [1, 2, 2, 0, 1, 1, 1] = some [0, 2, 0, 2, 0, 1, 1] :=
  specInv_white_7 [1, 2, 2, 0, 1, 1, 1] [2, 2, 1, 0, 1, 2, 2] [2, 2, 0, 2, 2, 2, 1] [0, 2, 0, 2, 0, 1, 1] demoR1_1220111 demoR2_1220111 demoC_1220111 demoM_1220111

theorem demoR1_2220111 : invRung 7 5 20 [2, 2, 2, 0, 1, 1, 1] [2, 2, 2, 0, 1, 1, 1] 1 2 false = ([1, 0, 0, 2, 2, 2, 2], 3) := by
  decide

theorem demoR2_2220111 : invRung 7 5 20 [2, 2, 2, 0, 1, 1, 1] [1, 0, 0, 2, 2, 2, 2] 3 1 true = ([1, 1, 0, 2, 0, 1, 2], 3) := by
  decide

theorem demoC_2220111 : fieldCube 7 5 20 [1, 1, 0, 2, 0, 1, 2] = [1, 0, 1, 0, 0, 2, 1] := by
  decide

theorem demoM_2220111 : fieldMul 7 5 20 [1, 0, 1, 0, 0, 2, 1] [2, 2, 2, 0, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2220111 : mirrorTrits [1, 0, 1, 0, 0, 2, 1] = [2, 0, 2, 0, 0, 1, 2] := by
  decide

theorem demoInv_2220111 : specInv 7 5 20 [2, 2, 2, 0, 1, 1, 1] = some [2, 0, 2, 0, 0, 1, 2] :=
  specInv_mirror_7 [2, 2, 2, 0, 1, 1, 1] [1, 0, 0, 2, 2, 2, 2] [1, 1, 0, 2, 0, 1, 2] [1, 0, 1, 0, 0, 2, 1] [2, 0, 2, 0, 0, 1, 2] demoR1_2220111 demoR2_2220111 demoC_2220111 demoM_2220111 demoMir_2220111

theorem demoR1_0001111 : invRung 7 5 20 [0, 0, 0, 1, 1, 1, 1] [0, 0, 0, 1, 1, 1, 1] 1 2 false = ([1, 2, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_0001111 : invRung 7 5 20 [0, 0, 0, 1, 1, 1, 1] [1, 2, 0, 1, 0, 1, 1] 3 1 true = ([0, 1, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_0001111 : fieldCube 7 5 20 [0, 1, 1, 2, 0, 2, 1] = [1, 0, 0, 2, 0, 2, 0] := by
  decide

theorem demoM_0001111 : fieldMul 7 5 20 [1, 0, 0, 2, 0, 2, 0] [0, 0, 0, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0001111 : mirrorTrits [1, 0, 0, 2, 0, 2, 0] = [2, 0, 0, 1, 0, 1, 0] := by
  decide

theorem demoInv_0001111 : specInv 7 5 20 [0, 0, 0, 1, 1, 1, 1] = some [2, 0, 0, 1, 0, 1, 0] :=
  specInv_mirror_7 [0, 0, 0, 1, 1, 1, 1] [1, 2, 0, 1, 0, 1, 1] [0, 1, 1, 2, 0, 2, 1] [1, 0, 0, 2, 0, 2, 0] [2, 0, 0, 1, 0, 1, 0] demoR1_0001111 demoR2_0001111 demoC_0001111 demoM_0001111 demoMir_0001111

theorem demoR1_1001111 : invRung 7 5 20 [1, 0, 0, 1, 1, 1, 1] [1, 0, 0, 1, 1, 1, 1] 1 2 false = ([0, 0, 0, 1, 0, 1, 2], 3) := by
  decide

theorem demoR2_1001111 : invRung 7 5 20 [1, 0, 0, 1, 1, 1, 1] [0, 0, 0, 1, 0, 1, 2] 3 1 true = ([2, 0, 2, 1, 2, 2, 0], 3) := by
  decide

theorem demoC_1001111 : fieldCube 7 5 20 [2, 0, 2, 1, 2, 2, 0] = [2, 1, 0, 2, 2, 2, 2] := by
  decide

theorem demoM_1001111 : fieldMul 7 5 20 [2, 1, 0, 2, 2, 2, 2] [1, 0, 0, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1001111 : specInv 7 5 20 [1, 0, 0, 1, 1, 1, 1] = some [2, 1, 0, 2, 2, 2, 2] :=
  specInv_white_7 [1, 0, 0, 1, 1, 1, 1] [0, 0, 0, 1, 0, 1, 2] [2, 0, 2, 1, 2, 2, 0] [2, 1, 0, 2, 2, 2, 2] demoR1_1001111 demoR2_1001111 demoC_1001111 demoM_1001111

theorem demoR1_2001111 : invRung 7 5 20 [2, 0, 0, 1, 1, 1, 1] [2, 0, 0, 1, 1, 1, 1] 1 2 false = ([1, 0, 0, 1, 1, 2, 1], 3) := by
  decide

theorem demoR2_2001111 : invRung 7 5 20 [2, 0, 0, 1, 1, 1, 1] [1, 0, 0, 1, 1, 2, 1] 3 1 true = ([0, 1, 1, 0, 1, 0, 1], 3) := by
  decide

theorem demoC_2001111 : fieldCube 7 5 20 [0, 1, 1, 0, 1, 0, 1] = [0, 2, 2, 0, 1, 2, 0] := by
  decide

theorem demoM_2001111 : fieldMul 7 5 20 [0, 2, 2, 0, 1, 2, 0] [2, 0, 0, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2001111 : specInv 7 5 20 [2, 0, 0, 1, 1, 1, 1] = some [0, 2, 2, 0, 1, 2, 0] :=
  specInv_white_7 [2, 0, 0, 1, 1, 1, 1] [1, 0, 0, 1, 1, 2, 1] [0, 1, 1, 0, 1, 0, 1] [0, 2, 2, 0, 1, 2, 0] demoR1_2001111 demoR2_2001111 demoC_2001111 demoM_2001111

theorem demoR1_0101111 : invRung 7 5 20 [0, 1, 0, 1, 1, 1, 1] [0, 1, 0, 1, 1, 1, 1] 1 2 false = ([0, 2, 0, 0, 2, 0, 1], 3) := by
  decide

theorem demoR2_0101111 : invRung 7 5 20 [0, 1, 0, 1, 1, 1, 1] [0, 2, 0, 0, 2, 0, 1] 3 1 true = ([1, 1, 1, 2, 0, 0, 2], 3) := by
  decide

theorem demoC_0101111 : fieldCube 7 5 20 [1, 1, 1, 2, 0, 0, 2] = [0, 2, 0, 0, 2, 1, 0] := by
  decide

theorem demoM_0101111 : fieldMul 7 5 20 [0, 2, 0, 0, 2, 1, 0] [0, 1, 0, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0101111 : mirrorTrits [0, 2, 0, 0, 2, 1, 0] = [0, 1, 0, 0, 1, 2, 0] := by
  decide

theorem demoInv_0101111 : specInv 7 5 20 [0, 1, 0, 1, 1, 1, 1] = some [0, 1, 0, 0, 1, 2, 0] :=
  specInv_mirror_7 [0, 1, 0, 1, 1, 1, 1] [0, 2, 0, 0, 2, 0, 1] [1, 1, 1, 2, 0, 0, 2] [0, 2, 0, 0, 2, 1, 0] [0, 1, 0, 0, 1, 2, 0] demoR1_0101111 demoR2_0101111 demoC_0101111 demoM_0101111 demoMir_0101111

theorem demoR1_1101111 : invRung 7 5 20 [1, 1, 0, 1, 1, 1, 1] [1, 1, 0, 1, 1, 1, 1] 1 2 false = ([0, 0, 2, 1, 0, 1, 1], 3) := by
  decide

theorem demoR2_1101111 : invRung 7 5 20 [1, 1, 0, 1, 1, 1, 1] [0, 0, 2, 1, 0, 1, 1] 3 1 true = ([0, 0, 0, 1, 1, 1, 0], 3) := by
  decide

theorem demoC_1101111 : fieldCube 7 5 20 [0, 0, 0, 1, 1, 1, 0] = [2, 2, 2, 1, 1, 0, 0] := by
  decide

theorem demoM_1101111 : fieldMul 7 5 20 [2, 2, 2, 1, 1, 0, 0] [1, 1, 0, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1101111 : specInv 7 5 20 [1, 1, 0, 1, 1, 1, 1] = some [2, 2, 2, 1, 1, 0, 0] :=
  specInv_white_7 [1, 1, 0, 1, 1, 1, 1] [0, 0, 2, 1, 0, 1, 1] [0, 0, 0, 1, 1, 1, 0] [2, 2, 2, 1, 1, 0, 0] demoR1_1101111 demoR2_1101111 demoC_1101111 demoM_1101111

theorem demoR1_2101111 : invRung 7 5 20 [2, 1, 0, 1, 1, 1, 1] [2, 1, 0, 1, 1, 1, 1] 1 2 false = ([1, 2, 0, 1, 2, 2, 2], 3) := by
  decide

theorem demoR2_2101111 : invRung 7 5 20 [2, 1, 0, 1, 1, 1, 1] [1, 2, 0, 1, 2, 2, 2] 3 1 true = ([2, 1, 2, 2, 2, 1, 2], 3) := by
  decide

theorem demoC_2101111 : fieldCube 7 5 20 [2, 1, 2, 2, 2, 1, 2] = [2, 2, 1, 2, 0, 1, 2] := by
  decide

theorem demoM_2101111 : fieldMul 7 5 20 [2, 2, 1, 2, 0, 1, 2] [2, 1, 0, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_2101111 : specInv 7 5 20 [2, 1, 0, 1, 1, 1, 1] = some [2, 2, 1, 2, 0, 1, 2] :=
  specInv_white_7 [2, 1, 0, 1, 1, 1, 1] [1, 2, 0, 1, 2, 2, 2] [2, 1, 2, 2, 2, 1, 2] [2, 2, 1, 2, 0, 1, 2] demoR1_2101111 demoR2_2101111 demoC_2101111 demoM_2101111

theorem demoR1_0201111 : invRung 7 5 20 [0, 2, 0, 1, 1, 1, 1] [0, 2, 0, 1, 1, 1, 1] 1 2 false = ([0, 0, 0, 2, 2, 2, 1], 3) := by
  decide

theorem demoR2_0201111 : invRung 7 5 20 [0, 2, 0, 1, 1, 1, 1] [0, 0, 0, 2, 2, 2, 1] 3 1 true = ([1, 2, 2, 0, 2, 0, 2], 3) := by
  decide

theorem demoC_0201111 : fieldCube 7 5 20 [1, 2, 2, 0, 2, 0, 2] = [1, 1, 1, 0, 2, 1, 0] := by
  decide

theorem demoM_0201111 : fieldMul 7 5 20 [1, 1, 1, 0, 2, 1, 0] [0, 2, 0, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_0201111 : mirrorTrits [1, 1, 1, 0, 2, 1, 0] = [2, 2, 2, 0, 1, 2, 0] := by
  decide

theorem demoInv_0201111 : specInv 7 5 20 [0, 2, 0, 1, 1, 1, 1] = some [2, 2, 2, 0, 1, 2, 0] :=
  specInv_mirror_7 [0, 2, 0, 1, 1, 1, 1] [0, 0, 0, 2, 2, 2, 1] [1, 2, 2, 0, 2, 0, 2] [1, 1, 1, 0, 2, 1, 0] [2, 2, 2, 0, 1, 2, 0] demoR1_0201111 demoR2_0201111 demoC_0201111 demoM_0201111 demoMir_0201111

theorem demoR1_1201111 : invRung 7 5 20 [1, 2, 0, 1, 1, 1, 1] [1, 2, 0, 1, 1, 1, 1] 1 2 false = ([1, 2, 1, 2, 0, 0, 1], 3) := by
  decide

theorem demoR2_1201111 : invRung 7 5 20 [1, 2, 0, 1, 1, 1, 1] [1, 2, 1, 2, 0, 0, 1] 3 1 true = ([0, 1, 1, 1, 2, 0, 1], 3) := by
  decide

theorem demoC_1201111 : fieldCube 7 5 20 [0, 1, 1, 1, 2, 0, 1] = [1, 0, 0, 1, 1, 1, 1] := by
  decide

theorem demoM_1201111 : fieldMul 7 5 20 [1, 0, 0, 1, 1, 1, 1] [1, 2, 0, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_1201111 : mirrorTrits [1, 0, 0, 1, 1, 1, 1] = [2, 0, 0, 2, 2, 2, 2] := by
  decide

theorem demoInv_1201111 : specInv 7 5 20 [1, 2, 0, 1, 1, 1, 1] = some [2, 0, 0, 2, 2, 2, 2] :=
  specInv_mirror_7 [1, 2, 0, 1, 1, 1, 1] [1, 2, 1, 2, 0, 0, 1] [0, 1, 1, 1, 2, 0, 1] [1, 0, 0, 1, 1, 1, 1] [2, 0, 0, 2, 2, 2, 2] demoR1_1201111 demoR2_1201111 demoC_1201111 demoM_1201111 demoMir_1201111

theorem demoR1_2201111 : invRung 7 5 20 [2, 2, 0, 1, 1, 1, 1] [2, 2, 0, 1, 1, 1, 1] 1 2 false = ([2, 1, 0, 0, 2, 0, 2], 3) := by
  decide

theorem demoR2_2201111 : invRung 7 5 20 [2, 2, 0, 1, 1, 1, 1] [2, 1, 0, 0, 2, 0, 2] 3 1 true = ([2, 1, 1, 2, 0, 2, 1], 3) := by
  decide

theorem demoC_2201111 : fieldCube 7 5 20 [2, 1, 1, 2, 0, 2, 1] = [0, 0, 0, 2, 0, 2, 0] := by
  decide

theorem demoM_2201111 : fieldMul 7 5 20 [0, 0, 0, 2, 0, 2, 0] [2, 2, 0, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2201111 : mirrorTrits [0, 0, 0, 2, 0, 2, 0] = [0, 0, 0, 1, 0, 1, 0] := by
  decide

theorem demoInv_2201111 : specInv 7 5 20 [2, 2, 0, 1, 1, 1, 1] = some [0, 0, 0, 1, 0, 1, 0] :=
  specInv_mirror_7 [2, 2, 0, 1, 1, 1, 1] [2, 1, 0, 0, 2, 0, 2] [2, 1, 1, 2, 0, 2, 1] [0, 0, 0, 2, 0, 2, 0] [0, 0, 0, 1, 0, 1, 0] demoR1_2201111 demoR2_2201111 demoC_2201111 demoM_2201111 demoMir_2201111

theorem demoR1_0011111 : invRung 7 5 20 [0, 0, 1, 1, 1, 1, 1] [0, 0, 1, 1, 1, 1, 1] 1 2 false = ([1, 2, 2, 1, 0, 2, 1], 3) := by
  decide

theorem demoR2_0011111 : invRung 7 5 20 [0, 0, 1, 1, 1, 1, 1] [1, 2, 2, 1, 0, 2, 1] 3 1 true = ([2, 0, 2, 0, 2, 1, 1], 3) := by
  decide

theorem demoC_0011111 : fieldCube 7 5 20 [2, 0, 2, 0, 2, 1, 1] = [0, 1, 0, 0, 2, 1, 1] := by
  decide

theorem demoM_0011111 : fieldMul 7 5 20 [0, 1, 0, 0, 2, 1, 1] [0, 0, 1, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0011111 : specInv 7 5 20 [0, 0, 1, 1, 1, 1, 1] = some [0, 1, 0, 0, 2, 1, 1] :=
  specInv_white_7 [0, 0, 1, 1, 1, 1, 1] [1, 2, 2, 1, 0, 2, 1] [2, 0, 2, 0, 2, 1, 1] [0, 1, 0, 0, 2, 1, 1] demoR1_0011111 demoR2_0011111 demoC_0011111 demoM_0011111

theorem demoR1_1011111 : invRung 7 5 20 [1, 0, 1, 1, 1, 1, 1] [1, 0, 1, 1, 1, 1, 1] 1 2 false = ([2, 2, 1, 1, 1, 0, 0], 3) := by
  decide

theorem demoR2_1011111 : invRung 7 5 20 [1, 0, 1, 1, 1, 1, 1] [2, 2, 1, 1, 1, 0, 0] 3 1 true = ([2, 1, 1, 1, 1, 0, 2], 3) := by
  decide

theorem demoC_1011111 : fieldCube 7 5 20 [2, 1, 1, 1, 1, 0, 2] = [0, 0, 2, 1, 2, 1, 1] := by
  decide

theorem demoM_1011111 : fieldMul 7 5 20 [0, 0, 2, 1, 2, 1, 1] [1, 0, 1, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1011111 : specInv 7 5 20 [1, 0, 1, 1, 1, 1, 1] = some [0, 0, 2, 1, 2, 1, 1] :=
  specInv_white_7 [1, 0, 1, 1, 1, 1, 1] [2, 2, 1, 1, 1, 0, 0] [2, 1, 1, 1, 1, 0, 2] [0, 0, 2, 1, 2, 1, 1] demoR1_1011111 demoR2_1011111 demoC_1011111 demoM_1011111

theorem demoR1_2011111 : invRung 7 5 20 [2, 0, 1, 1, 1, 1, 1] [2, 0, 1, 1, 1, 1, 1] 1 2 false = ([2, 0, 0, 0, 2, 1, 1], 3) := by
  decide

theorem demoR2_2011111 : invRung 7 5 20 [2, 0, 1, 1, 1, 1, 1] [2, 0, 0, 0, 2, 1, 1] 3 1 true = ([0, 2, 0, 1, 0, 1, 1], 3) := by
  decide

theorem demoC_2011111 : fieldCube 7 5 20 [0, 2, 0, 1, 0, 1, 1] = [2, 2, 1, 0, 2, 0, 0] := by
  decide

theorem demoM_2011111 : fieldMul 7 5 20 [2, 2, 1, 0, 2, 0, 0] [2, 0, 1, 1, 1, 1, 1] = 2 :: List.replicate 6 0 := by
  decide

theorem demoMir_2011111 : mirrorTrits [2, 2, 1, 0, 2, 0, 0] = [1, 1, 2, 0, 1, 0, 0] := by
  decide

theorem demoInv_2011111 : specInv 7 5 20 [2, 0, 1, 1, 1, 1, 1] = some [1, 1, 2, 0, 1, 0, 0] :=
  specInv_mirror_7 [2, 0, 1, 1, 1, 1, 1] [2, 0, 0, 0, 2, 1, 1] [0, 2, 0, 1, 0, 1, 1] [2, 2, 1, 0, 2, 0, 0] [1, 1, 2, 0, 1, 0, 0] demoR1_2011111 demoR2_2011111 demoC_2011111 demoM_2011111 demoMir_2011111

theorem demoR1_0111111 : invRung 7 5 20 [0, 1, 1, 1, 1, 1, 1] [0, 1, 1, 1, 1, 1, 1] 1 2 false = ([2, 1, 2, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_0111111 : invRung 7 5 20 [0, 1, 1, 1, 1, 1, 1] [2, 1, 2, 2, 0, 1, 0] 3 1 true = ([1, 2, 1, 2, 2, 0, 1], 3) := by
  decide

theorem demoC_0111111 : fieldCube 7 5 20 [1, 2, 1, 2, 2, 0, 1] = [0, 0, 1, 2, 1, 2, 1] := by
  decide

theorem demoM_0111111 : fieldMul 7 5 20 [0, 0, 1, 2, 1, 2, 1] [0, 1, 1, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_0111111 : specInv 7 5 20 [0, 1, 1, 1, 1, 1, 1] = some [0, 0, 1, 2, 1, 2, 1] :=
  specInv_white_7 [0, 1, 1, 1, 1, 1, 1] [2, 1, 2, 2, 0, 1, 0] [1, 2, 1, 2, 2, 0, 1] [0, 0, 1, 2, 1, 2, 1] demoR1_0111111 demoR2_0111111 demoC_0111111 demoM_0111111

theorem demoR1_1111111 : invRung 7 5 20 [1, 1, 1, 1, 1, 1, 1] [1, 1, 1, 1, 1, 1, 1] 1 2 false = ([1, 0, 1, 2, 0, 1, 0], 3) := by
  decide

theorem demoR2_1111111 : invRung 7 5 20 [1, 1, 1, 1, 1, 1, 1] [1, 0, 1, 2, 0, 1, 0] 3 1 true = ([1, 1, 2, 1, 2, 2, 1], 3) := by
  decide

theorem demoC_1111111 : fieldCube 7 5 20 [1, 1, 2, 1, 2, 2, 1] = [1, 2, 2, 1, 0, 0, 0] := by
  decide

theorem demoM_1111111 : fieldMul 7 5 20 [1, 2, 2, 1, 0, 0, 0] [1, 1, 1, 1, 1, 1, 1] = whiteHole0 7 := by
  decide

theorem demoInv_1111111 : specInv 7 5 20 [1, 1, 1, 1, 1, 1, 1] = some [1, 2, 2, 1, 0, 0, 0] :=
  specInv_white_7 [1, 1, 1, 1, 1, 1, 1] [1, 0, 1, 2, 0, 1, 0] [1, 1, 2, 1, 2, 2, 1] [1, 2, 2, 1, 0, 0, 0] demoR1_1111111 demoR2_1111111 demoC_1111111 demoM_1111111

end EcbsLink2.Link2
