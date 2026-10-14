/-
  The §5.1 base point, evaluated on the two tiers whose coordinates are written out.
-/
import EcbsLink2.SpecBase

namespace EcbsLink2.Spec

/-- SPEC.md §5.1 line 198, Demo, hole 0 first: x = `.RWR.WW`, y = `R..RRWR`.
    Line 197: the first working hole is 2, so hole 1 is not a hit. -/
private theorem demo_n : demo.n = 7 := by decide
private theorem demo_k : demo.k = 5 := by decide
private theorem demo_bench : demo.benchlen = 20 := by decide

private theorem demo_digits : rootDigits 7 = [2, 0, 2, 0, 2, 1] := by decide

private theorem demo_side1 :
    curveSide 7 5 20 (basisPeg 7 1) = [1, 0, 2, 1, 0, 0, 0] := by decide

private theorem demo_side2 :
    curveSide 7 5 20 (basisPeg 7 2) = [1, 0, 0, 0, 2, 0, 1] := by decide

private theorem demo_pow1 :
    fieldPowDigits 7 5 20 [1, 0, 2, 1, 0, 0, 0] [2, 0, 2, 0, 2, 1] =
      [0, 2, 0, 1, 0, 2, 2] := by
  unfold fieldPowDigits
  simp only [List.foldl_cons, List.foldl_nil]
  have h1 : powStep 7 5 20 [1, 0, 2, 1, 0, 0, 0] (whiteHole0 7) 2 =
      [1, 0, 1, 2, 1, 1, 1] := by decide
  rw [h1]
  have h2 : powStep 7 5 20 [1, 0, 2, 1, 0, 0, 0] [1, 0, 1, 2, 1, 1, 1] 0 =
      [1, 0, 2, 2, 2, 2, 2] := by decide
  rw [h2]
  have h3 : powStep 7 5 20 [1, 0, 2, 1, 0, 0, 0] [1, 0, 2, 2, 2, 2, 2] 2 =
      [0, 2, 1, 1, 2, 2, 1] := by decide
  rw [h3]
  have h4 : powStep 7 5 20 [1, 0, 2, 1, 0, 0, 0] [0, 2, 1, 1, 2, 2, 1] 0 =
      [0, 2, 2, 2, 0, 0, 2] := by decide
  rw [h4]
  have h5 : powStep 7 5 20 [1, 0, 2, 1, 0, 0, 0] [0, 2, 2, 2, 0, 0, 2] 2 =
      [0, 1, 1, 0, 1, 2, 2] := by decide
  rw [h5]
  decide

private theorem demo_pow2 :
    fieldPowDigits 7 5 20 [1, 0, 0, 0, 2, 0, 1] [2, 0, 2, 0, 2, 1] =
      [1, 1, 2, 0, 0, 1, 2] := by
  unfold fieldPowDigits
  simp only [List.foldl_cons, List.foldl_nil]
  have h1 : powStep 7 5 20 [1, 0, 0, 0, 2, 0, 1] (whiteHole0 7) 2 =
      [1, 0, 0, 2, 1, 1, 2] := by decide
  rw [h1]
  have h2 : powStep 7 5 20 [1, 0, 0, 0, 2, 0, 1] [1, 0, 0, 2, 1, 1, 2] 0 =
      [1, 1, 1, 0, 0, 0, 2] := by decide
  rw [h2]
  have h3 : powStep 7 5 20 [1, 0, 0, 0, 2, 0, 1] [1, 1, 1, 0, 0, 0, 2] 2 =
      [0, 1, 0, 2, 2, 0, 1] := by decide
  rw [h3]
  have h4 : powStep 7 5 20 [1, 0, 0, 0, 2, 0, 1] [0, 1, 0, 2, 2, 0, 1] 0 =
      [2, 0, 1, 1, 1, 2, 0] := by decide
  rw [h4]
  have h5 : powStep 7 5 20 [1, 0, 0, 0, 2, 0, 1] [2, 0, 1, 1, 1, 2, 0] 2 =
      [2, 1, 1, 1, 0, 0, 1] := by decide
  rw [h5]
  decide

private theorem demo_sq1 :
    fieldMul 7 5 20 [0, 2, 0, 1, 0, 2, 2] [0, 2, 0, 1, 0, 2, 2] =
      [2, 0, 1, 2, 0, 0, 0] := by decide

private theorem demo_sq2 :
    fieldMul 7 5 20 [1, 1, 2, 0, 0, 1, 2] [1, 1, 2, 0, 0, 1, 2] =
      [1, 0, 0, 0, 2, 0, 1] := by decide

theorem demo_root_hole1 :
    rootHit demo.n demo.k demo.benchlen (basisPeg demo.n 1) = false := by
  unfold rootHit rootY
  rw [demo_n, demo_k, demo_bench, demo_side1, demo_digits, demo_pow1, demo_sq1]
  decide

theorem demo_rootY :
    rootY demo.n demo.k demo.benchlen (basisPeg demo.n 2) = [1, 1, 2, 0, 0, 1, 2] := by
  unfold rootY
  rw [demo_n, demo_k, demo_bench, demo_side2, demo_digits, demo_pow2]

theorem demo_root_hole2 :
    rootHit demo.n demo.k demo.benchlen (basisPeg demo.n 2) = true := by
  unfold rootHit
  rw [demo_rootY, demo_n, demo_k, demo_bench, demo_sq2, demo_side2]
  decide

private theorem demo_rungs6 : specRungs 6 = [1, 2] := by
  unfold specRungs specRungsGo rungColour
  decide

private theorem specInv_white (x g1 g2 g : List Nat)
    (h1 : invRung 7 5 20 x x 1 2 false = (g1, 3))
    (h2 : invRung 7 5 20 x g1 3 1 true = (g2, 3))
    (hg : fieldCube 7 5 20 g2 = g)
    (hv : fieldMul 7 5 20 g x = whiteHole0 7) :
    specInv 7 5 20 x = some g := by
  unfold specInv invGapOf
  rw [show (7 - 1) = 6 by decide, demo_rungs6]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  unfold invClimb
  simp only [List.isEmpty]
  rw [h1]
  unfold invClimb
  simp only [List.isEmpty]
  rw [h2]
  unfold invClimb
  rw [hg, hv, if_pos rfl]

private theorem specInv_mirror (x g1 g2 g ans : List Nat)
    (h1 : invRung 7 5 20 x x 1 2 false = (g1, 3))
    (h2 : invRung 7 5 20 x g1 3 1 true = (g2, 3))
    (hg : fieldCube 7 5 20 g2 = g)
    (hv : fieldMul 7 5 20 g x = 2 :: List.replicate 6 0)
    (hm : mirrorTrits g = ans) :
    specInv 7 5 20 x = some ans := by
  unfold specInv invGapOf
  rw [show (7 - 1) = 6 by decide, demo_rungs6]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
  unfold invClimb
  simp only [List.isEmpty]
  rw [h1]
  unfold invClimb
  simp only [List.isEmpty]
  rw [h2]
  unfold invClimb
  rw [hg, hv]
  have hne : 2 :: List.replicate 6 0 ≠ whiteHole0 7 := by decide
  rw [if_neg hne, hm, if_pos rfl]

private theorem demo_run_inv :
    specInv 7 5 20 [0, 0, 1, 0, 0, 0, 2] = some [2, 1, 1, 1, 2, 1, 2] :=
  specInv_white [0, 0, 1, 0, 0, 0, 2] [0, 1, 0, 0, 0, 2, 1] [2, 0, 1, 0, 2, 0, 2]
    [2, 1, 1, 1, 2, 1, 2] (by decide) (by decide) (by decide) (by decide)

private theorem demo_chord
    (acc cubed : List Nat × List Nat) (cell : Nat) (y rise run inv slope slope2 x3 y3 : List Nat)
    (hcell : cell = 1 ∨ cell = 2)
    (hc : pointCube 7 5 20 acc = cubed)
    (hy : (if cell = 2 then mirrorTrits [1, 1, 2, 0, 0, 1, 2] else [1, 1, 2, 0, 0, 1, 2]) = y)
    (hrun : fieldSub 7 (basisPeg 7 2) cubed.1 = run)
    (hinv : specInv 7 5 20 run = some inv)
    (hrise : fieldSub 7 y cubed.2 = rise)
    (hslope : fieldMul 7 5 20 rise inv = slope)
    (hs2 : fieldMul 7 5 20 slope slope = slope2)
    (hx : fieldAdd 7 (fieldAdd 7 (fieldAdd 7 slope2 (whiteHole0 7)) cubed.1) (mirrorTrits run) = x3)
    (hy3 : fieldSub 7 (fieldMul 7 5 20 slope (fieldSub 7 cubed.1 x3)) cubed.2 = y3) :
    walkStep 7 5 20 (basisPeg 7 2, [1, 1, 2, 0, 0, 1, 2]) true acc cell =
      some (true, (x3, y3)) := by
  rcases hcell with rfl | rfl
  · have h0 : ¬ (1 = 0) := by decide
    have hbad : ¬ (1 ≠ 1 ∧ 1 ≠ 2) := by decide
    unfold walkStep
    rw [if_neg h0, if_neg hbad, hy, hc]
    simp only [eq_self_iff_true, if_true]
    unfold chordAdd
    rw [hrun]
    dsimp only
    rw [hinv]
    simp only [hrise, hslope, hs2, hx, hy3]
  · have h0 : ¬ (2 = 0) := by decide
    have hbad : ¬ (2 ≠ 1 ∧ 2 ≠ 2) := by decide
    unfold walkStep
    rw [if_neg h0, if_neg hbad, hy, hc]
    simp only [eq_self_iff_true, if_true]
    unfold chordAdd
    rw [hrun]
    dsimp only
    rw [hinv]
    simp only [hrise, hslope, hs2, hx, hy3]

private theorem demo_chord2 :
    walkStep 7 5 20 (basisPeg 7 2, [1, 1, 2, 0, 0, 1, 2]) true
        ([0, 0, 1, 0, 0, 0, 0], [1, 1, 2, 0, 0, 1, 2]) 2 =
      some (true, ([2, 0, 1, 2, 0, 2, 1], [0, 0, 2, 1, 0, 0, 0])) :=
  demo_chord ([0, 0, 1, 0, 0, 0, 0], [1, 1, 2, 0, 0, 1, 2])
    ([0, 0, 0, 0, 0, 0, 1], [2, 0, 2, 0, 0, 0, 0]) 2
    (mirrorTrits [1, 1, 2, 0, 0, 1, 2]) [0, 2, 2, 0, 0, 2, 1] [0, 0, 1, 0, 0, 0, 2]
    [2, 1, 1, 1, 2, 1, 2] [1, 2, 1, 1, 0, 1, 2] [1, 0, 2, 2, 0, 2, 2]
    [2, 0, 1, 2, 0, 2, 1] [0, 0, 2, 1, 0, 0, 0]
    (by decide) (by decide) (by decide) (by decide) demo_run_inv (by decide) (by decide)
    (by decide) (by decide) (by decide)

private theorem demo_inv3 :
    specInv 7 5 20 [0, 0, 1, 2, 0, 1, 0] = some [0, 1, 2, 1, 0, 2, 2] :=
  specInv_white [0, 0, 1, 2, 0, 1, 0] [1, 0, 0, 2, 0, 1, 2] [0, 2, 2, 1, 1, 2, 1]
    [0, 1, 2, 1, 0, 2, 2] (by decide) (by decide) (by decide) (by decide)

private theorem demo_step3 :
    walkStep 7 5 20 (basisPeg 7 2, [1, 1, 2, 0, 0, 1, 2]) true
        ([2, 0, 1, 2, 0, 2, 1], [0, 0, 2, 1, 0, 0, 0]) 1 =
      some (true, ([2, 2, 0, 2, 2, 0, 2], [1, 2, 1, 0, 0, 0, 0])) :=
  demo_chord ([2, 0, 1, 2, 0, 2, 1], [0, 0, 2, 1, 0, 0, 0])
    ([0, 0, 0, 1, 0, 2, 0], [1, 0, 1, 0, 0, 1, 2]) 1
    [1, 1, 2, 0, 0, 1, 2] [0, 1, 1, 0, 0, 0, 0] [0, 0, 1, 2, 0, 1, 0]
    [0, 1, 2, 1, 0, 2, 2] [1, 2, 1, 0, 0, 2, 1] [1, 2, 1, 0, 2, 2, 2]
    [2, 2, 0, 2, 2, 0, 2] [1, 2, 1, 0, 0, 0, 0]
    (by decide) (by decide) (by decide) (by decide) demo_inv3 (by decide) (by decide)
    (by decide) (by decide) (by decide)

private theorem demo_inv4 :
    specInv 7 5 20 [2, 2, 1, 0, 1, 0, 2] = some [2, 0, 0, 2, 1, 2, 2] :=
  specInv_mirror [2, 2, 1, 0, 1, 0, 2] [2, 2, 0, 0, 2, 2, 1] [1, 0, 2, 1, 1, 2, 0]
    [1, 0, 0, 1, 2, 1, 1] [2, 0, 0, 2, 1, 2, 2]
    (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem demo_step4 :
    walkStep 7 5 20 (basisPeg 7 2, [1, 1, 2, 0, 0, 1, 2]) true
        ([2, 2, 0, 2, 2, 0, 2], [1, 2, 1, 0, 0, 0, 0]) 2 =
      some (true, ([0, 2, 1, 2, 0, 1, 1], [2, 0, 0, 2, 2, 1, 2])) :=
  demo_chord ([2, 2, 0, 2, 2, 0, 2], [1, 2, 1, 0, 0, 0, 0])
    ([1, 1, 0, 0, 2, 0, 1], [1, 0, 0, 2, 0, 0, 1]) 2
    (mirrorTrits [1, 1, 2, 0, 0, 1, 2]) [1, 2, 1, 1, 0, 2, 0] [2, 2, 1, 0, 1, 0, 2]
    [2, 0, 0, 2, 1, 2, 2] [2, 1, 1, 2, 0, 1, 0] [0, 0, 2, 2, 2, 1, 2]
    [0, 2, 1, 2, 0, 1, 1] [2, 0, 0, 2, 2, 1, 2]
    (by decide) (by decide) (by decide) (by decide) demo_inv4 (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem demo_cofactor :
    cofactorWalk demo.n demo.k demo.benchlen
        (basisPeg demo.n 2, [1, 1, 2, 0, 0, 1, 2]) =
      some ([0, 2, 1, 2, 0, 1, 1], [2, 0, 0, 2, 2, 1, 2]) := by
  unfold cofactorWalk
  rw [demo_n, demo_k, demo_bench]
  simp only [cofactorCells]
  have h1 : walkStep 7 5 20 (basisPeg 7 2, [1, 1, 2, 0, 0, 1, 2]) false
      (whiteHole0 7, whiteHole0 7) 1 =
      some (true, ([0, 0, 1, 0, 0, 0, 0], [1, 1, 2, 0, 0, 1, 2])) := by decide
  simp only [walkGo, h1]
  simp only [walkGo, demo_chord2]
  simp only [walkGo, demo_step3, demo_step4]

end EcbsLink2.Spec
