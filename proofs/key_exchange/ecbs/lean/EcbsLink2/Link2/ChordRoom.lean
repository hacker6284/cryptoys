/-
  The settle rooms `chord_tail_point` still asks for, discharged from one
  move room, one slide room, and one room each for the marker, the control
  counter, and ops slot 0. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordTailPoint

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Rooms `chord_tail_point` still asks for, once the counters are the naturals
    on the board `invert_checked` returned. -/
structure TailRoom (n k bench script : Nat)
    (moves0 moves hole slides peakS cOps m ctrl : Nat)
    (inv rise accX accY run : List Nat) : Prop where
  fit0 : FitsLen (moves0 + 2 * n)
  bound : m + 2 < script
  bound3 : m + 3 < script
  fitM : FitsLen (m + 1)
  fitC : FitsLen (ctrl + 2)
  fit2 : FitsLen (m + 2)
  fitC4 : FitsLen (ctrl + 4)
  fit3 : FitsLen (m + 3)
  fitC6 : FitsLen (ctrl + 6)
  fit4 : FitsLen (m + 4)
  fops : FitsLen (cOps + 1)
  fops2 : FitsLen (cOps + 2)
  fops3 : FitsLen (cOps + 3)
  fi : FitsLen (2 * (n - 1))
  fm : FitsLen (moves + n * (n + 1))
  fitB : FitsLen bench
  fold : FitsLen (moves + n * (n + 1) + 3 * (bench - n))
  fitClear : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv)
  pegG : FitsLen (2 * pegCount ((gapProduct n k bench inv rise).take n))
  fitSM : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv +
    2 * pegCount ((gapProduct n k bench inv rise).take n))
  fitSS : FitsLen (slides + 2 * pegCount ((gapProduct n k bench inv rise).take n))
  fmS : FitsLen (mvGap moves inv rise n k bench +
    pegCount (fieldMul n k bench rise inv) + n * (n + 1))
  foldS : FitsLen (mvGap moves inv rise n k bench +
    pegCount (fieldMul n k bench rise inv) + n * (n + 1) + 3 * (bench - n))
  fitW : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench)
  fit1 : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench + n)
  fitA : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench +
    pegCount accX + n)
  fitRun : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench +
    pegCount accX + pegCount run + pegCount run)
  pegX : FitsLen (2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run))
  fitMX : FitsLen (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench +
    pegCount accX + pegCount run + pegCount run +
    2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run))
  fitSX : FitsLen (slGap slides inv rise n k bench +
    2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run))
  tailM : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
      pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
    FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) +
      3 * (bench - n) + 5 * n)
  tailS : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let slX := slGap slides inv rise n k bench + 2 * pegCount x3
    FitsLen (slX + 6 * n)
  fitP : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
      pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
    FitsLen (mvX + 2 * n)
  fitMo : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
      pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
    FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n)
  fmP : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
      pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
    FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1))
  foldP : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let mvX := mvSq (mvGap moves inv rise n k bench) slope n k bench +
      pegCount accX + pegCount run + pegCount run + 2 * pegCount x3
    FitsLen (mvX + pegCount x3 + pegCount accY + 2 * n + n * (n + 1) + 3 * (bench - n))
  fitSo : let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let slX := slGap slides inv rise n k bench + 2 * pegCount x3
    FitsLen (slX + 2 * n)

private theorem spend3 {a b c a' b' c' : Nat}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    a + b + c ≤ a' + b' + c' := by
  omega

private theorem fieldAdd_len (n : Nat) (xs ys : List Nat) :
    (fieldAdd n xs ys).length = n := by
  simp [fieldAdd, List.length_map, List.length_range]

private theorem chordX3_len (n k bench : Nat) (slope accX run : List Nat) :
    (chordX3 n k bench slope accX run).length = n := by
  unfold chordX3
  rw [fieldAdd_len]

private theorem school_fold_le (xs ys : List Nat) (n k bench : Nat) :
    foldCharge n (n - k) (school n xs ys (List.replicate bench 0) false) ≤
      3 * (bench - n) := by
  have hlen : (school n xs ys (List.replicate bench 0) false).length = bench := by
    rw [school_length, List.length_replicate]
  have hF := foldCharge_bound n (n - k)
    (school n xs ys (List.replicate bench 0) false)
  rw [hlen] at hF
  exact hF

private theorem mulNo_le (moves : Nat) (xs ys : List Nat) (n k bench : Nat) :
    mulMovesNo moves xs ys n k bench ≤
      moves + n * (n + 1) + 3 * (bench - n) := by
  have hdef : mulMovesNo moves xs ys n k bench =
      moves + schoolMoves xs ys n n +
        foldCharge n (n - k) (school n xs ys (List.replicate bench 0) false) := rfl
  rw [hdef]
  exact Nat.add_le_add (Nat.add_le_add_left (schoolMoves_bound xs ys n) moves)
    (school_fold_le xs ys n k bench)

private theorem mulYes_le (moves : Nat) (xs ys : List Nat) (n k bench : Nat)
    (hpeg : pegCount ys ≤ n) :
    mulMoves moves xs ys n k bench ≤
      moves + n + n * (n + 1) + 3 * (bench - n) := by
  have hdef : mulMoves moves xs ys n k bench =
      moves + pegCount ys + schoolMoves xs ys n n +
        foldCharge n (n - k) (school n xs ys (List.replicate bench 0) false) := rfl
  rw [hdef]
  have hsch := schoolMoves_bound xs ys n
  have hfold := school_fold_le xs ys n k bench
  omega

private theorem le_move (moves0 moves extra n bench : Nat)
    (hmov : moves ≤ moves0 + 2 * n)
    (hextra : 2 * n + extra ≤ tailMoveCap n bench) :
    moves + extra ≤ moves0 + tailMoveCap n bench := by
  omega

private theorem fitsFrom (moves0 moves n bench goal extra : Nat)
    (hBig : FitsLen (moves0 + tailMoveCap n bench))
    (hmov : moves ≤ moves0 + 2 * n)
    (hgoal : goal ≤ moves + extra)
    (hroom : 2 * n + extra ≤ tailMoveCap n bench) :
    FitsLen goal :=
  FitsLen.of_le hBig (Nat.le_trans hgoal (le_move moves0 moves extra n bench hmov hroom))

private theorem fitsSlide (slides n goal extra : Nat)
    (hBig : FitsLen (slides + tailSlideCap n))
    (hgoal : goal ≤ slides + extra)
    (hroom : extra ≤ tailSlideCap n) :
    FitsLen goal :=
  FitsLen.of_le hBig (Nat.le_trans hgoal (Nat.add_le_add_left hroom slides))

/-- Every settle `FitsLen` in `TailRoom`, from one move room, one slide room,
    and one room each for the marker, the control counter, and ops slot 0.
    A length-`n` home has at most `n` pegs. -/
theorem tailRoom_of (n k bench script moves0 moves hole slides peakS cOps m ctrl : Nat)
    (inv rise accX accY run : List Nat)
    (hmov : moves ≤ moves0 + 2 * n)
    (hinv : inv.length = n)
    (hx : accX.length = n) (hy : accY.length = n) (hrun : run.length = n)
    (hnb : n ≤ bench)
    (hBig : FitsLen (moves0 + tailMoveCap n bench))
    (hBigS : FitsLen (slides + tailSlideCap n))
    (hMark : m + 3 < script) (hMarkF : FitsLen (m + 4))
    (hCtrl : FitsLen (ctrl + 6)) (hOps : FitsLen (cOps + 3)) :
    TailRoom n k bench script moves0 moves hole slides peakS cOps m ctrl
      inv rise accX accY run := by
  have hpegI : pegCount inv ≤ n := by rw [← hinv]; exact pegCount_le inv
  have hpegX : pegCount accX ≤ n := by rw [← hx]; exact pegCount_le accX
  have hpegY : pegCount accY ≤ n := by rw [← hy]; exact pegCount_le accY
  have hpegRun : pegCount run ≤ n := by rw [← hrun]; exact pegCount_le run
  have hprod : pegCount ((gapProduct n k bench inv rise).take n) ≤ n :=
    pegCount_take_le (gapProduct n k bench inv rise) n
  have hlenS : (fieldMul n k bench rise inv).length = n :=
    fieldMul_length n k bench rise inv hnb
  have hpegS : pegCount (fieldMul n k bench rise inv) ≤ n := by
    have h := pegCount_le (fieldMul n k bench rise inv)
    rwa [hlenS] at h
  have hlenX3 : (chordX3 n k bench (fieldMul n k bench rise inv) accX run).length = n :=
    chordX3_len n k bench _ accX run
  have hpegX3 : pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) ≤ n := by
    have h := pegCount_le (chordX3 n k bench (fieldMul n k bench rise inv) accX run)
    rwa [hlenX3] at h
  have hno := mulNo_le moves inv rise n k bench
  have hgap : mvGap moves inv rise n k bench ≤
      moves + n * (n + 1) + 3 * (bench - n) + 3 * n := by
    have hdef : mvGap moves inv rise n k bench =
        mulMovesNo moves inv rise n k bench + pegCount inv +
          2 * pegCount ((gapProduct n k bench inv rise).take n) := rfl
    rw [hdef]
    omega
  have hsq : mvSq (mvGap moves inv rise n k bench)
      (fieldMul n k bench rise inv) n k bench ≤
      moves + 2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 4 * n + 1 := by
    have hdef : mvSq (mvGap moves inv rise n k bench)
        (fieldMul n k bench rise inv) n k bench =
        mulMoves (mvGap moves inv rise n k bench)
          (fieldMul n k bench rise inv) (fieldMul n k bench rise inv) n k bench + 1 := rfl
    have hmul := mulYes_le (mvGap moves inv rise n k bench)
      (fieldMul n k bench rise inv) (fieldMul n k bench rise inv) n k bench hpegS
    rw [hdef]
    omega
  let mvX := mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench +
    pegCount accX + pegCount run + pegCount run +
    2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run)
  have hmvX : mvX ≤ moves + 2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 9 * n + 1 := by
    have h := hsq
    omega
  let slX := slGap slides inv rise n k bench +
    2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run)
  have hslX : slX ≤ slides + 4 * n := by
    have hdef : slGap slides inv rise n k bench =
        slides + 2 * pegCount ((gapProduct n k bench inv rise).take n) := rfl
    change slGap slides inv rise n k bench +
      2 * pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) ≤ _
    rw [hdef]
    omega
  have htailM : mvX + pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) +
      pegCount accY + 2 * n + n * (n + 1) + 3 * (bench - n) + 5 * n ≤
      moves0 + tailMoveCap n bench := by
    have h := hmvX
    unfold tailMoveCap at *
    generalize n * (n + 1) = S at *
    generalize bench - n = D at *
    omega
  have htailS : slX + 6 * n ≤ slides + tailSlideCap n := by
    have h := hslX
    unfold tailSlideCap
    omega
  refine
    { fit0 := FitsLen.of_le hBig (
      by
        unfold tailMoveCap
        generalize n * (n + 1) = S
        generalize bench - n = D
        omega)
      bound := by omega
      bound3 := hMark
      fitM := FitsLen.of_le hMarkF (by omega)
      fitC := FitsLen.of_le hCtrl (by omega)
      fit2 := FitsLen.of_le hMarkF (by omega)
      fitC4 := FitsLen.of_le hCtrl (by omega)
      fit3 := FitsLen.of_le hMarkF (by omega)
      fitC6 := hCtrl
      fit4 := hMarkF
      fops := FitsLen.of_le hOps (by omega)
      fops2 := FitsLen.of_le hOps (by omega)
      fops3 := hOps
      fi := FitsLen.of_le hBig (
      by
        unfold tailMoveCap
        generalize n * (n + 1) = S
        generalize bench - n = D
        omega)
      fm := fitsFrom moves0 moves n bench
        (moves + n * (n + 1))
        (n * (n + 1))
        hBig hmov (by omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitB := FitsLen.of_le hBig (
      by
        have hcancel := Nat.sub_add_cancel hnb
        unfold tailMoveCap
        generalize n * (n + 1) = S at *
        generalize bench - n = D at *
        omega)
      fold := fitsFrom moves0 moves n bench
        (moves + n * (n + 1) + 3 * (bench - n))
        (n * (n + 1) + 3 * (bench - n))
        hBig hmov (by omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitClear := fitsFrom moves0 moves n bench
        (mulMovesNo moves inv rise n k bench + pegCount inv)
        (n * (n + 1) + 3 * (bench - n) + n)
        hBig hmov (by have h := Nat.add_le_add hno hpegI; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      pegG := FitsLen.of_le hBig (
      by
        have h := Nat.mul_le_mul_left 2 hprod
        unfold tailMoveCap
        generalize n * (n + 1) = S
        generalize bench - n = D
        omega)
      fitSM := fitsFrom moves0 moves n bench
        (mvGap moves inv rise n k bench)
        (n * (n + 1) + 3 * (bench - n) + 3 * n)
        hBig hmov (by omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitSS := fitsSlide slides n (slides + 2 * pegCount ((gapProduct n k bench inv rise).take n)) (2 * n) hBigS
        (by
          have h := Nat.mul_le_mul_left 2 hprod
          omega)
        (by unfold tailSlideCap; omega)
      fmS := fitsFrom moves0 moves n bench
        (mvGap moves inv rise n k bench + pegCount (fieldMul n k bench rise inv) + n * (n + 1))
        (2 * (n * (n + 1)) + 3 * (bench - n) + 4 * n)
        hBig hmov (by have h := hgap; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      foldS := fitsFrom moves0 moves n bench
        (mvGap moves inv rise n k bench + pegCount (fieldMul n k bench rise inv) + n * (n + 1) + 3 * (bench - n))
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 4 * n)
        hBig hmov (by have h := hgap; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitW := fitsFrom moves0 moves n bench
        (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 4 * n + 1)
        hBig hmov (
        by
          have h := hsq
          omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fit1 := fitsFrom moves0 moves n bench
        (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench + n)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 5 * n + 1)
        hBig hmov (by have h := hsq; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitA := fitsFrom moves0 moves n bench
        (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench + pegCount accX + n)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 6 * n + 1)
        hBig hmov (by have h := hsq; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitRun := fitsFrom moves0 moves n bench
        (mvSq (mvGap moves inv rise n k bench) (fieldMul n k bench rise inv) n k bench + pegCount accX + pegCount run + pegCount run)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 7 * n + 1)
        hBig hmov (by have h := hsq; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      pegX := FitsLen.of_le hBig (
      by
        have h := Nat.mul_le_mul_left 2 hpegX3
        unfold tailMoveCap
        generalize n * (n + 1) = S
        generalize bench - n = D
        omega)
      fitMX := fitsFrom moves0 moves n bench
        mvX
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 9 * n + 1)
        hBig hmov (
        by
          have h := hmvX
          omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitSX := fitsSlide slides n slX (4 * n) hBigS hslX (by unfold tailSlideCap; omega)
      tailM :=
      by
        simpa [mvX] using (FitsLen.of_le hBig htailM)
      tailS :=
      by
        simpa [slX] using (FitsLen.of_le hBigS htailS)
      fitP := fitsFrom moves0 moves n bench
        (mvX + 2 * n)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 11 * n + 1)
        hBig hmov (by have h := hmvX; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitMo := fitsFrom moves0 moves n bench
        (mvX + pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) +
          pegCount accY + 2 * n)
        (2 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 13 * n + 1)
        hBig hmov (by have h := hmvX; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fmP := fitsFrom moves0 moves n bench
        (mvX + pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) +
          pegCount accY + 2 * n + n * (n + 1))
        (3 * (n * (n + 1)) + 2 * (3 * (bench - n)) + 13 * n + 1)
        hBig hmov (by have h := hmvX; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      foldP := fitsFrom moves0 moves n bench
        (mvX + pegCount (chordX3 n k bench (fieldMul n k bench rise inv) accX run) +
          pegCount accY + 2 * n + n * (n + 1) + 3 * (bench - n))
        (3 * (n * (n + 1)) + 3 * (3 * (bench - n)) + 13 * n + 1)
        hBig hmov (by have h := hmvX; omega)
        (by
            unfold tailMoveCap
            generalize n * (n + 1) = S
            generalize bench - n = D
            omega)
      fitSo := by
        simpa [slX] using
          (fitsSlide slides n (slX + 2 * n) (6 * n) hBigS (by
            have h := hslX
            omega) (by unfold tailSlideCap; omega)) }


end EcbsLink2.Link2
