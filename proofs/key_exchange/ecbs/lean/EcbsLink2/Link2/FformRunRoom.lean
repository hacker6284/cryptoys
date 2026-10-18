/-
  The move and slide room `comb_u2z` spends on the run, and the `FitsLen`
  telescope those calls read. One cell's `8 * stepBudget` moves fit in the
  `TierWalk` room while a cell remains. The slide telescope needs twelve
  peg-lengths; each shipped tier has that inside one cell of slide charge.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformSpend
import EcbsLink2.Link2.WalkBound
import EcbsLink2.Link2.FformCell
import EcbsLink2.Link2.FformU2

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem mul_ge (n : Nat) : n ≤ n * (n + 1) := by
  simpa using Nat.mul_le_mul_left n (Nat.le_add_left 1 n)

private theorem budget8 (n d : Nat) :
    12 * n + 2 * (n * (n + 1)) + 6 * d + 2 * n + n + n * (n + 1) +
      3 * d + 2 * n + n * (n + 1) + 3 * d ≤
      8 * (2 * n + n * (n + 1) + 3 * d) := by
  have hquad : n ≤ n * (n + 1) := mul_ge n
  omega

private theorem budget7 (n d : Nat) :
    12 * n + 2 * (n * (n + 1)) + 6 * d + 2 * n + n + n * (n + 1) +
      3 * d ≤
      8 * (2 * n + n * (n + 1) + 3 * d) := by
  omega

private theorem budget6 (n d : Nat) :
    6 * n + n * (n + 1) + 3 * d + n + 2 * n + 3 * n + n * (n + 1) +
      3 * d ≤
      8 * (2 * n + n * (n + 1) + 3 * d) := by
  omega

private theorem budget5 (n d : Nat) :
    6 * n + n * (n + 1) + 3 * d + n + 2 * n + 3 * n + n * (n + 1) ≤
      8 * (2 * n + n * (n + 1) + 3 * d) := by
  omega

private theorem budget4 (n d : Nat) :
    6 * n + n * (n + 1) + 3 * d + n + 2 * n + 3 * n ≤
      8 * (2 * n + n * (n + 1) + 3 * d) := by
  omega

private theorem budget3 (n d : Nat) :
    6 * n + n * (n + 1) + 3 * d + n + 2 * n ≤
      8 * (2 * n + n * (n + 1) + 3 * d) := by
  omega

private theorem budget2 (n d : Nat) :
    6 * n + n * (n + 1) + 3 * d + n ≤
      8 * (2 * n + n * (n + 1) + 3 * d) := by
  omega

private theorem budget1 (n d : Nat) :
    6 * n + n * (n + 1) + 3 * d ≤
      8 * (2 * n + n * (n + 1) + 3 * d) := by
  omega

private theorem budget_two (n d : Nat) :
    2 * n ≤ 8 * (2 * n + n * (n + 1) + 3 * d) := by
  omega

theorem cell_big_room (t : Spec.Tier) (moves done : Nat) (tw : TierWalk t)
    (hmoves : moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hpos : done < t.cells)
    (hstep : 8 * stepBudget t.n t.benchlen ≤
      walkCharge t + (6 * t.benchlen + 2 * t.n)) :
    FitsLen (moves + 8 * stepBudget t.n t.benchlen) := by
  let W := walkCharge t
  let E := 6 * t.benchlen + 2 * t.n
  let B := W + E
  have hle : moves + 8 * stepBudget t.n t.benchlen ≤ (done + 1) * B := by
    have hsum : moves + 8 * stepBudget t.n t.benchlen ≤ done * B + B :=
      Nat.add_le_add hmoves hstep
    rw [← Nat.succ_mul] at hsum
    simpa [Nat.succ_eq_add_one] using hsum
  have hDE : (done + 1) * E ≤ t.cells * E :=
    Nat.mul_le_mul_right E (by omega : done + 1 ≤ t.cells)
  have hEW : t.cells * E ≤ W := by
    rw [Nat.mul_comm]
    simpa [E, W] using tw.moveOver
  have hE1 : (done + 1) * E ≤ W := Nat.le_trans hDE hEW
  have hgap : 1 ≤ t.cells - done := by omega
  have hWgap : W ≤ (t.cells - done) * W := by
    have hmul : 1 * W ≤ (t.cells - done) * W := Nat.mul_le_mul_right W hgap
    simpa using hmul
  have hEg : (done + 1) * E ≤ (t.cells - done) * W := Nat.le_trans hE1 hWgap
  have hcap : (done + 1) * B ≤ (t.cells + 1) * W := by
    have hleft : (done + 1) * B = (done + 1) * W + (done + 1) * E := by
      simp [B, Nat.mul_add]
    have hjoin : (done + 1) * W + (t.cells - done) * W =
        ((done + 1) + (t.cells - done)) * W := by
      rw [← Nat.add_mul]
    have hidx : (done + 1) + (t.cells - done) = t.cells + 1 := by omega
    calc
      (done + 1) * B = (done + 1) * W + (done + 1) * E := hleft
      _ ≤ (done + 1) * W + (t.cells - done) * W := Nat.add_le_add_left hEg _
      _ = ((done + 1) + (t.cells - done)) * W := hjoin
      _ = (t.cells + 1) * W := by rw [hidx]
  exact FitsLen.of_le tw.roomM (Nat.le_trans hle hcap)

theorem demo_big_room (moves done : Nat)
    (hmoves : moves ≤ done * (walkCharge demo + (6 * demo.benchlen + 2 * demo.n)))
    (hpos : done < demo.cells) :
    FitsLen (moves + 8 * stepBudget demo.n demo.benchlen) :=
  cell_big_room demo moves done demo_tier_walk hmoves hpos demo_tail_moves

theorem toy_big_room (moves done : Nat)
    (hmoves : moves ≤ done * (walkCharge toy + (6 * toy.benchlen + 2 * toy.n)))
    (hpos : done < toy.cells) :
    FitsLen (moves + 8 * stepBudget toy.n toy.benchlen) :=
  cell_big_room toy moves done toy_tier_walk hmoves hpos toy_tail_moves

theorem hobby_big_room (moves done : Nat)
    (hmoves : moves ≤ done * (walkCharge hobby + (6 * hobby.benchlen + 2 * hobby.n)))
    (hpos : done < hobby.cells) :
    FitsLen (moves + 8 * stepBudget hobby.n hobby.benchlen) :=
  cell_big_room hobby moves done hobby_tier_walk hmoves hpos hobby_tail_moves

theorem serious_big_room (moves done : Nat)
    (hmoves : moves ≤ done * (walkCharge serious + (6 * serious.benchlen + 2 * serious.n)))
    (hpos : done < serious.cells) :
    FitsLen (moves + 8 * stepBudget serious.n serious.benchlen) :=
  cell_big_room serious moves done serious_tier_walk hmoves hpos serious_tail_moves

private theorem ble_le (a b : Nat) (h : Nat.ble a b = true) : a ≤ b :=
  Nat.le_of_ble_eq_true h

theorem demo_slide12 : 12 * demo.n ≤ cellSlideCharge demo + slideCharge demo.n := by
  have h12 : 12 * demo.n = 84 := rfl
  rw [h12, demo_slideCharge]
  exact ble_le _ _ rfl

theorem toy_slide12 : 12 * toy.n ≤ cellSlideCharge toy + slideCharge toy.n := by
  have h12 : 12 * toy.n = 276 := rfl
  rw [h12, toy_slideCharge]
  exact ble_le _ _ rfl

theorem hobby_slide12 : 12 * hobby.n ≤ cellSlideCharge hobby + slideCharge hobby.n := by
  have h12 : 12 * hobby.n = 708 := rfl
  rw [h12, hobby_slideCharge]
  exact ble_le _ _ rfl

theorem serious_slide12 : 12 * serious.n ≤ cellSlideCharge serious + slideCharge serious.n := by
  have h12 : 12 * serious.n = 2148 := rfl
  rw [h12, serious_slideCharge]
  exact ble_le _ _ rfl

theorem cell_slide_room (t : Spec.Tier) (slides done : Nat) (tw : TierWalk t)
    (hslides : slides ≤ done * (cellSlideCharge t + slideCharge t.n))
    (hpos : done < t.cells)
    (h12 : 12 * t.n ≤ cellSlideCharge t + slideCharge t.n) :
    FitsLen (slides + 12 * t.n) := by
  let S := cellSlideCharge t + slideCharge t.n
  have hle : slides + 12 * t.n ≤ (done + 1) * S := by
    have hsum : slides + 12 * t.n ≤ done * S + S := Nat.add_le_add hslides h12
    rw [← Nat.succ_mul] at hsum
    simpa [Nat.succ_eq_add_one] using hsum
  have h4 : slideCharge t.n * t.cells ≤ cellSlideCharge t := by
    simpa [slideCharge] using tw.slideOver
  let C := cellSlideCharge t
  let F := slideCharge t.n
  have hcap : (done + 1) * S ≤ (t.cells + 1) * C := by
    have hDE : (done + 1) * F ≤ t.cells * F :=
      Nat.mul_le_mul_right F (by omega : done + 1 ≤ t.cells)
    have hEW : t.cells * F ≤ C := by
      rw [Nat.mul_comm]
      simpa [F, C] using h4
    have hE1 : (done + 1) * F ≤ C := Nat.le_trans hDE hEW
    have hgap : 1 ≤ t.cells - done := by omega
    have hWgap : C ≤ (t.cells - done) * C := by
      have hmul : 1 * C ≤ (t.cells - done) * C := Nat.mul_le_mul_right C hgap
      simpa using hmul
    have hEg : (done + 1) * F ≤ (t.cells - done) * C := Nat.le_trans hE1 hWgap
    have hleft : (done + 1) * S = (done + 1) * C + (done + 1) * F := by
      simp [S, Nat.mul_add]
    have hjoin : (done + 1) * C + (t.cells - done) * C =
        ((done + 1) + (t.cells - done)) * C := by
      rw [← Nat.add_mul]
    have hidx : (done + 1) + (t.cells - done) = t.cells + 1 := by omega
    calc
      (done + 1) * S = (done + 1) * C + (done + 1) * F := hleft
      _ ≤ (done + 1) * C + (t.cells - done) * C := Nat.add_le_add_left hEg _
      _ = ((done + 1) + (t.cells - done)) * C := hjoin
      _ = (t.cells + 1) * C := by rw [hidx]
  exact FitsLen.of_le tw.roomS (Nat.le_trans hle hcap)

private theorem peg_n (xs : List Nat) (n : Nat) (h : xs.length = n) : pegCount xs ≤ n := by
  simpa [h] using pegCount_le xs

private theorem peg_take (xs : List Nat) (n : Nat) (hn : n ≤ xs.length) :
    pegCount (xs.take n) ≤ n := by
  have hp := pegCount_le (xs.take n)
  rw [List.length_take, Nat.min_eq_left hn] at hp
  exact hp

private theorem peg_mirror (xs : List Nat) (n : Nat) (h : xs.length = n) :
    pegCount (mirrorTrits xs) ≤ n := by
  have hp := pegCount_le (mirrorTrits xs)
  rw [mirrorTrits, List.length_map, h] at hp
  exact hp

theorem run_moves_le (moves n k bench : Nat) (x x2 z lane : List Nat)
    (hx : x.length = n) (hz : z.length = n) (hnb : n ≤ bench) (hnle : n ≤ lane.length) :
    fformRunMoves moves n k bench x x2 z lane ≤
      moves + 6 * n + n * (n + 1) + 3 * (bench - n) := by
  unfold fformRunMoves
  have hpx := peg_n x n hx
  have hpl := peg_take lane n hnle
  have hpm := peg_mirror x n hx
  have hpz := peg_n z n hz
  have hsch : schoolMoves x2 z n n ≤ n * (n + 1) := schoolMoves_bound x2 z n
  have hpref : (pref (mirrorTrits x) bench n).length = bench :=
    pref_length hnb (by rw [mirrorTrits, List.length_map, hx]; exact Nat.le_refl _)
  have hstrip : (school n x2 z (pref (mirrorTrits x) bench n) false).length = bench := by
    rw [school_length, hpref]
  have hfold : foldCharge n (n - k)
      (school n x2 z (pref (mirrorTrits x) bench n) false) ≤ 3 * (bench - n) := by
    have h := foldCharge_bound n (n - k)
      (school n x2 z (pref (mirrorTrits x) bench n) false)
    rw [hstrip] at h
    exact h
  omega

theorem run_in_budget (moves n k bench : Nat) (x x2 z lane : List Nat)
    (hx : x.length = n) (hz : z.length = n) (hnb : n ≤ bench) (hnle : n ≤ lane.length) :
    fformRunMoves moves n k bench x x2 z lane ≤ moves + 8 * stepBudget n bench := by
  have h := run_moves_le moves n k bench x x2 z lane hx hz hnb hnle
  have hstep : 6 * n + n * (n + 1) + 3 * (bench - n) ≤ 8 * stepBudget n bench := by
    unfold stepBudget
    exact budget1 n (bench - n)
  omega

private theorem room_le {a b : Nat} (h : FitsLen b) (hle : a ≤ b) : FitsLen a :=
  FitsLen.of_le h hle

private theorem run_lane_len (n k bench : Nat) (x x2 z : List Nat)
    (hx : x.length = n) (hnb : n ≤ bench) :
    (fformRunLane n k bench x x2 z).length = bench := by
  unfold fformRunLane
  have hpref : (pref (mirrorTrits x) bench n).length = bench :=
    pref_length hnb (by rw [mirrorTrits, List.length_map, hx]; exact Nat.le_refl _)
  have hschool : (school n x2 z (pref (mirrorTrits x) bench n) false).length = bench := by
    rw [school_length, hpref]
  rw [laneFold_length n (n - k) _ (by rw [hschool]; exact hnb), hschool]

private theorem rise_le (moves n k bench : Nat) (x x2 y y2 z lane : List Nat) (red : Bool)
    (hx : x.length = n) (hy : y.length = n) (hz : z.length = n)
    (hnb : n ≤ bench) (hnle : n ≤ lane.length) :
    riseMoveCount y y2 z (fformRunLane n k bench x x2 z) red n k bench
        (fformRunMoves moves n k bench x x2 z lane) ≤
      moves + 12 * n + 2 * (n * (n + 1)) + 6 * (bench - n) := by
  have hrun := run_moves_le moves n k bench x x2 z lane hx hz hnb hnle
  have hlen := run_lane_len n k bench x x2 z hx hnb
  unfold riseMoveCount
  have hpy := peg_n y n hy
  have hpl := peg_take (fformRunLane n k bench x x2 z) n (by rw [hlen]; exact hnb)
  have hpm := peg_mirror y n hy
  have hpz := peg_n z n hz
  have hsch : schoolMoves y2 z n n ≤ n * (n + 1) := schoolMoves_bound y2 z n
  have hpref : (pref (mirrorTrits y) bench n).length = bench :=
    pref_length hnb (by rw [mirrorTrits, List.length_map, hy]; exact Nat.le_refl _)
  have hstrip : (school n y2 z (pref (mirrorTrits y) bench n) red).length = bench := by
    rw [school_length, hpref]
  have hfold : foldCharge n (n - k)
      (school n y2 z (pref (mirrorTrits y) bench n) red) ≤ 3 * (bench - n) := by
    have h := foldCharge_bound n (n - k)
      (school n y2 z (pref (mirrorTrits y) bench n) red)
    rw [hstrip] at h
    exact h
  omega

/-- The `FitsLen` facts `comb_u2z` reads after the run. Moves stay inside
    `moves + 8 * stepBudget`. Slides stay inside `slides + 12 * n`. -/
theorem run_fit (moves slides n k bench : Nat) (x x2 y y2 z lane : List Nat) (red : Bool)
    (hx : x.length = n) (hy : y.length = n) (hz : z.length = n)
    (hnb : n ≤ bench) (hnle : n ≤ lane.length)
    (hBig : FitsLen (moves + 8 * stepBudget n bench))
    (hSlide : FitsLen (slides + 12 * n)) :
    FitsLen (fformRunMoves moves n k bench x x2 z lane + n) ∧
    FitsLen (2 * pegCount ((fformRunLane n k bench x x2 z).take n)) ∧
    FitsLen ((fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n)) ∧
    FitsLen (fformRunSlides slides n x lane +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n)) ∧
    FitsLen ((fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n) ∧
    FitsLen (fformRunSlides slides n x lane +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 2 * n) ∧
    FitsLen ((fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n + n * (n + 1)) ∧
    FitsLen ((fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n + n * (n + 1) +
      3 * (bench - n)) ∧
    FitsLen (riseMoveCount y y2 z (fformRunLane n k bench x x2 z) red n k bench
        (fformRunMoves moves n k bench x x2 z lane) +
        2 * n + n + n * (n + 1) + 3 * (bench - n)) ∧
    FitsLen (riseSlideCount y (fformRunLane n k bench x x2 z) n
        (fformRunSlides slides n x lane) + 2 * n) ∧
    FitsLen ((riseMoveCount y y2 z (fformRunLane n k bench x x2 z) red n k bench
        (fformRunMoves moves n k bench x x2 z lane) +
        2 * n + n + n * (n + 1) + 3 * (bench - n)) +
        2 * n + n * (n + 1) + 3 * (bench - n)) ∧
    FitsLen (riseSlideCount y (fformRunLane n k bench x x2 z) n
        (fformRunSlides slides n x lane) + 2 * n + 2 * n) := by
  have hrun := run_moves_le moves n k bench x x2 z lane hx hz hnb hnle
  have hrise := rise_le moves n k bench x x2 y y2 z lane red hx hy hz hnb hnle
  have hlen := run_lane_len n k bench x x2 z hx hnb
  have hpl := peg_take (fformRunLane n k bench x x2 z) n (by rw [hlen]; exact hnb)
  have hpy := peg_n y n hy
  have hpx := peg_n x n hx
  have hpm := peg_mirror x n hx
  have hpmY := peg_mirror y n hy
  have hplt := peg_take lane n hnle
  have hslR : fformRunSlides slides n x lane ≤ slides + 4 * n := by
    unfold fformRunSlides
    omega
  have hslRise : riseSlideCount y (fformRunLane n k bench x x2 z) n
      (fformRunSlides slides n x lane) ≤ slides + 8 * n := by
    unfold riseSlideCount
    omega
  have h8 : 6 * n + n * (n + 1) + 3 * (bench - n) + n ≤ 8 * stepBudget n bench := by
    unfold stepBudget; exact budget2 n (bench - n)
  have h8b : 6 * n + n * (n + 1) + 3 * (bench - n) + n + 2 * n ≤ 8 * stepBudget n bench := by
    unfold stepBudget; exact budget3 n (bench - n)
  have h8c : 6 * n + n * (n + 1) + 3 * (bench - n) + n + 2 * n + 3 * n ≤
      8 * stepBudget n bench := by
    unfold stepBudget; exact budget4 n (bench - n)
  have h8d : 6 * n + n * (n + 1) + 3 * (bench - n) + n + 2 * n + 3 * n + n * (n + 1) ≤
      8 * stepBudget n bench := by
    unfold stepBudget; exact budget5 n (bench - n)
  have h8e : 6 * n + n * (n + 1) + 3 * (bench - n) + n + 2 * n + 3 * n + n * (n + 1) +
      3 * (bench - n) ≤ 8 * stepBudget n bench := by
    unfold stepBudget; exact budget6 n (bench - n)
  have h8f : 12 * n + 2 * (n * (n + 1)) + 6 * (bench - n) + 2 * n + n + n * (n + 1) +
      3 * (bench - n) ≤ 8 * stepBudget n bench := by
    unfold stepBudget; exact budget7 n (bench - n)
  have h8g : 12 * n + 2 * (n * (n + 1)) + 6 * (bench - n) + 2 * n + n + n * (n + 1) +
      3 * (bench - n) + 2 * n + n * (n + 1) + 3 * (bench - n) ≤ 8 * stepBudget n bench := by
    unfold stepBudget; exact budget8 n (bench - n)
  have h2peg : 2 * pegCount ((fformRunLane n k bench x x2 z).take n) ≤
      moves + 8 * stepBudget n bench := by
    have h2 : 2 * pegCount ((fformRunLane n k bench x x2 z).take n) ≤ 2 * n := by omega
    have h2b : 2 * n ≤ 8 * stepBudget n bench := by
      unfold stepBudget; exact budget_two n (bench - n)
    exact Nat.le_trans (Nat.le_trans h2 h2b) (Nat.le_add_left _ moves)
  have hRunN : fformRunMoves moves n k bench x x2 z lane + n ≤
      moves + 8 * stepBudget n bench := by
    have h1 : fformRunMoves moves n k bench x x2 z lane + n ≤
        moves + (6 * n + n * (n + 1) + 3 * (bench - n) + n) := by omega
    exact Nat.le_trans h1 (Nat.add_le_add_left h8 moves)
  have hRunP : (fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) ≤
      moves + 8 * stepBudget n bench := by
    have h1 : (fformRunMoves moves n k bench x x2 z lane + pegCount y) +
        2 * pegCount ((fformRunLane n k bench x x2 z).take n) ≤
        moves + (6 * n + n * (n + 1) + 3 * (bench - n) + n + 2 * n) := by omega
    exact Nat.le_trans h1 (Nat.add_le_add_left h8b moves)
  have hRun3 : (fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n ≤
      moves + 8 * stepBudget n bench := by
    have h1 : (fformRunMoves moves n k bench x x2 z lane + pegCount y) +
        2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n ≤
        moves + (6 * n + n * (n + 1) + 3 * (bench - n) + n + 2 * n + 3 * n) := by omega
    exact Nat.le_trans h1 (Nat.add_le_add_left h8c moves)
  have hRunQ : (fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n + n * (n + 1) ≤
      moves + 8 * stepBudget n bench := by
    have h1 : (fformRunMoves moves n k bench x x2 z lane + pegCount y) +
        2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n + n * (n + 1) ≤
        moves + (6 * n + n * (n + 1) + 3 * (bench - n) + n + 2 * n + 3 * n + n * (n + 1)) := by
      omega
    exact Nat.le_trans h1 (Nat.add_le_add_left h8d moves)
  have hRunF : (fformRunMoves moves n k bench x x2 z lane + pegCount y) +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n + n * (n + 1) +
      3 * (bench - n) ≤ moves + 8 * stepBudget n bench := by
    have h1 : (fformRunMoves moves n k bench x x2 z lane + pegCount y) +
        2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 3 * n + n * (n + 1) +
        3 * (bench - n) ≤ moves + (6 * n + n * (n + 1) + 3 * (bench - n) + n + 2 * n +
        3 * n + n * (n + 1) + 3 * (bench - n)) := by omega
    exact Nat.le_trans h1 (Nat.add_le_add_left h8e moves)
  have hSq : riseMoveCount y y2 z (fformRunLane n k bench x x2 z) red n k bench
        (fformRunMoves moves n k bench x x2 z lane) +
        2 * n + n + n * (n + 1) + 3 * (bench - n) ≤
      moves + 8 * stepBudget n bench := by
    have h1 : riseMoveCount y y2 z (fformRunLane n k bench x x2 z) red n k bench
          (fformRunMoves moves n k bench x x2 z lane) +
          2 * n + n + n * (n + 1) + 3 * (bench - n) ≤
        moves + (12 * n + 2 * (n * (n + 1)) + 6 * (bench - n) + 2 * n + n +
          n * (n + 1) + 3 * (bench - n)) := by omega
    exact Nat.le_trans h1 (Nat.add_le_add_left h8f moves)
  have hNext : (riseMoveCount y y2 z (fformRunLane n k bench x x2 z) red n k bench
        (fformRunMoves moves n k bench x x2 z lane) +
        2 * n + n + n * (n + 1) + 3 * (bench - n)) +
        2 * n + n * (n + 1) + 3 * (bench - n) ≤
      moves + 8 * stepBudget n bench := by
    have h1 : (riseMoveCount y y2 z (fformRunLane n k bench x x2 z) red n k bench
          (fformRunMoves moves n k bench x x2 z lane) +
          2 * n + n + n * (n + 1) + 3 * (bench - n)) +
          2 * n + n * (n + 1) + 3 * (bench - n) ≤
        moves + (12 * n + 2 * (n * (n + 1)) + 6 * (bench - n) + 2 * n + n +
          n * (n + 1) + 3 * (bench - n) + 2 * n + n * (n + 1) + 3 * (bench - n)) := by
      omega
    exact Nat.le_trans h1 (Nat.add_le_add_left h8g moves)
  have hSl1 : fformRunSlides slides n x lane +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) ≤ slides + 12 * n := by
    omega
  have hSl2 : fformRunSlides slides n x lane +
      2 * pegCount ((fformRunLane n k bench x x2 z).take n) + 2 * n ≤ slides + 12 * n := by
    omega
  have hSl3 : riseSlideCount y (fformRunLane n k bench x x2 z) n
      (fformRunSlides slides n x lane) + 2 * n ≤ slides + 12 * n := by omega
  have hSl4 : riseSlideCount y (fformRunLane n k bench x x2 z) n
      (fformRunSlides slides n x lane) + 2 * n + 2 * n ≤ slides + 12 * n := by omega
  refine ⟨room_le hBig hRunN, room_le hBig h2peg, room_le hBig hRunP, room_le hSlide hSl1,
    room_le hBig hRun3, room_le hSlide hSl2, room_le hBig hRunQ, room_le hBig hRunF,
    room_le hBig hSq, room_le hSlide hSl3, room_le hBig hNext, room_le hSlide hSl4⟩

end EcbsLink2.Link2
