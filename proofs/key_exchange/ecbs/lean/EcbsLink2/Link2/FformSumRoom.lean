/-
  The rooms `v2_on_comb` spends after the comb. One cube, then
  `u²Z` inside `8 * stepBudget`, then sixteen more step-budgets for the
  square and the sum. Toy, Hobby, and Serious keep that inside one cell of
  `TierWalk` room. Slides ask for twenty-eight peg-lengths past the comb,
  and control asks for forty past the comb, which is forty-six past the
  cell that opened it.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformRunRoom
import EcbsLink2.Link2.FrobeniusRead
import EcbsLink2.Link2.Cube

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem ble_le (a b : Nat) (h : Nat.ble a b = true) : a ≤ b :=
  Nat.le_of_ble_eq_true h

private theorem span_fit (cells done counter extra roomUnit step : Nat)
    (hroom : FitsLen ((cells + 1) * roomUnit))
    (hover : step * cells ≤ roomUnit)
    (hledger : counter ≤ done * (roomUnit + step))
    (hpos : done < cells)
    (hextra : extra ≤ roomUnit + step) :
    FitsLen (counter + extra) := by
  let W := roomUnit
  let E := step
  let B := W + E
  have hle : counter + extra ≤ (done + 1) * B := by
    have hsum : counter + extra ≤ done * B + B := Nat.add_le_add hledger hextra
    rw [← Nat.succ_mul] at hsum
    simpa [Nat.succ_eq_add_one] using hsum
  have hDE : (done + 1) * E ≤ cells * E :=
    Nat.mul_le_mul_right E (by omega : done + 1 ≤ cells)
  have hEW : cells * E ≤ W := by
    rw [Nat.mul_comm]
    simpa [E, W] using hover
  have hE1 : (done + 1) * E ≤ W := Nat.le_trans hDE hEW
  have hgap : 1 ≤ cells - done := by omega
  have hWgap : W ≤ (cells - done) * W := by
    have hmul : 1 * W ≤ (cells - done) * W := Nat.mul_le_mul_right W hgap
    simpa using hmul
  have hEg : (done + 1) * E ≤ (cells - done) * W := Nat.le_trans hE1 hWgap
  have hcap : (done + 1) * B ≤ (cells + 1) * W := by
    have hleft : (done + 1) * B = (done + 1) * W + (done + 1) * E := by
      simp [B, Nat.mul_add]
    have hjoin : (done + 1) * W + (cells - done) * W =
        ((done + 1) + (cells - done)) * W := by
      rw [← Nat.add_mul]
    have hidx : (done + 1) + (cells - done) = cells + 1 := by omega
    calc
      (done + 1) * B = (done + 1) * W + (done + 1) * E := hleft
      _ ≤ (done + 1) * W + (cells - done) * W := Nat.add_le_add_left hEg _
      _ = ((done + 1) + (cells - done)) * W := hjoin
      _ = (cells + 1) * W := by rw [hidx]
  exact FitsLen.of_le hroom (Nat.le_trans hle hcap)

private theorem mul_ge (n : Nat) : n ≤ n * (n + 1) := by
  simpa using Nat.mul_le_mul_left n (Nat.le_add_left 1 n)

private theorem budget8 (n d : Nat) :
    12 * n + 2 * (n * (n + 1)) + 6 * d + 2 * n + n + n * (n + 1) +
      3 * d + 2 * n + n * (n + 1) + 3 * d ≤
      8 * (2 * n + n * (n + 1) + 3 * d) := by
  have hquad : n ≤ n * (n + 1) := mul_ge n
  omega

private theorem cap_sum (moves n d rise s1 s2 : Nat)
    (hr : rise ≤ moves + 12 * n + 2 * (n * (n + 1)) + 6 * d)
    (hs1 : s1 ≤ n * (n + 1)) (hs2 : s2 ≤ n * (n + 1)) :
    (rise + 2 * n + n + s1 + 3 * d) + 2 * n + s2 + 3 * d ≤
      moves + (12 * n + 2 * (n * (n + 1)) + 6 * d + 2 * n + n + (n * (n + 1)) +
        3 * d + 2 * n + (n * (n + 1)) + 3 * d) := by
  omega

/-- `u²Z` stays inside `moves + 8 * stepBudget`. -/
theorem u2z_cap_le (moves n k bench : Nat) (x x2 y y2 z lane : List Nat) (red : Bool)
    (hx : x.length = n) (hy : y.length = n) (hz : z.length = n)
    (hnb : n ≤ bench) (hnle : n ≤ lane.length) :
    u2zMoveCap y y2 z (fformRunLane n k bench x x2 z) red n k bench
        (fformRunMoves moves n k bench x x2 z lane) ≤
      moves + 8 * stepBudget n bench := by
  have hrise := rise_le moves n k bench x x2 y y2 z lane red hx hy hz hnb hnle
  have hsum := cap_sum moves n (bench - n)
      (riseMoveCount y y2 z (fformRunLane n k bench x x2 z) red n k bench
        (fformRunMoves moves n k bench x x2 z lane))
      (n * (n + 1)) (n * (n + 1)) hrise (Nat.le_refl _) (Nat.le_refl _)
  have h8 : 12 * n + 2 * (n * (n + 1)) + 6 * (bench - n) + 2 * n + n + n * (n + 1) +
      3 * (bench - n) + 2 * n + n * (n + 1) + 3 * (bench - n) ≤
      8 * stepBudget n bench := by
    unfold stepBudget
    exact budget8 n (bench - n)
  have hle := Nat.le_trans hsum (Nat.add_le_add_left h8 moves)
  simpa [u2zMoveCap] using hle

private theorem four_pegs (slides n a b : Nat) (ha : a ≤ n) (hb : b ≤ n) :
    slides + 2 * a + 2 * b ≤ slides + 4 * n := by
  omega

private theorem run_slides_le (slides n : Nat) (x lane : List Nat)
    (hx : x.length = n) (hnle : n ≤ lane.length) :
    fformRunSlides slides n x lane ≤ slides + 4 * n := by
  unfold fformRunSlides
  have htake : pegCount (lane.take n) ≤ n := by
    have hp := pegCount_le (lane.take n)
    rw [List.length_take, Nat.min_eq_left hnle] at hp
    exact hp
  have hmir : pegCount (mirrorTrits x) ≤ n := by
    have hp := pegCount_le (mirrorTrits x)
    rw [mirrorTrits, List.length_map, hx] at hp
    exact hp
  exact four_pegs slides n _ _ htake hmir

private theorem lane_len (n k bench : Nat) (x x2 z : List Nat)
    (hx : x.length = n) (hnb : n ≤ bench) :
    (fformRunLane n k bench x x2 z).length = bench := by
  unfold fformRunLane
  have hpref : (pref (mirrorTrits x) bench n).length = bench :=
    pref_length hnb (by rw [mirrorTrits, List.length_map, hx]; exact Nat.le_refl _)
  have hschool : (school n x2 z (pref (mirrorTrits x) bench n) false).length = bench := by
    rw [school_length, hpref]
  rw [laneFold_length n (n - k) _ (by rw [hschool]; exact hnb), hschool]

private theorem slide_out (slides n base a b : Nat)
    (hbase : base ≤ slides + 4 * n) (ha : a ≤ n) (hb : b ≤ n) :
    (base + 2 * a + 2 * b) + 2 * n + 2 * n ≤ slides + 12 * n := by
  omega

/-- The slide counter `u²Z` leaves is at most twelve peg-lengths past the comb. -/
theorem u2z_slide_le (slides n k bench : Nat) (x x2 y z lane : List Nat)
    (hx : x.length = n) (hy : y.length = n) (hnb : n ≤ bench) (hnle : n ≤ lane.length) :
    u2zSlideCap y (fformRunLane n k bench x x2 z) n
        (fformRunSlides slides n x lane) ≤
      slides + 12 * n := by
  have hrun := run_slides_le slides n x lane hx hnle
  have hlen := lane_len n k bench x x2 z hx hnb
  have ha : pegCount ((fformRunLane n k bench x x2 z).take n) ≤ n := by
    have hp := pegCount_le ((fformRunLane n k bench x x2 z).take n)
    rw [List.length_take, Nat.min_eq_left (by rw [hlen]; exact hnb)] at hp
    exact hp
  have hb : pegCount (mirrorTrits y) ≤ n := by
    have hp := pegCount_le (mirrorTrits y)
    rw [mirrorTrits, List.length_map, hy] at hp
    exact hp
  have h := slide_out slides n (fformRunSlides slides n x lane) _ _ hrun ha hb
  simpa [u2zSlideCap, riseSlideCount] using h

private theorem cube_add (moves cap head n d out : Nat)
    (hhead : head ≤ moves + cap) (hout : out ≤ head + 2 * n + 3 * d) :
    out ≤ moves + cap + 2 * n + 3 * d := by
  omega

/-- The comb's move counter is one bottom cube past the up settle. -/
theorem comb_moves_le
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    cubeMoves (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)) z n k bench ≤
      moves + cubeCharge n bench + 2 * n + 3 * (bench - n) :=
  cube_add moves (cubeCharge n bench)
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)) n (bench - n) _
    (up_out_le a).2.1
    (cubeMoves_le (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)) z n k bench)

/-- The comb's slide counter is the up settle. -/
theorem comb_slides_le
    {b : Ecbs.Board} {x y : List Nat}
    {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    upSl a + 2 * pegCount ((upLane n k bench y).take n) ≤ slides + 4 * n := by
  simpa [slideCharge] using (up_out_le a).2.2

theorem toy_sum_move :
    cubeCharge toy.n toy.benchlen + 2 * toy.n + 3 * (toy.benchlen - toy.n) +
      24 * stepBudget toy.n toy.benchlen ≤
      walkCharge toy + (6 * toy.benchlen + 2 * toy.n) := by
  have hL : cubeCharge toy.n toy.benchlen + 2 * toy.n + 3 * (toy.benchlen - toy.n) +
      24 * stepBudget toy.n toy.benchlen = 18551 := by
    simp [cubeCharge, stepBudget, toy]
  have hR : 6 * toy.benchlen + 2 * toy.n = 478 := by simp [toy]
  rw [hL, hR, toy_walk]
  exact ble_le _ _ rfl

theorem hobby_sum_move :
    cubeCharge hobby.n hobby.benchlen + 2 * hobby.n + 3 * (hobby.benchlen - hobby.n) +
      24 * stepBudget hobby.n hobby.benchlen ≤
      walkCharge hobby + (6 * hobby.benchlen + 2 * hobby.n) := by
  have hL : cubeCharge hobby.n hobby.benchlen + 2 * hobby.n +
      3 * (hobby.benchlen - hobby.n) + 24 * stepBudget hobby.n hobby.benchlen = 98183 := by
    simp [cubeCharge, stepBudget, hobby]
  have hR : 6 * hobby.benchlen + 2 * hobby.n = 1198 := by simp [hobby]
  rw [hL, hR, hobby_walk]
  exact ble_le _ _ rfl

theorem serious_sum_move :
    cubeCharge serious.n serious.benchlen + 2 * serious.n +
      3 * (serious.benchlen - serious.n) + 24 * stepBudget serious.n serious.benchlen ≤
      walkCharge serious + (6 * serious.benchlen + 2 * serious.n) := by
  have hL : cubeCharge serious.n serious.benchlen + 2 * serious.n +
      3 * (serious.benchlen - serious.n) +
      24 * stepBudget serious.n serious.benchlen = 812903 := by
    simp [cubeCharge, stepBudget, serious]
  have hR : 6 * serious.benchlen + 2 * serious.n = 3598 := by simp [serious]
  rw [hL, hR, serious_walk]
  exact ble_le _ _ rfl

theorem demo_sum_slide : 32 * demo.n ≤ cellSlideCharge demo + slideCharge demo.n := by
  have h : 32 * demo.n = 224 := by simp [demo]
  rw [h, demo_slideCharge]
  exact ble_le _ _ rfl

theorem toy_sum_slide : 32 * toy.n ≤ cellSlideCharge toy + slideCharge toy.n := by
  have h : 32 * toy.n = 736 := by simp [toy]
  rw [h, toy_slideCharge]
  exact ble_le _ _ rfl

theorem hobby_sum_slide : 32 * hobby.n ≤ cellSlideCharge hobby + slideCharge hobby.n := by
  have h : 32 * hobby.n = 1888 := by simp [hobby]
  rw [h, hobby_slideCharge]
  exact ble_le _ _ rfl

theorem serious_sum_slide :
    32 * serious.n ≤ cellSlideCharge serious + slideCharge serious.n := by
  have h : 32 * serious.n = 5728 := by simp [serious]
  rw [h, serious_slideCharge]
  exact ble_le _ _ rfl

theorem demo_sum_ctrl : 46 ≤ cellCtrlCharge demo + 4 := by
  rw [demo_ctrlCharge]
  exact ble_le _ _ rfl

theorem toy_sum_ctrl : 46 ≤ cellCtrlCharge toy + 4 := by
  rw [toy_ctrlCharge]
  exact ble_le _ _ rfl

theorem hobby_sum_ctrl : 46 ≤ cellCtrlCharge hobby + 4 := by
  rw [hobby_ctrlCharge]
  exact ble_le _ _ rfl

theorem serious_sum_ctrl : 46 ≤ cellCtrlCharge serious + 4 := by
  rw [serious_ctrlCharge]
  exact ble_le _ _ rfl

private theorem add_cap (spend moves a b c s : Nat) (h : spend ≤ moves + a + b + c) :
    spend + s ≤ moves + (a + b + c + s) := by
  omega

theorem comb_move_fit (t : Spec.Tier) (moves done comb : Nat) (tw : TierWalk t)
    (hmoves : moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hpos : done < t.cells)
    (hcomb : comb ≤ moves + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n))
    (hwide : cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) +
        24 * stepBudget t.n t.benchlen ≤
        walkCharge t + (6 * t.benchlen + 2 * t.n)) :
    FitsLen (comb + 24 * stepBudget t.n t.benchlen) := by
  have hle := add_cap comb moves (cubeCharge t.n t.benchlen) (2 * t.n)
      (3 * (t.benchlen - t.n)) (24 * stepBudget t.n t.benchlen) hcomb
  exact FitsLen.of_le
      (span_fit t.cells done moves
        (cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) +
          24 * stepBudget t.n t.benchlen)
        (walkCharge t) (6 * t.benchlen + 2 * t.n) tw.roomM
        (by simpa using tw.moveOver) hmoves hpos hwide)
      hle

private theorem slide_add (comb slides n : Nat) (h : comb ≤ slides + 4 * n) :
    comb + 28 * n ≤ slides + 32 * n := by
  omega

theorem comb_slide_fit (t : Spec.Tier) (slides done comb : Nat) (tw : TierWalk t)
    (hslides : slides ≤ done * (cellSlideCharge t + slideCharge t.n))
    (hpos : done < t.cells)
    (hcomb : comb ≤ slides + 4 * t.n)
    (h32 : 32 * t.n ≤ cellSlideCharge t + slideCharge t.n) :
    FitsLen (comb + 28 * t.n) := by
  have hle := slide_add comb slides t.n hcomb
  exact FitsLen.of_le
      (span_fit t.cells done slides (32 * t.n) (cellSlideCharge t) (slideCharge t.n)
        tw.roomS (by simpa [slideCharge] using tw.slideOver) hslides hpos h32)
      hle

private theorem ctrl_eq (ctrl comb : Nat) (h : comb = ctrl + 6) : comb + 40 = ctrl + 46 := by
  omega

theorem comb_ctrl_fit (t : Spec.Tier) (ctrl done comb : Nat) (tw : TierWalk t)
    (hctrl : ctrl ≤ done * (cellCtrlCharge t + 4))
    (hpos : done < t.cells)
    (hcomb : comb = ctrl + 6)
    (h46 : 46 ≤ cellCtrlCharge t + 4) :
    FitsLen (comb + 40) := by
  have hle : comb + 40 ≤ ctrl + 46 := by
    rw [ctrl_eq ctrl comb hcomb]
    exact Nat.le_refl _
  exact FitsLen.of_le
      (span_fit t.cells done ctrl 46 (cellCtrlCharge t) 4 tw.roomC tw.ctrlOver
        hctrl hpos h46)
      hle

theorem toy_comb_move (moves done comb : Nat)
    (hmoves : moves ≤ done * (walkCharge toy + (6 * toy.benchlen + 2 * toy.n)))
    (hpos : done < toy.cells)
    (hcomb : comb ≤ moves + cubeCharge toy.n toy.benchlen + 2 * toy.n +
        3 * (toy.benchlen - toy.n)) :
    FitsLen (comb + 24 * stepBudget toy.n toy.benchlen) :=
  comb_move_fit toy moves done comb toy_tier_walk hmoves hpos hcomb toy_sum_move

theorem hobby_comb_move (moves done comb : Nat)
    (hmoves : moves ≤ done * (walkCharge hobby + (6 * hobby.benchlen + 2 * hobby.n)))
    (hpos : done < hobby.cells)
    (hcomb : comb ≤ moves + cubeCharge hobby.n hobby.benchlen + 2 * hobby.n +
        3 * (hobby.benchlen - hobby.n)) :
    FitsLen (comb + 24 * stepBudget hobby.n hobby.benchlen) :=
  comb_move_fit hobby moves done comb hobby_tier_walk hmoves hpos hcomb hobby_sum_move

theorem serious_comb_move (moves done comb : Nat)
    (hmoves : moves ≤ done * (walkCharge serious + (6 * serious.benchlen + 2 * serious.n)))
    (hpos : done < serious.cells)
    (hcomb : comb ≤ moves + cubeCharge serious.n serious.benchlen + 2 * serious.n +
        3 * (serious.benchlen - serious.n)) :
    FitsLen (comb + 24 * stepBudget serious.n serious.benchlen) :=
  comb_move_fit serious moves done comb serious_tier_walk hmoves hpos hcomb serious_sum_move

private theorem wide_step (cap moves s : Nat) (h : cap ≤ moves + 8 * s) :
    cap + 16 * s ≤ moves + 24 * s := by
  omega

private theorem wide_slide (cap slides n : Nat) (h : cap ≤ slides + 12 * n) :
    cap + 16 * n ≤ slides + 28 * n := by
  omega

/-- `v2_on_comb`'s move room, from the comb counter and one cell of walk room. -/
theorem v2_move_room (moves n k bench : Nat) (x x2 y y2 z lane : List Nat) (red : Bool)
    (hx : x.length = n) (hy : y.length = n) (hz : z.length = n)
    (hnb : n ≤ bench) (hnle : n ≤ lane.length)
    (h24 : FitsLen (moves + 24 * stepBudget n bench)) :
    FitsLen (u2zMoveCap y y2 z (fformRunLane n k bench x x2 z) red n k bench
        (fformRunMoves moves n k bench x x2 z lane) + 16 * stepBudget n bench) := by
  have hcap := u2z_cap_le moves n k bench x x2 y y2 z lane red hx hy hz hnb hnle
  exact FitsLen.of_le h24 (wide_step _ _ (stepBudget n bench) hcap)

/-- `v2_on_comb`'s slide room. -/
theorem v2_slide_room (slides n k bench : Nat) (x x2 y z lane : List Nat)
    (hx : x.length = n) (hy : y.length = n) (hnb : n ≤ bench) (hnle : n ≤ lane.length)
    (h28 : FitsLen (slides + 28 * n)) :
    FitsLen (u2zSlideCap y (fformRunLane n k bench x x2 z) n
        (fformRunSlides slides n x lane) + 16 * n) := by
  have hcap := u2z_slide_le slides n k bench x x2 y z lane hx hy hnb hnle
  exact FitsLen.of_le h28 (wide_slide _ _ n hcap)

/-- A bench settle of `2 · n` in front of the comb, then twenty-four step budgets.
    Toy, Hobby, and Serious keep that inside one cell of move charge. Demo does not. -/
theorem toy_wide_move :
    2 * toy.n + cubeCharge toy.n toy.benchlen + 2 * toy.n +
      3 * (toy.benchlen - toy.n) + 24 * stepBudget toy.n toy.benchlen ≤
      walkCharge toy + (6 * toy.benchlen + 2 * toy.n) := by
  have hL : 2 * toy.n + cubeCharge toy.n toy.benchlen + 2 * toy.n +
      3 * (toy.benchlen - toy.n) + 24 * stepBudget toy.n toy.benchlen = 18597 := by
    simp [cubeCharge, stepBudget, toy]
  have hR : 6 * toy.benchlen + 2 * toy.n = 478 := by simp [toy]
  rw [hL, hR, toy_walk]
  exact ble_le _ _ rfl

theorem hobby_wide_move :
    2 * hobby.n + cubeCharge hobby.n hobby.benchlen + 2 * hobby.n +
      3 * (hobby.benchlen - hobby.n) + 24 * stepBudget hobby.n hobby.benchlen ≤
      walkCharge hobby + (6 * hobby.benchlen + 2 * hobby.n) := by
  have hL : 2 * hobby.n + cubeCharge hobby.n hobby.benchlen + 2 * hobby.n +
      3 * (hobby.benchlen - hobby.n) + 24 * stepBudget hobby.n hobby.benchlen = 98301 := by
    simp [cubeCharge, stepBudget, hobby]
  have hR : 6 * hobby.benchlen + 2 * hobby.n = 1198 := by simp [hobby]
  rw [hL, hR, hobby_walk]
  exact ble_le _ _ rfl

theorem serious_wide_move :
    2 * serious.n + cubeCharge serious.n serious.benchlen + 2 * serious.n +
      3 * (serious.benchlen - serious.n) +
      24 * stepBudget serious.n serious.benchlen ≤
      walkCharge serious + (6 * serious.benchlen + 2 * serious.n) := by
  have hL : 2 * serious.n + cubeCharge serious.n serious.benchlen + 2 * serious.n +
      3 * (serious.benchlen - serious.n) +
      24 * stepBudget serious.n serious.benchlen = 813261 := by
    simp [cubeCharge, stepBudget, serious]
  have hR : 6 * serious.benchlen + 2 * serious.n = 3598 := by simp [serious]
  rw [hL, hR, serious_walk]
  exact ble_le _ _ rfl

theorem demo_seat_slide : 34 * demo.n ≤ cellSlideCharge demo + slideCharge demo.n := by
  have h : 34 * demo.n = 238 := by simp [demo]
  rw [h, demo_slideCharge]
  exact ble_le _ _ rfl

theorem toy_seat_slide : 34 * toy.n ≤ cellSlideCharge toy + slideCharge toy.n := by
  have h : 34 * toy.n = 782 := by simp [toy]
  rw [h, toy_slideCharge]
  exact ble_le _ _ rfl

theorem hobby_seat_slide : 34 * hobby.n ≤ cellSlideCharge hobby + slideCharge hobby.n := by
  have h : 34 * hobby.n = 2006 := by simp [hobby]
  rw [h, hobby_slideCharge]
  exact ble_le _ _ rfl

theorem serious_seat_slide :
    34 * serious.n ≤ cellSlideCharge serious + slideCharge serious.n := by
  have h : 34 * serious.n = 6086 := by simp [serious]
  rw [h, serious_slideCharge]
  exact ble_le _ _ rfl

private theorem add_cap4 (spend moves a b c d s : Nat)
    (h : spend ≤ moves + a + b + c + d) :
    spend + s ≤ moves + (a + b + c + d + s) := by
  omega

/-- The comb after a bench settle of at most `2 · n`. The extra two lengths sit in
    the Toy, Hobby, and Serious move charge. -/
theorem comb_move_fit_seat (t : Spec.Tier) (moves done comb : Nat) (tw : TierWalk t)
    (hmoves : moves ≤ done * (walkCharge t + (6 * t.benchlen + 2 * t.n)))
    (hpos : done < t.cells)
    (hcomb : comb ≤ moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
        3 * (t.benchlen - t.n))
    (hwide : 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) +
        24 * stepBudget t.n t.benchlen ≤
        walkCharge t + (6 * t.benchlen + 2 * t.n)) :
    FitsLen (comb + 24 * stepBudget t.n t.benchlen) := by
  have hle := add_cap4 comb moves (2 * t.n) (cubeCharge t.n t.benchlen) (2 * t.n)
      (3 * (t.benchlen - t.n)) (24 * stepBudget t.n t.benchlen) hcomb
  exact FitsLen.of_le
      (span_fit t.cells done moves
        (2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n + 3 * (t.benchlen - t.n) +
          24 * stepBudget t.n t.benchlen)
        (walkCharge t) (6 * t.benchlen + 2 * t.n) tw.roomM
        (by simpa using tw.moveOver) hmoves hpos hwide)
      hle

private theorem slide_add6 (comb slides n : Nat) (h : comb ≤ slides + 6 * n) :
    comb + 28 * n ≤ slides + 34 * n := by
  omega

/-- Six peg-lengths on the comb, then twenty-eight more. `34 · n` is the cell's slide charge. -/
theorem comb_slide_fit_seat (t : Spec.Tier) (slides done comb : Nat) (tw : TierWalk t)
    (hslides : slides ≤ done * (cellSlideCharge t + slideCharge t.n))
    (hpos : done < t.cells)
    (hcomb : comb ≤ slides + 6 * t.n)
    (h34 : 34 * t.n ≤ cellSlideCharge t + slideCharge t.n) :
    FitsLen (comb + 28 * t.n) := by
  have hle := slide_add6 comb slides t.n hcomb
  exact FitsLen.of_le
      (span_fit t.cells done slides (34 * t.n) (cellSlideCharge t) (slideCharge t.n)
        tw.roomS (by simpa [slideCharge] using tw.slideOver) hslides hpos h34)
      hle

end EcbsLink2.Link2
