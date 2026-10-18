/-
  Homes the three cubes of `frobenius_point` do not write. Home 0 is the
  across, home 1 is the up, and home 2 is the bottom. A later home is the
  one `b1On` already held.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BottomHomes
import EcbsLink2.Link2.CellCube

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

section
variable {b : Ecbs.Board} {x y : List Nat}
  {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}

private theorem feed_ix
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (i : Nat) (hi : i < 8) : i < (upFeed a).sudo_5Board_4home.size := by
  rw [upFeed_home a, a.hszHOn]; exact hi

theorem upSettled_home_ne
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (i : Nat) (hne : (0 : Nat) ≠ i) (hi : i < 8) :
    (upSettled a).sudo_5Board_4home[i]'(by rw [up_home_size a]; exact hi) =
      a.b1On.sudo_5Board_4home[i]'(by rw [a.hszHOn]; exact hi) := by
  have hset := settle_home_eq (upFeed a) 0 ⟨upH a, upD a⟩ a.laneX n a.mv1 slides a.pk1
  have hhome : (upSettled a).sudo_5Board_4home =
      (upFeed a).sudo_5Board_4home.set ⟨0, upH a⟩ (embed (a.laneX.take n)) := by
    rw [upSettled, hset]
  have hget := at_eq hhome (by rw [up_home_size a]; exact hi)
    (by rw [Array.size_set]; exact feed_ix a i hi)
  exact (hget.trans (set_ne (upFeed a).sudo_5Board_4home 0 i (upH a)
      (embed (a.laneX.take n)) hne (feed_ix a i hi))).trans
    (at_eq (upFeed_home a) (feed_ix a i hi) (by rw [a.hszHOn]; exact hi))

theorem upBoard_home_ne
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (i : Nat) (hne : (1 : Nat) ≠ i) (hi : i < 8) :
    (upBoard a).sudo_5Board_4home[i]'(by rw [up_board_home_size a]; exact hi) =
      (upSettled a).sudo_5Board_4home[i]'(by rw [up_home_size a]; exact hi) := by
  have hset := cube_off_home (upSettled a) 1 1 y n k (upMv a) a.hole1 bench (upPk a)
    a.peakS1 (cOps + 1) (up_ops_lt a) (up1D a) (up1H a)
  have hhome : (upBoard a).sudo_5Board_4home =
      (upSettled a).sudo_5Board_4home.set ⟨1, up1H a⟩ #[] := by
    rw [upBoard, hset]
  have hget := at_eq hhome (by rw [up_board_home_size a]; exact hi)
    (by rw [Array.size_set, up_home_size a]; exact hi)
  exact hget.trans (set_ne (upSettled a).sudo_5Board_4home 1 i (up1H a) #[] hne
    (by rw [up_home_size a]; exact hi))

theorem pointFeed_home_eq
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (pointFeed a).sudo_5Board_4home = (upBoard a).sudo_5Board_4home := by
  simp [pointFeed, upFlag, markerUpFeed]

theorem seatAt_szH
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script) :
    (seatAt a).sudo_5Board_4home.size = 8 := by
  rw [seatAt, settle_home_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
      (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a), Array.size_set,
    pointFeed_home_eq a, up_board_home_size]

theorem seatAt_home_ne
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (i : Nat) (hne : (1 : Nat) ≠ i) (hi : i < 8) :
    (seatAt a).sudo_5Board_4home[i]'(by rw [seatAt_szH a]; exact hi) =
      (upBoard a).sudo_5Board_4home[i]'(by rw [up_board_home_size a]; exact hi) := by
  have hset := settle_home_eq (pointFeed a) 1 ⟨pointFeed_homeIx a, pointFeed_heldIx a⟩
    (upLane n k bench y) n (upMv2 a) (upSl a) (upPk2 a)
  have hsrc : i < (pointFeed a).sudo_5Board_4home.size := by
    rw [pointFeed_home_eq a, up_board_home_size a]; exact hi
  have hhome : (seatAt a).sudo_5Board_4home =
      (pointFeed a).sudo_5Board_4home.set ⟨1, pointFeed_homeIx a⟩
        (embed ((upLane n k bench y).take n)) := by
    rw [seatAt, hset]
  have hget := at_eq hhome (by rw [seatAt_szH a]; exact hi)
    (by rw [Array.size_set]; exact hsrc)
  exact (hget.trans (set_ne (pointFeed a).sudo_5Board_4home 1 i (pointFeed_homeIx a)
      (embed ((upLane n k bench y).take n)) hne hsrc)).trans
    (at_eq (pointFeed_home_eq a) hsrc (by rw [up_board_home_size a]; exact hi))

/-- A home other than the across and the up is the one the across cube left. -/
theorem seat_keeps_later
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (i : Nat) (h0 : (0 : Nat) ≠ i) (h1 : (1 : Nat) ≠ i) (hi : i < 8) :
    (seatAt a).sudo_5Board_4home[i]'(by rw [seatAt_szH a]; exact hi) =
      a.b1On.sudo_5Board_4home[i]'(by rw [a.hszHOn]; exact hi) :=
  (seatAt_home_ne a i h1 hi).trans
    ((upBoard_home_ne a i h1 hi).trans (upSettled_home_ne a i h0 hi))

end

/-- The bottom comb writes home `src` only. -/
theorem off_home_ne (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (i : Nat) (hne : src ≠ i) (hi : i < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4home[i]'(by
      rw [cube_off_home, Array.size_set]; exact hi) =
      b.sudo_5Board_4home[i] := by
  have hset := cube_off_home b dst src xs n k moves hole bench peak peakS cOps hops hF hHome
  have hget := at_eq hset (by rw [hset, Array.size_set]; exact hi) (by rw [Array.size_set]; exact hi)
  exact hget.trans (set_ne b.sudo_5Board_4home src i hHome #[] hne hi)

section
variable {b : Ecbs.Board} {x y : List Nat}
  {n k w h r bench cg pk moves slides holeN cOps ctrl mx script : Nat}

/-- `frobenius_point` returns the bottom comb with the marker flag put back. -/
theorem frobenius_bottom_eq
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (hyt : allTritList y) (hy : y.length = n)
    (hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true)
    (hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed z)
    (hz : z.length = n) (hzt : allTritList z)
    (hn0 : 0 < n) (hnbL : n ≤ a.laneX.length) (hnb : n ≤ bench) (hgap0 : 0 < n - k)
    (hs1 : 1 < script) (hs2 : 2 < script)
    (hfitU : FitsLen ((ctrl + 1) + 2)) (hfitC : FitsLen (cOps + 2))
    (hfitCtrl : FitsLen (ctrl + 5)) (hfitC3 : FitsLen (cOps + 3))
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1))) (hnFit : FitsLen n) (hbenchFit : FitsLen bench)
    (hpeg : FitsLen (2 * pegCount ((upLane n k bench y).take n)))
    (hfitMv : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)))
    (hfitSl : FitsLen (upSl a + 2 * pegCount ((upLane n k bench y).take n)))
    (hfm : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n) + 2 * n))
    (hfold : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n) + 2 * n +
        3 * (bench - n)))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) :
    Ecbs.frobenius_point b = .ok
      { cubeOffBoard (seatAt a) 2 2 z n k
          (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
          (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
          (raisedPeak (upPk2 a)
            (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
          (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
          (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a) with
        sudo_5Board_9marker_on := true } := by
  have hseat := pointFeed_seat a hn0 hnb hgap0 hnFit hfitC3 hpeg hfitMv hfitSl hbenchFit
  have hcube := seatAt_cube a z hhome2 hheld2 hz hzt hn0 hspan h3 hnFit hbenchFit hfitC3
    hfm hfold hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm
  rw [frobenius_point_bottom a z hyt hy hheld2 hhome2 hz hzt hn0 hnbL hnb hgap0
    hs1 hs2 hfitU hfitC hfitCtrl hfitC3 hspan h3 hnFit hbenchFit hpeg hfitMv hfitSl hfm hfold
    hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm]
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl]
  rw [← pointFeed]
  rw [hseat, ← seatAt_cast a, hcube, ok_bind, pure_eq_ok]

def bottomOff
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) : Ecbs.Board :=
  cubeOffBoard (seatAt a) 2 2 z n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a)

def bottomFlag
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) : Ecbs.Board :=
  { bottomOff a z with sudo_5Board_9marker_on := true }

theorem bottomFlag_sz
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) :
    (bottomFlag a z).sudo_5Board_4home.size = 8 := by
  have hhome : (bottomFlag a z).sudo_5Board_4home = (bottomOff a z).sudo_5Board_4home := rfl
  rw [hhome, bottomOff, cube_off_home, Array.size_set, seatAt_szH]

/-- A home other than 0, 1, and 2 on the comb is the home the across cube left. -/
theorem bottomFlag_later
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat) (i : Nat) (h0 : (0 : Nat) ≠ i) (h1 : (1 : Nat) ≠ i)
    (h2 : (2 : Nat) ≠ i) (hi : i < 8) :
    (bottomFlag a z).sudo_5Board_4home[i]'(by rw [bottomFlag_sz a z]; exact hi) =
      a.b1On.sudo_5Board_4home[i]'(by rw [a.hszHOn]; exact hi) := by
  have hhome : (bottomFlag a z).sudo_5Board_4home = (bottomOff a z).sudo_5Board_4home := rfl
  have hoff := off_home_ne (seatAt a) 2 2 z n k
    (upMv2 a + 2 * pegCount ((upLane n k bench y).take n))
    (raisedHole a.hole1 (topIdx (combStrip n bench y))) bench
    (raisedPeak (upPk2 a)
      (countHeld ((pointFeed a).sudo_5Board_4held.set ⟨1, pointFeed_heldIx a⟩ true) 7))
    (raisedPeak a.peakS1 (countHeld (upSettled a).sudo_5Board_4held 7))
    (cOps + 2) (seatAt_ops a) (seatAt_held2ix a) (seatAt_home2ix a) i h2
    (by rw [seatAt_szH a]; exact hi)
  have hget := at_eq hhome (by rw [bottomFlag_sz a z]; exact hi)
    (by rw [bottomOff, cube_off_home, Array.size_set, seatAt_szH]; exact hi)
  exact (hget.trans hoff).trans (seat_keeps_later a i h0 h1 hi)

theorem frobenius_is_flag
    (a : DownAcross b x y n k w h r bench cg pk moves slides holeN cOps ctrl mx script)
    (z : List Nat)
    (hyt : allTritList y) (hy : y.length = n)
    (hheld2 : a.b1On.sudo_5Board_4held[2]'(by rw [a.hszDOn]; decide) = true)
    (hhome2 : a.b1On.sudo_5Board_4home[2]'(by rw [a.hszHOn]; decide) = embed z)
    (hz : z.length = n) (hzt : allTritList z)
    (hn0 : 0 < n) (hnbL : n ≤ a.laneX.length) (hnb : n ≤ bench) (hgap0 : 0 < n - k)
    (hs1 : 1 < script) (hs2 : 2 < script)
    (hfitU : FitsLen ((ctrl + 1) + 2)) (hfitC : FitsLen (cOps + 2))
    (hfitCtrl : FitsLen (ctrl + 5)) (hfitC3 : FitsLen (cOps + 3))
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1))) (hnFit : FitsLen n) (hbenchFit : FitsLen bench)
    (hpeg : FitsLen (2 * pegCount ((upLane n k bench y).take n)))
    (hfitMv : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n)))
    (hfitSl : FitsLen (upSl a + 2 * pegCount ((upLane n k bench y).take n)))
    (hfm : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n) + 2 * n))
    (hfold : FitsLen (upMv2 a + 2 * pegCount ((upLane n k bench y).take n) + 2 * n +
        3 * (bench - n)))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) :
    Ecbs.frobenius_point b = .ok (bottomFlag a z) := by
  simpa [bottomFlag, bottomOff] using
    frobenius_bottom_eq a z hyt hy hheld2 hhome2 hz hzt hn0 hnbL hnb hgap0
      hs1 hs2 hfitU hfitC hfitCtrl hfitC3 hspan h3 hnFit hbenchFit hpeg hfitMv hfitSl
      hfm hfold hw0 hh0 hrR hrP hnE hkLe hgap hsm hnsm

end

end EcbsLink2.Link2
