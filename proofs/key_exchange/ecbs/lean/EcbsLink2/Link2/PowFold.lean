/-
  One digit of the root power, starting from a seated marker.
  `marker_lift` sets the index to `-1`. Digit `0` then cubes and settles,
  and the up home is `powStep` on that digit. The list step is what the
  power loop folds into `rootY_digits`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.PowZero
import EcbsLink2.Link2.PowDigit
import EcbsLink2.Link2.WalkChord
import EcbsLink2.Link2.WalkCopy

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The board `marker_lift` leaves when the marker is already a natural. -/
def markerLifted (b : Ecbs.Board) (ctrl : Nat) : Ecbs.Board :=
  { b with
    sudo_5Board_6marker := -1
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } }

private theorem markerLifted_held (b : Ecbs.Board) (ctrl : Nat) :
    (markerLifted b ctrl).sudo_5Board_4held = b.sudo_5Board_4held := rfl

private theorem markerLifted_home (b : Ecbs.Board) (ctrl : Nat) :
    (markerLifted b ctrl).sudo_5Board_4home = b.sudo_5Board_4home := rfl

private theorem markerLifted_ops (b : Ecbs.Board) (ctrl : Nat) :
    (markerLifted b ctrl).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := rfl

private theorem cube_lane_len (n k bench : Nat) (xs : List Nat) (hn : n ≤ bench) :
    (laneFold n (n - k) (combStrip n bench xs)).length = bench := by
  have hsch : (combStrip n bench xs).length = bench := combStrip_length n bench xs
  rw [laneFold_length n (n - k) _ (by rw [hsch]; exact hn)]
  exact hsch

private theorem cube_lane_zero (n k bench : Nat) (xs : List Nat)
    (hn0 : 0 < n) (hgap0 : 0 < n - k) (hn : n ≤ bench) :
    ∀ i, n ≤ i →
      ∀ hi : i < (laneFold n (n - k) (combStrip n bench xs)).length,
        (laneFold n (n - k) (combStrip n bench xs))[i] = 0 := by
  intro i hi hlt
  have hlen := cube_lane_len n k bench xs hn
  have hltb : i < bench := by rw [← hlen]; exact hlt
  have hc := cube_off_high xs n k bench hn0 hgap0 i hi hltb
  rw [coeff_eq_get _ i hlt] at hc
  exact hc

private theorem pow_place_arr (b : Ecbs.Board) (dst : Nat)
    (hH : dst < b.sudo_5Board_4home.size) (hD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b dst hH hD xs moves peak).sudo_5Board_5bench = b.sudo_5Board_5bench := by
  unfold placeBoard
  dsimp only
  split <;> rfl

private theorem pow_place_on (b : Ecbs.Board) (dst : Nat)
    (hH : dst < b.sudo_5Board_4home.size) (hD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b dst hH hD xs moves peak).sudo_5Board_8bench_on =
      b.sudo_5Board_8bench_on := by
  unfold placeBoard
  dsimp only
  split <;> rfl

private theorem pow_place_to (b : Ecbs.Board) (dst : Nat)
    (hH : dst < b.sudo_5Board_4home.size) (hD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b dst hH hD xs moves peak).sudo_5Board_8bench_to =
      b.sudo_5Board_8bench_to := by
  unfold placeBoard
  dsimp only
  split <;> rfl

private theorem pow_place_flag (b : Ecbs.Board) (dst : Nat)
    (hH : dst < b.sudo_5Board_4home.size) (hD : dst < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b dst hH hD xs moves peak).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on := by
  unfold placeBoard
  dsimp only
  split <;> rfl

private theorem marker_lift_neg (b : Ecbs.Board) (hm : b.sudo_5Board_6marker < 0) :
    Ecbs.marker_lift b = .ok b := by
  unfold Ecbs.marker_lift
  have hdec : decide (b.sudo_5Board_6marker ≥ (0 : Int)) = false := by
    rw [decide_eq_false_iff_not]
    intro hle
    exact Int.lt_irrefl _ (Int.lt_of_lt_of_le hm hle)
  rw [hdec]
  simp [Bool.false_eq_true, if_false, pure_eq_ok]

/-- A root trit is red, empty, or white. -/
theorem rootDigit_cases (n i : Nat) :
    rootDigit n i = 0 ∨ rootDigit n i = 1 ∨ rootDigit n i = 2 := by
  unfold rootDigit
  by_cases h : i + 2 = n
  · simp [h]
  · by_cases he : i % 2 = 0
    · simp [h, he]
    · simp [h, he]

/-- Folding one more trit is `powStep` on the prefix. -/
theorem foldl_pow_succ (f : List Nat → Nat → List Nat) (acc : List Nat)
    (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    (xs.take (i + 1)).foldl f acc = f ((xs.take i).foldl f acc) (xs[i]'hi) := by
  have htake : xs.take (i + 1) = xs.take i ++ [xs[i]'hi] := by
    rw [List.take_succ, List.getElem?_eq_getElem hi]
    simp
  rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Digit `0` from a seated marker. Lift, cube the up, settle. The up home
    is `powStep` on digit `0`, the bench is off, and the marker is `0`. -/
theorem pow_zero_seated (b : Ecbs.Board) (up : Nat) (acc rhs : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps cg ctrl mx script m : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfitLift : FitsLen (ctrl + 1)) (hfitCube : FitsLen (ctrl + 2))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hF : up < b.sudo_5Board_4held.size)
    (hHome : up < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[up] = true)
    (hArr : b.sudo_5Board_4home[up] = embed acc)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : acc.length = n)
    (hfn : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList acc)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n)))
    (hpeg : FitsLen (2 * pegCount (fieldCube n k bench acc)))
    (hfitMv : FitsLen (cubeMoves moves acc n k bench + 2 * pegCount (fieldCube n k bench acc)))
    (hfitSl : FitsLen (slides + 2 * pegCount (fieldCube n k bench acc))) :
    ∃ bS,
      (do
          let b ← Ecbs.marker_lift b
          let b ← Ecbs.cube b ((up : Nat) : Int) ((up : Nat) : Int)
          Ecbs.settle b) = .ok bS ∧
        (bS.sudo_5Board_4home[up]?) = some (embed (powStep n k bench rhs acc 0)) ∧
        bS.sudo_5Board_8bench_on = false ∧
        (bS.sudo_5Board_4held[up]?) = some true ∧
        bS.sudo_5Board_6marker = 0 := by
  let bL := markerLifted b ctrl
  have hlift : Ecbs.marker_lift b = .ok bL := by
    simpa [bL, markerLifted] using marker_lift_refines b m ctrl hm hc hfitLift
  have hzero := pow_zero_home bL up acc rhs w h r n k moves slides hole bench peak peakS
      cOps cg (ctrl + 1) mx script
      (by simpa [bL, markerLifted] using hmk)
      (by simpa [bL, markerLifted] using hoff)
      (by simp [bL, markerLifted])
      (by simp [bL, markerLifted])
      (by simpa [bL, markerLifted] using hx)
      (by simpa [bL, markerLifted] using hs)
      hpos hfitCube
      (by simpa [bL, markerLifted] using hops)
      (by simpa [bL, markerLifted] using hop1)
      hfops
      (by simpa [bL, markerLifted] using hF)
      (by simpa [bL, markerLifted] using hHome)
      (by simpa [bL, markerLifted] using hHF)
      (by simpa [bL, markerLifted] using hArr)
      (by simpa [bL, markerLifted] using h7)
      (by simpa [bL, markerLifted] using hp)
      (by simpa [bL, markerLifted] using hpeak)
      hn0
      (by simpa [bL, markerLifted] using hn)
      hlenx hfn
      (by simpa [bL, markerLifted] using hmoves)
      (by simpa [bL, markerLifted] using hslides)
      (by simpa [bL, markerLifted] using hbl)
      (by simpa [bL, markerLifted] using hcg)
      hspan h3 hfm
      (by simpa [bL, markerLifted] using hhole)
      hxsT hw0 hh0 hrR hrP hnE hkLe hgap
      (by simpa [bL, markerLifted] using hw)
      (by simpa [bL, markerLifted] using hh)
      (by simpa [bL, markerLifted] using hr)
      (by simpa [bL, markerLifted] using hk)
      hsm hnsm hfitB hfold hpeg hfitMv hfitSl
  rcases hzero with ⟨bS, hrun, hhome, hoffS, hheldS, hmark⟩
  refine ⟨bS, ?_, hhome, hoffS, hheldS, hmark⟩
  · rw [hlift, ok_bind]
    have hid := marker_lift_neg bL (by simp [bL, markerLifted])
    rw [hid, ok_bind] at hrun
    exact hrun

/-- Cube of the up after the marker has been lifted off the script. -/
def powCubeBoard (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size)
    (hHome : up < b.sudo_5Board_4home.size) : Ecbs.Board :=
  { cubeOffBoard (markerDownFeed (markerLifted b ctrl) (ctrl + 1) mx) up up acc n k moves hole
      bench peak peakS cOps hops hF hHome with
    sudo_5Board_9marker_on := true }

/-- A seated marker lifts, then the up is cubed onto the bench. -/
theorem pow_cube_seated (b : Ecbs.Board) (up : Nat) (acc : List Nat)
    (w h r n k moves hole bench peak peakS cOps cg ctrl mx script m : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfitLift : FitsLen (ctrl + 1)) (hfitCube : FitsLen (ctrl + 2))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hF : up < b.sudo_5Board_4held.size)
    (hHome : up < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[up] = true)
    (hArr : b.sudo_5Board_4home[up] = embed acc)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : acc.length = n)
    (hfn : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList acc)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n))) :
    Ecbs.marker_lift b = .ok (markerLifted b ctrl) ∧
      Ecbs.cube (markerLifted b ctrl) ((up : Nat) : Int) ((up : Nat) : Int) =
        .ok (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome) := by
  let bL := markerLifted b ctrl
  refine ⟨?_, ?_⟩
  · simpa [bL, markerLifted] using marker_lift_refines b m ctrl hm hc hfitLift
  · have hcd := cube_down_eq bL up up acc w h r n k moves hole bench peak peakS cOps cg
      (ctrl + 1) mx script
      (by simpa [bL, markerLifted] using hmk)
      (by simpa [bL, markerLifted] using hoff)
      (by simp [bL, markerLifted])
      (by simp [bL, markerLifted])
      (by simpa [bL, markerLifted] using hx)
      (by simpa [bL, markerLifted] using hs)
      hpos hfitCube
      (by simpa [bL, markerLifted] using hops)
      (by simpa [bL, markerLifted] using hop1)
      hfops
      (by simpa [bL, markerLifted] using hF)
      (by simpa [bL, markerLifted] using hHome)
      (by simpa [bL, markerLifted] using hHF)
      (by simpa [bL, markerLifted] using hArr)
      (by simpa [bL, markerLifted] using h7)
      (by simpa [bL, markerLifted] using hp)
      (by simpa [bL, markerLifted] using hpeak)
      hn0
      (by simpa [bL, markerLifted] using hn)
      hlenx hfn
      (by simpa [bL, markerLifted] using hmoves)
      (by simpa [bL, markerLifted] using hbl)
      (by simpa [bL, markerLifted] using hcg)
      hspan h3 hfm
      (by simpa [bL, markerLifted] using hhole)
      hxsT hw0 hh0 hrR hrP hnE hkLe hgap
      (by simpa [bL, markerLifted] using hw)
      (by simpa [bL, markerLifted] using hh)
      (by simpa [bL, markerLifted] using hr)
      (by simpa [bL, markerLifted] using hk)
      hsm hnsm hfitB hfold
    simpa [bL, markerLifted, powCubeBoard] using hcd

private theorem powCube_moves (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (cubeMoves moves acc n k bench) := by
  unfold powCubeBoard
  rw [cube_off_moves]

private theorem powCube_slides (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps slides : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat slides := by
  unfold powCubeBoard
  rw [cube_off_slides]
  simpa [markerDownFeed, markerLifted] using hsl

private theorem powCube_peak (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨up, hF⟩ false) 7)) := by
  unfold powCubeBoard
  rw [cube_off_peak]
  simp [markerDownFeed, markerLifted]

private theorem powCube_strict (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      Int.ofNat (raisedPeak peakS (countHeld b.sudo_5Board_4held 7)) := by
  unfold powCubeBoard
  rw [cube_off_strict]
  simp [markerDownFeed, markerLifted]

private theorem powCube_hole (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole hole (topIdx (combStrip n bench acc))) := by
  unfold powCubeBoard
  rw [cube_off_hole]

private theorem powCube_ctrl (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      Int.ofNat (ctrl + 2) := by
  unfold powCubeBoard
  rw [cube_off_ctrl]
  simp only [markerDownFeed, markerLifted]

private theorem powCube_mx (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx 1) := by
  unfold powCubeBoard
  rw [cube_off_mx]
  simp [markerDownFeed, markerLifted]

private theorem powCube_mark (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_6marker = 0 := by
  unfold powCubeBoard
  rw [cube_off_ix]
  simp [markerDownFeed, markerLifted]

private theorem powCube_on (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_8bench_on = true := by
  unfold powCubeBoard
  rw [cube_off_on]

private theorem powCube_to (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_8bench_to =
      (up : Int) := by
  unfold powCubeBoard
  rw [cube_off_to]

private theorem powCube_bench (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_5bench =
      embed (laneFold n (n - k) (combStrip n bench acc)) := by
  unfold powCubeBoard
  rw [cube_off_bench]

private theorem powCube_tier_n (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int)) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_1t.sudo_4Tier_1n =
      (n : Int) := by
  unfold powCubeBoard
  rw [cube_off_tier]
  simpa [markerDownFeed, markerLifted] using hn

private theorem powCube_held_arr (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨up, hF⟩ false := by
  unfold powCubeBoard
  rw [cube_off_held]
  simp only [markerDownFeed, markerLifted]

private theorem powCube_home_arr (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨up, hHome⟩ #[] := by
  unfold powCubeBoard
  rw [cube_off_home]
  simp only [markerDownFeed, markerLifted]

/-- A home the cube does not clear keeps its flag. -/
private theorem powCube_held_some (b : Ecbs.Board) (up ctrl mx i : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size)
    (v : Bool) (hne : i ≠ up) (hv : b.sudo_5Board_4held[i]? = some v) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4held[i]? =
      some v := by
  rw [powCube_held_arr]
  rw [Array.getElem?_set_ne _ ⟨up, hF⟩ false hne.symm]
  exact hv

/-- A home the cube does not clear keeps its pegs. -/
private theorem powCube_home_some (b : Ecbs.Board) (up ctrl mx i : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size)
    (v : Array Int) (hne : i ≠ up) (hv : b.sudo_5Board_4home[i]? = some v) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4home[i]? =
      some v := by
  rw [powCube_home_arr]
  rw [Array.getElem?_set_ne _ ⟨up, hHome⟩ (#[] : Array Int) hne.symm]
  exact hv

end EcbsLink2.Link2
