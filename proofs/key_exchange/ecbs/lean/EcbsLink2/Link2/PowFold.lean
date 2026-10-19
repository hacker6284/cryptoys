/-
  One digit of the root power, starting from a seated marker.
  `marker_lift` sets the index to `-1`. Digit `0` then cubes and settles.
  A red or white digit cubes, copies the factor, and settles through
  `pow_digit_home`. Either way the up home is `powStep`. The list step
  `foldl_pow_succ` is what folds those digits into `rootY_digits`.
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
        bS.sudo_5Board_6marker = 0 ∧
        bS.sudo_5Board_9marker_on = true ∧
        bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_5moves =
          Int.ofNat (cubeMoves moves acc n k bench + 2 * pegCount (fieldCube n k bench acc)) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_6slides =
          Int.ofNat (slides + 2 * pegCount (fieldCube n k bench acc)) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
          Int.ofNat (raisedHole hole (topIdx (combStrip n bench acc))) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat (max mx 1) ∧
        (∃ pk, bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk) ∧
        (∃ ps, bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps) ∧
        (bS.sudo_5Board_4cost.sudo_5Costs_3ops[1]?) = some (Int.ofNat (cOps + 1)) ∧
        (∀ j, j ≠ 1 → (bS.sudo_5Board_4cost.sudo_5Costs_3ops[j]?) =
          (b.sudo_5Board_4cost.sudo_5Costs_3ops[j]?)) ∧
        (∀ i, i ≠ up → (bS.sudo_5Board_4home[i]?) = (b.sudo_5Board_4home[i]?)) ∧
        (∀ i, i ≠ up → (bS.sudo_5Board_4held[i]?) = (b.sudo_5Board_4held[i]?)) ∧
        bS.sudo_5Board_1t = b.sudo_5Board_1t ∧
        bS.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
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
  rcases hzero with ⟨bS, hrun, hhome, hoffS, hheldS, hmark, hflagZ, hctrlZ, hmvZ, hslZ,
      hopsZ, hholeZ, hmxZ, hpkZ, hpsZ, hhomeZ, hheldZ, htierZ, hszZ⟩
  have hctrl2 : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
    simpa [show (ctrl + 1) + 1 = ctrl + 2 by omega] using hctrlZ
  have hop1S : (bS.sudo_5Board_4cost.sudo_5Costs_3ops[1]?) = some (Int.ofNat (cOps + 1)) := by
    have hsz : 1 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hopsZ, Array.size_set]; exact hops
    rw [hopsZ, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hops)]
    simp [Array.getElem_set]
  have hopK : ∀ j, j ≠ 1 → (bS.sudo_5Board_4cost.sudo_5Costs_3ops[j]?) =
      (b.sudo_5Board_4cost.sudo_5Costs_3ops[j]?) := by
    intro j hj
    rw [hopsZ]
    refine Eq.trans (Array.getElem?_set_ne _ _ _ (by intro h; exact hj h.symm)) ?_
    simp [bL, markerLifted]
  have htierS : bS.sudo_5Board_1t = b.sudo_5Board_1t := by
    rw [htierZ]
    simp [bL, markerLifted]
  have hszS : bS.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hszZ]
    simp [bL, markerLifted]
  refine ⟨bS, ?_, hhome, hoffS, hheldS, hmark, hflagZ, hctrl2, hmvZ, hslZ, hholeZ, hmxZ,
      hpkZ, hpsZ, hop1S, hopK, hhomeZ, hheldZ, htierS, hszS⟩
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

private theorem powCube_tier (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_1t =
      b.sudo_5Board_1t := by
  unfold powCubeBoard
  rw [cube_off_tier]
  simp only [markerDownFeed, markerLifted]

private theorem powCube_ops_arr (b : Ecbs.Board) (up ctrl mx : Nat) (acc : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : up < b.sudo_5Board_4held.size) (hHome : up < b.sudo_5Board_4home.size) :
    (powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) := by
  unfold powCubeBoard
  rw [cube_off_ops]
  simp only [markerDownFeed, markerLifted]

/-- A nonzero root digit from a seated marker. Lift, cube, copy the factor
    (the squared side on red, the side on white), then `pow_digit_home`.
    The up home is `powStep`. -/
theorem pow_live_seated (b : Ecbs.Board) (up spare src : Nat) (acc rhs factor : List Nat)
    (d w h r n k moves slides hole bench peak peakS cOps cOp0 cg ctrl mx script m : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hposS : 0 < script) (h1 : 1 < script)
    (hfitLift : FitsLen (ctrl + 1)) (hfitCube : FitsLen (ctrl + 2))
    (hfitSeat : FitsLen (ctrl + 4))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hops0 : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops0) = (cOp0 : Int))
    (hfops0 : FitsLen (cOp0 + 1))
    (hF : up < b.sudo_5Board_4held.size)
    (hHome : up < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[up] = true)
    (hArr : b.sudo_5Board_4home[up] = embed acc)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hSpare : spare < b.sudo_5Board_4held.size)
    (hHomeSpare : spare < b.sudo_5Board_4home.size)
    (hemptySp : b.sudo_5Board_4held[spare] = false)
    (hSrc : src < b.sudo_5Board_4held.size)
    (hHomeSrc : src < b.sudo_5Board_4home.size)
    (hsrcHeld : b.sudo_5Board_4held[src] = true)
    (hsrcArr : b.sudo_5Board_4home[src] = embed factor)
    (hne : up ≠ spare) (hsrcU : src ≠ up) (hsrcS : src ≠ spare)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : acc.length = n) (hfacLen : factor.length = n)
    (hfn : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench) (hspan2 : 2 * (n - 1) < bench)
    (h3 : FitsLen (3 * (n - 1))) (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList acc) (hcubeT : allTritList (fieldCube n k bench acc))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfoldC : FitsLen (moves + 2 * n + 3 * (bench - n)))
    (hfitCopy : FitsLen (cubeMoves moves acc n k bench + pegCount factor))
    (hpegM : FitsLen (2 * pegCount (fieldCube n k bench acc)))
    (hfitMvM : FitsLen (cubeMoves moves acc n k bench + pegCount factor +
        2 * pegCount (fieldCube n k bench acc)))
    (hfitSlM : FitsLen (slides + 2 * pegCount (fieldCube n k bench acc)))
    (hfoldM : FitsLen (cubeMoves moves acc n k bench + pegCount factor +
        2 * pegCount (fieldCube n k bench acc) + n * (n + 1) + 3 * (bench - n)))
    (hbranch : (d = 2 ∧ factor = fieldMul n k bench rhs rhs) ∨ (d = 1 ∧ factor = rhs))
    (hfitClear : FitsLen (cubeMoves moves acc n k bench + pegCount factor +
        2 * pegCount (fieldCube n k bench acc) +
        schoolMoves (fieldCube n k bench acc) factor n n +
        foldCharge n (n - k) (school n (fieldCube n k bench acc) factor
          (List.replicate bench 0) false) +
        pegCount (fieldCube n k bench acc)))
    (hpegP : FitsLen (2 * pegCount (fieldMul n k bench (fieldCube n k bench acc) factor)))
    (hfitSet : FitsLen (cubeMoves moves acc n k bench + pegCount factor +
        2 * pegCount (fieldCube n k bench acc) +
        schoolMoves (fieldCube n k bench acc) factor n n +
        foldCharge n (n - k) (school n (fieldCube n k bench acc) factor
          (List.replicate bench 0) false) +
        pegCount (fieldCube n k bench acc) +
        2 * pegCount (fieldMul n k bench (fieldCube n k bench acc) factor)))
    (hfitSl2 : FitsLen (slides + 2 * pegCount (fieldCube n k bench acc) +
        2 * pegCount (fieldMul n k bench (fieldCube n k bench acc) factor))) :
    ∃ bS,
      (do
          let b ← Ecbs.marker_lift b
          let b ← Ecbs.cube b ((up : Nat) : Int) ((up : Nat) : Int)
          let b ← Ecbs.copy_band b ((spare : Nat) : Int) ((src : Nat) : Int) false
          let b ← Ecbs.mul b ((up : Nat) : Int) ((up : Nat) : Int) ((spare : Nat) : Int)
              false false false
          let b ← Ecbs.clear b ((up : Nat) : Int)
          Ecbs.settle b) = .ok bS ∧
        (bS.sudo_5Board_4home[up]?) = some (embed (powStep n k bench rhs acc d)) ∧
        bS.sudo_5Board_8bench_on = false ∧
        (bS.sudo_5Board_4held[up]?) = some true ∧
        bS.sudo_5Board_6marker = Int.ofNat 1 ∧
        bS.sudo_5Board_9marker_on = true ∧
        (bS.sudo_5Board_4home[src]?) = some (embed factor) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 4) ∧
        bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat (max mx 2) ∧
        (bS.sudo_5Board_4held[spare]?) = some false ∧
        (∀ i, i ≠ up → i ≠ spare →
          (bS.sudo_5Board_4home[i]?) = (b.sudo_5Board_4home[i]?) ∧
          (bS.sudo_5Board_4held[i]?) = (b.sudo_5Board_4held[i]?)) := by
  obtain ⟨hlift, hcube⟩ := pow_cube_seated b up acc w h r n k moves hole bench peak peakS cOps cg
      ctrl mx script m hmk hoff hm hc hx hs hposS hfitLift hfitCube hops hop1 hfops hF hHome hHF
      hArr h7 hp hpeak hn0 hn hlenx hfn hmoves hbl hcg hspan h3 hfm hhole hxsT hw0 hh0 hrR hrP
      hnE hkLe hgap hw hh hr hk hsm hnsm hfitB hfoldC
  let bC := powCubeBoard b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome
  let lane := laneFold n (n - k) (combStrip n bench acc)
  let mvC := cubeMoves moves acc n k bench
  let pkC := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨up, hF⟩ false) 7)
  let cube := fieldCube n k bench acc
  have hmvC := powCube_moves b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome
  have hpkC := powCube_peak b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome
  have hmvCast : bC.sudo_5Board_4cost.sudo_5Costs_5moves = (mvC : Int) := by
    simpa [bC, mvC, ofNat_eq_natCast] using hmvC
  have hpkCast : bC.sudo_5Board_4cost.sudo_5Costs_4peak = (pkC : Int) := by
    simpa [bC, pkC, ofNat_eq_natCast] using hpkC
  have hHomeSp : spare < bC.sudo_5Board_4home.size := by
    simp only [bC]; rw [powCube_home_arr, Array.size_set]
    exact hHomeSpare
  have hHeldSp : spare < bC.sudo_5Board_4held.size := by
    simp only [bC]; rw [powCube_held_arr, Array.size_set]
    exact hSpare
  have hHomeSrcC : src < bC.sudo_5Board_4home.size := by
    simp only [bC]; rw [powCube_home_arr, Array.size_set]
    exact hHomeSrc
  have hHeldSrcC : src < bC.sudo_5Board_4held.size := by
    simp only [bC]; rw [powCube_held_arr, Array.size_set]
    exact hSrc
  have h7C : 7 ≤ bC.sudo_5Board_4held.size := by
    simp only [bC]; rw [powCube_held_arr, Array.size_set]
    exact h7
  have hsrcHeldC : bC.sudo_5Board_4held[src] = true := by
    have h? := powCube_held_some b up ctrl mx src acc n k moves hole bench peak peakS cOps hops hF
        hHome true hsrcU (by rw [Array.getElem?_eq_getElem hSrc]; exact congrArg some hsrcHeld)
    simp only [bC] at h?
    rw [Array.getElem?_eq_getElem hHeldSrcC] at h?
    injection h?
  have hemptyC : bC.sudo_5Board_4held[spare] = false := by
    have h? := powCube_held_some b up ctrl mx spare acc n k moves hole bench peak peakS cOps hops hF
        hHome false hne.symm (by rw [Array.getElem?_eq_getElem hSpare]; exact congrArg some hemptySp)
    simp only [bC] at h?
    rw [Array.getElem?_eq_getElem hHeldSp] at h?
    injection h?
  have harrC : bC.sudo_5Board_4home[src] = embed factor := by
    have h? := powCube_home_some b up ctrl mx src acc n k moves hole bench peak peakS cOps hops hF
        hHome (embed factor) hsrcU
          (by rw [Array.getElem?_eq_getElem hHomeSrc]; exact congrArg some hsrcArr)
    simp only [bC] at h?
    rw [Array.getElem?_eq_getElem hHomeSrcC] at h?
    injection h?
  have hnC := powCube_tier_n b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome hn
  have hnLen : bC.sudo_5Board_1t.sudo_4Tier_1n = (factor.length : Int) := by
    simpa [bC, hfacLen] using hnC
  have hcopy := copy_band_refines bC spare src factor mvC pkC hHomeSp hHeldSp hHomeSrcC hHeldSrcC
      h7C hsrcHeldC harrC hemptyC hnLen (by simpa [hfacLen] using hfn) hmvCast hpkCast hfitCopy
  let bP := placeBoard bC spare hHomeSp hHeldSp factor mvC pkC
  let mvP := mvC + pegCount factor
  let pkS := raisedPeak peakS (countHeld b.sudo_5Board_4held 7)
  let pkP := raisedPeak pkC (countHeld (bC.sudo_5Board_4held.set ⟨spare, hHeldSp⟩ true) 7)
  let hole' := raisedHole hole (topIdx (combStrip n bench acc))
  have htake : lane.take n = cube := cube_off_prefix n k bench acc
  have hnbench : n ≤ bench := by omega
  have hgap0 : 0 < n - k := by rw [hgap]; exact Nat.mul_pos hw0 hrP
  have hlen := cube_lane_len n k bench acc hnbench
  have hposL : 0 < lane.length := by rw [hlen]; omega
  have hnle : n ≤ lane.length := by rw [hlen]; exact hnbench
  have hzero := cube_lane_zero n k bench acc hn0 hgap0 hnbench
  have hfitL : FitsLen lane.length := by rw [hlen]; exact hfitB
  have htierP : bP.sudo_5Board_1t = b.sudo_5Board_1t := by
    simp only [bP]; rw [place_tier_eq]; simp only [bC]; rw [powCube_tier]
  have hflagP : bP.sudo_5Board_9marker_on = true := by
    simp only [bP]; rw [pow_place_flag]; simp only [bC]; unfold powCubeBoard; rfl
  have honP : bP.sudo_5Board_8bench_on = true := by
    simp only [bP]; rw [pow_place_on]; simp only [bC]; rw [powCube_on]
  have htoP : bP.sudo_5Board_8bench_to = (up : Int) := by
    simp only [bP]; rw [pow_place_to]; simp only [bC]; rw [powCube_to]
  have hHP : up < bP.sudo_5Board_4home.size := by
    simp only [bP]; rw [place_home_eq, Array.size_set]; simp only [bC]; rw [powCube_home_arr, Array.size_set]
    exact hHome
  have hDP : up < bP.sudo_5Board_4held.size := by
    simp only [bP]; rw [place_held_eq, Array.size_set]; simp only [bC]; rw [powCube_held_arr, Array.size_set]
    exact hF
  have h7P : 7 ≤ bP.sudo_5Board_4held.size := by
    simp only [bP]; rw [place_held_eq, Array.size_set]
    exact h7C
  have hUpC : up < bC.sudo_5Board_4held.size := by
    simp only [bC]; rw [powCube_held_arr, Array.size_set]; exact hF
  have hemptyUp : bC.sudo_5Board_4held[up]'(hUpC) = false := by
    have h? : bC.sudo_5Board_4held[up]? = some false := by
      simp only [bC]; rw [powCube_held_arr]
      rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hF)]
      simp [Array.getElem_set]
    rw [Array.getElem?_eq_getElem hUpC] at h?
    injection h?
  have hemptyP : bP.sudo_5Board_4held[up] = false := by
    have h? : bP.sudo_5Board_4held[up]? = some false := by
      simp only [bP]; rw [place_held_eq]
      rw [Array.getElem?_set_ne _ ⟨spare, hHeldSp⟩ true hne.symm]
      rw [Array.getElem?_eq_getElem (by simp only [bC]; rw [powCube_held_arr, Array.size_set]; exact hF),
        hemptyUp]
    rw [Array.getElem?_eq_getElem hDP] at h?
    injection h?
  have hbenchP : bP.sudo_5Board_5bench = embed lane := by
    simp only [bP]; rw [pow_place_arr]; simp only [bC]; rw [powCube_bench]
  have hnP : bP.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [htierP]; exact hn
  have hmvP : bP.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvP := by
    simp only [bP]; rw [place_moves_eq]
  have hslP : bP.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simp only [bP]; rw [place_slides_eq]; simp only [bC]
    exact powCube_slides b up ctrl mx acc n k moves hole bench peak peakS cOps slides hops hF hHome
      hslides
  have hpkP : bP.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkP := by
    simp only [bP]; rw [place_peak_nat bC spare hHomeSp hHeldSp factor mvC pkC hpkCast]
    simp [pkP, raisedPeak]
  have hops0P : 0 < bP.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simp only [bP]; rw [place_ops_eq]; simp only [bC]; rw [powCube_ops_arr, Array.size_set]
    exact hops0
  have hop0P : bP.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (cOp0 : Int) := by
    have h? : bP.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (cOp0 : Int) := by
      simp only [bP]; rw [place_ops_eq]; simp only [bC]; rw [powCube_ops_arr]
      rw [Array.getElem?_set_ne _ ⟨1, hops⟩ (Int.ofNat (cOps + 1)) (by decide : (1 : Nat) ≠ 0)]
      rw [Array.getElem?_eq_getElem hops0, hop0]
    rw [Array.getElem?_eq_getElem hops0P] at h?
    injection h?
  have hmP : bP.sudo_5Board_6marker = Int.ofNat 0 := by
    simp only [bP]; rw [place_marker_eq]; simp only [bC]
    simpa [ofNat_eq_natCast] using
      powCube_mark b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome
  have hcP : bP.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
    simp only [bP]; rw [place_ctrl_eq]; simp only [bC]
    exact powCube_ctrl b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome
  have hxP : bP.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat (max mx 1) := by
    simp only [bP]; rw [place_mx_eq]; simp only [bC]
    exact powCube_mx b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome
  have hsP : bP.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    rw [htierP]; exact hs
  have hpkSP : bP.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (pkS : Int) := by
    simp only [bP]; rw [place_strict_eq]; simp only [bC]
    simpa [pkS, ofNat_eq_natCast] using
      powCube_strict b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome
  have hholeP : bP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole' := by
    simp only [bP]; rw [place_hole_eq]; simp only [bC]
    exact powCube_hole b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome
  have hblP : bP.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [htierP]; exact hbl
  have hSP : spare < bP.sudo_5Board_4held.size := by
    simp only [bP]; rw [place_held_eq, Array.size_set]
    exact hHeldSp
  have hHomeSP : spare < bP.sudo_5Board_4home.size := by
    simp only [bP]; rw [place_home_eq, Array.size_set]
    exact hHomeSp
  have hHSp : bP.sudo_5Board_4held[spare] = true := by
    have h? : bP.sudo_5Board_4held[spare]? = some true := by
      simp only [bP]; rw [place_held_eq]
      rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hHeldSp)]
      simp [Array.getElem_set]
    rw [Array.getElem?_eq_getElem hSP] at h?
    injection h?
  have hYsP : bP.sudo_5Board_4home[spare] = embed factor := by
    have h? : bP.sudo_5Board_4home[spare]? = some (embed factor) := by
      simp only [bP]; rw [place_home_eq]
      rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hHomeSp)]
      simp [Array.getElem_set]
    rw [Array.getElem?_eq_getElem hHomeSP] at h?
    injection h?
  have hwP : bP.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by rw [htierP]; exact hw
  have hhP : bP.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by rw [htierP]; exact hh
  have htrP : bP.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by rw [htierP]; exact hr
  have hkP : bP.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by rw [htierP]; exact hk
  have hdig := pow_digit_home bP up spare lane cube factor acc rhs d w h r n k mvP slides pkP pkS
      cOp0 0 (ctrl + 2) (max mx 1) script bench hole'
      hflagP honP htoP hHP hDP h7P hemptyP hbenchP hnP hposL hnle hzero hfn hfitL
      hmvP hslP hpkP
      (by simpa [htake, cube] using hpegM)
      (by simpa [htake, cube, mvP] using hfitMvM)
      (by simpa [htake, cube] using hfitSlM)
      hops0P hop0P hfops0
      hmP hcP hxP hsP h1
      (FitsLen.of_le hfitSeat (by omega))
      (by simpa using hfitSeat)
      (FitsLen.of_le hfitSeat (by omega))
      hSP hHomeSP hHSp hYsP hne
      hn0 htake hfacLen hblP hpkSP hspan2 hcubeT hfi hholeP
      hw0 hh0 hrR hrP hnE hkLe hgap hwP hhP htrP hkP hsm hnsm hfitB
      (by simpa [htake, cube, mvP] using hfoldM)
      rfl hbranch
      (by simpa [htake, cube, mvP] using hfitClear)
      (by simpa [cube] using hpegP)
      (by simpa [htake, cube, mvP] using hfitSet)
      (by simpa [htake, cube] using hfitSl2)
  rcases hdig with ⟨bS, hrun, hhome, hoffS, hheldS, hmarkS, hflagS, hctrlS, hkeep, hheldK, hspS,
      _hmvD, _hslD, _hopsD, _hpkD, hmxD⟩
  have hctrl4 : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 4) := by
    simpa [show (ctrl + 2) + 2 = ctrl + 4 by omega] using hctrlS
  have hmx2 : bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat (max mx 2) := by
    have hm : max (max mx 1) (0 + 2) = max mx 2 := by
      simp only [Nat.zero_add]
      by_cases h1 : mx ≤ 1
      · rw [Nat.max_eq_right h1, Nat.max_eq_right (by decide : (1 : Nat) ≤ 2),
          Nat.max_eq_right (Nat.le_trans h1 (by decide : (1 : Nat) ≤ 2))]
      · rw [Nat.max_eq_left (by omega : 1 ≤ mx)]
    simpa [hm] using hmxD
  refine ⟨bS, ?_, hhome, hoffS, hheldS, hmarkS, hflagS, ?_, hctrl4, hmx2, hspS, ?_⟩
  · rw [hlift, ok_bind, hcube, ok_bind, hcopy, ok_bind]
    exact hrun
  · rw [hkeep src hsrcU hsrcS]
    simp only [bP]
    rw [place_home_eq]
    rw [Array.getElem?_set_ne _ ⟨spare, hHomeSp⟩ (embed factor) hsrcS.symm]
    simpa [bC] using
      powCube_home_some b up ctrl mx src acc n k moves hole bench peak peakS cOps hops hF hHome
        (embed factor) hsrcU (by rw [Array.getElem?_eq_getElem hHomeSrc]; exact congrArg some hsrcArr)
  · intro i hiu his
    refine ⟨?_, ?_⟩
    · rw [hkeep i hiu his]
      simp only [bP]
      rw [place_home_eq, Array.getElem?_set_ne _ ⟨spare, hHomeSp⟩ (embed factor) his.symm]
      simp only [bC]
      rw [powCube_home_arr b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome]
      rw [Array.getElem?_set_ne _ ⟨up, hHome⟩ (#[] : Array Int) hiu.symm]
    · rw [hheldK i hiu his]
      simp only [bP]
      rw [place_held_eq, Array.getElem?_set_ne _ ⟨spare, hHeldSp⟩ true his.symm]
      simp only [bC]
      rw [powCube_held_arr b up ctrl mx acc n k moves hole bench peak peakS cOps hops hF hHome]
      rw [Array.getElem?_set_ne _ ⟨up, hF⟩ false hiu.symm]

end EcbsLink2.Link2
