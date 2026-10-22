/-
  The new point of `fform_add`, after the gap has been added into the bench.
  One settle-and-nocopy: the bench is aimed at `seat`, not at the destination,
  so it is written home and the product of the two factors is the new bench.
  SPEC.md §3 R7 line 152 is that product when the factors are the run and `v²Z`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformGapLay
import EcbsLink2.Link2.FformField
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The zero-strip schoolbook a nocopy multiply folds. -/
def nocopySchool (n bench : Nat) (xs ys : List Nat) (mirror : Bool) : List Nat :=
  school n xs ys (List.replicate bench 0) mirror

/-- Moves after settling `lane` and folding that schoolbook. -/
def nocopyCharge (n k moves bench : Nat) (xs ys lane : List Nat) (mirror : Bool) : Nat :=
  moves + 2 * pegCount (lane.take n) + schoolMoves xs ys n n +
    foldCharge n (n - k) (nocopySchool n bench xs ys mirror)

theorem idx_eq {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

theorem fold_held (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4held = b.sudo_5Board_4held := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_home (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4home = b.sudo_5Board_4home := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_marker (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_9marker_on =
      b.sudo_5Board_9marker_on := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_ix (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_6marker = b.sudo_5Board_6marker := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_on (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_8bench_on =
      b.sudo_5Board_8bench_on := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_to (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_8bench_to =
      b.sudo_5Board_8bench_to := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_tier (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_slides (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_ctrl (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_mx (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_ops (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_strict (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_moves (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mv + foldCharge n (n - k) sch) := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem fold_peak (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat)
    (hno : ¬ peak < countHeld b.sudo_5Board_4held 7) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_4peak =
      (peak : Int) := by
  unfold ontoFoldBoard peakBoard raisedPeak noteBench withMoves withHole
  dsimp only
  split <;> simp [hno, ofNat_eq_natCast]

theorem fold_peak_rise (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak peak (countHeld b.sudo_5Board_4held 7)) := by
  unfold ontoFoldBoard peakBoard
  simp [noteBench_held, ofNat_eq_natCast]

theorem fold_hole (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      (if decide (Int.ofNat (topIdx sch) >
            b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) then
          Int.ofNat (topIdx sch)
        else b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) := by
  unfold ontoFoldBoard peakBoard
  rw [noteBench_hole]

theorem home_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4home = b.sudo_5Board_4home := by
  unfold withMoves
  rfl

theorem on_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on := by
  unfold withMoves
  rfl

theorem to_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_8bench_to = b.sudo_5Board_8bench_to := by
  unfold withMoves
  rfl

theorem ix_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_6marker = b.sudo_5Board_6marker := by
  unfold withMoves
  rfl

theorem ctrl_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
  unfold withMoves
  rfl

theorem mx_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  unfold withMoves
  rfl

theorem ops_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold withMoves
  rfl

theorem slides_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold withMoves
  rfl

theorem strict_withMoves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
  unfold withMoves
  rfl

theorem prep_home (b : Ecbs.Board) (dst : Int) (strip : Array Int) (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨second, hHome⟩ #[] := by
  unfold mulPrep strictBoard mulAimed
  rfl

theorem prep_held (b : Ecbs.Board) (dst : Int) (strip : Array Int) (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨second, hS⟩ false := by
  unfold mulPrep strictBoard mulAimed
  rfl

theorem prep_on (b : Ecbs.Board) (dst : Int) (strip : Array Int) (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_8bench_on = true := by
  unfold mulPrep strictBoard mulAimed
  rfl

theorem prep_to (b : Ecbs.Board) (dst : Int) (strip : Array Int) (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_8bench_to = dst := by
  unfold mulPrep strictBoard mulAimed
  rfl

theorem prep_ix (b : Ecbs.Board) (dst : Int) (strip : Array Int) (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_6marker =
      b.sudo_5Board_6marker := by
  unfold mulPrep strictBoard mulAimed
  rfl

theorem prep_ctrl (b : Ecbs.Board) (dst : Int) (strip : Array Int) (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
  unfold mulPrep strictBoard mulAimed
  rfl

theorem prep_mx (b : Ecbs.Board) (dst : Int) (strip : Array Int) (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  unfold mulPrep strictBoard mulAimed
  rfl

theorem prep_ops (b : Ecbs.Board) (dst : Int) (strip : Array Int) (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold mulPrep strictBoard mulAimed
  rfl

theorem prep_slides (b : Ecbs.Board) (dst : Int) (strip : Array Int) (second peakS : Nat)
    (hS : second < b.sudo_5Board_4held.size)
    (hHome : second < b.sudo_5Board_4home.size) :
    (mulPrep b dst strip second peakS hS hHome).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold mulPrep strictBoard mulAimed
  rfl

/-- What one settle-and-nocopy leaves. The length-`n` bench is `fieldMul` of the
    two factors. `seat` receives the old bench. `second` is cleared. Every other
    home stays, and a home that was `seat` is the old prefix. -/
structure SettleNocopy
    (b b' : Ecbs.Board)
    (lane' lane xs ys : List Nat)
    (dst first second seat : Nat)
    (m ctrl mx cOps n k moves slides peak peakS hole bench : Nat) (mir : Bool) : Prop where
  mul_ok : Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
      false false mir = .ok b'
  bench_eq : b'.sudo_5Board_5bench = embed lane'
  lane_eq : lane' = laneFold n (n - k) (nocopySchool n bench xs ys mir)
  lane_len : lane'.length = bench
  take_eq : lane'.take n =
      if mir then mirrorTrits (fieldMul n k bench xs ys) else fieldMul n k bench xs ys
  tail : ∀ i, n ≤ i → ∀ hi : i < lane'.length, lane'[i] = 0
  mon : b'.sudo_5Board_9marker_on = true
  ix : b'.sudo_5Board_6marker = Int.ofNat (m + 1)
  ctrl : b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2)
  mx : b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx (m + 2))
  opsSz : b'.sudo_5Board_4cost.sudo_5Costs_3ops.size =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  ops0 : ∀ h : 0 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[0]'h = Int.ofNat (cOps + 1)
  ops1 : ∀ h1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(by rw [opsSz]; exact h1) =
        b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1
  ops4 : ∀ h4 : 4 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      b'.sudo_5Board_4cost.sudo_5Costs_3ops[4]'(by rw [opsSz]; exact h4) =
        b.sudo_5Board_4cost.sudo_5Costs_3ops[4]'h4
  on : b'.sudo_5Board_8bench_on = true
  to_eq : b'.sudo_5Board_8bench_to = ((dst : Nat) : Int)
  tier : b'.sudo_5Board_1t = b.sudo_5Board_1t
  moves_eq : b'.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (nocopyCharge n k moves bench xs ys lane mir)
  slides_eq : b'.sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (slides + 2 * pegCount (lane.take n))
  peak_eq : b'.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int)
  strict_eq : b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int)
  hole_eq : b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      Int.ofNat (raisedHole hole (topIdx (nocopySchool n bench xs ys mir)))
  heldSz : b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size
  homeSz : b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size
  clearedH : ∀ h : second < b'.sudo_5Board_4held.size,
      b'.sudo_5Board_4held[second]'h = false
  clearedA : ∀ h : second < b'.sudo_5Board_4home.size,
      b'.sudo_5Board_4home[second]'h = (#[] : Array Int)
  stayH : ∀ j, j ≠ second → ∀ hj : j < b.sudo_5Board_4held.size,
      ∀ hj' : j < b'.sudo_5Board_4held.size,
      b'.sudo_5Board_4held[j]'hj' =
        if j = seat then true else b.sudo_5Board_4held[j]'hj
  stayA : ∀ j, j ≠ second → ∀ hj : j < b.sudo_5Board_4home.size,
      ∀ hj' : j < b'.sudo_5Board_4home.size,
      b'.sudo_5Board_4home[j]'hj' =
        if j = seat then embed (lane.take n) else b.sudo_5Board_4home[j]'hj

/-- Settle a bench aimed at `seat`, then a nocopy multiply. The new bench prefix
    is `fieldMul` of the two homes. Used for the new bottom and for `F · v`. -/
theorem settle_nocopy (b : Ecbs.Board) (dst first second seat : Nat)
    (xs ys lane : List Nat)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (hSeatH : seat < b.sudo_5Board_4home.size)
    (hSeatD : seat < b.sudo_5Board_4held.size)
    (hFH : first < b.sudo_5Board_4home.size)
    (hFD : first < b.sudo_5Board_4held.size)
    (hSH : second < b.sudo_5Board_4home.size)
    (hSD : second < b.sudo_5Board_4held.size)
    (hHeldF : b.sudo_5Board_4held[first] = true)
    (hArrF : b.sudo_5Board_4home[first] = embed xs)
    (hHeldS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[seat] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hne : first ≠ second) (hneSeatF : seat ≠ first) (hneSeatS : seat ≠ second)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs) (hysT : allTritList ys)
    (mir : Bool)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1) +
        3 * (bench - n))) :
    ∃ b' lane' peak' strict',
      SettleNocopy b b' lane' lane xs ys dst first second seat
        m ctrl mx cOps n k moves slides peak' strict' hole bench mir := by
  let feed := markerUpFeed b m ctrl mx
  let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hops
  let bU := bumpOp feed 0 cOps hopsF
  let hHU : seat < bU.sudo_5Board_4home.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hSeatH
  let hDU : seat < bU.sudo_5Board_4held.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hSeatD
  have hflag := off_marker_else b dst first second seat lane m ctrl mx script cOps n
      moves slides peak false mir hmk hon hto hm hc hx hscript hbound hfitMk hfitC hfit2
      hn hops hop0 hfops hSeatH hSeatD h7 hempty hbench hposL hnle hzero hf hfitL
      hmoves hslides hpeak hpeg hfitM hfitS
  let mvS := moves + 2 * pegCount (lane.take n)
  let bS := markerOn (settleBoard bU seat hHU hDU lane n moves slides peak)
  have hinS : HomeIn bU seat := ⟨hHU, hDU⟩
  let peakIn := raisedPeak peak (countHeld (bU.sudo_5Board_4held.set ⟨seat, hDU⟩ true) 7)
  have hcostS : bS.sudo_5Board_4cost =
      (settleBoard bU seat hHU hDU lane n moves slides peak).sudo_5Board_4cost := by
    dsimp [bS, markerOn]
  have hpeakBd : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (peakIn : Int) := by
    have hpeakU : bU.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
      simp [bU, bumpOp, feed, markerUpFeed, hpeak]
    rw [hcostS, settle_peak_eq bU seat hinS lane n moves slides peak hpeakU]
    simp [peakIn, raisedPeak, ofNat_eq_natCast]
  have hmovesS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    rw [hcostS, settle_moves_eq bU seat hinS lane n moves slides peak]
    dsimp [mvS]
  have hslidesS : bS.sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (slides + 2 * pegCount (lane.take n)) := by
    rw [hcostS, settle_slides_eq bU seat hinS lane n moves slides peak]
  have hoffS : bS.sudo_5Board_8bench_on = false := by
    rw [markerOn_on]
    exact settle_bench_off bU seat ⟨hHU, hDU⟩ lane n moves slides peak
  have htierU : bU.sudo_5Board_1t = b.sudo_5Board_1t := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hhomeU : bU.sudo_5Board_4home = b.sudo_5Board_4home := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hheldU : bU.sudo_5Board_4held = b.sudo_5Board_4held := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
  have hhomeS : bS.sudo_5Board_4home =
      (settleBoard bU seat hHU hDU lane n moves slides peak).sudo_5Board_4home := by
    dsimp [bS, markerOn]
  have hheldS0 : bS.sudo_5Board_4held =
      (settleBoard bU seat hHU hDU lane n moves slides peak).sudo_5Board_4held := by
    dsimp [bS, markerOn]
  have htierS : bS.sudo_5Board_1t =
      (settleBoard bU seat hHU hDU lane n moves slides peak).sudo_5Board_1t := by
    dsimp [bS, markerOn]
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    rw [htierS, settle_tier_eq bU seat hinS lane n moves slides peak, htierU, hbl]
  have hIxU : bU.sudo_5Board_6marker = Int.ofNat (m + 1) := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have hIxS : bS.sudo_5Board_6marker = Int.ofNat (m + 1) := by
    rw [show bS.sudo_5Board_6marker =
        (settleBoard bU seat hHU hDU lane n moves slides peak).sudo_5Board_6marker from by
          dsimp [bS, markerOn],
      settle_ix_eq bU seat hinS lane n moves slides peak, hIxU]
  have hctrlU : bU.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have hctrlS : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
    rw [hcostS, settle_ctrl_eq bU seat hinS lane n moves slides peak, hctrlU]
  have hmxU : bU.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx (m + 2)) := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have hmxS : bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx (m + 2)) := by
    rw [hcostS, settle_mx_eq bU seat hinS lane n moves slides peak, hmxU]
  have hopsS : bS.sudo_5Board_4cost.sudo_5Costs_3ops =
      bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
    rw [show bS.sudo_5Board_4cost.sudo_5Costs_3ops =
        (settleBoard bU seat hHU hDU lane n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops
        from by dsimp [bS, markerOn],
      settle_ops bU seat hinS lane n moves slides peak]
  have hstrictU : bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
    exact hpeakS
  have hstrictS : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    rw [hcostS, settle_strict_eq bU seat hinS lane n moves slides peak, hstrictU]
  have hholeU : bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    dsimp [bU, bumpOp, feed, markerUpFeed]
    exact hhole
  have hholeS : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [hcostS, settle_hole_eq bU seat hinS lane n moves slides peak, hholeU]
  have hFirstD : first < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hFD
  have hFirstH : first < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU seat hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hFH
  have hHeldFirst : bS.sudo_5Board_4held[first]'(hFirstD) = true := by
    have hset := settle_held_eq bU seat hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) first hFirstD
    rw [Array.getElem_set_ne (h := hneSeatF)] at hget
    have hBU : first < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hFD
    exact (hget.trans (idx_eq hheldU first hBU)).trans hHeldF
  have hHomeFirst : bS.sudo_5Board_4home[first]'(hFirstH) = embed xs := by
    have hset := settle_home_eq bU seat hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) first hFirstH
    rw [Array.getElem_set_ne (h := hneSeatF)] at hget
    have hBU : first < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact hFH
    exact (hget.trans (idx_eq hhomeU first hBU)).trans hArrF
  have hSecD : second < bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n moves slides peak, Array.size_set, hheldU]
    exact hSD
  have hSecH : second < bS.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU seat hinS lane n moves slides peak, Array.size_set, hhomeU]
    exact hSH
  have hHeldSec : bS.sudo_5Board_4held[second]'(hSecD) = true := by
    have hset := settle_held_eq bU seat hinS lane n moves slides peak
    have hget := idx_eq (hheldS0.trans hset) second hSecD
    rw [Array.getElem_set_ne (h := hneSeatS)] at hget
    have hBU : second < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hSD
    exact (hget.trans (idx_eq hheldU second hBU)).trans hHeldS
  have hHomeSec : bS.sudo_5Board_4home[second]'(hSecH) = embed ys := by
    have hset := settle_home_eq bU seat hinS lane n moves slides peak
    have hget := idx_eq (hhomeS.trans hset) second hSecH
    rw [Array.getElem_set_ne (h := hneSeatS)] at hget
    have hBU : second < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact hSH
    exact (hget.trans (idx_eq hhomeU second hBU)).trans hYs
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n moves slides peak, Array.size_set, hheldU]
    exact h7
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [htierS, settle_tier_eq bU seat hinS lane n moves slides peak, htierU, hn]
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    rw [htierS, settle_tier_eq bU seat hinS lane n moves slides peak, htierU, hw]
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    rw [htierS, settle_tier_eq bU seat hinS lane n moves slides peak, htierU, hh]
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    rw [htierS, settle_tier_eq bU seat hinS lane n moves slides peak, htierU, hr]
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    rw [htierS, settle_tier_eq bU seat hinS lane n moves slides peak, htierU, hk]
  let pad := List.replicate bench 0
  let sch := school n xs ys pad mir
  let mvN := mvS + schoolMoves xs ys n n
  have hOff := nocopy_else_off bS dst first second xs ys n mvS peakS bench mir
      hoffS hblS hFirstD hFirstH hHeldFirst hHomeFirst hSecD hSecH hHeldSec hHomeSec
      h7S hne hn0 hnS hlenx hleny hf hmovesS hstrictS hspan hxsT hfi hfm
  let bP := mulPrep bS ((dst : Nat) : Int) (embed pad) second peakS hSecD hSecH
  let bFold := withMoves bP (Int.ofNat mvN)
  have hma : Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
      ((second : Nat) : Int) false false mir bS =
      mulAfter (Int.ofNat 0, (bFold, embed sch)) := by
    simpa [bFold, bP, sch, pad, mvN] using hOff
  have hschLen : sch.length = bench := by
    simpa [sch, pad, List.length_replicate] using school_length xs ys pad mir n
  have hschT : allTritList sch :=
    school_trits xs ys pad mir n
      (by
        intro x hx
        have hx' : ¬ bench = 0 ∧ x = 0 := by simpa [pad, List.mem_replicate] using hx
        omega)
      (by
        intro i hi
        rw [show pad.length = bench by simp [pad]]
        have hi' : i ≤ n - 1 := Nat.le_sub_one_of_lt hi
        have hle : i + (n - 1) ≤ 2 * (n - 1) := by
          rw [Nat.two_mul]
          exact Nat.add_le_add_right hi' (n - 1)
        exact Nat.lt_of_le_of_lt hle hspan)
  have hmB : bFold.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvN := by
    simp [bFold, withMoves]
  have hpeakB : bFold.sudo_5Board_4cost.sudo_5Costs_4peak = (peakIn : Int) := by
    rw [show bFold.sudo_5Board_4cost.sudo_5Costs_4peak = bP.sudo_5Board_4cost.sudo_5Costs_4peak
        from by simp [bFold, peak_withMoves], mulPrep_peak, hpeakBd]
  have hholeB : bFold.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    rw [show bFold.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        bP.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole from by
          simp [bFold, hole_withMoves], mulPrep_hole, hholeS]
  have h7B : 7 ≤ bFold.sudo_5Board_4held.size := by
    rw [show bFold.sudo_5Board_4held = bP.sudo_5Board_4held from by simp [bFold, held_withMoves],
      prep_held, Array.size_set]
    exact h7S
  have hfitF : FitsLen (mvN + 3 * (sch.length - n)) := by
    rw [hschLen]
    refine FitsLen.of_le hfold ?_
    have hsch : schoolMoves xs ys n n ≤ n * (n + 1) := schoolMoves_bound xs ys n
    simp only [mvN, mvS]
    omega
  have hOk := mulAfter_ok bFold sch w h r n k mvN hole bench peakIn
      (by rw [hschLen]; exact hfitB) hwS hhS hrS hnS hkS hblS hw0 hh0 hrR hrP hnE hkLe hgap
      hschT hmB hholeB hpeakB h7B (by rw [hschLen]; exact hsm) hnsm hfitF
      (by rw [hschLen]; exact Nat.le_refl bench) (Nat.lt_of_lt_of_le hn0 hnb)
  let bOut := ontoFoldBoard bFold sch n k mvN peakIn
  let lane' := laneFold n (n - k) sch
  have hhomeEq : bOut.sudo_5Board_4home = bS.sudo_5Board_4home.set ⟨second, hSecH⟩ #[] := by
    rw [fold_home bFold sch n k mvN peakIn, home_withMoves, prep_home]
  have hheldEq : bOut.sudo_5Board_4held = bS.sudo_5Board_4held.set ⟨second, hSecD⟩ false := by
    rw [fold_held bFold sch n k mvN peakIn, held_withMoves, prep_held]
  have hhomeSzS : bS.sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
    rw [hhomeS, settle_home_eq bU seat hinS lane n moves slides peak, Array.size_set, hhomeU]
  have hheldSzS : bS.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n moves slides peak, Array.size_set, hheldU]
  have hsetHome : bS.sudo_5Board_4home =
      bU.sudo_5Board_4home.set ⟨seat, hHU⟩ (embed (lane.take n)) := by
    rw [hhomeS, settle_home_eq bU seat hinS lane n moves slides peak]
  have hsetHeld : bS.sudo_5Board_4held =
      bU.sudo_5Board_4held.set ⟨seat, hDU⟩ true := by
    rw [hheldS0, settle_held_eq bU seat hinS lane n moves slides peak]
  let peak' := raisedPeak peakIn (countHeld bFold.sudo_5Board_4held 7)
  let strict' := raisedPeak peakS (countHeld bS.sudo_5Board_4held 7)
  have hschN : sch = nocopySchool n bench xs ys mir := by
    simp [sch, pad, nocopySchool]
  have hposG : 0 < n - k := by
    rw [hgap]
    exact Nat.mul_pos hw0 hrP
  exact ⟨bOut, lane', peak', strict', {
    mul_ok := by rw [hflag, hma, hOk]
    bench_eq := by simpa [lane', sch] using ontoFoldBoard_bench bFold sch n k mvN peakIn
    lane_eq := by simp [lane', hschN]
    lane_len := by
      have hle : n ≤ sch.length := by rw [hschLen]; exact hnb
      rw [show lane' = laneFold n (n - k) sch from rfl, laneFold_length n (n - k) sch hle,
        hschLen]
    take_eq := by
      cases mir with
      | false =>
          simpa [lane', sch, pad, nocopySchool] using zero_school_mul n k bench xs ys
      | true =>
          have hmir := fformMir_mul n k bench xs ys hxsT hysT
          simpa [lane', sch, pad, fformMir, nocopySchool] using hmir
    tail := by
      intro i hi hii
      have hle : n ≤ sch.length := by rw [hschLen]; exact hnb
      have hlenL := laneFold_length n (n - k) sch hle
      have hiiS : i < sch.length := by rw [← hlenL]; exact hii
      have hcof := laneFold_high n (n - k) sch i hn0 hposG hle hi hiiS
      rw [coeff_eq_get (laneFold n (n - k) sch) i (by rw [hlenL]; exact hiiS)] at hcof
      exact hcof
    mon := by rw [fold_marker bFold sch n k mvN peakIn, marker_withMoves, mulPrep_marker,
      markerOn_flag]
    ix := by rw [fold_ix bFold sch n k mvN peakIn, ix_withMoves, prep_ix, hIxS]
    ctrl := by rw [fold_ctrl bFold sch n k mvN peakIn, ctrl_withMoves, prep_ctrl, hctrlS]
    mx := by rw [fold_mx bFold sch n k mvN peakIn, mx_withMoves, prep_mx, hmxS]
    opsSz := by
      rw [show bOut.sudo_5Board_4cost.sudo_5Costs_3ops.size =
          bFold.sudo_5Board_4cost.sudo_5Costs_3ops.size from by rw [fold_ops]]
      rw [show bFold.sudo_5Board_4cost.sudo_5Costs_3ops =
          bP.sudo_5Board_4cost.sudo_5Costs_3ops from by rw [ops_withMoves], prep_ops, hopsS]
      simp [bU, bumpOp, feed, markerUpFeed]
    ops0 := by
      intro h
      have hopsEq : bOut.sudo_5Board_4cost.sudo_5Costs_3ops =
          bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
        rw [fold_ops, ops_withMoves, prep_ops, hopsS]
      have hget := idx_eq hopsEq 0 h
      rw [hget]
      have hset := bumpOp_ops feed 0 cOps hopsF
      have hUops : bU.sudo_5Board_4cost.sudo_5Costs_3ops =
          feed.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hopsF⟩ (Int.ofNat (cOps + 1)) := hset
      have hopsU : 0 < bU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hopsEq] at h
        exact h
      have hread := idx_eq hUops 0 hopsU
      rw [hread]
      simp [Array.getElem_set]
    ops1 := by
      intro h1
      have hopsEq : bOut.sudo_5Board_4cost.sudo_5Costs_3ops =
          bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
        rw [fold_ops, ops_withMoves, prep_ops, hopsS]
      have h1U : 1 < bU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [← hopsEq]
        rw [show bOut.sudo_5Board_4cost.sudo_5Costs_3ops.size =
            b.sudo_5Board_4cost.sudo_5Costs_3ops.size from by
          rw [show bOut.sudo_5Board_4cost.sudo_5Costs_3ops.size =
              bFold.sudo_5Board_4cost.sudo_5Costs_3ops.size from by rw [fold_ops]]
          rw [show bFold.sudo_5Board_4cost.sudo_5Costs_3ops =
              bP.sudo_5Board_4cost.sudo_5Costs_3ops from by rw [ops_withMoves], prep_ops, hopsS]
          simp [bU, bumpOp, feed, markerUpFeed]]
        exact h1
      have hget := idx_eq hopsEq 1 (by rw [hopsEq]; exact h1U)
      rw [hget]
      have hfeed : feed.sudo_5Board_4cost.sudo_5Costs_3ops =
          b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [feed, markerUpFeed]
      have h1F : 1 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hfeed]; exact h1
      have hkeep := bumpOp_other feed 0 cOps 1 hopsF h1F (by decide)
      have hU1 : bU.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1U =
          feed.sudo_5Board_4cost.sudo_5Costs_3ops[1]'h1F := hkeep
      rw [hU1]
      simp [hfeed]
    ops4 := by
      intro h4
      have hopsEq : bOut.sudo_5Board_4cost.sudo_5Costs_3ops =
          bU.sudo_5Board_4cost.sudo_5Costs_3ops := by
        rw [fold_ops, ops_withMoves, prep_ops, hopsS]
      have h4U : 4 < bU.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [← hopsEq]
        rw [show bOut.sudo_5Board_4cost.sudo_5Costs_3ops.size =
            b.sudo_5Board_4cost.sudo_5Costs_3ops.size from by
          rw [show bOut.sudo_5Board_4cost.sudo_5Costs_3ops.size =
              bFold.sudo_5Board_4cost.sudo_5Costs_3ops.size from by rw [fold_ops]]
          rw [show bFold.sudo_5Board_4cost.sudo_5Costs_3ops =
              bP.sudo_5Board_4cost.sudo_5Costs_3ops from by rw [ops_withMoves], prep_ops, hopsS]
          simp [bU, bumpOp, feed, markerUpFeed]]
        exact h4
      have hget := idx_eq hopsEq 4 (by rw [hopsEq]; exact h4U)
      rw [hget]
      have hfeed : feed.sudo_5Board_4cost.sudo_5Costs_3ops =
          b.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [feed, markerUpFeed]
      have h4F : 4 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
        rw [hfeed]; exact h4
      have hkeep := bumpOp_other feed 0 cOps 4 hopsF h4F (by decide)
      have hU4 : bU.sudo_5Board_4cost.sudo_5Costs_3ops[4]'h4U =
          feed.sudo_5Board_4cost.sudo_5Costs_3ops[4]'h4F := hkeep
      rw [hU4]
      simp [hfeed]
    on := by rw [fold_on bFold sch n k mvN peakIn, on_withMoves, prep_on]
    to_eq := by rw [fold_to bFold sch n k mvN peakIn, to_withMoves, prep_to]
    tier := by rw [fold_tier bFold sch n k mvN peakIn, tier_withMoves, mulPrep_tier, htierS,
      settle_tier_eq bU seat hinS lane n moves slides peak, htierU]
    moves_eq := by
      rw [fold_moves bFold sch n k mvN peakIn]
      simp [nocopyCharge, mvN, mvS, hschN]
    slides_eq := by rw [fold_slides bFold sch n k mvN peakIn, slides_withMoves, prep_slides,
      hslidesS]
    peak_eq := by
      simpa [peak', ofNat_eq_natCast] using
        fold_peak_rise bFold sch n k mvN peakIn
    strict_eq := by
      rw [fold_strict bFold sch n k mvN peakIn, strict_withMoves]
      simp [bP, mulPrep, strictBoard, mulAimed, raisedPeak, strict', hstrictS,
        ofNat_eq_natCast]
    hole_eq := by
      rw [fold_hole bFold sch n k mvN peakIn, hholeB, hschN]
      by_cases hlt : hole < topIdx (nocopySchool n bench xs ys mir)
      · have hdec : decide (Int.ofNat (topIdx (nocopySchool n bench xs ys mir)) > Int.ofNat hole) =
            true := by
          rw [decide_eq_true_eq]
          exact (ofNat_lt_iff hole _).mpr hlt
        rw [hdec, if_pos rfl, raisedHole, if_pos hlt]
      · have hdec : decide (Int.ofNat (topIdx (nocopySchool n bench xs ys mir)) > Int.ofNat hole) =
            false := by
          rw [decide_eq_false_iff_not]
          intro hgt
          exact hlt ((ofNat_lt_iff hole _).mp hgt)
        rw [hdec, if_neg (by decide), raisedHole, if_neg hlt]
    heldSz := by rw [hheldEq, Array.size_set, hheldSzS]
    homeSz := by rw [hhomeEq, Array.size_set, hhomeSzS]
    clearedH := by
      intro h
      have hget := idx_eq hheldEq second h
      rw [hget]
      simp [Array.getElem_set]
    clearedA := by
      intro h
      have hget := idx_eq hhomeEq second h
      rw [hget]
      simp [Array.getElem_set]
    stayH := by
      intro j hneJ hj hj'
      have hget := idx_eq hheldEq j hj'
      rw [Array.getElem_set_ne (h := Ne.symm hneJ)] at hget
      by_cases hjs : j = seat
      · subst hjs
        have hSz : j < bS.sudo_5Board_4held.size := by rw [hheldSzS]; exact hj
        have hread := idx_eq hsetHeld j hSz
        rw [hget, hread]
        simp [Array.getElem_set]
      · have hSz : j < bS.sudo_5Board_4held.size := by rw [hheldSzS]; exact hj
        have hread := idx_eq hsetHeld j hSz
        rw [Array.getElem_set_ne (h := Ne.symm hjs)] at hread
        have hBU : j < bU.sudo_5Board_4held.size := by rw [hheldU]; exact hj
        rw [hget, hread, idx_eq hheldU j hBU]
        simp [hjs]
    stayA := by
      intro j hneJ hj hj'
      have hget := idx_eq hhomeEq j hj'
      rw [Array.getElem_set_ne (h := Ne.symm hneJ)] at hget
      by_cases hjs : j = seat
      · subst hjs
        have hSz : j < bS.sudo_5Board_4home.size := by rw [hhomeSzS]; exact hj
        have hread := idx_eq hsetHome j hSz
        rw [hget, hread]
        simp [Array.getElem_set]
      · have hSz : j < bS.sudo_5Board_4home.size := by rw [hhomeSzS]; exact hj
        have hread := idx_eq hsetHome j hSz
        rw [Array.getElem_set_ne (h := Ne.symm hjs)] at hread
        have hBU : j < bU.sudo_5Board_4home.size := by rw [hhomeU]; exact hj
        rw [hget, hread, idx_eq hhomeU j hBU]
        simp [hjs]
  }⟩

/-- `v · (v²Z)` is SPEC.md §3 R7's new bottom. -/
theorem bottom_prod (n k bench : Nat) (v z : List Nat) :
    fieldMul n k bench v (fieldMul n k bench (fieldMul n k bench v v) z) =
      fformBottom n k bench v z := by
  unfold fformBottom
  rfl

theorem prod_trits (n k bench : Nat) (xs ys : List Nat)
    (hspan : 2 * (n - 1) < bench) (hn : n ≤ bench) :
    allTritList (fieldMul n k bench xs ys) := by
  have hrep : allTritList (List.replicate bench 0) := by
    intro x hx
    simp [List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩
    exact Nat.zero_le _
  have hwide : ∀ i, i < n → i + (n - 1) < (List.replicate bench 0).length := by
    intro i hi
    rw [List.length_replicate]
    have : i + (n - 1) ≤ 2 * (n - 1) := by omega
    omega
  have hsch := school_trits xs ys (List.replicate bench 0) false n hrep hwide
  have hlen : (school n xs ys (List.replicate bench 0) false).length = bench := by
    simpa [List.length_replicate] using school_length xs ys (List.replicate bench 0) false n
  have hfold := laneFold_trits n (n - k)
    (school n xs ys (List.replicate bench 0) false) hsch (Nat.sub_le _ _) (by rw [hlen]; exact hn)
  simpa [fieldMul, laneFold] using allTritList_take hfold n

/-- The new bottom on the board. The bench was aimed at `gap`, so that prefix is
    settled there, and the run times `v²Z` is the new bench. SPEC.md §3 R7 line 152. -/
theorem fform_new_bottom (b : Ecbs.Board) (across bot gap : Nat) (v z lane : List Nat)
    (m ctrl mx script cOps n k w h r moves slides hole peak peakS bench : Nat)
    (hSeatH : gap < b.sudo_5Board_4home.size)
    (hSeatD : gap < b.sudo_5Board_4held.size)
    (hFH : across < b.sudo_5Board_4home.size)
    (hFD : across < b.sudo_5Board_4held.size)
    (hSH : bot < b.sudo_5Board_4home.size)
    (hSD : bot < b.sudo_5Board_4held.size)
    (hHeldF : b.sudo_5Board_4held[across] = true)
    (hArrF : b.sudo_5Board_4home[across] = embed v)
    (hHeldS : b.sudo_5Board_4held[bot] = true)
    (hYs : b.sudo_5Board_4home[bot] =
      embed (fieldMul n k bench (fieldMul n k bench v v) z))
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (gap : Int))
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[gap] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hposL : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hne : across ≠ bot) (hneSeatF : gap ≠ across) (hneSeatS : gap ≠ bot)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hlenv : v.length = n)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hv : allTritList v)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1)))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen ((moves + 2 * pegCount (lane.take n)) + n * (n + 1) +
        3 * (bench - n))) :
    ∃ b' lane' peak' strict',
      SettleNocopy b b' lane' lane v
        (fieldMul n k bench (fieldMul n k bench v v) z)
        bot across bot gap m ctrl mx cOps n k moves slides peak' strict' hole bench false ∧
      lane'.take n = fformBottom n k bench v z := by
  have hys : allTritList (fieldMul n k bench (fieldMul n k bench v v) z) :=
    prod_trits n k bench _ z hspan hnb
  have hleny : (fieldMul n k bench (fieldMul n k bench v v) z).length = n :=
    fieldMul_len n k bench _ _ hnb
  obtain ⟨b', lane', peak', strict', h⟩ := settle_nocopy b bot across bot gap v
      (fieldMul n k bench (fieldMul n k bench v v) z) lane
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      hSeatH hSeatD hFH hFD hSH hSD hHeldF hArrF hHeldS hYs
      hmk hon hto hm hc hx hscript hbound hfitMk hfitC hfit2 hn hops hop0 hfops
      h7 hempty hbench hposL hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
      hbl hne hneSeatF hneSeatS hn0 hnb hlenv hleny hpeakS hspan hv hys
      false hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm hfitB hfold
  refine ⟨b', lane', peak', strict', h, ?_⟩
  rw [h.take_eq, if_neg (fun h : false = true => Bool.noConfusion h), bottom_prod]

end EcbsLink2.Link2
