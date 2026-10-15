/-
  A live white or red cell with a nonempty run. The emitted `chord_tail` is
  obtained from `chord_gap_mul`, the square, the across/bottom settle, the
  take and the mirror, the onto multiply, and `chord_up_slide`. Each board is
  abstract. SPEC.md §3 R7 line 156.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.ChordTail
import EcbsLink2.Link2.ChordSettle
import EcbsLink2.Link2.ChordWhite
import EcbsLink2.Link2.BenchSettle
import EcbsLink2.Link2.ChordTake
import EcbsLink2.Link2.ChordUp
import EcbsLink2.Link2.MulOnto
import EcbsLink2.Link2.WalkLive
import Lean.Elab.Tactic.Conv.Basic

open Lean Meta Elab Tactic Conv in
elab "zeta1" : conv => do
  let lhs ← getLhs
  match lhs with
  | .letE _ _ val body _ => changeLhs (body.instantiate1 val)
  | _ => throwError "zeta1: not a let"

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- New x of SPEC.md §3 R7 line 156: slope² + 1 + first x − run. -/
def chordX3 (n k bench : Nat) (slope accX run : List Nat) : List Nat :=
  fieldAdd n (fieldAdd n (fieldAdd n (fieldMul n k bench slope slope) (whiteHole0 n)) accX)
    (mirrorTrits run)

/-- New y of SPEC.md §3 R7 line 156: slope · (first x − new x) − first y. -/
def chordY3 (n k bench : Nat) (slope dx y : List Nat) : List Nat :=
  fieldSub n (fieldMul n k bench slope dx) y

def mvGap (moves : Nat) (inv rise : List Nat) (n k bench : Nat) : Nat :=
  mulMovesNo moves inv rise n k bench + pegCount inv +
    2 * pegCount ((gapProduct n k bench inv rise).take n)

def slGap (slides : Nat) (inv rise : List Nat) (n k bench : Nat) : Nat :=
  slides + 2 * pegCount ((gapProduct n k bench inv rise).take n)

def mvSq (moves : Nat) (slope : List Nat) (n k bench : Nat) : Nat :=
  mulMoves moves slope slope n k bench + 1

private theorem ix {α : Type} {a b : Array α} (h : a = b) (i : Nat) (ha : i < a.size) :
    a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

private theorem set_fin {α : Type} (a : Array α) (i : Nat) (h₁ h₂ : i < a.size) (v : α) :
    a.set ⟨i, h₁⟩ v = a.set ⟨i, h₂⟩ v := by
  have : (⟨i, h₁⟩ : Fin a.size) = ⟨i, h₂⟩ := Fin.ext rfl
  rw [this]

theorem benchAdd_held (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (benchAddBoard b arr mv).sudo_5Board_4held = b.sudo_5Board_4held := by
  unfold benchAddBoard withMoves
  rfl

theorem benchAdd_marker (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (benchAddBoard b arr mv).sudo_5Board_6marker = b.sudo_5Board_6marker := by
  unfold benchAddBoard withMoves
  rfl

theorem benchAdd_on (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (benchAddBoard b arr mv).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      (benchAddBoard b arr mv).sudo_5Board_8bench_to = b.sudo_5Board_8bench_to := by
  unfold benchAddBoard withMoves
  exact ⟨rfl, rfl⟩

theorem benchAdd_tier (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (benchAddBoard b arr mv).sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold benchAddBoard withMoves
  rfl

theorem benchAdd_slides (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (benchAddBoard b arr mv).sudo_5Board_4cost.sudo_5Costs_6slides =
      b.sudo_5Board_4cost.sudo_5Costs_6slides := by
  unfold benchAddBoard withMoves
  rfl

theorem benchAdd_peak (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (benchAddBoard b arr mv).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := by
  unfold benchAddBoard withMoves
  rfl

theorem benchAdd_ctrl (b : Ecbs.Board) (arr : Array Int) (mv : Nat) :
    (benchAddBoard b arr mv).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (benchAddBoard b arr mv).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
    (benchAddBoard b arr mv).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
    (benchAddBoard b arr mv).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
    (benchAddBoard b arr mv).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
  unfold benchAddBoard withMoves
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem add_held (b : Ecbs.Board) (home : Nat) (hH : home < b.sudo_5Board_4home.size)
    (arr : Array Int) (mv : Nat) :
    (addBoard b home hH arr mv).sudo_5Board_4held = b.sudo_5Board_4held := by
  unfold addBoard withMoves
  rfl

theorem add_marker (b : Ecbs.Board) (home : Nat) (hH : home < b.sudo_5Board_4home.size)
    (arr : Array Int) (mv : Nat) :
    (addBoard b home hH arr mv).sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      (addBoard b home hH arr mv).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      (addBoard b home hH arr mv).sudo_5Board_1t = b.sudo_5Board_1t ∧
      (addBoard b home hH arr mv).sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      (addBoard b home hH arr mv).sudo_5Board_4cost.sudo_5Costs_4ctrl =
        b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      (addBoard b home hH arr mv).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  unfold addBoard withMoves
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ontoFold_home (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4home = b.sudo_5Board_4home := by
  unfold ontoFoldBoard peakBoard
  simp [noteBench_home]

theorem ontoFold_held (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4held = b.sudo_5Board_4held := by
  unfold ontoFoldBoard peakBoard
  simp [noteBench_held]

theorem ontoFold_on (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      (ontoFoldBoard b sch n k mv peak).sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      (ontoFoldBoard b sch n k mv peak).sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      (ontoFoldBoard b sch n k mv peak).sudo_5Board_1t = b.sudo_5Board_1t ∧
      (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
        b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ontoFold_moves (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mv + foldCharge n (n - k) sch) := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

theorem settle_ix (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_6marker =
      b.sudo_5Board_6marker ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold settleBoard
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A live white or red cell. `walkStep` is the chord of the cubed accumulator. -/
theorem walkStep_live_chord (n k bench : Nat) (baseX baseY preX preY : List Nat)
    (c : Nat) (inv : List Nat) (hc : c = 1 ∨ c = 2)
    (hspec : specInv n k bench (fieldSub n baseX (fieldCube n k bench preX)) = some inv) :
    let accX := fieldCube n k bench preX
    let accY := fieldCube n k bench preY
    let y := if c = 2 then mirrorTrits baseY else baseY
    let run := fieldSub n baseX accX
    let rise := fieldSub n y accY
    let slope := fieldMul n k bench rise inv
    let x3 := chordX3 n k bench slope accX run
    let y3 := chordY3 n k bench slope (fieldSub n accX x3) accY
    walkStep n k bench (baseX, baseY) true (preX, preY) c = some (true, (x3, y3)) := by
  intro accX accY y run rise slope x3 y3
  unfold walkStep
  simp only [ite_true]
  have hc0 : c ≠ 0 := by rcases hc with h | h <;> omega
  rw [if_neg hc0]
  have hcol : ¬ (c ≠ 1 ∧ c ≠ 2) := by
    intro h
    rcases hc with h1 | h2
    · exact h.1 h1
    · exact h.2 h2
  rw [if_neg hcol]
  unfold chordAdd pointCube
  simp only [Prod.fst, Prod.snd]
  rw [hspec]
  rcases hc with h1 | h2
  · simp [h1, accX, accY, y, run, rise, slope, x3, y3, chordX3, chordY3, fieldSub]
  · simp [h2, accX, accY, y, run, rise, slope, x3, y3, chordX3, chordY3, fieldSub]

private theorem gapMul_ix (b : Ecbs.Board) (inv rise : List Nat)
    (n k moves hole bench peak peakS cOps m ctrl mx : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : 6 < b.sudo_5Board_4held.size) (hHomeS : 6 < b.sudo_5Board_4home.size) :
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_6marker =
      Int.ofNat (m + 1) ∧
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_4cost.sudo_5Costs_4ctrl =
      Int.ofNat (ctrl + 2) ∧
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat (max mx (m + 2)) ∧
    (gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) := by
  unfold gapMulBoard mulNoOffBoard markerUpFeed
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Gap times spare, clear, settle. The gap is the slope, the spare is empty,
    and homes other than the gap and the spare stay. -/
theorem gap_settle_lay (b : Ecbs.Board) (inv rise : List Nat)
    (w h r n k moves hole bench slides peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : 5 < b.sudo_5Board_4held.size) (hHome : 5 < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[5] = true)
    (hArr : b.sudo_5Board_4home[5] = embed inv)
    (hS : 6 < b.sudo_5Board_4held.size) (hHomeS : 6 < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[6] = true)
    (hYs : b.sudo_5Board_4home[6] = embed rise)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : inv.length = n) (hleny : rise.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList inv) (hrT : allTritList rise)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1)))
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
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n)))
    (hfitClear : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv))
    (hpeg : FitsLen (2 * pegCount ((gapProduct n k bench inv rise).take n)))
    (hfitSM : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv +
        2 * pegCount ((gapProduct n k bench inv rise).take n)))
    (hfitSS : FitsLen (slides + 2 * pegCount ((gapProduct n k bench inv rise).take n))) :
    let slope := fieldMul n k bench rise inv
    ∃ bS,
      (do
          let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
          let b ← Ecbs.clear b Ecbs.gap
          Ecbs.settle b) = .ok bS ∧
      bS.sudo_5Board_9marker_on = true ∧
      bS.sudo_5Board_8bench_on = false ∧
      bS.sudo_5Board_6marker = Int.ofNat (m + 1) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat (max mx (m + 2)) ∧
      bS.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bS.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (mvGap moves inv rise n k bench) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat (slGap slides inv rise n k bench) ∧
      bS.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      bS.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      (∀ h : 5 < bS.sudo_5Board_4home.size, bS.sudo_5Board_4home[5] = embed slope) ∧
      (∀ h : 5 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[5] = true) ∧
      (∀ h : 6 < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[6] = false) ∧
      (∀ i, i ≠ 5 → i ≠ 6 → ∀ hi : i < b.sudo_5Board_4home.size,
        ∀ hi' : i < bS.sudo_5Board_4home.size, bS.sudo_5Board_4home[i] = b.sudo_5Board_4home[i]) ∧
      (∀ i, i ≠ 5 → i ≠ 6 → ∀ hi : i < b.sudo_5Board_4held.size,
        ∀ hi' : i < bS.sudo_5Board_4held.size, bS.sudo_5Board_4held[i] = b.sudo_5Board_4held[i]) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) ∧
      (∃ peakG strictG holeG,
        bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakG ∧
        bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat strictG ∧
        bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeG) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  intro slope
  have hmul := chord_gap_mul b inv rise w h r n k moves hole bench peak peakS cOps m ctrl mx
    script hmk hoff hm hc hx hscript hbound hfitM hfitC hfit2 hops hop0 hfops hbl hF hHome hHF
    hArr hS hHomeS hHS hYs h7 hn0 hn hlenx hleny hf hmoves hpeak hpeakS hspan hxsT hfi hfm
    hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm hfitB hfold
  let bM := gapMulBoard b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS
  have h5 : 5 < bM.sudo_5Board_4home.size := by
    rw [gapMul_home, Array.size_set]
    exact hHome
  have h5D : 5 < bM.sudo_5Board_4held.size := by
    rw [gapMul_held, Array.size_set]
    exact hF
  have harr5 : bM.sudo_5Board_4home[5] = embed inv := by
    have hEq := gapMul_home (b := b) (inv := inv) (rise := rise) (n := n) (k := k)
      (moves := moves) (hole := hole) (bench := bench) (peak := peak) (peakS := peakS)
      (cOps := cOps) (m := m) (ctrl := ctrl) (mx := mx) hops hS hHomeS
    have h5s : 5 < (b.sudo_5Board_4home.set ⟨6, hHomeS⟩ #[]).size := by
      rw [Array.size_set]; exact hHome
    have htrans : bM.sudo_5Board_4home[5] =
        (b.sudo_5Board_4home.set ⟨6, hHomeS⟩ #[])[5]'(h5s) := by
      cases hEq
      rfl
    rw [htrans]
    have hne : (6 : Nat) ≠ 5 := by decide
    simp [Array.getElem_set, hne, hArr]
  have hheld5 : bM.sudo_5Board_4held[5] = true := by
    have hEq := gapMul_held (b := b) (inv := inv) (rise := rise) (n := n) (k := k)
      (moves := moves) (hole := hole) (bench := bench) (peak := peak) (peakS := peakS)
      (cOps := cOps) (m := m) (ctrl := ctrl) (mx := mx) hops hS hHomeS
    have h5s : 5 < (b.sudo_5Board_4held.set ⟨6, hS⟩ false).size := by
      rw [Array.size_set]; exact hF
    have htrans : bM.sudo_5Board_4held[5] =
        (b.sudo_5Board_4held.set ⟨6, hS⟩ false)[5]'(h5s) := by
      cases hEq
      rfl
    rw [htrans]
    have hne : (6 : Nat) ≠ 5 := by decide
    simp [Array.getElem_set, hne, hHF]
  have hmvM : bM.sudo_5Board_4cost.sudo_5Costs_5moves =
      ((mulMovesNo moves inv rise n k bench) : Int) := by
    rw [gapMul_moves, ofNat_eq_natCast]
  have hfI : FitsLen inv.length := by rw [hlenx]; exact hf
  have hclear := clear_held_refines bM 5 inv (mulMovesNo moves inv rise n k bench)
    h5 h5D hheld5 harr5 hmvM hfI hfitClear
  let mv := mulMovesNo moves inv rise n k bench + pegCount inv
  let bC := { bM with
    sudo_5Board_4home := bM.sudo_5Board_4home.set ⟨5, h5⟩ #[]
    sudo_5Board_4held := bM.sudo_5Board_4held.set ⟨5, h5D⟩ false
    sudo_5Board_4cost := { bM.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat mv } }
  have hmulEq : Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false = .ok bM := by
    simpa [bM, gapMulBoard] using hmul.1
  have hclearEq : Ecbs.clear bM Ecbs.gap = .ok bC := by
    simpa [bC, ofNat_eq_natCast, show Ecbs.gap = ((5 : Nat) : Int) from rfl] using hclear
  let xs := gapProduct n k bench inv rise
  have hnB : n ≤ bench := by omega
  have hlen : xs.length = bench := by
    have hs : (school n inv rise (List.replicate bench 0) false).length = bench := by
      simpa [List.length_replicate] using
        school_length inv rise (List.replicate bench 0) false n
    have hfoldL := laneFold_length n (n - k) (school n inv rise (List.replicate bench 0) false)
      (by rw [hs]; exact hnB)
    simpa [xs, gapProduct, hfoldL, hs] using hfoldL
  have hpos : 0 < xs.length := by rw [hlen]; omega
  have hnle : n ≤ xs.length := by rw [hlen]; exact hnB
  have hgap0 : 0 < n - k := by rw [hgap]; exact Nat.mul_pos hw0 hrP
  have hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0 := by
    intro i hlo hi
    have hiB : i < bench := by rw [hlen] at hi; exact hi
    have hc0 := mul_no_high inv rise n k bench hn0 hgap0 i hlo hiB
    rw [← coeff_eq_get xs i hi]
    simpa [xs, gapProduct] using hc0
  have hfitL : FitsLen xs.length := by rw [hlen]; exact hfitB
  have hH : 5 < bC.sudo_5Board_4home.size := by simp [bC, Array.size_set, h5]
  have hD : 5 < bC.sudo_5Board_4held.size := by simp [bC, Array.size_set, h5D]
  have h7C : 7 ≤ bC.sudo_5Board_4held.size := by
    simp only [bC, Array.size_set]
    rw [gapMul_held, Array.size_set]
    exact h7
  have hempty : bC.sudo_5Board_4held[5] = false := by simp [bC, Array.getElem_set]
  have hon : bC.sudo_5Board_8bench_on = true := by
    simp only [bC]
    exact (gapMul_bench b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).2.1
  have hto : bC.sudo_5Board_8bench_to = (5 : Int) := by
    simp only [bC]
    exact (gapMul_bench b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).2.2.1
  have hbench : bC.sudo_5Board_5bench = embed xs := by
    simp only [bC, xs, gapProduct]
    exact (gapMul_bench b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).1
  have hnC : bC.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp only [bC]
    rw [gapMul_tier, hn]
  have hmovesC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by simp [bC]
  have hslC : bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simp only [bC]
    rw [gapMul_slides, hslides]
  let peakC := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨6, hS⟩ false) 7)
  have hpkC : bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakC := by
    simp only [bC, peakC]
    exact gapMul_peak b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS
  have hset := settle_refines bC 5 xs n mv slides peakC hH hD h7C hon hto hempty hbench
    hnC hpos hnle hzero hf hfitL hmovesC hslC hpkC hpeg hfitSM hfitSS
  let bS := settleBoard bC 5 hH hD xs n mv slides peakC
  have hslope : xs.take n = slope := by
    have hpre : xs.take n = fieldMul n k bench inv rise := by
      simpa [xs, gapProduct] using mul_no_prefix n k bench inv rise
    rw [hpre]
    simpa [slope] using (slope_mul_swap n k bench rise inv hrT hxsT).symm
  have hmix := gapMul_ix b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS
  have hsix := settle_ix bC 5 hH hD xs n mv slides peakC
  refine ⟨bS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmulEq, ok_bind, hclearEq, ok_bind]
    simpa [bS, show Ecbs.gap = ((5 : Nat) : Int) from rfl] using hset
  · have hflag : bC.sudo_5Board_9marker_on = true := by
      simp only [bC]
      exact (gapMul_bench b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS).2.2.2
    simpa [bS, hflag] using settle_marker_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC
  · simpa [bS] using settle_bench_off bC 5 ⟨hH, hD⟩ xs n mv slides peakC
  · have hmC : bC.sudo_5Board_6marker = bM.sudo_5Board_6marker := by simp [bC]
    exact hsix.1.trans (hmC.trans hmix.1)
  · have hcC : bC.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        bM.sudo_5Board_4cost.sudo_5Costs_4ctrl := by simp [bC]
    exact hsix.2.1.trans (hcC.trans hmix.2.1)
  · have hxC : bC.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        bM.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by simp [bC]
    exact hsix.2.2.1.trans (hxC.trans hmix.2.2.1)
  · have htC : bC.sudo_5Board_1t = b.sudo_5Board_1t := by
      simp only [bC]
      exact gapMul_tier b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS
    simpa [bS] using (settle_tier_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC).trans htC
  · have hmvS := settle_moves_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC
    simpa [bS, mvGap, mv, hslope, Nat.add_assoc] using hmvS
  · have hslS := settle_slides_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC
    simpa [bS, slGap, hslope] using hslS
  · unfold bS
    rw [settle_home_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC, Array.size_set]
    simp [bC, Array.size_set, bM, gapMul_home]
  · unfold bS
    rw [settle_held_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC, Array.size_set]
    simp [bC, Array.size_set, bM, gapMul_held]
  · intro h5s
    have hh := settle_home_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC
    have hget := ix (by simpa [bS] using hh) 5 (by simpa [bS, hh] using h5s)
    simpa [Array.getElem_set_eq, hslope] using hget
  · intro h5s
    have hh := settle_held_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC
    have hget := ix (by simpa [bS] using hh) 5 (by simpa [bS, hh] using h5s)
    simpa [Array.getElem_set_eq] using hget
  · intro h6s
    have hh := settle_held_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC
    have hget := ix (by simpa [bS] using hh) 6 h6s
    have hne : (5 : Nat) ≠ 6 := by decide
    rw [Array.getElem_set_ne (h := hne)] at hget
    have h6c : 6 < bC.sudo_5Board_4held.size := by
      simpa [bS, hh, Array.size_set] using h6s
    have hpre : bC.sudo_5Board_4held[6]'h6c = false := by
      have hne5 : (5 : Nat) ≠ 6 := by decide
      simp [bC, bM, Array.getElem_set_ne, hne5, gapMul_held, Array.getElem_set_eq]
    exact hget.trans hpre
  · intro i hne5 hne6 hi hi'
    have hh := settle_home_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC
    have hget := ix (by simpa [bS] using hh) i hi'
    have hne : (5 : Nat) ≠ i := hne5.symm
    rw [Array.getElem_set_ne (h := hne)] at hget
    have hic : i < bC.sudo_5Board_4home.size := by
      simpa [bS, hh, Array.size_set] using hi'
    have hpre : bC.sudo_5Board_4home[i]'hic = b.sudo_5Board_4home[i] := by
      have hneG : (5 : Nat) ≠ i := hne5.symm
      have hneS : (6 : Nat) ≠ i := hne6.symm
      simp [bC, bM, Array.getElem_set_ne, hneG, gapMul_home, Array.getElem_set_ne, hneS]
    exact hget.trans hpre
  · intro i hne5 hne6 hi hi'
    have hh := settle_held_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC
    have hget := ix (by simpa [bS] using hh) i hi'
    have hne : (5 : Nat) ≠ i := hne5.symm
    rw [Array.getElem_set_ne (h := hne)] at hget
    have hic : i < bC.sudo_5Board_4held.size := by
      simpa [bS, hh, Array.size_set] using hi'
    have hpre : bC.sudo_5Board_4held[i]'hic = b.sudo_5Board_4held[i] := by
      have hneG : (5 : Nat) ≠ i := hne5.symm
      have hneS : (6 : Nat) ≠ i := hne6.symm
      simp [bC, bM, Array.getElem_set_ne, hneG, gapMul_held, Array.getElem_set_ne, hneS]
    exact hget.trans hpre
  · have hopC : bC.sudo_5Board_4cost.sudo_5Costs_3ops =
        bM.sudo_5Board_4cost.sudo_5Costs_3ops := by simp [bC]
    exact hsix.2.2.2.trans (hopC.trans hmix.2.2.2)
  · let strictG := raisedPeak peakS (countHeld b.sudo_5Board_4held 7)
    let holeG := raisedHole hole (topIdx (school n inv rise (List.replicate bench 0) false))
    let peakG := if peakC < countHeld (bC.sudo_5Board_4held.set ⟨5, hD⟩ true) 7
      then countHeld (bC.sudo_5Board_4held.set ⟨5, hD⟩ true) 7 else peakC
    refine ⟨peakG, strictG, holeG, ?_, ?_, ?_⟩
    · simpa [bS, peakG] using settle_peak_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC hpkC
    · have hst : bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat strictG := by
        simp only [bC, bM, strictG]
        unfold gapMulBoard mulNoOffBoard markerUpFeed
        rfl
      simpa [bS, hst] using settle_strict_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC
    · have hho : bC.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeG := by
        simp only [bC, bM, holeG]
        unfold gapMulBoard mulNoOffBoard markerUpFeed
        rfl
      simpa [bS, hho] using settle_hole_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC
  · have hM := gapMul_high b inv rise n k moves hole bench peak peakS cOps m ctrl mx hops hS hHomeS
    have hC : bC.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        bM.sudo_5Board_4cost.sudo_5Costs_15control_highest := by simp [bC]
    simpa [bS] using
      (settle_high_eq bC 5 ⟨hH, hD⟩ xs n mv slides peakC).trans (hC.trans hM)

/-- The square and the white peg. Homes other than the spare stay.
    The bench prefix is slope² + 1. -/
theorem square_white_lay (b : Ecbs.Board) (slope : List Nat)
    (w h r n k moves hole bench peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitCtrl : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (h5 : 5 < b.sudo_5Board_4held.size) (h5h : 5 < b.sudo_5Board_4home.size)
    (h5t : b.sudo_5Board_4held[5] = true)
    (h5a : b.sudo_5Board_4home[5] = embed slope)
    (h6 : 6 < b.sudo_5Board_4held.size) (h6h : 6 < b.sudo_5Board_4home.size)
    (h6e : b.sudo_5Board_4held[6] = false)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : slope.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (htri : allTritList slope)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount slope + n * (n + 1)))
    (hfitP : FitsLen (moves + pegCount slope))
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
    (hfold : FitsLen (moves + pegCount slope + n * (n + 1) + 3 * (bench - n)))
    (hfitW : FitsLen (mulMoves moves slope slope n k bench + 1)) :
    ∃ bW benchL,
      (do
          let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
          Ecbs.bench_white0 b) = .ok bW ∧
      bW.sudo_5Board_9marker_on = true ∧
      bW.sudo_5Board_8bench_on = true ∧
      bW.sudo_5Board_8bench_to = Ecbs.bottom ∧
      bW.sudo_5Board_6marker = Int.ofNat (m + 1) ∧
      bW.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) ∧
      bW.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max mx (m + 2)) ∧
      bW.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bW.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (mvSq moves slope n k bench) ∧
      bW.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      bW.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      bW.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      bW.sudo_5Board_5bench = embed benchL ∧
      benchL.take n = fieldAdd n (fieldMul n k bench slope slope) (whiteHole0 n) ∧
      benchL.length = bench ∧
      (∀ i, n ≤ i → ∀ hi : i < benchL.length, benchL[i] = 0) ∧
      (∀ i, i ≠ 6 → ∀ hi : i < b.sudo_5Board_4home.size,
        ∀ hi' : i < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[i] = b.sudo_5Board_4home[i]) ∧
      (∀ i, i ≠ 6 → ∀ hi : i < b.sudo_5Board_4held.size,
        ∀ hi' : i < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[i] = b.sudo_5Board_4held[i]) ∧
      (∀ h : 6 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[6] = false) ∧
      bW.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) ∧
      (∃ peakG strictG holeG,
        bW.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakG ∧
        bW.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat strictG ∧
        bW.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeG) ∧
      bW.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  let feed := markerUpFeed b m ctrl mx
  have hup := mul_copy_up_eq b 2 5 5 slope slope w h r n k moves hole bench peak peakS cOps
    m ctrl mx script hmk hoff hm hc hx hscript hbound hfitM hfitCtrl hfit2 hops hop0 hfops
    hbl h5 h5h h5t h5a h5 h5h h5t h5a h6 h6h h6e h7 (by decide) (by decide) hn0 hn hlen hlen
    hf hmoves hpeak hpeakS hspan htri hfi hfm hfitP hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh
    hr hk hsm hnsm hfitB hfold
  have href := mul_refines feed 2 5 5 slope slope w h r n k moves hole bench peak peakS cOps
    (by simp [feed, markerUpFeed]) hoff
    (by simpa [feed, markerUpFeed] using hops)
    (by simpa [feed, markerUpFeed] using hop0) hfops
    (by simp [feed, markerUpFeed, hbl])
    (by simp [feed, markerUpFeed]; exact h5) (by simp [feed, markerUpFeed]; exact h5h)
    (by simp [feed, markerUpFeed, h5t]) (by simp [feed, markerUpFeed, h5a])
    (by simp [feed, markerUpFeed]; exact h5) (by simp [feed, markerUpFeed]; exact h5h)
    (by simp [feed, markerUpFeed, h5t]) (by simp [feed, markerUpFeed, h5a])
    (by simp [feed, markerUpFeed]; exact h6) (by simp [feed, markerUpFeed]; exact h6h)
    (by simp [feed, markerUpFeed, h6e]) (by simp [feed, markerUpFeed]; exact h7)
    (by decide) (by decide) hn0 (by simp [feed, markerUpFeed, hn]) hlen hlen hf
    (by simp [feed, markerUpFeed, hmoves]) (by simp [feed, markerUpFeed, hpeak])
    (by simp [feed, markerUpFeed, hpeakS]) hfitP hspan htri hfi hfm ⟨hw0, hh0, hrR, hrP, hnE, hkLe, hgap⟩
    (by simp [feed, markerUpFeed, hw]) (by simp [feed, markerUpFeed, hh])
    (by simp [feed, markerUpFeed, hr]) (by simp [feed, markerUpFeed, hk])
    (by simp [feed, markerUpFeed, hhole]) hsm hnsm hfitB hfold
  rcases href with ⟨b0, hb, hon, hto, hbench, htake, hhigh, hmv, hpk, hsl, ht, hsz, hheld,
      _h5, hkeep, _hmk, hopsR, hstrict, hholeR, hmark, hctrl, hmxR, hhi0⟩
  let bF := { b0 with sudo_5Board_9marker_on := true }
  have hmulF : Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false = .ok bF := by
    rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl, show Ecbs.gap = ((5 : Nat) : Int) from rfl,
      hup, hb, ok_bind, pure_eq_ok]
  let sch := school n slope slope (List.replicate bench 0) false
  let folded := laneFold n (n - k) sch
  have hlenS : sch.length = bench := by
    simpa [sch, List.length_replicate] using school_length slope slope (List.replicate bench 0) false n
  have hnB : n ≤ bench := by omega
  have hlenF : folded.length = bench := by
    rw [show folded.length = sch.length from laneFold_length n (n - k) sch (by rw [hlenS]; exact hnB),
      hlenS]
  have hpos : 0 < folded.length := by rw [hlenF]; omega
  have hhead : folded[0]'(hpos) ≤ 2 := by
    have htakeL : folded.take n = fieldMul n k bench slope slope := by
      simpa [folded, sch] using htake
    have hlenM : (fieldMul n k bench slope slope).length = n := by
      rw [← htakeL, List.length_take, hlenF]; omega
    have htriF : allTritList (fieldMul n k bench slope slope) :=
      fieldMul_span_trits n k bench slope slope hspan hnB
    have hm0 : 0 < (fieldMul n k bench slope slope).length := by rw [hlenM]; exact hn0
    have hc0 : (fieldMul n k bench slope slope)[0]'(hm0) ≤ 2 :=
      htriF _ (List.getElem_mem hm0)
    have hget : folded[0]'(hpos) = (fieldMul n k bench slope slope)[0]'(hm0) := by
      have ht0 : (folded.take n)[0]'(by rw [List.length_take, hlenF]; omega) = folded[0] := by
        simp [List.getElem_take]
      simpa [htakeL] using ht0.symm
    rw [hget]
    exact hc0
  have hstep := bench_white0_step bF folded (mulMoves moves slope slope n k bench) hpos
    (by simpa [bF, folded] using hbench)
    (by simpa [bF, ofNat_eq_natCast] using hmv) hhead hfitW
  let benchL := folded.set 0 ((folded[0]'(hpos) + 1) % 3)
  let bW := { { bF with sudo_5Board_5bench := embed benchL } with
    sudo_5Board_4cost := { bF.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (mulMoves moves slope slope n k bench + 1) } }
  have hwhite : Ecbs.bench_white0 bF = .ok bW := by
    have hc0 : coeff folded 0 = folded[0]'(hpos) := by
      unfold coeff
      simp [hpos]
    simpa [bW, benchL, hc0] using hstep
  have hpre : benchL.take n = fieldAdd n (fieldMul n k bench slope slope) (whiteHole0 n) := by
    have htakeL : folded.take n = fieldMul n k bench slope slope := by
      simpa [folded, sch] using htake
    have htriF : allTritList (folded.take n) := by
      rw [htakeL]
      exact fieldMul_span_trits n k bench slope slope hspan hnB
    have hset := take_set_white folded n hn0 (by rw [hlenF]; exact hnB) htriF
    have hc0 : coeff folded 0 = folded[0]'(hpos) := by
      unfold coeff
      simp [hpos]
    simpa [benchL, hc0, htakeL] using hset
  refine ⟨bW, benchL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmulF, ok_bind, hwhite]
  · simp [bW, bF]
  · simpa [bW, bF] using hon
  · simpa [bW, bF, Ecbs.bottom] using hto
  · have hmF : feed.sudo_5Board_6marker = Int.ofNat (m + 1) := by simp [feed, markerUpFeed]
    simpa [bW, bF, hmF] using hmark
  · have hcF : feed.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 2) := by
      simp [feed, markerUpFeed]
    simpa [bW, bF, hcF] using hctrl
  · have hxF : feed.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        Int.ofNat (max mx (m + 2)) := by simp [feed, markerUpFeed]
    simpa [bW, bF, hxF] using hmxR
  · simpa [bW, bF, feed, markerUpFeed] using ht
  · simp [bW, bF, mvSq]
  · simpa [bW, bF, feed, markerUpFeed] using hsl
  · simpa [bW, bF] using hsz
  · have hheldSz : b0.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
      simpa [hheld, feed, markerUpFeed, Array.size_set]
    simpa [bW, bF, hheldSz]
  · simp [bW, bF]
  · exact hpre
  · simpa [benchL, List.length_set, hlenF]
  · intro i hi hlt
    have hne0 : (0 : Nat) ≠ i := by omega
    have hfi : i < folded.length := by simpa [benchL, List.length_set] using hlt
    have hget : benchL[i]'hlt = folded[i]'hfi := by
      simp [benchL, List.getElem_set_ne, hne0]
    have hc0 := hhigh i hi (by rw [hlenF] at hfi; exact hfi)
    have hcoe : coeff folded i = folded[i]'hfi := coeff_eq_get folded i hfi
    rw [hget, ← hcoe]
    simpa [folded, sch] using hc0
  · intro i hne hi hi'
    have hfeed : feed.sudo_5Board_4home[i]'(by simpa [feed, markerUpFeed] using hi) =
        b.sudo_5Board_4home[i] := by simp [feed, markerUpFeed]
    have h0h := hkeep i (by simpa [feed, markerUpFeed] using hi) (by simpa [bW, bF] using hi') hne
    simpa [bW, bF, hfeed] using h0h
  · intro i hne hi hi'
    have h6f : 6 < feed.sudo_5Board_4held.size := by simp [feed, markerUpFeed]; exact h6
    have hset : ((feed.sudo_5Board_4held.set ⟨6, h6f⟩ true).set
        ⟨6, by rw [Array.size_set]; exact h6f⟩ false)[i]'
        (by rw [Array.size_set, Array.size_set]; simpa [feed, markerUpFeed] using hi) =
        feed.sudo_5Board_4held[i]'(by simpa [feed, markerUpFeed] using hi) := by
      have hne6 : (6 : Nat) ≠ i := hne.symm
      simp [Array.getElem_set_ne, hne6]
    have h0h := ix hheld i (by simpa [bW, bF, hheld] using hi')
    simpa [bW, bF, feed, markerUpFeed, hset] using h0h.trans (by
      simpa [feed, markerUpFeed] using hset)
  · intro h6w
    have h6f : 6 < feed.sudo_5Board_4held.size := by simp [feed, markerUpFeed]; exact h6
    have hget := ix hheld 6 (by simpa [bW, bF, hheld] using h6w)
    simp [bW, bF, Array.getElem_set_eq, feed, markerUpFeed, h6e] at hget
    exact hget
  · have hopF : feed.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
      simp [feed, markerUpFeed]
    simpa [bW, bF, hopF] using hopsR
  · let peakG := mulPeak feed.sudo_5Board_4held b0.sudo_5Board_4held
      (by simp [feed, markerUpFeed]; exact h6) peak
    refine ⟨peakG, raisedPeak peakS (countHeld (feed.sudo_5Board_4held.set
        ⟨6, by simp [feed, markerUpFeed]; exact h6⟩ true) 7),
      raisedHole hole (topIdx sch), ?_, ?_, ?_⟩
    · simpa [bW, bF, peakG] using hpk
    · simpa [bW, bF, feed, markerUpFeed] using hstrict
    · simpa [bW, bF, sch] using hholeR
  · have hfeed : feed.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
      simp [feed, markerUpFeed]
    simpa [bW, bF] using hhi0.trans hfeed

/-- Gap settle, then the square, obtained from the settled board. -/
theorem gap_square_obtain (b : Ecbs.Board) (inv rise : List Nat)
    (w h r n k moves hole bench slides peak peakS cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 2 < script) (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hfitC4 : FitsLen (ctrl + 4)) (hfit3 : FitsLen (m + 3))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) (hfops2 : FitsLen (cOps + 2))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : 5 < b.sudo_5Board_4held.size) (hHome : 5 < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[5] = true)
    (hArr : b.sudo_5Board_4home[5] = embed inv)
    (hS : 6 < b.sudo_5Board_4held.size) (hHomeS : 6 < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[6] = true)
    (hYs : b.sudo_5Board_4home[6] = embed rise)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : inv.length = n) (hleny : rise.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList inv) (hrT : allTritList rise)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1)))
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
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n)))
    (hfitClear : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv))
    (hpeg : FitsLen (2 * pegCount ((gapProduct n k bench inv rise).take n)))
    (hfitSM : FitsLen (mulMovesNo moves inv rise n k bench + pegCount inv +
        2 * pegCount ((gapProduct n k bench inv rise).take n)))
    (hfitSS : FitsLen (slides + 2 * pegCount ((gapProduct n k bench inv rise).take n)))
    (hfmS : FitsLen (mvGap moves inv rise n k bench +
        pegCount (fieldMul n k bench rise inv) + n * (n + 1)))
    (hfoldS : FitsLen (mvGap moves inv rise n k bench +
        pegCount (fieldMul n k bench rise inv) + n * (n + 1) + 3 * (bench - n)))
    (hfitW : FitsLen (mvSq (mvGap moves inv rise n k bench)
        (fieldMul n k bench rise inv) n k bench)) :
    let slope := fieldMul n k bench rise inv
    ∃ bW benchL,
      (do
          let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
          Ecbs.bench_white0 b) = .ok bW ∧
      bW.sudo_5Board_5bench = embed benchL ∧
      benchL.take n = fieldAdd n (fieldMul n k bench slope slope) (whiteHole0 n) ∧
      (∀ i, n ≤ i → ∀ hi : i < benchL.length, benchL[i] = 0) ∧
      bW.sudo_5Board_8bench_on = true ∧
      bW.sudo_5Board_8bench_to = Ecbs.bottom := by
  intro slope
  obtain ⟨bS, hdo, _hmkS, hoffS, hmS, hcS, hxS, htS, hmvS, _hslS, hszHs, hszDs, h5a, h5t,
      h6e, _hhome, _hheld, hopsEq, hpeak⟩ :=
    gap_settle_lay b inv rise w h r n k moves hole bench slides peak peakS cOps m ctrl mx
      script hmk hoff hm hc hx hscript (by omega) hfitM hfitC hfit2 hops hop0 hfops hbl
      hF hHome hHF hArr hS hHomeS hHS hYs h7 hn0 hn hlenx hleny hf hmoves hslides hpeak
      hpeakS hspan hxsT hrT hfi hfm hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk hsm
      hnsm hfitB hfold hfitClear hpeg hfitSM hfitSS
  obtain ⟨hp, _hhiS⟩ := hpeak
  obtain ⟨peakG, strictG, holeG, hpk, hst, hho⟩ := hp
  have hlenS : slope.length = n := by
    simp only [slope]
    rw [← mul_no_prefix n k bench rise inv]
    have hs : (school n rise inv (List.replicate bench 0) false).length = bench := by
      simpa [List.length_replicate] using school_length rise inv (List.replicate bench 0) false n
    have hnB : n ≤ bench := by omega
    have hlenF := laneFold_length n (n - k) (school n rise inv (List.replicate bench 0) false)
      (by rw [hs]; exact hnB)
    simp [List.length_take, hlenF, hs]
    omega
  have htriS : allTritList slope := by
    simp only [slope]
    exact fieldMul_span_trits n k bench rise inv hspan (by omega)
  have h5hS : 5 < bS.sudo_5Board_4home.size := by rw [hszHs]; exact hHome
  have h5dS : 5 < bS.sudo_5Board_4held.size := by rw [hszDs]; exact hF
  have h6hS : 6 < bS.sudo_5Board_4home.size := by rw [hszHs]; exact hHomeS
  have h6dS : 6 < bS.sudo_5Board_4held.size := by rw [hszDs]; exact hS
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by rw [hszDs]; exact h7
  have hscriptS : bS.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by rw [htS]; exact hscript
  have hwS : bS.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by rw [htS]; exact hw
  have hhS : bS.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by rw [htS]; exact hh
  have hrS : bS.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by rw [htS]; exact hr
  have hkS : bS.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by rw [htS]; exact hk
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by rw [htS]; exact hn
  have hblS : bS.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by rw [htS]; exact hbl
  have hopsSz : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsEq, Array.size_set]; exact hops
  have hop0S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0] = ((cOps + 1 : Nat) : Int) := by
    have hidx : 0 < (b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1))).size := by
      rw [Array.size_set]; exact hops
    have hget : (b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)))[0] =
        Int.ofNat (cOps + 1) := by simp [Array.getElem_set]
    simpa [hopsEq] using hget
  have hfitP : FitsLen (mvGap moves inv rise n k bench + pegCount slope) := by
    simp only [slope]
    exact FitsLen.of_le hfmS (by omega)
  obtain ⟨bW, benchL, hW, _hmkW, honW, htoW, _hmW, _hcW, _hxW, _htW, _hmvW, _hslW,
      _hszW, _hheldW, hbenchW, hpreW, _hlenW, hzeroW, _⟩ :=
    square_white_lay bS slope w h r n k (mvGap moves inv rise n k bench) holeG bench
      peakG strictG (cOps + 1) (m + 1) (ctrl + 2) (max mx (m + 2)) script
      _hmkS hoffS hmS hcS hxS hscriptS hbound hfit2 hfitC4 hfit3 hopsSz hop0S hfops2 hblS
      h5dS h5hS (h5t h5dS) (h5a h5hS) h6dS h6hS (h6e h6dS) h7S hn0 hnS hlenS hf hmvS
      hpk hst hspan htriS hfi hfmS hfitP hho hw0 hh0 hrR hrP hnE hkLe hgap hwS hhS hrS hkS
      hsm hnsm hfitB hfoldS hfitW
  refine ⟨bW, benchL, ?_, hbenchW, hpreW, hzeroW, honW, htoW⟩
  have hassoc :
      (do
          let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
          let b ← Ecbs.clear b Ecbs.gap
          let b ← Ecbs.settle b
          let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
          Ecbs.bench_white0 b) =
      (do
          let b ←
            (do
              let b ← Ecbs.mul b Ecbs.gap Ecbs.gap Ecbs.spare false false false
              let b ← Ecbs.clear b Ecbs.gap
              Ecbs.settle b)
          let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
          Ecbs.bench_white0 b) := by
    simp only [except_pull]
  rw [hassoc, hdo, ok_bind, hW]

/-- Two bench adds and the settle. The bottom is slope² + 1 + across − run.
    Projections only: the settled record is not simplified. -/
theorem x3_settle_lay (b : Ecbs.Board) (accX run benchL : List Nat)
    (n k bench moves slides peak : Nat) (slope : List Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (2 : Int))
    (hbench : b.sudo_5Board_5bench = embed benchL)
    (h0a : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed accX)
    (h2t : b.sudo_5Board_4held[2]'(by rw [hszD]; decide) = true)
    (h2a : b.sudo_5Board_4home[2]'(by rw [hszH]; decide) = embed run)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx : accX.length = n) (hrun : run.length = n)
    (hpos : 0 < n) (hbLen : benchL.length = bench) (hnb : n ≤ bench)
    (htriX : allTritList accX) (htriR : allTritList run)
    (htriB : allTritList (benchL.take n))
    (hzero : ∀ i, n ≤ i → ∀ hi : i < benchL.length, benchL[i] = 0)
    (hpre : benchL.take n = fieldAdd n (fieldMul n k bench slope slope) (whiteHole0 n))
    (hf : FitsLen n) (hfitL : FitsLen bench)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit1 : FitsLen (moves + n))
    (hfitA : FitsLen (moves + pegCount accX + n))
    (hfitC : FitsLen (moves + pegCount accX + pegCount run + pegCount run))
    (hpeg : FitsLen (2 * pegCount (chordX3 n k bench slope accX run)))
    (hfitM : FitsLen (moves + pegCount accX + pegCount run + pegCount run +
        2 * pegCount (chordX3 n k bench slope accX run)))
    (hfitS : FitsLen (slides + 2 * pegCount (chordX3 n k bench slope accX run))) :
    let x3 := chordX3 n k bench slope accX run
    ∃ bX,
      (do
          let b ← Ecbs.bench_add b Ecbs.across false
          let b ← Ecbs.bench_add b Ecbs.bottom true
          let b ← Ecbs.clear b Ecbs.bottom
          Ecbs.settle b) = .ok bX ∧
      bX.sudo_5Board_8bench_on = false ∧
      (∀ h : 2 < bX.sudo_5Board_4home.size, bX.sudo_5Board_4home[2] = embed x3) ∧
      bX.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      bX.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bX.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (moves + pegCount accX + pegCount run + pegCount run + 2 * pegCount x3) ∧
      bX.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + 2 * pegCount x3) ∧
      bX.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      bX.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      bX.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      (∀ h : 2 < bX.sudo_5Board_4held.size, bX.sudo_5Board_4held[2] = true) ∧
      (∀ i, i ≠ 2 → ∀ hi : i < b.sudo_5Board_4home.size,
        ∀ hi' : i < bX.sudo_5Board_4home.size,
          bX.sudo_5Board_4home[i] = b.sudo_5Board_4home[i]) ∧
      (∀ i, i ≠ 2 → ∀ hi : i < b.sudo_5Board_4held.size,
        ∀ hi' : i < bX.sudo_5Board_4held.size,
          bX.sudo_5Board_4held[i] = b.sudo_5Board_4held[i]) ∧
      bX.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      bX.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      bX.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      bX.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      bX.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      ∃ peakX, bX.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peakX := by
  intro x3
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h2H : 2 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h2D : 2 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h1 := bench_add_prefix b 0 accX benchL n moves false h0H h0a hbench hx hpos
    (by rw [hbLen]; exact hnb) htriX htriB hmoves hfit1
  let L1 := addOnto benchL accX false n
  let mv1 := moves + pegCount accX
  let b1 := benchAddBoard b (embed L1) mv1
  have hlen1 : L1.length = benchL.length := addOnto_length benchL accX false n
  have h2H1 : 2 < b1.sudo_5Board_4home.size := by
    rw [benchAddBoard_home]; exact h2H
  have h2a1 : b1.sudo_5Board_4home[2]'(h2H1) = embed run := by
    have hget := ix (benchAddBoard_home b (embed L1) mv1) 2 h2H1
    exact hget.trans h2a
  have htri1 : allTritList (L1.take n) := by
    rw [addOnto_off benchL accX n (by rw [hbLen]; exact hnb)]
    exact fieldAdd_span_trits _ _ _
  have h2 := bench_add_prefix b1 2 run L1 n mv1 true h2H1 h2a1 rfl hrun hpos
    (by rw [hlen1, hbLen]; exact hnb) htriR htri1 (by rw [benchAddBoard_moves]) hfitA
  let L2 := addOnto L1 run true n
  let mv2 := mv1 + pegCount run
  let b2 := benchAddBoard b1 (embed L2) mv2
  have hlen2 : L2.length = benchL.length := by rw [addOnto_length, hlen1]
  have hzero2 : ∀ i, n ≤ i → ∀ hi : i < L2.length, L2[i] = 0 := by
    intro i hi hlt
    have hiB : i < benchL.length := by rw [hlen2] at hlt; exact hlt
    rw [addOnto_high L1 run true n i hi (by rw [hlen1]; exact hiB),
      addOnto_high benchL accX false n i hi hiB]
    exact hzero i hi hiB
  have hx3 : L2.take n = x3 := by
    rw [addOnto_on L1 run n (by rw [hlen1, hbLen]; exact hnb),
      addOnto_off benchL accX n (by rw [hbLen]; exact hnb), hpre]
    rfl
  have h2H2 : 2 < b2.sudo_5Board_4home.size := by rw [benchAddBoard_home]; exact h2H1
  have h2D2 : 2 < b2.sudo_5Board_4held.size := by rw [benchAdd_held]; rw [benchAdd_held]; exact h2D
  have h2t2 : b2.sudo_5Board_4held[2]'(h2D2) = true := by
    have h1e := ix (benchAdd_held b1 (embed L2) mv2) 2 h2D2
    have h0e := ix (benchAdd_held b (embed L1) mv1) 2
      (by rw [benchAdd_held]; exact h2D)
    exact h1e.trans (h0e.trans h2t)
  have h2a2 : b2.sudo_5Board_4home[2]'(h2H2) = embed run := by
    have h1e := ix (benchAddBoard_home b1 (embed L2) mv2) 2 h2H2
    exact h1e.trans h2a1
  have hclear := clear_held_refines b2 2 run mv2 h2H2 h2D2 h2t2 h2a2
    (by rw [benchAddBoard_moves]) (by rw [hrun]; exact hf) hfitC
  let bC := { b2 with
    sudo_5Board_4home := b2.sudo_5Board_4home.set ⟨2, h2H2⟩ #[]
    sudo_5Board_4held := b2.sudo_5Board_4held.set ⟨2, h2D2⟩ false
    sudo_5Board_4cost := { b2.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (mv2 + pegCount run) } }
  have hHc : 2 < bC.sudo_5Board_4home.size := by rw [show bC.sudo_5Board_4home.size = b2.sudo_5Board_4home.size from by rw [Array.size_set]]; exact h2H2
  have hDc : 2 < bC.sudo_5Board_4held.size := by rw [show bC.sudo_5Board_4held.size = b2.sudo_5Board_4held.size from by rw [Array.size_set]]; exact h2D2
  have h7c : 7 ≤ bC.sudo_5Board_4held.size := by
    rw [show bC.sudo_5Board_4held.size = b.sudo_5Board_4held.size from by
      rw [Array.size_set, benchAdd_held, benchAdd_held]]
    exact h7
  have hempty : bC.sudo_5Board_4held[2]'(hDc) = false := by
    simp [bC, Array.getElem_set_eq]
  have honC : bC.sudo_5Board_8bench_on = true := by
    rw [show bC.sudo_5Board_8bench_on = b2.sudo_5Board_8bench_on from rfl,
      (benchAdd_on b1 (embed L2) mv2).1, (benchAdd_on b (embed L1) mv1).1, hon]
  have htoC : bC.sudo_5Board_8bench_to = (2 : Int) := by
    rw [show bC.sudo_5Board_8bench_to = b2.sudo_5Board_8bench_to from rfl,
      (benchAdd_on b1 (embed L2) mv2).2, (benchAdd_on b (embed L1) mv1).2, hto]
  have hbenchC : bC.sudo_5Board_5bench = embed L2 := by
    rw [show bC.sudo_5Board_5bench = b2.sudo_5Board_5bench from rfl, benchAddBoard_bench]
  have hnC : bC.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [show bC.sudo_5Board_1t = b2.sudo_5Board_1t from rfl, benchAdd_tier, benchAdd_tier, hn]
  have hslC : bC.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int) := by
    rw [show bC.sudo_5Board_4cost.sudo_5Costs_6slides = b2.sudo_5Board_4cost.sudo_5Costs_6slides from rfl,
      benchAdd_slides, benchAdd_slides, hslides]
  have hpkC : bC.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    rw [show bC.sudo_5Board_4cost.sudo_5Costs_4peak = b2.sudo_5Board_4cost.sudo_5Costs_4peak from rfl,
      benchAdd_peak, benchAdd_peak, hpeak]
  have hmvC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (mv2 + pegCount run) := by
    rw [show bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (mv2 + pegCount run) from rfl]
  have hset := settle_refines bC 2 L2 n (mv2 + pegCount run) slides peak hHc hDc h7c
    honC htoC hempty hbenchC hnC
    (by rw [hlen2, hbLen]; omega) (by rw [hlen2, hbLen]; exact hnb) hzero2 hf
    (by rw [hlen2, hbLen]; exact hfitL) hmvC
    (by rw [hslC, ofNat_eq_natCast]) (by rw [hpkC, ofNat_eq_natCast])
    (by simpa [hx3] using hpeg)
    (by simpa [mv1, mv2, hx3, Nat.add_assoc] using hfitM)
    (by simpa [hx3] using hfitS)
  let bX := settleBoard bC 2 hHc hDc L2 n (mv2 + pegCount run) slides peak
  have hdo :
      (do
          let b ← Ecbs.bench_add b Ecbs.across false
          let b ← Ecbs.bench_add b Ecbs.bottom true
          let b ← Ecbs.clear b Ecbs.bottom
          Ecbs.settle b) = .ok bX := by
    rw [show Ecbs.across = ((0 : Nat) : Int) from rfl, h1, ok_bind]
    rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl, h2, ok_bind]
    rw [hclear, ok_bind]
    rw [hset]
  refine ⟨bX, hdo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact settle_bench_off bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak
  · intro h2x
    have hh := settle_home_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak
    have hget := ix hh 2 h2x
    simpa [Array.getElem_set_eq, hx3] using hget
  · exact ((settle_ix bC 2 hHc hDc L2 n (mv2 + pegCount run) slides peak).1).trans
      ((benchAdd_marker b1 (embed L2) mv2).trans (benchAdd_marker b (embed L1) mv1))
  · exact (settle_tier_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak).trans
      ((benchAdd_tier b1 (embed L2) mv2).trans (benchAdd_tier b (embed L1) mv1))
  · have hmv := settle_moves_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak
    rw [hmv, hx3]
  · have hsl := settle_slides_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak
    simpa [hx3] using hsl
  · have hh := settle_home_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak
    have hszX : bX.sudo_5Board_4home.size = bC.sudo_5Board_4home.size := by
      rw [show bX.sudo_5Board_4home.size =
          (settleBoard bC 2 hHc hDc L2 n (mv2 + pegCount run) slides peak).sudo_5Board_4home.size
          from rfl, hh, Array.size_set]
    have hszC : bC.sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
      simp [bC, Array.size_set, b2, b1, benchAddBoard, withMoves]
    exact hszX.trans hszC
  · have hh := settle_held_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak
    have hszX : bX.sudo_5Board_4held.size = bC.sudo_5Board_4held.size := by
      rw [show bX.sudo_5Board_4held.size =
          (settleBoard bC 2 hHc hDc L2 n (mv2 + pegCount run) slides peak).sudo_5Board_4held.size
          from rfl, hh, Array.size_set]
    have hszC : bC.sudo_5Board_4held.size = b.sudo_5Board_4held.size := by
      simp [bC, Array.size_set, b2, b1, benchAddBoard, withMoves]
    exact hszX.trans hszC
  · have hflagC : bC.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on := by
      simp [bC, b2, b1, benchAddBoard, withMoves]
    exact (settle_marker_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak).trans hflagC
  · intro h2x
    have hh := settle_held_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak
    have hget := ix (by simpa [bX] using hh) 2 h2x
    simpa [Array.getElem_set_eq] using hget
  · intro i hne hi hi'
    have hh := settle_home_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak
    have hget := ix (by simpa [bX] using hh) i hi'
    have hne2 : (2 : Nat) ≠ i := hne.symm
    rw [Array.getElem_set_ne (h := hne2)] at hget
    have hic : i < bC.sudo_5Board_4home.size := by
      simpa [bX, hh, Array.size_set] using hi'
    have hpre : bC.sudo_5Board_4home[i]'hic = b.sudo_5Board_4home[i] := by
      have hhome2 : b2.sudo_5Board_4home = b.sudo_5Board_4home := by
        rw [benchAddBoard_home, benchAddBoard_home]
      simp [bC, hhome2, Array.getElem_set_ne, hne2]
    exact hget.trans hpre
  · intro i hne hi hi'
    have hh := settle_held_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak
    have hget := ix (by simpa [bX] using hh) i hi'
    have hne2 : (2 : Nat) ≠ i := hne.symm
    rw [Array.getElem_set_ne (h := hne2)] at hget
    have hic : i < bC.sudo_5Board_4held.size := by
      simpa [bX, hh, Array.size_set] using hi'
    have hpre : bC.sudo_5Board_4held[i]'hic = b.sudo_5Board_4held[i] := by
      have hheld2 : b2.sudo_5Board_4held = b.sudo_5Board_4held := by
        rw [benchAdd_held, benchAdd_held]
      simp [bC, hheld2, Array.getElem_set_ne, hne2]
    exact hget.trans hpre
  · have hcC : bC.sudo_5Board_4cost.sudo_5Costs_4ctrl =
        b.sudo_5Board_4cost.sudo_5Costs_4ctrl := by
      simp [bC, b2, b1, benchAddBoard, withMoves]
    exact (settle_ctrl_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak).trans hcC
  · have hxC : bC.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
      simp [bC, b2, b1, benchAddBoard, withMoves]
    exact ((settle_ix bC 2 hHc hDc L2 n (mv2 + pegCount run) slides peak).2.2.1).trans hxC
  · have hopC : bC.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by
      simp [bC, b2, b1, benchAddBoard, withMoves]
    exact ((settle_ix bC 2 hHc hDc L2 n (mv2 + pegCount run) slides peak).2.2.2).trans hopC
  · have hsC : bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
      simp [bC, b2, b1, benchAddBoard, withMoves]
    exact (settle_strict_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak).trans hsC
  · have hoC : bC.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := by
      simp [bC, b2, b1, benchAddBoard, withMoves]
    exact (settle_hole_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak).trans hoC
  · let peakX := if peak < countHeld (bC.sudo_5Board_4held.set ⟨2, hDc⟩ true) 7
      then countHeld (bC.sudo_5Board_4held.set ⟨2, hDc⟩ true) 7 else peak
    refine ⟨peakX, ?_⟩
    have hpkI : bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
      rw [hpkC, ofNat_eq_natCast]
    simpa [bX, peakX] using
      settle_peak_eq bC 2 ⟨hHc, hDc⟩ L2 n (mv2 + pegCount run) slides peak hpkI

end EcbsLink2.Link2
