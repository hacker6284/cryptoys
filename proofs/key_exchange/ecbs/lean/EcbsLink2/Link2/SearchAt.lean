/-
  One hole of the base-point search, after the root power. The up home is
  `rootY`, the bottom is the curve side, and the gap is still held.
  The card lifts the marker, turns the flag off, clears the gap, squares
  the up into that gap, and compares. A hit is `rootHit`. A miss clears
  the five homes the loop drops before the next hole.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Mul
import EcbsLink2.Link2.Settle
import EcbsLink2.Link2.Place
import EcbsLink2.Link2.Board
import EcbsLink2.Link2.WalkChord
import EcbsLink2.Link2.RootHit
import EcbsLink2.Link2.EntryInv
import EcbsLink2.Link2.ClimbEmit
import EcbsLink2.Link2.CheckTail

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

def searchGap : Nat := 5
def searchUp : Nat := 1
def searchBottom : Nat := 2
def searchSpare : Nat := 6
def searchAcross : Nat := 0
def searchBase : Nat := 3

theorem searchGap_int : ((searchGap : Nat) : Int) = Ecbs.gap := rfl
theorem searchUp_int : ((searchUp : Nat) : Int) = Ecbs.up := rfl
theorem searchBottom_int : ((searchBottom : Nat) : Int) = Ecbs.bottom := rfl
theorem searchAcross_int : ((searchAcross : Nat) : Int) = Ecbs.across := rfl
theorem searchBase_int : ((searchBase : Nat) : Int) = Ecbs.base_across := rfl

/-- Moves the hit test can add: clearing the gap, the self-square, and the settle. -/
def searchMove (n bench : Nat) : Nat := n * n + 8 * n + 6 * bench

/-- Slides the settle can add. -/
def searchSlide (n : Nat) : Nat := 2 * n

private theorem some_idx {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) : i < a.size := by
  by_cases hlt : i < a.size
  · exact hlt
  · rw [Array.getElem?_ge a (by omega)] at h
    cases h

private theorem some_get {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) : a[i]'(some_idx a i v h) = v := by
  rw [Array.getElem?_eq_getElem (some_idx a i v h)] at h
  injection h

private theorem peg_len (n : Nat) (xs : List Nat) (h : xs.length = n) : pegCount xs ≤ n :=
  Nat.le_trans (pegCount_le _) (Nat.le_of_eq h)

/-- The board at the start of one hole's hit test. `y` is the root up and
    `side` is the curve side of `x`. `left` is how many hit tests may still run,
    counting this one. -/
structure SearchAt (b : Ecbs.Board) (t : Spec.Tier) (x y side gapXs ax bx : List Nat)
    (left : Nat) : Prop where
  tier : b.sudo_5Board_1t = embTier t
  shape : TierShape t
  sat : TierSat t
  nPos : 0 < t.n
  markerOn : b.sudo_5Board_9marker_on = true
  benchOff : b.sudo_5Board_8bench_on = false
  xLen : x.length = t.n
  yIs : y = rootY t.n t.k t.benchlen x
  sideIs : side = curveSide t.n t.k t.benchlen x
  yLen : y.length = t.n
  sideLen : side.length = t.n
  yT : allTritList y
  sideT : allTritList side
  gapLen : gapXs.length = t.n
  axLen : ax.length = t.n
  bxLen : bx.length = t.n
  upHome : b.sudo_5Board_4home[searchUp]? = some (embed y)
  upHeld : b.sudo_5Board_4held[searchUp]? = some true
  botHome : b.sudo_5Board_4home[searchBottom]? = some (embed side)
  botHeld : b.sudo_5Board_4held[searchBottom]? = some true
  gapHome : b.sudo_5Board_4home[searchGap]? = some (embed gapXs)
  gapHeld : b.sudo_5Board_4held[searchGap]? = some true
  axHome : b.sudo_5Board_4home[searchAcross]? = some (embed ax)
  axHeld : b.sudo_5Board_4held[searchAcross]? = some true
  bxHome : b.sudo_5Board_4home[searchBase]? = some (embed bx)
  bxHeld : b.sudo_5Board_4held[searchBase]? = some true
  spareOff : b.sudo_5Board_4held[searchSpare]? = some false
  homeWide : searchSpare < b.sudo_5Board_4home.size
  pack :
    ∃ (moves slides ctrl mark pk ps hole c0 : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
      b.sudo_5Board_6marker = Int.ofNat mark ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk ∧
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps ∧
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole ∧
      0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
      0 < left ∧
      FitsLen (moves + searchMove t.n t.benchlen * left) ∧
      FitsLen (slides + searchSlide t.n * left) ∧
      FitsLen (ctrl + left) ∧
      FitsLen (c0 + left)

/-- The board the compare reads. The gap is the squared root up and the
    bottom is still the curve side. Across and the base home are untouched. -/
structure HitAt (b : Ecbs.Board) (t : Spec.Tier) (x ax bx : List Nat) : Prop where
  benchOff : b.sudo_5Board_8bench_on = false
  gapHome : b.sudo_5Board_4home[searchGap]? =
    some (embed (fieldMul t.n t.k t.benchlen (rootY t.n t.k t.benchlen x)
      (rootY t.n t.k t.benchlen x)))
  gapHeld : b.sudo_5Board_4held[searchGap]? = some true
  botHome : b.sudo_5Board_4home[searchBottom]? =
    some (embed (curveSide t.n t.k t.benchlen x))
  botHeld : b.sudo_5Board_4held[searchBottom]? = some true
  upHome : b.sudo_5Board_4home[searchUp]? =
    some (embed (rootY t.n t.k t.benchlen x))
  upHeld : b.sudo_5Board_4held[searchUp]? = some true
  axHome : b.sudo_5Board_4home[searchAcross]? = some (embed ax)
  axHeld : b.sudo_5Board_4held[searchAcross]? = some true
  bxHome : b.sudo_5Board_4home[searchBase]? = some (embed bx)
  bxHeld : b.sudo_5Board_4held[searchBase]? = some true

/-- The five homes the miss branch empties. -/
structure MissAt (b : Ecbs.Board) : Prop where
  gapHeld : b.sudo_5Board_4held[searchGap]? = some false
  botHeld : b.sudo_5Board_4held[searchBottom]? = some false
  upHeld : b.sudo_5Board_4held[searchUp]? = some false
  axHeld : b.sudo_5Board_4held[searchAcross]? = some false
  bxHeld : b.sudo_5Board_4held[searchBase]? = some false
  gapHome : b.sudo_5Board_4home[searchGap]? = some (#[] : Array Int)
  botHome : b.sudo_5Board_4home[searchBottom]? = some (#[] : Array Int)
  upHome : b.sudo_5Board_4home[searchUp]? = some (#[] : Array Int)
  axHome : b.sudo_5Board_4home[searchAcross]? = some (#[] : Array Int)
  bxHome : b.sudo_5Board_4home[searchBase]? = some (#[] : Array Int)

/-- Lift, flag off, clear the gap, square the up into it, settle, compare. -/
def searchCheck (b : Ecbs.Board) : Except SudoRt.Trap (Bool × Ecbs.Board) :=
  do
    let b ← Ecbs.marker_lift b
    let b := { b with sudo_5Board_9marker_on := false }
    let b ← Ecbs.clear b ((searchGap : Nat) : Int)
    let b ← Ecbs.mul b ((searchGap : Nat) : Int) ((searchUp : Nat) : Int)
        ((searchUp : Nat) : Int) true false false
    let b ← Ecbs.settle b
    let y2 ← Ecbs.value b ((searchGap : Nat) : Int)
    let side ← Ecbs.value b ((searchBottom : Nat) : Int)
    pure (SudoRt.SEq.beq y2 side, b)

/-- The five clears the miss branch runs before the next hole. -/
def searchMiss (b : Ecbs.Board) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b ← Ecbs.clear b ((searchGap : Nat) : Int)
    let b ← Ecbs.clear b ((searchBottom : Nat) : Int)
    let b ← Ecbs.clear b ((searchUp : Nat) : Int)
    let b ← Ecbs.clear b ((searchAcross : Nat) : Int)
    Ecbs.clear b ((searchBase : Nat) : Int)

private theorem list_beq_decide (xs ys : List Nat) :
    (xs == ys) = decide (xs = ys) := by
  by_cases h : xs = ys
  · simp [h]
  · simp [h]

private theorem search_shape (t : Spec.Tier) (h : TierShape t) :
    BoardShape t.w t.h t.r t.n t.k :=
  { hw0 := h.w0, hh0 := h.h0, hrR := h.rlt, hrP := h.r0,
    hnE := h.n_eq, hkLe := h.k_le, hgap := h.gap }

/-- Lift, drop the flag, and empty the gap. The up and the bottom stay. -/
theorem search_prepared (b : Ecbs.Board) (t : Spec.Tier)
    (x y side gapXs ax bx : List Nat) (left : Nat)
    (h : SearchAt b t x y side gapXs ax bx left) :
    ∃ (bC : Ecbs.Board) (moves slides pk ps hole c0 movesC : Nat),
      (do
          let b ← Ecbs.marker_lift b
          let b := { b with sudo_5Board_9marker_on := false }
          Ecbs.clear b ((searchGap : Nat) : Int)) = .ok bC ∧
        b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
        b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
        b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk ∧
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps ∧
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole ∧
        b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
        bC.sudo_5Board_9marker_on = false ∧
        bC.sudo_5Board_8bench_on = false ∧
        bC.sudo_5Board_6marker = -1 ∧
        bC.sudo_5Board_4home[searchUp]? = some (embed y) ∧
        bC.sudo_5Board_4held[searchUp]? = some true ∧
        bC.sudo_5Board_4home[searchBottom]? = some (embed side) ∧
        bC.sudo_5Board_4held[searchBottom]? = some true ∧
        bC.sudo_5Board_4home[searchGap]? = some (#[] : Array Int) ∧
        bC.sudo_5Board_4held[searchGap]? = some false ∧
        bC.sudo_5Board_4home[searchAcross]? = some (embed ax) ∧
        bC.sudo_5Board_4held[searchAcross]? = some true ∧
        bC.sudo_5Board_4home[searchBase]? = some (embed bx) ∧
        bC.sudo_5Board_4held[searchBase]? = some true ∧
        bC.sudo_5Board_4held[searchSpare]? = some false ∧
        bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat movesC ∧
        movesC = moves + pegCount gapXs ∧
        bC.sudo_5Board_1t = embTier t ∧
        bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
        bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk ∧
        bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps ∧
        bC.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole ∧
        bC.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
        searchSpare < bC.sudo_5Board_4home.size ∧
        searchSpare < bC.sudo_5Board_4held.size ∧
        7 ≤ bC.sudo_5Board_4held.size ∧
        0 < left ∧
        FitsLen (moves + searchMove t.n t.benchlen * left) ∧
        FitsLen (slides + searchSlide t.n * left) ∧
        FitsLen (c0 + left) ∧
        bC.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
        bC.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
        (∃ c, b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c ∧
          bC.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c + 1)) ∧
        bC.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
        bC.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
          b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  obtain ⟨moves, slides, ctrl, mark, pk, ps, hole, c0, hmv, hsl, hc, hm, hpk, hps, hhole,
      hops0, hop0, hleft, hfitM, _hfitS, hfitC, _hfit0⟩ := h.pack
  have hG := some_idx _ _ _ h.gapHome
  have hGD := some_idx _ _ _ h.gapHeld
  have harr := some_get _ _ _ h.gapHome
  have hheld := some_get _ _ _ h.gapHeld
  have hfit1 : FitsLen (ctrl + 1) := FitsLen.of_le hfitC (by omega)
  have hpeg : pegCount gapXs ≤ t.n := peg_len t.n gapXs h.gapLen
  have hroom : t.n ≤ (t.n * t.n + 8 * t.n + 6 * t.benchlen) * left := by
    have h1 : t.n ≤ t.n * t.n + 8 * t.n + 6 * t.benchlen := by omega
    exact Nat.le_trans h1 (Nat.le_mul_of_pos_right _ hleft)
  have hfitN : FitsLen gapXs.length := by
    rw [h.gapLen]
    apply FitsLen.of_le hfitM
    unfold searchMove
    omega
  have hfitP : FitsLen (moves + pegCount gapXs) := by
    apply FitsLen.of_le hfitM
    unfold searchMove
    omega
  have hlift := marker_lift_refines b mark ctrl hm hc hfit1
  let bL := { b with
    sudo_5Board_6marker := -1
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1) } }
  let bF := { bL with sudo_5Board_9marker_on := false }
  have hclear := clear_held_refines bF searchGap gapXs moves hG hGD hheld harr hmv hfitN hfitP
  let bC := { bF with
    sudo_5Board_4home := bF.sudo_5Board_4home.set ⟨searchGap, hG⟩ #[]
    sudo_5Board_4held := bF.sudo_5Board_4held.set ⟨searchGap, hGD⟩ false
    sudo_5Board_4cost := { bF.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (moves + pegCount gapXs) } }
  have hkeepH {j : Nat} {v : Array Int} (hne : searchGap ≠ j)
      (hj : b.sudo_5Board_4home[j]? = some v) :
      bC.sudo_5Board_4home[j]? = some v := by
    simp only [bC, bF, bL]
    rw [Array.getElem?_set_ne _ ⟨searchGap, hG⟩ (#[] : Array Int) hne]
    exact hj
  have hkeepD {j : Nat} {v : Bool} (hne : searchGap ≠ j)
      (hj : b.sudo_5Board_4held[j]? = some v) :
      bC.sudo_5Board_4held[j]? = some v := by
    simp only [bC, bF, bL]
    rw [Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ false hne]
    exact hj
  have hdo :
      (do
          let b ← Ecbs.marker_lift b
          let b := { b with sudo_5Board_9marker_on := false }
          Ecbs.clear b ((searchGap : Nat) : Int)) = .ok bC := by
    rw [hlift, ok_bind]
    exact hclear
  have hflag : bC.sudo_5Board_9marker_on = false := by simp [bC, bF]
  have hoffC : bC.sudo_5Board_8bench_on = false := by simp [bC, bF, bL, h.benchOff]
  have hmarkC : bC.sudo_5Board_6marker = -1 := by simp [bC, bF, bL]
  have hgapH : bC.sudo_5Board_4home[searchGap]? = some (#[] : Array Int) := by
    simp only [bC, bF, bL]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hG)]
    simp [Array.getElem_set]
  have hgapD : bC.sudo_5Board_4held[searchGap]? = some false := by
    simp only [bC, bF, bL]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hGD)]
    simp [Array.getElem_set]
  have hmvC : bC.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + pegCount gapXs) := by simp [bC]
  have htierC : bC.sudo_5Board_1t = embTier t := by simp [bC, bF, bL, h.tier]
  have hslC : bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simp [bC, bF, bL, hsl]
  have hpkC : bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk := by
    simp [bC, bF, bL, hpk]
  have hpsC : bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps := by
    simp [bC, bF, bL, hps]
  have hholeC : bC.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bC, bF, bL, hhole]
  have hopC : bC.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) := by
    simp [bC, bF, bL, hop0]
  have hwideC : searchSpare < bC.sudo_5Board_4home.size := by
    simp only [bC, bF, bL, Array.size_set]
    exact h.homeWide
  have hspS : searchSpare < bC.sudo_5Board_4held.size := by
    simp only [bC, bF, bL, Array.size_set]
    exact some_idx _ _ _ h.spareOff
  have h7 : 7 ≤ bC.sudo_5Board_4held.size := by
    have h6 : searchSpare < b.sudo_5Board_4held.size := some_idx _ _ _ h.spareOff
    unfold searchSpare at h6
    simp only [bC, bF, bL, Array.size_set]
    omega
  exact ⟨bC, moves, slides, pk, ps, hole, c0, moves + pegCount gapXs, hdo, hmv, hsl, hpk, hps,
      hhole, hop0, hflag, hoffC, hmarkC,
      hkeepH (by decide) h.upHome, hkeepD (by decide) h.upHeld,
      hkeepH (by decide) h.botHome, hkeepD (by decide) h.botHeld,
      hgapH, hgapD,
      hkeepH (by decide) h.axHome, hkeepD (by decide) h.axHeld,
      hkeepH (by decide) h.bxHome, hkeepD (by decide) h.bxHeld,
      hkeepD (by decide) h.spareOff,
      hmvC, rfl, htierC, hslC, hpkC, hpsC, hholeC, hopC, hwideC, hspS, h7,
      hleft, hfitM, _hfitS, _hfit0,
      by simp [bC, bF, bL, Array.size_set],
      by simp [bC, bF, bL, Array.size_set],
      ⟨ctrl, hc, by simp [bC, bF, bL]⟩,
      by simp [bC, bF, bL],
      by simp [bC, bF, bL]⟩

private theorem search_room (n bench moves left pegG pegY : Nat)
    (hleft : 0 < left) (hg : pegG ≤ n) (hy : pegY ≤ n)
    (h : FitsLen (moves + searchMove n bench * left)) :
    FitsLen n ∧
      FitsLen (moves + pegG) ∧
      FitsLen (moves + pegG + pegY) ∧
      FitsLen (moves + pegG + pegY + n * (n + 1)) ∧
      FitsLen (moves + pegG + pegY + n * (n + 1) + 3 * (bench - n)) ∧
      FitsLen (moves + pegG + pegY + n * (n + 1) + 3 * (bench - n) + 2 * n) := by
  have hsq : n * (n + 1) = n * n + n := by rw [Nat.mul_succ]
  have hmul : n * n + 8 * n + 6 * bench ≤ (n * n + 8 * n + 6 * bench) * left :=
    Nat.le_mul_of_pos_right _ hleft
  unfold searchMove at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FitsLen.of_le h (by omega)
  · exact FitsLen.of_le h (by omega)
  · exact FitsLen.of_le h (by omega)
  · exact FitsLen.of_le h (by rw [hsq]; omega)
  · exact FitsLen.of_le h (by rw [hsq]; omega)
  · exact FitsLen.of_le h (by rw [hsq]; omega)

/-- The check and the five miss-clears stay inside one hole's move budget. -/
private theorem search_spent_le (n bench moves left pegG pegY sch fold pegSq pegSide pegUp
    pegAx pegBx : Nat)
    (hleft : 0 < left) (hnb : n ≤ bench)
    (hg : pegG ≤ n) (hy : pegY ≤ n) (hsq : pegSq ≤ n)
    (hside : pegSide ≤ n) (hup : pegUp ≤ n) (hax : pegAx ≤ n) (hbx : pegBx ≤ n)
    (hsch : sch ≤ n * n + n) (hfold : fold ≤ 3 * (bench - n))
    (h : FitsLen (moves + searchMove n bench * left)) :
    FitsLen (moves + pegG + pegY + sch + fold + 2 * pegSq + pegSq + pegSide + pegUp +
      pegAx + pegBx) := by
  have hmul : n * n + 8 * n + 6 * bench ≤ (n * n + 8 * n + 6 * bench) * left :=
    Nat.le_mul_of_pos_right _ hleft
  have hfoldN : fold + 3 * n ≤ 3 * bench := by
    have h3 : 3 * (bench - n) + 3 * n = 3 * ((bench - n) + n) := by
      rw [← Nat.mul_add]
    rw [Nat.sub_add_cancel hnb] at h3
    omega
  unfold searchMove at h
  apply FitsLen.of_le h
  omega

/-- One hit test, including the five clears a miss runs, stays inside `searchMove`. -/
private theorem one_check_spent (moves n bench pegG pegY sch fold pegSq pegSide pegUp
    pegAx pegBx : Nat)
    (hnb : n ≤ bench)
    (hg : pegG ≤ n) (hy : pegY ≤ n) (hsq : pegSq ≤ n)
    (hside : pegSide ≤ n) (hup : pegUp ≤ n) (hax : pegAx ≤ n) (hbx : pegBx ≤ n)
    (hsch : sch ≤ n * n + n) (hfold : fold ≤ 3 * (bench - n)) :
    moves + pegG + pegY + sch + fold + 2 * pegSq + pegSq + pegSide + pegUp + pegAx + pegBx ≤
      moves + (n * n + 8 * n + 6 * bench) := by
  have hfoldN : fold + 3 * n ≤ 3 * bench := by
    have h3 : 3 * (bench - n) + 3 * n = 3 * ((bench - n) + n) := by
      rw [← Nat.mul_add]
    rw [Nat.sub_add_cancel hnb] at h3
    omega
  omega

/-- Fields the hit test keeps, counted from the board it was given. -/
structure CheckKeep (b b0 : Ecbs.Board) (n : Nat) : Prop where
  marker : b.sudo_5Board_6marker = -1
  markerOn : b.sudo_5Board_9marker_on = false
  benchOff : b.sudo_5Board_8bench_on = false
  tier : b.sudo_5Board_1t = b0.sudo_5Board_1t
  szH : b.sudo_5Board_4home.size = b0.sudo_5Board_4home.size
  szD : b.sudo_5Board_4held.size = b0.sudo_5Board_4held.size
  ctrl : ∃ c, b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c ∧
    b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c + 1)
  slides : ∃ sl sl2, b0.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧
    b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl2 ∧ sl2 ≤ sl + 2 * n
  ops0 : ∃ c, b0.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c) ∧
    b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat (c + 1))
  ops1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = b0.sudo_5Board_4cost.sudo_5Costs_3ops[1]?
  opsSz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = b0.sudo_5Board_4cost.sudo_5Costs_3ops.size
  mx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
    b0.sudo_5Board_4cost.sudo_5Costs_17script_marker_max
  spare : b.sudo_5Board_4held[6]? = some false
  peak : ∃ pk, b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk
  strict : ∃ ps, b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps
  hole : ∃ holeN, b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat holeN

/-- One hole. The compare bit is `rootHit`, and the board it reads is `HitAt`.
    `movesS` still covers clearing the five homes a miss drops. -/
theorem search_check_at (b : Ecbs.Board) (t : Spec.Tier)
    (x y side gapXs ax bx : List Nat) (left : Nat)
    (h : SearchAt b t x y side gapXs ax bx left) :
    ∃ b' bit movesS,
      searchCheck b = .ok (bit, b') ∧
      bit = rootHit t.n t.k t.benchlen x ∧
      HitAt b' t x ax bx ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat movesS ∧
      FitsLen (movesS + pegCount (fieldMul t.n t.k t.benchlen y y) + pegCount side +
        pegCount y + pegCount ax + pegCount bx) ∧
      CheckKeep b' b t.n ∧
      ∃ moves0, b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves0 ∧
        movesS + pegCount (fieldMul t.n t.k t.benchlen y y) + pegCount side +
          pegCount y + pegCount ax + pegCount bx ≤
          moves0 + searchMove t.n t.benchlen := by
  obtain ⟨bC, moves, slides, pk, ps, hole, c0, movesC, hpre, hmv, hsl, hpk, hps, hhole, hop0,
      hflag, hoff, _hmark, hup, hupd, hbot, hbotd, _hgapH, hgapD, hax, haxd, hbx, hbxd, hsp,
      hmvC, hmovesC, htierC, hslC, hpkC, hpsC, hholeC, hopC, hwide, hspS, h7,
      hleft, hfitM, hfitS, hfit0, hszHC, hszDC, hctrlStep, hopsBC, hmxBC⟩ :=
    search_prepared b t x y side gapXs ax bx left h
  have hn0 : 0 < t.n := h.nPos
  have hnb : t.n ≤ t.benchlen := mul_span_n t.n t.benchlen hn0 h.sat.mul_span
  have hg := peg_len t.n gapXs h.gapLen
  have hy := peg_len t.n y h.yLen
  have hroom := search_room t.n t.benchlen moves left (pegCount gapXs) (pegCount y)
      hleft hg hy hfitM
  have hUp := some_idx _ _ _ hup
  have hUpD := some_idx _ _ _ hupd
  have hUpA := some_get _ _ _ hup
  have hUpH := some_get _ _ _ hupd
  have hopsC : 0 < bC.sudo_5Board_4cost.sudo_5Costs_3ops.size := some_idx _ _ _ hopC
  have hopA : bC.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hopsC) = (c0 : Int) := by
    rw [Array.getElem?_eq_getElem hopsC] at hopC
    injection hopC
  have hmul := mul_refines bC searchGap searchUp searchUp y y t.w t.h t.r t.n t.k movesC hole
      t.benchlen pk ps c0
      hflag hoff hopsC hopA
      (FitsLen.of_le hfit0 (by omega))
      (by simpa [htierC, embTier])
      hUpD hUp hUpH hUpA hUpD hUp hUpH hUpA
      hspS hwide (some_get _ _ _ hsp) h7
      (by decide) (by decide)
      hn0 (by simpa [htierC, embTier]) h.yLen h.yLen
      hroom.1
      hmvC (by simpa [ofNat_eq_natCast] using hpkC)
      (by simpa [ofNat_eq_natCast] using hpsC)
      (by simpa [hmovesC] using hroom.2.2.1)
      h.sat.mul_span h.yT
      (FitsLen.of_le hfitM (by
        unfold searchMove
        have h2 : 2 * (t.n - 1) ≤ t.n * t.n + 8 * t.n + 6 * t.benchlen := by omega
        have hmul : t.n * t.n + 8 * t.n + 6 * t.benchlen ≤
            (t.n * t.n + 8 * t.n + 6 * t.benchlen) * left :=
          Nat.le_mul_of_pos_right _ hleft
        omega))
      (by simpa [hmovesC] using hroom.2.2.2.1)
      (search_shape t h.shape)
      (by simpa [htierC, embTier]) (by simpa [htierC, embTier])
      (by simpa [htierC, embTier]) (by simpa [htierC, embTier])
      hholeC h.shape.small h.shape.n_small
      (FitsLen.of_le hfitM (by
        unfold searchMove
        have h1 : t.benchlen ≤ t.n * t.n + 8 * t.n + 6 * t.benchlen := by omega
        have hmul : t.n * t.n + 8 * t.n + 6 * t.benchlen ≤
            (t.n * t.n + 8 * t.n + 6 * t.benchlen) * left :=
          Nat.le_mul_of_pos_right _ hleft
        omega))
      (by simpa [hmovesC] using hroom.2.2.2.2.1)
  rcases hmul with ⟨bM, hmulEq, honM, htoM, hbenchM, htakeM, hzeroM, hmvM, hpkM, hslM,
      _htierM, hszHM, _hheldM, _h5M, hhomeM, _hflagM, _hopsM, _hstM, _hholeM, _hmarkM,
      _hctrlM, _hmxM, _hhiM, _hrowM, _hfrM⟩
  let lane := laneFold t.n (t.n - t.k) (school t.n y y (List.replicate t.benchlen 0) false)
  have hlenL : lane.length = t.benchlen := by
    have hsch : (school t.n y y (List.replicate t.benchlen 0) false).length = t.benchlen := by
      simpa [List.length_replicate] using
        school_length y y (List.replicate t.benchlen 0) false t.n
    simp only [lane]
    rw [laneFold_length t.n (t.n - t.k) _ (by rw [hsch]; exact hnb)]
    exact hsch
  have hpkN : bM.sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (mulPeak bC.sudo_5Board_4held bM.sudo_5Board_4held hspS pk) := hpkM
  have hmvN : bM.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mulMoves movesC y y t.n t.k t.benchlen) := hmvM
  have hslN : bM.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    rw [hslM, hslC]
  have hGD : searchGap < bM.sudo_5Board_4held.size := by
    have h5 : searchGap < bC.sudo_5Board_4held.size := some_idx _ _ _ hgapD
    have hsz : bM.sudo_5Board_4held.size = bC.sudo_5Board_4held.size := by
      rw [_hheldM, Array.size_set, Array.size_set]
    rw [hsz]; exact h5
  have h7M : 7 ≤ bM.sudo_5Board_4held.size := by
    have hsz : bM.sudo_5Board_4held.size = bC.sudo_5Board_4held.size := by
      rw [_hheldM, Array.size_set, Array.size_set]
    rw [hsz]
    exact h7
  have hGH : searchGap < bM.sudo_5Board_4home.size := by
    rw [hszHM]
    have h6 : (6 : Nat) < bC.sudo_5Board_4home.size := by simpa [searchSpare] using hwide
    have h5 : (5 : Nat) < bC.sudo_5Board_4home.size := by omega
    simpa [searchGap] using h5
  have hempty : bM.sudo_5Board_4held[searchGap] = false := by
    have h? : bM.sudo_5Board_4held[searchGap]? = some false := by
      rw [_hheldM]
      rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchGap)]
      rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchGap)]
      exact hgapD
    rw [Array.getElem?_eq_getElem hGD] at h?
    injection h?
  have hzeroL : ∀ i, t.n ≤ i → ∀ hi : i < lane.length, lane[i] = 0 := by
    intro i hi hlt
    have hcb : i < t.benchlen := by rw [← hlenL]; exact hlt
    have hc := hzeroM i hi hcb
    rw [coeff_eq_get _ i (by rw [hlenL]; exact hcb)] at hc
    exact hc
  have hprod : pegCount (fieldMul t.n t.k t.benchlen y y) ≤ t.n := by
    have hlen := fieldMul_length t.n t.k t.benchlen y y hnb
    exact Nat.le_trans (pegCount_le _) (Nat.le_of_eq hlen)
  have hset := settle_refines bM searchGap lane t.n (mulMoves movesC y y t.n t.k t.benchlen)
      slides (mulPeak bC.sudo_5Board_4held bM.sudo_5Board_4held hspS pk)
      hGH hGD h7M honM htoM hempty hbenchM
      (by rw [_htierM, htierC]; simp [embTier])
      (by rw [hlenL]; omega) (by rw [hlenL]; exact hnb) hzeroL
      hroom.1
      (by rw [hlenL]; exact (FitsLen.of_le hfitM (by
        unfold searchMove
        have h1 : t.benchlen ≤ t.n * t.n + 8 * t.n + 6 * t.benchlen := by omega
        have hmul : t.n * t.n + 8 * t.n + 6 * t.benchlen ≤
            (t.n * t.n + 8 * t.n + 6 * t.benchlen) * left :=
          Nat.le_mul_of_pos_right _ hleft
        omega)))
      hmvN hslN hpkN
      (by
        rw [htakeM]
        exact FitsLen.of_le hfitM (by
          unfold searchMove
          have h2 : 2 * pegCount (fieldMul t.n t.k t.benchlen y y) ≤
              (t.n * t.n + 8 * t.n + 6 * t.benchlen) * left := by
            have h2n : 2 * pegCount (fieldMul t.n t.k t.benchlen y y) ≤ 2 * t.n :=
              Nat.mul_le_mul_left _ hprod
            have hmul : t.n * t.n + 8 * t.n + 6 * t.benchlen ≤
                (t.n * t.n + 8 * t.n + 6 * t.benchlen) * left :=
              Nat.le_mul_of_pos_right _ hleft
            omega
          omega))
      (by
        rw [htakeM]
        apply FitsLen.of_le hfitM
        have hdef : mulMoves movesC y y t.n t.k t.benchlen =
            movesC + pegCount y + schoolMoves y y t.n t.n +
              foldCharge t.n (t.n - t.k)
                (school t.n y y (List.replicate t.benchlen 0) false) := by
          unfold mulMoves
          rfl
        have hschB := schoolMoves_bound y y t.n
        have hfoldB := foldCharge_bound t.n (t.n - t.k)
            (school t.n y y (List.replicate t.benchlen 0) false)
        have hlenS : (school t.n y y (List.replicate t.benchlen 0) false).length =
            t.benchlen := by
          simpa [List.length_replicate] using
            school_length y y (List.replicate t.benchlen 0) false t.n
        rw [hlenS] at hfoldB
        have hsq : t.n * (t.n + 1) = t.n * t.n + t.n := by rw [Nat.mul_succ]
        have hschN : schoolMoves y y t.n t.n ≤ t.n * t.n + t.n := by
          simpa [hsq] using hschB
        unfold searchMove
        rw [hdef, hmovesC]
        have h2 : 2 * pegCount (fieldMul t.n t.k t.benchlen y y) ≤ 2 * t.n :=
          Nat.mul_le_mul_left _ hprod
        have hmul : t.n * t.n + 8 * t.n + 6 * t.benchlen ≤
            (t.n * t.n + 8 * t.n + 6 * t.benchlen) * left :=
          Nat.le_mul_of_pos_right _ hleft
        omega)
      (by
        rw [htakeM]
        apply FitsLen.of_le hfitS
        unfold searchSlide
        have h2n : 2 * pegCount (fieldMul t.n t.k t.benchlen y y) ≤ 2 * t.n :=
          Nat.mul_le_mul_left _ hprod
        have hmul : 2 * t.n ≤ 2 * t.n * left := Nat.le_mul_of_pos_right _ hleft
        omega)
  let mvMul := mulMoves movesC y y t.n t.k t.benchlen
  let pkMul := mulPeak bC.sudo_5Board_4held bM.sudo_5Board_4held hspS pk
  let bS := settleBoard bM searchGap hGH hGD lane t.n mvMul slides pkMul
  have hprodTake : lane.take t.n = fieldMul t.n t.k t.benchlen y y := by
    simpa [lane] using htakeM
  have hgapS : bS.sudo_5Board_4home[searchGap]? =
      some (embed (fieldMul t.n t.k t.benchlen y y)) := by
    rw [show bS.sudo_5Board_4home =
        bM.sudo_5Board_4home.set ⟨searchGap, hGH⟩ (embed (lane.take t.n)) from
      settle_home_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hGH)]
    simp [Array.getElem_set, hprodTake]
  have hheldS : bS.sudo_5Board_4held[searchGap]? = some true := by
    rw [settle_held_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hGD)]
    simp [Array.getElem_set]
  have hbotS : bS.sudo_5Board_4home[searchBottom]? = some (embed side) := by
    rw [show bS.sudo_5Board_4home =
        bM.sudo_5Board_4home.set ⟨searchGap, hGH⟩ (embed (lane.take t.n)) from
      settle_home_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
    rw [Array.getElem?_set_ne _ ⟨searchGap, hGH⟩ _ (by decide : searchGap ≠ searchBottom)]
    have h2 : searchBottom < bC.sudo_5Board_4home.size := some_idx _ _ _ hbot
    have h2' : searchBottom < bM.sudo_5Board_4home.size := by rw [hszHM]; exact h2
    have hget := hhomeM searchBottom h2 h2' (by decide)
    rw [Array.getElem?_eq_getElem h2', hget]
    exact congrArg some (some_get _ _ _ hbot)
  have hlenSch : (school t.n y y (List.replicate t.benchlen 0) false).length = t.benchlen := by
    simpa [List.length_replicate] using
      school_length y y (List.replicate t.benchlen 0) false t.n
  have hschN : schoolMoves y y t.n t.n ≤ t.n * t.n + t.n := by
    have hsq : t.n * (t.n + 1) = t.n * t.n + t.n := by rw [Nat.mul_succ]
    simpa [hsq] using schoolMoves_bound y y t.n
  have hfoldN : foldCharge t.n (t.n - t.k)
      (school t.n y y (List.replicate t.benchlen 0) false) ≤ 3 * (t.benchlen - t.n) := by
    have hfoldB := foldCharge_bound t.n (t.n - t.k)
      (school t.n y y (List.replicate t.benchlen 0) false)
    rwa [hlenSch] at hfoldB
  let movesS := moves + pegCount gapXs + pegCount y + schoolMoves y y t.n t.n +
    foldCharge t.n (t.n - t.k) (school t.n y y (List.replicate t.benchlen 0) false) +
    2 * pegCount (fieldMul t.n t.k t.benchlen y y)
  have hmvS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat movesS := by
    rw [settle_moves_eq bM searchGap ⟨hGH, hGD⟩ lane t.n
        (mulMoves movesC y y t.n t.k t.benchlen) slides
        (mulPeak bC.sudo_5Board_4held bM.sudo_5Board_4held hspS pk)]
    have hpegs : pegCount (lane.take t.n) =
        pegCount (fieldMul t.n t.k t.benchlen y y) := by
      rw [hprodTake]
    rw [hpegs]
    apply congrArg Int.ofNat
    have hdef : mulMoves movesC y y t.n t.k t.benchlen =
        movesC + pegCount y + schoolMoves y y t.n t.n +
          foldCharge t.n (t.n - t.k)
            (school t.n y y (List.replicate t.benchlen 0) false) := by
      unfold mulMoves
      rfl
    rw [hdef, hmovesC]
  have hfitTail : FitsLen (movesS + pegCount (fieldMul t.n t.k t.benchlen y y) +
      pegCount side + pegCount y + pegCount ax + pegCount bx) := by
    have hsideP := peg_len t.n side h.sideLen
    have haxP := peg_len t.n ax h.axLen
    have hbxP := peg_len t.n bx h.bxLen
    have hraw := search_spent_le t.n t.benchlen moves left (pegCount gapXs) (pegCount y)
      (schoolMoves y y t.n t.n)
      (foldCharge t.n (t.n - t.k) (school t.n y y (List.replicate t.benchlen 0) false))
      (pegCount (fieldMul t.n t.k t.benchlen y y))
      (pegCount side) (pegCount y) (pegCount ax) (pegCount bx)
      hleft hnb hg hy hprod hsideP hy haxP hbxP hschN hfoldN hfitM
    simp only [movesS]
    exact hraw
  have hspent : movesS + pegCount (fieldMul t.n t.k t.benchlen y y) + pegCount side +
      pegCount y + pegCount ax + pegCount bx ≤ moves + searchMove t.n t.benchlen := by
    have hsideP := peg_len t.n side h.sideLen
    have haxP := peg_len t.n ax h.axLen
    have hbxP := peg_len t.n bx h.bxLen
    simp only [movesS, searchMove]
    exact one_check_spent moves t.n t.benchlen (pegCount gapXs) (pegCount y)
      (schoolMoves y y t.n t.n)
      (foldCharge t.n (t.n - t.k) (school t.n y y (List.replicate t.benchlen 0) false))
      (pegCount (fieldMul t.n t.k t.benchlen y y))
      (pegCount side) (pegCount y) (pegCount ax) (pegCount bx)
      hnb hg hy hprod hsideP hy haxP hbxP hschN hfoldN
  refine ⟨bS, rootHit t.n t.k t.benchlen x, movesS, ?_, rfl, ?_, hmvS, hfitTail, ?_, ?_⟩
  · have htail :
        (do
            let b ← Ecbs.marker_lift b
            let b := { b with sudo_5Board_9marker_on := false }
            let b ← Ecbs.clear b ((searchGap : Nat) : Int)
            let b ← Ecbs.mul b ((searchGap : Nat) : Int) ((searchUp : Nat) : Int)
                ((searchUp : Nat) : Int) true false false
            let b ← Ecbs.settle b
            let y2 ← Ecbs.value b ((searchGap : Nat) : Int)
            let side ← Ecbs.value b ((searchBottom : Nat) : Int)
            pure (SudoRt.SEq.beq y2 side, b)) =
          (do
            let b ← Ecbs.mul bC ((searchGap : Nat) : Int) ((searchUp : Nat) : Int)
                ((searchUp : Nat) : Int) true false false
            let b ← Ecbs.settle b
            let y2 ← Ecbs.value b ((searchGap : Nat) : Int)
            let side ← Ecbs.value b ((searchBottom : Nat) : Int)
            pure (SudoRt.SEq.beq y2 side, b)) := by
      rw [← bind_assoc, hpre, ok_bind]
    unfold searchCheck
    rw [htail, hmulEq, ok_bind, hset, ok_bind]
    have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
      rw [settle_tier_eq bM searchGap ⟨hGH, hGD⟩ lane t.n
          (mulMoves movesC y y t.n t.k t.benchlen) slides
          (mulPeak bC.sudo_5Board_4held bM.sudo_5Board_4held hspS pk),
        _htierM, htierC]
      simp [embTier]
    have hlenY : (fieldMul t.n t.k t.benchlen y y).length = t.n :=
      fieldMul_length t.n t.k t.benchlen y y hnb
    have hbotHeldS : bS.sudo_5Board_4held[searchBottom]? = some true := by
      rw [settle_held_eq bM searchGap ⟨hGH, hGD⟩ lane t.n
          (mulMoves movesC y y t.n t.k t.benchlen) slides
          (mulPeak bC.sudo_5Board_4held bM.sudo_5Board_4held hspS pk)]
      rw [Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ true
        (by decide : searchGap ≠ searchBottom)]
      rw [_hheldM]
      rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchBottom)]
      rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchBottom)]
      exact hbotd
    have hvG := value_held_refines bS searchGap (fieldMul t.n t.k t.benchlen y y) t.n
        (some_idx _ _ _ hheldS) (some_idx _ _ _ hgapS)
        (some_get _ _ _ hheldS) (some_get _ _ _ hgapS)
        hnS (Nat.le_of_eq hlenY.symm) hroom.1
    have hvB := value_held_refines bS searchBottom side t.n
        (some_idx _ _ _ hbotHeldS) (some_idx _ _ _ hbotS)
        (some_get _ _ _ hbotHeldS) (some_get _ _ _ hbotS)
        hnS (Nat.le_of_eq h.sideLen.symm) hroom.1
    have htY : (fieldMul t.n t.k t.benchlen y y).take t.n =
        fieldMul t.n t.k t.benchlen y y := by
      have htake := List.take_length (fieldMul t.n t.k t.benchlen y y)
      rwa [hlenY] at htake
    have htSide : side.take t.n = side := by
      have htake := List.take_length side
      rwa [h.sideLen] at htake
    have hvG0 := hvG
    rw [searchGap_int] at hvG0
    have hvB0 := hvB
    rw [searchBottom_int] at hvB0
    have hvG' : Ecbs.value bS Ecbs.gap =
        .ok (embed (fieldMul t.n t.k t.benchlen
          (rootY t.n t.k t.benchlen x) (rootY t.n t.k t.benchlen x))) := by
      rw [hvG0, htY, h.yIs]
    have hvB' : Ecbs.value bS Ecbs.bottom =
        .ok (embed (curveSide t.n t.k t.benchlen x)) := by
      rw [hvB0, htSide, h.sideIs]
    have hcmp := root_hit_cmp bS t.n t.k t.benchlen x hvG' hvB'
    rw [hvG, ok_bind, hvB, ok_bind, pure_eq_ok]
    have hbit : SudoRt.SEq.beq (embed ((fieldMul t.n t.k t.benchlen y y).take t.n))
        (embed (side.take t.n)) = rootHit t.n t.k t.benchlen x := by
      have hfull : SudoRt.SEq.beq
          (embed (fieldMul t.n t.k t.benchlen
            (rootY t.n t.k t.benchlen x) (rootY t.n t.k t.benchlen x)))
          (embed (curveSide t.n t.k t.benchlen x)) =
          rootHit t.n t.k t.benchlen x := by
        have hpure := hcmp
        rw [hvG', ok_bind, hvB', ok_bind, pure_eq_ok] at hpure
        injection hpure
      rw [htY, htSide, h.yIs, h.sideIs]
      exact hfull
    rw [hbit]
  · refine
      { benchOff := settle_bench_off bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul
        gapHome := by simpa [h.yIs] using hgapS
        gapHeld := hheldS
        botHome := by simpa [h.sideIs] using hbotS
        botHeld := by
          rw [settle_held_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
          rw [Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ true
            (by decide : searchGap ≠ searchBottom)]
          rw [_hheldM]
          rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchBottom)]
          rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchBottom)]
          exact hbotd
        upHome := by
          rw [show bS.sudo_5Board_4home =
              bM.sudo_5Board_4home.set ⟨searchGap, hGH⟩ (embed (lane.take t.n)) from
            settle_home_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
          rw [Array.getElem?_set_ne _ ⟨searchGap, hGH⟩ _ (by decide : searchGap ≠ searchUp)]
          have h1 : searchUp < bC.sudo_5Board_4home.size := some_idx _ _ _ hup
          have h1' : searchUp < bM.sudo_5Board_4home.size := by rw [hszHM]; exact h1
          have hget := hhomeM searchUp h1 h1' (by decide)
          rw [Array.getElem?_eq_getElem h1', hget]
          have hval : bC.sudo_5Board_4home[searchUp]'(h1) =
              embed (rootY t.n t.k t.benchlen x) := by
            exact (some_get _ _ _ hup).trans (congrArg embed h.yIs)
          exact congrArg some hval
        upHeld := by
          rw [settle_held_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
          rw [Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ true (by decide : searchGap ≠ searchUp)]
          have h1 : searchUp < bC.sudo_5Board_4held.size := some_idx _ _ _ hupd
          have h1M : bM.sudo_5Board_4held[searchUp]? = some true := by
            rw [_hheldM]
            rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchUp)]
            rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchUp)]
            exact hupd
          exact h1M
        axHome := by
          rw [show bS.sudo_5Board_4home =
              bM.sudo_5Board_4home.set ⟨searchGap, hGH⟩ (embed (lane.take t.n)) from
            settle_home_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
          rw [Array.getElem?_set_ne _ ⟨searchGap, hGH⟩ _ (by decide : searchGap ≠ searchAcross)]
          have h0 : searchAcross < bC.sudo_5Board_4home.size := some_idx _ _ _ hax
          have h0' : searchAcross < bM.sudo_5Board_4home.size := by rw [hszHM]; exact h0
          have hget := hhomeM searchAcross h0 h0' (by decide)
          rw [Array.getElem?_eq_getElem h0', hget]
          exact congrArg some (some_get _ _ _ hax)
        axHeld := by
          rw [settle_held_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
          rw [Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ true
            (by decide : searchGap ≠ searchAcross)]
          rw [_hheldM]
          rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchAcross)]
          rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchAcross)]
          exact haxd
        bxHome := by
          rw [show bS.sudo_5Board_4home =
              bM.sudo_5Board_4home.set ⟨searchGap, hGH⟩ (embed (lane.take t.n)) from
            settle_home_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
          rw [Array.getElem?_set_ne _ ⟨searchGap, hGH⟩ _ (by decide : searchGap ≠ searchBase)]
          have h3 : searchBase < bC.sudo_5Board_4home.size := some_idx _ _ _ hbx
          have h3' : searchBase < bM.sudo_5Board_4home.size := by rw [hszHM]; exact h3
          have hget := hhomeM searchBase h3 h3' (by decide)
          rw [Array.getElem?_eq_getElem h3', hget]
          exact congrArg some (some_get _ _ _ hbx)
        bxHeld := by
          rw [settle_held_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
          rw [Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ true
            (by decide : searchGap ≠ searchBase)]
          rw [_hheldM]
          rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchBase)]
          rw [Array.getElem?_set_ne _ _ _ (by decide : (6 : Nat) ≠ searchBase)]
          exact hbxd }
  · rcases hctrlStep with ⟨ctrl0, hctrl0, hctrlC⟩
    refine
      { marker := by
          rw [settle_ix_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul, _hmarkM]
          exact _hmark
        markerOn := by
          rw [settle_marker_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
          exact _hflagM
        benchOff := settle_bench_off bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul
        tier := by
          rw [settle_tier_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul, _htierM]
          exact htierC.trans h.tier.symm
        szH := by
          rw [settle_home_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul, Array.size_set, hszHM]
          exact hszHC
        szD := by
          rw [settle_held_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul, Array.size_set]
          rw [_hheldM, Array.size_set, Array.size_set]
          exact hszDC
        ctrl := ⟨ctrl0, hctrl0, by
          rw [settle_ctrl_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul, _hctrlM]
          exact hctrlC⟩
        slides := by
          refine ⟨slides, slides + 2 * pegCount (fieldMul t.n t.k t.benchlen y y), hsl, ?_, ?_⟩
          · rw [settle_slides_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
            exact congrArg (fun p => Int.ofNat (slides + 2 * p)) (congrArg pegCount hprodTake)
          · exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hprod) slides
        ops0 := ⟨c0, hop0, by
          have hS := settle_ops bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul
          have hszM : bM.sudo_5Board_4cost.sudo_5Costs_3ops.size =
              bC.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [_hopsM, Array.size_set]
          have h0 : 0 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [hszM]; exact hopsC
          have hget := get_eq_of_array _hopsM 0 h0
          simp [Array.getElem_set, ofNat_eq_natCast] at hget
          have hS0 : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [congrArg Array.size hS]; exact h0
          rw [Array.getElem?_eq_getElem hS0]
          exact congrArg some (cell_eq_of hS hget)⟩
        ops1 := by
          have hS := settle_ops bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul
          have hne : (0 : Nat) ≠ 1 := by decide
          have hset := Array.getElem?_set_ne (j := 1) bC.sudo_5Board_4cost.sudo_5Costs_3ops
            ⟨0, hopsC⟩ (Int.ofNat (c0 + 1)) hne
          have hM := congrArg (fun a => a[1]?) _hopsM
          have hBC := congrArg (fun a => a[1]?) hopsBC
          exact (congrArg (fun a => a[1]?) hS).trans (hM.trans (hset.trans hBC))
        opsSz := by
          have hS := settle_ops bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul
          have hszM : bM.sudo_5Board_4cost.sudo_5Costs_3ops.size =
              bC.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
            rw [_hopsM, Array.size_set]
          rw [congrArg Array.size hS, hszM]
          exact congrArg Array.size hopsBC
        mx := by
          rw [settle_mx_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul, _hmxM, hmxBC]
        spare := by
          rw [settle_held_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul]
          rw [Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ true (by decide : searchGap ≠ 6)]
          rw [_hheldM, Array.getElem?_eq_getElem (by
            rw [Array.size_set, Array.size_set]; exact hspS)]
          simp [Array.getElem_set]
        peak := ⟨_, settle_peak_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul hpkN⟩
        strict := ⟨_, (settle_strict_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul).trans _hstM⟩
        hole := ⟨_, (settle_hole_eq bM searchGap ⟨hGH, hGD⟩ lane t.n mvMul slides pkMul).trans _hholeM⟩ }
  · exact ⟨moves, hmv, hspent⟩

/-- One held home, emptied. Every other home and flag stays. -/
private theorem clear_next (b : Ecbs.Board) (home : Nat) (xs : List Nat) (moves : Nat)
    (hhome : b.sudo_5Board_4home[home]? = some (embed xs))
    (hheld? : b.sudo_5Board_4held[home]? = some true)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hf : FitsLen xs.length)
    (hfit : FitsLen (moves + pegCount xs)) :
    ∃ b',
      Ecbs.clear b (home : Int) = .ok b' ∧
      b'.sudo_5Board_4home[home]? = some (#[] : Array Int) ∧
      b'.sudo_5Board_4held[home]? = some false ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (moves + pegCount xs) ∧
      (∀ j v, home ≠ j → b.sudo_5Board_4home[j]? = some v →
        b'.sudo_5Board_4home[j]? = some v) ∧
      (∀ j v, home ≠ j → b.sudo_5Board_4held[j]? = some v →
        b'.sudo_5Board_4held[j]? = some v) := by
  have hH := some_idx _ _ _ hhome
  have hD := some_idx _ _ _ hheld?
  have harr := some_get _ _ _ hhome
  have hheld := some_get _ _ _ hheld?
  have hm' : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa [ofNat_eq_natCast] using hm
  have hcl := clear_held_refines b home xs moves hH hD hheld harr hm' hf hfit
  let b' := { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ #[]
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ false
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (moves + pegCount xs) } }
  refine ⟨b', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcl
  · simp only [b']
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hH)]
    simp [Array.getElem_set]
  · simp only [b']
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hD)]
    simp [Array.getElem_set]
  · simp [b']
  · intro j v hne hj
    simp only [b']
    rw [Array.getElem?_set_ne _ ⟨home, hH⟩ _ hne]
    exact hj
  · intro j v hne hj
    simp only [b']
    rw [Array.getElem?_set_ne _ ⟨home, hD⟩ _ hne]
    exact hj

/-- The five clears after a miss. Gap, bottom, up, across, then the base home. -/
theorem search_miss_clear (b : Ecbs.Board)
    (gapXs side y ax bx : List Nat) (moves : Nat)
    (hgap : b.sudo_5Board_4home[searchGap]? = some (embed gapXs))
    (hgapD : b.sudo_5Board_4held[searchGap]? = some true)
    (hbot : b.sudo_5Board_4home[searchBottom]? = some (embed side))
    (hbotD : b.sudo_5Board_4held[searchBottom]? = some true)
    (hup : b.sudo_5Board_4home[searchUp]? = some (embed y))
    (hupD : b.sudo_5Board_4held[searchUp]? = some true)
    (hax : b.sudo_5Board_4home[searchAcross]? = some (embed ax))
    (haxD : b.sudo_5Board_4held[searchAcross]? = some true)
    (hbx : b.sudo_5Board_4home[searchBase]? = some (embed bx))
    (hbxD : b.sudo_5Board_4held[searchBase]? = some true)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hfg : FitsLen gapXs.length) (hfs : FitsLen side.length) (hfy : FitsLen y.length)
    (hfa : FitsLen ax.length) (hfb : FitsLen bx.length)
    (hfit : FitsLen (moves + pegCount gapXs + pegCount side + pegCount y +
      pegCount ax + pegCount bx)) :
    ∃ bM, searchMiss b = .ok bM ∧ MissAt bM := by
  have hfit1 : FitsLen (moves + pegCount gapXs) := FitsLen.of_le hfit (by omega)
  obtain ⟨b1, hc1, hgapE, hgapF, hmv1, hH1, hD1⟩ :=
    clear_next b searchGap gapXs moves hgap hgapD hm hfg hfit1
  have hbot1 := hH1 searchBottom (embed side) (by decide) hbot
  have hbotD1 := hD1 searchBottom true (by decide) hbotD
  have hup1 := hH1 searchUp (embed y) (by decide) hup
  have hupD1 := hD1 searchUp true (by decide) hupD
  have hax1 := hH1 searchAcross (embed ax) (by decide) hax
  have haxD1 := hD1 searchAcross true (by decide) haxD
  have hbx1 := hH1 searchBase (embed bx) (by decide) hbx
  have hbxD1 := hD1 searchBase true (by decide) hbxD
  have hfit2 : FitsLen (moves + pegCount gapXs + pegCount side) :=
    FitsLen.of_le hfit (by omega)
  obtain ⟨b2, hc2, hbotE, hbotF, hmv2, hH2, hD2⟩ :=
    clear_next b1 searchBottom side (moves + pegCount gapXs) hbot1 hbotD1 hmv1 hfs hfit2
  have hgap2 := hH2 searchGap (#[] : Array Int) (by decide) hgapE
  have hgapF2 := hD2 searchGap false (by decide) hgapF
  have hup2 := hH2 searchUp (embed y) (by decide) hup1
  have hupD2 := hD2 searchUp true (by decide) hupD1
  have hax2 := hH2 searchAcross (embed ax) (by decide) hax1
  have haxD2 := hD2 searchAcross true (by decide) haxD1
  have hbx2 := hH2 searchBase (embed bx) (by decide) hbx1
  have hbxD2 := hD2 searchBase true (by decide) hbxD1
  have hfit3 : FitsLen (moves + pegCount gapXs + pegCount side + pegCount y) :=
    FitsLen.of_le hfit (by omega)
  obtain ⟨b3, hc3, hupE, hupF, hmv3, hH3, hD3⟩ :=
    clear_next b2 searchUp y (moves + pegCount gapXs + pegCount side) hup2 hupD2 hmv2 hfy hfit3
  have hgap3 := hH3 searchGap (#[] : Array Int) (by decide) hgap2
  have hgapF3 := hD3 searchGap false (by decide) hgapF2
  have hbot3 := hH3 searchBottom (#[] : Array Int) (by decide) hbotE
  have hbotF3 := hD3 searchBottom false (by decide) hbotF
  have hax3 := hH3 searchAcross (embed ax) (by decide) hax2
  have haxD3 := hD3 searchAcross true (by decide) haxD2
  have hbx3 := hH3 searchBase (embed bx) (by decide) hbx2
  have hbxD3 := hD3 searchBase true (by decide) hbxD2
  have hfit4 : FitsLen (moves + pegCount gapXs + pegCount side + pegCount y + pegCount ax) :=
    FitsLen.of_le hfit (by omega)
  obtain ⟨b4, hc4, haxE, haxF, hmv4, hH4, hD4⟩ :=
    clear_next b3 searchAcross ax
      (moves + pegCount gapXs + pegCount side + pegCount y) hax3 haxD3 hmv3 hfa hfit4
  have hgap4 := hH4 searchGap (#[] : Array Int) (by decide) hgap3
  have hgapF4 := hD4 searchGap false (by decide) hgapF3
  have hbot4 := hH4 searchBottom (#[] : Array Int) (by decide) hbot3
  have hbotF4 := hD4 searchBottom false (by decide) hbotF3
  have hup4 := hH4 searchUp (#[] : Array Int) (by decide) hupE
  have hupF4 := hD4 searchUp false (by decide) hupF
  have hbx4 := hH4 searchBase (embed bx) (by decide) hbx3
  have hbxD4 := hD4 searchBase true (by decide) hbxD3
  obtain ⟨b5, hc5, hbxE, hbxF, _, hH5, hD5⟩ :=
    clear_next b4 searchBase bx
      (moves + pegCount gapXs + pegCount side + pegCount y + pegCount ax)
      hbx4 hbxD4 hmv4 hfb hfit
  refine ⟨b5, ?_, ?_⟩
  · unfold searchMiss
    rw [hc1, ok_bind, hc2, ok_bind, hc3, ok_bind, hc4, ok_bind, hc5]
  · exact
      { gapHeld := hD5 searchGap false (by decide) hgapF4
        botHeld := hD5 searchBottom false (by decide) hbotF4
        upHeld := hD5 searchUp false (by decide) hupF4
        axHeld := hD5 searchAcross false (by decide) haxF
        bxHeld := hbxF
        gapHome := hH5 searchGap (#[] : Array Int) (by decide) hgap4
        botHome := hH5 searchBottom (#[] : Array Int) (by decide) hbot4
        upHome := hH5 searchUp (#[] : Array Int) (by decide) hup4
        axHome := hH5 searchAcross (#[] : Array Int) (by decide) haxE
        bxHome := hbxE }

/-- A hit. The compare bit is true and the squared root is still seated. -/
theorem search_hit_at (b : Ecbs.Board) (t : Spec.Tier)
    (x y side gapXs ax bx : List Nat) (left : Nat)
    (h : SearchAt b t x y side gapXs ax bx left)
    (hh : rootHit t.n t.k t.benchlen x = true) :
    ∃ b', searchCheck b = .ok (true, b') ∧ HitAt b' t x ax bx := by
  obtain ⟨b', bit, _, hck, hbit, hhit, _, _, _, _⟩ :=
    search_check_at b t x y side gapXs ax bx left h
  have htrue : bit = true := by rw [hbit, hh]
  refine ⟨b', ?_, hhit⟩
  simpa [htrue] using hck

/-- A miss. The compare bit is false, then the five homes are emptied. -/
theorem search_miss_at (b : Ecbs.Board) (t : Spec.Tier)
    (x y side gapXs ax bx : List Nat) (left : Nat)
    (h : SearchAt b t x y side gapXs ax bx left)
    (hh : rootHit t.n t.k t.benchlen x = false) :
    ∃ b' bM,
      searchCheck b = .ok (false, b') ∧
      HitAt b' t x ax bx ∧
      searchMiss b' = .ok bM ∧
      MissAt bM := by
  obtain ⟨b', bit, movesS, hck, hbit, hhit, hmv, hfit, _, _⟩ :=
    search_check_at b t x y side gapXs ax bx left h
  have hfalse : bit = false := by rw [hbit, hh]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hleft0, hfitM0, _, _, _⟩ :=
    h.pack
  have hfn : FitsLen t.n := by
    apply FitsLen.of_le hfitM0
    unfold searchMove
    have h1 : t.n ≤ t.n * t.n + 8 * t.n + 6 * t.benchlen := by omega
    have hmul : t.n * t.n + 8 * t.n + 6 * t.benchlen ≤
        (t.n * t.n + 8 * t.n + 6 * t.benchlen) * left :=
      Nat.le_mul_of_pos_right _ hleft0
    exact Nat.le_trans (Nat.le_trans h1 hmul) (Nat.le_add_left _ _)
  have hnb : t.n ≤ t.benchlen := mul_span_n t.n t.benchlen h.nPos h.sat.mul_span
  have hlenY : (fieldMul t.n t.k t.benchlen y y).length = t.n :=
    fieldMul_length t.n t.k t.benchlen y y hnb
  have hgap : b'.sudo_5Board_4home[searchGap]? =
      some (embed (fieldMul t.n t.k t.benchlen y y)) := by
    simpa [h.yIs] using hhit.gapHome
  have hbot : b'.sudo_5Board_4home[searchBottom]? = some (embed side) := by
    simpa [h.sideIs] using hhit.botHome
  have hup : b'.sudo_5Board_4home[searchUp]? = some (embed y) := by
    simpa [h.yIs] using hhit.upHome
  have hfg : FitsLen (fieldMul t.n t.k t.benchlen y y).length := by
    rw [hlenY]; exact hfn
  have hfs : FitsLen side.length := by rw [h.sideLen]; exact hfn
  have hfy : FitsLen y.length := by rw [h.yLen]; exact hfn
  have hfa : FitsLen ax.length := by rw [h.axLen]; exact hfn
  have hfb : FitsLen bx.length := by rw [h.bxLen]; exact hfn
  obtain ⟨bM, hm, hmiss⟩ := search_miss_clear b'
    (fieldMul t.n t.k t.benchlen y y) side y ax bx movesS
    hgap hhit.gapHeld hbot hhit.botHeld hup hhit.upHeld
    hhit.axHome hhit.axHeld hhit.bxHome hhit.bxHeld
    hmv hfg hfs hfy hfa hfb hfit
  refine ⟨b', bM, ?_, hhit, hm, hmiss⟩
  simpa [hfalse] using hck

/-- One hole, the way one digit steps `PowAt`. A hit stops on `HitAt`.
    A miss empties the five homes. -/
theorem search_step_at (b : Ecbs.Board) (t : Spec.Tier)
    (x y side gapXs ax bx : List Nat) (left : Nat)
    (h : SearchAt b t x y side gapXs ax bx left) :
    (∃ b', searchCheck b = .ok (true, b') ∧ HitAt b' t x ax bx ∧
        rootHit t.n t.k t.benchlen x = true) ∨
    (∃ b' bM, searchCheck b = .ok (false, b') ∧ HitAt b' t x ax bx ∧
        searchMiss b' = .ok bM ∧ MissAt bM ∧
        rootHit t.n t.k t.benchlen x = false) := by
  by_cases hh : rootHit t.n t.k t.benchlen x = true
  · left
    obtain ⟨b', hck, hhit⟩ := search_hit_at b t x y side gapXs ax bx left h hh
    exact ⟨b', hck, hhit, hh⟩
  · right
    have hf : rootHit t.n t.k t.benchlen x = false := by
      cases hb : rootHit t.n t.k t.benchlen x with
      | false => rfl
      | true => exact absurd hb hh
    obtain ⟨b', bM, hck, hhit, hm, hmiss⟩ :=
      search_miss_at b t x y side gapXs ax bx left h hf
    exact ⟨b', bM, hck, hhit, hm, hmiss, hf⟩

end EcbsLink2.Link2
