/-
  The board `cofactor_seat` leaves is the board a cofactor walk starts from.
  Homes 3 and 4 hold the base point, the accumulator homes are empty, and
  the painted frame survived the clears and the band move. The four-cell
  budget still fits on top of the search. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchCofactor
import EcbsLink2.Link2.CofactorRoom

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem peg_n (n : Nat) (xs : List Nat) (h : xs.length = n) : pegCount xs ≤ n :=
  Nat.le_trans (pegCount_le xs) (by omega)

private theorem read_held (b : Board) (i : Nat) (v : Bool)
    (hsz : b.sudo_5Board_4held.size = 8) (hi : i < 8)
    (h : b.sudo_5Board_4held[i]? = some v) :
    b.sudo_5Board_4held[i]'(by rw [hsz]; exact hi) = v := by
  rw [Array.getElem?_eq_getElem (by rw [hsz]; exact hi)] at h
  injection h

private theorem read_home (b : Board) (i : Nat) (v : Array Int)
    (hsz : b.sudo_5Board_4home.size = 8) (hi : i < 8)
    (h : b.sudo_5Board_4home[i]? = some v) :
    b.sudo_5Board_4home[i]'(by rw [hsz]; exact hi) = v := by
  rw [Array.getElem?_eq_getElem (by rw [hsz]; exact hi)] at h
  injection h

private theorem under_cap (a a0 c : Nat) (ha : a ≤ a0) (h : FitsLen (a0 + c)) :
    FitsLen (a + c) :=
  FitsLen.of_le h (by omega)

/-- After a hit, the seated root is a `ChordAt`. The search scalar is `x`;
    the point in homes 3 and 4 is `(bx, rootY x)`. -/
theorem hit_chordAt (b : Board) (t : Spec.Tier) (x ax bx : List Nat)
    (moves slides ctrl ops peak : Nat)
    (h : HitAt b t x ax bx)
    (hframe : PaintFrame b t)
    (htier : b.sudo_5Board_1t = embTier t)
    (hspare : b.sudo_5Board_4held[searchSpare]? = some false)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hmark : b.sudo_5Board_6marker = -1)
    (hctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int))
    (hbx : bx.length = t.n)
    (hy : (rootY t.n t.k t.benchlen x).length = t.n)
    (hside : (curveSide t.n t.k t.benchlen x).length = t.n)
    (hgapL : (fieldMul t.n t.k t.benchlen (rootY t.n t.k t.benchlen x)
        (rootY t.n t.k t.benchlen x)).length = t.n)
    (haxL : ax.length = t.n)
    (hf : FitsLen t.n)
    (hfit2 : FitsLen (2 * pegCount (rootY t.n t.k t.benchlen x)))
    (hfit : FitsLen (moves +
        pegCount (fieldMul t.n t.k t.benchlen (rootY t.n t.k t.benchlen x)
          (rootY t.n t.k t.benchlen x)) +
        pegCount (curveSide t.n t.k t.benchlen x) + pegCount ax +
        2 * pegCount (rootY t.n t.k t.benchlen x)))
    (hfitS : FitsLen (slides + 2 * pegCount (rootY t.n t.k t.benchlen x)))
    (hmvLe : moves ≤ perHole t.n t.benchlen * t.n)
    (hslLe : slides ≤ perSlide t.n * t.n)
    (hctrlLe : ctrl ≤ tierR t + perCtrl t.n * t.n)
    (hopsLe : ops ≤ perOp t.n * t.n)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious) :
    ∃ bS mvS pkS slS,
      cofactorSeat b = .ok bS ∧
      ChordAt bS t bx (rootY t.n t.k t.benchlen x) mvS pkS ∧
      mvS = moves +
        pegCount (fieldMul t.n t.k t.benchlen (rootY t.n t.k t.benchlen x)
          (rootY t.n t.k t.benchlen x)) +
        pegCount (curveSide t.n t.k t.benchlen x) + pegCount ax +
        2 * pegCount (rootY t.n t.k t.benchlen x) ∧
      slS = slides + 2 * pegCount (rootY t.n t.k t.benchlen x) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slS ∧
      bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
      FitsLen (mvS + walkCharge t * cofactorSpan) ∧
      FitsLen (slS + cellSlideCharge t * cofactorSpan) ∧
      FitsLen (ctrl + cellCtrlCharge t * cofactorSpan) ∧
      FitsLen (ops + cellOpsCharge t * cofactorSpan) := by
  let y := rootY t.n t.k t.benchlen x
  obtain ⟨bS, mvS, pkS, hseat, hszHS, hszDS, h0, h1, h3t, h3a, h4t, h4a, _hmvS, hmvEq,
      hpkS, hmarkS, _hnS, hslS, hfr, htS, hoffS, h2, h5, h6, hctrlS⟩ :=
    cofactor_seat b t x ax bx moves slides peak h hframe htier hspare hszH hszD
      hm hsl hpk hmark hn hy hside hgapL haxL hf hfit2 hfit hfitS
  have h0e := read_held bS 0 false hszDS (by decide) h0
  have h1e := read_held bS 1 false hszDS (by decide) h1
  have h2e := read_held bS 2 false hszDS (by decide) (by simpa [searchBottom] using h2)
  have h5e := read_held bS 5 false hszDS (by decide) (by simpa [searchGap] using h5)
  have h6e := read_held bS 6 false hszDS (by decide) (by simpa [searchSpare] using h6)
  have h3te := read_held bS 3 true hszDS (by decide) h3t
  have h4te := read_held bS 4 true hszDS (by decide) h4t
  have h3ae := read_home bS 3 (embed bx) hszHS (by decide) h3a
  have h4ae := read_home bS 4 (embed y) hszHS (by decide) (by simpa [y] using h4a)
  let slS := slides + 2 * pegCount y
  have hslEq : slS = slides + 2 * pegCount (rootY t.n t.k t.benchlen x) := by
    simp [slS, y]
  have hmvI : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    simpa [ofNat_eq_natCast] using _hmvS
  have hpkI : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (pkS : Int) := by
    simpa [ofNat_eq_natCast] using hpkS
  have hAt : ChordAt bS t bx y mvS pkS :=
    { frame := hfr
      szH := hszHS
      szD := hszDS
      bench := hoffS
      marker := hmarkS
      tier := htS
      tierN := by rw [htS]; simp [embTier, ofNat_eq_natCast]
      hmoves := hmvI
      hpeak := hpkI
      held0 := h0e
      held1 := h1e
      held2 := h2e
      held5 := h5e
      held6 := h6e
      held3 := h3te
      home3 := h3ae
      held4 := h4te
      home4 := h4ae }
  have hroom := cofactor_after_seat t hship
  have hgapP := peg_n t.n _ hgapL
  have hsideP := peg_n t.n _ hside
  have haxP := peg_n t.n _ haxL
  have hyP := peg_n t.n y hy
  have hmvCap : mvS ≤ perHole t.n t.benchlen * t.n + 5 * t.n := by
    rw [hmvEq]
    simp only [y] at hgapP hyP
    omega
  have hslCap : slS ≤ perSlide t.n * t.n + 2 * t.n := by
    simp only [slS, y]
    omega
  refine ⟨bS, mvS, pkS, slS, hseat, by simpa [y] using hAt, hmvEq, hslEq,
    by simpa [slS, y] using hslS, hctrlS.trans hctrl, ?_, ?_, ?_, ?_⟩
  · exact under_cap _ _ _ hmvCap hroom.1
  · exact under_cap _ _ _ hslCap hroom.2.1
  · exact under_cap _ _ _ hctrlLe hroom.2.2.1
  · exact under_cap _ _ _ hopsLe hroom.2.2.2

end EcbsLink2.Link2
