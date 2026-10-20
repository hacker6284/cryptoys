/-
  After a hit the card clears the gap, the bottom, and the across, then
  `move_band` writes the root up into `base_up`. Home 4 started empty, so
  `need_empty` succeeds. The board it leaves is the one
  `chord_fresh_white_down` copies into across and up.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchAt
import EcbsLink2.Link2.ChordUp
import EcbsLink2.Link2.WalkChord
import EcbsLink2.Link2.WalkLoop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- Clear gap, bottom, and across, then move the up home into `base_up`. -/
def cofactorSeat (b : Board) : Except SudoRt.Trap Board :=
  do
    let b ← clear b gap
    let b ← clear b bottom
    let b ← clear b across
    move_band b base_up up

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

private theorem fit_seat (a b c d e : Nat) (h : FitsLen (a + b + c + d + e)) :
    FitsLen (a + b) ∧ FitsLen (a + b + c) ∧ FitsLen (a + b + c + d) := by
  exact ⟨FitsLen.of_le h (by omega), FitsLen.of_le h (by omega),
    FitsLen.of_le h (by omega)⟩

private theorem keepH (b : Board) (i j : Nat) (v : Array Int)
    (hi : i < b.sudo_5Board_4home.size) (hne : i ≠ j)
    (hj : b.sudo_5Board_4home[j]? = some v) :
    (b.sudo_5Board_4home.set ⟨i, hi⟩ (#[] : Array Int))[j]? = some v :=
  (Array.getElem?_set_ne _ ⟨i, hi⟩ _ hne).trans hj

/-- A hit board. Three clears, then `move_band` of the root up into home 4. -/
theorem cofactor_seat (b : Board) (t : Spec.Tier) (x ax bx : List Nat)
    (moves slides peak : Nat)
    (h : HitAt b t x ax bx)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hmark : b.sudo_5Board_6marker = -1)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int))
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
    (hfitS : FitsLen (slides + 2 * pegCount (rootY t.n t.k t.benchlen x))) :
    ∃ bS mvS pkS,
      cofactorSeat b = .ok bS ∧
      bS.sudo_5Board_4home.size = 8 ∧
      bS.sudo_5Board_4held.size = 8 ∧
      bS.sudo_5Board_4held[0]? = some false ∧
      bS.sudo_5Board_4held[1]? = some false ∧
      bS.sudo_5Board_4held[3]? = some true ∧
      bS.sudo_5Board_4home[3]? = some (embed bx) ∧
      bS.sudo_5Board_4held[4]? = some true ∧
      bS.sudo_5Board_4home[4]? = some (embed (rootY t.n t.k t.benchlen x)) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvS ∧
      mvS = moves +
        pegCount (fieldMul t.n t.k t.benchlen (rootY t.n t.k t.benchlen x)
          (rootY t.n t.k t.benchlen x)) +
        pegCount (curveSide t.n t.k t.benchlen x) + pegCount ax +
        2 * pegCount (rootY t.n t.k t.benchlen x) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkS ∧
      bS.sudo_5Board_6marker = -1 ∧
      bS.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) ∧
      bS.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat
        (slides + 2 * pegCount (rootY t.n t.k t.benchlen x)) := by
  let y := rootY t.n t.k t.benchlen x
  let side := curveSide t.n t.k t.benchlen x
  let gapXs := fieldMul t.n t.k t.benchlen y y
  have hup : b.sudo_5Board_4home[searchUp]? = some (embed y) := by
    simpa [y] using h.upHome
  have hupD : b.sudo_5Board_4held[searchUp]? = some true := h.upHeld
  have hbot : b.sudo_5Board_4home[searchBottom]? = some (embed side) := by
    simpa [side] using h.botHome
  have hbotD : b.sudo_5Board_4held[searchBottom]? = some true := h.botHeld
  have hgap : b.sudo_5Board_4home[searchGap]? = some (embed gapXs) := by
    simpa [y, gapXs] using h.gapHome
  have hgapD : b.sudo_5Board_4held[searchGap]? = some true := h.gapHeld
  have hax : b.sudo_5Board_4home[searchAcross]? = some (embed ax) := h.axHome
  have haxD : b.sudo_5Board_4held[searchAcross]? = some true := h.axHeld
  have hbxH : b.sudo_5Board_4home[searchBase]? = some (embed bx) := h.bxHome
  have hbxD : b.sudo_5Board_4held[searchBase]? = some true := h.bxHeld
  have hbu : b.sudo_5Board_4home[4]? = some (#[] : Array Int) := h.buHome
  have hbuD : b.sudo_5Board_4held[4]? = some false := h.buOff
  have hG := some_idx _ _ _ hgap
  have hGD := some_idx _ _ _ hgapD
  have hB := some_idx _ _ _ hbot
  have hBD := some_idx _ _ _ hbotD
  have hA := some_idx _ _ _ hax
  have hAD := some_idx _ _ _ haxD
  have hmvI : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa [ofNat_eq_natCast] using hm
  have hfits := fit_seat moves (pegCount gapXs) (pegCount side) (pegCount ax)
      (2 * pegCount y) (by simpa [y, gapXs, side] using hfit)
  have hfG : FitsLen gapXs.length := by rw [hgapL]; simpa [y, gapXs] using hf
  have hfS : FitsLen side.length := by rw [hside]; simpa [side] using hf
  have hfA : FitsLen ax.length := by rw [haxL]; exact hf
  have hfY : FitsLen y.length := by rw [hy]; simpa [y] using hf
  have hclearG := clear_held_refines b searchGap gapXs moves hG hGD
      (some_get _ _ _ hgapD) (some_get _ _ _ hgap) hmvI hfG hfits.1
  let b1 := { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨searchGap, hG⟩ #[]
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨searchGap, hGD⟩ false
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (moves + pegCount gapXs) } }
  have hB1 : searchBottom < b1.sudo_5Board_4home.size := by
    simp only [b1, Array.size_set]; exact hB
  have hBD1 : searchBottom < b1.sudo_5Board_4held.size := by
    simp only [b1, Array.size_set]; exact hBD
  have hbot1 : b1.sudo_5Board_4home[searchBottom]? = some (embed side) := by
    simpa [b1] using keepH b searchGap searchBottom (embed side) hG (by decide) hbot
  have hbotD1 : b1.sudo_5Board_4held[searchBottom]? = some true := by
    simpa [b1] using
      (Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ false (by decide : searchGap ≠ searchBottom)).trans
        hbotD
  have hmv1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves =
      (moves + pegCount gapXs : Int) := by
    simp [b1, ofNat_eq_natCast]
  have hclearB := clear_held_refines b1 searchBottom side (moves + pegCount gapXs)
      hB1 hBD1 (some_get _ _ _ hbotD1) (some_get _ _ _ hbot1) hmv1 hfS hfits.2.1
  let b2 := { b1 with
    sudo_5Board_4home := b1.sudo_5Board_4home.set ⟨searchBottom, hB1⟩ #[]
    sudo_5Board_4held := b1.sudo_5Board_4held.set ⟨searchBottom, hBD1⟩ false
    sudo_5Board_4cost := { b1.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (moves + pegCount gapXs + pegCount side) } }
  have hA2 : searchAcross < b2.sudo_5Board_4home.size := by
    simp only [b2, b1, Array.size_set]; exact hA
  have hAD2 : searchAcross < b2.sudo_5Board_4held.size := by
    simp only [b2, b1, Array.size_set]; exact hAD
  have hax2 : b2.sudo_5Board_4home[searchAcross]? = some (embed ax) := by
    have h1 := keepH b searchGap searchAcross (embed ax) hG (by decide) hax
    simpa [b2, b1] using keepH b1 searchBottom searchAcross (embed ax) hB1 (by decide)
      (by simpa [b1] using h1)
  have haxD2 : b2.sudo_5Board_4held[searchAcross]? = some true := by
    simp only [b2, b1]
    rw [Array.getElem?_set_ne _ ⟨searchBottom, hBD1⟩ false
      (by decide : searchBottom ≠ searchAcross)]
    rw [Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ false
      (by decide : searchGap ≠ searchAcross)]
    exact haxD
  have hmv2 : b2.sudo_5Board_4cost.sudo_5Costs_5moves =
      (moves + pegCount gapXs + pegCount side : Int) := by
    simp [b2, ofNat_eq_natCast]
  have hclearA := clear_held_refines b2 searchAcross ax
      (moves + pegCount gapXs + pegCount side) hA2 hAD2
      (some_get _ _ _ haxD2) (some_get _ _ _ hax2) hmv2 hfA hfits.2.2
  let b3 := { b2 with
    sudo_5Board_4home := b2.sudo_5Board_4home.set ⟨searchAcross, hA2⟩ #[]
    sudo_5Board_4held := b2.sudo_5Board_4held.set ⟨searchAcross, hAD2⟩ false
    sudo_5Board_4cost := { b2.sudo_5Board_4cost with
      sudo_5Costs_5moves :=
        Int.ofNat (moves + pegCount gapXs + pegCount side + pegCount ax) } }
  have hmv3 : b3.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + pegCount gapXs + pegCount side + pegCount ax) := by
    simp [b3]
  have hsl3 : b3.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simp [b3, b2, b1, hsl]
  have hpk3 : b3.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simp [b3, b2, b1, hpk]
  have hmark3 : b3.sudo_5Board_6marker = -1 := by simp [b3, b2, b1, hmark]
  have hn3 : b3.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    simp [b3, b2, b1, hn]
  have hoff3 : b3.sudo_5Board_8bench_on = false := by
    simp [b3, b2, b1, h.benchOff]
  have hszH3 : b3.sudo_5Board_4home.size = 8 := by
    simp only [b3, b2, b1, Array.size_set]; exact hszH
  have hszD3 : b3.sudo_5Board_4held.size = 8 := by
    simp only [b3, b2, b1, Array.size_set]; exact hszD
  have h4H : 4 < b3.sudo_5Board_4home.size := by rw [hszH3]; decide
  have h4D : 4 < b3.sudo_5Board_4held.size := by rw [hszD3]; decide
  have h1H : searchUp < b3.sudo_5Board_4home.size := by rw [hszH3]; decide
  have h1D : searchUp < b3.sudo_5Board_4held.size := by rw [hszD3]; decide
  have h7 : 7 ≤ b3.sudo_5Board_4held.size := by rw [hszD3]; decide
  have hup3 : b3.sudo_5Board_4home[searchUp]? = some (embed y) := by
    simp only [b3, b2, b1]
    rw [Array.getElem?_set_ne _ ⟨searchAcross, hA2⟩ _ (by decide : searchAcross ≠ searchUp)]
    rw [Array.getElem?_set_ne _ ⟨searchBottom, hB1⟩ _ (by decide : searchBottom ≠ searchUp)]
    rw [Array.getElem?_set_ne _ ⟨searchGap, hG⟩ _ (by decide : searchGap ≠ searchUp)]
    exact hup
  have hupD3 : b3.sudo_5Board_4held[searchUp]? = some true := by
    simp only [b3, b2, b1]
    rw [Array.getElem?_set_ne _ ⟨searchAcross, hAD2⟩ false
      (by decide : searchAcross ≠ searchUp)]
    rw [Array.getElem?_set_ne _ ⟨searchBottom, hBD1⟩ false
      (by decide : searchBottom ≠ searchUp)]
    rw [Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ false
      (by decide : searchGap ≠ searchUp)]
    exact hupD
  have hbu3 : b3.sudo_5Board_4held[4]? = some false := by
    simp only [b3, b2, b1]
    rw [Array.getElem?_set_ne _ ⟨searchAcross, hAD2⟩ false (by decide : searchAcross ≠ 4)]
    rw [Array.getElem?_set_ne _ ⟨searchBottom, hBD1⟩ false (by decide : searchBottom ≠ 4)]
    rw [Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ false (by decide : searchGap ≠ 4)]
    exact hbuD
  have hbx3 : b3.sudo_5Board_4home[searchBase]? = some (embed bx) := by
    simp only [b3, b2, b1]
    rw [Array.getElem?_set_ne _ ⟨searchAcross, hA2⟩ _ (by decide : searchAcross ≠ searchBase)]
    rw [Array.getElem?_set_ne _ ⟨searchBottom, hB1⟩ _ (by decide : searchBottom ≠ searchBase)]
    rw [Array.getElem?_set_ne _ ⟨searchGap, hG⟩ _ (by decide : searchGap ≠ searchBase)]
    exact hbxH
  have hbxD3 : b3.sudo_5Board_4held[searchBase]? = some true := by
    simp only [b3, b2, b1]
    rw [Array.getElem?_set_ne _ ⟨searchAcross, hAD2⟩ false
      (by decide : searchAcross ≠ searchBase)]
    rw [Array.getElem?_set_ne _ ⟨searchBottom, hBD1⟩ false
      (by decide : searchBottom ≠ searchBase)]
    rw [Array.getElem?_set_ne _ ⟨searchGap, hGD⟩ false
      (by decide : searchGap ≠ searchBase)]
    exact hbxD
  have h0D3 : b3.sudo_5Board_4held[searchAcross]? = some false := by
    simp only [b3]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hAD2)]
    simp [Array.getElem_set]
  have hempty : b3.sudo_5Board_4held[4] = false := by
    have hget := some_get _ _ _ hbu3
    simpa [h4D] using hget
  have hsrc : b3.sudo_5Board_4held[searchUp] = true := by
    have hget := some_get _ _ _ hupD3
    simpa [h1D] using hget
  have harr : b3.sudo_5Board_4home[searchUp] = embed y := by
    have hget := some_get _ _ _ hup3
    simpa [h1H] using hget
  have hmv3I : b3.sudo_5Board_4cost.sudo_5Costs_5moves =
      (moves + pegCount gapXs + pegCount side + pegCount ax : Int) := by
    simp [ofNat_eq_natCast, hmv3]
  have hfitM : FitsLen (moves + pegCount gapXs + pegCount side + pegCount ax +
      2 * pegCount y) := by
    simpa [y, gapXs, side, Nat.add_assoc] using hfit
  have hmove := move_band_off b3 4 searchUp y
      (moves + pegCount gapXs + pegCount side + pegCount ax) slides peak
      hoff3 h4H h4D h1H h1D h7 hempty hsrc harr hfY hmv3I hsl3 hpk3 hfit2 hfitM
      (by simpa [y] using hfitS)
  let mv3 := moves + pegCount gapXs + pegCount side + pegCount ax
  let bS := moveBandBoard b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak
  have hseat : cofactorSeat b = .ok bS := by
    unfold cofactorSeat
    rw [show gap = ((searchGap : Nat) : Int) from rfl, hclearG, ok_bind]
    rw [show bottom = ((searchBottom : Nat) : Int) from rfl]
    have hB' : Ecbs.clear b1 ((searchBottom : Nat) : Int) = .ok b2 := by
      simpa [b2] using hclearB
    rw [hB', ok_bind]
    rw [show across = ((searchAcross : Nat) : Int) from rfl]
    have hA' : Ecbs.clear b2 ((searchAcross : Nat) : Int) = .ok b3 := by
      simpa [b3] using hclearA
    rw [hA', ok_bind]
    simpa [bS, mv3] using hmove
  obtain ⟨pkS, hpkS⟩ := moveBand_peak_nat b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak hpk3
  refine ⟨bS, mv3 + 2 * pegCount y, pkS, hseat, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [moveBand_home b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak]
    simp [Array.size_set, hszH3]
  · rw [moveBand_held b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak]
    simp [Array.size_set, hszD3]
  · rw [moveBand_held b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (4 : Nat) ≠ 0)]
    rw [Array.getElem?_set_ne _ _ _ (by decide : searchUp ≠ 0)]
    exact h0D3
  · rw [moveBand_held b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (4 : Nat) ≠ searchUp)]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set]; exact h1D)]
    simp [searchUp, Array.getElem_set]
  · rw [moveBand_held b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (4 : Nat) ≠ searchBase)]
    rw [Array.getElem?_set_ne _ _ _ (by decide : searchUp ≠ searchBase)]
    exact hbxD3
  · rw [moveBand_home b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak]
    rw [Array.getElem?_set_ne _ _ _ (by decide : (4 : Nat) ≠ searchBase)]
    rw [Array.getElem?_set_ne _ _ _ (by decide : searchUp ≠ searchBase)]
    exact hbx3
  · rw [moveBand_held b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set, Array.size_set]; exact h4D)]
    simp [Array.getElem_set]
  · rw [moveBand_home b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak]
    rw [Array.getElem?_eq_getElem (by rw [Array.size_set, Array.size_set]; exact h4H)]
    simp [Array.getElem_set, y]
  · exact moveBand_moves b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak
  · simp [mv3, y, gapXs, side, Nat.add_assoc]
  · simpa [bS] using hpkS
  · rw [moveBand_ix b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak]
    exact hmark3
  · rw [moveBand_tier b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak]
    exact hn3
  · exact moveBand_slides b3 4 searchUp h1H h1D h4H h4D y mv3 slides peak

/-- That seated root is the white opening `chord_fresh_white_down` copies.
    Across and up receive the base point, and `walkStep` on colour 1 is that copy. -/
theorem cofactor_white (b : Board) (t : Spec.Tier) (x ax bx : List Nat)
    (moves slides peak : Nat)
    (h : HitAt b t x ax bx)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hmark : b.sudo_5Board_6marker = -1)
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
        2 * pegCount (rootY t.n t.k t.benchlen x) + pegCount bx +
        pegCount (rootY t.n t.k t.benchlen x)))
    (hfitS : FitsLen (slides + 2 * pegCount (rootY t.n t.k t.benchlen x))) :
    ∃ bS b2,
      cofactorSeat b = .ok bS ∧
      (do
          let b ← marker_lift bS
          let b ← copy_band b across base_across false
          copy_band b up base_up false) = .ok b2 ∧
      (∀ h0 : 0 < b2.sudo_5Board_4home.size, b2.sudo_5Board_4home[0] = embed bx) ∧
      (∀ h1 : 1 < b2.sudo_5Board_4home.size,
        b2.sudo_5Board_4home[1] = embed (rootY t.n t.k t.benchlen x)) ∧
      walkStep t.n t.k t.benchlen (bx, rootY t.n t.k t.benchlen x) false
        (whiteHole0 t.n, whiteHole0 t.n) 1 =
        some (true, (bx, rootY t.n t.k t.benchlen x)) := by
  have hfitSeat : FitsLen (moves +
      pegCount (fieldMul t.n t.k t.benchlen (rootY t.n t.k t.benchlen x)
        (rootY t.n t.k t.benchlen x)) +
      pegCount (curveSide t.n t.k t.benchlen x) + pegCount ax +
      2 * pegCount (rootY t.n t.k t.benchlen x)) :=
    FitsLen.of_le hfit (by omega)
  obtain ⟨bS, mvS, pkS, hseat, hszHS, hszDS, h0, h1, h3t, h3a, h4t, h4a, hmvS, hmvEq,
      hpkS, hmarkS, hnS, _hslS⟩ :=
    cofactor_seat b t x ax bx moves slides peak h hszH hszD hm hsl hpk hmark hn
      hy hside hgapL haxL hf hfit2 hfitSeat hfitS
  have h0e : bS.sudo_5Board_4held[0]'(by rw [hszDS]; decide) = false := by
    rw [Array.getElem?_eq_getElem (by rw [hszDS]; decide)] at h0
    injection h0
  have h1e : bS.sudo_5Board_4held[1]'(by rw [hszDS]; decide) = false := by
    rw [Array.getElem?_eq_getElem (by rw [hszDS]; decide)] at h1
    injection h1
  have h3te : bS.sudo_5Board_4held[3]'(by rw [hszDS]; decide) = true := by
    rw [Array.getElem?_eq_getElem (by rw [hszDS]; decide)] at h3t
    injection h3t
  have h3ae : bS.sudo_5Board_4home[3]'(by rw [hszHS]; decide) = embed bx := by
    rw [Array.getElem?_eq_getElem (by rw [hszHS]; decide)] at h3a
    injection h3a
  have h4te : bS.sudo_5Board_4held[4]'(by rw [hszDS]; decide) = true := by
    rw [Array.getElem?_eq_getElem (by rw [hszDS]; decide)] at h4t
    injection h4t
  have h4ae : bS.sudo_5Board_4home[4]'(by rw [hszHS]; decide) =
      embed (rootY t.n t.k t.benchlen x) := by
    rw [Array.getElem?_eq_getElem (by rw [hszHS]; decide)] at h4a
    injection h4a
  have hmvI : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    simpa [ofNat_eq_natCast] using hmvS
  have hpkI : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (pkS : Int) := by
    simpa [ofNat_eq_natCast] using hpkS
  have hfitx : FitsLen (mvS + pegCount bx) := by
    rw [hmvEq]
    exact FitsLen.of_le hfit (by omega)
  have hfity : FitsLen (mvS + pegCount bx + pegCount (rootY t.n t.k t.benchlen x)) := by
    rw [hmvEq]
    exact FitsLen.of_le hfit (by omega)
  obtain ⟨b2, _, _, hcopy, hx0, hy1, _, _, _, _, _⟩ :=
    chord_fresh_white_down bS bx (rootY t.n t.k t.benchlen x) t.n mvS pkS
      hszHS hszDS hbx hy hf hfitx hfity hnS hmvI hpkI hmarkS h0e h1e h3te h3ae h4te h4ae
  refine ⟨bS, b2, hseat, hcopy, hx0, hy1, ?_⟩
  simpa [hbx, hy] using
    walkStep_fresh_white t.n t.k t.benchlen (bx, rootY t.n t.k t.benchlen x)
      (whiteHole0 t.n, whiteHole0 t.n)

/-- The walk turns the marker flag on, then the first cofactor cell (white,
    accumulator empty) copies the seated root. The loop continues at cell 1. -/
theorem cofactor_chord_open (b : Board) (x y : List Nat) (n moves peak : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n)
    (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hm : b.sudo_5Board_6marker = -1)
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ b2,
      chordStep (embed cofactorCells) (Int.ofNat 3)
          (Int.ofNat 0, (chordFlag b, false)) =
        .ok (SudoRt.Flow.cont (Int.ofNat 1, (b2, true))) ∧
      (∀ h0 : 0 < b2.sudo_5Board_4home.size, b2.sudo_5Board_4home[0] = embed x) ∧
      (∀ h1 : 1 < b2.sudo_5Board_4home.size, b2.sudo_5Board_4home[1] = embed y) := by
  let bF := chordFlag b
  have hmF : bF.sudo_5Board_6marker = -1 := by simp [chordFlag, bF, hm]
  have hlift := marker_lift_down bF hmF
  have hszHF : bF.sudo_5Board_4home.size = 8 := by simp [chordFlag, bF, hszH]
  have hszDF : bF.sudo_5Board_4held.size = 8 := by simp [chordFlag, bF, hszD]
  have hnF : bF.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by simp [chordFlag, bF, hn]
  have hmvF : bF.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa [chordFlag, bF, ofNat_eq_natCast] using hmoves
  have hpkF : bF.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simpa [chordFlag, bF, ofNat_eq_natCast] using hpeak
  have h0F : bF.sudo_5Board_4held[0]'(by rw [hszDF]; decide) = false := by
    simpa [chordFlag, bF] using h0
  have h1F : bF.sudo_5Board_4held[1]'(by rw [hszDF]; decide) = false := by
    simpa [chordFlag, bF] using h1
  have h3tF : bF.sudo_5Board_4held[3]'(by rw [hszDF]; decide) = true := by
    simpa [chordFlag, bF] using h3t
  have h3aF : bF.sudo_5Board_4home[3]'(by rw [hszHF]; decide) = embed x := by
    simpa [chordFlag, bF] using h3a
  have h4tF : bF.sudo_5Board_4held[4]'(by rw [hszDF]; decide) = true := by
    simpa [chordFlag, bF] using h4t
  have h4aF : bF.sudo_5Board_4home[4]'(by rw [hszHF]; decide) = embed y := by
    simpa [chordFlag, bF] using h4a
  obtain ⟨b2, _, _, hcopy, hx0, hy1, _, _, _, _, _⟩ :=
    chord_fresh_white_down bF x y n moves peak hszHF hszDF hx hy hf hfitx hfity
      hnF hmvF hpkF hmF h0F h1F h3tF h3aF h4tF h4aF
  have htail : (do
      let board ← copy_band bF across base_across false
      copy_band board up base_up false) = .ok b2 := by
    rw [hlift, ok_bind] at hcopy
    exact hcopy
  have hbeq : SudoRt.SEq.beq (Int.ofNat 1) (2 : Int) = false := by decide
  have hstep := chordStep_fresh cofactorCells 0 3 1 bF bF b2
      (by decide) (by simp [cofactorCells]) (by simp [cofactorCells])
      (by decide) (by decide) hlift
      (by simpa [hbeq] using htail)
      (fits_small (by decide))
  refine ⟨b2, ?_, hx0, hy1⟩
  rw [hstep]
  simp [if_neg (by decide : ¬ (0 = 3))]

end EcbsLink2.Link2
