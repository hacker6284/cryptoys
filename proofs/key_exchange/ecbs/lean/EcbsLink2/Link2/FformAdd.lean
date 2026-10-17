/-
  The run line of `fform_add` copies the bottom into the spare before the
  schoolbook, so the bottom home stays. The product is `school` of the first
  home by that copy, laid on the strip. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MulOnto

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem nat_beq_false (a b : Nat) (h : a ≠ b) :
    SudoRt.SEq.beq (a : Int) (b : Int) = false := by
  rw [sEq_int, decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj (by
    rw [← ofNat_eq_natCast a, ← ofNat_eq_natCast b] at hEq
    exact hEq))

private theorem aim_held_size (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by
  unfold placeBoard
  dsimp only
  split <;> simp

private theorem aim_home_size (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4home.size =
      b.sudo_5Board_4home.size := by
  unfold placeBoard
  dsimp only
  split <;> simp

private theorem aim_strict (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hH hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
  unfold placeBoard
  dsimp only
  split <;> rfl

/-- Placing into a home and then aiming the bench is aiming and then placing. -/
private theorem place_aim_comm (b : Ecbs.Board) (dst : Int) (strip : Array Int) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves peak : Nat) :
    placeBoard (mulAimed b dst strip) home hH hD xs moves peak =
      mulAimed (placeBoard b home hH hD xs moves peak) dst strip := by
  unfold placeBoard mulAimed
  dsimp only
  split <;> apply board_ext <;> rfl

/-- `mulFromHeld` with `copy_second`, mirror off, on a fresh aimed strip.
    The second home is copied into the spare and the schoolbook reads the copy,
    so the second home stays. The strip is `pad`, and the product laid on it is
    `school` of the first home by the second. -/
theorem held_copy_school (b : Ecbs.Board) (dst first second : Nat)
    (xs ys pad : List Nat) (n moves peak peakS : Nat)
    (hF : first < b.sudo_5Board_4held.size)
    (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (hSpH : 6 < b.sudo_5Board_4held.size)
    (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hne6F : first ≠ 6) (hne6S : second ≠ 6)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hfitP : FitsLen (moves + pegCount ys))
    (hspan : 2 * (n - 1) < pad.length)
    (hxsT : allTritList xs) (hpadT : allTritList pad)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount ys + n * (n + 1))) :
    let bU := placeBoard b 6 hSpHome hSpH ys moves peak
    let mv := moves + pegCount ys
    Ecbs.mulFromHeld ((n : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true false (mulAimed b ((dst : Nat) : Int) (embed pad)) (embed pad) =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep bU ((dst : Nat) : Int) (embed pad) 6 peakS
              (by rw [aim_held_size]; exact hSpH)
              (by rw [aim_home_size]; exact hSpHome))
            (Int.ofNat (mv + schoolMoves xs ys n n)),
          embed (school n xs ys pad false))) := by
  intro bU mv
  unfold Ecbs.mulFromHeld
  simp only [if_true]
  rw [mulAimed_held, ← ofNat_eq_natCast first, atL_ofNat _ first hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  rw [mulAimed_home, atL_ofNat _ first hHome, hArr, ok_bind]
  have hbeq : SudoRt.SEq.beq ((second : Nat) : Int) Ecbs.spare = false := by
    rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl]
    exact nat_beq_false second 6 hne6S
  rw [hbeq]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  let bA := mulAimed b ((dst : Nat) : Int) (embed pad)
  have hH6 : 6 < bA.sudo_5Board_4home.size := by
    simpa [bA, mulAimed] using hSpHome
  have hD6 : 6 < bA.sudo_5Board_4held.size := by
    simpa [bA, mulAimed] using hSpH
  have hS6 : second < bA.sudo_5Board_4held.size := by
    simpa [bA, mulAimed] using hS
  have hHome6 : second < bA.sudo_5Board_4home.size := by
    simpa [bA, mulAimed] using hHomeS
  have hHS6 : bA.sudo_5Board_4held[second]'hS6 = true := by
    simpa [bA, mulAimed] using hHS
  have hYs6 : bA.sudo_5Board_4home[second]'hHome6 = embed ys := by
    simpa [bA, mulAimed] using hYs
  have h7A : 7 ≤ bA.sudo_5Board_4held.size := by
    simpa [bA, mulAimed] using h7
  have hempty : bA.sudo_5Board_4held[6]'hD6 = false := by
    simpa [bA, mulAimed] using hSpE
  have hnA : bA.sudo_5Board_1t.sudo_4Tier_1n = (ys.length : Int) := by
    simp [bA, mulAimed, hn, hleny]
  have hmvA : bA.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa [bA, mulAimed] using hmoves
  have hpkA : bA.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simpa [bA, mulAimed] using hpeak
  have hfitY : FitsLen ys.length := by rw [hleny]; exact hf
  have hcopy := copy_band_refines bA 6 second ys moves peak hH6 hD6 hHome6 hS6 h7A
    hHS6 hYs6 hempty hnA hfitY hmvA hpkA hfitP
  rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl, hcopy, ok_bind]
  have hcomm :=
    place_aim_comm b ((dst : Nat) : Int) (embed pad) 6 hSpHome hSpH ys moves peak
  rw [show placeBoard bA 6 hH6 hD6 ys moves peak =
      mulAimed bU ((dst : Nat) : Int) (embed pad) from by
    simpa [bA, bU] using hcomm]
  have hFU : first < bU.sudo_5Board_4held.size := by
    simpa [bU, aim_held_size] using hF
  have hHomeU : first < bU.sudo_5Board_4home.size := by
    simpa [bU, aim_home_size] using hHome
  have h6U : 6 < bU.sudo_5Board_4held.size := by
    simpa [bU, aim_held_size] using hSpH
  have h6HU : 6 < bU.sudo_5Board_4home.size := by
    simpa [bU, aim_home_size] using hSpHome
  have hHFU : bU.sudo_5Board_4held[first]'hFU = true := by
    have hother := place_held_other b 6 first ⟨hSpHome, hSpH⟩ ys moves peak
      hne6F.symm hF (by rw [aim_held_size]; exact hF)
    simpa [bU] using hother.trans hHF
  have hArrU : bU.sudo_5Board_4home[first]'hHomeU = embed xs := by
    have hother := place_home_other b 6 first ⟨hSpHome, hSpH⟩ ys moves peak
      hne6F.symm hHome (by rw [aim_home_size]; exact hHome)
    simpa [bU] using hother.trans hArr
  have hHSU : bU.sudo_5Board_4held[6]'h6U = true := by
    simpa [bU] using place_held_here b 6 ⟨hSpHome, hSpH⟩ ys moves peak
      (by rw [aim_held_size]; exact hSpH)
  have hYsU : bU.sudo_5Board_4home[6]'h6HU = embed ys := by
    simpa [bU] using place_home_here b 6 ⟨hSpHome, hSpH⟩ ys moves peak
      (by rw [aim_home_size]; exact hSpHome)
  have h7U : 7 ≤ bU.sudo_5Board_4held.size := by
    simpa [bU, aim_held_size] using h7
  have hmvU : bU.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) := by
    simpa [bU, mv, ofNat_eq_natCast] using
      place_moves b 6 ⟨hSpHome, hSpH⟩ ys moves peak
  have hpkS : bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simpa [bU] using (aim_strict b 6 hSpHome hSpH ys moves peak).trans hpeakS
  have hback :
      Ecbs.mulFromSrc ((n : Nat) : Int) (Int.ofNat first) ((6 : Nat) : Int)
          (embed xs) false (mulAimed bU ((dst : Nat) : Int) (embed pad)) (embed pad) =
        Ecbs.mulFromHeld ((n : Nat) : Int) (Int.ofNat first) ((6 : Nat) : Int)
          false false (mulAimed bU ((dst : Nat) : Int) (embed pad)) (embed pad) := by
    unfold Ecbs.mulFromHeld
    simp only [Bool.false_eq_true, if_false]
    rw [mulAimed_held, atL_ofNat _ first hFU, hHFU]
    simp only [sudoAssert_true, ok_bind]
    rw [mulAimed_home, atL_ofNat _ first hHomeU, hArrU, ok_bind]
  rw [hback]
  exact mul_onto_school bU dst first 6 xs ys pad n mv peakS
    hFU hHomeU hHFU hArrU h6U h6HU hHSU hYsU h7U hne6F hn0 hlenx hleny hf
    hmvU hpkS hspan hxsT hpadT hfi hfm

private theorem aim3 (b : Ecbs.Board) (dst : Int) (strip : Array Int) :
    ({ { { b with sudo_5Board_8bench_on := true } with
        sudo_5Board_8bench_to := dst } with
      sudo_5Board_5bench := strip } : Ecbs.Board) =
      mulAimed b dst strip := by
  unfold mulAimed
  rfl

private theorem pegCount_nnz (xs : List Nat) :
    Spec.nnz (embed xs).toList = pegCount xs := by
  rw [toList_embed, nnz_embed]
  rfl

private theorem bind_ok_id {α : Type} (m : Except SudoRt.Trap α) :
    (do let r ← m; Except.ok r) = m := by
  cases m <;> rfl

/-- Marker off, bench off. The onto multiply copies the second home into the
    spare and lays the product on the destination's own number. The destination
    ends empty. The second home stays. -/
theorem run_onto_copy (b : Ecbs.Board) (dst first second : Nat)
    (home xs ys : List Nat) (n moves slides peak peakS bench : Nat)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hD : dst < b.sudo_5Board_4held.size)
    (hHD : dst < b.sudo_5Board_4home.size)
    (hHeldD : b.sudo_5Board_4held[dst] = true)
    (hHomeD : b.sudo_5Board_4home[dst] = embed home)
    (hF : first < b.sudo_5Board_4held.size)
    (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (hSpH : 6 < b.sudo_5Board_4held.size)
    (hSpHome : 6 < b.sudo_5Board_4home.size)
    (hSpE : b.sudo_5Board_4held[6] = false)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hneD1 : dst ≠ first) (hneD2 : dst ≠ second)
    (hne6D : dst ≠ 6) (hne6F : first ≠ 6) (hne6S : second ≠ 6)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenH : home.length = n) (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hhomeT : allTritList home) (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfitM : FitsLen (moves + 3 * n))
    (hfitS : FitsLen (slides + 2 * n))
    (hfm : FitsLen (moves + 3 * n + n * (n + 1))) :
    let peg := pegCount home
    let py := pegCount ys
    let bC := ontoCharge b dst hD hHD moves slides peg
    let pad := pref home bench n
    let mv := moves + 2 * peg + py
    Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) true true false b =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep (placeBoard bC 6
                (by dsimp [bC]; rw [ontoCharge_home_size]; exact hSpHome)
                (by dsimp [bC]; rw [ontoCharge_held_size]; exact hSpH)
                ys (moves + 2 * peg) peak)
              ((dst : Nat) : Int) (embed pad) 6 peakS
              (by dsimp [bC]; rw [aim_held_size, ontoCharge_held_size]; exact hSpH)
              (by dsimp [bC]; rw [aim_home_size, ontoCharge_home_size]; exact hSpHome))
            (Int.ofNat (mv + schoolMoves xs ys n n)),
          embed (school n xs ys pad false))) := by
  intro peg py bC pad mv
  have hpegLe : peg ≤ n := by simpa [peg, hlenH] using pegCount_le home
  have hpyLe : py ≤ n := by simpa [py, hleny] using pegCount_le ys
  have h2 : FitsLen (2 * peg) := FitsLen.of_le hfitM (by omega)
  have hfitMc : FitsLen (moves + 2 * peg) := FitsLen.of_le hfitM (by omega)
  have hfitSc : FitsLen (slides + 2 * peg) := FitsLen.of_le hfitS (by omega)
  have hfitCopy : FitsLen (moves + 2 * peg + py) := FitsLen.of_le hfitM (by omega)
  have hfmC : FitsLen (moves + 2 * peg + py + n * (n + 1)) :=
    FitsLen.of_le hfm (by omega)
  unfold Ecbs.mulElse
  simp only [if_true]
  rw [settle_off b hoff]
  simp only [ok_bind, pure_eq_ok]
  rw [hbl, filledL_ofNat, ok_bind, ← embed_replicate_zero]
  rw [← ofNat_eq_natCast dst, atL_ofNat _ dst hD, hHeldD]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ dst hHD, hHomeD, ok_bind]
  rw [putL_ofNat _ dst false hD, ok_bind]
  rw [putL_ofNat _ dst (#[] : Array Int) hHD, ok_bind]
  have hfs : FitsLen (embed home).size := by rw [size_embed, hlenH]; exact hf
  rw [npeg_refines (embed home) hfs, pegCount_nnz home, ok_bind]
  rw [show (2 : Int) = Int.ofNat 2 from rfl, mulI_ofNat 2 peg h2, ok_bind]
  rw [hmoves, ← ofNat_eq_natCast moves, addI_ofNat moves (2 * peg) hfitMc, ok_bind]
  rw [hslides, ← ofNat_eq_natCast slides, addI_ofNat slides (2 * peg) hfitSc, ok_bind]
  rw [show ((n : Nat) : Int) = Int.ofNat n from (ofNat_eq_natCast n).symm]
  rw [subI_ofNat_one n hn0 hf, ok_bind]
  have hfuel :
      (if (0 : Int) > Int.ofNat (n - 1) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelRange (0 : Int) (Int.ofNat (n - 1)) := rfl
  rw [hfuel]
  have hpadLen : pad.length = bench := pref_length hnb (by omega)
  have hspanP : 2 * (n - 1) < pad.length := by rw [hpadLen]; exact hspan
  have hpadT : allTritList pad := pref_trits home bench n hhomeT hnb (by omega)
  have h6HC : 6 < bC.sudo_5Board_4home.size := by
    simpa [bC, ontoCharge_home_size] using hSpHome
  have h6DC : 6 < bC.sudo_5Board_4held.size := by
    simpa [bC, ontoCharge_held_size] using hSpH
  have hpost :
      ontoAfter ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
          ((second : Nat) : Int) true false bC
          (Int.ofNat (n - 1), embed pad) =
        mulAfter (Int.ofNat 0,
          (withMoves
              (mulPrep (placeBoard bC 6 h6HC h6DC ys (moves + 2 * peg) peak)
                ((dst : Nat) : Int) (embed pad) 6 peakS
                (by rw [aim_held_size]; exact h6DC)
                (by rw [aim_home_size]; exact h6HC))
              (Int.ofNat (mv + schoolMoves xs ys n n)),
            embed (school n xs ys pad false))) := by
    unfold ontoAfter
    rw [aim3]
    have hmovesC : bC.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((moves + 2 * peg : Nat) : Int) := by
      simpa [bC, ofNat_eq_natCast] using
        ontoCharge_moves b dst hD hHD moves slides peg
    have hpeakC : bC.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
      simpa [bC, ontoCharge] using hpeak
    have hstrictC : bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
      simpa [bC] using (ontoCharge_strict b dst hD hHD moves slides peg).trans hpeakS
    have h7C : 7 ≤ bC.sudo_5Board_4held.size := by
      simpa [bC, ontoCharge_held_size] using h7
    have hnC : bC.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
      have ht := congrArg (fun t => t.sudo_4Tier_1n)
        (ontoCharge_tier b dst hD hHD moves slides peg)
      simpa [bC] using ht.trans hn
    have hFC : first < bC.sudo_5Board_4held.size := by
      simpa [bC, ontoCharge_held_size] using hF
    have hHomeC : first < bC.sudo_5Board_4home.size := by
      simpa [bC, ontoCharge_home_size] using hHome
    have hSC : second < bC.sudo_5Board_4held.size := by
      simpa [bC, ontoCharge_held_size] using hS
    have hHomeSC : second < bC.sudo_5Board_4home.size := by
      simpa [bC, ontoCharge_home_size] using hHomeS
    have hHFC : bC.sudo_5Board_4held[first] = true := by
      have hget := ontoCharge_held_get b dst first hD hHD moves slides peg hneD1 hF
      simpa [bC] using hget.trans hHF
    have hArrC : bC.sudo_5Board_4home[first] = embed xs := by
      have hget := ontoCharge_home_get b dst first hD hHD moves slides peg hneD1 hHome
      simpa [bC] using hget.trans hArr
    have hHSC : bC.sudo_5Board_4held[second] = true := by
      have hget := ontoCharge_held_get b dst second hD hHD moves slides peg hneD2 hS
      simpa [bC] using hget.trans hHS
    have hYsC : bC.sudo_5Board_4home[second] = embed ys := by
      have hget := ontoCharge_home_get b dst second hD hHD moves slides peg hneD2 hHomeS
      simpa [bC] using hget.trans hYs
    have hSpEC : bC.sudo_5Board_4held[6] = false := by
      have hget := ontoCharge_held_get b dst 6 hD hHD moves slides peg hne6D hSpH
      simpa [bC] using hget.trans hSpE
    exact held_copy_school bC dst first second xs ys pad n (moves + 2 * peg) peak peakS
      hFC hHomeC hHFC hArrC hSC hHomeSC hHSC hYsC h6DC h6HC hSpEC h7C
      hne6F hne6S hn0 hnC hlenx hleny hf hmovesC hpeakC hstrictC hfitCopy
      hspanP hxsT hpadT hfi hfmC
  conv =>
    pattern (fun σ : Int × Array Int => _)
    change ontoAfter ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
      ((second : Nat) : Int) true false bC
  have hcopy := band_copy_after home bench n
      (ontoAfter ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) true false bC)
      (fun r => Except.ok r)
      (mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep (placeBoard bC 6 h6HC h6DC ys (moves + 2 * peg) peak)
              ((dst : Nat) : Int) (embed pad) 6 peakS
              (by rw [aim_held_size]; exact h6DC)
              (by rw [aim_home_size]; exact h6HC))
            (Int.ofNat (mv + schoolMoves xs ys n n)),
          embed (school n xs ys pad false))))
      hn0 hnb (by rw [hlenH]; exact Nat.le_refl n) hf hpost
  rw [hcopy, bind_ok_id, ofNat_eq_natCast dst]

end EcbsLink2.Link2
