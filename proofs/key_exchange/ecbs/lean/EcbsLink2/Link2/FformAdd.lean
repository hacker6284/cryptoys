/-
  The run line of `fform_add` copies the bottom into the spare before the
  schoolbook, so the bottom home stays. The product is `school` of the first
  home by that copy, laid on the strip. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MulOnto
import EcbsLink2.Link2.MarkerBench
import EcbsLink2.Link2.Mirror

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

/-- `mulFromHeld` with `copy_second` on a fresh aimed strip. The mirror flag is
    `mirror`. The second home is copied into the spare and the schoolbook reads
    the copy, so the second home stays. The strip is `pad`, and the product laid
    on it is `school` of the first home by the second. -/
theorem held_copy_school (b : Ecbs.Board) (dst first second : Nat)
    (xs ys pad : List Nat) (n moves peak peakS : Nat) (mirror : Bool)
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
        true mirror (mulAimed b ((dst : Nat) : Int) (embed pad)) (embed pad) =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep bU ((dst : Nat) : Int) (embed pad) 6 peakS
              (by rw [aim_held_size]; exact hSpH)
              (by rw [aim_home_size]; exact hSpHome))
            (Int.ofNat (mv + schoolMoves xs ys n n)),
          embed (school n xs ys pad mirror))) := by
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
          (embed xs) mirror (mulAimed bU ((dst : Nat) : Int) (embed pad)) (embed pad) =
        Ecbs.mulFromHeld ((n : Nat) : Int) (Int.ofNat first) ((6 : Nat) : Int)
          false mirror (mulAimed bU ((dst : Nat) : Int) (embed pad)) (embed pad) := by
    unfold Ecbs.mulFromHeld
    simp only [Bool.false_eq_true, if_false]
    rw [mulAimed_held, atL_ofNat _ first hFU, hHFU]
    simp only [sudoAssert_true, ok_bind]
    rw [mulAimed_home, atL_ofNat _ first hHomeU, hArrU, ok_bind]
  rw [hback]
  exact mul_onto_school bU dst first 6 xs ys pad n mv peakS mirror
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
    (mirror : Bool)
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
        ((second : Nat) : Int) true true mirror b =
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
          embed (school n xs ys pad mirror))) := by
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
          ((second : Nat) : Int) true mirror bC
          (Int.ofNat (n - 1), embed pad) =
        mulAfter (Int.ofNat 0,
          (withMoves
              (mulPrep (placeBoard bC 6 h6HC h6DC ys (moves + 2 * peg) peak)
                ((dst : Nat) : Int) (embed pad) 6 peakS
                (by rw [aim_held_size]; exact h6DC)
                (by rw [aim_home_size]; exact h6HC))
              (Int.ofNat (mv + schoolMoves xs ys n n)),
            embed (school n xs ys pad mirror))) := by
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
    exact held_copy_school bC dst first second xs ys pad n (moves + 2 * peg) peak peakS mirror
      hFC hHomeC hHFC hArrC hSC hHomeSC hHSC hYsC h6DC h6HC hSpEC h7C
      hne6F hne6S hn0 hnC hlenx hleny hf hmovesC hpeakC hstrictC hfitCopy
      hspanP hxsT hpadT hfi hfmC
  conv =>
    pattern (fun σ : Int × Array Int => _)
    change ontoAfter ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
      ((second : Nat) : Int) true mirror bC
  have hcopy := band_copy_after home bench n
      (ontoAfter ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) true mirror bC)
      (fun r => Except.ok r)
      (mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep (placeBoard bC 6 h6HC h6DC ys (moves + 2 * peg) peak)
              ((dst : Nat) : Int) (embed pad) 6 peakS
              (by rw [aim_held_size]; exact h6DC)
              (by rw [aim_home_size]; exact h6HC))
            (Int.ofNat (mv + schoolMoves xs ys n n)),
          embed (school n xs ys pad mirror))))
      hn0 hnb (by rw [hlenH]; exact Nat.le_refl n) hf hpost
  rw [hcopy, bind_ok_id, ofNat_eq_natCast dst]

private theorem get_eq_of_array {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  cases h
  rfl

private theorem bump_with (b : Ecbs.Board) (cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    ({ b with sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_3ops :=
          b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) } } :
      Ecbs.Board) =
      bumpOp b 0 cOps hops := by
  simp [bumpOp]

/-- Marker off, bench off. The op bump, then `run_onto_copy`. -/
theorem run_onto_off (b : Ecbs.Board) (dst first second : Nat)
    (home xs ys : List Nat) (n moves slides peak peakS bench cOps : Nat)
    (mirror : Bool)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
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
    let b0 := bumpOp b 0 cOps hops
    let peg := pegCount home
    let py := pegCount ys
    let bC := ontoCharge b0 dst
      (by rw [bumpOp_held]; exact hD) (by rw [bumpOp_home]; exact hHD)
      moves slides peg
    let pad := pref home bench n
    let mv := moves + 2 * peg + py
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true true mirror =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep (placeBoard bC 6
                (by dsimp [bC]; rw [ontoCharge_home_size, bumpOp_home]; exact hSpHome)
                (by dsimp [bC]; rw [ontoCharge_held_size, bumpOp_held]; exact hSpH)
                ys (moves + 2 * peg) peak)
              ((dst : Nat) : Int) (embed pad) 6 peakS
              (by dsimp [bC]; rw [aim_held_size, ontoCharge_held_size, bumpOp_held]; exact hSpH)
              (by dsimp [bC]; rw [aim_home_size, ontoCharge_home_size, bumpOp_home]; exact hSpHome))
            (Int.ofNat (mv + schoolMoves xs ys n n)),
          embed (school n xs ys pad mirror))) := by
  intro b0 peg py bC pad mv
  rw [mul_keep_eq]
  unfold Ecbs.mulKeep
  rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
    ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
    putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  dsimp only
  have hbump :
      ({ b with sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_3ops :=
            b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) } } :
        Ecbs.Board) = b0 := by
    simp [b0, bumpOp]
  rw [hbump]
  rw [log_op_off b0 (by simp [b0, bumpOp, hmk])]
  simp only [ok_bind]
  have hnB : b0.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by simp [b0, bumpOp, hn]
  rw [hnB]
  have hoffB : b0.sudo_5Board_8bench_on = false := by simp [b0, bumpOp, hoff]
  simp only [hoffB, Bool.false_eq_true, if_false, if_true, pure_eq_ok, ok_bind]
  have hblB : b0.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [b0, bumpOp, hbl]
  have hDB : dst < b0.sudo_5Board_4held.size := by simp [b0, bumpOp_held]; exact hD
  have hHDB : dst < b0.sudo_5Board_4home.size := by simp [b0, bumpOp_home]; exact hHD
  have hHeldDB : b0.sudo_5Board_4held[dst] = true := by simp [b0, bumpOp_held, hHeldD]
  have hHomeDB : b0.sudo_5Board_4home[dst] = embed home := by simp [b0, bumpOp_home, hHomeD]
  have hFB : first < b0.sudo_5Board_4held.size := by simp [b0, bumpOp_held]; exact hF
  have hHomeB : first < b0.sudo_5Board_4home.size := by simp [b0, bumpOp_home]; exact hHome
  have hHFB : b0.sudo_5Board_4held[first] = true := by simp [b0, bumpOp_held, hHF]
  have hArrB : b0.sudo_5Board_4home[first] = embed xs := by simp [b0, bumpOp_home, hArr]
  have hSB : second < b0.sudo_5Board_4held.size := by simp [b0, bumpOp_held]; exact hS
  have hHomeSB : second < b0.sudo_5Board_4home.size := by simp [b0, bumpOp_home]; exact hHomeS
  have hHSB : b0.sudo_5Board_4held[second] = true := by simp [b0, bumpOp_held, hHS]
  have hYsB : b0.sudo_5Board_4home[second] = embed ys := by simp [b0, bumpOp_home, hYs]
  have hSpHB : 6 < b0.sudo_5Board_4held.size := by simp [b0, bumpOp_held]; exact hSpH
  have hSpHomeB : 6 < b0.sudo_5Board_4home.size := by simp [b0, bumpOp_home]; exact hSpHome
  have hSpEB : b0.sudo_5Board_4held[6] = false := by simp [b0, bumpOp_held, hSpE]
  have h7B : 7 ≤ b0.sudo_5Board_4held.size := by simp [b0, bumpOp_held]; exact h7
  have hmovesB : b0.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simp [b0, bumpOp_moves, hmoves]
  have hslidesB : b0.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int) := by
    simp [b0, bumpOp, hslides]
  have hpeakB : b0.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [b0, bumpOp, hpeak]
  have hstrictB : b0.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simp [b0, bumpOp, hpeakS]
  exact run_onto_copy b0 dst first second home xs ys n moves slides peak peakS bench mirror
    hoffB hblB hDB hHDB hHeldDB hHomeDB hFB hHomeB hHFB hArrB hSB hHomeSB hHSB hYsB
    hSpHB hSpHomeB hSpEB h7B hneD1 hneD2 hne6D hne6F hne6S hn0 hnb hnB hlenH hlenx hleny hf
    hmovesB hslidesB hpeakB hstrictB hspan hhomeT hxsT hfi hfitM hfitS hfm

/-- The bench is on and aimed at `seat`, which is not the multiply's destination.
    The onto-keep test fails, so `Ecbs.mul` settles that bench and then multiplies.
    Settling first leaves the same multiply: the second prologue sees the bench off. -/
theorem run_onto_settles (b : Ecbs.Board) (dst first second seat : Nat)
    (lane : List Nat) (n moves slides peak cOps : Nat)
    (mirror : Bool)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hseat : seat ≠ dst)
    (hH : seat < b.sudo_5Board_4home.size)
    (hD : seat < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[seat] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true true mirror =
      (Ecbs.settle b >>= fun b' =>
        Ecbs.mul b' ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
          true true mirror) := by
  have hset := settle_refines b seat lane n moves slides peak hH hD h7 hon hto hempty
    hbench hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
  rw [hset, ok_bind]
  let bS := settleBoard b seat hH hD lane n moves slides peak
  have hmkS : bS.sudo_5Board_9marker_on = false := by
    by_cases hpk : peak < countHeld (b.sudo_5Board_4held.set ⟨seat, hD⟩ true) 7
    · rw [show bS = settleBoard b seat hH hD lane n moves slides peak from rfl,
        settle_peak b seat ⟨hH, hD⟩ lane n moves slides peak hpk, hmk]
    · rw [show bS = settleBoard b seat hH hD lane n moves slides peak from rfl,
        settle_keep b seat ⟨hH, hD⟩ lane n moves slides peak hpk, hmk]
  have hoffS : bS.sudo_5Board_8bench_on = false :=
    settle_bench_off b seat ⟨hH, hD⟩ lane n moves slides peak
  have hopsS : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size :=
    settle_ops_lt b 0 seat hops ⟨hH, hD⟩ lane n moves slides peak
  have hop0S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsS = (cOps : Int) := by
    have hget := get_eq_of_array (settle_ops b seat ⟨hH, hD⟩ lane n moves slides peak) 0 hopsS
    exact hget.trans hop0
  rw [mul_keep_eq, mul_keep_eq]
  unfold Ecbs.mulKeep
  rw [show Ecbs.op_mul = Int.ofNat 0 from rfl]
  conv =>
    lhs
    rw [atL_ofNat _ 0 hops, hop0, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
    dsimp only
    rw [bump_with b cOps hops]
  conv =>
    rhs
    rw [atL_ofNat _ 0 hopsS, hop0S, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hopsS, ok_bind]
    dsimp only
    rw [bump_with bS cOps hopsS]
  rw [log_op_off (bumpOp b 0 cOps hops) (by simp [bumpOp, hmk])]
  rw [log_op_off (bumpOp bS 0 cOps hopsS) (by simp [bumpOp, hmkS])]
  simp only [ok_bind]
  have hnL : (bumpOp b 0 cOps hops).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp [bumpOp, hn]
  have hnR : (bumpOp bS 0 cOps hopsS).sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    have ht := settle_tier_eq b seat ⟨hH, hD⟩ lane n moves slides peak
    simp [bumpOp, bS, ht, hn]
  rw [hnL, hnR]
  have honL : (bumpOp b 0 cOps hops).sudo_5Board_8bench_on = true := by simp [bumpOp, hon]
  have htoL : (bumpOp b 0 cOps hops).sudo_5Board_8bench_to = (seat : Int) := by
    simp [bumpOp, hto]
  have hoffR : (bumpOp bS 0 cOps hopsS).sudo_5Board_8bench_on = false := by
    simp [bumpOp, hoffS]
  have hbeq : SudoRt.SEq.beq (seat : Int) ((dst : Nat) : Int) = false :=
    nat_beq_false seat dst hseat
  simp only [honL, htoL, hbeq, hoffR, Bool.false_eq_true, if_false, if_true,
    pure_eq_ok, ok_bind]
  unfold Ecbs.mulElse
  have hsetL := settle_refines (bumpOp b 0 cOps hops) seat lane n moves slides peak
      (bump_home_lt b 0 cOps seat hops hH) (bump_held_lt b 0 cOps seat hops hD) h7
      honL htoL (by simpa [bumpOp] using hempty)
      (by simp [bumpOp, hbench]) hnL hpos hnle hzero hf hfitL
      (by simp [bumpOp, hmoves]) (by simp [bumpOp, hslides]) (by simp [bumpOp, hpeak])
      hpeg hfitM hfitS
  rw [hsetL, ok_bind]
  rw [settle_bump_comm b 0 cOps hops seat ⟨hH, hD⟩ lane n moves slides peak]
  rw [settle_off (bumpOp bS 0 cOps hopsS) hoffR, ok_bind]

/-- Settling the bench first is the multiply `run_onto_settles` leaves. -/
theorem run_onto_at (b : Ecbs.Board) (dst first second seat : Nat)
    (lane : List Nat) (n moves slides peak cOps : Nat)
    (mirror : Bool)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hseat : seat ≠ dst)
    (hH : seat < b.sudo_5Board_4home.size)
    (hD : seat < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[seat] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) :
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true true mirror =
      Ecbs.mul (settleBoard b seat hH hD lane n moves slides peak)
        ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true true mirror := by
  rw [run_onto_settles b dst first second seat lane n moves slides peak cOps mirror
      hmk hon hto hseat hH hD h7 hempty hbench hn hpos hnle hzero hf hfitL
      hmoves hslides hpeak hpeg hfitM hfitS hops hop0 hfops]
  rw [settle_refines b seat lane n moves slides peak hH hD h7 hon hto hempty
      hbench hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS,
      ok_bind]

/-- After `frobenius_point` the marker is on and the bench is aimed at `seat`.
    The run multiply's `log_op` is `marker_step`. The onto-keep test fails, so
    the multiply continues as `mulElse` on the flagged board that step leaves.
    The mirror flag is `mirror`: `false` on the run, `true` when the rise is red. -/
theorem run_marker_seat (b : Ecbs.Board) (dst first second seat : Nat)
    (m ctrl mx script cOps n : Nat) (mirror : Bool)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hseat : seat ≠ dst)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) :
    let feed := markerUpFeed b m ctrl mx
    let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simpa [markerUpFeed] using hops
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true true mirror =
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) true true mirror
        (markerOn (bumpOp feed 0 cOps hopsF)) := by
  intro feed hopsF
  rw [mul_keep_eq]
  unfold Ecbs.mulKeep
  rw [show Ecbs.op_mul = Int.ofNat 0 from rfl]
  conv =>
    lhs
    rw [atL_ofNat _ 0 hops, hop0, ok_bind,
      ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
      putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
    dsimp only
    rw [bump_with b cOps hops]
  rw [log_op_on (bumpOp b 0 cOps hops) (by simp [bumpOp, hmk])]
  have hmB : (bumpOp b 0 cOps hops).sudo_5Board_6marker = Int.ofNat m := by
    simp [bumpOp, hm]
  have hcB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simp [bumpOp, hc]
  have hxB : (bumpOp b 0 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx := by simp [bumpOp, hx]
  have hsB : (bumpOp b 0 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simp [bumpOp, hscript]
  rw [marker_step_up (bumpOp b 0 cOps hops) m ctrl mx script hmB hcB hxB hsB
      hbound hfitMk hfitC hfit2]
  rw [← mul_up_bump b m ctrl mx cOps hops hmk]
  simp only [ok_bind]
  have hU : { bumpOp feed 0 cOps hopsF with sudo_5Board_9marker_on := true } =
      markerOn (bumpOp feed 0 cOps hopsF) := by
    simp [markerOn, feed]
  rw [hU]
  have hnL : (bumpOp (markerUpFeed b m ctrl mx) 0 cOps hopsF).sudo_5Board_1t.sudo_4Tier_1n =
      (n : Int) := by
    simp [bumpOp, markerUpFeed, hn]
  rw [hnL]
  have honL : (bumpOp (markerUpFeed b m ctrl mx) 0 cOps hopsF).sudo_5Board_8bench_on = true := by
    simp [bumpOp, markerUpFeed, hon]
  have htoL : (bumpOp (markerUpFeed b m ctrl mx) 0 cOps hopsF).sudo_5Board_8bench_to = (seat : Int) := by
    simp [bumpOp, markerUpFeed, hto]
  have hbeq : SudoRt.SEq.beq (seat : Int) ((dst : Nat) : Int) = false :=
    nat_beq_false seat dst hseat
  simp only [honL, htoL, hbeq, Bool.false_eq_true, if_false, if_true, pure_eq_ok, ok_bind]

/-- `mulElse` settles a bench aimed at `seat`. The marker flag is not read, so
    it stays on, and the multiply that follows is `mulElse` of that flagged settle. -/
theorem run_else_flag (b : Ecbs.Board) (dst first second seat : Nat)
    (lane : List Nat) (n moves slides peak : Nat) (mirror : Bool)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hH : seat < b.sudo_5Board_4home.size)
    (hD : seat < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[seat] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n))) :
    Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) true true mirror (markerOn b) =
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) true true mirror
        (markerOn (settleBoard b seat hH hD lane n moves slides peak)) := by
  have hsettle :
      Ecbs.settle (markerOn b) =
        .ok (markerOn (settleBoard b seat hH hD lane n moves slides peak)) := by
    rw [markerOn_def]
    rw [settle_flag b seat lane n moves slides peak hmk hH hD h7 hon hto hempty
        hbench hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS]
    rw [settle_refines b seat lane n moves slides peak hH hD h7 hon hto hempty
        hbench hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS]
    simp only [ok_bind, pure_eq_ok, ← markerOn_def]
  have hoffS :
      (markerOn (settleBoard b seat hH hD lane n moves slides peak)).sudo_5Board_8bench_on =
        false := by
    rw [markerOn_on]
    exact settle_bench_off b seat ⟨hH, hD⟩ lane n moves slides peak
  unfold Ecbs.mulElse
  conv =>
    lhs
    rw [hsettle, ok_bind]
  conv =>
    rhs
    rw [settle_off (markerOn (settleBoard b seat hH hD lane n moves slides peak)) hoffS, ok_bind]

/-- The marker step, then the settle inside `mulElse`. The flag stays on.
    `mirror` is `false` for the run and the constant `true` or `false` for the rise. -/
theorem run_marker_else (b : Ecbs.Board) (dst first second seat : Nat)
    (lane : List Nat) (m ctrl mx script cOps n moves slides peak : Nat)
    (mirror : Bool)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hseat : seat ≠ dst)
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
    (hH : seat < b.sudo_5Board_4home.size)
    (hD : seat < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[seat] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n))) :
    let feed := markerUpFeed b m ctrl mx
    let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simpa [markerUpFeed] using hops
    let bU := bumpOp feed 0 cOps hopsF
    let hHU : seat < bU.sudo_5Board_4home.size := by
      simpa [bU, bumpOp, feed, markerUpFeed] using hH
    let hDU : seat < bU.sudo_5Board_4held.size := by
      simpa [bU, bumpOp, feed, markerUpFeed] using hD
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        true true mirror =
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) true true mirror
        (markerOn (settleBoard bU seat hHU hDU lane n moves slides peak)) := by
  intro feed hopsF bU hHU hDU
  rw [run_marker_seat b dst first second seat m ctrl mx script cOps n mirror
      hmk hon hto hseat hm hc hx hscript hbound hfitMk hfitC hfit2 hn hops hop0 hfops]
  have hmkU : bU.sudo_5Board_9marker_on = false := by
    simp [bU, bumpOp, feed, markerUpFeed]
  have honU : bU.sudo_5Board_8bench_on = true := by
    simp [bU, bumpOp, feed, markerUpFeed, hon]
  have htoU : bU.sudo_5Board_8bench_to = (seat : Int) := by
    simp [bU, bumpOp, feed, markerUpFeed, hto]
  have h7U : 7 ≤ bU.sudo_5Board_4held.size := by
    simpa [bU, bumpOp, feed, markerUpFeed] using h7
  have hemptyU : bU.sudo_5Board_4held[seat] = false := by
    simpa [bU, bumpOp, feed, markerUpFeed] using hempty
  have hbenchU : bU.sudo_5Board_5bench = embed lane := by
    simp [bU, bumpOp, feed, markerUpFeed, hbench]
  have hnU : bU.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp [bU, bumpOp, feed, markerUpFeed, hn]
  have hmovesU : bU.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    simp [bU, bumpOp, feed, markerUpFeed, hmoves]
  have hslidesU : bU.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simp [bU, bumpOp, feed, markerUpFeed, hslides]
  have hpeakU : bU.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simp [bU, bumpOp, feed, markerUpFeed, hpeak]
  exact run_else_flag bU dst first second seat lane n moves slides peak mirror
    hmkU honU htoU hHU hDU h7U hemptyU hbenchU hnU hpos hnle hzero hf hfitL
    hmovesU hslidesU hpeakU hpeg hfitM hfitS

/-- The rise mirrors `home`, then the onto multiply steps the marker. The mirror
    flag of that multiply is the constant `mirror` (`false` on white, `true` on red).
    `mirror` does not move the bench, the marker, or the op counter. -/
theorem rise_marker (b : Ecbs.Board) (home dst first second seat : Nat)
    (L : List Nat) (m ctrl mx script cOps n moves : Nat) (mirror : Bool)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (harr : b.sudo_5Board_4home[home] = embed L)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : L.length = n) (hpos : 0 < n) (htri : allTritList L)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n))
    (hmk : b.sudo_5Board_9marker_on = true)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (seat : Int))
    (hseat : seat ≠ dst)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) :
    let bM := mirrorHome b home hH (embed (mirrorTrits L)) (moves + pegCount L)
    let feed := markerUpFeed bM m ctrl mx
    let hopsM : 0 < bM.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simpa [bM, mirrorHome, withMoves] using hops
    let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simpa [markerUpFeed] using hopsM
    (Ecbs.mirror b ((home : Nat) : Int) >>= fun b1 =>
        Ecbs.mul b1 ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
          true true mirror) =
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) true true mirror
        (markerOn (bumpOp feed 0 cOps hopsF)) := by
  intro bM feed hopsM hopsF
  rw [mirror_refines b home L n moves hH hD hheld harr hn hlen hpos htri hmv hfit]
  simp only [ok_bind]
  have hmkM : bM.sudo_5Board_9marker_on = true := by
    simp [bM, mirrorHome, withMoves, hmk]
  have honM : bM.sudo_5Board_8bench_on = true := by
    simp [bM, mirrorHome, withMoves, hon]
  have htoM : bM.sudo_5Board_8bench_to = (seat : Int) := by
    simp [bM, mirrorHome, withMoves, hto]
  have hmM : bM.sudo_5Board_6marker = Int.ofNat m := by
    simp [bM, mirrorHome, withMoves, hm]
  have hcM : bM.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simp [bM, mirrorHome, withMoves, hc]
  have hxM : bM.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := by
    simp [bM, mirrorHome, withMoves, hx]
  have hsM : bM.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simp [bM, mirrorHome, withMoves, hscript]
  have hnM : bM.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp [bM, mirrorHome, withMoves, hn]
  have hop0M : bM.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsM = (cOps : Int) := by
    simpa [bM, mirrorHome, withMoves] using hop0
  exact run_marker_seat bM dst first second seat m ctrl mx script cOps n mirror
    hmkM honM htoM hseat hmM hcM hxM hsM hbound hfitMk hfitC hfit2 hnM hopsM hop0M hfops

private theorem replicate_trits (k : Nat) : allTritList (List.replicate k 0) := by
  intro x hx
  have hx' : ¬ k = 0 ∧ x = 0 := by simpa [List.mem_replicate] using hx
  omega

/-- Bench off, `onto = false`, `copy_second = true`. `mulElse` aims a zero strip
    at the destination and `held_copy_school` lays `school` on it. The mirror
    flag is `mirror`. This is a gap multiply once the bench has been settled. -/
theorem copy_else_off (b : Ecbs.Board) (dst first second : Nat)
    (xs ys : List Nat) (n moves peak peakS bench : Nat) (mirror : Bool)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
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
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + pegCount ys + n * (n + 1))) :
    let pad := List.replicate bench 0
    let bU := placeBoard b 6 hSpHome hSpH ys moves peak
    let mv := moves + pegCount ys
    Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) true false mirror b =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep bU ((dst : Nat) : Int) (embed pad) 6 peakS
              (by rw [aim_held_size]; exact hSpH)
              (by rw [aim_home_size]; exact hSpHome))
            (Int.ofNat (mv + schoolMoves xs ys n n)),
          embed (school n xs ys pad mirror))) := by
  intro pad bU mv
  unfold Ecbs.mulElse
  simp only [Bool.false_eq_true, if_false]
  rw [settle_off b hoff]
  simp only [ok_bind, pure_eq_ok]
  rw [hbl, filledL_ofNat, ok_bind, ← embed_replicate_zero]
  rw [aim3]
  have hspanP : 2 * (n - 1) < pad.length := by
    simpa [pad, List.length_replicate] using hspan
  have hpadT : allTritList pad := by simpa [pad] using replicate_trits bench
  exact held_copy_school b dst first second xs ys pad n moves peak peakS mirror
    hF hHome hHF hArr hS hHomeS hHS hYs hSpH hSpHome hSpE h7
    hne6F hne6S hn0 hn hlenx hleny hf hmoves hpeak hpeakS hfitP
    hspanP hxsT hpadT hfi hfm

/-- Bench off, `onto = false`, `copy_second = false`. `mulElse` aims a zero
    strip at the destination and `mul_onto_school` lays `school` on it. The
    mirror flag is `mirror`. The later gap lines and the new point's first
    multiply have this shape. -/
theorem nocopy_else_off (b : Ecbs.Board) (dst first second : Nat)
    (xs ys : List Nat) (n moves peakS bench : Nat) (mirror : Bool)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hF : first < b.sudo_5Board_4held.size)
    (hHome : first < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[first] = true)
    (hArr : b.sudo_5Board_4home[first] = embed xs)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size)
    (hHS : b.sudo_5Board_4held[second] = true)
    (hYs : b.sudo_5Board_4home[second] = embed ys)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hne : first ≠ second) (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1))) :
    let pad := List.replicate bench 0
    Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) false false mirror b =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep b ((dst : Nat) : Int) (embed pad) second peakS hS hHomeS)
            (Int.ofNat (moves + schoolMoves xs ys n n)),
          embed (school n xs ys pad mirror))) := by
  intro pad
  unfold Ecbs.mulElse
  simp only [Bool.false_eq_true, if_false]
  rw [settle_off b hoff]
  simp only [ok_bind, pure_eq_ok]
  rw [hbl, filledL_ofNat, ok_bind, ← embed_replicate_zero]
  rw [aim3]
  have hspanP : 2 * (n - 1) < pad.length := by
    simpa [pad, List.length_replicate] using hspan
  have hpadT : allTritList pad := by simpa [pad] using replicate_trits bench
  exact mul_onto_school b dst first second xs ys pad n moves peakS mirror
    hF hHome hHF hArr hS hHomeS hHS hYs h7 hne hn0 hlenx hleny hf
    hmoves hpeakS hspanP hxsT hpadT hfi hfm

end EcbsLink2.Link2
