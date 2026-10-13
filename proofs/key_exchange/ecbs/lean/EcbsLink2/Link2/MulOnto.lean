/-
  `mul` with `onto = true`, `copy_second = false`, and `mirror = false`.
  The destination home is copied onto a zero strip, the schoolbook lays the
  product onto that copy, and the lane fold is `mulAfter`. The length-`n`
  prefix of that fold is `fieldAdd` of the home and `fieldMul`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.MarkerMul
import EcbsLink2.Link2.BandCopy
import EcbsLink2.Link2.StripFold

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

private theorem bind_pure_id {α : Type} (m : Except SudoRt.Trap α) :
    (do let r ← m; pure r) = m := by
  cases m <;> rfl

private theorem bind_ok_id {α : Type} (m : Except SudoRt.Trap α) :
    (do let r ← m; Except.ok r) = m := by
  cases m <;> rfl

private theorem pegCount_nnz (xs : List Nat) :
    Spec.nnz (embed xs).toList = pegCount xs := by
  rw [toList_embed, nnz_embed]
  rfl

/-- The board after the `onto` arm clears `dst` and charges `2 * peg`
    moves and the same number of slides. -/
def ontoCharge (b : Ecbs.Board) (dst : Nat)
    (hD : dst < b.sudo_5Board_4held.size)
    (hH : dst < b.sudo_5Board_4home.size)
    (moves slides peg : Nat) : Ecbs.Board :=
  { b with
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨dst, hD⟩ false
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨dst, hH⟩ (#[] : Array Int)
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (moves + 2 * peg)
      sudo_5Costs_6slides := Int.ofNat (slides + 2 * peg) } }

theorem ontoCharge_held_size (b : Ecbs.Board) (dst : Nat)
    (hD : dst < b.sudo_5Board_4held.size)
    (hH : dst < b.sudo_5Board_4home.size)
    (moves slides peg : Nat) :
    (ontoCharge b dst hD hH moves slides peg).sudo_5Board_4held.size =
      b.sudo_5Board_4held.size := by
  simp [ontoCharge]

theorem ontoCharge_home_size (b : Ecbs.Board) (dst : Nat)
    (hD : dst < b.sudo_5Board_4held.size)
    (hH : dst < b.sudo_5Board_4home.size)
    (moves slides peg : Nat) :
    (ontoCharge b dst hD hH moves slides peg).sudo_5Board_4home.size =
      b.sudo_5Board_4home.size := by
  simp [ontoCharge]

theorem ontoCharge_moves (b : Ecbs.Board) (dst : Nat)
    (hD : dst < b.sudo_5Board_4held.size)
    (hH : dst < b.sudo_5Board_4home.size)
    (moves slides peg : Nat) :
    (ontoCharge b dst hD hH moves slides peg).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (moves + 2 * peg) := rfl

theorem ontoCharge_strict (b : Ecbs.Board) (dst : Nat)
    (hD : dst < b.sudo_5Board_4held.size)
    (hH : dst < b.sudo_5Board_4home.size)
    (moves slides peg : Nat) :
    (ontoCharge b dst hD hH moves slides peg).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := rfl

theorem ontoCharge_tier (b : Ecbs.Board) (dst : Nat)
    (hD : dst < b.sudo_5Board_4held.size)
    (hH : dst < b.sudo_5Board_4home.size)
    (moves slides peg : Nat) :
    (ontoCharge b dst hD hH moves slides peg).sudo_5Board_1t = b.sudo_5Board_1t := rfl

theorem ontoCharge_held_get (b : Ecbs.Board) (dst i : Nat)
    (hD : dst < b.sudo_5Board_4held.size)
    (hH : dst < b.sudo_5Board_4home.size)
    (moves slides peg : Nat) (hne : dst ≠ i)
    (hi : i < b.sudo_5Board_4held.size) :
    (ontoCharge b dst hD hH moves slides peg).sudo_5Board_4held[i]'(by
      rw [ontoCharge_held_size]; exact hi) =
      b.sudo_5Board_4held[i] := by
  simp [ontoCharge, Array.getElem_set_ne, hne]

theorem ontoCharge_home_get (b : Ecbs.Board) (dst i : Nat)
    (hD : dst < b.sudo_5Board_4held.size)
    (hH : dst < b.sudo_5Board_4home.size)
    (moves slides peg : Nat) (hne : dst ≠ i)
    (hi : i < b.sudo_5Board_4home.size) :
    (ontoCharge b dst hD hH moves slides peg).sudo_5Board_4home[i]'(by
      rw [ontoCharge_home_size]; exact hi) =
      b.sudo_5Board_4home[i] := by
  simp [ontoCharge, Array.getElem_set_ne, hne]

/-- Aim the bench, then `mulFromHeld`. The closure `mulElse` runs after the copy. -/
def ontoAfter (n dst first second : Int) (copy_second mirror : Bool)
    (b : Ecbs.Board) (σ : Int × Array Int) : Except SudoRt.Trap Ecbs.Board :=
  let strip := σ.2
  do
    let _t772 := ({ b with sudo_5Board_8bench_on := true } : Ecbs.Board)
    let b := _t772
    let _t773 := ({ b with sudo_5Board_8bench_to := dst } : Ecbs.Board)
    let b := _t773
    let _t774 := ({ b with sudo_5Board_5bench := strip } : Ecbs.Board)
    let b := _t774
    Ecbs.mulFromHeld n first second copy_second mirror b strip

private theorem aim3 (b : Ecbs.Board) (dst : Int) (strip : Array Int) :
    ({ { { b with sudo_5Board_8bench_on := true } with
        sudo_5Board_8bench_to := dst } with
      sudo_5Board_5bench := strip } : Ecbs.Board) =
      mulAimed b dst strip := by
  unfold mulAimed
  rfl

/-- `mulFromHeld` on a strip that already holds `pad`. The schoolbook is
    `school_loop_refines` starting from `pad`, and the fold is `mulAfter`. -/
theorem mul_onto_school (b : Ecbs.Board) (dst first second : Nat)
    (xs ys pad : List Nat) (n moves peakS : Nat)
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
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < pad.length)
    (hxsT : allTritList xs) (hpadT : allTritList pad)
    (hfi : FitsLen (2 * (n - 1)))
    (hfm : FitsLen (moves + n * (n + 1))) :
    Ecbs.mulFromHeld ((n : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        false false (mulAimed b ((dst : Nat) : Int) (embed pad)) (embed pad) =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep b ((dst : Nat) : Int) (embed pad) second peakS hS hHomeS)
            (Int.ofNat (moves + schoolMoves xs ys n n)),
          embed (school n xs ys pad false))) := by
  unfold Ecbs.mulFromHeld
  simp only [Bool.false_eq_true, if_false]
  rw [mulAimed_held, ← ofNat_eq_natCast first, atL_ofNat _ first hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  rw [mulAimed_home, atL_ofNat _ first hHome, hArr, ok_bind]
  unfold Ecbs.mulFromSrc
  have hbf : SudoRt.SEq.beq (↑second) (Int.ofNat first) = false := by
    rw [ofNat_eq_natCast first]
    exact nat_beq_false second first hne.symm
  rw [hbf]
  simp only [Bool.not_false, sudoAssert_true, ok_bind]
  let bA := mulAimed b ((dst : Nat) : Int) (embed pad)
  conv =>
    pattern (Ecbs.note_strict _)
    change Ecbs.note_strict bA
  have h7a : 7 ≤ bA.sudo_5Board_4held.size := by simpa [bA, mulAimed] using h7
  have hps : bA.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simpa [bA, mulAimed] using hpeakS
  rw [note_strict_eq bA peakS h7a hps]
  simp only [ok_bind, pure_eq_ok]
  let bS := strictBoard bA peakS
  have hheldS : bS.sudo_5Board_4held = bA.sudo_5Board_4held := rfl
  have hhomeS : bS.sudo_5Board_4home = bA.sudo_5Board_4home := rfl
  have hSs : second < bS.sudo_5Board_4held.size := by
    rw [hheldS]; simpa [bA, mulAimed] using hS
  have hHs : second < bS.sudo_5Board_4home.size := by
    rw [hhomeS]; simpa [bA, mulAimed] using hHomeS
  have hHeld2 : bS.sudo_5Board_4held[second] = true := by
    simp [bS, strictBoard, bA, mulAimed, hHS]
  have hHome2 : bS.sudo_5Board_4home[second] = embed ys := by
    simp [bS, strictBoard, bA, mulAimed, hYs]
  rw [← ofNat_eq_natCast second, atL_ofNat _ second hSs, hHeld2]
  simp only [sudoAssert_true, ok_bind]
  rw [atL_ofNat _ second hHs, hHome2, ok_bind]
  rw [putL_ofNat _ second false hSs, ok_bind]
  rw [putL_ofNat _ second (#[] : Array Int) hHs, ok_bind]
  rw [show ((n : Nat) : Int) = Int.ofNat n from (ofNat_eq_natCast n).symm]
  unfold Ecbs.schoolFinish
  rw [subI_ofNat_one n hn0 hf, ok_bind]
  dsimp only
  have hfuel :
      (if Int.ofNat (n - 1) < (0 : Int) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelDown (Int.ofNat (n - 1)) (Int.ofNat 0) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  rw [hfuel]
  conv =>
    pattern (rowStep _ _ _ _ _)
    change rowStep (embed xs) (embed ys) false (Int.ofNat n) (0 : Int)
  conv =>
    pattern (fun σ : Int × (Ecbs.Board × Array Int) => _)
    change mulAfter
  let bL := mulPrep b ((dst : Nat) : Int) (embed pad) second peakS hS hHomeS
  conv =>
    pattern (Int.ofNat (n - 1), _)
    change (Int.ofNat (n - 1), (bL, embed pad))
  have hmL : bL.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    rw [show bL.sudo_5Board_4cost.sudo_5Costs_5moves =
        b.sudo_5Board_4cost.sudo_5Costs_5moves from by simp [bL, mulPrep_moves]]
    simpa [ofNat_eq_natCast] using hmoves
  rw [school_loop_refines xs ys pad moves n false bL mulAfter (fun r => pure r)
      hn0 (by rw [hlenx]; exact Nat.le_refl _) (by rw [hleny]; exact Nat.le_refl _)
      hspan hxsT hpadT hmL hf hfi hfm]
  exact bind_pure_id _

/-- Clearing `dst`, charging twice its peg count, copying it onto the zero
    strip, then the schoolbook. Marker flag is untouched. Bench starts off,
    so `settle` is the identity. -/
theorem mul_onto_else (b : Ecbs.Board) (dst first second : Nat)
    (home xs ys : List Nat) (n moves slides peakS bench : Nat)
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
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hneD1 : dst ≠ first) (hneD2 : dst ≠ second) (hne : first ≠ second)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hlenH : home.length = n) (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hhomeT : allTritList home) (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfitM : FitsLen (moves + 2 * n))
    (hfitS : FitsLen (slides + 2 * n))
    (hfm : FitsLen (moves + 2 * n + n * (n + 1))) :
    let peg := pegCount home
    let bC := ontoCharge b dst hD hHD moves slides peg
    let pad := pref home bench n
    Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) false true false b =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep bC ((dst : Nat) : Int) (embed pad) second peakS
              (by rw [ontoCharge_held_size]; exact hS)
              (by rw [ontoCharge_home_size]; exact hHomeS))
            (Int.ofNat (moves + 2 * peg + schoolMoves xs ys n n)),
          embed (school n xs ys pad false))) := by
  intro peg bC pad
  have hpegLe : peg ≤ n := by
    simpa [peg, hlenH] using pegCount_le home
  have h2 : FitsLen (2 * peg) := FitsLen.of_le hfitM (by omega)
  have hfitMc : FitsLen (moves + 2 * peg) := FitsLen.of_le hfitM (by omega)
  have hfitSc : FitsLen (slides + 2 * peg) := FitsLen.of_le hfitS (by omega)
  have hfmC : FitsLen (moves + 2 * peg + n * (n + 1)) :=
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
  have hpadT : allTritList pad :=
    pref_trits home bench n hhomeT hnb (by omega)
  have hpost :
      ontoAfter ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
          ((second : Nat) : Int) false false bC
          (Int.ofNat (n - 1), embed pad) =
        mulAfter (Int.ofNat 0,
          (withMoves
              (mulPrep bC ((dst : Nat) : Int) (embed pad) second peakS
                (by rw [ontoCharge_held_size]; exact hS)
                (by rw [ontoCharge_home_size]; exact hHomeS))
              (Int.ofNat (moves + 2 * peg + schoolMoves xs ys n n)),
            embed (school n xs ys pad false))) := by
    unfold ontoAfter
    rw [aim3]
    have hmovesC : bC.sudo_5Board_4cost.sudo_5Costs_5moves =
        ((moves + 2 * peg : Nat) : Int) := by
      rw [ontoCharge_moves, ofNat_eq_natCast]
    have hpeakC : bC.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
      rw [ontoCharge_strict]; exact hpeakS
    have h7C : 7 ≤ bC.sudo_5Board_4held.size := by
      rw [ontoCharge_held_size]; exact h7
    have hFC : first < bC.sudo_5Board_4held.size := by
      rw [ontoCharge_held_size]; exact hF
    have hHomeC : first < bC.sudo_5Board_4home.size := by
      rw [ontoCharge_home_size]; exact hHome
    have hSC : second < bC.sudo_5Board_4held.size := by
      rw [ontoCharge_held_size]; exact hS
    have hHomeSC : second < bC.sudo_5Board_4home.size := by
      rw [ontoCharge_home_size]; exact hHomeS
    have hHFC : bC.sudo_5Board_4held[first] = true := by
      rw [ontoCharge_held_get _ _ _ _ _ _ _ _ hneD1 hF]; exact hHF
    have hArrC : bC.sudo_5Board_4home[first] = embed xs := by
      rw [ontoCharge_home_get _ _ _ _ _ _ _ _ hneD1 hHome]; exact hArr
    have hHSC : bC.sudo_5Board_4held[second] = true := by
      rw [ontoCharge_held_get _ _ _ _ _ _ _ _ hneD2 hS]; exact hHS
    have hYsC : bC.sudo_5Board_4home[second] = embed ys := by
      rw [ontoCharge_home_get _ _ _ _ _ _ _ _ hneD2 hHomeS]; exact hYs
    exact mul_onto_school bC dst first second xs ys pad n (moves + 2 * peg) peakS
      hFC hHomeC hHFC hArrC hSC hHomeSC hHSC hYsC h7C hne hn0 hlenx hleny hf
      hmovesC hpeakC hspanP hxsT hpadT hfi hfmC
  conv =>
    pattern (fun σ : Int × Array Int => _)
    change ontoAfter ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
      ((second : Nat) : Int) false false bC
  have hcopy := band_copy_after home bench n
      (ontoAfter ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
        ((second : Nat) : Int) false false bC)
      (fun r => Except.ok r)
      (mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep bC ((dst : Nat) : Int) (embed pad) second peakS
              (by rw [ontoCharge_held_size]; exact hS)
              (by rw [ontoCharge_home_size]; exact hHomeS))
            (Int.ofNat (moves + 2 * peg + schoolMoves xs ys n n)),
          embed (school n xs ys pad false))))
      hn0 hnb (by rw [hlenH]; exact Nat.le_refl n) hf hpost
  rw [hcopy, bind_ok_id, ofNat_eq_natCast dst]

/-- Marker off, bench off. `Ecbs.mul` with `onto` is `mulElse` after the op bump. -/
theorem mul_onto_off (b : Ecbs.Board) (dst first second : Nat)
    (home xs ys : List Nat) (n moves slides peakS bench cOps : Nat)
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
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hneD1 : dst ≠ first) (hneD2 : dst ≠ second) (hne : first ≠ second)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenH : home.length = n) (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hhomeT : allTritList home) (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfitM : FitsLen (moves + 2 * n))
    (hfitS : FitsLen (slides + 2 * n))
    (hfm : FitsLen (moves + 2 * n + n * (n + 1))) :
    let b0 := bumpOp b 0 cOps hops
    let peg := pegCount home
    let bC := ontoCharge b0 dst
      (by rw [bumpOp_held]; exact hD) (by rw [bumpOp_home]; exact hHD)
      moves slides peg
    let pad := pref home bench n
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        false true false =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep bC ((dst : Nat) : Int) (embed pad) second peakS
              (by rw [ontoCharge_held_size, bumpOp_held]; exact hS)
              (by rw [ontoCharge_home_size, bumpOp_home]; exact hHomeS))
            (Int.ofNat (moves + 2 * peg + schoolMoves xs ys n n)),
          embed (school n xs ys pad false))) := by
  intro b0 peg bC pad
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
  have hHeldDB : b0.sudo_5Board_4held[dst] = true := by
    simp [b0, bumpOp_held, hHeldD]
  have hHomeDB : b0.sudo_5Board_4home[dst] = embed home := by
    simp [b0, bumpOp_home, hHomeD]
  have hFB : first < b0.sudo_5Board_4held.size := by simp [b0, bumpOp_held]; exact hF
  have hHomeB : first < b0.sudo_5Board_4home.size := by simp [b0, bumpOp_home]; exact hHome
  have hHFB : b0.sudo_5Board_4held[first] = true := by simp [b0, bumpOp_held, hHF]
  have hArrB : b0.sudo_5Board_4home[first] = embed xs := by simp [b0, bumpOp_home, hArr]
  have hSB : second < b0.sudo_5Board_4held.size := by simp [b0, bumpOp_held]; exact hS
  have hHomeSB : second < b0.sudo_5Board_4home.size := by simp [b0, bumpOp_home]; exact hHomeS
  have hHSB : b0.sudo_5Board_4held[second] = true := by simp [b0, bumpOp_held, hHS]
  have hYsB : b0.sudo_5Board_4home[second] = embed ys := by simp [b0, bumpOp_home, hYs]
  have h7B : 7 ≤ b0.sudo_5Board_4held.size := by simp [b0, bumpOp_held]; exact h7
  have hmovesB : b0.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simp [b0, bumpOp_moves, hmoves]
  have hslidesB : b0.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int) := by
    simp [b0, bumpOp, hslides]
  have hpeakB : b0.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simp [b0, bumpOp, hpeakS]
  exact mul_onto_else b0 dst first second home xs ys n moves slides peakS bench
    hoffB hblB hDB hHDB hHeldDB hHomeDB hFB hHomeB hHFB hArrB hSB hHomeSB hHSB hYsB
    h7B hneD1 hneD2 hne hn0 hnb hlenH hlenx hleny hf hmovesB hslidesB hpeakB
    hspan hhomeT hxsT hfi hfitM hfitS hfm

/-- Marker on and already seated, bench off. `log_op` steps the marker, then the
    onto multiply is `mulElse` on that board. The flag stays on. -/
theorem mul_onto_up (b : Ecbs.Board) (dst first second : Nat)
    (home xs ys : List Nat)
    (n moves slides peakS bench cOps m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hscript : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitMk : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
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
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hneD1 : dst ≠ first) (hneD2 : dst ≠ second) (hne : first ≠ second)
    (hn0 : 0 < n) (hnb : n ≤ bench)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenH : home.length = n) (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hspan : 2 * (n - 1) < bench)
    (hhomeT : allTritList home) (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfitM : FitsLen (moves + 2 * n))
    (hfitS : FitsLen (slides + 2 * n))
    (hfm : FitsLen (moves + 2 * n + n * (n + 1))) :
    let feed := markerUpFeed b m ctrl mx
    let hopsF : 0 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      simpa [feed, markerUpFeed] using hops
    let bU := { bumpOp feed 0 cOps hopsF with sudo_5Board_9marker_on := true }
    let peg := pegCount home
    let bC := ontoCharge bU dst
      (by simp only [bU, bumpOp_held, feed, markerUpFeed]; exact hD)
      (by simp only [bU, bumpOp_home, feed, markerUpFeed]; exact hHD)
      moves slides peg
    let pad := pref home bench n
    Ecbs.mul b ((dst : Nat) : Int) ((first : Nat) : Int) ((second : Nat) : Int)
        false true false =
      mulAfter (Int.ofNat 0,
        (withMoves
            (mulPrep bC ((dst : Nat) : Int) (embed pad) second peakS
              (by simp only [bC, ontoCharge_held_size, bU, bumpOp_held, feed, markerUpFeed]; exact hS)
              (by simp only [bC, ontoCharge_home_size, bU, bumpOp_home, feed, markerUpFeed]; exact hHomeS))
            (Int.ofNat (moves + 2 * peg + schoolMoves xs ys n n)),
          embed (school n xs ys pad false))) := by
  intro feed hopsF bU peg bC pad
  rw [mul_keep_eq]
  unfold Ecbs.mulKeep
  rw [show Ecbs.op_mul = Int.ofNat 0 from rfl, atL_ofNat _ 0 hops, hop0, ok_bind,
    ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
    putL_ofNat _ 0 (Int.ofNat (cOps + 1)) hops, ok_bind]
  dsimp only
  let b0 := bumpOp b 0 cOps hops
  have hbump :
      ({ b with sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_3ops :=
            b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) } } :
        Ecbs.Board) = b0 := by
    simp [b0, bumpOp]
  rw [hbump]
  rw [log_op_on b0 (by simp [b0, bumpOp, hmk])]
  have hmB : b0.sudo_5Board_6marker = Int.ofNat m := by simp [b0, bumpOp, hm]
  have hcB : b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simp [b0, bumpOp, hc]
  have hxB : b0.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx := by
    simp [b0, bumpOp, hx]
  have hsB : b0.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simp [b0, bumpOp, hscript]
  rw [marker_step_up b0 m ctrl mx script hmB hcB hxB hsB hbound hfitMk hfitC hfit2]
  rw [← mul_up_bump b m ctrl mx cOps hops hmk]
  simp only [ok_bind]
  have hU : { bumpOp feed 0 cOps hopsF with sudo_5Board_9marker_on := true } = bU := rfl
  rw [hU]
  have hnB : bU.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp [bU, bumpOp, feed, markerUpFeed, hn]
  rw [hnB]
  have hoffP : (bumpOp feed 0 cOps hopsF).sudo_5Board_8bench_on = false := by
    simp only [bumpOp, feed, markerUpFeed, hoff]
  rw [hoffP]
  simp only [decide_False, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]
  have hoffB : bU.sudo_5Board_8bench_on = false := by
    simp [bU, bumpOp, feed, markerUpFeed, hoff]
  have hblB : bU.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [bU, bumpOp, feed, markerUpFeed, hbl]
  have hDB : dst < bU.sudo_5Board_4held.size := by
    simp [bU, bumpOp_held, feed, markerUpFeed]; exact hD
  have hHDB : dst < bU.sudo_5Board_4home.size := by
    simp [bU, bumpOp_home, feed, markerUpFeed]; exact hHD
  have hHeldDB : bU.sudo_5Board_4held[dst] = true := by
    simp [bU, bumpOp_held, feed, markerUpFeed, hHeldD]
  have hHomeDB : bU.sudo_5Board_4home[dst] = embed home := by
    simp [bU, bumpOp_home, feed, markerUpFeed, hHomeD]
  have hFB : first < bU.sudo_5Board_4held.size := by
    simp [bU, bumpOp_held, feed, markerUpFeed]; exact hF
  have hHomeB : first < bU.sudo_5Board_4home.size := by
    simp [bU, bumpOp_home, feed, markerUpFeed]; exact hHome
  have hHFB : bU.sudo_5Board_4held[first] = true := by
    simp [bU, bumpOp_held, feed, markerUpFeed, hHF]
  have hArrB : bU.sudo_5Board_4home[first] = embed xs := by
    simp [bU, bumpOp_home, feed, markerUpFeed, hArr]
  have hSB : second < bU.sudo_5Board_4held.size := by
    simp [bU, bumpOp_held, feed, markerUpFeed]; exact hS
  have hHomeSB : second < bU.sudo_5Board_4home.size := by
    simp [bU, bumpOp_home, feed, markerUpFeed]; exact hHomeS
  have hHSB : bU.sudo_5Board_4held[second] = true := by
    simp [bU, bumpOp_held, feed, markerUpFeed, hHS]
  have hYsB : bU.sudo_5Board_4home[second] = embed ys := by
    simp [bU, bumpOp_home, feed, markerUpFeed, hYs]
  have h7B : 7 ≤ bU.sudo_5Board_4held.size := by
    simp [bU, bumpOp_held, feed, markerUpFeed]; exact h7
  have hmovesB : bU.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simp [bU, bumpOp, feed, markerUpFeed, hmoves]
  have hslidesB : bU.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int) := by
    simp [bU, bumpOp, feed, markerUpFeed, hslides]
  have hpeakB : bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simp [bU, bumpOp, feed, markerUpFeed, hpeakS]
  exact mul_onto_else bU dst first second home xs ys n moves slides peakS bench
    hoffB hblB hDB hHDB hHeldDB hHomeDB hFB hHomeB hHFB hArrB hSB hHomeSB hHSB hYsB
    h7B hneD1 hneD2 hne hn0 hnb hlenH hlenx hleny hf hmovesB hslidesB hpeakB
    hspan hhomeT hxsT hfi hfitM hfitS hfm

/-- The folded `onto` strip's length-`n` prefix is the home plus `fieldMul`. -/
theorem mul_onto_add (n k bench : Nat) (xs ys home : List Nat)
    (ht : allTritList home) (hlen : home.length = n)
    (hspan : 2 * (n - 1) < bench) (hnb : n ≤ bench) :
    (laneFold n (n - k) (school n xs ys (pref home bench n) false)).take n =
      fieldAdd n home (fieldMul n k bench xs ys) :=
  onto_add n k bench xs ys home ht hlen (Or.inl hspan) hnb

end EcbsLink2.Link2
