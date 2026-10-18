/-
  A bench-off multiply folds to a field value. `copy_second` and `onto` both
  false is `fieldMul`. That is a gap line of `fform_add`, and the first
  multiply of the new across and the new up when the mirror flag is off.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformGap
import EcbsLink2.Link2.FieldLin

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem fold_ops_here (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

private theorem fold_peak_out (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat)
    (hno : ¬ peak < countHeld b.sudo_5Board_4held 7) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_4peak =
      (peak : Int) := by
  unfold ontoFoldBoard peakBoard raisedPeak noteBench withMoves withHole
  dsimp only
  split <;> simp [hno, ofNat_eq_natCast]

private theorem fold_strict_out (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

private theorem fold_hole_out (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      (if decide (Int.ofNat (topIdx sch) >
            b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) then
          Int.ofNat (topIdx sch)
        else b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) := by
  unfold ontoFoldBoard peakBoard
  rw [noteBench_hole]

private theorem fold_held_out (b : Ecbs.Board) (sch : List Nat) (n k mv peak : Nat) :
    (ontoFoldBoard b sch n k mv peak).sudo_5Board_4held = b.sudo_5Board_4held := by
  unfold ontoFoldBoard peakBoard noteBench withMoves withHole
  split <;> rfl

/-- Bench off, not onto, not a copy. The length-`n` prefix is `fieldMul` of
    the two homes. The mirror flag is off, so this is SPEC.md's product, not
    a mirrored one. -/
theorem nocopy_else_field (b : Ecbs.Board) (dst first second : Nat)
    (xs ys : List Nat)
    (w h r n k moves hole peak peakS bench : Nat)
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
    (hne : first ≠ second) (hn0 : 0 < n) (hnb : n ≤ bench)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeak7 : 7 ≤ peak)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeakS7 : 7 ≤ peakS)
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
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
    (hfold : FitsLen (moves + n * (n + 1) + 3 * (bench - n))) :
    ∃ b',
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
          ((second : Nat) : Int) false false false b = .ok b' ∧
      b'.sudo_5Board_5bench =
        embed (laneFold n (n - k)
          (school n xs ys (List.replicate bench 0) false)) ∧
      (laneFold n (n - k)
          (school n xs ys (List.replicate bench 0) false)).take n =
        fieldMul n k bench xs ys ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        (if decide (Int.ofNat (topIdx (school n xs ys (List.replicate bench 0) false)) >
              Int.ofNat hole) then
            Int.ofNat (topIdx (school n xs ys (List.replicate bench 0) false))
          else Int.ofNat hole) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      (∀ j, j ≠ second → ∀ hj : j < b.sudo_5Board_4held.size,
        ∀ hj' : j < b'.sudo_5Board_4held.size,
          b'.sudo_5Board_4held[j]'hj' = b.sudo_5Board_4held[j]'hj) := by
  have hOff := nocopy_else_off b dst first second xs ys n moves peakS bench false
    hoff hbl hF hHome hHF hArr hS hHomeS hHS hYs h7 hne hn0 hn hlenx hleny hf
    hmoves hpeakS hspan hxsT hfi hfm
  let pad := List.replicate bench 0
  let sch := school n xs ys pad false
  let mvN := moves + schoolMoves xs ys n n
  let bFold := withMoves
      (mulPrep b ((dst : Nat) : Int) (embed pad) second peakS hS hHomeS)
      (Int.ofNat mvN)
  have hma : Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
      ((second : Nat) : Int) false false false b =
      mulAfter (Int.ofNat 0, (bFold, embed sch)) := by
    simpa [bFold, sch, pad, mvN] using hOff
  have hschLen : sch.length = bench := by
    simpa [sch, pad, List.length_replicate] using school_length xs ys pad false n
  have hschT : allTritList sch :=
    school_trits xs ys pad false n
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
  have hpeakB : bFold.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, hpeak]
  have hholeB : bFold.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, hhole]
  have h7B : 7 ≤ bFold.sudo_5Board_4held.size := by
    simp [bFold, withMoves, mulPrep, mulAimed, strictBoard, Array.size_set]
    exact h7
  have hwB : bFold.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, hw]
  have hhB : bFold.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, hh]
  have hrB : bFold.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, hr]
  have hnB : bFold.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, hn, ofNat_eq_natCast]
  have hkB : bFold.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, hk]
  have hblB : bFold.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, hbl]
  have hfitF : FitsLen (mvN + 3 * (sch.length - n)) := by
    rw [hschLen]
    refine FitsLen.of_le hfold ?_
    have hsch : schoolMoves xs ys n n ≤ n * (n + 1) := schoolMoves_bound xs ys n
    omega
  have hOk := mulAfter_ok bFold sch w h r n k mvN hole bench peak
      (by rw [hschLen]; exact hfitB) hwB hhB hrB hnB hkB hblB hw0 hh0 hrR hrP hnE hkLe hgap
      hschT hmB hholeB hpeakB h7B (by rw [hschLen]; exact hsm) hnsm hfitF
      (by rw [hschLen]; exact Nat.le_refl bench) (Nat.lt_of_lt_of_le hn0 hnb)
  have hnoF : ¬ peak < countHeld bFold.sudo_5Board_4held 7 := by
    have hle : countHeld bFold.sudo_5Board_4held 7 ≤ 7 := countHeld_seven _
    omega
  have hstrictB : bFold.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    have hcount : countHeld b.sudo_5Board_4held 7 ≤ 7 := countHeld_seven _
    have hnot : ¬ peakS < countHeld b.sudo_5Board_4held 7 := by omega
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed, raisedPeak, hpeakS, hnot,
      ofNat_eq_natCast]
  have hopsB : bFold.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops := by
    simp [bFold, withMoves, mulPrep, strictBoard, mulAimed]
  have hheldB : bFold.sudo_5Board_4held =
      b.sudo_5Board_4held.set ⟨second, hS⟩ false := by
    simp [bFold, withMoves, mulPrep, mulAimed]
  refine ⟨ontoFoldBoard bFold sch n k mvN peak, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hma]
    exact hOk
  · simpa [sch, pad] using ontoFoldBoard_bench bFold sch n k mvN peak
  · simpa [sch, pad] using zero_school_mul n k bench xs ys
  · exact fold_peak_out bFold sch n k mvN peak hnoF
  · rw [fold_strict_out bFold sch n k mvN peak, hstrictB]
  · rw [fold_hole_out bFold sch n k mvN peak, hholeB]
  · exact (fold_ops_here bFold sch n k mvN peak).trans hopsB
  · rw [fold_held_out bFold sch n k mvN peak, hheldB, Array.size_set]
  · intro j hneJ hj hj'
    have hEq : (ontoFoldBoard bFold sch n k mvN peak).sudo_5Board_4held =
        b.sudo_5Board_4held.set ⟨second, hS⟩ false :=
      (fold_held_out bFold sch n k mvN peak).trans hheldB
    have hset : j < (b.sudo_5Board_4held.set ⟨second, hS⟩ false).size := by
      rw [Array.size_set]; exact hj
    have hv : (b.sudo_5Board_4held.set ⟨second, hS⟩ false)[j]'hset =
        b.sudo_5Board_4held[j]'hj := by
      rw [Array.getElem_set, if_neg (Ne.symm hneJ)]
    exact cell_eq_of hEq hv

/-- The run multiply with the across already mirrored. The bench prefix is
    SPEC.md §3 R7's run `v = x₂Z − X`. -/
theorem run_is_fformRun (b : Ecbs.Board) (dst first second : Nat)
    (x xs ys : List Nat)
    (w h r n k moves slides hole peak peakS bench : Nat)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hD : dst < b.sudo_5Board_4held.size)
    (hHD : dst < b.sudo_5Board_4home.size)
    (hHeldD : b.sudo_5Board_4held[dst] = true)
    (hHomeD : b.sudo_5Board_4home[dst] = embed (mirrorTrits x))
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
    (hlenx0 : x.length = n) (hlenx : xs.length = n) (hleny : ys.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hpeak7 : 7 ≤ peak)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeakS7 : 7 ≤ peakS)
    (hspan : 2 * (n - 1) < bench)
    (hxsT : allTritList xs)
    (hfi : FitsLen (2 * (n - 1)))
    (hfitM : FitsLen (moves + 3 * n))
    (hfitS : FitsLen (slides + 2 * n))
    (hfm : FitsLen (moves + 3 * n + n * (n + 1)))
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
    (hfold : FitsLen (moves + 3 * n + n * (n + 1) + 3 * (bench - n))) :
    ∃ b',
      Ecbs.mulElse ((n : Nat) : Int) ((dst : Nat) : Int) ((first : Nat) : Int)
          ((second : Nat) : Int) true true false b = .ok b' ∧
      (laneFold n (n - k)
          (school n xs ys (pref (mirrorTrits x) bench n) false)).take n =
        fformRun n k bench xs ys x := by
  have hmir : allTritList (mirrorTrits x) := by
    intro a ha
    simp only [mirrorTrits, List.mem_map] at ha
    rcases ha with ⟨c, _, rfl⟩
    by_cases hc0 : c = 0
    · simp [hc0]
    · by_cases hc1 : c = 1
      · simp [hc1]
      · by_cases hc2 : c = 2
        · simp [hc2]
        · have hge : 3 ≤ c := by omega
          simp [hc0]
          omega
  have hlenM : (mirrorTrits x).length = n := by
    simp [mirrorTrits, List.length_map, hlenx0]
  obtain ⟨b', hok, _, htake, _, _, _, _, _, _⟩ := run_else_field b dst first second (mirrorTrits x) xs ys
    w h r n k moves slides hole peak peakS bench hoff hbl hD hHD hHeldD hHomeD
    hF hHome hHF hArr hS hHomeS hHS hYs hSpH hSpHome hSpE h7 hneD1 hneD2 hne6D
    hne6F hne6S hn0 hnb hn hlenM hlenx hleny hf hmoves hslides hpeak hpeak7 hpeakS hpeakS7
    hspan hmir hxsT hfi hfitM hfitS hfm hhole hw0 hh0 hrR hrP hnE hkLe hgap hw hh hr hk
    hsm hnsm hfitB hfold
  refine ⟨b', hok, ?_⟩
  rw [htake]
  unfold fformRun
  rfl

private theorem embed_zero_decide (ys : List Nat) (n : Nat) (hlen : ys.length = n) :
    decide (∀ i (h : i < (embed ys).size), (embed ys)[i] = 0) =
      decide (ys = List.replicate n 0) := by
  have hiff :
      (∀ i (h : i < (embed ys).size), (embed ys)[i] = 0) ↔ ys = List.replicate n 0 := by
    constructor
    · intro hzero
      apply List.ext_getElem
      · simp [hlen, List.length_replicate]
      · intro i hi1 hi2
        have hi : i < n := by simpa [List.length_replicate] using hi2
        have hembed : i < (embed ys).size := by rw [size_embed, hlen]; exact hi
        have hget := hzero i hembed
        rw [get_embed] at hget
        have hnat : ys[i]'(by rw [hlen]; exact hi) = 0 := by
          have hz : Int.ofNat (ys[i]'(by rw [hlen]; exact hi)) = Int.ofNat 0 := by
            simpa using hget
          exact Int.ofNat.inj hz
        simpa [List.getElem_replicate] using hnat
    · intro hys i hi
      subst hys
      rw [get_embed, List.getElem_replicate]
      simp
  by_cases hq : ys = List.replicate n 0
  · rw [decide_eq_true (hiff.2 hq), decide_eq_true hq]
  · rw [decide_eq_false (fun h => hq (hiff.1 h)), decide_eq_false hq]

/-- `is_zero` reads the bench when that home is empty and the bench is aimed
    there. The flag is whether the length-`n` prefix is the zero home. -/
theorem bench_is_zero (b : Ecbs.Board) (home : Nat) (xs : List Nat) (n : Nat)
    (hD : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx : n ≤ xs.length) (hf : FitsLen n)
    (hlen : (xs.take n).length = n) :
    Ecbs.is_zero b (home : Int) = .ok (decide (xs.take n = List.replicate n 0)) := by
  unfold Ecbs.is_zero
  rw [value_bench_refines b home xs n hD hheld hon hto hbench hn hx hf, ok_bind]
  have hfA : FitsLen (embed (xs.take n)).size := by
    rw [size_embed, hlen]
    exact hf
  rw [is_empty_refines _ hfA, ok_bind, pure_eq_ok, embed_zero_decide (xs.take n) n hlen]

/-- Laying a mirrored schoolbook onto a home and folding is the home plus
    `mirrorTrits` of the product. A red rise uses this. -/
theorem onto_add_mirror (n k bench : Nat) (a b home : List Nat)
    (ht : allTritList home) (ha : allTritList a) (hb : allTritList b)
    (hlen : home.length = n)
    (hspan : 2 * (n - 1) < bench) (hnb : n ≤ bench) :
    (laneFold n (n - k) (school n a b (pref home bench n) true)).take n =
      fieldAdd n home (mirrorTrits (fieldMul n k bench a b)) := by
  have hx : n ≤ home.length := by omega
  have hpadLen : (pref home bench n).length = bench := pref_length hnb hx
  have hpadT : allTritList (pref home bench n) := pref_trits home bench n ht hnb hx
  have hy : ∀ e, n ≤ e → coeff (pref home bench n) e = 0 :=
    fun e he => pref_coeff_hi home bench n e hnb hx he
  have hspanP : 2 * (n - 1) < (pref home bench n).length ∨ n = 0 := by
    rw [hpadLen]
    exact Or.inl hspan
  rw [school_onto n a b (pref home bench n) true hpadT hspanP]
  have hmir := school_mirror n bench a b ha hb
  rw [hpadLen, hmir]
  have hsch : allTritList (school n a b (List.replicate bench 0) false) :=
    school_zero_trits n bench a b hb
  have hfold := laneFold_pad n (n - k)
      ((school n a b (List.replicate bench 0) false).map flipTrit) (pref home bench n)
      (by
        rw [List.length_map, school_length, List.length_replicate]
        exact hpadLen)
      (by
        intro x hxmem
        simp only [List.mem_map] at hxmem
        rcases hxmem with ⟨c, hc, rfl⟩
        exact flipTrit_le c)
      hy (Nat.sub_le n k)
  rw [hfold]
  have hflip : laneFold n (n - k) ((school n a b (List.replicate bench 0) false).map flipTrit) =
      (laneFold n (n - k) (school n a b (List.replicate bench 0) false)).map flipTrit := by
    rw [laneFold, laneFold, reduceStrip_flip n (n - k) _ hsch]
  rw [hflip]
  have hlenF : (laneFold n (n - k) (school n a b (List.replicate bench 0) false)).length = bench := by
    rw [laneFold_length _ _ _ (by rw [school_length, List.length_replicate]; exact hnb),
      school_length, List.length_replicate]
  have htake : n ≤
      ((laneFold n (n - k) (school n a b (List.replicate bench 0) false)).map flipTrit).length := by
    rw [List.length_map, hlenF]
    exact hnb
  rw [stripAdd_take n _ _ htake, fieldAdd_comm]
  have hlo : ∀ i, i < n → coeff (pref home bench n) i = coeff home i :=
    fun i hi => pref_coeff_lo home bench n i hnb hx hi
  rw [fieldAdd_coeff n (pref home bench n)
      ((laneFold n (n - k) (school n a b (List.replicate bench 0) false)).map flipTrit)
      home ((laneFold n (n - k) (school n a b (List.replicate bench 0) false)).map flipTrit)
      hlo (fun _ _ => rfl)]
  rw [← fieldAdd_right_take n home _ (by rw [List.length_map, hlenF]; exact hnb)]
  have hmap : (((laneFold n (n - k) (school n a b (List.replicate bench 0) false)).take n).map
      flipTrit) =
      mirrorTrits ((laneFold n (n - k) (school n a b (List.replicate bench 0) false)).take n) := by
    rw [mirrorTrits_map, List.map_take]
  rw [← List.map_take, hmap]
  unfold fieldMul laneFold
  rfl

end EcbsLink2.Link2
