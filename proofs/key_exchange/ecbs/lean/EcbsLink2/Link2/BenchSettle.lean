/-
  Clear a held home the bench is aimed at, then settle. The home becomes the
  length-`n` bench prefix. SPEC.md §3 R7 line 156, put it into the bottom.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BenchAdd
import EcbsLink2.Link2.Settle

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

theorem settleBoard_on (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_8bench_on = false := by
  unfold settleBoard
  split <;> rfl

theorem settleBoard_home (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat) :
    (settleBoard b home hH hD xs n moves slides peak).sudo_5Board_4home =
      b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (xs.take n)) := by
  unfold settleBoard
  split <;> rfl

/-- `clear` of the held home, then `settle` of the bench aimed at it.
    The home becomes the length-`n` prefix. The bench turns off. The settle
    charges stay hypotheses, as in `chord_gap_settle`. -/
theorem clear_settle_held (b : Ecbs.Board) (home : Nat) (zs bench : List Nat)
    (n moves slides peak : Nat)
    (hH : home < b.sudo_5Board_4home.size)
    (hD : home < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home] = true)
    (harr : b.sudo_5Board_4home[home] = embed zs)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (home : Int))
    (hbench : b.sudo_5Board_5bench = embed bench)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hposB : 0 < bench.length) (hnle : n ≤ bench.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < bench.length, bench[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen bench.length) (hfitZ : FitsLen zs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfitC : FitsLen (moves + pegCount zs))
    (hpeg : FitsLen (2 * pegCount (bench.take n)))
    (hfitM : FitsLen (moves + pegCount zs + 2 * pegCount (bench.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (bench.take n))) :
    ∃ b',
      (do
          let b ← Ecbs.clear b (home : Int)
          Ecbs.settle b) = .ok b' ∧
      b'.sudo_5Board_8bench_on = false ∧
      b'.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨home, hH⟩ (embed (bench.take n)) := by
  have hclear := clear_held_refines b home zs moves hH hD hheld harr hmoves hfitZ hfitC
  rw [hclear, ok_bind]
  let mvC := moves + pegCount zs
  let bC :=
    { b with
      sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ #[]
      sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ false
      sudo_5Board_4cost := { b.sudo_5Board_4cost with
        sudo_5Costs_5moves := Int.ofNat mvC } }
  have hHc : home < bC.sudo_5Board_4home.size := by
    simpa [bC, Array.size_set] using hH
  have hDc : home < bC.sudo_5Board_4held.size := by
    simpa [bC, Array.size_set] using hD
  have h7c : 7 ≤ bC.sudo_5Board_4held.size := by
    simpa [bC, Array.size_set] using h7
  have hempty : bC.sudo_5Board_4held[home] = false := by
    simp [bC, Array.get_set_eq]
  have hbenchC : bC.sudo_5Board_5bench = embed bench := by
    simpa [bC] using hbench
  have honC : bC.sudo_5Board_8bench_on = true := by simpa [bC] using hon
  have htoC : bC.sudo_5Board_8bench_to = (home : Int) := by simpa [bC] using hto
  have hnC : bC.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by simpa [bC] using hn
  have hmC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simp [bC, mvC]
  have hsC : bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    simpa [bC, ofNat_eq_natCast] using hslides
  have hpC : bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    simpa [bC, ofNat_eq_natCast] using hpeak
  have hsettle := settle_refines bC home bench n mvC slides peak hHc hDc h7c honC htoC
    hempty hbenchC hnC hposB hnle hzero hf hfitL hmC hsC hpC hpeg hfitM hfitS
  rw [hsettle]
  refine ⟨settleBoard bC home hHc hDc bench n mvC slides peak, rfl, ?_, ?_⟩
  · exact settleBoard_on bC home hHc hDc bench n mvC slides peak
  · rw [settleBoard_home bC home hHc hDc bench n mvC slides peak]
    apply Array.ext
    · simp [Array.size_set]
    · intro j _ _
      by_cases hje : home = j
      · simp [Array.getElem_set_eq, hje]
      · simp [Array.getElem_set_ne, hje]

theorem addOnto_high (bench src : List Nat) (mirror : Bool) (k i : Nat)
    (hk : k ≤ i) (hi : i < bench.length) :
    (addOnto bench src mirror k)[i]'(by rw [addOnto_length]; exact hi) = bench[i] := by
  rw [addOnto_get bench src mirror k i hi, if_neg (by omega), coeff_eq_get bench i hi]

/-- Across with the mirror off, the bottom with the mirror on, clear that home,
    then settle. The bottom becomes `fieldAdd` of the starting prefix with the
    across, then with `mirrorTrits` of the bottom. SPEC.md §3 R7 line 156.
    The bench turns off. The settle charges stay hypotheses. -/
theorem across_bottom_settle (b : Ecbs.Board) (xHome zHome : Nat)
    (xs zs bench : List Nat) (n moves slides peak : Nat)
    (hxH : xHome < b.sudo_5Board_4home.size)
    (hxA : b.sudo_5Board_4home[xHome] = embed xs)
    (hzH : zHome < b.sudo_5Board_4home.size)
    (hzA : b.sudo_5Board_4home[zHome] = embed zs)
    (hD : zHome < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[zHome] = true)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (zHome : Int))
    (hbench : b.sudo_5Board_5bench = embed bench)
    (hx : xs.length = n) (hz : zs.length = n)
    (hpos : 0 < n) (hbLen : n ≤ bench.length)
    (htriX : allTritList xs) (htriZ : allTritList zs)
    (htriB : allTritList (bench.take n))
    (hzero : ∀ i, n ≤ i → ∀ hi : i < bench.length, bench[i] = 0)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hf : FitsLen n) (hfitL : FitsLen bench.length) (hfitZ : FitsLen zs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit2 : FitsLen (moves + 2 * n))
    (hfitC : FitsLen (moves + pegCount xs + pegCount zs + pegCount zs))
    (hpeg : FitsLen (2 * pegCount ((addOnto (addOnto bench xs false n) zs true n).take n)))
    (hfitM : FitsLen (moves + pegCount xs + pegCount zs + pegCount zs +
        2 * pegCount ((addOnto (addOnto bench xs false n) zs true n).take n)))
    (hfitS : FitsLen (slides + 2 * pegCount ((addOnto (addOnto bench xs false n) zs true n).take n))) :
    ∃ b',
      (do
          let b ← Ecbs.bench_add b (xHome : Int) false
          let b ← Ecbs.bench_add b (zHome : Int) true
          let b ← Ecbs.clear b (zHome : Int)
          Ecbs.settle b) = .ok b' ∧
      b'.sudo_5Board_8bench_on = false ∧
      b'.sudo_5Board_4home =
        b.sudo_5Board_4home.set ⟨zHome, hzH⟩
          (embed (fieldAdd n (fieldAdd n (bench.take n) xs) (mirrorTrits zs))) := by
  have hfit1 : FitsLen (moves + n) := FitsLen.of_le hfit2 (by omega)
  have h1 := bench_add_prefix b xHome xs bench n moves false hxH hxA hbench hx hpos hbLen
    htriX htriB hmoves hfit1
  rw [h1, ok_bind]
  let L1 := addOnto bench xs false n
  let mv1 := moves + pegCount xs
  have hlen1 : L1.length = bench.length := addOnto_length bench xs false n
  have hpx : pegCount xs ≤ n := by rw [← hx]; exact pegCount_le xs
  have hfitB : FitsLen (mv1 + n) := FitsLen.of_le hfit2 (by omega)
  have h2 := bench_add_prefix (benchAddBoard b (embed L1) mv1) zHome zs L1 n mv1 true
    (by simpa [benchAddBoard, withMoves] using hzH)
    (by simpa [benchAddBoard, withMoves] using hzA)
    rfl hz hpos (by rw [hlen1]; exact hbLen) htriZ
    (by rw [addOnto_off bench xs n hbLen]; exact fieldAdd_span_trits _ _ _)
    (benchAddBoard_moves _ _ _) hfitB
  rw [h2, ok_bind]
  let L2 := addOnto L1 zs true n
  let mv2 := mv1 + pegCount zs
  let b2 := benchAddBoard (benchAddBoard b (embed L1) mv1) (embed L2) mv2
  have hlen2 : L2.length = bench.length := by
    rw [addOnto_length, hlen1]
  have hzero2 : ∀ i, n ≤ i → ∀ hi : i < L2.length, L2[i] = 0 := by
    intro i hi hlt
    have hiB : i < bench.length := by rw [hlen2] at hlt; exact hlt
    have hL1 : L1[i]'(by rw [hlen1]; exact hiB) = bench[i] :=
      addOnto_high bench xs false n i hi hiB
    rw [addOnto_high L1 zs true n i hi (by rw [hlen1]; exact hiB), hL1]
    exact hzero i hi hiB
  have hpre : L2.take n = fieldAdd n (fieldAdd n (bench.take n) xs) (mirrorTrits zs) := by
    rw [addOnto_on L1 zs n (by rw [hlen1]; exact hbLen), addOnto_off bench xs n hbLen]
  have hcs := clear_settle_held b2 zHome zs L2 n mv2 slides peak
    (by simpa [b2, benchAddBoard, withMoves] using hzH)
    (by simpa [b2, benchAddBoard, withMoves] using hD)
    (by simpa [b2, benchAddBoard, withMoves] using h7)
    (by simpa [b2, benchAddBoard, withMoves] using hheld)
    (by simpa [b2, benchAddBoard, withMoves] using hzA)
    (by simpa [b2, benchAddBoard, withMoves] using hon)
    (by simpa [b2, benchAddBoard, withMoves] using hto)
    rfl
    (by simpa [b2, benchAddBoard, withMoves] using hn)
    (by rw [hlen2]; omega)
    (by rw [hlen2]; exact hbLen)
    hzero2 hf (by rw [hlen2]; exact hfitL) hfitZ
    (by simp [b2, benchAddBoard, withMoves, mv2, ofNat_eq_natCast])
    (by simpa [b2, benchAddBoard, withMoves, ofNat_eq_natCast] using hslides)
    (by simpa [b2, benchAddBoard, withMoves, ofNat_eq_natCast] using hpeak)
    (by simpa [mv1, mv2, Nat.add_assoc] using hfitC)
    (by simpa [hpre] using hpeg)
    (by simpa [mv1, mv2, hpre, Nat.add_assoc] using hfitM)
    (by simpa [hpre] using hfitS)
  rcases hcs with ⟨b', heq, hoff, hhome⟩
  rw [heq]
  refine ⟨b', rfl, hoff, ?_⟩
  rw [hhome, hpre]
  simp [b2, benchAddBoard, withMoves, Array.set_set]

end EcbsLink2.Link2
