/-
  `bench_white0` writes `(peg + 1) mod 3` into hole 0 of the bench and
  charges one move. On the square's bench that is `fieldAdd` with
  `whiteHole0` (SPEC.md §3 R7 line 156, the plus one). Proof-only.
  Not a security claim.
-/
import EcbsLink2.Link2.MarkerCopyEq
import EcbsLink2.SpecBase

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem modI_three (a : Nat) :
    SudoRt.modI (Int.ofNat a) (3 : Int) = .ok (Int.ofNat (a % 3)) :=
  modI_ofNat a (by decide)

/-- `bench_white0` writes `(peg + 1) mod 3` into hole 0 and charges one move. -/
theorem bench_white0_step (b : Ecbs.Board) (xs : List Nat) (moves : Nat)
    (hpos : 0 < xs.length)
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hc : xs[0] ≤ 2)
    (hfitM : FitsLen (moves + 1)) :
    Ecbs.bench_white0 b =
      .ok { { b with sudo_5Board_5bench := embed (xs.set 0 ((xs[0] + 1) % 3)) }
          with sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + 1) } } := by
  have hfit : FitsLen (xs[0] + 1) := by
    have hle : xs[0] + 1 ≤ 3 := by omega
    have h3 : FitsLen 3 := by unfold FitsLen i64MaxNat; omega
    exact FitsLen.of_le h3 hle
  unfold Ecbs.bench_white0
  rw [hbench, show (0 : Int) = Int.ofNat 0 from rfl, atL_embed xs 0 hpos, ok_bind,
    addI_ofNat_one (xs[0]) hfit, ok_bind, modI_three (xs[0] + 1), ok_bind]
  have hsz : 0 < (embed xs).size := by rw [size_embed]; exact hpos
  rw [putL_ofNat (embed xs) 0 (Int.ofNat ((xs[0] + 1) % 3)) hsz, ok_bind,
    embed_set xs 0 ((xs[0] + 1) % 3) hpos]
  conv =>
    lhs
    zeta
  rw [hmoves, ← ofNat_eq_natCast moves, addI_ofNat_one moves hfitM]
  simp only [ok_bind, pure_eq_ok]

private theorem coeff_lt (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    coeff xs i = xs[i] := by
  unfold coeff
  simp [hi]

private theorem white_coeff (n i : Nat) (hn : 0 < n) (hi : i < n) :
    coeff (whiteHole0 n) i = if i = 0 then 1 else 0 := by
  unfold coeff whiteHole0
  cases i with
  | zero => simp [hn]
  | succ j =>
    simp only [List.getD_cons_succ]
    have hlt : j < (List.replicate (n - 1) 0).length := by simp; omega
    have hv : (List.replicate (n - 1) 0)[j]'(hlt) = 0 := by simp [List.getElem_replicate]
    dsimp [List.getD]
    rw [List.get?_eq_getElem?, List.getElem?_eq_getElem hlt]
    simp [hv]

/-- Hole 0 of a length-`n` trit prefix, plus a white peg, is `fieldAdd` with
    `whiteHole0`. SPEC.md §3 R7 line 156, the plus one. -/
theorem take_set_white (xs : List Nat) (n : Nat)
    (hn : 0 < n) (hx : n ≤ xs.length) (htri : allTritList (xs.take n)) :
    ((xs.set 0 ((xs[0]'(Nat.lt_of_lt_of_le hn hx) + 1) % 3)).take n) =
      fieldAdd n (xs.take n) (whiteHole0 n) := by
  apply List.ext_getElem
  · simp [fieldAdd, whiteHole0, List.length_take]
    omega
  · intro i hi _hi'
    have hiN : i < n := by
      have hmin : i < min n xs.length := by simpa [List.length_take] using hi
      omega
    have hix : i < xs.length := Nat.lt_of_lt_of_le hiN hx
    have hlenT : i < (xs.take n).length := by simp [List.length_take]; omega
    have hxI : xs[i]'(hix) ≤ 2 := by
      simpa [List.getElem_take] using htri _ (List.getElem_mem hlenT)
    rw [List.getElem_take, List.getElem_set]
    by_cases hzero : i = 0
    · subst hzero
      simp [fieldAdd, tritAdd, coeff_lt (xs.take n) 0 (by simp [List.length_take]; omega),
        List.getElem_take, white_coeff n 0 hn hn, if_pos rfl]
    · have hne : ¬ 0 = i := fun h => hzero h.symm
      have hlt3 : xs[i]'(hix) < 3 := by omega
      simp [hzero, hne, fieldAdd, tritAdd, coeff_lt (xs.take n) i hlenT, List.getElem_take,
        white_coeff n i hn hiN, if_neg hne, Nat.mod_eq_of_lt hlt3]

/-- The square, then the white peg in hole 0. The length-`n` prefix is
    `fieldAdd` of the squared slope with `whiteHole0`. SPEC.md §3 R7 line 156. -/
theorem chord_square_white (b : Ecbs.Board) (slope : List Nat)
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
    ∃ b',
      (do
        let b ← Ecbs.mul b Ecbs.bottom Ecbs.gap Ecbs.gap true false false
        Ecbs.bench_white0 b) = .ok b' ∧
      b'.sudo_5Board_9marker_on = true ∧
      ((laneFold n (n - k) (school n slope slope (List.replicate bench 0) false)).set 0
          ((coeff (laneFold n (n - k) (school n slope slope (List.replicate bench 0) false)) 0 + 1) % 3)).take n =
        fieldAdd n (fieldMul n k bench slope slope) (whiteHole0 n) ∧
      b'.sudo_5Board_5bench =
        embed ((laneFold n (n - k) (school n slope slope (List.replicate bench 0) false)).set 0
          ((coeff (laneFold n (n - k) (school n slope slope (List.replicate bench 0) false)) 0 + 1) % 3)) := by
  rcases chord_square b slope w h r n k moves hole bench peak peakS cOps m ctrl mx script
      hmk hoff hm hc hx hscript hbound hfitM hfitCtrl hfit2 hops hop0 hfops hbl h5 h5h h5t h5a
      h6 h6h h6e h7 hn0 hn hlen hf hmoves hpeak hpeakS hspan htri hfi hfm hfitP hhole hw0 hh0
      hrR hrP hnE hkLe hgap hw hh hr hk hsm hnsm hfitB hfold with
    ⟨b0, hb, hmk0, _, _, hbench, htake, _, hmv, _, _, _⟩
  let sch := school n slope slope (List.replicate bench 0) false
  let folded := laneFold n (n - k) sch
  have hlenS : sch.length = bench := by
    simpa [sch, List.length_replicate] using
      school_length slope slope (List.replicate bench 0) false n
  have hnB : n ≤ bench := by omega
  have hlenF : folded.length = bench := by
    rw [show folded.length = sch.length from laneFold_length n (n - k) sch (by rw [hlenS]; exact hnB),
      hlenS]
  have hpos : 0 < folded.length := by rw [hlenF]; omega
  have htakeL : folded.take n = fieldMul n k bench slope slope := by
    simpa [folded, sch] using htake
  have hlenM : (fieldMul n k bench slope slope).length = n := by
    rw [← htakeL, List.length_take, hlenF]; omega
  have htriF : allTritList (fieldMul n k bench slope slope) :=
    fieldMul_span_trits n k bench slope slope hspan hnB
  have hhead : folded[0]'(hpos) ≤ 2 := by
    have hm0 : 0 < (fieldMul n k bench slope slope).length := by rw [hlenM]; exact hn0
    have hmem : (fieldMul n k bench slope slope)[0]'(hm0) ∈ fieldMul n k bench slope slope :=
      List.getElem_mem hm0
    have hc0 : (fieldMul n k bench slope slope)[0]'(hm0) ≤ 2 := htriF _ hmem
    have hget : folded[0]'(hpos) = (fieldMul n k bench slope slope)[0]'(hm0) := by
      have ht0 : (folded.take n)[0]'(by rw [List.length_take, hlenF]; omega) = folded[0]'(hpos) := by
        simp [List.getElem_take]
      simpa [htakeL] using ht0.symm
    rw [hget]
    exact hc0
  have hstep := bench_white0_step b0 folded (mulMoves moves slope slope n k bench) hpos
    (by simpa [folded] using hbench)
    (by simpa [ofNat_eq_natCast] using hmv) hhead hfitW
  have hpre := take_set_white folded n hn0 (by rw [hlenF]; exact hnB)
    (by simpa [htakeL] using htriF)
  have hcEq : coeff folded 0 = folded[0]'(hpos) := coeff_lt folded 0 hpos
  rw [hb, ok_bind, hstep]
  refine ⟨_, rfl, by simp [hmk0], ?_, ?_⟩
  · simpa [folded, hcEq, htakeL] using hpre
  · simp [folded, hcEq]

end EcbsLink2.Link2
