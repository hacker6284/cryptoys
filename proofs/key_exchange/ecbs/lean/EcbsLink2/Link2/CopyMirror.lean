/-
  `copy_band` with `mirror = true`: flip every coefficient of the source,
  then write that array into an empty home. The flip is indexed by the
  coefficient, and after `i` steps the array is `mirrorPrefix`. At the end it
  is `mirrorTrits`, which is what a fresh red cell copies into up.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Mirror
import EcbsLink2.Link2.WalkCopy

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem embed_put (xs : List Nat) (j v : Nat) (hj : j < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat j) (Int.ofNat v) = .ok (embed (xs.set j v)) := by
  have hsz : j < (embed xs).size := by rw [size_embed]; exact hj
  rw [putL_ofNat (embed xs) j (Int.ofNat v) hsz]
  apply congrArg Except.ok
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro k hk hk'
    simp [embed, Array.getElem_set, List.getElem_set]

/-- `do let x ← m; Except.ok x` is `m`. The flip loop's trailing `pure` has
    already been reduced to `Except.ok`. -/
private theorem bind_ok {ε α} (m : Except ε α) :
    (do let x ← m; Except.ok x) = m := by
  cases m <;> rfl

private theorem pegCount_embed (xs : List Nat) :
    nnz (embed xs).toList = pegCount xs := by
  rw [toList_embed, nnz_embed]
  rfl

private theorem addI_cast_ofNat (a b : Nat) (h : FitsLen (a + b)) :
    SudoRt.addI (a : Int) (Int.ofNat b) = .ok (Int.ofNat (a + b)) := by
  rw [ofNat_eq_natCast b]
  exact addI_cast a b h

private theorem decide_gt_ofNat (a b : Nat) :
    decide (Int.ofNat a > (b : Int)) = decide (b < a) := by
  rw [decide_eq_decide, show (b : Int) = Int.ofNat b from ofNat_eq_natCast b]
  exact ofNat_lt_iff b a

theorem flipTrit_zero_iff (c : Nat) (hc : c ≤ 2) : flipTrit c = 0 ↔ c = 0 := by
  unfold flipTrit
  by_cases h : c = 0
  · simp [h]
  · simp [h]
    omega

theorem pegCount_mirror (xs : List Nat) (h : allTritList xs) :
    pegCount (mirrorTrits xs) = pegCount xs := by
  rw [mirrorTrits_flip]
  induction xs with
  | nil => rfl
  | cons c xs ih =>
    have hc : c ≤ 2 := h c (List.mem_cons_self c xs)
    have hxs : allTritList xs := fun z hz => h z (List.mem_cons_of_mem c hz)
    have ih' := ih hxs
    unfold pegCount at ih' ⊢
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    by_cases hz : c = 0
    · subst hz
      have hf : flipTrit 0 = 0 := by unfold flipTrit; rfl
      have hz0 : decide ((0 : Nat) ≠ 0) = false := by decide
      simp only [hf, hz0, Bool.false_eq_true, ite_false, ih']
    · have hf : flipTrit c ≠ 0 := fun e => hz ((flipTrit_zero_iff c hc).1 e)
      have hz1 : decide (c ≠ 0) = true := decide_eq_true hz
      have hf1 : decide (flipTrit c ≠ 0) = true := decide_eq_true hf
      simp only [hz1, hf1, ite_true, List.length_cons, ih']

/-- The inlined flip inside `copy_band`. Every coefficient is flipped, zeros
    included (`flip 0 = 0`). The board is not touched. -/
def bandFlipStep (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) Ecbs.Board) :=
  let i := σ.1
  let s := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, s))
    else
      match ← (do
        let c ← SudoRt.atL s i
        let f ← Ecbs.flip c
        let s ← SudoRt.putL s i f
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) s)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs))

private theorem bandFlipStep_hit (xs : List Nat) (i n : Nat)
    (hi : i < xs.length) (hto : i ≤ n - 1)
    (hc : xs[i] ≤ 2) (hfi : FitsLen (i + 1)) :
    bandFlipStep (Int.ofNat (n - 1))
        (Int.ofNat i, embed (mirrorPrefix xs i)) =
      (if i = n - 1 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embed (mirrorPrefix xs (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed (mirrorPrefix xs (i + 1))))) := by
  unfold bandFlipStep
  dsimp only
  split
  · next hgt => exact absurd hgt (not_gt_cast hto)
  · have hpref : i < (mirrorPrefix xs i).length := by
      rw [mirrorPrefix_length xs i (Nat.le_of_lt hi)]; exact hi
    rw [atL_embed (mirrorPrefix xs i) i hpref, mirrorPrefix_cell xs i hi, ok_bind,
      flip_refines _ hc, ok_bind]
    have hset : i < (mirrorPrefix xs i).length := hpref
    rw [embed_put (mirrorPrefix xs i) i (flipTrit xs[i]) hset, ok_bind]
    rw [show (mirrorPrefix xs i).set i (flipTrit xs[i]) = mirrorPrefix xs (i + 1) from
      (mirrorPrefix_succ xs i hi).symm]
    exact asc_tail (n - 1) i hfi _

/-- `mirror = true`: the destination receives `mirrorTrits` of the source.
    Moves grow by the nonzero count, which flipping does not change. -/
theorem copy_band_mirror_refines (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (moves peak : Nat)
    (hHd : dst < b.sudo_5Board_4home.size)
    (hDd : dst < b.sudo_5Board_4held.size)
    (hHs : src < b.sudo_5Board_4home.size)
    (hDs : src < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hsrc : b.sudo_5Board_4held[src] = true)
    (harr : b.sudo_5Board_4home[src] = embed xs)
    (hempty : b.sudo_5Board_4held[dst] = false)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (xs.length : Int))
    (hpos : 0 < xs.length)
    (htri : allTritList xs)
    (hf : FitsLen xs.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + pegCount xs)) :
    Ecbs.copy_band b (dst : Int) (src : Int) true =
      .ok (placeBoard b dst hHd hDd (mirrorTrits xs) moves peak) := by
  have hpeg : pegCount (mirrorTrits xs) = pegCount xs := pegCount_mirror xs htri
  have hfitY : FitsLen (moves + pegCount (mirrorTrits xs)) := by rw [hpeg]; exact hfit
  have hlenY : (mirrorTrits xs).length = xs.length := by
    rw [mirrorTrits_flip, List.length_map]
  unfold Ecbs.copy_band Ecbs.need_empty
  simp only [if_true]
  have hv := value_held_refines b src xs xs.length hDs hHs hsrc harr hn (Nat.le_refl _) hf
  rw [hv, ok_bind, List.take_length]
  rw [show (dst : Int) = Int.ofNat dst from ofNat_eq_natCast dst, atL_ofNat _ dst hDd, hempty]
  simp only [Bool.not_false, sudoAssert_true, ok_bind, pure_eq_ok]
  rw [listLen_embed, subI_ofNat_one xs.length hpos hf, ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, fuelRange_eq]
  conv =>
    zeta
    pattern (fun σ : Int × Array Int => _)
    change bandFlipStep (Int.ofNat (xs.length - 1))
  rw [bind_ok]
  rw [show embed xs = embed (mirrorPrefix xs 0) from by rw [mirrorPrefix_zero]]
  refine asc_goal (fromN := 0) (toN := xs.length - 1)
      (fun i (s : Array Int) => s = embed (mirrorPrefix xs i))
      (Nat.zero_le _) (by simp [mirrorPrefix_zero]) ?_ ?_
  · intro i s _ hi hs
    have hii : i < xs.length := by omega
    have hc : xs[i] ≤ 2 := trit_get htri hii
    have hfi : FitsLen (i + 1) := FitsLen.succ_le hii hf
    refine ⟨embed (mirrorPrefix xs (i + 1)), ?_, ?_⟩
    · rfl
    · rw [hs]
      exact bandFlipStep_hit xs i xs.length hii (by omega) hc hfi
  · intro s hs
    have hlast : xs.length - 1 + 1 = xs.length := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
    rw [hlast] at hs
    have hpre : mirrorPrefix xs xs.length = mirrorTrits xs := mirrorPrefix_all xs
    have hs' : s = embed (mirrorTrits xs) := by rw [hs, hpre]
    rw [hs']
    unfold Ecbs.note_peak placeBoard
    dsimp only
    rw [putL_ofNat _ dst (embed (mirrorTrits xs)) hHd, ok_bind,
      putL_ofNat _ dst true hDd, ok_bind]
    have hfs : FitsLen (embed (mirrorTrits xs)).size := by rw [size_embed, hlenY]; exact hf
    rw [npeg_refines (embed (mirrorTrits xs)) hfs, pegCount_embed, ok_bind]
    have hmI : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := hmoves
    rw [hmI, addI_cast_ofNat _ _ hfitY, ok_bind]
    have h7' : 7 ≤ (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true).size := by
      rw [Array.size_set]; exact h7
    have hocc := occupied_refines
      ({ b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨dst, hHd⟩ (embed (mirrorTrits xs))
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨dst, hDd⟩ true
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + pegCount (mirrorTrits xs)) } }) h7'
    rw [hocc, ok_bind, hpeak, decide_gt_ofNat]
    by_cases hlt : peak < countHeld (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true) 7
    · have hcI : decide (peak < countHeld (b.sudo_5Board_4held.set ⟨dst, hDd⟩ true) 7) = true := by
        rw [decide_eq_true_eq]; exact hlt
      rw [hcI, if_pos rfl, bind_ok, pure_eq_ok]
      simp only [hlt, ite_true]
    · simp only [decide_False, Bool.false_eq_true, if_false, bind_ok, pure_eq_ok, hlt]

/-- Red first cell: across receives the base across, up receives the negated base up. -/
theorem walk_copy_red (b : Ecbs.Board) (x y : List Nat) (n moves peak : Nat)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (hx : x.length = n) (hy : y.length = n) (hpos : 0 < n)
    (hyt : allTritList y) (hf : FitsLen n)
    (hfitx : FitsLen (moves + pegCount x))
    (hfity : FitsLen (moves + pegCount x + pegCount y))
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (h0 : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = false)
    (h1 : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = false)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed x)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed y) :
    ∃ b2 mv2 pk2,
      (do
          let b ← Ecbs.copy_band b Ecbs.across Ecbs.base_across false
          Ecbs.copy_band b Ecbs.up Ecbs.base_up true) = .ok b2 ∧
      (∀ (h : 0 < b2.sudo_5Board_4home.size), b2.sudo_5Board_4home[0] = embed x) ∧
      (∀ (h : 1 < b2.sudo_5Board_4home.size),
        b2.sudo_5Board_4home[1] = embed (mirrorTrits y)) ∧
      mv2 = moves + pegCount x + pegCount (mirrorTrits y) ∧
      b2.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv2 ∧
      b2.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk2 ∧
      b2.sudo_5Board_6marker = b.sudo_5Board_6marker := by
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h3H : 3 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h3D : 3 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h4H : 4 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h4D : 4 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hszD]; decide
  have hnx : b.sudo_5Board_1t.sudo_4Tier_1n = (x.length : Int) := by rw [hn, hx]
  have hypos : 0 < y.length := by rw [hy]; exact hpos
  have hny0 : b.sudo_5Board_1t.sudo_4Tier_1n = (y.length : Int) := by rw [hn, hy]
  have hcopy1 := copy_band_refines b 0 3 x moves peak
    h0H h0D h3H h3D h7 h3t h3a h0 hnx (by simpa [hx] using hf)
    hmoves (by rw [hpeak]) hfitx
  let b1 := placeBoard b 0 h0H h0D x moves peak
  have hszH1 : b1.sudo_5Board_4home.size = 8 := by
    rw [place_home_eq, Array.size_set, hszH]
  have hszD1 : b1.sudo_5Board_4held.size = 8 := by
    rw [place_held_eq, Array.size_set, hszD]
  have h1D1 : 1 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h1H1 : 1 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h4D1 : 4 < b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have h4H1 : 4 < b1.sudo_5Board_4home.size := by rw [hszH1]; decide
  have h7_1 : 7 ≤ b1.sudo_5Board_4held.size := by rw [hszD1]; decide
  have hempty1 : b1.sudo_5Board_4held[1] = false := by
    have hget := get_eq_of_array (place_held_eq b 0 h0H h0D x moves peak) 1 h1D1
    have hne : (0 : Nat) ≠ 1 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans h1
  have h4t1 : b1.sudo_5Board_4held[4] = true := by
    have hget := get_eq_of_array (place_held_eq b 0 h0H h0D x moves peak) 4 h4D1
    have hne : (0 : Nat) ≠ 4 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans h4t
  have h4a1 : b1.sudo_5Board_4home[4] = embed y := by
    have hget := get_eq_of_array (place_home_eq b 0 h0H h0D x moves peak) 4 h4H1
    have hne : (0 : Nat) ≠ 4 := by decide
    simp only [Array.getElem_set, hne] at hget
    exact hget.trans h4a
  let mv1 := moves + pegCount x
  let pk1 := if peak < countHeld (b.sudo_5Board_4held.set ⟨0, h0D⟩ true) 7
    then countHeld (b.sudo_5Board_4held.set ⟨0, h0D⟩ true) 7 else peak
  have hmv1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves = (mv1 : Int) := by
    rw [place_moves_eq]; exact ofNat_eq_natCast _
  have hpk1 : b1.sudo_5Board_4cost.sudo_5Costs_4peak = (pk1 : Int) := by
    rw [place_peak_nat b 0 h0H h0D x moves peak (by rw [hpeak])]
    exact ofNat_eq_natCast _
  have ht1 : b1.sudo_5Board_1t = b.sudo_5Board_1t := place_tier_eq b 0 h0H h0D x moves peak
  have hny : b1.sudo_5Board_1t.sudo_4Tier_1n = (y.length : Int) := by rw [ht1, hny0]
  have hpegY : pegCount (mirrorTrits y) = pegCount y := pegCount_mirror y hyt
  have hfit2 : FitsLen (mv1 + pegCount y) := by simpa [mv1] using hfity
  have hcopy2 := copy_band_mirror_refines b1 1 4 y mv1 pk1
    h1H1 h1D1 h4H1 h4D1 h7_1 h4t1 h4a1 hempty1 hny hypos hyt
    (by simpa [hy] using hf) hmv1 hpk1 hfit2
  let b2 := placeBoard b1 1 h1H1 h1D1 (mirrorTrits y) mv1 pk1
  refine ⟨b2, mv1 + pegCount (mirrorTrits y),
      if pk1 < countHeld (b1.sudo_5Board_4held.set ⟨1, h1D1⟩ true) 7
        then countHeld (b1.sudo_5Board_4held.set ⟨1, h1D1⟩ true) 7 else pk1,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show Ecbs.across = ((0 : Nat) : Int) from rfl,
        show Ecbs.base_across = ((3 : Nat) : Int) from rfl,
        show Ecbs.up = ((1 : Nat) : Int) from rfl,
        show Ecbs.base_up = ((4 : Nat) : Int) from rfl, hcopy1, ok_bind]
    simpa [b1, b2] using hcopy2
  · intro h0
    have hget := get_eq_of_array
      (place_home_eq b1 1 h1H1 h1D1 (mirrorTrits y) mv1 pk1) 0 h0
    have hne : (1 : Nat) ≠ 0 := by decide
    simp only [Array.getElem_set, hne] at hget
    have hsrc := get_eq_of_array (place_home_eq b 0 h0H h0D x moves peak) 0
      (by rw [hszH1]; decide)
    simp only [Array.getElem_set] at hsrc
    exact hget.trans hsrc
  · intro h1
    have hget := get_eq_of_array
      (place_home_eq b1 1 h1H1 h1D1 (mirrorTrits y) mv1 pk1) 1 h1
    simp only [Array.getElem_set] at hget
    exact hget
  · rw [hpegY]
  · rw [place_moves_eq, hpegY]
  · rw [place_peak_nat b1 1 h1H1 h1D1 (mirrorTrits y) mv1 pk1 (by rw [hpk1])]
  · rw [place_marker_eq b1 1 h1H1 h1D1 (mirrorTrits y) mv1 pk1,
      place_marker_eq b 0 h0H h0D x moves peak]

end EcbsLink2.Link2
