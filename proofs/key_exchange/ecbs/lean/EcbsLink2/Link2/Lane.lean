/-
  The lane-fold accumulation: highest-hole scan, then one descending loop that clears
  a peg and adds it at both images. Both `max_bench_hole` branches of `Ecbs.lane_fold`
  are this loop. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Fold
import EcbsLink2.Link2.School

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-! ### Model: high-first fold, same as `Spec.laneFold` -/

def foldDown (n gap : Nat) (strip : List Nat) : Nat → List Nat
  | 0 => strip
  | k + 1 => foldHigh n gap (strip.length - 1 - k) (foldDown n gap strip k)

def foldMoves (n gap : Nat) (strip : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let prev := foldDown n gap strip k
    let e := strip.length - 1 - k
    let c := coeff prev e
    foldMoves n gap strip k + if c = 0 ∨ e < n then 0 else 3

private theorem foldDown_succ (n gap : Nat) (strip : List Nat) (k : Nat) :
    foldDown n gap strip (k + 1) =
      foldHigh n gap (strip.length - 1 - k) (foldDown n gap strip k) :=
  rfl

private theorem foldMoves_succ (n gap : Nat) (strip : List Nat) (k : Nat) :
    foldMoves n gap strip (k + 1) =
      foldMoves n gap strip k +
        if coeff (foldDown n gap strip k) (strip.length - 1 - k) = 0 ∨
            strip.length - 1 - k < n then 0 else 3 :=
  rfl

private theorem range_succ_cons : ∀ k, List.range (k + 1) = 0 :: (List.range k).map Nat.succ
  | 0 => by simp [List.range_succ, List.range_zero]
  | k + 1 => by
    conv => lhs; rw [List.range_succ (k + 1), range_succ_cons k]
    conv => rhs; rw [List.range_succ k]
    simp [List.map_append, List.cons_append]

private theorem foldDown_high (n gap : Nat) (strip : List Nat) (k : Nat) (hk : k ≤ strip.length) :
    foldDown n gap strip k =
      ((List.range k).map (fun d => strip.length - k + d)).foldr
        (fun e st => foldHigh n gap e st) strip := by
  induction k with
  | zero => simp [foldDown, List.range_zero]
  | succ k ih =>
    have hk' : k ≤ strip.length := Nat.le_of_succ_le hk
    rw [foldDown_succ, ih hk', range_succ_cons]
    simp only [List.map_cons, Nat.add_zero, List.foldr_cons, List.map_map]
    have hidx : strip.length - 1 - k = strip.length - (k + 1) := by omega
    rw [hidx]
    have hmap : (List.range k).map (fun d => strip.length - k + d) =
        (List.range k).map ((fun d => strip.length - (k + 1) + d) ∘ Nat.succ) := by
      apply List.map_congr_left
      intro d _
      show strip.length - k + d = strip.length - (k + 1) + (d + 1)
      omega
    rw [hmap]

private theorem foldr_map {α β γ : Type} (f : α → β) (g : β → γ → γ) (init : γ) (xs : List α) :
    (xs.map f).foldr g init = xs.foldr (fun a acc => g (f a) acc) init := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih]

theorem foldDown_lane (n gap : Nat) (strip : List Nat) (hn : n ≤ strip.length) :
    foldDown n gap strip (strip.length - n) = laneFold n gap strip := by
  rw [foldDown_high _ _ _ _ (Nat.sub_le _ _)]
  have hbase : strip.length - (strip.length - n) = n := by omega
  have hmap : (List.range (strip.length - n)).map (fun d => strip.length - (strip.length - n) + d) =
      (List.range (strip.length - n)).map (fun d => n + d) := by
    apply List.map_congr_left
    intro d _
    rw [hbase]
  rw [hmap, foldr_map]
  unfold laneFold reduceStrip
  rfl

private theorem foldHigh_length (n gap e : Nat) (strip : List Nat) :
    (foldHigh n gap e strip).length = strip.length := by
  unfold foldHigh
  by_cases hz : coeff strip e = 0
  · simp [hz]
  · by_cases hlt : e < n
    · simp [hz, hlt]
    · simp [hz, hlt, List.length_set]

private theorem foldDown_length (n gap : Nat) (strip : List Nat) :
    ∀ k, (foldDown n gap strip k).length = strip.length
  | 0 => rfl
  | k + 1 => by rw [foldDown_succ, foldHigh_length, foldDown_length n gap strip k]

private theorem foldMoves_le (n gap : Nat) (strip : List Nat) (k : Nat) :
    foldMoves n gap strip k ≤ 3 * k := by
  induction k with
  | zero => simp [foldMoves]
  | succ k ih =>
    rw [foldMoves_succ]
    have hstep : (if coeff (foldDown n gap strip k) (strip.length - 1 - k) = 0 ∨
        strip.length - 1 - k < n then 0 else 3) ≤ 3 := by
      by_cases h0 : coeff (foldDown n gap strip k) (strip.length - 1 - k) = 0 ∨
          strip.length - 1 - k < n
      · simp [h0]
      · simp [h0]
    have := Nat.add_le_add ih hstep
    omega

/-! ### One descending step: clear, both images, three moves -/

private theorem embed_put (xs : List Nat) (j v : Nat) (hj : j < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat j) (Int.ofNat v) = .ok (embed (xs.set j v)) := by
  have hsz : j < (embed xs).size := by rw [size_embed]; exact hj
  rw [putL_ofNat (embed xs) j (Int.ofNat v) hsz]
  apply congrArg Except.ok
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro i hi hi'
    simp [embed, Array.getElem_set, List.getElem_set]

private theorem embed_put_zero (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat j) (0 : Int) = .ok (embed (xs.set j 0)) := by
  rw [show (0 : Int) = Int.ofNat 0 from rfl]
  exact embed_put xs j 0 hj

private theorem coeff_get (xs : List Nat) (j : Nat) (hj : j < xs.length) : coeff xs j = xs[j] := by
  unfold coeff
  simp [hj]

private theorem modI_three (a : Nat) :
    SudoRt.modI (Int.ofNat a) (3 : Int) = .ok (Int.ofNat (a % 3)) :=
  modI_ofNat a (by decide)

private theorem addI_two (m : Nat) (h : FitsLen (m + 2)) :
    SudoRt.addI (Int.ofNat m) (2 : Int) = .ok (Int.ofNat (m + 2)) := by
  rw [show (2 : Int) = Int.ofNat 2 from rfl, addI_ofNat m 2 h]

private theorem fits_le (n : Nat) (h : n ≤ 10000000) : FitsLen n := by
  unfold FitsLen i64MaxNat
  omega

private theorem withMoves_moves (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_5moves = m := by
  unfold withMoves
  rfl

private theorem withMoves_withMoves (b : Ecbs.Board) (m₁ m₂ : Int) :
    withMoves (withMoves b m₁) m₂ = withMoves b m₂ := by
  unfold withMoves
  rfl

private theorem tritAdd_le (a b : Nat) : tritAdd a b ≤ 2 := by
  unfold tritAdd
  have : (a + b) % 3 < 3 := Nat.mod_lt _ (by decide)
  omega

private theorem trit_set {xs : List Nat} (hs : allTritList xs) {i v : Nat}
    (hi : i < xs.length) (hv : v ≤ 2) : allTritList (xs.set i v) := by
  intro x hx
  rw [List.mem_iff_getElem] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have hlen : (xs.set i v).length = xs.length := by rw [List.length_set]
  have hj' : j < xs.length := by rw [← hlen]; exact hj
  rw [List.getElem_set]
  by_cases hij : i = j
  · simp [hij, hv]
  · simp [hij]
    exact hs _ (List.getElem_mem hj')

private theorem foldHigh_trits {strip : List Nat} (hs : allTritList strip) (n gap e : Nat)
    (he : e < strip.length) (hn : n ≤ e) (hg : gap ≤ e) :
    allTritList (foldHigh n gap e strip) := by
  unfold foldHigh
  by_cases hz : coeff strip e = 0
  · simp [hz, hs]
  · have hlt : ¬ e < n := by omega
    simp only [hz, hlt, ite_false]
    have hc : coeff strip e ≤ 2 := by
      rw [coeff_get _ _ he]; exact hs _ (List.getElem_mem he)
    have hlen1 : (strip.set e 0).length = strip.length := by rw [List.length_set]
    have hd1 : e - n < (strip.set e 0).length := by rw [hlen1]; omega
    have cleared := trit_set hs he (by decide : (0 : Nat) ≤ 2)
    have onceT := trit_set cleared hd1
      (tritAdd_le (coeff (strip.set e 0) (e - n)) (coeff strip e))
    have hlen2 : ((strip.set e 0).set (e - n) (tritAdd (coeff (strip.set e 0) (e - n)) (coeff strip e))).length =
        strip.length := by rw [List.length_set, hlen1]
    have hd2 : e - gap < ((strip.set e 0).set (e - n)
        (tritAdd (coeff (strip.set e 0) (e - n)) (coeff strip e))).length := by
      rw [hlen2]; omega
    exact trit_set onceT hd2 (tritAdd_le _ (coeff strip e))

private theorem lay_image (xs : List Nat) (j c : Nat) (hj : j < xs.length)
    (hc : c ≤ 2) (hcell : coeff xs j ≤ 2) :
    (do
        let cur ← SudoRt.atL (embed xs) (Int.ofNat j)
        let sum ← SudoRt.addI cur (Int.ofNat c)
        let r ← SudoRt.modI sum (3 : Int)
        SudoRt.putL (embed xs) (Int.ofNat j) r) =
      .ok (embed (xs.set j (tritAdd (coeff xs j) c))) := by
  have hcf : coeff xs j = xs[j] := coeff_get xs j hj
  rw [atL_embed xs j hj, ok_bind, hcf,
    addI_ofNat _ _ (fits_small (by rw [hcf] at hcell; omega)), ok_bind, modI_three, ok_bind,
    embed_put xs j _ hj]
  simp [tritAdd, hcf]

private theorem foldHigh_zero (n gap e : Nat) (strip : List Nat) (hz : coeff strip e = 0) :
    foldHigh n gap e strip = strip := by
  unfold foldHigh
  simp [hz]

private theorem foldDown_at (n gap : Nat) (strip : List Nat) (i : Nat) (hi : i < strip.length) :
    foldDown n gap strip (strip.length - i) =
      foldHigh n gap i (foldDown n gap strip (strip.length - (i + 1))) := by
  have hk : strip.length - (i + 1) + 1 = strip.length - i := by omega
  have hidx : strip.length - 1 - (strip.length - (i + 1)) = i := by omega
  rw [← hk, foldDown_succ, hidx]

/-- One hole of the descending fold. The `d1`/`d2` block is `foldGeom`; the asserts
    and the two image adds are the emitted tail, including the subs inside the
    `d1 = e − n` branch. -/
def foldPeg (w h r n k : Nat) (strip : Array Int) (e : Nat) (b : Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int)) :=
  do
    let _t443 ← SudoRt.atL strip (Int.ofNat e)
    let c := _t443
    if !(SudoRt.SEq.beq c (0 : Int)) then
      do
        let _ix445 := Int.ofNat e
        let _t446 ← SudoRt.putL strip _ix445 (0 : Int)
        let strip := _t446
        let _t447 ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int)
        let b := withMoves b _t447
        let geom ← foldGeom w h r e
        let d1 := geom.1
        let d2 := geom.2
        let _t461 ← SudoRt.subI (Int.ofNat e) (Int.ofNat n)
        let _t463 ← (if (SudoRt.SEq.beq d1 _t461) then (do
          let _t464 ← SudoRt.subI (Int.ofNat n) (Int.ofNat k)
          let _t465 ← SudoRt.subI (Int.ofNat e) _t464
          pure (SudoRt.SEq.beq d2 _t465)) else pure false)
        let _u ← SudoRt.sudoAssert _t463 530
        let _t469 ← (if (decide (d1 ≥ (0 : Int))) then (do
          pure (decide (d1 < Int.ofNat e))) else pure false)
        let _t471 ← (if _t469 then (do
          pure (decide (d2 ≥ (0 : Int)))) else pure false)
        let _t473 ← (if _t471 then (do
          pure (decide (d2 < Int.ofNat e))) else pure false)
        let _v ← SudoRt.sudoAssert _t473 531
        let _ix476 := d1
        let _t477 ← SudoRt.atL strip d1
        let _t478 ← SudoRt.addI _t477 c
        let _t479 ← SudoRt.modI _t478 (3 : Int)
        let _t480 ← SudoRt.putL strip _ix476 _t479
        let strip := _t480
        let _ix481 := d2
        let _t482 ← SudoRt.atL strip d2
        let _t483 ← SudoRt.addI _t482 c
        let _t484 ← SudoRt.modI _t483 (3 : Int)
        let _t485 ← SudoRt.putL strip _ix481 _t484
        let strip := _t485
        let _t486 ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (2 : Int)
        let b := withMoves b _t486
        pure (SudoRt.Flow.cont (strip, b))
    else
      pure (SudoRt.Flow.cont (strip, b))

private theorem foldPeg_zero (xs : List Nat) (w h r n k e : Nat) (b : Ecbs.Board)
    (he : e < xs.length) (hz : xs[e] = 0) :
    foldPeg w h r n k (embed xs) e b = .ok (.cont (embed xs, b)) := by
  unfold foldPeg
  rw [atL_embed xs e he, ok_bind]
  dsimp only
  rw [sEq_ofNat_zero, hz]
  simp only [decide_True, Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok]

private theorem foldPeg_nz (xs : List Nat) (w h r n k e m : Nat) (b : Ecbs.Board)
    (hw : 0 < w) (hh : 0 < h) (hr : r < h) (hr0 : 0 < r)
    (hn : n = w * h - 1) (hk : k ≤ n) (hgap : n - k = w * r)
    (he : e < xs.length) (hen : n ≤ e) (hz : xs[e] ≠ 0) (hs : allTritList xs)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat m)
    (hf1 : FitsLen (m + 1)) (hf3 : FitsLen (m + 3))
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ e ≤ 1000000)
    (hnsm : n ≤ 1000000) :
    foldPeg w h r n k (embed xs) e b =
      .ok (.cont (embed (foldHigh n (n - k) e xs), withMoves b (Int.ofNat (m + 3)))) := by
  have hposg : 0 < n - k := by
    rw [hgap]
    exact Nat.mul_pos hw hr0
  have hnpos : 0 < n := by omega
  have hgle : n - k ≤ e := by omega
  have hc2 : xs[e] ≤ 2 := hs _ (List.getElem_mem he)
  unfold foldPeg
  rw [atL_embed xs e he, ok_bind]
  dsimp only
  rw [sEq_ofNat_zero]
  simp only [hz, decide_False, Bool.not_false, if_true, ok_bind]
  rw [embed_put_zero xs e he, ok_bind, hm, addI_ofNat_one m hf1, ok_bind,
    foldGeom_dest w h r k e hw hh hr (by rw [← hn]; exact hgap) (by rw [← hn]; exact hen) hsm,
    ok_bind, subI_ofNat e n (fits_small hsm.2.2.2) hen, ok_bind]
  rw [← hn]
  have hb1 : SudoRt.SEq.beq (Int.ofNat (e - n)) (Int.ofNat (e - n)) = true := by
    rw [sEq_ofNat]; simp
  simp only [hb1, if_pos rfl]
  rw [subI_ofNat n k (fits_small hnsm) hk, ok_bind,
    subI_ofNat e (n - k) (fits_small hsm.2.2.2) hgle, ok_bind]
  have hb2 : SudoRt.SEq.beq (Int.ofNat (e - (n - k))) (Int.ofNat (e - (n - k))) = true := by
    rw [sEq_ofNat]; simp
  simp only [hb2, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  have hlt1 : e - n < e := by omega
  have hlt2 : e - (n - k) < e := Nat.sub_lt (Nat.lt_of_lt_of_le hnpos hen) hposg
  have hdlt1 : decide (Int.ofNat (e - n) < Int.ofNat e) = true :=
    decide_eq_true ((ofNat_lt_iff _ _).mpr hlt1)
  have hdlt2 : decide (Int.ofNat (e - (n - k)) < Int.ofNat e) = true :=
    decide_eq_true ((ofNat_lt_iff _ _).mpr hlt2)
  have hge1 : decide (Int.ofNat (e - n) ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]; exact Int.ofNat_nonneg _
  have hge2 : decide (Int.ofNat (e - (n - k)) ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]; exact Int.ofNat_nonneg _
  simp only [hge1, hdlt1, hge2, hdlt2, if_pos rfl, pure_eq_ok, ok_bind, sudoAssert_true, if_true]
  have hcleared : allTritList (xs.set e 0) := trit_set hs he (by decide : (0 : Nat) ≤ 2)
  have hd1 : e - n < (xs.set e 0).length := by rw [List.length_set]; omega
  have hcell1 : coeff (xs.set e 0) (e - n) ≤ 2 := by
    rw [coeff_get _ _ hd1]; exact hcleared _ (List.getElem_mem hd1)
  have hsum1 : (xs.set e 0)[e - n] + xs[e] ≤ 1000000 := by
    have := hcell1
    rw [coeff_get _ _ hd1] at this
    omega
  rw [atL_embed (xs.set e 0) (e - n) hd1, ok_bind,
    addI_ofNat _ _ (fits_small hsum1), ok_bind, modI_three, ok_bind,
    embed_put (xs.set e 0) (e - n) _ hd1, ok_bind]
  rw [show ((xs.set e 0)[e - n] + xs[e]) % 3 =
      tritAdd (coeff (xs.set e 0) (e - n)) xs[e] from by
    rw [coeff_get (xs.set e 0) (e - n) hd1, tritAdd]]
  have once := trit_set hcleared hd1 (tritAdd_le (coeff (xs.set e 0) (e - n)) xs[e])
  have hlen2 : ((xs.set e 0).set (e - n) (tritAdd (coeff (xs.set e 0) (e - n)) xs[e])).length =
      xs.length := by rw [List.length_set, List.length_set]
  have hd2 : e - (n - k) < ((xs.set e 0).set (e - n)
      (tritAdd (coeff (xs.set e 0) (e - n)) xs[e])).length := by rw [hlen2]; omega
  have hcell2 : coeff ((xs.set e 0).set (e - n) (tritAdd (coeff (xs.set e 0) (e - n)) xs[e]))
      (e - (n - k)) ≤ 2 := by
    rw [coeff_get _ _ hd2]; exact once _ (List.getElem_mem hd2)
  have hsum2 : ((xs.set e 0).set (e - n) (tritAdd (coeff (xs.set e 0) (e - n)) xs[e]))[e - (n - k)]
      + xs[e] ≤ 1000000 := by
    have := hcell2
    rw [coeff_get _ _ hd2] at this
    omega
  rw [atL_embed _ (e - (n - k)) hd2, ok_bind, addI_ofNat _ _ (fits_small hsum2), ok_bind,
    modI_three, ok_bind, embed_put _ (e - (n - k)) _ hd2, ok_bind,
    withMoves_moves, addI_two (m + 1) hf3, ok_bind, withMoves_withMoves]
  unfold foldHigh
  have hnz : ¬ coeff xs e = 0 := by rw [coeff_get xs e he]; exact hz
  have hnot : ¬ e < n := by omega
  simp [hnz, hnot, hz, coeff_get xs e he]
  rw [← tritAdd, coeff_get _ _ hd2]
  have : ((m : Int) + 1 + 2) = (m : Int) + 3 := by omega
  rw [this]
  constructor
  · rfl
  · rfl

private theorem foldMoves_at (n gap : Nat) (strip : List Nat) (i : Nat) (hi : i < strip.length) :
    foldMoves n gap strip (strip.length - i) =
      foldMoves n gap strip (strip.length - (i + 1)) +
        if coeff (foldDown n gap strip (strip.length - (i + 1))) i = 0 ∨ i < n then 0 else 3 := by
  have hk : strip.length - (i + 1) + 1 = strip.length - i := by omega
  have hidx : strip.length - 1 - (strip.length - (i + 1)) = i := by omega
  rw [← hk, foldMoves_succ, hidx]

private theorem desc_tail_to {S ρ : Type} (toN i : Nat) (hle : toN ≤ i) (hfit : FitsLen i)
    (s : S) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (Except.ok (SudoRt.Flow.brk (Int.ofNat i, s)) : Except SudoRt.Trap (SudoRt.Flow (Int × S) ρ))
      else SudoRt.subI (Int.ofNat i) 1 >>= fun i' => Except.ok (SudoRt.Flow.cont (i', s))) =
      if i = toN then .ok (.brk (Int.ofNat i, s)) else .ok (.cont (Int.ofNat (i - 1), s)) := by
  by_cases h : i = toN
  · subst h
    simp [beq_int_iff]
  · have hlt : toN < i := Nat.lt_of_le_of_ne hle (Ne.symm h)
    have hne : ¬ (Int.ofNat i = Int.ofNat toN) := fun eq => h (Int.ofNat.inj eq)
    simp only [beq_int_iff, hne, if_false, h]
    rw [subI_ofNat_one i (by omega) hfit]
    rfl

/-! ### Top scan and the descending loop

`foldPeg` is one hole. `foldStep` is the emitted descending stepper (the guard, that peg,
the index tail). Both `max_bench_hole` branches of `laneFoldGo` call `foldLoop`, so the
accumulation is proved once. The strip is `Spec.laneFold`; the scan is `Spec.topIdx`. -/

private theorem withMoves_id (b : Ecbs.Board) {m : Int}
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = m) :
    withMoves b m = b := by
  rw [← hm]
  unfold withMoves
  rfl

private theorem natAbs_of (i : Nat) : (Int.ofNat i).natAbs = i :=
  Int.natAbs_ofNat i

private theorem not_ofNat_lt {a b : Nat} (h : b ≤ a) : ¬ Int.ofNat a < Int.ofNat b :=
  Int.not_lt.mpr ((ofNat_le_iff b a).mpr h)

private theorem not_ofNat_gt {a b : Nat} (h : a ≤ b) : ¬ Int.ofNat a > Int.ofNat b :=
  Int.not_lt.mpr ((ofNat_le_iff a b).mpr h)

def foldCharge (n gap : Nat) (strip : List Nat) : Nat :=
  if n < strip.length then foldMoves n gap strip (strip.length - n) else 0

private theorem foldCharge_hi (n gap : Nat) (xs : List Nat) (h : n < xs.length) :
    foldCharge n gap xs = foldMoves n gap xs (xs.length - n) := by
  simp [foldCharge, h]

private theorem foldCharge_lo (n gap : Nat) (xs : List Nat) (h : xs.length ≤ n) :
    foldCharge n gap xs = 0 := by
  rw [foldCharge, if_neg (Nat.not_lt.mpr h)]

/-- Each folded hole charges at most three moves, and only holes at or above `n` fold. -/
theorem foldCharge_bound (n gap : Nat) (strip : List Nat) :
    foldCharge n gap strip ≤ 3 * (strip.length - n) := by
  unfold foldCharge
  split
  · exact foldMoves_le n gap strip (strip.length - n)
  · exact Nat.zero_le _

theorem laneFold_length (n gap : Nat) (strip : List Nat) (hn : n ≤ strip.length) :
    (laneFold n gap strip).length = strip.length := by
  rw [← foldDown_lane n gap strip hn, foldDown_length]

private theorem laneFold_short (n gap : Nat) (xs : List Nat) (h : xs.length ≤ n) :
    laneFold n gap xs = xs := by
  unfold laneFold reduceStrip
  have : xs.length - n = 0 := by omega
  simp [this, List.range_zero]

private theorem foldDown_trits (n gap : Nat) (strip : List Nat)
    (hs : allTritList strip) (hg : gap ≤ n) (hn : n ≤ strip.length) :
    ∀ k, k ≤ strip.length - n → allTritList (foldDown n gap strip k) := by
  intro k hk
  induction k with
  | zero => simpa [foldDown] using hs
  | succ k ih =>
    have hk' : k ≤ strip.length - n := Nat.le_of_succ_le hk
    rw [foldDown_succ]
    have hidx_ge : n ≤ strip.length - 1 - k := by omega
    have hidx_lt : strip.length - 1 - k < (foldDown n gap strip k).length := by
      rw [foldDown_length]
      omega
    exact foldHigh_trits (ih hk') n gap (strip.length - 1 - k) hidx_lt hidx_ge
      (Nat.le_trans hg hidx_ge)

def topAt (xs : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if coeff xs k = 0 then topAt xs k else k

private theorem topAt_foldl (xs : List Nat) :
    ∀ k, topAt xs k = (List.range k).foldl (fun t i => if coeff xs i = 0 then t else i) 0
  | 0 => by simp [topAt, List.range_zero]
  | k + 1 => by
    rw [topAt, List.range_succ, List.foldl_append, topAt_foldl xs k]
    simp

private theorem topIdx_eq (xs : List Nat) : topIdx xs = topAt xs xs.length := by
  unfold topIdx
  exact (topAt_foldl xs xs.length).symm

private theorem topAt_pred (xs : List Nat) : ∀ k, topAt xs (k + 1) ≤ k
  | 0 => by simp [topAt]
  | k + 1 => by
    rw [topAt]
    by_cases h : coeff xs (k + 1) = 0
    · simp only [h, ite_true]
      exact Nat.le_trans (topAt_pred xs k) (Nat.le_succ k)
    · simp only [h, ite_false]
      exact Nat.le_refl _

private theorem topIdx_lt (xs : List Nat) (h : 0 < xs.length) : topIdx xs < xs.length := by
  rw [topIdx_eq]
  cases hL : xs.length with
  | zero => omega
  | succ k =>
    exact Nat.lt_succ_of_le (topAt_pred xs k)

private theorem top_below (xs : List Nat) (benchlen : Nat)
    (hlen : xs.length ≤ benchlen) (hpos : 0 < benchlen) : topIdx xs < benchlen := by
  by_cases h0 : xs.length = 0
  · have : topIdx xs = 0 := by
      unfold topIdx
      simp [h0, List.range_zero]
    omega
  · exact Nat.lt_of_lt_of_le (topIdx_lt xs (Nat.pos_of_ne_zero h0)) hlen

/-- One step of the ascending highest-hole scan. The return channel is the same
    `Board × Array` the emitted scan uses; the body only continues. -/
def topBody (strip : Array Int) (i top : Int) :
    Except SudoRt.Trap (SudoRt.Flow Int (Ecbs.Board × Array Int)) :=
  do
    let c ← SudoRt.atL strip i
    if !(SudoRt.SEq.beq c (0 : Int)) then
      do
        let top := i
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board × Array Int) top)
    else
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board × Array Int) top)

def topStep (strip : Array Int) (toV : Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) (Ecbs.Board × Array Int)) :=
  let i := σ.1
  let top := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board × Array Int) (i, top))
    else
      match ← topBody strip i top with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board × Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board × Array Int) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board × Array Int) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board × Array Int) (i', fs))

/-- Highest nonzero hole, or `0` when the strip is empty. -/
def topScan (strip : Array Int) : Except SudoRt.Trap Int :=
  do
    let top := (0 : Int)
    let last ← SudoRt.subI (SudoRt.listLen strip) (1 : Int)
    let fromV := (0 : Int)
    let fuel : Nat := if fromV > last then 1 else (last - fromV).natAbs + 1
    let out ← SudoRt.runLoopOn (ρ := Ecbs.Board × Array Int) (fromV, top) fuel (topStep strip last)
      (fun σ => pure σ.2) (fun _ => pure 0)
    pure out

private theorem topBody_at (xs : List Nat) (i t : Nat) (hi : i < xs.length) :
    topBody (embed xs) (Int.ofNat i) (Int.ofNat t) =
      .ok (SudoRt.Flow.cont (Int.ofNat (if xs[i] = 0 then t else i))) := by
  unfold topBody
  rw [atL_embed xs i hi, ok_bind, sEq_ofNat_zero]
  by_cases hz : xs[i] = 0
  · simp only [hz, decide_True, Bool.not_true, Bool.false_eq_true, if_false, pure_eq_ok]
    rfl
  · simp only [hz, decide_False, Bool.not_false, if_true, pure_eq_ok]
    rw [if_false]

private theorem topStep_at (xs : List Nat) (toN i t : Nat)
    (hi : i < xs.length) (hle : i ≤ toN) (hfit : FitsLen (i + 1)) :
    topStep (embed xs) (Int.ofNat toN) (Int.ofNat i, Int.ofNat t) =
      if i = toN then
        .ok (.brk (Int.ofNat i, Int.ofNat (if xs[i] = 0 then t else i)))
      else
        .ok (.cont (Int.ofNat (i + 1), Int.ofNat (if xs[i] = 0 then t else i))) := by
  unfold topStep
  dsimp only
  rw [if_neg (not_ofNat_gt hle), topBody_at xs i t hi, ok_bind]
  exact asc_tail toN i hfit (Int.ofNat (if xs[i] = 0 then t else i))

private theorem top_scan_refines (xs : List Nat) (hfit : FitsLen xs.length) :
    topScan (embed xs) = .ok (Int.ofNat (topIdx xs)) := by
  unfold topScan
  rw [listLen_embed]
  by_cases h0 : xs.length = 0
  · rw [h0, show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
    have hgt : (0 : Int) > (-1) := by decide
    dsimp only
    rw [if_pos hgt, show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    have hstep : topStep (embed xs) (-1) ((0 : Int), (0 : Int)) =
        .ok (.brk ((0 : Int), (0 : Int))) := by
      unfold topStep
      dsimp only
      rw [if_pos hgt, pure_eq_ok]
    rw [hstep]
    dsimp
    unfold topIdx
    simp [h0, List.range_zero, toPure_eq_ok]
  · have hpos : 0 < xs.length := Nat.pos_of_ne_zero h0
    rw [subI_ofNat_one xs.length hpos hfit, ok_bind]
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    dsimp only
    have hfuel :
        (if Int.ofNat 0 > Int.ofNat (xs.length - 1) then 1
          else (Int.ofNat (xs.length - 1) - Int.ofNat 0).natAbs + 1) =
        fuelRange (Int.ofNat 0) (Int.ofNat (xs.length - 1)) := rfl
    rw [hfuel, except_bind_pure]
    refine asc_goal (fun i top => top = Int.ofNat (topAt xs i)) (Nat.zero_le _) rfl ?_ ?_
    · intro i top _ hi hI
      have hiL : i < xs.length := by omega
      have hfiti : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
      rw [hI]
      have hnext : (if xs[i] = 0 then topAt xs i else i) = topAt xs (i + 1) := by
        rw [topAt, coeff_get xs i hiL]
      have hstep := topStep_at xs (xs.length - 1) i (topAt xs i) hiL (by omega) hfiti
      rw [hnext] at hstep
      exact ⟨Int.ofNat (topAt xs (i + 1)), rfl, hstep⟩
    · intro top hI
      rw [pure_eq_ok, hI, topIdx_eq]
      have : xs.length - 1 + 1 = xs.length := by omega
      rw [this]

/-- The scan's `after` may read the highest hole. `onRet` is unused: the step never returns. -/
private theorem top_join {α : Type} (xs : List Nat) (hfit : FitsLen xs.length)
    (body : Int → Except SudoRt.Trap α)
    (onRet : Ecbs.Board × Array Int → Except SudoRt.Trap α) :
    (do
      let top := (0 : Int)
      let last ← SudoRt.subI (SudoRt.listLen (embed xs)) (1 : Int)
      let fromV := (0 : Int)
      let fuel : Nat := if fromV > last then 1 else (last - fromV).natAbs + 1
      SudoRt.runLoopOn (fromV, top) fuel (topStep (embed xs) last)
        (fun σ => body σ.2) onRet) =
      body (Int.ofNat (topIdx xs)) := by
  rw [listLen_embed]
  by_cases h0 : xs.length = 0
  · rw [h0, show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
    have hgt : (0 : Int) > (-1) := by decide
    dsimp only
    rw [if_pos hgt, show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    have hstep : topStep (embed xs) (-1) ((0 : Int), (0 : Int)) =
        .ok (.brk ((0 : Int), (0 : Int))) := by
      unfold topStep
      dsimp only
      rw [if_pos hgt, pure_eq_ok]
    rw [hstep]
    dsimp
    unfold topIdx
    simp [h0, List.range_zero]
  · have hpos : 0 < xs.length := Nat.pos_of_ne_zero h0
    rw [subI_ofNat_one xs.length hpos hfit, ok_bind]
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    dsimp only
    have hfuel :
        (if Int.ofNat 0 > Int.ofNat (xs.length - 1) then 1
          else (Int.ofNat (xs.length - 1) - Int.ofNat 0).natAbs + 1) =
        fuelRange (Int.ofNat 0) (Int.ofNat (xs.length - 1)) := rfl
    rw [hfuel]
    refine asc_goal (fun i top => top = Int.ofNat (topAt xs i)) (Nat.zero_le _) rfl ?_ ?_
    · intro i top _ hi hI
      have hiL : i < xs.length := by omega
      have hfiti : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
      rw [hI]
      have hnext : (if xs[i] = 0 then topAt xs i else i) = topAt xs (i + 1) := by
        rw [topAt, coeff_get xs i hiL]
      have hstep := topStep_at xs (xs.length - 1) i (topAt xs i) hiL (by omega) hfiti
      rw [hnext] at hstep
      exact ⟨Int.ofNat (topAt xs (i + 1)), rfl, hstep⟩
    · intro top hI
      rw [hI, topIdx_eq]
      have : xs.length - 1 + 1 = xs.length := by omega
      rw [this]

/-- The descending stepper. `foldPeg` is the clear and the two image adds. -/
def foldStep (w h r n k : Nat) (toV : Int)
    (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) (Ecbs.Board × Array Int)) :=
  let e := σ.1
  let strip := σ.2.1
  let b := σ.2.2
  do
    if e < toV then
      pure (SudoRt.Flow.brk (e, (strip, b)))
    else
      match ← foldPeg w h r n k strip e.natAbs b with
      | .ret r => pure (SudoRt.Flow.ret r)
      | .brk fs => pure (SudoRt.Flow.brk (e, fs))
      | .cont fs => do
          if e == toV then
            pure (SudoRt.Flow.brk (e, fs))
          else do
            let i' ← SudoRt.subI e (1 : Int)
            pure (SudoRt.Flow.cont (i', fs))

/-- One copy of the descending accumulation. Both hole-record branches call this. -/
def foldLoop (w h r n k : Nat) (strip : Array Int) (b : Ecbs.Board) (nI : Int) :
    Except SudoRt.Trap (Ecbs.Board × Array Int) :=
  do
    let fromV ← SudoRt.subI (SudoRt.listLen strip) (1 : Int)
    let fuel : Nat := if fromV < nI then 1 else (fromV - nI).natAbs + 1
    let out ← SudoRt.runLoopOn (ρ := Ecbs.Board × Array Int) (fromV, (strip, b)) fuel
      (foldStep w h r n k nI)
      (fun σ => pure (σ.2.2, σ.2.1))
      (fun r => pure r)
    pure out

private theorem foldStep_break (w h r n k i n0 : Nat) (strip : Array Int) (b : Ecbs.Board)
    (hlt : i < n0) :
    foldStep w h r n k (Int.ofNat n0) (Int.ofNat i, (strip, b)) =
      .ok (.brk (Int.ofNat i, (strip, b))) := by
  unfold foldStep
  dsimp only
  rw [if_pos ((ofNat_lt_iff i n0).mpr hlt), pure_eq_ok]

private theorem foldStep_zero (prev : List Nat) (w h r n k i : Nat) (b : Ecbs.Board)
    (hi : i < prev.length) (hz : prev[i] = 0) (hle : n ≤ i) (hfit : FitsLen i) :
    foldStep w h r n k (Int.ofNat n) (Int.ofNat i, (embed prev, b)) =
      if i = n then .ok (.brk (Int.ofNat i, (embed prev, b)))
      else .ok (.cont (Int.ofNat (i - 1), (embed prev, b))) := by
  unfold foldStep
  dsimp only
  rw [if_neg (not_ofNat_lt hle), natAbs_of, foldPeg_zero prev w h r n k i b hi hz, ok_bind]
  exact desc_tail_to n i hle hfit (embed prev, b)

private theorem foldStep_nz (prev : List Nat) (w h r n k i m : Nat) (b : Ecbs.Board)
    (hw : 0 < w) (hh : 0 < h) (hr : r < h) (hr0 : 0 < r)
    (hn : n = w * h - 1) (hk : k ≤ n) (hgap : n - k = w * r)
    (hi : i < prev.length) (hen : n ≤ i) (hz : prev[i] ≠ 0) (hs : allTritList prev)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat m)
    (hf1 : FitsLen (m + 1)) (hf3 : FitsLen (m + 3))
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ i ≤ 1000000)
    (hnsm : n ≤ 1000000) (hfit : FitsLen i) :
    foldStep w h r n k (Int.ofNat n) (Int.ofNat i, (embed prev, b)) =
      if i = n then
        .ok (.brk (Int.ofNat i,
          (embed (foldHigh n (n - k) i prev), withMoves b (Int.ofNat (m + 3)))))
      else
        .ok (.cont (Int.ofNat (i - 1),
          (embed (foldHigh n (n - k) i prev), withMoves b (Int.ofNat (m + 3))))) := by
  unfold foldStep
  dsimp only
  rw [if_neg (not_ofNat_lt hen), natAbs_of,
    foldPeg_nz prev w h r n k i m b hw hh hr hr0 hn hk hgap hi hen hz hs hm hf1 hf3 hsm hnsm,
    ok_bind]
  exact desc_tail_to n i hen hfit
    (embed (foldHigh n (n - k) i prev), withMoves b (Int.ofNat (m + 3)))

private theorem move_room (moves L n i extra : Nat) (hn : n ≤ i) (hi : i < L)
    (hex : extra ≤ 3 * (L - (i + 1))) :
    moves + extra + 3 ≤ moves + 3 * (L - n) := by
  have hspan : L - (i + 1) + 1 ≤ L - n := by omega
  have hmul : 3 * (L - (i + 1)) + 3 = 3 * (L - (i + 1) + 1) := by omega
  omega

/-- The descending accumulation, from the far end down through hole `n`.
    A shorter strip breaks at once and is already `Spec.laneFold`. -/
theorem fold_loop_refines (xs : List Nat) (w h r n k moves : Nat) (b : Ecbs.Board)
    (hw : 0 < w) (hh : 0 < h) (hr : r < h) (hr0 : 0 < r)
    (hn : n = w * h - 1) (hk : k ≤ n) (hgap : n - k = w * r)
    (hs : allTritList xs)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ xs.length ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfm : FitsLen (moves + 3 * (xs.length - n))) :
    foldLoop w h r n k (embed xs) b (Int.ofNat n) =
      .ok (withMoves b (Int.ofNat (moves + foldCharge n (n - k) xs)),
        embed (laneFold n (n - k) xs)) := by
  by_cases hlt : n < xs.length
  · -- Far end is at least hole `n`: the loop runs.
    unfold foldLoop
    rw [listLen_embed]
    have hpos : 0 < xs.length := Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hlt) (Nat.le_refl _)
    have hfitL : FitsLen xs.length := fits_le _ (by have := hsm.2.2.2; omega)
    rw [subI_ofNat_one xs.length hpos hfitL, ok_bind]
    have hfrom : n ≤ xs.length - 1 := by omega
    have hfuel :
        (if Int.ofNat (xs.length - 1) < Int.ofNat n then 1
          else (Int.ofNat (xs.length - 1) - Int.ofNat n).natAbs + 1) =
        fuelDown (Int.ofNat (xs.length - 1)) (Int.ofNat n) := rfl
    rw [hfuel, except_bind_pure]
    refine desc_goal
      (fun t (st : Array Int × Ecbs.Board) =>
        st.1 = embed (foldDown n (n - k) xs (xs.length - t)) ∧
        st.2 = withMoves b (Int.ofNat (moves + foldMoves n (n - k) xs (xs.length - t))) ∧
        allTritList (foldDown n (n - k) xs (xs.length - t)))
      hfrom ?_ ?_ ?_
    · have hz : xs.length - (xs.length - 1 + 1) = 0 := by omega
      refine ⟨?_, ?_, ?_⟩
      · simp [hz, foldDown]
      · simp [hz, foldMoves, Nat.add_zero]
        exact (withMoves_id b hm).symm
      · simpa [hz, foldDown] using hs
    · intro i st hlo hiU hI
      have hi : i < xs.length := by omega
      have hfiti : FitsLen i := fits_small (by
        have hL := hsm.2.2.2
        omega)
      have hpair : st =
          (embed (foldDown n (n - k) xs (xs.length - (i + 1))),
            withMoves b (Int.ofNat (moves + foldMoves n (n - k) xs (xs.length - (i + 1))))) :=
        Prod.ext hI.1 hI.2.1
      rw [hpair]
      let prev := foldDown n (n - k) xs (xs.length - (i + 1))
      let mv := moves + foldMoves n (n - k) xs (xs.length - (i + 1))
      have hprev : foldDown n (n - k) xs (xs.length - (i + 1)) = prev := rfl
      have hmvEq : moves + foldMoves n (n - k) xs (xs.length - (i + 1)) = mv := rfl
      rw [hprev, hmvEq]
      have hlenp : prev.length = xs.length := foldDown_length n (n - k) xs _
      have ht : allTritList prev := by simpa [prev] using hI.2.2
      have hmvb : (withMoves b (Int.ofNat mv)).sudo_5Board_4cost.sudo_5Costs_5moves =
          Int.ofNat mv := withMoves_moves _ _
      by_cases hz : coeff prev i = 0
      · have hiz : i < prev.length := by rw [hlenp]; exact hi
        have hz0 : prev[i] = 0 := by rw [← coeff_get prev i hiz]; exact hz
        have hstep := foldStep_zero prev w h r n k i (withMoves b (Int.ofNat mv))
          hiz hz0 hlo hfiti
        refine ⟨(embed prev, withMoves b (Int.ofNat mv)), ?_, hstep⟩
        refine ⟨?_, ?_, ?_⟩
        · have heq : foldDown n (n - k) xs (xs.length - i) = prev := by
            rw [foldDown_at n (n - k) xs i hi, foldHigh_zero _ _ _ _ hz]
          exact congrArg embed heq.symm
        · have hsum : mv = moves + foldMoves n (n - k) xs (xs.length - i) := by
            rw [foldMoves_at n (n - k) xs i hi]
            simp [prev, hz, show ¬ i < n from by omega, Nat.add_zero]
          exact congrArg (fun t => withMoves b (Int.ofNat t)) hsum
        · exact foldDown_trits n (n - k) xs hs (Nat.sub_le n k)
            (Nat.le_of_lt hlt) (xs.length - i) (by omega)
      · have hiz : i < prev.length := by rw [hlenp]; exact hi
        have hnz : prev[i] ≠ 0 := by
          intro h
          exact hz (by rw [coeff_get prev i hiz]; exact h)
        have hex : foldMoves n (n - k) xs (xs.length - (i + 1)) ≤
            3 * (xs.length - (i + 1)) := foldMoves_le _ _ _ _
        have hroom := move_room moves xs.length n i _ hlo hi hex
        have hf1 : FitsLen (mv + 1) := FitsLen.of_le hfm (by omega)
        have hf3 : FitsLen (mv + 3) := FitsLen.of_le hfm hroom
        have hsmI : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ i ≤ 1000000 :=
          ⟨hsm.1, hsm.2.1, hsm.2.2.1, by have := hsm.2.2.2; omega⟩
        have hstep := foldStep_nz prev w h r n k i mv (withMoves b (Int.ofNat mv))
          hw hh hr hr0 hn hk hgap hiz hlo hnz ht hmvb hf1 hf3 hsmI hnsm hfiti
        rw [withMoves_withMoves] at hstep
        refine ⟨(embed (foldHigh n (n - k) i prev), withMoves b (Int.ofNat (mv + 3))), ?_, hstep⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [foldDown_at n (n - k) xs i hi]
        · have hsum : mv + 3 = moves + foldMoves n (n - k) xs (xs.length - i) := by
            rw [foldMoves_at n (n - k) xs i hi, hprev]
            simp [hz, show ¬ i < n from by omega]
            have : moves + (foldMoves n (n - k) xs (xs.length - (i + 1)) + 3) =
                (moves + foldMoves n (n - k) xs (xs.length - (i + 1))) + 3 := by omega
            rw [this, hmvEq]
          exact congrArg (fun t => withMoves b (Int.ofNat t)) hsum
        · exact foldDown_trits n (n - k) xs hs (Nat.sub_le n k)
            (Nat.le_of_lt hlt) (xs.length - i) (by omega)
    · intro st hI
      dsimp only
      rw [pure_eq_ok]
      have hfold := foldDown_lane n (n - k) xs (Nat.le_of_lt hlt)
      have hch := foldCharge_hi n (n - k) xs hlt
      apply congrArg Except.ok
      apply Prod.ext
      · rw [hI.2.1, hch]
      · rw [hI.1, hfold]
  · have hle : xs.length ≤ n := Nat.le_of_not_lt hlt
    unfold foldLoop
    rw [listLen_embed]
    by_cases h0 : xs.length = 0
    · rw [h0, show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind]
      have hneg : (-1 : Int) < Int.ofNat n :=
        Int.lt_of_lt_of_le (by decide : (-1 : Int) < 0) (Int.ofNat_nonneg n)
      rw [if_pos hneg]
      dsimp only
      have hstep : foldStep w h r n k (Int.ofNat n) ((-1), (embed xs, b)) =
          .ok (.brk ((-1), (embed xs, b))) := by
        unfold foldStep
        dsimp only
        rw [if_pos hneg, pure_eq_ok]
      rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, hstep]
      dsimp
      rw [ofNat_eq_natCast moves] at hm
      rw [except_bind_pure, laneFold_short n (n - k) xs hle, foldCharge_lo n (n - k) xs hle,
        Nat.add_zero, withMoves_id b hm]
      exact toPure_eq_ok (b, embed xs)
    · have hpos : 0 < xs.length := Nat.pos_of_ne_zero h0
      have hfitL : FitsLen xs.length := fits_le _ (by have := hsm.2.2.2; omega)
      rw [subI_ofNat_one xs.length hpos hfitL, ok_bind]
      have hfrom : xs.length - 1 < n := by omega
      have hltI : Int.ofNat (xs.length - 1) < Int.ofNat n := (ofNat_lt_iff _ _).mpr hfrom
      rw [if_pos hltI]
      dsimp only
      rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ,
        foldStep_break w h r n k (xs.length - 1) n (embed xs) b hfrom]
      dsimp
      rw [ofNat_eq_natCast moves] at hm
      rw [except_bind_pure, laneFold_short n (n - k) xs hle, foldCharge_lo n (n - k) xs hle,
        Nat.add_zero, withMoves_id b hm]
      exact toPure_eq_ok (b, embed xs)

def withHole (b : Ecbs.Board) (top : Int) : Ecbs.Board :=
  { b with sudo_5Board_4cost :=
      { b.sudo_5Board_4cost with sudo_5Costs_14max_bench_hole := top } }

private theorem withHole_moves (b : Ecbs.Board) (top : Int) :
    (withHole b top).sudo_5Board_4cost.sudo_5Costs_5moves =
      b.sudo_5Board_4cost.sudo_5Costs_5moves := rfl

/-- Record the highest hole when it beats the old one, then fold. The two branches are
    the same `foldLoop`. -/
def noteBench (b : Ecbs.Board) (top mv : Int) : Ecbs.Board :=
  withMoves (if decide (top > b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) then
    withHole b top else b) mv

def laneFoldGo (w h r n k : Nat) (benchlen : Int) (b : Ecbs.Board) (strip : Array Int) :
    Except SudoRt.Trap (Ecbs.Board × Array Int) :=
  do
    let top ← topScan strip
    if decide (top > b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) then
      do
        let b := withHole b top
        let _u ← SudoRt.sudoAssert (decide (top < benchlen)) 515
        foldLoop w h r n k strip b (Int.ofNat n)
    else
      do
        let _u ← SudoRt.sudoAssert (decide (top < benchlen)) 515
        foldLoop w h r n k strip b (Int.ofNat n)

/-- `lane_fold` on the layout: the scan, then one descending fold (clear, both images,
    three moves per nonzero high peg). Both `max_bench_hole` branches are `fold_loop_refines`. -/
theorem lane_fold_refines (xs : List Nat) (w h r n k moves hole benchlen : Nat) (b : Ecbs.Board)
    (hw : 0 < w) (hh : 0 < h) (hr : r < h) (hr0 : 0 < r)
    (hn : n = w * h - 1) (hk : k ≤ n) (hgap : n - k = w * r)
    (hs : allTritList xs)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ xs.length ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfm : FitsLen (moves + 3 * (xs.length - n)))
    (hfit : FitsLen xs.length)
    (hlen : xs.length ≤ benchlen) (hpos : 0 < benchlen) :
    laneFoldGo w h r n k (Int.ofNat benchlen) b (embed xs) =
      .ok (noteBench b (Int.ofNat (topIdx xs)) (Int.ofNat (moves + foldCharge n (n - k) xs)),
        embed (laneFold n (n - k) xs)) := by
  have hbelow : topIdx xs < benchlen := top_below xs benchlen hlen hpos
  unfold laneFoldGo noteBench
  rw [top_scan_refines xs hfit, ok_bind, hhole]
  by_cases hgt : hole < topIdx xs
  · have hdec : decide (Int.ofNat (topIdx xs) > Int.ofNat hole) = true := by
      rw [decide_eq_true_eq]
      exact (ofNat_lt_iff hole (topIdx xs)).mpr hgt
    have htop : decide (Int.ofNat (topIdx xs) < Int.ofNat benchlen) = true :=
      decide_eq_true ((ofNat_lt_iff _ _).mpr hbelow)
    simp only [hdec, ite_true, ok_bind, htop, sudoAssert_true, ok_bind]
    have hm' : (withHole b (Int.ofNat (topIdx xs))).sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat moves := by rw [withHole_moves, hm]
    rw [fold_loop_refines xs w h r n k moves (withHole b (Int.ofNat (topIdx xs)))
      hw hh hr hr0 hn hk hgap hs hm' hsm hnsm hfm]
  · have hdec : decide (Int.ofNat (topIdx xs) > Int.ofNat hole) = false := by
      rw [decide_eq_false_iff_not]
      intro h
      exact hgt ((ofNat_lt_iff hole (topIdx xs)).mp h)
    have htop : decide (Int.ofNat (topIdx xs) < Int.ofNat benchlen) = true :=
      decide_eq_true ((ofNat_lt_iff _ _).mpr hbelow)
    simp only [hdec, Bool.false_eq_true, if_false, ok_bind, htop, sudoAssert_true, ok_bind]
    rw [fold_loop_refines xs w h r n k moves b hw hh hr hr0 hn hk hgap hs hm hsm hnsm hfm]

private theorem coeff_set_same (xs : List Nat) (i v : Nat) (hi : i < xs.length) :
    coeff (xs.set i v) i = v := by
  have hi' : i < (xs.set i v).length := by rw [List.length_set]; exact hi
  rw [coeff_get _ _ hi', List.getElem_set_self]

private theorem coeff_set_ne (xs : List Nat) (i v j : Nat) (hj : j < xs.length) (hne : i ≠ j) :
    coeff (xs.set i v) j = coeff xs j := by
  have hj' : j < (xs.set i v).length := by rw [List.length_set]; exact hj
  rw [coeff_get _ _ hj', List.getElem_set, if_neg hne, ← coeff_get xs j hj]

private theorem foldHigh_above (n gap e i : Nat) (strip : List Nat)
    (hi : i < strip.length) (hgt : e < i) :
    coeff (foldHigh n gap e strip) i = coeff strip i := by
  unfold foldHigh
  by_cases hz : coeff strip e = 0
  · simp [hz]
  · by_cases hlt : e < n
    · simp [hz, hlt]
    · simp only [hz, hlt, false_or, ite_false]
      have hne1 : e ≠ i := Nat.ne_of_lt hgt
      have hne2 : e - n ≠ i := by omega
      have hne3 : e - gap ≠ i := by omega
      rw [coeff_set_ne _ (e - gap) _ i (by rw [List.length_set, List.length_set]; exact hi) hne3,
        coeff_set_ne _ (e - n) _ i (by rw [List.length_set]; exact hi) hne2,
        coeff_set_ne _ e 0 i hi hne1]

/-- A high peg is cleared, and both images sit strictly below it when `n` and the gap are positive. -/
private theorem foldHigh_clear (n gap e : Nat) (strip : List Nat)
    (he : e < strip.length) (hn : 0 < n) (hg : 0 < gap) (hen : n ≤ e) :
    coeff (foldHigh n gap e strip) e = 0 := by
  unfold foldHigh
  by_cases hz : coeff strip e = 0
  · simp [hz, coeff_get strip e he]
  · have hlt : ¬ e < n := by omega
    simp only [hz, hlt, false_or, ite_false]
    have hne2 : e - n ≠ e := by omega
    have hne3 : e - gap ≠ e := by omega
    rw [coeff_set_ne _ (e - gap) _ e (by rw [List.length_set, List.length_set]; exact he) hne3,
      coeff_set_ne _ (e - n) _ e (by rw [List.length_set]; exact he) hne2,
      coeff_set_same _ e 0 he]

private theorem foldDown_cleared (n gap : Nat) (strip : List Nat)
    (hn0 : 0 < n) (hg : 0 < gap) (hn : n ≤ strip.length) :
    ∀ m, m ≤ strip.length - n → ∀ i, strip.length - m ≤ i → i < strip.length →
      coeff (foldDown n gap strip m) i = 0 := by
  intro m hm
  induction m with
  | zero =>
    intro i hlo hi
    omega
  | succ m ih =>
    intro i hlo hi
    rw [foldDown_succ]
    have he : strip.length - 1 - m < strip.length := by omega
    have hen : n ≤ strip.length - 1 - m := by omega
    by_cases hgt : strip.length - 1 - m < i
    · have hi' : i < (foldDown n gap strip m).length := by rw [foldDown_length]; exact hi
      rw [foldHigh_above n gap (strip.length - 1 - m) i (foldDown n gap strip m) hi' hgt]
      exact ih (Nat.le_of_succ_le hm) i (by omega) hi
    · have heq : i = strip.length - 1 - m := by omega
      rw [heq, foldHigh_clear n gap (strip.length - 1 - m) (foldDown n gap strip m)
        (by rw [foldDown_length]; exact he) hn0 hg hen]

/-- After the lane fold, every hole at or above `n` is empty. That is the tail `settle` checks. -/
theorem laneFold_high (n gap : Nat) (strip : List Nat) (i : Nat)
    (hn0 : 0 < n) (hg : 0 < gap) (hn : n ≤ strip.length)
    (hlo : n ≤ i) (hi : i < strip.length) :
    coeff (laneFold n gap strip) i = 0 := by
  rw [← foldDown_lane n gap strip hn]
  exact foldDown_cleared n gap strip hn0 hg hn (strip.length - n) (Nat.le_refl _) i (by omega) hi


/-! ### Emitted `lane_fold` is the model scan and `foldLoop` -/

def lanePeg (strip : Array Int) (e : Int) (b : Ecbs.Board) (w h r n k : Int) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int × Ecbs.Board) (Ecbs.Board × Array Int)) :=
  do
  let _t443 ← SudoRt.atL strip e
  let c := _t443
  if (!(SudoRt.SEq.beq c (0 : Int))) then
    do
      let _ix445 := e
      let _t446 ← SudoRt.putL strip _ix445 (0 : Int)
      let strip := _t446
      let _t447 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_5moves (1 : Int)
      let _t448 := ({ (b).sudo_5Board_4cost with sudo_5Costs_5moves := _t447 } : Ecbs.Costs)
      let _t449 := ({ b with sudo_5Board_4cost := _t448 } : Ecbs.Board)
      let b := _t449
      let _t450 ← SudoRt.divI e w
      let row := _t450
      let _t451 ← SudoRt.modI e w
      let col := _t451
      let _t452 ← SudoRt.subI row h
      let r1 := _t452
      let _t453 ← SudoRt.addI col (1 : Int)
      let c1 := _t453
      if (SudoRt.SEq.beq c1 w) then
        do
          let _t455 ← SudoRt.addI r1 (1 : Int)
          let r1 := _t455
          let c1 := (0 : Int)
          let _t456 ← SudoRt.mulI r1 w
          let _t457 ← SudoRt.addI _t456 c1
          let d1 := _t457
          let _t458 ← SudoRt.subI row r
          let _t459 ← SudoRt.mulI _t458 w
          let _t460 ← SudoRt.addI _t459 col
          let d2 := _t460
          let _t461 ← SudoRt.subI e n
          let _t463 ← (if (SudoRt.SEq.beq d1 _t461) then (do
  let _t464 ← SudoRt.subI n k
  let _t465 ← SudoRt.subI e _t464
  pure (SudoRt.SEq.beq d2 _t465)) else pure false)
          let _as467 ← SudoRt.sudoAssert _t463 530
          let _t469 ← (if (decide (d1 ≥ (0 : Int))) then (do
  pure (decide (d1 < e))) else pure false)
          let _t471 ← (if _t469 then (do
  pure (decide (d2 ≥ (0 : Int)))) else pure false)
          let _t473 ← (if _t471 then (do
  pure (decide (d2 < e))) else pure false)
          let _as475 ← SudoRt.sudoAssert _t473 531
          let _ix476 := d1
          let _t477 ← SudoRt.atL strip d1
          let _t478 ← SudoRt.addI _t477 c
          let _t479 ← SudoRt.modI _t478 (3 : Int)
          let _t480 ← SudoRt.putL strip _ix476 _t479
          let strip := _t480
          let _ix481 := d2
          let _t482 ← SudoRt.atL strip d2
          let _t483 ← SudoRt.addI _t482 c
          let _t484 ← SudoRt.modI _t483 (3 : Int)
          let _t485 ← SudoRt.putL strip _ix481 _t484
          let strip := _t485
          let _t486 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_5moves (2 : Int)
          let _t487 := ({ (b).sudo_5Board_4cost with sudo_5Costs_5moves := _t486 } : Ecbs.Costs)
          let _t488 := ({ b with sudo_5Board_4cost := _t487 } : Ecbs.Board)
          let b := _t488
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board × (Array Int)) (strip, b))
      else
        do
          let _t489 ← SudoRt.mulI r1 w
          let _t490 ← SudoRt.addI _t489 c1
          let d1 := _t490
          let _t491 ← SudoRt.subI row r
          let _t492 ← SudoRt.mulI _t491 w
          let _t493 ← SudoRt.addI _t492 col
          let d2 := _t493
          let _t494 ← SudoRt.subI e n
          let _t496 ← (if (SudoRt.SEq.beq d1 _t494) then (do
  let _t497 ← SudoRt.subI n k
  let _t498 ← SudoRt.subI e _t497
  pure (SudoRt.SEq.beq d2 _t498)) else pure false)
          let _as500 ← SudoRt.sudoAssert _t496 530
          let _t502 ← (if (decide (d1 ≥ (0 : Int))) then (do
  pure (decide (d1 < e))) else pure false)
          let _t504 ← (if _t502 then (do
  pure (decide (d2 ≥ (0 : Int)))) else pure false)
          let _t506 ← (if _t504 then (do
  pure (decide (d2 < e))) else pure false)
          let _as508 ← SudoRt.sudoAssert _t506 531
          let _ix509 := d1
          let _t510 ← SudoRt.atL strip d1
          let _t511 ← SudoRt.addI _t510 c
          let _t512 ← SudoRt.modI _t511 (3 : Int)
          let _t513 ← SudoRt.putL strip _ix509 _t512
          let strip := _t513
          let _ix514 := d2
          let _t515 ← SudoRt.atL strip d2
          let _t516 ← SudoRt.addI _t515 c
          let _t517 ← SudoRt.modI _t516 (3 : Int)
          let _t518 ← SudoRt.putL strip _ix514 _t517
          let strip := _t518
          let _t519 ← SudoRt.addI ((b).sudo_5Board_4cost).sudo_5Costs_5moves (2 : Int)
          let _t520 := ({ (b).sudo_5Board_4cost with sudo_5Costs_5moves := _t519 } : Ecbs.Costs)
          let _t521 := ({ b with sudo_5Board_4cost := _t520 } : Ecbs.Board)
          let b := _t521
          pure (SudoRt.Flow.cont (ρ := Ecbs.Board × (Array Int)) (strip, b))
  else
    do
      pure (SudoRt.Flow.cont (ρ := Ecbs.Board × (Array Int)) (strip, b))

def laneFoldStep (w h r n k toV : Int)
    (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) (Ecbs.Board × Array Int)) :=
  let e := σ.1
  let strip := σ.2.1
  let b := σ.2.2
  do
    if e < toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board × Array Int) (e, (strip, b)))
    else
      match ← lanePeg strip e b w h r n k with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board × Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board × Array Int) (e, fs))
      | .cont fs => do
          if e == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board × Array Int) (e, fs))
          else do
            let i' ← SudoRt.subI e (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board × Array Int) (i', fs))


theorem lanePeg_fold (w h r n k e : Nat) (strip : Array Int) (b : Ecbs.Board) :
    lanePeg strip (Int.ofNat e) b (Int.ofNat w) (Int.ofNat h) (Int.ofNat r)
        (Int.ofNat n) (Int.ofNat k) =
      foldPeg w h r n k strip e b := by
  simp [lanePeg, foldPeg, laneGeom, foldGeom, bind, Except.bind, withMoves]
  repeat (first | rfl | split)

theorem laneFold_step_at (w h r n k i : Nat) (toV : Int) (strip : Array Int) (b : Ecbs.Board) :
    laneFoldStep (Int.ofNat w) (Int.ofNat h) (Int.ofNat r) (Int.ofNat n) (Int.ofNat k) toV
        (Int.ofNat i, (strip, b)) =
      foldStep w h r n k toV (Int.ofNat i, (strip, b)) := by
  unfold laneFoldStep foldStep
  dsimp only
  rw [show (Int.ofNat i).natAbs = i from Int.natAbs_ofNat i, lanePeg_fold]

theorem laneFold_step (w h r n k : Nat) :
    laneFoldStep (Int.ofNat w) (Int.ofNat h) (Int.ofNat r) (Int.ofNat n) (Int.ofNat k)
        (Int.ofNat n) =
      foldStep w h r n k (Int.ofNat n) := by
  funext σ
  cases σ with
  | mk e st =>
    cases st with
    | mk strip b =>
      by_cases hlt : e < Int.ofNat n
      · unfold laneFoldStep foldStep
        dsimp only
        rw [if_pos hlt, if_pos hlt]
      · have hge : Int.ofNat n ≤ e := (Int.not_lt).mp hlt
        have hnn : 0 ≤ e := Int.le_trans (Int.ofNat_nonneg n) hge
        have he : e = ↑e.natAbs := (Int.natAbs_of_nonneg hnn).symm
        rw [he]
        exact laneFold_step_at w h r n k e.natAbs (Int.ofNat n) strip b

def descBlock
    (step : Int × (Array Int × Ecbs.Board) →
      Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) (Ecbs.Board × Array Int)))
    (nI : Int) (strip : Array Int) (b : Ecbs.Board) :
    Except SudoRt.Trap (Ecbs.Board × Array Int) :=
  do
    let fromV ← SudoRt.subI (SudoRt.listLen strip) (1 : Int)
    let fuel : Nat := if fromV < nI then 1 else (fromV - nI).natAbs + 1
    let out ← SudoRt.runLoopOn (ρ := Ecbs.Board × Array Int) (fromV, (strip, b)) fuel step
      (fun σ =>
        let strip := σ.2.1
        let b := σ.2.2
        pure (b, strip))
      (fun r => pure r)
    pure out

theorem descBlock_fold (w h r n k : Nat) (strip : Array Int) (b : Ecbs.Board) :
    descBlock (foldStep w h r n k (Int.ofNat n)) (Int.ofNat n) strip b =
      foldLoop w h r n k strip b (Int.ofNat n) := by
  unfold descBlock foldLoop
  rfl

theorem descBlock_emit (w h r n k : Nat) (strip : Array Int) (b : Ecbs.Board) :
    descBlock (laneFoldStep (Int.ofNat w) (Int.ofNat h) (Int.ofNat r) (Int.ofNat n) (Int.ofNat k)
        (Int.ofNat n)) (Int.ofNat n) strip b =
      foldLoop w h r n k strip b (Int.ofNat n) := by
  rw [laneFold_step, descBlock_fold]

def laneFoldEmit (w h r n k bench : Int) (b : Ecbs.Board) (strip : Array Int) :
    Except SudoRt.Trap (Ecbs.Board × Array Int) :=
  do
    let top := (0 : Int)
    let last ← SudoRt.subI (SudoRt.listLen strip) (1 : Int)
    let fromV := (0 : Int)
    let toV := last
    let fuel : Nat := if fromV > toV then 1 else (toV - fromV).natAbs + 1
    let out ← SudoRt.runLoopOn (ρ := Ecbs.Board × Array Int) (fromV, top) fuel
      (topStep strip toV)
      (fun σ =>
        let top := σ.2
        do
          if decide (top > b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) then
            do
              let b := withHole b top
              let _u ← SudoRt.sudoAssert (decide (top < bench)) 515
              descBlock (laneFoldStep w h r n k n) n strip b
          else
            do
              let _u ← SudoRt.sudoAssert (decide (top < bench)) 515
              descBlock (laneFoldStep w h r n k n) n strip b)
      (fun r => pure r)
    pure out

theorem laneFold_emit (b : Ecbs.Board) (strip : Array Int) :
    Ecbs.lane_fold b strip =
      laneFoldEmit b.sudo_5Board_1t.sudo_4Tier_1w b.sudo_5Board_1t.sudo_4Tier_1h
        b.sudo_5Board_1t.sudo_4Tier_1r b.sudo_5Board_1t.sudo_4Tier_1n
        b.sudo_5Board_1t.sudo_4Tier_1k b.sudo_5Board_1t.sudo_4Tier_8benchlen b strip := by
  unfold laneFoldEmit descBlock laneFoldStep lanePeg topStep topBody withHole
  rfl


/-- Emitted `Ecbs.lane_fold`: the inlined geometry is `laneFoldStep` / `foldPeg`,
    both hole branches are `foldLoop`, and the scan is `topScan`. `lane_fold_refines`
    then reads this as `Spec.laneFold`. -/
theorem lane_fold_eq (xs : List Nat) (w h r n k benchlen : Nat) (b : Ecbs.Board)
    (hfit : FitsLen xs.length)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat benchlen) :
    Ecbs.lane_fold b (embed xs) =
      laneFoldGo w h r n k (Int.ofNat benchlen) b (embed xs) := by
  rw [laneFold_emit, hw, hh, hr, hn, hk, hbl]
  unfold laneFoldEmit laneFoldGo
  simp only [descBlock_emit, except_bind_pure]
  rw [top_scan_refines xs hfit, ok_bind]
  exact top_join xs hfit
    (fun top =>
      if decide (top > b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) = true then
        (do
          SudoRt.sudoAssert (decide (top < Int.ofNat benchlen)) 515
          foldLoop w h r n k (embed xs) (withHole b top) (Int.ofNat n))
      else
        (do
          SudoRt.sudoAssert (decide (top < Int.ofNat benchlen)) 515
          foldLoop w h r n k (embed xs) b (Int.ofNat n)))
    (fun r => pure r)

end EcbsLink2.Link2
