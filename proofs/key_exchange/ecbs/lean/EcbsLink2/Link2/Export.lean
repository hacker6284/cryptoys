/-
  Exported `multiply` and `cube_number`: `new_board`, `put`, `mul` or `cube`,
  `settle`, `value`. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.BoardBuild
import EcbsLink2.Link2.Cube
import EcbsLink2.Link2.Mul

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem set_reset_bool :
    (((Array.mkArray 8 false).set ⟨6, by simp [Array.size_mkArray]⟩ true).set
        ⟨6, by simp [Array.size_set, Array.size_mkArray]⟩ false) =
      Array.mkArray 8 false := by
  apply Array.ext
  · simp [Array.size_set, Array.size_mkArray]
  · intro i h1 h2
    simp [Array.getElem_set, Array.getElem_mkArray]

private theorem set_reset_home (xs : Array Int) :
    (((Array.mkArray 8 (#[] : Array Int)).set ⟨6, by simp [Array.size_mkArray]⟩ xs).set
        ⟨6, by simp [Array.size_set, Array.size_mkArray]⟩ (#[] : Array Int)) =
      Array.mkArray 8 (#[] : Array Int) := by
  apply Array.ext
  · simp [Array.size_set, Array.size_mkArray]
  · intro i h1 h2
    by_cases hi : i = 6
    · simp [hi, Array.getElem_set, Array.getElem_mkArray]
    · simp only [Array.getElem_set]
      split
      · rename_i heq
        exact absurd heq.symm hi
      · simp only [Array.getElem_set, Array.getElem_mkArray, hi]

private theorem built_held (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4held = Array.mkArray 8 false := by
  simp [builtBoard, midBoard, placed, blankOf, set_reset_bool]

private theorem built_home (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4home = Array.mkArray 8 (#[] : Array Int) := by
  simp [builtBoard, midBoard, placed, blankOf, set_reset_home]

private theorem built_moves (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_5moves = 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

private theorem built_peak (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_4peak = 1 := by
  simp [builtBoard, midBoard, placed, blankOf]

private theorem built_ops0 (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0 := by
  simp [builtBoard, midBoard, placed, blankOf]

private theorem countHeld_across :
    countHeld ((Array.mkArray 8 false).set ⟨0, by simp [Array.size_mkArray]⟩ true) 7 = 1 := by
  decide

private theorem across_home (t : Spec.Tier) : 0 < (builtBoard t).sudo_5Board_4home.size := by
  rw [built_home]
  simp [Array.size_mkArray]

private theorem across_held (t : Spec.Tier) : 0 < (builtBoard t).sudo_5Board_4held.size := by
  rw [built_held]
  simp [Array.size_mkArray]

private theorem put_built_across (t : Spec.Tier) (h : BoardOk t) (xs : List Nat)
    (hx : xs.length = t.n) (hf : FitsLen (pegCount xs)) :
    Ecbs.put (builtBoard t) ((0 : Nat) : Int) (embed xs) =
      .ok (placeBoard (builtBoard t) 0 (across_home t) (across_held t) xs 0 1) := by
  have hfn : FitsLen t.n := FitsLen.of_le (fits_of h.fits_n) (by omega)
  rw [put_refines (builtBoard t) 0 xs 0 1 (across_home t) (across_held t)
    (by simp [built_held, Array.size_mkArray])
    (by simp [built_held, Array.getElem_mkArray])
    (by
      have ht : (builtBoard t).sudo_5Board_1t = embTier t := by
        simp [builtBoard, midBoard, placed, blankOf]
      rw [ht, hx]
      exact ofNat_eq_natCast _)
    (by rw [hx]; exact hfn)
    (by simp [built_moves])
    (by simp [built_peak])
    (by simpa [Nat.zero_add] using hf)]

private theorem place_across_peak (t : Spec.Tier) (xs : List Nat)
    (hH : 0 < (builtBoard t).sudo_5Board_4home.size)
    (hD : 0 < (builtBoard t).sudo_5Board_4held.size) :
    placeBoard (builtBoard t) 0 hH hD xs 0 1 =
      { builtBoard t with
        sudo_5Board_4home := (builtBoard t).sudo_5Board_4home.set ⟨0, hH⟩ (embed xs)
        sudo_5Board_4held := (builtBoard t).sudo_5Board_4held.set ⟨0, hD⟩ true
        sudo_5Board_4cost := { (builtBoard t).sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (pegCount xs) } } := by
  unfold placeBoard
  dsimp only
  have hocc : countHeld ((builtBoard t).sudo_5Board_4held.set ⟨0, hD⟩ true) 7 = 1 := by
    simpa [← built_held] using countHeld_across
  rw [hocc]
  simp [Nat.zero_add, show ¬ ((1 : Nat) < 1) from by decide]

private theorem countHeld_two :
    countHeld ((((Array.mkArray 8 false).set ⟨0, by simp [Array.size_mkArray]⟩ true).set
        ⟨1, by simp [Array.size_set, Array.size_mkArray]⟩ true)) 7 = 2 := by
  decide

/-- Across written, peak still 1, moves equal to the nonzero count. -/
def boardAcross (t : Spec.Tier) (xs : List Nat) : Ecbs.Board :=
  let b := builtBoard t
  { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨0, across_home t⟩ (embed xs)
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨0, across_held t⟩ true
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (pegCount xs) } }

private theorem boardAcross_eq (t : Spec.Tier) (xs : List Nat) :
    placeBoard (builtBoard t) 0 (across_home t) (across_held t) xs 0 1 = boardAcross t xs := by
  rw [place_across_peak]
  rfl

/-- A sum bounded by the schoolbook of a million-trit number, plus a short bench, fits an i64. -/
private theorem fits_budget {k : Nat}
    (hk : k ≤ 1000000 * 1000001 + 10 * 1000001) : FitsLen k := by
  have hbig : FitsLen (1000000 * 1000001 + 10 * 1000001) := by
    unfold FitsLen i64MaxNat
    decide
  exact FitsLen.of_le hbig hk

private theorem coeff_at (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    coeff xs i = xs[i] := by
  simp [coeff, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem array_get_congr {α : Type} {a b : Array α} (h : a = b) (i : Nat)
    (ha : i < a.size) : a[i] = b[i]'(h ▸ ha) := by
  induction h
  rfl

/-- Layout `Spec.fieldMul` and `Ecbs.mul` both assume, on top of `BoardOk`.
    `n`, `k`, `w`, `h`, `r` are the tier's own fields. The million bound is the
    one `mul_refines` uses for the schoolbook fuel. -/
structure FieldLay (t : Spec.Tier) : Prop where
  board : BoardOk t
  w_pos : 0 < t.w
  h_pos : 0 < t.h
  r_pos : 0 < t.r
  r_lt : t.r < t.h
  n_eq : t.n = t.w * t.h - 1
  k_le : t.k ≤ t.n
  gap_eq : t.n - t.k = t.w * t.r
  mul_span : 2 * (t.n - 1) < t.benchlen
  small : t.w ≤ 1000000 ∧ t.h ≤ 1000000 ∧ t.r ≤ 1000000 ∧ t.benchlen ≤ 1000001
  n_small : t.n ≤ 1000000

theorem demo_lay : FieldLay Spec.demo := by
  refine ⟨demo_board, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

theorem toy_lay : FieldLay Spec.toy := by
  refine ⟨toy_board, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

theorem hobby_lay : FieldLay Spec.hobby := by
  refine ⟨hobby_board, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

theorem serious_lay : FieldLay Spec.serious := by
  refine ⟨serious_board, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

private theorem up_home (t : Spec.Tier) (xs : List Nat) :
    1 < (boardAcross t xs).sudo_5Board_4home.size := by
  simp [boardAcross, built_home, Array.size_set, Array.size_mkArray]

private theorem up_held (t : Spec.Tier) (xs : List Nat) :
    1 < (boardAcross t xs).sudo_5Board_4held.size := by
  simp [boardAcross, built_held, Array.size_set, Array.size_mkArray]

private theorem up_occ (t : Spec.Tier) (xs : List Nat) :
    countHeld ((boardAcross t xs).sudo_5Board_4held.set ⟨1, up_held t xs⟩ true) 7 = 2 := by
  simp only [boardAcross, built_held]
  exact countHeld_two

/-- Up written on the across board. Two homes are held, so the peak rises from 1 to 2.
    Moves are the two nonzero counts. -/
def boardUp (t : Spec.Tier) (xs ys : List Nat) : Ecbs.Board :=
  let b := boardAcross t xs
  { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨1, up_home t xs⟩ (embed ys)
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨1, up_held t xs⟩ true
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (pegCount xs + pegCount ys)
      sudo_5Costs_4peak := Int.ofNat 2 } }

private theorem place_up_peak (t : Spec.Tier) (xs ys : List Nat) :
    placeBoard (boardAcross t xs) 1 (up_home t xs) (up_held t xs) ys (pegCount xs) 1 =
      boardUp t xs ys := by
  unfold placeBoard
  dsimp only
  rw [up_occ t xs, if_pos (by decide : (1 : Nat) < 2)]
  rfl

private theorem put_up (t : Spec.Tier) (xs ys : List Nat)
    (hy : ys.length = t.n)
    (hfn : FitsLen t.n) (hf : FitsLen (pegCount xs + pegCount ys)) :
    Ecbs.put (boardAcross t xs) ((1 : Nat) : Int) (embed ys) = .ok (boardUp t xs ys) := by
  rw [put_refines (boardAcross t xs) 1 ys (pegCount xs) 1 (up_home t xs) (up_held t xs)
    (by simp [boardAcross, built_held, Array.size_set, Array.size_mkArray])
    (by simp [boardAcross, built_held, Array.getElem_set, Array.getElem_mkArray])
    (by
      have ht : (boardAcross t xs).sudo_5Board_1t = embTier t := by
        simp [boardAcross, builtBoard, midBoard, placed, blankOf]
      rw [ht, hy]
      exact ofNat_eq_natCast _)
    (by rw [hy]; exact hfn)
    (by simp [boardAcross, ofNat_eq_natCast])
    (by simp [boardAcross, built_peak, ofNat_eq_natCast])
    hf, place_up_peak]

private theorem up_tier (t : Spec.Tier) (xs ys : List Nat) :
    (boardUp t xs ys).sudo_5Board_1t = embTier t := by
  simp [boardUp, boardAcross, builtBoard, midBoard, placed, blankOf]

private theorem up_off (t : Spec.Tier) (xs ys : List Nat) :
    (boardUp t xs ys).sudo_5Board_9marker_on = false ∧
    (boardUp t xs ys).sudo_5Board_8bench_on = false ∧
    (boardUp t xs ys).sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0 ∧
    (boardUp t xs ys).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0 ∧
    (boardUp t xs ys).sudo_5Board_4cost.sudo_5Costs_6slides = 0 := by
  simp [boardUp, boardAcross, builtBoard, midBoard, placed, blankOf]

private theorem up_ops (t : Spec.Tier) (xs ys : List Nat) :
    (boardUp t xs ys).sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0 := by
  simp [boardUp, boardAcross, built_ops0]

private theorem up_sz (t : Spec.Tier) (xs ys : List Nat) :
    (boardUp t xs ys).sudo_5Board_4held.size = 8 ∧
    (boardUp t xs ys).sudo_5Board_4home.size = 8 := by
  simp [boardUp, boardAcross, built_held, built_home, Array.size_set, Array.size_mkArray]

private theorem up_at0 (t : Spec.Tier) (xs ys : List Nat)
    (_hD : 0 < (boardUp t xs ys).sudo_5Board_4held.size)
    (hH : 0 < (boardUp t xs ys).sudo_5Board_4home.size) :
    (boardUp t xs ys).sudo_5Board_4held[0] = true ∧
    (boardUp t xs ys).sudo_5Board_4home[0] = embed xs := by
  simp [boardUp, boardAcross, built_held, built_home, Array.getElem_set, Array.getElem_mkArray]

private theorem up_at1 (t : Spec.Tier) (xs ys : List Nat)
    (hD : 1 < (boardUp t xs ys).sudo_5Board_4held.size)
    (hH : 1 < (boardUp t xs ys).sudo_5Board_4home.size) :
    (boardUp t xs ys).sudo_5Board_4held[1] = true ∧
    (boardUp t xs ys).sudo_5Board_4home[1] = embed ys := by
  simp [boardUp, Array.getElem_set]

private theorem up_spare (t : Spec.Tier) (xs ys : List Nat)
    (_hD : 6 < (boardUp t xs ys).sudo_5Board_4held.size) :
    (boardUp t xs ys).sudo_5Board_4held[6] = false := by
  simp [boardUp, boardAcross, built_held, Array.getElem_set, Array.getElem_mkArray]

/-- `multiply`: `new_board`, across `put`, up `put` (peak 1 → 2), `mul`, `settle`, `value`.
    The array is the embedded `Spec.fieldMul` of the two length-`n` inputs. `xs` is a trit
    list because the lane fold's trit invariant is; `ys` is any length-`n` list. -/
theorem multiply_refines (t : Spec.Tier) (lay : FieldLay t) (xs ys : List Nat)
    (hx : xs.length = t.n) (hy : ys.length = t.n) (hxs : allTritList xs) :
    Ecbs.multiply (embTier t) (embed xs) (embed ys) =
      .ok (embed (fieldMul t.n t.k t.benchlen xs ys)) := by
  let n := t.n
  let k := t.k
  let w := t.w
  let h := t.h
  let r := t.r
  let bench := t.benchlen
  let px := pegCount xs
  let py := pegCount ys
  have hpx : px ≤ n := by simpa [px, n, hx] using pegCount_le xs
  have hpy : py ≤ n := by simpa [py, n, hy] using pegCount_le ys
  have hnsm : n ≤ 1000000 := lay.n_small
  have hbnd : bench ≤ 1000001 := lay.small.2.2.2
  have hnb : n ≤ bench := by have := lay.mul_span; omega
  have hprod : n * (n + 1) ≤ 1000000 * 1000001 := Nat.mul_le_mul hnsm (by omega)
  have hcap : px + py + py + n * (n + 1) + 3 * bench ≤
      1000000 * 1000001 + 10 * 1000001 := by omega
  have hfn : FitsLen n := fits_small hnsm
  have hfitC : FitsLen ((px + py) + py) := fits_budget (by omega)
  have hfm : FitsLen ((px + py) + py + n * (n + 1)) := fits_budget (by omega)
  have hfold : FitsLen ((px + py) + py + n * (n + 1) + 3 * (bench - n)) :=
    fits_budget (by omega)
  have hfitB : FitsLen bench := fits_budget (by omega)
  have hfi : FitsLen (2 * (n - 1)) := fits_budget (by omega)
  have hpeg2 : FitsLen (px + py) := fits_budget (by omega)
  unfold Ecbs.multiply
  rw [new_board_refines t lay.board]
  simp only [ok_bind, pure_eq_ok]
  have hAcross := put_built_across t lay.board xs hx (fits_budget (by omega))
  conv =>
    pattern (Ecbs.put _ Ecbs.across _)
    change Ecbs.put (builtBoard t) ((0 : Nat) : Int) (embed xs)
  rw [hAcross]
  simp only [ok_bind]
  rw [boardAcross_eq]
  have hUp := put_up t xs ys hy hfn hpeg2
  conv =>
    pattern (Ecbs.put _ Ecbs.up _)
    change Ecbs.put (boardAcross t xs) ((1 : Nat) : Int) (embed ys)
  rw [hUp]
  simp only [ok_bind]
  let bU := boardUp t xs ys
  have hHeld8 : bU.sudo_5Board_4held.size = 8 := by
    change (boardUp t xs ys).sudo_5Board_4held.size = 8
    exact (up_sz t xs ys).1
  have hHome8 : bU.sudo_5Board_4home.size = 8 := by
    change (boardUp t xs ys).sudo_5Board_4home.size = 8
    exact (up_sz t xs ys).2
  have hD0 : 0 < bU.sudo_5Board_4held.size := by rw [hHeld8]; decide
  have hH0 : 0 < bU.sudo_5Board_4home.size := by rw [hHome8]; decide
  have hD1 : 1 < bU.sudo_5Board_4held.size := by rw [hHeld8]; decide
  have hH1 : 1 < bU.sudo_5Board_4home.size := by rw [hHome8]; decide
  have hD6 : 6 < bU.sudo_5Board_4held.size := by rw [hHeld8]; decide
  have hH6 : 6 < bU.sudo_5Board_4home.size := by rw [hHome8]; decide
  have h7b : 7 ≤ bU.sudo_5Board_4held.size := by rw [hHeld8]; decide
  have hmul := mul_refines bU 5 0 1 xs ys w h r n k (px + py) 0 bench 2 0 0
    (up_off t xs ys).1 (up_off t xs ys).2.1
    (by simp [bU, up_ops, Array.size_mkArray])
    (by simp [bU, up_ops, Array.getElem_mkArray, ofNat_eq_natCast])
    (fits_small (by decide))
    (by rw [up_tier]; rfl)
    hD0 hH0 (up_at0 t xs ys hD0 hH0).1 (up_at0 t xs ys hD0 hH0).2
    hD1 hH1 (up_at1 t xs ys hD1 hH1).1 (up_at1 t xs ys hD1 hH1).2
    hD6 hH6 (up_spare t xs ys hD6) h7b
    (by decide) (by decide)
    lay.board.n_pos
    (by rw [up_tier]; exact ofNat_eq_natCast _)
    hx hy hfn
    (by simp [bU, boardUp, ofNat_eq_natCast])
    (by simp [bU, boardUp, ofNat_eq_natCast])
    (by
      have := (up_off t xs ys).2.2.1
      simpa [bU, ofNat_eq_natCast] using this)
    hfitC lay.mul_span hxs hfi hfm
    lay.w_pos lay.h_pos lay.r_lt lay.r_pos lay.n_eq lay.k_le lay.gap_eq
    (by rw [up_tier]; rfl)
    (by rw [up_tier]; rfl)
    (by rw [up_tier]; rfl)
    (by rw [up_tier]; rfl)
    (by
      have := (up_off t xs ys).2.2.2.1
      simpa [bU, ofNat_eq_natCast] using this)
    lay.small hnsm hfitB hfold
  obtain ⟨b', hok, hon, hto, hbench, htake, htail⟩ := hmul
  obtain ⟨hhigh, hmov, hpeakM, hslides, ht, hhome, hheld⟩ := htail
  conv =>
    pattern (Ecbs.mul _ _ _ _ _ _ _)
    change Ecbs.mul bU ((5 : Nat) : Int) ((0 : Nat) : Int) ((1 : Nat) : Int) true false false
  rw [hok]
  simp only [ok_bind, pure_eq_ok]
  let sch := school n xs ys (List.replicate bench 0) false
  let lane := laneFold n (n - k) sch
  have hlenS : sch.length = bench := by
    simpa [sch, List.length_replicate] using
      school_length xs ys (List.replicate bench 0) false n
  have hlenL : lane.length = bench := by
    simpa [lane, hlenS] using laneFold_length n (n - k) sch (by rw [hlenS]; exact hnb)
  have h5H : 5 < b'.sudo_5Board_4home.size := by
    rw [hhome]
    simp [bU, boardUp, boardAcross, built_home, Array.size_set, Array.size_mkArray]
  have h5D : 5 < b'.sudo_5Board_4held.size := by
    rw [hheld, Array.size_set, Array.size_set]
    simp [bU, boardUp, boardAcross, built_held, Array.size_set, Array.size_mkArray]
  have h7' : 7 ≤ b'.sudo_5Board_4held.size := by
    rw [hheld, Array.size_set, Array.size_set, hHeld8]
    decide
  have hempty : b'.sudo_5Board_4held[5] = false := by
    have hpre : 5 <
        ((bU.sudo_5Board_4held.set ⟨6, by
            simp [bU, boardUp, boardAcross, built_held, Array.size_set, Array.size_mkArray]⟩ true).set
          ⟨6, by rw [Array.size_set]; simp [bU, boardUp, boardAcross, built_held,
            Array.size_set, Array.size_mkArray]⟩ false).size := by
      simp [Array.size_set, bU, boardUp, boardAcross, built_held, Array.size_mkArray]
    have hget := array_get_congr hheld.symm 5 hpre
    rw [← hget]
    simp [Array.getElem_set, bU, boardUp, boardAcross, built_held, Array.getElem_mkArray]
  have hslides0 : b'.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat 0 := by
    rw [hslides]
    simp [bU, boardUp, boardAcross, builtBoard, midBoard, placed, blankOf, ofNat_eq_natCast]
  have hn' : b'.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [ht]
    change (boardUp t xs ys).sudo_5Board_1t.sudo_4Tier_1n = (n : Int)
    rw [up_tier]
    exact ofNat_eq_natCast _
  have hpegN : pegCount (lane.take n) ≤ n := by
    have hle := pegCount_le (lane.take n)
    rw [List.length_take, hlenL] at hle
    exact Nat.le_trans hle (Nat.min_le_left _ _)
  have hmovN : mulMoves (px + py) xs ys n k bench + 2 * pegCount (lane.take n) ≤
      1000000 * 1000001 + 10 * 1000001 := by
    have hsch : schoolMoves xs ys n n ≤ n * (n + 1) := schoolMoves_bound xs ys n
    have hfc : foldCharge n (n - k) sch ≤ 3 * (sch.length - n) := foldCharge_bound _ _ _
    simp only [mulMoves, sch] at *
    rw [hlenS] at hfc
    omega
  have hread := folded_read b' 5 lane n (mulMoves (px + py) xs ys n k bench) 0
      (mulPeak bU.sudo_5Board_4held b'.sudo_5Board_4held hD6 2)
      h5H h5D h7' hon
      (by simpa using hto)
      hempty
      (by simpa [lane, sch] using hbench)
      hn'
      (by rw [hlenL]; have := lay.mul_span; omega)
      (by rw [hlenL]; exact hnb)
      (by
        intro i hi hii
        have hib : i < bench := by rw [hlenL] at hii; exact hii
        have hc := hhigh i hi hib
        rw [coeff_at lane i hii] at hc
        exact hc)
      hfn (by rw [hlenL]; exact hfitB)
      hmov hslides0
      hpeakM
      (fits_budget (by omega))
      (fits_budget hmovN)
      (fits_budget (by omega))
  conv =>
    lhs
    arg 2
    intro _io
    arg 2
    intro _v
    rw [← pure_eq_ok]
  conv =>
    lhs
    arg 2
    intro _io
    rw [except_bind_pure]
  rw [show Ecbs.gap = ((5 : Nat) : Int) from rfl]
  rw [hread]
  change Except.ok (embed (List.take n (laneFold n (n - k) sch))) = _
  rw [htake]

private theorem ax_tier (t : Spec.Tier) (xs : List Nat) :
    (boardAcross t xs).sudo_5Board_1t = embTier t := by
  simp [boardAcross, builtBoard, midBoard, placed, blankOf]

private theorem ax_off (t : Spec.Tier) (xs : List Nat) :
    (boardAcross t xs).sudo_5Board_9marker_on = false ∧
    (boardAcross t xs).sudo_5Board_8bench_on = false ∧
    (boardAcross t xs).sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0 ∧
    (boardAcross t xs).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0 ∧
    (boardAcross t xs).sudo_5Board_4cost.sudo_5Costs_6slides = 0 := by
  simp [boardAcross, builtBoard, midBoard, placed, blankOf]

private theorem ax_ops (t : Spec.Tier) (xs : List Nat) :
    (boardAcross t xs).sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0 := by
  simp [boardAcross, built_ops0]

private theorem ax_sz (t : Spec.Tier) (xs : List Nat) :
    (boardAcross t xs).sudo_5Board_4held.size = 8 ∧
    (boardAcross t xs).sudo_5Board_4home.size = 8 := by
  simp [boardAcross, built_held, built_home, Array.size_set, Array.size_mkArray]

private theorem ax_at0 (t : Spec.Tier) (xs : List Nat)
    (_hD : 0 < (boardAcross t xs).sudo_5Board_4held.size)
    (hH : 0 < (boardAcross t xs).sudo_5Board_4home.size) :
    (boardAcross t xs).sudo_5Board_4held[0] = true ∧
    (boardAcross t xs).sudo_5Board_4home[0] = embed xs := by
  simp [boardAcross, built_held, built_home, Array.getElem_set, Array.getElem_mkArray]

/-- `cube_number`: `new_board`, across `put`, `cube` of that home onto itself, `settle`, `value`.
    The array is embedded `Spec.fieldCube`. The comb reach `3·(n−1) + combgap < benchlen` is
    the check the emitted cube asserts. -/
theorem cube_number_refines (t : Spec.Tier) (lay : FieldLay t) (xs : List Nat)
    (hx : xs.length = t.n) (hxs : allTritList xs)
    (hspan : 3 * (t.n - 1) + t.combgap < t.benchlen) :
    Ecbs.cube_number (embTier t) (embed xs) =
      .ok (embed (fieldCube t.n t.k t.benchlen xs)) := by
  let n := t.n
  let k := t.k
  let w := t.w
  let h := t.h
  let r := t.r
  let bench := t.benchlen
  let cg := t.combgap
  let px := pegCount xs
  have hpx : px ≤ n := by simpa [px, n, hx] using pegCount_le xs
  have hnsm : n ≤ 1000000 := lay.n_small
  have hbnd : bench ≤ 1000001 := lay.small.2.2.2
  have hnb : n ≤ bench := by have := lay.mul_span; omega
  have hprod : n * (n + 1) ≤ 1000000 * 1000001 := Nat.mul_le_mul hnsm (by omega)
  have hfn : FitsLen n := fits_small hnsm
  have h3 : FitsLen (3 * (n - 1)) := fits_budget (by omega)
  have hfm : FitsLen (px + 2 * n) := fits_budget (by omega)
  have hfold : FitsLen (px + 2 * n + 3 * (bench - n)) := fits_budget (by omega)
  have hfitB : FitsLen bench := fits_budget (by omega)
  have hpeg : FitsLen px := fits_budget (by omega)
  unfold Ecbs.cube_number
  rw [new_board_refines t lay.board]
  simp only [ok_bind, pure_eq_ok]
  have hAcross := put_built_across t lay.board xs hx hpeg
  conv =>
    pattern (Ecbs.put _ Ecbs.across _)
    change Ecbs.put (builtBoard t) ((0 : Nat) : Int) (embed xs)
  rw [hAcross]
  simp only [ok_bind]
  rw [boardAcross_eq]
  let bA := boardAcross t xs
  have hHeld8 : bA.sudo_5Board_4held.size = 8 := by
    change (boardAcross t xs).sudo_5Board_4held.size = 8
    exact (ax_sz t xs).1
  have hHome8 : bA.sudo_5Board_4home.size = 8 := by
    change (boardAcross t xs).sudo_5Board_4home.size = 8
    exact (ax_sz t xs).2
  have hD0 : 0 < bA.sudo_5Board_4held.size := by rw [hHeld8]; decide
  have hH0 : 0 < bA.sudo_5Board_4home.size := by rw [hHome8]; decide
  have h7b : 7 ≤ bA.sudo_5Board_4held.size := by rw [hHeld8]; decide
  have hcube := cube_refines bA 0 0 xs w h r n k px 0 bench 1 0 0 cg
    (ax_off t xs).1 (ax_off t xs).2.1
    (by simp [bA, ax_ops, Array.size_mkArray])
    (by simp [bA, ax_ops, Array.getElem_mkArray, ofNat_eq_natCast])
    (fits_small (by decide))
    (by rw [ax_tier]; rfl)
    (by rw [ax_tier]; rfl)
    hspan
    hD0 hH0 (ax_at0 t xs hD0 hH0).1 (ax_at0 t xs hD0 hH0).2
    h7b lay.board.n_pos
    (by rw [ax_tier]; exact ofNat_eq_natCast _)
    hx hfn
    (by simp [bA, boardAcross, ofNat_eq_natCast])
    (by simp [bA, boardAcross, built_peak, ofNat_eq_natCast])
    (by
      have := (ax_off t xs).2.2.1
      simpa [bA, ofNat_eq_natCast] using this)
    hxs h3 hfm
    lay.w_pos lay.h_pos lay.r_lt lay.r_pos lay.n_eq lay.k_le lay.gap_eq
    (by rw [ax_tier]; rfl) (by rw [ax_tier]; rfl) (by rw [ax_tier]; rfl) (by rw [ax_tier]; rfl)
    (by
      have := (ax_off t xs).2.2.2.1
      simpa [bA, ofNat_eq_natCast] using this)
    lay.small hnsm hfitB hfold
  obtain ⟨b', hok, hon, hto, hbench, _htake, hhigh, hmov, hpeakM, hslides, ht, hhome, _hhomeArr, hheld, _hmk', _hrow', _hop',
      _htally', _hhigh', _hctrl'⟩ :=
    hcube
  conv =>
    pattern (Ecbs.cube _ _ _)
    change Ecbs.cube bA ((0 : Nat) : Int) ((0 : Nat) : Int)
  rw [hok]
  simp only [ok_bind, pure_eq_ok]
  let sch := combStrip n bench xs
  let lane := laneFold n (n - k) sch
  have hlenS : sch.length = bench := by
    simp [sch, combStrip_length]
  have hlenL : lane.length = bench := by
    simpa [lane, hlenS] using laneFold_length n (n - k) sch (by rw [hlenS]; exact hnb)
  have h0H : 0 < b'.sudo_5Board_4home.size := by rw [hhome, hHome8]; decide
  have h0D : 0 < b'.sudo_5Board_4held.size := by
    rw [hheld, Array.size_set, hHeld8]; decide
  have h7' : 7 ≤ b'.sudo_5Board_4held.size := by rw [hheld, Array.size_set, hHeld8]; decide
  have hempty : b'.sudo_5Board_4held[0] = false := by
    have hpre : 0 < (bA.sudo_5Board_4held.set ⟨0, hD0⟩ false).size := by
      simp [Array.size_set, hHeld8]
    have hget := array_get_congr hheld.symm 0 hpre
    rw [← hget]
    simp [Array.getElem_set]
  have hslides0 : b'.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat 0 := by
    rw [hslides]
    simp [bA, boardAcross, builtBoard, midBoard, placed, blankOf, ofNat_eq_natCast]
  have hn' : b'.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    rw [ht]
    change (boardAcross t xs).sudo_5Board_1t.sudo_4Tier_1n = (n : Int)
    rw [ax_tier]
    exact ofNat_eq_natCast _
  have hpegN : pegCount (lane.take n) ≤ n := by
    have hle := pegCount_le (lane.take n)
    rw [List.length_take, hlenL] at hle
    exact Nat.le_trans hle (Nat.min_le_left _ _)
  have hmovN : cubeMoves px xs n k bench + 2 * pegCount (lane.take n) ≤
      1000000 * 1000001 + 10 * 1000001 := by
    have hlaid : laidCount xs n ≤ n := laidCount_le xs n
    have hfc : foldCharge n (n - k) sch ≤ 3 * (sch.length - n) := foldCharge_bound _ _ _
    simp only [cubeMoves, sch] at *
    rw [hlenS] at hfc
    omega
  have hread := folded_read b' 0 lane n (cubeMoves px xs n k bench) 0
      (raisedPeak 1 (countHeld (bA.sudo_5Board_4held.set ⟨0, hD0⟩ false) 7))
      h0H h0D h7' hon hto hempty
      (by simpa [lane, sch] using hbench)
      hn'
      (by rw [hlenL]; have := lay.mul_span; omega)
      (by rw [hlenL]; exact hnb)
      (by
        intro i hi hii
        have hc := hhigh i hi (by rw [hlenL] at hii; exact hii)
        rw [coeff_at lane i hii] at hc
        exact hc)
      hfn (by rw [hlenL]; exact hfitB)
      hmov hslides0 hpeakM
      (fits_budget (by omega)) (fits_budget hmovN) (fits_budget (by omega))
  conv =>
    lhs
    arg 2
    intro _io
    arg 2
    intro _v
    rw [← pure_eq_ok]
  conv =>
    lhs
    arg 2
    intro _io
    rw [except_bind_pure]
  rw [show Ecbs.across = ((0 : Nat) : Int) from rfl]
  rw [hread]
  change Except.ok (embed (List.take n (laneFold n (n - k) sch))) = _
  unfold fieldCube
  rfl

end EcbsLink2.Link2
