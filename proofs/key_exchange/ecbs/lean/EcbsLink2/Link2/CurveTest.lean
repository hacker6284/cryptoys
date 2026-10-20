/-
  `curve_test` puts `x` at base across (home 3) and `y` at base up (home 4).
-/
import EcbsLink2.Link2.OneField
import EcbsLink2.Link2.Export
import EcbsLink2.Link2.MulSettle
import EcbsLink2.Link2.Add

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

private theorem n_le_four (n : Nat) : n ≤ 4 * n + 8 := by omega

private theorem two_pegs (n a b : Nat) (ha : a ≤ n) (hb : b ≤ n) : a + b ≤ 4 * n + 8 := by
  omega

private theorem home_lt (t : Spec.Tier) (i : Nat) (hi : i < 8) :
    i < (builtBoard t).sudo_5Board_4home.size := by
  rw [built_home_blank]
  simp [Array.size_mkArray, hi]

private theorem held_lt (t : Spec.Tier) (i : Nat) (hi : i < 8) :
    i < (builtBoard t).sudo_5Board_4held.size := by
  rw [built_held_blank]
  simp [Array.size_mkArray, hi]

private theorem held_false (t : Spec.Tier) (i : Nat) (hi : i < 8) :
    (builtBoard t).sudo_5Board_4held[i]'(held_lt t i hi) = false := by
  simp [built_held_blank, Array.getElem_mkArray]

private theorem count_one (t : Spec.Tier)
    (hD : 3 < (builtBoard t).sudo_5Board_4held.size) :
    countHeld ((builtBoard t).sudo_5Board_4held.set ⟨3, hD⟩ true) 7 = 1 := by
  have hclosed :
      countHeld ((Array.mkArray 8 false).set ⟨3, by simp [Array.size_mkArray]⟩ true) 7 = 1 := by
    decide
  have hs : (builtBoard t).sudo_5Board_4held.set ⟨3, hD⟩ true =
      (Array.mkArray 8 false).set ⟨3, by simp [Array.size_mkArray]⟩ true := by
    apply Array.ext
    · simp [built_held_blank, Array.size_set, Array.size_mkArray]
    · intro i hi hi'
      simp [built_held_blank, Array.getElem_set]
  rw [hs, hclosed]

def baseAcrossBoard (t : Spec.Tier) (x : List Nat)
    (hH : 3 < (builtBoard t).sudo_5Board_4home.size)
    (hD : 3 < (builtBoard t).sudo_5Board_4held.size) : Ecbs.Board :=
  { builtBoard t with
    sudo_5Board_4home := (builtBoard t).sudo_5Board_4home.set ⟨3, hH⟩ (embed x)
    sudo_5Board_4held := (builtBoard t).sudo_5Board_4held.set ⟨3, hD⟩ true
    sudo_5Board_4cost := { (builtBoard t).sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (pegCount x) } }

private theorem place_across (t : Spec.Tier) (x : List Nat)
    (hH : 3 < (builtBoard t).sudo_5Board_4home.size)
    (hD : 3 < (builtBoard t).sudo_5Board_4held.size) :
    placeBoard (builtBoard t) 3 hH hD x 0 1 = baseAcrossBoard t x hH hD := by
  unfold placeBoard baseAcrossBoard
  simp [count_one t hD, show ¬ ((1 : Nat) < 1) from by decide]

theorem put_base_across (t : Spec.Tier) (hOk : BoardOk t) (x : List Nat)
    (hx : x.length = t.n) :
    Ecbs.put (builtBoard t) Ecbs.base_across (embed x) =
      .ok (baseAcrossBoard t x (home_lt t 3 (by decide)) (held_lt t 3 (by decide))) := by
  have hfn : FitsLen t.n := FitsLen.of_le (fits_of hOk.fits_n) (n_le_four t.n)
  have hpx : FitsLen (pegCount x) :=
    FitsLen.of_le (by rw [hx]; exact hfn) (pegCount_le x)
  have hput := put_refines (builtBoard t) 3 x 0 1
    (home_lt t 3 (by decide)) (held_lt t 3 (by decide)) (held7_le t)
    (held_false t 3 (by decide))
    (by rw [built_tier, hx]; exact ofNat_eq_natCast _)
    (by rw [hx]; exact hfn)
    (by rw [built_moves0]; rfl)
    (by rw [built_peak1]; rfl)
    (by simpa using hpx)
  rw [show Ecbs.base_across = ((3 : Nat) : Int) from rfl, hput, place_across]

theorem put_base_up (t : Spec.Tier) (hOk : BoardOk t) (x y : List Nat)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hH : 3 < (builtBoard t).sudo_5Board_4home.size)
    (hD : 3 < (builtBoard t).sudo_5Board_4held.size) :
    let b := baseAcrossBoard t x hH hD
    ∃ (hH4 : 4 < b.sudo_5Board_4home.size) (hD4 : 4 < b.sudo_5Board_4held.size),
      Ecbs.put b Ecbs.base_up (embed y) =
        .ok (placeBoard b 4 hH4 hD4 y (pegCount x) 1) := by
  intro b
  have hfn : FitsLen t.n := FitsLen.of_le (fits_of hOk.fits_n) (n_le_four t.n)
  have hpy : FitsLen (pegCount x + pegCount y) :=
    FitsLen.of_le (fits_of hOk.fits_n)
      (two_pegs t.n _ _ (by rw [← hx]; exact pegCount_le x) (by rw [← hy]; exact pegCount_le y))
  have hH4 : 4 < b.sudo_5Board_4home.size := by
    simp [b, baseAcrossBoard, built_home_blank, Array.size_set, Array.size_mkArray]
  have hD4 : 4 < b.sudo_5Board_4held.size := by
    simp [b, baseAcrossBoard, built_held_blank, Array.size_set, Array.size_mkArray]
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by
    simp [b, baseAcrossBoard, built_held_blank, Array.size_set, Array.size_mkArray]
  have hempty : b.sudo_5Board_4held[4] = false := by
    simp [b, baseAcrossBoard, built_held_blank, Array.getElem_set]
  refine ⟨hH4, hD4, ?_⟩
  rw [show Ecbs.base_up = ((4 : Nat) : Int) from rfl]
  exact put_refines b 4 y (pegCount x) 1 hH4 hD4 h7 hempty
    (by simp [b, baseAcrossBoard, built_tier, hy]; exact ofNat_eq_natCast _)
    (by rw [hy]; exact hfn)
    (by simp [b, baseAcrossBoard])
    (by simp [b, baseAcrossBoard, built_peak1])
    hpy

private theorem fits_budget {k : Nat}
    (hk : k ≤ 1000000 * 1000001 + 10 * 1000001) : FitsLen k := by
  have hbig : FitsLen (1000000 * 1000001 + 10 * 1000001) := by
    unfold FitsLen i64MaxNat
    decide
  exact FitsLen.of_le hbig hk

private theorem countHeld_34 :
    countHeld (((Array.mkArray 8 false).set ⟨3, by simp [Array.size_mkArray]⟩ true).set
      ⟨4, by simp [Array.size_set, Array.size_mkArray]⟩ true) 7 = 2 := by
  decide

private theorem curve_home4 (t : Spec.Tier) (x : List Nat) :
    4 < (baseAcrossBoard t x (home_lt t 3 (by decide)) (held_lt t 3 (by decide))).sudo_5Board_4home.size := by
  simp [baseAcrossBoard, built_home_blank, Array.size_set, Array.size_mkArray]

private theorem curve_held4 (t : Spec.Tier) (x : List Nat) :
    4 < (baseAcrossBoard t x (home_lt t 3 (by decide)) (held_lt t 3 (by decide))).sudo_5Board_4held.size := by
  simp [baseAcrossBoard, built_held_blank, Array.size_set, Array.size_mkArray]

private theorem curve_occ (t : Spec.Tier) (x : List Nat) :
    countHeld ((baseAcrossBoard t x (home_lt t 3 (by decide)) (held_lt t 3 (by decide))).sudo_5Board_4held.set
      ⟨4, curve_held4 t x⟩ true) 7 = 2 := by
  simp only [baseAcrossBoard, built_held_blank]
  exact countHeld_34

/-- Across at home 3, up at home 4. Two homes are held, so the peak is 2. -/
def boardCurve (t : Spec.Tier) (x y : List Nat) : Ecbs.Board :=
  let b := baseAcrossBoard t x (home_lt t 3 (by decide)) (held_lt t 3 (by decide))
  { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨4, curve_home4 t x⟩ (embed y)
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨4, curve_held4 t x⟩ true
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (pegCount x + pegCount y)
      sudo_5Costs_4peak := Int.ofNat 2 } }

private theorem place_curve (t : Spec.Tier) (x y : List Nat) :
    placeBoard (baseAcrossBoard t x (home_lt t 3 (by decide)) (held_lt t 3 (by decide)))
      4 (curve_home4 t x) (curve_held4 t x) y (pegCount x) 1 = boardCurve t x y := by
  unfold placeBoard
  dsimp only
  rw [curve_occ t x, if_pos (by decide : (1 : Nat) < 2)]
  rfl

theorem put_curve (t : Spec.Tier) (hOk : BoardOk t) (x y : List Nat)
    (hx : x.length = t.n) (hy : y.length = t.n) :
    Ecbs.put (baseAcrossBoard t x (home_lt t 3 (by decide)) (held_lt t 3 (by decide)))
        Ecbs.base_up (embed y) = .ok (boardCurve t x y) := by
  have hfn : FitsLen t.n := FitsLen.of_le (fits_of hOk.fits_n) (n_le_four t.n)
  have hpy : FitsLen (pegCount x + pegCount y) :=
    FitsLen.of_le (fits_of hOk.fits_n)
      (two_pegs t.n _ _ (by rw [← hx]; exact pegCount_le x) (by rw [← hy]; exact pegCount_le y))
  rw [show Ecbs.base_up = ((4 : Nat) : Int) from rfl,
    put_refines (baseAcrossBoard t x (home_lt t 3 (by decide)) (held_lt t 3 (by decide)))
      4 y (pegCount x) 1 (curve_home4 t x) (curve_held4 t x)
      (by simp [baseAcrossBoard, built_held_blank, Array.size_set, Array.size_mkArray])
      (by simp [baseAcrossBoard, built_held_blank, Array.getElem_set, Array.getElem_mkArray])
      (by simp [baseAcrossBoard, built_tier, hy]; exact ofNat_eq_natCast _)
      (by rw [hy]; exact hfn)
      (by simp [baseAcrossBoard])
      (by simp [baseAcrossBoard, built_peak1])
      hpy,
    place_curve]

private theorem curve_tier (t : Spec.Tier) (x y : List Nat) :
    (boardCurve t x y).sudo_5Board_1t = embTier t := by
  simp [boardCurve, baseAcrossBoard, builtBoard, midBoard, placed, blankOf]

private theorem curve_off (t : Spec.Tier) (x y : List Nat) :
    (boardCurve t x y).sudo_5Board_9marker_on = false ∧
    (boardCurve t x y).sudo_5Board_8bench_on = false ∧
    (boardCurve t x y).sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0 ∧
    (boardCurve t x y).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0 ∧
    (boardCurve t x y).sudo_5Board_4cost.sudo_5Costs_6slides = 0 := by
  simp [boardCurve, baseAcrossBoard, builtBoard, midBoard, placed, blankOf]

private theorem curve_ops (t : Spec.Tier) (x y : List Nat) :
    (boardCurve t x y).sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0 := by
  simp [boardCurve, baseAcrossBoard, built_ops_blank]

private theorem curve_sz (t : Spec.Tier) (x y : List Nat) :
    (boardCurve t x y).sudo_5Board_4held.size = 8 ∧
    (boardCurve t x y).sudo_5Board_4home.size = 8 := by
  simp [boardCurve, baseAcrossBoard, built_held_blank, built_home_blank,
    Array.size_set, Array.size_mkArray]

private theorem curve_at3 (t : Spec.Tier) (x y : List Nat)
    (_hD : 3 < (boardCurve t x y).sudo_5Board_4held.size)
    (_hH : 3 < (boardCurve t x y).sudo_5Board_4home.size) :
    (boardCurve t x y).sudo_5Board_4held[3] = true ∧
    (boardCurve t x y).sudo_5Board_4home[3] = embed x := by
  simp [boardCurve, baseAcrossBoard, built_held_blank, built_home_blank,
    Array.getElem_set, Array.getElem_mkArray]

private theorem curve_at4 (t : Spec.Tier) (x y : List Nat)
    (_hD : 4 < (boardCurve t x y).sudo_5Board_4held.size)
    (_hH : 4 < (boardCurve t x y).sudo_5Board_4home.size) :
    (boardCurve t x y).sudo_5Board_4held[4] = true ∧
    (boardCurve t x y).sudo_5Board_4home[4] = embed y := by
  simp [boardCurve, Array.getElem_set]

private theorem curve_blank5 (t : Spec.Tier) (x y : List Nat)
    (_hH : 5 < (boardCurve t x y).sudo_5Board_4home.size)
    (_hD : 5 < (boardCurve t x y).sudo_5Board_4held.size) :
    (boardCurve t x y).sudo_5Board_4home[5] = (#[] : Array Int) ∧
    (boardCurve t x y).sudo_5Board_4held[5] = false := by
  simp [boardCurve, baseAcrossBoard, built_home_blank, built_held_blank,
    Array.getElem_set, Array.getElem_mkArray]

private theorem curve_blank2 (t : Spec.Tier) (x y : List Nat)
    (_hH : 2 < (boardCurve t x y).sudo_5Board_4home.size)
    (_hD : 2 < (boardCurve t x y).sudo_5Board_4held.size) :
    (boardCurve t x y).sudo_5Board_4home[2] = (#[] : Array Int) ∧
    (boardCurve t x y).sudo_5Board_4held[2] = false := by
  simp [boardCurve, baseAcrossBoard, built_home_blank, built_held_blank,
    Array.getElem_set, Array.getElem_mkArray]

private theorem curve_spare (t : Spec.Tier) (x y : List Nat)
    (_hD : 6 < (boardCurve t x y).sudo_5Board_4held.size) :
    (boardCurve t x y).sudo_5Board_4held[6] = false := by
  simp [boardCurve, baseAcrossBoard, built_held_blank, Array.getElem_set, Array.getElem_mkArray]

/-- `on_curve`'s first bind: `mul` of the up by itself, into the gap.
    Homes 3 and 4 stay the across and the up. The product sits on the bench,
    and its length-`n` prefix is `y²`. -/
theorem curve_mul_gap (t : Spec.Tier) (lay : FieldLay t) (x y : List Nat)
    (hx : x.length = t.n) (hy : y.length = t.n) (hyT : allTritList y) :
    ∃ b',
      Ecbs.mul (boardCurve t x y) Ecbs.gap Ecbs.base_up Ecbs.base_up true false false = .ok b' ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = Ecbs.gap ∧
      b'.sudo_5Board_5bench =
        embed (laneFold t.n (t.n - t.k)
          (school t.n y y (List.replicate t.benchlen 0) false)) ∧
      (laneFold t.n (t.n - t.k)
          (school t.n y y (List.replicate t.benchlen 0) false)).take t.n =
        fieldMul t.n t.k t.benchlen y y ∧
      (∀ (h3 : 3 < b'.sudo_5Board_4home.size), b'.sudo_5Board_4home[3] = embed x) ∧
      (∀ (h4 : 4 < b'.sudo_5Board_4home.size), b'.sudo_5Board_4home[4] = embed y) ∧
      (∀ (h2 : 2 < b'.sudo_5Board_4home.size), b'.sudo_5Board_4home[2] = (#[] : Array Int)) ∧
      (∀ (h3 : 3 < b'.sudo_5Board_4held.size), b'.sudo_5Board_4held[3] = true) ∧
      (∀ (h4 : 4 < b'.sudo_5Board_4held.size), b'.sudo_5Board_4held[4] = true) ∧
      (∀ (h2 : 2 < b'.sudo_5Board_4held.size), b'.sudo_5Board_4held[2] = false) ∧
      b'.sudo_5Board_4home.size = 8 ∧
      b'.sudo_5Board_4held.size = 8 ∧
      (∀ (h5 : 5 < b'.sudo_5Board_4home.size),
        b'.sudo_5Board_4home[5] = (#[] : Array Int)) ∧
      (∀ (h5 : 5 < b'.sudo_5Board_4held.size), b'.sudo_5Board_4held[5] = false) ∧
      (∀ i, t.n ≤ i → i < t.benchlen →
        coeff (laneFold t.n (t.n - t.k)
          (school t.n y y (List.replicate t.benchlen 0) false)) i = 0) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves =
        (mulMoves (pegCount x + pegCount y) y y t.n t.k t.benchlen : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak =
        (mulPeak (boardCurve t x y).sudo_5Board_4held b'.sudo_5Board_4held
          (by
            have h8 := (curve_sz t x y).1
            rw [h8]; decide : 6 < (boardCurve t x y).sudo_5Board_4held.size) 2 : Int) ∧
      b'.sudo_5Board_1t = embTier t ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = 0 ∧
      b'.sudo_5Board_9marker_on = false ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops =
        (boardCurve t x y).sudo_5Board_4cost.sudo_5Costs_3ops.set
          ⟨0, by simp [curve_ops, Array.size_mkArray]⟩ 1 ∧
      b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        Int.ofNat (raisedPeak 0 (countHeld ((boardCurve t x y).sudo_5Board_4held.set
          ⟨6, by
            have h8 := (curve_sz t x y).1
            rw [h8]; decide⟩ true) 7)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        Int.ofNat (raisedHole 0 (topIdx
          (school t.n y y (List.replicate t.benchlen 0) false))) ∧
      (∀ (h6 : 6 < b'.sudo_5Board_4held.size), b'.sudo_5Board_4held[6] = false) ∧
      FitsLen (mulMoves (pegCount x + pegCount y) y y t.n t.k t.benchlen + pegCount x) := by
  let n := t.n
  let k := t.k
  let w := t.w
  let h := t.h
  let r := t.r
  let bench := t.benchlen
  let px := pegCount x
  let py := pegCount y
  have hpx : px ≤ n := by simpa [px, n, hx] using pegCount_le x
  have hpy : py ≤ n := by simpa [py, n, hy] using pegCount_le y
  have hnsm : n ≤ 1000000 := lay.n_small
  have hbnd : bench ≤ 1000001 := lay.small.2.2.2
  have hnb : n ≤ bench := by have := lay.mul_span; omega
  have hprod : n * (n + 1) ≤ 1000000 * 1000001 := Nat.mul_le_mul hnsm (by omega)
  have hfn : FitsLen n := fits_small hnsm
  have hfitC : FitsLen ((px + py) + py) := fits_budget (by omega)
  have hfm : FitsLen ((px + py) + py + n * (n + 1)) := fits_budget (by omega)
  have hfold : FitsLen ((px + py) + py + n * (n + 1) + 3 * (bench - n)) :=
    fits_budget (by omega)
  have hfitB : FitsLen bench := fits_budget (by omega)
  have hfi : FitsLen (2 * (n - 1)) := fits_budget (by omega)
  let bU := boardCurve t x y
  have hHeld8 : bU.sudo_5Board_4held.size = 8 := (curve_sz t x y).1
  have hHome8 : bU.sudo_5Board_4home.size = 8 := (curve_sz t x y).2
  have hD4 : 4 < bU.sudo_5Board_4held.size := by rw [hHeld8]; decide
  have hH4 : 4 < bU.sudo_5Board_4home.size := by rw [hHome8]; decide
  have hD3 : 3 < bU.sudo_5Board_4held.size := by rw [hHeld8]; decide
  have hH3 : 3 < bU.sudo_5Board_4home.size := by rw [hHome8]; decide
  have hD6 : 6 < bU.sudo_5Board_4held.size := by rw [hHeld8]; decide
  have hH6 : 6 < bU.sudo_5Board_4home.size := by rw [hHome8]; decide
  have h7b : 7 ≤ bU.sudo_5Board_4held.size := by rw [hHeld8]; decide
  have hmul := mul_refines bU 5 4 4 y y w h r n k (px + py) 0 bench 2 0 0 (curve_off t x y).1 (curve_off t x y).2.1 (by simp [bU, curve_ops, Array.size_mkArray]) (by simp [bU, curve_ops, Array.getElem_mkArray, ofNat_eq_natCast]) (fits_small (by decide)) (by rw [curve_tier]; rfl) hD4 hH4 (curve_at4 t x y hD4 hH4).1 (curve_at4 t x y hD4 hH4).2 hD4 hH4 (curve_at4 t x y hD4 hH4).1 (curve_at4 t x y hD4 hH4).2 hD6 hH6 (curve_spare t x y hD6) h7b (by decide) (by decide) lay.board.n_pos (by rw [curve_tier]; exact ofNat_eq_natCast _) hy hy hfn (by simp [bU, boardCurve, ofNat_eq_natCast]) (by simp [bU, boardCurve, ofNat_eq_natCast]) (by
      have := (curve_off t x y).2.2.1
      simpa [bU, ofNat_eq_natCast] using this) hfitC lay.mul_span hyT hfi hfm ⟨lay.w_pos, lay.h_pos, lay.r_lt, lay.r_pos, lay.n_eq, lay.k_le, lay.gap_eq⟩ (by rw [curve_tier]; rfl) (by rw [curve_tier]; rfl) (by rw [curve_tier]; rfl) (by rw [curve_tier]; rfl) (by
      have := (curve_off t x y).2.2.2.1
      simpa [bU, ofNat_eq_natCast] using this) lay.small hnsm hfitB hfold
  obtain ⟨b', hok, hon, hto, hbench, htake, htail⟩ := hmul
  obtain ⟨hhigh, hmov, hpeakM, hslides, ht, hhsz, hheld, _h5, hframe, _hmk, _hops,
      hstrict, hhole, _hmark, _hctrl, _hmx⟩ := htail
  have h2H : 2 < bU.sudo_5Board_4home.size := by rw [hHome8]; decide
  have h2D : 2 < bU.sudo_5Board_4held.size := by rw [hHeld8]; decide
  let sch := school n y y (List.replicate bench 0) false
  have hlenS : sch.length = bench := by
    simpa [sch, List.length_replicate] using school_length y y (List.replicate bench 0) false n
  have hmovFit : FitsLen (mulMoves (px + py) y y n k bench + px) := by
    have hsch : schoolMoves y y n n ≤ n * (n + 1) := schoolMoves_bound y y n
    have hfc : foldCharge n (n - k) sch ≤ 3 * (sch.length - n) := foldCharge_bound n (n - k) sch
    rw [hlenS] at hfc
    have hdef : mulMoves (px + py) y y n k bench =
        (px + py) + py + schoolMoves y y n n + foldCharge n (n - k) sch := rfl
    exact fits_budget (by omega)
  have h5H : 5 < bU.sudo_5Board_4home.size := by rw [hHome8]; decide
  have h5D : 5 < bU.sudo_5Board_4held.size := by rw [hHeld8]; decide
  refine ⟨b', hok, hon, hto, hbench, htake, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hmovFit⟩
  · intro h3
    rw [hframe 3 hH3 h3 (by decide)]
    exact (curve_at3 t x y hD3 hH3).2
  · intro h4
    rw [hframe 4 hH4 h4 (by decide)]
    exact (curve_at4 t x y hD4 hH4).2
  · intro h2
    rw [hframe 2 h2H h2 (by decide)]
    exact (curve_blank2 t x y h2H h2D).1
  · intro h3
    revert h3
    rw [hheld]
    intro h3
    simp [Array.getElem_set, bU, curve_at3 t x y hD3 hH3]
  · intro h4
    revert h4
    rw [hheld]
    intro h4
    simp [Array.getElem_set, bU, curve_at4 t x y hD4 hH4]
  · intro h2
    revert h2
    rw [hheld]
    intro h2
    simp [Array.getElem_set, bU, curve_blank2 t x y h2H h2D]
  · rw [hhsz, hHome8]
  · rw [hheld, Array.size_set, Array.size_set, hHeld8]
  · intro h5
    rw [hframe 5 h5H h5 (by decide)]
    exact (curve_blank5 t x y h5H h5D).1
  · intro h5
    revert h5
    rw [hheld]
    intro h5
    simp [Array.getElem_set, bU, curve_blank5 t x y h5H h5D]
  · exact hhigh
  · simpa [px, py, n, k, bench, ofNat_eq_natCast] using hmov
  · simpa [bU, ofNat_eq_natCast] using hpeakM
  · rw [ht]; exact curve_tier t x y
  · rw [hslides]
    simpa [bU, ofNat_eq_natCast] using (curve_off t x y).2.2.2.2
  · exact _hmk
  · simpa [bU, curve_ops, ofNat_eq_natCast] using _hops
  · simpa [bU, ofNat_eq_natCast] using hstrict
  · simpa [bU, n, bench, ofNat_eq_natCast] using hhole
  · intro h6
    revert h6
    rw [hheld]
    intro h6
    simp [Array.getElem_set, bU, curve_spare t x y hD6]

/-- `on_curve`'s second bind: copy the across into the empty bottom.
    `placeBoard` writes `embed x` at home 2 and marks it held. The bench is untouched. -/
theorem curve_copy_across (b : Ecbs.Board) (x : List Nat) (n moves peak : Nat)
    (h2H : 2 < b.sudo_5Board_4home.size) (h2D : 2 < b.sudo_5Board_4held.size)
    (h3H : 3 < b.sudo_5Board_4home.size) (h3D : 3 < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hsrc : b.sudo_5Board_4held[3] = true)
    (harr : b.sudo_5Board_4home[3] = embed x)
    (hempty : b.sudo_5Board_4held[2] = false)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx : x.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hfit : FitsLen (moves + pegCount x)) :
    Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false =
      .ok (placeBoard b 2 h2H h2D x moves peak) := by
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl,
    show Ecbs.base_across = ((3 : Nat) : Int) from rfl]
  exact copy_band_refines b 2 3 x moves peak h2H h2D h3H h3D h7 hsrc harr hempty
    (by rw [hn, hx]) (hx ▸ hf) hmoves hpeak hfit

/-- `on_curve`'s cube starts by settling the pending gap, which holds `y²`.
    The cube of the bottom is then the cube on that settled board. -/
theorem curve_cube_settles (b : Ecbs.Board) (lane : List Nat)
    (n moves slides pk cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = Ecbs.gap)
    (hH : 5 < b.sudo_5Board_4home.size) (hD : 5 < b.sudo_5Board_4held.size)
    (h2 : 2 < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty : b.sudo_5Board_4held[5] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak =
      Int.ofNat (raisedPeak pk (countHeld (b.sudo_5Board_4held.set ⟨2, h2⟩ true) 7)))
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) :
    Ecbs.cube b Ecbs.bottom Ecbs.bottom =
      Ecbs.cube (settleBoard b 5 hH hD lane n moves slides
          (raisedPeak pk (countHeld (b.sudo_5Board_4held.set ⟨2, h2⟩ true) 7)))
        Ecbs.bottom Ecbs.bottom := by
  let peak := raisedPeak pk (countHeld (b.sudo_5Board_4held.set ⟨2, h2⟩ true) 7)
  have hto5 : b.sudo_5Board_8bench_to = ((5 : Nat) : Int) := by
    rw [hto, show Ecbs.gap = ((5 : Nat) : Int) from rfl]
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl]
  exact cube_settle_other b 2 2 5 lane n moves slides peak cOps
    hmk hon hto5 hH hD h7 hempty hbench hn hpos hnle hzero hf hfitL
    hmoves hslides hpeak hpeg hfitM hfitS hops hop1 hfops

/-- After the gap has been settled, `cube bottom bottom` leaves `x³` on the bench
    aimed at the bottom, and clears that home. -/
theorem curve_cube_bottom (b : Ecbs.Board) (x : List Nat)
    (w h r n k moves hole bench pk peakS cOps cg : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'hops = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (hF : 2 < b.sudo_5Board_4held.size)
    (hHome : 2 < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[2] = true)
    (hArr : b.sudo_5Board_4home[2] = embed x)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : x.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak =
      (raisedPeak pk (countHeld (b.sudo_5Board_4held.set ⟨2, hF⟩ true) 7) : Int))
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hxsT : allTritList x)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (shape : BoardShape w h r n k)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n))) :
    ∃ b',
      Ecbs.cube b Ecbs.bottom Ecbs.bottom = .ok b' ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = Ecbs.bottom ∧
      b'.sudo_5Board_5bench =
        embed (laneFold n (n - k) (combStrip n bench x)) ∧
      (laneFold n (n - k) (combStrip n bench x)).take n = fieldCube n k bench x ∧
      b'.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨2, hF⟩ false ∧
      b'.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨2, hHome⟩ #[] ∧
      b'.sudo_5Board_9marker_on = false ∧
      (∀ i, n ≤ i → i < bench →
        coeff (laneFold n (n - k) (combStrip n bench x)) i = 0) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (cubeMoves moves x n k bench) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak =
        Int.ofNat (raisedPeak
          (raisedPeak pk (countHeld (b.sudo_5Board_4held.set ⟨2, hF⟩ true) 7))
          (countHeld (b.sudo_5Board_4held.set ⟨2, hF⟩ false) 7)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨1, hops⟩ (Int.ofNat (cOps + 1)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        Int.ofNat (raisedPeak peakS (countHeld b.sudo_5Board_4held 7)) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        Int.ofNat (raisedHole hole (topIdx (combStrip n bench x))) ∧
      b'.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max := by
  let peak := raisedPeak pk (countHeld (b.sudo_5Board_4held.set ⟨2, hF⟩ true) 7)
  have hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simpa [peak, ofNat_eq_natCast] using hpeak
  have hcube := cube_refines b 2 2 x w h r n k moves hole bench peak peakS cOps cg hmk hoff hops hop1 hfops hbl hcg hspan hF hHome hHF hArr h7 hn0 hn hlenx hf hmoves hpk hpeakS hxsT h3 hfm ⟨shape.hw0, shape.hh0, shape.hrR, shape.hrP, shape.hnE, shape.hkLe, shape.hgap⟩ hwF hhF hrF hkF hHole hsm hnsm hfitB hfold
  have hoffB := cube_off_eq b 2 2 x w h r n k moves hole bench peak peakS cOps cg hmk hoff hops hop1 hfops hbl hcg hspan hF hHome hHF hArr h7 hn0 hn hlenx hf hmoves hpk hpeakS hxsT h3 hfm ⟨shape.hw0, shape.hh0, shape.hrR, shape.hrP, shape.hnE, shape.hkLe, shape.hgap⟩ hwF hhF hrF hkF hHole hsm hnsm hfitB hfold
  obtain ⟨b', hok, hon, hto, hbench, htake, hhigh, hmov, hpeakOut, hslides, ht,
      _hhsz, hhome, hheld, hmk', _hrow, hops', _htally, _hctrlH, _hctrl⟩ := hcube
  have hb' : b' = cubeOffBoard b 2 2 x n k moves hole bench peak peakS cOps hops hF hHome := by
    have hok2 : Ecbs.cube b ((2 : Nat) : Int) ((2 : Nat) : Int) = .ok b' := by
      rw [← show Ecbs.bottom = ((2 : Nat) : Int) from rfl]
      exact hok
    rw [hoffB] at hok2
    injection hok2.symm
  refine ⟨b', ?_, hon, ?_, hbench, htake, hheld, hhome, hmk', hhigh, hmov, ?_, hslides, ht, hops', ?_, ?_, ?_, ?_, ?_⟩
  · rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl]; exact hok
  · rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl]; exact hto
  · simpa [peak] using hpeakOut
  · simp [hb', cubeOffBoard]
  · simp [hb', cubeOffBoard]
  · simp [hb', cubeOffBoard]
  · simp [hb', cubeOffBoard]
  · simp [hb', cubeOffBoard]

private theorem ops_set_eq (a c : Array Int) (h : a = c) (ha : 0 < a.size) (v : Int) :
    a.set ⟨0, ha⟩ v = c.set ⟨0, h ▸ ha⟩ v := by
  subst h
  rfl

private theorem set0_irrel (a : Array Int) (h1 h2 : 0 < a.size) (v : Int) :
    a.set ⟨0, h1⟩ v = a.set ⟨0, h2⟩ v := by
  have : (⟨0, h1⟩ : Fin a.size) = ⟨0, h2⟩ := Fin.ext rfl
  simp [this]

/-- The spare multiply in `on_curve`. The bench holds the cube and is aimed at the
    empty bottom, so `mul` settles `x³` there and then squares the across.
    The square sits on a fresh bench aimed at the spare. -/
theorem curve_mul_spare (b : Ecbs.Board) (x lane : List Nat)
    (w h r n k moves slides hole bench peak peakS cOps : Nat)
    (hmk : b.sudo_5Board_9marker_on = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = ((2 : Nat) : Int))
    (h2H : 2 < b.sudo_5Board_4home.size) (h2D : 2 < b.sudo_5Board_4held.size)
    (h3H : 3 < b.sudo_5Board_4home.size) (h3D : 3 < b.sudo_5Board_4held.size)
    (h6H : 6 < b.sudo_5Board_4home.size) (h6D : 6 < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hempty2 : b.sudo_5Board_4held[2] = false)
    (hheld3 : b.sudo_5Board_4held[3] = true)
    (harr3 : b.sudo_5Board_4home[3] = embed x)
    (hspE : b.sudo_5Board_4held[6] = false)
    (hbench : b.sudo_5Board_5bench = embed lane)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hpos : 0 < lane.length) (hnle : n ≤ lane.length)
    (hzero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i] = 0)
    (hf : FitsLen n) (hfitL : FitsLen lane.length)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hslides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (hpeakS : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeg : FitsLen (2 * pegCount (lane.take n)))
    (hfitM : FitsLen (moves + 2 * pegCount (lane.take n)))
    (hfitS : FitsLen (slides + 2 * pegCount (lane.take n)))
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hx : x.length = n) (hxt : allTritList x)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hwF : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hhF : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hrF : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hkF : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hHole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hn0 : 0 < n) (hspan : 2 * (n - 1) < bench)
    (hfi : FitsLen (2 * (n - 1))) (hfitB : FitsLen bench)
    (hfitC : FitsLen (moves + 2 * pegCount (lane.take n) + pegCount x))
    (hfm : FitsLen (moves + 2 * pegCount (lane.take n) + pegCount x + n * (n + 1)))
    (hfold : FitsLen (moves + 2 * pegCount (lane.take n) + pegCount x + n * (n + 1) +
        3 * (bench - n)))
    (shape : BoardShape w h r n k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) :
    ∃ b',
      Ecbs.mul b Ecbs.spare Ecbs.base_across Ecbs.base_across true false false = .ok b' ∧
      b'.sudo_5Board_8bench_on = true ∧
      b'.sudo_5Board_8bench_to = Ecbs.spare ∧
      (laneFold n (n - k) (school n x x (List.replicate bench 0) false)).take n =
        fieldMul n k bench x x ∧
      (∀ (h2 : 2 < b'.sudo_5Board_4home.size),
        b'.sudo_5Board_4home[2] = embed (lane.take n)) ∧
      b'.sudo_5Board_5bench =
        embed (laneFold n (n - k) (school n x x (List.replicate bench 0) false)) ∧
      (∀ i, n ≤ i → i < bench →
        coeff (laneFold n (n - k) (school n x x (List.replicate bench 0) false)) i = 0) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (mulMoves (moves + 2 * pegCount (lane.take n)) x x n k bench) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + 2 * pegCount (lane.take n)) ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      (∀ (h6 : 6 < b'.sudo_5Board_4held.size), b'.sudo_5Board_4held[6] = false) ∧
      (∀ (h2 : 2 < b'.sudo_5Board_4held.size), b'.sudo_5Board_4held[2] = true) ∧
      (∀ i (hi : i < b.sudo_5Board_4held.size) (hi' : i < b'.sudo_5Board_4held.size),
        i ≠ 6 → i ≠ 2 → b'.sudo_5Board_4held[i] = b.sudo_5Board_4held[i]) ∧
      (∀ i (hi : i < b.sudo_5Board_4home.size) (hi' : i < b'.sudo_5Board_4home.size),
        i ≠ 6 → i ≠ 2 → b'.sudo_5Board_4home[i] = b.sudo_5Board_4home[i]) ∧
      b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      (∃ pk', b'.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk') ∧
      b'.sudo_5Board_9marker_on = false ∧
      b'.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops.set ⟨0, hops⟩ (Int.ofNat (cOps + 1)) := by
  have hpair := mul_settles_first b Ecbs.spare Ecbs.base_across Ecbs.base_across true
    2 lane n moves slides peak cOps hmk hon hto h2H h2D h7 hempty2 hbench hn hpos hnle hzero
    hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
    hops hop0 hfops
  have hset := settle_refines b 2 lane n moves slides peak h2H h2D h7 hon hto hempty2 hbench
    hn hpos hnle hzero hf hfitL hmoves hslides hpeak
    hpeg hfitM hfitS
  rw [hpair.1, hset, ok_bind]
  let bS := settleBoard b 2 h2H h2D lane n moves slides peak
  let pegs := pegCount (lane.take n)
  let mvS := moves + 2 * pegs
  let occ := countHeld (b.sudo_5Board_4held.set ⟨2, h2D⟩ true) 7
  let pkS := if peak < occ then occ else peak
  have hmkS : bS.sudo_5Board_9marker_on = false := by
    by_cases hpk : peak < occ
    · simp [bS, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, hmk]
    · simp [bS, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, hmk]
  have hoffS : bS.sudo_5Board_8bench_on = false := by
    simp [bS, settle_bench_off b 2 ⟨h2H, h2D⟩ lane n moves slides peak]
  have hmovS : bS.sudo_5Board_4cost.sudo_5Costs_5moves = (mvS : Int) := by
    by_cases hpk : peak < occ
    · simp [bS, mvS, pegs, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, ofNat_eq_natCast]
    · simp [bS, mvS, pegs, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, ofNat_eq_natCast]
  have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (pkS : Int) := by
    by_cases hpk : peak < occ
    · simp [bS, pkS, occ, hpk, if_pos, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk,
        ofNat_eq_natCast]
    · simp [bS, pkS, occ, hpk, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, hpeak,
        ofNat_eq_natCast]
  have hstrict : bS.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    by_cases hpk : peak < occ
    · simp [bS, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, hpeakS]
    · simp [bS, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, hpeakS]
  have hhole : bS.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    by_cases hpk : peak < occ
    · simp [bS, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, hHole]
    · simp [bS, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, hHole]
  have hopsS : 0 < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [bS] using settle_ops_lt b 0 2 hops ⟨h2H, h2D⟩ lane n moves slides peak
  have hop0S : bS.sudo_5Board_4cost.sudo_5Costs_3ops[0]'hopsS = (cOps : Int) := by
    have hget := get_eq_of_array (settle_ops b 2 ⟨h2H, h2D⟩ lane n moves slides peak) 0 hopsS
    exact hget.trans hop0
  have htier : bS.sudo_5Board_1t = b.sudo_5Board_1t := by
    dsimp [bS]
    unfold settleBoard
    split <;> rfl
  have h3Ds : 3 < bS.sudo_5Board_4held.size := by
    simp [bS, settleBoard, h3D]
    split <;> simp [Array.size_set, h3D]
  have h3Hs : 3 < bS.sudo_5Board_4home.size := by
    simp [bS, settleBoard, h3H]
    split <;> simp [Array.size_set, h3H]
  have h6Ds : 6 < bS.sudo_5Board_4held.size := by
    simp [bS, settleBoard, h6D]
    split <;> simp [Array.size_set, h6D]
  have h6Hs : 6 < bS.sudo_5Board_4home.size := by
    simp [bS, settleBoard, h6H]
    split <;> simp [Array.size_set, h6H]
  have h7s : 7 ≤ bS.sudo_5Board_4held.size := by
    simp [bS, settleBoard, h7]
    split <;> simp [Array.size_set, h7]
  have hheld3s : bS.sudo_5Board_4held[3] = true := by
    by_cases hpk : peak < occ
    · simp [bS, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, Array.getElem_set, hheld3]
    · simp [bS, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, Array.getElem_set, hheld3]
  have harr3s : bS.sudo_5Board_4home[3] = embed x := by
    by_cases hpk : peak < occ
    · simp [bS, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, Array.getElem_set, harr3]
    · simp [bS, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, Array.getElem_set, harr3]
  have hspEs : bS.sudo_5Board_4held[6] = false := by
    by_cases hpk : peak < occ
    · simp [bS, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, Array.getElem_set, hspE]
    · simp [bS, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, Array.getElem_set, hspE]
  have hmul := mul_refines bS 6 3 3 x x w h r n k mvS hole bench pkS peakS cOps hmkS hoffS hopsS hop0S hfops (by rw [htier]; exact hbl) h3Ds h3Hs hheld3s harr3s h3Ds h3Hs hheld3s harr3s h6Ds h6Hs hspEs h7s (by decide) (by decide) hn0 (by rw [htier]; exact hn) hx hx hf hmovS hpkS hstrict hfitC hspan hxt hfi hfm ⟨shape.hw0, shape.hh0, shape.hrR, shape.hrP, shape.hnE, shape.hkLe, shape.hgap⟩ (by rw [htier]; exact hwF) (by rw [htier]; exact hhF) (by rw [htier]; exact hrF) (by rw [htier]; exact hkF) hhole hsm hnsm hfitB hfold
  obtain ⟨b', hok, hon', hto', hbench, htake, htail⟩ := hmul
  obtain ⟨hhigh, hmov, hpk, hsl, ht, hsz, hheld, _h5, hframe, hmkR, hopsR, _hstrict,
      _hhole, hmarkR, hctrlR, hmxR, _hhi, _hrow, _hfr⟩ := htail
  have h2s : 2 < bS.sudo_5Board_4home.size := by
    simp [bS, settleBoard]
    split <;> simp [Array.size_set, h2H]
  refine ⟨b', ?_, hon', ?_, htake, ?_, hbench, hhigh, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
  · rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl,
      show Ecbs.base_across = ((3 : Nat) : Int) from rfl]
    exact hok
  · rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl]
    exact hto'
  · intro h2
    rw [hframe 2 h2s h2 (by decide)]
    by_cases hpk : peak < occ
    · simp [bS, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, Array.getElem_set]
    · simp [bS, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, Array.getElem_set]
  · simpa [mvS, pegs] using hmov
  · rw [hsl]
    by_cases hpk : peak < occ
    · simp [bS, mvS, pegs, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, ofNat_eq_natCast]
    · simp [bS, mvS, pegs, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, ofNat_eq_natCast]
  · rw [ht, htier]
  · intro h6
    simp [hheld, Array.getElem_set]
  · intro h2
    have h2Ds : 2 < bS.sudo_5Board_4held.size := by
      simp [bS, settleBoard]
      split <;> simp [Array.size_set, h2D]
    have h2true : bS.sudo_5Board_4held[2] = true := by
      by_cases hpk : peak < occ
      · simp [bS, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, Array.getElem_set]
      · simp [bS, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk, Array.getElem_set]
    have hne : (6 : Nat) ≠ 2 := by decide
    simp [hheld, Array.getElem_set, hne, h2true]
  · intro i hi hi' h6ne h2ne
    have hSi : i < bS.sudo_5Board_4held.size := by
      simp [bS, settleBoard]
      split <;> simp [Array.size_set, hi]
    have hget : b'.sudo_5Board_4held[i] = bS.sudo_5Board_4held[i] := by
      have hne6 : (6 : Nat) ≠ i := Ne.symm h6ne
      simp [hheld, Array.getElem_set, hne6]
    have hne2 : (2 : Nat) ≠ i := Ne.symm h2ne
    by_cases hpk : peak < occ
    · simp only [bS, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk,
        Array.getElem_set, hne2] at hget
      exact hget
    · simp only [bS, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk,
        Array.getElem_set, hne2] at hget
      exact hget
  · intro i hi hi' h6 h2
    have hSi : i < bS.sudo_5Board_4home.size := by
      simp [bS, settleBoard]
      split <;> simp [Array.size_set, hi]
    have hget := hframe i hSi hi' h6
    have hne2 : 2 ≠ i := Ne.symm h2
    by_cases hpk : peak < occ
    · simp only [bS, occ, settle_peak b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk,
        Array.getElem_set, hne2] at hget
      exact hget
    · simp only [bS, occ, settle_keep b 2 ⟨h2H, h2D⟩ lane n moves slides peak hpk,
        Array.getElem_set, hne2] at hget
      exact hget
  · rw [hsz]
    simp [bS, settleBoard]
    split <;> simp [Array.size_set, h2H]
  · rw [hheld, Array.size_set, Array.size_set]
    simp [bS, settleBoard]
    split <;> simp [Array.size_set, h2D]
  · exact ⟨_, hpk⟩
  · exact hmkR
  · rw [hmarkR]
    exact settle_ix_eq b 2 ⟨h2H, h2D⟩ lane n moves slides peak
  · rw [hctrlR]
    exact settle_ctrl_eq b 2 ⟨h2H, h2D⟩ lane n moves slides peak
  · rw [hmxR]
    exact settle_mx_eq b 2 ⟨h2H, h2D⟩ lane n moves slides peak
  · rw [hopsR]
    have hopsEq : bS.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by
      simpa [bS] using settle_ops b 2 ⟨h2H, h2D⟩ lane n moves slides peak
    exact (ops_set_eq _ _ hopsEq hopsS _).trans (set0_irrel _ _ hops _)

/-- The explicit `settle` after the spare multiply. The square is on the bench,
    aimed at the empty spare, so the spare home becomes the length-`n` prefix. -/
theorem curve_settle_spare (b : Ecbs.Board) (lane sq : List Nat) (n moves slides peak : Nat)
    (h6H : 6 < b.sudo_5Board_4home.size) (h6D : 6 < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = ((6 : Nat) : Int))
    (hempty : b.sudo_5Board_4held[6] = false)
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
    (htake : lane.take n = sq) :
    ∃ b',
      Ecbs.settle b = .ok b' ∧
      b'.sudo_5Board_8bench_on = false ∧
      (∀ (h6 : 6 < b'.sudo_5Board_4home.size), b'.sudo_5Board_4home[6] = embed sq) ∧
      (∀ (h6 : 6 < b'.sudo_5Board_4held.size), b'.sudo_5Board_4held[6] = true) ∧
      (∀ i (hi : i < b.sudo_5Board_4home.size) (hi' : i < b'.sudo_5Board_4home.size),
        i ≠ 6 → b'.sudo_5Board_4home[i] = b.sudo_5Board_4home[i]) ∧
      (∀ i (hi : i < b.sudo_5Board_4held.size) (hi' : i < b'.sudo_5Board_4held.size),
        i ≠ 6 → b'.sudo_5Board_4held[i] = b.sudo_5Board_4held[i]) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (moves + 2 * pegCount (lane.take n)) ∧
      b'.sudo_5Board_1t = b.sudo_5Board_1t ∧
      b'.sudo_5Board_4home.size = b.sudo_5Board_4home.size ∧
      b'.sudo_5Board_4held.size = b.sudo_5Board_4held.size ∧
      b'.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      b'.sudo_5Board_6marker = b.sudo_5Board_6marker ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = b.sudo_5Board_4cost.sudo_5Costs_4ctrl ∧
      b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
        b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max ∧
      b'.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + 2 * pegCount (lane.take n)) := by
  have hset := settle_refines b 6 lane n moves slides peak h6H h6D h7 hon hto hempty hbench
    hn hpos hnle hzero hf hfitL hmoves hslides hpeak hpeg hfitM hfitS
  let b' := settleBoard b 6 h6H h6D lane n moves slides peak
  refine ⟨b', hset, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [b']
    unfold settleBoard
    split <;> rfl
  · intro h6
    dsimp [b']
    unfold settleBoard
    split <;> simp [Array.getElem_set, htake]
  · intro h6
    dsimp [b']
    unfold settleBoard
    split <;> simp [Array.getElem_set]
  · intro i hi hi' hne
    dsimp [b']
    unfold settleBoard
    split <;> simp [Array.getElem_set, hne]
    · intro heq
      exact absurd heq.symm hne
    · intro heq
      exact absurd heq.symm hne
  · intro i hi hi' hne
    dsimp [b']
    unfold settleBoard
    split <;> simp [Array.getElem_set, hne]
    · intro heq
      exact absurd heq.symm hne
    · intro heq
      exact absurd heq.symm hne
  · dsimp [b']
    unfold settleBoard
    split <;> simp [ofNat_eq_natCast]
  · dsimp [b']
    unfold settleBoard
    split <;> rfl
  · dsimp [b']
    unfold settleBoard
    split <;> simp [Array.size_set]
  · dsimp [b']
    unfold settleBoard
    split <;> simp [Array.size_set]
  · dsimp [b']
    unfold settleBoard
    split <;> simp
  · dsimp [b']
    unfold settleBoard
    split <;> simp
  · dsimp [b']
    unfold settleBoard
    split <;> simp
  · dsimp [b']
    unfold settleBoard
    split <;> simp
  · dsimp [b']
    unfold settleBoard
    split <;> simp [ofNat_eq_natCast]

/-- `bottom + mirror(spare)` after the square has been settled into the spare.
    The destination is `fieldAdd` of the cube and the flipped square. -/
theorem curve_add_bottom (b : Ecbs.Board) (x3 x2 : List Nat) (n moves : Nat)
    (h2H : 2 < b.sudo_5Board_4home.size) (h2D : 2 < b.sudo_5Board_4held.size)
    (h6H : 6 < b.sudo_5Board_4home.size) (h6D : 6 < b.sudo_5Board_4held.size)
    (hheld2 : b.sudo_5Board_4held[2] = true)
    (harr2 : b.sudo_5Board_4home[2] = embed x3)
    (hheld6 : b.sudo_5Board_4held[6] = true)
    (harr6 : b.sudo_5Board_4home[6] = embed x2)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx3 : x3.length = n) (hx2 : x2.length = n) (hpos : 0 < n)
    (ht3 : allTritList x3) (ht2 : allTritList x2)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n)) :
    Ecbs.add b Ecbs.bottom Ecbs.spare true =
      .ok (addBoard b 2 h2H (embed (fieldAdd n x3 (mirrorTrits x2))) (moves + pegCount x2)) := by
    exact add_refines b 2 6 x3 x2 n moves h2H h2D h6H h6D
      hheld2 harr2 hheld6 harr6 hn hx2 hx3 hpos ht3 ht2 hm hfit

private theorem coeff_trit (xs : List Nat) (h : allTritList xs) (i : Nat) : coeff xs i ≤ 2 := by
  unfold coeff
  by_cases hi : i < xs.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact trit_get h hi
  · have hle : xs.length ≤ i := Nat.le_of_not_lt hi
    simp [List.getElem?_eq_none hle]

private theorem mirror_trits {xs : List Nat} (h : allTritList xs) : allTritList (mirrorTrits xs) := by
  rw [mirrorTrits_flip]
  intro z hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  have ha2 : a ≤ 2 := h a ha
  unfold flipTrit
  split <;> omega

private theorem fieldAdd_trits (n : Nat) (xs ys : List Nat)
    (hx : allTritList xs) (hy : allTritList ys) : allTritList (fieldAdd n xs ys) := by
  intro z hz
  simp [fieldAdd, List.mem_map] at hz
  rcases hz with ⟨i, _, rfl⟩
  have hx2 := coeff_trit xs hx i
  have hy2 := coeff_trit ys hy i
  unfold tritAdd
  omega

private theorem fieldAdd_len (n : Nat) (xs ys : List Nat) : (fieldAdd n xs ys).length = n := by
  simp [fieldAdd, List.length_map, List.length_range]

private theorem except_bind_assoc {α β γ}
    (m : Except SudoRt.Trap α) (f : α → Except SudoRt.Trap β) (g : β → Except SudoRt.Trap γ) :
    (m >>= fun x => f x >>= g) = ((m >>= f) >>= g) := by
  cases m with
  | error _ => simp
  | ok a => simp [ok_bind]

private theorem addBoard_home_size (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (addBoard b home hH arr mv).sudo_5Board_4home.size = b.sudo_5Board_4home.size := by
  unfold addBoard withMoves
  simp [Array.size_set]

private theorem addBoard_held (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (addBoard b home hH arr mv).sudo_5Board_4held = b.sudo_5Board_4held := by
  unfold addBoard withMoves
  rfl

private theorem addBoard_moves (b : Ecbs.Board) (home : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat) :
    (addBoard b home hH arr mv).sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by
  unfold addBoard withMoves
  rfl

private theorem addBoard_get_ne (b : Ecbs.Board) (home i : Nat)
    (hH : home < b.sudo_5Board_4home.size) (arr : Array Int) (mv : Nat)
    (hi : i < b.sudo_5Board_4home.size) (hne : i ≠ home) :
    ∀ (hi' : i < (addBoard b home hH arr mv).sudo_5Board_4home.size),
      (addBoard b home hH arr mv).sudo_5Board_4home[i] = b.sudo_5Board_4home[i] := by
  intro hi'
  unfold addBoard withMoves
  simp [Array.getElem_set, hne]
  intro heq
  exact absurd heq.symm hne

/-- The two clears after the curve compare. Gap first, then bottom.
    Neither clear changes the bool already read. -/
theorem curve_clear_ends (b : Ecbs.Board) (gapXs botXs : List Nat) (moves : Nat)
    (h5H : 5 < b.sudo_5Board_4home.size) (h5D : 5 < b.sudo_5Board_4held.size)
    (h2H : 2 < b.sudo_5Board_4home.size) (h2D : 2 < b.sudo_5Board_4held.size)
    (hheld5 : b.sudo_5Board_4held[5] = true)
    (harr5 : b.sudo_5Board_4home[5] = embed gapXs)
    (hheld2 : b.sudo_5Board_4held[2] = true)
    (harr2 : b.sudo_5Board_4home[2] = embed botXs)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hf5 : FitsLen gapXs.length) (hf2 : FitsLen botXs.length)
    (hfit5 : FitsLen (moves + pegCount gapXs))
    (hfit2 : FitsLen (moves + pegCount gapXs + pegCount botXs)) :
    (Ecbs.clear b Ecbs.gap >>= fun b1 => Ecbs.clear b1 Ecbs.bottom) =
      .ok { { b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨5, h5H⟩ #[]
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨5, h5D⟩ false
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + pegCount gapXs) } } with
        sudo_5Board_4home :=
          (b.sudo_5Board_4home.set ⟨5, h5H⟩ #[]).set
            ⟨2, by simpa [Array.size_set] using h2H⟩ #[]
        sudo_5Board_4held :=
          (b.sudo_5Board_4held.set ⟨5, h5D⟩ false).set
            ⟨2, by simpa [Array.size_set] using h2D⟩ false
        sudo_5Board_4cost := { b.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (moves + pegCount gapXs + pegCount botXs) } } := by
  have h1 := clear_held_refines b 5 gapXs moves h5H h5D hheld5 harr5 hm hf5 hfit5
  rw [show Ecbs.gap = ((5 : Nat) : Int) from rfl, h1, ok_bind]
  let b1 := { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨5, h5H⟩ #[]
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨5, h5D⟩ false
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (moves + pegCount gapXs) } }
  have h2H1 : 2 < b1.sudo_5Board_4home.size := by
    simpa [b1, Array.size_set] using h2H
  have h2D1 : 2 < b1.sudo_5Board_4held.size := by
    simpa [b1, Array.size_set] using h2D
  have hheld21 : b1.sudo_5Board_4held[2] = true := by
    have hne : (2 : Nat) ≠ 5 := by decide
    simp [b1, Array.getElem_set, hne, hheld2]
  have harr21 : b1.sudo_5Board_4home[2] = embed botXs := by
    have hne : (2 : Nat) ≠ 5 := by decide
    simp [b1, Array.getElem_set, hne, harr2]
  have hm1 : b1.sudo_5Board_4cost.sudo_5Costs_5moves =
      ((moves + pegCount gapXs) : Int) := by
    simp [b1, ofNat_eq_natCast]
  have h2 := clear_held_refines b1 2 botXs (moves + pegCount gapXs) h2H1 h2D1
    hheld21 harr21 hm1 hf2 (by simpa [Nat.add_assoc] using hfit2)
  rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl, h2]

/-- After the mirror add, clear the spare, add the white peg at hole 0, and
    compare the gap with the bottom. The compare is array `SEq.beq`. -/
theorem curve_white_beq (b : Ecbs.Board) (x3 x2 y2 : List Nat) (n moves : Nat)
    (h2H : 2 < b.sudo_5Board_4home.size) (h2D : 2 < b.sudo_5Board_4held.size)
    (h5H : 5 < b.sudo_5Board_4home.size) (h5D : 5 < b.sudo_5Board_4held.size)
    (h6H : 6 < b.sudo_5Board_4home.size) (h6D : 6 < b.sudo_5Board_4held.size)
    (hheld2 : b.sudo_5Board_4held[2] = true)
    (harr2 : b.sudo_5Board_4home[2] = embed x3)
    (hheld5 : b.sudo_5Board_4held[5] = true)
    (harr5 : b.sudo_5Board_4home[5] = embed y2)
    (hheld6 : b.sudo_5Board_4held[6] = true)
    (harr6 : b.sudo_5Board_4home[6] = embed x2)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hx3 : x3.length = n) (hx2 : x2.length = n) (hy2 : y2.length = n) (hpos : 0 < n)
    (ht3 : allTritList x3) (ht2 : allTritList x2)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hfit : FitsLen (moves + n))
    (hf : FitsLen n)
    (hfitC : FitsLen (moves + pegCount x2 + pegCount x2))
    (hfitW : FitsLen (moves + pegCount x2 + pegCount x2 + 1))
    (hfitG : FitsLen (moves + pegCount x2 + pegCount x2 + 1 + pegCount y2))
    (hfitBot : FitsLen (moves + pegCount x2 + pegCount x2 + 1 + pegCount y2 + n)) :
    ∃ bF,
      (Ecbs.add b Ecbs.bottom Ecbs.spare true >>= fun b1 =>
        Ecbs.clear b1 Ecbs.spare >>= fun b2 =>
        Ecbs.white0 b2 Ecbs.bottom >>= fun b3 =>
        Ecbs.value b3 Ecbs.gap >>= fun g =>
        Ecbs.value b3 Ecbs.bottom >>= fun bot =>
        Ecbs.clear b3 Ecbs.gap >>= fun b4 =>
        Ecbs.clear b4 Ecbs.bottom >>= fun b5 =>
        pure (SudoRt.SEq.beq g bot, b5)) =
        .ok (decide (y2 =
          fieldAdd n (fieldAdd n x3 (mirrorTrits x2)) (1 :: List.replicate (n - 1) 0)), bF) := by
  have hadd := curve_add_bottom b x3 x2 n moves h2H h2D h6H h6D
    hheld2 harr2 hheld6 harr6 hn hx3 hx2 hpos ht3 ht2 hm hfit
  let sum := fieldAdd n x3 (mirrorTrits x2)
  let mvA := moves + pegCount x2
  let bA := addBoard b 2 h2H (embed sum) mvA
  have h6HA : 6 < bA.sudo_5Board_4home.size := by
    simpa [bA, addBoard_home_size] using h6H
  have h6DA : 6 < bA.sudo_5Board_4held.size := by
    simpa [bA, addBoard_held] using h6D
  have hheld6A : bA.sudo_5Board_4held[6] = true := by
    simpa [bA, addBoard_held] using hheld6
  have harr6A : bA.sudo_5Board_4home[6] = embed x2 :=
    addBoard_get_ne b 2 6 h2H (embed sum) mvA h6H (by decide) h6HA ▸ harr6
  have hmA : bA.sudo_5Board_4cost.sudo_5Costs_5moves = (mvA : Int) := by
    simpa [bA, addBoard_moves, ofNat_eq_natCast]
  have hC := clear_held_refines bA 6 x2 mvA h6HA h6DA hheld6A harr6A hmA
    (by simpa [hx2] using hf) hfitC
  let mvC := mvA + pegCount x2
  let bC := { bA with
    sudo_5Board_4home := bA.sudo_5Board_4home.set ⟨6, h6HA⟩ #[]
    sudo_5Board_4held := bA.sudo_5Board_4held.set ⟨6, h6DA⟩ false
    sudo_5Board_4cost := { bA.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat mvC } }
  have hsumL : sum.length = n := fieldAdd_len n x3 (mirrorTrits x2)
  have htriS : allTritList sum :=
    fieldAdd_trits n x3 (mirrorTrits x2) ht3 (mirror_trits ht2)
  have h2HC : 2 < bC.sudo_5Board_4home.size := by
    simpa [bC, Array.size_set] using (addBoard_home_size b 2 h2H (embed sum) mvA ▸ h2H)
  have h2DC : 2 < bC.sudo_5Board_4held.size := by
    simpa [bC, Array.size_set, bA, addBoard_held] using h2D
  have hheld2C : bC.sudo_5Board_4held[2] = true := by
    simpa [bC, Array.getElem_set, bA, addBoard_held] using hheld2
  have harr2A : bA.sudo_5Board_4home[2] = embed sum := by
    unfold bA addBoard withMoves
    simp [Array.getElem_set]
  have harr2C : bC.sudo_5Board_4home[2] = embed sum := by
    have hne : (2 : Nat) ≠ 6 := by decide
    simp [bC, Array.getElem_set, hne, harr2A]
  have hmC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simp [bC]
  have h0s : 0 < sum.length := by rw [hsumL]; exact hpos
  have hcell : sum[0] ≤ 2 := trit_get htriS h0s
  have hfitW' : FitsLen (mvC + 1) := by simpa [mvC, mvA, Nat.add_assoc] using hfitW
  have hW := white0_held bC 2 sum mvC h2HC h2DC hheld2C harr2C h0s hcell hmC hfitW'
  let white := sum.set 0 (tritAdd sum[0] 1)
  let bW := addBoard bC 2 h2HC (embed white) (mvC + 1)
  have h5HW : 5 < bW.sudo_5Board_4home.size := by
    simpa [bW, addBoard_home_size] using
      (by simpa [bC, Array.size_set] using (addBoard_home_size b 2 h2H (embed sum) mvA ▸ h5H))
  have h5DW : 5 < bW.sudo_5Board_4held.size := by
    simpa [bW, addBoard_held, bC, Array.size_set, bA, addBoard_held] using h5D
  have hheld5W : bW.sudo_5Board_4held[5] = true := by
    simpa [bW, addBoard_held, bC, Array.getElem_set, bA, addBoard_held] using hheld5
  have h5szA : 5 < bA.sudo_5Board_4home.size := by
    simpa [bA, addBoard_home_size] using h5H
  have h5A : bA.sudo_5Board_4home[5] = embed y2 :=
    (addBoard_get_ne b 2 5 h2H (embed sum) mvA h5H (by decide) h5szA).trans harr5
  have h5szC : 5 < bC.sudo_5Board_4home.size := by
    simpa [bC, Array.size_set] using h5szA
  have h5C : bC.sudo_5Board_4home[5] = embed y2 := by
    have hne6 : (5 : Nat) ≠ 6 := by decide
    simp [bC, Array.getElem_set, hne6, h5A]
  have harr5W : bW.sudo_5Board_4home[5] = embed y2 := by
    have hne : (5 : Nat) ≠ 2 := by decide
    exact (addBoard_get_ne bC 2 5 h2HC (embed white) (mvC + 1) h5szC hne h5HW).trans h5C
  have h2HW : 2 < bW.sudo_5Board_4home.size := by
    simpa [bW, addBoard_home_size] using h2HC
  have h2DW : 2 < bW.sudo_5Board_4held.size := by
    simpa [bW, addBoard_held] using h2DC
  have hheld2W : bW.sudo_5Board_4held[2] = true := by
    simpa [bW, addBoard_held] using hheld2C
  have harr2W : bW.sudo_5Board_4home[2] = embed white := by
    unfold bW addBoard withMoves
    simp [Array.getElem_set]
  have hwhiteL : white.length = n := by simp [white, List.length_set, hsumL]
  have hG := value_held_refines bW 5 y2 n h5DW h5HW hheld5W harr5W hn
    (by rw [hy2]; exact Nat.le_refl _) hf
  have hB := value_held_refines bW 2 white n h2DW h2HW hheld2W harr2W hn
    (by rw [hwhiteL]; exact Nat.le_refl _) hf
  have htakeY : y2.take n = y2 := by rw [← hy2]; exact List.take_length y2
  have htakeW : white.take n = white := by rw [← hwhiteL]; exact List.take_length white
  have hwhiteEq := fieldAdd_white n sum hsumL hpos htriS
  have hmW : bW.sudo_5Board_4cost.sudo_5Costs_5moves = ((mvC + 1) : Int) := by
    simpa [bW, addBoard_moves, mvC, ofNat_eq_natCast]
  have hpegW : pegCount white ≤ n := by rw [← hwhiteL]; exact pegCount_le white
  have hfitWbot : FitsLen (mvC + 1 + pegCount y2 + pegCount white) :=
    FitsLen.of_le (by simpa [mvC, mvA, Nat.add_assoc] using hfitBot) (by omega)
  have hcl := curve_clear_ends bW y2 white (mvC + 1) h5HW h5DW h2HW h2DW
    hheld5W harr5W hheld2W harr2W hmW
    (by simpa [hy2] using hf) (by simpa [hwhiteL] using hf)
    (by simpa [mvC, mvA, Nat.add_assoc] using hfitG) hfitWbot
  have hcl' : (Ecbs.clear bW ((5 : Nat) : Int) >>= fun b1 =>
      Ecbs.clear b1 ((2 : Nat) : Int)) = Except.ok
      ({ { bW with
          sudo_5Board_4home := bW.sudo_5Board_4home.set ⟨5, h5HW⟩ #[]
          sudo_5Board_4held := bW.sudo_5Board_4held.set ⟨5, h5DW⟩ false
          sudo_5Board_4cost := { bW.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (mvC + 1 + pegCount y2) } } with
        sudo_5Board_4home :=
          (bW.sudo_5Board_4home.set ⟨5, h5HW⟩ #[]).set
            ⟨2, by simpa [Array.size_set] using h2HW⟩ #[]
        sudo_5Board_4held :=
          (bW.sudo_5Board_4held.set ⟨5, h5DW⟩ false).set
            ⟨2, by simpa [Array.size_set] using h2DW⟩ false
        sudo_5Board_4cost := { bW.sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat (mvC + 1 + pegCount y2 + pegCount white) } }) := by
    simpa [show Ecbs.gap = ((5 : Nat) : Int) from rfl,
      show Ecbs.bottom = ((2 : Nat) : Int) from rfl] using hcl
  exact ⟨_, by
    rw [hadd, ok_bind]
    rw [show Ecbs.spare = ((6 : Nat) : Int) from rfl, hC, ok_bind]
    rw [show Ecbs.bottom = ((2 : Nat) : Int) from rfl, hW, ok_bind]
    rw [show Ecbs.gap = ((5 : Nat) : Int) from rfl, hG, ok_bind]
    rw [hB, ok_bind]
    rw [htakeY, htakeW, embed_beq]
    rw [except_bind_assoc, hcl', ok_bind, pure_eq_ok]
    simp [white, hwhiteEq]
    rfl⟩

theorem placeBoard_home (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    ∀ (h : home < (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4home.size),
      (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4home[home] = embed xs := by
  intro h
  unfold placeBoard
  dsimp only
  split <;> simp [Array.getElem_set]

end EcbsLink2.Link2
