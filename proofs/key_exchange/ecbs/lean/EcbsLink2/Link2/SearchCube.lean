/-
  After `search_copy`, `curve_side` cubes the bottom. The bench comes back on,
  aimed at that home, holding `fieldCube` of the planted peg. The bottom home
  is cleared. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchPlant
import EcbsLink2.Link2.CurveCopy
import EcbsLink2.Link2.OpenBoard
import EcbsLink2.Link2.WalkInd
import EcbsLink2.Link2.EntryInv

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem bind_assoc {α β γ : Type}
    (m : Except SudoRt.Trap α) (f : α → Except SudoRt.Trap β) (g : β → Except SudoRt.Trap γ) :
    (m >>= fun x => f x >>= g) = ((m >>= f) >>= g) := by
  cases m <;> simp [ok_bind, error_bind]

private theorem set_true_id (a : Array Bool) (i : Nat) (hi : i < a.size) (ht : a[i] = true) :
    a.set ⟨i, hi⟩ true = a := by
  apply Array.ext
  · simp [Array.size_set]
  · intro j hj hj'
    by_cases h : j = i
    · simp [h, Array.getElem_set, ht]
    · have hne : i ≠ j := Ne.symm h
      simp [Array.getElem_set, hne]

private theorem countHeld_side :
    countHeld (((Array.mkArray 8 false).set ⟨3, by simp [Array.size_mkArray]⟩ true).set
      ⟨2, by simp [Array.size_set, Array.size_mkArray]⟩ true) 7 = 2 := by
  decide

theorem putAcross_home2 (t : Spec.Tier) (x : List Nat) :
    2 < (putAcross t x).sudo_5Board_4home.size := by
  rw [putAcross_szH]; decide

theorem putAcross_held2 (t : Spec.Tier) (x : List Nat) :
    2 < (putAcross t x).sudo_5Board_4held.size := by
  rw [putAcross_szD]; decide

theorem putAcross_home3 (t : Spec.Tier) (x : List Nat) :
    3 < (putAcross t x).sudo_5Board_4home.size := by
  rw [putAcross_szH]; decide

theorem putAcross_held3 (t : Spec.Tier) (x : List Nat) :
    3 < (putAcross t x).sudo_5Board_4held.size := by
  rw [putAcross_szD]; decide

/-- Homes 3 and 2 are held, so the copy's peak is 2. -/
theorem put_occ_side (t : Spec.Tier) (x : List Nat) :
    countHeld ((putAcross t x).sudo_5Board_4held.set ⟨2, putAcross_held2 t x⟩ true) 7 = 2 := by
  simpa [putAcross, putAcross_held2, heldIx, ← built_held_arr] using countHeld_side

/-- The planted peg copied into the bottom. Peak is 2. -/
def searchSideBoard (t : Spec.Tier) (x : List Nat) : Ecbs.Board :=
  let b := putAcross t x
  { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨2, putAcross_home2 t x⟩ (embed x)
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨2, putAcross_held2 t x⟩ true
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (pegCount x + pegCount x)
      sudo_5Costs_4peak := 2 } }

theorem searchSide_place (t : Spec.Tier) (x : List Nat) :
    placeBoard (putAcross t x) 2 (putAcross_home2 t x) (putAcross_held2 t x)
      x (pegCount x) 1 = searchSideBoard t x := by
  have hlt : 1 < countHeld
      ((putAcross t x).sudo_5Board_4held.set ⟨2, putAcross_held2 t x⟩ true) 7 := by
    rw [put_occ_side]
    decide
  rw [place_raise (putAcross t x) 2 (putAcross_home2 t x) (putAcross_held2 t x)
    x (pegCount x) 1 hlt, put_occ_side]
  rfl

theorem side_szH (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_4home.size = 8 := by
  simp [searchSideBoard, putAcross, Array.size_set, built_szH]

theorem side_szD (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_4held.size = 8 := by
  simp [searchSideBoard, putAcross, Array.size_set, built_szD]

theorem side_held2 (t : Spec.Tier) (x : List Nat)
    (h : 2 < (searchSideBoard t x).sudo_5Board_4held.size) :
    (searchSideBoard t x).sudo_5Board_4held[2] = true := by
  simp [searchSideBoard, Array.getElem_set]

theorem side_home2 (t : Spec.Tier) (x : List Nat)
    (h : 2 < (searchSideBoard t x).sudo_5Board_4home.size) :
    (searchSideBoard t x).sudo_5Board_4home[2] = embed x := by
  simp [searchSideBoard, Array.getElem_set]

theorem side_held3 (t : Spec.Tier) (x : List Nat)
    (h : 3 < (searchSideBoard t x).sudo_5Board_4held.size) :
    (searchSideBoard t x).sudo_5Board_4held[3] = true := by
  simp [searchSideBoard, putAcross, Array.getElem_set]

theorem side_home3 (t : Spec.Tier) (x : List Nat)
    (h : 3 < (searchSideBoard t x).sudo_5Board_4home.size) :
    (searchSideBoard t x).sudo_5Board_4home[3] = embed x := by
  simp [searchSideBoard, putAcross, Array.getElem_set]

theorem side_held6 (t : Spec.Tier) (x : List Nat)
    (h : 6 < (searchSideBoard t x).sudo_5Board_4held.size) :
    (searchSideBoard t x).sudo_5Board_4held[6] = false := by
  simp [searchSideBoard, putAcross, built_held_arr, Array.getElem_set, Array.getElem_mkArray]

theorem side_held1 (t : Spec.Tier) (x : List Nat)
    (h : 1 < (searchSideBoard t x).sudo_5Board_4held.size) :
    (searchSideBoard t x).sudo_5Board_4held[1] = false := by
  simp [searchSideBoard, putAcross, built_held_arr, Array.getElem_set, Array.getElem_mkArray]

theorem side_held5 (t : Spec.Tier) (x : List Nat)
    (h : 5 < (searchSideBoard t x).sudo_5Board_4held.size) :
    (searchSideBoard t x).sudo_5Board_4held[5] = false := by
  simp [searchSideBoard, putAcross, built_held_arr, Array.getElem_set, Array.getElem_mkArray]

theorem side_mark (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_6marker = -1 := by
  simp [searchSideBoard, putAcross, built_marker_down]

theorem side_ctrl (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t) := by
  simp [searchSideBoard, putAcross, built_ctrl_eq]

theorem side_mx (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_4cost.sudo_5Costs_17script_marker_max = 0 := by
  simp [searchSideBoard, putAcross, built_mx0]

theorem side_home1 (t : Spec.Tier) (x : List Nat)
    (h : 1 < (searchSideBoard t x).sudo_5Board_4home.size) :
    (searchSideBoard t x).sudo_5Board_4home[1] = (#[] : Array Int) := by
  simp [searchSideBoard, putAcross, built_home_blank, Array.getElem_set, Array.getElem_mkArray]

theorem side_home5 (t : Spec.Tier) (x : List Nat)
    (h : 5 < (searchSideBoard t x).sudo_5Board_4home.size) :
    (searchSideBoard t x).sudo_5Board_4home[5] = (#[] : Array Int) := by
  simp [searchSideBoard, putAcross, built_home_blank, Array.getElem_set, Array.getElem_mkArray]

theorem side_moves (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_4cost.sudo_5Costs_5moves =
      ((pegCount x + pegCount x : Nat) : Int) := by
  simp [searchSideBoard, ofNat_eq_natCast]

theorem side_flag (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_9marker_on = false := by
  simp [searchSideBoard, putAcross, built_flag_off]

theorem side_bench (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_8bench_on = false := by
  simp [searchSideBoard, putAcross, built_bench_off]

theorem side_tier (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_1t = embTier t := by
  simp [searchSideBoard, putAcross, built_tier]

theorem side_ops (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0 := by
  simp [searchSideBoard, putAcross, built_ops_blank]

theorem side_strict (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0 := by
  simp [searchSideBoard, putAcross, built_strict]

theorem side_hole (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0 := by
  simp [searchSideBoard, putAcross, built_hole]

theorem side_slides (t : Spec.Tier) (x : List Nat) :
    (searchSideBoard t x).sudo_5Board_4cost.sudo_5Costs_6slides = 0 := by
  simp [searchSideBoard, putAcross, built_slides0]

theorem side_occ (t : Spec.Tier) (x : List Nat) :
    countHeld (searchSideBoard t x).sudo_5Board_4held 7 = 2 := by
  simpa [searchSideBoard] using put_occ_side t x

/-- Setting the bottom again does not change the held count. The peak is that count. -/
theorem side_peak (t : Spec.Tier) (x : List Nat)
    (hF : 2 < (searchSideBoard t x).sudo_5Board_4held.size) :
    (searchSideBoard t x).sudo_5Board_4held[2] = true ∧
    (searchSideBoard t x).sudo_5Board_4cost.sudo_5Costs_4peak =
      (raisedPeak 1 (countHeld
        ((searchSideBoard t x).sudo_5Board_4held.set ⟨2, hF⟩ true) 7) : Int) := by
  have htrue : (searchSideBoard t x).sudo_5Board_4held[2] = true := by
    simp [searchSideBoard, Array.getElem_set]
  refine ⟨htrue, ?_⟩
  have hid := set_true_id _ 2 hF htrue
  have hc : countHeld ((searchSideBoard t x).sudo_5Board_4held.set ⟨2, hF⟩ true) 7 = 2 := by
    rw [hid, side_occ]
  rw [hc, raisedPeak]
  simp [searchSideBoard, ofNat_eq_natCast]

theorem putAcross_src (t : Spec.Tier) (x : List Nat) :
    (putAcross t x).sudo_5Board_4held[3]'(putAcross_held3 t x) = true := by
  simp [putAcross, Array.getElem_set]

theorem putAcross_arr (t : Spec.Tier) (x : List Nat) :
    (putAcross t x).sudo_5Board_4home[3]'(putAcross_home3 t x) = embed x := by
  simp [putAcross, Array.getElem_set]

theorem putAcross_empty2 (t : Spec.Tier) (x : List Nat) :
    (putAcross t x).sudo_5Board_4held[2]'(putAcross_held2 t x) = false := by
  simp [putAcross, built_held_arr, Array.getElem_set, Array.getElem_mkArray]

theorem putAcross_moves (t : Spec.Tier) (x : List Nat) :
    (putAcross t x).sudo_5Board_4cost.sudo_5Costs_5moves = (pegCount x : Int) := by
  simp [putAcross, Nat.zero_add, ofNat_eq_natCast]

theorem putAcross_peak1 (t : Spec.Tier) (x : List Nat) :
    (putAcross t x).sudo_5Board_4cost.sudo_5Costs_4peak = (1 : Int) := by
  simp [putAcross, built_peak1, ofNat_eq_natCast]

theorem putAcross_n (t : Spec.Tier) (x : List Nat) :
    (putAcross t x).sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat t.n := by
  simp [putAcross, built_tier, embTier]

private theorem held3_empty (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4held[3]'(heldIx t 3 (by decide)) = false := by
  have hb : 3 < (Array.mkArray 8 false).size := by simp [Array.size_mkArray]
  exact cell_eq_of (built_held_blank t) (hb := hb) (by simp [Array.getElem_mkArray])

private theorem cube_room (peg n bench : Nat) (hp : peg ≤ n) :
    peg + peg ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    peg + peg + 2 * n ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    peg + peg + 2 * n + 3 * (bench - n) ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    3 * (n - 1) ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    n ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    bench ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 ∧
    (1 : Nat) ≤ 2 * (n * (n + 1)) + 12 * bench + 24 * n + 8 := by
  omega

/-- `curve_side` after the planted copy: `cube bottom bottom`. -/
theorem search_cube (t : Spec.Tier) (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj : j < t.n) :
    ∃ b',
      (do
          let b ← Ecbs.new_board (embTier t)
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b Ecbs.base_across x
          let b ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
          Ecbs.cube b Ecbs.bottom Ecbs.bottom) = .ok b' ∧
        b'.sudo_5Board_8bench_on = true ∧
        b'.sudo_5Board_8bench_to = Ecbs.bottom ∧
        b'.sudo_5Board_5bench =
          embed (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen (basisPeg t.n j))) ∧
        (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen (basisPeg t.n j))).take t.n =
          fieldCube t.n t.k t.benchlen (basisPeg t.n j) ∧
        (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen (basisPeg t.n j))).length =
          t.benchlen ∧
        (∀ i, t.n ≤ i →
          ∀ hi : i <
            (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen (basisPeg t.n j))).length,
            (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen (basisPeg t.n j)))[i] = 0) ∧
        b'.sudo_5Board_9marker_on = false ∧
        b'.sudo_5Board_4home.size = 8 ∧
        b'.sudo_5Board_4held.size = 8 ∧
        (∀ h : 2 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[2] = false) ∧
        (∀ h : 2 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[2] = (#[] : Array Int)) ∧
        (∀ h : 3 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[3] = true) ∧
        (∀ h : 3 < b'.sudo_5Board_4home.size,
          b'.sudo_5Board_4home[3] = embed (basisPeg t.n j)) ∧
        (∀ h : 6 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[6] = false) ∧
        b'.sudo_5Board_4cost.sudo_5Costs_5moves =
          Int.ofNat (cubeMoves (pegCount (basisPeg t.n j) + pegCount (basisPeg t.n j))
            (basisPeg t.n j) t.n t.k t.benchlen) ∧
        b'.sudo_5Board_4cost.sudo_5Costs_6slides = 0 ∧
        (∃ pk, b'.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk) ∧
        (∃ ps, b'.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps) ∧
        (∃ hole, b'.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole) ∧
        b'.sudo_5Board_1t = embTier t ∧
        0 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size ∧
        (∀ h : 0 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size,
          b'.sudo_5Board_4cost.sudo_5Costs_3ops[0] = 0) ∧
        (∀ h : 1 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[1] = false) ∧
        (∀ h : 5 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[5] = false) ∧
        b'.sudo_5Board_6marker = -1 ∧
        b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (tierR t) ∧
        b'.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = 0 ∧
        b'.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 ∧
        (∀ h : 1 < b'.sudo_5Board_4cost.sudo_5Costs_3ops.size,
          b'.sudo_5Board_4cost.sudo_5Costs_3ops[1] = 1) ∧
        (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = (#[] : Array Int)) ∧
        (∀ h : 5 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[5] = (#[] : Array Int)) := by
  let x := basisPeg t.n j
  have hx : x.length = t.n := basisPeg_length t.n j
  have hxt : allTritList x := basisPeg_trits t.n j
  have hpeg : pegCount x ≤ t.n := by
    have h := pegCount_le x
    rwa [hx] at h
  have hroom := cube_room (pegCount x) t.n t.benchlen hpeg
  have fit (m : Nat) (hm : m ≤ 2 * (t.n * (t.n + 1)) + 12 * t.benchlen + 24 * t.n + 8) :
      FitsLen m :=
    curveLayFit t.n t.benchlen m hsh.n_small hsh.small.2.2.2 hm
  have hfn : FitsLen t.n := fit t.n hroom.2.2.2.2.1
  have hfit0 : FitsLen (0 + pegCount x) := fit (0 + pegCount x) (by omega)
  have hn0 : (builtBoard t).sudo_5Board_1t.sudo_4Tier_1n = (x.length : Int) := by
    rw [built_tier, hx]
    exact ofNat_eq_natCast _
  have hput := put_refines (builtBoard t) 3 x 0 1
    (homeIx t 3 (by decide)) (heldIx t 3 (by decide)) (held7_le t) (held3_empty t)
    hn0 (by rw [hx]; exact hfn)
    (by rw [built_moves0]; rfl) (by rw [built_peak1]; rfl) hfit0
  rw [putAcross_place] at hput
  have hcopy := curve_copy_across (putAcross t x) x t.n (pegCount x) 1
    (putAcross_home2 t x) (putAcross_held2 t x)
    (putAcross_home3 t x) (putAcross_held3 t x)
    (by rw [putAcross_szD]; decide)
    (putAcross_src t x) (putAcross_arr t x) (putAcross_empty2 t x)
    (by rw [putAcross_n]; exact ofNat_eq_natCast _)
    hx hfn (putAcross_moves t x) (putAcross_peak1 t x)
    (fit (pegCount x + pegCount x) hroom.1)
  rw [searchSide_place] at hcopy
  let b := searchSideBoard t x
  have hF : 2 < b.sudo_5Board_4held.size := by rw [side_szD]; decide
  have hHome : 2 < b.sudo_5Board_4home.size := by rw [side_szH]; decide
  have hpk := side_peak t x hF
  have hops1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [side_ops]; simp [Array.size_mkArray]
  have hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (0 : Int) := by
    have hb : 1 < (Array.mkArray 5 0).size := by simp [Array.size_mkArray]
    exact cell_eq_of (side_ops t x) (hb := hb) (by simp [Array.getElem_mkArray])
  have h3D : 3 < b.sudo_5Board_4held.size := by rw [side_szD]; decide
  have h3H : 3 < b.sudo_5Board_4home.size := by rw [side_szH]; decide
  have h6D : 6 < b.sudo_5Board_4held.size := by rw [side_szD]; decide
  have hcube := curve_cube_bottom b x t.w t.h t.r t.n t.k (pegCount x + pegCount x) 0
      t.benchlen 1 0 0 t.combgap
      (side_flag t x) (side_bench t x) hops1 hop1 (fit 1 hroom.2.2.2.2.2.2)
      (by rw [side_tier]; rfl) (by rw [side_tier]; rfl) sat.cube_span
      hF hHome hpk.1 (side_home2 t x hHome) (by rw [side_szD]; decide) hOk.n_pos
      (by rw [side_tier]; exact ofNat_eq_natCast _) hx hfn (side_moves t x) hpk.2
      (side_strict t x) hxt
      (fit (3 * (t.n - 1)) hroom.2.2.2.1)
      (fit (pegCount x + pegCount x + 2 * t.n) hroom.2.1)
      ⟨hsh.w0, hsh.h0, hsh.rlt, hsh.r0, hsh.n_eq, hsh.k_le, hsh.gap⟩
      (by rw [side_tier]; rfl) (by rw [side_tier]; rfl) (by rw [side_tier]; rfl)
      (by rw [side_tier]; rfl)
      (by rw [side_hole]; exact (ofNat_eq_natCast 0).symm)
      hsh.small hsh.n_small (fit t.benchlen hroom.2.2.2.2.2.1)
      (fit (pegCount x + pegCount x + 2 * t.n + 3 * (t.benchlen - t.n)) hroom.2.2.1)
  obtain ⟨b', hok, hon, hto, hbench, htake, hheld, hhome, hmk', hhigh, hmov, hpeakOut,
      hslides, ht, hops', hstrict', hhole', hmarkC, hctrlC, hmxC⟩ := hcube
  have hlenL : (laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen x)).length = t.benchlen := by
    have hstrip := combStrip_length t.n t.benchlen x
    have hnle : t.n ≤ t.benchlen := by
      have hsp := sat.cube_span
      omega
    rw [laneFold_length t.n (t.n - t.k) (combStrip t.n t.benchlen x) (by rwa [hstrip])]
    exact hstrip
  refine ⟨b', ?_, hon, hto, ?_, ?_, hlenL, ?_, hmk', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨_, hpeakOut⟩, ⟨_, hstrict'⟩, ⟨_, hhole'⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hputS : Ecbs.put (builtBoard t) ((searchBase : Nat) : Int) (embed x) =
        .ok (putAcross t x) := by
      simpa [searchBase] using hput
    have hcopyS : Ecbs.copy_band (putAcross t x) Ecbs.bottom ((searchBase : Nat) : Int) false =
        .ok (searchSideBoard t x) := by
      simpa [searchBase_int] using hcopy
    rw [new_board_refines t hOk, ok_bind, bind_assoc, basis_fill t.n j hj, ok_bind,
      ← searchBase_int, hputS, ok_bind, hcopyS, ok_bind]
    exact hok
  · simpa [x] using hbench
  · simpa [x] using htake
  · intro i hi hlt
    have hltb : i < t.benchlen := by rwa [hlenL] at hlt
    have hc := hhigh i hi hltb
    rwa [coeff_eq_get _ _ hlt] at hc
  · rw [hhome, Array.size_set, side_szH]
  · rw [hheld, Array.size_set, side_szD]
  · intro h
    have hget := get_eq_of_array hheld 2 h
    simpa [Array.getElem_set] using hget
  · intro h
    have hget := get_eq_of_array hhome 2 h
    simpa [Array.getElem_set] using hget
  · intro h
    have hget := get_eq_of_array hheld 3 h
    have hne : (2 : Nat) ≠ 3 := by decide
    simpa [Array.getElem_set, hne] using hget.trans (side_held3 t x h3D)
  · intro h
    have hget := get_eq_of_array hhome 3 h
    have hne : (2 : Nat) ≠ 3 := by decide
    simpa [Array.getElem_set, hne] using hget.trans (side_home3 t x h3H)
  · intro h
    have hget := get_eq_of_array hheld 6 h
    have hne : (2 : Nat) ≠ 6 := by decide
    simpa [Array.getElem_set, hne] using hget.trans (side_held6 t x h6D)
  · simpa [x] using hmov
  · rw [hslides, side_slides]
  · rw [ht, side_tier]
  · rw [hops', Array.size_set]
    exact Nat.lt_trans (by decide : 0 < 1) hops1
  · intro h
    have hget := get_eq_of_array hops' 0 h
    have hne : (1 : Nat) ≠ 0 := by decide
    have h0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]'(by
        rw [side_ops]; simp [Array.size_mkArray]) = 0 := by
      have hb : 0 < (Array.mkArray 5 0).size := by simp [Array.size_mkArray]
      exact cell_eq_of (side_ops t x) (hb := hb) (by simp [Array.getElem_mkArray])
    simpa [Array.getElem_set, hne] using hget.trans h0
  · intro h
    have hget := get_eq_of_array hheld 1 h
    have hne : (2 : Nat) ≠ 1 := by decide
    have h1b : 1 < b.sudo_5Board_4held.size := by rw [side_szD]; decide
    simpa [Array.getElem_set, hne] using hget.trans (side_held1 t x h1b)
  · intro h
    have hget := get_eq_of_array hheld 5 h
    have hne : (2 : Nat) ≠ 5 := by decide
    have h5b : 5 < b.sudo_5Board_4held.size := by rw [side_szD]; decide
    simpa [Array.getElem_set, hne] using hget.trans (side_held5 t x h5b)
  · rw [hmarkC]; exact side_mark t x
  · rw [hctrlC]; exact side_ctrl t x
  · rw [hmxC]; exact side_mx t x
  · rw [hops', Array.size_set, side_ops t x]
    simp [Array.size_mkArray]
  · intro h
    have hget := get_eq_of_array hops' 1 h
    simp [Array.getElem_set, Nat.zero_add, ofNat_eq_natCast] at hget
    exact hget
  · intro h
    have hget := get_eq_of_array hhome 1 h
    have hne : (2 : Nat) ≠ 1 := by decide
    have h1b : 1 < b.sudo_5Board_4home.size := by rw [side_szH]; decide
    simpa [Array.getElem_set, hne] using hget.trans (side_home1 t x h1b)
  · intro h
    have hget := get_eq_of_array hhome 5 h
    have hne : (2 : Nat) ≠ 5 := by decide
    have h5b : 5 < b.sudo_5Board_4home.size := by rw [side_szH]; decide
    simpa [Array.getElem_set, hne] using hget.trans (side_home5 t x h5b)

end EcbsLink2.Link2
