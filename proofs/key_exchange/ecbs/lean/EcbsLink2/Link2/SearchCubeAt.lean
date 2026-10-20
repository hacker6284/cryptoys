/-
  `cube bottom bottom` on a `PlantAt` board. The plant's move counter is `mv0`,
  its slide counter is `sl0`, and its control counter is `c0 + tierR`
  (`c0` is the charge from earlier holes; a fresh board has `c0 = 0`).
  The cube adds `cubeMoves` of the two peg copies, leaves the slides at `sl0`,
  and leaves the control counter where it was.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchPlant
import EcbsLink2.Link2.OpenBoard

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem bind_assoc {α β γ : Type}
    (m : Except SudoRt.Trap α) (f : α → Except SudoRt.Trap β) (g : β → Except SudoRt.Trap γ) :
    (m >>= fun x => f x >>= g) = ((m >>= f) >>= g) := by
  cases m <;> simp [ok_bind, error_bind]

private theorem do_copy (b : Ecbs.Board) (n j : Nat) :
    (do
        let x ← SudoRt.filledL (Int.ofNat n) (0 : Int)
        let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
        let b ← Ecbs.put b Ecbs.base_across x
        Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false) =
      ((do
          let x ← SudoRt.filledL (Int.ofNat n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          Ecbs.put b Ecbs.base_across x) >>= fun b =>
        Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false) :=
  bind_assoc
    (SudoRt.filledL (Int.ofNat n) (0 : Int) >>= fun x => SudoRt.putL x (Int.ofNat j) (1 : Int))
    (fun x => Ecbs.put b Ecbs.base_across x)
    (fun b => Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false)

private theorem do_put (b : Ecbs.Board) (n j : Nat) :
    (do
        let x ← SudoRt.filledL (Int.ofNat n) (0 : Int)
        let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
        Ecbs.put b Ecbs.base_across x) =
      ((do
          let x ← SudoRt.filledL (Int.ofNat n) (0 : Int)
          SudoRt.putL x (Int.ofNat j) (1 : Int)) >>= fun x =>
        Ecbs.put b Ecbs.base_across x) :=
  bind_assoc
    (SudoRt.filledL (Int.ofNat n) (0 : Int))
    (fun x => SudoRt.putL x (Int.ofNat j) (1 : Int))
    (fun x => Ecbs.put b Ecbs.base_across x)

private theorem do_cube (b : Ecbs.Board) (n j : Nat) :
    (do
        let x ← SudoRt.filledL (Int.ofNat n) (0 : Int)
        let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
        let b ← Ecbs.put b Ecbs.base_across x
        let b ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
        Ecbs.cube b Ecbs.bottom Ecbs.bottom) =
      ((do
          let x ← SudoRt.filledL (Int.ofNat n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b Ecbs.base_across x
          Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false) >>= fun bc =>
        Ecbs.cube bc Ecbs.bottom Ecbs.bottom) := by
  rw [bind_assoc, bind_assoc, bind_assoc, do_copy, do_put]

private theorem cubeMoves_shift (mv0 a : Nat) (xs : List Nat) (n k bench : Nat) :
    cubeMoves (mv0 + a) xs n k bench = mv0 + cubeMoves a xs n k bench := by
  simp only [cubeMoves]
  omega

private theorem shape_of (t : Spec.Tier) (h : TierShape t) : BoardShape t.w t.h t.r t.n t.k where
  hw0 := h.w0
  hh0 := h.h0
  hrR := h.rlt
  hrP := h.r0
  hnE := h.n_eq
  hkLe := h.k_le
  hgap := h.gap

private theorem peak_if (pk occ : Nat) :
    (if pk < occ then occ else pk) = raisedPeak pk occ := by
  unfold raisedPeak
  rfl

private theorem countHeld_set_eq (a c : Array Bool) (h : a = c) (i : Nat)
    (ha : i < a.size) (k : Nat) :
    countHeld (a.set ⟨i, ha⟩ true) k = countHeld (c.set ⟨i, h ▸ ha⟩ true) k := by
  subst h
  rfl

private theorem peg_le (n : Nat) (xs : List Nat) (h : xs.length = n) : pegCount xs ≤ n := by
  have hlen : pegCount xs ≤ xs.length := pegCount_le xs
  rwa [h] at hlen

private theorem two_add (mv peg : Nat) : (mv + peg) + peg = mv + (peg + peg) := by
  omega

private theorem per_ge (n bench : Nat) : plantRoom n bench ≤ perHole n bench := by
  unfold perHole
  omega

private theorem room_mul (p k : Nat) (hk : 0 < k) : p ≤ p * k := by
  have hmul : p * 1 ≤ p * k := Nat.mul_le_mul_left p hk
  simpa [Nat.mul_one] using hmul

private theorem room_in (n bench k : Nat) (hk : 0 < k) :
    plantRoom n bench ≤ perHole n bench * k :=
  Nat.le_trans (per_ge n bench) (room_mul _ _ hk)

private theorem le_budget (mv extra n bench k : Nat) (hk : 0 < k)
    (he : extra ≤ plantRoom n bench) :
    mv + extra ≤ mv + perHole n bench * k :=
  Nat.le_trans (Nat.add_le_add_left he mv) (Nat.add_le_add_left (room_in n bench k hk) mv)

private theorem under_budget (extra mv n bench k : Nat) (hk : 0 < k)
    (he : extra ≤ plantRoom n bench) :
    extra ≤ mv + perHole n bench * k :=
  Nat.le_trans (Nat.le_trans he (room_in n bench k hk))
    (Nat.le_add_left (perHole n bench * k) mv)

private theorem n_room (n bench : Nat) : n ≤ plantRoom n bench := by
  unfold plantRoom
  omega

private theorem three_room (n bench : Nat) : 3 * (n - 1) ≤ plantRoom n bench := by
  unfold plantRoom
  omega

private theorem bench_room (n bench : Nat) : bench ≤ plantRoom n bench := by
  unfold plantRoom
  omega

private theorem cube_add_room (peg n bench : Nat) (hp : peg ≤ n) :
    peg + peg + 2 * n + 3 * (bench - n) ≤ plantRoom n bench := by
  unfold plantRoom
  omega

private theorem four_room (peg n bench : Nat) (hp : peg ≤ n) :
    peg + peg + 2 * n ≤ plantRoom n bench := by
  have h := cube_add_room peg n bench hp
  omega

private theorem two_peg_room (peg n bench : Nat) (hp : peg ≤ n) :
    peg + peg ≤ plantRoom n bench := by
  have h := four_room peg n bench hp
  omega

private theorem one_peg_room (peg n bench : Nat) (hp : peg ≤ n) :
    peg ≤ plantRoom n bench :=
  Nat.le_trans hp (n_room n bench)

private theorem n_le_bench (n bench cg : Nat) (h : 3 * (n - 1) + cg < bench) : n ≤ bench := by
  omega

private theorem lane_len (n k bench : Nat) (xs : List Nat) (hn : n ≤ bench) :
    (laneFold n (n - k) (combStrip n bench xs)).length = bench := by
  have hstrip := combStrip_length n bench xs
  rw [laneFold_length n (n - k) (combStrip n bench xs) (by rwa [hstrip])]
  exact hstrip

private theorem mv_fold (mv peg n bench : Nat) :
    (mv + (peg + peg)) + 2 * n + 3 * (bench - n) =
      mv + (peg + peg + 2 * n + 3 * (bench - n)) := by
  omega

private theorem mv_in (mv peg n : Nat) :
    (mv + (peg + peg)) + 2 * n = mv + (peg + peg + 2 * n) := by
  omega

private theorem set_true_twice (a : Array Bool) (i : Nat) (hi : i < a.size)
    (h2 : i < (a.set ⟨i, hi⟩ true).size) :
    (a.set ⟨i, hi⟩ true).set ⟨i, h2⟩ true = a.set ⟨i, hi⟩ true := by
  apply Array.ext
  · simp [Array.size_set]
  · intro j _ _
    by_cases h : j = i
    · simp [h, Array.getElem_set]
    · simp [Array.getElem_set, h]

private theorem set_at_true (a : Array Bool) (i : Nat) (hi : i < a.size) :
    (a.set ⟨i, hi⟩ true)[i]'(by rw [Array.size_set]; exact hi) = true := by
  simp [Array.getElem_set]

private theorem set_at_val {α : Type} (a : Array α) (i : Nat) (hi : i < a.size) (v : α) :
    (a.set ⟨i, hi⟩ v)[i]'(by rw [Array.size_set]; exact hi) = v := by
  simp [Array.getElem_set]

private theorem of_some {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) (hi : i < a.size) : a[i] = v := by
  rw [Array.getElem?_eq_getElem hi] at h
  injection h

private theorem place_held_ne (b : Ecbs.Board) (home j : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (mv pk : Nat) (hne : home ≠ j) :
    (placeBoard b home hH hD xs mv pk).sudo_5Board_4held[j]? =
      b.sudo_5Board_4held[j]? := by
  rw [place_held_eq, Array.getElem?_set_ne _ ⟨home, hD⟩ true hne]

private theorem place_home_ne (b : Ecbs.Board) (home j : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (xs : List Nat) (mv pk : Nat) (hne : home ≠ j) :
    (placeBoard b home hH hD xs mv pk).sudo_5Board_4home[j]? =
      b.sudo_5Board_4home[j]? := by
  rw [place_home_eq, Array.getElem?_set_ne _ ⟨home, hH⟩ (embed xs) hne]

private theorem eq_idx {α : Type} {a b : Array α} (h : a = b) (j : Nat) :
    a[j]? = b[j]? := by
  rw [h]

def cubeLane (t : Spec.Tier) (j : Nat) : List Nat :=
  laneFold t.n (t.n - t.k) (combStrip t.n t.benchlen (basisPeg t.n j))

def cubeSpend (t : Spec.Tier) (j : Nat) : Nat :=
  cubeMoves (pegCount (basisPeg t.n j) + pegCount (basisPeg t.n j))
    (basisPeg t.n j) t.n t.k t.benchlen

attribute [irreducible] cubeLane cubeSpend

/-- The board after cubing a planted peg. Counters are relative to the plant. -/
structure CubeAt (b : Ecbs.Board) (t : Spec.Tier) (j mv0 sl0 c0 : Nat) : Prop where
  benchOn : b.sudo_5Board_8bench_on = true
  benchTo : b.sudo_5Board_8bench_to = Ecbs.bottom
  bench : b.sudo_5Board_5bench = embed (cubeLane t j)
  take : (cubeLane t j).take t.n = fieldCube t.n t.k t.benchlen (basisPeg t.n j)
  len : (cubeLane t j).length = t.benchlen
  high : ∀ i, t.n ≤ i → ∀ hi : i < (cubeLane t j).length, (cubeLane t j)[i] = 0
  markerOn : b.sudo_5Board_9marker_on = false
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  held2 : ∀ h : 2 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[2] = false
  home2 : ∀ h : 2 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[2] = (#[] : Array Int)
  held3 : ∀ h : 3 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[3] = true
  home3 : ∀ h : 3 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[3] = embed (basisPeg t.n j)
  held6 : ∀ h : 6 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[6] = false
  moves : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (mv0 + cubeSpend t j)
  slides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl0
  peak : ∃ (pk : Nat), b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk
  strict : ∃ (ps : Nat), b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps
  hole : ∃ (hole : Nat), b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole
  tier : b.sudo_5Board_1t = embTier t
  opsSz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5
  ops0 : ∃ (o0 : Nat), (∀ h : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (o0 : Int)) ∧
    FitsLen (o0 + 1)
  held1 : ∀ h : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1] = false
  held5 : ∀ h : 5 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[5] = false
  marker : b.sudo_5Board_6marker = -1
  ctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)
  mx : ∃ (mx : Nat), b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx
  ops1 : ∃ (o1 : Nat), ∀ h : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
    b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = ((o1 + 1 : Nat) : Int)
  home1 : ∀ h : 1 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[1] = (#[] : Array Int)
  home5 : ∀ h : 5 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[5] = (#[] : Array Int)
  held0 : ∀ h : 0 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[0] = false
  home0 : ∀ h : 0 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[0] = (#[] : Array Int)

private theorem set_true_id (a : Array Bool) (i : Nat) (hi : i < a.size) (ht : a[i] = true) :
    a.set ⟨i, hi⟩ true = a := by
  apply Array.ext
  · simp [Array.size_set]
  · intro j _ _
    by_cases h : j = i
    · simp [h, Array.getElem_set, ht]
    · simp [Array.getElem_set, Ne.symm h]

/-- Setting an already-true home does not change the held count the peak reads. -/
private theorem peak_set (b : Ecbs.Board) (pk : Nat) (hF : 2 < b.sudo_5Board_4held.size)
    (htrue : b.sudo_5Board_4held[2] = true)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak =
      (raisedPeak pk (countHeld b.sudo_5Board_4held 7) : Int)) :
    b.sudo_5Board_4cost.sudo_5Costs_4peak =
      (raisedPeak pk (countHeld (b.sudo_5Board_4held.set ⟨2, hF⟩ true) 7) : Int) := by
  have hid := set_true_id b.sudo_5Board_4held 2 hF htrue
  rw [hpeak, hid]

/-- The copied board's peak is `raisedPeak` of the pre-copy peak and the held count. -/
private theorem copy_peak_eq (b : Ecbs.Board)
    (hH : 2 < b.sudo_5Board_4home.size) (hD : 2 < b.sudo_5Board_4held.size)
    (x : List Nat) (mv pk : Nat)
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int)) :
    let bC := placeBoard b 2 hH hD x mv pk
    bC.sudo_5Board_4held[2]'(by rw [place_held_eq, Array.size_set]; exact hD) = true ∧
      bC.sudo_5Board_4cost.sudo_5Costs_4peak =
        (raisedPeak pk (countHeld bC.sudo_5Board_4held 7) : Int) := by
  let bC := placeBoard b 2 hH hD x mv pk
  have hheld : bC.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨2, hD⟩ true :=
    place_held_eq b 2 hH hD x mv pk
  have htrue : bC.sudo_5Board_4held[2]'(by rw [place_held_eq, Array.size_set]; exact hD) = true :=
    cell_eq_of hheld (set_at_true _ 2 hD)
  have hraw := place_peak_nat b 2 hH hD x mv pk hpk
  refine ⟨htrue, ?_⟩
  rw [peak_if pk (countHeld (b.sudo_5Board_4held.set ⟨2, hD⟩ true) 7)] at hraw
  have hcount : countHeld bC.sudo_5Board_4held 7 =
      countHeld (b.sudo_5Board_4held.set ⟨2, hD⟩ true) 7 := by
    rw [hheld]
  rw [← hcount] at hraw
  rw [hraw]
  exact ofNat_eq_natCast _

/-- Homes the cube does not rewrite, after the peg is planted and copied. -/
structure CopyAt (b : Ecbs.Board) (t : Spec.Tier) (j mv0 sl0 c0 : Nat) : Prop where
  szH : b.sudo_5Board_4home.size = 8
  szD : b.sudo_5Board_4held.size = 8
  home2 : b.sudo_5Board_4home[2]? = some (embed (basisPeg t.n j))
  held2 : b.sudo_5Board_4held[2]? = some true
  home3 : b.sudo_5Board_4home[3]? = some (embed (basisPeg t.n j))
  held3 : b.sudo_5Board_4held[3]? = some true
  moves : b.sudo_5Board_4cost.sudo_5Costs_5moves =
    Int.ofNat (mv0 + (pegCount (basisPeg t.n j) + pegCount (basisPeg t.n j)))
  slides : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl0
  ctrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)
  marker : b.sudo_5Board_6marker = -1
  markerOn : b.sudo_5Board_9marker_on = false
  benchOff : b.sudo_5Board_8bench_on = false
  tier : b.sudo_5Board_1t = embTier t
  peak : ∃ pk, b.sudo_5Board_4cost.sudo_5Costs_4peak =
    (raisedPeak pk (countHeld b.sudo_5Board_4held 7) : Int)
  strict : ∃ (ps : Nat), b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (ps : Int)
  hole : ∃ (hole : Nat), b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole
  mx : ∃ (mx : Nat), b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx
  opsSz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5
  ops0 : ∃ (o0 : Nat), (∀ h : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0] = (o0 : Int)) ∧ FitsLen (o0 + 1)
  ops1 : ∃ (o1 : Nat), (∀ h : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      b.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (o1 : Int)) ∧ FitsLen (o1 + 1)
  held0 : b.sudo_5Board_4held[0]? = some false
  held1 : b.sudo_5Board_4held[1]? = some false
  held5 : b.sudo_5Board_4held[5]? = some false
  held6 : b.sudo_5Board_4held[6]? = some false
  home0 : b.sudo_5Board_4home[0]? = some (#[] : Array Int)
  home1 : b.sudo_5Board_4home[1]? = some (#[] : Array Int)
  home5 : b.sudo_5Board_4home[5]? = some (#[] : Array Int)

theorem copy_at (b : Ecbs.Board) (t : Spec.Tier) (holesLeft : Nat)
    (hp : PlantAt b t holesLeft) (j : Nat) (hj : j < t.n)
    (mv0 sl0 c0 : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv0)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)) :
    ∃ bC,
      (do
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b Ecbs.base_across x
          Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false) = .ok bC ∧
        CopyAt bC t j mv0 sl0 c0 := by
  let x := basisPeg t.n j
  have hx : x.length = t.n := basisPeg_length t.n j
  have hpeg := peg_le t.n x hx
  rcases hp.moves with ⟨mvP, hmvP, hfit0⟩
  have hmvSame : mvP = mv0 := Int.ofNat.inj (hmvP.symm.trans hmv)
  have hfit : FitsLen (mv0 + perHole t.n t.benchlen * holesLeft) := by
    simpa [hmvSame] using hfit0
  rcases hp.peak with ⟨pk0, hpk0⟩
  rcases hp.strict with ⟨ps0, hps0⟩
  rcases hp.hole with ⟨hole0, hhole0⟩
  rcases hp.mx with ⟨mx0, hmx0⟩
  rcases hp.ops0 with ⟨o0, ho0, hfo0⟩
  rcases hp.ops1 with ⟨o1, ho1, hfo1⟩
  have hk := hp.holesPos
  have hH3 : 3 < b.sudo_5Board_4home.size := by rw [hp.szH]; decide
  have hD3 : 3 < b.sudo_5Board_4held.size := by rw [hp.szD]; decide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by rw [hp.szD]; decide
  have hempty3 : b.sudo_5Board_4held[3] = false := of_some _ 3 false hp.baseOff hD3
  have hmvI : b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv0 : Int) := by
    rw [hmv]; exact ofNat_eq_natCast mv0
  have hpkI : b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk0 : Int) := by
    rw [hpk0]; exact ofNat_eq_natCast pk0
  have hn : b.sudo_5Board_1t.sudo_4Tier_1n = (x.length : Int) := by
    rw [hp.tier, hx]; simp [embTier, ofNat_eq_natCast]
  have hfn : FitsLen t.n :=
    FitsLen.of_le hfit (under_budget t.n mv0 t.n t.benchlen holesLeft hk (n_room t.n t.benchlen))
  have hfitPeg : FitsLen (mv0 + pegCount x) :=
    FitsLen.of_le hfit (le_budget mv0 (pegCount x) t.n t.benchlen holesLeft hk
      (one_peg_room (pegCount x) t.n t.benchlen hpeg))
  have hput := put_refines b 3 x mv0 pk0 hH3 hD3 h7 hempty3 hn (by rw [hx]; exact hfn)
    hmvI hpkI hfitPeg
  let bP := placeBoard b 3 hH3 hD3 x mv0 pk0
  let occP := countHeld (b.sudo_5Board_4held.set ⟨3, hD3⟩ true) 7
  let pkP := if pk0 < occP then occP else pk0
  have hpkP : bP.sudo_5Board_4cost.sudo_5Costs_4peak = (pkP : Int) := by
    simp only [bP, pkP, occP]
    rw [place_peak_nat b 3 hH3 hD3 x mv0 pk0 hpkI]
    exact ofNat_eq_natCast _
  let mvIn := mv0 + pegCount x
  have hmvP : bP.sudo_5Board_4cost.sudo_5Costs_5moves = (mvIn : Int) := by
    simp only [bP, mvIn]
    rw [place_moves_eq]; exact ofNat_eq_natCast _
  have hszHP : bP.sudo_5Board_4home.size = 8 := by
    simp only [bP]; rw [place_home_eq, Array.size_set]; exact hp.szH
  have hszDP : bP.sudo_5Board_4held.size = 8 := by
    simp only [bP]; rw [place_held_eq, Array.size_set]; exact hp.szD
  have hH2P : 2 < bP.sudo_5Board_4home.size := by rw [hszHP]; decide
  have hD2P : 2 < bP.sudo_5Board_4held.size := by rw [hszDP]; decide
  have hH3P : 3 < bP.sudo_5Board_4home.size := by rw [hszHP]; decide
  have hD3P : 3 < bP.sudo_5Board_4held.size := by rw [hszDP]; decide
  have h7P : 7 ≤ bP.sudo_5Board_4held.size := by rw [hszDP]; decide
  have hsrc : bP.sudo_5Board_4held[3] = true := by
    have h? : bP.sudo_5Board_4held[3]? = some true := by
      simp only [bP]
      rw [place_held_eq, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hD3)]
      exact congrArg some (set_at_true _ 3 hD3)
    exact of_some _ 3 true h? hD3P
  have harr : bP.sudo_5Board_4home[3] = embed x := by
    have h? : bP.sudo_5Board_4home[3]? = some (embed x) := by
      simp only [bP]
      rw [place_home_eq, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hH3)]
      exact congrArg some (set_at_val _ 3 hH3 (embed x))
    exact of_some _ 3 (embed x) h? hH3P
  have hempty2 : bP.sudo_5Board_4held[2] = false := by
    have h? : bP.sudo_5Board_4held[2]? = some false := by
      simp only [bP]
      rw [place_held_ne b 3 2 hH3 hD3 x mv0 pk0 (by decide)]
      exact hp.botOff
    exact of_some _ 2 false h? hD2P
  have hnP : bP.sudo_5Board_1t.sudo_4Tier_1n = (x.length : Int) := by
    simp only [bP]; rw [place_tier_eq]; exact hn
  have hfit2 : FitsLen (mvIn + pegCount x) := by
    have hle := le_budget mv0 (pegCount x + pegCount x) t.n t.benchlen holesLeft hk
      (two_peg_room (pegCount x) t.n t.benchlen hpeg)
    have hs : mvIn + pegCount x = mv0 + (pegCount x + pegCount x) := by
      simpa [mvIn] using two_add mv0 (pegCount x)
    exact FitsLen.of_le hfit (hs.symm ▸ hle)
  have hcopy := copy_band_refines bP 2 3 x mvIn pkP hH2P hD2P hH3P hD3P h7P
    hsrc harr hempty2 hnP (by rw [hx]; exact hfn) hmvP hpkP hfit2
  let bC := placeBoard bP 2 hH2P hD2P x mvIn pkP
  have hpeak := copy_peak_eq bP hH2P hD2P x mvIn pkP hpkP
  have hszHC : bC.sudo_5Board_4home.size = 8 := by
    simp only [bC]; rw [place_home_eq, Array.size_set]; exact hszHP
  have hszDC : bC.sudo_5Board_4held.size = 8 := by
    simp only [bC]; rw [place_held_eq, Array.size_set]; exact hszDP
  have hdo :
      (do
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b Ecbs.base_across x
          Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false) = .ok bC := by
    rw [do_copy b t.n j, bind_assoc, basis_fill t.n j hj, ok_bind,
      show basisPeg t.n j = x from rfl, ← searchBase_int]
    simp only [searchBase]
    rw [hput, ok_bind, show Ecbs.bottom = ((2 : Nat) : Int) from rfl]
    simpa [bC, bP] using hcopy
  have stayH (i : Nat) (hne3 : (3 : Nat) ≠ i) (hne2 : (2 : Nat) ≠ i)
      (h0 : b.sudo_5Board_4held[i]? = some false) :
      bC.sudo_5Board_4held[i]? = some false := by
    simp only [bC, bP]
    rw [place_held_ne bP 2 i hH2P hD2P x mvIn pkP hne2,
      place_held_ne b 3 i hH3 hD3 x mv0 pk0 hne3]
    exact h0
  have stayA (i : Nat) (hne3 : (3 : Nat) ≠ i) (hne2 : (2 : Nat) ≠ i)
      (h0 : b.sudo_5Board_4home[i]? = some (#[] : Array Int)) :
      bC.sudo_5Board_4home[i]? = some (#[] : Array Int) := by
    simp only [bC, bP]
    rw [place_home_ne bP 2 i hH2P hD2P x mvIn pkP hne2,
      place_home_ne b 3 i hH3 hD3 x mv0 pk0 hne3]
    exact h0
  refine ⟨bC, hdo, ?_⟩
  refine
    { szH := hszHC
      szD := hszDC
      home2 := by
        simp only [bC, x]
        rw [place_home_eq, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hH2P)]
        exact congrArg some (set_at_val _ 2 hH2P (embed (basisPeg t.n j)))
      held2 := by
        have hlt : 2 < bC.sudo_5Board_4held.size := by rw [hszDC]; decide
        rw [Array.getElem?_eq_getElem hlt]
        exact congrArg some hpeak.1
      home3 := by
        simp only [bC, bP, x]
        rw [place_home_ne bP 2 3 hH2P hD2P (basisPeg t.n j) mvIn pkP (by decide),
          place_home_eq, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hH3)]
        exact congrArg some (set_at_val _ 3 hH3 (embed (basisPeg t.n j)))
      held3 := by
        simp only [bC, bP]
        rw [place_held_ne bP 2 3 hH2P hD2P x mvIn pkP (by decide),
          place_held_eq, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hD3)]
        exact congrArg some (set_at_true _ 3 hD3)
      moves := by
        simp only [bC, x]
        rw [place_moves_eq]
        have hs : mvIn + pegCount (basisPeg t.n j) =
            mv0 + (pegCount (basisPeg t.n j) + pegCount (basisPeg t.n j)) := by
          simpa [mvIn, x] using two_add mv0 (pegCount (basisPeg t.n j))
        rw [hs]
      slides := by simp only [bC, bP]; rw [place_slides_eq, place_slides_eq]; exact hsl
      ctrl := by simp only [bC, bP]; rw [place_ctrl_eq, place_ctrl_eq]; exact hc
      marker := by simp only [bC, bP]; rw [place_marker_eq, place_marker_eq]; exact hp.marker
      markerOn := by simp only [bC, bP]; rw [place_flag, place_flag]; exact hp.markerOn
      benchOff := by simp only [bC, bP]; rw [place_bench, place_bench]; exact hp.benchOff
      tier := by simp only [bC, bP]; rw [place_tier_eq, place_tier_eq]; exact hp.tier
      peak := ⟨pkP, by simp only [bC]; exact hpeak.2⟩
      strict := ⟨ps0, by
        simp only [bC, bP]
        rw [place_strict_eq, place_strict_eq, hps0]
        exact ofNat_eq_natCast ps0⟩
      hole := ⟨hole0, by simp only [bC, bP]; rw [place_hole_eq, place_hole_eq]; exact hhole0⟩
      mx := ⟨mx0, by simp only [bC, bP]; rw [place_mx_eq, place_mx_eq]; exact hmx0⟩
      opsSz := by simp only [bC, bP]; rw [place_ops_eq, place_ops_eq]; exact hp.opsSz
      ops0 := ⟨o0, fun h => cell_eq_of
        (by simp only [bC, bP]; rw [place_ops_eq, place_ops_eq])
        (ho0 (by rw [hp.opsSz]; decide)), hfo0⟩
      ops1 := ⟨o1, fun h => cell_eq_of
        (by simp only [bC, bP]; rw [place_ops_eq, place_ops_eq])
        (ho1 (by rw [hp.opsSz]; decide)), hfo1⟩
      held0 := stayH 0 (by decide) (by decide) hp.axOff
      held1 := stayH 1 (by decide) (by decide) hp.upOff
      held5 := stayH 5 (by decide) (by decide) hp.gapOff
      held6 := stayH 6 (by decide) (by decide) hp.spareOff
      home0 := stayA 0 (by decide) (by decide) hp.axHome
      home1 := stayA 1 (by decide) (by decide) hp.upHome
      home5 := stayA 5 (by decide) (by decide) hp.gapHome }

/-- Plant the basis peg, copy it into the bottom, and cube that copy.
    Moves come back as `mv0` plus `cubeMoves` of the two copies. Slides stay
    `sl0`. Control stays `c0 + tierR`. -/
theorem search_cube_at (b : Ecbs.Board) (t : Spec.Tier) (holesLeft : Nat)
    (hp : PlantAt b t holesLeft)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj : j < t.n)
    (mv0 sl0 c0 : Nat)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv0)
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)) :
    ∃ b',
      (do
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b Ecbs.base_across x
          let b ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
          Ecbs.cube b Ecbs.bottom Ecbs.bottom) = .ok b' ∧
        CubeAt b' t j mv0 sl0 c0 := by
  obtain ⟨bC, hdoC, c⟩ := copy_at b t holesLeft hp j hj mv0 sl0 c0 hmv hsl hc
  let x := basisPeg t.n j
  have hx : x.length = t.n := basisPeg_length t.n j
  have hxt : allTritList x := basisPeg_trits t.n j
  have hpeg := peg_le t.n x hx
  have hF : 2 < bC.sudo_5Board_4held.size := by rw [c.szD]; decide
  have hHome : 2 < bC.sudo_5Board_4home.size := by rw [c.szH]; decide
  have hHF : bC.sudo_5Board_4held[2] = true := of_some _ 2 true c.held2 hF
  have hArr : bC.sudo_5Board_4home[2] = embed x := by
    simpa [x] using of_some _ 2 (embed (basisPeg t.n j)) c.home2 hHome
  rcases c.peak with ⟨pk, hpk0⟩
  have hpeak := peak_set bC pk hF hHF hpk0
  rcases c.strict with ⟨ps0, hps⟩
  rcases c.hole with ⟨hole0, hhole⟩
  rcases c.mx with ⟨mx0, _hmx⟩
  rcases c.ops0 with ⟨o0, ho0, hfo0⟩
  rcases c.ops1 with ⟨o1, ho1, hfo1⟩
  have hops1 : 1 < bC.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [c.opsSz]; decide
  have hop1 : bC.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (o1 : Int) := ho1 hops1
  have h7 : 7 ≤ bC.sudo_5Board_4held.size := by rw [c.szD]; decide
  have hn : bC.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
    rw [c.tier]; exact ofNat_eq_natCast t.n
  rcases hp.moves with ⟨mvP, hmvP, hfit0⟩
  have hmvSame : mvP = mv0 := Int.ofNat.inj (hmvP.symm.trans hmv)
  have hfit : FitsLen (mv0 + perHole t.n t.benchlen * holesLeft) := by
    simpa [hmvSame] using hfit0
  have hk := hp.holesPos
  let mv2 := mv0 + (pegCount x + pegCount x)
  have hmvC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = (mv2 : Int) := by
    simpa [x, mv2, ofNat_eq_natCast] using c.moves
  have hfn : FitsLen t.n :=
    FitsLen.of_le hfit (under_budget t.n mv0 t.n t.benchlen holesLeft hk (n_room t.n t.benchlen))
  have h3 : FitsLen (3 * (t.n - 1)) :=
    FitsLen.of_le hfit (under_budget (3 * (t.n - 1)) mv0 t.n t.benchlen holesLeft hk
      (three_room t.n t.benchlen))
  have hfitB : FitsLen t.benchlen :=
    FitsLen.of_le hfit (under_budget t.benchlen mv0 t.n t.benchlen holesLeft hk
      (bench_room t.n t.benchlen))
  have hfm : FitsLen (mv2 + 2 * t.n) := by
    have hle := le_budget mv0 (pegCount x + pegCount x + 2 * t.n) t.n t.benchlen holesLeft hk
      (four_room (pegCount x) t.n t.benchlen hpeg)
    exact FitsLen.of_le hfit ((mv_in mv0 (pegCount x) t.n).symm ▸ by simpa [mv2] using hle)
  have hfold : FitsLen (mv2 + 2 * t.n + 3 * (t.benchlen - t.n)) := by
    have hle := le_budget mv0 (pegCount x + pegCount x + 2 * t.n + 3 * (t.benchlen - t.n))
      t.n t.benchlen holesLeft hk (cube_add_room (pegCount x) t.n t.benchlen hpeg)
    exact FitsLen.of_le hfit
      ((mv_fold mv0 (pegCount x) t.n t.benchlen).symm ▸ by simpa [mv2] using hle)
  have hcube := curve_cube_bottom bC x t.w t.h t.r t.n t.k mv2 hole0 t.benchlen pk ps0 o1
      t.combgap c.markerOn c.benchOff hops1 hop1 hfo1
      (by rw [c.tier]; rfl) (by rw [c.tier]; rfl) sat.cube_span
      hF hHome hHF hArr h7 hOk.n_pos hn hx hfn hmvC hpeak hps hxt
      h3 hfm (shape_of t hsh)
      (by rw [c.tier]; rfl) (by rw [c.tier]; rfl) (by rw [c.tier]; rfl) (by rw [c.tier]; rfl)
      hhole hsh.small hsh.n_small hfitB hfold
  obtain ⟨bK, hok, hon, hto, hbench, htake, hheld, hhome, hmk, hhigh, hmov, hpeakOut,
      hslides, ht, hops', hstrict', hhole', hmarkK, hctrlK, hmxK⟩ := hcube
  have hlenL := lane_len t.n t.k t.benchlen x
    (n_le_bench t.n t.benchlen t.combgap sat.cube_span)
  have hdo :
      (do
          let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
          let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
          let b ← Ecbs.put b Ecbs.base_across x
          let b ← Ecbs.copy_band b Ecbs.bottom Ecbs.base_across false
          Ecbs.cube b Ecbs.bottom Ecbs.bottom) = .ok bK := by
    rw [do_cube b t.n j, hdoC, ok_bind]
    exact hok
  refine ⟨bK, hdo, ?_⟩
  refine
    { benchOn := hon
      benchTo := hto
      bench := by unfold cubeLane; simpa [x] using hbench
      take := by unfold cubeLane; simpa [x] using htake
      len := by unfold cubeLane; simpa [x] using hlenL
      high := by
        unfold cubeLane
        intro i hi hlt
        have hltb : i < t.benchlen := by simpa [x, hlenL] using hlt
        have hc0 := hhigh i hi hltb
        simpa [x, coeff_eq_get _ _ hlt] using hc0
      markerOn := hmk
      szH := by rw [hhome, Array.size_set]; exact c.szH
      szD := by rw [hheld, Array.size_set]; exact c.szD
      held2 := by
        intro h
        have h? : bK.sudo_5Board_4held[2]? = some false := by
          rw [hheld, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hF)]
          exact congrArg some (set_at_val _ 2 hF false)
        exact of_some _ 2 false h? h
      home2 := by
        intro h
        have h? : bK.sudo_5Board_4home[2]? = some (#[] : Array Int) := by
          rw [hhome, Array.getElem?_eq_getElem (by rw [Array.size_set]; exact hHome)]
          exact congrArg some (set_at_val _ 2 hHome (#[] : Array Int))
        exact of_some _ 2 _ h? h
      held3 := by
        intro h
        have h? : bK.sudo_5Board_4held[3]? = some true := by
          rw [eq_idx hheld 3, Array.getElem?_set_ne _ ⟨2, hF⟩ false (by decide : (2 : Nat) ≠ 3)]
          exact c.held3
        exact of_some _ 3 true h? h
      home3 := by
        intro h
        have h? : bK.sudo_5Board_4home[3]? = some (embed x) := by
          rw [eq_idx hhome 3, Array.getElem?_set_ne _ ⟨2, hHome⟩ (#[] : Array Int)
            (by decide : (2 : Nat) ≠ 3)]
          simpa [x] using c.home3
        exact of_some _ 3 _ h? h
      held6 := by
        intro h
        have h? : bK.sudo_5Board_4held[6]? = some false := by
          rw [eq_idx hheld 6, Array.getElem?_set_ne _ ⟨2, hF⟩ false (by decide : (2 : Nat) ≠ 6)]
          exact c.held6
        exact of_some _ 6 false h? h
      moves := by
        unfold cubeSpend
        rw [hmov, show mv2 = mv0 + (pegCount x + pegCount x) from rfl, cubeMoves_shift]
      slides := by rw [hslides]; exact c.slides
      peak := ⟨_, hpeakOut⟩
      strict := ⟨_, hstrict'⟩
      hole := ⟨_, hhole'⟩
      tier := by rw [ht]; exact c.tier
      opsSz := by rw [hops', Array.size_set]; exact c.opsSz
      ops0 := ⟨o0, by
        intro h
        have hget := get_eq_of_array hops' 0 h
        have hne : (1 : Nat) ≠ 0 := by decide
        simp [Array.getElem_set, hne] at hget
        exact hget.trans (ho0 (by rw [c.opsSz]; decide)),
        hfo0⟩
      held1 := by
        intro h
        have h? : bK.sudo_5Board_4held[1]? = some false := by
          rw [eq_idx hheld 1, Array.getElem?_set_ne _ ⟨2, hF⟩ false (by decide : (2 : Nat) ≠ 1)]
          exact c.held1
        exact of_some _ 1 false h? h
      held5 := by
        intro h
        have h? : bK.sudo_5Board_4held[5]? = some false := by
          rw [eq_idx hheld 5, Array.getElem?_set_ne _ ⟨2, hF⟩ false (by decide : (2 : Nat) ≠ 5)]
          exact c.held5
        exact of_some _ 5 false h? h
      marker := by rw [hmarkK]; exact c.marker
      ctrl := by rw [hctrlK]; exact c.ctrl
      mx := ⟨mx0, hmxK.trans _hmx⟩
      ops1 := ⟨o1, by
        intro h
        have hget := get_eq_of_array hops' 1 h
        simpa [Array.getElem_set, ofNat_eq_natCast] using hget⟩
      home1 := by
        intro h
        have h? : bK.sudo_5Board_4home[1]? = some (#[] : Array Int) := by
          rw [eq_idx hhome 1, Array.getElem?_set_ne _ ⟨2, hHome⟩ (#[] : Array Int)
            (by decide : (2 : Nat) ≠ 1)]
          exact c.home1
        exact of_some _ 1 _ h? h
      home5 := by
        intro h
        have h? : bK.sudo_5Board_4home[5]? = some (#[] : Array Int) := by
          rw [eq_idx hhome 5, Array.getElem?_set_ne _ ⟨2, hHome⟩ (#[] : Array Int)
            (by decide : (2 : Nat) ≠ 5)]
          exact c.home5
        exact of_some _ 5 _ h? h
      held0 := by
        intro h
        have h? : bK.sudo_5Board_4held[0]? = some false := by
          rw [eq_idx hheld 0, Array.getElem?_set_ne _ ⟨2, hF⟩ false (by decide : (2 : Nat) ≠ 0)]
          exact c.held0
        exact of_some _ 0 false h? h
      home0 := by
        intro h
        have h? : bK.sudo_5Board_4home[0]? = some (#[] : Array Int) := by
          rw [eq_idx hhome 0, Array.getElem?_set_ne _ ⟨2, hHome⟩ (#[] : Array Int)
            (by decide : (2 : Nat) ≠ 0)]
          exact c.home0
        exact of_some _ 0 _ h? h }

end EcbsLink2.Link2

