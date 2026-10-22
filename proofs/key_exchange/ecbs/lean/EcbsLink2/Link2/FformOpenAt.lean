/-
  The board `start_walk` leaves. It is the opening live frame: homes 0 and 1
  are the seated base point, home 2 is the one-peg, and the ledger matches
  `FformAt` at one seated cell. The marker index stays `-1`. A later cube is
  what writes `Int.ofNat 2`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformStart
import EcbsLink2.Link2.WalkFformInd
import EcbsLink2.Link2.FieldUnit
import EcbsLink2.Link2.FieldNeg
import EcbsLink2.Link2.CheckTail

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- The opening live board. `done = 1` is the seating cell. The marker is `-1`. -/
def StartAt (t : Spec.Tier) (b : Ecbs.Board) (baseX baseY : List Nat)
    (red : Bool) : Prop :=
  let ySeat := if red then mirrorTrits baseY else baseY
  b.sudo_5Board_9marker_on = true ∧
  b.sudo_5Board_1t = embTier t ∧
  baseX.length = t.n ∧ ySeat.length = t.n ∧
  allTritList baseX ∧ allTritList ySeat ∧
  baseY.length = t.n ∧ allTritList baseY ∧
  b.sudo_5Board_4home.size = 8 ∧
  b.sudo_5Board_4held.size = 8 ∧
  (∀ h : 0 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[0] = true) ∧
  b.sudo_5Board_6marker = -1 ∧
  ProjOn t b baseX ySeat ∧
  ∃ (moves ctrl pk : Nat),
    b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
    b.sudo_5Board_4cost.sudo_5Costs_6slides = 0 ∧
    b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
    b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = 0 ∧
    b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk ∧
    b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = 0 ∧
    b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = 0 ∧
    b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat 0) ∧
    b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (0 : Int) ∧
    b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 ∧
    b.sudo_5Board_4cost.sudo_5Costs_3ops[4]? = some (Int.ofNat 0) ∧
    b.sudo_5Board_4held[5]? = some false ∧
    b.sudo_5Board_4held[6]? = some false ∧
    FitsLen (ctrl + 6) ∧
    FitsLen (0 + 3 * (t.cells - 1)) ∧
    FitsLen (0 + 13 * (t.cells - 1)) ∧
    FitsLen (0 + (t.cells - 1)) ∧
    FitsLen (moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n)) ∧
    FitsLen (0 + 2 * t.n + slideCharge t.n) ∧
    moves ≤ walkCharge t + (6 * t.benchlen + 2 * t.n) ∧
    ctrl ≤ cellCtrlCharge t + 4

private theorem k_lt (t : Spec.Tier) (hsh : TierShape t) : t.k < t.n := by
  have hgap : 0 < t.n - t.k := by
    rw [hsh.gap]
    exact Nat.mul_pos hsh.w0 hsh.r0
  omega

private theorem put_home_ne (b : Ecbs.Board) (j : Nat)
    (hH : 2 < b.sudo_5Board_4home.size) (hD : 2 < b.sudo_5Board_4held.size)
    (n moves : Nat) (hne : (2 : Nat) ≠ j)
    (hj : j < b.sudo_5Board_4home.size) :
    (whitePut b 2 hH hD n moves).sudo_5Board_4home[j]'(by
      simp [whitePut, Array.size_set]; exact hj) =
      b.sudo_5Board_4home[j] := by
  simp [whitePut, Array.getElem_set_ne, hne]

private theorem put_home_at (b : Ecbs.Board)
    (hH : 2 < b.sudo_5Board_4home.size) (hD : 2 < b.sudo_5Board_4held.size)
    (n moves : Nat) :
    (whitePut b 2 hH hD n moves).sudo_5Board_4home[2]'(by
      simp [whitePut, Array.size_set]; exact hH) =
      embed (whiteHole0 n) := by
  simp [whitePut, Array.getElem_set]

private theorem put_held_at (b : Ecbs.Board)
    (hH : 2 < b.sudo_5Board_4home.size) (hD : 2 < b.sudo_5Board_4held.size)
    (n moves : Nat) :
    (whitePut b 2 hH hD n moves).sudo_5Board_4held[2]'(by
      simp [whitePut, Array.size_set]; exact hD) = true := by
  simp [whitePut, Array.getElem_set]

private theorem put_held_ne (b : Ecbs.Board) (j : Nat)
    (hH : 2 < b.sudo_5Board_4home.size) (hD : 2 < b.sudo_5Board_4held.size)
    (n moves : Nat) (hne : (2 : Nat) ≠ j)
    (hj : j < b.sudo_5Board_4held.size) :
    (whitePut b 2 hH hD n moves).sudo_5Board_4held[j]'(by
      simp [whitePut, Array.size_set]; exact hj) =
      b.sudo_5Board_4held[j] := by
  simp [whitePut, Array.getElem_set_ne, hne]

private theorem zero_ops1 :
    (Array.mkArray 5 (0 : Int))[1]? = some (0 : Int) := by
  have h1 : 1 < (Array.mkArray 5 (0 : Int)).size := by simp [Array.size_mkArray]
  rw [Array.getElem?_eq_getElem h1]
  simp [Array.getElem_mkArray]

private theorem zero_ops4 :
    (Array.mkArray 5 (0 : Int))[4]? = some (Int.ofNat 0) := by
  have h4 : 4 < (Array.mkArray 5 (0 : Int)).size := by simp [Array.size_mkArray]
  rw [Array.getElem?_eq_getElem h4]
  simp [Array.getElem_mkArray]

private theorem zero_ops0 :
    (Array.mkArray 5 (0 : Int))[0]? = some (Int.ofNat 0) := by
  have h0 : 0 < (Array.mkArray 5 (0 : Int)).size := by simp [Array.size_mkArray]
  rw [Array.getElem?_eq_getElem h0]
  simp [Array.getElem_mkArray]

private theorem one_ne_zero (n : Nat) (hn : 0 < n) :
    onePeg n ≠ List.replicate n 0 := by
  cases n with
  | zero => omega
  | succ n =>
    intro h
    simp only [onePeg, Nat.succ_sub_one, List.replicate_succ] at h
    injection h with h0
    cases h0

private theorem open_ctrl_le (t : Spec.Tier) :
    tierR t ≤ cellCtrlCharge t + 4 := by
  unfold cellCtrlCharge
  have hone : 1 ≤ 3 * rowRoom t + 5 := by omega
  have hmul : tierR t ≤ (tierR t + 1) * (3 * rowRoom t + 5) := by
    calc tierR t = tierR t * 1 := by omega
      _ ≤ (tierR t + 1) * 1 := by omega
      _ ≤ (tierR t + 1) * (3 * rowRoom t + 5) := Nat.mul_le_mul_left _ hone
  omega

private theorem open_move_le (t : Spec.Tier) (moves n : Nat)
    (hn : 0 < n) (hm : moves ≤ 2 * n + 1) (hne : n = t.n) :
    moves ≤ walkCharge t + (6 * t.benchlen + 2 * t.n) := by
  subst hne
  unfold walkCharge
  omega

private theorem ble_le (a b : Nat) (h : Nat.ble a b = true) : a ≤ b :=
  Nat.le_of_ble_eq_true h

private theorem demo_open_move_fit :
    FitsLen ((2 * demo.n + 1) + 2 * demo.n + cubeCharge demo.n demo.benchlen +
      2 * demo.n + 3 * (demo.benchlen - demo.n)) := by
  unfold FitsLen cubeCharge i64MaxNat
  exact ble_le _ _ rfl

private theorem toy_open_move_fit :
    FitsLen ((2 * toy.n + 1) + 2 * toy.n + cubeCharge toy.n toy.benchlen +
      2 * toy.n + 3 * (toy.benchlen - toy.n)) := by
  unfold FitsLen cubeCharge i64MaxNat
  exact ble_le _ _ rfl

private theorem hobby_open_move_fit :
    FitsLen ((2 * hobby.n + 1) + 2 * hobby.n + cubeCharge hobby.n hobby.benchlen +
      2 * hobby.n + 3 * (hobby.benchlen - hobby.n)) := by
  unfold FitsLen cubeCharge i64MaxNat
  exact ble_le _ _ rfl

private theorem serious_open_move_fit :
    FitsLen ((2 * serious.n + 1) + 2 * serious.n + cubeCharge serious.n serious.benchlen +
      2 * serious.n + 3 * (serious.benchlen - serious.n)) := by
  unfold FitsLen cubeCharge i64MaxNat
  exact ble_le _ _ rfl

private theorem open_move_fit (t : Spec.Tier) (moves : Nat)
    (h : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (hm : moves ≤ 2 * t.n + 1) :
    FitsLen (moves + 2 * t.n + cubeCharge t.n t.benchlen + 2 * t.n +
      3 * (t.benchlen - t.n)) := by
  have hbig : FitsLen ((2 * t.n + 1) + 2 * t.n + cubeCharge t.n t.benchlen +
      2 * t.n + 3 * (t.benchlen - t.n)) := by
    rcases h with rfl | rfl | rfl | rfl
    · exact demo_open_move_fit
    · exact toy_open_move_fit
    · exact hobby_open_move_fit
    · exact serious_open_move_fit
  exact FitsLen.of_le hbig (by omega)

private theorem open_slide_fit (t : Spec.Tier) (hn : t.n ≤ 1000000) :
    FitsLen (0 + 2 * t.n + slideCharge t.n) := by
  unfold FitsLen slideCharge i64MaxNat
  have h6 : 6 * t.n ≤ 6 * 1000000 := Nat.mul_le_mul_left 6 hn
  have hmax : 6 * 1000000 ≤ 9223372036854775807 := by decide
  have hsum : 0 + 2 * t.n + 4 * t.n = 6 * t.n := by omega
  rw [hsum]
  exact Nat.le_trans h6 hmax

private theorem open_ctrl_fit (t : Spec.Tier) (hn : t.n ≤ 1000000) :
    FitsLen (tierR t + 6) := by
  have hlen : (rungList (t.n - 1)).length ≤ t.n - 1 := rungList_length_le _
  unfold FitsLen tierR i64MaxNat
  have hsmall : (rungList (t.n - 1)).length + 6 ≤ 1000006 := by omega
  have hmax : 1000006 ≤ 9223372036854775807 := by decide
  exact Nat.le_trans hsmall hmax

private theorem cell_room_le (t : Spec.Tier)
    (h : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious) :
    FitsLen (0 + 3 * (t.cells - 1)) ∧ FitsLen (0 + 13 * (t.cells - 1)) ∧
      FitsLen (0 + (t.cells - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact FitsLen.of_le (start_walk_cube_room t h) (by omega)
  · exact FitsLen.of_le (start_walk_mul_room t h) (by omega)
  · exact FitsLen.of_le (start_walk_fadd_room t h) (by omega)

private theorem seat_proj (t : Spec.Tier) (b : Ecbs.Board) (x ySeat : List Nat)
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hx : x.length = t.n) (hy : ySeat.length = t.n)
    (hxt : allTritList x) (hyt : allTritList ySeat)
    (h0 : ∀ h : 0 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[0] = embed x)
    (h1 : ∀ h : 1 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[1] = embed ySeat)
    (h2 : ∀ h : 2 < b.sudo_5Board_4home.size,
      b.sudo_5Board_4home[2] = embed (onePeg t.n))
    (hheld1 : ∀ h : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1] = true)
    (hheld2 : ∀ h : 2 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[2] = true)
    (hoff : b.sudo_5Board_8bench_on = false) :
    ProjOn t b x ySeat := by
  have hn := hOk.n_pos
  have hk := k_lt t hsh
  have hspan := sat.mul_span
  have hb := mul_span_n t.n t.benchlen hn hspan
  have honeX := fieldMul_one_right t.n t.k t.benchlen x hn hk hb hspan hxt hx
  have honeY := fieldMul_one_right t.n t.k t.benchlen ySeat hn hk hb hspan hyt hy
  have hone1 := fieldMul_one_right t.n t.k t.benchlen (onePeg t.n) hn hk hb hspan
    (onePeg_trits _) (onePeg_length _ hn)
  refine ⟨x, ySeat, onePeg t.n, ProjLay.homes, hx, hy, onePeg_length _ hn,
    hxt, hyt, onePeg_trits _, honeX.symm, honeY.symm, one_ne_zero _ hn, h0, ?_,
    ⟨onePeg t.n, onePeg_length _ hn, onePeg_trits _, hone1⟩⟩
  exact ⟨hoff, h1, h2, hheld1, hheld2⟩

private theorem tier_n_of (t : Spec.Tier) (b : Ecbs.Board)
    (h : b.sudo_5Board_1t = embTier t) :
    b.sudo_5Board_1t.sudo_4Tier_1n = (t.n : Int) := by
  rw [h]
  simp [embTier]

private theorem finish_walk (t : Spec.Tier) (b2 : Ecbs.Board)
    (x y1 y4 : List Nat) (mv2 pk2 : Nat)
    (out : OutLay t b2 x y1 y4 mv2 pk2)
    (hpos : 0 < t.n) (hf : FitsLen t.n) (hfit1 : FitsLen (mv2 + 1)) :
    Ecbs.white0 b2 Ecbs.bottom =
      .ok (peakBoard
        (whitePut b2 2 (by rw [out.szH]; decide) (by rw [out.szD]; decide) t.n mv2)
        pk2) := by
  have h2H : 2 < b2.sudo_5Board_4home.size := by rw [out.szH]; decide
  have h2D : 2 < b2.sudo_5Board_4held.size := by rw [out.szD]; decide
  have hwhite := white0_fresh b2 2 t.n mv2 pk2 h2H h2D out.held2 out.bench
    (tier_n_of t b2 out.tier) hpos out.moves
    (by simpa [ofNat_eq_natCast] using out.peak)
    (by rw [out.szD]; decide) hf hfit1
  simpa [show Ecbs.bottom = ((2 : Nat) : Int) from rfl] using hwhite

private theorem ops_of_out (b2 : Ecbs.Board) (pk2 n mv2 : Nat)
    (hH : 2 < b2.sudo_5Board_4home.size) (hD : 2 < b2.sudo_5Board_4held.size)
    (hops : b2.sudo_5Board_4cost.sudo_5Costs_3ops = Array.mkArray 5 0) :
    (peakBoard (whitePut b2 2 hH hD n mv2) pk2).sudo_5Board_4cost.sudo_5Costs_3ops =
      Array.mkArray 5 0 := by
  simp [peakBoard, whitePut, hops]

/-- Seating the base point. The projective denominator is the one-peg. -/
theorem start_walk_at (t : Spec.Tier) (b : Ecbs.Board) (x y : List Nat)
    (mv pk : Nat) (lay : InLay t b x y mv pk) (red : Bool)
    (hx : x.length = t.n) (hy : y.length = t.n)
    (hxt : allTritList x) (hyt : allTritList y)
    (hpos : 0 < t.n) (hf : FitsLen t.n)
    (hfitx : FitsLen (mv + pegCount x))
    (hfity : FitsLen (mv + pegCount x + pegCount y))
    (hfit1 : FitsLen (mv + pegCount x + pegCount y + 1))
    (hsh : TierShape t) (hOk : BoardOk t) (sat : TierSat t)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (hmv0 : mv = 0)
    (hfresh : lay.sl0 = 0 ∧ lay.ops0 = 0 ∧ lay.strict0 = 0 ∧ lay.hole0 = 0 ∧
      lay.mx0 = 0 ∧ lay.ctrl0 = tierR t) :
    ∃ bW, Ecbs.start_walk b red = .ok bW ∧ StartAt t bW x y red := by
  let mv2 := mv + pegCount x + pegCount y
  have hmvLe : mv2 + 1 ≤ 2 * t.n + 1 := by
    have hxP : pegCount x ≤ t.n := by rw [← hx]; exact pegCount_le x
    have hyP : pegCount y ≤ t.n := by rw [← hy]; exact pegCount_le y
    unfold mv2
    rw [hmv0]
    omega
  have hrooms := cell_room_le t hship
  rcases hfresh with ⟨hsl0, hops0, hstrict0, hhole0, hmx0, hctrl0⟩
  cases red with
  | false =>
    obtain ⟨b2, pk2, out, hsl, hctrl, hopsC, hstrict, hhole, hmx, _, _, hcopy⟩ :=
      white_copy_kept t b x y mv pk lay hx hy hf hfitx hfity
    have houtS : out.sl0 = 0 := hsl.trans hsl0
    have houtC : out.ctrl0 = tierR t := hctrl.trans hctrl0
    have houtM : out.mx0 = 0 := hmx.trans hmx0
    have houtP : out.strict0 = 0 := hstrict.trans hstrict0
    have houtH : out.hole0 = 0 := hhole.trans hhole0
    have harr := ops_mk_of_zero b2 out.ops0 out.opsSz (hopsC.trans hops0) out.opsBound
    have h2H : 2 < b2.sudo_5Board_4home.size := by rw [out.szH]; decide
    have h2D : 2 < b2.sudo_5Board_4held.size := by rw [out.szD]; decide
    let bPut := whitePut b2 2 h2H h2D t.n mv2
    let bW := peakBoard bPut pk2
    have hplant := finish_walk t b2 x y y mv2 pk2 out hpos hf hfit1
    refine ⟨bW, ?_, ?_⟩
    · unfold Ecbs.start_walk
      conv => lhs; zeta
      rw [← bind_assoc, hcopy, ok_bind, hplant, ok_bind, pure_eq_ok]
    · have hops := ops_of_out b2 pk2 t.n mv2 h2H h2D harr
      have h0 : ∀ h : 0 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[0] = embed x := by
        intro _
        simp only [bW, peakBoard]
        have hget := put_home_ne b2 0 h2H h2D t.n mv2 (by decide)
          (by rw [out.szH]; decide)
        simpa using hget.trans out.home0
      have h1 : ∀ h : 1 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[1] = embed y := by
        intro _
        simp only [bW, peakBoard]
        have hget := put_home_ne b2 1 h2H h2D t.n mv2 (by decide)
          (by rw [out.szH]; decide)
        simpa using hget.trans out.home1
      have h2 : ∀ h : 2 < bW.sudo_5Board_4home.size,
          bW.sudo_5Board_4home[2] = embed (onePeg t.n) := by
        intro _
        simp only [bW, peakBoard, whiteHole0_eq_onePeg]
        simpa using put_home_at b2 h2H h2D t.n mv2
      have hd1 : ∀ h : 1 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[1] = true := by
        intro _
        simp only [bW, peakBoard]
        have hget := put_held_ne b2 1 h2H h2D t.n mv2 (by decide)
          (by rw [out.szD]; decide)
        simpa using hget.trans out.held1
      have hd2 : ∀ h : 2 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[2] = true := by
        intro _
        simp only [bW, peakBoard]
        simpa using put_held_at b2 h2H h2D t.n mv2
      have hproj := seat_proj t bW x y hsh hOk sat hx hy hxt hyt h0 h1 h2 hd1 hd2
        (by simp only [bW, bPut, peakBoard, whitePut, out.bench])
      refine ⟨?_, ?_, hx, hy, hxt, hyt, hy, hyt, ?_, ?_, ?_, ?_, hproj, ?_⟩
      · simp only [bW, bPut, peakBoard, whitePut, out.flag]
      · simp only [bW, bPut, peakBoard, whitePut, out.tier]
      · simp only [bW, bPut, peakBoard, whitePut, Array.size_set, out.szH]
      · simp only [bW, bPut, peakBoard, whitePut, Array.size_set, out.szD]
      · intro _
        simp only [bW, peakBoard]
        have hget := put_held_ne b2 0 h2H h2D t.n mv2 (by decide)
          (by rw [out.szD]; decide)
        simpa using hget.trans out.held0
      · simp only [bW, bPut, peakBoard, whitePut, out.marker]
      · refine ⟨mv2 + 1, tierR t, raisedPeak pk2 (countHeld bPut.sudo_5Board_4held 7),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [bW, bPut, peakBoard, whitePut]
        · simp only [bW, bPut, peakBoard, whitePut, out.slides, houtS, ← ofNat_eq_natCast]; exact Int.ofNat_zero
        · simp only [bW, bPut, peakBoard, whitePut, out.ctrl, houtC, ofNat_eq_natCast]
        · simp only [bW, bPut, peakBoard, whitePut, out.mx, houtM, ← ofNat_eq_natCast]; exact Int.ofNat_zero
        · simp only [bW, peakBoard]
        · simp only [bW, bPut, peakBoard, whitePut, out.strict, houtP, ← ofNat_eq_natCast]; exact Int.ofNat_zero
        · simp only [bW, bPut, peakBoard, whitePut, out.hole, houtH, ← ofNat_eq_natCast]; exact Int.ofNat_zero
        · rw [hops]; exact zero_ops0
        · rw [hops]; exact zero_ops1
        · rw [hops]; simp [Array.size_mkArray]
        · rw [hops]; exact zero_ops4
        · rw [show bW.sudo_5Board_4held[5]? = bPut.sudo_5Board_4held[5]? from by
            simp [bW, peakBoard],
            show bPut.sudo_5Board_4held[5]? = b2.sudo_5Board_4held[5]? from by
            simp [bPut, whitePut, Array.getElem?_set_ne]]
          exact (Array.getElem?_eq_getElem (by rw [out.szD]; decide)).trans
            (congrArg some out.held5)
        · rw [show bW.sudo_5Board_4held[6]? = bPut.sudo_5Board_4held[6]? from by
            simp [bW, peakBoard],
            show bPut.sudo_5Board_4held[6]? = b2.sudo_5Board_4held[6]? from by
            simp [bPut, whitePut, Array.getElem?_set_ne]]
          exact (Array.getElem?_eq_getElem (by rw [out.szD]; decide)).trans
            (congrArg some out.held6)
        · exact open_ctrl_fit t hsh.n_small
        · exact hrooms.1
        · exact hrooms.2.1
        · exact hrooms.2.2
        · exact open_move_fit t (mv2 + 1) hship hmvLe
        · exact open_slide_fit t hsh.n_small
        · exact open_move_le t (mv2 + 1) t.n hpos hmvLe rfl
        · exact open_ctrl_le t
  | true =>
    obtain ⟨b2, pk2, out, hsl, hctrl, hopsC, hstrict, hhole, hmx, _, _, hcopy⟩ :=
      red_copy_kept t b x y mv pk lay hx hy hpos hyt hf hfitx hfity
    have houtS : out.sl0 = 0 := hsl.trans hsl0
    have houtC : out.ctrl0 = tierR t := hctrl.trans hctrl0
    have houtM : out.mx0 = 0 := hmx.trans hmx0
    have houtP : out.strict0 = 0 := hstrict.trans hstrict0
    have houtH : out.hole0 = 0 := hhole.trans hhole0
    have harr := ops_mk_of_zero b2 out.ops0 out.opsSz (hopsC.trans hops0) out.opsBound
    have h2H : 2 < b2.sudo_5Board_4home.size := by rw [out.szH]; decide
    have h2D : 2 < b2.sudo_5Board_4held.size := by rw [out.szD]; decide
    have hseat : (mirrorTrits y).length = t.n := by
      simpa [mirrorTrits, List.length_map] using hy
    have hseatT : allTritList (mirrorTrits y) := mirror_trits y
    let bPut := whitePut b2 2 h2H h2D t.n mv2
    let bW := peakBoard bPut pk2
    have hplant := finish_walk t b2 x (mirrorTrits y) y mv2 pk2 out hpos hf hfit1
    refine ⟨bW, ?_, ?_⟩
    · unfold Ecbs.start_walk
      conv => lhs; zeta
      rw [← bind_assoc, hcopy, ok_bind, hplant, ok_bind, pure_eq_ok]
    · have hops := ops_of_out b2 pk2 t.n mv2 h2H h2D harr
      have h0 : ∀ h : 0 < bW.sudo_5Board_4home.size, bW.sudo_5Board_4home[0] = embed x := by
        intro _
        simp only [bW, peakBoard]
        have hget := put_home_ne b2 0 h2H h2D t.n mv2 (by decide)
          (by rw [out.szH]; decide)
        simpa using hget.trans out.home0
      have h1 : ∀ h : 1 < bW.sudo_5Board_4home.size,
          bW.sudo_5Board_4home[1] = embed (mirrorTrits y) := by
        intro _
        simp only [bW, peakBoard]
        have hget := put_home_ne b2 1 h2H h2D t.n mv2 (by decide)
          (by rw [out.szH]; decide)
        simpa using hget.trans out.home1
      have h2 : ∀ h : 2 < bW.sudo_5Board_4home.size,
          bW.sudo_5Board_4home[2] = embed (onePeg t.n) := by
        intro _
        simp only [bW, peakBoard, whiteHole0_eq_onePeg]
        simpa using put_home_at b2 h2H h2D t.n mv2
      have hd1 : ∀ h : 1 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[1] = true := by
        intro _
        simp only [bW, peakBoard]
        have hget := put_held_ne b2 1 h2H h2D t.n mv2 (by decide)
          (by rw [out.szD]; decide)
        simpa using hget.trans out.held1
      have hd2 : ∀ h : 2 < bW.sudo_5Board_4held.size, bW.sudo_5Board_4held[2] = true := by
        intro _
        simp only [bW, peakBoard]
        simpa using put_held_at b2 h2H h2D t.n mv2
      have hproj := seat_proj t bW x (mirrorTrits y) hsh hOk sat hx hseat hxt hseatT
        h0 h1 h2 hd1 hd2 (by simp only [bW, bPut, peakBoard, whitePut, out.bench])
      refine ⟨?_, ?_, hx, hseat, hxt, hseatT, hy, hyt, ?_, ?_, ?_, ?_, hproj, ?_⟩
      · simp only [bW, bPut, peakBoard, whitePut, out.flag]
      · simp only [bW, bPut, peakBoard, whitePut, out.tier]
      · simp only [bW, bPut, peakBoard, whitePut, Array.size_set, out.szH]
      · simp only [bW, bPut, peakBoard, whitePut, Array.size_set, out.szD]
      · intro _
        simp only [bW, peakBoard]
        have hget := put_held_ne b2 0 h2H h2D t.n mv2 (by decide)
          (by rw [out.szD]; decide)
        simpa using hget.trans out.held0
      · simp only [bW, bPut, peakBoard, whitePut, out.marker]
      · refine ⟨mv2 + 1, tierR t, raisedPeak pk2 (countHeld bPut.sudo_5Board_4held 7),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [bW, bPut, peakBoard, whitePut]
        · simp only [bW, bPut, peakBoard, whitePut, out.slides, houtS, ← ofNat_eq_natCast]; exact Int.ofNat_zero
        · simp only [bW, bPut, peakBoard, whitePut, out.ctrl, houtC, ofNat_eq_natCast]
        · simp only [bW, bPut, peakBoard, whitePut, out.mx, houtM, ← ofNat_eq_natCast]; exact Int.ofNat_zero
        · simp only [bW, peakBoard]
        · simp only [bW, bPut, peakBoard, whitePut, out.strict, houtP, ← ofNat_eq_natCast]; exact Int.ofNat_zero
        · simp only [bW, bPut, peakBoard, whitePut, out.hole, houtH, ← ofNat_eq_natCast]; exact Int.ofNat_zero
        · rw [hops]; exact zero_ops0
        · rw [hops]; exact zero_ops1
        · rw [hops]; simp [Array.size_mkArray]
        · rw [hops]; exact zero_ops4
        · rw [show bW.sudo_5Board_4held[5]? = bPut.sudo_5Board_4held[5]? from by
            simp [bW, peakBoard],
            show bPut.sudo_5Board_4held[5]? = b2.sudo_5Board_4held[5]? from by
            simp [bPut, whitePut, Array.getElem?_set_ne]]
          exact (Array.getElem?_eq_getElem (by rw [out.szD]; decide)).trans
            (congrArg some out.held5)
        · rw [show bW.sudo_5Board_4held[6]? = bPut.sudo_5Board_4held[6]? from by
            simp [bW, peakBoard],
            show bPut.sudo_5Board_4held[6]? = b2.sudo_5Board_4held[6]? from by
            simp [bPut, whitePut, Array.getElem?_set_ne]]
          exact (Array.getElem?_eq_getElem (by rw [out.szD]; decide)).trans
            (congrArg some out.held6)
        · exact open_ctrl_fit t hsh.n_small
        · exact hrooms.1
        · exact hrooms.2.1
        · exact hrooms.2.2
        · exact open_move_fit t (mv2 + 1) hship hmvLe
        · exact open_slide_fit t hsh.n_small
        · exact open_move_le t (mv2 + 1) t.n hpos hmvLe rfl
        · exact open_ctrl_le t
