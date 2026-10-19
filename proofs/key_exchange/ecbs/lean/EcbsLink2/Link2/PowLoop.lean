/-
  The power loop as one digit at a time. `PowAt` is the board with `ds`
  digits still to run. Each counter keeps a remaining budget
  `FitsLen (c + perDigit * ds.length)`, the same shape as `FformAt`.
  A digit spends at most one unit of that budget. The marker seated by a
  digit is 0 or 1, and every shipped script is at least 2, so the
  `marker < script` assert does not fail on Demo.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.PowFold
import EcbsLink2.Link2.CheckTail
import EcbsLink2.Link2.FieldNeg
import EcbsLink2.Link2.EntryInv
import EcbsLink2.Link2.ClimbEmit

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

def powUp : Nat := 1
def powBottom : Nat := 2
def powGap : Nat := 5
def powSpare : Nat := 6

/-- Moves one root digit can add: the cube, the copy, the schoolbook, and the settles. -/
def powMove (n bench : Nat) : Nat := n * n + 6 * n + 6 * bench

/-- Slides one root digit can add: two settles, two pegs each. -/
def powSlide (n : Nat) : Nat := 4 * n

/-- Control one root digit can add: lift, cube feed, and the multiply's seat. -/
def powCtrl : Nat := 4

theorem room_move (moves spend n bench k : Nat)
    (h : FitsLen (moves + powMove n bench * (k + 1)))
    (hs : spend ≤ powMove n bench) :
    FitsLen (moves + spend) ∧
      FitsLen (moves + spend + powMove n bench * k) := by
  refine ⟨FitsLen.of_le h ?_, FitsLen.of_le h ?_⟩
  · have hmul : powMove n bench ≤ powMove n bench * (k + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  · have hmul : powMove n bench * (k + 1) = powMove n bench + powMove n bench * k := by
      rw [Nat.mul_succ, Nat.add_comm]
    omega

theorem room_slide (slides spend n k : Nat)
    (h : FitsLen (slides + powSlide n * (k + 1)))
    (hs : spend ≤ powSlide n) :
    FitsLen (slides + spend) ∧
      FitsLen (slides + spend + powSlide n * k) := by
  refine ⟨FitsLen.of_le h ?_, FitsLen.of_le h ?_⟩
  · have hmul : powSlide n ≤ powSlide n * (k + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  · have hmul : powSlide n * (k + 1) = powSlide n + powSlide n * k := by
      rw [Nat.mul_succ, Nat.add_comm]
    omega

theorem room_ctrl (ctrl spend k : Nat)
    (h : FitsLen (ctrl + powCtrl * (k + 1)))
    (hs : spend ≤ powCtrl) :
    FitsLen (ctrl + spend) ∧
      FitsLen (ctrl + spend + powCtrl * k) := by
  refine ⟨FitsLen.of_le h ?_, FitsLen.of_le h ?_⟩
  · have hmul : powCtrl ≤ powCtrl * (k + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  · have hmul : powCtrl * (k + 1) = powCtrl + powCtrl * k := by
      rw [Nat.mul_succ, Nat.add_comm]
    omega

theorem room_ops (c k : Nat) (h : FitsLen (c + (k + 1))) :
    FitsLen (c + 1) ∧ FitsLen ((c + 1) + k) := by
  refine ⟨FitsLen.of_le h (by omega), ?_⟩
  have hsum : c + (k + 1) = (c + 1) + k := by omega
  simpa [hsum] using h

theorem room_ops_keep (c k : Nat) (h : FitsLen (c + (k + 1))) :
    FitsLen (c + k) :=
  FitsLen.of_le h (by omega)

/-- `2 ≤ script` is `1 < script`. The power loop's assert is `1 < script`. -/
theorem script_one (t : Spec.Tier) (h : TierShape t) : 1 < t.script := by
  have h2 := h.script_ge
  omega

theorem demo_pow_script : 1 < demo.script := by decide
theorem toy_pow_script : 1 < toy.script := by decide
theorem hobby_pow_script : 1 < hobby.script := by decide
theorem serious_pow_script : 1 < serious.script := by decide

theorem powStep_trits (n k bench : Nat) (rhs acc : List Nat) (d : Nat)
    (ht : allTritList acc) (hk : k ≤ n) (hspan : 3 * (n - 1) < bench)
    (hn : n ≤ bench) (hr : rhs.length = n) :
    allTritList (powStep n k bench rhs acc d) := by
  rw [powStep_branch]
  have hcube := fieldCube_trits n k bench acc ht hspan hk
  have htakeR : rhs.take n = rhs := by rw [← hr, List.take_length]
  have hrhs : allTritList (fieldMul n k bench (fieldCube n k bench acc) rhs) := by
    simpa [htakeR] using fieldMul_trits n k bench (fieldCube n k bench acc) rhs hspan hn
  have hsq : allTritList (fieldMul n k bench rhs rhs) := by
    simpa [htakeR] using fieldMul_trits n k bench rhs rhs hspan hn
  have hsqLen : (fieldMul n k bench rhs rhs).length = n := fieldMul_length n k bench rhs rhs hn
  have htakeS : (fieldMul n k bench rhs rhs).take n = fieldMul n k bench rhs rhs := by
    have h := List.take_length (fieldMul n k bench rhs rhs)
    rwa [hsqLen] at h
  have hboth : allTritList (fieldMul n k bench (fieldCube n k bench acc)
      (fieldMul n k bench rhs rhs)) := by
    simpa [htakeS] using
      fieldMul_trits n k bench (fieldCube n k bench acc) (fieldMul n k bench rhs rhs) hspan hn
  by_cases h2 : d = 2
  · simpa [h2] using hboth
  · by_cases h1 : d = 1
    · simpa [h2, h1] using hrhs
    · simpa [h2, h1] using hcube

/-- One digit of the emitted power loop. Digit 0 settles the cube.
    Any other digit copies `src` into the spare and multiplies. -/
def powDigitRun (b : Ecbs.Board) (d src : Nat) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b ← Ecbs.marker_lift b
    let b ← Ecbs.cube b ((powUp : Nat) : Int) ((powUp : Nat) : Int)
    if d = 0 then
      Ecbs.settle b
    else
      do
        let b ← Ecbs.copy_band b ((powSpare : Nat) : Int) ((src : Nat) : Int) false
        let b ← Ecbs.mul b ((powUp : Nat) : Int) ((powUp : Nat) : Int)
            ((powSpare : Nat) : Int) false false false
        let b ← Ecbs.clear b ((powUp : Nat) : Int)
        Ecbs.settle b

/-- The power loop while `ds` digits remain. Counters carry
    `FitsLen (c + perDigit * ds.length)`. -/
structure PowAt (b : Ecbs.Board) (t : Spec.Tier) (rhs acc : List Nat) (ds : List Nat) : Prop where
  tier : b.sudo_5Board_1t = embTier t
  shape : TierShape t
  sat : TierSat t
  markerOn : b.sudo_5Board_9marker_on = true
  benchOff : b.sudo_5Board_8bench_on = false
  accLen : acc.length = t.n
  rhsLen : rhs.length = t.n
  nPos : 0 < t.n
  accT : allTritList acc
  rhsT : allTritList rhs
  upHome : b.sudo_5Board_4home[powUp]? = some (embed acc)
  upHeld : b.sudo_5Board_4held[powUp]? = some true
  botHome : b.sudo_5Board_4home[powBottom]? = some (embed rhs)
  botHeld : b.sudo_5Board_4held[powBottom]? = some true
  gapHome : b.sudo_5Board_4home[powGap]? =
    some (embed (fieldMul t.n t.k t.benchlen rhs rhs))
  gapHeld : b.sudo_5Board_4held[powGap]? = some true
  spareOff : b.sudo_5Board_4held[powSpare]? = some false
  pack :
    ∃ (moves slides ctrl mark mx pk ps hole c0 c1 : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves ∧
      b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides ∧
      b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl ∧
      b.sudo_5Board_6marker = Int.ofNat mark ∧
      mark ≤ 1 ∧
      b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx ∧
      b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pk ∧
      b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = Int.ofNat ps ∧
      b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
      b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (Int.ofNat c1) ∧
      FitsLen (moves + powMove t.n t.benchlen * ds.length) ∧
      FitsLen (slides + powSlide t.n * ds.length) ∧
      FitsLen (ctrl + powCtrl * ds.length) ∧
      FitsLen (c0 + ds.length) ∧
      FitsLen (c1 + ds.length)

theorem zero_delta_le (n bench moves k : Nat) (acc : List Nat) :
    cubeMoves moves acc n k bench + 2 * pegCount (fieldCube n k bench acc) ≤
      moves + powMove n bench := by
  have hc := cubeMoves_le moves acc n k bench
  have hpeg : pegCount (fieldCube n k bench acc) ≤ n := by
    have hlen : (fieldCube n k bench acc).length ≤ n := by
      rw [← cube_off_prefix n k bench acc]
      exact List.length_take_le _ _
    exact Nat.le_trans (pegCount_le _) hlen
  have hsub : 3 * (bench - n) ≤ 3 * bench := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  unfold powMove
  omega

private theorem some_idx {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) : i < a.size := by
  by_cases hlt : i < a.size
  · exact hlt
  · rw [Array.getElem?_ge a (by omega)] at h
    cases h

private theorem some_get {α : Type} (a : Array α) (i : Nat) (v : α)
    (h : a[i]? = some v) : a[i]'(some_idx a i v h) = v := by
  rw [Array.getElem?_eq_getElem (some_idx a i v h)] at h
  injection h

/-- A new counter that still fits inside `moves + per` keeps a `FitsLen`,
    and so does that counter plus `per` for every digit still waiting. -/
theorem room_abs (moves new per k : Nat)
    (h : FitsLen (moves + per * (k + 1)))
    (hs : new ≤ moves + per) :
    FitsLen new ∧ FitsLen (new + per * k) := by
  refine ⟨FitsLen.of_le h ?_, FitsLen.of_le h ?_⟩
  · have hmul : per ≤ per * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  · have hmul : per * (k + 1) = per + per * k := by
      rw [Nat.mul_succ, Nat.add_comm]
    omega

theorem fit_of_pow (moves n bench k bound : Nat)
    (h : FitsLen (moves + powMove n bench * (k + 1)))
    (hb : bound ≤ powMove n bench) :
    FitsLen bound := by
  apply FitsLen.of_le h
  have hmul : powMove n bench ≤ powMove n bench * (k + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem fit_add_pow (moves n bench k extra : Nat)
    (h : FitsLen (moves + powMove n bench * (k + 1)))
    (hb : extra ≤ powMove n bench) :
    FitsLen (moves + extra) := by
  apply FitsLen.of_le h
  have hmul : powMove n bench ≤ powMove n bench * (k + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem pow_ge_n (n bench : Nat) : n ≤ powMove n bench := by
  unfold powMove
  omega

theorem pow_ge_bench (n bench : Nat) : bench ≤ powMove n bench := by
  unfold powMove
  omega

theorem pow_ge_span (n bench : Nat) : 3 * (n - 1) ≤ powMove n bench := by
  unfold powMove
  omega

theorem pow_ge_two (n bench : Nat) : 2 * n ≤ powMove n bench := by
  unfold powMove
  omega

theorem pow_ge_fold (n bench : Nat) : 2 * n + 3 * (bench - n) ≤ powMove n bench := by
  unfold powMove
  omega

theorem pow_ge_two_peg (n bench peg : Nat) (hp : peg ≤ n) : 2 * peg ≤ powMove n bench := by
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left _ hp
  unfold powMove
  omega

theorem cube_peg_le (n k bench : Nat) (acc : List Nat) :
    pegCount (fieldCube n k bench acc) ≤ n := by
  have hlen : (fieldCube n k bench acc).length ≤ n := by
    rw [← cube_off_prefix n k bench acc]
    exact List.length_take_le _ _
  exact Nat.le_trans (pegCount_le _) hlen

/-- Digit 0. The up home becomes the cube, which is `powStep` on digit 0,
    and one unit of each budget is spent. -/
theorem pow_zero_at (b : Ecbs.Board) (t : Spec.Tier) (rhs acc : List Nat) (ds : List Nat)
    (h : PowAt b t rhs acc (0 :: ds)) :
    ∃ b', powDigitRun b 0 powBottom = .ok b' ∧
      PowAt b' t rhs (powStep t.n t.k t.benchlen rhs acc 0) ds := by
  obtain ⟨moves, slides, ctrl, mark, mx, pk, ps, hole, c0, c1, hmv, hsl, hc, hm, hmark,
      hmx, hpk, hps, hhole, hsz, hop0, hop1, hfitM, hfitS, hfitC, hfit0, hfit1⟩ := h.pack
  have hlen : (0 :: ds).length = ds.length + 1 := by simp
  have hn0 : 0 < t.n := h.nPos
  have hnb : t.n ≤ t.benchlen := mul_span_n t.n t.benchlen hn0 h.sat.mul_span
  have hspan3 : 3 * (t.n - 1) < t.benchlen := cube_span_le t.n t.benchlen t.combgap h.sat.cube_span
  have hscript := script_one t h.shape
  have hUp : powUp < b.sudo_5Board_4home.size := some_idx _ _ _ h.upHome
  have hUpD : powUp < b.sudo_5Board_4held.size := some_idx _ _ _ h.upHeld
  have h6 : powSpare < b.sudo_5Board_4held.size := some_idx _ _ _ h.spareOff
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by
    unfold powSpare at h6
    omega
  have hmov : FitsLen (moves + powMove t.n t.benchlen * (ds.length + 1)) := by
    simpa [hlen] using hfitM
  have hslR : FitsLen (slides + powSlide t.n * (ds.length + 1)) := by
    simpa [hlen] using hfitS
  have hcR : FitsLen (ctrl + powCtrl * (ds.length + 1)) := by
    simpa [hlen] using hfitC
  have hpegN := cube_peg_le t.n t.k t.benchlen acc
  have hnew := zero_delta_le t.n t.benchlen moves t.k acc
  have hmovePair := room_abs moves
      (cubeMoves moves acc t.n t.k t.benchlen + 2 * pegCount (fieldCube t.n t.k t.benchlen acc))
      (powMove t.n t.benchlen) ds.length hmov hnew
  have hfoldF : FitsLen (moves + 2 * t.n + 3 * (t.benchlen - t.n)) := by
    simpa [Nat.add_assoc] using
      (fit_add_pow moves t.n t.benchlen ds.length (2 * t.n + 3 * (t.benchlen - t.n)) hmov
        (pow_ge_fold t.n t.benchlen))
  have hslidePair := room_slide slides (2 * pegCount (fieldCube t.n t.k t.benchlen acc))
      t.n ds.length hslR (by
        have h2 : 2 * pegCount (fieldCube t.n t.k t.benchlen acc) ≤ 2 * t.n :=
          Nat.mul_le_mul_left _ hpegN
        unfold powSlide
        omega)
  have hzero := pow_zero_seated b powUp acc rhs t.w t.h t.r t.n t.k moves slides hole
      t.benchlen pk ps c1 t.combgap ctrl mx t.script mark
      h.markerOn h.benchOff hm hc hmx (by simpa [h.tier, embTier])
      (by omega : 0 < t.script)
      (room_ctrl ctrl 1 ds.length hcR (by unfold powCtrl; decide)).1
      (room_ctrl ctrl 2 ds.length hcR (by unfold powCtrl; decide)).1
      (by rw [hsz]; decide) (by
        have h1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [hsz]; decide
        rw [Array.getElem?_eq_getElem h1] at hop1
        injection hop1)
      (room_ops c1 ds.length (by simpa [hlen] using hfit1)).1
      hUpD hUp (some_get _ _ _ h.upHeld) (some_get _ _ _ h.upHome) h7
      (by simpa [ofNat_eq_natCast] using hps) (by simpa [ofNat_eq_natCast] using hpk)
      hn0 (by simpa [h.tier, embTier]) h.accLen
      (fit_of_pow moves t.n t.benchlen ds.length t.n hmov (pow_ge_n _ _))
      (by simpa [ofNat_eq_natCast] using hmv) hsl
      (by simpa [h.tier, embTier]) (by simpa [h.tier, embTier]) h.sat.cube_span
      (fit_of_pow moves t.n t.benchlen ds.length (3 * (t.n - 1)) hmov (pow_ge_span _ _))
      (fit_add_pow moves t.n t.benchlen ds.length (2 * t.n) hmov (pow_ge_two _ _))
      hhole h.accT
      h.shape.w0 h.shape.h0 h.shape.rlt h.shape.r0 h.shape.n_eq h.shape.k_le h.shape.gap
      (by simpa [h.tier, embTier]) (by simpa [h.tier, embTier])
      (by simpa [h.tier, embTier]) (by simpa [h.tier, embTier])
      h.shape.small h.shape.n_small
      (fit_of_pow moves t.n t.benchlen ds.length t.benchlen hmov (pow_ge_bench _ _))
      hfoldF
      (fit_of_pow moves t.n t.benchlen ds.length
        (2 * pegCount (fieldCube t.n t.k t.benchlen acc)) hmov (pow_ge_two_peg _ _ _ hpegN))
      hmovePair.1
      hslidePair.1
  rcases hzero with ⟨bS, hrun, hhome, hoff, hheld, hmark0, hflag, hctrl, hmvS, hslS, hholeS,
      hmxS, hpkS, hpsS, hop1S, hopK, hhomeK, hheldK, htierS, hszS⟩
  have hpowLen : (powStep t.n t.k t.benchlen rhs acc 0).length = t.n := by
    rw [powStep_branch]
    simp
    rw [← cube_off_prefix t.n t.k t.benchlen acc, List.length_take]
    have hsch : (combStrip t.n t.benchlen acc).length = t.benchlen := combStrip_length _ _ _
    have hlane := laneFold_length t.n (t.n - t.k) (combStrip t.n t.benchlen acc)
      (by rw [hsch]; exact hnb)
    rw [hlane, hsch, Nat.min_eq_left hnb]
  refine ⟨bS, ?_, ?_⟩
  · simp only [powDigitRun, powUp, if_true]
    exact hrun
  · refine
      { tier := by
          rw [htierS]
          exact h.tier
        shape := h.shape
        sat := h.sat
        markerOn := hflag
        benchOff := hoff
        accLen := hpowLen
        rhsLen := h.rhsLen
        nPos := h.nPos
        accT := powStep_trits t.n t.k t.benchlen rhs acc 0 h.accT h.shape.k_le hspan3 hnb h.rhsLen
        rhsT := h.rhsT
        upHome := by simpa [powUp] using hhome
        upHeld := by simpa [powUp] using hheld
        botHome := by
          have hbot := hhomeK powBottom (by decide)
          simpa [powBottom] using hbot.trans h.botHome
        botHeld := by
          have hb := hheldK powBottom (by decide)
          simpa [powBottom] using hb.trans h.botHeld
        gapHome := by
          have hg := hhomeK powGap (by decide)
          simpa [powGap] using hg.trans h.gapHome
        gapHeld := by
          have hg := hheldK powGap (by decide)
          simpa [powGap] using hg.trans h.gapHeld
        spareOff := by
          have hs := hheldK powSpare (by decide)
          simpa [powSpare] using hs.trans h.spareOff
        pack := ?_ }
    rcases hpkS with ⟨pk', hpk'⟩
    rcases hpsS with ⟨ps', hps'⟩
    refine ⟨cubeMoves moves acc t.n t.k t.benchlen + 2 * pegCount (fieldCube t.n t.k t.benchlen acc),
      slides + 2 * pegCount (fieldCube t.n t.k t.benchlen acc), ctrl + 2, 0, max mx 1, pk', ps',
      raisedHole hole (topIdx (combStrip t.n t.benchlen acc)), c0, c1 + 1,
      hmvS, hslS, hctrl, hmark0, by decide, hmxS, hpk', hps', hholeS, ?_, ?_, hop1S, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hszS]; exact hsz
    · exact (hopK 0 (by decide)).trans hop0
    · exact hmovePair.2
    · exact hslidePair.2
    · exact (room_ctrl ctrl 2 ds.length hcR (by unfold powCtrl; decide)).2
    · exact room_ops_keep c0 ds.length (by simpa [hlen] using hfit0)
    · exact (room_ops c1 ds.length (by simpa [hlen] using hfit1)).2

end EcbsLink2.Link2
