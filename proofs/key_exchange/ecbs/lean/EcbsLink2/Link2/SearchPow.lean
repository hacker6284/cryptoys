/-
  The first root digit starts with the marker at `-1` and the flag on.
  `marker_lift` is the identity there. A phantom board whose marker is `0`
  and whose control counter is one behind lifts to that board, so the
  seated digit theorem applies. The tail is `pow_fold`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchStrip
import EcbsLink2.Link2.PowLoop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- Moves through the strip, plus one `powMove` for every root digit. -/
def holeMove (n bench : Nat) : Nat :=
  gapCap n bench + 1 + n + powMove n bench * n

private theorem gap_le (n bench : Nat) :
    gapCap n bench + 1 + n ≤ 2 * (n * n) + 17 * n + 9 * bench + 2 := by
  unfold gapCap sideCap
  have hmul : n * (n + 1) = n * n + n := by rw [Nat.mul_succ]
  have hsub : 9 * (bench - n) ≤ 9 * bench := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  rw [hmul]
  omega

private theorem pow_prod (n bench : Nat) :
    powMove n bench * n = n * n * n + 6 * (n * n) + 6 * bench * n := by
  unfold powMove
  have h1 : (n * n + 6 * n + 6 * bench) * n =
      (n * n + 6 * n) * n + (6 * bench) * n := by rw [Nat.add_mul]
  have h2 : (n * n + 6 * n) * n = (n * n) * n + (6 * n) * n := by rw [Nat.add_mul]
  rw [h1, h2, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]

private theorem hole_le (n bench : Nat) :
    holeMove n bench ≤ n * n * n + 8 * (n * n) + 6 * bench * n + 17 * n + 9 * bench + 2 := by
  unfold holeMove
  rw [pow_prod]
  have hg := gap_le n bench
  omega

theorem hole_move_fit (n bench m : Nat) (hn : n ≤ 1000000) (hb : bench ≤ 1000001)
    (hm : m ≤ holeMove n bench) : FitsLen m := by
  have hbig : 1000000 * 1000000 * 1000000 + 8 * (1000000 * 1000000) +
      6 * 1000001 * 1000000 + 17 * 1000000 + 9 * 1000001 + 2 ≤ 9223372036854775807 := by
    decide
  have h3 : n * n * n ≤ 1000000 * 1000000 * 1000000 :=
    Nat.mul_le_mul (Nat.mul_le_mul hn hn) hn
  have h2 : 8 * (n * n) ≤ 8 * (1000000 * 1000000) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hn hn)
  have h6 : 6 * bench * n ≤ 6 * 1000001 * 1000000 := by
    have hbn : bench * n ≤ 1000001 * 1000000 := Nat.mul_le_mul hb hn
    have h6' : 6 * (bench * n) ≤ 6 * (1000001 * 1000000) := Nat.mul_le_mul_left 6 hbn
    simpa [Nat.mul_assoc] using h6'
  have h17 : 17 * n ≤ 17 * 1000000 := Nat.mul_le_mul_left _ hn
  have h9 : 9 * bench ≤ 9 * 1000001 := Nat.mul_le_mul_left _ hb
  have hsum := hole_le n bench
  have : holeMove n bench ≤ 1000000 * 1000000 * 1000000 + 8 * (1000000 * 1000000) +
      6 * 1000001 * 1000000 + 17 * 1000000 + 9 * 1000001 + 2 := by
    omega
  unfold FitsLen i64MaxNat
  omega

private theorem small_fit (m : Nat) (hm : m ≤ 5000000000000) : FitsLen m := by
  have hbig : 5000000000000 ≤ 9223372036854775807 := by decide
  unfold FitsLen i64MaxNat
  omega

private theorem slide_fit (n sl k : Nat) (hn : n ≤ 1000000) (hs : sl ≤ 6 * n) (hk : k ≤ n) :
    FitsLen (sl + powSlide n * k) := by
  unfold powSlide
  have heq : (4 * n) * k = 4 * (n * k) := by rw [Nat.mul_assoc]
  have hnk : n * k ≤ n * n := Nat.mul_le_mul_left n hk
  have h4 : 4 * (n * k) ≤ 4 * (n * n) := Nat.mul_le_mul_left 4 hnk
  have hsum : sl + 4 * (n * k) ≤ 6 * n + 4 * (n * n) := by omega
  have hnn : n * n ≤ 1000000 * 1000000 := Nat.mul_le_mul hn hn
  have h6n : 6 * n ≤ 6 * 1000000 := Nat.mul_le_mul_left 6 hn
  have h4m : 4 * (n * n) ≤ 4 * (1000000 * 1000000) := Nat.mul_le_mul_left 4 hnn
  have htop : 6 * n + 4 * (n * n) ≤ 6 * 1000000 + 4 * (1000000 * 1000000) := by omega
  have hbig : 6 * 1000000 + 4 * (1000000 * 1000000) ≤ 5000000000000 := by decide
  rw [heq]
  exact small_fit _ (Nat.le_trans (Nat.le_trans hsum htop) hbig)

private theorem ctrl_fit (c k : Nat) (hc : c ≤ 1000000) (hk : k ≤ 1000000) :
    FitsLen (c + 4 * k) := by
  have hle : c + 4 * k ≤ 1000000 + 4 * 1000000 := by omega
  exact small_fit _ (Nat.le_trans hle (by decide))

private theorem ops_fit (c k : Nat) (hc : c ≤ 1000000) (hk : k ≤ 1000000) :
    FitsLen (c + k) := by
  have hle : c + k ≤ 2000000 := by omega
  exact small_fit _ (Nat.le_trans hle (by decide))

private theorem six (sl n : Nat) (h : sl ≤ 4 * n + 2 * n) : sl ≤ 6 * n := by
  omega

private theorem spend_add (mv mv' p cap : Nat) (h : mv' ≤ mv + p) (hc : mv ≤ cap) :
    mv' ≤ cap + p := by omega

private theorem ctrl_pad (c r k : Nat) (h : c ≤ r - 1 + 4 * k) : c ≤ r + 4 * k := by
  omega

private theorem tail_len (n : Nat) (ds : List Nat)
    (h : rootDigits n = 2 :: ds) (hlen : (rootDigits n).length = n - 1) :
    ds.length + 1 = n - 1 := by
  have hcons : (2 :: ds).length = ds.length + 1 := by simp
  rw [← hcons, ← h]
  exact hlen

private theorem strip_len (n : Nat) (hn : 2 ≤ n) : (rootStrip n).length = n := by
  rw [rootStrip_eq n hn]
  simp [rootDigits, List.length_append, List.length_map, List.length_range]
  omega

theorem tierR_pos (t : Spec.Tier) (hn : 3 ≤ t.n) : 0 < tierR t := by
  unfold tierR
  have h : 1 < t.n - 1 := by omega
  rw [rungList_gt h, List.length_cons]
  omega

private theorem range_pos (k : Nat) :
    List.range (k + 1) = 0 :: (List.range k).map Nat.succ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    calc
      List.range (k + 1 + 1) = List.range (k + 1) ++ [k + 1] := by rw [List.range_succ]
      _ = (0 :: (List.range k).map Nat.succ) ++ [k + 1] := by rw [ih]
      _ = 0 :: ((List.range k).map Nat.succ ++ [Nat.succ k]) := by simp [Nat.succ_eq_add_one]
      _ = 0 :: (List.range (k + 1)).map Nat.succ := by
        rw [List.range_succ, List.map_append]
        simp [Nat.succ_eq_add_one]

theorem root_red (n : Nat) (hn : 3 ≤ n) :
    rootDigits n = 2 :: (rootDigits n).tail := by
  have hn1 : n - 1 = (n - 2) + 1 := by omega
  have h0 : rootDigit n 0 = 2 := by
    unfold rootDigit
    simp [show ¬ 0 + 2 = n by omega, Nat.zero_mod]
  have hsplit : rootDigits n =
      rootDigit n 0 :: ((List.range (n - 2)).map (fun i => rootDigit n (i + 1))) := by
    simp [rootDigits, hn1, range_pos, List.map_cons, Nat.succ_eq_add_one]
  rw [hsplit, h0]
  simp

private theorem white_len (n : Nat) (_hn : 0 < n) : (whiteHole0 n).length = n := by
  simp [whiteHole0, List.length_replicate]
  omega

private theorem white_trits (n : Nat) (_hn : 0 < n) : allTritList (whiteHole0 n) := by
  intro x hx
  simp [whiteHole0, List.mem_cons, List.mem_replicate] at hx
  rcases hx with rfl | ⟨_, rfl⟩
  · decide
  · decide

private theorem add_len (n : Nat) (xs ys : List Nat) : (fieldAdd n xs ys).length = n := by
  simp [fieldAdd, List.length_map, List.length_range]

private theorem side_len (n k bench : Nat) (x : List Nat) :
    (curveSide n k bench x).length = n := by
  unfold curveSide
  rw [add_len]

private theorem side_trits (n k bench : Nat) (x : List Nat) :
    allTritList (curveSide n k bench x) := by
  unfold curveSide
  exact fieldAdd_trits _ _ _

/-- The strip board with the marker seated at `0` and the control counter
    one behind, so `marker_lift` restores the strip board. -/
def coldPhantom (b : Ecbs.Board) (ctrl : Nat) : Ecbs.Board :=
  { b with
    sudo_5Board_6marker := Int.ofNat 0
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat ctrl } }

theorem cold_lift (b : Ecbs.Board) (ctrl : Nat)
    (hm : b.sudo_5Board_6marker = -1)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (ctrl + 1))
    (hfit : FitsLen (ctrl + 1)) :
    Ecbs.marker_lift (coldPhantom b ctrl) = .ok b := by
  have hl := marker_lift_refines (coldPhantom b ctrl) 0 ctrl
    (by simp [coldPhantom]) (by simp [coldPhantom, ofNat_eq_natCast]) hfit
  rw [hl]
  congr 1
  apply board_ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · apply cost_ext
    · rfl
    · rfl
    · simpa [coldPhantom] using hc.symm
    all_goals simp [coldPhantom]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa [coldPhantom] using hm.symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

private theorem digit_same (b : Ecbs.Board) (ctrl : Nat)
    (hl : Ecbs.marker_lift (coldPhantom b ctrl) = .ok b)
    (hb : Ecbs.marker_lift b = .ok b) (d src : Nat) :
    powDigitRun b d src = powDigitRun (coldPhantom b ctrl) d src := by
  unfold powDigitRun
  by_cases hd : d = 0
  · simp [hd, hl, hb, ok_bind]
  · simp [hd, hl, hb, ok_bind]

private theorem slot_some (b : Ecbs.Board) (i v : Nat)
    (hsz : b.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5)
    (hlt : i < 5)
    (hv : ∀ h : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size,
      b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (v : Int)) :
    b.sudo_5Board_4cost.sudo_5Costs_3ops[i]? = some (Int.ofNat v) := by
  have hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [hsz]; exact hlt
  rw [Array.getElem?_eq_getElem hi]
  simpa [ofNat_eq_natCast] using hv hi

private theorem home_some (b : Ecbs.Board) (i : Nat) (v : Array Int)
    (hsz : b.sudo_5Board_4home.size = 8) (hi : i < 8)
    (hv : ∀ h : i < b.sudo_5Board_4home.size, b.sudo_5Board_4home[i] = v) :
    b.sudo_5Board_4home[i]? = some v := by
  have h : i < b.sudo_5Board_4home.size := by rw [hsz]; exact hi
  rw [Array.getElem?_eq_getElem h]
  exact congrArg some (hv h)

private theorem held_some (b : Ecbs.Board) (i : Nat) (v : Bool)
    (hsz : b.sudo_5Board_4held.size = 8) (hi : i < 8)
    (hv : ∀ h : i < b.sudo_5Board_4held.size, b.sudo_5Board_4held[i] = v) :
    b.sudo_5Board_4held[i]? = some v := by
  have h : i < b.sudo_5Board_4held.size := by rw [hsz]; exact hi
  rw [Array.getElem?_eq_getElem h]
  exact congrArg some (hv h)

/-- The root power on the strip board. The up home is `rootY`. -/
theorem pow_from_strip (b : Ecbs.Board) (t : Spec.Tier) (j : Nat)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t) (s : StripAt b t j)
    (hn3 : 3 ≤ t.n) :
    ∃ b',
      powRun b (rootDigits t.n) = .ok b' ∧
        PowAt b' t (curveSide t.n t.k t.benchlen (basisPeg t.n j))
          (rootY t.n t.k t.benchlen (basisPeg t.n j)) [] ∧
        b'.sudo_5Board_4home[0]? = some (embed (rootStrip t.n)) ∧
        b'.sudo_5Board_4held[0]? = some true ∧
        b'.sudo_5Board_4home[3]? = some (embed (basisPeg t.n j)) ∧
        b'.sudo_5Board_4held[3]? = some true ∧
        (∃ mv, b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧
          mv ≤ gapCap t.n t.benchlen + 1 + t.n + powMove t.n t.benchlen * (t.n - 1)) ∧
        (∃ sl, b'.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧
          sl ≤ 6 * t.n + powSlide t.n * (t.n - 1)) ∧
        (∃ c, b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c ∧
          c ≤ tierR t + powCtrl * (t.n - 1)) ∧
        (∃ c0, b'.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) ∧
          c0 ≤ 2 + (t.n - 1)) ∧
        b'.sudo_5Board_4home[4]? = some (#[] : Array Int) ∧
        b'.sudo_5Board_4held[4]? = some false := by
  let x := basisPeg t.n j
  let side := curveSide t.n t.k t.benchlen x
  let acc := whiteHole0 t.n
  have hRpos : 0 < tierR t := tierR_pos t hn3
  let cPh := tierR t - 1
  have hcPh : cPh + 1 = tierR t := by omega
  have hm : b.sudo_5Board_6marker = -1 := s.marker
  have hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (cPh + 1) := by
    simpa [hcPh] using s.ctrl
  have hRle : tierR t ≤ 1000000 := by
    have hlen := rungList_length_le (t.n - 1)
    exact Nat.le_trans (by simpa [tierR] using hlen) (Nat.le_trans (Nat.sub_le _ _) hsh.n_small)
  have hfitC1 : FitsLen (cPh + 1) :=
    ctrl_fit (cPh + 1) 0 (by simpa [hcPh] using hRle) (by decide)
  have hlift := cold_lift b cPh hm hc hfitC1
  have hself := marker_lift_below b (by rw [hm]; decide)
  let bP := coldPhantom b cPh
  have hred := root_red t.n hn3
  let tail := (rootDigits t.n).tail
  have hlenD : (rootDigits t.n).length = t.n - 1 := rootDigits_length t.n
  rcases s.moves with ⟨mv, hmv, hmvLe⟩
  rcases s.slides with ⟨sl, hsl, hslLe⟩
  rcases s.peak with ⟨pk, hpk⟩
  rcases s.strict with ⟨ps, hps⟩
  rcases s.hole with ⟨holeN, hhole⟩
  have hnb : t.n ≤ t.benchlen := mul_span_n t.n t.benchlen hOk.n_pos sat.mul_span
  have hmvFit : FitsLen (mv + powMove t.n t.benchlen * (t.n - 1)) := by
    have hle : mv + powMove t.n t.benchlen * (t.n - 1) ≤ holeMove t.n t.benchlen := by
      have hmul : powMove t.n t.benchlen * (t.n - 1) ≤ powMove t.n t.benchlen * t.n :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      unfold holeMove
      omega
    exact hole_move_fit t.n t.benchlen _ hsh.n_small hsh.small.2.2.2 hle
  have hslFit : FitsLen (sl + powSlide t.n * (t.n - 1)) :=
    slide_fit t.n sl (t.n - 1) hsh.n_small (six sl t.n hslLe) (Nat.sub_le _ _)
  have hcFit : FitsLen (cPh + powCtrl * (t.n - 1)) := by
    unfold powCtrl
    exact ctrl_fit cPh (t.n - 1) (Nat.le_trans (Nat.sub_le _ _) hRle)
      (Nat.le_trans (Nat.sub_le _ _) hsh.n_small)
  have hop0Fit : FitsLen (2 + (t.n - 1)) :=
    ops_fit 2 (t.n - 1) (by decide) (Nat.le_trans (Nat.sub_le _ _) hsh.n_small)
  have hop1Fit : FitsLen (1 + (t.n - 1)) :=
    ops_fit 1 (t.n - 1) (by decide) (Nat.le_trans (Nat.sub_le _ _) hsh.n_small)
  have hPow : PowAt bP t side acc (rootDigits t.n) := {
    tier := by simp [bP, coldPhantom, s.tier]
    shape := hsh
    sat := sat
    markerOn := by simp [bP, coldPhantom, s.markerOn]
    benchOff := by simp [bP, coldPhantom, s.benchOff]
    accLen := white_len t.n hOk.n_pos
    rhsLen := side_len t.n t.k t.benchlen x
    nPos := hOk.n_pos
    accT := white_trits t.n hOk.n_pos
    rhsT := side_trits t.n t.k t.benchlen x
    upHome := by
      simpa [bP, coldPhantom, powUp, acc] using
        home_some b powUp (embed acc) s.szH (by decide) (by intro h; simpa [powUp, acc] using s.upHome h)
    upHeld := by
      simpa [bP, coldPhantom, powUp] using
        held_some b powUp true s.szD (by decide) (by intro h; simpa [powUp] using s.upHeld h)
    botHome := by
      simpa [bP, coldPhantom, powBottom, side, x] using
        home_some b powBottom (embed side) s.szH (by decide)
          (by intro h; simpa [powBottom, side, x] using s.botHome h)
    botHeld := by
      simpa [bP, coldPhantom, powBottom] using
        held_some b powBottom true s.szD (by decide) (by intro h; simpa [powBottom] using s.botHeld h)
    gapHome := by
      simpa [bP, coldPhantom, powGap, side, x] using
        home_some b powGap (embed (fieldMul t.n t.k t.benchlen side side)) s.szH (by decide)
          (by intro h; simpa [powGap, side, x] using s.gapHome h)
    gapHeld := by
      simpa [bP, coldPhantom, powGap] using
        held_some b powGap true s.szD (by decide) (by intro h; simpa [powGap] using s.gapHeld h)
    spareOff := by
      simpa [bP, coldPhantom, powSpare] using
        held_some b powSpare false s.szD (by decide) (by intro h; simpa [powSpare] using s.spareOff h)
    homeWide := by simp [bP, coldPhantom, powSpare, s.szH]
    pack := ⟨mv, sl, cPh, 0, 0, pk, ps, holeN, 2, 1,
      by simpa [bP, coldPhantom] using hmv,
      by simpa [bP, coldPhantom] using hsl,
      by simp [bP, coldPhantom],
      by simp [bP, coldPhantom],
      by decide,
      by simpa [bP, coldPhantom] using s.mx,
      by simpa [bP, coldPhantom, ofNat_eq_natCast] using hpk,
      by simpa [bP, coldPhantom] using hps,
      by simpa [bP, coldPhantom] using hhole,
      by simpa [bP, coldPhantom] using s.opsSz,
      by simpa [bP, coldPhantom] using slot_some b 0 2 s.opsSz (by decide) s.ops0,
      by simpa [bP, coldPhantom] using slot_some b 1 1 s.opsSz (by decide) s.ops1,
      by simpa [hlenD] using hmvFit,
      by simpa [hlenD] using hslFit,
      by simpa [hlenD] using hcFit,
      by simpa [hlenD] using hop0Fit,
      by simpa [hlenD] using hop1Fit⟩ }
  have hPow2 : PowAt bP t side acc (2 :: tail) := by
    rw [hred] at hPow
    exact hPow
  have hstep := pow_step_at bP t side acc 2 tail hPow2 (Or.inr (Or.inr rfl))
  obtain ⟨b1, hrunP, hAt, hk1, hsp1, _hctrl1⟩ := hstep
  have hrun := digit_same b cPh hlift hself 2 powGap
  have hrunB : powDigitRun b 2 powGap = .ok b1 := by
    have hif : (if (2 : Nat) = 2 then powGap else powBottom) = powGap := by simp
    rw [hrun]
    simpa [hif] using hrunP
  have hmem : ∀ e, e ∈ tail → e = 0 ∨ e = 1 ∨ e = 2 := by
    intro e he
    exact rootDigits_trit t.n e (List.mem_of_mem_tail he)
  obtain ⟨b', hr, hEnd, hk2, hsp2⟩ :=
    pow_fold b1 t side (powStep t.n t.k t.benchlen side acc 2) tail hAt hmem
  have hdigits : tail.length + 1 = t.n - 1 := tail_len t.n tail hred hlenD
  have hcount : CounterLe bP b' (powMove t.n t.benchlen * (t.n - 1))
      (powSlide t.n * (t.n - 1)) (powCtrl * (t.n - 1)) (t.n - 1) := by
    simpa [hdigits] using counterLe_pow t.n t.benchlen tail.length hsp1 hsp2
  have hkeep : ∀ i, i ≠ powUp → i ≠ powSpare →
      b'.sudo_5Board_4home[i]? = b.sudo_5Board_4home[i]? ∧
      b'.sudo_5Board_4held[i]? = b.sudo_5Board_4held[i]? := by
    intro i hu hs
    obtain ⟨hhome1, hheld1⟩ := hk1 i hu hs
    obtain ⟨hhome2, hheld2⟩ := hk2 i hu hs
    have hhomeP : bP.sudo_5Board_4home[i]? = b.sudo_5Board_4home[i]? := by
      simp [bP, coldPhantom]
    have hheldP : bP.sudo_5Board_4held[i]? = b.sudo_5Board_4held[i]? := by
      simp [bP, coldPhantom]
    exact ⟨hhome2.trans (hhome1.trans hhomeP), hheld2.trans (hheld1.trans hheldP)⟩
  refine ⟨b', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hred]
    simp only [powRun, if_true, hrunB, ok_bind]
    exact hr
  · have hacc : tail.foldl (powStep t.n t.k t.benchlen side) (powStep t.n t.k t.benchlen side acc 2) =
        rootY t.n t.k t.benchlen x := by
      rw [← List.foldl_cons, ← hred, rootY_digits]
    have hEnd' : PowAt b' t side (rootY t.n t.k t.benchlen x) [] :=
      hacc ▸ hEnd
    simpa [side, x] using hEnd'
  · exact (hkeep 0 (by decide) (by decide)).1.trans
      (home_some b 0 (embed (rootStrip t.n)) s.szH (by decide)
        (by intro h; simpa using s.axHome h))
  · exact (hkeep 0 (by decide) (by decide)).2.trans
      (held_some b 0 true s.szD (by decide) (by intro h; simpa using s.axHeld h))
  · exact (hkeep 3 (by decide) (by decide)).1.trans
      (home_some b 3 (embed x) s.szH (by decide) (by intro h; simpa [x] using s.baseHome h))
  · exact (hkeep 3 (by decide) (by decide)).2.trans
      (held_some b 3 true s.szD (by decide) (by intro h; simpa using s.baseHeld h))
  · have hmvP : bP.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by
      simpa [bP, coldPhantom] using hmv
    obtain ⟨mv', hmv', hle⟩ := hcount.moves mv hmvP
    exact ⟨mv', hmv', spend_add mv mv' _ _ hle hmvLe⟩
  · have hslP : bP.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl := by
      simpa [bP, coldPhantom] using hsl
    obtain ⟨sl', hsl', hle⟩ := hcount.slides sl hslP
    exact ⟨sl', hsl', spend_add sl sl' _ _ hle (six sl t.n hslLe)⟩
  · have hcP : bP.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat cPh := by
      simp [bP, coldPhantom]
    obtain ⟨c', hc', _, hle⟩ := hcount.ctrl cPh hcP
    exact ⟨c', hc', ctrl_pad c' (tierR t) (t.n - 1) (by simpa [powCtrl, cPh] using hle)⟩
  · have hopP : bP.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat 2) := by
      simpa [bP, coldPhantom] using slot_some b 0 2 s.opsSz (by decide) s.ops0
    obtain ⟨c0', hc0', hle⟩ := hcount.ops0 2 hopP
    exact ⟨c0', hc0', hle⟩
  · exact (hkeep 4 (by decide) (by decide)).1.trans
      (home_some b 4 (#[] : Array Int) s.szH (by decide)
        (by intro h; simpa using s.buHome h))
  · exact (hkeep 4 (by decide) (by decide)).2.trans
      (held_some b 4 false s.szD (by decide)
        (by intro h; simpa using s.buOff h))

private theorem mul_ge (p k : Nat) (hk : 0 < k) : p ≤ p * k := by
  simpa [Nat.mul_one] using Nat.mul_le_mul_left p (Nat.succ_le_of_lt hk)

private theorem gap_pow_under (n bench : Nat) :
    gapCap n bench + 1 + n + powMove n bench * n ≤ perHole n bench := by
  unfold gapCap sideCap powMove perHole plantRoom
  omega

private theorem move_pow_room (mv0 mv n bench k : Nat) (hk : 0 < k)
    (hm : mv ≤ mv0 + gapCap n bench + 1 + n) :
    mv + powMove n bench * (n - 1) ≤ mv0 + perHole n bench * k := by
  have hpow : powMove n bench * (n - 1) ≤ powMove n bench * n :=
    Nat.mul_le_mul_left _ (Nat.sub_le n 1)
  have h1 := Nat.add_le_add_right hm (powMove n bench * (n - 1))
  have h2 : mv0 + gapCap n bench + 1 + n + powMove n bench * (n - 1) ≤
      mv0 + gapCap n bench + 1 + n + powMove n bench * n :=
    Nat.add_le_add_left hpow _
  have hassoc : mv0 + gapCap n bench + 1 + n + powMove n bench * n =
      mv0 + (gapCap n bench + 1 + n + powMove n bench * n) := by
    simp [Nat.add_assoc]
  have h3 : mv0 + (gapCap n bench + 1 + n + powMove n bench * n) ≤
      mv0 + perHole n bench :=
    Nat.add_le_add_left (gap_pow_under n bench) mv0
  have h2b : mv0 + gapCap n bench + 1 + n + powMove n bench * (n - 1) ≤
      mv0 + perHole n bench := by
    rw [hassoc] at h2
    exact Nat.le_trans h2 h3
  have h4 : mv0 + perHole n bench ≤ mv0 + perHole n bench * k :=
    Nat.add_le_add_left (mul_ge _ _ hk) mv0
  exact Nat.le_trans h1 (Nat.le_trans h2b h4)

private theorem slide_pow_room (sl0 sl n k : Nat) (hk : 0 < k) (hs : sl ≤ sl0 + 6 * n) :
    sl + powSlide n * (n - 1) ≤ sl0 + perSlide n * k := by
  unfold powSlide perSlide
  have hsub : (4 * n) * (n - 1) ≤ (4 * n) * n :=
    Nat.mul_le_mul_left _ (Nat.sub_le n 1)
  have hassoc : (4 * n) * n = 4 * (n * n) := Nat.mul_assoc 4 n n
  have hpiece : 6 * n + (4 * n) * (n - 1) ≤ 4 * (n * n) + 6 * n := by
    have hA : 6 * n + (4 * n) * (n - 1) ≤ 6 * n + 4 * (n * n) :=
      Nat.add_le_add_left (by rw [← hassoc]; exact hsub) _
    simpa [Nat.add_comm] using hA
  have h1 : sl + (4 * n) * (n - 1) ≤ sl0 + 6 * n + (4 * n) * (n - 1) :=
    Nat.add_le_add_right hs _
  have h2 : sl0 + 6 * n + (4 * n) * (n - 1) = sl0 + (6 * n + (4 * n) * (n - 1)) :=
    Nat.add_assoc _ _ _
  have h3 : sl0 + (6 * n + (4 * n) * (n - 1)) ≤ sl0 + (4 * (n * n) + 6 * n) :=
    Nat.add_le_add_left hpiece _
  have h4 : 4 * (n * n) + 6 * n ≤ (4 * (n * n) + 6 * n) * k := mul_ge _ _ hk
  have h5 : sl0 + (4 * (n * n) + 6 * n) ≤ sl0 + (4 * (n * n) + 6 * n) * k :=
    Nat.add_le_add_left h4 _
  have hper : 4 * n * n + 6 * n = 4 * (n * n) + 6 * n := by
    rw [Nat.mul_assoc]
  rw [hper]
  exact Nat.le_trans h1 (by rw [h2]; exact Nat.le_trans h3 h5)

private theorem ctrl_pow_room (base c n k : Nat) (hk : 0 < k) (_hpos : 0 < base)
    (hc : c = base - 1) :
    c + powCtrl * (n - 1) ≤ base + perCtrl n * k := by
  unfold powCtrl perCtrl
  have hsub : 4 * (n - 1) ≤ 4 * n := Nat.mul_le_mul_left 4 (Nat.sub_le n 1)
  have hper : 4 * n ≤ 4 * n + 4 := Nat.le_add_right _ _
  have hmul : 4 * n + 4 ≤ (4 * n + 4) * k := mul_ge _ _ hk
  have h1 : c + 4 * (n - 1) ≤ base + 4 * (n - 1) := by
    rw [hc]
    exact Nat.add_le_add_right (Nat.sub_le base 1) _
  have h2 : base + 4 * (n - 1) ≤ base + 4 * n := Nat.add_le_add_left hsub _
  have h3 : base + 4 * n ≤ base + (4 * n + 4) := Nat.add_le_add_left hper _
  have h4 : base + (4 * n + 4) ≤ base + (4 * n + 4) * k := Nat.add_le_add_left hmul _
  exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4))

private theorem op_pow_room (o n k : Nat) (hk : 0 < k) :
    o + 2 + (n - 1) ≤ o + perOp n * k := by
  unfold perOp
  have hstep : 2 + (n - 1) ≤ 2 + n := Nat.add_le_add_left (Nat.sub_le n 1) _
  have hcomm : 2 + n = n + 2 := Nat.add_comm _ _
  have hmul : n + 2 ≤ (n + 2) * k := mul_ge _ _ hk
  have hsum : 2 + (n - 1) ≤ (n + 2) * k :=
    Nat.le_trans hstep (Nat.le_trans (Nat.le_of_eq hcomm) hmul)
  have hassoc : o + 2 + (n - 1) = o + (2 + (n - 1)) := Nat.add_assoc _ _ _
  rw [hassoc]
  exact Nat.add_le_add_left hsum _

private theorem seven_eight (s : Nat) (h1 : 7 < s) (h2 : ¬ 8 < s) : s = 8 := by
  omega

private theorem op1_pow_room (o n k : Nat) (hk : 0 < k) :
    o + 1 + (n - 1) ≤ o + perOp n * k := by
  unfold perOp
  have hstep : 1 + (n - 1) ≤ 1 + n := Nat.add_le_add_left (Nat.sub_le n 1) _
  have hcomm : 1 + n = n + 1 := Nat.add_comm _ _
  have hone : n + 1 ≤ n + 2 := Nat.le_succ _
  have hmul : n + 2 ≤ (n + 2) * k := mul_ge _ _ hk
  have hsum : 1 + (n - 1) ≤ (n + 2) * k :=
    Nat.le_trans hstep (Nat.le_trans (by rw [hcomm]; exact hone) hmul)
  have hassoc : o + 1 + (n - 1) = o + (1 + (n - 1)) := Nat.add_assoc _ _ _
  rw [hassoc]
  exact Nat.add_le_add_left hsum _

/-- The root power on a planted strip. The phantom board, marker `0` and one
    control step behind, is only the device that seats the first digit.
    `powRun` is the real strip board. -/
theorem pow_from_strip_at (b : Ecbs.Board) (t : Spec.Tier) (j : Nat)
    (mv0 sl0 c0 o0 o1 holesLeft : Nat)
    (s : StripKeep b t j mv0 sl0 c0 o0 o1 holesLeft)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t) (hn3 : 3 ≤ t.n)
    (hk : 0 < holesLeft)
    (hmvB : FitsLen (mv0 + perHole t.n t.benchlen * holesLeft))
    (hslB : FitsLen (sl0 + perSlide t.n * holesLeft))
    (hcB : FitsLen (c0 + tierR t + perCtrl t.n * holesLeft)) :
    ∃ b',
      powRun b (rootDigits t.n) = .ok b' ∧
        PowAt b' t (curveSide t.n t.k t.benchlen (basisPeg t.n j))
          (rootY t.n t.k t.benchlen (basisPeg t.n j)) [] ∧
        b'.sudo_5Board_4home[0]? = some (embed (rootStrip t.n)) ∧
        b'.sudo_5Board_4held[0]? = some true ∧
        b'.sudo_5Board_4home[3]? = some (embed (basisPeg t.n j)) ∧
        b'.sudo_5Board_4held[3]? = some true ∧
        (∃ mv, b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv ∧
          mv ≤ mv0 + gapCap t.n t.benchlen + 1 + t.n +
            powMove t.n t.benchlen * (t.n - 1)) ∧
        (∃ sl, b'.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl ∧
          sl ≤ sl0 + 6 * t.n + powSlide t.n * (t.n - 1)) ∧
        (∃ c, b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c ∧
          c0 + tierR t ≤ c ∧
          c ≤ c0 + tierR t + powCtrl * (t.n - 1)) ∧
        (∃ cOp, b'.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat cOp) ∧
          cOp ≤ o0 + 2 + (t.n - 1)) ∧
        (∃ c1, b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (Int.ofNat c1) ∧
          c1 ≤ o1 + 1 + (t.n - 1)) ∧
        b'.sudo_5Board_4cost.sudo_5Costs_3ops.size = 5 ∧
        b'.sudo_5Board_4home.size = 8 ∧
        b'.sudo_5Board_4held.size = 8 ∧
        b'.sudo_5Board_4home[4]? = some (#[] : Array Int) ∧
        b'.sudo_5Board_4held[4]? = some false := by
  let x := basisPeg t.n j
  let side := curveSide t.n t.k t.benchlen x
  let acc := whiteHole0 t.n
  let base := c0 + tierR t
  have hbase : 0 < base := Nat.lt_of_lt_of_le (tierR_pos t hn3) (Nat.le_add_left _ c0)
  let cPh := base - 1
  have hcPh : cPh + 1 = base := Nat.sub_add_cancel (Nat.succ_le_of_lt hbase)
  have hm : b.sudo_5Board_6marker = -1 := s.marker
  have hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (cPh + 1) := by
    simpa [base, hcPh] using s.ctrl
  have hfitC1 : FitsLen (cPh + 1) := by
    have hle : cPh + 1 ≤ base + perCtrl t.n * holesLeft := by
      rw [hcPh]
      exact Nat.le_add_right _ _
    exact FitsLen.of_le hcB (by simpa [base] using hle)
  have hlift := cold_lift b cPh hm hc hfitC1
  have hself := marker_lift_below b (by rw [hm]; decide)
  let bP := coldPhantom b cPh
  have hred := root_red t.n hn3
  let tail := (rootDigits t.n).tail
  have hlenD : (rootDigits t.n).length = t.n - 1 := rootDigits_length t.n
  rcases s.moves with ⟨mv, hmv, hmvLe⟩
  rcases s.slides with ⟨sl, hsl, hslLe⟩
  rcases s.peak with ⟨pk, hpk⟩
  rcases s.strict with ⟨ps, hps⟩
  rcases s.hole with ⟨holeN, hhole⟩
  rcases s.mx with ⟨mxN, hmx⟩
  let oS0 := o0 + 2
  let oS1 := o1 + 1
  have hmvFit : FitsLen (mv + powMove t.n t.benchlen * (t.n - 1)) :=
    FitsLen.of_le hmvB (move_pow_room mv0 mv t.n t.benchlen holesLeft hk hmvLe)
  have hslFit : FitsLen (sl + powSlide t.n * (t.n - 1)) :=
    FitsLen.of_le hslB (slide_pow_room sl0 sl t.n holesLeft hk hslLe)
  have hcFit : FitsLen (cPh + powCtrl * (t.n - 1)) :=
    FitsLen.of_le hcB (by
      simpa [base] using ctrl_pow_room base cPh t.n holesLeft hk hbase rfl)
  have hop0Fit : FitsLen (oS0 + (t.n - 1)) :=
    FitsLen.of_le s.opsRoom (by
      simpa [oS0, Nat.add_assoc] using op_pow_room o0 t.n holesLeft hk)
  have hop1Fit : FitsLen (oS1 + (t.n - 1)) :=
    FitsLen.of_le s.ops1Room (by
      simpa [oS1, Nat.add_assoc] using op1_pow_room o1 t.n holesLeft hk)
  have hPow : PowAt bP t side acc (rootDigits t.n) := {
    tier := by simp [bP, coldPhantom, s.tier]
    shape := hsh
    sat := sat
    markerOn := by simp [bP, coldPhantom, s.markerOn]
    benchOff := by simp [bP, coldPhantom, s.benchOff]
    accLen := white_len t.n hOk.n_pos
    rhsLen := side_len t.n t.k t.benchlen x
    nPos := hOk.n_pos
    accT := white_trits t.n hOk.n_pos
    rhsT := side_trits t.n t.k t.benchlen x
    upHome := by
      simpa [bP, coldPhantom, powUp, acc] using
        home_some b powUp (embed acc) s.szH (by decide)
          (by intro h; simpa [powUp, acc] using s.upHome h)
    upHeld := by
      simpa [bP, coldPhantom, powUp] using
        held_some b powUp true s.szD (by decide) (by intro h; simpa [powUp] using s.upHeld h)
    botHome := by
      simpa [bP, coldPhantom, powBottom, side, x] using
        home_some b powBottom (embed side) s.szH (by decide)
          (by intro h; simpa [powBottom, side, x] using s.botHome h)
    botHeld := by
      simpa [bP, coldPhantom, powBottom] using
        held_some b powBottom true s.szD (by decide)
          (by intro h; simpa [powBottom] using s.botHeld h)
    gapHome := by
      simpa [bP, coldPhantom, powGap, side, x] using
        home_some b powGap (embed (fieldMul t.n t.k t.benchlen side side)) s.szH (by decide)
          (by intro h; simpa [powGap, side, x] using s.gapHome h)
    gapHeld := by
      simpa [bP, coldPhantom, powGap] using
        held_some b powGap true s.szD (by decide) (by intro h; simpa [powGap] using s.gapHeld h)
    spareOff := by
      simpa [bP, coldPhantom, powSpare] using
        held_some b powSpare false s.szD (by decide)
          (by intro h; simpa [powSpare] using s.spareOff h)
    homeWide := by simp [bP, coldPhantom, powSpare, s.szH]
    pack := ⟨mv, sl, cPh, 0, mxN, pk, ps, holeN, oS0, oS1,
      by simpa [bP, coldPhantom] using hmv,
      by simpa [bP, coldPhantom] using hsl,
      by simp [bP, coldPhantom, ofNat_eq_natCast],
      by simp [bP, coldPhantom],
      by decide,
      by simpa [bP, coldPhantom] using hmx,
      by simpa [bP, coldPhantom, ofNat_eq_natCast] using hpk,
      by simpa [bP, coldPhantom] using hps,
      by simpa [bP, coldPhantom] using hhole,
      by simpa [bP, coldPhantom] using s.opsSz,
      by simpa [bP, coldPhantom, oS0] using slot_some b 0 oS0 s.opsSz (by decide) s.ops0,
      by simpa [bP, coldPhantom, oS1] using slot_some b 1 oS1 s.opsSz (by decide) s.ops1,
      by simpa [hlenD] using hmvFit,
      by simpa [hlenD] using hslFit,
      by simpa [hlenD] using hcFit,
      by simpa [hlenD] using hop0Fit,
      by simpa [hlenD] using hop1Fit⟩ }
  have hPow2 : PowAt bP t side acc (2 :: tail) := by
    rw [hred] at hPow
    exact hPow
  have hstep := pow_step_at bP t side acc 2 tail hPow2 (Or.inr (Or.inr rfl))
  obtain ⟨b1, hrunP, hAt, hk1, hsp1, _hctrl1⟩ := hstep
  have hrun := digit_same b cPh hlift hself 2 powGap
  have hrunB : powDigitRun b 2 powGap = .ok b1 := by
    have hif : (if (2 : Nat) = 2 then powGap else powBottom) = powGap := by simp
    rw [hrun]
    simpa [hif] using hrunP
  have hmem : ∀ e, e ∈ tail → e = 0 ∨ e = 1 ∨ e = 2 := by
    intro e he
    exact rootDigits_trit t.n e (List.mem_of_mem_tail he)
  obtain ⟨b', hr, hEnd, hk2, hsp2⟩ :=
    pow_fold b1 t side (powStep t.n t.k t.benchlen side acc 2) tail hAt hmem
  have hdigits : tail.length + 1 = t.n - 1 := tail_len t.n tail hred hlenD
  have hcount : CounterLe bP b' (powMove t.n t.benchlen * (t.n - 1))
      (powSlide t.n * (t.n - 1)) (powCtrl * (t.n - 1)) (t.n - 1) := by
    simpa [hdigits] using counterLe_pow t.n t.benchlen tail.length hsp1 hsp2
  have hkeep : ∀ i, i ≠ powUp → i ≠ powSpare →
      b'.sudo_5Board_4home[i]? = b.sudo_5Board_4home[i]? ∧
      b'.sudo_5Board_4held[i]? = b.sudo_5Board_4held[i]? := by
    intro i hu hs
    obtain ⟨hhome1, hheld1⟩ := hk1 i hu hs
    obtain ⟨hhome2, hheld2⟩ := hk2 i hu hs
    exact ⟨hhome2.trans (hhome1.trans (by simp [bP, coldPhantom])),
      hheld2.trans (hheld1.trans (by simp [bP, coldPhantom]))⟩
  have slot_lt (i : Nat) (hi : i < 8) (hne1 : i ≠ powUp) (hne6 : i ≠ powSpare) :
      i < b'.sudo_5Board_4home.size := by
    have hsome : b.sudo_5Board_4home[i]? =
        some (b.sudo_5Board_4home[i]'(by rw [s.szH]; exact hi)) :=
      Array.getElem?_eq_getElem _
    have heq := (hkeep i hne1 hne6).1
    rw [← heq] at hsome
    exact (Array.getElem?_eq_some_iff.mp hsome).1
  have slot_ge (i : Nat) (hi : 8 ≤ i) : ¬ i < b'.sudo_5Board_4home.size := by
    have hnone : b.sudo_5Board_4home[i]? = none := by
      rw [Array.getElem?_eq_none_iff, s.szH]
      exact hi
    have hne1 : i ≠ powUp := by
      intro h
      exact Nat.not_le_of_lt (by decide : powUp < 8) (by rw [← h]; exact hi)
    have hne6 : i ≠ powSpare := by
      intro h
      exact Nat.not_le_of_lt (by decide : powSpare < 8) (by rw [← h]; exact hi)
    have heq := (hkeep i hne1 hne6).1
    rw [← heq] at hnone
    exact Nat.not_lt.mpr (Array.getElem?_eq_none_iff.mp hnone)
  refine ⟨b', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hred]
    simp only [powRun, if_true, hrunB, ok_bind]
    exact hr
  · have hacc : tail.foldl (powStep t.n t.k t.benchlen side) (powStep t.n t.k t.benchlen side acc 2) =
        rootY t.n t.k t.benchlen x := by
      rw [← List.foldl_cons, ← hred, rootY_digits]
    exact (hacc ▸ hEnd)
  · exact (hkeep 0 (by decide) (by decide)).1.trans
      (home_some b 0 (embed (rootStrip t.n)) s.szH (by decide)
        (by intro h; simpa using s.axHome h))
  · exact (hkeep 0 (by decide) (by decide)).2.trans
      (held_some b 0 true s.szD (by decide) (by intro h; simpa using s.axHeld h))
  · exact (hkeep 3 (by decide) (by decide)).1.trans
      (home_some b 3 (embed x) s.szH (by decide) (by intro h; simpa [x] using s.baseHome h))
  · exact (hkeep 3 (by decide) (by decide)).2.trans
      (held_some b 3 true s.szD (by decide) (by intro h; simpa using s.baseHeld h))
  · have hmvP : bP.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by
      simpa [bP, coldPhantom] using hmv
    obtain ⟨mv', hmv', hle⟩ := hcount.moves mv hmvP
    exact ⟨mv', hmv', spend_add mv mv' _ _ hle hmvLe⟩
  · have hslP : bP.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl := by
      simpa [bP, coldPhantom] using hsl
    obtain ⟨sl', hsl', hle⟩ := hcount.slides sl hslP
    exact ⟨sl', hsl', spend_add sl sl' _ _ hle hslLe⟩
  · have hcP : bP.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat cPh := by
      simp [bP, coldPhantom, ofNat_eq_natCast]
    obtain ⟨c', hc', _, hle⟩ := hcount.ctrl cPh hcP
    obtain ⟨cDig, hcDig, hc1⟩ := _hctrl1
    have hdig : cDig = cPh := Int.ofNat.inj (hcDig.symm.trans hcP)
    have hb1 : b1.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (cPh + 4) := by
      have hif : (if (2 : Nat) = 0 then 2 else 4) = 4 := by decide
      simpa [hdig, hif] using hc1
    obtain ⟨cTail, hcTail, hge, _⟩ := hsp2.ctrl (cPh + 4) hb1
    have hfinal : c' = cTail := Int.ofNat.inj (hc'.symm.trans hcTail)
    exact ⟨c', hc', by
      have h3 : cPh + 4 = base + 3 := by
        have hback : cPh + 1 = base := hcPh
        omega
      have hlo : base ≤ c' := by
        have hge' : cPh + 4 ≤ c' := by rw [hfinal]; exact hge
        omega
      exact hlo, by
      have hpad := ctrl_pad c' base (t.n - 1) (by
        simpa [powCtrl, cPh, base] using hle)
      simpa [base, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hpad⟩
  · have hopP : bP.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat oS0) := by
      simpa [bP, coldPhantom, oS0] using slot_some b 0 oS0 s.opsSz (by decide) s.ops0
    obtain ⟨cOp', hcOp', hle⟩ := hcount.ops0 oS0 hopP
    exact ⟨cOp', hcOp', by simpa [oS0, Nat.add_assoc] using hle⟩
  · have hop1P : bP.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (Int.ofNat oS1) := by
      simpa [bP, coldPhantom, oS1] using slot_some b 1 oS1 s.opsSz (by decide) s.ops1
    obtain ⟨c1', hc1', hle⟩ := hcount.ops1 oS1 hop1P
    exact ⟨c1', hc1', by simpa [oS1, Nat.add_assoc] using hle⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsz, _, _, _, _, _, _, _⟩ :=
      hEnd.pack
    exact hsz
  · exact seven_eight _ (slot_lt 7 (by decide) (by decide) (by decide))
      (slot_ge 8 (by decide))
  · have held_lt (i : Nat) (hi : i < 8) (hne1 : i ≠ powUp) (hne6 : i ≠ powSpare) :
        i < b'.sudo_5Board_4held.size := by
      have hsome : b.sudo_5Board_4held[i]? =
          some (b.sudo_5Board_4held[i]'(by rw [s.szD]; exact hi)) :=
        Array.getElem?_eq_getElem _
      have heq := (hkeep i hne1 hne6).2
      rw [← heq] at hsome
      exact (Array.getElem?_eq_some_iff.mp hsome).1
    have held_ge (i : Nat) (hi : 8 ≤ i) : ¬ i < b'.sudo_5Board_4held.size := by
      have hnone : b.sudo_5Board_4held[i]? = none := by
        rw [Array.getElem?_eq_none_iff, s.szD]
        exact hi
      have hne1 : i ≠ powUp := by
        intro h
        exact Nat.not_le_of_lt (by decide : powUp < 8) (by rw [← h]; exact hi)
      have hne6 : i ≠ powSpare := by
        intro h
        exact Nat.not_le_of_lt (by decide : powSpare < 8) (by rw [← h]; exact hi)
      have heq := (hkeep i hne1 hne6).2
      rw [← heq] at hnone
      exact Nat.not_lt.mpr (Array.getElem?_eq_none_iff.mp hnone)
    exact seven_eight _ (held_lt 7 (by decide) (by decide) (by decide))
      (held_ge 8 (by decide))
  · exact (hkeep 4 (by decide) (by decide)).1.trans
      (home_some b 4 (#[] : Array Int) s.szH (by decide)
        (by intro h; simpa using s.buHome h))
  · exact (hkeep 4 (by decide) (by decide)).2.trans
      (held_some b 4 false s.szD (by decide)
        (by intro h; simpa using s.buOff h))

end EcbsLink2.Link2
