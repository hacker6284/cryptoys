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

/-- The cold first digit, then the remaining root digits. The up home is `rootY`. -/
theorem pow_from_strip (t : Spec.Tier) (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj0 : 0 < j) (hj : j < t.n) (hn3 : 3 ≤ t.n) :
    ∃ b',
      (do
          let b ← (do
            let b ← (do
              let b ← (do
                let b ← (do
                  let b ← Ecbs.new_board (embTier t)
                  let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
                  let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
                  let b ← Ecbs.put b Ecbs.base_across x
                  Ecbs.curve_side b Ecbs.base_across Ecbs.bottom)
                let b ← Ecbs.mul b Ecbs.gap Ecbs.bottom Ecbs.bottom true false false
                Ecbs.settle b)
              Ecbs.white0 b Ecbs.up)
            let strip ← emittedStrip t.n
            let b ← Ecbs.put b Ecbs.across strip
            pure ({ b with sudo_5Board_9marker_on := true }))
          powRun b (rootDigits t.n)) = .ok b' ∧
        PowAt b' t (curveSide t.n t.k t.benchlen (basisPeg t.n j))
          (rootY t.n t.k t.benchlen (basisPeg t.n j)) [] := by
  obtain ⟨b, hdo, s⟩ := search_strip t hOk hsh sat j hj0 hj
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
  obtain ⟨b1, hrunP, hAt⟩ := hstep
  have hrun := digit_same b cPh hlift hself 2 powGap
  have hrunB : powDigitRun b 2 powGap = .ok b1 := by
    have hif : (if (2 : Nat) = 2 then powGap else powBottom) = powGap := by simp
    rw [hrun]
    simpa [hif] using hrunP
  have hmem : ∀ e, e ∈ tail → e = 0 ∨ e = 1 ∨ e = 2 := by
    intro e he
    exact rootDigits_trit t.n e (List.mem_of_mem_tail he)
  obtain ⟨b', hr, hEnd⟩ := pow_fold b1 t side (powStep t.n t.k t.benchlen side acc 2) tail hAt hmem
  refine ⟨b', ?_, ?_⟩
  · rw [hdo, ok_bind, hred]
    simp only [powRun, if_true, hrunB, ok_bind]
    exact hr
  · have hacc : tail.foldl (powStep t.n t.k t.benchlen side) (powStep t.n t.k t.benchlen side acc 2) =
        rootY t.n t.k t.benchlen x := by
      rw [← List.foldl_cons, ← hred, rootY_digits]
    have hEnd' : PowAt b' t side (rootY t.n t.k t.benchlen x) [] :=
      hacc ▸ hEnd
    simpa [side, x] using hEnd'

end EcbsLink2.Link2
