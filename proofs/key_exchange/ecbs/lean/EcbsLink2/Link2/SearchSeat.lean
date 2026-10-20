/-
  The strip power is the board the hit test reads. Across still holds the
  root strip, the base home still holds the planted peg, and one search
  budget remains. A hit is `rootHit`; a miss moves one hole on.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchPow
import EcbsLink2.Link2.SearchLoop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

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

private theorem search_prod (n bench : Nat) :
    searchMove n bench * n = n * n * n + 8 * (n * n) + 6 * bench * n := by
  unfold searchMove
  have h1 : (n * n + 8 * n + 6 * bench) * n =
      (n * n + 8 * n) * n + (6 * bench) * n := by rw [Nat.add_mul]
  have h2 : (n * n + 8 * n) * n = (n * n) * n + (8 * n) * n := by rw [Nat.add_mul]
  rw [h1, h2, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]

private theorem poly_sum (a b c d e : Nat) :
    (a + b + c + d + e + 2) + (a + b + c) = 2 * a + 2 * b + 2 * c + d + e + 2 := by
  omega

private theorem scale16 (n : Nat) : 2 * (8 * (n * n)) = 16 * (n * n) := by omega

private theorem scale12 (b n : Nat) : 2 * (6 * b * n) = 12 * b * n := by
  have h : 2 * 6 = 12 := by decide
  calc
    2 * ((6 * b) * n) = (2 * (6 * b)) * n := by rw [← Nat.mul_assoc]
    _ = ((2 * 6) * b) * n := by rw [← Nat.mul_assoc]
    _ = (12 * b) * n := by rw [h]

private theorem seat_le (n bench : Nat) :
    holeMove n bench + searchMove n bench * n ≤
      2 * (n * n * n) + 16 * (n * n) + 12 * bench * n + 17 * n + 9 * bench + 2 := by
  have hh := hole_le n bench
  rw [search_prod]
  have h := Nat.add_le_add_right hh (n * n * n + 8 * (n * n) + 6 * bench * n)
  apply Nat.le_trans h
  rw [poly_sum (n * n * n) (8 * (n * n)) (6 * bench * n) (17 * n) (9 * bench),
    scale16 n, scale12 bench n]
  exact Nat.le_refl _

private theorem final_room (n bench mv left : Nat)
    (hmv : mv ≤ gapCap n bench + 1 + n + powMove n bench * (n - 1))
    (hleft : left ≤ n) :
    mv + searchMove n bench * left ≤ holeMove n bench + searchMove n bench * n := by
  unfold holeMove
  have hp : powMove n bench * (n - 1) ≤ powMove n bench * n :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hs : searchMove n bench * left ≤ searchMove n bench * n :=
    Nat.mul_le_mul_left _ hleft
  omega

theorem seat_move_fit (n bench m : Nat) (hn : n ≤ 1000000) (hb : bench ≤ 1000001)
    (hm : m ≤ holeMove n bench + searchMove n bench * n) : FitsLen m := by
  have hbig : 2 * (1000000 * 1000000 * 1000000) + 16 * (1000000 * 1000000) +
      12 * 1000001 * 1000000 + 17 * 1000000 + 9 * 1000001 + 2 ≤ 9223372036854775807 := by
    decide
  have h3 : 2 * (n * n * n) ≤ 2 * (1000000 * 1000000 * 1000000) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul hn hn) hn)
  have h2 : 16 * (n * n) ≤ 16 * (1000000 * 1000000) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hn hn)
  have h12 : 12 * bench * n ≤ 12 * 1000001 * 1000000 := by
    have hbn : bench * n ≤ 1000001 * 1000000 := Nat.mul_le_mul hb hn
    have h12' : 12 * (bench * n) ≤ 12 * (1000001 * 1000000) := Nat.mul_le_mul_left 12 hbn
    simpa [Nat.mul_assoc] using h12'
  have h17 : 17 * n ≤ 17 * 1000000 := Nat.mul_le_mul_left _ hn
  have h9 : 9 * bench ≤ 9 * 1000001 := Nat.mul_le_mul_left _ hb
  have hsum := seat_le n bench
  have : holeMove n bench + searchMove n bench * n ≤
      2 * (1000000 * 1000000 * 1000000) + 16 * (1000000 * 1000000) +
        12 * 1000001 * 1000000 + 17 * 1000000 + 9 * 1000001 + 2 := by
    omega
  unfold FitsLen i64MaxNat
  omega

private theorem small_fit (m : Nat) (hm : m ≤ 7000000000000) : FitsLen m := by
  have hbig : 7000000000000 ≤ 9223372036854775807 := by decide
  unfold FitsLen i64MaxNat
  omega

private theorem slide_cap (n : Nat) :
    6 * n + (4 * n) * (n - 1) + (2 * n) * n ≤ 6 * (n * n) + 6 * n := by
  have hsub : n - 1 ≤ n := Nat.sub_le _ _
  have h4 : (4 * n) * (n - 1) ≤ 4 * (n * n) := by
    have h := Nat.mul_le_mul_left (4 * n) hsub
    simpa [Nat.mul_assoc] using h
  have h2 : (2 * n) * n = 2 * (n * n) := by rw [Nat.mul_assoc]
  rw [h2]
  omega

private theorem slide_room (n sl left : Nat)
    (hs : sl ≤ 6 * n + powSlide n * (n - 1)) (hl : left ≤ n) :
    sl + searchSlide n * left ≤ 6 * (n * n) + 6 * n := by
  unfold powSlide at hs
  unfold searchSlide
  have hleft : (2 * n) * left ≤ (2 * n) * n := Nat.mul_le_mul_left _ hl
  have hcap := slide_cap n
  have hsum : sl + (2 * n) * left ≤ 6 * n + (4 * n) * (n - 1) + (2 * n) * n := by
    have h1 : sl + (2 * n) * left ≤ (6 * n + (4 * n) * (n - 1)) + (2 * n) * left :=
      Nat.add_le_add_right hs _
    exact Nat.le_trans h1 (Nat.add_le_add_left hleft _)
  exact Nat.le_trans hsum hcap

private theorem slide_search_fit (n sl left : Nat) (hn : n ≤ 1000000)
    (hs : sl ≤ 6 * n + powSlide n * (n - 1)) (hl : left ≤ n) :
    FitsLen (sl + searchSlide n * left) := by
  have hle := slide_room n sl left hs hl
  have hnn : n * n ≤ 1000000 * 1000000 := Nat.mul_le_mul hn hn
  have h6 : 6 * (n * n) ≤ 6 * (1000000 * 1000000) := Nat.mul_le_mul_left _ hnn
  have h6n : 6 * n ≤ 6 * 1000000 := Nat.mul_le_mul_left _ hn
  have htop : 6 * (n * n) + 6 * n ≤ 6 * (1000000 * 1000000) + 6 * 1000000 := by omega
  have hbig : 6 * (1000000 * 1000000) + 6 * 1000000 ≤ 7000000000000 := by decide
  exact small_fit _ (Nat.le_trans (Nat.le_trans hle htop) hbig)

private theorem tierR_small (t : Spec.Tier) (hn : t.n ≤ 1000000) : tierR t ≤ 1000000 := by
  have hlen := rungList_length_le (t.n - 1)
  exact Nat.le_trans (by simpa [tierR] using hlen) (Nat.le_trans (Nat.sub_le _ _) hn)

private theorem ctrl_cap (r n : Nat) (hr : r ≤ 1000000) (hn : n ≤ 1000000) :
    r + 4 * (n - 1) ≤ 5000000 := by omega

private theorem ctrl_room (c left cap : Nat) (hc : c ≤ cap) (hl : left ≤ 1000000)
    (hcap : cap ≤ 5000000) : c + left ≤ 6000000 := by omega

private theorem ctrl_search_fit (c left : Nat) (hc : c ≤ 5000000) (hl : left ≤ 1000000) :
    FitsLen (c + left) := by
  have hle := ctrl_room c left 5000000 hc hl (Nat.le_refl _)
  have hbig : 6000000 ≤ 7000000000000 := by decide
  exact small_fit _ (Nat.le_trans hle hbig)

private theorem ops_room (c left : Nat) (hc : c ≤ 1000002) (hl : left ≤ 1000000) :
    c + left ≤ 2000002 := by omega

private theorem ops_search_fit (c left : Nat) (hc : c ≤ 1000002) (hl : left ≤ 1000000) :
    FitsLen (c + left) := by
  have hle := ops_room c left hc hl
  have hbig : 2000002 ≤ 7000000000000 := by decide
  exact small_fit _ (Nat.le_trans hle hbig)

private theorem ops_cap (n : Nat) (hn : n ≤ 1000000) : 2 + (n - 1) ≤ 1000002 := by omega

private theorem strip_len (n : Nat) (hn : 2 ≤ n) : (rootStrip n).length = n := by
  rw [rootStrip_eq n hn]
  simp [rootDigits, List.length_append, List.length_map, List.length_range]
  omega

private theorem two_le (n : Nat) (h : 3 ≤ n) : 2 ≤ n := by omega

/-- After the root power, across is the strip and the base home is the planted
    peg. `left` hit tests still fit. -/
theorem search_ready (t : Spec.Tier) (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj0 : 0 < j) (hj : j < t.n) (hn3 : 3 ≤ t.n)
    (left : Nat) (hleft : 0 < left) (hleftN : left ≤ t.n) :
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
        SearchAt b' t (basisPeg t.n j) (rootY t.n t.k t.benchlen (basisPeg t.n j))
          (curveSide t.n t.k t.benchlen (basisPeg t.n j))
          (fieldMul t.n t.k t.benchlen
            (curveSide t.n t.k t.benchlen (basisPeg t.n j))
            (curveSide t.n t.k t.benchlen (basisPeg t.n j)))
          (rootStrip t.n) (basisPeg t.n j) left := by
  obtain ⟨bS, hstrip, s⟩ := search_strip t hOk hsh sat j hj0 hj
  obtain ⟨b', hpow, hPow, hax, haxD, hbx, hbxD, hmvE, hslE, hcE, hopE⟩ :=
    pow_from_strip bS t j hOk hsh sat s hn3
  rcases hmvE with ⟨mv, hmv, hmvLe⟩
  rcases hslE with ⟨sl, hsl, hslLe⟩
  rcases hcE with ⟨ctrl, hctrl, hctrlLe⟩
  rcases hopE with ⟨c0, hop, hopLe⟩
  have hb : t.benchlen ≤ 1000001 := hsh.small.2.2.2
  have hn : t.n ≤ 1000000 := hsh.n_small
  have hM : ∀ moves, b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves →
      FitsLen (moves + searchMove t.n t.benchlen * left) := by
    intro moves hmoves
    have hsame : moves = mv := Int.ofNat.inj (hmoves.symm.trans hmv)
    rw [hsame]
    exact seat_move_fit t.n t.benchlen _ hn hb
      (final_room t.n t.benchlen mv left hmvLe hleftN)
  have hS : ∀ slides, b'.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides →
      FitsLen (slides + searchSlide t.n * left) := by
    intro slides hsl0
    have hsame : slides = sl := Int.ofNat.inj (hsl0.symm.trans hsl)
    rw [hsame]
    exact slide_search_fit t.n sl left hn hslLe hleftN
  have hC : ∀ c, b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c →
      FitsLen (c + left) := by
    intro c hc
    have hsame : c = ctrl := Int.ofNat.inj (hc.symm.trans hctrl)
    rw [hsame]
    have hcap := ctrl_cap (tierR t) t.n (tierR_small t hn) hn
    have hpow : powCtrl = 4 := rfl
    have hle : ctrl ≤ 5000000 := by
      rw [hpow] at hctrlLe
      exact Nat.le_trans hctrlLe hcap
    exact ctrl_search_fit ctrl left hle (Nat.le_trans hleftN hn)
  have hOp : ∀ c, b'.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c) →
      FitsLen (c + left) := by
    intro c hc
    have hslot : some (Int.ofNat c) = some (Int.ofNat c0) := hc.symm.trans hop
    have hsame : c = c0 := by
      injection hslot with hEq
      exact Int.ofNat.inj hEq
    rw [hsame]
    exact ops_search_fit c0 left (Nat.le_trans hopLe (ops_cap t.n hn))
      (Nat.le_trans hleftN hn)
  refine ⟨b', ?_, ?_⟩
  · rw [hstrip, ok_bind]
    exact hpow
  exact search_of_pow b' t (basisPeg t.n j) (rootStrip t.n) (basisPeg t.n j) left hPow
    (basisPeg_length t.n j) hax haxD (strip_len t.n (two_le t.n hn3))
    hbx hbxD (basisPeg_length t.n j) hleft hM hS hC hOp

private theorem gap_plant (n bench : Nat) :
    gapCap n bench + 1 + n ≤ plantRoom n bench := by
  unfold gapCap sideCap plantRoom
  omega

private theorem ready_move (mv0 mv n bench k left : Nat) (hk : 0 < k) (hl : left ≤ k)
    (hm : mv ≤ mv0 + gapCap n bench + 1 + n + powMove n bench * (n - 1)) :
    mv + searchMove n bench * left ≤ mv0 + perHole n bench * k := by
  let A := plantRoom n bench + powMove n bench * n
  let S := searchMove n bench
  have hper : perHole n bench = A + S := by
    simp [perHole, powMove, searchMove, plantRoom, A, S]
  have hpow : powMove n bench * (n - 1) ≤ powMove n bench * n :=
    Nat.mul_le_mul_left _ (Nat.sub_le n 1)
  have hgap : gapCap n bench + 1 + n + powMove n bench * (n - 1) ≤ A := by
    exact Nat.le_trans
      (Nat.add_le_add_right (gap_plant n bench) (powMove n bench * (n - 1)))
      (Nat.add_le_add_left hpow (plantRoom n bench))
  have hS : S * left ≤ S * k := Nat.mul_le_mul_left _ hl
  have hAk : A ≤ A * k := by
    simpa [Nat.mul_one] using Nat.mul_le_mul_left A (Nat.succ_le_of_lt hk)
  have hjoin : A + S * left ≤ (A + S) * k := by
    simpa [Nat.add_mul] using Nat.add_le_add hAk hS
  have hinner : gapCap n bench + 1 + n + powMove n bench * (n - 1) + S * left ≤
      (A + S) * k :=
    Nat.le_trans (Nat.add_le_add_right hgap (S * left)) hjoin
  have hmv1 := Nat.add_le_add_right hm (S * left)
  have hassoc : mv0 + gapCap n bench + 1 + n + powMove n bench * (n - 1) + S * left =
      mv0 + (gapCap n bench + 1 + n + powMove n bench * (n - 1) + S * left) := by
    simp [Nat.add_assoc]
  have hlift : mv0 + (gapCap n bench + 1 + n + powMove n bench * (n - 1) + S * left) ≤
      mv0 + perHole n bench * k := by
    rw [hper]
    exact Nat.add_le_add_left hinner mv0
  exact Nat.le_trans hmv1 (by rw [hassoc]; exact hlift)

private theorem k_le_mul (k : Nat) : k ≤ 4 * k := by
  have h : k * 1 ≤ k * 4 := Nat.mul_le_mul_left k (by decide : (1 : Nat) ≤ 4)
  simpa [Nat.mul_one, Nat.mul_comm] using h

private theorem ready_ctrl (base ctrl n k left : Nat) (hk : 0 < k) (hl : left ≤ k)
    (hc : ctrl ≤ base + powCtrl * (n - 1)) :
    ctrl + left ≤ base + perCtrl n * k := by
  unfold powCtrl at hc
  unfold perCtrl
  have h4 : 4 * (n - 1) ≤ 4 * n := Nat.mul_le_mul_left 4 (Nat.sub_le n 1)
  have hnk : 4 * n ≤ 4 * n * k := by
    simpa [Nat.mul_one] using Nat.mul_le_mul_left (4 * n) (Nat.succ_le_of_lt hk)
  have hck : k ≤ 4 * k := k_le_mul k
  have hleft : left ≤ k := hl
  have hsum : 4 * (n - 1) + left ≤ 4 * n * k + 4 * k :=
    Nat.le_trans (Nat.add_le_add h4 hleft)
      (Nat.add_le_add hnk (Nat.le_trans (Nat.le_refl k) hck))
  have hdist : 4 * n * k + 4 * k = (4 * n + 4) * k :=
    (Nat.add_mul (4 * n) 4 k).symm
  have h1 : ctrl + left ≤ base + 4 * (n - 1) + left := Nat.add_le_add_right hc left
  have h2 : base + 4 * (n - 1) + left = base + (4 * (n - 1) + left) := Nat.add_assoc _ _ _
  have h3 : base + (4 * (n - 1) + left) ≤ base + (4 * n + 4) * k := by
    rw [← hdist]
    exact Nat.add_le_add_left hsum base
  exact Nat.le_trans h1 (by rw [h2]; exact h3)

private theorem ready_op (o cOp n k left : Nat) (hn : 0 < n) (hk : 0 < k) (hl : left ≤ k)
    (hc : cOp ≤ o + 2 + (n - 1)) :
    cOp + left ≤ o + perOp n * k := by
  unfold perOp
  have hcancel : (n - 1) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have htwo : 2 + (n - 1) = n + 1 := by
    calc
      2 + (n - 1) = 1 + 1 + (n - 1) := rfl
      _ = 1 + (1 + (n - 1)) := Nat.add_assoc 1 1 (n - 1)
      _ = 1 + ((n - 1) + 1) := by rw [Nat.add_comm 1 (n - 1)]
      _ = 1 + n := by rw [hcancel]
      _ = n + 1 := Nat.add_comm 1 n
  have hk1 : (k - 1) + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk)
  have hsplit : (n + 2) * k = (n + 2) + (n + 2) * (k - 1) := by
    have h := Nat.mul_add (n + 2) 1 (k - 1)
    have hcomm : 1 + (k - 1) = (k - 1) + 1 := Nat.add_comm _ _
    rw [hcomm, hk1, Nat.mul_one] at h
    exact h
  have hone : (1 : Nat) ≤ n + 2 := Nat.succ_le_succ (Nat.zero_le (n + 1))
  have htail : k - 1 ≤ (n + 2) * (k - 1) := by
    simpa [Nat.one_mul] using Nat.mul_le_mul_right (k - 1) hone
  have hnum : n + 1 + k ≤ (n + 2) * k := by
    have hEq : (n + 2) + (k - 1) = n + 1 + k := by
      calc
        (n + 2) + (k - 1) = n + (2 + (k - 1)) := Nat.add_assoc n 2 (k - 1)
        _ = n + (1 + 1 + (k - 1)) := rfl
        _ = n + (1 + (1 + (k - 1))) := by rw [Nat.add_assoc 1 1 (k - 1)]
        _ = n + (1 + ((k - 1) + 1)) := by rw [Nat.add_comm 1 (k - 1)]
        _ = n + (1 + k) := by rw [hk1]
        _ = n + 1 + k := (Nat.add_assoc n 1 k).symm
    rw [← hEq, hsplit]
    exact Nat.add_le_add_left htail (n + 2)
  have hleft : n + 1 + left ≤ n + 1 + k := Nat.add_le_add_left hl _
  have hsum : 2 + (n - 1) + left ≤ (n + 2) * k := by
    rw [htwo]
    exact Nat.le_trans hleft hnum
  have h1 : cOp + left ≤ o + 2 + (n - 1) + left := Nat.add_le_add_right hc left
  have h2 : o + 2 + (n - 1) + left = o + (2 + (n - 1) + left) := by
    simp [Nat.add_assoc]
  exact Nat.le_trans h1 (by rw [h2]; exact Nat.add_le_add_left hsum o)

private theorem ready_slide (sl0 sl n k left : Nat) (hn : 0 < n) (hk : 0 < k) (hl : left ≤ k)
    (hs : sl ≤ sl0 + 6 * n + (4 * n) * (n - 1)) :
    sl + (2 * n) * left ≤ sl0 + (4 * n * n + 6 * n) * k := by
  have hcancel : (n - 1) + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have h4 : (4 * n) * (n - 1) + 4 * n = (4 * n) * n := by
    have h := Nat.mul_add (4 * n) (n - 1) 1
    rw [hcancel, Nat.mul_one] at h
    exact h.symm
  have hsq : (4 * n) * n = 4 * (n * n) := Nat.mul_assoc 4 n n
  have h6n : 4 * n + 2 * n = 6 * n := by
    rw [← Nat.add_mul]
  have hpiece : (4 * n) * (n - 1) + 6 * n = 4 * (n * n) + 2 * n := by
    have h := congrArg (fun z => z + 2 * n) h4
    rw [hsq] at h
    calc
      (4 * n) * (n - 1) + 6 * n = (4 * n) * (n - 1) + (4 * n + 2 * n) := by rw [← h6n]
      _ = (4 * n) * (n - 1) + 4 * n + 2 * n := by rw [← Nat.add_assoc]
      _ = 4 * (n * n) + 2 * n := h
  have hk1 : 1 ≤ k := Nat.succ_le_of_lt hk
  have hnn : 4 * (n * n) ≤ 4 * (n * n) * k := by
    simpa [Nat.mul_one] using Nat.mul_le_mul_left (4 * (n * n)) hk1
  have h2k : 2 ≤ 2 * k := by
    simpa [Nat.mul_one] using Nat.mul_le_mul_left 2 hk1
  have hthree : k + 1 ≤ 3 * k := by
    have hstep : k + 1 ≤ k + 2 * k :=
      Nat.add_le_add_left (Nat.le_trans (by decide : (1 : Nat) ≤ 2) h2k) k
    have hsum : k + 2 * k = 3 * k := by
      simpa [Nat.one_mul, Nat.add_comm] using (Nat.add_mul 2 1 k).symm
    rw [hsum] at hstep
    exact hstep
  have h6 : 2 * n * (3 * k) = 6 * n * k := by
    calc
      2 * n * (3 * k) = 2 * (n * (3 * k)) := Nat.mul_assoc 2 n (3 * k)
      _ = 2 * (n * 3 * k) := by rw [Nat.mul_assoc n 3 k]
      _ = 2 * (3 * n * k) := by rw [Nat.mul_comm n 3]
      _ = 2 * (3 * (n * k)) := by rw [Nat.mul_assoc 3 n k]
      _ = (2 * 3) * (n * k) := (Nat.mul_assoc 2 3 (n * k)).symm
      _ = 6 * (n * k) := rfl
      _ = 6 * n * k := (Nat.mul_assoc 6 n k).symm
  have hlin : 2 * n * (left + 1) ≤ 6 * n * k := by
    have hL : left + 1 ≤ 3 * k := Nat.le_trans (Nat.add_le_add_right hl 1) hthree
    have hM : 2 * n * (left + 1) ≤ 2 * n * (3 * k) := Nat.mul_le_mul_left _ hL
    rw [h6] at hM
    exact hM
  have hcoeff : 4 * (n * n) + 2 * n * (left + 1) ≤ 4 * (n * n) * k + 6 * n * k :=
    Nat.add_le_add hnn hlin
  have hdist : 4 * (n * n) * k + 6 * n * k = (4 * (n * n) + 6 * n) * k := by
    rw [Nat.add_mul, Nat.mul_comm (4 * (n * n)) k, Nat.mul_comm (6 * n) k]
  have hpoly : 4 * n * n + 6 * n = 4 * (n * n) + 6 * n := by rw [Nat.mul_assoc]
  have h1 : sl + (2 * n) * left ≤ sl0 + 6 * n + (4 * n) * (n - 1) + (2 * n) * left :=
    Nat.add_le_add_right hs _
  have h2 : sl0 + 6 * n + (4 * n) * (n - 1) + (2 * n) * left =
      sl0 + ((4 * n) * (n - 1) + 6 * n + (2 * n) * left) := by
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have h3 : (4 * n) * (n - 1) + 6 * n + (2 * n) * left =
      4 * (n * n) + (2 * n) * (left + 1) := by
    rw [hpiece]
    have hmul := Nat.mul_add (2 * n) left 1
    rw [Nat.mul_one] at hmul
    calc
      4 * (n * n) + 2 * n + (2 * n) * left
          = 4 * (n * n) + ((2 * n) * left + 2 * n) := by
            rw [Nat.add_assoc, Nat.add_comm (2 * n) ((2 * n) * left), ← Nat.add_assoc]
      _ = 4 * (n * n) + (2 * n) * (left + 1) := by rw [← hmul]
  have h4 : sl0 + (4 * (n * n) + 2 * n * (left + 1)) ≤
      sl0 + (4 * (n * n) + 6 * n) * k := by
    rw [← hdist]
    exact Nat.add_le_add_left hcoeff sl0
  rw [hpoly]
  exact Nat.le_trans h1 (by rw [h2, h3]; exact h4)

/-- After the root power on a planted strip, across is the strip and the base
    home is the planted peg. `left` hit tests still fit inside the holes left. -/
theorem search_ready_at (b0 : Ecbs.Board) (t : Spec.Tier) (holesLeft : Nat)
    (hp : PlantAt b0 t holesLeft)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj0 : 0 < j) (hj : j < t.n) (hn3 : 3 ≤ t.n)
    (mv0 sl0 c0 : Nat)
    (hmv0 : b0.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv0)
    (hsl0 : b0.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl0)
    (hc0 : b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t))
    (left : Nat) (hleft : 0 < left) (hleftH : left ≤ holesLeft) :
    ∃ b',
      (do
          let b ← (do
            let b ← (do
              let b ← (do
                let b ← (do
                  let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
                  let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
                  let b ← Ecbs.put b0 Ecbs.base_across x
                  Ecbs.curve_side b Ecbs.base_across Ecbs.bottom)
                let b ← Ecbs.mul b Ecbs.gap Ecbs.bottom Ecbs.bottom true false false
                Ecbs.settle b)
              Ecbs.white0 b Ecbs.up)
            let strip ← emittedStrip t.n
            let b ← Ecbs.put b Ecbs.across strip
            pure ({ b with sudo_5Board_9marker_on := true }))
          powRun b (rootDigits t.n)) = .ok b' ∧
        SearchAt b' t (basisPeg t.n j) (rootY t.n t.k t.benchlen (basisPeg t.n j))
          (curveSide t.n t.k t.benchlen (basisPeg t.n j))
          (fieldMul t.n t.k t.benchlen
            (curveSide t.n t.k t.benchlen (basisPeg t.n j))
            (curveSide t.n t.k t.benchlen (basisPeg t.n j)))
          (rootStrip t.n) (basisPeg t.n j) left := by
  obtain ⟨bS, o0, o1, hstrip, s⟩ :=
    search_strip_at b0 t holesLeft hp hOk hsh sat j hj0 hj mv0 sl0 c0 hmv0 hsl0 hc0
  rcases hp.moves with ⟨mvP, hmvP, hfitM⟩
  have hmvSame : mvP = mv0 := Int.ofNat.inj (hmvP.symm.trans hmv0)
  have hmvB : FitsLen (mv0 + perHole t.n t.benchlen * holesLeft) := by
    simpa [hmvSame] using hfitM
  rcases hp.slides with ⟨slP, hslP, hfitS⟩
  have hslSame : slP = sl0 := Int.ofNat.inj (hslP.symm.trans hsl0)
  have hslB : FitsLen (sl0 + perSlide t.n * holesLeft) := by
    simpa [hslSame] using hfitS
  rcases hp.ctrl with ⟨cP, hcP, hfitC⟩
  have hcSame : cP = c0 + tierR t := Int.ofNat.inj (hcP.symm.trans hc0)
  have hcB : FitsLen (c0 + tierR t + perCtrl t.n * holesLeft) := by
    simpa [hcSame, Nat.add_assoc] using hfitC
  obtain ⟨b', hpow, hPow, hax, haxD, hbx, hbxD, hmvE, hslE, hcE, hopE⟩ :=
    pow_from_strip_at bS t j mv0 sl0 c0 o0 o1 holesLeft s hOk hsh sat hn3
      hp.holesPos hmvB hslB hcB
  rcases hmvE with ⟨mv, hmv, hmvLe⟩
  have hM : ∀ moves, b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves →
      FitsLen (moves + searchMove t.n t.benchlen * left) := by
    intro moves hmoves
    have hsame : moves = mv := Int.ofNat.inj (hmoves.symm.trans hmv)
    rw [hsame]
    exact FitsLen.of_le hmvB
      (ready_move mv0 mv t.n t.benchlen holesLeft left hp.holesPos hleftH hmvLe)
  refine ⟨b', ?_, ?_⟩
  · rw [hstrip, ok_bind]
    exact hpow
  · exact search_of_pow b' t (basisPeg t.n j) (rootStrip t.n) (basisPeg t.n j) left hPow
      (basisPeg_length t.n j) hax haxD (strip_len t.n (two_le t.n hn3))
      hbx hbxD (basisPeg_length t.n j) hleft hM
      (by
        intro slides hsl0b
        rcases hslE with ⟨sl, hsl, hslLe⟩
        have hsame : slides = sl := Int.ofNat.inj (hsl0b.symm.trans hsl)
        rw [hsame]
        exact FitsLen.of_le hslB
          (by simpa [searchSlide, powSlide, perSlide] using
            ready_slide sl0 sl t.n holesLeft left hOk.n_pos hp.holesPos hleftH hslLe))
      (by
        intro c hc
        rcases hcE with ⟨ctrl, hctrl, hctrlLe⟩
        have hsame : c = ctrl := Int.ofNat.inj (hc.symm.trans hctrl)
        rw [hsame]
        exact FitsLen.of_le hcB
          (by simpa [Nat.add_assoc] using
            ready_ctrl (c0 + tierR t) ctrl t.n holesLeft left hp.holesPos hleftH hctrlLe))
      (by
        intro c hc
        rcases hopE with ⟨cOp, hop, hopLe⟩
        have hslot : some (Int.ofNat c) = some (Int.ofNat cOp) := hc.symm.trans hop
        have hsame : c = cOp := by
          injection hslot with hEq
          exact Int.ofNat.inj hEq
        rw [hsame]
        exact FitsLen.of_le s.opsRoom
          (ready_op o0 cOp t.n holesLeft left hOk.n_pos hp.holesPos hleftH hopLe))

/-- One planted hole, after the root power. A hit stops; a miss is the next hole. -/
theorem search_plant_step (t : Spec.Tier) (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (j : Nat) (hj0 : 0 < j) (hj : j < t.n) (hn3 : 3 ≤ t.n)
    (left : Nat) (hleft : 0 < left) (hleftN : left ≤ t.n) :
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
        ((∃ bH, searchCheck b' = .ok (true, bH) ∧
            HitAt bH t (basisPeg t.n j) (rootStrip t.n) (basisPeg t.n j) ∧
            rootHit t.n t.k t.benchlen (basisPeg t.n j) = true ∧
            searchRoot t.n t.k t.benchlen left j =
              some (basisPeg t.n j, rootY t.n t.k t.benchlen (basisPeg t.n j))) ∨
          (∃ bC bM, searchCheck b' = .ok (false, bC) ∧
            searchMiss bC = .ok bM ∧ MissAt bM ∧
            rootHit t.n t.k t.benchlen (basisPeg t.n j) = false ∧
            searchRoot t.n t.k t.benchlen left j =
              searchRoot t.n t.k t.benchlen (left - 1) (j + 1))) := by
  obtain ⟨b', hdo, hAt⟩ := search_ready t hOk hsh sat j hj0 hj hn3 left hleft hleftN
  refine ⟨b', hdo, ?_⟩
  exact search_hole b' t j
    (fieldMul t.n t.k t.benchlen
      (curveSide t.n t.k t.benchlen (basisPeg t.n j))
      (curveSide t.n t.k t.benchlen (basisPeg t.n j)))
    (rootStrip t.n) (basisPeg t.n j) left hAt hj

end EcbsLink2.Link2
