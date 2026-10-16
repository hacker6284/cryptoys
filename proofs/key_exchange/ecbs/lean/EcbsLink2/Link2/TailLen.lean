/-
  What the rung tail does to the tally length. A final rung keeps it. A non-final
  rung doubles it, and a non-final red rung adds one. That is `tallyAfter`.
  Cube and mul, bench off, return the named boards, which do not write the length.
-/
import EcbsLink2.Link2.RungBody

namespace EcbsLink2.Link2

open MegaDreifach.Link2

theorem tally_note_len (b b' : Ecbs.Board) (h : Ecbs.tally_note b = .ok b') :
    b'.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len := by
  unfold Ecbs.tally_note at h
  dsimp only at h
  by_cases hc :
      decide (b.sudo_5Board_9tally_len > b.sudo_5Board_4cost.sudo_5Costs_9tally_max) = true
  · rw [if_pos hc, pure_eq_ok] at h
    cases h
    rfl
  · rw [if_neg hc, pure_eq_ok] at h
    cases h
    rfl

theorem cubeOffBoard_tally_len (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) :
    (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome).sudo_5Board_9tally_len =
      b.sudo_5Board_9tally_len := rfl

theorem cubeLiveBoard_tally_len (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (bud : Budget b 1)
    (hin : HomeIn b src) :
    (cubeLiveBoard b dst src xs bud hin).sudo_5Board_9tally_len =
      b.sudo_5Board_9tally_len := by
  simp [cubeLiveBoard, cubeOffBoard, settleBoard]
  split <;> rfl

theorem cube_off_len (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (h : Ecbs.cube b (dst : Int) (src : Int) =
      .ok (cubeOffBoard b dst src xs n k moves hole bench peak peakS cOps hops hF hHome))
    (b' : Ecbs.Board) (hb : Ecbs.cube b (dst : Int) (src : Int) = .ok b') :
    b'.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len := by
  rw [h] at hb
  cases hb
  rfl

theorem mul_no_len (b : Ecbs.Board) (dst second : Nat) (first : Int) (xs ys : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size)
    (h : Ecbs.mul b (dst : Int) first (second : Int) false false false =
      .ok (mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS))
    (b' : Ecbs.Board)
    (hb : Ecbs.mul b (dst : Int) first (second : Int) false false false = .ok b') :
    b'.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len := by
  rw [h] at hb
  cases hb
  rfl

theorem mulNoOffBoard_tally_len (b : Ecbs.Board) (dst second : Nat) (xs ys : List Nat)
    (n k moves hole bench peak peakS cOps : Nat)
    (hops : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hS : second < b.sudo_5Board_4held.size)
    (hHomeS : second < b.sudo_5Board_4home.size) :
    (mulNoOffBoard b dst second xs ys n k moves hole bench peak peakS cOps hops hS hHomeS).sudo_5Board_9tally_len =
      b.sudo_5Board_9tally_len := rfl

theorem beq_rung_false (rung : Nat) (hr : rung ≠ 2) :
    SudoRt.SEq.beq (rung : Int) (2 : Int) = false := by
  rw [sEq_int, ← ofNat_eq_natCast rung, show (2 : Int) = Int.ofNat 2 from rfl]
  rw [decide_eq_false_iff_not]
  intro hEq
  exact hr (Int.ofNat.inj hEq)

theorem beq_rung_true (rung : Nat) (hr : rung = 2) :
    SudoRt.SEq.beq (rung : Int) (2 : Int) = true := by
  rw [sEq_int, ← ofNat_eq_natCast rung, show (2 : Int) = Int.ofNat 2 from rfl, hr]
  exact decide_eq_true rfl

/-- A final white rung's tail is the board it was given. -/
theorem rungNest_final_white (b : Ecbs.Board) (rung : Nat) (x : Int) (hr : rung ≠ 2) :
    rungNest (rung : Int) x true b = pure b := by
  unfold rungNest
  simp only [Bool.not_true, if_false, beq_rung_false rung hr, Bool.false_eq_true, if_false]

theorem rungNest_final_white_len (b b' : Ecbs.Board) (rung : Nat) (x : Int) (m : Nat)
    (hr : rung ≠ 2) (hlen : b.sudo_5Board_9tally_len = Int.ofNat m)
    (h : rungNest (rung : Int) x true b = .ok b') :
    b'.sudo_5Board_9tally_len = Int.ofNat (tallyAfter m rung true) := by
  rw [rungNest_final_white b rung x hr, pure_eq_ok] at h
  cases h
  simpa [tallyAfter, hr] using hlen

/-- A non-final white rung's tail is `tally_double`. -/
theorem rungNest_open_white (b : Ecbs.Board) (rung : Nat) (x : Int) (hr : rung ≠ 2) :
    rungNest (rung : Int) x false b = Ecbs.tally_double b := by
  unfold rungNest
  simp only [Bool.not_false, if_true, beq_rung_false rung hr, Bool.false_eq_true, if_false]
  exact except_bind_pure _

theorem tally_double_len (b : Ecbs.Board) (xs : List Nat)
    (t0 m c0 high control tmax : Nat)
    (hm : 0 < m)
    (hLen : b.sudo_5Board_9tally_len = (m : Int))
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed xs)
    (hRoom : t0 + 2 * m ≤ xs.length)
    (hRed : ∀ j (hj : j < m), xs[t0 + j]'(by omega) = 2)
    (hZero : ∀ k (hk : k < m), xs[t0 + m + k]'(by omega) = 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hTop : high = t0 + m - 1)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (c0 : Int))
    (hIn : t0 + 2 * m ≤ control)
    (hfit : FitsLen (t0 + 2 * m))
    (hfitC : FitsLen (c0 + 2 * m))
    (hfitM : FitsLen (2 * m))
    (hMax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hNote : tmax < 2 * m)
    (b' : Ecbs.Board) (h : Ecbs.tally_double b = .ok b') :
    b'.sudo_5Board_9tally_len = Int.ofNat (2 * m) := by
  have href := tally_double_refines b xs t0 m c0 high control tmax hm hLen hT0 hRow hRoom
    hRed hZero hCtrlN hHigh (Nat.le_of_eq hTop.symm) hCtrl hIn hfit hfitC hfitM hMax hNote
  rw [href] at h
  cases h
  rfl

theorem rungNest_open_white_len (b : Ecbs.Board) (xs : List Nat)
    (rung : Nat) (x : Int) (t0 m c0 high control tmax : Nat)
    (hr : rung ≠ 2) (hm : 0 < m)
    (hLen : b.sudo_5Board_9tally_len = (m : Int))
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hRow : b.sudo_5Board_3row = embed xs)
    (hRoom : t0 + 2 * m ≤ xs.length)
    (hRed : ∀ j (hj : j < m), xs[t0 + j]'(by omega) = 2)
    (hZero : ∀ k (hk : k < m), xs[t0 + m + k]'(by omega) = 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hTop : high = t0 + m - 1)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (c0 : Int))
    (hIn : t0 + 2 * m ≤ control)
    (hfit : FitsLen (t0 + 2 * m))
    (hfitC : FitsLen (c0 + 2 * m))
    (hfitM : FitsLen (2 * m))
    (hMax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hNote : tmax < 2 * m)
    (b' : Ecbs.Board) (h : rungNest (rung : Int) x false b = .ok b') :
    b'.sudo_5Board_9tally_len = Int.ofNat (tallyAfter m rung false) := by
  rw [rungNest_open_white b rung x hr] at h
  have hlen := tally_double_len b xs t0 m c0 high control tmax hm hLen hT0 hRow hRoom
    hRed hZero hCtrlN hHigh hTop hCtrl hIn hfit hfitC hfitM hMax hNote b' h
  simpa [tallyAfter, hr] using hlen

/-- A non-final red rung's tail is double, cube onto the gap, mul by `x`, one peg. -/
theorem rungNest_open_red (b : Ecbs.Board) (rung : Nat) (x : Int) (hr : rung = 2) :
    rungNest (rung : Int) x false b =
      (do
        let b ← Ecbs.tally_double b
        let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
        let b ← Ecbs.mul b ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false
        Ecbs.tally_add_one b) := by
  unfold rungNest
  simp only [Bool.not_false, if_true, beq_rung_true rung hr]

theorem tally_add_one_len (b : Ecbs.Board) (t0 len high control ctrl tmax : Nat)
    (hLen : b.sudo_5Board_9tally_len = (len : Int))
    (hT0 : b.sudo_5Board_6tally0 = (t0 : Int))
    (hrow : t0 + len < b.sudo_5Board_3row.size)
    (hZero : b.sudo_5Board_3row[t0 + len] = 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hic : t0 + len < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hgt : high < t0 + len)
    (hFitI : FitsLen (t0 + len))
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFitC : FitsLen (ctrl + 1))
    (hFitL : FitsLen (len + 1))
    (hMax : b.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int))
    (hNote : tmax < len + 1)
    (b' : Ecbs.Board) (h : Ecbs.tally_add_one b = .ok b') :
    b'.sudo_5Board_9tally_len = Int.ofNat (len + 1) := by
  have href := tally_add_one_raise b t0 len high control ctrl tmax hLen hT0 hrow hZero
    hCtrlN hic hHigh hgt hFitI hCtrl hFitC hFitL hMax hNote
  rw [href] at h
  cases h
  rfl

/-- Cube and mul between the double and the extra peg do not write the length,
    so a non-final red tail leaves `2 · m + 1`. -/
theorem rungNest_open_red_len
    (b bD bC bM b' : Ecbs.Board) (rung : Nat) (x : Int) (m : Nat)
    (hr : rung = 2)
    (hD : Ecbs.tally_double b = .ok bD)
    (hlenD : bD.sudo_5Board_9tally_len = Int.ofNat (2 * m))
    (hC : Ecbs.cube bD ((6 : Nat) : Int) ((5 : Nat) : Int) = .ok bC)
    (hlenC : bC.sudo_5Board_9tally_len = bD.sudo_5Board_9tally_len)
    (hM : Ecbs.mul bC ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false = .ok bM)
    (hlenM : bM.sudo_5Board_9tally_len = bC.sudo_5Board_9tally_len)
    (hA : Ecbs.tally_add_one bM = .ok b')
    (hlenA : b'.sudo_5Board_9tally_len = Int.ofNat (2 * m + 1))
    (h : rungNest (rung : Int) x false b = .ok b') :
    b'.sudo_5Board_9tally_len = Int.ofNat (tallyAfter m rung false) := by
  have hmid : bM.sudo_5Board_9tally_len = Int.ofNat (2 * m) :=
    hlenM.trans (hlenC.trans hlenD)
  rw [rungNest_open_red b rung x hr, hD, ok_bind, hC, ok_bind, hM, ok_bind, hA] at h
  cases h
  simpa [tallyAfter, hr, hmid] using hlenA

end EcbsLink2.Link2
