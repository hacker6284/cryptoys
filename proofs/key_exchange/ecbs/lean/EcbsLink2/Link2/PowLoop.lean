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
  homeWide : powSpare < b.sudo_5Board_4home.size
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

/-- Two arrays that agree off one index, and both store something there, have one length. -/
private theorem size_of_slot {α : Type} (a b : Array α) (i : Nat) (v w : α)
    (ha : a[i]? = some v) (hb : b[i]? = some w)
    (hk : ∀ j, j ≠ i → a[j]? = b[j]?) : a.size = b.size := by
  have hai : i < a.size := some_idx a i v ha
  have hbi : i < b.size := some_idx b i w hb
  have hle : a.size ≤ b.size := by
    have hnone : a[b.size]? = none := by
      rw [hk b.size (by omega : b.size ≠ i)]
      rw [Array.getElem?_eq_none_iff]
      exact Nat.le_refl _
    exact Array.getElem?_eq_none_iff.mp hnone
  have hge : b.size ≤ a.size := by
    have hnone : b[a.size]? = none := by
      rw [← hk a.size (by omega : a.size ≠ i)]
      rw [Array.getElem?_eq_none_iff]
      exact Nat.le_refl _
    exact Array.getElem?_eq_none_iff.mp hnone
  omega

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

theorem fit_le_move (moves n bench k new : Nat)
    (h : FitsLen (moves + powMove n bench * (k + 1)))
    (hs : new ≤ moves + powMove n bench) :
    FitsLen new :=
  (room_abs moves new (powMove n bench) k h hs).1

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

private theorem two_peg_slide (n peg : Nat) (hp : peg ≤ n) : 2 * peg ≤ powSlide n := by
  unfold powSlide
  have h2 : 2 * peg ≤ 2 * n := Nat.mul_le_mul_left _ hp
  omega

/-- Moves, slides, control, and ops slot 0 grow by at most these amounts. -/
structure CounterLe (b b' : Ecbs.Board) (mvAdd slAdd cAdd opAdd : Nat) : Prop where
  moves : ∀ mv, b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv →
    ∃ mv', b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv' ∧ mv' ≤ mv + mvAdd
  slides : ∀ sl, b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl →
    ∃ sl', b'.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl' ∧ sl' ≤ sl + slAdd
  ctrl : ∀ c, b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c →
    ∃ c', b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c' ∧
      c ≤ c' ∧ c' ≤ c + cAdd
  ops0 : ∀ c0, b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) →
    ∃ c0', b'.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0') ∧
      c0' ≤ c0 + opAdd
  ops1 : ∀ c1, b.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (Int.ofNat c1) →
    ∃ c1', b'.sudo_5Board_4cost.sudo_5Costs_3ops[1]? = some (Int.ofNat c1') ∧
      c1' ≤ c1 + opAdd

private theorem chain_le (x y z a b : Nat) (h1 : y ≤ x + a) (h2 : z ≤ y + b) :
    z ≤ x + (a + b) := by omega

private theorem add_le_add_left_le (a s p : Nat) (h : s ≤ p) : a + s ≤ a + p :=
  Nat.add_le_add_left h a

private theorem ctrl_step_zero (c : Nat) : c + 2 ≤ c + powCtrl := by
  unfold powCtrl
  omega

private theorem ctrl_step_live (c : Nat) : c + 4 ≤ c + powCtrl := by
  unfold powCtrl
  omega

private theorem mul_step (p k : Nat) : p + p * k = p * (k + 1) := by
  rw [Nat.mul_succ, Nat.add_comm]

private theorem one_step (k : Nat) : 1 + k = k + 1 := by omega

theorem counterLe_refl (b : Ecbs.Board) : CounterLe b b 0 0 0 0 where
  moves := by
    intro mv h
    exact ⟨mv, h, Nat.le_refl _⟩
  slides := by
    intro sl h
    exact ⟨sl, h, Nat.le_refl _⟩
  ctrl := by
    intro c h
    exact ⟨c, h, Nat.le_refl _, Nat.le_refl _⟩
  ops0 := by
    intro c0 h
    exact ⟨c0, h, Nat.le_refl _⟩
  ops1 := by
    intro c1 h
    exact ⟨c1, h, Nat.le_refl _⟩

theorem counterLe_trans {b b1 b' : Ecbs.Board} {m1 s1 c1 o1 m2 s2 c2 o2 : Nat}
    (h1 : CounterLe b b1 m1 s1 c1 o1) (h2 : CounterLe b1 b' m2 s2 c2 o2) :
    CounterLe b b' (m1 + m2) (s1 + s2) (c1 + c2) (o1 + o2) where
  moves := by
    intro mv hmv
    obtain ⟨mv1, hmv1, hle1⟩ := h1.moves mv hmv
    obtain ⟨mv', hmv', hle2⟩ := h2.moves mv1 hmv1
    exact ⟨mv', hmv', chain_le mv mv1 mv' m1 m2 hle1 hle2⟩
  slides := by
    intro sl hsl
    obtain ⟨sl1, hsl1, hle1⟩ := h1.slides sl hsl
    obtain ⟨sl', hsl', hle2⟩ := h2.slides sl1 hsl1
    exact ⟨sl', hsl', chain_le sl sl1 sl' s1 s2 hle1 hle2⟩
  ctrl := by
    intro c hc
    obtain ⟨c1', hc1, hge1, hle1⟩ := h1.ctrl c hc
    obtain ⟨c', hc', hge2, hle2⟩ := h2.ctrl c1' hc1
    exact ⟨c', hc', Nat.le_trans hge1 hge2, chain_le c c1' c' c1 c2 hle1 hle2⟩
  ops0 := by
    intro c0 hc0
    obtain ⟨c01, hc01, hle1⟩ := h1.ops0 c0 hc0
    obtain ⟨c0', hc0', hle2⟩ := h2.ops0 c01 hc01
    exact ⟨c0', hc0', chain_le c0 c01 c0' o1 o2 hle1 hle2⟩
  ops1 := by
    intro c1a hc1
    obtain ⟨c11, hc11, hle1⟩ := h1.ops1 c1a hc1
    obtain ⟨c1', hc1', hle2⟩ := h2.ops1 c11 hc11
    exact ⟨c1', hc1', chain_le c1a c11 c1' o1 o2 hle1 hle2⟩

theorem counterLe_pow {b b1 b' : Ecbs.Board} (n bench k : Nat)
    (h1 : CounterLe b b1 (powMove n bench) (powSlide n) powCtrl 1)
    (h2 : CounterLe b1 b' (powMove n bench * k) (powSlide n * k) (powCtrl * k) k) :
    CounterLe b b' (powMove n bench * (k + 1)) (powSlide n * (k + 1))
      (powCtrl * (k + 1)) (k + 1) := by
  have h := counterLe_trans h1 h2
  have hm : powMove n bench + powMove n bench * k = powMove n bench * (k + 1) := mul_step _ _
  have hs : powSlide n + powSlide n * k = powSlide n * (k + 1) := mul_step _ _
  have hcEq : powCtrl + powCtrl * k = powCtrl * (k + 1) := mul_step _ _
  have ho : 1 + k = k + 1 := one_step k
  refine
    { moves := by
        intro mv hmv
        obtain ⟨mv', hmv', hle⟩ := h.moves mv hmv
        rw [hm] at hle
        exact ⟨mv', hmv', hle⟩
      slides := by
        intro sl hsl
        obtain ⟨sl', hsl', hle⟩ := h.slides sl hsl
        rw [hs] at hle
        exact ⟨sl', hsl', hle⟩
      ctrl := by
        intro c hc
        obtain ⟨c', hc', hge, hle⟩ := h.ctrl c hc
        rw [hcEq] at hle
        exact ⟨c', hc', hge, hle⟩
      ops0 := by
        intro c0 hc0
        obtain ⟨c0', hc0', hle⟩ := h.ops0 c0 hc0
        rw [ho] at hle
        exact ⟨c0', hc0', hle⟩
      ops1 := by
        intro c1a hc1
        obtain ⟨c1', hc1', hle⟩ := h.ops1 c1a hc1
        rw [ho] at hle
        exact ⟨c1', hc1', hle⟩ }

/-- Digit 0. The up home becomes the cube, which is `powStep` on digit 0,
    and one unit of each budget is spent. -/
theorem pow_zero_at (b : Ecbs.Board) (t : Spec.Tier) (rhs acc : List Nat) (ds : List Nat)
    (h : PowAt b t rhs acc (0 :: ds)) :
    ∃ b', powDigitRun b 0 powBottom = .ok b' ∧
      PowAt b' t rhs (powStep t.n t.k t.benchlen rhs acc 0) ds ∧
      (∀ i, i ≠ powUp → i ≠ powSpare →
        b'.sudo_5Board_4home[i]? = b.sudo_5Board_4home[i]? ∧
        b'.sudo_5Board_4held[i]? = b.sudo_5Board_4held[i]?) ∧
      CounterLe b b' (powMove t.n t.benchlen) (powSlide t.n) powCtrl 1 ∧
      ∃ c, b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c ∧
        b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c + 2) := by
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
  refine ⟨bS, ?_, ?_, ?_, ?_, ?_⟩
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
        homeWide := by
          have hszHome := size_of_slot bS.sudo_5Board_4home b.sudo_5Board_4home powUp
              (embed (powStep t.n t.k t.benchlen rhs acc 0)) (embed acc) hhome h.upHome hhomeK
          rw [hszHome]
          exact h.homeWide
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
  · intro i hu _
    exact ⟨hhomeK i hu, hheldK i hu⟩
  · refine
      { moves := ?_
        slides := ?_
        ctrl := ?_
        ops0 := ?_
        ops1 := ?_ }
    · intro mv0 hmv0
      have hsame : mv0 = moves := Int.ofNat.inj (hmv0.symm.trans hmv)
      refine ⟨cubeMoves moves acc t.n t.k t.benchlen +
          2 * pegCount (fieldCube t.n t.k t.benchlen acc), hmvS, ?_⟩
      simpa [hsame] using zero_delta_le t.n t.benchlen moves t.k acc
    · intro sl0 hsl0
      have hsame : sl0 = slides := Int.ofNat.inj (hsl0.symm.trans hsl)
      refine ⟨slides + 2 * pegCount (fieldCube t.n t.k t.benchlen acc), hslS, ?_⟩
      simpa [hsame] using
        add_le_add_left_le slides _ _
          (two_peg_slide t.n _ (cube_peg_le t.n t.k t.benchlen acc))
    · intro cIn hcIn
      have hsame : cIn = ctrl := Int.ofNat.inj (hcIn.symm.trans hc)
      refine ⟨ctrl + 2, hctrl, ?_, ?_⟩
      · rw [hsame]
        exact Nat.le_add_right _ _
      · simpa [hsame] using ctrl_step_zero ctrl
    · intro c0in hc0in
      have hslot : some (Int.ofNat c0in) = some (Int.ofNat c0) := hc0in.symm.trans hop0
      have hsame : c0in = c0 := by
        injection hslot with hEq
        exact Int.ofNat.inj hEq
      refine ⟨c0, (hopK 0 (by decide)).trans hop0, ?_⟩
      rw [hsame]
      exact Nat.le_succ c0
    · intro c1in hc1in
      have hslot : some (Int.ofNat c1in) = some (Int.ofNat c1) := hc1in.symm.trans hop1
      have hsame : c1in = c1 := by
        injection hslot with hEq
        exact Int.ofNat.inj hEq
      refine ⟨c1 + 1, hop1S, ?_⟩
      rw [hsame]
      exact Nat.le_refl _
  · exact ⟨ctrl, hc, hctrl⟩

/-- Moves one live root digit adds: the cube, the copy, the schoolbook, and the settles. -/
def liveMove (n k bench moves : Nat) (acc factor : List Nat) : Nat :=
  cubeMoves moves acc n k bench + pegCount factor +
    2 * pegCount (fieldCube n k bench acc) +
    schoolMoves (fieldCube n k bench acc) factor n n +
    foldCharge n (n - k) (school n (fieldCube n k bench acc) factor
      (List.replicate bench 0) false) +
    pegCount (fieldCube n k bench acc) +
    2 * pegCount (fieldMul n k bench (fieldCube n k bench acc) factor)

/-- Slides one live root digit adds: the cube settle and the product settle. -/
def liveSlide (n k bench : Nat) (acc factor : List Nat) : Nat :=
  2 * pegCount (fieldCube n k bench acc) +
    2 * pegCount (fieldMul n k bench (fieldCube n k bench acc) factor)

theorem pow_ge_span2 (n bench : Nat) : 2 * (n - 1) ≤ powMove n bench := by
  unfold powMove
  omega

theorem prod_peg_le (n k bench : Nat) (cube factor : List Nat) (hn : n ≤ bench) :
    pegCount (fieldMul n k bench cube factor) ≤ n := by
  have hlen := fieldMul_length n k bench cube factor hn
  exact Nat.le_trans (pegCount_le _) (Nat.le_of_eq hlen)

private theorem fac_peg_le (n : Nat) (factor : List Nat) (hf : factor.length = n) :
    pegCount factor ≤ n :=
  Nat.le_trans (pegCount_le _) (Nat.le_of_eq hf)

theorem live_copy_le (n k bench moves : Nat) (acc factor : List Nat)
    (hf : factor.length = n) :
    cubeMoves moves acc n k bench + pegCount factor ≤ moves + powMove n bench := by
  have hc := cubeMoves_le moves acc n k bench
  have hfac := fac_peg_le n factor hf
  unfold powMove
  omega

theorem live_mid_le (n k bench moves : Nat) (acc factor : List Nat)
    (hf : factor.length = n) :
    cubeMoves moves acc n k bench + pegCount factor +
      2 * pegCount (fieldCube n k bench acc) ≤ moves + powMove n bench := by
  have hc := cubeMoves_le moves acc n k bench
  have hfac := fac_peg_le n factor hf
  have hcube := cube_peg_le n k bench acc
  unfold powMove
  omega

theorem live_fold_le (n k bench moves : Nat) (acc factor : List Nat)
    (hf : factor.length = n) :
    cubeMoves moves acc n k bench + pegCount factor +
      2 * pegCount (fieldCube n k bench acc) + n * (n + 1) + 3 * (bench - n) ≤
        moves + powMove n bench := by
  have hc := cubeMoves_le moves acc n k bench
  have hfac := fac_peg_le n factor hf
  have hcube := cube_peg_le n k bench acc
  have hsq : n * (n + 1) = n * n + n := by rw [Nat.mul_succ]
  unfold powMove
  rw [hsq]
  omega

theorem live_clear_le (n k bench moves : Nat) (acc factor : List Nat)
    (hn : n ≤ bench) (hf : factor.length = n) :
    cubeMoves moves acc n k bench + pegCount factor +
      2 * pegCount (fieldCube n k bench acc) +
      schoolMoves (fieldCube n k bench acc) factor n n +
      foldCharge n (n - k) (school n (fieldCube n k bench acc) factor
        (List.replicate bench 0) false) +
      pegCount (fieldCube n k bench acc) ≤ moves + powMove n bench := by
  have hc := cubeMoves_le moves acc n k bench
  have hfac := fac_peg_le n factor hf
  have hcube := cube_peg_le n k bench acc
  have hsch := schoolMoves_bound (fieldCube n k bench acc) factor n
  have hfold := foldCharge_bound n (n - k)
      (school n (fieldCube n k bench acc) factor (List.replicate bench 0) false)
  have hlenS : (school n (fieldCube n k bench acc) factor
      (List.replicate bench 0) false).length = bench := by
    simpa [List.length_replicate] using
      school_length (fieldCube n k bench acc) factor (List.replicate bench 0) false n
  rw [hlenS] at hfold
  have hsq : n * (n + 1) = n * n + n := by rw [Nat.mul_succ]
  rw [hsq] at hsch
  unfold powMove
  omega

theorem live_delta_le (n k bench moves : Nat) (acc factor : List Nat)
    (hn : n ≤ bench) (hf : factor.length = n) :
    liveMove n k bench moves acc factor ≤ moves + powMove n bench := by
  have hc := cubeMoves_le moves acc n k bench
  have hfac := fac_peg_le n factor hf
  have hcube := cube_peg_le n k bench acc
  have hprod := prod_peg_le n k bench (fieldCube n k bench acc) factor hn
  have hsch := schoolMoves_bound (fieldCube n k bench acc) factor n
  have hfold := foldCharge_bound n (n - k)
      (school n (fieldCube n k bench acc) factor (List.replicate bench 0) false)
  have hlenS : (school n (fieldCube n k bench acc) factor
      (List.replicate bench 0) false).length = bench := by
    simpa [List.length_replicate] using
      school_length (fieldCube n k bench acc) factor (List.replicate bench 0) false n
  rw [hlenS] at hfold
  have hsq : n * (n + 1) = n * n + n := by rw [Nat.mul_succ]
  rw [hsq] at hsch
  unfold liveMove powMove
  omega

theorem cube_slide_le (n k bench : Nat) (acc : List Nat) :
    2 * pegCount (fieldCube n k bench acc) ≤ powSlide n := by
  have hcube := cube_peg_le n k bench acc
  unfold powSlide
  omega

theorem live_slide_le (n k bench : Nat) (acc factor : List Nat) (hn : n ≤ bench) :
    liveSlide n k bench acc factor ≤ powSlide n := by
  have hcube := cube_peg_le n k bench acc
  have hprod := prod_peg_le n k bench (fieldCube n k bench acc) factor hn
  unfold liveSlide powSlide
  omega

theorem powStep_len (n k bench : Nat) (rhs acc : List Nat) (d : Nat) (hn : n ≤ bench) :
    (powStep n k bench rhs acc d).length = n := by
  rw [powStep_branch]
  by_cases h2 : d = 2
  · simpa [h2] using fieldMul_length n k bench (fieldCube n k bench acc)
      (fieldMul n k bench rhs rhs) hn
  · by_cases h1 : d = 1
    · simpa [h2, h1] using fieldMul_length n k bench (fieldCube n k bench acc) rhs hn
    · simp [h2, h1]
      rw [← cube_off_prefix n k bench acc, List.length_take]
      have hsch : (combStrip n bench acc).length = bench := combStrip_length _ _ _
      have hlane := laneFold_length n (n - k) (combStrip n bench acc)
        (by rw [hsch]; exact hn)
      rw [hlane, hsch, Nat.min_eq_left hn]

/-- A red or white digit. The up home becomes `powStep`, and one unit of each
    budget is spent. `src` is the gap on red and the bottom on white. -/
theorem pow_live_at (b : Ecbs.Board) (t : Spec.Tier) (rhs acc : List Nat)
    (d src : Nat) (factor : List Nat) (ds : List Nat)
    (h : PowAt b t rhs acc (d :: ds))
    (hd : (d = 2 ∧ factor = fieldMul t.n t.k t.benchlen rhs rhs) ∨
      (d = 1 ∧ factor = rhs))
    (hsrc : src = if d = 2 then powGap else powBottom)
    (hhome : b.sudo_5Board_4home[src]? = some (embed factor))
    (hheld : b.sudo_5Board_4held[src]? = some true)
    (hfacLen : factor.length = t.n) :
    ∃ b', powDigitRun b d src = .ok b' ∧
      PowAt b' t rhs (powStep t.n t.k t.benchlen rhs acc d) ds ∧
      (∀ i, i ≠ powUp → i ≠ powSpare →
        b'.sudo_5Board_4home[i]? = b.sudo_5Board_4home[i]? ∧
        b'.sudo_5Board_4held[i]? = b.sudo_5Board_4held[i]?) ∧
      CounterLe b b' (powMove t.n t.benchlen) (powSlide t.n) powCtrl 1 ∧
      ∃ c, b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c ∧
        b'.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c + 4) := by
  obtain ⟨moves, slides, ctrl, mark, mx, pk, ps, hole, c0, c1, hmv, hsl, hc, hm, hmark,
      hmx, hpk, hps, hhole, hsz, hop0, hop1, hfitM, hfitS, hfitC, hfit0, hfit1⟩ := h.pack
  have hlen : (d :: ds).length = ds.length + 1 := by simp
  have hn0 : 0 < t.n := h.nPos
  have hnb : t.n ≤ t.benchlen := mul_span_n t.n t.benchlen hn0 h.sat.mul_span
  have hspan3 : 3 * (t.n - 1) < t.benchlen :=
    cube_span_le t.n t.benchlen t.combgap h.sat.cube_span
  have hscript := script_one t h.shape
  have hmov : FitsLen (moves + powMove t.n t.benchlen * (ds.length + 1)) := by
    simpa [hlen] using hfitM
  have hslR : FitsLen (slides + powSlide t.n * (ds.length + 1)) := by
    simpa [hlen] using hfitS
  have hcR : FitsLen (ctrl + powCtrl * (ds.length + 1)) := by
    simpa [hlen] using hfitC
  have hUp : powUp < b.sudo_5Board_4home.size := some_idx _ _ _ h.upHome
  have hUpD : powUp < b.sudo_5Board_4held.size := some_idx _ _ _ h.upHeld
  have hSpare : powSpare < b.sudo_5Board_4held.size := some_idx _ _ _ h.spareOff
  have hHomeSpare : powSpare < b.sudo_5Board_4home.size := h.homeWide
  have h7 : 7 ≤ b.sudo_5Board_4held.size := by
    unfold powSpare at hSpare
    omega
  have hSrc : src < b.sudo_5Board_4held.size := some_idx _ _ _ hheld
  have hHomeSrc : src < b.sudo_5Board_4home.size := some_idx _ _ _ hhome
  have hsrcU : src ≠ powUp := by
    rcases hd with ⟨hd2, _⟩ | ⟨hd1, _⟩
    · rw [hsrc, if_pos hd2]; decide
    · have hne2 : ¬ d = 2 := by rw [hd1]; decide
      rw [hsrc, if_neg hne2]; decide
  have hsrcS : src ≠ powSpare := by
    rcases hd with ⟨hd2, _⟩ | ⟨hd1, _⟩
    · rw [hsrc, if_pos hd2]; decide
    · have hne2 : ¬ d = 2 := by rw [hd1]; decide
      rw [hsrc, if_neg hne2]; decide
  have hcubeT := fieldCube_trits t.n t.k t.benchlen acc h.accT hspan3 h.shape.k_le
  have hnew := live_delta_le t.n t.k t.benchlen moves acc factor hnb hfacLen
  have hmovePair := room_abs moves (liveMove t.n t.k t.benchlen moves acc factor)
      (powMove t.n t.benchlen) ds.length hmov hnew
  have hslidePair := room_slide slides (liveSlide t.n t.k t.benchlen acc factor)
      t.n ds.length hslR (live_slide_le t.n t.k t.benchlen acc factor hnb)
  have hlive := pow_live_seated b powUp powSpare src acc rhs factor d
      t.w t.h t.r t.n t.k moves slides hole t.benchlen pk ps c1 c0 t.combgap
      ctrl mx t.script mark
      h.markerOn h.benchOff hm hc hmx
      (by simpa [h.tier, embTier])
      (by omega : 0 < t.script) hscript
      (room_ctrl ctrl 1 ds.length hcR (by unfold powCtrl; decide)).1
      (room_ctrl ctrl 2 ds.length hcR (by unfold powCtrl; decide)).1
      (room_ctrl ctrl 4 ds.length hcR (by unfold powCtrl; decide)).1
      (by rw [hsz]; decide) (by
        have h1 : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [hsz]; decide
        rw [Array.getElem?_eq_getElem h1] at hop1
        injection hop1)
      (room_ops c1 ds.length (by simpa [hlen] using hfit1)).1
      (by rw [hsz]; decide) (by
        have h0 : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size := by rw [hsz]; decide
        rw [Array.getElem?_eq_getElem h0] at hop0
        injection hop0)
      (room_ops c0 ds.length (by simpa [hlen] using hfit0)).1
      hUpD hUp (some_get _ _ _ h.upHeld) (some_get _ _ _ h.upHome) h7
      (by simpa [ofNat_eq_natCast] using hps) (by simpa [ofNat_eq_natCast] using hpk)
      hSpare hHomeSpare (some_get _ _ _ h.spareOff)
      hSrc hHomeSrc (some_get _ _ _ hheld) (some_get _ _ _ hhome)
      (by decide) hsrcU hsrcS
      hn0 (by simpa [h.tier, embTier]) h.accLen hfacLen
      (fit_of_pow moves t.n t.benchlen ds.length t.n hmov (pow_ge_n _ _))
      (by simpa [ofNat_eq_natCast] using hmv) hsl
      (by simpa [h.tier, embTier]) (by simpa [h.tier, embTier])
      h.sat.cube_span h.sat.mul_span
      (fit_of_pow moves t.n t.benchlen ds.length (3 * (t.n - 1)) hmov (pow_ge_span _ _))
      (fit_of_pow moves t.n t.benchlen ds.length (2 * (t.n - 1)) hmov (pow_ge_span2 _ _))
      (fit_add_pow moves t.n t.benchlen ds.length (2 * t.n) hmov (pow_ge_two _ _))
      hhole h.accT hcubeT
      h.shape.w0 h.shape.h0 h.shape.rlt h.shape.r0 h.shape.n_eq h.shape.k_le h.shape.gap
      (by simpa [h.tier, embTier]) (by simpa [h.tier, embTier])
      (by simpa [h.tier, embTier]) (by simpa [h.tier, embTier])
      h.shape.small h.shape.n_small
      (fit_of_pow moves t.n t.benchlen ds.length t.benchlen hmov (pow_ge_bench _ _))
      (by simpa [Nat.add_assoc] using
        (fit_add_pow moves t.n t.benchlen ds.length (2 * t.n + 3 * (t.benchlen - t.n)) hmov
          (pow_ge_fold _ _)))
      (fit_le_move moves t.n t.benchlen ds.length
        (cubeMoves moves acc t.n t.k t.benchlen + pegCount factor) hmov
        (live_copy_le _ _ _ _ _ _ hfacLen))
      (fit_of_pow moves t.n t.benchlen ds.length
        (2 * pegCount (fieldCube t.n t.k t.benchlen acc)) hmov
        (pow_ge_two_peg _ _ _ (cube_peg_le _ _ _ _)))
      (fit_le_move moves t.n t.benchlen ds.length
        (cubeMoves moves acc t.n t.k t.benchlen + pegCount factor +
          2 * pegCount (fieldCube t.n t.k t.benchlen acc)) hmov
        (live_mid_le _ _ _ _ _ _ hfacLen))
      (room_slide slides (2 * pegCount (fieldCube t.n t.k t.benchlen acc)) t.n ds.length hslR
        (cube_slide_le _ _ _ _)).1
      (fit_le_move moves t.n t.benchlen ds.length
        (cubeMoves moves acc t.n t.k t.benchlen + pegCount factor +
          2 * pegCount (fieldCube t.n t.k t.benchlen acc) + t.n * (t.n + 1) +
          3 * (t.benchlen - t.n)) hmov
        (live_fold_le _ _ _ _ _ _ hfacLen))
      hd
      (fit_le_move moves t.n t.benchlen ds.length
        (cubeMoves moves acc t.n t.k t.benchlen + pegCount factor +
          2 * pegCount (fieldCube t.n t.k t.benchlen acc) +
          schoolMoves (fieldCube t.n t.k t.benchlen acc) factor t.n t.n +
          foldCharge t.n (t.n - t.k) (school t.n (fieldCube t.n t.k t.benchlen acc) factor
            (List.replicate t.benchlen 0) false) +
          pegCount (fieldCube t.n t.k t.benchlen acc)) hmov
        (live_clear_le _ _ _ _ _ _ hnb hfacLen))
      (fit_of_pow moves t.n t.benchlen ds.length
        (2 * pegCount (fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen acc) factor))
        hmov (pow_ge_two_peg _ _ _ (prod_peg_le _ _ _ _ _ hnb)))
      hmovePair.1
      (by simpa [liveSlide, Nat.add_assoc] using hslidePair.1)
  rcases hlive with ⟨bS, hrun, hhomeS, hoff, hheldS, hmarkS, hflag, hfacS, hctrlS, hmxS, hspS,
      hkeep, hholeS, hpsS, hpkS, htierS, hmvS, hslS, hszS, hop0S, hop1S, hopK, hszHome⟩
  have hpowLen := powStep_len t.n t.k t.benchlen rhs acc d hnb
  refine ⟨bS, ?_, ?_, ?_, ?_, ?_⟩
  · have hd0 : ¬ d = 0 := by
      rcases hd with ⟨hd2, _⟩ | ⟨hd1, _⟩
      · rw [hd2]; decide
      · rw [hd1]; decide
    unfold powDigitRun
    split
    · next hEq => exact (hd0 hEq).elim
    · simp only [powUp, powSpare]
      exact hrun
  · refine
      { tier := htierS.trans h.tier
        shape := h.shape
        sat := h.sat
        markerOn := hflag
        benchOff := hoff
        accLen := hpowLen
        rhsLen := h.rhsLen
        nPos := h.nPos
        accT := powStep_trits t.n t.k t.benchlen rhs acc d h.accT h.shape.k_le hspan3 hnb h.rhsLen
        rhsT := h.rhsT
        upHome := by simpa [powUp] using hhomeS
        upHeld := by simpa [powUp] using hheldS
        botHome := by
          have hbot := (hkeep powBottom (by decide) (by decide)).1
          simpa [powBottom] using hbot.trans h.botHome
        botHeld := by
          have hb := (hkeep powBottom (by decide) (by decide)).2
          simpa [powBottom] using hb.trans h.botHeld
        gapHome := by
          have hg := (hkeep powGap (by decide) (by decide)).1
          simpa [powGap] using hg.trans h.gapHome
        gapHeld := by
          have hg := (hkeep powGap (by decide) (by decide)).2
          simpa [powGap] using hg.trans h.gapHeld
        spareOff := by simpa [powSpare] using hspS
        homeWide := by
          rw [hszHome]
          exact h.homeWide
        pack := ?_ }
    rcases hholeS with ⟨hole', hhole'⟩
    rcases hpsS with ⟨ps', hps'⟩
    rcases hpkS with ⟨pk', hpk'⟩
    have hmvN : bS.sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat (liveMove t.n t.k t.benchlen moves acc factor) := by
      simpa [liveMove] using hmvS
    have hslN : bS.sudo_5Board_4cost.sudo_5Costs_6slides =
        Int.ofNat (slides + liveSlide t.n t.k t.benchlen acc factor) := by
      have heq : slides + 2 * pegCount (fieldCube t.n t.k t.benchlen acc) +
          2 * pegCount (fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen acc) factor) =
          slides + liveSlide t.n t.k t.benchlen acc factor := by
        rw [liveSlide, Nat.add_assoc]
      rw [← heq]
      exact hslS
    refine ⟨liveMove t.n t.k t.benchlen moves acc factor,
      slides + liveSlide t.n t.k t.benchlen acc factor, ctrl + 4, 1, max mx 2, pk', ps',
      hole', c0 + 1, c1 + 1,
      hmvN, hslN, hctrlS, hmarkS, by decide, hmxS, hpk', hps', hhole', ?_, hop0S, hop1S,
      hmovePair.2, hslidePair.2,
      (room_ctrl ctrl 4 ds.length hcR (by unfold powCtrl; decide)).2,
      (room_ops c0 ds.length (by simpa [hlen] using hfit0)).2,
      (room_ops c1 ds.length (by simpa [hlen] using hfit1)).2⟩
    · rw [hszS]; exact hsz
  · intro i hu hs
    exact hkeep i hu hs
  · refine
      { moves := ?_
        slides := ?_
        ctrl := ?_
        ops0 := ?_
        ops1 := ?_ }
    · intro mv0 hmv0
      have hsame : mv0 = moves := Int.ofNat.inj (hmv0.symm.trans hmv)
      refine ⟨liveMove t.n t.k t.benchlen moves acc factor,
        by simpa [liveMove] using hmvS, ?_⟩
      simpa [hsame] using live_delta_le t.n t.k t.benchlen moves acc factor hnb hfacLen
    · intro sl0 hsl0
      have hsame : sl0 = slides := Int.ofNat.inj (hsl0.symm.trans hsl)
      have hslLive : bS.sudo_5Board_4cost.sudo_5Costs_6slides =
          Int.ofNat (slides + liveSlide t.n t.k t.benchlen acc factor) := by
        have heq : slides + 2 * pegCount (fieldCube t.n t.k t.benchlen acc) +
            2 * pegCount (fieldMul t.n t.k t.benchlen (fieldCube t.n t.k t.benchlen acc) factor) =
            slides + liveSlide t.n t.k t.benchlen acc factor := by
          rw [liveSlide, Nat.add_assoc]
        rw [← heq]
        exact hslS
      refine ⟨slides + liveSlide t.n t.k t.benchlen acc factor, hslLive, ?_⟩
      simpa [hsame] using
        add_le_add_left_le slides _ _ (live_slide_le t.n t.k t.benchlen acc factor hnb)
    · intro cIn hcIn
      have hsame : cIn = ctrl := Int.ofNat.inj (hcIn.symm.trans hc)
      refine ⟨ctrl + 4, hctrlS, ?_, ?_⟩
      · rw [hsame]
        exact Nat.le_add_right _ _
      · simpa [hsame] using ctrl_step_live ctrl
    · intro c0in hc0in
      have hslot : some (Int.ofNat c0in) = some (Int.ofNat c0) := hc0in.symm.trans hop0
      have hsame : c0in = c0 := by
        injection hslot with hEq
        exact Int.ofNat.inj hEq
      refine ⟨c0 + 1, hop0S, ?_⟩
      rw [hsame]
      exact Nat.le_refl _
    · intro c1in hc1in
      have hslot : some (Int.ofNat c1in) = some (Int.ofNat c1) := hc1in.symm.trans hop1
      have hsame : c1in = c1 := by
        injection hslot with hEq
        exact Int.ofNat.inj hEq
      refine ⟨c1 + 1, hop1S, ?_⟩
      rw [hsame]
      exact Nat.le_refl _
  · exact ⟨ctrl, hc, hctrlS⟩

/-- One digit, red, white, or empty. The up home becomes `powStep`, and the
    budget that remains covers `ds`. -/
theorem pow_step_at (b : Ecbs.Board) (t : Spec.Tier) (rhs acc : List Nat)
    (d : Nat) (ds : List Nat)
    (h : PowAt b t rhs acc (d :: ds))
    (hd : d = 0 ∨ d = 1 ∨ d = 2) :
    ∃ b', powDigitRun b d (if d = 2 then powGap else powBottom) = .ok b' ∧
      PowAt b' t rhs (powStep t.n t.k t.benchlen rhs acc d) ds ∧
      (∀ i, i ≠ powUp → i ≠ powSpare →
        b'.sudo_5Board_4home[i]? = b.sudo_5Board_4home[i]? ∧
        b'.sudo_5Board_4held[i]? = b.sudo_5Board_4held[i]?) ∧
      CounterLe b b' (powMove t.n t.benchlen) (powSlide t.n) powCtrl 1 ∧
      ∃ c, b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat c ∧
        b'.sudo_5Board_4cost.sudo_5Costs_4ctrl =
          Int.ofNat (c + (if d = 0 then 2 else 4)) := by
  rcases hd with hd0 | hd1 | hd2
  · obtain ⟨b', hr, hAt, hk, hsp, hctrl⟩ := pow_zero_at b t rhs acc ds (by simpa [hd0] using h)
    refine ⟨b', ?_, ?_, ?_, ?_, ?_⟩
    · simpa [hd0] using hr
    · simpa [hd0] using hAt
    · simpa [hd0] using hk
    · simpa [hd0] using hsp
    · simpa [hd0] using hctrl
  · obtain ⟨b', hr, hAt, hk, hsp, hctrl⟩ := pow_live_at b t rhs acc d powBottom rhs ds
        (by simpa [hd1] using h) (Or.inr ⟨hd1, rfl⟩)
        (by rw [hd1, if_neg (by decide : ¬ (1 = 2))])
        (by simpa [hd1] using h.botHome) (by simpa [hd1] using h.botHeld) h.rhsLen
    refine ⟨b', ?_, hAt, hk, hsp, ?_⟩
    · have hif : (if d = 2 then powGap else powBottom) = powBottom := by
        rw [hd1, if_neg (by decide : ¬ (1 = 2))]
      simpa [hif] using hr
    · have hif : (if d = 0 then 2 else 4) = 4 := by
        rw [hd1]; decide
      simpa [hif] using hctrl
  · have hnb : t.n ≤ t.benchlen := mul_span_n t.n t.benchlen h.nPos h.sat.mul_span
    have hfacLen : (fieldMul t.n t.k t.benchlen rhs rhs).length = t.n :=
      fieldMul_length t.n t.k t.benchlen rhs rhs hnb
    obtain ⟨b', hr, hAt, hk, hsp, hctrl⟩ := pow_live_at b t rhs acc d powGap
        (fieldMul t.n t.k t.benchlen rhs rhs) ds
        (by simpa [hd2] using h) (Or.inl ⟨hd2, rfl⟩)
        (by rw [hd2, if_pos rfl])
        (by simpa [hd2] using h.gapHome) (by simpa [hd2] using h.gapHeld) hfacLen
    refine ⟨b', ?_, hAt, hk, hsp, ?_⟩
    · have hif : (if d = 2 then powGap else powBottom) = powGap := by
        rw [hd2, if_pos rfl]
      simpa [hif] using hr
    · have hif : (if d = 0 then 2 else 4) = 4 := by
        rw [hd2]; decide
      simpa [hif] using hctrl

/-- The emitted power loop, one digit at a time. -/
def powRun : Ecbs.Board → List Nat → Except SudoRt.Trap Ecbs.Board
  | b, [] => .ok b
  | b, d :: ds => do
      let b ← powDigitRun b d (if d = 2 then powGap else powBottom)
      powRun b ds

/-- Folding the digits that remain leaves `foldl powStep` on the up home. -/
theorem pow_fold (b : Ecbs.Board) (t : Spec.Tier) (rhs acc : List Nat) (ds : List Nat)
    (h : PowAt b t rhs acc ds)
    (hdig : ∀ e, e ∈ ds → e = 0 ∨ e = 1 ∨ e = 2) :
    ∃ b', powRun b ds = .ok b' ∧
      PowAt b' t rhs (ds.foldl (powStep t.n t.k t.benchlen rhs) acc) [] ∧
      (∀ i, i ≠ powUp → i ≠ powSpare →
        b'.sudo_5Board_4home[i]? = b.sudo_5Board_4home[i]? ∧
        b'.sudo_5Board_4held[i]? = b.sudo_5Board_4held[i]?) ∧
      CounterLe b b' (powMove t.n t.benchlen * ds.length) (powSlide t.n * ds.length)
        (powCtrl * ds.length) ds.length := by
  induction ds generalizing b acc with
  | nil =>
    refine ⟨b, rfl, ?_, ?_, ?_⟩
    · simpa using h
    · intro _ _ _
      exact ⟨rfl, rfl⟩
    · exact counterLe_refl b
  | cons d ds ih =>
    have hd := hdig d (List.mem_cons_self d ds)
    obtain ⟨b1, hr, hAt, hk, hsp, _⟩ := pow_step_at b t rhs acc d ds h hd
    have hmem : ∀ e, e ∈ ds → e = 0 ∨ e = 1 ∨ e = 2 := by
      intro e he
      exact hdig e (List.mem_cons_of_mem d he)
    obtain ⟨b', hr2, hEnd, hk2, hsp2⟩ :=
      ih b1 (powStep t.n t.k t.benchlen rhs acc d) hAt hmem
    refine ⟨b', ?_, ?_, ?_, ?_⟩
    · rw [powRun, hr, ok_bind]
      exact hr2
    · simpa [List.foldl_cons] using hEnd
    · intro i hu hs
      obtain ⟨hhome1, hheld1⟩ := hk i hu hs
      obtain ⟨hhome2, hheld2⟩ := hk2 i hu hs
      exact ⟨hhome2.trans hhome1, hheld2.trans hheld1⟩
    · have hlen : (d :: ds).length = ds.length + 1 := by simp
      simpa [hlen] using counterLe_pow t.n t.benchlen ds.length hsp hsp2

theorem rootDigits_length (n : Nat) : (rootDigits n).length = n - 1 := by
  unfold rootDigits
  simp

theorem rootDigits_trit (n d : Nat) (hd : d ∈ rootDigits n) :
    d = 0 ∨ d = 1 ∨ d = 2 := by
  unfold rootDigits at hd
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
  exact rootDigit_cases n i

/-- The whole root power. The up home is `rootY`. -/
theorem pow_root (b : Ecbs.Board) (t : Spec.Tier) (x : List Nat)
    (h : PowAt b t (curveSide t.n t.k t.benchlen x) (whiteHole0 t.n) (rootDigits t.n)) :
    ∃ b', powRun b (rootDigits t.n) = .ok b' ∧
      PowAt b' t (curveSide t.n t.k t.benchlen x) (rootY t.n t.k t.benchlen x) [] := by
  obtain ⟨b', hr, hAt, _, _⟩ := pow_fold b t (curveSide t.n t.k t.benchlen x) (whiteHole0 t.n)
      (rootDigits t.n) h (fun e he => rootDigits_trit t.n e he)
  refine ⟨b', hr, ?_⟩
  simpa [rootY_digits] using hAt

/-- The numeric room a fresh power loop needs: one budget per root digit,
    and a script the seated marker does not meet. -/
structure PowRoom (t : Spec.Tier) : Prop where
  moves : FitsLen (powMove t.n t.benchlen * (t.n - 1))
  slides : FitsLen (powSlide t.n * (t.n - 1))
  ctrl : FitsLen (powCtrl * (t.n - 1))
  ops : FitsLen (t.n - 1)
  nPos : 0 < t.n
  script : 1 < t.script

theorem demo_pow_room : PowRoom demo where
  moves := by
    unfold FitsLen powMove demo i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  slides := by
    unfold FitsLen powSlide demo i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  ctrl := by
    unfold FitsLen powCtrl demo i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  ops := by
    unfold FitsLen demo i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  nPos := by decide
  script := demo_pow_script

theorem toy_pow_room : PowRoom toy where
  moves := by
    unfold FitsLen powMove toy i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  slides := by
    unfold FitsLen powSlide toy i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  ctrl := by
    unfold FitsLen powCtrl toy i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  ops := by
    unfold FitsLen toy i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  nPos := by decide
  script := toy_pow_script

theorem hobby_pow_room : PowRoom hobby where
  moves := by
    unfold FitsLen powMove hobby i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  slides := by
    unfold FitsLen powSlide hobby i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  ctrl := by
    unfold FitsLen powCtrl hobby i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  ops := by
    unfold FitsLen hobby i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  nPos := by decide
  script := hobby_pow_script

theorem serious_pow_room : PowRoom serious where
  moves := by
    unfold FitsLen powMove serious i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  slides := by
    unfold FitsLen powSlide serious i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  ctrl := by
    unfold FitsLen powCtrl serious i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  ops := by
    unfold FitsLen serious i64MaxNat
    exact Nat.le_of_ble_eq_true rfl
  nPos := by decide
  script := serious_pow_script

theorem pow_room (t : Spec.Tier) (h : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious) :
    PowRoom t := by
  rcases h with rfl | rfl | rfl | rfl
  · exact demo_pow_room
  · exact toy_pow_room
  · exact hobby_pow_room
  · exact serious_pow_room

end EcbsLink2.Link2
