/-
  The ladder `for`, one rung at a time. The emitted body is the park-through-clear
  prefix followed by the `if not last` / `if rung = 2` nest. Each branch of that
  nest is one of the eight successors. `climbEmit` is the induction form, and it
  is the `List.foldlM` / `forIn` walk of the stored ladder (build order reversed).
-/
import EcbsLink2.Link2.OpenRed
import EcbsLink2.Link2.TightDelta

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Park, copy, the white scan, the cube-peg loop, the gap mul, and clear. -/
def climbClear (b : Ecbs.Board) (rung m : Nat) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b ← Ecbs.park_rung b (rung : Int)
    let b ← Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false
    let _ ← SudoRt.runLoopOn (Int.ofNat 0)
        (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (whiteStep b (Int.ofNat (m - 1)))
        (fun j => .ok (b, j))
        (fun _ => .ok (b, (0 : Int)))
    let out ← SudoRt.runLoopOn (Int.ofNat 0, b)
        (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (cubePegStep 6 (Int.ofNat (m - 1)))
        (fun σ => .ok σ)
        (fun r => .ok ((0 : Int), r))
    let b := out.2
    let b ← Ecbs.mul b (5 : Int) (5 : Int) (6 : Int) false false false
    Ecbs.clear b (5 : Int)

/-- One rung of the ladder `for`: the clear, then double unless this is the
    last rung, and on a red rung the extra cube, multiply, and peg. -/
def climbRung (b : Ecbs.Board) (rung : Nat) (last : Bool) (x : Int) (m : Nat) :
    Except SudoRt.Trap Ecbs.Board :=
  do
    let b ← climbClear b rung m
    if !last then
      do
        let b ← Ecbs.tally_double b
        if SudoRt.SEq.beq (rung : Int) (2 : Int) then
          do
            let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
            let b ← Ecbs.mul b ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false
            if !last then Ecbs.tally_add_one b else pure b
        else pure b
    else if SudoRt.SEq.beq (rung : Int) (2 : Int) then
      do
        let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
        let b ← Ecbs.mul b ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false
        if !last then Ecbs.tally_add_one b else pure b
    else pure b

/-- Final white rung: the clear, and nothing after it. -/
def progWhiteFinal (b : Ecbs.Board) (rung m : Nat) : Except SudoRt.Trap Ecbs.Board :=
  climbClear b rung m

/-- Non-final white rung: the clear, then `tally_double`. -/
def progWhiteOpen (b : Ecbs.Board) (rung m : Nat) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b ← climbClear b rung m
    Ecbs.tally_double b

/-- Final red rung: the clear, then cube the gap and multiply by `x`. -/
def progRedFinal (b : Ecbs.Board) (m : Nat) (x : Int) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b ← climbClear b 2 m
    let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
    Ecbs.mul b ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false

/-- Non-final red rung: double, then cube, multiply by `x`, and one white peg. -/
def progRedOpen (b : Ecbs.Board) (rung m : Nat) (x : Int) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b ← climbClear b rung m
    let b ← Ecbs.tally_double b
    let b ← Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int)
    let b ← Ecbs.mul b ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false
    Ecbs.tally_add_one b

private theorem beq_rung_two (rung : Nat) (h : rung = 2) :
    SudoRt.SEq.beq (rung : Int) (2 : Int) = true := by
  rw [sEq_int, ← ofNat_eq_natCast rung, show (2 : Int) = Int.ofNat 2 from rfl, h]
  exact decide_eq_true rfl

private theorem beq_rung_not_two (rung : Nat) (h : rung ≠ 2) :
    SudoRt.SEq.beq (rung : Int) (2 : Int) = false := by
  rw [sEq_int, ← ofNat_eq_natCast rung, show (2 : Int) = Int.ofNat 2 from rfl]
  rw [decide_eq_false_iff_not]
  intro hEq
  exact h (Int.ofNat.inj hEq)

private theorem bind_pure_eq {α} (x : Except SudoRt.Trap α) :
    x >>= pure = x := by
  cases x with
  | error _ => rfl
  | ok _ => simp [pure_eq_ok, ok_bind]

private theorem bind_pure_after {α β}
    (x : Except SudoRt.Trap α) (f : α → Except SudoRt.Trap β) :
    (do
        let a ← x
        let b ← f a
        pure b) =
      (do
        let a ← x
        f a) := by
  cases x with
  | error _ => rfl
  | ok a =>
    rw [ok_bind, ok_bind]
    exact bind_pure_eq (f a)

private theorem seq_pure {α β γ}
    (x : Except SudoRt.Trap α) (f : α → Except SudoRt.Trap β)
    (g : β → Except SudoRt.Trap γ) :
    (do
        let a ← x
        let b ← f a
        let c ← g b
        pure c) =
      (do
        let a ← x
        let b ← f a
        g b) := by
  cases x with
  | error _ => rfl
  | ok a =>
    rw [ok_bind, ok_bind]
    exact bind_pure_after (f a) g

private theorem white_final_body (b : Ecbs.Board) (rung m : Nat) (x : Int)
    (hwhite : rung ≠ 2) :
    climbRung b rung true x m = progWhiteFinal b rung m := by
  unfold climbRung progWhiteFinal
  simp only [Bool.not_true, if_false]
  rw [beq_rung_not_two rung hwhite]
  simp only [Bool.false_eq_true, if_false]
  exact bind_pure_eq _

private theorem white_open_body (b : Ecbs.Board) (rung m : Nat) (x : Int)
    (hwhite : rung ≠ 2) :
    climbRung b rung false x m = progWhiteOpen b rung m := by
  unfold climbRung progWhiteOpen
  simp only [Bool.not_false, if_true]
  rw [beq_rung_not_two rung hwhite]
  simp only [Bool.false_eq_true, if_false]
  exact bind_pure_after (climbClear b rung m) (fun b => Ecbs.tally_double b)

private theorem red_final_body (b : Ecbs.Board) (rung m : Nat) (x : Int)
    (hr : rung = 2) :
    climbRung b rung true x m = progRedFinal b m x := by
  unfold climbRung progRedFinal
  rw [hr]
  simp only [Bool.not_true, if_false]
  rw [beq_rung_two 2 rfl]
  simp only [if_true, Bool.not_true, if_false]
  exact seq_pure (climbClear b 2 m)
    (fun b => Ecbs.cube b ((6 : Nat) : Int) ((5 : Nat) : Int))
    (fun b => Ecbs.mul b ((5 : Nat) : Int) x ((6 : Nat) : Int) false false false)

private theorem red_open_body (b : Ecbs.Board) (rung m : Nat) (x : Int)
    (hr : rung = 2) :
    climbRung b rung false x m = progRedOpen b rung m x := by
  unfold climbRung progRedOpen
  rw [hr]
  simp only [Bool.not_false, if_true]
  rw [beq_rung_two 2 rfl]
  simp only [if_true]

/-- Idle final white rung. The emitted nest is the clear. -/
theorem dispatch_idle_white_final (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (_hF : fromHole < 0) (hwhite : rung ≠ 2) (hlast : last = true) :
    climbRung b rung last x m = progWhiteFinal b rung m := by
  rw [hlast]
  exact white_final_body b rung m x hwhite

/-- Idle non-final white rung. The emitted nest is the clear, then the double. -/
theorem dispatch_idle_white_open (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (_hF : fromHole < 0) (hwhite : rung ≠ 2) (hlast : last = false) :
    climbRung b rung last x m = progWhiteOpen b rung m := by
  rw [hlast]
  exact white_open_body b rung m x hwhite

/-- Idle non-final red rung. The emitted nest doubles, cubes, multiplies, and
    lays one peg. -/
theorem dispatch_idle_red_open (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (_hF : fromHole < 0) (hr : rung = 2) (hlast : last = false) :
    climbRung b rung last x m = progRedOpen b rung m x := by
  rw [hlast]
  exact red_open_body b rung m x hr

/-- Idle final red rung. The emitted nest cubes and multiplies, and does not
    double or lay the extra peg. -/
theorem dispatch_idle_red_final (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (_hF : fromHole < 0) (hr : rung = 2) (hlast : last = true) :
    climbRung b rung last x m = progRedFinal b m x := by
  rw [hlast]
  exact red_final_body b rung m x hr

/-- Parked final white rung. Same emitted nest as the idle final white rung. -/
theorem dispatch_park_white_final (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (_hge : 0 ≤ fromHole) (hwhite : rung ≠ 2) (hlast : last = true) :
    climbRung b rung last x m = progWhiteFinal b rung m := by
  rw [hlast]
  exact white_final_body b rung m x hwhite

/-- Parked non-final white rung. -/
theorem dispatch_park_white_open (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (_hge : 0 ≤ fromHole) (hwhite : rung ≠ 2) (hlast : last = false) :
    climbRung b rung last x m = progWhiteOpen b rung m := by
  rw [hlast]
  exact white_open_body b rung m x hwhite

/-- Parked final red rung. -/
theorem dispatch_park_red_final (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (_hge : 0 ≤ fromHole) (hr : rung = 2) (hlast : last = true) :
    climbRung b rung last x m = progRedFinal b m x := by
  rw [hlast]
  exact red_final_body b rung m x hr

/-- Parked non-final red rung. -/
theorem dispatch_park_red_open (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (_hge : 0 ≤ fromHole) (hr : rung = 2) (hlast : last = false) :
    climbRung b rung last x m = progRedOpen b rung m x := by
  rw [hlast]
  exact red_open_body b rung m x hr

/-- `climbEmit` carries the unconsumed tail, so `last` is that tail's emptiness.
    That is `List.foldlM` over the ladder. -/
theorem climbEmit_foldlM
    (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (b : Ecbs.Board) (rs : List Nat) :
    rs.foldlM (fun (st : Ecbs.Board × List Nat) r => do
        let b ← step st.1 r st.2.tail.isEmpty
        pure (b, st.2.tail)) (b, rs) =
      (climbEmit step b rs).map (fun b' => (b', [])) := by
  induction rs generalizing b with
  | nil =>
    simp [climbEmit, List.foldlM_nil, pure_eq_ok, Except.map]
  | cons r rest ih =>
    rw [List.foldlM_cons]
    simp only [Prod.fst, Prod.snd, List.tail_cons]
    rw [climbEmit]
    cases hstep : step b r rest.isEmpty with
    | error e =>
      simp [hstep, Except.bind, Except.map, pure_eq_ok]
    | ok b' =>
      simp [hstep, ok_bind, pure_eq_ok, Except.map]
      exact ih b'

/-- The ladder `for`, as `forIn` over the stored list. The list is build order
    reversed; `last` is the empty tail. -/
def climbFor
    (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (b : Ecbs.Board) (rs : List Nat) : Except SudoRt.Trap Ecbs.Board := do
  let st ← forIn rs (b, rs) fun r (st : Ecbs.Board × List Nat) => do
    let b' ← step st.1 r st.2.tail.isEmpty
    pure (ForInStep.yield (b', st.2.tail))
  pure st.1

private theorem loop_aux
    (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (orig rs : List Nat) (b : Ecbs.Board)
    (h : ∃ t, t ++ rs = orig) :
    List.forIn'.loop orig
        (fun r _ (st : Ecbs.Board × List Nat) => do
          let b' ← step st.1 r st.2.tail.isEmpty
          pure (ForInStep.yield (b', st.2.tail)))
        rs (b, rs) h =
      (climbEmit step b rs).map (fun b' => (b', [])) := by
  induction rs generalizing b orig with
  | nil =>
    unfold List.forIn'.loop
    simp [climbEmit, Except.map, pure_eq_ok]
  | cons r rest ih =>
    unfold List.forIn'.loop
    simp only [Prod.fst, Prod.snd, List.tail_cons]
    rw [climbEmit]
    cases hstep : step b r rest.isEmpty with
    | error e =>
      simp [hstep, Except.bind, Except.map, pure_eq_ok]
    | ok b' =>
      simp [hstep, ok_bind, pure_eq_ok, Except.map]
      exact ih orig b' (by
        obtain ⟨t, ht⟩ := h
        refine ⟨t ++ [r], ?_⟩
        rw [List.append_assoc]
        simpa using ht)

/-- `forIn` over the reversed ladder is the `foldlM` / `climbEmit` induction. -/
theorem climbFor_emit
    (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (b : Ecbs.Board) (rs : List Nat) :
    climbFor step b rs = climbEmit step b rs := by
  unfold climbFor
  simp only [forIn, instForInOfForIn']
  have hred :
      (forIn' rs (b, rs) fun r _ st => do
          let b' ← step st.1 r st.2.tail.isEmpty
          pure (ForInStep.yield (b', st.2.tail))) =
        List.forIn'.loop rs
          (fun r _ st => do
            let b' ← step st.1 r st.2.tail.isEmpty
            pure (ForInStep.yield (b', st.2.tail)))
          rs (b, rs) ⟨[], rfl⟩ := rfl
  rw [hred, loop_aux step rs rs b ⟨[], rfl⟩]
  cases hfold : climbEmit step b rs with
  | error e =>
    simp [hfold, Except.map, Except.bind, pure_eq_ok]
  | ok b' =>
    simp [hfold, Except.map, ok_bind, pure_eq_ok]

/-- The bits `new_board` stores are `(rungList (n − 1)).reverse`. `forIn` of
    that reversed list is the induction `climb_refines` uses. -/
theorem climbFor_reversed
    (step : Ecbs.Board → Nat → Bool → Except SudoRt.Trap Ecbs.Board)
    (b : Ecbs.Board) (bits : List Nat) :
    climbFor step b bits.reverse = climbEmit step b bits.reverse :=
  climbFor_emit step b bits.reverse

/-- One emitted rung, when the gap is still in the home. The three splits are
    the park (`fromHole < 0` or not), the colour, and the empty tail. Each arm
    is the matching successor. -/
theorem climb_step_home
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hM : MoveHeadroom b base.n base.bench base.mMax)
    (hS : SlideHeadroom b base.n base.mMax)
    (hhome : s.onBench = false) (hm : 0 < s.tally)
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ b',
      climbRung b r rest.isEmpty ((base.xHome : Nat) : Int) s.tally = .ok b' ∧
      ClimbInv b' (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) rest.isEmpty) ∧
      RungDeltaTight b b' base s.tally ∧
      ClimbShape b' (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) rest.isEmpty)
        rest base ∧
      (∃ tmax : Nat,
        b'.sudo_5Board_4cost.sudo_5Costs_9tally_max = (tmax : Int) ∧
          (0 < (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) rest.isEmpty).tally →
            tmax < 2 * (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx)
              rest.isEmpty).tally)) := by
  have hT : s.tally ≤ base.mMax := h.tally_le hCap
  rcases Classical.em (s.fromHole < 0) with hF | hnge
  · rcases Classical.em (r = 2) with hr | hwhite
    · rcases rest with (_ | ⟨hd, tl⟩)
      · dsimp only [List.isEmpty]
        rw [hr] at h hCap ⊢
        obtain ⟨b', hprog, hK', hδ⟩ :=
          red_final_k h hM hS hF hm hT hhome hParkAt hCap hxLen hxT
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_idle_red_final b 2 s.tally ((base.xHome : Nat) : Int) s.fromHole
          true hF rfl rfl]
        exact hprog
      · dsimp only [List.isEmpty]
        have hrest : (hd :: tl) ≠ [] := by simp
        obtain ⟨b', hprog, hK', hδ⟩ :=
          red_open_k h hM hS hF hm hT hhome hr hrest hParkAt hCap hxLen hxT
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_idle_red_open b r s.tally ((base.xHome : Nat) : Int) s.fromHole
          false hF hr rfl]
        exact hprog
    · rcases rest with (_ | ⟨hd, tl⟩)
      · dsimp only [List.isEmpty]
        obtain ⟨b', hprog, hK', hδ⟩ :=
          white_final_k h hM hS hF hm hT hhome h.parkBelow h.holeBelow hwhite hParkAt hCap
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_idle_white_final b r s.tally ((base.xHome : Nat) : Int) s.fromHole
          true hF hwhite rfl]
        exact hprog
      · dsimp only [List.isEmpty]
        have hrest : (hd :: tl) ≠ [] := by simp
        obtain ⟨b', hprog, hK', hδ⟩ :=
          white_open_k h hM hS hF hm hT hhome hwhite hrest hParkAt hCap
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_idle_white_open b r s.tally ((base.xHome : Nat) : Int) s.fromHole
          false hF hwhite rfl]
        exact hprog
  · have hge : 0 ≤ s.fromHole := Int.not_lt.mp hnge
    rcases Classical.em (r = 2) with hr | hwhite
    · rcases rest with (_ | ⟨hd, tl⟩)
      · dsimp only [List.isEmpty]
        rw [hr] at h hCap ⊢
        obtain ⟨b', hprog, hK', hδ⟩ :=
          red_final_ge h hM hS hge hm hT hhome hParkAt hCap hxLen hxT
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_park_red_final b 2 s.tally ((base.xHome : Nat) : Int) s.fromHole
          true hge rfl rfl]
        exact hprog
      · dsimp only [List.isEmpty]
        have hrest : (hd :: tl) ≠ [] := by simp
        obtain ⟨b', hprog, hK', hδ⟩ :=
          red_open_ge h hM hS hge hm hT hhome hr hrest hParkAt hCap hxLen hxT
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_park_red_open b r s.tally ((base.xHome : Nat) : Int) s.fromHole
          false hge hr rfl]
        exact hprog
    · rcases rest with (_ | ⟨hd, tl⟩)
      · dsimp only [List.isEmpty]
        obtain ⟨b', hprog, hK', hδ⟩ :=
          white_final_ge h hM hS hge hm hT hhome hwhite hParkAt hCap
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_park_white_final b r s.tally ((base.xHome : Nat) : Int) s.fromHole
          true hge hwhite rfl]
        exact hprog
      · dsimp only [List.isEmpty]
        have hrest : (hd :: tl) ≠ [] := by simp
        obtain ⟨b', hprog, hK', hδ⟩ :=
          white_open_ge h hM hS hge hm hT hhome hwhite hrest hParkAt hCap
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_park_white_open b r s.tally ((base.xHome : Nat) : Int) s.fromHole
          false hge hwhite rfl]
        exact hprog

/-- The first cube-peg body determines the loop. A bench-on cube slides the gap
    before it reads the spare, and `cube_settle_other` makes that the same body
    as the cube on the already-slid board. -/
theorem cubePegStep_at_zero (src toN : Nat) (b b' : Ecbs.Board)
    (hbody : cubePegBody src b (Int.ofNat 0) = cubePegBody src b' (Int.ofNat 0))
    (hng : ¬ Int.ofNat 0 > Int.ofNat toN) :
    cubePegStep src (Int.ofNat toN) (Int.ofNat 0, b) =
      cubePegStep src (Int.ofNat toN) (Int.ofNat 0, b') := by
  unfold cubePegStep
  simp only [Prod.fst, Prod.snd]
  rw [if_neg hng, if_neg hng, hbody]

theorem peg_loop_of_body (src m : Nat) (b b' : Ecbs.Board) (hm : 0 < m)
    (hbody : cubePegBody src b (Int.ofNat 0) = cubePegBody src b' (Int.ofNat 0)) :
    SudoRt.runLoopOn (Int.ofNat 0, b)
        (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (cubePegStep src (Int.ofNat (m - 1)))
        (fun σ => .ok σ)
        (fun r => .ok ((0 : Int), r)) =
      SudoRt.runLoopOn (Int.ofNat 0, b')
        (fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)))
        (cubePegStep src (Int.ofNat (m - 1)))
        (fun σ => .ok σ)
        (fun r => .ok ((0 : Int), r)) := by
  have hfuel : fuelRange (Int.ofNat 0) (Int.ofNat (m - 1)) = (m - 1) + 1 := by
    rw [fuelRange_le (Nat.zero_le _)]
    omega
  have hng : ¬ Int.ofNat 0 > Int.ofNat (m - 1) := by
    rw [Int.not_lt]
    simpa [ofNat_eq_natCast] using (Int.ofNat_le.mpr (Nat.zero_le (m - 1)))
  rw [hfuel, runLoopOn_succ, runLoopOn_succ,
    cubePegStep_at_zero src (m - 1) b b' hbody hng]

/-- After `settle`, the bench is off, so a second `settle` is the identity. -/
theorem settle_idem (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (n moves slides peak : Nat) :
    Ecbs.settle (settleBoard b home hin.hH hin.hD xs n moves slides peak) =
      .ok (settleBoard b home hin.hH hin.hD xs n moves slides peak) :=
  settle_off _ (settle_bench_off b home ⟨hin.hH, hin.hD⟩ xs n moves slides peak)

/-- The resume record is unpark followed by the keep-park. -/
theorem park_rung_resume_board (b : Ecbs.Board) (holes : List Nat)
    (i src hole park prev rung high control ctrl : Nat)
    (hClimb : Ecbs.climb_holes b = .ok (embed holes))
    (hIdx : b.sudo_5Board_8rung_idx = (i : Int))
    (hAt : i < holes.length) (hHole : holes[i] = hole)
    (hFrom : b.sudo_5Board_11parked_from = (src : Int))
    (hParkF : b.sudo_5Board_9park_hole = (park : Int))
    (hRowS : src < b.sudo_5Board_3row.size)
    (hRowH : hole < b.sudo_5Board_3row.size)
    (hRowP : park < b.sudo_5Board_3row.size)
    (hPrev : b.sudo_5Board_3row[park] = (prev : Int))
    (hColour : b.sudo_5Board_3row[hole] = (rung : Int))
    (hRung : rung ≠ 0)
    (hCtrlN : b.sudo_5Board_1t.sudo_4Tier_7control = (control : Int))
    (hSrcC : src < control) (hParkC : park < control)
    (hHigh : b.sudo_5Board_4cost.sudo_5Costs_15control_highest = (high : Int))
    (hLeS : src ≤ high) (hLeP : park ≤ high)
    (hCtrl : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = (ctrl : Int))
    (hFitU : FitsLen (ctrl + 2)) (hFit : FitsLen ((ctrl + 2) + 2))
    (hneP : hole ≠ park) (hneS : hole ≠ src)
    (hFitI : FitsLen (i + 1)) :
    Ecbs.park_rung b (rung : Int) =
      .ok (parkResumeBoard b src hole park prev rung i ctrl hRowS hRowP hRowH) := by
  rw [park_rung_resume b holes i src hole park prev rung high control ctrl
    hClimb hIdx hAt hHole hFrom hParkF hRowS hRowH hRowP hPrev hColour hRung
    hCtrlN hSrcC hParkC hHigh hLeS hLeP hCtrl hFitU hFit hneP hneS hFitI]
  unfold parkResumeBoard parkKeepBoard
  apply congrArg Except.ok
  apply board_ext
  all_goals simp [unparkedBoard, ofNat_eq_natCast]

/-- `park_rung` commutes with `settle`. The idle arm is `parkKeep`. The resume
    arm is unpark then `parkKeep`. Neither reads the home array or the bench.
    The parked source is a control-row index strictly before the tally. -/
theorem park_rung_settle_comm
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hS : ClimbInvKCore done (r :: rest) bS { s with onBench := false } base)
    (h5H : 5 < b.sudo_5Board_4home.size) (h5D : 5 < b.sudo_5Board_4held.size)
    (xs : List Nat) (moves slides peak : Nat)
    (hbS : bS = settleBoard b 5 h5H h5D xs s.n moves slides peak) :
    ∃ bPark hH hD,
      Ecbs.park_rung b (r : Int) = .ok bPark ∧
      Ecbs.park_rung bS (r : Int) =
        .ok (settleBoard bPark 5 hH hD xs s.n moves slides peak) := by
  let hole := climbAt base.ladder0 base.R s.ridx
  by_cases hF : s.fromHole < 0
  · obtain ⟨bPark, hpark, _, _, hkeep⟩ := park_of_shape h
    obtain ⟨hRowP, hRowH, hEq⟩ := hkeep hF
    have hFs : ({ s with onBench := false } : ClimbModel).fromHole < 0 := hF
    obtain ⟨bParkS, hparkS, _, _, hkeepS⟩ := park_of_shape hS
    obtain ⟨hRowPS, hRowHS, hEqS⟩ := hkeepS hFs
    have hcomm := parkKeep_settle_comm b hole s.parkAt r s.ridx s.ctrl 5
      hRowP hRowH h5H h5D xs s.n moves slides peak
    have hrow := settleBoard_row b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
    refine ⟨parkKeepBoard b hole s.parkAt r s.ridx s.ctrl hRowP hRowH,
      by rw [parkKeep_home]; exact h5H,
      by rw [parkKeep_held]; exact h5D,
      hpark.trans (congrArg Except.ok hEq), ?_⟩
    rw [hparkS, hEqS]
    have hcast := parkKeep_cast hbS hole s.parkAt r s.ridx s.ctrl hRowPS hRowHS
    rw [hcast]
    have hp : (hbS ▸ hRowPS) = (hrow ▸ hRowP) := Subsingleton.elim _ _
    have hh : (hbS ▸ hRowHS) = (hrow ▸ hRowH) := Subsingleton.elim _ _
    rw [hp, hh]
    exact congrArg Except.ok hcomm
  · have hge : 0 ≤ s.fromHole := Int.not_lt.mp hF
    have hsrcBelow : s.fromHole.toNat < s.t0 := h.fromBelow hge
    let holes := downFrom (base.ladder0 + base.R - 1) base.R
    have hidxN : s.ridx < base.R := by
      rw [h.idx]
      have hk := h.kLe
      simp [List.length_append, List.length_cons] at hk
      omega
    have hAt : s.ridx < holes.length := by
      simpa [holes, downFromLen] using hidxN
    have hHole : holes[s.ridx] = hole := by
      simpa [holes, hole, climbAt] using
        downFromAt (base.ladder0 + base.R - 1) base.R s.ridx hidxN
    have hr := h.shape.park.nextRung r rest rfl
    have hRowH : hole < b.sudo_5Board_3row.size := by
      rw [h.inv.row, size_embed]; exact h.shape.park.holeLt
    have hRowP : s.parkAt < b.sudo_5Board_3row.size := by
      rw [h.inv.row, size_embed]; exact h.shape.park.parkLt
    have hColour : b.sudo_5Board_3row[hole] = (r : Int) := by
      have hget := embed_nat s.row hole h.shape.park.holeLt
      simp [hole, h.inv.row, hget, hr.1]
    have hpos : r ≠ 0 := hr.2
    obtain ⟨prev, hprev⟩ := h.shape.park.parkHeld hge
    have hsrc := h.shape.park.srcOk hge
    have hFrom : b.sudo_5Board_11parked_from = (s.fromHole.toNat : Int) := by
      rw [h.inv.fromP]
      exact h.shape.park.fromNat hge
    have hPrevB : b.sudo_5Board_3row[s.parkAt] = (prev : Int) := by
      have hget := embed_nat s.row s.parkAt h.shape.park.parkLt
      simp [h.inv.row, hget, hprev]
    have hRowS : s.fromHole.toNat < b.sudo_5Board_3row.size := by
      rw [h.inv.row, size_embed]; exact hsrc.1
    have hres := park_rung_resume_board b holes s.ridx s.fromHole.toNat hole s.parkAt prev r
      s.high base.control s.ctrl h.shape.park.climbH h.inv.ridx hAt hHole hFrom h.inv.park
      hRowS hRowH hRowP hPrevB hColour hpos h.shape.tierC hsrc.2.1 h.shape.park.parkIn
      h.inv.high hsrc.2.2.1 h.shape.park.parkLe h.inv.ctrl h.shape.park.fit2
      h.shape.park.fit4 h.shape.park.parkNe (Ne.symm hsrc.2.2.2) h.shape.park.fitI
    have hrow := settleBoard_row b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
    have hClimbS : Ecbs.climb_holes bS = .ok (embed holes) := by
      simpa [holes] using hS.shape.park.climbH
    have hIdxS : bS.sudo_5Board_8rung_idx = (s.ridx : Int) := hS.inv.ridx
    have hFromS : bS.sudo_5Board_11parked_from = (s.fromHole.toNat : Int) := by
      rw [hS.inv.fromP]
      exact h.shape.park.fromNat hge
    have hParkS : bS.sudo_5Board_9park_hole = (s.parkAt : Int) := hS.inv.park
    have hRowSS : s.fromHole.toNat < bS.sudo_5Board_3row.size := by
      rw [hS.inv.row, size_embed]; exact hsrc.1
    have hRowHS : hole < bS.sudo_5Board_3row.size := by
      rw [hS.inv.row, size_embed]; exact h.shape.park.holeLt
    have hRowPS : s.parkAt < bS.sudo_5Board_3row.size := by
      rw [hS.inv.row, size_embed]; exact h.shape.park.parkLt
    have hPrevS : bS.sudo_5Board_3row[s.parkAt] = (prev : Int) := by
      have hget := embed_nat s.row s.parkAt h.shape.park.parkLt
      simp [hS.inv.row, hget, hprev]
    have hColourS : bS.sudo_5Board_3row[hole] = (r : Int) := by
      have hget := embed_nat s.row hole h.shape.park.holeLt
      simp [hole, hS.inv.row, hget, hr.1]
    have hCtrlS : bS.sudo_5Board_4cost.sudo_5Costs_4ctrl = (s.ctrl : Int) := hS.inv.ctrl
    have hHighS : bS.sudo_5Board_4cost.sudo_5Costs_15control_highest = (s.high : Int) :=
      hS.inv.high
    have hresS := park_rung_resume_board bS holes s.ridx s.fromHole.toNat hole s.parkAt prev r
      s.high base.control s.ctrl hClimbS hIdxS hAt hHole hFromS hParkS
      hRowSS hRowHS hRowPS hPrevS hColourS hpos hS.shape.tierC hsrc.2.1 h.shape.park.parkIn
      hHighS hsrc.2.2.1 h.shape.park.parkLe hCtrlS h.shape.park.fit2
      h.shape.park.fit4 h.shape.park.parkNe (Ne.symm hsrc.2.2.2) h.shape.park.fitI
    have hcomm := parkResume_settle_comm b s.fromHole.toNat hole s.parkAt prev r
      s.ridx s.ctrl 5 hRowS hRowP hRowH h5H h5D xs s.n moves slides peak
    let bU := unparkedBoard b s.fromHole.toNat s.parkAt prev s.ctrl hRowS hRowP
    let hPU : s.parkAt < bU.sudo_5Board_3row.size := by
      simp [bU, unparkedBoard, Array.size_set]; exact hRowP
    let hHU : hole < bU.sudo_5Board_3row.size := by
      simp [bU, unparkedBoard, Array.size_set]; exact hRowH
    refine ⟨parkResumeBoard b s.fromHole.toNat hole s.parkAt prev r s.ridx s.ctrl hRowS hRowP hRowH,
      parkKeep_home bU hole s.parkAt r s.ridx (s.ctrl + 2) hPU hHU ▸
        (unparked_home b s.fromHole.toNat s.parkAt prev s.ctrl hRowS hRowP ▸ h5H),
      parkKeep_held bU hole s.parkAt r s.ridx (s.ctrl + 2) hPU hHU ▸
        (unparked_held b s.fromHole.toNat s.parkAt prev s.ctrl hRowS hRowP ▸ h5D),
      hres, ?_⟩
    rw [hresS]
    have hcast := parkResume_cast hbS s.fromHole.toNat hole s.parkAt prev r s.ridx s.ctrl
      hRowSS hRowPS hRowHS
    rw [hcast]
    have hs : (hbS ▸ hRowSS) = (hrow ▸ hRowS) := Subsingleton.elim _ _
    have hp : (hbS ▸ hRowPS) = (hrow ▸ hRowP) := Subsingleton.elim _ _
    have hh : (hbS ▸ hRowHS) = (hrow ▸ hRowH) := Subsingleton.elim _ _
    rw [hs, hp, hh]
    exact congrArg Except.ok hcomm

/-- `copy_band 6 5 false` against a bench aimed at home 5, and against that
    bench already slid home. `place_settle_comm` is the run-19 record commute:
    the two copies write the same spare and the same move and peak counters
    once the settle's `2 · pegs` is counted on the slid side. -/
theorem copy_band_settle
    (b : Ecbs.Board)
    (h5H : 5 < b.sudo_5Board_4home.size) (h5D : 5 < b.sudo_5Board_4held.size)
    (h6H : 6 < b.sudo_5Board_4home.size) (h6D : 6 < b.sudo_5Board_4held.size)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (xs : List Nat) (n moves slides peak : Nat)
    (hempty5 : b.sudo_5Board_4held[5] = false)
    (hon : b.sudo_5Board_8bench_on = true)
    (hto : b.sudo_5Board_8bench_to = (5 : Int))
    (hbench : b.sudo_5Board_5bench = embed xs)
    (hspare : b.sudo_5Board_4held[6] = false)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlen : n ≤ xs.length) (hf : FitsLen n)
    (_hpos : 0 < xs.length) (_hfitL : FitsLen xs.length)
    (_hzero : ∀ i, n ≤ i → ∀ hi : i < xs.length, xs[i] = 0)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak)
    (_hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int))
    (hfitC : FitsLen (moves + pegCount (xs.take n)))
    (hfitCS : FitsLen (moves + 2 * pegCount (xs.take n) + pegCount (xs.take n)))
    (_hpeg : FitsLen (2 * pegCount (xs.take n)))
    (_hfitM : FitsLen (moves + 2 * pegCount (xs.take n)))
    (_hfitS : FitsLen (slides + 2 * pegCount (xs.take n))) :
    let g := xs.take n
    let bS := settleBoard b 5 h5H h5D xs n moves slides peak
    let pkS := raisedPeak peak (countHeld (b.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7)
    let bC := placeBoard b 6 h6H h6D g moves peak
    let c6 := countHeld (b.sudo_5Board_4held.set ⟨6, h6D⟩ true) 7
    let pkP := raisedPeak peak c6
    let h5C : 5 < bC.sudo_5Board_4home.size := by
      rw [place_size_home b 6 ⟨h6H, h6D⟩ g moves peak]; exact h5H
    let h5Cd : 5 < bC.sudo_5Board_4held.size := by
      rw [place_size_held b 6 ⟨h6H, h6D⟩ g moves peak]; exact h5D
    ∃ (h6HS : 6 < bS.sudo_5Board_4home.size) (h6DS : 6 < bS.sudo_5Board_4held.size),
      Ecbs.copy_band b ((6 : Nat) : Int) ((5 : Nat) : Int) false =
        .ok (placeBoard b 6 h6H h6D g moves peak) ∧
      Ecbs.copy_band bS ((6 : Nat) : Int) ((5 : Nat) : Int) false =
        .ok (placeBoard bS 6 h6HS h6DS g (moves + 2 * pegCount g) pkS) ∧
      placeBoard bS 6 h6HS h6DS g (moves + 2 * pegCount g) pkS =
        settleBoard bC 5 h5C h5Cd xs n (moves + pegCount g) slides pkP := by
  intro g bS pkS bC c6 pkP h5C h5Cd
  have h6HS : 6 < bS.sudo_5Board_4home.size := by
    rw [settle_home_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak, Array.size_set]; exact h6H
  have h6DS : 6 < bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak, Array.size_set]; exact h6D
  have h5HS : 5 < bS.sudo_5Board_4home.size := by
    rw [settle_home_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak, Array.size_set]; exact h5H
  have h5DS : 5 < bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak, Array.size_set]; exact h5D
  have h7S : 7 ≤ bS.sudo_5Board_4held.size := by
    rw [settle_held_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak, Array.size_set]; exact h7
  have hheld5 : bS.sudo_5Board_4held[5] = true := by
    rw [idx_get (settle_held_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak) 5 h5DS, Array.getElem_set]
    simp
  have harr5 : bS.sudo_5Board_4home[5] = embed g := by
    rw [idx_get (settle_home_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak) 5 h5HS, Array.getElem_set]
    rfl
  have hspareS : bS.sudo_5Board_4held[6] = false := by
    rw [idx_get (settle_held_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak) 6 h6DS,
      Array.getElem_set, if_neg (by decide : (5 : Nat) ≠ 6)]
    exact hspare
  have hmvS : bS.sudo_5Board_4cost.sudo_5Costs_5moves =
      ((moves + 2 * pegCount g : Nat) : Int) := by
    rw [settle_moves_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak, ofNat_eq_natCast]
  have hpkS : bS.sudo_5Board_4cost.sudo_5Costs_4peak = (pkS : Int) := by
    rw [settle_peak_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak hpk]
    simp [pkS, raisedPeak, ofNat_eq_natCast]
  have hnS : bS.sudo_5Board_1t.sudo_4Tier_1n = (g.length : Int) := by
    rw [settle_tier_eq b 5 ⟨h5H, h5D⟩ xs n moves slides peak, hn]
    have hg : g.length = n := by
      simp [g, List.length_take, Nat.min_eq_left hlen]
    rw [hg]
  have hcopy := copy_band_bench_refines b 6 5 xs n moves peak h6H h6D h5D h7
    hempty5 hon hto hbench hspare hn hlen hf hmv hpk hfitC
  have hcopyS := copy_band_refines bS 6 5 g (moves + 2 * pegCount g) pkS
    h6HS h6DS h5HS h5DS h7S hheld5 harr5 hspareS hnS
    (by simp [g, List.length_take, Nat.min_eq_left hlen]; exact hf)
    hmvS hpkS hfitCS
  have hcomm := place_settle_comm b 5 6 ⟨h5H, h5D⟩ h6H h6D (by decide) xs g n moves slides peak hpk
  refine ⟨h6HS, h6DS, hcopy, ?_, ?_⟩
  · simpa [g, bS, pkS] using hcopyS
  · simpa [g, bS, pkS, bC, c6, pkP, h5C, h5Cd] using hcomm

/-- Park does not touch the homes, the bench, or the move, slide, and peak counters.
    The source hole it rewrites is a control-row index before the tally. -/
theorem bench_of_park
    {done rest : List Nat} {r : Nat} {b bPark : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hpark : Ecbs.park_rung b (r : Int) = .ok bPark) :
    bPark.sudo_5Board_4home = b.sudo_5Board_4home ∧
    bPark.sudo_5Board_4held = b.sudo_5Board_4held ∧
    bPark.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
    bPark.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
    bPark.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
    bPark.sudo_5Board_4cost.sudo_5Costs_5moves = b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
    bPark.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
    bPark.sudo_5Board_4cost.sudo_5Costs_4peak = b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
    bPark.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
    bPark.sudo_5Board_1t = b.sudo_5Board_1t ∧
    bPark.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
    bPark.sudo_5Board_4cost.sudo_5Costs_3ops = b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  by_cases hF : s.fromHole < 0
  · obtain ⟨bP, hp, _, _, hkeep⟩ := park_of_shape h
    obtain ⟨hRowP, hRowH, hEq⟩ := hkeep hF
    have hsame : bPark = bP := Except.ok.inj (hpark.symm.trans hp)
    rw [hsame, hEq, parkKeepBoard]
    simp
  · have hge : 0 ≤ s.fromHole := Int.not_lt.mp hF
    obtain ⟨bP, hp, _, _, _, _, _, _, _, _, _, hW⟩ := resume_park_row h hge
    obtain ⟨hRowP, hRowH, hW⟩ := hW
    have hsame : bPark = bP := Except.ok.inj (hpark.symm.trans hp)
    rw [hsame, hW, withPark, parkKeepBoard]
    simp

/-- `place` leaves the tally origin, the marker, the bench, the tier, and the
    ops array where they were. -/
theorem place_frame (b : Ecbs.Board) (home : Nat)
    (hin : HomeIn b home)
    (xs : List Nat) (moves peak : Nat) :
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_6tally0 =
        b.sudo_5Board_6tally0 ∧
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_9marker_on =
        b.sudo_5Board_9marker_on ∧
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_5bench =
        b.sudo_5Board_5bench ∧
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_8bench_to =
        b.sudo_5Board_8bench_to ∧
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_1t = b.sudo_5Board_1t ∧
    (placeBoard b home hin.hH hin.hD xs moves peak).sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops := by
  unfold placeBoard
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Park rewrites the control row and leaves the tally origin. The new row is
    `afterPark`, idle or resume. -/
theorem park_row
    {done rest : List Nat} {r : Nat} {b bPark : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hpark : Ecbs.park_rung b (r : Int) = .ok bPark) :
    bPark.sudo_5Board_3row =
      embed (afterPark s.row s.fromHole s.parkAt
        (climbAt base.ladder0 base.R s.ridx) r) ∧
    bPark.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 := by
  let hole := climbAt base.ladder0 base.R s.ridx
  by_cases hF : s.fromHole < 0
  · obtain ⟨bP, hp, _, _, hkeep⟩ := park_of_shape h
    obtain ⟨hRowP, hRowH, hEq⟩ := hkeep hF
    have hsame : bPark = bP := Except.ok.inj (hpark.symm.trans hp)
    have hrowK := parkKeep_row b s.row hole s.parkAt r s.ridx s.ctrl
      hRowP hRowH h.inv.row h.shape.park.parkLt h.shape.park.holeLt
    have hidle := afterPark_idle s.row s.parkAt hole r
    have hneg := afterPark_neg s.row s.fromHole s.parkAt hole r hF
    refine ⟨?_, ?_⟩
    · rw [hsame, hEq, hrowK, ← hidle, ← hneg]
    · rw [hsame, hEq]
      simp [parkKeepBoard]
  · have hge : 0 ≤ s.fromHole := Int.not_lt.mp hF
    obtain ⟨bP, hp, hrow, _, _, _, _, _, _, _, _, hW⟩ := resume_park_row h hge
    obtain ⟨_, _, hEq⟩ := hW
    have hsame : bPark = bP := Except.ok.inj (hpark.symm.trans hp)
    refine ⟨hsame ▸ hrow, ?_⟩
    rw [hsame, hEq, withPark_tally0]
    simp [parkKeepBoard]

/-- The white scan reads the row and the tally origin. Park writes both of
    those holes before the tally, so the segment stays white (`(r :: rest)` is
    never empty) and the scan returns the board it was given. -/
theorem white_after_park
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board}
    {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvKCore done (r :: rest) b s base)
    (hm : 0 < s.tally) (bScan : Ecbs.Board)
    (hrow : bScan.sudo_5Board_3row =
      embed (afterPark s.row s.fromHole s.parkAt
        (climbAt base.ladder0 base.R s.ridx) r))
    (ht0 : bScan.sudo_5Board_6tally0 = (s.t0 : Int)) :
    SudoRt.runLoopOn (Int.ofNat 0)
        (fuelRange (Int.ofNat 0) (Int.ofNat (s.tally - 1)))
        (whiteStep bScan (Int.ofNat (s.tally - 1)))
        (fun j => .ok (bScan, j))
        (fun _ => .ok (bScan, (0 : Int))) =
      .ok (bScan, Int.ofNat (s.tally - 1)) := by
  let rowP := afterPark s.row s.fromHole s.parkAt
    (climbAt base.ladder0 base.R s.ridx) r
  have hfin : (r :: rest).isEmpty = false := by simp
  have hseg0 : RowSeg s.row s.t0 s.tally false := by
    simpa [hfin] using h.shape.seg
  have hfrom : s.fromHole < 0 ∨ s.fromHole.toNat < s.t0 := by
    by_cases hf : s.fromHole < 0
    · exact Or.inl hf
    · exact Or.inr (h.fromBelow (Int.not_lt.mp hf))
  have hseg := afterPark_seg s.row s.fromHole s.parkAt
    (climbAt base.ladder0 base.R s.ridx) r s.t0 s.tally
    hseg0 h.parkBelow h.holeBelow hfrom
  have hroom : s.t0 + s.tally ≤ rowP.length := hseg.room
  have hwhite : ∀ j (hj : j < s.tally),
      rowP[s.t0 + j]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) hroom) = 1 := by
    intro j hj
    simpa using hseg.colour j hj
  have hwhite' : ∀ j (hj : j < s.tally), rowP[s.t0 + j]'(by omega) = 1 := by
    intro j hj
    have hc := hwhite j hj
    have hix :
        (⟨s.t0 + j, by omega⟩ : Fin rowP.length) =
          ⟨s.t0 + j, Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj s.t0) hroom⟩ :=
      Fin.ext rfl
    simpa [hix] using hc
  exact white_scan_loop_refines bScan rowP s.t0 s.tally hm ht0 hrow hroom
    hwhite' h.shape.peg.fitRow h.shape.peg.fitTall

/-- One bench-on clear and the clear of the slid board are the same program.
    Park commutes with settle, the copy is the run-19 place commute, the white
    scan only reads the row and the tally origin, and the first cube on the
    unslid board is the cube of the settled board. The peg loop is that body,
    so everything after it is the same program on equal boards. -/
theorem climbClear_slide
    {done rest : List Nat} {r : Nat} {b bS : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hon : s.onBench = true)
    (hm : 0 < s.tally)
    (hS : slideGap b = .ok bS) :
    climbClear b r s.tally = climbClear bS r s.tally := by
  let xs := s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0
  obtain ⟨moves, slides, peak, hmv, hsl, hpk, hbench, hslide⟩ := slideGap_run h hon
  have h5H : 5 < b.sudo_5Board_4home.size :=
    Nat.lt_trans (by decide : (5 : Nat) < 6) h.shape.spareH
  have h5D : 5 < b.sudo_5Board_4held.size :=
    Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h.shape.h7
  have hbS : bS = settleBoard b 5 h5H h5D xs s.n moves slides peak :=
    Except.ok.inj (hS.symm.trans (by simpa [xs, h5H, h5D] using hslide))
  have hcore := climbCore_slideGap h.toCore hon xs moves slides peak hmv hsl hpk hbench rfl
  have hcoreS : ClimbInvKCore done (r :: rest) bS { s with onBench := false } base := by
    rw [hbS]
    exact hcore
  obtain ⟨bPark, hHp, hDp, hpark, hparkS⟩ :=
    park_rung_settle_comm h.toCore hcoreS h5H h5D xs moves slides peak hbS
  have hfix := bench_of_park h.toCore hpark
  have hpkI : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak := by
    rw [hpk, ofNat_eq_natCast]
  have hmvP : bPark.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) :=
    hfix.2.2.2.2.2.1.trans hmv
  have hslP : bPark.sudo_5Board_4cost.sudo_5Costs_6slides = (slides : Int) :=
    hfix.2.2.2.2.2.2.1.trans hsl
  have hpkP : bPark.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak :=
    hfix.2.2.2.2.2.2.2.1.trans hpkI
  have honP : bPark.sudo_5Board_8bench_on = true :=
    hfix.2.2.1.trans (h.inv.gapBench hon).1
  have htoP : bPark.sudo_5Board_8bench_to = (5 : Int) := by
    rw [hfix.2.2.2.2.1]
    exact (h.inv.gapBench hon).2.1
  have hbenchP : bPark.sudo_5Board_5bench = embed xs := hfix.2.2.2.1.trans hbench
  have h5DP : 5 < bPark.sudo_5Board_4held.size := by
    rw [hfix.2.1]; exact h5D
  have hemptyP : bPark.sudo_5Board_4held[5] = false := by
    rw [idx_get hfix.2.1 5 h5DP]
    exact (h.shape.gapClear hon)
  have h6HP : 6 < bPark.sudo_5Board_4home.size := by
    rw [hfix.1]; exact h.shape.spareH
  have h6DP : 6 < bPark.sudo_5Board_4held.size := by
    rw [hfix.2.1]; exact h.shape.spareD
  have h7P : 7 ≤ bPark.sudo_5Board_4held.size := by
    rw [hfix.2.1]; exact h.shape.h7
  have hspareP : bPark.sudo_5Board_4held[6] = false := by
    rw [idx_get hfix.2.1 6 h6DP]
    exact h.shape.spareE
  have hnP : bPark.sudo_5Board_1t.sudo_4Tier_1n = (s.n : Int) := by
    rw [hfix.2.2.2.2.2.2.2.2.2.1]
    exact h.shape.tierN
  have hnleB : s.n ≤ s.benchlen := by
    have hsp := h.shape.peg.span
    omega
  have hlenX : xs.length = s.benchlen :=
    bench_pad_len s.gap s.n s.benchlen h.shape.gapLen hnleB
  have hlen : s.n ≤ xs.length := by rw [hlenX]; exact hnleB
  have hpos : 0 < xs.length := by
    rw [hlenX]
    exact Nat.lt_of_lt_of_le h.shape.peg.n_pos hnleB
  have hzero : ∀ i, s.n ≤ i → ∀ hi : i < xs.length, xs[i] = 0 :=
    bench_pad_zero s.gap s.n s.benchlen h.shape.gapLen hnleB
  have hpegs : pegCount (xs.take s.n) ≤ base.n :=
    Nat.le_trans (pegCount_take_le xs s.n) (Nat.le_of_eq h.hn)
  have hpegCharge : pegCount (xs.take s.n) + 2 * base.n ≤
      rungCharge base.n base.bench base.mMax := by
    have h4 : 4 * base.n ≤ pegCharge base.n base.bench := by
      unfold pegCharge
      omega
    have hpiece : pegCharge base.n base.bench ≤
        (base.mMax + 1) * pegCharge base.n base.bench := by
      simpa [Nat.one_mul] using
        Nat.mul_le_mul_right (pegCharge base.n base.bench) (Nat.le_add_left 1 base.mMax)
    have hrc : 2 * base.n + pegCharge base.n base.bench ≤
        rungCharge base.n base.bench base.mMax := by
      unfold rungCharge
      exact Nat.le_trans (Nat.add_le_add_left hpiece _) (Nat.le_add_right _ _)
    have hp : pegCount (xs.take s.n) ≤ base.n := hpegs
    omega
  have hfitC : FitsLen (moves + pegCount (xs.take s.n)) := by
    let hM := moveHeadroom_of_cons h
    have hmvN : moves = hM.mv := ofNat_inj_nat (hmv.symm.trans hM.eq)
    have hroom : FitsLen (moves + (rungCharge base.n base.bench base.mMax - 2 * base.n)) := by
      simpa [hmvN] using hM.room
    apply FitsLen.of_le hroom
    have hsub : pegCount (xs.take s.n) ≤
        rungCharge base.n base.bench base.mMax - 2 * base.n :=
      Nat.le_sub_of_add_le hpegCharge
    omega
  have hfitCS : FitsLen (moves + 2 * pegCount (xs.take s.n) + pegCount (xs.take s.n)) := by
    have hk : done.length + 1 ≤ base.R := by
      have hlen := h.kLe
      simp [List.length_append, List.length_cons] at hlen
      omega
    have hmvLe : moves + 2 * base.n ≤
        base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
      obtain ⟨mv0, hmv0, hle⟩ := h.moves
      have := ofNat_inj_nat (hmv.symm.trans hmv0)
      simpa [hon, this] using hle
    apply FitsLen.of_le (bench_headroom_of base.moves0 base.R done.length base.n base.bench
      base.mMax moves (pegCount (xs.take s.n)) hk hmvLe hpegs base.fitM)
    have hsub : pegCount (xs.take s.n) ≤
        rungCharge base.n base.bench base.mMax - 2 * base.n :=
      Nat.le_sub_of_add_le hpegCharge
    omega
  have hfitM : FitsLen (moves + 2 * pegCount (xs.take s.n)) :=
    FitsLen.of_le hfitCS (Nat.le_add_right _ _)
  have hpegF : FitsLen (2 * pegCount (xs.take s.n)) :=
    FitsLen.of_le hfitM (Nat.le_add_left _ moves)
  have hfitSl : FitsLen (slides + 2 * pegCount (xs.take s.n)) := by
    apply FitsLen.of_le (bench_slide_headroom_of base.slides0 base.R done.length base.n
      base.mMax slides (pegCount (xs.take s.n)) (by
        have hlen := h.kLe
        simp [List.length_append, List.length_cons] at hlen
        omega) (by
        obtain ⟨sl0, hsl0, hle⟩ := h.slides
        have := ofNat_inj_nat (hsl.symm.trans hsl0)
        simpa [hon, this] using hle) hpegs base.fitS)
    omega
  obtain ⟨h6HS, h6DS, hcopy, hcopyS, hplace⟩ :=
    copy_band_settle bPark hHp hDp h6HP h6DP h7P xs s.n moves slides peak
      hemptyP honP htoP hbenchP hspareP hnP hlen h.shape.peg.fitN hpos
      (by rw [hlenX]; exact h.shape.peg.fitBn) hzero hmvP hpkP hslP
      hfitC hfitCS hpegF hfitM hfitSl
  let bC := placeBoard bPark 6 h6HP h6DP (xs.take s.n) moves peak
  let h5C : 5 < bC.sudo_5Board_4home.size := by
    rw [place_size_home bPark 6 ⟨h6HP, h6DP⟩ (xs.take s.n) moves peak]; exact hHp
  let h5Cd : 5 < bC.sudo_5Board_4held.size := by
    rw [place_size_held bPark 6 ⟨h6HP, h6DP⟩ (xs.take s.n) moves peak]; exact hDp
  let mvC := moves + pegCount (xs.take s.n)
  let pkC := raisedPeak peak (countHeld (bPark.sudo_5Board_4held.set ⟨6, h6DP⟩ true) 7)
  let bCS := settleBoard bC 5 h5C h5Cd xs s.n mvC slides pkC
  have hCS : placeBoard (settleBoard bPark 5 hHp hDp xs s.n moves slides peak) 6 h6HS h6DS
      (xs.take s.n) (moves + 2 * pegCount (xs.take s.n))
      (raisedPeak peak (countHeld (bPark.sudo_5Board_4held.set ⟨5, hDp⟩ true) 7)) = bCS := by
    refine hplace.trans ?_
    exact settleBoard_irrel bC 5 _ h5C _ h5Cd xs s.n mvC slides pkC
  have hprow := park_row h.toCore hpark
  obtain ⟨ht0Pl, hmkPl, hbenchPl, htoPl, htierPl, hopsPl⟩ :=
    place_frame bPark 6 ⟨h6HP, h6DP⟩ (xs.take s.n) moves peak
  have hrowC : bC.sudo_5Board_3row =
      embed (afterPark s.row s.fromHole s.parkAt
        (climbAt base.ladder0 base.R s.ridx) r) := by
    rw [place_row_out bPark 6 ⟨h6HP, h6DP⟩ (xs.take s.n) moves peak]
    exact hprow.1
  have ht0C : bC.sudo_5Board_6tally0 = (s.t0 : Int) := by
    rw [ht0Pl, hprow.2, h.inv.t0]
  have hrowS : bCS.sudo_5Board_3row =
      embed (afterPark s.row s.fromHole s.parkAt
        (climbAt base.ladder0 base.R s.ridx) r) := by
    rw [settle_row_out bC 5 ⟨h5C, h5Cd⟩ xs s.n mvC slides pkC, hrowC]
  have ht0S : bCS.sudo_5Board_6tally0 = (s.t0 : Int) := by
    rw [settle_tally_eq bC 5 ⟨h5C, h5Cd⟩ xs s.n mvC slides pkC, ht0C]
  have hscanC := white_after_park h.toCore hm bC hrowC ht0C
  have hscanS := white_after_park h.toCore hm bCS hrowS ht0S
  have hmkC : bC.sudo_5Board_9marker_on = false := by
    rw [hmkPl, hfix.2.2.2.2.2.2.2.2.2.2.1, h.inv.marker]
  have honC : bC.sudo_5Board_8bench_on = true := by
    rw [place_on_out bPark 6 ⟨h6HP, h6DP⟩ (xs.take s.n) moves peak]
    exact honP
  have htoC : bC.sudo_5Board_8bench_to = (5 : Int) := htoPl.trans htoP
  have hbenchC : bC.sudo_5Board_5bench = embed xs := hbenchPl.trans hbenchP
  have hnC : bC.sudo_5Board_1t.sudo_4Tier_1n = (s.n : Int) := by
    rw [show bC.sudo_5Board_1t = bPark.sudo_5Board_1t from htierPl]
    exact hnP
  have h7C : 7 ≤ bC.sudo_5Board_4held.size := by
    rw [place_size_held bPark 6 ⟨h6HP, h6DP⟩ (xs.take s.n) moves peak]
    exact h7P
  have hemptyC : bC.sudo_5Board_4held[5] = false := by
    rw [place_held_other bPark 6 5 ⟨h6HP, h6DP⟩ (xs.take s.n) moves peak (by decide : (6 : Nat) ≠ 5) h5DP h5Cd]
    exact hemptyP
  have hmvC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvC := by
    simpa [bC, mvC] using place_moves_out bPark 6 ⟨h6HP, h6DP⟩ (xs.take s.n) moves peak
  have hslC : bC.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides := by
    rw [place_slides_out bPark 6 ⟨h6HP, h6DP⟩ (xs.take s.n) moves peak, hslP,
      ofNat_eq_natCast]
  have hpkC : bC.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat pkC := by
    have hpkOut := place_peak_out bPark 6 ⟨h6HP, h6DP⟩ (xs.take s.n) moves peak hpkP
    simpa [bC, pkC] using hpkOut
  have hfitCube : FitsLen (mvC + 2 * pegCount (xs.take s.n)) := by
    apply FitsLen.of_le hfitCS
    simp only [mvC]
    omega
  have hopsB : bPark.sudo_5Board_4cost.sudo_5Costs_3ops =
      b.sudo_5Board_4cost.sudo_5Costs_3ops :=
    hfix.2.2.2.2.2.2.2.2.2.2.2
  have hopsC : 1 < bC.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    rw [hopsPl, hopsB]
    exact h.shape.peg.opsGt
  obtain ⟨cOps, hcOps, hcBound⟩ := h.ops_loose 1 h.shape.peg.opsGt
  have hop1 : bC.sudo_5Board_4cost.sudo_5Costs_3ops[1] = (cOps : Int) := by
    have hget := idx_get (hopsPl.trans hopsB) 1 hopsC
    exact (hget.trans (get_proof_irrel _ 1 _ _)).trans hcOps
  have hkOps : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    simp [List.length_append, List.length_cons] at hlen
    omega
  have hfops : FitsLen (cOps + 1) := by
    apply FitsLen.of_le base.fitO
    have hmul : done.length * (base.mMax + 3) + (base.mMax + 3) =
        (done.length + 1) * (base.mMax + 3) := by
      rw [← Nat.succ_mul]
    have h1 : cOps + 1 ≤
        base.ops0 + done.length * (base.mMax + 3) + (base.mMax + 3) := by
      omega
    have h2 : base.ops0 + done.length * (base.mMax + 3) + (base.mMax + 3) =
        base.ops0 + (done.length + 1) * (base.mMax + 3) := by
      rw [Nat.add_assoc, hmul]
    have h3 : (done.length + 1) * (base.mMax + 3) ≤ base.R * (base.mMax + 3) :=
      Nat.mul_le_mul_right _ hkOps
    omega
  have hcube := cube_settle_other bC 6 6 5 xs s.n mvC slides pkC cOps
    hmkC honC htoC h5C h5Cd h7C hemptyC hbenchC hnC
    hpos hlen hzero h.shape.peg.fitN
    (by rw [hlenX]; exact h.shape.peg.fitBn)
    hmvC hslC hpkC hpegF hfitCube hfitSl hopsC hop1 hfops
  have hbody := cubePegBody_cube 6 bC bCS (Int.ofNat 0) hcube
  have hloop := peg_loop_of_body 6 s.tally bC bCS hm hbody
  unfold climbClear
  rw [hpark, hparkS, ok_bind, ok_bind, hcopy,
    hcopyS.trans (congrArg Except.ok hCS), ok_bind, ok_bind,
    hscanC, hscanS, ok_bind, ok_bind, hloop]

/-- A bench-on rung and the rung of the slid board run the same program. -/
theorem climbRung_slide
    {done rest : List Nat} {r : Nat} {b bS : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hon : s.onBench = true)
    (hm : 0 < s.tally)
    (hS : slideGap b = .ok bS) :
    climbRung b r rest.isEmpty ((base.xHome : Nat) : Int) s.tally =
      climbRung bS r rest.isEmpty ((base.xHome : Nat) : Int) s.tally := by
  unfold climbRung
  rw [climbClear_slide h hon hm hS]

/-- Two boards with the same row and tally origin run the same white-scan step. -/
theorem whiteStep_row (b b' : Ecbs.Board) (toV j : Int)
    (hrow : b.sudo_5Board_3row = b'.sudo_5Board_3row)
    (ht : b.sudo_5Board_6tally0 = b'.sudo_5Board_6tally0) :
    whiteStep b toV j = whiteStep b' toV j := by
  unfold whiteStep
  simp [hrow, ht]

/-- A home rung's tight delta is the carry `climbInvK_succ` needs: the bench
    reservation on the way in is zero, and the successor reserves `2 · n`. -/
theorem moveCarry_off {b b' : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (hδ : RungDeltaTight b b' base m) (onBench : Bool) (hoff : onBench = false) :
    ∃ (mv mv' : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = (mv' : Int) ∧
      mv' + 2 * base.n ≤
        mv + (if onBench then 2 * base.n else 0) +
          rungCharge base.n base.bench m := by
  obtain ⟨mv, mv', hb, hb', hle⟩ := hδ.moveTight
  refine ⟨mv, mv', hb, hb', ?_⟩
  simpa [hoff] using hle

theorem slideCarry_off {b b' : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (hδ : RungDeltaTight b b' base m) (onBench : Bool) (hoff : onBench = false) :
    ∃ (sl sl' : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = (sl' : Int) ∧
      sl' + 2 * base.n ≤
        sl + (if onBench then 2 * base.n else 0) +
          rungSlideCharge base.n m := by
  obtain ⟨sl, sl', hb, hb', hle⟩ := hδ.slideTight
  refine ⟨sl, sl', hb, hb', ?_⟩
  simpa [hoff] using hle

/-- A home rung's ops slack is the carry `climbInvK_succ` needs. The bench
    reservation on the way in is zero, and the successor reserves one op. -/
theorem opsCarry_off {b b' : Ecbs.Board} {base : ClimbBudget} {m : Nat}
    (hδ : RungDeltaTight b b' base m) (onBench : Bool) (hoff : onBench = false) :
    ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ (c c' : Nat),
        b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hδ.delta.opsSize ▸ hi) = (c' : Int) ∧
        c' + 1 ≤ c + (if onBench then 1 else 0) + (base.mMax + 3) := by
  intro i hi
  obtain ⟨c, c', hc, hc', hle⟩ := hδ.opsTight i hi
  refine ⟨c, c', hc, hc', ?_⟩
  have h1 : c' + 1 ≤ c + (base.mMax + 3) := by omega
  simpa [hoff] using h1

/-- One rung, gap still in home 5. That is the entry rung: `new_board` leaves the
    bench off, and `invert` copies the input into home 5 before the ladder `for`.
    `modelRung` then sets `onBench`, so a second rung is not this theorem. -/
theorem climb_refines_one
    {r : Nat} {b0 : Ecbs.Board} {s0 : ClimbModel} {base : ClimbBudget}
    (h0 : ClimbInvK [] [r] b0 s0 base)
    (hEntry : s0.onBench = false)
    (hm : 0 < s0.tally)
    (hPark : s0.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 [] [r] ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ b',
      climbRung b0 r true ((base.xHome : Nat) : Int) s0.tally = .ok b' ∧
      ClimbInvK [r] [] b'
        (modelRung s0 base.x r (climbAt base.ladder0 base.R s0.ridx) true) base := by
  obtain ⟨b', hprog, hinv, hδ, hshape, htmax⟩ :=
    climb_step_home h0.toCore (moveHeadroom_of_cons h0) (slideHeadroom_of_cons h0)
      hEntry hm hPark hCap hxLen hxT
  refine ⟨b', hprog, ?_⟩
  exact climbInvK_succ h0 hinv hδ.delta
    (moveCarry_off hδ s0.onBench hEntry) (slideCarry_off hδ s0.onBench hEntry)
    (opsCarry_off hδ s0.onBench hEntry)
    hCap hshape h0.holeBelow htmax rfl

/-- Bench rung, once `climbRung` on the original board agrees with `climbRung`
    on the slid board. `slideGap` restores the core, shape, and tight headroom.
    The home successor returns a tight delta from the slid counter. The settle
    spends `2 · pegs ≤ 2 · n`, so that tight delta is one loose `RungDelta`
    from the pre-slide board, and `climbInvK_succ` rebuilds the absolute fields. -/
theorem climb_step_bench_of
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hon : s.onBench = true)
    (hm : 0 < s.tally)
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x)
    (hprogEq : ∀ bS,
      slideGap b = .ok bS →
      climbRung b r rest.isEmpty ((base.xHome : Nat) : Int) s.tally =
        climbRung bS r rest.isEmpty ((base.xHome : Nat) : Int) s.tally) :
    ∃ b',
      climbRung b r rest.isEmpty ((base.xHome : Nat) : Int) s.tally = .ok b' ∧
      ClimbInvK (done ++ [r]) rest b'
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) rest.isEmpty) base := by
  let xs := s.gap.take s.n ++ List.replicate (s.benchlen - s.n) 0
  obtain ⟨moves, slides, peak, hmv, hsl, hpk, hbench, hslide⟩ := slideGap_run h hon
  have h5H : 5 < b.sudo_5Board_4home.size :=
    Nat.lt_trans (by decide : (5 : Nat) < 6) h.shape.spareH
  have h5D : 5 < b.sudo_5Board_4held.size :=
    Nat.lt_of_lt_of_le (by decide : (5 : Nat) < 7) h.shape.h7
  let bS := settleBoard b 5 h5H h5D xs s.n moves slides peak
  have hcore := climbCore_slideGap h.toCore hon xs moves slides peak hmv hsl hpk hbench rfl
  have hslideB : slideGap b = .ok bS := by
    simpa [bS, h5H, h5D] using hslide
  obtain ⟨mv0, hmv0, hmvLe⟩ := h.moves
  obtain ⟨sl0, hsl0, hslLe⟩ := h.slides
  have hmvN : moves = mv0 := ofNat_inj_nat (hmv.symm.trans hmv0)
  have hslN : slides = sl0 := ofNat_inj_nat (hsl.symm.trans hsl0)
  have hmvRes : moves + 2 * base.n ≤
      base.moves0 + done.length * rungCharge base.n base.bench base.mMax := by
    simpa [hon, hmvN] using hmvLe
  have hslRes : slides + 2 * base.n ≤
      base.slides0 + done.length * rungSlideCharge base.n base.mMax := by
    simpa [hon, hslN] using hslLe
  have hpegs : pegCount (xs.take s.n) ≤ base.n := by
    rw [← h.hn]
    exact pegCount_take_le xs s.n
  have hk : done.length + 1 ≤ base.R := by
    have hlen := h.kLe
    simp [List.length_append, List.length_cons] at hlen
    omega
  have hroomM := bench_headroom_of base.moves0 base.R done.length base.n base.bench
    base.mMax moves (pegCount (xs.take s.n)) hk hmvRes hpegs base.fitM
  have hroomS := bench_slide_headroom_of base.slides0 base.R done.length base.n
    base.mMax slides (pegCount (xs.take s.n)) hk hslRes hpegs base.fitS
  have hmvS := settle_moves_eq b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
  have hslS := settle_slides_eq b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
  have hpkS := settle_peak_eq b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak (by rw [hpk, ofNat_eq_natCast])
  let pegs := pegCount (xs.take s.n)
  let mvS : Nat := moves + 2 * pegs
  let slS : Nat := slides + 2 * pegs
  let pkS : Nat :=
    if peak < countHeld (b.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7 then
      countHeld (b.sudo_5Board_4held.set ⟨5, h5D⟩ true) 7 else peak
  have hM : MoveHeadroom bS base.n base.bench base.mMax :=
    ⟨mvS, by simpa [bS, mvS, pegs, ofNat_eq_natCast] using hmvS, by simpa [pegs] using hroomM⟩
  have hSl : SlideHeadroom bS base.n base.mMax :=
    ⟨slS, by simpa [bS, slS, pegs, ofNat_eq_natCast] using hslS, by simpa [pegs] using hroomS⟩
  let sH : ClimbModel := { s with onBench := false }
  obtain ⟨b', hprogS, hinv, hδ, hshape, htmax⟩ :=
    climb_step_home hcore hM hSl rfl hm hParkAt hCap hxLen hxT
  have hprogS' : climbRung bS r rest.isEmpty ((base.xHome : Nat) : Int) s.tally = .ok b' := by
    simpa [bS, sH] using hprogS
  have hprog : climbRung b r rest.isEmpty ((base.xHome : Nat) : Int) s.tally = .ok b' := by
    rw [hprogEq bS hslideB]
    exact hprogS'
  have hops := settle_ops b 5 ⟨h5H, h5D⟩ xs s.n moves slides peak
  obtain ⟨pk0, hpk0, _⟩ := h.peak
  have hpkN : peak = pk0 := ofNat_inj_nat (hpk.symm.trans hpk0)
  have hpkLe : pkS ≤ max pk0 7 := by
    have hocc := countHeld_seven (b.sudo_5Board_4held.set ⟨5, h5D⟩ true)
    simpa [pkS, hpkN] using settle_peak_le peak _ hocc
  have hδL := rungDelta_of_slide hδ moves slides pk0 mvS slS pkS pegs
    hmv hsl hpk0
    (by simpa [bS, mvS, pegs, ofNat_eq_natCast] using hmvS)
    (by simpa [bS, slS, pegs, ofNat_eq_natCast] using hslS)
    (by simpa [bS, pkS] using hpkS)
    rfl rfl hpegs hpkLe (by simpa [bS] using hops)
  have hmod : modelRung sH base.x r (climbAt base.ladder0 base.R s.ridx) rest.isEmpty =
      modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) rest.isEmpty := by
    simp [sH, modelRung]
  refine ⟨b', hprog, ?_⟩
  have hmoveCarry : ∃ (mv mv' : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = (mv' : Int) ∧
      mv' + 2 * base.n ≤
        mv + (if s.onBench then 2 * base.n else 0) +
          rungCharge base.n base.bench s.tally := by
    obtain ⟨mv0, mv', hb, hb', hle⟩ := hδ.moveTight
    have h0 : mv0 = mvS := ofNat_inj_nat (hb.symm.trans
      (by simpa [bS, mvS, pegs, ofNat_eq_natCast] using hmvS))
    refine ⟨moves, mv', hmv, hb', ?_⟩
    simp only [hon, ite_true]
    have hle' : mv' + 2 * base.n ≤
        moves + 2 * pegs + rungCharge base.n base.bench s.tally := by
      simpa [h0, mvS, pegs] using hle
    have hpeg2 : 2 * pegs ≤ 2 * base.n := Nat.mul_le_mul_left 2 hpegs
    omega
  have hslideCarry : ∃ (sl sl' : Nat),
      b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = (sl' : Int) ∧
      sl' + 2 * base.n ≤
        sl + (if s.onBench then 2 * base.n else 0) +
          rungSlideCharge base.n s.tally := by
    obtain ⟨sl0, sl', hb, hb', hle⟩ := hδ.slideTight
    have h0 : sl0 = slS := ofNat_inj_nat (hb.symm.trans
      (by simpa [bS, slS, pegs, ofNat_eq_natCast] using hslS))
    refine ⟨slides, sl', hsl, hb', ?_⟩
    simp only [hon, ite_true]
    have hle' : sl' + 2 * base.n ≤
        slides + 2 * pegs + rungSlideCharge base.n s.tally := by
      simpa [h0, slS, pegs] using hle
    have hpeg2 : 2 * pegs ≤ 2 * base.n := Nat.mul_le_mul_left 2 hpegs
    omega
  have hopsCarry : ∀ i (hi : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size),
      ∃ (c c' : Nat),
        b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (c : Int) ∧
        b'.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hδL.opsSize ▸ hi) = (c' : Int) ∧
        c' + 1 ≤ c + (if s.onBench then 1 else 0) + (base.mMax + 3) := by
    intro i hi
    have hiS : i < bS.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
      rw [hops]; exact hi
    obtain ⟨cS, c', hcS, hc', hle⟩ := hδ.opsTight i hiS
    have hcB : b.sudo_5Board_4cost.sudo_5Costs_3ops[i] = (cS : Int) :=
      (idx_get hops.symm i hi).trans hcS
    refine ⟨cS, c', hcB, ?_, ?_⟩
    · have hix :
          b'.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hδL.opsSize ▸ hi) =
            b'.sudo_5Board_4cost.sudo_5Costs_3ops[i]'(hδ.delta.opsSize ▸ hiS) := by
        have hfin : (⟨i, hδL.opsSize ▸ hi⟩ : Fin _) = ⟨i, hδ.delta.opsSize ▸ hiS⟩ :=
          Fin.ext rfl
        simp [hfin]
      exact hix.trans hc'
    · simp only [hon, ite_true]
      omega
  have hK := climbInvK_succ h (by simpa [hmod] using hinv) hδL hmoveCarry hslideCarry
    hopsCarry hCap
    (by simpa [hmod] using hshape) h.holeBelow (by simpa [hmod] using htmax) rfl
  simpa [hmod] using hK

/-- One emitted rung. The gap is either still in home 5 or on the bench aimed
    at home 5. The bench arm slides first; `climbRung_slide` says that is the
    home program. -/
theorem climb_step
    {done rest : List Nat} {r : Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done (r :: rest) b s base)
    (hm : 0 < s.tally)
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ b',
      climbRung b r rest.isEmpty ((base.xHome : Nat) : Int) s.tally = .ok b' ∧
      ClimbInvK (done ++ [r]) rest b'
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) rest.isEmpty) base := by
  cases hon : s.onBench
  · obtain ⟨b', hprog, hinv, hδ, hshape, htmax⟩ :=
      climb_step_home h.toCore (moveHeadroom_of_cons h) (slideHeadroom_of_cons h)
        hon hm hParkAt hCap hxLen hxT
    refine ⟨b', hprog, climbInvK_succ h hinv hδ.delta
      (moveCarry_off hδ s.onBench hon) (slideCarry_off hδ s.onBench hon)
      (opsCarry_off hδ s.onBench hon)
      hCap hshape h.holeBelow htmax rfl⟩
  · exact climb_step_bench_of h hon hm hParkAt hCap hxLen hxT
      (fun _ hs => climbRung_slide h hon hm hs)

/-- The ladder step the emitted `for` runs: `m` is the board's tally length. -/
def climbStepBoard (x : Int) (b : Ecbs.Board) (rung : Nat) (last : Bool) :
    Except SudoRt.Trap Ecbs.Board :=
  climbRung b rung last x b.sudo_5Board_9tally_len.toNat

/-- The whole ladder, with no step hypothesis. Each rung's tally length is the
    one `ClimbInv` records on the board, `parkAt` stays the top of the ladder,
    and `tallyAfter` keeps the tally positive. -/
theorem climb_refines_emit
    (rs : List Nat) (b0 : Ecbs.Board) (s0 : ClimbModel) (base : ClimbBudget)
    (h0 : ClimbInvK [] rs b0 s0 base)
    (hPark : s0.parkAt = base.ladder0 + base.R)
    (hm : 0 < s0.tally)
    (hCap : ∀ done rest, rs = done ++ rest →
      climbTallyPrefix base.tally0 done rest ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ b' s',
      climbEmit (climbStepBoard ((base.xHome : Nat) : Int)) b0 rs = .ok b' ∧
      s' = modelClimb s0 base.x
        (fun s _ _ => climbAt base.ladder0 base.R s.ridx) rs ∧
      ClimbInvK rs [] b' s' base ∧
      (s'.gap, s'.tally) =
        invClimb s0.n s0.k s0.benchlen base.x (s0.gap, s0.tally) rs ∧
      s'.tally ≤ base.mMax := by
  let hole : ClimbModel → Nat → Bool → Nat :=
    fun s _ _ => climbAt base.ladder0 base.R s.ridx
  have hmain : ∀ (done rest : List Nat) (b : Ecbs.Board) (s : ClimbModel),
      rs = done ++ rest →
      ClimbInvK done rest b s base →
      s.parkAt = base.ladder0 + base.R →
      0 < s.tally →
      ∃ b' s',
        climbEmit (climbStepBoard ((base.xHome : Nat) : Int)) b rest = .ok b' ∧
        s' = modelClimb s base.x hole rest ∧
        ClimbInvK (done ++ rest) [] b' s' base := by
    intro done rest
    induction rest generalizing done with
    | nil =>
      intro b s _hrs h _hPark _hm
      exact ⟨b, s, by simp [climbEmit], rfl, by simpa using h⟩
    | cons r rest ih =>
      intro b s hrs h hPark hm
      have hCap1 := hCap done (r :: rest) hrs
      have htall : b.sudo_5Board_9tally_len.toNat = s.tally := by
        rw [h.inv.len]
        exact Int.toNat_ofNat s.tally
      obtain ⟨b1, hprog, hK⟩ := climb_step h hm hPark hCap1 hxLen hxT
      have hprog' : climbStepBoard ((base.xHome : Nat) : Int) b r rest.isEmpty = .ok b1 := by
        simpa [climbStepBoard, htall] using hprog
      have hPark1 : (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx)
          rest.isEmpty).parkAt = base.ladder0 + base.R := by
        simpa [modelRung] using hPark
      have hm1 : 0 < (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx)
          rest.isEmpty).tally := by
        rw [modelRung_tally]
        exact Nat.lt_of_lt_of_le hm (tallyAfter_ge s.tally r rest.isEmpty)
      have hrs1 : rs = (done ++ [r]) ++ rest := by
        simp [hrs, List.append_assoc]
      obtain ⟨b', s', hfold, hs', hK'⟩ := ih (done ++ [r]) b1
        (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) rest.isEmpty)
        hrs1 hK hPark1 hm1
      refine ⟨b', s', ?_, ?_, ?_⟩
      · rw [climbEmit, hprog', ok_bind]
        exact hfold
      · simp [modelClimb, hole, hs']
      · simpa [List.append_assoc] using hK'
  obtain ⟨b', s', hfold, hs', hK⟩ := hmain [] rs b0 s0 (by simp) h0 hPark hm
  refine ⟨b', s', hfold, hs', hK, ?_, hK.tally_le (hCap rs [] (by simp))⟩
  rw [hs']
  exact modelClimb_spec s0 base.x hole rs

/-- After the ladder something is parked. `unpark_rung` puts that colour back
    and zeros the rung index. The bench and the homes stay, so the final cube
    still reads the gap off the bench. -/
theorem unpark_after_climb
    {done : List Nat} {b : Ecbs.Board} {s : ClimbModel} {base : ClimbBudget}
    (h : ClimbInvK done [] b s base)
    (hge : 0 ≤ s.fromHole) :
    ∃ bU, Ecbs.unpark_rung b = .ok bU ∧
      bU.sudo_5Board_11parked_from = -1 ∧
      bU.sudo_5Board_8rung_idx = 0 ∧
      bU.sudo_5Board_4home = b.sudo_5Board_4home ∧
      bU.sudo_5Board_4held = b.sudo_5Board_4held ∧
      bU.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      bU.sudo_5Board_8bench_to = b.sudo_5Board_8bench_to ∧
      bU.sudo_5Board_5bench = b.sudo_5Board_5bench ∧
      bU.sudo_5Board_4cost.sudo_5Costs_5moves =
        b.sudo_5Board_4cost.sudo_5Costs_5moves ∧
      bU.sudo_5Board_4cost.sudo_5Costs_6slides =
        b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      bU.sudo_5Board_4cost.sudo_5Costs_4peak =
        b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
      bU.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (s.ctrl + 2) ∧
      bU.sudo_5Board_6tally0 = b.sudo_5Board_6tally0 ∧
      bU.sudo_5Board_1t = b.sudo_5Board_1t ∧
      bU.sudo_5Board_9marker_on = b.sudo_5Board_9marker_on ∧
      bU.sudo_5Board_4cost.sudo_5Costs_3ops =
        b.sudo_5Board_4cost.sudo_5Costs_3ops ∧
      bU.sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        b.sudo_5Board_4cost.sudo_5Costs_11peak_strict ∧
      bU.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole ∧
      bU.sudo_5Board_9tally_len = b.sudo_5Board_9tally_len ∧
      bU.sudo_5Board_4cost.sudo_5Costs_15control_highest =
        b.sudo_5Board_4cost.sudo_5Costs_15control_highest := by
  obtain ⟨colour, hcell⟩ := h.shape.park.parkHeld hge
  have hsrc := h.shape.park.srcOk hge
  let src := s.fromHole.toNat
  have hRowS : src < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact hsrc.1
  have hRowP : s.parkAt < b.sudo_5Board_3row.size := by
    rw [h.inv.row, size_embed]; exact h.shape.park.parkLt
  have hColour : b.sudo_5Board_3row[s.parkAt] = (colour : Int) := by
    have hget := embed_nat s.row s.parkAt h.shape.park.parkLt
    simp [h.inv.row, hget, hcell]
  have hFrom : b.sudo_5Board_11parked_from = (src : Int) := by
    rw [h.inv.fromP]
    exact h.shape.park.fromNat hge
  have hrun := unpark_rung_back b src s.parkAt colour s.high base.control s.ctrl
    hFrom h.inv.park hRowS hRowP hColour h.shape.tierC hsrc.2.1 h.inv.high
    hsrc.2.2.1 h.inv.ctrl h.shape.park.fit2
  refine ⟨_, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rfl

end EcbsLink2.Link2
