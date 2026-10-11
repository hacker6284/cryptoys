/-
  The ladder `for`, one rung at a time. The emitted body is the park-through-clear
  prefix followed by the `if not last` / `if rung = 2` nest. Each branch of that
  nest is one of the eight successors. `climbEmit` is the induction form, and it
  is the `List.foldlM` / `forIn` walk of the stored ladder (build order reversed).
-/
import EcbsLink2.Link2.OpenRed

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
    (last : Bool) (hF : fromHole < 0) (hwhite : rung ≠ 2) (hlast : last = true) :
    climbRung b rung last x m = progWhiteFinal b rung m := by
  rw [hlast]
  exact white_final_body b rung m x hwhite

/-- Idle non-final white rung. The emitted nest is the clear, then the double. -/
theorem dispatch_idle_white_open (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (hF : fromHole < 0) (hwhite : rung ≠ 2) (hlast : last = false) :
    climbRung b rung last x m = progWhiteOpen b rung m := by
  rw [hlast]
  exact white_open_body b rung m x hwhite

/-- Idle non-final red rung. The emitted nest doubles, cubes, multiplies, and
    lays one peg. -/
theorem dispatch_idle_red_open (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (hF : fromHole < 0) (hr : rung = 2) (hlast : last = false) :
    climbRung b rung last x m = progRedOpen b rung m x := by
  rw [hlast]
  exact red_open_body b rung m x hr

/-- Idle final red rung. The emitted nest cubes and multiplies, and does not
    double or lay the extra peg. -/
theorem dispatch_idle_red_final (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (hF : fromHole < 0) (hr : rung = 2) (hlast : last = true) :
    climbRung b rung last x m = progRedFinal b m x := by
  rw [hlast]
  exact red_final_body b rung m x hr

/-- Parked final white rung. Same emitted nest as the idle final white rung. -/
theorem dispatch_park_white_final (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (hge : 0 ≤ fromHole) (hwhite : rung ≠ 2) (hlast : last = true) :
    climbRung b rung last x m = progWhiteFinal b rung m := by
  rw [hlast]
  exact white_final_body b rung m x hwhite

/-- Parked non-final white rung. -/
theorem dispatch_park_white_open (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (hge : 0 ≤ fromHole) (hwhite : rung ≠ 2) (hlast : last = false) :
    climbRung b rung last x m = progWhiteOpen b rung m := by
  rw [hlast]
  exact white_open_body b rung m x hwhite

/-- Parked final red rung. -/
theorem dispatch_park_red_final (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (hge : 0 ≤ fromHole) (hr : rung = 2) (hlast : last = true) :
    climbRung b rung last x m = progRedFinal b m x := by
  rw [hlast]
  exact red_final_body b rung m x hr

/-- Parked non-final red rung. -/
theorem dispatch_park_red_open (b : Ecbs.Board) (rung m : Nat) (x fromHole : Int)
    (last : Bool) (hge : 0 ≤ fromHole) (hr : rung = 2) (hlast : last = false) :
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
    (h : ClimbInvK done (r :: rest) b s base)
    (hhome : s.onBench = false) (hm : 0 < s.tally)
    (hParkAt : s.parkAt = base.ladder0 + base.R)
    (hCap : climbTallyPrefix base.tally0 done (r :: rest) ≤ base.mMax)
    (hxLen : base.x.length = base.n) (hxT : allTritList base.x) :
    ∃ b',
      climbRung b r rest.isEmpty ((base.xHome : Nat) : Int) s.tally = .ok b' ∧
      ClimbInv b' (modelRung s base.x r (climbAt base.ladder0 base.R s.ridx) rest.isEmpty) ∧
      RungDelta b b' base s.tally ∧
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
          red_final_k h hF hm hT hhome hParkAt hCap hxLen hxT
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_idle_red_final b 2 s.tally ((base.xHome : Nat) : Int) s.fromHole
          true hF rfl rfl]
        exact hprog
      · dsimp only [List.isEmpty]
        have hrest : (hd :: tl) ≠ [] := by simp
        obtain ⟨b', hprog, hK', hδ⟩ :=
          red_open_k h hF hm hT hhome hr hrest hParkAt hCap hxLen hxT
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_idle_red_open b r s.tally ((base.xHome : Nat) : Int) s.fromHole
          false hF hr rfl]
        exact hprog
    · rcases rest with (_ | ⟨hd, tl⟩)
      · dsimp only [List.isEmpty]
        obtain ⟨b', hprog, hK', hδ⟩ :=
          white_final_k h hF hm hT hhome h.parkBelow h.holeBelow hwhite hParkAt hCap
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_idle_white_final b r s.tally ((base.xHome : Nat) : Int) s.fromHole
          true hF hwhite rfl]
        exact hprog
      · dsimp only [List.isEmpty]
        have hrest : (hd :: tl) ≠ [] := by simp
        obtain ⟨b', hprog, hK', hδ⟩ :=
          white_open_k h hF hm hT hhome hwhite hrest hParkAt hCap
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
          red_final_ge h hge hm hT hhome hParkAt hCap hxLen hxT
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_park_red_final b 2 s.tally ((base.xHome : Nat) : Int) s.fromHole
          true hge rfl rfl]
        exact hprog
      · dsimp only [List.isEmpty]
        have hrest : (hd :: tl) ≠ [] := by simp
        obtain ⟨b', hprog, hK', hδ⟩ :=
          red_open_ge h hge hm hT hhome hr hrest hParkAt hCap hxLen hxT
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_park_red_open b r s.tally ((base.xHome : Nat) : Int) s.fromHole
          false hge hr rfl]
        exact hprog
    · rcases rest with (_ | ⟨hd, tl⟩)
      · dsimp only [List.isEmpty]
        obtain ⟨b', hprog, hK', hδ⟩ :=
          white_final_ge h hge hm hT hhome hwhite hParkAt hCap
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_park_white_final b r s.tally ((base.xHome : Nat) : Int) s.fromHole
          true hge hwhite rfl]
        exact hprog
      · dsimp only [List.isEmpty]
        have hrest : (hd :: tl) ≠ [] := by simp
        obtain ⟨b', hprog, hK', hδ⟩ :=
          white_open_ge h hge hm hT hhome hwhite hrest hParkAt hCap
        refine ⟨b', ?_, hK'.inv, hδ, hK'.shape, hK'.tmaxLt⟩
        rw [dispatch_park_white_open b r s.tally ((base.xHome : Nat) : Int) s.fromHole
          false hge hwhite rfl]
        exact hprog

end EcbsLink2.Link2
