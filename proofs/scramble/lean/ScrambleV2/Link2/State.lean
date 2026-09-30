/-
  LINK 2. The emitted digest path against the model: `fresh`, the v2 constructors,
  `push_step` (trace text is not modelled; a digest-only state returns unchanged),
  `do_move`, `do_rule`, `apply_v2_symbol`. Proof-only. No algorithm change.
-/
import ScrambleV2.Link2.Reorient
import ScrambleV2.Link2.Facelets

namespace ScrambleV2.Link2
open MegaDreifach.Link2

theorem Reach.length26 (cube : Cube) (h : Reach cube) : cube.length = 26 := by
  obtain ⟨_, hF⟩ := h
  have hmap : cube.length = lattice.length := by simpa using hF.2.2.length_eq
  have hlatt : lattice.length = 26 := by decide
  rw [hmap, hlatt]

theorem Reach.fits26 (cube : Cube) (h : Reach cube) : FitsLen cube.length := by
  rw [Reach.length26 cube h]
  unfold FitsLen i64MaxNat
  decide

theorem Reach.after_turns (f : Face) :
    ∀ (n : Nat) (cube : Cube), Reach cube → Reach (turnsN f n cube)
  | 0, cube, h => by simpa [turnsN] using h
  | n + 1, cube, h => by
    change Reach (quarter f (turnsN f n cube))
    exact Reach.quarter_turn f _ (Reach.after_turns f n cube h)

theorem turns_one (f : Face) (cube : Cube) : turnsN f 1 cube = quarter f cube := rfl

theorem blank_ok : Scramble.blank = .ok (#[] : Array Int) := by
  unfold Scramble.blank
  rfl

theorem fresh_refines (version : Int) (traced : Bool) :
    Scramble.fresh version traced = .ok
      { sudo_8Scramble_7version := version
        sudo_8Scramble_7pending := #[]
        sudo_8Scramble_5total := 0
        sudo_8Scramble_9processed := 0
        sudo_8Scramble_4cube := embedCube solvedCube
        sudo_8Scramble_5steps := #[]
        sudo_8Scramble_6traced := traced
        sudo_8Scramble_4done := false } := by
  unfold Scramble.fresh
  rw [solved_cube_refines]
  rfl

theorem scramble_v2_refines : Scramble.scramble_v2 = Scramble.fresh (2 : Int) true := by
  unfold Scramble.scramble_v2
  rfl

theorem scramble_v2_digest_refines :
    Scramble.scramble_v2_digest = Scramble.fresh (2 : Int) false := by
  unfold Scramble.scramble_v2_digest
  rfl

/-- On a digest-only state, `push_step` is the identity. The trace is not recorded. -/
theorem push_step_digest (s : Scramble.Scramble) (h : s.sudo_8Scramble_6traced = false)
    (kind move nybble up front : Array Int) (block at_ : Int) :
    Scramble.push_step s kind move nybble block at_ up front = .ok s := by
  unfold Scramble.push_step
  simp [h, pure_eq_ok]

/-- A traced `push_step` keeps the cube (and every field but the step list). -/
theorem push_step_traced (s : Scramble.Scramble) (cube : Cube)
    (hcube : s.sudo_8Scramble_4cube = embedCube cube) (hR : Reach cube)
    (htr : s.sudo_8Scramble_6traced = true)
    (kind move nybble up front : Array Int) (block at_ : Int) :
    ∃ faces s', Scramble.facelets_of (embedCube cube) = .ok faces ∧
      Scramble.push_step s kind move nybble block at_ up front = .ok s' ∧
      s'.sudo_8Scramble_4cube = s.sudo_8Scramble_4cube ∧
      s'.sudo_8Scramble_7pending = s.sudo_8Scramble_7pending ∧
      s'.sudo_8Scramble_5total = s.sudo_8Scramble_5total ∧
      s'.sudo_8Scramble_9processed = s.sudo_8Scramble_9processed ∧
      s'.sudo_8Scramble_7version = s.sudo_8Scramble_7version ∧
      s'.sudo_8Scramble_6traced = s.sudo_8Scramble_6traced ∧
      s'.sudo_8Scramble_4done = s.sudo_8Scramble_4done := by
  unfold Scramble.push_step
  simp only [htr, if_true]
  obtain ⟨cols, _, hf⟩ := Reach.facelets_of cube hR
  rw [hcube, hf, ok_bind, appendL_spec, pure_eq_ok]
  exact ⟨Array.mk (cols.map Color.letter),
    { sudo_8Scramble_7version := s.sudo_8Scramble_7version,
      sudo_8Scramble_7pending := s.sudo_8Scramble_7pending,
      sudo_8Scramble_5total := s.sudo_8Scramble_5total,
      sudo_8Scramble_9processed := s.sudo_8Scramble_9processed,
      sudo_8Scramble_4cube := embedCube cube,
      sudo_8Scramble_5steps := s.sudo_8Scramble_5steps.push
        { sudo_4Step_4kind := kind, sudo_4Step_4move := move, sudo_4Step_6nybble := nybble,
          sudo_4Step_5block := block, sudo_4Step_5index := at_, sudo_4Step_2up := up,
          sudo_4Step_5front := front, sudo_4Step_8facelets := Array.mk (cols.map Color.letter) },
      sudo_8Scramble_6traced := true,
      sudo_8Scramble_4done := s.sudo_8Scramble_4done },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `do_move` turns the cube and, when not tracing, leaves every other field. -/
theorem do_move_refines (s : Scramble.Scramble) (cube : Cube) (hR : Reach cube)
    (hcube : s.sudo_8Scramble_4cube = embedCube cube) (f : Face) (n : Nat)
    (hn : n = 1 ∨ n = 2 ∨ n = 3) (nybble : Nat) (hny : nybble < 16) (block at_ : Int) :
    ∃ s', Scramble.do_move s f.code (Int.ofNat n) (Int.ofNat nybble) block at_ = .ok s' ∧
      s'.sudo_8Scramble_4cube = embedCube (turnsN f n cube) ∧
      Reach (turnsN f n cube) ∧
      s'.sudo_8Scramble_7pending = s.sudo_8Scramble_7pending ∧
      s'.sudo_8Scramble_5total = s.sudo_8Scramble_5total ∧
      s'.sudo_8Scramble_9processed = s.sudo_8Scramble_9processed ∧
      s'.sudo_8Scramble_7version = s.sudo_8Scramble_7version ∧
      s'.sudo_8Scramble_6traced = s.sudo_8Scramble_6traced ∧
      s'.sudo_8Scramble_4done = s.sudo_8Scramble_4done ∧
      (s.sudo_8Scramble_6traced = false →
        s' = { s with sudo_8Scramble_4cube := embedCube (turnsN f n cube) }) := by
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl | rfl <;> decide
  have hnfit : FitsLen (n + 1) := by rcases hn with rfl | rfl | rfl <;> unfold FitsLen i64MaxNat <;> decide
  have hpos : ∀ c ∈ cube, Unit3 c.pos := fun c hc => Reach.pos_unit cube hR hc
  unfold Scramble.do_move
  rw [hcube, apply_turns_refines f n hn1 hnfit cube hpos (Reach.fits26 cube hR), ok_bind]
  have htn : (Int.ofNat n = 1 ∨ Int.ofNat n = 2 ∨ Int.ofNat n = 3) := by
    rcases hn with rfl | rfl | rfl <;> simp
  rw [move_name_refines f (Int.ofNat n) htn, ok_bind, hex_digit_refines nybble hny, ok_bind,
    blank_ok, ok_bind, ok_bind]
  by_cases hquiet : s.sudo_8Scramble_6traced = false
  · have htr' : ({ s with sudo_8Scramble_4cube := embedCube (turnsN f n cube) }).sudo_8Scramble_6traced = false :=
      hquiet
    rw [push_step_digest _ htr']
    exact ⟨{ s with sudo_8Scramble_4cube := embedCube (turnsN f n cube) }, rfl, rfl,
      Reach.after_turns f n cube hR, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · have htr : s.sudo_8Scramble_6traced = true := by
      cases h : s.sudo_8Scramble_6traced <;> simp_all
    have htr' :
        ({ s with sudo_8Scramble_4cube := embedCube (turnsN f n cube) }).sudo_8Scramble_6traced = true := htr
    obtain ⟨_, s', _, hs', hc', hp', ht', hpr', hv', htr'', hd'⟩ :=
      push_step_traced { s with sudo_8Scramble_4cube := embedCube (turnsN f n cube) }
        (turnsN f n cube) rfl (Reach.after_turns f n cube hR) htr'
        (#[109, 111, 118, 101] : Array Int) (moveName f (Int.ofNat n)) #[hexChar nybble]
        (#[] : Array Int) (#[] : Array Int) block at_
    rw [hs']
    exact ⟨s', rfl, hc', Reach.after_turns f n cube hR, hp', ht', hpr', hv', htr'', hd',
      fun hq => by simp [htr] at hq⟩

/-- The cubie at `(1,1,1)` on a reachable cube, and Rule B's two colors. -/
theorem urf_colors (cube : Cube) (h : Reach cube) :
    ∃ j, ∃ (hj : j < cube.length), ∃ up front : Color,
      cube[j].pos = ⟨1, 1, 1⟩ ∧
      (∀ i (hi : i < j), (cube[i]'(by omega)).pos ≠ ⟨1, 1, 1⟩) ∧
      colorFacing cube[j] ax_yp = some up ∧
      colorFacing cube[j] ax_zp = some front ∧
      V3.dot (homeAxis up) (homeAxis front) = 0 ∧
      ruleB cube = rotateTo cube up front := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨g, hg, hc, _⟩ := cubieAt_reach F cube hF _ mem_lattice_111
  have hfind : (cube.find? fun c => decide (c.pos = ⟨1, 1, 1⟩)) =
      some (moveCubie g.app (solvedCubie (g.transpose.app ⟨1, 1, 1⟩))) := by
    simpa [cubieAt] using hc
  have hex := find?_index (fun c => decide (c.pos = ⟨1, 1, 1⟩)) cube _ hfind
  refine Exists.elim hex ?_
  intro j hex
  refine Exists.elim hex ?_
  intro hj rest
  have hjc : cube[j] = moveCubie g.app (solvedCubie (g.transpose.app ⟨1, 1, 1⟩)) := rest.1
  have hfirst : ∀ i (hi : i < j), decide ((cube[i]'(by omega)).pos = ⟨1, 1, 1⟩) = false := rest.2
  have hpos : cube[j].pos = ⟨1, 1, 1⟩ := by
    have := List.find?_some hfind
    simpa [hjc] using this
  have hbefore : ∀ i (hi : i < j), (cube[i]'(by omega)).pos ≠ ⟨1, 1, 1⟩ := by
    intro i hi
    have := hfirst i hi
    simpa using this
  have hk := cornerOK_all g hg
  unfold cornerOK at hk
  revert hk
  cases h1 : colorFacing (solvedCubie (g.transpose.app ⟨1, 1, 1⟩)) (g.transpose.app ⟨0, 1, 0⟩) with
  | none => simp
  | some up =>
    cases h2 : colorFacing (solvedCubie (g.transpose.app ⟨1, 1, 1⟩)) (g.transpose.app ⟨0, 0, 1⟩) with
    | none => simp
    | some front =>
      intro hk
      have hperp : V3.dot (homeAxis up) (homeAxis front) = 0 := by
        simpa [h1, h2, decide_eq_true_eq] using hk
      refine ⟨j, hj, up, front, hpos, hbefore, ?_, ?_, hperp, ?_⟩
      · rw [hjc, show ax_yp = ⟨0, 1, 0⟩ from rfl, colorFacing_rot g hg]; exact h1
      · rw [hjc, show ax_zp = ⟨0, 0, 1⟩ from rfl, colorFacing_rot g hg]; exact h2
      · unfold ruleB
        rw [hc]
        simp only [Option.bind_eq_bind, Option.some_bind, colorFacing_rot g hg, h1, h2,
          Option.some_bind]

/-- `do_rule` on a digest-only reachable state is the model's `ruleB`. -/
theorem do_rule_digest (s : Scramble.Scramble) (cube : Cube) (hR : Reach cube)
    (hcube : s.sudo_8Scramble_4cube = embedCube cube) (htr : s.sudo_8Scramble_6traced = false)
    (block : Int) :
    ∃ cube', Scramble.do_rule s block =
        .ok { s with sudo_8Scramble_4cube := embedCube cube' } ∧
      ruleB cube = some cube' ∧ Reach cube' := by
  obtain ⟨j, hj, up, front, hpos, hbefore, hup, hfront, hperp, hrule⟩ := urf_colors cube hR
  unfold Scramble.do_rule
  rw [hcube, cubie_at_refines cube ⟨1, 1, 1⟩ j hj hpos hbefore (Reach.fits26 cube hR), ok_bind,
    atL_embedCube cube j hj, ok_bind]
  have hyp : (embedC cube[j]).sudo_5Cubie_2yp = up.code := by
    rw [embedC, slot_of_facing _ _ _ hup]
  have hfr : (embedC cube[j]).sudo_5Cubie_2zp = front.code := by
    rw [embedC, slot_of_facing _ _ _ hfront]
  dsimp only
  rw [hyp, hfr]
  obtain ⟨cube', hr, hrot, hReach⟩ := reorient_refines cube hR up front hperp
  rw [hr, ok_bind, blank_ok, ok_bind, ok_bind, letter_refines up, ok_bind, letter_refines front,
    ok_bind]
  have htr' : ({ s with sudo_8Scramble_4cube := embedCube cube' }).sudo_8Scramble_6traced = false := htr
  rw [push_step_digest _ htr']
  refine ⟨cube', rfl, ?_, hReach⟩
  rw [hrule, hrot]

theorem v2_faces (n : Nat) (hn : n < 16) :
    SudoRt.atL Scramble.v2_a (Int.ofNat n) = .ok (v2Turns n).1.code ∧
    SudoRt.atL Scramble.v2_b (Int.ofNat n) = .ok (v2Turns n).2.code := by
  have hall : ∀ n ∈ List.range 16,
      SudoRt.atL Scramble.v2_a (Int.ofNat n) = .ok (v2Turns n).1.code ∧
      SudoRt.atL Scramble.v2_b (Int.ofNat n) = .ok (v2Turns n).2.code := by
    decide
  exact hall n (List.mem_range.mpr hn)

/-- One v2 symbol on a digest-only reachable state is the model's `symbolV2`. -/
theorem apply_v2_symbol_digest (s : Scramble.Scramble) (cube : Cube) (hR : Reach cube)
    (hcube : s.sudo_8Scramble_4cube = embedCube cube) (htr : s.sudo_8Scramble_6traced = false)
    (n : Nat) (hn : n < 16) (block : Int) :
    ∃ cube', Scramble.apply_v2_symbol s (Int.ofNat n) block =
        .ok { s with sudo_8Scramble_4cube := embedCube cube' } ∧
      symbolV2 cube n = some cube' ∧ Reach cube' := by
  unfold Scramble.apply_v2_symbol symbolV2
  obtain ⟨ha, hb⟩ := v2_faces n hn
  rw [ha, ok_bind]
  have hturn : (1 : Nat) = 1 ∨ (1 : Nat) = 2 ∨ (1 : Nat) = 3 := by simp
  obtain ⟨s1, hs1, hc1, r1, _, _, _, _, htr1, _, hq1⟩ :=
    do_move_refines s cube hR hcube (v2Turns n).1 1 hturn n hn block 0
  rw [show (1 : Int) = Int.ofNat 1 from rfl, hs1]
  have hs1' := hq1 htr
  rw [hb, ok_bind]
  obtain ⟨s2, hs2, hc2, r2, _, _, _, _, htr2, _, hq2⟩ :=
    do_move_refines s1 (turnsN (v2Turns n).1 1 cube) r1 hc1 (v2Turns n).2 1 hturn n hn block
      (Int.ofNat 1)
  dsimp only
  rw [ok_bind, hs2]
  have htr_s1 : s1.sudo_8Scramble_6traced = false := by rw [hs1']; exact htr
  have hs2' := hq2 htr_s1
  have htr_s2 : s2.sudo_8Scramble_6traced = false := by rw [hs2']; exact htr_s1
  obtain ⟨cube', hd, hrule, r3⟩ :=
    do_rule_digest s2 (turnsN (v2Turns n).2 1 (turnsN (v2Turns n).1 1 cube)) r2 hc2 htr_s2 block
  rw [ok_bind, hd]
  refine ⟨cube', ?_, ?_, r3⟩
  · rw [hs2', hs1']
    simp [turns_one]
  · rw [turns_one, turns_one] at hrule
    simp [hrule]

end ScrambleV2.Link2
