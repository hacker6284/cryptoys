/-
  LINK 2. The digest path end to end, for the digest-only v2 state (`traced = false`):
  `pad`, `apply_ready`, `update`, `finish`, `evaluate`, and the headline
  `scramble_v2_digest_refines_digestV2` (a byte message through `scramble_v2_digest`,
  `update`, `evaluate` returns `.ok` with digest `embed (digestV2 msg)`).

  Scope: digest equality only. The trace, the traced constructor `scramble_v2`, and v1
  (`version = 1`) are not claimed. States are written out field by field
  (`Scramble.Scramble.mk version pending total processed cube steps traced done`), so each
  statement says exactly which fields change. Proof-only. No algorithm change.
-/
import ScrambleV2.Link2.State
import ScrambleV2.Link2.Index

namespace ScrambleV2.Link2
open MegaDreifach.Link2

/-- What `pad` appends to a v2 tape when `total = t`: the marker `8`, then the cycle up to
    12 nybbles. -/
def padTailV2 (t : Nat) : List Nat := 8 :: tapeI (12 - (t + 1))

theorem narrowI_in (n : Int) (h1 : SudoRt.i64Min ≤ n) (h2 : n ≤ SudoRt.i64Max) :
    SudoRt.narrowI n = .ok n := by
  unfold SudoRt.narrowI
  have a : ¬ n < SudoRt.i64Min := Int.not_lt.mpr h1
  have b : ¬ n > SudoRt.i64Max := Int.not_lt.mpr h2
  simp [a, b]

theorem tape_i_at (j : Nat) (hj : j < 4) :
    SudoRt.atL Scramble.tape_i (Int.ofNat j) = .ok (Int.ofNat ([6, 0, 7, 1].getD j 0)) := by
  have hall : ∀ j ∈ List.range 4,
      SudoRt.atL Scramble.tape_i (Int.ofNat j) = .ok (Int.ofNat ([6, 0, 7, 1].getD j 0)) := by
    decide
  exact hall j (List.mem_range.mpr hj)

theorem push_append_embed (a : Array Int) (x : Nat) (l : List Nat) :
    (a ++ embed l).push (Int.ofNat x) = a ++ embed (l ++ [x]) := by
  apply Array.ext'; simp [embed]

theorem append_embed_cons (a : Array Int) (x : Nat) (l : List Nat) :
    a ++ embed (x :: l) = a.push (Int.ofNat x) ++ embed l := by
  apply Array.ext'; simp [embed]

theorem tapeI_succ (i : Nat) : tapeI (i + 1) = tapeI i ++ [[6, 0, 7, 1].getD (i % 4) 0] := by
  simp [tapeI, List.range_succ]

/-- `pad` on a v2 state with `total = t` appends `padTailV2 t` to `pending`; nothing else
    changes. -/
theorem pad_v2 (pend : Array Int) (t : Nat) (proc : Int) (cb : Array Scramble.Cubie)
    (st : Array Scramble.Step) (tr dn : Bool) (ht : FitsLen (t + 1)) :
    Scramble.pad (Scramble.Scramble.mk 2 pend (Int.ofNat t) proc cb st tr dn) =
      .ok (Scramble.Scramble.mk 2 (pend ++ embed (padTailV2 t)) (Int.ofNat t) proc cb st tr dn) := by
  unfold Scramble.pad
  simp only [addI_ofNat_one t ht, ok_bind, appendL_spec,
    show SudoRt.SEq.beq (2 : Int) (1 : Int) = false from rfl, Bool.false_eq_true, if_false,
    fuelRange_eq, bind_pure_right]
  by_cases hs : t + 1 < 12
  · rw [show (12 : Int) = Int.ofNat 12 from rfl,
      subI_ofNat 12 (t + 1) (fits_small (by omega)) (by omega), ok_bind,
      subI_ofNat_one (12 - (t + 1)) (by omega) (fits_small (by omega)), ok_bind]
    refine chain_eq _ _ _ (fun i => Scramble.Scramble.mk 2 (pend.push 8 ++ embed (tapeI i))
        (Int.ofNat t) proc cb st tr dn) 0 (12 - (t + 1) - 1) (Nat.zero_le _) ?_ _ ?_ _ ?_
    · intro i _ hi
      dsimp only
      rw [if_neg (ofNat_not_gt hi)]
      have hm : SudoRt.modI (Int.ofNat i) 4 = .ok (Int.ofNat (i % 4)) :=
        modI_ofNat i (b := 4) (by decide)
      simp only [hm, ok_bind,
        tape_i_at (i % 4) (Nat.mod_lt _ (by decide)), pure_eq_ok]
      rw [push_append_embed, ← tapeI_succ, asc_tail _ i (fits_small (by omega))]
    · dsimp only
      rw [show 12 - (t + 1) - 1 + 1 = 12 - (t + 1) by omega, padTailV2, append_embed_cons]
      rfl
    · apply congrArg (Scramble.Scramble.mk 2 · (Int.ofNat t) proc cb st tr dn)
      apply Array.ext'; simp [embed, tapeI]
  · have hsub : SudoRt.subI 12 (Int.ofNat (t + 1)) = .ok (12 - Int.ofNat (t + 1)) := by
      unfold SudoRt.subI
      apply narrowI_in <;> unfold FitsLen i64MaxNat at ht <;>
        simp only [SudoRt.i64Min, SudoRt.i64Max, Int.ofNat_eq_coe] <;> omega
    have hsub1 : SudoRt.subI (12 - Int.ofNat (t + 1)) 1 = .ok (12 - Int.ofNat (t + 1) - 1) := by
      unfold SudoRt.subI
      apply narrowI_in <;> unfold FitsLen i64MaxNat at ht <;>
        simp only [SudoRt.i64Min, SudoRt.i64Max, Int.ofNat_eq_coe] <;> omega
    have hgt : (0 : Int) > 12 - Int.ofNat (t + 1) - 1 := by
      simp only [Int.ofNat_eq_coe]; omega
    rw [hsub, ok_bind, hsub1, ok_bind,
      asc_break (0 : Int) _ _ _ _ _ hgt (by rw [if_pos hgt]; rfl)]
    have h0 : 12 - (t + 1) = 0 := by omega
    rw [padTailV2, h0, append_embed_cons]
    rfl

theorem walkV2_append (cube : Cube) (a b : List Nat) :
    walkV2 cube (a ++ b) = walkV2 cube a >>= fun c => walkV2 c b := by
  unfold walkV2; rw [List.foldlM_append]

theorem walkV2_take_succ (cube : Cube) (ny : List Nat) (i : Nat) (hi : i < ny.length) :
    walkV2 cube (ny.take (i + 1)) = walkV2 cube (ny.take i) >>= fun c => symbolV2 c ny[i] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi, walkV2_append]
  simp [walkV2]

theorem apply_ready_v2_digest (v tot proc : Int) (st : Array Scramble.Step) (dn : Bool) (cube : Cube)
    (hR : Reach cube) (hv : v = 2) (ny : List Nat) (hny : ∀ x ∈ ny, x < 16) (p : Nat)
    (hp : proc = Int.ofNat p) (hfit : FitsLen (p + ny.length)) :
    ∃ cube', Scramble.apply_ready
        { sudo_8Scramble_7version := v, sudo_8Scramble_7pending := embed ny,
          sudo_8Scramble_5total := tot, sudo_8Scramble_9processed := proc,
          sudo_8Scramble_4cube := embedCube cube, sudo_8Scramble_5steps := st,
          sudo_8Scramble_6traced := false, sudo_8Scramble_4done := dn } =
      .ok {
            sudo_8Scramble_7version := v, sudo_8Scramble_7pending := (#[] : Array Int),
            sudo_8Scramble_5total := tot, sudo_8Scramble_9processed := Int.ofNat (p + ny.length),
            sudo_8Scramble_4cube := embedCube cube', sudo_8Scramble_5steps := st,
            sudo_8Scramble_6traced := false, sudo_8Scramble_4done := dn } ∧
      walkV2 cube ny = some cube' ∧ Reach cube' := by
  subst hv hp
  unfold Scramble.apply_ready
  simp only [show SudoRt.SEq.beq (2 : Int) (1 : Int) = false from rfl, Bool.false_eq_true,
    if_false, listLen_embed, fuelRange_eq, bind_pure_right]
  rcases Nat.eq_zero_or_pos ny.length with h0 | hpos
  · have hnil : ny = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    rw [show Int.ofNat ([] : List Nat).length = (0 : Int) from rfl, subI_zero_one, ok_bind,
      asc_break (0 : Int) (-1 : Int) _ _ _ _ (by decide) (by rw [if_pos (show (0 : Int) > -1 by decide)]; rfl)]
    exact ⟨cube, rfl, rfl, hR⟩
  · have hfl : FitsLen ny.length := FitsLen.of_le hfit (by omega)
    rw [subI_ofNat_one _ hpos hfl, ok_bind]
    refine chain_inv _ _ _ (fun i (σs : Scramble.Scramble) => ∃ c, σs = Scramble.Scramble.mk
          2 (embed ny) tot (Int.ofNat (p + i)) (embedCube c) st false dn ∧
        walkV2 cube (ny.take i) = some c ∧ Reach c) 0 (ny.length - 1) (Nat.zero_le _) ?_
      (fun (r : Except SudoRt.Trap Scramble.Scramble) => ∃ c, r = .ok (Scramble.Scramble.mk
            2 #[] tot (Int.ofNat (p + ny.length)) (embedCube c) st false dn) ∧
        walkV2 cube ny = some c ∧ Reach c) ?_ _ ⟨cube, rfl, rfl, hR⟩
    · rintro i σs - hi ⟨c, rfl, hw, hr⟩
      have hil : i < ny.length := by omega
      obtain ⟨c', hs, hsym, hr'⟩ := apply_v2_symbol_digest
        { sudo_8Scramble_7version := 2, sudo_8Scramble_7pending := embed ny,
          sudo_8Scramble_5total := tot, sudo_8Scramble_9processed := Int.ofNat (p + i),
          sudo_8Scramble_4cube := embedCube c, sudo_8Scramble_5steps := st,
          sudo_8Scramble_6traced := false, sudo_8Scramble_4done := dn }
        c hr rfl rfl ny[i] (hny _ (List.getElem_mem hil)) (Int.ofNat (p + i))
      refine ⟨_, ⟨c', rfl, by rw [walkV2_take_succ _ _ _ hil, hw]; exact hsym, hr'⟩, ?_⟩
      dsimp only
      rw [if_neg (ofNat_not_gt hi)]
      simp only [atL_embed ny i hil, ok_bind]
      rw [hs, ok_bind]
      dsimp only
      rw [addI_ofNat_one (p + i) (FitsLen.of_le hfit (by omega))]
      simp only [ok_bind, pure_eq_ok]
      rw [asc_tail _ i (FitsLen.of_le hfl (by omega))]
      rfl
    · rintro σs ⟨c, rfl, hw, hr⟩
      have e : ny.length - 1 + 1 = ny.length := by omega
      rw [e, List.take_length] at hw
      refine ⟨c, ?_, hw, hr⟩
      simp only [e]
      rfl


theorem nybbles_length (msg : List Nat) : (nybbles msg).length = 2 * msg.length := by
  induction msg with
  | nil => rfl
  | cons b t ih => simp [nybbles, List.flatMap_cons] at ih ⊢; omega

theorem nybbles_take_succ (msg : List Nat) (i : Nat) (hi : i < msg.length) :
    nybbles (msg.take (i + 1)) = nybbles (msg.take i) ++ [msg[i] / 16, msg[i] % 16] := by
  rw [List.take_succ, List.getElem?_eq_getElem hi]
  simp [nybbles, List.flatMap_append]

theorem nybbles_lt (msg : List Nat) (hb : ∀ b ∈ msg, b ≤ 255) : ∀ x ∈ nybbles msg, x < 16 := by
  intro x hx
  simp only [nybbles, List.mem_flatMap, List.mem_cons, List.mem_singleton] at hx
  obtain ⟨b, hbm, hx | hx | hx⟩ := hx
  · have := hb b hbm; omega
  · subst hx; exact Nat.mod_lt _ (by decide)
  · simp at hx

theorem embed_push (l : List Nat) (x : Nat) : (embed l).push (Int.ofNat x) = embed (l ++ [x]) := by
  apply Array.ext'; simp [embed]

/-- `update` on a digest-only v2 state (not done) with a byte message: it appends the
    message's nybbles to `pending` and walks all of `pending` (the model's `walkV2`), leaving
    `pending` empty; `total` and `processed` grow by the nybble count. -/
theorem update_v2_digest (ny : List Nat) (hny : ∀ x ∈ ny, x < 16) (t p : Nat) (cube : Cube)
    (hR : Reach cube) (st : Array Scramble.Step) (msg : List Nat) (hb : ∀ b ∈ msg, b ≤ 255)
    (hfitP : FitsLen (p + ny.length + 2 * msg.length)) (hfitT : FitsLen (t + 2 * msg.length)) :
    ∃ cube', Scramble.update
        (Scramble.Scramble.mk 2 (embed ny) (Int.ofNat t) (Int.ofNat p) (embedCube cube) st false
          false) (embed msg) =
      .ok (Scramble.Scramble.mk 2 #[] (Int.ofNat (t + 2 * msg.length))
          (Int.ofNat (p + ny.length + 2 * msg.length)) (embedCube cube') st false false) ∧
      walkV2 cube (ny ++ nybbles msg) = some cube' ∧ Reach cube' := by
  have hny' : ∀ x ∈ ny ++ nybbles msg, x < 16 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hny x h
    · exact nybbles_lt msg hb x h
  have hlen : (ny ++ nybbles msg).length = ny.length + 2 * msg.length := by
    rw [List.length_append, nybbles_length]
  obtain ⟨c', hc', hw, hr⟩ := apply_ready_v2_digest 2 (Int.ofNat (t + 2 * msg.length)) (Int.ofNat p) st
    false cube hR rfl (ny ++ nybbles msg) hny' p rfl (by rw [hlen, ← Nat.add_assoc]; exact hfitP)
  rw [hlen, ← Nat.add_assoc] at hc'
  refine ⟨c', ?_, hw, hr⟩
  have hmul : SudoRt.mulI 2 (Int.ofNat msg.length) = .ok (Int.ofNat (2 * msg.length)) :=
    mulI_ofNat 2 msg.length (FitsLen.of_le hfitT (by omega))
  unfold Scramble.update
  simp only [show (!false) = true from rfl, sudoAssert_true, ok_bind, listLen_embed, fuelRange_eq,
    bind_pure_right, appendL_spec]
  have htot : SudoRt.addI (Int.ofNat t) (Int.ofNat (2 * msg.length)) =
      .ok (Int.ofNat (t + 2 * msg.length)) := addI_ofNat t _ hfitT
  rcases Nat.eq_zero_or_pos msg.length with h0 | hpos
  · have hnil : msg = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    rw [show Int.ofNat ([] : List Nat).length = (0 : Int) from rfl, subI_zero_one, ok_bind,
      idx_break (0 : Int) (-1 : Int) _ _ _ (by decide)
        (by rw [if_pos (show (0 : Int) > -1 by decide)]; rfl)]
    rw [ok_bind,
      asc_break (0 : Int) (-1 : Int) _ _ _ _ (by decide)
        (by rw [if_pos (show (0 : Int) > -1 by decide)]; rfl)]
    dsimp only
    have hmul0 : SudoRt.mulI 2 0 = .ok 0 := rfl
    have htot0 : SudoRt.addI (Int.ofNat t) 0 = .ok (Int.ofNat t) :=
      addI_ofNat t 0 (by simpa using hfitT)
    rw [hmul0, ok_bind, htot0, ok_bind]
    simpa [nybbles] using hc'
  · have hfl : FitsLen msg.length := FitsLen.of_le hfitT (by omega)
    rw [subI_ofNat_one _ hpos hfl, ok_bind]
    refine chain_idx _ _ _ 0 (msg.length - 1) (Nat.zero_le _) ?_ _ ?_
    · intro i _ hi
      have hil : i < msg.length := by omega
      rw [if_neg (ofNat_not_gt hi)]
      simp only [atL_embed msg i hil, ok_bind]
      have hnn : decide (Int.ofNat msg[i] ≥ (0 : Int)) = true := by
        rw [decide_eq_true_eq]; exact Int.ofNat_zero_le _
      have hle : decide (Int.ofNat msg[i] ≤ (255 : Int)) = true := by
        rw [decide_eq_true_eq]; exact Int.ofNat_le.mpr (hb _ (List.getElem_mem hil))
      simp only [hnn, hle, if_true, pure_eq_ok, ok_bind, sudoAssert_true]
      rw [asc_tail_idx _ i (FitsLen.of_le hfl (by omega))]
    · rw [ok_bind]
      refine chain_eq _ _ _ (fun i => Scramble.Scramble.mk 2 (embed (ny ++ nybbles (msg.take i)))
          (Int.ofNat t) (Int.ofNat p) (embedCube cube) st false false) 0 (msg.length - 1)
          (Nat.zero_le _) ?_ _ ?_ _ (by simp [nybbles])
      · intro i _ hi
        have hil : i < msg.length := by omega
        dsimp only
        rw [if_neg (ofNat_not_gt hi)]
        have hd : SudoRt.divI (Int.ofNat msg[i]) 16 = .ok (Int.ofNat (msg[i] / 16)) :=
          divI_ofNat _ (b := 16) (by decide)
        have hm : SudoRt.modI (Int.ofNat msg[i]) 16 = .ok (Int.ofNat (msg[i] % 16)) :=
          modI_ofNat _ (b := 16) (by decide)
        simp only [atL_embed msg i hil, ok_bind, hd, hm, pure_eq_ok]
        rw [embed_push, embed_push, List.append_assoc, List.append_assoc, List.singleton_append,
          ← nybbles_take_succ msg i hil, asc_tail _ i (FitsLen.of_le hfl (by omega))]
      · dsimp only
        rw [show msg.length - 1 + 1 = msg.length by omega, List.take_length, hmul, ok_bind, htot,
          ok_bind]
        exact hc'

theorem apply_turns_two (f : Face) (cube : Cube) (hR : Reach cube) :
    Scramble.apply_turns (embedCube cube) f.code (2 : Int) = .ok (embedCube (turnsN f 2 cube)) :=
  apply_turns_refines f 2 (by decide) (by unfold FitsLen i64MaxNat; decide) cube
    (fun _ hc => Reach.pos_unit cube hR hc) (Reach.fits26 cube hR)

/-- `finish` on a digest-only reachable state is the model's `seat` (closer `F2 B2`, then
    Rule B with `up = W`, `front = G`), and sets `done`. -/
theorem finish_digest (s : Scramble.Scramble) (cube : Cube) (hR : Reach cube)
    (hcube : s.sudo_8Scramble_4cube = embedCube cube) (htr : s.sudo_8Scramble_6traced = false) :
    ∃ cube', Scramble.finish s =
        .ok { s with sudo_8Scramble_4cube := embedCube cube', sudo_8Scramble_4done := true } ∧
      seat cube = some cube' ∧ Reach cube' := by
  have r1 := Reach.after_turns .F 2 cube hR
  have r2 := Reach.after_turns .B 2 _ r1
  obtain ⟨c3, h3, hrot, r3⟩ := reorient_refines _ r2 .W .G (by decide)
  have hF : Scramble.apply_turns (embedCube cube) 4 2 = .ok (embedCube (turnsN .F 2 cube)) :=
    apply_turns_two .F cube hR
  have hB : Scramble.apply_turns (embedCube (turnsN .F 2 cube)) 5 2 =
      .ok (embedCube (turnsN .B 2 (turnsN .F 2 cube))) := apply_turns_two .B _ r1
  have hW : Scramble.reorient (embedCube (turnsN .B 2 (turnsN .F 2 cube))) 1 6 =
      .ok (embedCube c3) := h3
  unfold Scramble.finish
  simp only [hcube, hF, blank_ok, ok_bind]
  rw [push_step_digest { s with sudo_8Scramble_4cube := embedCube (turnsN .F 2 cube) } htr, ok_bind]
  dsimp only
  rw [hB, ok_bind,
    push_step_digest { s with sudo_8Scramble_4cube := embedCube (turnsN .B 2 (turnsN .F 2 cube)) } htr,
    ok_bind]
  dsimp only
  rw [hW, ok_bind, push_step_digest { s with sudo_8Scramble_4cube := embedCube c3 } htr, ok_bind]
  exact ⟨c3, rfl, hrot, r3⟩

theorem padTailV2_lt (t : Nat) : ∀ x ∈ padTailV2 t, x < 16 := by
  intro x hx
  simp only [padTailV2, tapeI, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨k, -, rfl⟩
  · decide
  · have hk : k % 4 < 4 := Nat.mod_lt _ (by decide)
    generalize k % 4 = j at hk ⊢
    rcases j with _ | _ | _ | _ | j
    all_goals first | decide | omega

theorem padTailV2_length (t : Nat) : (padTailV2 t).length ≤ 12 := by
  simp only [padTailV2, tapeI, List.length_cons, List.length_map, List.length_range]; omega

theorem padV2_eq (ny : List Nat) : padV2 ny = ny ++ padTailV2 ny.length := by
  simp [padV2, padTailV2, tapeI]

/-- `evaluate` on a digest-only v2 state (not done) with `total = t`: `pad`, `apply_ready`,
    `finish`, `index_bytes` return `.ok`, and the digest is the model's `digestOf` after
    walking `pending ++ padTailV2 t` and seating. -/
theorem evaluate_v2_digest (ny : List Nat) (hny : ∀ x ∈ ny, x < 16) (t p : Nat) (cube : Cube)
    (hR : Reach cube) (st : Array Scramble.Step) (ht : FitsLen (t + 1))
    (hp : FitsLen (p + ny.length + 12)) :
    ∃ ev s' d, Scramble.evaluate
        (Scramble.Scramble.mk 2 (embed ny) (Int.ofNat t) (Int.ofNat p) (embedCube cube) st false
          false) = .ok (ev, s') ∧
      (walkV2 cube (ny ++ padTailV2 t) >>= seat >>= ScrambleV2.digestOf) = some d ∧
      ev.sudo_10Evaluation_6digest = embed d := by
  have hny' : ∀ x ∈ ny ++ padTailV2 t, x < 16 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hny x h
    · exact padTailV2_lt t x h
  have hfit : FitsLen (p + (ny ++ padTailV2 t).length) :=
    FitsLen.of_le hp (by rw [List.length_append]; have := padTailV2_length t; omega)
  obtain ⟨c1, h1, hw, r1⟩ := apply_ready_v2_digest 2 (Int.ofNat t) (Int.ofNat p) st false cube hR rfl
    (ny ++ padTailV2 t) hny' p rfl hfit
  obtain ⟨c2, h2, hseat, r2⟩ := finish_digest (Scramble.Scramble.mk 2 #[] (Int.ofNat t)
    (Int.ofNat (p + (ny ++ padTailV2 t).length)) (embedCube c1) st false false) c1 r1 rfl rfl
  obtain ⟨d, hd, hidx⟩ := Reach.index_bytes c2 r2
  refine ⟨⟨embed d, st⟩, Scramble.Scramble.mk 2 #[] (Int.ofNat t)
    (Int.ofNat (p + (ny ++ padTailV2 t).length)) (embedCube c2) st false true, d, ?_,
    by simp [hw, hseat, hd], rfl⟩
  unfold Scramble.evaluate
  simp only [show (!false) = true from rfl, sudoAssert_true, ok_bind]
  rw [pad_v2 (embed ny) t _ _ _ false false ht, ok_bind, ← embed_append, h1, ok_bind, h2, ok_bind]
  dsimp only
  rw [hidx]
  rfl

/-- LINK 2 headline (digest only). For a byte message whose length leaves room in `i64`
    (`2·len + 12` fits), the digest-only constructor `scramble_v2_digest`, then `update`,
    then `evaluate` all return `.ok`, and the evaluation's digest is the model's
    `digestV2 msg`. The trace (and the traced constructor `scramble_v2`) is not part of the
    claim. -/
theorem scramble_v2_digest_refines_digestV2 (msg : List Nat) (hb : ∀ b ∈ msg, b ≤ 255)
    (hlen : FitsLen (2 * msg.length + 12)) :
    ∃ s0 s1 ev s2, Scramble.scramble_v2_digest = .ok s0 ∧
      Scramble.update s0 (embed msg) = .ok s1 ∧
      Scramble.evaluate s1 = .ok (ev, s2) ∧
      ev.sudo_10Evaluation_6digest = embed (digestV2 msg) := by
  obtain ⟨c1, hu, hw1, r1⟩ := update_v2_digest [] (by simp) 0 0 solvedCube ⟨_, reach_solved⟩ #[] msg hb
    (FitsLen.of_le hlen (by simp)) (FitsLen.of_le hlen (by simp))
  obtain ⟨ev, s2, d, he, hd, hdig⟩ := evaluate_v2_digest [] (by simp) (0 + 2 * msg.length)
    (0 + [].length + 2 * msg.length) c1 r1 #[] (FitsLen.of_le hlen (by simp))
    (FitsLen.of_le hlen (by simp))
  refine ⟨_, _, ev, s2, ?_, hu, he, ?_⟩
  · rw [scramble_v2_digest_refines, fresh_refines]
    rfl
  · rw [hdig]
    congr 1
    have hv : digestV2? msg = some d := by
      unfold digestV2?
      rw [padV2_eq, walkV2_append, nybbles_length]
      simp only [List.nil_append] at hw1
      simp only [List.nil_append, Nat.zero_add] at hd
      simpa [hw1, Option.bind_assoc] using hd
    simp [digestV2, hv]

end ScrambleV2.Link2
