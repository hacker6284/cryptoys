/-
  LINK 2. The v2 path for a traced or digest-only state (`traced` either value), the trace
  it returns, and several `update` calls in a row.

  Trace scope. `Emits tr x tags`: on a traced state the appended steps have exactly the
  given kind, move token, nybble digit, block and index (`Tag`, in the emitted text codes;
  SPEC "Trace"), in order, and each facelet string is 54 color letters; on a digest-only
  state nothing is appended. Not claimed: the `up` / `front` letters of Rule B steps and
  which letters the facelet strings hold. Proof-only. No algorithm change.
-/
import ScrambleV2.Link2.Evaluate

namespace ScrambleV2.Link2
open MegaDreifach.Link2

/-- The fields of a trace step this package claims: kind, move token, nybble digit, block,
    index (all as the emitted text codes). `up`, `front` are not claimed; the facelet
    string is only claimed to be 54 color letters (`Faces54`). -/
abbrev Tag := Array Int × Array Int × Array Int × Int × Int

def stepTag (y : Scramble.Step) : Tag :=
  (y.sudo_4Step_4kind, y.sudo_4Step_4move, y.sudo_4Step_6nybble, y.sudo_4Step_5block,
    y.sudo_4Step_5index)

def Faces54 (y : Scramble.Step) : Prop :=
  ∃ cols : List Color, cols.length = 54 ∧ y.sudo_4Step_8facelets = Array.mk (cols.map Color.letter)

/-- The steps `x` a call appends: on a traced state, steps with exactly these tags (in
    order) and 54-letter facelet strings; on a digest-only state, none. -/
def Emits : Bool → Array Scramble.Step → List Tag → Prop
  | true, x, tags => x.toList.map stepTag = tags ∧ ∀ y ∈ x.toList, Faces54 y
  | false, x, _ => x = #[]

theorem Emits.nil (tr : Bool) : Emits tr #[] [] := by cases tr <;> simp [Emits]

theorem Emits.append {tr : Bool} {x y : Array Scramble.Step} {t1 t2 : List Tag}
    (h1 : Emits tr x t1) (h2 : Emits tr y t2) : Emits tr (x ++ y) (t1 ++ t2) := by
  cases tr
  · simp only [Emits] at *; subst h1 h2; rfl
  · simp only [Emits] at *
    obtain ⟨a1, b1⟩ := h1
    obtain ⟨a2, b2⟩ := h2
    refine ⟨by simp [a1, a2], ?_⟩
    intro y hy
    simp only [Array.toList_append, List.mem_append] at hy
    rcases hy with hy | hy
    · exact b1 y hy
    · exact b2 y hy

/-- On a traced state the emitted trace has exactly `tags.length` steps. -/
theorem Emits.size {x : Array Scramble.Step} {tags : List Tag} (h : Emits true x tags) :
    x.size = tags.length := by
  obtain ⟨h, _⟩ := h
  rw [← h, List.length_map, Array.length_toList]

/-- Kind codes: `move`, `ruleB`, `closer`, `canonicalize`. -/
def kMove : Array Int := #[109, 111, 118, 101]
def kRule : Array Int := #[114, 117, 108, 101, 66]
def kCloser : Array Int := #[99, 108, 111, 115, 101, 114]
def kCanon : Array Int := #[99, 97, 110, 111, 110, 105, 99, 97, 108, 105, 122, 101]

def moveTag (f : Face) (n nyb : Nat) (block at_ : Int) : Tag :=
  (kMove, moveName f (Int.ofNat n), #[hexChar nyb], block, at_)

def ruleTag (block : Int) : Tag := (kRule, #[], #[], block, 0)

/-- SPEC "Trace": the closer `F2`, `B2`, then the seat. -/
def closerTags : List Tag :=
  [(kCloser, #[70, 50], #[], 0, 0), (kCloser, #[66, 50], #[], 0, 0), (kCanon, #[], #[], 0, 0)]

/-- One v2 symbol: its two turns (index 0 and 1), then Rule B, all in block `block`. -/
def symTagsV2 (n : Nat) (block : Int) : List Tag :=
  [moveTag (v2Turns n).1 1 n block 0, moveTag (v2Turns n).2 1 n block 1, ruleTag block]

/-- A v2 tape walked from block `p` on. -/
def tapeTagsV2 : Nat → List Nat → List Tag
  | _, [] => []
  | p, n :: ny => symTagsV2 n (Int.ofNat p) ++ tapeTagsV2 (p + 1) ny

theorem tapeTagsV2_append (p : Nat) (a b : List Nat) :
    tapeTagsV2 p (a ++ b) = tapeTagsV2 p a ++ tapeTagsV2 (p + a.length) b := by
  induction a generalizing p with
  | nil => rfl
  | cons n a ih =>
    show symTagsV2 n (Int.ofNat p) ++ tapeTagsV2 (p + 1) (a ++ b) =
      symTagsV2 n (Int.ofNat p) ++ tapeTagsV2 (p + 1) a ++ tapeTagsV2 (p + (a.length + 1)) b
    rw [ih, List.append_assoc, Nat.add_assoc, Nat.add_comm 1 a.length]

theorem tapeTagsV2_length (p : Nat) (ny : List Nat) : (tapeTagsV2 p ny).length = 3 * ny.length := by
  induction ny generalizing p with
  | nil => rfl
  | cons n ny ih => simp only [tapeTagsV2, List.length_append, ih, symTagsV2]; simp; omega

theorem push_step_gen (v : Int) (pend : Array Int) (tot proc : Int) (cube : Cube) (hR : Reach cube)
    (st : Array Scramble.Step) (tr dn : Bool) (kind move nybble up front : Array Int)
    (block at_ : Int) :
    ∃ x, Emits tr x [(kind, move, nybble, block, at_)] ∧
      Scramble.push_step (Scramble.Scramble.mk v pend tot proc (embedCube cube) st tr dn)
          kind move nybble block at_ up front =
        .ok (Scramble.Scramble.mk v pend tot proc (embedCube cube) (st ++ x) tr dn) := by
  cases tr
  · refine ⟨#[], rfl, ?_⟩
    unfold Scramble.push_step
    simp [pure_eq_ok]
  · obtain ⟨cols, hlen, hf⟩ := Reach.facelets_of cube hR
    refine ⟨#[Scramble.Step.mk kind move nybble block at_ up front (Array.mk (cols.map Color.letter))],
      ⟨rfl, ?_⟩, ?_⟩
    · intro y hy
      simp only [List.mem_singleton, Array.toList_toArray] at hy
      subst hy
      exact ⟨cols, hlen, rfl⟩
    · unfold Scramble.push_step
      simp only [if_true]
      rw [hf, ok_bind, appendL_spec, pure_eq_ok]
      rfl

theorem do_move_gen (v : Int) (pend : Array Int) (tot proc : Int) (cube : Cube) (hR : Reach cube)
    (st : Array Scramble.Step) (tr dn : Bool) (f : Face) (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 3)
    (nyb : Nat) (hny : nyb < 16) (block at_ : Int) :
    ∃ x, Emits tr x [moveTag f n nyb block at_] ∧
      Scramble.do_move (Scramble.Scramble.mk v pend tot proc (embedCube cube) st tr dn) f.code
          (Int.ofNat n) (Int.ofNat nyb) block at_ =
        .ok (Scramble.Scramble.mk v pend tot proc (embedCube (turnsN f n cube)) (st ++ x) tr dn) ∧
      Reach (turnsN f n cube) := by
  have hn1 : 1 ≤ n := by rcases hn with rfl | rfl | rfl <;> decide
  have hnfit : FitsLen (n + 1) := by
    rcases hn with rfl | rfl | rfl <;> unfold FitsLen i64MaxNat <;> decide
  have hpos : ∀ c ∈ cube, Unit3 c.pos := fun c hc => Reach.pos_unit cube hR hc
  have hR' := Reach.after_turns f n cube hR
  have htn : (Int.ofNat n = 1 ∨ Int.ofNat n = 2 ∨ Int.ofNat n = 3) := by
    rcases hn with rfl | rfl | rfl <;> simp
  obtain ⟨x, hx, hps⟩ := push_step_gen v pend tot proc (turnsN f n cube) hR' st tr dn kMove
    (moveName f (Int.ofNat n)) #[hexChar nyb] #[] #[] block at_
  refine ⟨x, hx, ?_, hR'⟩
  unfold Scramble.do_move
  simp only [apply_turns_refines f n hn1 hnfit cube hpos (Reach.fits26 cube hR), ok_bind,
    move_name_refines f (Int.ofNat n) htn, hex_digit_refines nyb hny, blank_ok]
  exact (bind_ok_of hps _).trans rfl

theorem do_rule_gen (v : Int) (pend : Array Int) (tot proc : Int) (cube : Cube) (hR : Reach cube)
    (st : Array Scramble.Step) (tr dn : Bool) (block : Int) :
    ∃ x cube', Emits tr x [ruleTag block] ∧
      Scramble.do_rule (Scramble.Scramble.mk v pend tot proc (embedCube cube) st tr dn) block =
        .ok (Scramble.Scramble.mk v pend tot proc (embedCube cube') (st ++ x) tr dn) ∧
      ruleB cube = some cube' ∧ Reach cube' := by
  obtain ⟨j, hj, up, front, hpos, hbefore, hup, hfront, hperp, hrule⟩ := urf_colors cube hR
  obtain ⟨cube', hr, hrot, hReach⟩ := reorient_refines cube hR up front hperp
  obtain ⟨x, hx, hps⟩ := push_step_gen v pend tot proc cube' hReach st tr dn kRule #[] #[]
    #[up.letter] #[front.letter] block 0
  refine ⟨x, cube', hx, ?_, by rw [hrule, hrot], hReach⟩
  unfold Scramble.do_rule
  rw [cubie_at_refines cube ⟨1, 1, 1⟩ j hj hpos hbefore (Reach.fits26 cube hR), ok_bind,
    atL_embedCube cube j hj, ok_bind]
  have hyp : (embedC cube[j]).sudo_5Cubie_2yp = up.code := by
    rw [embedC, slot_of_facing _ _ _ hup]
  have hfr : (embedC cube[j]).sudo_5Cubie_2zp = front.code := by
    rw [embedC, slot_of_facing _ _ _ hfront]
  dsimp only
  rw [hyp, hfr, hr, ok_bind]
  simp only [blank_ok, ok_bind, letter_refines]
  exact (bind_ok_of hps _).trans rfl

theorem apply_v2_symbol_gen (v : Int) (pend : Array Int) (tot proc : Int) (cube : Cube)
    (hR : Reach cube) (st : Array Scramble.Step) (tr dn : Bool) (n : Nat) (hn : n < 16)
    (block : Int) :
    ∃ x cube', Emits tr x (symTagsV2 n block) ∧
      Scramble.apply_v2_symbol (Scramble.Scramble.mk v pend tot proc (embedCube cube) st tr dn)
          (Int.ofNat n) block =
        .ok (Scramble.Scramble.mk v pend tot proc (embedCube cube') (st ++ x) tr dn) ∧
      symbolV2 cube n = some cube' ∧ Reach cube' := by
  obtain ⟨ha, hb⟩ := v2_faces n hn
  have h1 : (1 : Nat) = 1 ∨ (1 : Nat) = 2 ∨ (1 : Nat) = 3 := Or.inl rfl
  obtain ⟨x1, hx1, hs1, r1⟩ := do_move_gen v pend tot proc cube hR st tr dn (v2Turns n).1 1 h1 n hn
    block 0
  obtain ⟨x2, hx2, hs2, r2⟩ := do_move_gen v pend tot proc _ r1 (st ++ x1) tr dn (v2Turns n).2 1 h1
    n hn block (Int.ofNat 1)
  obtain ⟨x3, c3, hx3, hs3, hrule, r3⟩ := do_rule_gen v pend tot proc _ r2 (st ++ x1 ++ x2) tr dn
    block
  refine ⟨x1 ++ x2 ++ x3, c3, ?_, ?_, ?_, r3⟩
  · exact (hx1.append hx2).append hx3
  · unfold Scramble.apply_v2_symbol
    rw [ha, ok_bind, show (1 : Int) = Int.ofNat 1 from rfl, hs1, ok_bind, hb, ok_bind]
    dsimp only
    rw [hs2, ok_bind, hs3]
    simp only [Array.append_assoc, pure_eq_ok]
    rfl
  · unfold symbolV2
    rw [turns_one, turns_one] at hrule
    exact hrule

theorem tapeTagsV2_take_succ (p : Nat) (ny : List Nat) (i : Nat) (hi : i < ny.length) :
    tapeTagsV2 p (ny.take (i + 1)) = tapeTagsV2 p (ny.take i) ++ symTagsV2 ny[i] (Int.ofNat (p + i)) := by
  rw [List.take_succ, List.getElem?_eq_getElem hi, Option.toList_some, tapeTagsV2_append,
    List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
  simp [tapeTagsV2]

/-- `apply_ready` on a v2 state, traced or not: as `apply_ready_v2_digest`, and the appended trace
    steps are the tape's (`tapeTagsV2`, blocks numbered from `processed`). -/
theorem apply_ready_v2_gen (tot : Int) (st : Array Scramble.Step) (tr dn : Bool) (cube : Cube)
    (hR : Reach cube) (ny : List Nat) (hny : ∀ x ∈ ny, x < 16) (p : Nat)
    (hfit : FitsLen (p + ny.length)) :
    ∃ x cube', Emits tr x (tapeTagsV2 p ny) ∧
      Scramble.apply_ready (Scramble.Scramble.mk 2 (embed ny) tot (Int.ofNat p) (embedCube cube)
          st tr dn) =
        .ok (Scramble.Scramble.mk 2 #[] tot (Int.ofNat (p + ny.length)) (embedCube cube')
          (st ++ x) tr dn) ∧
      walkV2 cube ny = some cube' ∧ Reach cube' := by
  unfold Scramble.apply_ready
  simp only [show SudoRt.SEq.beq (2 : Int) (1 : Int) = false from rfl, Bool.false_eq_true,
    if_false, listLen_embed, fuelRange_eq, bind_pure_right]
  rcases Nat.eq_zero_or_pos ny.length with h0 | hpos
  · have hnil : ny = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    refine ⟨#[], cube, Emits.nil tr, ?_, rfl, hR⟩
    rw [show Int.ofNat ([] : List Nat).length = (0 : Int) from rfl, subI_zero_one, ok_bind,
      asc_break (0 : Int) (-1 : Int) _ _ _ _ (by decide)
        (by rw [if_pos (show (0 : Int) > -1 by decide)]; rfl)]
    simp [pure_eq_ok]
  · have hfl : FitsLen ny.length := FitsLen.of_le hfit (by omega)
    rw [subI_ofNat_one _ hpos hfl, ok_bind]
    refine chain_inv _ _ _ (fun i (σs : Scramble.Scramble) => ∃ x c, σs = Scramble.Scramble.mk
          2 (embed ny) tot (Int.ofNat (p + i)) (embedCube c) (st ++ x) tr dn ∧
        Emits tr x (tapeTagsV2 p (ny.take i)) ∧
        walkV2 cube (ny.take i) = some c ∧ Reach c) 0 (ny.length - 1) (Nat.zero_le _) ?_
      (fun (r : Except SudoRt.Trap Scramble.Scramble) => ∃ x c, Emits tr x (tapeTagsV2 p ny) ∧
        r = .ok (Scramble.Scramble.mk 2 #[] tot (Int.ofNat (p + ny.length)) (embedCube c)
          (st ++ x) tr dn) ∧
        walkV2 cube ny = some c ∧ Reach c) ?_ _ ⟨#[], cube, by simp, Emits.nil tr, rfl, hR⟩
    · rintro i σs - hi ⟨x, c, rfl, hx, hw, hr⟩
      have hil : i < ny.length := by omega
      obtain ⟨x', c', hx', hs, hsym, hr'⟩ := apply_v2_symbol_gen 2 (embed ny) tot
        (Int.ofNat (p + i)) c hr (st ++ x) tr dn ny[i] (hny _ (List.getElem_mem hil))
        (Int.ofNat (p + i))
      refine ⟨_, ⟨x ++ x', c', rfl, by rw [tapeTagsV2_take_succ _ _ _ hil]; exact hx.append hx',
        by rw [walkV2_take_succ _ _ _ hil, hw]; exact hsym, hr'⟩, ?_⟩
      dsimp only
      rw [if_neg (ofNat_not_gt hi)]
      simp only [atL_embed ny i hil, ok_bind]
      rw [hs, ok_bind]
      dsimp only
      rw [addI_ofNat_one (p + i) (FitsLen.of_le hfit (by omega))]
      simp only [ok_bind, pure_eq_ok]
      rw [asc_tail _ i (FitsLen.of_le hfl (by omega))]
      simp only [Array.append_assoc]
      rfl
    · rintro σs ⟨x, c, rfl, hx, hw, hr⟩
      have e : ny.length - 1 + 1 = ny.length := by omega
      rw [e, List.take_length] at hw hx
      refine ⟨x, c, hx, ?_, hw, hr⟩
      simp only [e]
      rfl

/-- `update` on a v2 state (not done), traced or not, with a byte message: as `update_v2_digest`,
    and the appended trace steps are those of the walked tape. -/
theorem update_v2_gen (ny : List Nat) (hny : ∀ x ∈ ny, x < 16) (t p : Nat) (cube : Cube)
    (hR : Reach cube) (st : Array Scramble.Step) (tr : Bool) (msg : List Nat)
    (hb : ∀ b ∈ msg, b ≤ 255)
    (hfitP : FitsLen (p + ny.length + 2 * msg.length)) (hfitT : FitsLen (t + 2 * msg.length)) :
    ∃ x cube', Emits tr x (tapeTagsV2 p (ny ++ nybbles msg)) ∧
      Scramble.update
        (Scramble.Scramble.mk 2 (embed ny) (Int.ofNat t) (Int.ofNat p) (embedCube cube) st tr
          false) (embed msg) =
      .ok (Scramble.Scramble.mk 2 #[] (Int.ofNat (t + 2 * msg.length))
          (Int.ofNat (p + ny.length + 2 * msg.length)) (embedCube cube') (st ++ x) tr false) ∧
      walkV2 cube (ny ++ nybbles msg) = some cube' ∧ Reach cube' := by
  have hny' : ∀ x ∈ ny ++ nybbles msg, x < 16 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hny x h
    · exact nybbles_lt msg hb x h
  have hlen : (ny ++ nybbles msg).length = ny.length + 2 * msg.length := by
    rw [List.length_append, nybbles_length]
  obtain ⟨x, c', hx, hc', hw, hr⟩ := apply_ready_v2_gen (Int.ofNat (t + 2 * msg.length)) st tr
    false cube hR (ny ++ nybbles msg) hny' p (by rw [hlen, ← Nat.add_assoc]; exact hfitP)
  rw [hlen, ← Nat.add_assoc] at hc'
  refine ⟨x, c', hx, ?_, hw, hr⟩
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
          (Int.ofNat t) (Int.ofNat p) (embedCube cube) st tr false) 0 (msg.length - 1)
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

/-- `finish`, traced or not: the model's seat, `done` set, and the three closer / seat
    steps (`closerTags`). -/
theorem finish_gen (v : Int) (pend : Array Int) (tot proc : Int) (cube : Cube) (hR : Reach cube)
    (st : Array Scramble.Step) (tr dn : Bool) :
    ∃ x cube', Emits tr x closerTags ∧
      Scramble.finish (Scramble.Scramble.mk v pend tot proc (embedCube cube) st tr dn) =
        .ok (Scramble.Scramble.mk v pend tot proc (embedCube cube') (st ++ x) tr true) ∧
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
  obtain ⟨x1, hx1, hp1⟩ := push_step_gen v pend tot proc _ r1 st tr dn kCloser #[70, 50] #[] #[] #[]
    0 0
  obtain ⟨x2, hx2, hp2⟩ := push_step_gen v pend tot proc _ r2 (st ++ x1) tr dn kCloser #[66, 50] #[]
    #[] #[] 0 0
  obtain ⟨x3, hx3, hp3⟩ := push_step_gen v pend tot proc _ r3 (st ++ x1 ++ x2) tr dn kCanon #[] #[]
    #[] #[] 0 0
  refine ⟨x1 ++ x2 ++ x3, c3, (hx1.append hx2).append hx3, ?_, hrot, r3⟩
  simp only [kCloser, kCanon] at hp1 hp2 hp3
  unfold Scramble.finish
  simp only [hF, blank_ok, ok_bind]
  rw [bind_ok_of hp1]
  dsimp only
  rw [hB, ok_bind, bind_ok_of hp2]
  dsimp only
  rw [hW, ok_bind, bind_ok_of hp3]
  simp only [Array.append_assoc, pure_eq_ok]

/-- `evaluate` on a v2 state (not done), traced or not, with `total = t`: as
    `evaluate_v2_digest`, and the returned trace is the state's steps followed by those of the
    padding walk and the closer. -/
theorem evaluate_v2_gen (ny : List Nat) (hny : ∀ x ∈ ny, x < 16) (t p : Nat) (cube : Cube)
    (hR : Reach cube) (st : Array Scramble.Step) (tr : Bool) (ht : FitsLen (t + 1))
    (hp : FitsLen (p + ny.length + 12)) :
    ∃ ev s' d x, Scramble.evaluate
        (Scramble.Scramble.mk 2 (embed ny) (Int.ofNat t) (Int.ofNat p) (embedCube cube) st tr
          false) = .ok (ev, s') ∧
      (walkV2 cube (ny ++ padTailV2 t) >>= seat >>= ScrambleV2.digestOf) = some d ∧
      ev.sudo_10Evaluation_6digest = embed d ∧
      ev.sudo_10Evaluation_5trace = st ++ x ∧
      Emits tr x (tapeTagsV2 p (ny ++ padTailV2 t) ++ closerTags) := by
  have hny' : ∀ x ∈ ny ++ padTailV2 t, x < 16 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hny x h
    · exact padTailV2_lt t x h
  have hfit : FitsLen (p + (ny ++ padTailV2 t).length) :=
    FitsLen.of_le hp (by rw [List.length_append]; have := padTailV2_length t; omega)
  obtain ⟨x1, c1, hx1, h1, hw, r1⟩ := apply_ready_v2_gen (Int.ofNat t) st tr false cube hR
    (ny ++ padTailV2 t) hny' p hfit
  obtain ⟨x2, c2, hx2, h2, hseat, r2⟩ := finish_gen 2 #[] (Int.ofNat t)
    (Int.ofNat (p + (ny ++ padTailV2 t).length)) c1 r1 (st ++ x1) tr false
  obtain ⟨d, hd, hidx⟩ := Reach.index_bytes c2 r2
  refine ⟨⟨embed d, st ++ x1 ++ x2⟩, Scramble.Scramble.mk 2 #[] (Int.ofNat t)
    (Int.ofNat (p + (ny ++ padTailV2 t).length)) (embedCube c2) (st ++ x1 ++ x2) tr true, d,
    x1 ++ x2, ?_, by simp [hw, hseat, hd], rfl, (Array.append_assoc _ _ _), hx1.append hx2⟩
  unfold Scramble.evaluate
  simp only [show (!false) = true from rfl, sudoAssert_true, ok_bind]
  rw [pad_v2 (embed ny) t _ _ _ tr false ht, ok_bind, ← embed_append, h1, ok_bind, h2, ok_bind]
  dsimp only
  rw [hidx]
  rfl

theorem nybbles_append (a b : List Nat) : nybbles (a ++ b) = nybbles a ++ nybbles b := by
  simp [nybbles, List.flatMap_append]

/-- Several `update` calls in a row on a v2 state with nothing pending (traced or not):
    together they walk the nybbles of the concatenated message and append its trace steps. -/
theorem updates_v2 (msgs : List (List Nat)) (hb : ∀ m ∈ msgs, ∀ b ∈ m, b ≤ 255) :
    ∀ (t : Nat) (cube : Cube) (st : Array Scramble.Step) (tr : Bool), Reach cube →
    FitsLen (t + 2 * msgs.flatten.length) →
    ∃ x cube', Emits tr x (tapeTagsV2 t (nybbles msgs.flatten)) ∧
      msgs.foldlM (fun s m => Scramble.update s (embed m))
          (Scramble.Scramble.mk 2 (embed []) (Int.ofNat t) (Int.ofNat t) (embedCube cube) st tr
            false) =
        .ok (Scramble.Scramble.mk 2 (embed []) (Int.ofNat (t + 2 * msgs.flatten.length))
          (Int.ofNat (t + 2 * msgs.flatten.length)) (embedCube cube') (st ++ x) tr false) ∧
      walkV2 cube (nybbles msgs.flatten) = some cube' ∧ Reach cube' := by
  induction msgs with
  | nil =>
    intro t cube st tr hR _
    refine ⟨#[], cube, Emits.nil tr, ?_, rfl, hR⟩
    simp [pure_eq_ok]
  | cons m ms ih =>
    intro t cube st tr hR hfit
    have hbm : ∀ b ∈ m, b ≤ 255 := hb m (List.mem_cons_self _ _)
    have hbs : ∀ m' ∈ ms, ∀ b ∈ m', b ≤ 255 := fun m' h => hb m' (List.mem_cons_of_mem _ h)
    have hL : (m :: ms).flatten.length = m.length + ms.flatten.length := by
      rw [List.flatten_cons, List.length_append]
    rw [hL] at hfit ⊢
    obtain ⟨x1, c1, hx1, hu, hw1, r1⟩ := update_v2_gen [] (by simp) t t cube hR st tr m hbm
      (FitsLen.of_le hfit (by simp; omega)) (FitsLen.of_le hfit (by omega))
    simp only [List.length_nil, Nat.add_zero, List.nil_append] at hu hx1 hw1
    obtain ⟨x2, c2, hx2, hf, hw2, r2⟩ := ih hbs (t + 2 * m.length) c1 (st ++ x1) tr r1
      (FitsLen.of_le hfit (by omega))
    refine ⟨x1 ++ x2, c2, ?_, ?_, ?_, r2⟩
    · rw [List.flatten_cons, nybbles_append, tapeTagsV2_append, nybbles_length]
      exact hx1.append hx2
    · rw [List.foldlM_cons, hu, ok_bind]
      rw [show t + 2 * (m.length + ms.flatten.length) = t + 2 * m.length + 2 * ms.flatten.length
        by omega, ← Array.append_assoc]
      exact hf
    · rw [List.flatten_cons, nybbles_append, walkV2_append, hw1]
      exact hw2

/-- LINK 2, several updates, traced or not. From `fresh(2, traced)` (`scramble_v2` is
    `fresh(2, true)`, `scramble_v2_digest` is `fresh(2, false)`), `update` with each
    message of `msgs` in order, then `evaluate`, all return `.ok`; the digest is the
    model's digest of the concatenated message; the trace is `Emits`: on a traced state
    exactly the SPEC's steps (kind, move, nybble, block, index) of the padded tape and the
    closer, each with a 54-letter facelet string; on a digest-only state, empty. -/
theorem updates_evaluate_v2 (tr : Bool) (msgs : List (List Nat))
    (hb : ∀ m ∈ msgs, ∀ b ∈ m, b ≤ 255) (hlen : FitsLen (2 * msgs.flatten.length + 12)) :
    ∃ s0 s1 ev s2, Scramble.fresh 2 tr = .ok s0 ∧
      msgs.foldlM (fun s m => Scramble.update s (embed m)) s0 = .ok s1 ∧
      Scramble.evaluate s1 = .ok (ev, s2) ∧
      ev.sudo_10Evaluation_6digest = embed (digestV2 msgs.flatten) ∧
      Emits tr ev.sudo_10Evaluation_5trace
        (tapeTagsV2 0 (padV2 (nybbles msgs.flatten)) ++ closerTags) := by
  obtain ⟨x1, c1, hx1, hf, hw1, r1⟩ := updates_v2 msgs hb 0 solvedCube #[] tr ⟨_, reach_solved⟩
    (FitsLen.of_le hlen (by omega))
  obtain ⟨ev, s2, d, x2, he, hd, hdig, htr, hx2⟩ := evaluate_v2_gen [] (by simp)
    (0 + 2 * msgs.flatten.length) (0 + 2 * msgs.flatten.length) c1 r1 (#[] ++ x1) tr
    (FitsLen.of_le hlen (by omega)) (FitsLen.of_le hlen (by simp))
  refine ⟨_, _, ev, s2, fresh_refines 2 tr, hf, he, ?_, ?_⟩
  · rw [hdig]
    congr 1
    have hv : digestV2? msgs.flatten = some d := by
      unfold digestV2?
      rw [padV2_eq, walkV2_append, nybbles_length]
      simp only [List.nil_append, Nat.zero_add] at hd
      simpa [hw1, Option.bind_assoc] using hd
    simp [digestV2, hv]
  · have he0 : (#[] : Array Scramble.Step) ++ x1 = x1 := by simp
    rw [htr, he0, padV2_eq, tapeTagsV2_append, nybbles_length, List.append_assoc, Nat.zero_add]
    simp only [List.nil_append, Nat.zero_add] at hx2
    exact hx1.append hx2

/-- LINK 2 headline, traced. For a byte message with `2·len + 12` fitting `i64`: the traced
    constructor `scramble_v2`, then `update`, then `evaluate` return `.ok`; the digest is
    the model's `digestV2 msg`; the trace has `3·|padded tape| + 3` steps whose kind, move
    token, nybble, block and index are the SPEC's (`tapeTagsV2`, `closerTags`), each with a
    facelet string of 54 color letters. The `up` / `front` letters and which letters the
    facelet strings hold are not claimed. -/
theorem scramble_v2_refines_digestV2 (msg : List Nat) (hb : ∀ b ∈ msg, b ≤ 255)
    (hlen : FitsLen (2 * msg.length + 12)) :
    ∃ s0 s1 ev s2, Scramble.scramble_v2 = .ok s0 ∧
      Scramble.update s0 (embed msg) = .ok s1 ∧
      Scramble.evaluate s1 = .ok (ev, s2) ∧
      ev.sudo_10Evaluation_6digest = embed (digestV2 msg) ∧
      ev.sudo_10Evaluation_5trace.toList.map stepTag =
        tapeTagsV2 0 (padV2 (nybbles msg)) ++ closerTags ∧
      (∀ y ∈ ev.sudo_10Evaluation_5trace.toList, Faces54 y) ∧
      ev.sudo_10Evaluation_5trace.size = 3 * (padV2 (nybbles msg)).length + 3 := by
  obtain ⟨s0, s1, ev, s2, h0, hf, he, hdig, hx⟩ := updates_evaluate_v2 true [msg]
    (by simpa using hb) (by simpa using hlen)
  have hsz := hx.size
  obtain ⟨htags, hfaces⟩ := hx
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil] at hdig htags hfaces hsz
  refine ⟨s0, s1, ev, s2, by rw [scramble_v2_refines]; exact h0, ?_, he, hdig, htags, hfaces, ?_⟩
  · simpa [List.foldlM_cons, List.foldlM_nil] using hf
  · rw [hsz, List.length_append, tapeTagsV2_length]
    rfl

/-- The padded v2 tape has `max (len + 1) 12` nybbles; so a traced message of at most 5
    bytes has `3·12 + 3 = 39` steps, the SPEC table's Steps column. -/
theorem padV2_length (ny : List Nat) : (padV2 ny).length = max (ny.length + 1) 12 := by
  simp only [padV2, tapeI, List.length_append, List.length_map, List.length_range,
    List.length_singleton]
  omega

end ScrambleV2.Link2
