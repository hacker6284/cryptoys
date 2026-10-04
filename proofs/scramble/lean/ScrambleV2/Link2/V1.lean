/-
  LINK 2, v1 (digest only). The digest-only v1 path, `scramble_v1_digest` then `update`
  then `evaluate`, against the v1 model `ScrambleV2.SpecV1` (written from the SPEC's
  superseded `scramble_v1` section): `apply_v1_block` (eight moves then Rule B),
  `apply_ready` on a v1 state (every complete block of 8 nybbles walked, the partial block
  kept), `pad` (marker, cycle to a multiple of 8, cycle to 24), `update`, `evaluate`, and the
  headline `scramble_v1_digest_refines_digestV1`.

  Scope: digest equality for one `update` from `scramble_v1_digest`. The traced v1
  constructor `scramble_v1` and the v1 trace are not claimed. Proof-only. No algorithm change.
-/
import ScrambleV2.Link2.Traced
import ScrambleV2.SpecV1

namespace ScrambleV2.Link2
open MegaDreifach.Link2

theorem v1_tables (n : Nat) (hn : n < 16) :
    SudoRt.atL Scramble.v1_face (Int.ofNat n) = .ok (v1Move n).1.code ∧
    SudoRt.atL Scramble.v1_turns (Int.ofNat n) = .ok (Int.ofNat (v1Move n).2) ∧
    ((v1Move n).2 = 1 ∨ (v1Move n).2 = 2 ∨ (v1Move n).2 = 3) := by
  have hall : ∀ n ∈ List.range 16,
      SudoRt.atL Scramble.v1_face (Int.ofNat n) = .ok (v1Move n).1.code ∧
      SudoRt.atL Scramble.v1_turns (Int.ofNat n) = .ok (Int.ofNat (v1Move n).2) ∧
      ((v1Move n).2 = 1 ∨ (v1Move n).2 = 2 ∨ (v1Move n).2 = 3) := by
    decide
  exact hall n (List.mem_range.mpr hn)

theorem apply_v1_block_digest (v : Int) (pend : Array Int) (tot proc : Int) (cube : Cube)
    (hR : Reach cube) (st : Array Scramble.Step) (dn : Bool) (ny : List Nat)
    (hny : ∀ x ∈ ny, x < 16) (b : Nat) (hb : b + 8 ≤ ny.length) (hfit : FitsLen ny.length)
    (block : Int) :
    ∃ cube', Scramble.apply_v1_block
        (Scramble.Scramble.mk v pend tot proc (embedCube cube) st false dn) (embed ny)
        (Int.ofNat b) block =
      .ok (Scramble.Scramble.mk v pend tot proc (embedCube cube') st false dn) ∧
      blockV1 cube ((ny.drop b).take 8) = some cube' ∧ Reach cube' := by
  unfold Scramble.apply_v1_block
  simp only [fuelRange_eq, bind_pure_right]
  rw [show (7 : Int) = Int.ofNat 7 from rfl]
  refine chain_inv _ _ _ (fun k (σs : Scramble.Scramble) => ∃ c, σs = Scramble.Scramble.mk
        v pend tot proc (embedCube c) st false dn ∧
        ((ny.drop b).take k).foldl moveV1 cube = c ∧ Reach c) 0 7 (by omega) ?_
    (fun (r : Except SudoRt.Trap Scramble.Scramble) => ∃ c, r = .ok (Scramble.Scramble.mk
        v pend tot proc (embedCube c) st false dn) ∧
      blockV1 cube ((ny.drop b).take 8) = some c ∧ Reach c) ?_ _ ⟨cube, rfl, rfl, hR⟩
  · rintro k σs - hk ⟨c, rfl, hc, hr⟩
    have hbk : b + k < ny.length := by omega
    have hn := hny _ (List.getElem_mem hbk)
    obtain ⟨hf, ht, hm⟩ := v1_tables ny[b + k] hn
    obtain ⟨x, hx, hmv, hr'⟩ := do_move_gen v pend tot proc c hr st false dn (v1Move ny[b + k]).1
      (v1Move ny[b + k]).2 hm ny[b + k] hn block (Int.ofNat k)
    simp only [Emits] at hx
    subst hx
    refine ⟨_, ⟨turnsN (v1Move ny[b + k]).1 (v1Move ny[b + k]).2 c, rfl, ?_, hr'⟩, ?_⟩
    · have hkl : k < (ny.drop b).length := by rw [List.length_drop]; omega
      rw [List.take_succ, List.getElem?_eq_getElem hkl, Option.toList_some, List.foldl_append, hc,
        List.getElem_drop]
      simp [moveV1]
    · dsimp only
      rw [if_neg (ofNat_not_gt hk)]
      simp only [addI_ofNat b k (FitsLen.of_le hfit (by omega)), ok_bind, atL_embed ny _ hbk, hf,
        ht, hmv, pure_eq_ok]
      rw [asc_tail _ k (fits_small (by omega))]
      simp
  · rintro σs ⟨c, rfl, hc, hr⟩
    obtain ⟨x, c', hx, hrule, hb', hr'⟩ := do_rule_gen v pend tot proc c hr st false dn block
    simp only [Emits] at hx
    subst hx
    refine ⟨c', ?_, ?_, hr'⟩
    · dsimp only
      rw [hrule]
      simp
    · unfold blockV1
      rw [hc]
      exact hb'

theorem embed_snoc (xs : List Nat) (x : Nat) :
    embed (xs ++ [x]) = (embed xs).push (Int.ofNat x) := by
  simp [embed, List.map_append, Array.push]

theorem walkV1_eq (cube : Cube) (tape : List Nat) :
    walkV1 cube tape = (List.range (tape.length / 8)).foldlM
      (fun c j => blockV1 c ((tape.drop (8 * j)).take 8)) cube := rfl

theorem foldlM_range_succ {α : Type} (f : α → Nat → Option α) (a : α) (b : Nat) :
    (List.range (b + 1)).foldlM f a = (List.range b).foldlM f a >>= fun c => f c b := by
  rw [List.range_succ, List.foldlM_append]
  simp

/-- `apply_ready` on a v1 digest-only state with `processed = 8q`: every complete block of
    `pending` is walked (the model's `walkV1`), `processed` advances by 8 per block, and the
    trailing partial block stays in `pending`. -/
theorem apply_ready_v1_digest (tot : Int) (st : Array Scramble.Step) (dn : Bool) (cube : Cube)
    (hR : Reach cube) (ny : List Nat) (hny : ∀ x ∈ ny, x < 16) (q : Nat)
    (hfit : FitsLen (8 * q + ny.length + 8)) :
    ∃ cube', Scramble.apply_ready (Scramble.Scramble.mk 1 (embed ny) tot (Int.ofNat (8 * q))
          (embedCube cube) st false dn) =
        .ok (Scramble.Scramble.mk 1 (embed (ny.drop (8 * (ny.length / 8)))) tot
          (Int.ofNat (8 * (q + ny.length / 8))) (embedCube cube') st false dn) ∧
      walkV1 cube ny = some cube' ∧ Reach cube' := by
  have hfl : FitsLen ny.length := FitsLen.of_le hfit (by omega)
  have div8 : ∀ a, SudoRt.divI (Int.ofNat a) 8 = .ok (Int.ofNat (a / 8)) :=
    fun a => divI_ofNat a (b := 8) (by decide)
  have mul8 : ∀ a, FitsLen (a * 8) → SudoRt.mulI (Int.ofNat a) 8 = .ok (Int.ofNat (a * 8)) :=
    fun a h => mulI_ofNat a 8 h
  have add8 : ∀ a, FitsLen (a + 8) → SudoRt.addI (Int.ofNat a) 8 = .ok (Int.ofNat (a + 8)) :=
    fun a h => addI_ofNat a 8 h
  unfold Scramble.apply_ready
  simp only [show SudoRt.SEq.beq (1 : Int) (1 : Int) = true from rfl, if_true, listLen_embed,
    fuelRange_eq, bind_pure_right, appendL_spec]
  rw [div8, ok_bind]
  rcases Nat.eq_zero_or_pos (ny.length / 8) with hm0 | hmpos
  · have hsub : SudoRt.subI (Int.ofNat (ny.length / 8)) 1 = .ok (-1) := by
      rw [hm0]; exact subI_zero_one
    rw [hsub, ok_bind,
      asc_break (0 : Int) (-1 : Int) _ _ _ _ (by decide)
        (by rw [if_pos (show (0 : Int) > -1 by decide)]; rfl)]
    dsimp only
    have hw : walkV1 cube ny = some cube := by rw [walkV1_eq, hm0]; rfl
    rw [show (8 * q) = 8 * (q + ny.length / 8) by omega]
    -- second loop: copy the trailing partial block into `rest`
    rw [mul8 _ (FitsLen.of_le hfl (by omega)), ok_bind]
    rcases Nat.eq_zero_or_pos (ny.length % 8) with hr0 | hrpos
    · have hall : ny.length / 8 * 8 = ny.length := by omega
      have hdrop : ny.drop (8 * (ny.length / 8)) = [] :=
        List.drop_eq_nil_of_le (by omega)
      rcases Nat.eq_zero_or_pos ny.length with hl0 | hlpos
      · rw [show Int.ofNat ny.length = (0 : Int) by rw [hl0]; rfl, subI_zero_one, ok_bind]
        rw [asc_break _ (-1 : Int) _ _ _ _ (by rw [hall, hl0]; decide)
          (by rw [if_pos (by rw [hall, hl0]; decide)]; rfl)]
        refine ⟨cube, ?_, hw, hR⟩
        rw [hdrop]
        rfl
      · rw [subI_ofNat_one _ hlpos hfl, ok_bind]
        have hgt : Int.ofNat (ny.length / 8 * 8) > Int.ofNat (ny.length - 1) := by
          rw [hall]; exact Int.ofNat_lt.mpr (by omega)
        rw [asc_break _ _ _ _ _ _ hgt (by rw [if_pos hgt]; rfl)]
        refine ⟨cube, ?_, hw, hR⟩
        rw [hdrop]
        rfl
    · have hlpos : 0 < ny.length := by omega
      rw [subI_ofNat_one _ hlpos hfl, ok_bind]
      refine ⟨cube, ?_, hw, hR⟩
      refine chain_eq _ _ _
        (fun i => embed ((ny.drop (ny.length / 8 * 8)).take (i - ny.length / 8 * 8)))
        (ny.length / 8 * 8) (ny.length - 1) (by omega) ?_ _ ?_ _ ?_
      · intro i h1 h2
        have hi : i < (embed ny).size := by rw [size_embed]; omega
        have hil : i < ny.length := by omega
        dsimp only
        rw [if_neg (ofNat_not_gt h2)]
        simp only [atL_embed ny i hil, ok_bind, pure_eq_ok]
        rw [asc_tail _ i (FitsLen.of_le hfl (by omega))]
        have hpush : (embed ((ny.drop (ny.length / 8 * 8)).take (i - ny.length / 8 * 8))).push
              (Int.ofNat ny[i]) =
            embed ((ny.drop (ny.length / 8 * 8)).take (i + 1 - ny.length / 8 * 8)) := by
          have hk : i + 1 - ny.length / 8 * 8 = (i - ny.length / 8 * 8) + 1 := by omega
          have hkl : i - ny.length / 8 * 8 < (ny.drop (ny.length / 8 * 8)).length := by
            rw [List.length_drop]; omega
          rw [hk, List.take_succ, List.getElem?_eq_getElem hkl, Option.toList_some,
            embed_snoc]
          congr 1
          simp only [List.getElem_drop]
          congr 2
          omega
        rw [hpush]
      · simp only [pure_eq_ok]
        rw [show ny.length - 1 + 1 - ny.length / 8 * 8 = (ny.drop (ny.length / 8 * 8)).length by
          rw [List.length_drop]; omega, List.take_length, Nat.mul_comm]
      · simp [embed]
  · rw [subI_ofNat_one _ hmpos (FitsLen.of_le hfl (by omega)), ok_bind]
    refine chain_inv _ _ _ (fun b (σs : Scramble.Scramble) => ∃ c, σs = Scramble.Scramble.mk
          1 (embed ny) tot (Int.ofNat (8 * (q + b))) (embedCube c) st false dn ∧
        (List.range b).foldlM (fun c j => blockV1 c ((ny.drop (8 * j)).take 8)) cube = some c ∧
        Reach c) 0 (ny.length / 8 - 1) (Nat.zero_le _) ?_
      (fun (r : Except SudoRt.Trap Scramble.Scramble) => ∃ c, r = .ok (Scramble.Scramble.mk 1
          (embed (ny.drop (8 * (ny.length / 8)))) tot (Int.ofNat (8 * (q + ny.length / 8)))
          (embedCube c) st false dn) ∧ walkV1 cube ny = some c ∧ Reach c) ?_ _
      ⟨cube, rfl, rfl, hR⟩
    · rintro b σs - hb ⟨c, rfl, hw, hr⟩
      have hbl : b * 8 + 8 ≤ ny.length := by omega
      obtain ⟨c', hblk, hbv, hr'⟩ := apply_v1_block_digest 1 (embed ny) tot
        (Int.ofNat (8 * (q + b))) c hr st dn ny hny (b * 8) hbl hfl (Int.ofNat (q + b))
      refine ⟨_, ⟨c', rfl, ?_, hr'⟩, ?_⟩
      · rw [foldlM_range_succ, hw]
        simpa [Nat.mul_comm] using hbv
      · dsimp only
        rw [if_neg (ofNat_not_gt hb)]
        have hdiv : SudoRt.divI (Int.ofNat (8 * (q + b))) 8 = .ok (Int.ofNat (q + b)) := by
          rw [div8]; congr 2; omega
        rw [mul8 b (FitsLen.of_le hfl (by omega)), ok_bind, hdiv, ok_bind, hblk, ok_bind]
        dsimp only
        rw [add8 (8 * (q + b)) (FitsLen.of_le hfit (by omega))]
        simp only [ok_bind, pure_eq_ok]
        rw [show 8 * (q + b) + 8 = 8 * (q + (b + 1)) by omega,
          asc_tail _ b (FitsLen.of_le hfl (by omega))]
    · rintro σs ⟨c, rfl, hw, hr⟩
      rw [show ny.length / 8 - 1 + 1 = ny.length / 8 by omega] at hw
      have hw : walkV1 cube ny = some c := by rw [walkV1_eq]; exact hw
      dsimp only
      rw [show ny.length / 8 - 1 + 1 = ny.length / 8 by omega]
      -- second loop: copy the trailing partial block into `rest`
      rw [mul8 _ (FitsLen.of_le hfl (by omega)), ok_bind]
      rcases Nat.eq_zero_or_pos (ny.length % 8) with hr0 | hrpos
      · have hall : ny.length / 8 * 8 = ny.length := by omega
        have hdrop : ny.drop (8 * (ny.length / 8)) = [] :=
          List.drop_eq_nil_of_le (by omega)
        rcases Nat.eq_zero_or_pos ny.length with hl0 | hlpos
        · rw [show Int.ofNat ny.length = (0 : Int) by rw [hl0]; rfl, subI_zero_one, ok_bind]
          rw [asc_break _ (-1 : Int) _ _ _ _ (by rw [hall, hl0]; decide)
            (by rw [if_pos (by rw [hall, hl0]; decide)]; rfl)]
          refine ⟨c, ?_, hw, hr⟩
          rw [hdrop]
          rfl
        · rw [subI_ofNat_one _ hlpos hfl, ok_bind]
          have hgt : Int.ofNat (ny.length / 8 * 8) > Int.ofNat (ny.length - 1) := by
            rw [hall]; exact Int.ofNat_lt.mpr (by omega)
          rw [asc_break _ _ _ _ _ _ hgt (by rw [if_pos hgt]; rfl)]
          refine ⟨c, ?_, hw, hr⟩
          rw [hdrop]
          rfl
      · have hlpos : 0 < ny.length := by omega
        rw [subI_ofNat_one _ hlpos hfl, ok_bind]
        refine ⟨c, ?_, hw, hr⟩
        refine chain_eq _ _ _
          (fun i => embed ((ny.drop (ny.length / 8 * 8)).take (i - ny.length / 8 * 8)))
          (ny.length / 8 * 8) (ny.length - 1) (by omega) ?_ _ ?_ _ ?_
        · intro i h1 h2
          have hi : i < (embed ny).size := by rw [size_embed]; omega
          have hil : i < ny.length := by omega
          dsimp only
          rw [if_neg (ofNat_not_gt h2)]
          simp only [atL_embed ny i hil, ok_bind, pure_eq_ok]
          rw [asc_tail _ i (FitsLen.of_le hfl (by omega))]
          have hpush : (embed ((ny.drop (ny.length / 8 * 8)).take (i - ny.length / 8 * 8))).push
                (Int.ofNat ny[i]) =
              embed ((ny.drop (ny.length / 8 * 8)).take (i + 1 - ny.length / 8 * 8)) := by
            have hk : i + 1 - ny.length / 8 * 8 = (i - ny.length / 8 * 8) + 1 := by omega
            have hkl : i - ny.length / 8 * 8 < (ny.drop (ny.length / 8 * 8)).length := by
              rw [List.length_drop]; omega
            rw [hk, List.take_succ, List.getElem?_eq_getElem hkl, Option.toList_some,
              embed_snoc]
            congr 1
            simp only [List.getElem_drop]
            congr 2
            omega
          rw [hpush]
        · simp only [pure_eq_ok]
          rw [show ny.length - 1 + 1 - ny.length / 8 * 8 = (ny.drop (ny.length / 8 * 8)).length by
            rw [List.length_drop]; omega, List.take_length, Nat.mul_comm]
        · simp [embed]

/-- v1 pad count: cycle nybbles appended after the marker to reach a multiple of 8. -/
def padKV1 (t : Nat) : Nat := (8 - (t + 1) % 8) % 8

/-- What `pad` appends to a v1 tape when `total = t`. -/
def padTailV1 (t : Nat) : List Nat :=
  8 :: (cycleV1.take (padKV1 t) ++ tapeF (24 - (t + 1 + padKV1 t)))

theorem padV1_eq (ny : List Nat) : padV1 ny = ny ++ padTailV1 ny.length := by
  have h8 : ∀ k, k < 8 → (cycleV1.take k).length = k := by decide
  have hk : padKV1 ny.length < 8 := Nat.mod_lt _ (by decide)
  simp only [padKV1] at hk
  simp only [padV1, padTailV1, padKV1, tapeF, List.length_append, List.length_singleton,
    List.length_cons, h8 _ hk, List.append_assoc, List.cons_append, List.nil_append,
    List.singleton_append]
  have e : ∀ a b : Nat, 24 - (a + (b + 1)) = 24 - (a + 1 + b) := by intros; omega
  rw [e]
  simp only [List.length_nil, Nat.zero_add]
  rw [h8 _ hk]

theorem tape_f_at (j : Nat) (hj : j < 8) :
    SudoRt.atL Scramble.tape_f (Int.ofNat j) = .ok (Int.ofNat (cycleV1.getD j 0)) := by
  have hall : ∀ j ∈ List.range 8,
      SudoRt.atL Scramble.tape_f (Int.ofNat j) = .ok (Int.ofNat (cycleV1.getD j 0)) := by
    decide
  exact hall j (List.mem_range.mpr hj)

theorem tapeF_succ (i : Nat) : tapeF (i + 1) = tapeF i ++ [cycleV1.getD (i % 8) 0] := by
  simp [tapeF, List.range_succ]

theorem cycle_take_succ : ∀ i, i < 8 → cycleV1.take (i + 1) = cycleV1.take i ++ [cycleV1.getD i 0] := by
  decide

theorem pad_arr (pend : Array Int) (k m : Nat) :
    pend.push 8 ++ embed (cycleV1.take k) ++ embed (tapeF m) =
      pend ++ embed (8 :: (cycleV1.take k ++ tapeF m)) := by
  apply Array.ext'; simp [embed]

/-- `pad` on a v1 state with `total = t` appends `padTailV1 t` to `pending`; nothing else
    changes. -/
theorem pad_v1 (pend : Array Int) (t : Nat) (proc : Int) (cb : Array Scramble.Cubie)
    (st : Array Scramble.Step) (tr dn : Bool) (ht : FitsLen (t + 25)) :
    Scramble.pad (Scramble.Scramble.mk 1 pend (Int.ofNat t) proc cb st tr dn) =
      .ok (Scramble.Scramble.mk 1 (pend ++ embed (padTailV1 t)) (Int.ofNat t) proc cb st tr dn) := by
  unfold Scramble.pad
  simp only [addI_ofNat_one t (FitsLen.of_le ht (by omega)), ok_bind, appendL_spec,
    show SudoRt.SEq.beq (1 : Int) (1 : Int) = true from rfl, if_true,
    fuelRange_eq, bind_pure_right]
  have hm1 : SudoRt.modI (Int.ofNat (t + 1)) 8 = .ok (Int.ofNat ((t + 1) % 8)) :=
    modI_ofNat _ (b := 8) (by decide)
  have hs1 : SudoRt.subI 8 (Int.ofNat ((t + 1) % 8)) = .ok (Int.ofNat (8 - (t + 1) % 8)) :=
    subI_ofNat 8 _ (fits_small (by omega)) (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
  have hm2 : SudoRt.modI (Int.ofNat (8 - (t + 1) % 8)) 8 = .ok (Int.ofNat (padKV1 t)) :=
    modI_ofNat _ (b := 8) (by decide)
  rw [hm1, ok_bind, hs1, ok_bind, hm2, ok_bind]
  unfold padTailV1
  have hk8 : padKV1 t < 8 := Nat.mod_lt _ (by decide)
  generalize padKV1 t = k at hk8 ⊢
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [show SudoRt.subI (Int.ofNat k) 1 = .ok (-1) by rw [hk0]; exact subI_zero_one, ok_bind,
      asc_break (0 : Int) (-1 : Int) _ _ _ _ (by decide)
        (by rw [if_pos (show (0 : Int) > -1 by decide)]; rfl)]
    rw [show pend.push 8 = pend.push 8 ++ embed (cycleV1.take k) by simp [hk0, embed]]
    -- second loop: repeat the cycle up to 24 nybbles
    dsimp only
    rw [addI_ofNat (t + 1) k (FitsLen.of_le ht (by omega)), ok_bind]
    by_cases hs : t + 1 + k < 24
    · rw [show (24 : Int) = Int.ofNat 24 from rfl,
        subI_ofNat 24 (t + 1 + k) (fits_small (by omega)) (by omega), ok_bind,
        subI_ofNat_one (24 - (t + 1 + k)) (by omega) (fits_small (by omega)), ok_bind]
      refine chain_eq _ _ _ (fun i => Scramble.Scramble.mk 1
          (pend.push 8 ++ embed (cycleV1.take k) ++ embed (tapeF i)) (Int.ofNat t) proc cb st tr dn)
          0 (24 - (t + 1 + k) - 1) (Nat.zero_le _) ?_ _ ?_ _ ?_
      · intro i _ hi
        dsimp only
        rw [if_neg (ofNat_not_gt hi)]
        have hm : SudoRt.modI (Int.ofNat i) 8 = .ok (Int.ofNat (i % 8)) :=
          modI_ofNat i (b := 8) (by decide)
        simp only [hm, ok_bind, tape_f_at (i % 8) (Nat.mod_lt _ (by decide)), pure_eq_ok]
        rw [push_append_embed, ← tapeF_succ, asc_tail _ i (fits_small (by omega))]
      · dsimp only
        rw [show 24 - (t + 1 + k) - 1 + 1 = 24 - (t + 1 + k) by omega]
        simp only [pure_eq_ok]
        rw [pad_arr]
      · simp [tapeF, embed]
    · have hsub : SudoRt.subI 24 (Int.ofNat (t + 1 + k)) = .ok (24 - Int.ofNat (t + 1 + k)) := by
        unfold SudoRt.subI
        apply narrowI_in <;> unfold FitsLen i64MaxNat at ht <;>
          simp only [SudoRt.i64Min, SudoRt.i64Max, Int.ofNat_eq_coe] <;> omega
      have hsub1 : SudoRt.subI (24 - Int.ofNat (t + 1 + k)) 1 =
          .ok (24 - Int.ofNat (t + 1 + k) - 1) := by
        unfold SudoRt.subI
        apply narrowI_in <;> unfold FitsLen i64MaxNat at ht <;>
          simp only [SudoRt.i64Min, SudoRt.i64Max, Int.ofNat_eq_coe] <;> omega
      have hgt : (0 : Int) > 24 - Int.ofNat (t + 1 + k) - 1 := by
        simp only [Int.ofNat_eq_coe]; omega
      rw [hsub, ok_bind, hsub1, ok_bind,
        asc_break (0 : Int) _ _ _ _ _ hgt (by rw [if_pos hgt]; rfl)]
      have h0 : 24 - (t + 1 + k) = 0 := by omega
      dsimp only
      rw [h0, show pend.push 8 ++ embed (cycleV1.take k) =
          pend.push 8 ++ embed (cycleV1.take k) ++ embed (tapeF 0) by simp [tapeF, embed]]
      simp only [pure_eq_ok]
      rw [pad_arr]

  · rw [subI_ofNat_one k hkpos (fits_small (by omega)), ok_bind]
    refine chain_eq _ _ _ (fun i => Scramble.Scramble.mk 1 (pend.push 8 ++ embed (cycleV1.take i))
        (Int.ofNat t) proc cb st tr dn) 0 (k - 1) (Nat.zero_le _) ?_ _ ?_ _ ?_
    · intro i _ hi
      dsimp only
      rw [if_neg (ofNat_not_gt hi)]
      simp only [tape_f_at i (by omega), ok_bind, pure_eq_ok]
      rw [push_append_embed, ← cycle_take_succ i (by omega), asc_tail _ i (fits_small (by omega))]
    · rw [show k - 1 + 1 = k by omega]
      -- second loop: repeat the cycle up to 24 nybbles
      dsimp only
      rw [addI_ofNat (t + 1) k (FitsLen.of_le ht (by omega)), ok_bind]
      by_cases hs : t + 1 + k < 24
      · rw [show (24 : Int) = Int.ofNat 24 from rfl,
          subI_ofNat 24 (t + 1 + k) (fits_small (by omega)) (by omega), ok_bind,
          subI_ofNat_one (24 - (t + 1 + k)) (by omega) (fits_small (by omega)), ok_bind]
        refine chain_eq _ _ _ (fun i => Scramble.Scramble.mk 1
            (pend.push 8 ++ embed (cycleV1.take k) ++ embed (tapeF i)) (Int.ofNat t) proc cb st tr dn)
            0 (24 - (t + 1 + k) - 1) (Nat.zero_le _) ?_ _ ?_ _ ?_
        · intro i _ hi
          dsimp only
          rw [if_neg (ofNat_not_gt hi)]
          have hm : SudoRt.modI (Int.ofNat i) 8 = .ok (Int.ofNat (i % 8)) :=
            modI_ofNat i (b := 8) (by decide)
          simp only [hm, ok_bind, tape_f_at (i % 8) (Nat.mod_lt _ (by decide)), pure_eq_ok]
          rw [push_append_embed, ← tapeF_succ, asc_tail _ i (fits_small (by omega))]
        · dsimp only
          rw [show 24 - (t + 1 + k) - 1 + 1 = 24 - (t + 1 + k) by omega]
          simp only [pure_eq_ok]
          rw [pad_arr]
        · simp [tapeF, embed]
      · have hsub : SudoRt.subI 24 (Int.ofNat (t + 1 + k)) = .ok (24 - Int.ofNat (t + 1 + k)) := by
          unfold SudoRt.subI
          apply narrowI_in <;> unfold FitsLen i64MaxNat at ht <;>
            simp only [SudoRt.i64Min, SudoRt.i64Max, Int.ofNat_eq_coe] <;> omega
        have hsub1 : SudoRt.subI (24 - Int.ofNat (t + 1 + k)) 1 =
            .ok (24 - Int.ofNat (t + 1 + k) - 1) := by
          unfold SudoRt.subI
          apply narrowI_in <;> unfold FitsLen i64MaxNat at ht <;>
            simp only [SudoRt.i64Min, SudoRt.i64Max, Int.ofNat_eq_coe] <;> omega
        have hgt : (0 : Int) > 24 - Int.ofNat (t + 1 + k) - 1 := by
          simp only [Int.ofNat_eq_coe]; omega
        rw [hsub, ok_bind, hsub1, ok_bind,
          asc_break (0 : Int) _ _ _ _ _ hgt (by rw [if_pos hgt]; rfl)]
        have h0 : 24 - (t + 1 + k) = 0 := by omega
        dsimp only
        rw [h0, show pend.push 8 ++ embed (cycleV1.take k) =
            pend.push 8 ++ embed (cycleV1.take k) ++ embed (tapeF 0) by simp [tapeF, embed]]
        simp only [pure_eq_ok]
        rw [pad_arr]

    · simp [embed]

theorem foldlM_congr_mem {α β : Type} (f g : α → β → Option α) :
    ∀ (l : List β), (∀ a, ∀ b ∈ l, f a b = g a b) → ∀ a, l.foldlM f a = l.foldlM g a
  | [], _, _ => rfl
  | b :: l, h, a => by
    simp only [List.foldlM_cons]
    rw [h a b (List.mem_cons_self _ _)]
    cases g a b with
    | none => rfl
    | some c =>
      exact foldlM_congr_mem f g l (fun a' b' hb' => h a' b' (List.mem_cons_of_mem _ hb')) c

theorem walkV1_short (cube : Cube) (ys : List Nat) (h : ys.length < 8) :
    walkV1 cube ys = some cube := by
  rw [walkV1_eq, show ys.length / 8 = 0 by omega]
  rfl

/-- Walking a tape whose first part is whole blocks walks that part, then the rest. -/
theorem walkV1_append8 (cube : Cube) (xs ys : List Nat) (m : Nat) (hx : xs.length = 8 * m) :
    walkV1 cube (xs ++ ys) = walkV1 cube xs >>= fun c => walkV1 c ys := by
  simp only [walkV1_eq, List.length_append, hx]
  rw [show (8 * m + ys.length) / 8 = m + ys.length / 8 by omega, List.range_add,
    List.foldlM_append, show 8 * m / 8 = m by omega]
  simp only [List.foldlM_map]
  rw [foldlM_congr_mem _ (fun c j => blockV1 c ((xs.drop (8 * j)).take 8)) _ ?_ cube]
  · cases (List.range m).foldlM (fun c j => blockV1 c ((xs.drop (8 * j)).take 8)) cube with
    | none => rfl
    | some c =>
      refine foldlM_congr_mem _ _ _ (fun a j _ => ?_) c
      dsimp only
      rw [show 8 * (m + j) = xs.length + 8 * j by omega, ← List.drop_drop, List.drop_left]
  · intro a j hj
    have hj' : j < m := List.mem_range.mp hj
    rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length
      (by rw [List.length_drop]; omega)]

/-- `update` on a digest-only v1 state (not done) with `processed = 8q`: it appends the
    message's nybbles to `pending`, walks every complete block of `pending` (the model's
    `walkV1`), and keeps the trailing partial block in `pending`. -/
theorem update_v1_digest (ny : List Nat) (hny : ∀ x ∈ ny, x < 16) (t q : Nat) (cube : Cube)
    (hR : Reach cube) (st : Array Scramble.Step) (msg : List Nat) (hb : ∀ b ∈ msg, b ≤ 255)
    (hfitP : FitsLen (8 * q + ny.length + 2 * msg.length + 8))
    (hfitT : FitsLen (t + 2 * msg.length)) :
    ∃ cube', Scramble.update
        (Scramble.Scramble.mk 1 (embed ny) (Int.ofNat t) (Int.ofNat (8 * q)) (embedCube cube) st
          false false) (embed msg) =
      .ok (Scramble.Scramble.mk 1
          (embed ((ny ++ nybbles msg).drop (8 * ((ny ++ nybbles msg).length / 8))))
          (Int.ofNat (t + 2 * msg.length))
          (Int.ofNat (8 * (q + (ny ++ nybbles msg).length / 8))) (embedCube cube') st false
          false) ∧
      walkV1 cube (ny ++ nybbles msg) = some cube' ∧ Reach cube' := by
  have hny' : ∀ x ∈ ny ++ nybbles msg, x < 16 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hny x h
    · exact nybbles_lt msg hb x h
  have hlen : (ny ++ nybbles msg).length = ny.length + 2 * msg.length := by
    rw [List.length_append, nybbles_length]
  obtain ⟨c', hc', hw, hr⟩ := apply_ready_v1_digest (Int.ofNat (t + 2 * msg.length)) st false
    cube hR (ny ++ nybbles msg) hny' q (by rw [hlen, ← Nat.add_assoc]; exact hfitP)
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
      refine chain_eq _ _ _ (fun i => Scramble.Scramble.mk 1 (embed (ny ++ nybbles (msg.take i)))
          (Int.ofNat t) (Int.ofNat (8 * q)) (embedCube cube) st false false) 0 (msg.length - 1)
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

theorem padTailV1_lt (t : Nat) : ∀ x ∈ padTailV1 t, x < 16 := by
  have hc : ∀ x ∈ cycleV1, x < 16 := by decide
  have hg : ∀ i, cycleV1.getD (i % 8) 0 < 16 := by
    intro i
    have : i % 8 < 8 := Nat.mod_lt _ (by decide)
    have hall : ∀ j, j < 8 → cycleV1.getD j 0 < 16 := by decide
    exact hall _ this
  intro x hx
  simp only [padTailV1, tapeF, List.mem_cons, List.mem_append, List.mem_map] at hx
  rcases hx with rfl | hx | ⟨i, -, rfl⟩
  · decide
  · exact hc x (List.mem_of_mem_take hx)
  · exact hg i

theorem padTailV1_length (t : Nat) : (padTailV1 t).length ≤ 32 := by
  have h8 : ∀ k, k < 8 → (cycleV1.take k).length = k := by decide
  have hk : padKV1 t < 8 := Nat.mod_lt _ (by decide)
  simp only [padTailV1, tapeF, List.length_cons, List.length_append, List.length_map,
    List.length_range, h8 _ hk]
  omega

/-- `evaluate` on a digest-only v1 state (not done) with `total = t` and `processed = 8q`:
    `pad`, `apply_ready`, `finish`, `index_bytes` return `.ok`, and the digest is the model's
    `digestOf` after walking `pending ++ padTailV1 t` and seating. -/
theorem evaluate_v1_digest (ny : List Nat) (hny : ∀ x ∈ ny, x < 16) (t q : Nat) (cube : Cube)
    (hR : Reach cube) (st : Array Scramble.Step) (ht : FitsLen (t + 25))
    (hp : FitsLen (8 * q + ny.length + 40)) :
    ∃ ev s' d, Scramble.evaluate
        (Scramble.Scramble.mk 1 (embed ny) (Int.ofNat t) (Int.ofNat (8 * q)) (embedCube cube) st
          false false) = .ok (ev, s') ∧
      (walkV1 cube (ny ++ padTailV1 t) >>= seat >>= ScrambleV2.digestOf) = some d ∧
      ev.sudo_10Evaluation_6digest = embed d := by
  have hny' : ∀ x ∈ ny ++ padTailV1 t, x < 16 := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hny x h
    · exact padTailV1_lt t x h
  have hfit : FitsLen (8 * q + (ny ++ padTailV1 t).length + 8) :=
    FitsLen.of_le hp (by rw [List.length_append]; have := padTailV1_length t; omega)
  obtain ⟨c1, h1, hw, r1⟩ := apply_ready_v1_digest (Int.ofNat t) st false cube hR
    (ny ++ padTailV1 t) hny' q hfit
  obtain ⟨c2, h2, hseat, r2⟩ := finish_digest (Scramble.Scramble.mk 1
    (embed ((ny ++ padTailV1 t).drop (8 * ((ny ++ padTailV1 t).length / 8)))) (Int.ofNat t)
    (Int.ofNat (8 * (q + (ny ++ padTailV1 t).length / 8))) (embedCube c1) st false false)
    c1 r1 rfl rfl
  obtain ⟨d, hd, hidx⟩ := Reach.index_bytes c2 r2
  refine ⟨⟨embed d, st⟩, Scramble.Scramble.mk 1
    (embed ((ny ++ padTailV1 t).drop (8 * ((ny ++ padTailV1 t).length / 8)))) (Int.ofNat t)
    (Int.ofNat (8 * (q + (ny ++ padTailV1 t).length / 8))) (embedCube c2) st false true, d, ?_,
    by simp [hw, hseat, hd], rfl⟩
  unfold Scramble.evaluate
  simp only [show (!false) = true from rfl, sudoAssert_true, ok_bind]
  rw [pad_v1 (embed ny) t _ _ _ false false ht, ok_bind, ← embed_append, h1, ok_bind, h2, ok_bind]
  dsimp only
  rw [hidx]
  rfl

theorem scramble_v1_digest_refines :
    Scramble.scramble_v1_digest = Scramble.fresh (1 : Int) false := by
  unfold Scramble.scramble_v1_digest
  rfl

/-- LINK 2, v1 (digest only). For a byte message whose length leaves room in `i64`
    (`2·len + 40` fits), the digest-only v1 constructor `scramble_v1_digest`, then `update`,
    then `evaluate` all return `.ok`, and the evaluation's digest is the v1 model's
    `digestV1 msg`. The traced v1 constructor `scramble_v1` and its trace are not claimed. -/
theorem scramble_v1_digest_refines_digestV1 (msg : List Nat) (hb : ∀ b ∈ msg, b ≤ 255)
    (hlen : FitsLen (2 * msg.length + 40)) :
    ∃ s0 s1 ev s2, Scramble.scramble_v1_digest = .ok s0 ∧
      Scramble.update s0 (embed msg) = .ok s1 ∧
      Scramble.evaluate s1 = .ok (ev, s2) ∧
      ev.sudo_10Evaluation_6digest = embed (digestV1 msg) := by
  have hL : (nybbles msg).length = 2 * msg.length := nybbles_length msg
  obtain ⟨c1, hu, hw1, r1⟩ := update_v1_digest [] (by simp) 0 0 solvedCube ⟨_, reach_solved⟩ #[] msg
    hb (FitsLen.of_le hlen (by simp)) (FitsLen.of_le hlen (by simp))
  simp only [List.nil_append, Nat.zero_add] at hu hw1
  have hRl : ∀ x ∈ (nybbles msg).drop (8 * ((nybbles msg).length / 8)), x < 16 :=
    fun x hx => nybbles_lt msg hb x (List.mem_of_mem_drop hx)
  obtain ⟨ev, s2, d, he, hd, hdig⟩ := evaluate_v1_digest _ hRl (2 * msg.length)
    ((nybbles msg).length / 8) c1 r1 #[] (FitsLen.of_le hlen (by omega))
    (FitsLen.of_le hlen (by rw [List.length_drop, hL]; omega))
  refine ⟨_, _, ev, s2, ?_, hu, he, ?_⟩
  · rw [scramble_v1_digest_refines, fresh_refines]
    rfl
  · rw [hdig]
    congr 1
    have hsplit := List.take_append_drop (8 * ((nybbles msg).length / 8)) (nybbles msg)
    have htl : ((nybbles msg).take (8 * ((nybbles msg).length / 8))).length =
        8 * ((nybbles msg).length / 8) := by rw [List.length_take]; omega
    have hshort : ((nybbles msg).drop (8 * ((nybbles msg).length / 8))).length < 8 := by
      rw [List.length_drop]; omega
    have hX : walkV1 solvedCube ((nybbles msg).take (8 * ((nybbles msg).length / 8))) =
        some c1 := by
      rw [← hw1]
      conv => rhs; rw [← hsplit]
      rw [walkV1_append8 _ _ _ _ htl]
      cases walkV1 solvedCube ((nybbles msg).take (8 * ((nybbles msg).length / 8))) with
      | none => rfl
      | some c => exact (walkV1_short c _ hshort).symm
    have hv : digestV1? msg = some d := by
      unfold digestV1?
      have hpad : nybbles msg ++ padTailV1 (nybbles msg).length =
          (nybbles msg).take (8 * ((nybbles msg).length / 8)) ++
            ((nybbles msg).drop (8 * ((nybbles msg).length / 8)) ++ padTailV1 (2 * msg.length)) := by
        rw [← List.append_assoc, hsplit, hL]
      rw [padV1_eq, hpad, walkV1_append8 _ _ _ _ htl, hX]
      simpa [Option.bind_assoc] using hd
    simp [digestV1, hv]

end ScrambleV2.Link2
