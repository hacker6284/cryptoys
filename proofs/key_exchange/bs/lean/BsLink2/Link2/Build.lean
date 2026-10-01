/-
  BS Link 2: §4.2 BUILD. The emitted `build_key_grid`, `build_letting_go` and
  `grow_until_it_bumps` refine `Spec.buildKeyGrid`, `Spec.buildLettingGo` and
  `Spec.growUntilItBumps`, traps included: the emitted code succeeds with the embedded
  model result exactly when the model does, and traps exactly when the model fails. The
  let-go list is an arbitrary input. No probability. Proof-only.
-/
import BsLink2.Link2.Dice
import BsLink2.Link2.Opt

namespace BsLink2.Link2

open MegaDreifach.Link2

theorem atL_toOpt {α} (a : Array α) (i : Nat) : (SudoRt.atL a (Int.ofNat i)).toOption = a[i]? := by
  by_cases h : i < a.size
  · rw [atL_ofNat _ _ h, Array.getElem?_eq_getElem h]; rfl
  · have hf : (SudoRt.idxCheck a.size (Int.ofNat i)).toOption = none := by
      unfold SudoRt.idxCheck
      rw [if_pos (by simp; omega)]; rfl
    unfold SudoRt.atL
    rw [show a[i]? = none by simp; omega]
    revert hf
    cases SudoRt.idxCheck a.size (Int.ofNat i) with
    | error e => intro _; rfl
    | ok j => intro hf; cases hf

/-- Dice whose three streams have lengths that fit `i64` (so the read counts do). -/
def DiceFit (d : Spec.Dice) : Prop :=
  FitsLen d.d12.length ∧ FitsLen d.d6.length ∧ FitsLen d.d10.length

theorem sudoAssert_false_opt (line : Nat) : (SudoRt.sudoAssert false line).toOption = none := rfl

/-- §4.2: the emitted `roll_hole_die` is `Spec.rollHole`, traps included. -/
theorem roll_hole_die_spec (d : Spec.Dice) (hfit : FitsLen d.d12.length) :
    (Bs.roll_hole_die (embDice d)).toOption =
      (Spec.rollHole d).map (fun p => (Int.ofNat p.1, embDice p.2)) := by
  unfold Bs.roll_hole_die Spec.rollHole
  simp only [embDice]
  rw [toOpt_bind, atL_toOpt, List.getElem?_toArray]
  cases h : d.d12[d.next12]? with
  | none => rfl
  | some f =>
    have hlt : d.next12 < d.d12.length := by
      rcases List.getElem?_eq_some_iff.mp h with ⟨hl, _⟩; exact hl
    simp only [Option.some_bind]
    rw [toOpt_bind, addI_ofNat_one _ (FitsLen.of_le hfit hlt)]
    simp only [toOpt_ok, Option.some_bind]
    by_cases hf : 1 ≤ f ∧ f ≤ 12
    · have h1 : (decide (f ≥ 1)) = true := decide_eq_true hf.1
      have h2 : (decide (f ≤ 12)) = true := decide_eq_true hf.2
      simp only [h1, h2, if_true, if_pos hf, pure_eq_ok, ok_bind, sudoAssert_true, toOpt_bind,
        toOpt_ok, Option.some_bind, Option.map_some']
      have : Int.ofNat f.toNat = f := Int.toNat_of_nonneg (by omega)
      rw [this]
    · rw [if_neg hf]
      by_cases h1 : f ≥ 1
      · have h2 : ¬ f ≤ 12 := fun h2 => hf ⟨h1, h2⟩
        simp only [decide_eq_true h1, decide_eq_false h2, if_true, pure_eq_ok, ok_bind,
          toOpt_bind, sudoAssert_false_opt]; rfl
      · simp only [decide_eq_false h1, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind,
          toOpt_bind, sudoAssert_false_opt]; rfl

/-- §4.2: the emitted `roll_d6` is `Spec.rollD6`, traps included. -/
theorem roll_d6_spec (d : Spec.Dice) (hfit : FitsLen d.d6.length) :
    (Bs.roll_d6 (embDice d)).toOption =
      (Spec.rollD6 d).map (fun p => (Int.ofNat p.1, embDice p.2)) := by
  unfold Bs.roll_d6 Spec.rollD6
  simp only [embDice]
  rw [toOpt_bind, atL_toOpt, List.getElem?_toArray]
  cases h : d.d6[d.next6]? with
  | none => rfl
  | some f =>
    have hlt : d.next6 < d.d6.length := by
      rcases List.getElem?_eq_some_iff.mp h with ⟨hl, _⟩; exact hl
    simp only [Option.some_bind]
    rw [toOpt_bind, addI_ofNat_one _ (FitsLen.of_le hfit hlt)]
    simp only [toOpt_ok, Option.some_bind]
    by_cases hf : 1 ≤ f ∧ f ≤ 6
    · have h1 : (decide (f ≥ 1)) = true := decide_eq_true hf.1
      have h2 : (decide (f ≤ 6)) = true := decide_eq_true hf.2
      simp only [h1, h2, if_true, if_pos hf, pure_eq_ok, ok_bind, sudoAssert_true, toOpt_bind,
        toOpt_ok, Option.some_bind, Option.map_some']
      have : Int.ofNat f.toNat = f := Int.toNat_of_nonneg (by omega)
      rw [this]
    · rw [if_neg hf]
      by_cases h1 : f ≥ 1
      · have h2 : ¬ f ≤ 6 := fun h2 => hf ⟨h1, h2⟩
        simp only [decide_eq_true h1, decide_eq_false h2, if_true, pure_eq_ok, ok_bind,
          toOpt_bind, sudoAssert_false_opt]; rfl
      · simp only [decide_eq_false h1, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind,
          toOpt_bind, sudoAssert_false_opt]; rfl

/-! ### throw_d10 -/

/-- One iteration of `throw_d10`'s loop on model dice: read face `i`, stop on 1–9, go on
    after a zero, fail on a face off the die. The state is (last face, dice). -/
def d10Step (i : Nat) (s : Int × Spec.Dice) : Option ((Int × Spec.Dice) ⊕ (Int × Spec.Dice)) :=
  match s.2.d10[i]? with
  | none => none
  | some f =>
    if 0 ≤ f ∧ f ≤ 9 then
      some (if f = 0 then .inl (f, { s.2 with next10 := i + 1 }) else .inr (f, { s.2 with next10 := i + 1 }))
    else none

def d10After (s : Int × Spec.Dice) : Option (Int × Bs.Dice) :=
  if s.1 = 0 then none else some (s.1, embDice s.2)

theorem d10_fold (D : List Int) : ∀ k i (dd : Spec.Dice), dd.d10 = D → i + k = D.length →
    (brkFold d10Step i k ((0 : Int), dd)).bind d10After =
      (Spec.d10Scan (D.drop i) i).map (fun p => (Int.ofNat p.1, embDice { dd with next10 := p.2 }))
  | 0, i, dd, _, hk => by
    rw [List.drop_of_length_le (by omega)]; rfl
  | k + 1, i, dd, hD, hk => by
    have hi : i < D.length := by omega
    rw [List.drop_eq_getElem_cons hi]
    simp only [brkFold, d10Step, hD, List.getElem?_eq_getElem hi, Spec.d10Scan]
    by_cases hr : 0 ≤ D[i] ∧ D[i] ≤ 9
    · rw [if_pos hr, if_pos hr]
      by_cases h0 : D[i] = 0
      · rw [if_pos h0, if_pos h0]
        simp only [Option.some_bind]
        have := d10_fold D k (i + 1) { dd with next10 := i + 1 } hD (by omega)
        rw [h0]; subst hD; exact this
      · rw [if_neg h0, if_neg h0]
        simp only [Option.some_bind, d10After, Option.map_some', if_neg h0]
        simp only [ofNat_eq_natCast, Int.toNat_of_nonneg hr.1]
    · rw [if_neg hr, if_neg hr]; rfl

theorem throw_d10_spec (d : Spec.Dice) (hfit : FitsLen d.d10.length) :
    (Bs.throw_d10 (embDice d)).toOption =
      (Spec.throwD10 d).map (fun p => (Int.ofNat p.1, embDice p.2)) := by
  unfold Bs.throw_d10 Spec.throwD10
  have hlen : SudoRt.listLen (embDice d).sudo_4Dice_3d10 = Int.ofNat d.d10.length := by
    simp [embDice, listLen_eq]
  rw [hlen, subI_len_one _ hfit, ok_bind, except_bind_pure, fuelRange_eq]
  rw [show (embDice d).sudo_4Dice_6next10 = Int.ofNat d.next10 from rfl]
  rw [Option.map_map]
  by_cases ht : d.next10 < d.d10.length
  · rw [show Int.ofNat d.d10.length - 1 = Int.ofNat (d.d10.length - 1) by
      simp only [ofNat_eq_natCast]; omega]
    refine (loop_brk_opt (S := Int × Spec.Dice) (fun s => (s.1, embDice s.2)) _ _ _ d10Step
      d10After d.next10 d.d10.length ht ?_ ?_ ((0 : Int), d)).trans ?_
    · intro i s hi1 hi2
      obtain ⟨f0, dd⟩ := s
      dsimp only
      rw [if_neg (by simp only [ofNat_eq_natCast]; omega)]
      simp only [embDice]
      rw [toOpt_bind, toOpt_bind, atL_toOpt, List.getElem?_toArray]
      unfold d10Step
      dsimp only
      cases hf : dd.d10[i]? with
      | none => rfl
      | some f =>
        simp only [Option.some_bind]
        rw [toOpt_bind, addI_ofNat_one _ (FitsLen.of_le hfit (show i + 1 ≤ d.d10.length by omega)),
          toOpt_ok, Option.some_bind]
        have hbeq : (Int.ofNat i == Int.ofNat (d.d10.length - 1)) = decide (i + 1 = d.d10.length) := by
          by_cases hl : i + 1 = d.d10.length
          · rw [decide_eq_true hl]; apply beq_iff_eq.mpr; congr 1; omega
          · rw [decide_eq_false hl]; apply beq_false_of_ne; intro h; have := Int.ofNat.inj h; omega
        by_cases hr : 0 ≤ f ∧ f ≤ 9
        · rw [if_pos hr]
          simp only [decide_eq_true hr.1, decide_eq_true hr.2, if_true, pure_eq_ok, ok_bind,
            sudoAssert_true]
          by_cases h0 : f = 0
          · subst h0
            simp only [if_pos rfl, SudoRt.SEq.beq, decide_True, Bool.not_true, Bool.false_eq_true,
              if_false, toOpt_ok, Option.some_bind, Option.map_some', hbeq]
            by_cases hl : i + 1 = d.d10.length
            · simp only [hl, decide_True, if_true, toOpt_ok]
            · simp only [hl, decide_False, Bool.false_eq_true, if_false, toOpt_bind,
                addI_ofNat_one _ (FitsLen.of_le hfit (show i + 1 ≤ d.d10.length by omega)), toOpt_ok,
                Option.some_bind]; rfl
          · simp only [if_neg h0, SudoRt.SEq.beq, decide_eq_false h0, Bool.not_false, if_true,
              toOpt_ok, Option.some_bind, Option.map_some']
        · rw [if_neg hr]
          by_cases h1 : 0 ≤ f
          · have h2 : ¬ f ≤ 9 := fun h2 => hr ⟨h1, h2⟩
            simp only [decide_eq_true h1, decide_eq_false h2, if_true, pure_eq_ok, ok_bind]; rfl
          · simp only [decide_eq_false h1, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]; rfl
    · intro j s
      obtain ⟨f0, dd⟩ := s
      unfold d10After
      dsimp only
      by_cases h0 : f0 = 0
      · subst h0; rfl
      · simp only [if_neg h0, SudoRt.SEq.beq, decide_eq_false h0, Bool.not_false, sudoAssert_true,
          ok_bind, toOpt_ok]; rfl
    · rw [d10_fold d.d10 _ d.next10 d rfl (by omega)]
      congr 1
  · refine (congrArg Except.toOption (loop_opt_empty (S := Int × Spec.Dice)
      (fun s => (s.1, embDice s.2)) _ _ _ d.next10 _ ?_ ((0 : Int), d) ?_)).trans ?_
    · simp only [ofNat_eq_natCast]; omega
    · dsimp only; rw [if_pos (by simp only [ofNat_eq_natCast]; omega)]; rfl
    · rw [List.drop_of_length_le (by omega)]; rfl

theorem throwD10_d10 {d d' : Spec.Dice} {f : Nat} (h : Spec.throwD10 d = some (f, d')) :
    d'.d10 = d.d10 := by
  unfold Spec.throwD10 at h
  cases hs : Spec.d10Scan (d.d10.drop d.next10) d.next10 with
  | none => rw [hs] at h; cases h
  | some p => rw [hs] at h; cases h; rfl

theorem embed_snoc (l : List Nat) (x : Nat) : embed (l ++ [x]) = (embed l).push (Int.ofNat x) := by
  simp [embed, Array.push]

theorem bind_some_map {α β} (o : Option α) (f : α → β) : o.bind (fun a => some (f a)) = o.map f := by
  cases o <;> rfl

/-- A fold whose step ignores the index does not care where the range starts. -/
theorem foldlM_range'_shift {S} (g : S → Option S) (a b : Nat) : ∀ (k : Nat) (s : S),
    (List.range' a k).foldlM (fun s _ => g s) s = (List.range' b k).foldlM (fun s _ => g s) s
  | 0, _ => rfl
  | k + 1, s => by
    simp only [List.range', List.foldlM_cons]
    cases g s with
    | none => rfl
    | some s' => exact foldlM_range'_shift g (a + 1) (b + 1) k s'

/-! ### throw_row_cup -/

/-- §4.2: the emitted `throw_row_cup` is `Spec.throwRowCup` (five d10s), traps included. -/
theorem throw_row_cup_spec (d : Spec.Dice) (hfit : FitsLen d.d10.length) :
    (Bs.throw_row_cup (embDice d)).toOption =
      (Spec.throwRowCup d).map (fun p => (embed p.1, embDice p.2)) := by
  unfold Bs.throw_row_cup Spec.throwRowCup
  simp only [Bs.cup_dice]
  rw [except_bind_pure, fuelRange_eq]
  refine (loop_opt (S := List Nat × Spec.Dice) (fun s => (embDice s.2, embed s.1)) _ _ _
    (fun _ s => (Spec.throwD10 s.2).map (fun p => (s.1 ++ [p.1], p.2)))
    (fun _ s => s.2.d10 = d.d10) (fun s => some (embed s.1, embDice s.2)) 1 6 (by decide)
    ?_ ?_ ?_ ([], d) rfl).trans ?_
  · intro i s hi1 hi2 hP
    obtain ⟨tr, dd⟩ := s
    dsimp only at hP ⊢
    rw [if_neg (by simp only [ofNat_eq_natCast]; omega), toOpt_bind, toOpt_bind,
      throw_d10_spec dd (by rw [hP]; exact hfit)]
    cases ht : Spec.throwD10 dd with
    | none => rfl
    | some p =>
      obtain ⟨f, dd'⟩ := p
      simp only [Option.map_some', Option.some_bind, appendL_spec, ← embed_snoc]
      by_cases hl : i + 1 = 6
      · have : i = 5 := by omega
        subst this; rfl
      · have hb : (Int.ofNat i == (5 : Int)) = false := by
          apply beq_false_of_ne; intro h
          have := Int.ofNat.inj (h.trans (show (5 : Int) = Int.ofNat 5 from rfl)); omega
        simp only [hb, Bool.false_eq_true, if_false, if_neg hl, toOpt_bind,
          addI_ofNat_one _ (fits_small (show i + 1 ≤ 1000 by omega)), toOpt_ok, Option.some_bind]
        rfl
  · intro i s s' _ _ hP hm
    obtain ⟨tr, dd⟩ := s
    cases ht : Spec.throwD10 dd with
    | none => simp [ht] at hm
    | some p =>
      simp only [ht, Option.map_some', Option.some.injEq] at hm
      subst hm
      exact (throwD10_d10 ht).trans hP
  · intro j s _; rfl
  · rw [show List.range 5 = List.range' 0 5 from List.range_eq_range' 5]
    rw [foldlM_range'_shift _ 1 0 5]
    exact bind_some_map _ _

/-! ### rethrow_unread -/

theorem embed_set (l : List Nat) (k x : Nat) (h : k < (embed l).size) :
    (embed l).set ⟨k, h⟩ (Int.ofNat x) = embed (l.set k x) := by
  simp [embed, Array.set, List.map_set]

theorem size_embed' (l : List Nat) : (embed l).size = l.length := by simp [embed]

/-- §4.2 letting go: the emitted `rethrow_unread` is `Spec.rethrowUnread`, traps included. -/
theorem rethrow_unread_spec (d : Spec.Dice) (tray : List Nat) (read : Nat)
    (hfit : FitsLen d.d10.length) (htr : FitsLen tray.length) :
    (Bs.rethrow_unread (embDice d) (embed tray) (Int.ofNat read)).toOption =
      (Spec.rethrowUnread d tray read).map (fun p => (embDice p.1, embed p.2)) := by
  unfold Bs.rethrow_unread Spec.rethrowUnread
  rw [listLen_embed, subI_len_one _ htr, ok_bind, except_bind_pure, fuelRange_eq]
  by_cases hr : read < tray.length
  · rw [show Int.ofNat tray.length - 1 = Int.ofNat (tray.length - 1) by
      simp only [ofNat_eq_natCast]; omega]
    refine (loop_opt (S := Spec.Dice × List Nat) (fun s => (embed s.2, embDice s.1)) _ _ _
      (fun k s => (Spec.throwD10 s.1).map (fun p => (p.2, s.2.set k p.1)))
      (fun _ s => s.1.d10 = d.d10 ∧ s.2.length = tray.length)
      (fun s => some (embDice s.1, embed s.2)) read tray.length hr ?_ ?_ ?_ (d, tray)
      ⟨rfl, rfl⟩).trans ?_
    · intro i s hi1 hi2 hP
      obtain ⟨dd, tr⟩ := s
      dsimp only at hP ⊢
      rw [if_neg (by simp only [ofNat_eq_natCast]; omega), toOpt_bind, toOpt_bind,
        throw_d10_spec dd (by rw [hP.1]; exact hfit)]
      cases ht : Spec.throwD10 dd with
      | none => rfl
      | some p =>
        obtain ⟨f, dd'⟩ := p
        have hi : i < (embed tr).size := by rw [size_embed']; omega
        simp only [Option.map_some', Option.some_bind]
        rw [toOpt_bind, putL_ofNat _ _ _ hi, toOpt_ok, Option.some_bind, embed_set]
        by_cases hl : i + 1 = tray.length
        · have hb : (Int.ofNat i == Int.ofNat (tray.length - 1)) = true := by
            apply beq_iff_eq.mpr; congr 1; omega
          simp only [hb, if_true, if_pos hl, toOpt_ok]
          rfl
        · have hb : (Int.ofNat i == Int.ofNat (tray.length - 1)) = false := by
            apply beq_false_of_ne; intro h; have := Int.ofNat.inj h; omega
          simp only [hb, Bool.false_eq_true, if_false, if_neg hl, toOpt_bind,
            addI_ofNat_one _ (FitsLen.of_le htr (show i + 1 ≤ tray.length by omega)), toOpt_ok,
            Option.some_bind]
          rfl
    · intro i s s' _ _ hP hm
      obtain ⟨dd, tr⟩ := s
      cases ht : Spec.throwD10 dd with
      | none => simp [ht] at hm
      | some p =>
        simp only [ht, Option.map_some', Option.some.injEq] at hm
        subst hm
        exact ⟨(throwD10_d10 ht).trans hP.1, by rw [List.length_set]; exact hP.2⟩
    · intro j s _; rfl
    · exact bind_some_map _ _
  · refine (congrArg Except.toOption (loop_opt_empty (S := Spec.Dice × List Nat)
      (fun s => (embed s.2, embDice s.1)) _ _ _ read _ ?_ (d, tray) ?_)).trans ?_
    · simp only [ofNat_eq_natCast]; omega
    · dsimp only; rw [if_pos (by simp only [ofNat_eq_natCast]; omega)]; rfl
    · rw [show tray.length - read = 0 by omega]; rfl

/-! ### Let-go lists -/

/-- A model let-go point as the emitted record. -/
def embLetGo (x : Spec.LetGo) : Bs.LetGo := ⟨x.hole, x.gap⟩

/-- A model let-go list as the emitted array. -/
def embLG (lg : List Spec.LetGo) : Array Bs.LetGo := (lg.map embLetGo).toArray

theorem size_embLG (lg : List Spec.LetGo) : (embLG lg).size = lg.length := by simp [embLG]

theorem embLG_get (lg : List Spec.LetGo) (i : Nat) (h : i < (embLG lg).size) :
    (embLG lg)[i] = embLetGo (lg[i]'(by rw [size_embLG] at h; exact h)) := by
  simp [embLG]

/-- §4.2: the emitted `lets_go` is `Spec.letsGo`; it never traps. -/
theorem lets_go_spec (lg : List Spec.LetGo) (hole : Nat) (gap : Bool) (hfit : FitsLen lg.length) :
    Bs.lets_go (embLG lg) (Int.ofNat hole) gap = .ok (Spec.letsGo lg hole gap) := by
  unfold Bs.lets_go
  rw [show SudoRt.listLen (embLG lg) = Int.ofNat lg.length by rw [listLen_eq, size_embLG],
    subI_len_one _ hfit, ok_bind, except_bind_pure, fuelRange_eq]
  cases hl : lg.length with
  | zero =>
    have : lg = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    rfl
  | succ n =>
    rw [show Int.ofNat (n + 1) - 1 = Int.ofNat n by simp only [ofNat_eq_natCast]; omega]
    refine asc_scan_ret_goal true _ _ _
      (fun i => if h : i < lg.length then decide (lg[i].hole = Int.ofNat hole) && lg[i].gap == gap
        else false) 0 n (Nat.zero_le _) _ ?_ ?_ ?_
    · intro i _ hi
      have hi' : i < lg.length := by omega
      have hi'' : i < (embLG lg).size := by rw [size_embLG]; omega
      dsimp only
      rw [if_neg (by simp only [ofNat_eq_natCast]; omega), atL_ofNat _ _ hi'', ok_bind,
        embLG_get, dif_pos hi']
      simp only [embLetGo, SudoRt.SEq.beq]
      by_cases hh : lg[i].hole = Int.ofNat hole
      · simp only [hh, decide_True, if_true, atL_ofNat _ _ hi'', ok_bind, embLG_get, pure_eq_ok,
          ok_bind, Bool.true_and]
        cases lg[i].gap <;> cases gap <;> simp <;> by_cases hn : i = n <;> simp [hn] <;>
          (first | rfl | (rw [if_neg (by omega), show ((i : Int)) = Int.ofNat i from rfl,
          addI_ofNat_one i (FitsLen.of_le hfit (show i + 1 ≤ lg.length by omega))]; rfl))
      · simp only [hh, decide_False, if_false, pure_eq_ok, ok_bind, Bool.false_and,
          Bool.false_eq_true]
        by_cases hn : i = n <;> simp [hn] <;>
          (first | rfl | (rw [if_neg (by omega), show ((i : Int)) = Int.ofNat i from rfl,
          addI_ofNat_one i (FitsLen.of_le hfit (show i + 1 ≤ lg.length by omega))]; rfl))
    · intro hall
      unfold Spec.letsGo
      have : lg.any (fun x => decide (x.hole = Int.ofNat hole) && x.gap == gap) = false := by
        rw [List.any_eq_false]
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have := hall i (Nat.zero_le _) (by omega)
        dsimp only at this
        rw [dif_pos hi] at this
        rw [this]; decide
      rw [this]; rfl
    · intro i _ hi hb
      have hi' : i < lg.length := by omega
      dsimp only at hb
      rw [dif_pos hi'] at hb
      unfold Spec.letsGo
      have : lg.any (fun x => decide (x.hole = Int.ofNat hole) && x.gap == gap) = true :=
        List.any_eq_true.mpr ⟨lg[i], List.getElem_mem hi', hb⟩
      rw [this]; rfl

end BsLink2.Link2
