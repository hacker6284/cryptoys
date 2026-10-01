/-
  BS Link 2: §4.2 BUILD. The emitted `build_key_grid`, `build_letting_go` and
  `grow_until_it_bumps` refine `Spec.buildKeyGrid`, `Spec.buildLettingGo` and
  `Spec.growUntilItBumps`, traps included: the emitted code succeeds with the embedded
  model result exactly when the model does, and traps exactly when the model fails. The
  let-go list is an arbitrary input. No probability. Proof-only.
-/
import BsLink2.Link2.Dice
import BsLink2.Link2.Key
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

theorem beq_embLetGo (a b : Spec.LetGo) :
    SudoRt.SEq.beq (embLetGo a) (embLetGo b) = decide (a = b) := by
  obtain ⟨h1, g1⟩ := a
  obtain ⟨h2, g2⟩ := b
  show (decide (h1 = h2) && decide (g1 = g2)) = _
  by_cases e1 : h1 = h2 <;> by_cases e2 : g1 = g2 <;> simp [e1, e2]

open Classical in
/-- Whether entry `i` of the list equals a later one (classical; a proof device). -/
noncomputable def dupAt (lg : List Spec.LetGo) (i : Nat) : Bool :=
  if ∃ j, ∃ (hi : i < lg.length) (hj : j < lg.length), i < j ∧ lg[i] = lg[j] then true else false

theorem nodup_iff_dupAt (lg : List Spec.LetGo) :
    lg.Nodup ↔ ∀ i, i < lg.length → dupAt lg i = false := by
  unfold List.Nodup
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i hi
    unfold dupAt
    rw [if_neg]
    rintro ⟨j, hi', hj, hij, he⟩
    exact h i j hi' hj hij he
  · intro h i j hi hj hij he
    have := h i hi
    unfold dupAt at this
    rw [if_pos ⟨j, hi, hj, hij, he⟩] at this
    cases this

/-- §4.2: the emitted `letgo_unique` says whether the let-go list has no repeats. -/
theorem letgo_unique_spec (lg : List Spec.LetGo) (hfit : FitsLen lg.length) :
    Bs.letgo_unique (embLG lg) = .ok (decide lg.Nodup) := by
  unfold Bs.letgo_unique
  rw [show SudoRt.listLen (embLG lg) = Int.ofNat lg.length by rw [listLen_eq, size_embLG],
    subI_len_one _ hfit, ok_bind, except_bind_pure, fuelRange_eq]
  cases hl : lg.length with
  | zero =>
    have : lg = [] := List.eq_nil_of_length_eq_zero hl
    subst this
    rfl
  | succ n =>
    rw [show Int.ofNat (n + 1) - 1 = Int.ofNat n by simp only [ofNat_eq_natCast]; omega]
    refine asc_scan_ret_goal false _ _ _ (dupAt lg) 0 n (Nat.zero_le _) _ ?_ ?_ ?_
    · intro i _ hi
      dsimp only
      rw [if_neg (by simp only [ofNat_eq_natCast]; omega),
        addI_ofNat_one _ (FitsLen.of_le hfit (show i + 1 ≤ lg.length by omega)), ok_bind,
        ok_bind, except_bind_pure, fuelRange_eq]
      have hinner : ∀ (R : Except SudoRt.Trap (SudoRt.Flow Unit Bool)),
          R = .ok (if dupAt lg i then .ret false else .cont ()) → ∀ step after,
          (∀ j, i + 1 ≤ j → j ≤ n → step (Int.ofNat j) =
            if (if h : j < lg.length ∧ i < lg.length then decide (lg[i] = lg[j]) else false)
            then .ok (.ret false)
            else if j = n then .ok (.brk (Int.ofNat j)) else .ok (.cont (Int.ofNat (j + 1)))) →
          (∀ j, after j = .ok (.cont ())) → 
          (Int.ofNat (i + 1) > Int.ofNat n → step (Int.ofNat (i + 1)) = .ok (.brk (Int.ofNat (i + 1)))) →
          SudoRt.runLoopOn (Int.ofNat (i + 1)) (fuelRange (Int.ofNat (i + 1)) (Int.ofNat n))
            step after (fun r => pure (SudoRt.Flow.ret r)) = R := by
        intro R hR step after hst haf hemp
        by_cases hlast : i = n
        · subst hlast
          have hgt : Int.ofNat (i + 1) > Int.ofNat i := by simp only [ofNat_eq_natCast]; omega
          rw [fuelRange_gt hgt, show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, hemp hgt]
          have hd : dupAt lg i = false := by
            unfold dupAt
            rw [if_neg (by rintro ⟨j, _, hj, hij, _⟩; omega)]
          rw [hR, hd]
          exact haf _
        · refine asc_scan_ret_goal false step after _ _ (i + 1) n (by omega) R hst ?_ ?_
          · intro hall
            have hd : dupAt lg i = false := by
              unfold dupAt
              rw [if_neg]
              rintro ⟨j, hi', hj, hij, he⟩
              have := hall j (by omega) (by omega)
              rw [dif_pos ⟨hj, hi'⟩, decide_eq_true he] at this
              cases this
            rw [hR, haf, hd]; rfl
          · intro j h1 h2 hb
            rw [hR]
            have hj : j < lg.length ∧ i < lg.length := by omega
            rw [dif_pos hj] at hb
            have hex : ∃ j, ∃ (hi : i < lg.length) (hj : j < lg.length), i < j ∧ lg[i] = lg[j] :=
              ⟨j, hj.2, hj.1, by omega, of_decide_eq_true hb⟩
            have hd : dupAt lg i = true := by unfold dupAt; rw [if_pos hex]
            rw [hd]; rfl
      rw [hinner _ rfl]
      · by_cases hd : dupAt lg i = true
        · rw [if_pos hd, if_pos hd]; rfl
        · rw [if_neg hd, if_neg hd]
          by_cases hn : i = n
          · subst hn; rw [if_pos rfl]; simp; rfl
          · have hb : (Int.ofNat i == Int.ofNat n) = false := by
              apply beq_false_of_ne; intro h; have := Int.ofNat.inj h; omega
            rw [if_neg hn]; simp only [hb]; rfl
      · intro j h1 h2
        have hj : j < lg.length := by omega
        have hi' : i < lg.length := by omega
        rw [if_neg (by simp only [ofNat_eq_natCast]; omega),
          atL_ofNat _ _ (by rw [size_embLG]; exact hi'), ok_bind,
          atL_ofNat _ _ (by rw [size_embLG]; exact hj), ok_bind, embLG_get, embLG_get,
          beq_embLetGo, dif_pos ⟨hj, hi'⟩]
        by_cases he : lg[i] = lg[j]
        · simp only [decide_eq_true he, if_true]; rfl
        · simp only [decide_eq_false he, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]
          by_cases hn : j = n
          · subst hn; simp
          · have hb : (Int.ofNat j == Int.ofNat n) = false := by
              apply beq_false_of_ne; intro h; have := Int.ofNat.inj h; omega
            simp only [hb, if_neg hn, Bool.false_eq_true, if_false,
              addI_ofNat_one _ (FitsLen.of_le hfit (show j + 1 ≤ lg.length by omega)), ok_bind]
      · intro j; rfl
      · intro hgt; dsimp only; rw [if_pos hgt]; rfl
    · intro hall
      rw [decide_eq_true ((nodup_iff_dupAt lg).mpr (fun i hi => hall i (Nat.zero_le _) (by omega)))]
      rfl
    · intro i _ hi hb
      have : ¬ lg.Nodup := fun h => by
        rw [(nodup_iff_dupAt lg).mp h i (by omega)] at hb; cases hb
      rw [decide_eq_false this]
      rfl

/-! ### keypad, has_room, cover -/

/-- §4.2 step 2: the emitted `keypad_first` is `Spec.keypadFirst` on faces `≥ 1`. -/
theorem keypad_first_spec (f : Nat) (hf : 1 ≤ f) (hfit : FitsLen f) :
    Bs.keypad_first (Int.ofNat f) = .ok (Int.ofNat (Spec.keypadFirst f)) := by
  unfold Bs.keypad_first Spec.keypadFirst
  rw [subI_ofNat_one _ hf hfit, ok_bind, show (3 : Int) = Int.ofNat 3 from rfl,
    divI_ofNat _ (by decide), except_bind_pure]

/-- §4.2 step 2: the emitted `keypad_second` is `Spec.keypadSecond` on faces `≥ 1`. -/
theorem keypad_second_spec (f : Nat) (hf : 1 ≤ f) (hfit : FitsLen f) :
    Bs.keypad_second (Int.ofNat f) = .ok (Int.ofNat (Spec.keypadSecond f)) := by
  unfold Bs.keypad_second Spec.keypadSecond
  rw [subI_ofNat_one _ hf hfit, ok_bind, show (3 : Int) = Int.ofNat 3 from rfl,
    modI_ofNat _ (by decide), except_bind_pure]
  congr 2
  omega

/-- §4.2 step 1: the emitted `has_room` is `Spec.hasRoom` on the covered table. -/
theorem has_room_spec (cov : Nat → Bool) (row col : Nat) :
    Bs.has_room (tab cov) (Int.ofNat row) (Int.ofNat col) = .ok (Spec.hasRoom cov row col) := by
  unfold Bs.has_room Spec.hasRoom
  simp only [Bs.grid_rows, Bs.grid_cols]
  by_cases hr : row < 10
  · have h1 : decide (Int.ofNat row ≥ 10) = false := by
      apply decide_eq_false; simp only [ofNat_eq_natCast]; omega
    rw [h1]
    by_cases hc : col < 10
    · have h2 : decide (Int.ofNat col ≥ 10) = false := by
        apply decide_eq_false; simp only [ofNat_eq_natCast]; omega
      simp only [h2, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]
      rw [show (10 : Int) = Int.ofNat 10 from rfl, mulI_ofNat _ _ (fits_small (by omega)), ok_bind,
        addI_ofNat _ _ (fits_small (by omega)), ok_bind,
        atL_ofNat _ _ (by rw [tab_size]; omega), ok_bind, tab_get]
      simp [hr, hc]
    · have h2 : decide (Int.ofNat col ≥ 10) = true := by
        apply decide_eq_true; simp only [ofNat_eq_natCast]; omega
      simp only [h2, if_true, Bool.false_eq_true, if_false, pure_eq_ok, ok_bind]
      simp [hc]
  · have h1 : decide (Int.ofNat row ≥ 10) = true := by
      apply decide_eq_true; simp only [ofNat_eq_natCast]; omega
    rw [h1]
    simp [hr]; rfl

/-- Covering a ship's holes. -/
theorem cover_spec (cov : Nat → Bool) (s : Spec.Ship) (hs : s.OnGrid) :
    Bs.cover (tab cov) (embShip s) = .ok (tab (Spec.cover cov s)) := by
  unfold Bs.cover
  rw [ship_holes_spec s hs, ok_bind]
  dsimp only
  rw [listLen_embed,
    subI_len_one _ (fits_small (by have := s.kind.len_le_five; simp [Spec.Ship.holes]; omega)),
    ok_bind, except_bind_pure, fuelRange_eq]
  refine asc_goal_upto (fun i (c : Array Bool) =>
      c = tab (fun h => cov h || decide (h ∈ s.holes.take i))) (by simp) ?_ ?_ ?_
  · intro hn
    have := s.kind.two_le_len
    simp [Spec.Ship.holes] at hn; omega
  · intro i c hi hI
    subst hI
    have hlt : i < (embed s.holes).size := by rw [size_embed']; exact hi
    have hh : s.holes[i] < 100 := holes_lt s hs (List.getElem_mem hi)
    refine ⟨tab (fun h => cov h || decide (h ∈ s.holes.take (i + 1))), rfl, ?_⟩
    dsimp only
    rw [if_neg (not_gt_len hi), atL_ofNat _ _ hlt, ok_bind]
    have hget : (embed s.holes)[i] = Int.ofNat s.holes[i] := by simp [embed]
    rw [hget, putL_ofNat _ _ _ (by rw [tab_size]; exact hh), ok_bind, tab_set]
    have htab : tab (fun h => if h = s.holes[i] then true
        else (cov h || decide (h ∈ s.holes.take i))) =
        tab (fun h => cov h || decide (h ∈ s.holes.take (i + 1))) := by
      congr 1; funext h
      rw [List.take_succ, List.getElem?_eq_getElem hi]
      by_cases e : h = s.holes[i]
      · subst e; simp
      · simp [e]
    rw [htab, pure_eq_ok, ok_bind]
    dsimp only
    exact asc_tail_len _ _ hi (fits_small (by
      have := s.kind.len_le_five; simp [Spec.Ship.holes] at hi; omega)) _
  · intro j c hI
    subst hI
    rw [List.take_of_length_le (Nat.le_refl _)]
    rfl

/-! ### grow_until_it_bumps -/

open Bs in
/-- The body of `grow_until_it_bumps`'s growing loop, copied verbatim from the emitted code
    (both headings share it; `lay_down` is the heading). A proof device: the theorem below
    is about the emitted function itself. -/
def growStepE (covered : Array Bool) (row col : Int) (lay_down : Bool) (_toV : Int) :
    Int × (Dice × Int) → Except SudoRt.Trap (SudoRt.Flow (Int × (Dice × Int)) ((Option Ship) × Dice)) :=
  fun σ =>
    let grow := σ.1
    let d := σ.2.1
    let _sp508 := σ.2.2
    let len := _sp508
    do
      if grow > _toV then
        pure (SudoRt.Flow.brk (ρ := (Option (Ship)) × (Dice)) (grow, (d, len)))
      else
        match ← ((do
  let next_row := row
  let _t475 ← SudoRt.addI col len
  let next_col := _t475
  if lay_down then
    do
      let _t476 ← SudoRt.addI row len
      let next_row := _t476
      let next_col := col
      let _t477 ← has_room covered next_row next_col
      if (!( _t477 )) then
        do
          pure (SudoRt.Flow.brk (ρ := (Option (Ship)) × (Dice)) (d, len))
      else
        do
          let need := (6 : Int)
          if (SudoRt.SEq.beq len (2 : Int)) then
            do
              let need := (4 : Int)
              let _io479 ← roll_d6 d
              let ⟨_ret480, _iw0481⟩ := _io479
              let d := _iw0481
              let _sudo_h0 := _ret480
              if (decide (_sudo_h0 ≥ need)) then
                do
                  let _t483 ← SudoRt.addI len (1 : Int)
                  let len := _t483
                  pure (SudoRt.Flow.cont (ρ := (Option (Ship)) × (Dice)) (d, len))
              else
                do
                  pure (SudoRt.Flow.brk (ρ := (Option (Ship)) × (Dice)) (d, len))
          else
            do
              let _io484 ← roll_d6 d
              let ⟨_ret485, _iw0486⟩ := _io484
              let d := _iw0486
              let _sudo_h0 := _ret485
              if (decide (_sudo_h0 ≥ need)) then
                do
                  let _t488 ← SudoRt.addI len (1 : Int)
                  let len := _t488
                  pure (SudoRt.Flow.cont (ρ := (Option (Ship)) × (Dice)) (d, len))
              else
                do
                  pure (SudoRt.Flow.brk (ρ := (Option (Ship)) × (Dice)) (d, len))
  else
    do
      let _t489 ← has_room covered next_row next_col
      if (!( _t489 )) then
        do
          pure (SudoRt.Flow.brk (ρ := (Option (Ship)) × (Dice)) (d, len))
      else
        do
          let need := (6 : Int)
          if (SudoRt.SEq.beq len (2 : Int)) then
            do
              let need := (4 : Int)
              let _io491 ← roll_d6 d
              let ⟨_ret492, _iw0493⟩ := _io491
              let d := _iw0493
              let _sudo_h0 := _ret492
              if (decide (_sudo_h0 ≥ need)) then
                do
                  let _t495 ← SudoRt.addI len (1 : Int)
                  let len := _t495
                  pure (SudoRt.Flow.cont (ρ := (Option (Ship)) × (Dice)) (d, len))
              else
                do
                  pure (SudoRt.Flow.brk (ρ := (Option (Ship)) × (Dice)) (d, len))
          else
            do
              let _io496 ← roll_d6 d
              let ⟨_ret497, _iw0498⟩ := _io496
              let d := _iw0498
              let _sudo_h0 := _ret497
              if (decide (_sudo_h0 ≥ need)) then
                do
                  let _t500 ← SudoRt.addI len (1 : Int)
                  let len := _t500
                  pure (SudoRt.Flow.cont (ρ := (Option (Ship)) × (Dice)) (d, len))
              else
                do
                  pure (SudoRt.Flow.brk (ρ := (Option (Ship)) × (Dice)) (d, len))) : Except SudoRt.Trap (SudoRt.Flow _ ((Option (Ship)) × (Dice)))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := (Option (Ship)) × (Dice)) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := (Option (Ship)) × (Dice)) (grow, _fs))
        | .cont _fs => do
            if grow == _toV then
              pure (SudoRt.Flow.brk (ρ := (Option (Ship)) × (Dice)) (grow, _fs))
            else do
              let i' ← SudoRt.addI grow (1 : Int)
              pure (SudoRt.Flow.cont (ρ := (Option (Ship)) × (Dice)) (i', _fs))

open Bs in
/-- What `grow_until_it_bumps` does after its growing loop (the piece), copied verbatim. -/
def growAfterE (row col : Int) (lay_down bow_last : Bool) :
    Int × (Dice × Int) → Except SudoRt.Trap ((Option Ship) × Dice) :=
  fun σ =>
    let d := σ.2.1
    let _sp509 := σ.2.2
    let len := _sp509
    do
      let kind := Kind.Sudo_4Kind_9Destroyer
      if (SudoRt.SEq.beq len (3 : Int)) then
        do
          let kind := Kind.Sudo_4Kind_7Cruiser
          let _io502 ← roll_d6 d
          let ⟨_ret503, _iw0504⟩ := _io502
          let d := _iw0504
          let _sudo_h1 := _ret503
          if (decide (_sudo_h1 ≤ (3 : Int))) then
            do
              let kind := Kind.Sudo_4Kind_3Sub
              pure ((some ({ sudo_4Ship_4kind := kind, sudo_4Ship_4down := lay_down, sudo_4Ship_3row := row, sudo_4Ship_3col := col, sudo_4Ship_8bow_last := bow_last } : Ship)), d)
          else
            do
              pure ((some ({ sudo_4Ship_4kind := kind, sudo_4Ship_4down := lay_down, sudo_4Ship_3row := row, sudo_4Ship_3col := col, sudo_4Ship_8bow_last := bow_last } : Ship)), d)
      else
        do
          if (SudoRt.SEq.beq len (4 : Int)) then
            do
              let kind := Kind.Sudo_4Kind_10Battleship
              pure ((some ({ sudo_4Ship_4kind := kind, sudo_4Ship_4down := lay_down, sudo_4Ship_3row := row, sudo_4Ship_3col := col, sudo_4Ship_8bow_last := bow_last } : Ship)), d)
          else
            do
              if (SudoRt.SEq.beq len (5 : Int)) then
                do
                  let kind := Kind.Sudo_4Kind_7Carrier
                  pure ((some ({ sudo_4Ship_4kind := kind, sudo_4Ship_4down := lay_down, sudo_4Ship_3row := row, sudo_4Ship_3col := col, sudo_4Ship_8bow_last := bow_last } : Ship)), d)
              else
                do
                  pure ((some ({ sudo_4Ship_4kind := kind, sudo_4Ship_4down := lay_down, sudo_4Ship_3row := row, sudo_4Ship_3col := col, sudo_4Ship_8bow_last := bow_last } : Ship)), d)

theorem rollD6_d6 {d d' : Spec.Dice} {f : Nat} (h : Spec.rollD6 d = some (f, d')) :
    d'.d6 = d.d6 := by
  unfold Spec.rollD6 at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h

/-- One growth step of the model, as `brkFold` takes it. -/
def growM (cov : Nat → Bool) (row col : Nat) (down : Bool) (_ : Nat) (s : Spec.Dice × Nat) :
    Option ((Spec.Dice × Nat) ⊕ (Spec.Dice × Nat)) :=
  if Spec.hasRoom cov (if down then row + s.2 else row) (if down then col else col + s.2) then
    match Spec.rollD6 s.1 with
    | none => none
    | some (f, d') => if (if s.2 = 2 then 4 else 6) ≤ f then some (.inl (d', s.2 + 1)) else some (.inr (d', s.2))
  else some (.inr s)

theorem brkFold_growM (cov : Nat → Bool) (row col : Nat) (down : Bool) :
    ∀ k i (d : Spec.Dice) (len : Nat),
      brkFold (growM cov row col down) i k (d, len) = Spec.growLoop cov row col down k d len
  | 0, _, _, _ => rfl
  | k + 1, i, d, len => by
    simp only [brkFold, growM, Spec.growLoop]
    by_cases hb : Spec.hasRoom cov (if down then row + len else row)
        (if down then col else col + len) = true
    · rw [if_pos hb, if_pos hb]
      cases Spec.rollD6 d with
      | none => rfl
      | some p =>
        obtain ⟨f, d'⟩ := p
        dsimp only
        by_cases hf : (if len = 2 then 4 else 6) ≤ f
        · rw [if_pos hf, if_pos hf]
          exact brkFold_growM cov row col down k (i + 1) d' (len + 1)
        · rw [if_neg hf, if_neg hf]; rfl
    · rw [if_neg hb, if_neg hb]; rfl

/-- The growing loop and the piece, for either heading `ld` and bow `bl`. -/
theorem grow_loop_spec (cov : Nat → Bool) (row col : Nat) (ld bl : Bool) (d : Spec.Dice)
    (hr : row < 10) (hc : col < 10) (h6 : FitsLen d.d6.length) :
    (SudoRt.runLoopOn ((1 : Int), (embDice d, (2 : Int))) (fuelRange 1 3)
      (growStepE (tab cov) (Int.ofNat row) (Int.ofNat col) ld 3)
      (growAfterE (Int.ofNat row) (Int.ofNat col) ld bl) (fun r => pure r)).toOption =
    ((Spec.growLoop cov row col ld 3 d 2).bind (fun p => Spec.pieceOf p.2 p.1)).map
      (fun p => (some (embShip ⟨p.1, ld, row, col, bl⟩), embDice p.2)) := by
  refine (loop_brk_inv (S := Spec.Dice × Nat) (fun s => (embDice s.1, Int.ofNat s.2)) _ _ _
    (growM cov row col ld) (fun i s => s.1.d6 = d.d6 ∧ 2 ≤ s.2 ∧ s.2 ≤ i + 1)
    (fun s => (Spec.pieceOf s.2 s.1).map
      (fun p => (some (embShip ⟨p.1, ld, row, col, bl⟩), embDice p.2)))
    1 4 (by decide) ?_ ?_ ?_ (d, 2) ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩).trans ?_
  · intro i s hi1 hi2 hP
    obtain ⟨dd, len⟩ := s
    obtain ⟨hd6, hl1, hl2⟩ := hP
    dsimp only at hd6 hl1 hl2
    unfold growStepE growM
    dsimp only
    rw [if_neg (by simp only [ofNat_eq_natCast]; omega), toOpt_bind,
      addI_ofNat _ _ (fits_small (show col + len ≤ 1000 by omega)), ok_bind]
    have hbeq2 : SudoRt.SEq.beq (Int.ofNat len) (2 : Int) = decide (len = 2) := by
      show decide _ = _; by_cases h : len = 2 <;> simp [h]; omega
    have hb3 : (Int.ofNat i == (3 : Int)) = decide (i + 1 = 4) := by
      by_cases h : i + 1 = 4
      · rw [decide_eq_true h]; apply beq_iff_eq.mpr; show Int.ofNat i = Int.ofNat 3; congr 1; omega
      · rw [decide_eq_false h]; apply beq_false_of_ne; intro e
        have := Int.ofNat.inj (e.trans (show (3 : Int) = Int.ofNat 3 from rfl)); omega
    cases ld
    · simp only [Bool.false_eq_true, if_false]
      rw [toOpt_bind, has_room_spec]
      cases hb : Spec.hasRoom cov row (col + len)
      · rfl
      · simp only [toOpt_ok, Option.some_bind, Bool.not_true, Bool.false_eq_true, if_false,
          if_true, hbeq2]
        by_cases h2 : len = 2
        · rw [decide_eq_true h2, if_pos rfl, if_pos h2]
          rw [toOpt_bind, roll_d6_spec dd (hd6 ▸ h6)]
          cases hroll : Spec.rollD6 dd with
          | none => rfl
          | some p =>
            obtain ⟨f, d'⟩ := p
            simp only [Option.map_some', Option.some_bind]
            by_cases hf : 4 ≤ f
            · have : decide (Int.ofNat f ≥ 4) = true := by
                apply decide_eq_true; show ((4 : Nat) : Int) ≤ (f : Int); omega
              rw [this, if_pos rfl, if_pos hf, toOpt_bind,
                addI_ofNat_one _ (fits_small (show len + 1 ≤ 1000 by omega)), toOpt_ok, Option.some_bind]
              rw [pure_eq_ok, toOpt_ok, Option.some_bind]
              dsimp only
              rw [hb3]
              by_cases h4 : i + 1 = 4
              · simp only [h4, decide_True, if_true, Option.map_some']; rfl
              · simp only [h4, decide_False, Bool.false_eq_true, if_false, Option.map_some',
                  addI_ofNat_one _ (fits_small (show i + 1 ≤ 1000 by omega))]; rfl
            · have : decide (Int.ofNat f ≥ 4) = false := by
                apply decide_eq_false; show ¬ ((4 : Nat) : Int) ≤ (f : Int); omega
              rw [this, if_neg (by decide), if_neg hf]
              rfl
        · rw [decide_eq_false h2, if_neg (by decide), if_neg h2]
          rw [toOpt_bind, roll_d6_spec dd (hd6 ▸ h6)]
          cases hroll : Spec.rollD6 dd with
          | none => rfl
          | some p =>
            obtain ⟨f, d'⟩ := p
            simp only [Option.map_some', Option.some_bind]
            by_cases hf : 6 ≤ f
            · have : decide (Int.ofNat f ≥ 6) = true := by
                apply decide_eq_true; show ((6 : Nat) : Int) ≤ (f : Int); omega
              rw [this, if_pos rfl, if_pos hf, toOpt_bind,
                addI_ofNat_one _ (fits_small (show len + 1 ≤ 1000 by omega)), toOpt_ok, Option.some_bind]
              rw [pure_eq_ok, toOpt_ok, Option.some_bind]
              dsimp only
              rw [hb3]
              by_cases h4 : i + 1 = 4
              · simp only [h4, decide_True, if_true, Option.map_some']; rfl
              · simp only [h4, decide_False, Bool.false_eq_true, if_false, Option.map_some',
                  addI_ofNat_one _ (fits_small (show i + 1 ≤ 1000 by omega))]; rfl
            · have : decide (Int.ofNat f ≥ 6) = false := by
                apply decide_eq_false; show ¬ ((6 : Nat) : Int) ≤ (f : Int); omega
              rw [this, if_neg (by decide), if_neg hf]
              rfl
    · simp only [if_true]
      rw [toOpt_bind, addI_ofNat _ _ (fits_small (show row + len ≤ 1000 by omega)), toOpt_ok,
        Option.some_bind, toOpt_bind, has_room_spec]
      cases hb : Spec.hasRoom cov (row + len) col
      · rfl
      · simp only [toOpt_ok, Option.some_bind, Bool.not_true, Bool.false_eq_true, if_false,
          if_true, hbeq2]
        by_cases h2 : len = 2
        · rw [decide_eq_true h2, if_pos rfl, if_pos h2]
          rw [toOpt_bind, roll_d6_spec dd (hd6 ▸ h6)]
          cases hroll : Spec.rollD6 dd with
          | none => rfl
          | some p =>
            obtain ⟨f, d'⟩ := p
            simp only [Option.map_some', Option.some_bind]
            by_cases hf : 4 ≤ f
            · have : decide (Int.ofNat f ≥ 4) = true := by
                apply decide_eq_true; show ((4 : Nat) : Int) ≤ (f : Int); omega
              rw [this, if_pos rfl, if_pos hf, toOpt_bind,
                addI_ofNat_one _ (fits_small (show len + 1 ≤ 1000 by omega)), toOpt_ok, Option.some_bind]
              rw [pure_eq_ok, toOpt_ok, Option.some_bind]
              dsimp only
              rw [hb3]
              by_cases h4 : i + 1 = 4
              · simp only [h4, decide_True, if_true, Option.map_some']; rfl
              · simp only [h4, decide_False, Bool.false_eq_true, if_false, Option.map_some',
                  addI_ofNat_one _ (fits_small (show i + 1 ≤ 1000 by omega))]; rfl
            · have : decide (Int.ofNat f ≥ 4) = false := by
                apply decide_eq_false; show ¬ ((4 : Nat) : Int) ≤ (f : Int); omega
              rw [this, if_neg (by decide), if_neg hf]
              rfl
        · rw [decide_eq_false h2, if_neg (by decide), if_neg h2]
          rw [toOpt_bind, roll_d6_spec dd (hd6 ▸ h6)]
          cases hroll : Spec.rollD6 dd with
          | none => rfl
          | some p =>
            obtain ⟨f, d'⟩ := p
            simp only [Option.map_some', Option.some_bind]
            by_cases hf : 6 ≤ f
            · have : decide (Int.ofNat f ≥ 6) = true := by
                apply decide_eq_true; show ((6 : Nat) : Int) ≤ (f : Int); omega
              rw [this, if_pos rfl, if_pos hf, toOpt_bind,
                addI_ofNat_one _ (fits_small (show len + 1 ≤ 1000 by omega)), toOpt_ok, Option.some_bind]
              rw [pure_eq_ok, toOpt_ok, Option.some_bind]
              dsimp only
              rw [hb3]
              by_cases h4 : i + 1 = 4
              · simp only [h4, decide_True, if_true, Option.map_some']; rfl
              · simp only [h4, decide_False, Bool.false_eq_true, if_false, Option.map_some',
                  addI_ofNat_one _ (fits_small (show i + 1 ≤ 1000 by omega))]; rfl
            · have : decide (Int.ofNat f ≥ 6) = false := by
                apply decide_eq_false; show ¬ ((6 : Nat) : Int) ≤ (f : Int); omega
              rw [this, if_neg (by decide), if_neg hf]
              rfl
  · intro i s r _ _ hP hm
    obtain ⟨dd, len⟩ := s
    obtain ⟨hd6, hl1, hl2⟩ := hP
    unfold growM at hm
    dsimp only at hm hd6 hl1 hl2
    by_cases hb : Spec.hasRoom cov (if ld then row + len else row)
        (if ld then col else col + len) = true
    · rw [if_pos hb] at hm
      cases hroll : Spec.rollD6 dd with
      | none => rw [hroll] at hm; cases hm
      | some p =>
        obtain ⟨f, d'⟩ := p
        rw [hroll] at hm
        have hd' := rollD6_d6 hroll
        dsimp only at hm
        by_cases hf : (if len = 2 then 4 else 6) ≤ f
        · rw [if_pos hf] at hm
          rw [← Option.some.inj hm]
          exact ⟨hd'.trans hd6, by simp; omega, by simp; omega⟩
        · rw [if_neg hf] at hm
          rw [← Option.some.inj hm]
          exact ⟨hd'.trans hd6, by simp; omega, by simp; omega⟩
    · rw [if_neg hb] at hm
      rw [← Option.some.inj hm]
      exact ⟨hd6, by simp; omega, by simp; omega⟩
  · intro i j s hi hP
    obtain ⟨dd, len⟩ := s
    obtain ⟨hd6, hl1, hl2⟩ := hP
    dsimp only at hd6 hl1 hl2 ⊢
    unfold growAfterE Spec.pieceOf
    dsimp only
    have hbeq : ∀ a b : Nat, SudoRt.SEq.beq (Int.ofNat a) (Int.ofNat b) = decide (a = b) := by
      intro a b; show decide _ = _; by_cases h : a = b <;> simp [h]; omega
    by_cases h3 : len = 3
    · subst h3
      rw [show (3 : Int) = Int.ofNat 3 from rfl, hbeq, if_pos (by decide)]
      rw [toOpt_bind, roll_d6_spec dd (hd6 ▸ h6)]
      cases hroll : Spec.rollD6 dd with
      | none => rfl
      | some p =>
        obtain ⟨f, d'⟩ := p
        simp only [Option.map_some', Option.some_bind]
        by_cases hf : f ≤ 3
        · have : decide (Int.ofNat f ≤ Int.ofNat 3) = true := by
            apply decide_eq_true; simp only [ofNat_eq_natCast]; omega
          rw [this, if_pos rfl, if_pos hf]; rfl
        · have : decide (Int.ofNat f ≤ Int.ofNat 3) = false := by
            apply decide_eq_false; simp only [ofNat_eq_natCast]; omega
          rw [this, if_neg (by decide), if_neg hf]; rfl
    · rw [show (3 : Int) = Int.ofNat 3 from rfl, hbeq, if_neg (by simpa using h3), if_neg h3]
      by_cases h4 : len = 4
      · subst h4
        rw [show (4 : Int) = Int.ofNat 4 from rfl, hbeq, if_pos (by decide)]; rfl
      · rw [show (4 : Int) = Int.ofNat 4 from rfl, hbeq, if_neg (by simpa using h4), if_neg h4]
        by_cases h5 : len = 5
        · subst h5
          rw [show (5 : Int) = Int.ofNat 5 from rfl, hbeq, if_pos (by decide)]; rfl
        · rw [show (5 : Int) = Int.ofNat 5 from rfl, hbeq, if_neg (by simpa using h5), if_neg h5]
          rfl
  · rw [show 4 - 1 = 3 from rfl, brkFold_growM]
    cases Spec.growLoop cov row col ld 3 d 2 <;> rfl

theorem rollHole_d6 {d d' : Spec.Dice} {f : Nat} (h : Spec.rollHole d = some (f, d')) :
    d'.d6 = d.d6 := by
  unfold Spec.rollHole at h
  split at h
  · cases h
  · split at h
    · cases h; rfl
    · cases h

/-- §4.2 step 1: the emitted `grow_until_it_bumps` is `Spec.growUntilItBumps`, traps
    included, at any hole of the grid and any covered table. -/
theorem grow_until_it_bumps_spec (d : Spec.Dice) (cov : Nat → Bool) (row col : Nat)
    (hr : row < 10) (hc : col < 10) (h12 : FitsLen d.d12.length) (h6 : FitsLen d.d6.length) :
    (Bs.grow_until_it_bumps (embDice d) (tab cov) (Int.ofNat row) (Int.ofNat col)).toOption =
      (Spec.growUntilItBumps d cov row col).map (fun p => (p.1.map embShip, embDice p.2)) := by
  unfold Bs.grow_until_it_bumps Spec.growUntilItBumps
  rw [addI_ofNat_one _ (fits_small (show col + 1 ≤ 1000 by omega)), ok_bind, has_room_spec,
    ok_bind, addI_ofNat_one _ (fits_small (show row + 1 ≤ 1000 by omega)), ok_bind,
    has_room_spec, ok_bind]
  cases ha : Spec.hasRoom cov row (col + 1) <;> cases hb : Spec.hasRoom cov (row + 1) col
  · rfl
  · simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_and, Bool.and_true,
      Bool.and_false, Bool.false_and, if_false, if_true, pure_eq_ok, ok_bind]
    rw [toOpt_bind, roll_hole_die_spec d h12]
    cases hroll : Spec.rollHole d with
    | none => rfl
    | some p =>
      obtain ⟨f, d'⟩ := p
      have h6' : FitsLen d'.d6.length := by rw [rollHole_d6 hroll]; exact h6
      simp only [Option.map_some', Option.some_bind]
      have hbl : SudoRt.SEq.beq (Int.ofNat (f % 2)) (0 : Int) = decide (f % 2 = 0) := by
        show decide _ = _; by_cases h : f % 2 = 0 <;> simp [h]; omega
      have hld : decide (Int.ofNat f ≥ 9) = decide (9 ≤ f) := by
        by_cases h : 9 ≤ f
        · rw [decide_eq_true h]; apply decide_eq_true; show ((9 : Nat) : Int) ≤ (f : Int); omega
        · rw [decide_eq_false h]; apply decide_eq_false; show ¬ ((9 : Nat) : Int) ≤ (f : Int); omega
      by_cases hf : f ≤ 6
      · rw [decide_eq_true (show Int.ofNat f ≤ 6 by show (f : Int) ≤ ((6 : Nat) : Int); omega),
          if_pos rfl, if_pos hf]; rfl
      · rw [decide_eq_false (show ¬ Int.ofNat f ≤ 6 by show ¬ (f : Int) ≤ ((6 : Nat) : Int); omega),
          if_neg (by decide), if_neg hf, show (2 : Int) = Int.ofNat 2 from rfl,
          modI_ofNat _ (by decide), ok_bind, bind_ok_right]
        refine (grow_loop_spec cov row col true (SudoRt.SEq.beq (Int.ofNat (f % 2)) (0 : Int)) d' hr hc h6').trans ?_
        rw [hbl]
        unfold Spec.layShip
        cases Spec.growLoop cov row col _ 3 d' 2 with
    | none => rfl
    | some q =>
      obtain ⟨dd, len⟩ := q
      simp only [Option.some_bind]
      cases Spec.pieceOf len dd <;> rfl
  · simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_and, Bool.and_true,
      Bool.and_false, Bool.false_and, if_false, if_true, pure_eq_ok, ok_bind]
    rw [toOpt_bind, roll_hole_die_spec d h12]
    cases hroll : Spec.rollHole d with
    | none => rfl
    | some p =>
      obtain ⟨f, d'⟩ := p
      have h6' : FitsLen d'.d6.length := by rw [rollHole_d6 hroll]; exact h6
      simp only [Option.map_some', Option.some_bind]
      have hbl : SudoRt.SEq.beq (Int.ofNat (f % 2)) (0 : Int) = decide (f % 2 = 0) := by
        show decide _ = _; by_cases h : f % 2 = 0 <;> simp [h]; omega
      have hld : decide (Int.ofNat f ≥ 9) = decide (9 ≤ f) := by
        by_cases h : 9 ≤ f
        · rw [decide_eq_true h]; apply decide_eq_true; show ((9 : Nat) : Int) ≤ (f : Int); omega
        · rw [decide_eq_false h]; apply decide_eq_false; show ¬ ((9 : Nat) : Int) ≤ (f : Int); omega
      by_cases hf : f ≤ 6
      · rw [decide_eq_true (show Int.ofNat f ≤ 6 by show (f : Int) ≤ ((6 : Nat) : Int); omega),
          if_pos rfl, if_pos hf]; rfl
      · rw [decide_eq_false (show ¬ Int.ofNat f ≤ 6 by show ¬ (f : Int) ≤ ((6 : Nat) : Int); omega),
          if_neg (by decide), if_neg hf, show (2 : Int) = Int.ofNat 2 from rfl,
          modI_ofNat _ (by decide), ok_bind, bind_ok_right]
        refine (grow_loop_spec cov row col false (SudoRt.SEq.beq (Int.ofNat (f % 2)) (0 : Int)) d' hr hc h6').trans ?_
        rw [hbl]
        unfold Spec.layShip
        cases Spec.growLoop cov row col _ 3 d' 2 with
    | none => rfl
    | some q =>
      obtain ⟨dd, len⟩ := q
      simp only [Option.some_bind]
      cases Spec.pieceOf len dd <;> rfl
  · simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_and, Bool.and_true,
      Bool.and_false, Bool.false_and, if_false, if_true, pure_eq_ok, ok_bind]
    rw [toOpt_bind, roll_hole_die_spec d h12]
    cases hroll : Spec.rollHole d with
    | none => rfl
    | some p =>
      obtain ⟨f, d'⟩ := p
      have h6' : FitsLen d'.d6.length := by rw [rollHole_d6 hroll]; exact h6
      simp only [Option.map_some', Option.some_bind]
      have hbl : SudoRt.SEq.beq (Int.ofNat (f % 2)) (0 : Int) = decide (f % 2 = 0) := by
        show decide _ = _; by_cases h : f % 2 = 0 <;> simp [h]; omega
      have hld : decide (Int.ofNat f ≥ 9) = decide (9 ≤ f) := by
        by_cases h : 9 ≤ f
        · rw [decide_eq_true h]; apply decide_eq_true; show ((9 : Nat) : Int) ≤ (f : Int); omega
        · rw [decide_eq_false h]; apply decide_eq_false; show ¬ ((9 : Nat) : Int) ≤ (f : Int); omega
      by_cases hf : f ≤ 4
      · rw [decide_eq_true (show Int.ofNat f ≤ 4 by show (f : Int) ≤ ((4 : Nat) : Int); omega),
          if_pos rfl, if_pos hf]; rfl
      · rw [decide_eq_false (show ¬ Int.ofNat f ≤ 4 by show ¬ (f : Int) ≤ ((4 : Nat) : Int); omega),
          if_neg (by decide), if_neg hf, show (2 : Int) = Int.ofNat 2 from rfl,
          modI_ofNat _ (by decide), ok_bind, bind_ok_right]
        refine (grow_loop_spec cov row col (decide (Int.ofNat f ≥ 9)) (SudoRt.SEq.beq (Int.ofNat (f % 2)) (0 : Int)) d' hr hc h6').trans ?_
        rw [hbl, hld]
        unfold Spec.layShip
        cases Spec.growLoop cov row col _ 3 d' 2 with
    | none => rfl
    | some q =>
      obtain ⟨dd, len⟩ := q
      simp only [Option.some_bind]
      cases Spec.pieceOf len dd <;> rfl

/-! ### Facts about the model's dice and tray -/

/-- The three face streams are those of `d0` (only the read counts differ). -/
def Streams (d0 d : Spec.Dice) : Prop := d.d12 = d0.d12 ∧ d.d6 = d0.d6 ∧ d.d10 = d0.d10

theorem Streams.refl (d : Spec.Dice) : Streams d d := ⟨rfl, rfl, rfl⟩

theorem Streams.trans {a b c : Spec.Dice} (h1 : Streams a b) (h2 : Streams b c) : Streams a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem d10Scan_face : ∀ (fs : List Int) (t : Nat) {f t' : Nat}, Spec.d10Scan fs t = some (f, t') →
    1 ≤ f ∧ f ≤ 9
  | [], _, _, _, h => by cases h
  | x :: fs, t, f, t', h => by
    unfold Spec.d10Scan at h
    by_cases hr : 0 ≤ x ∧ x ≤ 9
    · rw [if_pos hr] at h
      by_cases h0 : x = 0
      · rw [if_pos h0] at h; exact d10Scan_face fs (t + 1) h
      · rw [if_neg h0] at h
        cases h; omega
    · rw [if_neg hr] at h; cases h

theorem throwD10_facts {d d' : Spec.Dice} {f : Nat} (h : Spec.throwD10 d = some (f, d')) :
    1 ≤ f ∧ f ≤ 9 ∧ Streams d d' := by
  unfold Spec.throwD10 at h
  cases hs : Spec.d10Scan (d.d10.drop d.next10) d.next10 with
  | none => rw [hs] at h; cases h
  | some p =>
    rw [hs] at h; cases h
    exact ⟨(d10Scan_face _ _ hs).1, (d10Scan_face _ _ hs).2, rfl, rfl, rfl⟩

/-- A tray of row-cup faces: every die shows 1–9. -/
def TrayOk (tray : List Nat) : Prop := ∀ x ∈ tray, 1 ≤ x ∧ x ≤ 9

theorem throwRowCup_facts {d d' : Spec.Dice} {tray : List Nat}
    (h : Spec.throwRowCup d = some (tray, d')) :
    tray.length = 5 ∧ TrayOk tray ∧ Streams d d' := by
  unfold Spec.throwRowCup at h
  have key : ∀ (k : List Nat) (acc : List Nat × Spec.Dice) (r : List Nat × Spec.Dice),
      TrayOk acc.1 → k.foldlM (fun (acc : List Nat × Spec.Dice) _ =>
        (Spec.throwD10 acc.2).map (fun p => (acc.1 ++ [p.1], p.2))) acc = some r →
      r.1.length = acc.1.length + k.length ∧ TrayOk r.1 ∧ Streams acc.2 r.2 := by
    intro k
    induction k with
    | nil => intro acc r ht h; cases h; exact ⟨rfl, ht, Streams.refl _⟩
    | cons x k ih =>
      intro acc r ht h
      simp only [List.foldlM_cons] at h
      cases hd : Spec.throwD10 acc.2 with
      | none => rw [hd] at h; cases h
      | some p =>
        obtain ⟨f, d1⟩ := p
        rw [hd] at h
        obtain ⟨hf1, hf2, hs⟩ := throwD10_facts hd
        have := ih (acc.1 ++ [f], d1) r (by
          intro y hy; rcases List.mem_append.mp hy with hy | hy
          · exact ht y hy
          · simp at hy; omega) h
        refine ⟨by rw [this.1]; simp; omega, this.2.1, hs.trans this.2.2⟩
  have := key (List.range 5) ([], d) (tray, d') (by intro y hy; cases hy) h
  exact ⟨by simpa using this.1, this.2.1, this.2.2⟩

theorem rethrowUnread_facts {d d' : Spec.Dice} {tray tray' : List Nat} {read : Nat}
    (ht : TrayOk tray) (h : Spec.rethrowUnread d tray read = some (d', tray')) :
    tray'.length = tray.length ∧ TrayOk tray' ∧ Streams d d' := by
  unfold Spec.rethrowUnread at h
  have key : ∀ (k : List Nat) (acc : Spec.Dice × List Nat) (r : Spec.Dice × List Nat),
      TrayOk acc.2 → k.foldlM (fun (acc : Spec.Dice × List Nat) k =>
        (Spec.throwD10 acc.1).map (fun p => (p.2, acc.2.set k p.1))) acc = some r →
      r.2.length = acc.2.length ∧ TrayOk r.2 ∧ Streams acc.1 r.1 := by
    intro k
    induction k with
    | nil => intro acc r ht h; cases h; exact ⟨rfl, ht, Streams.refl _⟩
    | cons x k ih =>
      intro acc r ht h
      simp only [List.foldlM_cons] at h
      cases hd : Spec.throwD10 acc.1 with
      | none => rw [hd] at h; cases h
      | some p =>
        obtain ⟨f, d1⟩ := p
        rw [hd] at h
        obtain ⟨hf1, hf2, hs⟩ := throwD10_facts hd
        have := ih (d1, acc.2.set x f) r (by
          intro y hy
          rcases List.mem_or_eq_of_mem_set hy with hy | hy
          · exact ht y hy
          · omega) h
        exact ⟨by rw [this.1]; simp, this.2.1, hs.trans this.2.2⟩
  have := key _ (d, tray) (d', tray') ht h
  exact this

theorem rollHole_facts {d d' : Spec.Dice} {f : Nat} (h : Spec.rollHole d = some (f, d')) :
    Streams d d' := by
  unfold Spec.rollHole at h
  split at h
  · cases h
  · split at h
    · cases h; exact Streams.refl _
    · cases h

theorem rollD6_facts {d d' : Spec.Dice} {f : Nat} (h : Spec.rollD6 d = some (f, d')) :
    Streams d d' := by
  unfold Spec.rollD6 at h
  split at h
  · cases h
  · split at h
    · cases h; exact Streams.refl _
    · cases h

/-- The extent the heading reaches from the first hole: `len` holes fit on the grid. -/
def Fits (row col : Nat) (down : Bool) (len : Nat) : Prop :=
  if down then row + len ≤ 10 else col + len ≤ 10

theorem growLoop_facts (cov : Nat → Bool) (row col : Nat) (down : Bool) :
    ∀ (fuel : Nat) (d d' : Spec.Dice) (len len' : Nat), Fits row col down len →
      Spec.growLoop cov row col down fuel d len = some (d', len') →
      Streams d d' ∧ len ≤ len' ∧ len' ≤ len + fuel ∧ Fits row col down len'
  | 0, d, d', len, len', hf, h => by
    cases h; exact ⟨Streams.refl _, Nat.le_refl _, by omega, hf⟩
  | fuel + 1, d, d', len, len', hf, h => by
    unfold Spec.growLoop at h
    by_cases hb : Spec.hasRoom cov (if down then row + len else row)
        (if down then col else col + len) = true
    · rw [if_pos hb] at h
      cases hr : Spec.rollD6 d with
      | none => rw [hr] at h; cases h
      | some p =>
        obtain ⟨f, d1⟩ := p
        rw [hr] at h
        have hs := rollD6_facts hr
        dsimp only at h
        by_cases hg : (if len = 2 then 4 else 6) ≤ f
        · rw [if_pos hg] at h
          have hf' : Fits row col down (len + 1) := by
            unfold Spec.hasRoom at hb
            unfold Fits
            cases down <;> simp at hb ⊢ <;> omega
          have := growLoop_facts cov row col down fuel d1 d' (len + 1) len' hf' h
          exact ⟨hs.trans this.1, by omega, by omega, this.2.2.2⟩
        · rw [if_neg hg] at h
          cases h
          exact ⟨hs, Nat.le_refl _, by omega, hf⟩
    · rw [if_neg hb] at h
      cases h
      exact ⟨Streams.refl _, Nat.le_refl _, by omega, hf⟩

theorem pieceOf_facts {len : Nat} {d d' : Spec.Dice} {k : Spec.Kind} (h2 : 2 ≤ len) (h5 : len ≤ 5)
    (h : Spec.pieceOf len d = some (k, d')) : k.len = len ∧ Streams d d' := by
  unfold Spec.pieceOf at h
  by_cases e3 : len = 3
  · rw [if_pos e3] at h
    cases hr : Spec.rollD6 d with
    | none => rw [hr] at h; cases h
    | some p =>
      rw [hr] at h
      obtain ⟨f, d1⟩ := p
      simp only [Option.map_some', Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hk, hd⟩ := h
      subst hd
      refine ⟨?_, rollD6_facts hr⟩
      rw [← hk]; split <;> simp [Spec.Kind.len, e3]
  · rw [if_neg e3] at h
    by_cases e4 : len = 4
    · rw [if_pos e4] at h; cases h; exact ⟨by simp [Spec.Kind.len, e4], Streams.refl _⟩
    · rw [if_neg e4] at h
      by_cases e5 : len = 5
      · rw [if_pos e5] at h; cases h; exact ⟨by simp [Spec.Kind.len, e5], Streams.refl _⟩
      · rw [if_neg e5] at h; cases h
        exact ⟨by simp [Spec.Kind.len]; omega, Streams.refl _⟩

theorem layShip_facts (cov : Nat → Bool) (row col : Nat) (d d' : Spec.Dice) (face : Nat) (down : Bool)
    (o : Option Spec.Ship) (hr : row < 10) (hc : col < 10) (hf : Fits row col down 2)
    (h : Spec.layShip cov row col d face down = some (o, d')) :
    Streams d d' ∧ ∀ s, o = some s → s.OnGrid := by
  unfold Spec.layShip at h
  cases hg : Spec.growLoop cov row col down 3 d 2 with
  | none => rw [hg] at h; cases h
  | some p =>
    obtain ⟨d1, len⟩ := p
    rw [hg] at h
    obtain ⟨hs1, hl1, hl2, hfit⟩ := growLoop_facts cov row col down 3 d d1 2 len hf hg
    dsimp only at h
    cases hp : Spec.pieceOf len d1 with
    | none => rw [hp] at h; cases h
    | some q =>
      obtain ⟨k, d2⟩ := q
      rw [hp] at h
      obtain ⟨hk, hs2⟩ := pieceOf_facts (by omega) (by omega) hp
      simp only [Option.map_some', Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨ho, hd⟩ := h
      subst hd
      refine ⟨hs1.trans hs2, ?_⟩
      intro s hs
      rw [← ho] at hs
      cases hs
      unfold Spec.Ship.OnGrid Fits at *
      cases down <;> simp [hk] at hfit ⊢ <;> omega

theorem growUntilItBumps_facts (d d' : Spec.Dice) (cov : Nat → Bool) (row col : Nat)
    (o : Option Spec.Ship) (hr : row < 10) (hc : col < 10)
    (h : Spec.growUntilItBumps d cov row col = some (o, d')) :
    Streams d d' ∧ ∀ s, o = some s → s.OnGrid := by
  unfold Spec.growUntilItBumps at h
  dsimp only at h
  by_cases hn : (!Spec.hasRoom cov row (col + 1) && !Spec.hasRoom cov (row + 1) col) = true
  · rw [if_pos hn] at h; cases h
    exact ⟨Streams.refl _, fun s hs => by cases hs⟩
  · rw [if_neg hn] at h
    cases hrh : Spec.rollHole d with
    | none => rw [hrh] at h; cases h
    | some p =>
      obtain ⟨face, d1⟩ := p
      rw [hrh] at h
      have hs1 := rollHole_facts hrh
      dsimp only at h
      have hA : Spec.hasRoom cov row (col + 1) = true → Fits row col false 2 := by
        intro ha; unfold Spec.hasRoom at ha; unfold Fits; simp at ha ⊢; omega
      have hD : Spec.hasRoom cov (row + 1) col = true → Fits row col true 2 := by
        intro ha; unfold Spec.hasRoom at ha; unfold Fits; simp at ha ⊢; omega
      split at h
      · next hab =>
        simp only [Bool.and_eq_true] at hab
        split at h
        · cases h; exact ⟨hs1, fun s hs => by cases hs⟩
        · have hf : Fits row col (decide (9 ≤ face)) 2 := by
            cases decide (9 ≤ face)
            · exact hA hab.1
            · exact hD hab.2
          have := layShip_facts cov row col d1 d' face _ o hr hc hf h
          exact ⟨hs1.trans this.1, this.2⟩
      · next hab =>
        split at h
        · cases h; exact ⟨hs1, fun s hs => by cases hs⟩
        · have hf : Fits row col (Spec.hasRoom cov (row + 1) col) 2 := by
            cases hb : Spec.hasRoom cov (row + 1) col
            · have : Spec.hasRoom cov row (col + 1) = true := by
                cases ha : Spec.hasRoom cov row (col + 1)
                · rw [ha, hb] at hn; exact absurd rfl hn
                · rfl
              exact hA this
            · exact hD hb
          have := layShip_facts cov row col d1 d' face _ o hr hc hf h
          exact ⟨hs1.trans this.1, this.2⟩

/-! ### build: one hole -/

open Bs in
/-- The body of `build`'s hole loop (`for col = 0 to 9`), copied verbatim from the emitted
    code. A proof device: the theorems below are about the emitted `build` itself. -/
def holeStepE (letgo : Array LetGo) (row : Int) (_toV : Int) :
    Int × (Dice × Array Int × Int × Array Bool × Array Ship × Int × Array Int) →
      Except SudoRt.Trap (SudoRt.Flow
        (Int × (Dice × Array Int × Int × Array Bool × Array Ship × Int × Array Int)) (KeyGrid × Dice)) :=
  fun σ =>
    let col := σ.1
    let d := σ.2.1
    let _sp908 := σ.2.2
    let tray := _sp908.1
    let _sp909 := _sp908.2
    let read := _sp909.1
    let _sp910 := _sp909.2
    let covered := _sp910.1
    let _sp911 := _sp910.2
    let ships := _sp911.1
    let _sp912 := _sp911.2
    let face := _sp912.1
    let _sp913 := _sp912.2
    let pegs := _sp913
    do
      if col > _toV then
        pure (SudoRt.Flow.brk (ρ := (KeyGrid) × (Dice)) (col, (d, tray, read, covered, ships, face, pegs)))
      else
        match ← ((do
  let _t573 ← SudoRt.mulI row grid_cols
  let _t574 ← SudoRt.addI _t573 col
  let h := _t574
  let _t575 ← lets_go letgo h false
  if _t575 then
    do
      let _io576 ← rethrow_unread d tray read
      let ⟨_iw0577, _iw1578⟩ := _io576
      let d := _iw0577
      let tray := _iw1578
      if (SudoRt.SEq.beq col (0 : Int)) then
        do
          let _io580 ← throw_row_cup d
          let ⟨_ret581, _iw0582⟩ := _io580
          let d := _iw0582
          let tray := _ret581
          let read := (0 : Int)
          let _t583 ← SudoRt.atL covered h
          if (!( _t583 )) then
            do
              let _io584 ← grow_until_it_bumps d covered row col
              let ⟨_ret585, _iw0586⟩ := _io584
              let d := _iw0586
              let laid := _ret585
              match (laid : Option (Ship)) with
              | some s =>
                do
                  let _io587 ← cover covered s
                  let covered := _io587
                  let _mb588 := SudoRt.appendL ships s
                  let ⟨_nr589, _⟩ := _mb588
                  let ships := _nr589
                  let _hm551 := ()
                  let _u590 := _hm551
                  let _t591 ← lets_go letgo h true
                  if _t591 then
                    do
                      let _io592 ← rethrow_unread d tray read
                      let ⟨_iw0593, _iw1594⟩ := _io592
                      let d := _iw0593
                      let tray := _iw1594
                      let _t595 ← SudoRt.modI col (2 : Int)
                      if (SudoRt.SEq.beq _t595 (0 : Int)) then
                        do
                          let _t597 ← SudoRt.atL tray read
                          let face := _t597
                          let _t598 ← SudoRt.addI read (1 : Int)
                          let read := _t598
                          let _ix599 := h
                          let _t600 ← keypad_first face
                          let _t601 ← SudoRt.putL pegs _ix599 _t600
                          let pegs := _t601
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _ix602 := h
                          let _t603 ← keypad_second face
                          let _t604 ← SudoRt.putL pegs _ix602 _t603
                          let pegs := _t604
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _t605 ← SudoRt.modI col (2 : Int)
                      if (SudoRt.SEq.beq _t605 (0 : Int)) then
                        do
                          let _t607 ← SudoRt.atL tray read
                          let face := _t607
                          let _t608 ← SudoRt.addI read (1 : Int)
                          let read := _t608
                          let _ix609 := h
                          let _t610 ← keypad_first face
                          let _t611 ← SudoRt.putL pegs _ix609 _t610
                          let pegs := _t611
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _ix612 := h
                          let _t613 ← keypad_second face
                          let _t614 ← SudoRt.putL pegs _ix612 _t613
                          let pegs := _t614
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
              | _ =>
                do
                  match (laid : Option (Ship)) with
                  | none =>
                    do
                      let _t615 ← lets_go letgo h true
                      if _t615 then
                        do
                          let _io616 ← rethrow_unread d tray read
                          let ⟨_iw0617, _iw1618⟩ := _io616
                          let d := _iw0617
                          let tray := _iw1618
                          let _t619 ← SudoRt.modI col (2 : Int)
                          if (SudoRt.SEq.beq _t619 (0 : Int)) then
                            do
                              let _t621 ← SudoRt.atL tray read
                              let face := _t621
                              let _t622 ← SudoRt.addI read (1 : Int)
                              let read := _t622
                              let _ix623 := h
                              let _t624 ← keypad_first face
                              let _t625 ← SudoRt.putL pegs _ix623 _t624
                              let pegs := _t625
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                          else
                            do
                              let _ix626 := h
                              let _t627 ← keypad_second face
                              let _t628 ← SudoRt.putL pegs _ix626 _t627
                              let pegs := _t628
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _t629 ← SudoRt.modI col (2 : Int)
                          if (SudoRt.SEq.beq _t629 (0 : Int)) then
                            do
                              let _t631 ← SudoRt.atL tray read
                              let face := _t631
                              let _t632 ← SudoRt.addI read (1 : Int)
                              let read := _t632
                              let _ix633 := h
                              let _t634 ← keypad_first face
                              let _t635 ← SudoRt.putL pegs _ix633 _t634
                              let pegs := _t635
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                          else
                            do
                              let _ix636 := h
                              let _t637 ← keypad_second face
                              let _t638 ← SudoRt.putL pegs _ix636 _t637
                              let pegs := _t638
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  | _ => SudoRt.fail "AssertFailed" "non-exhaustive match"
          else
            do
              let _t639 ← lets_go letgo h true
              if _t639 then
                do
                  let _io640 ← rethrow_unread d tray read
                  let ⟨_iw0641, _iw1642⟩ := _io640
                  let d := _iw0641
                  let tray := _iw1642
                  let _t643 ← SudoRt.modI col (2 : Int)
                  if (SudoRt.SEq.beq _t643 (0 : Int)) then
                    do
                      let _t645 ← SudoRt.atL tray read
                      let face := _t645
                      let _t646 ← SudoRt.addI read (1 : Int)
                      let read := _t646
                      let _ix647 := h
                      let _t648 ← keypad_first face
                      let _t649 ← SudoRt.putL pegs _ix647 _t648
                      let pegs := _t649
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _ix650 := h
                      let _t651 ← keypad_second face
                      let _t652 ← SudoRt.putL pegs _ix650 _t651
                      let pegs := _t652
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
              else
                do
                  let _t653 ← SudoRt.modI col (2 : Int)
                  if (SudoRt.SEq.beq _t653 (0 : Int)) then
                    do
                      let _t655 ← SudoRt.atL tray read
                      let face := _t655
                      let _t656 ← SudoRt.addI read (1 : Int)
                      let read := _t656
                      let _ix657 := h
                      let _t658 ← keypad_first face
                      let _t659 ← SudoRt.putL pegs _ix657 _t658
                      let pegs := _t659
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _ix660 := h
                      let _t661 ← keypad_second face
                      let _t662 ← SudoRt.putL pegs _ix660 _t661
                      let pegs := _t662
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
      else
        do
          let _t663 ← SudoRt.atL covered h
          if (!( _t663 )) then
            do
              let _io664 ← grow_until_it_bumps d covered row col
              let ⟨_ret665, _iw0666⟩ := _io664
              let d := _iw0666
              let laid := _ret665
              match (laid : Option (Ship)) with
              | some s =>
                do
                  let _io667 ← cover covered s
                  let covered := _io667
                  let _mb668 := SudoRt.appendL ships s
                  let ⟨_nr669, _⟩ := _mb668
                  let ships := _nr669
                  let _hm551 := ()
                  let _u670 := _hm551
                  let _t671 ← lets_go letgo h true
                  if _t671 then
                    do
                      let _io672 ← rethrow_unread d tray read
                      let ⟨_iw0673, _iw1674⟩ := _io672
                      let d := _iw0673
                      let tray := _iw1674
                      let _t675 ← SudoRt.modI col (2 : Int)
                      if (SudoRt.SEq.beq _t675 (0 : Int)) then
                        do
                          let _t677 ← SudoRt.atL tray read
                          let face := _t677
                          let _t678 ← SudoRt.addI read (1 : Int)
                          let read := _t678
                          let _ix679 := h
                          let _t680 ← keypad_first face
                          let _t681 ← SudoRt.putL pegs _ix679 _t680
                          let pegs := _t681
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _ix682 := h
                          let _t683 ← keypad_second face
                          let _t684 ← SudoRt.putL pegs _ix682 _t683
                          let pegs := _t684
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _t685 ← SudoRt.modI col (2 : Int)
                      if (SudoRt.SEq.beq _t685 (0 : Int)) then
                        do
                          let _t687 ← SudoRt.atL tray read
                          let face := _t687
                          let _t688 ← SudoRt.addI read (1 : Int)
                          let read := _t688
                          let _ix689 := h
                          let _t690 ← keypad_first face
                          let _t691 ← SudoRt.putL pegs _ix689 _t690
                          let pegs := _t691
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _ix692 := h
                          let _t693 ← keypad_second face
                          let _t694 ← SudoRt.putL pegs _ix692 _t693
                          let pegs := _t694
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
              | _ =>
                do
                  match (laid : Option (Ship)) with
                  | none =>
                    do
                      let _t695 ← lets_go letgo h true
                      if _t695 then
                        do
                          let _io696 ← rethrow_unread d tray read
                          let ⟨_iw0697, _iw1698⟩ := _io696
                          let d := _iw0697
                          let tray := _iw1698
                          let _t699 ← SudoRt.modI col (2 : Int)
                          if (SudoRt.SEq.beq _t699 (0 : Int)) then
                            do
                              let _t701 ← SudoRt.atL tray read
                              let face := _t701
                              let _t702 ← SudoRt.addI read (1 : Int)
                              let read := _t702
                              let _ix703 := h
                              let _t704 ← keypad_first face
                              let _t705 ← SudoRt.putL pegs _ix703 _t704
                              let pegs := _t705
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                          else
                            do
                              let _ix706 := h
                              let _t707 ← keypad_second face
                              let _t708 ← SudoRt.putL pegs _ix706 _t707
                              let pegs := _t708
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _t709 ← SudoRt.modI col (2 : Int)
                          if (SudoRt.SEq.beq _t709 (0 : Int)) then
                            do
                              let _t711 ← SudoRt.atL tray read
                              let face := _t711
                              let _t712 ← SudoRt.addI read (1 : Int)
                              let read := _t712
                              let _ix713 := h
                              let _t714 ← keypad_first face
                              let _t715 ← SudoRt.putL pegs _ix713 _t714
                              let pegs := _t715
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                          else
                            do
                              let _ix716 := h
                              let _t717 ← keypad_second face
                              let _t718 ← SudoRt.putL pegs _ix716 _t717
                              let pegs := _t718
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  | _ => SudoRt.fail "AssertFailed" "non-exhaustive match"
          else
            do
              let _t719 ← lets_go letgo h true
              if _t719 then
                do
                  let _io720 ← rethrow_unread d tray read
                  let ⟨_iw0721, _iw1722⟩ := _io720
                  let d := _iw0721
                  let tray := _iw1722
                  let _t723 ← SudoRt.modI col (2 : Int)
                  if (SudoRt.SEq.beq _t723 (0 : Int)) then
                    do
                      let _t725 ← SudoRt.atL tray read
                      let face := _t725
                      let _t726 ← SudoRt.addI read (1 : Int)
                      let read := _t726
                      let _ix727 := h
                      let _t728 ← keypad_first face
                      let _t729 ← SudoRt.putL pegs _ix727 _t728
                      let pegs := _t729
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _ix730 := h
                      let _t731 ← keypad_second face
                      let _t732 ← SudoRt.putL pegs _ix730 _t731
                      let pegs := _t732
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
              else
                do
                  let _t733 ← SudoRt.modI col (2 : Int)
                  if (SudoRt.SEq.beq _t733 (0 : Int)) then
                    do
                      let _t735 ← SudoRt.atL tray read
                      let face := _t735
                      let _t736 ← SudoRt.addI read (1 : Int)
                      let read := _t736
                      let _ix737 := h
                      let _t738 ← keypad_first face
                      let _t739 ← SudoRt.putL pegs _ix737 _t738
                      let pegs := _t739
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _ix740 := h
                      let _t741 ← keypad_second face
                      let _t742 ← SudoRt.putL pegs _ix740 _t741
                      let pegs := _t742
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
  else
    do
      if (SudoRt.SEq.beq col (0 : Int)) then
        do
          let _io744 ← throw_row_cup d
          let ⟨_ret745, _iw0746⟩ := _io744
          let d := _iw0746
          let tray := _ret745
          let read := (0 : Int)
          let _t747 ← SudoRt.atL covered h
          if (!( _t747 )) then
            do
              let _io748 ← grow_until_it_bumps d covered row col
              let ⟨_ret749, _iw0750⟩ := _io748
              let d := _iw0750
              let laid := _ret749
              match (laid : Option (Ship)) with
              | some s =>
                do
                  let _io751 ← cover covered s
                  let covered := _io751
                  let _mb752 := SudoRt.appendL ships s
                  let ⟨_nr753, _⟩ := _mb752
                  let ships := _nr753
                  let _hm551 := ()
                  let _u754 := _hm551
                  let _t755 ← lets_go letgo h true
                  if _t755 then
                    do
                      let _io756 ← rethrow_unread d tray read
                      let ⟨_iw0757, _iw1758⟩ := _io756
                      let d := _iw0757
                      let tray := _iw1758
                      let _t759 ← SudoRt.modI col (2 : Int)
                      if (SudoRt.SEq.beq _t759 (0 : Int)) then
                        do
                          let _t761 ← SudoRt.atL tray read
                          let face := _t761
                          let _t762 ← SudoRt.addI read (1 : Int)
                          let read := _t762
                          let _ix763 := h
                          let _t764 ← keypad_first face
                          let _t765 ← SudoRt.putL pegs _ix763 _t764
                          let pegs := _t765
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _ix766 := h
                          let _t767 ← keypad_second face
                          let _t768 ← SudoRt.putL pegs _ix766 _t767
                          let pegs := _t768
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _t769 ← SudoRt.modI col (2 : Int)
                      if (SudoRt.SEq.beq _t769 (0 : Int)) then
                        do
                          let _t771 ← SudoRt.atL tray read
                          let face := _t771
                          let _t772 ← SudoRt.addI read (1 : Int)
                          let read := _t772
                          let _ix773 := h
                          let _t774 ← keypad_first face
                          let _t775 ← SudoRt.putL pegs _ix773 _t774
                          let pegs := _t775
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _ix776 := h
                          let _t777 ← keypad_second face
                          let _t778 ← SudoRt.putL pegs _ix776 _t777
                          let pegs := _t778
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
              | _ =>
                do
                  match (laid : Option (Ship)) with
                  | none =>
                    do
                      let _t779 ← lets_go letgo h true
                      if _t779 then
                        do
                          let _io780 ← rethrow_unread d tray read
                          let ⟨_iw0781, _iw1782⟩ := _io780
                          let d := _iw0781
                          let tray := _iw1782
                          let _t783 ← SudoRt.modI col (2 : Int)
                          if (SudoRt.SEq.beq _t783 (0 : Int)) then
                            do
                              let _t785 ← SudoRt.atL tray read
                              let face := _t785
                              let _t786 ← SudoRt.addI read (1 : Int)
                              let read := _t786
                              let _ix787 := h
                              let _t788 ← keypad_first face
                              let _t789 ← SudoRt.putL pegs _ix787 _t788
                              let pegs := _t789
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                          else
                            do
                              let _ix790 := h
                              let _t791 ← keypad_second face
                              let _t792 ← SudoRt.putL pegs _ix790 _t791
                              let pegs := _t792
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _t793 ← SudoRt.modI col (2 : Int)
                          if (SudoRt.SEq.beq _t793 (0 : Int)) then
                            do
                              let _t795 ← SudoRt.atL tray read
                              let face := _t795
                              let _t796 ← SudoRt.addI read (1 : Int)
                              let read := _t796
                              let _ix797 := h
                              let _t798 ← keypad_first face
                              let _t799 ← SudoRt.putL pegs _ix797 _t798
                              let pegs := _t799
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                          else
                            do
                              let _ix800 := h
                              let _t801 ← keypad_second face
                              let _t802 ← SudoRt.putL pegs _ix800 _t801
                              let pegs := _t802
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  | _ => SudoRt.fail "AssertFailed" "non-exhaustive match"
          else
            do
              let _t803 ← lets_go letgo h true
              if _t803 then
                do
                  let _io804 ← rethrow_unread d tray read
                  let ⟨_iw0805, _iw1806⟩ := _io804
                  let d := _iw0805
                  let tray := _iw1806
                  let _t807 ← SudoRt.modI col (2 : Int)
                  if (SudoRt.SEq.beq _t807 (0 : Int)) then
                    do
                      let _t809 ← SudoRt.atL tray read
                      let face := _t809
                      let _t810 ← SudoRt.addI read (1 : Int)
                      let read := _t810
                      let _ix811 := h
                      let _t812 ← keypad_first face
                      let _t813 ← SudoRt.putL pegs _ix811 _t812
                      let pegs := _t813
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _ix814 := h
                      let _t815 ← keypad_second face
                      let _t816 ← SudoRt.putL pegs _ix814 _t815
                      let pegs := _t816
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
              else
                do
                  let _t817 ← SudoRt.modI col (2 : Int)
                  if (SudoRt.SEq.beq _t817 (0 : Int)) then
                    do
                      let _t819 ← SudoRt.atL tray read
                      let face := _t819
                      let _t820 ← SudoRt.addI read (1 : Int)
                      let read := _t820
                      let _ix821 := h
                      let _t822 ← keypad_first face
                      let _t823 ← SudoRt.putL pegs _ix821 _t822
                      let pegs := _t823
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _ix824 := h
                      let _t825 ← keypad_second face
                      let _t826 ← SudoRt.putL pegs _ix824 _t825
                      let pegs := _t826
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
      else
        do
          let _t827 ← SudoRt.atL covered h
          if (!( _t827 )) then
            do
              let _io828 ← grow_until_it_bumps d covered row col
              let ⟨_ret829, _iw0830⟩ := _io828
              let d := _iw0830
              let laid := _ret829
              match (laid : Option (Ship)) with
              | some s =>
                do
                  let _io831 ← cover covered s
                  let covered := _io831
                  let _mb832 := SudoRt.appendL ships s
                  let ⟨_nr833, _⟩ := _mb832
                  let ships := _nr833
                  let _hm551 := ()
                  let _u834 := _hm551
                  let _t835 ← lets_go letgo h true
                  if _t835 then
                    do
                      let _io836 ← rethrow_unread d tray read
                      let ⟨_iw0837, _iw1838⟩ := _io836
                      let d := _iw0837
                      let tray := _iw1838
                      let _t839 ← SudoRt.modI col (2 : Int)
                      if (SudoRt.SEq.beq _t839 (0 : Int)) then
                        do
                          let _t841 ← SudoRt.atL tray read
                          let face := _t841
                          let _t842 ← SudoRt.addI read (1 : Int)
                          let read := _t842
                          let _ix843 := h
                          let _t844 ← keypad_first face
                          let _t845 ← SudoRt.putL pegs _ix843 _t844
                          let pegs := _t845
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _ix846 := h
                          let _t847 ← keypad_second face
                          let _t848 ← SudoRt.putL pegs _ix846 _t847
                          let pegs := _t848
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _t849 ← SudoRt.modI col (2 : Int)
                      if (SudoRt.SEq.beq _t849 (0 : Int)) then
                        do
                          let _t851 ← SudoRt.atL tray read
                          let face := _t851
                          let _t852 ← SudoRt.addI read (1 : Int)
                          let read := _t852
                          let _ix853 := h
                          let _t854 ← keypad_first face
                          let _t855 ← SudoRt.putL pegs _ix853 _t854
                          let pegs := _t855
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _ix856 := h
                          let _t857 ← keypad_second face
                          let _t858 ← SudoRt.putL pegs _ix856 _t857
                          let pegs := _t858
                          pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
              | _ =>
                do
                  match (laid : Option (Ship)) with
                  | none =>
                    do
                      let _t859 ← lets_go letgo h true
                      if _t859 then
                        do
                          let _io860 ← rethrow_unread d tray read
                          let ⟨_iw0861, _iw1862⟩ := _io860
                          let d := _iw0861
                          let tray := _iw1862
                          let _t863 ← SudoRt.modI col (2 : Int)
                          if (SudoRt.SEq.beq _t863 (0 : Int)) then
                            do
                              let _t865 ← SudoRt.atL tray read
                              let face := _t865
                              let _t866 ← SudoRt.addI read (1 : Int)
                              let read := _t866
                              let _ix867 := h
                              let _t868 ← keypad_first face
                              let _t869 ← SudoRt.putL pegs _ix867 _t868
                              let pegs := _t869
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                          else
                            do
                              let _ix870 := h
                              let _t871 ← keypad_second face
                              let _t872 ← SudoRt.putL pegs _ix870 _t871
                              let pegs := _t872
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                      else
                        do
                          let _t873 ← SudoRt.modI col (2 : Int)
                          if (SudoRt.SEq.beq _t873 (0 : Int)) then
                            do
                              let _t875 ← SudoRt.atL tray read
                              let face := _t875
                              let _t876 ← SudoRt.addI read (1 : Int)
                              let read := _t876
                              let _ix877 := h
                              let _t878 ← keypad_first face
                              let _t879 ← SudoRt.putL pegs _ix877 _t878
                              let pegs := _t879
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                          else
                            do
                              let _ix880 := h
                              let _t881 ← keypad_second face
                              let _t882 ← SudoRt.putL pegs _ix880 _t881
                              let pegs := _t882
                              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  | _ => SudoRt.fail "AssertFailed" "non-exhaustive match"
          else
            do
              let _t883 ← lets_go letgo h true
              if _t883 then
                do
                  let _io884 ← rethrow_unread d tray read
                  let ⟨_iw0885, _iw1886⟩ := _io884
                  let d := _iw0885
                  let tray := _iw1886
                  let _t887 ← SudoRt.modI col (2 : Int)
                  if (SudoRt.SEq.beq _t887 (0 : Int)) then
                    do
                      let _t889 ← SudoRt.atL tray read
                      let face := _t889
                      let _t890 ← SudoRt.addI read (1 : Int)
                      let read := _t890
                      let _ix891 := h
                      let _t892 ← keypad_first face
                      let _t893 ← SudoRt.putL pegs _ix891 _t892
                      let pegs := _t893
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _ix894 := h
                      let _t895 ← keypad_second face
                      let _t896 ← SudoRt.putL pegs _ix894 _t895
                      let pegs := _t896
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
              else
                do
                  let _t897 ← SudoRt.modI col (2 : Int)
                  if (SudoRt.SEq.beq _t897 (0 : Int)) then
                    do
                      let _t899 ← SudoRt.atL tray read
                      let face := _t899
                      let _t900 ← SudoRt.addI read (1 : Int)
                      let read := _t900
                      let _ix901 := h
                      let _t902 ← keypad_first face
                      let _t903 ← SudoRt.putL pegs _ix901 _t902
                      let pegs := _t903
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                  else
                    do
                      let _ix904 := h
                      let _t905 ← keypad_second face
                      let _t906 ← SudoRt.putL pegs _ix904 _t905
                      let pegs := _t906
                      pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))) : Except SudoRt.Trap (SudoRt.Flow _ ((KeyGrid) × (Dice)))) with
        | .ret r => pure (SudoRt.Flow.ret (ρ := (KeyGrid) × (Dice)) r)
        | .brk _fs => pure (SudoRt.Flow.brk (ρ := (KeyGrid) × (Dice)) (col, _fs))
        | .cont _fs => do
            if col == _toV then
              pure (SudoRt.Flow.brk (ρ := (KeyGrid) × (Dice)) (col, _fs))
            else do
              let i' ← SudoRt.addI col (1 : Int)
              pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (i', _fs))

open Bs in
/-- The emitted hole step from the peg (keypad row at a pair's first hole, column at its second), copied verbatim (one of its identical copies). -/
def stageEE (_letgo : Array LetGo) (_row : Int) (col h : Int) (d : Dice) (tray : Array Int) (read : Int)
    (covered : Array Bool) (ships : Array Ship) (face : Int) (pegs : Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Dice × Array Int × Int × Array Bool × Array Ship × Int × Array Int)
      (KeyGrid × Dice)) :=
  do
    let _t595 ← SudoRt.modI col (2 : Int)
    if (SudoRt.SEq.beq _t595 (0 : Int)) then
      do
        let _t597 ← SudoRt.atL tray read
        let face := _t597
        let _t598 ← SudoRt.addI read (1 : Int)
        let read := _t598
        let _ix599 := h
        let _t600 ← keypad_first face
        let _t601 ← SudoRt.putL pegs _ix599 _t600
        let pegs := _t601
        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
    else
      do
        let _ix602 := h
        let _t603 ← keypad_second face
        let _t604 ← SudoRt.putL pegs _ix602 _t603
        let pegs := _t604
        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))

open Bs in
/-- The emitted hole step from letting go in the step 1 → 2 gap, then the peg, copied verbatim (one of its identical copies). -/
def stageDE (letgo : Array LetGo) (_row : Int) (col h : Int) (d : Dice) (tray : Array Int) (read : Int)
    (covered : Array Bool) (ships : Array Ship) (face : Int) (pegs : Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Dice × Array Int × Int × Array Bool × Array Ship × Int × Array Int)
      (KeyGrid × Dice)) :=
  do
    let _t591 ← lets_go letgo h true
    if _t591 then
      do
        let _io592 ← rethrow_unread d tray read
        let ⟨_iw0593, _iw1594⟩ := _io592
        let d := _iw0593
        let tray := _iw1594
        let _t595 ← SudoRt.modI col (2 : Int)
        if (SudoRt.SEq.beq _t595 (0 : Int)) then
          do
            let _t597 ← SudoRt.atL tray read
            let face := _t597
            let _t598 ← SudoRt.addI read (1 : Int)
            let read := _t598
            let _ix599 := h
            let _t600 ← keypad_first face
            let _t601 ← SudoRt.putL pegs _ix599 _t600
            let pegs := _t601
            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
        else
          do
            let _ix602 := h
            let _t603 ← keypad_second face
            let _t604 ← SudoRt.putL pegs _ix602 _t603
            let pegs := _t604
            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
    else
      do
        let _t605 ← SudoRt.modI col (2 : Int)
        if (SudoRt.SEq.beq _t605 (0 : Int)) then
          do
            let _t607 ← SudoRt.atL tray read
            let face := _t607
            let _t608 ← SudoRt.addI read (1 : Int)
            let read := _t608
            let _ix609 := h
            let _t610 ← keypad_first face
            let _t611 ← SudoRt.putL pegs _ix609 _t610
            let pegs := _t611
            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
        else
          do
            let _ix612 := h
            let _t613 ← keypad_second face
            let _t614 ← SudoRt.putL pegs _ix612 _t613
            let pegs := _t614
            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))

open Bs in
/-- The emitted hole step from growing until it bumps at an uncovered hole, then the gap let-go and the peg, copied verbatim (one of its identical copies). -/
def stageCE (letgo : Array LetGo) (row col h : Int) (d : Dice) (tray : Array Int) (read : Int)
    (covered : Array Bool) (ships : Array Ship) (face : Int) (pegs : Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Dice × Array Int × Int × Array Bool × Array Ship × Int × Array Int)
      (KeyGrid × Dice)) :=
  do
    let _t583 ← SudoRt.atL covered h
    if (!( _t583 )) then
      do
        let _io584 ← grow_until_it_bumps d covered row col
        let ⟨_ret585, _iw0586⟩ := _io584
        let d := _iw0586
        let laid := _ret585
        match (laid : Option (Ship)) with
        | some s =>
          do
            let _io587 ← cover covered s
            let covered := _io587
            let _mb588 := SudoRt.appendL ships s
            let ⟨_nr589, _⟩ := _mb588
            let ships := _nr589
            let _hm551 := ()
            let _u590 := _hm551
            let _t591 ← lets_go letgo h true
            if _t591 then
              do
                let _io592 ← rethrow_unread d tray read
                let ⟨_iw0593, _iw1594⟩ := _io592
                let d := _iw0593
                let tray := _iw1594
                let _t595 ← SudoRt.modI col (2 : Int)
                if (SudoRt.SEq.beq _t595 (0 : Int)) then
                  do
                    let _t597 ← SudoRt.atL tray read
                    let face := _t597
                    let _t598 ← SudoRt.addI read (1 : Int)
                    let read := _t598
                    let _ix599 := h
                    let _t600 ← keypad_first face
                    let _t601 ← SudoRt.putL pegs _ix599 _t600
                    let pegs := _t601
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                else
                  do
                    let _ix602 := h
                    let _t603 ← keypad_second face
                    let _t604 ← SudoRt.putL pegs _ix602 _t603
                    let pegs := _t604
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
            else
              do
                let _t605 ← SudoRt.modI col (2 : Int)
                if (SudoRt.SEq.beq _t605 (0 : Int)) then
                  do
                    let _t607 ← SudoRt.atL tray read
                    let face := _t607
                    let _t608 ← SudoRt.addI read (1 : Int)
                    let read := _t608
                    let _ix609 := h
                    let _t610 ← keypad_first face
                    let _t611 ← SudoRt.putL pegs _ix609 _t610
                    let pegs := _t611
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                else
                  do
                    let _ix612 := h
                    let _t613 ← keypad_second face
                    let _t614 ← SudoRt.putL pegs _ix612 _t613
                    let pegs := _t614
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
        | _ =>
          do
            match (laid : Option (Ship)) with
            | none =>
              do
                let _t615 ← lets_go letgo h true
                if _t615 then
                  do
                    let _io616 ← rethrow_unread d tray read
                    let ⟨_iw0617, _iw1618⟩ := _io616
                    let d := _iw0617
                    let tray := _iw1618
                    let _t619 ← SudoRt.modI col (2 : Int)
                    if (SudoRt.SEq.beq _t619 (0 : Int)) then
                      do
                        let _t621 ← SudoRt.atL tray read
                        let face := _t621
                        let _t622 ← SudoRt.addI read (1 : Int)
                        let read := _t622
                        let _ix623 := h
                        let _t624 ← keypad_first face
                        let _t625 ← SudoRt.putL pegs _ix623 _t624
                        let pegs := _t625
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                    else
                      do
                        let _ix626 := h
                        let _t627 ← keypad_second face
                        let _t628 ← SudoRt.putL pegs _ix626 _t627
                        let pegs := _t628
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                else
                  do
                    let _t629 ← SudoRt.modI col (2 : Int)
                    if (SudoRt.SEq.beq _t629 (0 : Int)) then
                      do
                        let _t631 ← SudoRt.atL tray read
                        let face := _t631
                        let _t632 ← SudoRt.addI read (1 : Int)
                        let read := _t632
                        let _ix633 := h
                        let _t634 ← keypad_first face
                        let _t635 ← SudoRt.putL pegs _ix633 _t634
                        let pegs := _t635
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                    else
                      do
                        let _ix636 := h
                        let _t637 ← keypad_second face
                        let _t638 ← SudoRt.putL pegs _ix636 _t637
                        let pegs := _t638
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
            | _ => SudoRt.fail "AssertFailed" "non-exhaustive match"
    else
      do
        let _t639 ← lets_go letgo h true
        if _t639 then
          do
            let _io640 ← rethrow_unread d tray read
            let ⟨_iw0641, _iw1642⟩ := _io640
            let d := _iw0641
            let tray := _iw1642
            let _t643 ← SudoRt.modI col (2 : Int)
            if (SudoRt.SEq.beq _t643 (0 : Int)) then
              do
                let _t645 ← SudoRt.atL tray read
                let face := _t645
                let _t646 ← SudoRt.addI read (1 : Int)
                let read := _t646
                let _ix647 := h
                let _t648 ← keypad_first face
                let _t649 ← SudoRt.putL pegs _ix647 _t648
                let pegs := _t649
                pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
            else
              do
                let _ix650 := h
                let _t651 ← keypad_second face
                let _t652 ← SudoRt.putL pegs _ix650 _t651
                let pegs := _t652
                pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
        else
          do
            let _t653 ← SudoRt.modI col (2 : Int)
            if (SudoRt.SEq.beq _t653 (0 : Int)) then
              do
                let _t655 ← SudoRt.atL tray read
                let face := _t655
                let _t656 ← SudoRt.addI read (1 : Int)
                let read := _t656
                let _ix657 := h
                let _t658 ← keypad_first face
                let _t659 ← SudoRt.putL pegs _ix657 _t658
                let pegs := _t659
                pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
            else
              do
                let _ix660 := h
                let _t661 ← keypad_second face
                let _t662 ← SudoRt.putL pegs _ix660 _t661
                let pegs := _t662
                pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))

open Bs in
/-- The emitted hole step from the row cup at a row's first hole, then the rest of the hole, copied verbatim (one of its identical copies). -/
def stageBE (letgo : Array LetGo) (row col h : Int) (d : Dice) (tray : Array Int) (read : Int)
    (covered : Array Bool) (ships : Array Ship) (face : Int) (pegs : Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Dice × Array Int × Int × Array Bool × Array Ship × Int × Array Int)
      (KeyGrid × Dice)) :=
  do
    if (SudoRt.SEq.beq col (0 : Int)) then
      do
        let _io580 ← throw_row_cup d
        let ⟨_ret581, _iw0582⟩ := _io580
        let d := _iw0582
        let tray := _ret581
        let read := (0 : Int)
        let _t583 ← SudoRt.atL covered h
        if (!( _t583 )) then
          do
            let _io584 ← grow_until_it_bumps d covered row col
            let ⟨_ret585, _iw0586⟩ := _io584
            let d := _iw0586
            let laid := _ret585
            match (laid : Option (Ship)) with
            | some s =>
              do
                let _io587 ← cover covered s
                let covered := _io587
                let _mb588 := SudoRt.appendL ships s
                let ⟨_nr589, _⟩ := _mb588
                let ships := _nr589
                let _hm551 := ()
                let _u590 := _hm551
                let _t591 ← lets_go letgo h true
                if _t591 then
                  do
                    let _io592 ← rethrow_unread d tray read
                    let ⟨_iw0593, _iw1594⟩ := _io592
                    let d := _iw0593
                    let tray := _iw1594
                    let _t595 ← SudoRt.modI col (2 : Int)
                    if (SudoRt.SEq.beq _t595 (0 : Int)) then
                      do
                        let _t597 ← SudoRt.atL tray read
                        let face := _t597
                        let _t598 ← SudoRt.addI read (1 : Int)
                        let read := _t598
                        let _ix599 := h
                        let _t600 ← keypad_first face
                        let _t601 ← SudoRt.putL pegs _ix599 _t600
                        let pegs := _t601
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                    else
                      do
                        let _ix602 := h
                        let _t603 ← keypad_second face
                        let _t604 ← SudoRt.putL pegs _ix602 _t603
                        let pegs := _t604
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                else
                  do
                    let _t605 ← SudoRt.modI col (2 : Int)
                    if (SudoRt.SEq.beq _t605 (0 : Int)) then
                      do
                        let _t607 ← SudoRt.atL tray read
                        let face := _t607
                        let _t608 ← SudoRt.addI read (1 : Int)
                        let read := _t608
                        let _ix609 := h
                        let _t610 ← keypad_first face
                        let _t611 ← SudoRt.putL pegs _ix609 _t610
                        let pegs := _t611
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                    else
                      do
                        let _ix612 := h
                        let _t613 ← keypad_second face
                        let _t614 ← SudoRt.putL pegs _ix612 _t613
                        let pegs := _t614
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
            | _ =>
              do
                match (laid : Option (Ship)) with
                | none =>
                  do
                    let _t615 ← lets_go letgo h true
                    if _t615 then
                      do
                        let _io616 ← rethrow_unread d tray read
                        let ⟨_iw0617, _iw1618⟩ := _io616
                        let d := _iw0617
                        let tray := _iw1618
                        let _t619 ← SudoRt.modI col (2 : Int)
                        if (SudoRt.SEq.beq _t619 (0 : Int)) then
                          do
                            let _t621 ← SudoRt.atL tray read
                            let face := _t621
                            let _t622 ← SudoRt.addI read (1 : Int)
                            let read := _t622
                            let _ix623 := h
                            let _t624 ← keypad_first face
                            let _t625 ← SudoRt.putL pegs _ix623 _t624
                            let pegs := _t625
                            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                        else
                          do
                            let _ix626 := h
                            let _t627 ← keypad_second face
                            let _t628 ← SudoRt.putL pegs _ix626 _t627
                            let pegs := _t628
                            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                    else
                      do
                        let _t629 ← SudoRt.modI col (2 : Int)
                        if (SudoRt.SEq.beq _t629 (0 : Int)) then
                          do
                            let _t631 ← SudoRt.atL tray read
                            let face := _t631
                            let _t632 ← SudoRt.addI read (1 : Int)
                            let read := _t632
                            let _ix633 := h
                            let _t634 ← keypad_first face
                            let _t635 ← SudoRt.putL pegs _ix633 _t634
                            let pegs := _t635
                            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                        else
                          do
                            let _ix636 := h
                            let _t637 ← keypad_second face
                            let _t638 ← SudoRt.putL pegs _ix636 _t637
                            let pegs := _t638
                            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                | _ => SudoRt.fail "AssertFailed" "non-exhaustive match"
        else
          do
            let _t639 ← lets_go letgo h true
            if _t639 then
              do
                let _io640 ← rethrow_unread d tray read
                let ⟨_iw0641, _iw1642⟩ := _io640
                let d := _iw0641
                let tray := _iw1642
                let _t643 ← SudoRt.modI col (2 : Int)
                if (SudoRt.SEq.beq _t643 (0 : Int)) then
                  do
                    let _t645 ← SudoRt.atL tray read
                    let face := _t645
                    let _t646 ← SudoRt.addI read (1 : Int)
                    let read := _t646
                    let _ix647 := h
                    let _t648 ← keypad_first face
                    let _t649 ← SudoRt.putL pegs _ix647 _t648
                    let pegs := _t649
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                else
                  do
                    let _ix650 := h
                    let _t651 ← keypad_second face
                    let _t652 ← SudoRt.putL pegs _ix650 _t651
                    let pegs := _t652
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
            else
              do
                let _t653 ← SudoRt.modI col (2 : Int)
                if (SudoRt.SEq.beq _t653 (0 : Int)) then
                  do
                    let _t655 ← SudoRt.atL tray read
                    let face := _t655
                    let _t656 ← SudoRt.addI read (1 : Int)
                    let read := _t656
                    let _ix657 := h
                    let _t658 ← keypad_first face
                    let _t659 ← SudoRt.putL pegs _ix657 _t658
                    let pegs := _t659
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                else
                  do
                    let _ix660 := h
                    let _t661 ← keypad_second face
                    let _t662 ← SudoRt.putL pegs _ix660 _t661
                    let pegs := _t662
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
    else
      do
        let _t663 ← SudoRt.atL covered h
        if (!( _t663 )) then
          do
            let _io664 ← grow_until_it_bumps d covered row col
            let ⟨_ret665, _iw0666⟩ := _io664
            let d := _iw0666
            let laid := _ret665
            match (laid : Option (Ship)) with
            | some s =>
              do
                let _io667 ← cover covered s
                let covered := _io667
                let _mb668 := SudoRt.appendL ships s
                let ⟨_nr669, _⟩ := _mb668
                let ships := _nr669
                let _hm551 := ()
                let _u670 := _hm551
                let _t671 ← lets_go letgo h true
                if _t671 then
                  do
                    let _io672 ← rethrow_unread d tray read
                    let ⟨_iw0673, _iw1674⟩ := _io672
                    let d := _iw0673
                    let tray := _iw1674
                    let _t675 ← SudoRt.modI col (2 : Int)
                    if (SudoRt.SEq.beq _t675 (0 : Int)) then
                      do
                        let _t677 ← SudoRt.atL tray read
                        let face := _t677
                        let _t678 ← SudoRt.addI read (1 : Int)
                        let read := _t678
                        let _ix679 := h
                        let _t680 ← keypad_first face
                        let _t681 ← SudoRt.putL pegs _ix679 _t680
                        let pegs := _t681
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                    else
                      do
                        let _ix682 := h
                        let _t683 ← keypad_second face
                        let _t684 ← SudoRt.putL pegs _ix682 _t683
                        let pegs := _t684
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                else
                  do
                    let _t685 ← SudoRt.modI col (2 : Int)
                    if (SudoRt.SEq.beq _t685 (0 : Int)) then
                      do
                        let _t687 ← SudoRt.atL tray read
                        let face := _t687
                        let _t688 ← SudoRt.addI read (1 : Int)
                        let read := _t688
                        let _ix689 := h
                        let _t690 ← keypad_first face
                        let _t691 ← SudoRt.putL pegs _ix689 _t690
                        let pegs := _t691
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                    else
                      do
                        let _ix692 := h
                        let _t693 ← keypad_second face
                        let _t694 ← SudoRt.putL pegs _ix692 _t693
                        let pegs := _t694
                        pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
            | _ =>
              do
                match (laid : Option (Ship)) with
                | none =>
                  do
                    let _t695 ← lets_go letgo h true
                    if _t695 then
                      do
                        let _io696 ← rethrow_unread d tray read
                        let ⟨_iw0697, _iw1698⟩ := _io696
                        let d := _iw0697
                        let tray := _iw1698
                        let _t699 ← SudoRt.modI col (2 : Int)
                        if (SudoRt.SEq.beq _t699 (0 : Int)) then
                          do
                            let _t701 ← SudoRt.atL tray read
                            let face := _t701
                            let _t702 ← SudoRt.addI read (1 : Int)
                            let read := _t702
                            let _ix703 := h
                            let _t704 ← keypad_first face
                            let _t705 ← SudoRt.putL pegs _ix703 _t704
                            let pegs := _t705
                            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                        else
                          do
                            let _ix706 := h
                            let _t707 ← keypad_second face
                            let _t708 ← SudoRt.putL pegs _ix706 _t707
                            let pegs := _t708
                            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                    else
                      do
                        let _t709 ← SudoRt.modI col (2 : Int)
                        if (SudoRt.SEq.beq _t709 (0 : Int)) then
                          do
                            let _t711 ← SudoRt.atL tray read
                            let face := _t711
                            let _t712 ← SudoRt.addI read (1 : Int)
                            let read := _t712
                            let _ix713 := h
                            let _t714 ← keypad_first face
                            let _t715 ← SudoRt.putL pegs _ix713 _t714
                            let pegs := _t715
                            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                        else
                          do
                            let _ix716 := h
                            let _t717 ← keypad_second face
                            let _t718 ← SudoRt.putL pegs _ix716 _t717
                            let pegs := _t718
                            pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                | _ => SudoRt.fail "AssertFailed" "non-exhaustive match"
        else
          do
            let _t719 ← lets_go letgo h true
            if _t719 then
              do
                let _io720 ← rethrow_unread d tray read
                let ⟨_iw0721, _iw1722⟩ := _io720
                let d := _iw0721
                let tray := _iw1722
                let _t723 ← SudoRt.modI col (2 : Int)
                if (SudoRt.SEq.beq _t723 (0 : Int)) then
                  do
                    let _t725 ← SudoRt.atL tray read
                    let face := _t725
                    let _t726 ← SudoRt.addI read (1 : Int)
                    let read := _t726
                    let _ix727 := h
                    let _t728 ← keypad_first face
                    let _t729 ← SudoRt.putL pegs _ix727 _t728
                    let pegs := _t729
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                else
                  do
                    let _ix730 := h
                    let _t731 ← keypad_second face
                    let _t732 ← SudoRt.putL pegs _ix730 _t731
                    let pegs := _t732
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
            else
              do
                let _t733 ← SudoRt.modI col (2 : Int)
                if (SudoRt.SEq.beq _t733 (0 : Int)) then
                  do
                    let _t735 ← SudoRt.atL tray read
                    let face := _t735
                    let _t736 ← SudoRt.addI read (1 : Int)
                    let read := _t736
                    let _ix737 := h
                    let _t738 ← keypad_first face
                    let _t739 ← SudoRt.putL pegs _ix737 _t738
                    let pegs := _t739
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))
                else
                  do
                    let _ix740 := h
                    let _t741 ← keypad_second face
                    let _t742 ← SudoRt.putL pegs _ix740 _t741
                    let pegs := _t742
                    pure (SudoRt.Flow.cont (ρ := (KeyGrid) × (Dice)) (d, tray, read, covered, ships, face, pegs))

/-- A model build state as the emitted loop state. -/
def embSt (st : Spec.BuildSt) :
    Bs.Dice × Array Int × Int × Array Bool × Array Bs.Ship × Int × Array Int :=
  (embDice st.dice, embed st.tray, Int.ofNat st.read, tab st.covered,
    (st.ships.map embShip).toArray, Int.ofNat st.face, tab (fun h => Int.ofNat (st.pegs h)))

/-- What the hole step needs of the state before hole (`row`, `col`). -/
structure HoleInv (d0 : Spec.Dice) (col : Nat) (st : Spec.BuildSt) : Prop where
  streams : Streams d0 st.dice
  tray : TrayOk st.tray
  trayLen : st.tray.length ≤ 5
  read : st.read ≤ st.tray.length
  face : col % 2 = 1 → 1 ≤ st.face ∧ st.face ≤ 9

theorem embed_getElem? (l : List Nat) (i : Nat) : (embed l)[i]? = (l[i]?).map Int.ofNat := by
  simp [embed]

theorem tab_pegs_set (pegs : Nat → Nat) (h v : Nat) (hh : h < 100) :
    (tab (fun x => Int.ofNat (pegs x))).set ⟨h, by rw [tab_size]; exact hh⟩ (Int.ofNat v) =
      tab (fun x => Int.ofNat (Spec.setPeg pegs h v x)) := by
  rw [tab_set]
  congr 1; funext x
  unfold Spec.setPeg
  by_cases e : x = h <;> simp [e]

/-- The emitted peg stage is `Spec.pegAt`. -/
theorem stageE_spec (lg : List Spec.LetGo) (row col : Nat) (hr : row < 10) (hc : col < 10)
    (st : Spec.BuildSt) (hread : st.read ≤ 5) (htray : TrayOk st.tray)
    (hface : col % 2 = 1 → 1 ≤ st.face ∧ st.face ≤ 9) :
    (stageEE (embLG lg) (Int.ofNat row) (Int.ofNat col) (Int.ofNat (row * 10 + col))
      (embDice st.dice) (embed st.tray) (Int.ofNat st.read) (tab st.covered)
      (st.ships.map embShip).toArray (Int.ofNat st.face)
      (tab (fun x => Int.ofNat (st.pegs x)))).toOption =
    (Spec.pegAt (row * 10 + col) col st).map (fun st' => SudoRt.Flow.cont (embSt st')) := by
  unfold stageEE Spec.pegAt
  rw [show (2 : Int) = Int.ofNat 2 from rfl, modI_ofNat _ (by decide), ok_bind]
  have hh : row * 10 + col < (tab (fun x => Int.ofNat (st.pegs x))).size := by
    rw [tab_size]; omega
  by_cases hp : col % 2 = 0
  · have hb : SudoRt.SEq.beq (Int.ofNat (col % 2)) (0 : Int) = true := by
      show decide _ = _; rw [hp]; rfl
    rw [if_pos hb, if_pos hp, toOpt_bind, atL_toOpt, embed_getElem?]
    cases ht : st.tray[st.read]? with
    | none => rfl
    | some f =>
      have hf := htray f (by
        obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.mp ht; rw [← he]; exact List.getElem_mem hl)
      simp only [Option.map_some', Option.some_bind]
      rw [addI_ofNat_one _ (fits_small (show st.read + 1 ≤ 1000 by omega)), ok_bind,
        keypad_first_spec f hf.1 (fits_small (by omega)), ok_bind,
        putL_ofNat _ _ _ hh, ok_bind, tab_pegs_set _ _ _ (by omega)]
      rfl
  · have hb : SudoRt.SEq.beq (Int.ofNat (col % 2)) (0 : Int) = false := by
      show decide _ = _; apply decide_eq_false; show ¬ ((col % 2 : Nat) : Int) = ((0 : Nat) : Int); omega
    have hf := hface (by omega)
    rw [if_neg (by rw [hb]; decide), if_neg hp,
      keypad_second_spec _ hf.1 (fits_small (by omega)), ok_bind,
      putL_ofNat _ _ _ hh, ok_bind, tab_pegs_set _ _ _ (by omega)]
    rfl

/-- The emitted gap let-go and peg stage is `Spec.letGoAt … true` then `Spec.pegAt`. -/
theorem stageD_spec (lg : List Spec.LetGo) (hlg : FitsLen lg.length) (row col : Nat)
    (hr : row < 10) (hc : col < 10) (st : Spec.BuildSt) (h10 : FitsLen st.dice.d10.length)
    (hread : st.read ≤ 5) (htray : TrayOk st.tray) (hlen : st.tray.length ≤ 5)
    (hface : col % 2 = 1 → 1 ≤ st.face ∧ st.face ≤ 9) :
    (stageDE (embLG lg) (Int.ofNat row) (Int.ofNat col) (Int.ofNat (row * 10 + col))
      (embDice st.dice) (embed st.tray) (Int.ofNat st.read) (tab st.covered)
      (st.ships.map embShip).toArray (Int.ofNat st.face)
      (tab (fun x => Int.ofNat (st.pegs x)))).toOption =
    ((Spec.letGoAt lg (row * 10 + col) true st).bind (Spec.pegAt (row * 10 + col) col)).map
      (fun st' => SudoRt.Flow.cont (embSt st')) := by
  unfold stageDE Spec.letGoAt
  rw [lets_go_spec _ _ _ hlg, ok_bind]
  by_cases hA : Spec.letsGo lg (row * 10 + col) true = true
  · rw [if_pos hA, if_pos hA]
    unfold Spec.BuildSt.rethrow
    rw [toOpt_bind, rethrow_unread_spec _ _ _ h10 (fits_small (by omega))]
    cases hrt : Spec.rethrowUnread st.dice st.tray st.read with
    | none => rfl
    | some p =>
      obtain ⟨d1, t1⟩ := p
      obtain ⟨hl1, ht1, _⟩ := rethrowUnread_facts htray hrt
      simp only [Option.map_some', Option.some_bind]
      exact stageE_spec lg row col hr hc { st with dice := d1, tray := t1 } hread ht1 hface
  · rw [if_neg hA, if_neg hA]
    simp only [Option.some_bind]
    exact stageE_spec lg row col hr hc st hread htray hface

theorem ships_push (l : List Spec.Ship) (s : Spec.Ship) :
    (l.map embShip).toArray.push (embShip s) = ((l ++ [s]).map embShip).toArray := by
  simp [Array.push]

/-- The emitted grow stage (then the gap let-go and the peg) is `Spec.growAt` then the rest. -/
theorem stageC_spec (lg : List Spec.LetGo) (hlg : FitsLen lg.length) (row col : Nat)
    (hr : row < 10) (hc : col < 10) (st : Spec.BuildSt) (hd : DiceFit st.dice)
    (hread : st.read ≤ 5) (htray : TrayOk st.tray) (hlen : st.tray.length ≤ 5)
    (hface : col % 2 = 1 → 1 ≤ st.face ∧ st.face ≤ 9) :
    (stageCE (embLG lg) (Int.ofNat row) (Int.ofNat col) (Int.ofNat (row * 10 + col))
      (embDice st.dice) (embed st.tray) (Int.ofNat st.read) (tab st.covered)
      (st.ships.map embShip).toArray (Int.ofNat st.face)
      (tab (fun x => Int.ofNat (st.pegs x)))).toOption =
    ((Spec.growAt row col st).bind fun st =>
      (Spec.letGoAt lg (row * 10 + col) true st).bind (Spec.pegAt (row * 10 + col) col)).map
      (fun st' => SudoRt.Flow.cont (embSt st')) := by
  unfold stageCE Spec.growAt
  rw [atL_ofNat _ _ (by rw [tab_size]; omega), ok_bind, tab_get]
  by_cases hcv : st.covered (row * 10 + col) = true
  · rw [hcv]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, Option.some_bind]
    exact stageD_spec lg hlg row col hr hc st hd.2.2 hread htray hlen hface
  · have hcv' : st.covered (row * 10 + col) = false := by simpa using hcv
    rw [hcv']
    simp only [Bool.not_false, if_true]
    rw [toOpt_bind, grow_until_it_bumps_spec _ _ _ _ hr hc hd.1 hd.2.1]
    cases hg : Spec.growUntilItBumps st.dice st.covered row col with
    | none => rfl
    | some p =>
      obtain ⟨o, d1⟩ := p
      obtain ⟨hs, hon⟩ := growUntilItBumps_facts _ _ _ _ _ _ hr hc hg
      have h10 : FitsLen d1.d10.length := by rw [hs.2.2]; exact hd.2.2
      cases o with
      | none =>
        simp only [Option.map_some', Option.some_bind, Option.map_none']
        exact stageD_spec lg hlg row col hr hc { st with dice := d1 } h10 hread htray hlen hface
      | some s =>
        simp only [Option.map_some', Option.some_bind]
        rw [cover_spec _ _ (hon s rfl), ok_bind, appendL_spec, ships_push]
        exact stageD_spec lg hlg row col hr hc
          { st with dice := d1, covered := Spec.cover st.covered s, ships := st.ships ++ [s] }
          h10 hread htray hlen hface

theorem DiceFit.of_streams {d0 d : Spec.Dice} (hd : DiceFit d0) (hs : Streams d0 d) : DiceFit d :=
  ⟨by rw [hs.1]; exact hd.1, by rw [hs.2.1]; exact hd.2.1, by rw [hs.2.2]; exact hd.2.2⟩

/-- The emitted hole step after the first let-go (row cup, grow, gap let-go, peg) is
    `Spec.rowCupAt` then the rest. -/
theorem stageB_spec (lg : List Spec.LetGo) (hlg : FitsLen lg.length) (row col : Nat)
    (hr : row < 10) (hc : col < 10) (st : Spec.BuildSt) (hd : DiceFit st.dice)
    (hread : st.read ≤ 5) (htray : TrayOk st.tray) (hlen : st.tray.length ≤ 5)
    (hface : col % 2 = 1 → 1 ≤ st.face ∧ st.face ≤ 9) :
    (stageBE (embLG lg) (Int.ofNat row) (Int.ofNat col) (Int.ofNat (row * 10 + col))
      (embDice st.dice) (embed st.tray) (Int.ofNat st.read) (tab st.covered)
      (st.ships.map embShip).toArray (Int.ofNat st.face)
      (tab (fun x => Int.ofNat (st.pegs x)))).toOption =
    ((Spec.rowCupAt col st).bind fun st => (Spec.growAt row col st).bind fun st =>
      (Spec.letGoAt lg (row * 10 + col) true st).bind (Spec.pegAt (row * 10 + col) col)).map
      (fun st' => SudoRt.Flow.cont (embSt st')) := by
  unfold stageBE Spec.rowCupAt
  have hb : SudoRt.SEq.beq (Int.ofNat col) (0 : Int) = decide (col = 0) := by
    show decide _ = _
    exact decide_eq_decide.mpr (by show ((col : Nat) : Int) = ((0 : Nat) : Int) ↔ _; omega)
  rw [hb]
  by_cases h0 : col = 0
  · subst h0
    simp only [decide_True, if_true]
    rw [toOpt_bind, throw_row_cup_spec _ hd.2.2]
    cases ht : Spec.throwRowCup st.dice with
    | none => rfl
    | some p =>
      obtain ⟨t1, d1⟩ := p
      obtain ⟨hl1, ht1, hs⟩ := throwRowCup_facts ht
      simp only [Option.map_some', Option.some_bind]
      exact stageC_spec lg hlg row 0 hr hc { st with dice := d1, tray := t1, read := 0 }
        (hd.of_streams hs) (Nat.zero_le _) ht1 (by show t1.length ≤ 5; omega) (by intro h; simp at h)
  · simp only [h0, decide_False, Bool.false_eq_true, if_false, Option.some_bind]
    exact stageC_spec lg hlg row col hr hc st hd hread htray hlen hface

end BsLink2.Link2
