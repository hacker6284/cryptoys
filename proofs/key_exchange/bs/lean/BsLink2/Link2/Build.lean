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

end BsLink2.Link2
