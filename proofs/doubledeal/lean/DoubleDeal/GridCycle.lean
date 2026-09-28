/-
  GridCycle (MixColumns stand-in) — walk placement + row-major scoop/lay.
  v11 rule (SPEC §3.5): ghost finger; a blocked placement is sent by its
  blocker (scan row marker + suit(blocker) from column target + rank(blocker),
  dropping a row if full; marker + 1; finger := target + step(blocker)).
  Proves invMixColumns ∘ mixColumns = id and mixColumns ∘ invMixColumns = id
  (both for every packet Fin 52 → Nat). Correctness, zero sorry. No Mathlib.
-/
import DoubleDeal.Basic
import DoubleDeal.Grid

namespace DoubleDeal

/-! ## Geometry -/

def asStart : Fin 4 × Fin 13 := (⟨2, by decide⟩, ⟨0, by decide⟩)

def gridStep (card : Nat) (pos : Fin 4 × Fin 13) : Fin 4 × Fin 13 :=
  (⟨(pos.1.val + suit card) % 4, Nat.mod_lt _ (by decide)⟩,
   ⟨(pos.2.val + rank card) % 13, Nat.mod_lt _ (by decide)⟩)

/-! ## Occupancy

A 52-slot array (column-major bit index `r + 4*c`). Function-valued
occupancy made MixColumns too slow to evaluate; this is the same walk.
-/

abbrev Occ := Array Bool

def occBit (r : Fin 4) (c : Fin 13) : Nat := r.val + 4 * c.val

theorem occBit_lt (r : Fin 4) (c : Fin 13) : occBit r c < 52 := by
  unfold occBit
  have := r.isLt
  have := c.isLt
  omega

theorem occBit_inj {r₁ r₂ : Fin 4} {c₁ c₂ : Fin 13}
    (h : occBit r₁ c₁ = occBit r₂ c₂) : r₁ = r₂ ∧ c₁ = c₂ := by
  have hr₁ := r₁.isLt; have hr₂ := r₂.isLt
  have hc₁ := c₁.isLt; have hc₂ := c₂.isLt
  have : r₁.val = r₂.val ∧ c₁.val = c₂.val := by
    simp only [occBit] at h; omega
  exact ⟨Fin.ext this.1, Fin.ext this.2⟩

def emptyOcc : Occ := Array.mkArray 52 false

theorem size_emptyOcc : emptyOcc.size = 52 := Array.size_mkArray 52 false

def occGet (occ : Occ) (r : Fin 4) (c : Fin 13) : Bool :=
  match occ[occBit r c]? with
  | some b => b
  | none => false

def occAt (occ : Occ) (p : Fin 4 × Fin 13) : Bool := occGet occ p.1 p.2

def setOcc (occ : Occ) (p : Fin 4 × Fin 13) : Occ :=
  if h : occBit p.1 p.2 < occ.size then
    occ.set ⟨occBit p.1 p.2, h⟩ true
  else occ

theorem occGet_empty (r : Fin 4) (c : Fin 13) : occGet emptyOcc r c = false := by
  have hi : occBit r c < 52 := occBit_lt r c
  simp only [occGet, emptyOcc, Array.getElem?_mkArray, hi, ↓reduceIte]

theorem occAt_empty (p : Fin 4 × Fin 13) : occAt emptyOcc p = false :=
  occGet_empty p.1 p.2

theorem size_setOcc (occ : Occ) (p : Fin 4 × Fin 13) :
    (setOcc occ p).size = occ.size := by
  unfold setOcc
  split
  · exact Array.size_set occ _ true
  · rfl

theorem occGet_setOcc (occ : Occ) (p : Fin 4 × Fin 13) (r : Fin 4) (c : Fin 13)
    (hsz : occ.size = 52) :
    occGet (setOcc occ p) r c = (decide (r = p.1 ∧ c = p.2) || occGet occ r c) := by
  have hbitp : occBit p.1 p.2 < occ.size := by rw [hsz]; exact occBit_lt _ _
  unfold occGet setOcc
  simp only [hbitp, ↓reduceDIte]
  rw [Array.get?_set]
  by_cases hb : occBit p.1 p.2 = occBit r c
  · have ⟨hr, hc⟩ := occBit_inj hb
    simp only [hb, ↓reduceIte, hr, hc]
    rfl
  · have hne : ¬ (r = p.1 ∧ c = p.2) := fun ⟨hr, hc⟩ =>
      hb (by simp [hr, hc])
    simp only [hb, ↓reduceIte, hne, ↓reduceIte]
    rfl

theorem setOcc_at_self (occ : Occ) (p : Fin 4 × Fin 13) (hsz : occ.size = 52) :
    occAt (setOcc occ p) p = true := by
  unfold occAt
  rw [occGet_setOcc occ p p.1 p.2 hsz]
  simp

theorem setOcc_at_ne (occ : Occ) {p q : Fin 4 × Fin 13} (hne : p ≠ q)
    (hsz : occ.size = 52) :
    occAt (setOcc occ p) q = occAt occ q := by
  have hne' : ¬ (q.1 = p.1 ∧ q.2 = p.2) := fun hq =>
    hne (Prod.ext hq.1 hq.2).symm
  unfold occAt
  rw [occGet_setOcc occ p q.1 q.2 hsz]
  simp only [decide_eq_false hne', Bool.false_or]

theorem eq_false_of_ne_true {b : Bool} (h : ¬b = true) : b = false := by
  cases b <;> simp_all

def fins13 : List (Fin 13) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

def fins4 : List (Fin 4) := [0, 1, 2, 3]

theorem length_fins13 : fins13.length = 13 := rfl
theorem length_fins4 : fins4.length = 4 := rfl

theorem mem_fins13 (c : Fin 13) : c ∈ fins13 := by
  have : c.val < 13 := c.isLt
  simp [fins13, List.mem_cons]; omega

theorem mem_fins4 (r : Fin 4) : r ∈ fins4 := by
  have : r.val < 4 := r.isLt
  simp [fins4, List.mem_cons]; omega

theorem nodup_fins13 : fins13.Nodup := by decide
theorem nodup_fins4 : fins4.Nodup := by decide

def countCols (occ : Occ) (r : Fin 4) : Nat :=
  (fins13.filter (fun c => occGet occ r c)).length

def occCount (occ : Occ) : Nat :=
  (fins4.map (countCols occ)).sum

theorem countCols_le (occ : Occ) (r : Fin 4) : countCols occ r ≤ 13 := by
  simpa [countCols, length_fins13] using List.length_filter_le (fun c => occGet occ r c) fins13

theorem occCount_le (occ : Occ) : occCount occ ≤ 52 := by
  simp only [occCount, fins4, List.map, List.sum_cons, List.sum_nil, Nat.add_zero]
  have a0 := countCols_le occ 0
  have a1 := countCols_le occ 1
  have a2 := countCols_le occ 2
  have a3 := countCols_le occ 3
  omega

theorem occCount_empty : occCount emptyOcc = 0 := by
  have z : ∀ r : Fin 4, countCols emptyOcc r = 0 := by
    intro r
    simp only [countCols]
    have : fins13.filter (fun c => occGet emptyOcc r c) = [] := by
      refine (List.filter_eq_nil_iff (l := fins13)).mpr ?_
      intro c _; simp [occGet_empty r c]
    simp [this]
  simp [occCount, fins4, List.map, List.sum_cons, List.sum_nil, z]

theorem countCols_full (occ : Occ) (r : Fin 4) (h : ∀ c, occGet occ r c = true) :
    countCols occ r = 13 := by
  simp only [countCols]
  have : fins13.filter (fun c => occGet occ r c) = fins13 :=
    List.filter_eq_self.mpr fun c _ => h c
  simp [this, length_fins13]

theorem occCount_full (occ : Occ) (h : ∀ p : Fin 4 × Fin 13, occAt occ p = true) :
    occCount occ = 52 := by
  simp only [occCount, fins4, List.map, List.sum_cons, List.sum_nil, Nat.add_zero]
  have hr : ∀ r : Fin 4, ∀ c, occGet occ r c = true := fun r c => h (r, c)
  simp [countCols_full occ 0 (hr 0), countCols_full occ 1 (hr 1),
        countCols_full occ 2 (hr 2), countCols_full occ 3 (hr 3)]

theorem exists_free_of_count_lt (occ : Occ) (h : occCount occ < 52) :
    ∃ p : Fin 4 × Fin 13, occAt occ p = false := by
  refine Classical.byContradiction fun hne => ?_
  have hall : ∀ p, occAt occ p = true := by
    intro p
    by_cases hp : occAt occ p = true
    · exact hp
    · exact False.elim (hne ⟨p, eq_false_of_ne_true hp⟩)
  have := occCount_full occ hall
  omega

theorem nodup_cons_iff {α : Type} {a : α} {l : List α} :
    (a :: l).Nodup ↔ (∀ a', a' ∈ l → a ≠ a') ∧ l.Nodup := by
  simp only [List.Nodup, List.pairwise_cons]

theorem map_eq_of_mem {α β} (f g : α → β) (l : List α) (h : ∀ x ∈ l, f x = g x) :
    l.map f = l.map g := (List.map_eq_map_iff).mpr h

theorem filter_mark_one {α : Type} [DecidableEq α]
    (target : α) (f : α → Bool) (xs : List α)
    (hn : xs.Nodup) (hc : target ∈ xs) (hf : f target = false) :
    (xs.filter (fun x => decide (x = target) || f x)).length =
      (xs.filter f).length + 1 := by
  induction xs with
  | nil => cases hc
  | cons a rest ih =>
    have ⟨hnotin_head, hnRest⟩ := (nodup_cons_iff).mp hn
    simp only [List.mem_cons] at hc
    simp only [List.filter]
    cases hc with
    | inl heq =>
      cases heq
      have ht : (decide (target = target) || f target) = true := by simp
      simp only [ht, ↓reduceIte, hf]
      have heqRest :
          rest.filter (fun x => decide (x = target) || f x) = rest.filter f :=
        List.filter_congr fun x hx => by
          have hxne : x ≠ target := fun he => hnotin_head x hx he.symm
          simp [decide_eq_false hxne]
      simp [heqRest]
    | inr hrest =>
      have ih' := ih hnRest hrest
      by_cases ha : a = target
      · cases ha
        exact False.elim (hnotin_head target hrest rfl)
      · simp only [decide_eq_false ha, Bool.false_or]
        split <;> simp [ih']

theorem countCols_set_free (occ : Occ) (r : Fin 4) (c : Fin 13)
    (hsz : occ.size = 52) (hfree : occGet occ r c = false) :
    countCols (setOcc occ (r, c)) r = countCols occ r + 1 := by
  have hfun : ∀ col, occGet (setOcc occ (r, c)) r col =
      (decide (col = c) || occGet occ r col) := by
    intro col
    have h := occGet_setOcc occ (r, c) r col hsz
    simp only [true_and] at h
    exact h
  unfold countCols
  have hfilter :
      fins13.filter (fun col => occGet (setOcc occ (r, c)) r col) =
        fins13.filter (fun col => decide (col = c) || occGet occ r col) :=
    List.filter_congr fun col _ => by rw [hfun col]
  rw [hfilter]
  exact filter_mark_one c (occGet occ r) fins13 nodup_fins13 (mem_fins13 c) hfree

theorem countCols_set_other_row (occ : Occ) (r : Fin 4) (p : Fin 4 × Fin 13)
    (hsz : occ.size = 52) (hne : r ≠ p.1) :
    countCols (setOcc occ p) r = countCols occ r := by
  simp only [countCols]
  apply congrArg List.length
  exact List.filter_congr fun col _ => by
    have : decide (r = p.1 ∧ col = p.2) = false :=
      decide_eq_false fun ⟨hr, _⟩ => hne hr
    simp [occGet_setOcc occ p r col hsz, this]

theorem sum_incr_at {α : Type} [DecidableEq α]
    (f : α → Nat) (r0 : α) (xs : List α)
    (hn : xs.Nodup) (hc : r0 ∈ xs) :
    (xs.map (fun r => if r = r0 then f r + 1 else f r)).sum =
      (xs.map f).sum + 1 := by
  induction xs with
  | nil => cases hc
  | cons a rest ih =>
    have ⟨hhead, hnRest⟩ := (nodup_cons_iff).mp hn
    simp only [List.mem_cons] at hc
    simp only [List.map, List.sum_cons]
    cases hc with
    | inl heq =>
      cases heq
      simp only [ite_true]
      have heqRest :
          rest.map (fun r => if r = r0 then f r + 1 else f r) = rest.map f :=
        map_eq_of_mem _ _ rest fun r hr => by
          have : r ≠ r0 := fun he => hhead r hr he.symm
          simp [this]
      rw [heqRest]; omega
    | inr hrest =>
      have hne : a ≠ r0 := fun he => hhead r0 hrest he
      simp only [hne, ite_false]
      have := ih hnRest hrest
      omega

theorem occCount_set_free (occ : Occ) (p : Fin 4 × Fin 13)
    (hsz : occ.size = 52) (hfree : occAt occ p = false) :
    occCount (setOcc occ p) = occCount occ + 1 := by
  simp only [occCount]
  have hmap :
      fins4.map (countCols (setOcc occ p)) =
        fins4.map (fun r => if r = p.1 then countCols occ r + 1 else countCols occ r) := by
    apply map_eq_of_mem
    intro r _
    by_cases he : r = p.1
    · cases he
      simp [countCols_set_free occ p.1 p.2 hsz hfree]
    · simp [he, countCols_set_other_row occ r p hsz he]
  rw [hmap]
  exact sum_incr_at (countCols occ) p.1 fins4 nodup_fins4 (mem_fins4 p.1)


/-! ## Overflow scan

A blocked placement scans one row from column `start` and wraps from 12 back
to 0 (SPEC §3.5; sudo `scan_row`). In v11 the row is marker + suit(blocker)
and `start` is target column + rank(blocker); a full row drops to the next.
-/

/-- Column visited at offset `k` of a scan from `start`. -/
def rotCol (start k : Nat) : Fin 13 := ⟨(start + k) % 13, Nat.mod_lt _ (by decide)⟩

def scanRowN (occ : Occ) (row : Fin 4) (start : Nat) : Nat → Nat → Option (Fin 13)
  | 0, _ => none
  | fuel + 1, k =>
      if occGet occ row (rotCol start k) then scanRowN occ row start fuel (k + 1)
      else some (rotCol start k)

def scanRow (occ : Occ) (row : Fin 4) (start : Nat) : Option (Fin 13) :=
  scanRowN occ row start 13 0

theorem scanRowN_some_free (occ : Occ) (row : Fin 4) (start : Nat) :
    ∀ (fuel k : Nat) (c : Fin 13),
      scanRowN occ row start fuel k = some c → occGet occ row c = false
  | 0, k, c, h => by cases h
  | fuel + 1, k, c, h => by
      simp only [scanRowN] at h
      split at h
      · next => exact scanRowN_some_free occ row start fuel (k + 1) c h
      · next hne =>
          injection h with heq; cases heq
          exact eq_false_of_ne_true hne

theorem scanRowN_none_occupied (occ : Occ) (row : Fin 4) (start : Nat) :
    ∀ (fuel k : Nat), scanRowN occ row start fuel k = none →
      ∀ j : Nat, k ≤ j → j < k + fuel → occGet occ row (rotCol start j) = true
  | 0, k, _, j, hj1, hj2 => by omega
  | fuel + 1, k, hnone, j, hj1, hj2 => by
      simp only [scanRowN] at hnone
      split at hnone
      · next hocc =>
        have ih := scanRowN_none_occupied occ row start fuel (k + 1) hnone
        by_cases heq : j = k
        · subst heq; exact hocc
        · exact ih j (by omega) (by omega)
      · next => cases hnone

/-- Every column is hit by some offset `k < 13` from `start`. -/
theorem mod13_cover (start : Nat) (c : Fin 13) :
    ∃ k, k < 13 ∧ (start + k) % 13 = c.val := by
  have hc := c.isLt
  refine ⟨(c.val + 13 - start % 13) % 13, Nat.mod_lt _ (by decide), ?_⟩
  omega

theorem scanRow_none_full (occ : Occ) (row : Fin 4) (start : Nat)
    (h : scanRow occ row start = none) :
    ∀ c : Fin 13, occGet occ row c = true := by
  intro c
  obtain ⟨k, hk, hkc⟩ := mod13_cover start c
  have := scanRowN_none_occupied occ row start 13 0 h k (by omega) (by omega)
  have hfin : rotCol start k = c := Fin.ext hkc
  rwa [hfin] at this

theorem scanRow_some_free (occ : Occ) (row : Fin 4) (start : Nat) (c : Fin 13)
    (h : scanRow occ row start = some c) : occGet occ row c = false :=
  scanRowN_some_free occ row start 13 0 c h

def overflowN (occ : Occ) (start : Nat) : Nat → Nat → Option (Fin 4 × Fin 13)
  | 0, _ => none
  | fuel + 1, t =>
      let row : Fin 4 := ⟨t % 4, Nat.mod_lt _ (by decide)⟩
      match scanRow occ row start with
      | some c => some (row, c)
      | none => overflowN occ start fuel ((t + 1) % 4)

/-- Blocked-placement seat: rows `row, row+1, …` (mod 4), each scanned from
    `start` (sudo `overflow_seat`). -/
def overflowSeat (occ : Occ) (row start : Nat) : Option (Fin 4 × Fin 13) :=
  overflowN occ start 4 row

theorem overflowN_some_free (occ : Occ) (start : Nat) :
    ∀ (fuel t : Nat) (p : Fin 4 × Fin 13),
      overflowN occ start fuel t = some p → occAt occ p = false
  | 0, t, p, h => by cases h
  | fuel + 1, t, p, h => by
      match hs : scanRow occ ⟨t % 4, Nat.mod_lt _ (by decide)⟩ start with
      | some c =>
          have h' : overflowN occ start (fuel + 1) t =
              some (⟨t % 4, Nat.mod_lt _ (by decide)⟩, c) := by
            simp only [overflowN, hs]
          rw [h'] at h
          injection h with hp
          cases hp
          exact scanRow_some_free occ _ start c hs
      | none =>
          have h' : overflowN occ start (fuel + 1) t = overflowN occ start fuel ((t + 1) % 4) := by
            simp only [overflowN, hs]
          rw [h'] at h
          exact overflowN_some_free occ start fuel ((t + 1) % 4) p h

theorem add_left_mod_mod (a b n : Nat) : (a + b % n) % n = (a + b) % n := by
  calc (a + b % n) % n
      = (a % n + b % n % n) % n := by rw [Nat.add_mod]
    _ = (a % n + b % n) % n := by rw [Nat.mod_mod]
    _ = (a + b) % n := by rw [← Nat.add_mod]

theorem mod4_cover (t : Nat) (r : Fin 4) :
    ∃ i : Fin 4, (t + i.val) % 4 = r.val := by
  have ht : t % 4 < 4 := Nat.mod_lt t (by decide)
  have hr : r.val < 4 := r.isLt
  let iVal := (r.val + 4 - t % 4) % 4
  have hi : iVal < 4 := Nat.mod_lt _ (by decide)
  refine ⟨⟨iVal, hi⟩, ?_⟩
  have h1 : (t + iVal) % 4 = (t % 4 + iVal) % 4 := by
    calc (t + iVal) % 4
        = (t % 4 + iVal % 4) % 4 := Nat.add_mod t iVal 4
      _ = (t % 4 + iVal) % 4 := by rw [Nat.mod_eq_of_lt hi]
  rw [h1]
  show (t % 4 + (r.val + 4 - t % 4) % 4) % 4 = r.val
  rw [add_left_mod_mod]
  have : t % 4 + (r.val + 4 - t % 4) = r.val + 4 := by omega
  rw [this, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hr

theorem overflowN_none_row_full (occ : Occ) (start : Nat) :
    ∀ (fuel t : Nat), overflowN occ start fuel t = none →
      ∀ i : Nat, i < fuel → ∀ c : Fin 13,
        occGet occ ⟨(t + i) % 4, Nat.mod_lt _ (by decide)⟩ c = true
  | 0, t, _, i, hi, c => by omega
  | fuel + 1, t, hnone, i, hi, c => by
      match hs : scanRow occ ⟨t % 4, Nat.mod_lt _ (by decide)⟩ start with
      | some c0 =>
          simp only [overflowN, hs] at hnone
          cases hnone
      | none =>
          have hrec : overflowN occ start (fuel + 1) t = overflowN occ start fuel ((t + 1) % 4) := by
            simp only [overflowN, hs]
          rw [hrec] at hnone
          cases i with
          | zero =>
              exact scanRow_none_full occ ⟨t % 4, Nat.mod_lt _ (by decide)⟩ start hs c
          | succ j =>
              have hj : j < fuel := by omega
              have ih := overflowN_none_row_full occ start fuel ((t + 1) % 4) hnone j hj c
              have heq : (((t + 1) % 4) + j) % 4 = (t + (j + 1)) % 4 := by
                rw [Nat.mod_add_mod]; ac_rfl
              have hrow :
                  (⟨(((t + 1) % 4) + j) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) =
                  ⟨(t + (j + 1)) % 4, Nat.mod_lt _ (by decide)⟩ := Fin.ext heq
              rw [← hrow]; exact ih

theorem overflow_none_full (occ : Occ) (t start : Nat)
    (h : overflowSeat occ t start = none) :
    ∀ p : Fin 4 × Fin 13, occAt occ p = true := by
  intro ⟨r, c⟩
  obtain ⟨i, hi⟩ := mod4_cover t r
  have hocc := overflowN_none_row_full occ start 4 t h i.val i.isLt c
  have hrow : (⟨(t + i.val) % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = r := Fin.ext hi
  simpa [occAt, hrow] using hocc

theorem overflow_some_of_count_lt (occ : Occ) (t start : Nat) (h : occCount occ < 52) :
    ∃ p, overflowSeat occ t start = some p ∧ occAt occ p = false := by
  cases hs : overflowSeat occ t start with
  | none =>
      have := occCount_full occ (overflow_none_full occ t start hs)
      omega
  | some p =>
      refine ⟨p, rfl, overflowN_some_free occ start 4 t p hs⟩

/-! ## Card grid -/

abbrev NatGrid := Grid Nat

def setGrid (g : NatGrid) (p : Fin 4 × Fin 13) (card : Nat) : NatGrid :=
  fun r c => if decide (r = p.1 ∧ c = p.2) then card else g r c

theorem get_setGrid_self (g : NatGrid) (p : Fin 4 × Fin 13) (card : Nat) :
    setGrid g p card p.1 p.2 = card := by
  simp [setGrid]

theorem get_setGrid_ne (g : NatGrid) {p q : Fin 4 × Fin 13} (card : Nat) (hne : p ≠ q) :
    setGrid g p card q.1 q.2 = g q.1 q.2 := by
  simp only [setGrid]
  by_cases hq : q.1 = p.1 ∧ q.2 = p.2
  · exact False.elim (hne (Prod.ext hq.1 hq.2).symm)
  · simp [decide_eq_false hq]

/-! ## Shared walk step

`prev` holds the last card and the **finger** (v11: the ghost finger, i.e.
the last target, not necessarily the seat the card landed on). `board` is the
table so far, so a blocked placement can read its blocker. -/

structure WalkState where
  occ : Occ
  t : Nat
  prev : Option (Nat × (Fin 4 × Fin 13))
  board : NatGrid

def initWalk : WalkState :=
  { occ := emptyOcc, t := 0, prev := none, board := fun _ _ => (0 : Nat) }

/-- A chooser's answer: the seat, then the next marker and the next finger. -/
abbrev SeatChoice := (Fin 4 × Fin 13) × (Nat × (Fin 4 × Fin 13))

def advance (st : WalkState) (card : Nat) (pos : Fin 4 × Fin 13)
    (tf : Nat × (Fin 4 × Fin 13)) : WalkState where
  occ := setOcc st.occ pos
  t := tf.1
  prev := some (card, tf.2)
  board := setGrid st.board pos card

/-- v11 blocked placement at `target` with blocker `b`: scan row
    `(t + suit b) % 4` from column `(target.col + rank b) % 13`, dropping rows;
    marker `t + 1`; finger `target + step b`. -/
def blockedChoice (st : WalkState) (target : Fin 4 × Fin 13) : Option SeatChoice :=
  let b := st.board target.1 target.2
  (overflowSeat st.occ ((st.t + suit b) % 4) ((target.2.val + rank b) % 13)).map
    fun p => (p, ((st.t + 1) % 4, gridStep b target))

def chooseSeat? (st : WalkState) : Option SeatChoice :=
  match st.prev with
  | none => some (asStart, (st.t, asStart))
  | some (card, finger) =>
      let target := gridStep card finger
      if occAt st.occ target then blockedChoice st target
      else some (target, (st.t, target))

theorem blockedChoice_some (st : WalkState) (target : Fin 4 × Fin 13)
    (hct : occCount st.occ < 52) :
    ∃ p, blockedChoice st target =
        some (p, ((st.t + 1) % 4, gridStep (st.board target.1 target.2) target)) ∧
      occAt st.occ p = false := by
  obtain ⟨p, hs, hf⟩ := overflow_some_of_count_lt st.occ
    ((st.t + suit (st.board target.1 target.2)) % 4)
    ((target.2.val + rank (st.board target.1 target.2)) % 13) hct
  exact ⟨p, by simp [blockedChoice, hs], hf⟩

/-- `chooseSeat?` returns `some` while a free seat exists. Matches sudo
    `overflow_seat`'s `assert false` being unreachable on a 52-card walk. -/
theorem chooseSeat?_isSome (st : WalkState) (hct : occCount st.occ < 52) :
    (chooseSeat? st).isSome := by
  match hprev_eq : st.prev with
  | none =>
      simp [chooseSeat?, hprev_eq, Option.isSome]
  | some pair =>
      simp only [chooseSeat?, hprev_eq, Option.isSome]
      by_cases ht : occAt st.occ (gridStep pair.1 pair.2)
      · simp only [ht, ↓reduceIte]
        obtain ⟨p, hs, _hf⟩ := blockedChoice_some st (gridStep pair.1 pair.2) hct
        simp [hs]
      · simp [eq_false_of_ne_true ht]

/-- Total choose. The `none` branch is unreachable under `chooseSeat?_isSome`
    (occCount < 52). Fail like doubledeal.sudo `assert false`, not a silent AS. -/
def chooseSeat! (st : WalkState) : SeatChoice :=
  match chooseSeat? st with
  | some x => x
  | none =>
      panic! "DoubleDeal.chooseSeat!: overflow scan returned none (grid full?)"

theorem chooseSeat!_free (st : WalkState) (hct : occCount st.occ < 52)
    (hprev : st.prev.isSome ∨ occAt st.occ asStart = false) :
    occAt st.occ (chooseSeat! st).1 = false := by
  match hprev_eq : st.prev with
  | none =>
      have : chooseSeat? st = some (asStart, (st.t, asStart)) := by simp [chooseSeat?, hprev_eq]
      simp only [chooseSeat!, this]
      cases hprev with
      | inl h => simp [hprev_eq] at h
      | inr h => exact h
  | some pair =>
      simp only [chooseSeat!, chooseSeat?, hprev_eq]
      by_cases ht : occAt st.occ (gridStep pair.1 pair.2)
      · simp only [ht, ↓reduceIte]
        obtain ⟨p, hs, hf⟩ := blockedChoice_some st (gridStep pair.1 pair.2) hct
        simp only [hs]
        exact hf
      · have hf := eq_false_of_ne_true ht
        simp [hf]

/-! ## Placement and inverse on Fin 52 → Nat -/

/-- Place first `n` cards of `hand` (n ≤ 52). -/
def placeN (hand : Fin 52 → Nat) : Nat → NatGrid × WalkState
  | 0 => ((fun _ _ => (0 : Nat)), initWalk)
  | n + 1 =>
      let (g, st) := placeN hand n
      if h : n < 52 then
        let (pos, markerFinger) := chooseSeat! st
        let card := hand ⟨n, h⟩
        (setGrid g pos card, advance st card pos markerFinger)
      else (g, st)

def placedGrid (hand : Fin 52 → Nat) : NatGrid := (placeN hand 52).1

/-- MixColumns: place then scoop row-major. -/
def mixColumns (hand : Fin 52 → Nat) : Fin 52 → Nat :=
  scoopRowMajor (placedGrid hand)

/-- Recover first `n` cards from grid by the same walk. -/
def invN (g : NatGrid) : Nat → (Fin 52 → Nat) × WalkState
  | 0 => ((fun _ => (0 : Nat)), initWalk)
  | n + 1 =>
      let (out, st) := invN g n
      if _h : n < 52 then
        let (pos, markerFinger) := chooseSeat! st
        let card := g pos.1 pos.2
        (fun j => if j.val = n then card else out j, advance st card pos markerFinger)
      else (out, st)

/-- Inv MixColumns: lay row-major then walk-recover. -/
def invMixColumns (packet : Fin 52 → Nat) : Fin 52 → Nat :=
  (invN (layRowMajor packet) 52).1

/-! ## Placement succeeds: after n ≤ 52 steps, occCount = n and last choose was free -/

theorem placeN_occ_size (hand : Fin 52 → Nat) :
    ∀ n, (placeN hand n).2.occ.size = 52
  | 0 => by simp [placeN, initWalk, size_emptyOcc]
  | n + 1 => by
      simp only [placeN]
      split
      · rw [advance, size_setOcc]; exact placeN_occ_size hand n
      · exact placeN_occ_size hand n

theorem placeN_count (hand : Fin 52 → Nat) :
    ∀ n : Nat, n ≤ 52 → occCount (placeN hand n).2.occ = n
  | 0, _ => by simp [placeN, initWalk, occCount_empty]
  | n + 1, hn => by
      have hn' : n ≤ 52 := by omega
      have hc := placeN_count hand n hn'
      have hlt : n < 52 := by omega
      simp only [placeN, hlt, ↓reduceDIte]
      -- After simp, goal is about advance (placeN hand n).2 ...
      have hct : occCount (placeN hand n).2.occ < 52 := by omega
      have hfree :
          occAt (placeN hand n).2.occ (chooseSeat! (placeN hand n).2).1 = false := by
        refine chooseSeat!_free (placeN hand n).2 hct ?_
        cases hpv : (placeN hand n).2.prev with
        | none =>
            cases n with
            | zero =>
                exact Or.inr (by simp [placeN, initWalk, occAt_empty])
            | succ n' =>
                simp only [placeN, show n' < 52 by omega, ↓reduceDIte, advance] at hpv
                cases hpv
        | some _ =>
            exact Or.inl (by simp [Option.isSome, hpv])
      change occCount
          (setOcc (placeN hand n).2.occ (chooseSeat! (placeN hand n).2).1) = n + 1
      have hset := occCount_set_free (placeN hand n).2.occ
          (chooseSeat! (placeN hand n).2).1 (placeN_occ_size hand n) hfree
      omega

/-- Alias kept for Round imports / length lemmas. -/
def gridCycle (deck : List Nat) : List Nat :=
  if h : deck.length = 52 then
    let f := fun i : Fin 52 => deck[i.val]'(by omega)
    (Array.ofFn (mixColumns f)).toList
  else deck

theorem gridCycle_length_le (deck : List Nat) :
    (gridCycle deck).length ≤ deck.length := by
  simp only [gridCycle]
  split
  · next _h =>
      have : ((Array.ofFn (mixColumns fun i : Fin 52 =>
          deck[i.val]'(by omega))).toList).length = 52 := Array.size_ofFn _
      omega
  · exact Nat.le_refl _

/-! ## Round-trip helpers -/

theorem placeN_choose_free (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52) :
    occAt (placeN hand n).2.occ (chooseSeat! (placeN hand n).2).1 = false := by
  have hc := placeN_count hand n (Nat.le_of_lt hn)
  have hct : occCount (placeN hand n).2.occ < 52 := by omega
  refine chooseSeat!_free (placeN hand n).2 hct ?_
  cases hpv : (placeN hand n).2.prev with
  | none =>
      cases n with
      | zero => exact Or.inr (by simp [placeN, initWalk, occAt_empty])
      | succ n' =>
          simp only [placeN, show n' < 52 by omega, ↓reduceDIte, advance] at hpv
          cases hpv
  | some _ => exact Or.inl (by simp [Option.isSome, hpv])

def placeSeat (hand : Fin 52 → Nat) (n : Nat) (_hn : n < 52) : Fin 4 × Fin 13 :=
  (chooseSeat! (placeN hand n).2).1

theorem occ_mono (hand : Fin 52 → Nat) :
    ∀ (m n : Nat), n ≤ m → m ≤ 52 → ∀ (p : Fin 4 × Fin 13),
      occAt (placeN hand n).2.occ p = true →
      occAt (placeN hand m).2.occ p = true
  | 0, n, hnm, hm, p, hp => by
      have : n = 0 := by omega
      subst this; exact hp
  | m + 1, n, hnm, hm, p, hp => by
      by_cases hnm' : n ≤ m
      · have hprev := occ_mono hand m n hnm' (by omega) p hp
        have hlt : m < 52 := by omega
        simp only [placeN, hlt, ↓reduceDIte, advance]
        by_cases he : p = (chooseSeat! (placeN hand m).2).1
        · cases he; exact setOcc_at_self _ _ (placeN_occ_size hand m)
        · rw [setOcc_at_ne (placeN hand m).2.occ (Ne.symm he) (placeN_occ_size hand m)]; exact hprev
      · have : n = m + 1 := by omega
        cases this; exact hp

theorem seat_occupied_after (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52) :
    occAt (placeN hand (n + 1)).2.occ (placeSeat hand n hn) = true := by
  simp only [placeN, placeSeat, hn, ↓reduceDIte, advance]
  exact setOcc_at_self _ _ (placeN_occ_size hand n)

theorem place_write_stable (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52)
    (m : Nat) (hnm : n < m) (hm : m ≤ 52) :
    (placeN hand m).1 (placeSeat hand n hn).1 (placeSeat hand n hn).2 =
      hand ⟨n, hn⟩ := by
  induction m with
  | zero => omega
  | succ m ih =>
      have hlt : m < 52 := by omega
      simp only [placeN, hlt, ↓reduceDIte]
      by_cases heq : (chooseSeat! (placeN hand m).2).1 = placeSeat hand n hn
      · by_cases hmn : m = n
        · cases hmn
          simp only [placeSeat, get_setGrid_self]
        · have hocc := occ_mono hand m (n + 1) (by omega) (by omega)
            (placeSeat hand n hn) (seat_occupied_after hand n hn)
          have hfree := placeN_choose_free hand m hlt
          rw [heq] at hfree
          simp only [hocc] at hfree
          exact (Bool.noConfusion hfree)
      · have hne : (chooseSeat! (placeN hand m).2).1 ≠ placeSeat hand n hn := heq
        rw [get_setGrid_ne (placeN hand m).1 (hand ⟨m, hlt⟩) hne]
        rcases Nat.lt_trichotomy n m with hlt' | heq' | hgt
        · exact ih hlt' (by omega)
        · cases heq'; exact False.elim (hne rfl)
        · omega

theorem placed_at_seat (hand : Fin 52 → Nat) (n : Nat) (hn : n < 52) :
    placedGrid hand (placeSeat hand n hn).1 (placeSeat hand n hn).2 =
      hand ⟨n, hn⟩ :=
  place_write_stable hand n hn 52 (by omega) (by omega)

theorem inv_place_agree (hand : Fin 52 → Nat) (n : Nat) (hn : n ≤ 52) :
    (invN (placedGrid hand) n).2 = (placeN hand n).2 ∧
    ∀ (i : Fin 52), i.val < n → (invN (placedGrid hand) n).1 i = hand i := by
  induction n with
  | zero =>
      constructor
      · rfl
      · intro i hi; omega
  | succ n ih =>
      have hn' : n ≤ 52 := by omega
      have ⟨hst, hout⟩ := ih hn'
      have hlt : n < 52 := by omega
      have hchoose :
          chooseSeat! (invN (placedGrid hand) n).2 =
            chooseSeat! (placeN hand n).2 := by rw [hst]
      have hcard :
          placedGrid hand
              (chooseSeat! (placeN hand n).2).1.1
              (chooseSeat! (placeN hand n).2).1.2 =
            hand ⟨n, hlt⟩ := by
        simpa [placeSeat] using placed_at_seat hand n hlt
      simp only [invN, hlt, ↓reduceDIte]
      constructor
      · simp only [placeN, hlt, ↓reduceDIte]
        rw [hst]
        have : placedGrid hand
            (chooseSeat! (placeN hand n).2).1.1
            (chooseSeat! (placeN hand n).2).1.2 = hand ⟨n, hlt⟩ := hcard
        simp only [this]
      · intro i hi
        by_cases he : i.val = n
        · simp only [he, ↓reduceIte]
          have : i = ⟨n, hlt⟩ := Fin.ext he
          rw [hst]
          simpa [placeSeat, this] using placed_at_seat hand n hlt
        · have hil : i.val < n := by omega
          simp only [he, ↓reduceIte]
          exact hout i hil

attribute [irreducible] setOcc occGet emptyOcc

theorem invMixColumns_mixColumns (hand : Fin 52 → Nat) :
    invMixColumns (mixColumns hand) = hand := by
  funext i
  unfold invMixColumns mixColumns placedGrid
  rw [lay_scoop_rowMajor]
  exact (inv_place_agree hand 52 (by omega)).2 i i.isLt

/-! ## Right inverse: mixColumns ∘ invMixColumns = id

For an arbitrary packet `p : Fin 52 → Nat` (no deck / permutation hypothesis),
let `g := layRowMajor p` and `h := invMixColumns p`. The decrypt walk `invN g`
and the encrypt walk `placeN h` pass through identical `WalkState`s (every
seat decision reads only the state and the card being placed, and the card
`invN` records at step `n` is exactly the card `placeN` places at step `n`).
After 52 steps all 52 seats are occupied, so every seat of `g` was written by
the encrypt walk with the value `invN` read from it: `placedGrid h = g`. -/

/-- Seat chosen at step `n` of the decrypt walk over grid `g`. -/
def invSeat (g : NatGrid) (n : Nat) : Fin 4 × Fin 13 :=
  (chooseSeat! (invN g n).2).1

/-- `invN` records, at index `j < n`, the grid value at the seat of step `j`,
    and later steps never overwrite it. -/
theorem invN_out (g : NatGrid) :
    ∀ n, n ≤ 52 → ∀ j : Fin 52, j.val < n →
      (invN g n).1 j = g (invSeat g j.val).1 (invSeat g j.val).2 := by
  intro n
  induction n with
  | zero => intro _ j hj; omega
  | succ n ih =>
      intro hn j hj
      have hlt : n < 52 := by omega
      simp only [invN, hlt, ↓reduceDIte]
      by_cases he : j.val = n
      · simp only [he, ↓reduceIte, invSeat]
      · simp only [he, ↓reduceIte]
        exact ih (by omega) j (by omega)

/-- The encrypt walk on `invMixColumns`'s output shadows the decrypt walk. -/
theorem placeN_invN_state (g : NatGrid) :
    ∀ n, n ≤ 52 → (placeN (invN g 52).1 n).2 = (invN g n).2 := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hlt : n < 52 := by omega
      have hst := ih (by omega)
      have hcard : (invN g 52).1 ⟨n, hlt⟩ =
          g (chooseSeat! (invN g n).2).1.1 (chooseSeat! (invN g n).2).1.2 :=
        invN_out g 52 (by omega) ⟨n, hlt⟩ hlt
      generalize (invN g 52).1 = H at hst hcard ⊢
      simp only [placeN, invN, hlt, ↓reduceDIte]
      rw [hst, hcard]

/-- Every occupied seat after `n` placement steps was chosen at some step `k < n`. -/
theorem placeN_occ_chosen (hand : Fin 52 → Nat) :
    ∀ n, n ≤ 52 → ∀ q : Fin 4 × Fin 13, occAt (placeN hand n).2.occ q = true →
      ∃ k, k < n ∧ (chooseSeat! (placeN hand k).2).1 = q := by
  intro n
  induction n with
  | zero =>
      intro _ q hq
      have : occAt (placeN hand 0).2.occ q = false := by
        simp [placeN, initWalk, occAt_empty]
      rw [this] at hq; cases hq
  | succ n ih =>
      intro hn q hq
      have hlt : n < 52 := by omega
      by_cases he : q = (chooseSeat! (placeN hand n).2).1
      · exact ⟨n, by omega, he.symm⟩
      · simp only [placeN, hlt, ↓reduceDIte, advance] at hq
        rw [setOcc_at_ne (placeN hand n).2.occ (Ne.symm he) (placeN_occ_size hand n)] at hq
        obtain ⟨k, hk, hkq⟩ := ih (by omega) q hq
        exact ⟨k, by omega, hkq⟩

theorem filter_length_lt {α : Type _} (f : α → Bool) :
    ∀ (xs : List α) (x : α), x ∈ xs → f x = false → (xs.filter f).length < xs.length
  | [], _, hx, _ => by cases hx
  | y :: ys, x, hx, hf => by
      have hle := List.length_filter_le f ys
      rcases List.mem_cons.mp hx with h | h
      · subst h; simp [List.filter_cons, hf]; omega
      · have ih := filter_length_lt f ys x h hf
        by_cases hy : f y = true
        · simp [List.filter_cons, hy]; omega
        · simp [List.filter_cons, hy]; omega

theorem occCount_lt_of_free (occ : Occ) (q : Fin 4 × Fin 13) (hq : occAt occ q = false) :
    occCount occ < 52 := by
  have hrow : countCols occ q.1 < 13 := by
    have := filter_length_lt (fun c => occGet occ q.1 c) fins13 q.2 (mem_fins13 q.2) hq
    simpa [countCols, length_fins13] using this
  simp only [occCount, fins4, List.map, List.sum_cons, List.sum_nil, Nat.add_zero]
  have a0 := countCols_le occ 0
  have a1 := countCols_le occ 1
  have a2 := countCols_le occ 2
  have a3 := countCols_le occ 3
  have hv : q.1.val < 4 := q.1.isLt
  have hcases : q.1 = 0 ∨ q.1 = 1 ∨ q.1 = 2 ∨ q.1 = 3 := by
    rcases (by omega : q.1.val = 0 ∨ q.1.val = 1 ∨ q.1.val = 2 ∨ q.1.val = 3)
      with h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
  rcases hcases with h | h | h | h <;> rw [h] at hrow <;> omega

/-- After 52 placement steps every seat is occupied. -/
theorem placeN_all_occ (hand : Fin 52 → Nat) (q : Fin 4 × Fin 13) :
    occAt (placeN hand 52).2.occ q = true := by
  cases hq : occAt (placeN hand 52).2.occ q with
  | true => rfl
  | false =>
      have h1 := occCount_lt_of_free _ q hq
      have h2 := placeN_count hand 52 (by omega)
      omega

/-- The encrypt walk on `invMixColumns p` rebuilds exactly the laid grid of `p`. -/
theorem placedGrid_invN (g : NatGrid) : placedGrid (invN g 52).1 = g := by
  funext r c
  obtain ⟨k, hk, hkq⟩ :=
    placeN_occ_chosen (invN g 52).1 52 (by omega) (r, c) (placeN_all_occ _ (r, c))
  have hseat : placeSeat (invN g 52).1 k hk = invSeat g k := by
    simp only [placeSeat, invSeat, placeN_invN_state g k (by omega)]
  have hp := placed_at_seat (invN g 52).1 k hk
  rw [invN_out g 52 (by omega) ⟨k, hk⟩ hk, hseat] at hp
  have hrc : invSeat g k = (r, c) := by
    rw [← hseat]; exact hkq
  rw [hrc] at hp
  exact hp

/-- Right inverse (encrypt-after-decrypt) of the v11 GridCycle layer, for every
    packet `Fin 52 → Nat` (no deck / permutation hypothesis). -/
theorem mixColumns_invMixColumns (packet : Fin 52 → Nat) :
    mixColumns (invMixColumns packet) = packet := by
  unfold mixColumns invMixColumns
  rw [placedGrid_invN, scoop_lay_rowMajor]

end DoubleDeal
