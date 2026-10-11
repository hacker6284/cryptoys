/-
  `new_board`: a fresh board, spare pegs, the halving loop, `lay_rung`, `clear`,
  `climb_holes`, and the ladder list. The control row is `Spec.rungList` in build
  order. The ladder array is that list climbed from the last rung, which is how
  `invert` reads it. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Basic
import EcbsLink2.Link2.Place
import EcbsLink2.Link2.School

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-! ### Halving arithmetic -/

def afterDiv (c : Nat) : Nat → Nat
  | 0 => c
  | k + 1 => afterDiv c k / 2

private theorem afterDiv_zero (c : Nat) : afterDiv c 0 = c := rfl

private theorem afterDiv_succ (c k : Nat) : afterDiv c (k + 1) = afterDiv c k / 2 := rfl

private theorem afterDiv_shift (c k : Nat) : afterDiv c (k + 1) = afterDiv (c / 2) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [afterDiv_succ, ih, afterDiv_succ]

def charged (c : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => charged c k + if afterDiv c k ≤ 1 then 0 else rungMoves (afterDiv c k)

private theorem charged_zero (c : Nat) : charged c 0 = 0 := rfl

private theorem charged_succ (c k : Nat) :
    charged c (k + 1) = charged c k + if afterDiv c k ≤ 1 then 0 else rungMoves (afterDiv c k) := rfl

private theorem charged_shift (c k : Nat) :
    charged c (k + 1) = (if c ≤ 1 then 0 else rungMoves c) + charged (c / 2) k := by
  induction k with
  | zero =>
    simp [charged_succ, charged_zero, afterDiv_zero]
  | succ k ih =>
    rw [charged_succ c (k + 1), ih, afterDiv_shift, charged_succ, Nat.add_assoc]

private theorem charged_rung (c : Nat) :
    charged c (rungList c).length = halveMoves c := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    by_cases h : c ≤ 1
    · simp [rungList_le h, halveMoves_le h, charged_zero]
    · have hlt : c / 2 < c := Nat.div_lt_self (by omega) (by decide)
      rw [rungList_gt (by omega), halveMoves_gt (by omega), List.length_cons,
        charged_shift, if_neg h, ih _ hlt]

private theorem afterDiv_gt (c k : Nat) (hk : k < (rungList c).length) :
    1 < afterDiv c k := by
  induction c using Nat.strongRecOn generalizing k with
  | ind c ih =>
    by_cases h : c ≤ 1
    · simp [rungList_le h] at hk
    · cases k with
      | zero =>
        rw [afterDiv_zero]
        omega
      | succ k =>
        rw [rungList_gt (by omega), List.length_cons] at hk
        rw [afterDiv_shift]
        exact ih (c / 2) (Nat.div_lt_self (by omega) (by decide)) k (by omega)

private theorem afterDiv_len (c : Nat) : afterDiv c (rungList c).length ≤ 1 := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    by_cases h : c ≤ 1
    · simp [rungList_le h, afterDiv_zero, h]
    · rw [rungList_gt (by omega), List.length_cons, afterDiv_shift]
      exact ih _ (Nat.div_lt_self (by omega) (by decide))

private theorem rung_take_succ (c k : Nat) (hk : k < (rungList c).length) :
    (rungList c).take (k + 1) =
      (rungList c).take k ++ [rungColour (afterDiv c k)] := by
  induction c using Nat.strongRecOn generalizing k with
  | ind c ih =>
    by_cases h : c ≤ 1
    · simp [rungList_le h] at hk
    · rw [rungList_gt (by omega)]
      cases k with
      | zero =>
        simp [afterDiv_zero, rungColour]
      | succ k =>
        rw [rungList_gt (by omega), List.length_cons] at hk
        rw [List.take_succ_cons, List.take_succ_cons, afterDiv_shift]
        have hlt : c / 2 < c := Nat.div_lt_self (by omega) (by decide)
        rw [ih _ hlt k (by omega), ← List.cons_append]

/-! ### Painting the control row, and the spare pegs -/

def paint (row : List Nat) (i : Nat) : List Nat → List Nat
  | [] => row
  | c :: cs => paint (row.set i c) (i + 1) cs

private theorem paint_nil (row : List Nat) (i : Nat) : paint row i [] = row := rfl

private theorem get_idx {α : Type} {xs : List α} {i j : Nat} (h : i = j) (hi : i < xs.length) :
    xs[i] = xs[j]'(h ▸ hi) := by
  subst h
  rfl

private theorem paint_cons (row : List Nat) (i c : Nat) (cs : List Nat) :
    paint row i (c :: cs) = paint (row.set i c) (i + 1) cs := rfl

private theorem paint_length (row : List Nat) (i : Nat) (cols : List Nat) :
    (paint row i cols).length = row.length := by
  induction cols generalizing row i with
  | nil => rfl
  | cons c cs ih => rw [paint_cons, ih, List.length_set]

private theorem paint_lo (row : List Nat) (i : Nat) (cols : List Nat) (j : Nat)
    (hj : j < i) (hj' : j < row.length) :
    (paint row i cols)[j]'(by rw [paint_length]; exact hj') = row[j] := by
  induction cols generalizing row i with
  | nil => rfl
  | cons c cs ih =>
    simp only [paint_cons]
    have hne : i ≠ j := by omega
    have hj1 : j < i + 1 := by omega
    have hj2 : j < (row.set i c).length := by rw [List.length_set]; exact hj'
    rw [ih _ _ hj1 hj2, List.getElem_set, if_neg hne]

private theorem paint_hi (row : List Nat) (i : Nat) (cols : List Nat) (j : Nat)
    (hj : i + cols.length ≤ j) (hj' : j < row.length) :
    (paint row i cols)[j]'(by rw [paint_length]; exact hj') = row[j] := by
  induction cols generalizing row i with
  | nil => rfl
  | cons c cs ih =>
    simp only [paint_cons]
    have hj1 : i + 1 + cs.length ≤ j := by
      simp [List.length_cons] at hj
      omega
    have hne : i ≠ j := by omega
    have hj2 : j < (row.set i c).length := by rw [List.length_set]; exact hj'
    rw [ih _ _ hj1 hj2, List.getElem_set, if_neg hne]

private theorem paint_at (row : List Nat) (start : Nat) (cols : List Nat)
    (h : start + cols.length ≤ row.length) (k : Nat) (hk : k < cols.length) :
    (paint row start cols)[start + k]'(by rw [paint_length]; omega) = cols[k] := by
  induction cols generalizing row start k with
  | nil => cases hk
  | cons c cs ih =>
    simp only [paint_cons]
    by_cases hk0 : k = 0
    · subst hk0
      simp only [Nat.add_zero]
      have hlen : start < (row.set start c).length := by rw [List.length_set]; omega
      rw [paint_lo (row.set start c) (start + 1) cs start (by omega) hlen,
        List.getElem_set_self]
      simp
    · have hlenCs : (c :: cs).length = cs.length + 1 := by simp
      have hk' : k - 1 < cs.length := by omega
      have hrest : start + 1 + cs.length ≤ (row.set start c).length := by
        rw [List.length_set]
        omega
      have ih' := ih (row.set start c) (start + 1) hrest (k - 1) hk'
      have hcons : (c :: cs)[(k - 1) + 1]'(by omega) = cs[k - 1] := by
        simp [List.getElem_cons_succ]
      have hget : (c :: cs)[k] = cs[k - 1] := by
        have hidx : (k - 1) + 1 = k := by omega
        exact (get_idx hidx (by omega)).symm.trans hcons
      have hpi : start + 1 + (k - 1) < (paint (row.set start c) (start + 1) cs).length := by
        rw [paint_length, List.length_set]; omega
      have hidx : start + 1 + (k - 1) = start + k := by omega
      rw [← get_idx hidx hpi, ih', hget]

private theorem paint_snoc (row : List Nat) (start : Nat) (xs : List Nat) (c : Nat)
    (h : start + xs.length < row.length) :
    paint row start (xs ++ [c]) =
      (paint row start xs).set (start + xs.length) c := by
  induction xs generalizing row start with
  | nil => simp [paint]
  | cons x xs ih =>
    rw [show (x :: xs) ++ [c] = x :: (xs ++ [c]) from rfl, paint_cons, paint_cons]
    have h' : start + 1 + xs.length < (row.set start x).length := by
      rw [List.length_set]; simp at h; omega
    rw [ih _ _ h']
    simp [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def ones (n i : Nat) : List Nat :=
  List.replicate i 1 ++ List.replicate (n - i) 0

private theorem ones_zero (n : Nat) : ones n 0 = List.replicate n 0 := by
  simp [ones]

private theorem ones_get (n i j : Nat) (hi : i ≤ n) (hj : j < n) :
    (ones n i)[j]'(by simp [ones, List.length_append, List.length_replicate]; omega) =
      if j < i then 1 else 0 := by
  unfold ones
  by_cases hlt : j < i
  · have h1 : j < (List.replicate i 1).length := by simp [hlt]
    simp [List.getElem_append_left h1, List.getElem_replicate, hlt]
  · have h1 : (List.replicate i 1).length ≤ j := by simp; omega
    have h2 : j - i < (List.replicate (n - i) 0).length := by simp; omega
    simp [List.getElem_append_right h1, List.getElem_replicate, hlt]

private theorem ones_succ (n i : Nat) (hi : i < n) :
    (ones n i).set i 1 = ones n (i + 1) := by
  have hlen : (ones n i).length = n := by
    simp [ones, List.length_append, List.length_replicate]; omega
  have hlen' : (ones n (i + 1)).length = n := by
    simp [ones, List.length_append, List.length_replicate]; omega
  apply List.ext_getElem
  · rw [List.length_set, hlen, hlen']
  · intro j hj hj'
    rw [List.getElem_set]
    have hjn : j < n := by rw [List.length_set, hlen] at hj; exact hj
    by_cases hij : i = j
    · subst hij
      rw [ones_get n (i + 1) i (by omega) hi]
      simp
    · rw [ones_get n i j (by omega) hjn, ones_get n (i + 1) j (by omega) hjn]
      by_cases hlt : j < i
      · have hlt1 : j < i + 1 := by omega
        simp [hlt, hlt1]
      · have hnot : ¬ j < i + 1 := by omega
        simp [hij, hlt, hnot]

private theorem ones_spare (n : Nat) (hn : 0 < n) : ones n (n - 1) = sparePegs n := by
  have h1 : n - (n - 1) = 1 := by omega
  simp [ones, sparePegs, h1]

private theorem countHeld_spare :
    countHeld ((Array.mkArray 8 false).set ⟨6, by simp⟩ true) 7 = 1 := by
  decide

/-- The board `new_board` builds before it lays pegs. -/
def blankOf (t : Ecbs.Tier) (control script : Nat) : Ecbs.Board where
  sudo_5Board_1t := t
  sudo_5Board_4home := Array.mkArray 8 (#[] : Array Int)
  sudo_5Board_4held := Array.mkArray 8 false
  sudo_5Board_8bench_on := false
  sudo_5Board_8bench_to := -1
  sudo_5Board_5bench := (#[] : Array Int)
  sudo_5Board_4cost :=
    { sudo_5Costs_5moves := 0
      sudo_5Costs_6slides := 0
      sudo_5Costs_4ctrl := 0
      sudo_5Costs_5calls := 0
      sudo_5Costs_13stale_cleared := 0
      sudo_5Costs_14key_grid_moves := 0
      sudo_5Costs_12ladder_moves := 0
      sudo_5Costs_4peak := 0
      sudo_5Costs_11peak_strict := 0
      sudo_5Costs_14max_bench_hole := 0
      sudo_5Costs_15control_highest := -1
      sudo_5Costs_17script_marker_max := 0
      sudo_5Costs_9tally_max := 0
      sudo_5Costs_14moves_by_phase := Array.mkArray 8 0
      sudo_5Costs_13peak_by_phase := Array.mkArray 8 0
      sudo_5Costs_3ops := Array.mkArray 5 0 }
  sudo_5Board_5phase := 0
  sudo_5Board_8phase_m0 := 0
  sudo_5Board_8phase_pk := 0
  sudo_5Board_3row := Array.mkArray control 0
  sudo_5Board_10phase_hole := Int.ofNat script
  sudo_5Board_12calling_hole := Int.ofNat (script + 1)
  sudo_5Board_7ladder0 := Int.ofNat (script + 2)
  sudo_5Board_6nrungs := 0
  sudo_5Board_9park_hole := -1
  sudo_5Board_6tally0 := -1
  sudo_5Board_6marker := -1
  sudo_5Board_11parked_from := -1
  sudo_5Board_9tally_len := 0
  sudo_5Board_9marker_on := false
  sudo_5Board_8rung_idx := 0
  sudo_5Board_6ladder := (#[] : Array Int)
  sudo_5Board_3log := (#[] : Array Ecbs.Call)

private theorem blank_home6 (t : Ecbs.Tier) (c s : Nat) :
    6 < (blankOf t c s).sudo_5Board_4home.size := by
  simp [blankOf, Array.size_mkArray]

private theorem blank_held6 (t : Ecbs.Tier) (c s : Nat) :
    6 < (blankOf t c s).sudo_5Board_4held.size := by
  simp [blankOf, Array.size_mkArray]

private theorem blank_held7 (t : Ecbs.Tier) (c s : Nat) :
    7 ≤ (blankOf t c s).sudo_5Board_4held.size := by
  simp [blankOf, Array.size_mkArray]

/-- Spare filled, peak raised to the one held home, `n − 1` moves. -/
def placed (t : Spec.Tier) : Ecbs.Board :=
  let b0 := blankOf (embTier t) t.control t.script
  { b0 with
    sudo_5Board_4home := b0.sudo_5Board_4home.set ⟨6, blank_home6 _ _ _⟩ (embed (sparePegs t.n))
    sudo_5Board_4held := b0.sudo_5Board_4held.set ⟨6, blank_held6 _ _ _⟩ true
    sudo_5Board_4cost := { b0.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (t.n - 1)
      sudo_5Costs_4peak := 1 } }

/-- During the halving: `laid` rungs painted from `ladder0`, `moves` charged so far. -/
def midBoard (t : Spec.Tier) (laid : List Nat) (moves : Nat) : Ecbs.Board :=
  let b1 := placed t
  { b1 with
    sudo_5Board_3row := embed (paint (List.replicate t.control 0) (t.script + 2) laid)
    sudo_5Board_6nrungs := Int.ofNat laid.length
    sudo_5Board_4cost := { b1.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat moves
      sudo_5Costs_4ctrl := Int.ofNat laid.length
      sudo_5Costs_15control_highest :=
        if laid.length = 0 then -1 else Int.ofNat (t.script + 2 + laid.length - 1) } }

private theorem embed_set1 (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    (embed xs).set ⟨i, by rw [size_embed]; exact hi⟩ (1 : Int) = embed (xs.set i 1) := by
  rw [show (1 : Int) = Int.ofNat 1 from rfl]
  exact embed_set xs i 1 hi

def spareStep (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) Ecbs.Board) :=
  let i := σ.1
  let pegs := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, pegs))
    else
      match ← (do
        let pegs ← SudoRt.putL pegs i (1 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) pegs) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) Ecbs.Board)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs))

private theorem spareStep_hit (n i toN : Nat) (hi : i ≤ toN) (hn : i < n)
    (hfi : FitsLen (i + 1)) :
    spareStep (Int.ofNat toN) (Int.ofNat i, embed (ones n i)) =
      (if i = toN then
          .ok (.brk (Int.ofNat i, embed (ones n (i + 1))))
        else
          .ok (.cont (Int.ofNat (i + 1), embed (ones n (i + 1))))) := by
  unfold spareStep
  dsimp only
  have hngt : ¬ (Int.ofNat i > Int.ofNat toN) := not_gt_cast hi
  rw [if_neg hngt]
  have hsz : i < (embed (ones n i)).size := by
    rw [size_embed, ones]
    simp [List.length_append, List.length_replicate]
    omega
  rw [putL_ofNat _ i (1 : Int) hsz, ok_bind, embed_set1 _ _ (by
    rw [ones]; simp [List.length_append, List.length_replicate]; omega), ones_succ n i hn]
  simp only [pure_eq_ok, ok_bind]
  exact asc_tail toN i hfi _

/-- `for i = 0 to n - 2` fills `n − 1` ones. `n ≥ 2`. -/
theorem spare_loop_refines {β} (n : Nat)
    (after : Int × Array Int → Except SudoRt.Trap β)
    (onRet : Ecbs.Board → Except SudoRt.Trap β)
    (hn : 2 ≤ n) (hf : FitsLen n) :
    SudoRt.runLoopOn (ρ := Ecbs.Board)
        (Int.ofNat 0, embed (List.replicate n 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat (n - 2)))
        (spareStep (Int.ofNat (n - 2))) after onRet =
      after (Int.ofNat (n - 2), embed (sparePegs n)) := by
  have h0 : embed (List.replicate n 0) = embed (ones n 0) := by rw [ones_zero]
  rw [h0]
  refine asc_goal (fromN := 0) (toN := n - 2)
    (fun i (a : Array Int) => a = embed (ones n i))
    (Nat.zero_le _) rfl ?_ ?_
  · intro i a _ hi ha
    have hin : i < n := by omega
    have hfi : FitsLen (i + 1) := FitsLen.of_le hf (by omega)
    rw [ha]
    refine ⟨embed (ones n (i + 1)), rfl, spareStep_hit n i (n - 2) hi hin hfi⟩
  · intro a ha
    have hn1 : n - 2 + 1 = n - 1 := by omega
    rw [ha, hn1, ones_spare n (by omega)]

private theorem paint_zero_next (control start : Nat) (cols : List Nat)
    (h : start + cols.length < control) :
    (paint (List.replicate control 0) start cols)[start + cols.length]'(by
      rw [paint_length, List.length_replicate]; exact h) = 0 := by
  rw [paint_hi _ _ _ _ (Nat.le_refl _) (by rw [List.length_replicate]; exact h)]
  simp [List.getElem_replicate]

private theorem fits_script_add (t : Spec.Tier) (h : BoardOk t) (k : Nat) (hk : k ≤ 2) :
    FitsLen (t.script + k) :=
  FitsLen.of_le (fits_of h.fits_script) (by omega)

private theorem fits_board (t : Spec.Tier) (h : BoardOk t) (m : Nat)
    (hm : m ≤ 4 * t.n + 8) : FitsLen m :=
  FitsLen.of_le (fits_of h.fits_n) hm

/-- One rung on the mid-halving board. The new colour is painted at the next hole,
    `nrungs` and `ctrl` grow by one, and the move counter is left alone. -/
theorem lay_rung_mid (t : Spec.Tier) (laid : List Nat) (moves colour : Nat) (h : BoardOk t)
    (hroom : t.script + 2 + laid.length < t.control) :
    Ecbs.lay_rung (midBoard t laid moves) (Int.ofNat colour) =
      .ok (midBoard t (laid ++ [colour]) moves) := by
  have hfit : FitsLen (t.script + 2 + laid.length) := by
    have hle : t.script + 2 + laid.length ≤ t.control := by omega
    exact FitsLen.of_le (fits_of h.fits_control) (by omega)
  have hfit1 : FitsLen (laid.length + 1) := by
    have : laid.length + 1 ≤ t.control + 1 := by omega
    exact FitsLen.of_le (fits_of h.fits_control) this
  unfold Ecbs.lay_rung Ecbs.set_control
  simp only [midBoard, placed, blankOf, ok_bind]
  rw [addI_ofNat (t.script + 2) laid.length hfit, ok_bind]
  have hlt : Int.ofNat (t.script + 2 + laid.length) < (embTier t).sudo_4Tier_7control := by
    rw [show (embTier t).sudo_4Tier_7control = Int.ofNat t.control from rfl]
    exact (ofNat_lt_iff _ _).mpr hroom
  rw [decide_eq_true hlt, sudoAssert_true, ok_bind]
  have hidx : t.script + 2 + laid.length <
      (paint (List.replicate t.control 0) (t.script + 2) laid).length := by
    rw [paint_length, List.length_replicate]; exact hroom
  rw [atL_embed _ _ hidx, paint_zero_next _ _ _ hroom, ok_bind,
    sudoAssertEq_int (show Int.ofNat 0 = (0 : Int) from rfl), ok_bind]
  have hnonneg : decide (Int.ofNat (t.script + 2 + laid.length) ≥ (0 : Int)) = true := by
    rw [decide_eq_true_eq]
    exact Int.ofNat_zero_le _
  simp only [hnonneg, decide_eq_true hlt, Bool.and_true, ite_true, ok_bind, sudoAssert_true]
  have hsz : t.script + 2 + laid.length < (embed (paint (List.replicate t.control 0)
      (t.script + 2) laid)).size := by
    rw [size_embed]; exact hidx
  rw [putL_ofNat _ _ (Int.ofNat colour) hsz, ok_bind]
  rw [pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  have hgt : decide (Int.ofNat (t.script + 2 + laid.length) >
      (if laid.length = 0 then (-1 : Int) else Int.ofNat (t.script + 2 + laid.length - 1))) = true := by
    rw [decide_eq_true_eq]
    by_cases hz : laid.length = 0
    · simp [hz]; omega
    · simp [hz, ofNat_lt_iff]; omega
  rw [hgt, if_pos rfl, pure_eq_ok, ok_bind]
  simp only [addI_ofNat_one laid.length hfit1, ok_bind]
  have hpaint := paint_snoc (List.replicate t.control 0) (t.script + 2) laid colour
    (by rw [List.length_replicate]; exact hroom)
  have hset := embed_set (paint (List.replicate t.control 0) (t.script + 2) laid)
    (t.script + 2 + laid.length) colour hidx
  simp only [midBoard, placed, blankOf, List.length_append, List.length_singleton,
    Nat.zero_ne_add_one, if_false, hpaint, ← hset]
  rfl

private theorem mid_moves (t : Spec.Tier) (laid : List Nat) (m₁ m₂ : Nat) :
    { midBoard t laid m₁ with sudo_5Board_4cost :=
        { (midBoard t laid m₁).sudo_5Board_4cost with
          sudo_5Costs_5moves := Int.ofNat m₂ } } =
      midBoard t laid m₂ := by
  simp [midBoard, placed, blankOf]

/-- The halving body. `c ≤ 1` breaks; otherwise one `lay_rung` and `c := c / 2`. -/
def halveStep (toV : Int) (σ : Int × (Ecbs.Board × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Ecbs.Board × Int)) Ecbs.Board) :=
  let step := σ.1
  let b := σ.2.1
  let c := σ.2.2
  do
    if step > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (step, (b, c)))
    else
      match ← (do
        if decide (c ≤ (1 : Int)) then
          pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (b, c))
        else
          do
            let left ← SudoRt.modI c (2 : Int)
            if SudoRt.SEq.beq left (1 : Int) then
              do
                let b ← Ecbs.lay_rung b (2 : Int)
                let m ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves left
                let q ← SudoRt.divI c (2 : Int)
                let m ← SudoRt.addI m q
                let b := { b with sudo_5Board_4cost :=
                  { b.sudo_5Board_4cost with sudo_5Costs_5moves := m } }
                let c ← SudoRt.divI c (2 : Int)
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (b, c))
            else
              do
                let b ← Ecbs.lay_rung b (1 : Int)
                let m ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves left
                let q ← SudoRt.divI c (2 : Int)
                let m ← SudoRt.addI m q
                let b := { b with sudo_5Board_4cost :=
                  { b.sudo_5Board_4cost with sudo_5Costs_5moves := m } }
                let c ← SudoRt.divI c (2 : Int)
                pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (b, c)) :
          Except SudoRt.Trap (SudoRt.Flow (Ecbs.Board × Int) Ecbs.Board)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (step, fs))
      | .cont fs => do
          if step == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (step, fs))
          else do
            let step' ← SudoRt.addI step (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (step', fs))

private theorem halve_lay (t : Spec.Tier) (n k moves : Nat) (h : BoardOk t)
    (hk : k < (rungList (n - 1)).length)
    (hroom : t.script + 2 + k < t.control)
    (hfit : FitsLen (moves + afterDiv (n - 1) k)) :
    let c := afterDiv (n - 1) k
    let laid := (rungList (n - 1)).take k
    let colour := rungColour c
    (Ecbs.lay_rung (midBoard t laid moves) (Int.ofNat colour) >>= fun b =>
      (do
        let m ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (Int.ofNat (c % 2))
        let q ← SudoRt.divI (Int.ofNat c) (2 : Int)
        let m ← SudoRt.addI m q
        let b := { b with sudo_5Board_4cost :=
          { b.sudo_5Board_4cost with sudo_5Costs_5moves := m } }
        let c' ← SudoRt.divI (Int.ofNat c) (2 : Int)
        pure (b, c'))) =
      .ok (midBoard t ((rungList (n - 1)).take (k + 1))
          (moves + rungMoves c), Int.ofNat (c / 2)) := by
  intro c laid colour
  have htake : laid.length = k := by
    dsimp [laid]
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hroom' : t.script + 2 + laid.length < t.control := by rw [htake]; exact hroom
  have hc2 : c % 2 ≤ c := Nat.mod_le _ _
  have hdiv : c / 2 ≤ c := Nat.div_le_self _ _
  have h1 : FitsLen (moves + c % 2) := FitsLen.of_le hfit (by omega)
  have h2 : FitsLen (moves + c % 2 + c / 2) := FitsLen.of_le hfit (by
    have : c % 2 + c / 2 ≤ c := by
      have := Nat.div_add_mod c 2
      omega
    omega)
  rw [lay_rung_mid t laid moves colour h hroom', ok_bind]
  have hm : (midBoard t (laid ++ [colour]) moves).sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat moves := by simp [midBoard]
  rw [hm, addI_ofNat moves (c % 2) h1, ok_bind]
  rw [show (2 : Int) = Int.ofNat 2 from rfl, divI_ofNat c (by decide)]
  simp only [ok_bind]
  rw [addI_ofNat (moves + c % 2) (c / 2) h2, ok_bind]
  have hlist : laid ++ [colour] = (rungList (n - 1)).take (k + 1) := by
    dsimp [laid]
    rw [rung_take_succ (n - 1) k hk]
  have hmov : moves + c % 2 + c / 2 = moves + rungMoves c := by
    unfold rungMoves; omega
  simp [midBoard, placed, blankOf, pure_eq_ok, hlist, hmov, List.length_append,
    List.length_singleton]

private theorem afterDiv_le_base (c k : Nat) : afterDiv c k ≤ c := by
  induction k with
  | zero => simp [afterDiv_zero]
  | succ k ih =>
    rw [afterDiv_succ]
    exact Nat.le_trans (Nat.div_le_self _ _) ih

private theorem charged_le (c k : Nat) (hk : k ≤ (rungList c).length) :
    charged c k ≤ halveMoves c := by
  induction c using Nat.strongRecOn generalizing k with
  | ind c ih =>
    by_cases h : c ≤ 1
    · have hk0 : k = 0 := by simp [rungList_le h] at hk; omega
      simp [hk0, charged_zero, halveMoves_le h]
    · cases k with
      | zero =>
        rw [charged_zero]
        exact Nat.zero_le _
      | succ k =>
        rw [rungList_gt (by omega), List.length_cons] at hk
        rw [charged_shift, if_neg h, halveMoves_gt (by omega)]
        exact Nat.add_le_add_left
          (ih (c / 2) (Nat.div_lt_self (by omega) (by decide)) k (by omega)) _

private theorem charged_step (n i : Nat) (hi : 0 < i)
    (hgt : 1 < afterDiv (n - 1) (i - 1)) :
    (n - 1) + charged (n - 1) (i - 1) + afterDiv (n - 1) (i - 1) % 2 +
        afterDiv (n - 1) (i - 1) / 2 =
      (n - 1) + charged (n - 1) i := by
  have hch : charged (n - 1) i =
      charged (n - 1) (i - 1) + rungMoves (afterDiv (n - 1) (i - 1)) := by
    have hi1 : i = (i - 1) + 1 := by omega
    have hc := congrArg (charged (n - 1)) hi1
    rw [hc, charged_succ]
    have hnot : ¬ afterDiv (n - 1) (i - 1) ≤ 1 := Nat.not_le_of_gt hgt
    simp only [hnot, ite_false]
  rw [hch]
  unfold rungMoves
  omega

/-- The halving loop's continue tail, once the rung has been laid. `i ≠ n`. -/
private theorem halve_tail (n i : Nat) (s : Ecbs.Board × Int)
    (hne : i ≠ n) (hfi : FitsLen (i + 1)) :
    (if ((i : Int) == (n : Int)) = true then
        pure (SudoRt.Flow.brk (ρ := Ecbs.Board) ((i : Int), s))
      else do
        let step' ← SudoRt.addI (i : Int) (1 : Int)
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (step', s))) =
      Except.ok (SudoRt.Flow.cont (ρ := Ecbs.Board) (((i + 1 : Nat) : Int), s)) := by
  have hneI : ¬ (((i : Int) == (n : Int)) = true) := by
    intro hb
    have heq : (i : Int) = (n : Int) := (beq_int_iff _ _).mp hb
    exact hne (by omega)
  rw [if_neg hneI]
  rw [← ofNat_eq_natCast i, addI_ofNat_one i hfi, ok_bind, pure_eq_ok]
  rfl

/-- Halving from `n - 1`, breaking when the peg count drops to one. The board is `midBoard`
    with the first `k` rungs of `Spec.rungList`. -/
theorem halve_loop_refines {β} (t : Spec.Tier) (h : BoardOk t)
    (after : Int × (Ecbs.Board × Int) → Except SudoRt.Trap β)
    (onRet : Ecbs.Board → Except SudoRt.Trap β) :
    let n := t.n
    let rungs := rungList (n - 1)
    SudoRt.runLoopOn (ρ := Ecbs.Board)
        (Int.ofNat 1, (midBoard t [] (n - 1), Int.ofNat (n - 1)))
        (fuelRange (Int.ofNat 1) (Int.ofNat n))
        (halveStep (Int.ofNat n)) after onRet =
      after (Int.ofNat (rungs.length + 1),
        (midBoard t rungs ((n - 1) + halveMoves (n - 1)),
          Int.ofNat (afterDiv (n - 1) rungs.length))) := by
  intro n rungs
  have hn : 0 < n := h.n_pos
  refine asc_brk_goal
    (fun i (st : Ecbs.Board × Int) =>
      let k := i - 1
      k ≤ rungs.length ∧
      st.1 = midBoard t (rungs.take k) ((n - 1) + charged (n - 1) k) ∧
      st.2 = Int.ofNat (afterDiv (n - 1) k))
    (fun i (st : Ecbs.Board × Int) =>
      let k := i - 1
      k = rungs.length ∧
      st.1 = midBoard t rungs ((n - 1) + halveMoves (n - 1)) ∧
      st.2 = Int.ofNat (afterDiv (n - 1) rungs.length))
    (by omega : 1 ≤ n)
    (by
      refine ⟨by simp [rungs], ?_, ?_⟩
      · simp [midBoard, charged_zero, List.take_zero]
      · simp [afterDiv_zero])
    ?_ ?_
  · intro i st hi htop hI
    obtain ⟨hklen, hb, hc⟩ := hI
    have hk : i - 1 ≤ rungs.length := hklen
    by_cases hdone : i - 1 = rungs.length
    · refine Or.inr ⟨st, ?_, ?_⟩
      · refine ⟨hdone, ?_, ?_⟩
        · rw [hb, hdone, List.take_length, charged_rung]
        · rw [hc, hdone]
      · unfold halveStep
        dsimp
        have hle : afterDiv (n - 1) rungs.length ≤ 1 := afterDiv_len (n - 1)
        have hdec : decide (Int.ofNat (afterDiv (n - 1) rungs.length) ≤ (1 : Int)) = true := by
          rw [decide_eq_true_eq, show (1 : Int) = Int.ofNat 1 from rfl, ofNat_le_iff]
          exact hle
        rw [hc, hdone, hdec]
        split
        · rename_i hgt
          exact absurd hgt (not_gt_cast htop)
        · simp only [ite_true, pure_eq_ok, ok_bind]
          cases st with
          | mk b c =>
            have hc' : c = Int.ofNat (afterDiv (n - 1) rungs.length) := by
              simpa [hdone] using hc
            simp [hc']
    · have hklt : i - 1 < rungs.length := by omega
      have hgt1 : 1 < afterDiv (n - 1) (i - 1) := afterDiv_gt (n - 1) (i - 1) hklt
      have hroom : t.script + 2 + (i - 1) < t.control := by
        have hlen := h.ladder
        have hk' : i - 1 < (rungList (t.n - 1)).length := by simpa [rungs, n] using hklt
        omega
      have hfit : FitsLen ((n - 1) + charged (n - 1) (i - 1) + afterDiv (n - 1) (i - 1)) := by
        apply fits_board t h
        have hch := charged_le (n - 1) (i - 1) (Nat.le_of_lt hklt)
        have hhm := halveMoves_le_self (n - 1)
        have had := afterDiv_le_base (n - 1) (i - 1)
        omega
      have hine : i ≠ n := by
        have hlen := rungList_length_le (n - 1)
        have hk' : i - 1 < (rungList (n - 1)).length := by simpa [rungs] using hklt
        omega
      have hfi : FitsLen (i + 1) := fits_board t h _ (by omega)
      refine Or.inl ⟨(midBoard t (rungs.take i) ((n - 1) + charged (n - 1) i),
          Int.ofNat (afterDiv (n - 1) i)), ?_, ?_⟩
      · refine ⟨by omega, rfl, rfl⟩
      unfold halveStep
      dsimp
      rw [hc, hb]
      split
      · rename_i hgt
        exact absurd hgt (not_gt_cast htop)
      have hdec : decide (Int.ofNat (afterDiv (n - 1) (i - 1)) ≤ (1 : Int)) = false := by
        rw [decide_eq_false_iff_not, show (1 : Int) = Int.ofNat 1 from rfl, ofNat_le_iff]
        exact Nat.not_le_of_gt hgt1
      simp only [hdec, Bool.false_eq_true, if_false, ok_bind]
      rw [show (2 : Int) = Int.ofNat 2 from rfl, modI_ofNat _ (by decide), ok_bind]
      have hcolour : rungColour (afterDiv (n - 1) (i - 1)) =
          if afterDiv (n - 1) (i - 1) % 2 = 1 then 2 else 1 := by
        unfold rungColour; rfl
      by_cases hbit : afterDiv (n - 1) (i - 1) % 2 = 1
      · have hbeq : SudoRt.SEq.beq (Int.ofNat (afterDiv (n - 1) (i - 1) % 2)) (1 : Int) = true := by
          rw [show (1 : Int) = Int.ofNat 1 from rfl, sEq_ofNat, hbit]
          exact decide_eq_true rfl
        simp only [hbeq, ite_true]
        have hc2 : rungColour (afterDiv (n - 1) (i - 1)) = 2 := by
          rw [hcolour, if_pos hbit]
        rw [lay_rung_mid t (rungs.take (i - 1)) ((n - 1) + charged (n - 1) (i - 1)) 2 h
          (by simpa [rungs, List.length_take, Nat.min_eq_left (Nat.le_of_lt hklt)] using hroom),
          ok_bind]
        have hm : (midBoard t (rungs.take (i - 1) ++ [2])
            ((n - 1) + charged (n - 1) (i - 1))).sudo_5Board_4cost.sudo_5Costs_5moves =
            Int.ofNat ((n - 1) + charged (n - 1) (i - 1)) := by simp [midBoard]
        have h1 : FitsLen ((n - 1) + charged (n - 1) (i - 1) +
            afterDiv (n - 1) (i - 1) % 2) := FitsLen.of_le hfit (by
          have := Nat.mod_le (afterDiv (n - 1) (i - 1)) 2; omega)
        have h2 : FitsLen ((n - 1) + charged (n - 1) (i - 1) +
            afterDiv (n - 1) (i - 1) % 2 + afterDiv (n - 1) (i - 1) / 2) :=
          FitsLen.of_le hfit (by
            have hsum := Nat.div_add_mod (afterDiv (n - 1) (i - 1)) 2
            omega)
        rw [hm,
          addI_ofNat ((n - 1) + charged (n - 1) (i - 1)) (afterDiv (n - 1) (i - 1) % 2) h1,
          ok_bind]
        rw [divI_ofNat (afterDiv (n - 1) (i - 1)) (by decide)]
        simp only [ok_bind]
        rw [addI_ofNat ((n - 1) + charged (n - 1) (i - 1) + afterDiv (n - 1) (i - 1) % 2)
            (afterDiv (n - 1) (i - 1) / 2) h2]
        simp only [ok_bind]
        rw [pure_eq_ok, ok_bind]
        have hmovN := charged_step n i (by omega) hgt1
        have hdivN : afterDiv (n - 1) (i - 1) / 2 = afterDiv (n - 1) i := by
          have hidx : afterDiv (n - 1) ((i - 1) + 1) = afterDiv (n - 1) i := by
            apply congrArg
            omega
          rw [← hidx, afterDiv_succ]
        have hlist : rungs.take (i - 1) ++ [2] = rungs.take i := by
          have hi1 : (i - 1) + 1 = i := by omega
          rw [← hi1, rung_take_succ (n - 1) (i - 1) (by simpa [rungs] using hklt), hc2]
          simp [rungs]
        simp only [mid_moves]
        rw [hlist, hmovN, hdivN]
        exact halve_tail n i
          (midBoard t (rungs.take i) ((n - 1) + charged (n - 1) i),
            Int.ofNat (afterDiv (n - 1) i))
          hine hfi
      · have hbeq : SudoRt.SEq.beq (Int.ofNat (afterDiv (n - 1) (i - 1) % 2)) (1 : Int) = false := by
          rw [show (1 : Int) = Int.ofNat 1 from rfl, sEq_ofNat]
          exact decide_eq_false hbit
        simp only [hbeq, Bool.false_eq_true, if_false]
        rw [show (1 : Int) = Int.ofNat 1 from rfl]
        rw [lay_rung_mid t (rungs.take (i - 1)) ((n - 1) + charged (n - 1) (i - 1)) 1 h
          (by simpa [rungs, List.length_take, Nat.min_eq_left (Nat.le_of_lt hklt)] using hroom),
          ok_bind]
        have hm : (midBoard t (rungs.take (i - 1) ++ [1])
            ((n - 1) + charged (n - 1) (i - 1))).sudo_5Board_4cost.sudo_5Costs_5moves =
            Int.ofNat ((n - 1) + charged (n - 1) (i - 1)) := by simp [midBoard]
        have h1 : FitsLen ((n - 1) + charged (n - 1) (i - 1) +
            afterDiv (n - 1) (i - 1) % 2) := FitsLen.of_le hfit (by
          have := Nat.mod_le (afterDiv (n - 1) (i - 1)) 2; omega)
        have h2 : FitsLen ((n - 1) + charged (n - 1) (i - 1) +
            afterDiv (n - 1) (i - 1) % 2 + afterDiv (n - 1) (i - 1) / 2) :=
          FitsLen.of_le hfit (by
            have hsum := Nat.div_add_mod (afterDiv (n - 1) (i - 1)) 2
            omega)
        rw [hm,
          addI_ofNat ((n - 1) + charged (n - 1) (i - 1)) (afterDiv (n - 1) (i - 1) % 2) h1,
          ok_bind]
        rw [divI_ofNat (afterDiv (n - 1) (i - 1)) (by decide)]
        simp only [ok_bind]
        rw [addI_ofNat ((n - 1) + charged (n - 1) (i - 1) + afterDiv (n - 1) (i - 1) % 2)
            (afterDiv (n - 1) (i - 1) / 2) h2]
        simp only [ok_bind]
        rw [pure_eq_ok, ok_bind]
        have hmovN := charged_step n i (by omega) hgt1
        have hdivN : afterDiv (n - 1) (i - 1) / 2 = afterDiv (n - 1) i := by
          have hidx : afterDiv (n - 1) ((i - 1) + 1) = afterDiv (n - 1) i := by
            apply congrArg
            omega
          rw [← hidx, afterDiv_succ]
        have hc1 : rungColour (afterDiv (n - 1) (i - 1)) = 1 := by
          rw [hcolour, if_neg hbit]
        have hlist : rungs.take (i - 1) ++ [1] = rungs.take i := by
          have hi1 : (i - 1) + 1 = i := by omega
          rw [← hi1, rung_take_succ (n - 1) (i - 1) hklt, hc1]
          simp [rungs]
        simp only [mid_moves]
        rw [hlist, hmovN, hdivN]
        exact halve_tail n i
          (midBoard t (rungs.take i) ((n - 1) + charged (n - 1) i),
            Int.ofNat (afterDiv (n - 1) i))
          hine hfi
  · intro j st hj1 hj2 hs
    rcases hs with hfull | hdone
    · have hbad : n ≤ rungs.length := hfull.1
      have hlen := rungList_length_le (n - 1)
      simp [rungs] at hbad hlen
      omega
    · obtain ⟨hlen, hb, hc⟩ := hdone
      have hj : j = rungs.length + 1 := by omega
      have hst : st =
          (midBoard t rungs ((n - 1) + halveMoves (n - 1)),
            Int.ofNat (afterDiv (n - 1) rungs.length)) := Prod.ext hb hc
      simp [hj, hst]

/-! ### From the fresh board to the ladder -/

private theorem pegCount_spare (n : Nat) : pegCount (sparePegs n) = n - 1 := by
  simpa [pegCount] using nnz_sparePegs n

private theorem placed_eq (t : Spec.Tier) :
    placeBoard (blankOf (embTier t) t.control t.script) 6
      (blank_home6 (embTier t) t.control t.script)
      (blank_held6 (embTier t) t.control t.script)
      (sparePegs t.n) 0 0 = placed t := by
  have hpeg : pegCount (sparePegs t.n) = t.n - 1 := pegCount_spare _
  have hocc : countHeld
      ((blankOf (embTier t) t.control t.script).sudo_5Board_4held.set
        ⟨6, blank_held6 _ _ _⟩ true) 7 = 1 := by
    simpa [blankOf] using countHeld_spare
  unfold placeBoard
  simp only [hpeg, Nat.zero_add, hocc]
  have hlt : (0 : Nat) < 1 := by decide
  simp only [hlt, ite_true]
  unfold placed
  rfl

/-- Halving starts from the spare just put down: no rungs yet, `n − 1` moves. -/
private theorem mid_init (t : Spec.Tier) :
    midBoard t [] (t.n - 1) = placed t := by
  simp [midBoard, paint_nil, embed_replicate_zero, placed, blankOf]

private theorem held6_mid (t : Spec.Tier) (laid : List Nat) (moves : Nat) :
    6 < (midBoard t laid moves).sudo_5Board_4held.size := by
  simp [midBoard, placed, blankOf, Array.size_mkArray]

private theorem home6_mid (t : Spec.Tier) (laid : List Nat) (moves : Nat) :
    6 < (midBoard t laid moves).sudo_5Board_4home.size := by
  simp [midBoard, placed, blankOf, Array.size_mkArray]

/-- `clear` of the spare after the ladder is painted. `bench_on` is false, so this is the
    home branch: charge the `n − 1` whites again and empty the spare. -/
private theorem clear_spare (t : Spec.Tier) (h : BoardOk t) (laid : List Nat) (moves : Nat)
    (hfit : FitsLen (moves + (t.n - 1))) :
    Ecbs.clear (midBoard t laid moves) ((6 : Nat) : Int) =
      .ok (let b := midBoard t laid moves
        { b with
          sudo_5Board_4home := b.sudo_5Board_4home.set ⟨6, home6_mid t laid moves⟩ (#[] : Array Int)
          sudo_5Board_4held := b.sudo_5Board_4held.set ⟨6, held6_mid t laid moves⟩ false
          sudo_5Board_4cost := { b.sudo_5Board_4cost with
            sudo_5Costs_5moves := Int.ofNat (moves + (t.n - 1)) } }) := by
  unfold Ecbs.clear
  simp only [midBoard, placed, blankOf]
  simp only [pure_eq_ok, ok_bind, Bool.false_eq_true, if_false]
  have hheld : ((Array.mkArray 8 false).set ⟨6, by simp [Array.size_mkArray]⟩ true)[6]'(by
      simp [Array.size_set, Array.size_mkArray]) = true := by
    simp [Array.getElem_set, Array.getElem_mkArray]
  rw [show ((6 : Nat) : Int) = Int.ofNat 6 from rfl]
  rw [atL_ofNat _ 6 (by simp [Array.size_set, Array.size_mkArray]), hheld, ok_bind,
    sudoAssert_true, ok_bind]
  rw [atL_ofNat _ 6 (by simp [Array.size_mkArray]), ok_bind]
  have hhome : ((Array.mkArray 8 (#[] : Array Int)).set ⟨6, by simp [Array.size_mkArray]⟩
      (embed (sparePegs t.n)))[6]'(by simp [Array.size_set, Array.size_mkArray]) =
      embed (sparePegs t.n) := by
    simp [Array.getElem_set]
  rw [hhome]
  have hfs : FitsLen (embed (sparePegs t.n)).size := by
    rw [size_embed, sparePegs_length h.n_pos]
    exact fits_board t h t.n (by omega)
  rw [npeg_refines (embed (sparePegs t.n)) hfs]
  have hnnz : nnz (embed (sparePegs t.n)).toList = t.n - 1 := by
    rw [toList_embed, nnz_embed]
    simpa [pegCount] using pegCount_spare t.n
  rw [hnnz, ok_bind]
  rw [addI_ofNat moves (t.n - 1) hfit, ok_bind]
  rw [putL_ofNat _ 6 false (by simp [Array.size_set, Array.size_mkArray]), ok_bind]
  rw [putL_ofNat _ 6 (#[] : Array Int) (by simp [Array.size_mkArray]), ok_bind]

/-- Indices from `hi` downward, `k` of them. `climb_holes` builds this list. -/
def downFrom (hi : Nat) : Nat → List Nat
  | 0 => []
  | k + 1 => hi :: downFrom (hi - 1) k

private theorem downFrom_zero (hi : Nat) : downFrom hi 0 = [] := rfl

private theorem downFrom_succ (hi k : Nat) : downFrom hi (k + 1) = hi :: downFrom (hi - 1) k := rfl

private theorem downFrom_length (hi k : Nat) : (downFrom hi k).length = k := by
  induction k generalizing hi with
  | zero => rfl
  | succ k ih => simp [downFrom, ih]

private theorem downFrom_snoc (hi k : Nat) :
    downFrom hi (k + 1) = downFrom hi k ++ [hi - k] := by
  induction k generalizing hi with
  | zero => simp [downFrom]
  | succ k ih =>
    rw [downFrom_succ, ih (hi - 1), downFrom_succ]
    have hsub : (hi - 1) - k = hi - (k + 1) := by omega
    simp [hsub, List.cons_append]

/-- One descending step of `climb_holes`. -/
def climbStep (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  let i := σ.1
  let holes := σ.2
  do
    if i < toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (i, holes))
    else
      match ← (do
        let holes := (SudoRt.appendL holes i).1
        pure (SudoRt.Flow.cont (ρ := Array Int) holes) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
          else do
            let i' ← SudoRt.subI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

private theorem climb_at (start len i : Nat) (holes : List Nat)
    (hi : i ≤ start + len - 1) (hpos : 0 < i) (hfi : FitsLen i)
    (hh : holes = downFrom (start + len - 1) (start + len - 1 - i))
    (hto : start ≤ i) :
    climbStep (Int.ofNat start) (Int.ofNat i, embed holes) =
      if i = start then
        .ok (.brk (Int.ofNat i, embed (downFrom (start + len - 1) (start + len - i))))
      else
        .ok (.cont (Int.ofNat (i - 1), embed (downFrom (start + len - 1) (start + len - i)))) := by
  unfold climbStep
  dsimp only
  have hlt : ¬ (Int.ofNat i < Int.ofNat start) := by
    rw [ofNat_lt_iff]; omega
  rw [if_neg hlt]
  have happ : ((embed holes).push (Int.ofNat i), ()).1 = embed (holes ++ [i]) := by
    simp
    apply Array.ext'
    simp [embed, toList_push]
  rw [appendL_spec, happ, hh, pure_eq_ok, ok_bind]
  have hnext : downFrom (start + len - 1) (start + len - 1 - i) ++ [i] =
      downFrom (start + len - 1) (start + len - i) := by
    have hk : (start + len - 1) - (start + len - 1 - i) = i := by omega
    conv =>
      lhs
      arg 2
      rw [← hk]
    have happ := downFrom_snoc (start + len - 1) (start + len - 1 - i)
    rw [← happ]
    have hcount : start + len - 1 - i + 1 = start + len - i := by omega
    rw [hcount]
  rw [hnext]
  by_cases heq : i = start
  · simp [heq, beq_int_iff, pure_eq_ok]
  · have hneI : ¬ ((Int.ofNat i == Int.ofNat start) = true) := by
      intro hb
      exact heq (Int.ofNat.inj ((beq_int_iff _ _).mp hb))
    simp only [hneI, Bool.false_eq_true, if_false, heq]
    rw [subI_ofNat_one i hpos hfi, ok_bind, pure_eq_ok]

private theorem climb_loop {β} (start len : Nat)
    (after : Int × Array Int → Except SudoRt.Trap β)
    (onRet : Array Int → Except SudoRt.Trap β)
    (hlen : 0 < len) (hstart : 0 < start) (hfit : FitsLen (start + len)) :
    SudoRt.runLoopOn (Int.ofNat (start + len - 1), (#[] : Array Int))
      (fuelDown (Int.ofNat (start + len - 1)) (Int.ofNat start))
      (climbStep (Int.ofNat start)) after onRet =
    after (Int.ofNat start, embed (downFrom (start + len - 1) len)) := by
  refine desc_goal
    (fun i (a : Array Int) =>
      a = embed (downFrom (start + len - 1) (start + len - i)))
    (by omega : start ≤ start + len - 1)
    (by
      show (#[] : Array Int) =
        embed (downFrom (start + len - 1) (start + len - (start + len - 1 + 1)))
      have hz : start + len - (start + len - 1 + 1) = 0 := by omega
      rw [hz]
      simp [downFrom, embed_nil])
    ?_ ?_
  · intro i a hlo hhi hI
    have hpos : 0 < i := Nat.lt_of_lt_of_le hstart hlo
    have hfi : FitsLen i := FitsLen.of_le hfit (by omega)
    have hholes : downFrom (start + len - 1) (start + len - (i + 1)) =
        downFrom (start + len - 1) (start + len - 1 - i) := by
      congr 1
      omega
    refine ⟨embed (downFrom (start + len - 1) (start + len - i)), rfl, ?_⟩
    rw [hI, hholes]
    exact climb_at start len i _ hhi hpos hfi rfl hlo
  · intro a ha
    have hz : start + len - start = len := by omega
    rw [ha, hz]

theorem climb_holes_refines (b : Ecbs.Board) (start len : Nat)
    (h0 : b.sudo_5Board_7ladder0 = Int.ofNat start)
    (hnr : b.sudo_5Board_6nrungs = Int.ofNat len)
    (hstart : 0 < start) (hfit0 : FitsLen start) (hfit : FitsLen (start + len)) :
    Ecbs.climb_holes b = .ok (embed (downFrom (start + len - 1) len)) := by
  unfold Ecbs.climb_holes
  rw [h0, hnr]
  by_cases hlen0 : len = 0
  · simp only [hlen0, downFrom_zero, embed_nil]
    rw [addI_ofNat start 0 hfit0, ok_bind]
    rw [Nat.add_zero, subI_ofNat_one start hstart hfit0, ok_bind]
    have hlt : Int.ofNat (start - 1) < Int.ofNat start := by
      rw [ofNat_lt_iff]; omega
    rw [fuelDown_eq, fuelDown_lt hlt]
    rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
    simp only [hlt, pure_eq_ok]
    rfl
  · have hlen : 0 < len := Nat.pos_of_ne_zero hlen0
    rw [addI_ofNat start len hfit, ok_bind]
    rw [subI_ofNat_one (start + len) (by omega) hfit, ok_bind]
    dsimp only
    rw [fuelDown_eq]
    conv =>
      pattern (fun σ : Int × Array Int => _)
      change climbStep (Int.ofNat start)
    rw [climb_loop start len _ _ hlen hstart hfit, except_bind_pure, pure_eq_ok]

private theorem down_get (hi k i : Nat) (hik : i < k) :
    (downFrom hi k)[i]'(by rw [downFrom_length]; exact hik) = hi - i := by
  induction k generalizing hi i with
  | zero => cases hik
  | succ k ih =>
    simp only [downFrom_succ]
    cases i with
    | zero => simp
    | succ i =>
      have hik' : i < k := by omega
      have ih' := ih (hi - 1) i hik'
      simp [List.getElem_cons_succ, ih']
      omega

private theorem take_snoc (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  rw [List.take_succ]
  simp [List.getElem?_eq_getElem hi]

/-- Append one control-row colour onto the ladder, in the shape `new_board` emits. -/
def readStep (holes : Array Int) (toV : Int) (σ : Int × Ecbs.Board) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Ecbs.Board) Ecbs.Board) :=
  let i := σ.1
  let b := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, b))
    else
      match ← (do
        let hole ← SudoRt.atL holes i
        let colour ← SudoRt.atL b.sudo_5Board_3row hole
        pure (SudoRt.Flow.cont (ρ := Ecbs.Board)
          { b with sudo_5Board_6ladder := (SudoRt.appendL b.sudo_5Board_6ladder colour).1 }) :
          Except SudoRt.Trap (SudoRt.Flow Ecbs.Board Ecbs.Board)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Ecbs.Board) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Ecbs.Board) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Ecbs.Board) (i', fs))

private theorem colour_ix (t : Spec.Tier) (h : BoardOk t) (i : Nat)
    (hi : i < (rungList (t.n - 1)).length) :
    t.script + 2 + (rungList (t.n - 1)).length - 1 - i <
      (embed (paint (List.replicate t.control 0) (t.script + 2) (rungList (t.n - 1)))).size := by
  rw [size_embed, paint_length, List.length_replicate]
  have := h.ladder
  omega

private theorem colour_at (t : Spec.Tier) (h : BoardOk t) (i : Nat)
    (hi : i < (rungList (t.n - 1)).length) :
    (embed (paint (List.replicate t.control 0) (t.script + 2) (rungList (t.n - 1))))[t.script + 2 + (rungList (t.n - 1)).length - 1 - i]'(colour_ix t h i hi) =
      Int.ofNat ((rungList (t.n - 1)).reverse[i]'(by simp; exact hi)) := by
  let rungs := rungList (t.n - 1)
  have hk : rungs.length - 1 - i < rungs.length := by
    dsimp [rungs]; omega
  have hrev : rungs.reverse[i]'(by dsimp [rungs]; simp; exact hi) =
      rungs[rungs.length - 1 - i]'hk := by
    rw [List.getElem_reverse]
  have hix : t.script + 2 + (rungs.length - 1 - i) =
      t.script + 2 + rungs.length - 1 - i := by
    dsimp [rungs]; omega
  have hpaint := paint_at (List.replicate t.control 0) (t.script + 2) rungs
    (by dsimp [rungs]; rw [List.length_replicate]; have := h.ladder; omega)
    (rungs.length - 1 - i) hk
  have hsz : t.script + 2 + rungs.length - 1 - i <
      (embed (paint (List.replicate t.control 0) (t.script + 2) rungs)).size := by
    dsimp [rungs]
    rw [size_embed, paint_length, List.length_replicate]
    have := h.ladder; omega
  have hget :
      (embed (paint (List.replicate t.control 0) (t.script + 2) rungs))[t.script + 2 + rungs.length - 1 - i]'hsz =
      Int.ofNat (rungs[rungs.length - 1 - i]'hk) := by
    have hpi : t.script + 2 + (rungs.length - 1 - i) <
        (paint (List.replicate t.control 0) (t.script + 2) rungs).length := by
      dsimp [rungs]; rw [paint_length, List.length_replicate]; have := h.ladder; omega
    simp only [get_embed]
    exact congrArg Int.ofNat (((get_idx hix hpi).symm).trans hpaint)
  simpa [rungs] using hget.trans (congrArg Int.ofNat hrev.symm)

private theorem push_colour (acc : List Nat) (c : Nat) :
    ((embed acc).push (Int.ofNat c), ()).1 = embed (acc ++ [c]) := by
  simp
  apply Array.ext'
  simp [embed, toList_push]

private theorem read_hit (t : Spec.Tier) (h : BoardOk t) (b : Ecbs.Board) (i : Nat)
    (hlen : 0 < (rungList (t.n - 1)).length)
    (hi : i ≤ (rungList (t.n - 1)).length - 1)
    (hfi : FitsLen (i + 1))
    (hrow : b.sudo_5Board_3row =
      embed (paint (List.replicate t.control 0) (t.script + 2) (rungList (t.n - 1))))
    (acc : List Nat) (hacc : acc = (rungList (t.n - 1)).reverse.take i) :
    let rungs := rungList (t.n - 1)
    let holes := embed (downFrom (t.script + 2 + rungs.length - 1) rungs.length)
    readStep holes (Int.ofNat (rungs.length - 1))
      (Int.ofNat i, { b with sudo_5Board_6ladder := embed acc }) =
    (if i = rungs.length - 1 then
      .ok (SudoRt.Flow.brk (Int.ofNat i,
        { b with sudo_5Board_6ladder := embed (rungs.reverse.take (i + 1)) }))
    else
      .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
        { b with sudo_5Board_6ladder := embed (rungs.reverse.take (i + 1)) }))) := by
  intro rungs holes
  have hlt : i < (rungList (t.n - 1)).length := by omega
  unfold readStep
  dsimp
  have hngt : ¬ ((i : Int) > ((rungs.length - 1 : Nat) : Int)) :=
    not_gt_cast (by dsimp [rungs]; omega)
  rw [if_neg hngt]
  rw [← ofNat_eq_natCast i]
  have hdg := down_get (t.script + 2 + rungs.length - 1) rungs.length i hlt
  rw [atL_embed _ _ (by rw [downFrom_length]; exact hlt), hdg, ok_bind]
  have hcol := colour_at t h i hlt
  rw [hrow, atL_ofNat _ _ (colour_ix t h i hlt), hcol, ok_bind]
  rw [appendL_spec, push_colour, hacc, pure_eq_ok, ok_bind]
  rw [← take_snoc (rungList (t.n - 1)).reverse i (by simp; exact hlt)]
  exact asc_tail ((rungList (t.n - 1)).length - 1) i hfi _

private theorem read_loop (t : Spec.Tier) (h : BoardOk t) (b : Ecbs.Board)
    (hrow : b.sudo_5Board_3row =
      embed (paint (List.replicate t.control 0) (t.script + 2) (rungList (t.n - 1))))
    (hlad : b.sudo_5Board_6ladder = (#[] : Array Int))
    (hlen : 0 < (rungList (t.n - 1)).length)
    (hfit : FitsLen (rungList (t.n - 1)).length) :
    let rungs := rungList (t.n - 1)
    let holes := embed (downFrom (t.script + 2 + rungs.length - 1) rungs.length)
    SudoRt.runLoopOn (Int.ofNat 0, b)
      (fuelRange (Int.ofNat 0) (Int.ofNat (rungs.length - 1)))
      (readStep holes (Int.ofNat (rungs.length - 1)))
      (fun σ => pure σ.2) (fun r => pure r) =
    pure { b with sudo_5Board_6ladder := embed rungs.reverse } := by
  intro rungs holes
  dsimp only [rungs, holes] at *
  refine asc_goal
    (fun i (s : Ecbs.Board) =>
      s = { b with sudo_5Board_6ladder := embed (rungs.reverse.take i) })
    (Nat.zero_le _) ?_ ?_ ?_
  · show b = { b with sudo_5Board_6ladder := embed (rungs.reverse.take 0) }
    simp only [List.take_zero, embed_nil]
    rw [← hlad]
  · intro i s _ hi hs
    have hfi : FitsLen (i + 1) := FitsLen.of_le hfit (by omega)
    rw [hs]
    refine ⟨{ b with sudo_5Board_6ladder := embed (rungs.reverse.take (i + 1)) }, rfl, ?_⟩
    simpa [rungs, holes] using
      read_hit t h b i hlen (by omega) hfi hrow (rungs.reverse.take i) rfl
  · intro s hs
    have htake : List.take ((rungList (t.n - 1)).length - 1 + 1) (rungList (t.n - 1)).reverse =
        (rungList (t.n - 1)).reverse := by
      have hlen1 : (rungList (t.n - 1)).length - 1 + 1 = (rungList (t.n - 1)).length := by omega
      rw [hlen1, ← List.length_reverse (rungList (t.n - 1)), List.take_length]
    rw [hs, htake]

/-- The board `new_board` returns. The control row is `Spec.rungList` in build order.
    The ladder array is that list in climb order. -/
def builtBoard (t : Spec.Tier) : Ecbs.Board :=
  let rungs := rungList (t.n - 1)
  let moves := (t.n - 1) + halveMoves (t.n - 1)
  let base := midBoard t rungs moves
  { base with
    sudo_5Board_4home := base.sudo_5Board_4home.set ⟨6, home6_mid t rungs moves⟩ (#[] : Array Int)
    sudo_5Board_4held := base.sudo_5Board_4held.set ⟨6, held6_mid t rungs moves⟩ false
    sudo_5Board_4cost := { base.sudo_5Board_4cost with
      sudo_5Costs_5moves := 0
      sudo_5Costs_12ladder_moves := Int.ofNat (ladderMoves t.n) }
    sudo_5Board_9park_hole := Int.ofNat (t.script + 2 + rungs.length)
    sudo_5Board_6tally0 := Int.ofNat (t.script + 2 + rungs.length + 1)
    sudo_5Board_6ladder := embed rungs.reverse }

/-- `new_board` on a `BoardOk` tier. The control row, from `ladder0`, is `Spec.rungList`
    in build order. The ladder array is that list reversed, which is the order
    `climb_holes` walks and the order `invert` reads. -/
theorem new_board_refines (t : Spec.Tier) (h : BoardOk t) :
    Ecbs.new_board (embTier t) = .ok (builtBoard t) := by
  have ht : (embTier t).sudo_4Tier_7control = Int.ofNat t.control := rfl
  have hs : (embTier t).sudo_4Tier_6script = Int.ofNat t.script := rfl
  have hn : (embTier t).sudo_4Tier_1n = Int.ofNat t.n := rfl
  have hs1 : FitsLen (t.script + 1) := fits_script_add t h 1 (by decide)
  have hs2 : FitsLen (t.script + 2) := fits_script_add t h 2 (by decide)
  unfold Ecbs.new_board
  simp only [negI_one,
    (show Ecbs.phase_count = Int.ofNat 8 from rfl),
    (show Ecbs.op_count = Int.ofNat 5 from rfl),
    (show Ecbs.home_count = Int.ofNat 8 from rfl),
    ht, hs, hn, filledL_ofNat, ok_bind]
  rw [addI_ofNat_one t.script hs1, ok_bind]
  rw [show (2 : Int) = Int.ofNat 2 from rfl, addI_ofNat t.script 2 hs2, ok_bind]
  have hfn : FitsLen t.n := fits_board t h t.n (by omega)
  rw [subI_ofNat_one t.n h.n_pos hfn, ok_bind]
  by_cases hn1 : t.n = 1
  · simp only [hn1]
    rw [subI_cast_zero, ok_bind]
    rw [if_pos (by decide : (0 : Int) > -1)]
    conv =>
      pattern (SudoRt.runLoopOn (0, Array.mkArray 1 0) 1)
      rw [show (1 : Nat) = 0 + 1 from rfl]
    rw [runLoopOn_succ]
    simp only [show (0 : Int) > (-1 : Int) by decide, if_true, pure_eq_ok, ok_bind]
    conv =>
      pattern (Ecbs.put _ Ecbs.spare (Array.mkArray (0 + 1) 0))
      change Ecbs.put (blankOf (embTier t) t.control t.script) Ecbs.spare
        (Array.mkArray (0 + 1) (0 : Int))
    have hpeg : Array.mkArray (0 + 1) (0 : Int) = embed (sparePegs t.n) := by
      rw [hn1]
      simp [sparePegs]
      exact (embed_replicate_zero 1).symm
    rw [hpeg]
    conv =>
      pattern (Ecbs.put _ Ecbs.spare _)
      change Ecbs.put (blankOf (embTier t) t.control t.script) ((6 : Nat) : Int)
        (embed (sparePegs t.n))
    rw [put_refines (blankOf (embTier t) t.control t.script) 6 (sparePegs t.n) 0 0
        (blank_home6 _ _ _) (blank_held6 _ _ _) (blank_held7 _ _ _)
        (by simp [blankOf, Array.getElem_mkArray])
        (by simp [blankOf, hn, sparePegs_length h.n_pos, ofNat_eq_natCast])
        (by rw [sparePegs_length h.n_pos]; exact hfn)
        (by simp [blankOf]) (by simp [blankOf])
        (by rw [pegCount_spare, Nat.zero_add]; exact FitsLen.of_le hfn (Nat.sub_le _ _))]
    rw [placed_eq]
    simp only [ok_bind]
    have hc0 : (1 - 1 : Nat) = t.n - 1 := by simp [hn1]
    rw [hc0, ← mid_init t]
    conv =>
      pattern (SudoRt.runLoopOn ((1 : Int), midBoard t [] (t.n - 1), Int.ofNat (t.n - 1)))
      rw [show (1 : Int) = Int.ofNat 1 from rfl]
    rw [fuelRange_eq]
    conv =>
      pattern (fun σ : Int × (Ecbs.Board × Int) => _)
      rw [show (1 : Nat) = t.n from hn1.symm]
    conv =>
      pattern (fuelRange (1 : Int) (Int.ofNat 1))
      conv =>
        enter [2]
        rw [show (1 : Nat) = t.n from hn1.symm]
    conv =>
      pattern (fuelRange (1 : Int) (Int.ofNat t.n))
      rw [show (1 : Int) = Int.ofNat 1 from rfl]
    conv =>
      pattern (fun σ : Int × (Ecbs.Board × Int) => _)
      change halveStep (Int.ofNat t.n)
    rw [halve_loop_refines t h]
    dsimp only
    conv =>
      pattern (Ecbs.clear _ Ecbs.spare)
      change Ecbs.clear (midBoard t (rungList (t.n - 1))
        ((t.n - 1) + halveMoves (t.n - 1))) ((6 : Nat) : Int)
    have hfitc : FitsLen ((t.n - 1) + halveMoves (t.n - 1) + (t.n - 1)) :=
      fits_board t h _ (by
        have := halveMoves_le_self (t.n - 1)
        omega)
    rw [clear_spare t h (rungList (t.n - 1)) ((t.n - 1) + halveMoves (t.n - 1)) hfitc]
    simp only [ok_bind]
    have hlad : (midBoard t (rungList (t.n - 1)) ((t.n - 1) + halveMoves (t.n - 1))).sudo_5Board_7ladder0 =
        Int.ofNat (t.script + 2) := by simp [midBoard, placed, blankOf]
    have hnr : (midBoard t (rungList (t.n - 1)) ((t.n - 1) + halveMoves (t.n - 1))).sudo_5Board_6nrungs =
        Int.ofNat (rungList (t.n - 1)).length := by simp [midBoard]
    rw [hlad, hnr]
    have hfitp : FitsLen (t.script + 2 + (rungList (t.n - 1)).length) :=
      FitsLen.of_le (fits_of h.fits_control) (by have := h.ladder; omega)
    rw [addI_ofNat (t.script + 2) (rungList (t.n - 1)).length hfitp, ok_bind]
    have hfit1 : FitsLen (t.script + 2 + (rungList (t.n - 1)).length + 1) :=
      FitsLen.of_le (fits_of h.fits_control) (by have := h.ladder; omega)
    rw [addI_ofNat_one (t.script + 2 + (rungList (t.n - 1)).length) hfit1, ok_bind]
    have hL : (t.n - 1) + halveMoves (t.n - 1) + (t.n - 1) = ladderMoves t.n := by
      unfold ladderMoves
      omega
    rw [hL]
    conv =>
      pattern (SudoRt.subI (Int.ofNat (ladderMoves t.n)) (0 : Int))
      rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rw [subI_ofNat (ladderMoves t.n) 0
      (fits_board t h (ladderMoves t.n) (by
        unfold ladderMoves
        have := halveMoves_le_self (t.n - 1)
        omega)) (Nat.zero_le _), ok_bind]
    rw [climb_holes_refines _ (t.script + 2) (rungList (t.n - 1)).length rfl rfl
      (by omega) (fits_script_add t h 2 (by decide)) hfitp]
    simp only [ok_bind]
    rw [listLen_embed, downFrom_length, Nat.sub_zero]
    by_cases hlen0 : (rungList (t.n - 1)).length = 0
    · rw [hlen0, subI_cast_zero, ok_bind]
      rw [if_pos (by decide : (0 : Int) > -1)]
      conv =>
        pattern (SudoRt.runLoopOn ((0 : Int), _) (1 : Nat) _ _ _)
        enter [2]
        rw [show (1 : Nat) = 0 + 1 from rfl]
      rw [runLoopOn_succ]
      simp only [show (0 : Int) > (-1 : Int) by decide, if_true, pure_eq_ok, ok_bind]
      have hempty : rungList (t.n - 1) = [] := List.eq_nil_of_length_eq_zero hlen0
      simp [hempty, builtBoard, midBoard, placed, blankOf, embed_nil, List.reverse_nil]
    · have hnil : (rungList (t.n - 1)).length = 0 := by simp [hn1, rungList]
      exact absurd hnil hlen0
  · have hn2 : 2 ≤ t.n := by
      have h1 : 1 ≤ t.n := Nat.succ_le_of_lt h.n_pos
      have hlt : 1 < t.n := Nat.lt_of_le_of_ne h1 (fun h => hn1 h.symm)
      exact Nat.succ_le_of_lt hlt
    rw [subI_ofNat_one (t.n - 1) (by omega) (FitsLen.of_le hfn (by omega)), ok_bind]
    rw [fuelRange_eq]
    have hsub : t.n - 1 - 1 = t.n - 2 := by omega
    conv =>
      pattern (fuelRange (0 : Int) (Int.ofNat (t.n - 1 - 1)))
      rw [show (0 : Int) = Int.ofNat 0 from rfl, hsub]
    conv =>
      pattern (fun σ : Int × Array Int => _)
      change spareStep (Int.ofNat (t.n - 2))
    have hpair : ((0 : Int), Array.mkArray t.n (0 : Int)) =
        (Int.ofNat 0, embed (List.replicate t.n 0)) := by
      apply Prod.ext
      · rfl
      · exact (embed_replicate_zero t.n).symm
    conv =>
      pattern (SudoRt.runLoopOn ((0 : Int), Array.mkArray t.n (0 : Int)))
      rw [hpair]
    rw [spare_loop_refines t.n _ _ hn2 hfn]
    conv =>
      pattern (Ecbs.put _ Ecbs.spare _)
      change Ecbs.put (blankOf (embTier t) t.control t.script) Ecbs.spare
        (embed (sparePegs t.n))
    conv =>
      pattern (Ecbs.put _ Ecbs.spare _)
      change Ecbs.put (blankOf (embTier t) t.control t.script) ((6 : Nat) : Int)
        (embed (sparePegs t.n))
    rw [put_refines (blankOf (embTier t) t.control t.script) 6 (sparePegs t.n) 0 0
        (blank_home6 _ _ _) (blank_held6 _ _ _) (blank_held7 _ _ _)
        (by simp [blankOf, Array.getElem_mkArray])
        (by simp [blankOf, hn, sparePegs_length h.n_pos, ofNat_eq_natCast])
        (by rw [sparePegs_length h.n_pos]; exact hfn)
        (by simp [blankOf]) (by simp [blankOf])
        (by rw [pegCount_spare, Nat.zero_add]; exact FitsLen.of_le hfn (Nat.sub_le _ _))]
    rw [placed_eq]
    simp only [ok_bind]
    rw [← mid_init t]
    conv =>
      pattern (SudoRt.runLoopOn ((1 : Int), midBoard t [] (t.n - 1), Int.ofNat (t.n - 1)))
      rw [show (1 : Int) = Int.ofNat 1 from rfl]
    rw [fuelRange_eq]
    conv =>
      pattern (fuelRange (1 : Int) (Int.ofNat t.n))
      rw [show (1 : Int) = Int.ofNat 1 from rfl]
    conv =>
      pattern (fun σ : Int × (Ecbs.Board × Int) => _)
      change halveStep (Int.ofNat t.n)
    rw [halve_loop_refines t h]
    dsimp only
    conv =>
      pattern (Ecbs.clear _ Ecbs.spare)
      change Ecbs.clear (midBoard t (rungList (t.n - 1))
        ((t.n - 1) + halveMoves (t.n - 1))) ((6 : Nat) : Int)
    have hfitc : FitsLen ((t.n - 1) + halveMoves (t.n - 1) + (t.n - 1)) :=
      fits_board t h _ (by
        have := halveMoves_le_self (t.n - 1)
        omega)
    rw [clear_spare t h (rungList (t.n - 1)) ((t.n - 1) + halveMoves (t.n - 1)) hfitc]
    simp only [ok_bind]
    have hlad : (midBoard t (rungList (t.n - 1)) ((t.n - 1) + halveMoves (t.n - 1))).sudo_5Board_7ladder0 =
        Int.ofNat (t.script + 2) := by simp [midBoard, placed, blankOf]
    have hnr : (midBoard t (rungList (t.n - 1)) ((t.n - 1) + halveMoves (t.n - 1))).sudo_5Board_6nrungs =
        Int.ofNat (rungList (t.n - 1)).length := by simp [midBoard]
    rw [hlad, hnr]
    have hfitp : FitsLen (t.script + 2 + (rungList (t.n - 1)).length) :=
      FitsLen.of_le (fits_of h.fits_control) (by have := h.ladder; omega)
    rw [addI_ofNat (t.script + 2) (rungList (t.n - 1)).length hfitp, ok_bind]
    have hfit1 : FitsLen (t.script + 2 + (rungList (t.n - 1)).length + 1) :=
      FitsLen.of_le (fits_of h.fits_control) (by have := h.ladder; omega)
    rw [addI_ofNat_one (t.script + 2 + (rungList (t.n - 1)).length) hfit1, ok_bind]
    have hL : (t.n - 1) + halveMoves (t.n - 1) + (t.n - 1) = ladderMoves t.n := by
      unfold ladderMoves
      omega
    rw [hL]
    conv =>
      pattern (SudoRt.subI (Int.ofNat (ladderMoves t.n)) (0 : Int))
      rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rw [subI_ofNat (ladderMoves t.n) 0
      (fits_board t h (ladderMoves t.n) (by
        unfold ladderMoves
        have := halveMoves_le_self (t.n - 1)
        omega)) (Nat.zero_le _), ok_bind]
    rw [climb_holes_refines _ (t.script + 2) (rungList (t.n - 1)).length rfl rfl
      (by omega) (fits_script_add t h 2 (by decide)) hfitp]
    simp only [ok_bind]
    rw [listLen_embed, downFrom_length, Nat.sub_zero]
    by_cases hlen0 : (rungList (t.n - 1)).length = 0
    · rw [hlen0, subI_cast_zero, ok_bind]
      rw [if_pos (by decide : (0 : Int) > -1)]
      conv =>
        pattern (SudoRt.runLoopOn ((0 : Int), _) (1 : Nat) _ _ _)
        enter [2]
        rw [show (1 : Nat) = 0 + 1 from rfl]
      rw [runLoopOn_succ]
      simp only [show (0 : Int) > (-1 : Int) by decide, if_true, pure_eq_ok, ok_bind]
      have hempty : rungList (t.n - 1) = [] := List.eq_nil_of_length_eq_zero hlen0
      simp [hempty, builtBoard, midBoard, placed, blankOf, embed_nil, List.reverse_nil]
    · have hlen : 0 < (rungList (t.n - 1)).length := Nat.pos_of_ne_zero hlen0
      have hfitL : FitsLen (rungList (t.n - 1)).length :=
        fits_board t h _ (by
          have := rungList_length_le (t.n - 1)
          omega)
      rw [subI_ofNat_one _ hlen hfitL, ok_bind]
      rw [fuelRange_eq]
      conv =>
        pattern (fuelRange (0 : Int) (Int.ofNat ((rungList (t.n - 1)).length - 1)))
        rw [show (0 : Int) = Int.ofNat 0 from rfl]
      conv =>
        pattern (SudoRt.runLoopOn ((0 : Int), _))
        enter [1, 1]
        rw [show (0 : Int) = Int.ofNat 0 from rfl]
      conv =>
        pattern (fun σ : Int × Ecbs.Board => _)
        change readStep
          (embed (downFrom (t.script + 2 + (rungList (t.n - 1)).length - 1)
            (rungList (t.n - 1)).length))
          (Int.ofNat ((rungList (t.n - 1)).length - 1))
      rw [read_loop t h _ (by simp [midBoard]) (by simp [midBoard, placed, blankOf]) hlen hfitL]
      rw [except_bind_pure, except_bind_pure, except_bind_pure, pure_eq_ok]
      simp [builtBoard, midBoard, placed, blankOf]

end EcbsLink2.Link2
