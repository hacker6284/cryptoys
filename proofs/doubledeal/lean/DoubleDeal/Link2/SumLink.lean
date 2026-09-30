/-
  LINK 2. Bridge the emitted v10 `sum_ranks` to the algebraic `sumRanksV10`.
  Each emitted helper (`row_total`, `row_turn`, `sum_rows`, `suit_label`,
  `gf_add`, `gf_times_w`, `column_value`, `column_suits`, `column_turn`,
  `turn_column`, `sum_columns`) gets its own refinement lemma. Loop bodies are
  restated as twin step functions that are definitionally the emitted ones.
  v10 turn amounts are small (row totals ≤ 1183, column turns < 4), so no
  card-size bound is needed beyond what the callers already carry.
-/
import Doubledeal
import DoubleDeal.Round
import DoubleDeal.SumRanks
import DoubleDeal.SumRanksV10
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Loop
import DoubleDeal.Link2.Deck
import DoubleDeal.Link2.Helpers
import DoubleDeal.Link2.Rotate
import DoubleDeal.Link2.Shift

namespace DoubleDeal.Link2

def fuel13 : Nat := if (0 : Int) > 12 then 1 else ((12 : Int) - 0).natAbs + 1
def fuel4 : Nat := if (0 : Int) > 3 then 1 else ((3 : Int) - 0).natAbs + 1

def colCollectStep (g : Array (Array Int)) (j toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array (Array Int))) :=
  let i := σ.1
  let col := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, col))
    else
      match ← ((do
        let row ← SudoRt.atL g i
        let cell ← SudoRt.atL row j
        let _mb := SudoRt.appendL col cell
        let ⟨col, _⟩ := _mb
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) col)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
      | .cont fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
          else do
            let i' ← SudoRt.addI i 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', fs))

def freshStep (col : Array Int) (s toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array (Array Int))) :=
  let i := σ.1
  let fresh := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fresh))
    else
      match ← ((do
        let d ← SudoRt.subI i s
        let ix ← SudoRt.modI d 4
        let cell ← SudoRt.atL col ix
        let _mb := SudoRt.appendL fresh cell
        let ⟨fresh, _⟩ := _mb
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) fresh)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
      | .cont fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
          else do
            let i' ← SudoRt.addI i 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', fs))

def writeColStep (fresh : Array Int) (j toV : Int) (σ : Int × Array (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array (Array Int)) (Array (Array Int))) :=
  let i := σ.1
  let g := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, g))
    else
      match ← ((do
        let row ← SudoRt.atL g i
        let cell ← SudoRt.atL fresh i
        let row ← SudoRt.putL row j cell
        let g ← SudoRt.putL g i row
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) g)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
      | .cont fs =>
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (i, fs))
          else do
            let i' ← SudoRt.addI i 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', fs))

theorem fits169 : FitsLen 169 := by
  unfold FitsLen i64MaxNat
  decide

theorem take_succ_append {α : Type} (xs : List α) (n : Nat) (h : n < xs.length) :
    xs.take (n + 1) = xs.take n ++ [xs[n]'h] := by
  induction xs generalizing n with
  | nil => simp at h
  | cons a xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      have h' : n < xs.length :=
        Nat.lt_of_succ_lt_succ (by simpa [List.length_cons] using h)
      simp only [List.take, List.getElem_cons_succ]
      rw [ih n h']
      simp

theorem fuel13_eq : fuel13 = fuelRange (Int.ofNat 0) (Int.ofNat 12) := by
  rw [fuel13, fuelRange_le (Nat.zero_le _)]
  decide

theorem fuel4_eq : fuel4 = fuelRange (Int.ofNat 0) (Int.ofNat 3) := by
  rw [fuel4, fuelRange_le (Nat.zero_le _)]
  decide

theorem rotL_mod (xs : List Nat) (k : Nat) (hne : xs.length ≠ 0) :
    rotL xs (k % xs.length) = rotL xs k := by
  simp [rotL, hne, Nat.mod_mod]

theorem subI_bounded (a b : Nat) (ha : a ≤ 4) (hb : b ≤ 4) :
    SudoRt.subI (Int.ofNat a) (Int.ofNat b) = .ok ((a : Int) - (b : Int)) := by
  unfold SudoRt.subI SudoRt.narrowI
  have hmin : ¬ ((a : Int) - (b : Int)) < SudoRt.i64Min := by
    have : SudoRt.i64Min < (-4 : Int) := by decide
    omega
  have hmax : ¬ ((a : Int) - (b : Int)) > SudoRt.i64Max := by
    have : (4 : Int) ≤ SudoRt.i64Max := by decide
    have : (a : Int) - (b : Int) ≤ 4 := by omega
    omega
  simp [hmin, hmax]

theorem modI_sub_small (a b n : Nat) (ha : a < n) (hb : b < n) (hn : 0 < n) :
    SudoRt.modI ((a : Int) - (b : Int)) (Int.ofNat n) =
      .ok (Int.ofNat ((a + (n - b)) % n)) := by
  unfold SudoRt.modI
  have hb0 : ((Int.ofNat n) == (0 : Int)) = false := by
    cases hbv : (Int.ofNat n) == (0 : Int) with
    | false => rfl
    | true =>
      exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hbv))
        (Nat.ne_of_gt hn)
  rw [hb0]
  exact congrArg Except.ok (fmod_sub_small a b n ha hb hn)

theorem colCollectStep_hit (grid : Grid Nat) (j : Nat) (hj : j < 13) (i : Nat) (hi : i ≤ 3) :
    colCollectStep (embedGrid grid) (Int.ofNat j) 3
      (Int.ofNat i, embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take i)) =
      if i = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat i,
          embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
          embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take (i + 1)))) := by
  have hi4 : i < 4 := by omega
  unfold colCollectStep
  rw [if_neg (show ¬ Int.ofNat i > (3 : Int) from ofNat_not_gt hi)]
  have hat := atL_ofNat (embedGrid grid) i (by rw [embedGrid_size]; exact hi4)
  have hrow := embedGrid_get grid ⟨i, hi4⟩
  have hat' :
      (embedGrid grid)[i]'(by rw [embedGrid_size]; exact hi4) =
        embed (toList13 (grid ⟨i, hi4⟩)) := by simpa using hrow
  rw [hat'] at hat
  simp only [hat, ok_bind]
  have hget := getElem_toList13 (grid ⟨i, hi4⟩) ⟨j, hj⟩
  have hatC := atL_embed (toList13 (grid ⟨i, hi4⟩)) j (by rw [length_toList13]; exact hj)
  rw [hatC]
  have hpush :
      (embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take i)).push
          (Int.ofNat (grid ⟨i, hi4⟩ ⟨j, hj⟩)) =
        embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take i ++
          [grid ⟨i, hi4⟩ ⟨j, hj⟩]) := by
    simp [embed, Array.push]
  simp only [ok_bind, hget, appendL_spec, hpush]
  have hidx : (toList4 (fun r => grid r ⟨j, hj⟩))[i]'(by rw [length_toList4]; exact hi4) =
      grid ⟨i, hi4⟩ ⟨j, hj⟩ := getElem_toList4 _ ⟨i, hi4⟩
  have hnext :
      (toList4 (fun r => grid r ⟨j, hj⟩)).take i ++ [grid ⟨i, hi4⟩ ⟨j, hj⟩] =
        (toList4 (fun r => grid r ⟨j, hj⟩)).take (i + 1) := by
    rw [← hidx]
    exact (take_succ_append (toList4 (fun r => grid r ⟨j, hj⟩)) i
      (by rw [length_toList4]; exact hi4)).symm
  rw [hnext]
  by_cases heq : i = 3
  · subst heq
    simp only [ok_bind]
    have hbeq : ((3 : Int) == (3 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat i) == (3 : Int)) = false := by
      cases hb : (Int.ofNat i) == (3 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one i (fits_succ_lt (by omega : i < 3) (by decide : 3 ≤ 52))]
    simp [ok_bind, heq]

theorem rotR_mod (xs : List Nat) (k : Nat) (hne : xs.length ≠ 0) :
    rotR xs (k % xs.length) = rotR xs k := by
  simp [rotR, hne, Nat.mod_mod]

theorem getElem_toList13_nat (f : Fin 13 → α) (i : Nat) (hi : i < 13) :
    (toList13 f)[i]'(by rw [length_toList13]; exact hi) = f ⟨i, hi⟩ := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | n + 13 => omega

theorem toList13_set {α : Type} (f : Fin 13 → α) (j : Nat) (_hj : j < 13) (v : α) :
    (toList13 f).set j v = toList13 (fun c => if c.val = j then v else f c) := by
  apply List.ext_getElem
  · simp [length_toList13, List.length_set]
  · intro i hi hi'
    have hi13 : i < 13 := by simpa [length_toList13] using hi
    have hL := getElem_toList13_nat f i hi13
    have hR := getElem_toList13_nat (fun c => if c.val = j then v else f c) i hi13
    rw [List.getElem_set]
    by_cases h : j = i
    · subst h
      simp only [↓reduceIte]
      have hfun : (fun c => if c.val = j then v else f c) ⟨j, hi13⟩ = v := by simp
      exact (hR.trans hfun).symm
    · simp only [h, ↓reduceIte]
      have hne : i ≠ j := fun h' => h h'.symm
      have hfun : (fun c => if c.val = j then v else f c) ⟨i, hi13⟩ = f ⟨i, hi13⟩ := by
        simp [hne]
      exact hL.trans (hfun.symm.trans hR.symm)

theorem embed_list_set (xs : List Nat) (k : Nat) (hk : k < xs.length) (v : Nat) :
    (embed xs).set ⟨k, by rw [size_embed]; exact hk⟩ (Int.ofNat v) = embed (xs.set k v) := by
  apply Array.ext
  · simp [embed, size_embed, List.length_set]
  · intro i hi hi'
    rw [Array.getElem_set]
    by_cases h : k = i
    · simp [h, embed, get_embed, List.getElem_set]
    · simp [h, embed, get_embed, List.getElem_set]

theorem embedGrid_setCell (g : Grid Nat) (i j : Nat) (hi : i < 4) (hj : j < 13) (v : Nat) :
    ((embedGrid g).set ⟨i, by rw [embedGrid_size]; exact hi⟩
        ((embed (toList13 (g ⟨i, hi⟩))).set
          ⟨j, by rw [size_embed, length_toList13]; exact hj⟩ (Int.ofNat v))) =
      embedGrid (fun r c => if r = ⟨i, hi⟩ ∧ c = ⟨j, hj⟩ then v else g r c) := by
  let idx : Fin (embedGrid g).size := ⟨i, by rw [embedGrid_size]; exact hi⟩
  apply Array.ext
  · simp [embedGrid, Array.size_set]
  · intro n hn hn'
    have hn4 : n < 4 := by simpa [embedGrid] using hn'
    rw [Array.getElem_set]
    by_cases heq : idx.val = n
    · rw [if_pos heq]
      have hin : (⟨i, hi⟩ : Fin 4) = ⟨n, hn4⟩ := by
        apply Fin.ext
        simpa [idx] using heq
      have hset := embed_list_set (toList13 (g ⟨i, hi⟩)) j
        (by rw [length_toList13]; exact hj) v
      rw [hset]
      have hget := embedGrid_get
        (fun r c => if r = ⟨i, hi⟩ ∧ c = ⟨j, hj⟩ then v else g r c) ⟨n, hn4⟩
      rw [hget]
      apply congrArg embed
      rw [toList13_set (g ⟨i, hi⟩) j hj v]
      apply congrArg toList13
      funext c
      by_cases hc : c.val = j
      · have hc' : c = ⟨j, hj⟩ := Fin.ext hc
        simp [hin, hc, hc']
      · have hc' : ¬ (c = ⟨j, hj⟩) := by
          intro h
          exact hc (by simpa using congrArg Fin.val h)
        simp [hin, hc, hc']
    · simp only [heq, ↓reduceIte]
      have hget := embedGrid_get g ⟨n, hn4⟩
      have hget' := embedGrid_get
        (fun r c => if r = ⟨i, hi⟩ ∧ c = ⟨j, hj⟩ then v else g r c) ⟨n, hn4⟩
      rw [hget, hget']
      have hr : (⟨n, hn4⟩ : Fin 4) ≠ ⟨i, hi⟩ := by
        intro h
        exact heq (by simpa [idx] using (Fin.ext_iff.mp h).symm)
      apply congrArg embed
      apply congrArg toList13
      funext c
      simp [hr]

theorem freshStep_hit (xs : List Nat) (s i : Nat) (hi : i ≤ 3) (hs : s < 4)
    (hlen : xs.length = 4) :
    freshStep (embed xs) (Int.ofNat s) 3
      (Int.ofNat i, embed ((rotR xs s).take i)) =
      if i = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, embed ((rotR xs s).take (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed ((rotR xs s).take (i + 1)))) := by
  have hi4 : i < 4 := by omega
  have hiL : i < xs.length := by rw [hlen]; exact hi4
  have hiR : i < (rotR xs s).length := by rw [length_rotR]; exact hiL
  unfold freshStep
  rw [if_neg (show ¬ Int.ofNat i > (3 : Int) from ofNat_not_gt hi)]
  rw [subI_bounded i s (by omega) (by omega)]
  simp only [ok_bind]
  rw [show (4 : Int) = Int.ofNat 4 from rfl]
  rw [modI_sub_small i s 4 hi4 hs (by decide)]
  simp only [ok_bind]
  have hixlt : (i + (4 - s)) % 4 < xs.length := by
    rw [hlen]
    exact Nat.mod_lt _ (by decide)
  have hat := atL_embed xs ((i + (4 - s)) % 4) hixlt
  rw [hat]
  simp only [ok_bind]
  have hcell :
      xs[(i + (4 - s)) % 4]'hixlt = (rotR xs s)[i]'hiR := by
    rw [getElem_rotR xs s i (by rw [hlen]; decide) hiL]
    have hidx :
        (i + (xs.length - s % xs.length)) % xs.length = (i + (4 - s)) % 4 := by
      rw [hlen, Nat.mod_eq_of_lt hs]
    simp [hidx]
  rw [hcell]
  have hpush :
      (embed ((rotR xs s).take i)).push (Int.ofNat ((rotR xs s)[i]'hiR)) =
        embed ((rotR xs s).take i ++ [(rotR xs s)[i]'hiR]) := by
    simp [embed, Array.push]
  simp only [appendL_spec, hpush]
  have hnext :
      (rotR xs s).take i ++ [(rotR xs s)[i]'hiR] = (rotR xs s).take (i + 1) :=
    (take_succ_append (rotR xs s) i hiR).symm
  rw [hnext]
  by_cases heq : i = 3
  · subst heq
    simp only [ok_bind]
    have hbeq : ((3 : Int) == (3 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat i) == (3 : Int)) = false := by
      cases hb : (Int.ofNat i) == (3 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one i (fits_succ_lt (by omega : i < 3) (by decide : 3 ≤ 52))]
    simp [ok_bind, heq]

/-- Column `j` while its first `n` rows have been written with `turnCol g0 j s`. -/
def colWriting (g0 : Grid Nat) (j : Nat) (hj : j < 13) (s n : Nat) : Grid Nat :=
  fun r c => if c = ⟨j, hj⟩ ∧ r.val < n then turnCol g0 ⟨j, hj⟩ s r c else g0 r c

theorem colWriting_zero (g0 : Grid Nat) (j : Nat) (hj : j < 13) (s : Nat) :
    colWriting g0 j hj s 0 = g0 := by
  funext r c
  simp [colWriting]

theorem colWriting_four (g0 : Grid Nat) (j : Nat) (hj : j < 13) (s : Nat) :
    colWriting g0 j hj s 4 = turnCol g0 ⟨j, hj⟩ s := by
  funext r c
  by_cases hc : c = ⟨j, hj⟩
  · simp [colWriting, hc, r.isLt]
  · simp only [colWriting, hc, false_and, ↓reduceIte]
    exact (turnCol_other g0 ⟨j, hj⟩ s r hc).symm

theorem colWriting_succ (g0 : Grid Nat) (j : Nat) (hj : j < 13) (s : Nat) (i : Nat) (hi : i < 4) :
    (fun r c =>
      if r = ⟨i, hi⟩ ∧ c = ⟨j, hj⟩ then turnCol g0 ⟨j, hj⟩ s r c
      else colWriting g0 j hj s i r c) =
      colWriting g0 j hj s (i + 1) := by
  funext r c
  by_cases hr : r = ⟨i, hi⟩
  · by_cases hc : c = ⟨j, hj⟩
    · simp [hr, hc, colWriting]
    · simp [colWriting, hr, hc]
  · have hrne : r.val ≠ i := by
      intro h
      exact hr (Fin.ext h)
    by_cases hc : c = ⟨j, hj⟩
    · have hiff : r.val < i + 1 ↔ r.val < i := by omega
      simp [colWriting, hr, hc, hiff]
    · simp [colWriting, hr, hc]

theorem writeColStep_hit (g0 : Grid Nat) (j : Nat) (hj : j < 13) (s : Nat) (i : Nat) (hi : i ≤ 3)
    (fresh : List Nat) (hf : fresh.length = 4)
    (hv : fresh[i]'(by rw [hf]; omega) = turnCol g0 ⟨j, hj⟩ s ⟨i, by omega⟩ ⟨j, hj⟩) :
    writeColStep (embed fresh) (Int.ofNat j) 3
      (Int.ofNat i, embedGrid (colWriting g0 j hj s i)) =
      if i = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, embedGrid (colWriting g0 j hj s (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embedGrid (colWriting g0 j hj s (i + 1)))) := by
  have hi4 : i < 4 := by omega
  unfold writeColStep
  rw [if_neg (show ¬ Int.ofNat i > (3 : Int) from ofNat_not_gt hi)]
  have hatG := atL_ofNat (embedGrid (colWriting g0 j hj s i)) i (by rw [embedGrid_size]; exact hi4)
  have hrow := embedGrid_get (colWriting g0 j hj s i) ⟨i, hi4⟩
  have hatG' :
      (embedGrid (colWriting g0 j hj s i))[i]'(by rw [embedGrid_size]; exact hi4) =
        embed (toList13 (colWriting g0 j hj s i ⟨i, hi4⟩)) := by simpa using hrow
  rw [hatG'] at hatG
  simp only [hatG, ok_bind]
  have hatF := atL_embed fresh i (by rw [hf]; exact hi4)
  rw [hatF]
  simp only [ok_bind, hv]
  have hputR := putL_ofNat (embed (toList13 (colWriting g0 j hj s i ⟨i, hi4⟩))) j
    (Int.ofNat (turnCol g0 ⟨j, hj⟩ s ⟨i, hi4⟩ ⟨j, hj⟩))
    (by rw [size_embed, length_toList13]; exact hj)
  rw [hputR]
  simp only [ok_bind]
  have hputG := putL_ofNat (embedGrid (colWriting g0 j hj s i)) i
    ((embed (toList13 (colWriting g0 j hj s i ⟨i, hi4⟩))).set
      ⟨j, by rw [size_embed, length_toList13]; exact hj⟩
      (Int.ofNat (turnCol g0 ⟨j, hj⟩ s ⟨i, hi4⟩ ⟨j, hj⟩)))
    (by rw [embedGrid_size]; exact hi4)
  rw [hputG]
  simp only [ok_bind]
  rw [embedGrid_setCell (colWriting g0 j hj s i) i j hi4 hj _]
  have hswap :
      (fun r c =>
        if r = ⟨i, hi4⟩ ∧ c = ⟨j, hj⟩ then
          turnCol g0 ⟨j, hj⟩ s ⟨i, hi4⟩ ⟨j, hj⟩
        else colWriting g0 j hj s i r c) =
        (fun r c =>
          if r = ⟨i, hi4⟩ ∧ c = ⟨j, hj⟩ then turnCol g0 ⟨j, hj⟩ s r c
          else colWriting g0 j hj s i r c) := by
    funext r c
    by_cases hrc : r = ⟨i, hi4⟩ ∧ c = ⟨j, hj⟩ <;> simp [hrc]
  rw [hswap, colWriting_succ g0 j hj s i hi4]
  by_cases heq : i = 3
  · subst heq
    simp only [ok_bind]
    have hbeq : ((3 : Int) == (3 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat i) == (3 : Int)) = false := by
      cases hb : (Int.ofNat i) == (3 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one i (fits_succ_lt (by omega : i < 3) (by decide : 3 ≤ 52))]
    simp [ok_bind, heq]

theorem write_loop (g0 : Grid Nat) (j : Nat) (hj : j < 13) (s : Nat) (fresh : List Nat)
    (hf : fresh.length = 4)
    (hv : ∀ i : Nat, (hi : i < 4) →
      fresh[i]'(by rw [hf]; exact hi) = turnCol g0 ⟨j, hj⟩ s ⟨i, hi⟩ ⟨j, hj⟩) :
    SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), embedGrid g0) fuel4
      (writeColStep (embed fresh) (Int.ofNat j) 3)
      (fun σ => pure σ.2) (fun r => pure r) =
      .ok (embedGrid (turnCol g0 ⟨j, hj⟩ s)) := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      writeColStep (embed fresh) (Int.ofNat j) 3
        (Int.ofNat i, embedGrid (colWriting g0 j hj s i)) =
        if i = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embedGrid (colWriting g0 j hj s (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embedGrid (colWriting g0 j hj s (i + 1)))) := by
    intro i _ hi
    have hi4 : i < 4 := by omega
    exact writeColStep_hit g0 j hj s i hi fresh hf (by
      simpa [hf] using hv i hi4)
  have hrun := chain_loop
    (writeColStep (embed fresh) (Int.ofNat j) 3)
    (fun σ => pure σ.2) (fun r => pure r)
    (fun i => embedGrid (colWriting g0 j hj s i)) 0 3 (Nat.zero_le _) hstep
    (.ok (embedGrid (turnCol g0 ⟨j, hj⟩ s)))
    (by show Except.ok (embedGrid (colWriting g0 j hj s 4)) = _; rw [colWriting_four])
  have hcast :
      SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), embedGrid g0) fuel4
        (writeColStep (embed fresh) (Int.ofNat j) 3)
        (fun σ => pure σ.2) (fun r => pure r) =
      SudoRt.runLoopOn (Int.ofNat 0, embedGrid (colWriting g0 j hj s 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 3))
        (writeColStep (embed fresh) (Int.ofNat j) 3)
        (fun σ => pure σ.2) (fun r => pure r) := by
    rw [fuel4_eq, colWriting_zero]
    rfl
  exact hcast.trans hrun

theorem fresh_loop {β : Type} (xs : List Nat) (s : Nat) (hs : s < 4) (hlen : xs.length = 4)
    (after : Int × Array Int → Except SudoRt.Trap β)
    (onRet : Array (Array Int) → Except SudoRt.Trap β)
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat 3, embed (rotR xs s)) = goal) :
    SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel4
      (freshStep (embed xs) (Int.ofNat s) 3) after onRet = goal := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      freshStep (embed xs) (Int.ofNat s) 3
        (Int.ofNat i, embed ((rotR xs s).take i)) =
        if i = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat i, embed ((rotR xs s).take (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed ((rotR xs s).take (i + 1)))) :=
    fun i _ hi => freshStep_hit xs s i hi hs hlen
  have ht : (rotR xs s).take 4 = rotR xs s := by
    simpa [length_rotR, hlen] using (List.take_length (rotR xs s))
  have hrun := chain_loop
    (freshStep (embed xs) (Int.ofNat s) 3) after onRet
    (fun i => embed ((rotR xs s).take i)) 0 3 (Nat.zero_le _) hstep goal
    (by simpa [ht] using hafter)
  have hcast :
      SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel4
        (freshStep (embed xs) (Int.ofNat s) 3) after onRet =
      SudoRt.runLoopOn (Int.ofNat 0, embed ((rotR xs s).take 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 3))
        (freshStep (embed xs) (Int.ofNat s) 3) after onRet := by
    rw [fuel4_eq, List.take_zero, embed_nil]
    rfl
  exact hcast.trans hrun

theorem collect_loop {β : Type} (grid : Grid Nat) (j : Nat) (hj : j < 13)
    (after : Int × Array Int → Except SudoRt.Trap β)
    (onRet : Array (Array Int) → Except SudoRt.Trap β)
    (goal : Except SudoRt.Trap β)
    (hafter : after (Int.ofNat 3, embed (toList4 (fun r => grid r ⟨j, hj⟩))) = goal) :
    SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel4
      (colCollectStep (embedGrid grid) (Int.ofNat j) 3) after onRet = goal := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      colCollectStep (embedGrid grid) (Int.ofNat j) 3
        (Int.ofNat i, embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take i)) =
        if i = 3 then
          .ok (SudoRt.Flow.brk (Int.ofNat i,
            embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take (i + 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
            embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take (i + 1)))) :=
    fun i _ hi => colCollectStep_hit grid j hj i hi
  have ht : (toList4 (fun r => grid r ⟨j, hj⟩)).take 4 =
      toList4 (fun r => grid r ⟨j, hj⟩) := by
    simpa [length_toList4] using
      (List.take_length (toList4 (fun r => grid r ⟨j, hj⟩)))
  have hrun := chain_loop
    (colCollectStep (embedGrid grid) (Int.ofNat j) 3) after onRet
    (fun i => embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take i)) 0 3 (Nat.zero_le _) hstep
    goal (by simpa [ht] using hafter)
  have hcast :
      SudoRt.runLoopOn ((0 : Int), (#[] : Array Int)) fuel4
        (colCollectStep (embedGrid grid) (Int.ofNat j) 3) after onRet =
      SudoRt.runLoopOn (Int.ofNat 0, embed ((toList4 (fun r => grid r ⟨j, hj⟩)).take 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 3))
        (colCollectStep (embedGrid grid) (Int.ofNat j) 3) after onRet := by
    rw [fuel4_eq, List.take_zero, embed_nil]
    rfl
  exact hcast.trans hrun

/-! ## Small arithmetic -/

theorem fits4096 : FitsLen 4096 := by
  unfold FitsLen i64MaxNat
  decide

theorem lit_ofNat (n : Nat) : (OfNat.ofNat n : Int) = Int.ofNat n := rfl

theorem atL_grid (G : Grid Nat) (r : Nat) (hr : r < 4) :
    SudoRt.atL (embedGrid G) (Int.ofNat r) = .ok (embed (toList13 (G ⟨r, hr⟩))) := by
  rw [atL_ofNat (embedGrid G) r (by rw [embedGrid_size]; exact hr)]
  exact congrArg (Except.ok (ε := SudoRt.Trap)) (embedGrid_get G ⟨r, hr⟩)

theorem atL_row (x : Fin 13 → Nat) (c : Nat) (hc : c < 13) :
    SudoRt.atL (embed (toList13 x)) (Int.ofNat c) = .ok (Int.ofNat (x ⟨c, hc⟩)) := by
  rw [atL_embed (toList13 x) c (by rw [length_toList13]; exact hc), getElem_toList13_nat x c hc]

/-! ## Rows: `row_total`, `row_turn`, `sum_rows` -/

def rowTotalStep (row : Array Int) (toV : Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) Int) :=
  let j := σ.1
  let total := σ.2
  do
    if j > toV then
      pure (SudoRt.Flow.brk (ρ := Int) (j, total))
    else
      match ← ((do
        let w ← SudoRt.subI (13 : Int) j
        let cell ← SudoRt.atL row j
        let rk ← Doubledeal.rank_of cell
        let m ← SudoRt.mulI w rk
        let total ← SudoRt.addI total m
        pure (SudoRt.Flow.cont (ρ := Int) total)
      ) : Except SudoRt.Trap (SudoRt.Flow _ Int)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Int) (j, fs))
      | .cont fs =>
          if (j == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Int) (j, fs))
          else do
            let j' ← SudoRt.addI j 1
            pure (SudoRt.Flow.cont (ρ := Int) (j', fs))

theorem row_total_as_loop (row : Array Int) :
    Doubledeal.row_total row =
      (do
        let _out ← SudoRt.runLoopOn (ρ := Int) ((0 : Int), (0 : Int)) fuel13
          (rowTotalStep row 12) (fun σ => pure σ.2) (fun r => pure r)
        pure _out) := by
  unfold Doubledeal.row_total
  rfl

theorem rowPref_le (xs : List Nat) (n : Nat) : rowPref xs n ≤ 169 * n := by
  induction n with
  | zero => simp [rowPref]
  | succ n ih =>
    have hr : rank (xs.getD n 0) ≤ 13 := by simp only [rank]; omega
    have hm : (13 - n) * rank (xs.getD n 0) ≤ 13 * 13 :=
      Nat.mul_le_mul (Nat.sub_le _ _) hr
    simp only [rowPref]
    omega

theorem rowTotalStep_hit (xs : List Nat) (j : Nat) (hj : j ≤ 12) (hlen : xs.length = 13) :
    rowTotalStep (embed xs) 12 (Int.ofNat j, Int.ofNat (rowPref xs j)) =
      if j = 12 then
        .ok (SudoRt.Flow.brk (Int.ofNat j, Int.ofNat (rowPref xs (j + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), Int.ofNat (rowPref xs (j + 1)))) := by
  unfold rowTotalStep
  rw [if_neg (show ¬ Int.ofNat j > (12 : Int) from ofNat_not_gt hj)]
  rw [show (13 : Int) = Int.ofNat 13 from rfl,
    subI_ofNat 13 j (FitsLen.of_le fits4096 (by decide)) (by omega)]
  simp only [ok_bind]
  rw [atL_embed xs j (by omega)]
  simp only [ok_bind]
  have hcell : xs[j]'(by omega) = xs.getD j 0 := by simp [List.getD, show j < xs.length by omega]
  rw [show Int.ofNat (xs[j]'(by omega)) = Int.ofNat (xs.getD j 0) from by simp [hcell]]
  rw [rank_of_refines (xs.getD j 0)]
  simp only [ok_bind]
  have hr : rank (xs.getD j 0) ≤ 13 := by simp only [rank]; omega
  have hm : (13 - j) * rank (xs.getD j 0) ≤ 13 * 13 := Nat.mul_le_mul (Nat.sub_le _ _) hr
  rw [mulI_ofNat (13 - j) (rank (xs.getD j 0)) (FitsLen.of_le fits4096 (by omega))]
  simp only [ok_bind]
  have hp := rowPref_le xs j
  rw [addI_ofNat (rowPref xs j) _ (FitsLen.of_le fits4096 (by omega))]
  simp only [ok_bind]
  have hnext : rowPref xs j + (13 - j) * rank (xs.getD j 0) = rowPref xs (j + 1) := rfl
  rw [hnext]
  by_cases heq : j = 12
  · subst heq
    have hbeq : ((12 : Int) == (12 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat j) == (12 : Int)) = false := by
      cases hb : (Int.ofNat j) == (12 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one j (fits_succ_lt (by omega : j < 12) (by decide))]
    simp [ok_bind, heq]

theorem row_total_refines (x : Fin 13 → Nat) :
    Doubledeal.row_total (embed (toList13 x)) = .ok (Int.ofNat (rowTotal x)) := by
  rw [row_total_as_loop, except_bind_pure]
  let xs := toList13 x
  have hlen : xs.length = 13 := length_toList13 _
  have hrun := chain_loop (rowTotalStep (embed xs) 12) (fun σ => pure σ.2) (fun r => pure r)
    (fun j => Int.ofNat (rowPref xs j)) 0 12 (Nat.zero_le _)
    (fun j _ hj => rowTotalStep_hit xs j hj hlen)
    (.ok (Int.ofNat (rowTotal x))) rfl
  have hcast :
      SudoRt.runLoopOn (ρ := Int) ((0 : Int), (0 : Int)) fuel13 (rowTotalStep (embed xs) 12)
          (fun σ => pure σ.2) (fun r => pure r) =
        SudoRt.runLoopOn (Int.ofNat 0, Int.ofNat (rowPref xs 0))
          (fuelRange (Int.ofNat 0) (Int.ofNat 12)) (rowTotalStep (embed xs) 12)
          (fun σ => pure σ.2) (fun r => pure r) := by
    rw [fuel13_eq]
    rfl
  exact hcast.trans hrun

theorem row_turn_refines (x : Fin 13 → Nat) :
    Doubledeal.row_turn (embed (toList13 x)) = .ok (Int.ofNat (rowTurnV10 x)) := by
  unfold Doubledeal.row_turn
  rw [row_total_refines]
  simp only [ok_bind]
  rw [show (13 : Int) = Int.ofNat 13 from rfl, modI_ofNat _ (by decide)]
  rfl

/-- `sum_rows` loop body (emitted `for a = 1 to 4`). -/
def sumRowsStep (toV : Int) (σ : Int × Array (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array (Array Int)) (Array (Array Int))) :=
  let a := σ.1
  let g := σ.2
  do
    if a > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (a, g))
    else
      match ← ((do
        let i ← SudoRt.modI a (4 : Int)
        let row ← SudoRt.atL g i
        let p ← SudoRt.addI i (3 : Int)
        let p ← SudoRt.modI p (4 : Int)
        let prev ← SudoRt.atL g p
        let t ← Doubledeal.row_turn prev
        let row' ← Doubledeal.left_rotate row t
        let g ← SudoRt.putL g i row'
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) g)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (a, fs))
      | .cont fs =>
          if (a == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (a, fs))
          else do
            let a' ← SudoRt.addI a 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (a', fs))

def fuelRows : Nat := if (1 : Int) > 4 then 1 else ((4 : Int) - 1).natAbs + 1

theorem fuelRows_eq : fuelRows = fuelRange (Int.ofNat 1) (Int.ofNat 4) := by
  rw [fuelRows, fuelRange_le (by decide : 1 ≤ 4)]
  decide

theorem sum_rows_as_loop (g : Array (Array Int)) :
    Doubledeal.sum_rows g =
      (do
        let _out ← SudoRt.runLoopOn (ρ := Array (Array Int)) ((1 : Int), g) fuelRows
          (sumRowsStep 4) (fun σ => pure σ.2) (fun r => pure r)
        pure _out) := by
  unfold Doubledeal.sum_rows
  rfl

theorem setRow_turnRow (G : Grid Nat) (i : Fin 4) (k : Nat) (h) :
    (fun r c => if r = i then ofList13 (rotL (toList13 (G i)) k) h c else G r c) =
      turnRow G i k := by
  funext r c
  by_cases hr : r = i
  · subst hr
    simp only [↓reduceIte]
    unfold turnRow rowRotate
    exact congrFun (ofList13_eq _ _ (by simp)) c
  · rw [if_neg hr, turnRow_other _ _ _ hr]

theorem sumRowsStep_hit (G : Grid Nat) (a : Nat) (ha : a ≤ 4) :
    sumRowsStep 4 (Int.ofNat a, embedGrid G) =
      if a = 4 then
        .ok (SudoRt.Flow.brk (Int.ofNat a,
          embedGrid (rowStep rowTurnV10 G ⟨a % 4, Nat.mod_lt _ (by decide)⟩)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (a + 1),
          embedGrid (rowStep rowTurnV10 G ⟨a % 4, Nat.mod_lt _ (by decide)⟩))) := by
  have hi : a % 4 < 4 := Nat.mod_lt _ (by decide)
  have hp : (a % 4 + 3) % 4 < 4 := Nat.mod_lt _ (by decide)
  unfold sumRowsStep
  rw [if_neg (show ¬ Int.ofNat a > (4 : Int) from ofNat_not_gt ha)]
  simp only [lit_ofNat]
  rw [modI_ofNat a (by decide)]
  simp only [ok_bind]
  rw [atL_grid G _ hi]
  simp only [ok_bind]
  rw [addI_ofNat _ _ (FitsLen.of_le fits4096 (by omega))]
  simp only [ok_bind]
  rw [modI_ofNat _ (by decide)]
  simp only [ok_bind]
  rw [atL_grid G _ hp]
  simp only [ok_bind]
  rw [row_turn_refines]
  simp only [ok_bind]
  rw [left_rotate_refines _ _ (fits52 (by rw [length_toList13]; decide))]
  simp only [ok_bind]
  rw [putL_ofNat _ _ _ (by rw [embedGrid_size]; exact hi)]
  simp only [ok_bind]
  rw [embedGrid_setRow G (a % 4) hi _ (by rw [length_rotL, length_toList13])]
  rw [setRow_turnRow]
  have hstep : turnRow G ⟨a % 4, hi⟩ (rowTurnV10 (G ⟨(a % 4 + 3) % 4, hp⟩)) =
      rowStep rowTurnV10 G ⟨a % 4, hi⟩ := rfl
  rw [hstep]
  by_cases heq : a = 4
  · subst heq
    have hbeq : ((Int.ofNat 4) == (Int.ofNat 4)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat a) == (Int.ofNat 4)) = false := by
      cases hb : (Int.ofNat a) == (Int.ofNat 4) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, heq]
    rw [addI_ofNat a 1 (fits_succ_lt (by omega : a < 4) (by decide))]
    simp [ok_bind]

theorem sum_rows_refines (G : Grid Nat) :
    Doubledeal.sum_rows (embedGrid G) = .ok (embedGrid (rowsDone rowTurnV10 G 4)) := by
  rw [sum_rows_as_loop, except_bind_pure]
  have hstep : ∀ a, 1 ≤ a → a ≤ 4 →
      sumRowsStep 4 (Int.ofNat a, embedGrid (rowsDone rowTurnV10 G (a - 1))) =
        if a = 4 then
          .ok (SudoRt.Flow.brk (Int.ofNat a, embedGrid (rowsDone rowTurnV10 G (a + 1 - 1))))
        else
          .ok (SudoRt.Flow.cont
            (Int.ofNat (a + 1), embedGrid (rowsDone rowTurnV10 G (a + 1 - 1)))) := by
    intro a h1 h4
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact sumRowsStep_hit (rowsDone rowTurnV10 G m) (m + 1) h4
  have hrun := chain_loop (sumRowsStep 4) (fun σ => pure σ.2) (fun r => pure r)
    (fun a => embedGrid (rowsDone rowTurnV10 G (a - 1))) 1 4 (by decide) hstep
    (.ok (embedGrid (rowsDone rowTurnV10 G 4))) rfl
  have hcast :
      SudoRt.runLoopOn (ρ := Array (Array Int)) ((1 : Int), embedGrid G) fuelRows
          (sumRowsStep 4) (fun σ => pure σ.2) (fun r => pure r) =
        SudoRt.runLoopOn (Int.ofNat 1, embedGrid (rowsDone rowTurnV10 G (1 - 1)))
          (fuelRange (Int.ofNat 1) (Int.ofNat 4)) (sumRowsStep 4)
          (fun σ => pure σ.2) (fun r => pure r) := by
    rw [fuelRows_eq]
    rfl
  exact hcast.trans hrun


/-! ## Columns: GF(4) labels, `column_turn`, `turn_column`, `sum_columns` -/

theorem suit_label_refines (c : Nat) :
    Doubledeal.suit_label (Int.ofNat c) = .ok (Int.ofNat (suitLabel c)) := by
  unfold Doubledeal.suit_label
  rw [suit_of_refines]
  simp only [ok_bind]
  rw [sEq_ofNat_zero]
  by_cases h : suit c = 0
  · simp [h, suitLabel, Pure.pure, Except.pure]
  · rw [if_neg (by simpa using h)]
    simp only [lit_ofNat]
    rw [modI_ofNat _ (by decide)]
    simp only [ok_bind]
    rw [addI_ofNat _ _ (FitsLen.of_le fits4096 (by omega))]
    simp [suitLabel, h]

theorem gf_times_w_refines (x : Nat) :
    Doubledeal.gf_times_w (Int.ofNat x) = .ok (Int.ofNat (gfTimesW x)) := by
  unfold Doubledeal.gf_times_w
  rw [sEq_ofNat_zero]
  by_cases h : x = 0
  · simp [h, gfTimesW, Pure.pure, Except.pure]
  · rw [if_neg (by simpa using h)]
    simp only [lit_ofNat]
    rw [modI_ofNat _ (by decide)]
    simp only [ok_bind]
    rw [addI_ofNat _ _ (FitsLen.of_le fits4096 (by omega))]
    simp [gfTimesW, h]

theorem gf_add_refines (a b : Nat) (ha : a < 4) (hb : b < 4) :
    Doubledeal.gf_add (Int.ofNat a) (Int.ofNat b) = .ok (Int.ofNat (gfAdd a b)) := by
  unfold Doubledeal.gf_add
  simp only [lit_ofNat]
  rw [modI_ofNat a (by decide)]
  simp only [ok_bind]
  rw [modI_ofNat b (by decide)]
  simp only [ok_bind]
  rw [addI_ofNat _ _ (FitsLen.of_le fits4096 (by omega))]
  simp only [ok_bind]
  rw [modI_ofNat _ (by decide)]
  simp only [ok_bind]
  rw [divI_ofNat a (by decide)]
  simp only [ok_bind]
  rw [divI_ofNat b (by decide)]
  simp only [ok_bind]
  rw [addI_ofNat _ _ (FitsLen.of_le fits4096 (by omega))]
  simp only [ok_bind]
  rw [modI_ofNat _ (by decide)]
  simp only [ok_bind]
  rw [mulI_ofNat 2 _ (FitsLen.of_le fits4096 (by omega))]
  simp only [ok_bind]
  rw [addI_ofNat _ _ (FitsLen.of_le fits4096 (by omega))]
  rfl

theorem column_value_refines (G : Grid Nat) (p : Nat) (hp : p < 13) :
    Doubledeal.column_value (embedGrid G) (Int.ofNat p) =
      .ok (Int.ofNat (colValue (column G ⟨p, hp⟩))) := by
  unfold Doubledeal.column_value
  simp only [lit_ofNat]
  rw [atL_grid G 1 (by decide)]
  simp only [ok_bind]
  rw [atL_row _ p hp]
  simp only [ok_bind]
  rw [suit_label_refines]
  simp only [ok_bind]
  rw [atL_grid G 2 (by decide)]
  simp only [ok_bind]
  rw [atL_row _ p hp]
  simp only [ok_bind]
  rw [suit_label_refines]
  simp only [ok_bind]
  rw [gf_times_w_refines]
  simp only [ok_bind]
  rw [gf_add_refines _ _ (suitLabel_lt _) (gfTimesW_lt _)]
  simp only [ok_bind]
  rw [atL_grid G 3 (by decide)]
  simp only [ok_bind]
  rw [atL_row _ p hp]
  simp only [ok_bind]
  rw [suit_label_refines]
  simp only [ok_bind]
  rw [gf_times_w_refines]
  simp only [ok_bind]
  rw [gf_times_w_refines]
  simp only [ok_bind]
  rw [gf_add_refines _ _ (gfAdd_lt _ _) (gfTimesW_lt _)]
  rfl

theorem column_suits_refines (G : Grid Nat) (j : Nat) (hj : j < 13) :
    Doubledeal.column_suits (embedGrid G) (Int.ofNat j) =
      .ok (Int.ofNat (colSuits (column G ⟨j, hj⟩))) := by
  unfold Doubledeal.column_suits
  simp only [lit_ofNat]
  rw [atL_grid G 0 (by decide)]
  simp only [ok_bind]
  rw [atL_row _ j hj]
  simp only [ok_bind]
  rw [suit_label_refines]
  simp only [ok_bind]
  rw [atL_grid G 1 (by decide)]
  simp only [ok_bind]
  rw [atL_row _ j hj]
  simp only [ok_bind]
  rw [suit_label_refines]
  simp only [ok_bind]
  rw [gf_add_refines _ _ (suitLabel_lt _) (suitLabel_lt _)]
  simp only [ok_bind]
  rw [atL_grid G 2 (by decide)]
  simp only [ok_bind]
  rw [atL_row _ j hj]
  simp only [ok_bind]
  rw [suit_label_refines]
  simp only [ok_bind]
  rw [gf_add_refines _ _ (gfAdd_lt _ _) (suitLabel_lt _)]
  simp only [ok_bind]
  rw [atL_grid G 3 (by decide)]
  simp only [ok_bind]
  rw [atL_row _ j hj]
  simp only [ok_bind]
  rw [suit_label_refines]
  simp only [ok_bind]
  rw [gf_add_refines _ _ (gfAdd_lt _ _) (suitLabel_lt _)]
  rfl

theorem column_turn_refines (G : Grid Nat) (j : Nat) (hj : j < 13) :
    Doubledeal.column_turn (embedGrid G) (Int.ofNat j) =
      .ok (Int.ofNat (colTurnV10 (column G (prevCol ⟨j, hj⟩)) (column G ⟨j, hj⟩))) := by
  unfold Doubledeal.column_turn
  simp only [lit_ofNat]
  rw [addI_ofNat j 12 (FitsLen.of_le fits4096 (by omega))]
  simp only [ok_bind]
  rw [modI_ofNat _ (by decide)]
  simp only [ok_bind]
  rw [column_value_refines G _ (Nat.mod_lt _ (by decide))]
  simp only [ok_bind]
  rw [column_suits_refines G j hj]
  simp only [ok_bind]
  rw [gf_add_refines _ _ (show colValue _ < 4 from gfAdd_lt _ _)
    (show colSuits _ < 4 from gfAdd_lt _ _)]
  rfl

theorem turn_column_as_loop (g : Array (Array Int)) (j s : Int) :
    Doubledeal.turn_column g j s =
      (do
        let _out ← SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), (#[] : Array Int)) fuel4
          (colCollectStep g j 3)
          (fun σ => do
            let col := σ.2
            let _out ← SudoRt.runLoopOn (ρ := Array (Array Int))
              ((0 : Int), (#[] : Array Int)) fuel4
              (freshStep col s 3)
              (fun σ => do
                let fresh := σ.2
                let _out ← SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), g) fuel4
                  (writeColStep fresh j 3) (fun σ => pure σ.2) (fun r => pure r)
                pure _out)
              (fun r => pure r)
            pure _out)
          (fun r => pure r)
        pure _out) := by
  unfold Doubledeal.turn_column
  rfl

theorem turn_column_refines (G : Grid Nat) (j : Nat) (hj : j < 13) (s : Nat) (hs : s < 4) :
    Doubledeal.turn_column (embedGrid G) (Int.ofNat j) (Int.ofNat s) =
      .ok (embedGrid (turnCol G ⟨j, hj⟩ s)) := by
  rw [turn_column_as_loop, except_bind_pure]
  let xs := toList4 (fun r => G r ⟨j, hj⟩)
  have hlen : xs.length = 4 := length_toList4 _
  have hv : ∀ i : Nat, (hi : i < 4) →
      (rotR xs s)[i]'(by rw [length_rotR, hlen]; exact hi) =
        turnCol G ⟨j, hj⟩ s ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i hi
    simp [turnCol, colRotate, ofList4, xs]
  exact collect_loop G j hj _ _ _ (by
    dsimp only
    rw [except_bind_pure]
    exact fresh_loop xs s hs hlen _ _ _ (by
      dsimp only
      rw [except_bind_pure]
      exact write_loop G j hj s (rotR xs s) (by rw [length_rotR, hlen]) hv))

/-- `sum_columns` loop body (emitted `for a = 1 to 13`). -/
def sumColsStep (toV : Int) (σ : Int × Array (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array (Array Int)) (Array (Array Int))) :=
  let a := σ.1
  let g := σ.2
  do
    if a > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (a, g))
    else
      match ← ((do
        let j ← SudoRt.modI a (13 : Int)
        let t ← Doubledeal.column_turn g j
        let g ← Doubledeal.turn_column g j t
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) g)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (a, fs))
      | .cont fs =>
          if (a == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (a, fs))
          else do
            let a' ← SudoRt.addI a 1
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (a', fs))

def fuelCols : Nat := if (1 : Int) > 13 then 1 else ((13 : Int) - 1).natAbs + 1

theorem fuelCols_eq : fuelCols = fuelRange (Int.ofNat 1) (Int.ofNat 13) := by
  rw [fuelCols, fuelRange_le (by decide : 1 ≤ 13)]
  decide

theorem sum_columns_as_loop (g : Array (Array Int)) :
    Doubledeal.sum_columns g =
      (do
        let _out ← SudoRt.runLoopOn (ρ := Array (Array Int)) ((1 : Int), g) fuelCols
          (sumColsStep 13) (fun σ => pure σ.2) (fun r => pure r)
        pure _out) := by
  unfold Doubledeal.sum_columns
  rfl

theorem sumColsStep_hit (G : Grid Nat) (a : Nat) (ha : a ≤ 13) :
    sumColsStep 13 (Int.ofNat a, embedGrid G) =
      if a = 13 then
        .ok (SudoRt.Flow.brk (Int.ofNat a,
          embedGrid (colStep colTurnV10 G ⟨a % 13, Nat.mod_lt _ (by decide)⟩)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (a + 1),
          embedGrid (colStep colTurnV10 G ⟨a % 13, Nat.mod_lt _ (by decide)⟩))) := by
  have hi : a % 13 < 13 := Nat.mod_lt _ (by decide)
  unfold sumColsStep
  rw [if_neg (show ¬ Int.ofNat a > (13 : Int) from ofNat_not_gt ha)]
  simp only [lit_ofNat]
  rw [modI_ofNat a (by decide)]
  simp only [ok_bind]
  rw [column_turn_refines G _ hi]
  simp only [ok_bind]
  rw [turn_column_refines G _ hi _ (colTurnV10_lt _ _)]
  simp only [ok_bind]
  have hstep : turnCol G ⟨a % 13, hi⟩
      (colTurnV10 (column G (prevCol ⟨a % 13, hi⟩)) (column G ⟨a % 13, hi⟩)) =
      colStep colTurnV10 G ⟨a % 13, hi⟩ := rfl
  rw [hstep]
  by_cases heq : a = 13
  · subst heq
    have hbeq : ((Int.ofNat 13) == (Int.ofNat 13)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat a) == (Int.ofNat 13)) = false := by
      cases hb : (Int.ofNat a) == (Int.ofNat 13) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte, heq]
    rw [addI_ofNat a 1 (fits_succ_lt (by omega : a < 13) (by decide))]
    simp [ok_bind]

theorem sum_columns_refines (G : Grid Nat) :
    Doubledeal.sum_columns (embedGrid G) = .ok (embedGrid (colsDone colTurnV10 G 13)) := by
  rw [sum_columns_as_loop, except_bind_pure]
  have hstep : ∀ a, 1 ≤ a → a ≤ 13 →
      sumColsStep 13 (Int.ofNat a, embedGrid (colsDone colTurnV10 G (a - 1))) =
        if a = 13 then
          .ok (SudoRt.Flow.brk (Int.ofNat a, embedGrid (colsDone colTurnV10 G (a + 1 - 1))))
        else
          .ok (SudoRt.Flow.cont (Int.ofNat (a + 1),
            embedGrid (colsDone colTurnV10 G (a + 1 - 1)))) := by
    intro a h1 h13
    obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    exact sumColsStep_hit (colsDone colTurnV10 G m) (m + 1) h13
  have hrun := chain_loop (sumColsStep 13) (fun σ => pure σ.2) (fun r => pure r)
    (fun a => embedGrid (colsDone colTurnV10 G (a - 1))) 1 13 (by decide) hstep
    (.ok (embedGrid (colsDone colTurnV10 G 13))) rfl
  have hcast :
      SudoRt.runLoopOn (ρ := Array (Array Int)) ((1 : Int), embedGrid G) fuelCols
          (sumColsStep 13) (fun σ => pure σ.2) (fun r => pure r) =
        SudoRt.runLoopOn (Int.ofNat 1, embedGrid (colsDone colTurnV10 G (1 - 1)))
          (fuelRange (Int.ofNat 1) (Int.ofNat 13)) (sumColsStep 13)
          (fun σ => pure σ.2) (fun r => pure r) := by
    rw [fuelCols_eq]
    rfl
  exact hcast.trans hrun

/-- `sum_ranks` refines the v10 `sumRanksV10` on every grid (no card bound:
v10 turn amounts stay small). -/
theorem sum_ranks_refines (g : Grid Nat) :
    Doubledeal.sum_ranks (embedGrid g) = .ok (embedGrid (sumRanksV10 g)) := by
  unfold Doubledeal.sum_ranks
  rw [sum_rows_refines]
  simp only [ok_bind]
  rw [sum_columns_refines]
  rfl

end DoubleDeal.Link2
