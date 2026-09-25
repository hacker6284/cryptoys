/-
  LINK 2. Empty grid, lay/scoop column-major and row-major.
-/
import Doubledeal
import DoubleDeal.Concrete
import DoubleDeal.Grid
import DoubleDeal.SumRanks
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Loop
import DoubleDeal.Link2.Deck
import DoubleDeal.Link2.Shift

namespace DoubleDeal.Link2

def repInt (n : Nat) (v : Int) : Array Int :=
  Array.mk (List.replicate n v)

theorem repInt_zero (v : Int) : repInt 0 v = #[] := rfl

theorem repInt_push (n : Nat) (v : Int) :
    (repInt n v).push v = repInt (n + 1) v := by
  simp only [repInt, Array.push]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate, List.concat_eq_append, List.append_assoc] at ih ⊢
    -- replicate (n+1) = v :: replicate n; appending v
    simpa [List.replicate, List.concat_eq_append] using
      congrArg (List.cons v) (by
        have h : List.replicate n v ++ [v] = List.replicate (n + 1) v := by
          simpa [repInt, Array.push, List.concat_eq_append] using congrArg Array.toList ih
        simpa [List.replicate] using h)

def blankRows (n : Nat) : Array (Array Int) :=
  Array.mk (List.replicate n (repInt 13 (-1)))

theorem blankRows_push (n : Nat) :
    (blankRows n).push (repInt 13 (-1)) = blankRows (n + 1) := by
  simp only [blankRows, Array.push, repInt]
  induction n with
  | zero => rfl
  | succ n ih =>
    apply congrArg Array.mk
    simp only [List.replicate, List.concat_eq_append]
    exact congrArg (List.cons (Array.mk (List.replicate 13 (-1))))
      (by simpa [blankRows, Array.push, List.concat_eq_append, repInt] using congrArg Array.toList ih)

def negRowStep (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array (Array Int))) :=
  let c := σ.1
  let row := σ.2
  do
    if c > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (c, row))
    else
      match ← ((do
        let _t34 ← SudoRt.negI (1 : Int)
        let _mb35 := SudoRt.appendL row _t34
        let ⟨_nr36, _⟩ := _mb35
        let row := _nr36
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) row)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (c, _fs))
      | .cont _fs =>
          if (c == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (c, _fs))
          else do
            let i' ← SudoRt.addI c (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', _fs))

theorem negRowStep_hit (c : Nat) (hc : c ≤ 12) :
    negRowStep 12 (Int.ofNat c, repInt c (-1)) =
      if c = 12 then
        .ok (SudoRt.Flow.brk (Int.ofNat c, repInt (c + 1) (-1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (c + 1), repInt (c + 1) (-1))) := by
  unfold negRowStep
  rw [if_neg (show ¬ Int.ofNat c > (12 : Int) from ofNat_not_gt hc)]
  simp only [negI_one, ok_bind, appendL_spec, repInt_push]
  by_cases heq : c = 12
  · subst heq
    simp only [ok_bind]
    have hbeq : ((12 : Int) == (12 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat c) == (12 : Int)) = false := by
      cases hb : (Int.ofNat c) == (12 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one c (fits_succ_lt (by omega : c < 12) (by decide : 12 ≤ 52))]
    simp [ok_bind, heq]

theorem neg_row_loop (onRet : Array (Array Int) → Except SudoRt.Trap (Array Int)) :
    SudoRt.runLoopOn (Int.ofNat 0, repInt 0 (-1))
      (fuelRange (Int.ofNat 0) (Int.ofNat 12))
      (negRowStep 12)
      (fun σ => pure σ.2) onRet =
      .ok (repInt 13 (-1)) := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 12 →
      negRowStep 12 (Int.ofNat i, repInt i (-1)) =
        if i = 12 then .ok (SudoRt.Flow.brk (Int.ofNat i, repInt (i + 1) (-1)))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), repInt (i + 1) (-1))) :=
    fun i _ hi => negRowStep_hit i hi
  have hrun := chain_loop (negRowStep 12)
    (fun σ => pure σ.2) onRet
    (fun i => repInt i (-1)) 0 12 (Nat.zero_le _) hstep
    (pure (repInt 13 (-1))) rfl
  simpa [Pure.pure, Except.pure, repInt_zero] using hrun

def emptyOuterStep (toV : Int) (σ : Int × Array (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array (Array Int)) (Array (Array Int))) :=
  let r := σ.1
  let g := σ.2
  do
    if r > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (r, g))
    else
      match ← ((do
        let row ← (SudoRt.runLoopOn (ρ := Array (Array Int)) ((0 : Int), (#[] : Array Int))
          (if (0 : Int) > 12 then 1 else ((12 : Int) - 0).natAbs + 1)
          (negRowStep 12)
          (fun σ => pure σ.2) (fun _ => pure (#[] : Array Int)))
        let _mb := SudoRt.appendL g row
        let ⟨g', _⟩ := _mb
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) g')
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (r, _fs))
      | .cont _fs =>
          if (r == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (r, _fs))
          else do
            let i' ← SudoRt.addI r (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', _fs))

theorem empty_rows_as_loop :
    Doubledeal.empty_rows =
      (do
        let g := (#[] : Array (Array Int))
        let _fromV := (0 : Int)
        let _toV := (3 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) (_fromV, g) fuel
          (emptyOuterStep _toV)
          (fun σ => pure σ.2)
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.empty_rows
  rfl

theorem emptyOuterStep_hit (r : Nat) (hr : r ≤ 3) :
    emptyOuterStep 3 (Int.ofNat r, blankRows r) =
      if r = 3 then
        .ok (SudoRt.Flow.brk (Int.ofNat r, blankRows (r + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (r + 1), blankRows (r + 1))) := by
  unfold emptyOuterStep
  rw [if_neg (show ¬ Int.ofNat r > (3 : Int) from ofNat_not_gt hr)]
  have hfuel : (if (0 : Int) > (12 : Int) then 1 else ((12 : Int) - 0).natAbs + 1) =
      fuelRange (Int.ofNat 0) (Int.ofNat 12) := by
    rw [fuelRange_le (Nat.zero_le _)]
    decide
  simp only [hfuel]
  have hrow := neg_row_loop (fun _ => pure (#[] : Array Int))
  have hsame :
      SudoRt.runLoopOn ((0 : Int), (#[] : Array Int))
        (fuelRange (Int.ofNat 0) (Int.ofNat 12)) (negRowStep 12)
        (fun σ => pure σ.2) (fun _ => pure (#[] : Array Int)) =
      SudoRt.runLoopOn (Int.ofNat 0, repInt 0 (-1))
        (fuelRange (Int.ofNat 0) (Int.ofNat 12)) (negRowStep 12)
        (fun σ => pure σ.2) (fun _ => pure (#[] : Array Int)) := by
    simp [repInt_zero]
  rw [← hsame] at hrow
  rw [hrow]
  simp only [ok_bind, appendL_spec, blankRows_push]
  by_cases heq : r = 3
  · subst heq
    simp only [ok_bind]
    have hbeq : ((3 : Int) == (3 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat r) == (3 : Int)) = false := by
      cases hb : (Int.ofNat r) == (3 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one r (fits_succ_lt (by omega : r < 3) (by decide : 3 ≤ 52))]
    simp [ok_bind, heq]

theorem empty_rows_spec :
    Doubledeal.empty_rows = .ok (blankRows 4) := by
  rw [empty_rows_as_loop]
  have hfuel : (if (0 : Int) > (3 : Int) then 1 else ((3 : Int) - 0).natAbs + 1) =
      fuelRange (Int.ofNat 0) (Int.ofNat 3) := by
    rw [fuelRange_le (Nat.zero_le _)]
    decide
  have h0 : blankRows 0 = (#[] : Array (Array Int)) := rfl
  simp only [hfuel, except_bind_pure]
  have hstep : ∀ i, 0 ≤ i → i ≤ 3 →
      emptyOuterStep 3 (Int.ofNat i, blankRows i) =
        if i = 3 then .ok (SudoRt.Flow.brk (Int.ofNat i, blankRows (i + 1)))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), blankRows (i + 1))) :=
    fun i _ hi => emptyOuterStep_hit i hi
  have hrun := chain_loop (emptyOuterStep 3)
    (fun σ => pure σ.2) (fun r => pure r)
    (fun i => blankRows i) 0 3 (Nat.zero_le _) hstep
    (pure (blankRows 4)) rfl
  simpa [h0, Pure.pure, Except.pure] using hrun

/-- Column-major lay of the first `n` cards; unread seats stay `-1`. -/
def layCell (d : List Nat) (n r c : Nat) : Int :=
  let k := r + 4 * c
  if h : k < n ∧ k < d.length then Int.ofNat (d[k]'h.2) else -1

def layPartial (d : List Nat) (n : Nat) : Fin 4 → Fin 13 → Int :=
  fun r c => layCell d n r.val c.val

def embedRowI (f : Fin 13 → Int) : Array Int :=
  Array.mk (toList13 f)

def embedGridI (g : Fin 4 → Fin 13 → Int) : Array (Array Int) :=
  #[embedRowI (g 0), embedRowI (g 1), embedRowI (g 2), embedRowI (g 3)]

theorem toList13_replicate_neg :
    toList13 (fun _ : Fin 13 => (-1 : Int)) = List.replicate 13 (-1) := by
  decide

theorem embedGridI_blank (d : List Nat) :
    embedGridI (layPartial d 0) = blankRows 4 := by
  have hrow : embedRowI (fun _ : Fin 13 => (-1 : Int)) = repInt 13 (-1) := by
    simp [embedRowI, repInt, layCell, toList13_replicate_neg]
  have hfun : layPartial d 0 = fun _ _ => (-1 : Int) := by
    funext r c
    simp [layPartial, layCell]
  simp [embedGridI, hfun, hrow, blankRows, repInt]

def layStep (d : Array Int) (toV : Int) (σ : Int × Array (Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array (Array Int)) (Array (Array Int))) :=
  let k := σ.1
  let g := σ.2
  do
    if k > toV then
      pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (k, g))
    else
      match ← ((do
        let r ← SudoRt.modI k (4 : Int)
        let c ← SudoRt.divI k (4 : Int)
        let row ← SudoRt.atL g r
        let card ← SudoRt.atL d k
        let row ← SudoRt.putL row c card
        let g ← SudoRt.putL g r row
        pure (SudoRt.Flow.cont (ρ := Array (Array Int)) g)
      ) : Except SudoRt.Trap (SudoRt.Flow _ (Array (Array Int)))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array (Array Int)) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (k, _fs))
      | .cont _fs =>
          if (k == toV) = true then
            pure (SudoRt.Flow.brk (ρ := Array (Array Int)) (k, _fs))
          else do
            let i' ← SudoRt.addI k (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array (Array Int)) (i', _fs))

theorem lay_cm_as_loop (d : Array Int) :
    Doubledeal.lay_cm d =
      (do
        let g ← Doubledeal.empty_rows
        let _fromV := (0 : Int)
        let _toV := (51 : Int)
        let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
        let _out ← (SudoRt.runLoopOn (ρ := Array (Array Int)) (_fromV, g) fuel
          (layStep d _toV)
          (fun σ => pure σ.2)
          (fun r => pure r))
        pure _out) := by
  unfold Doubledeal.lay_cm
  rfl

theorem embedRowI_size (f : Fin 13 → Int) : (embedRowI f).size = 13 := by
  simp [embedRowI, length_toList13]

theorem embedGridI_size (g : Fin 4 → Fin 13 → Int) : (embedGridI g).size = 4 := by
  simp [embedGridI]

theorem embedRowI_get (f : Fin 13 → Int) (i : Fin 13) :
    (embedRowI f)[i.val]'(by rw [embedRowI_size]; exact i.isLt) = f i :=
  getElem_toList13 f i

theorem embedGridI_get (g : Fin 4 → Fin 13 → Int) (r : Fin 4) :
    (embedGridI g)[r.val]'(by rw [embedGridI_size]; exact r.isLt) = embedRowI (g r) := by
  revert r; intro ⟨v, hv⟩
  match v with
  | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
  | n + 4 => omega

def setRowI (g : Fin 4 → Fin 13 → Int) (r : Fin 4) (row : Fin 13 → Int) :
    Fin 4 → Fin 13 → Int :=
  fun r' => if r' = r then row else g r'

theorem embedRowI_set (f : Fin 13 → Int) (c : Nat) (v : Int)
    (hsz : c < (embedRowI f).size) :
    (embedRowI f).set ⟨c, hsz⟩ v =
      embedRowI (fun i => if i.val = c then v else f i) := by
  have hc : c < 13 := by simpa [embedRowI_size] using hsz
  apply Array.ext'
  simp only [embedRowI, Array.toList_set]
  apply List.ext_getElem
  · simp [length_toList13, List.length_set]
  · intro j hj hj'
    have hj13 : j < 13 := by simpa [length_toList13] using hj'
    rw [List.getElem_set]
    by_cases heq : c = j
    · simp only [heq, ↓reduceIte]
      simpa using (getElem_toList13 (fun i => if i.val = j then v else f i) ⟨j, hj13⟩).symm
    · simp only [heq, ↓reduceIte]
      rw [getElem_toList13 f ⟨j, hj13⟩]
      have hne : (⟨j, hj13⟩ : Fin 13).val ≠ c := by simpa using Ne.symm heq
      simpa [hne] using (getElem_toList13 (fun i => if i.val = c then v else f i) ⟨j, hj13⟩).symm

theorem embedGridI_setRow (g : Fin 4 → Fin 13 → Int) (r : Nat)
    (row : Fin 13 → Int) (hsz : r < (embedGridI g).size) :
    (embedGridI g).set ⟨r, hsz⟩ (embedRowI row) =
      embedGridI (setRowI g ⟨r, by simpa [embedGridI_size] using hsz⟩ row) := by
  have hr : r < 4 := by simpa [embedGridI_size] using hsz
  apply Array.ext'
  simp only [embedGridI, Array.toList_set]
  apply List.ext_getElem
  · simp [List.length_set]
  · intro j hj hj'
    have hj4 : j < 4 := by simpa using hj
    have hcase : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hcase with rfl | rfl | rfl | rfl
    · rw [List.getElem_set]
      by_cases heq : r = 0
      · simp [heq, setRowI]
      · have hfin : ¬ ((0 : Fin 4) = ⟨r, hr⟩) := fun h => heq (Fin.ext_iff.mp h).symm
        simp [heq, hfin, setRowI]
    · rw [List.getElem_set]
      by_cases heq : r = 1
      · simp [heq, setRowI]
      · have hfin : ¬ ((1 : Fin 4) = ⟨r, hr⟩) := fun h => heq (Fin.ext_iff.mp h).symm
        simp [heq, hfin, setRowI]
    · rw [List.getElem_set]
      by_cases heq : r = 2
      · simp [heq, setRowI]
      · have hfin : ¬ ((2 : Fin 4) = ⟨r, hr⟩) := fun h => heq (Fin.ext_iff.mp h).symm
        simp [heq, hfin, setRowI]
    · rw [List.getElem_set]
      by_cases heq : r = 3
      · simp [heq, setRowI]
      · have hfin : ¬ ((3 : Fin 4) = ⟨r, hr⟩) := fun h => heq (Fin.ext_iff.mp h).symm
        simp [heq, hfin, setRowI]

theorem layCell_succ (d : List Nat) (k : Nat) (hk : k < d.length) (r c : Nat) :
    layCell d (k + 1) r c =
      if r + 4 * c = k then Int.ofNat (d[k]'hk) else layCell d k r c := by
  unfold layCell
  by_cases heq : r + 4 * c = k
  · simp [heq, hk]
  · by_cases hlt : r + 4 * c < k
    · simp [heq, hlt, Nat.lt_succ_of_lt hlt]
    · have hge : ¬ r + 4 * c < k + 1 := by omega
      simp [heq, hlt, hge]

theorem layPartial_succ (d : List Nat) (k : Nat) (hk : k < d.length) (hk52 : k < 52) :
    layPartial d (k + 1) =
      setRowI (layPartial d k) ⟨k % 4, Nat.mod_lt _ (by decide)⟩
        (fun c => if c.val = k / 4 then Int.ofNat (d[k]'hk) else layPartial d k ⟨k % 4, Nat.mod_lt _ (by decide)⟩ c) := by
  funext r c
  have hdiv : (k % 4) + 4 * (k / 4) = k := Nat.mod_add_div k 4
  have hr4 : r.val < 4 := r.isLt
  by_cases hrow : r = ⟨k % 4, Nat.mod_lt _ (by decide)⟩
  · subst hrow
    by_cases hcol : c.val = k / 4
    · have hkidx : (k % 4) + 4 * c.val = k := by rw [hcol, hdiv]
      rw [layPartial, setRowI]
      simp only [↓reduceIte, hcol]
      rw [layCell_succ d k hk (k % 4) (k / 4)]
      simp [hdiv]
    · have hne : (k % 4) + 4 * c.val ≠ k := by
        intro h
        have hc : c.val = k / 4 := by
          have hmul : 4 * c.val = 4 * (k / 4) := by
            have := congrArg (fun n => n - k % 4) h
            have hdiv' := hdiv
            omega
          exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) hmul
        exact hcol hc
      simp [layPartial, setRowI, hcol, layCell_succ d k hk (k % 4) c.val, hne]
  · have hr : r.val ≠ k % 4 := by
      intro h
      exact hrow (Fin.ext h)
    have hne : r.val + 4 * c.val ≠ k := by
      intro h
      have : (r.val + 4 * c.val) % 4 = k % 4 := by rw [h]
      have hmod : (r.val + 4 * c.val) % 4 = r.val := by
        rw [Nat.mul_comm 4 c.val, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr4]
      exact hr (hmod.symm.trans this)
    simp [layPartial, setRowI, hrow, layCell_succ d k hk r.val c.val, hne]

theorem layStep_hit (d : List Nat) (hd : d.length = 52) (k : Nat) (hk : k ≤ 51) :
    layStep (embed d) 51 (Int.ofNat k, embedGridI (layPartial d k)) =
      if k = 51 then
        .ok (SudoRt.Flow.brk (Int.ofNat k, embedGridI (layPartial d (k + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (k + 1), embedGridI (layPartial d (k + 1)))) := by
  unfold layStep
  dsimp only
  rw [if_neg (show ¬ Int.ofNat k > (51 : Int) from ofNat_not_gt hk)]
  rw [show (4 : Int) = Int.ofNat 4 from rfl]
  rw [modI_ofNat k (by decide : (4 : Nat) ≠ 0), divI_ofNat k (by decide : (4 : Nat) ≠ 0)]
  simp only [ok_bind]
  have hr4 : k % 4 < 4 := Nat.mod_lt _ (by decide)
  have hc13 : k / 4 < 13 := by
    have hle : 4 * (k / 4) ≤ k := Nat.mul_div_le k 4
    have : 4 * (k / 4) < 4 * 13 := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hatG := atL_ofNat (embedGridI (layPartial d k)) (k % 4)
    (by rw [embedGridI_size]; exact hr4)
  have hrow := embedGridI_get (layPartial d k) ⟨k % 4, hr4⟩
  have hatG' :
      (embedGridI (layPartial d k))[k % 4]'(by rw [embedGridI_size]; exact hr4) =
        embedRowI (layPartial d k ⟨k % 4, hr4⟩) := by simpa using hrow
  rw [hatG'] at hatG
  simp only [hatG, ok_bind]
  have hatD := atL_embed d k (by rw [hd]; omega)
  rw [hatD]
  simp only [ok_bind]
  have hszR : k / 4 < (embedRowI (layPartial d k ⟨k % 4, hr4⟩)).size := by
    rw [embedRowI_size]; exact hc13
  have hputR := putL_ofNat (embedRowI (layPartial d k ⟨k % 4, hr4⟩)) (k / 4)
    (Int.ofNat (d[k]'(by rw [hd]; omega))) hszR
  rw [hputR]
  simp only [ok_bind]
  rw [embedRowI_set (layPartial d k ⟨k % 4, hr4⟩) (k / 4)
    (Int.ofNat (d[k]'(by rw [hd]; omega))) hszR]
  have hszG : k % 4 < (embedGridI (layPartial d k)).size := by
    rw [embedGridI_size]; exact hr4
  have hputG := putL_ofNat (embedGridI (layPartial d k)) (k % 4)
    (embedRowI (fun i => if i.val = k / 4 then Int.ofNat (d[k]'(by rw [hd]; omega)) else
        layPartial d k ⟨k % 4, hr4⟩ i))
    hszG
  rw [hputG]
  simp only [ok_bind]
  rw [embedGridI_setRow (layPartial d k) (k % 4)
    (fun i => if i.val = k / 4 then Int.ofNat (d[k]'(by rw [hd]; omega)) else
        layPartial d k ⟨k % 4, hr4⟩ i) hszG]
  have hpartial := layPartial_succ d k (by rw [hd]; omega) (by omega)
  simp only [hpartial]
  by_cases heq : k = 51
  · subst heq
    simp only [ok_bind]
    have hbeq : ((51 : Int) == (51 : Int)) = true := by decide
    simp [hbeq, Pure.pure, Except.pure]
  · simp only [Pure.pure, Except.pure, ok_bind]
    have hbeq : ((Int.ofNat k) == (51 : Int)) = false := by
      cases hb : (Int.ofNat k) == (51 : Int) with
      | false => rfl
      | true =>
        exact absurd (Int.ofNat.inj (by simpa [ofNat_eq_natCast] using (beq_int_iff _ _).mp hb)) heq
    simp only [hbeq, ↓reduceIte]
    rw [addI_ofNat_one k (fits_succ_lt (by omega : k < 51) (by decide : 51 ≤ 52))]
    simp [ok_bind, heq]

theorem toList13_ofNat (g : Fin 13 → Nat) :
    (toList13 g).map Int.ofNat = toList13 (fun i => Int.ofNat (g i)) := by
  simp [toList13]

theorem embedGrid_ofNat (g : Grid Nat) :
    embedGrid g = embedGridI (fun r c => Int.ofNat (g r c)) := by
  simp [embedGrid, embedGridI, embed, embedRowI, toList13_ofNat]

theorem layPartial_lay (d : List Nat) (h : d.length = 52) :
    layPartial d 52 = fun r c => Int.ofNat (layColumnMajor (ofDeck d h) r c) := by
  funext r c
  have hr := r.isLt
  have hc := c.isLt
  have hk : r.val + 4 * c.val < 52 := by omega
  have hlen : r.val + 4 * c.val < d.length := by rw [h]; exact hk
  simp [layPartial, layCell, hlen, hk, layColumnMajor, cmFlat, ofDeck]

theorem lay_cm_loop (d : List Nat) (h : d.length = 52) :
    SudoRt.runLoopOn (Int.ofNat 0, embedGridI (layPartial d 0))
      (fuelRange (Int.ofNat 0) (Int.ofNat 51))
      (layStep (embed d) 51)
      (fun σ => pure σ.2) (fun r => pure r) =
      .ok (embedGridI (layPartial d 52)) := by
  have hstep : ∀ i, 0 ≤ i → i ≤ 51 →
      layStep (embed d) 51 (Int.ofNat i, embedGridI (layPartial d i)) =
        if i = 51 then .ok (SudoRt.Flow.brk (Int.ofNat i, embedGridI (layPartial d (i + 1))))
        else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embedGridI (layPartial d (i + 1)))) :=
    fun i _ hi => layStep_hit d h i hi
  have hrun := chain_loop (layStep (embed d) 51)
    (fun σ => pure σ.2) (fun r => pure r)
    (fun i => embedGridI (layPartial d i)) 0 51 (Nat.zero_le _) hstep
    (pure (embedGridI (layPartial d 52))) rfl
  simpa [Pure.pure, Except.pure] using hrun

theorem lay_cm_refines (d : List Nat) (h : d.length = 52) :
    Doubledeal.lay_cm (embed d) =
      .ok (embedGrid (layColumnMajor (ofDeck d h))) := by
  rw [lay_cm_as_loop, empty_rows_spec]
  simp only [ok_bind]
  have hfuel : (if (0 : Int) > (51 : Int) then 1 else ((51 : Int) - 0).natAbs + 1) =
      fuelRange (Int.ofNat 0) (Int.ofNat 51) := by
    rw [fuelRange_le (Nat.zero_le _)]
    decide
  simp only [hfuel, except_bind_pure]
  have hloop := lay_cm_loop d h
  have hstart :
      SudoRt.runLoopOn ((0 : Int), blankRows 4) (fuelRange (Int.ofNat 0) (Int.ofNat 51))
        (layStep (embed d) 51) (fun σ => pure σ.2) (fun r => pure r) =
      SudoRt.runLoopOn (Int.ofNat 0, embedGridI (layPartial d 0))
        (fuelRange (Int.ofNat 0) (Int.ofNat 51))
        (layStep (embed d) 51) (fun σ => pure σ.2) (fun r => pure r) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl, embedGridI_blank d]
  rw [hstart, hloop, layPartial_lay d h, embedGrid_ofNat]

end DoubleDeal.Link2
