/-
  LINK 2. `Generated.compose` refines algebraic `compose` on `PosWf`.

  A generated position is well-formed when the four cubie tables have the
  SPEC lengths (20/20/30/30), every entry is nonnegative, permutation
  entries are in-range indices, and orientations lie in `0..2` / `0..1`.
  Those Nats fit in an i64, so `atL` / `addI` / `modI` do not trap.

  Algebraic Link 2 only. Not `v_Hash`. Not emitter soundness.
  Not collision resistance.
-/
import Megadreifach
import MegaDreifach.Group
import MegaDreifach.Link2.Loop

namespace MegaDreifach.Link2

/-! ## List prefixes -/

private def natMap (f : Nat → Nat) (n : Nat) : List Nat :=
  (List.range n).map f

private theorem natMap_take (f : Nat → Nat) (k n : Nat) (hk : k ≤ n) :
    (natMap f n).take k = natMap f k := by
  unfold natMap
  rw [← List.map_take, List.take_range, Nat.min_eq_left hk]

private theorem natMap_succ (f : Nat → Nat) (k : Nat) :
    natMap f (k + 1) = natMap f k ++ [f k] := by
  simp [natMap, List.range_succ, List.map_append, List.map_singleton]

private theorem push_embed (xs : List Nat) (b : Nat) :
    (embed xs).push (Int.ofNat b) = embed (xs ++ [b]) := by
  apply Array.ext'
  simp [embed, toList_push]

private theorem embed_take_push (f : Nat → Nat) (n i : Nat) (hi : i < n) :
    (embed ((natMap f n).take i)).push (Int.ofNat (f i)) =
      embed ((natMap f n).take (i + 1)) := by
  rw [push_embed, natMap_take f i n (Nat.le_of_lt hi),
    natMap_take f (i + 1) n (Nat.succ_le_of_lt hi), natMap_succ]

private theorem take_all {α : Type _} (xs : List α) {n : Nat} (h : xs.length = n) :
    xs.take n = xs := by
  rw [← h, List.take_length]

private theorem fits_le (n k : Nat) (hk : k ≤ n) (hn : FitsLen n) : FitsLen k :=
  FitsLen.of_le hn hk

private theorem fits4 : FitsLen 4 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits2 : FitsLen 2 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits_sum3 (a b : Fin 3) : FitsLen (a.val + b.val) := by
  have ha := a.isLt
  have hb := b.isLt
  exact fits_le 4 (a.val + b.val) (by omega) fits4

private theorem fits_sum2 (a b : Fin 2) : FitsLen (a.val + b.val) := by
  have ha := a.isLt
  have hb := b.isLt
  exact fits_le 2 (a.val + b.val) (by omega) fits2

private theorem fuel_0_19 : fuelRange (0 : Int) (19 : Int) = 20 := by
  unfold fuelRange
  decide

private theorem fuel_0_29 : fuelRange (0 : Int) (29 : Int) = 30 := by
  unfold fuelRange
  decide

/-! ## Reading embedded `Fin` tables -/

private theorem coe_int (n : Nat) : (n : Int) = Int.ofNat n := rfl

private theorem atL_listOf {n : Nat} (f : Fin n → Fin n) (i : Nat) (hi : i < n) :
    SudoRt.atL (embed (listOf f)) (Int.ofNat i) =
      .ok (Int.ofNat (f ⟨i, hi⟩).val) := by
  have hlen : i < (listOf f).length := by rw [listOf_length]; exact hi
  rw [atL_embed (listOf f) i hlen]
  simp [listOf, List.getElem_map, List.getElem_range, hi]

private theorem atL_listOfOri {n m : Nat} (f : Fin n → Fin m) (i : Nat) (hi : i < n) :
    SudoRt.atL (embed (listOfOri f)) (Int.ofNat i) =
      .ok (Int.ofNat (f ⟨i, hi⟩).val) := by
  have hlen : i < (listOfOri f).length := by rw [listOfOri_length]; exact hi
  rw [atL_embed (listOfOri f) i hlen]
  simp [listOfOri, List.getElem_map, List.getElem_range, hi]

private theorem listOf_bound {n : Nat} (f : Fin n → Fin n) {x : Nat}
    (hx : x ∈ listOf f) : x < n := by
  rw [listOf, List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [List.mem_range] at hi
  simp [hi]

private theorem listOfOri_bound {n m : Nat} (f : Fin n → Fin m) {x : Nat}
    (hx : x ∈ listOfOri f) : x < m := by
  rw [listOfOri, List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [List.mem_range] at hi
  simp [hi]

/-! ## Position bridge -/

/-- Algebraic position → emitted tables. Lengths are 20/20/30/30 and every
    entry is a `Fin` value, so it is an i64-safe index for `compose`. -/
def embedPos (p : Position) : Megadreifach.Position where
  sudo_8Position_2cp := embed (listOf p.cp)
  sudo_8Position_2co := embed (listOfOri p.co)
  sudo_8Position_2ep := embed (listOf p.ep)
  sudo_8Position_2eo := embed (listOfOri p.eo)

/-- Trap-free domain for `Generated.compose`.

    `cp` / `ep` entries are legal indices into a length-20 / length-30 table.
    `co` / `eo` entries lie in `0..2` / `0..1`, so the orientation sums
    (`< 6` and `< 4`) fit in an i64 and `modI` agrees with `Fin` addition.
    Nonnegativity stops `Int.toNat` from hiding a negative index. -/
structure PosWf (p : Megadreifach.Position) : Prop where
  cpLen : p.sudo_8Position_2cp.size = 20
  coLen : p.sudo_8Position_2co.size = 20
  epLen : p.sudo_8Position_2ep.size = 30
  eoLen : p.sudo_8Position_2eo.size = 30
  cpNn : Nonneg p.sudo_8Position_2cp
  coNn : Nonneg p.sudo_8Position_2co
  epNn : Nonneg p.sudo_8Position_2ep
  eoNn : Nonneg p.sudo_8Position_2eo
  cpB : ∀ x ∈ decode p.sudo_8Position_2cp, x < 20
  coB : ∀ x ∈ decode p.sudo_8Position_2co, x < 3
  epB : ∀ x ∈ decode p.sudo_8Position_2ep, x < 30
  eoB : ∀ x ∈ decode p.sudo_8Position_2eo, x < 2

theorem posWf_embed (p : Position) : PosWf (embedPos p) where
  cpLen := by simp [embedPos, size_embed, listOf_length]
  coLen := by simp [embedPos, size_embed, listOfOri_length]
  epLen := by simp [embedPos, size_embed, listOf_length]
  eoLen := by simp [embedPos, size_embed, listOfOri_length]
  cpNn := by simpa [embedPos] using nonneg_embed (listOf p.cp)
  coNn := by simpa [embedPos] using nonneg_embed (listOfOri p.co)
  epNn := by simpa [embedPos] using nonneg_embed (listOf p.ep)
  eoNn := by simpa [embedPos] using nonneg_embed (listOfOri p.eo)
  cpB := by
    rw [embedPos, decode_embed]
    exact fun _ hx => listOf_bound p.cp hx
  coB := by
    rw [embedPos, decode_embed]
    exact fun _ hx => listOfOri_bound p.co hx
  epB := by
    rw [embedPos, decode_embed]
    exact fun _ hx => listOf_bound p.ep hx
  eoB := by
    rw [embedPos, decode_embed]
    exact fun _ hx => listOfOri_bound p.eo hx

/-- Table lengths are i64-safe (they are 20 or 30). -/
theorem PosWf.lengths_fit (p : Megadreifach.Position) (h : PosWf p) :
    FitsLen p.sudo_8Position_2cp.size ∧ FitsLen p.sudo_8Position_2co.size ∧
    FitsLen p.sudo_8Position_2ep.size ∧ FitsLen p.sudo_8Position_2eo.size := by
  have h30 : FitsLen 30 := by unfold FitsLen i64MaxNat; decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fits_le 30 _ (by rw [h.cpLen]; decide) h30
  · exact fits_le 30 _ (by rw [h.coLen]; decide) h30
  · rw [h.epLen]; exact h30
  · rw [h.eoLen]; exact h30

private theorem decode_length (a : Array Int) : (decode a).length = a.size := by
  simp [decode]

private def decLen (a : Array Int) {n : Nat} (h : a.size = n) :
    (decode a).length = n :=
  (decode_length a).trans h

private def nthFin {n : Nat} (xs : List Nat) (hlen : xs.length = n)
    (hb : ∀ x ∈ xs, x < n) (i : Fin n) : Fin n :=
  have hi : i.val < xs.length := by rw [hlen]; exact i.isLt
  ⟨xs[i.val], hb _ (List.getElem_mem hi)⟩

private def nthOri {n m : Nat} (xs : List Nat) (hlen : xs.length = n)
    (hb : ∀ x ∈ xs, x < m) (i : Fin n) : Fin m :=
  have hi : i.val < xs.length := by rw [hlen]; exact i.isLt
  ⟨xs[i.val], hb _ (List.getElem_mem hi)⟩

/-- Decode a well-formed generated position. -/
def decodePos (p : Megadreifach.Position) (h : PosWf p) : Position where
  cp := nthFin (decode p.sudo_8Position_2cp) (decLen _ h.cpLen) h.cpB
  co := nthOri (decode p.sudo_8Position_2co) (decLen _ h.coLen) h.coB
  ep := nthFin (decode p.sudo_8Position_2ep) (decLen _ h.epLen) h.epB
  eo := nthOri (decode p.sudo_8Position_2eo) (decLen _ h.eoLen) h.eoB

private theorem listOf_nthFin {n : Nat} (xs : List Nat) (hlen : xs.length = n)
    (hb : ∀ x ∈ xs, x < n) :
    listOf (nthFin xs hlen hb) = xs := by
  apply List.ext_getElem
  · simp [listOf, hlen]
  · intro i _ hi2
    have hi : i < n := by rw [hlen] at hi2; exact hi2
    simp [listOf, nthFin, List.getElem_map, List.getElem_range, hi, hlen]

private theorem listOfOri_nthOri {n m : Nat} (xs : List Nat) (hlen : xs.length = n)
    (hb : ∀ x ∈ xs, x < m) :
    listOfOri (nthOri xs hlen hb) = xs := by
  apply List.ext_getElem
  · simp [listOfOri, hlen]
  · intro i _ hi2
    have hi : i < n := by rw [hlen] at hi2; exact hi2
    simp [listOfOri, nthOri, List.getElem_map, List.getElem_range, hi, hlen]

private theorem gen_ext (a b : Megadreifach.Position)
    (h1 : a.sudo_8Position_2cp = b.sudo_8Position_2cp)
    (h2 : a.sudo_8Position_2co = b.sudo_8Position_2co)
    (h3 : a.sudo_8Position_2ep = b.sudo_8Position_2ep)
    (h4 : a.sudo_8Position_2eo = b.sudo_8Position_2eo) : a = b := by
  cases a; cases b; simp_all

theorem embedPos_decode (p : Megadreifach.Position) (h : PosWf p) :
    embedPos (decodePos p h) = p := by
  apply gen_ext
  · have hlist := listOf_nthFin (decode p.sudo_8Position_2cp) (decLen _ h.cpLen) h.cpB
    simp [embedPos, decodePos, hlist, embed_decode _ h.cpNn]
  · have hlist := listOfOri_nthOri (decode p.sudo_8Position_2co) (decLen _ h.coLen) h.coB
    simp [embedPos, decodePos, hlist, embed_decode _ h.coNn]
  · have hlist := listOf_nthFin (decode p.sudo_8Position_2ep) (decLen _ h.epLen) h.epB
    simp [embedPos, decodePos, hlist, embed_decode _ h.epNn]
  · have hlist := listOfOri_nthOri (decode p.sudo_8Position_2eo) (decLen _ h.eoLen) h.eoB
    simp [embedPos, decodePos, hlist, embed_decode _ h.eoNn]

/-! ## Cells of algebraic `compose` -/

private def cpCell (g h : Position) (i : Nat) : Nat :=
  if hi : i < 20 then (h.cp (g.cp ⟨i, hi⟩)).val else 0

private def coCell (g h : Position) (i : Nat) : Nat :=
  if hi : i < 20 then (h.co (g.cp ⟨i, hi⟩) + g.co ⟨i, hi⟩).val else 0

private def epCell (g h : Position) (i : Nat) : Nat :=
  if hi : i < 30 then (h.ep (g.ep ⟨i, hi⟩)).val else 0

private def eoCell (g h : Position) (i : Nat) : Nat :=
  if hi : i < 30 then (h.eo (g.ep ⟨i, hi⟩) + g.eo ⟨i, hi⟩).val else 0

private def cpOut (g h : Position) : List Nat := listOf (compose g h).cp
private def coOut (g h : Position) : List Nat := listOfOri (compose g h).co
private def epOut (g h : Position) : List Nat := listOf (compose g h).ep
private def eoOut (g h : Position) : List Nat := listOfOri (compose g h).eo

private theorem cpOut_eq (g h : Position) : cpOut g h = natMap (cpCell g h) 20 := rfl
private theorem coOut_eq (g h : Position) : coOut g h = natMap (coCell g h) 20 := rfl
private theorem epOut_eq (g h : Position) : epOut g h = natMap (epCell g h) 30 := rfl
private theorem eoOut_eq (g h : Position) : eoOut g h = natMap (eoCell g h) 30 := rfl

private def cornerAcc (g h : Position) (i : Nat) : Array Int × Array Int :=
  (embed ((cpOut g h).take i), embed ((coOut g h).take i))

private def edgeAcc (g h : Position) (i : Nat) : Array Int × Array Int :=
  (embed ((epOut g h).take i), embed ((eoOut g h).take i))

private theorem cornerAcc_zero (g h : Position) :
    cornerAcc g h 0 = (#[], #[]) := by
  simp [cornerAcc, List.take_zero, embed_nil]

private theorem edgeAcc_zero (g h : Position) :
    edgeAcc g h 0 = (#[], #[]) := by
  simp [edgeAcc, List.take_zero, embed_nil]

private theorem cornerAcc_done (g h : Position) :
    cornerAcc g h 20 = (embed (cpOut g h), embed (coOut g h)) := by
  have hcp : (cpOut g h).length = 20 := by simp [cpOut, listOf_length]
  have hco : (coOut g h).length = 20 := by simp [coOut, listOfOri_length]
  unfold cornerAcc
  rw [take_all (cpOut g h) hcp, take_all (coOut g h) hco]

private theorem edgeAcc_done (g h : Position) :
    edgeAcc g h 30 = (embed (epOut g h), embed (eoOut g h)) := by
  have hep : (epOut g h).length = 30 := by simp [epOut, listOf_length]
  have heo : (eoOut g h).length = 30 := by simp [eoOut, listOfOri_length]
  unfold edgeAcc
  rw [take_all (epOut g h) hep, take_all (eoOut g h) heo]

private theorem cp_push (g h : Position) (i : Nat) (hi : i < 20) :
    (embed ((cpOut g h).take i)).push (h.cp (g.cp ⟨i, hi⟩) : Int) =
      embed ((cpOut g h).take (i + 1)) := by
  have hc : (h.cp (g.cp ⟨i, hi⟩) : Nat) = cpCell g h i := by simp [cpCell, hi]
  have hint : (h.cp (g.cp ⟨i, hi⟩) : Int) = Int.ofNat (cpCell g h i) := by
    rw [← hc]; rfl
  rw [hint, cpOut_eq, embed_take_push (cpCell g h) 20 i hi]

private theorem co_push (g h : Position) (i : Nat) (hi : i < 20) :
    (embed (List.take i (coOut g h))).push
        ((↑((h.co (g.cp ⟨i, hi⟩) : Nat) + (g.co ⟨i, hi⟩ : Nat)) : Int) % (3 : Int)) =
      embed (List.take (i + 1) (coOut g h)) := by
  have hmod :
      ((↑((h.co (g.cp ⟨i, hi⟩) : Nat) + (g.co ⟨i, hi⟩ : Nat)) : Int) % (3 : Int)) =
        Int.ofNat (coCell g h i) := by
    change (↑(((h.co (g.cp ⟨i, hi⟩)).val + (g.co ⟨i, hi⟩).val) % 3) : Int) =
      Int.ofNat (coCell g h i)
    rw [coe_int]
    simp [coCell, hi, fin_val_add]
  rw [hmod, coOut_eq, embed_take_push (coCell g h) 20 i hi]

private theorem ep_push (g h : Position) (i : Nat) (hi : i < 30) :
    (embed ((epOut g h).take i)).push (h.ep (g.ep ⟨i, hi⟩) : Int) =
      embed ((epOut g h).take (i + 1)) := by
  have hc : (h.ep (g.ep ⟨i, hi⟩) : Nat) = epCell g h i := by simp [epCell, hi]
  have hint : (h.ep (g.ep ⟨i, hi⟩) : Int) = Int.ofNat (epCell g h i) := by
    rw [← hc]; rfl
  rw [hint, epOut_eq, embed_take_push (epCell g h) 30 i hi]

private theorem eo_push (g h : Position) (i : Nat) (hi : i < 30) :
    (embed (List.take i (eoOut g h))).push
        ((↑((h.eo (g.ep ⟨i, hi⟩) : Nat) + (g.eo ⟨i, hi⟩ : Nat)) : Int) % (2 : Int)) =
      embed (List.take (i + 1) (eoOut g h)) := by
  have hmod :
      ((↑((h.eo (g.ep ⟨i, hi⟩) : Nat) + (g.eo ⟨i, hi⟩ : Nat)) : Int) % (2 : Int)) =
        Int.ofNat (eoCell g h i) := by
    change (↑(((h.eo (g.ep ⟨i, hi⟩)).val + (g.eo ⟨i, hi⟩).val) % 2) : Int) =
      Int.ofNat (eoCell g h i)
    rw [coe_int]
    simp [eoCell, hi, fin_val_add]
  rw [hmod, eoOut_eq, embed_take_push (eoCell g h) 30 i hi]

/-! ## Corner loop (`s = 0` to `19`) -/

/-- One iteration of the emitted corner loop, in the shape `compose` leaves. -/
def cornerStep (g h : Megadreifach.Position) (toV : Int)
    (σ : Int × (Array Int × Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Array Int)) Megadreifach.Position) :=
  let s := σ.1
  let cp := σ.2.1
  let co := σ.2.2
  do
    if s > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, (cp, co)))
    else
      match ← ((do
        let gcp ← SudoRt.atL g.sudo_8Position_2cp s
        let hcp ← SudoRt.atL h.sudo_8Position_2cp gcp
        let cp := (SudoRt.appendL cp hcp).1
        let gcp2 ← SudoRt.atL g.sudo_8Position_2cp s
        let hco ← SudoRt.atL h.sudo_8Position_2co gcp2
        let gco ← SudoRt.atL g.sudo_8Position_2co s
        let sum ← SudoRt.addI hco gco
        let m ← SudoRt.modI sum (3 : Int)
        let co := (SudoRt.appendL co m).1
        pure (SudoRt.Flow.cont (ρ := Megadreifach.Position) (cp, co))
      ) : Except SudoRt.Trap (SudoRt.Flow _ Megadreifach.Position)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.Position) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, fs))
      | .cont fs => do
          if s == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, fs))
          else do
            let i' ← SudoRt.addI s (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.Position) (i', fs))

private theorem corner_do (g h : Position) (i : Nat) (hi : i < 20) :
    (do
      let gcp ← SudoRt.atL (embed (listOf g.cp)) (i : Int)
      let hcp ← SudoRt.atL (embed (listOf h.cp)) gcp
      let gcp2 ← SudoRt.atL (embed (listOf g.cp)) (i : Int)
      let hco ← SudoRt.atL (embed (listOfOri h.co)) gcp2
      let gco ← SudoRt.atL (embed (listOfOri g.co)) (i : Int)
      let sum ← SudoRt.addI hco gco
      let m ← SudoRt.modI sum (3 : Int)
      pure (SudoRt.Flow.cont
        ((SudoRt.appendL (embed (List.take i (cpOut g h))) hcp).1,
         (SudoRt.appendL (embed (List.take i (coOut g h))) m).1)) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int × Array Int) Megadreifach.Position)) =
    .ok (SudoRt.Flow.cont (cornerAcc g h (i + 1))) := by
  rw [coe_int i]
  rw [atL_listOf g.cp i hi, ok_bind]
  rw [atL_listOf h.cp (g.cp ⟨i, hi⟩).val (g.cp ⟨i, hi⟩).isLt, ok_bind]
  rw [ok_bind]
  rw [atL_listOfOri h.co (g.cp ⟨i, hi⟩).val (g.cp ⟨i, hi⟩).isLt, ok_bind]
  rw [atL_listOfOri g.co i hi, ok_bind]
  rw [addI_ofNat _ _ (fits_sum3 _ _), ok_bind]
  rw [show (3 : Int) = Int.ofNat 3 from rfl, modI_ofNat _ (by decide : 3 ≠ 0), ok_bind]
  rw [appendL_spec, appendL_spec]
  dsimp
  rw [cp_push g h i hi, co_push g h i hi]
  rfl

private theorem cornerStep_hit (g h : Position) (i : Nat) (hi : i ≤ 19) :
    cornerStep (embedPos g) (embedPos h) (19 : Int) (Int.ofNat i, cornerAcc g h i) =
      if i = 19 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, cornerAcc g h (i + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), cornerAcc g h (i + 1))) := by
  have hi20 : i < 20 := by omega
  unfold cornerStep embedPos cornerAcc
  dsimp
  have hngt : ¬ (i : Int) > (19 : Int) := ofNat_not_gt hi
  rw [if_neg hngt, corner_do g h i hi20, ok_bind]
  dsimp
  by_cases heq : i = 19
  · subst heq
    simp [beq_int_iff]
    rfl
  · have hneI : ¬ (i : Int) = (19 : Int) := fun h => heq (Int.ofNat.inj h)
    have hfits : FitsLen (i + 1) :=
      fits_le 20 (i + 1) (by omega) (by unfold FitsLen i64MaxNat; decide)
    have hadd := addI_ofNat_one i hfits
    rw [ofNat_eq_natCast i] at hadd
    rw [ite_int_beq, if_neg hneI, hadd, ok_bind, if_neg heq, coe_int (i + 1)]
    simp [cornerAcc]
    rfl

/-! ## Edge loop (`s = 0` to `29`) -/

/-- One iteration of the emitted edge loop. -/
def edgeStep (g h : Megadreifach.Position) (toV : Int)
    (σ : Int × (Array Int × Array Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Array Int)) Megadreifach.Position) :=
  let s := σ.1
  let ep := σ.2.1
  let eo := σ.2.2
  do
    if s > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, (ep, eo)))
    else
      match ← ((do
        let gep ← SudoRt.atL g.sudo_8Position_2ep s
        let hep ← SudoRt.atL h.sudo_8Position_2ep gep
        let ep := (SudoRt.appendL ep hep).1
        let gep2 ← SudoRt.atL g.sudo_8Position_2ep s
        let heo ← SudoRt.atL h.sudo_8Position_2eo gep2
        let geo ← SudoRt.atL g.sudo_8Position_2eo s
        let sum ← SudoRt.addI heo geo
        let m ← SudoRt.modI sum (2 : Int)
        let eo := (SudoRt.appendL eo m).1
        pure (SudoRt.Flow.cont (ρ := Megadreifach.Position) (ep, eo))
      ) : Except SudoRt.Trap (SudoRt.Flow _ Megadreifach.Position)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.Position) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, fs))
      | .cont fs => do
          if s == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, fs))
          else do
            let i' ← SudoRt.addI s (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.Position) (i', fs))

private theorem edge_do (g h : Position) (i : Nat) (hi : i < 30) :
    (do
      let gep ← SudoRt.atL (embed (listOf g.ep)) (i : Int)
      let hep ← SudoRt.atL (embed (listOf h.ep)) gep
      let gep2 ← SudoRt.atL (embed (listOf g.ep)) (i : Int)
      let heo ← SudoRt.atL (embed (listOfOri h.eo)) gep2
      let geo ← SudoRt.atL (embed (listOfOri g.eo)) (i : Int)
      let sum ← SudoRt.addI heo geo
      let m ← SudoRt.modI sum (2 : Int)
      pure (SudoRt.Flow.cont
        ((SudoRt.appendL (embed (List.take i (epOut g h))) hep).1,
         (SudoRt.appendL (embed (List.take i (eoOut g h))) m).1)) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int × Array Int) Megadreifach.Position)) =
    .ok (SudoRt.Flow.cont (edgeAcc g h (i + 1))) := by
  rw [coe_int i]
  rw [atL_listOf g.ep i hi, ok_bind]
  rw [atL_listOf h.ep (g.ep ⟨i, hi⟩).val (g.ep ⟨i, hi⟩).isLt, ok_bind]
  rw [ok_bind]
  rw [atL_listOfOri h.eo (g.ep ⟨i, hi⟩).val (g.ep ⟨i, hi⟩).isLt, ok_bind]
  rw [atL_listOfOri g.eo i hi, ok_bind]
  rw [addI_ofNat _ _ (fits_sum2 _ _), ok_bind]
  rw [show (2 : Int) = Int.ofNat 2 from rfl, modI_ofNat _ (by decide : 2 ≠ 0), ok_bind]
  rw [appendL_spec, appendL_spec]
  dsimp
  rw [ep_push g h i hi, eo_push g h i hi]
  rfl

private theorem edgeStep_hit (g h : Position) (i : Nat) (hi : i ≤ 29) :
    edgeStep (embedPos g) (embedPos h) (29 : Int) (Int.ofNat i, edgeAcc g h i) =
      if i = 29 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, edgeAcc g h (i + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), edgeAcc g h (i + 1))) := by
  have hi30 : i < 30 := by omega
  unfold edgeStep embedPos edgeAcc
  dsimp
  have hngt : ¬ (i : Int) > (29 : Int) := ofNat_not_gt hi
  rw [if_neg hngt, edge_do g h i hi30, ok_bind]
  dsimp
  by_cases heq : i = 29
  · subst heq
    simp [beq_int_iff]
    rfl
  · have hneI : ¬ (i : Int) = (29 : Int) := fun h => heq (Int.ofNat.inj h)
    have hfits : FitsLen (i + 1) :=
      fits_le 30 (i + 1) (by omega) (by unfold FitsLen i64MaxNat; decide)
    have hadd := addI_ofNat_one i hfits
    rw [ofNat_eq_natCast i] at hadd
    rw [ite_int_beq, if_neg hneI, hadd, ok_bind, if_neg heq, coe_int (i + 1)]
    simp [edgeAcc]
    rfl

/-- Edge loop plus the `Position` join. `cp` / `co` are the corner results. -/
def edgeAfter (g h : Megadreifach.Position) (cp co : Array Int) :
    Except SudoRt.Trap Megadreifach.Position :=
  do
    let ep := (#[] : Array Int)
    let eo := (#[] : Array Int)
    let _fromV := (0 : Int)
    let _toV := (29 : Int)
    let fuel : Nat := if _fromV > _toV then 1 else (_toV - _fromV).natAbs + 1
    let _out ← (SudoRt.runLoopOn (ρ := Megadreifach.Position) (_fromV, (ep, eo)) fuel
      (edgeStep g h _toV)
      (fun σ =>
        let ep := σ.2.1
        let eo := σ.2.2
        do
          pure ({ sudo_8Position_2cp := cp, sudo_8Position_2co := co,
                  sudo_8Position_2ep := ep, sudo_8Position_2eo := eo } :
            Megadreifach.Position))
      (fun r => pure r))
    pure _out

private theorem edgeAfter_eq (g h : Position) :
    edgeAfter (embedPos g) (embedPos h) (embed (cpOut g h)) (embed (coOut g h)) =
      .ok (embedPos (compose g h)) := by
  unfold edgeAfter
  dsimp
  rw [except_bind_pure, ← fuel_0_29, ← edgeAcc_zero g h]
  apply chain_loop (f := edgeAcc g h) (fromN := 0) (toN := 29)
    (goal := .ok (embedPos (compose g h))) (hle := by decide)
  · intro i _ hi
    exact edgeStep_hit g h i hi
  · dsimp
    rw [edgeAcc_done g h]
    unfold embedPos cpOut coOut epOut eoOut
    rfl

/-- Corner-loop join: run the edge loop on the corner tables. -/
def cornerAfter (g h : Megadreifach.Position)
    (σ : Int × (Array Int × Array Int)) : Except SudoRt.Trap Megadreifach.Position :=
  let cp := σ.2.1
  let co := σ.2.2
  edgeAfter g h cp co

private theorem composeRun_eq (g h : Position) :
    SudoRt.runLoopOn (ρ := Megadreifach.Position)
      ((0 : Int), ((#[] : Array Int), (#[] : Array Int)))
      (fuelRange (0 : Int) (19 : Int))
      (cornerStep (embedPos g) (embedPos h) (19 : Int))
      (cornerAfter (embedPos g) (embedPos h))
      (fun r => pure r) =
    .ok (embedPos (compose g h)) := by
  rw [← cornerAcc_zero g h]
  apply chain_loop (f := cornerAcc g h) (fromN := 0) (toN := 19)
    (goal := .ok (embedPos (compose g h))) (hle := by decide)
  · intro i _ hi
    exact cornerStep_hit g h i hi
  · unfold cornerAfter
    dsimp
    rw [cornerAcc_done g h]
    exact edgeAfter_eq g h

private theorem runLoopOn_congr {σ ρ α} (s0 : σ) (fuel : Nat)
    (step step' : σ → Except SudoRt.Trap (SudoRt.Flow σ ρ))
    (after after' : σ → Except SudoRt.Trap α)
    (onRet onRet' : ρ → Except SudoRt.Trap α)
    (hstep : ∀ s, step s = step' s)
    (hafter : ∀ s, after s = after' s)
    (hret : ∀ r, onRet r = onRet' r) :
    SudoRt.runLoopOn (ρ := ρ) s0 fuel step after onRet =
      SudoRt.runLoopOn (ρ := ρ) s0 fuel step' after' onRet' := by
  rw [show step = step' from funext hstep,
    show after = after' from funext hafter,
    show onRet = onRet' from funext hret]

/-- `Generated.compose` on the embedding of two algebraic positions equals the
    embedding of algebraic `compose`.

    The embedded tables are `PosWf`: lengths 20/20/30/30, in-range indices,
    orientations in `0..2` / `0..1`. That is the trap-free i64 domain.
    Not `v_Hash`, not emitter soundness, not collision resistance. -/
theorem compose_refines (g h : Position) :
    Megadreifach.compose (embedPos g) (embedPos h) =
      .ok (embedPos (compose g h)) := by
  unfold Megadreifach.compose
  dsimp
  rw [except_bind_pure, ← fuel_0_19]
  apply Eq.trans
  · apply runLoopOn_congr
      (step' := cornerStep (embedPos g) (embedPos h) (19 : Int))
      (after' := cornerAfter (embedPos g) (embedPos h))
      (onRet' := fun r => pure r)
    · intro σ
      unfold cornerStep
      dsimp
      rfl
    · intro σ
      unfold cornerAfter edgeAfter edgeStep
      dsimp
      rfl
    · intro r
      rfl
  · exact composeRun_eq g h

/-- Same refinement on a `PosWf` array position. `decodePos` is the inverse
    of `embedPos` on this domain. -/
theorem compose_refines_array (g h : Megadreifach.Position) (hg : PosWf g) (hh : PosWf h) :
    Megadreifach.compose g h =
      .ok (embedPos (compose (decodePos g hg) (decodePos h hh))) := by
  have hr := compose_refines (decodePos g hg) (decodePos h hh)
  simpa [embedPos_decode g hg, embedPos_decode h hh] using hr

end MegaDreifach.Link2
