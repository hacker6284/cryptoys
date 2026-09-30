/-
  LINK 2. `Generated.inverse` refines the algebraic `Em.inverse`
  (= M2 `inverseWith g (permInv g.cp) (permInv g.ep)`).

  The emitted body runs four loops on zero-filled tables:
  `cp_inv[g.cp[s]] = s`, `co_inv[s] = (3 - g.co[cp_inv[s]] mod 3) mod 3`, and
  the same for edges.  `Em.permInv` is defined by the same last-writer fold
  (`Em.invList`), so the refinement holds for *every* algebraic position,
  with no injectivity hypothesis: every index is a `Fin` value and every
  write lands in range.

  Algebraic Link 2 only. Not `em_block`. Not `v_Hash`.
-/
import MegaDreifachV1.Link2.Compose
import MegaDreifachV1.Em

namespace MegaDreifachV1.Link2

open MegaDreifachV1.Em

/-! ## List folds behind the two loop shapes -/

/-- State of the permutation-inverse loop after `k` writes. -/
def invPre (p : List Nat) (n k : Nat) : List Nat :=
  (List.range k).foldl (fun acc s => acc.set (p.getD s 0) s) (List.replicate n 0)

theorem invPre_succ (p : List Nat) (n k : Nat) :
    invPre p n (k + 1) = (invPre p n k).set (p.getD k 0) k := by
  simp [invPre, List.range_succ, List.foldl_append]

theorem invPre_length (p : List Nat) (n k : Nat) : (invPre p n k).length = n := by
  induction k with
  | zero => simp [invPre]
  | succ k ih => rw [invPre_succ, List.length_set, ih]

theorem invPre_bound (p : List Nat) (n k : Nat) (hk : k ≤ n) (hn : 0 < n) :
    ∀ x ∈ invPre p n k, x < n := by
  induction k with
  | zero =>
    intro x hx
    simp [invPre] at hx
    rw [hx.2]; exact hn
  | succ k ih =>
    intro x hx
    rw [invPre_succ] at hx
    rcases List.mem_or_eq_of_mem_set hx with h | h
    · exact ih (by omega) x h
    · omega

theorem invPre_full (p : List Nat) (n : Nat) : invPre p n n = invList p n := rfl

/-- State of the orientation loop after `k` writes (`acc[s] := f s`). -/
def setPre (f : Nat → Nat) (n k : Nat) : List Nat :=
  (List.range k).foldl (fun acc s => acc.set s (f s)) (List.replicate n 0)

theorem setPre_succ (f : Nat → Nat) (n k : Nat) :
    setPre f n (k + 1) = (setPre f n k).set k (f k) := by
  simp [setPre, List.range_succ, List.foldl_append]

theorem setPre_eq (f : Nat → Nat) (n k : Nat) (hk : k ≤ n) :
    setPre f n k = (List.range k).map f ++ List.replicate (n - k) 0 := by
  induction k with
  | zero => simp [setPre]
  | succ k ih =>
    rw [setPre_succ, ih (by omega)]
    have hlen : ((List.range k).map f).length = k := by simp
    rw [List.set_append_right _ _ (by omega)]
    rw [hlen, Nat.sub_self]
    obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
    rw [hm, List.replicate_succ, List.set_cons_zero, List.range_succ, List.map_append,
      List.map_singleton, List.append_assoc, List.singleton_append]
    have hm' : n - (k + 1) = m := by omega
    rw [hm']

theorem setPre_length (f : Nat → Nat) (n k : Nat) : (setPre f n k).length = n := by
  induction k with
  | zero => simp [setPre]
  | succ k ih => rw [setPre_succ, List.length_set, ih]

theorem setPre_full (f : Nat → Nat) (n : Nat) : setPre f n n = (List.range n).map f := by
  rw [setPre_eq f n n (Nat.le_refl n), Nat.sub_self, List.replicate_zero, List.append_nil]

/-! ## `embed` and writes -/

theorem embed_set (xs : List Nat) (i v : Nat) (h : i < (embed xs).size) :
    (embed xs).set ⟨i, h⟩ (Int.ofNat v) = embed (xs.set i v) := by
  apply Array.ext'
  simp [embed, List.map_set]

theorem putL_embed (xs : List Nat) (i v : Nat) (h : i < xs.length) :
    SudoRt.putL (embed xs) (Int.ofNat i) (Int.ofNat v) = .ok (embed (xs.set i v)) := by
  have hs : i < (embed xs).size := by rw [size_embed]; exact h
  rw [putL_ofNat _ _ _ hs, embed_set]

theorem mkArray_zero_embed (n : Nat) :
    Array.mkArray n (0 : Int) = embed (List.replicate n 0) := by
  apply Array.ext'
  simp [embed, Array.toList_mkArray, List.map_replicate]


/-! ## Loop 1 / 3: `inv[p[s]] = s` -/

/-- Emitted permutation-inverse loop body (`ρ := Position`). -/
def invPermStep (p : Array Int) (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) Megadreifach.Position) :=
  let s := σ.1
  let inv := σ.2
  do
    if s > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, inv))
    else
      match ← ((do
        let _t104 ← SudoRt.atL p s
        let _ix105 := _t104
        let _t106 ← SudoRt.putL inv _ix105 s
        let inv := _t106
        pure (SudoRt.Flow.cont (ρ := Megadreifach.Position) inv)) :
          Except SudoRt.Trap (SudoRt.Flow _ Megadreifach.Position)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.Position) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, _fs))
      | .cont _fs => do
          if s == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, _fs))
          else do
            let i' ← SudoRt.addI s (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.Position) (i', _fs))

private theorem fits31 (k : Nat) (hk : k ≤ 31) : FitsLen k :=
  FitsLen.of_le (by unfold FitsLen i64MaxNat; decide : FitsLen 31) hk

/-- Close the inclusive-loop tail at index `i ≤ toN`. -/
theorem loopTail {α} (i toN : Nat) (hi : i ≤ toN) (htoN : toN ≤ 30) (st : α) :
    (if (Int.ofNat i == Int.ofNat toN) = true then
        (pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (Int.ofNat i, st)) :
          Except SudoRt.Trap _)
      else do
        let i' ← SudoRt.addI (Int.ofNat i) (1 : Int)
        pure (SudoRt.Flow.cont (ρ := Megadreifach.Position) (i', st))) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, st))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), st)) := by
  by_cases heq : i = toN
  · subst heq; simp [beq_int_iff]; rfl
  · have hneI : ¬ (Int.ofNat i = Int.ofNat toN) := fun h => heq (Int.ofNat.inj h)
    rw [ite_int_beq, if_neg hneI, addI_ofNat_one i (fits31 _ (by omega)), ok_bind, if_neg heq]
    rfl

theorem invPermStep_hit (p : List Nat) (toN : Nat) (htoN : toN ≤ 29)
    (hlen : p.length = toN + 1) (hb : ∀ x ∈ p, x < toN + 1)
    (i : Nat) (hi : i ≤ toN) :
    invPermStep (embed p) (Int.ofNat toN) (Int.ofNat i, embed (invPre p (toN + 1) i)) =
      if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, embed (invPre p (toN + 1) (i + 1))))
      else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed (invPre p (toN + 1) (i + 1)))) := by
  have hip : i < p.length := by omega
  have hpi : p[i] < toN + 1 := hb _ (List.getElem_mem hip)
  have hgd : p.getD i 0 = p[i] := by simp [List.getD, hip]
  unfold invPermStep
  dsimp only
  rw [if_neg (ofNat_not_gt hi), atL_embed p i hip, ok_bind]
  rw [putL_embed _ _ _ (by rw [invPre_length]; exact hpi), ok_bind, pure_bind]
  dsimp only
  rw [invPre_succ, hgd]
  exact loopTail i toN hi (by omega) _

/-! ## Loop 2 / 4: `acc[s] = (m - ori[inv[s]] mod m) mod m` -/

/-- Emitted orientation-inverse loop body. -/
def invOriStep (inv ori : Array Int) (m : Int) (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) Megadreifach.Position) :=
  let s := σ.1
  let acc := σ.2
  do
    if s > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, acc))
    else
      match ← ((do
        let _ix109 := s
        let _t110 ← SudoRt.atL inv s
        let _t111 ← SudoRt.atL ori _t110
        let _t112 ← SudoRt.modI _t111 m
        let _t113 ← SudoRt.subI m _t112
        let _t114 ← SudoRt.modI _t113 m
        let _t115 ← SudoRt.putL acc _ix109 _t114
        let acc := _t115
        pure (SudoRt.Flow.cont (ρ := Megadreifach.Position) acc)) :
          Except SudoRt.Trap (SudoRt.Flow _ Megadreifach.Position)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.Position) r)
      | .brk _fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, _fs))
      | .cont _fs => do
          if s == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.Position) (s, _fs))
          else do
            let i' ← SudoRt.addI s (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.Position) (i', _fs))

/-- Cell written by the orientation loop at `s`. -/
def oriCell (inv ori : List Nat) (m s : Nat) : Nat :=
  (m - ori.getD (inv.getD s 0) 0 % m) % m

theorem invOriStep_hit (inv ori : List Nat) (m toN : Nat) (hm : 0 < m) (hm3 : m ≤ 3)
    (htoN : toN ≤ 29)
    (hinvLen : inv.length = toN + 1) (hinvB : ∀ x ∈ inv, x < toN + 1)
    (horiLen : ori.length = toN + 1)
    (i : Nat) (hi : i ≤ toN) :
    invOriStep (embed inv) (embed ori) (Int.ofNat m) (Int.ofNat toN)
        (Int.ofNat i, embed (setPre (oriCell inv ori m) (toN + 1) i)) =
      if i = toN then
        .ok (SudoRt.Flow.brk (Int.ofNat i, embed (setPre (oriCell inv ori m) (toN + 1) (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
          embed (setPre (oriCell inv ori m) (toN + 1) (i + 1)))) := by
  have hii : i < inv.length := by omega
  have hvi : inv[i] < ori.length := by
    have := hinvB _ (List.getElem_mem hii); omega
  have hgd1 : inv.getD i 0 = inv[i] := by simp [List.getD, hii]
  have hgd2 : ori.getD inv[i] 0 = ori[inv[i]] := by simp [List.getD, hvi]
  have hmne : m ≠ 0 := by omega
  have hmodle : ori[inv[i]] % m ≤ m := Nat.le_of_lt (Nat.mod_lt _ hm)
  unfold invOriStep
  dsimp only
  rw [if_neg (ofNat_not_gt hi), atL_embed inv i hii, ok_bind, atL_embed ori _ hvi, ok_bind,
    modI_ofNat _ hmne, ok_bind, subI_ofNat _ _ (fits31 m (by omega)) hmodle, ok_bind,
    modI_ofNat _ hmne, ok_bind,
    putL_embed _ _ _ (by rw [setPre_length]; omega), ok_bind, pure_bind]
  dsimp only
  have hcell : (m - ori[inv[i]] % m) % m = oriCell inv ori m i := by
    unfold oriCell; rw [hgd1, hgd2]
  rw [hcell, ← setPre_succ]
  exact loopTail i toN hi (by omega) _


/-! ## Algebraic side, as tables -/

private theorem listOf_eq_self {n : Nat} (xs : List Nat) (hlen : xs.length = n)
    (_hb : ∀ x ∈ xs, x < n) (f : Fin n → Fin n)
    (hf : ∀ i (h : i < n), (f ⟨i, h⟩).val = xs.getD i 0) : listOf f = xs := by
  apply List.ext_getElem
  · simp [listOf, hlen]
  · intro i h1 h2
    have hi : i < n := by rw [hlen] at h2; exact h2
    simp [listOf, hi, hf i hi, List.getD, h2]

theorem listOf_permInv {n : Nat} (hn : 0 < n) (_hn30 : n ≤ 30) (p : Fin n → Fin n) :
    listOf (permInv hn p) = invList (listOf p) n := by
  apply listOf_eq_self _ (invPre_length _ _ _) (invPre_bound _ _ _ (Nat.le_refl _) hn)
  intro i _
  simp only [permInv, rd]
  exact Nat.mod_eq_of_lt (by
    have hb := invPre_bound (listOf p) n n (Nat.le_refl _) hn
    rw [invPre_full] at hb
    by_cases hi : i < (invList (listOf p) n).length
    · have : (invList (listOf p) n).getD i 0 = (invList (listOf p) n)[i] := by
        simp [List.getD, hi]
      rw [this]; exact hb _ (List.getElem_mem hi)
    · exfalso; apply hi; rw [← invPre_full, invPre_length]; assumption)

private theorem getD_listOfOri {n m : Nat} (f : Fin n → Fin m) (j : Nat) (hj : j < n) :
    (listOfOri f).getD j 0 = (f ⟨j, hj⟩).val := by
  have := listOfOri_get f ⟨j, hj⟩
  simpa [List.getD] using this

private theorem listOfOri_eq_map {n m : Nat} (f : Fin n → Fin m) (F : Nat → Nat)
    (hF : ∀ i (h : i < n), (f ⟨i, h⟩).val = F i) : listOfOri f = (List.range n).map F := by
  apply List.ext_getElem
  · simp [listOfOri]
  · intro i h1 _
    have hi : i < n := by simpa [listOfOri] using h1
    simp [listOfOri, hi, hF i hi]

private theorem permInv_val {n : Nat} (hn : 0 < n) (hn30 : n ≤ 30) (p : Fin n → Fin n)
    (i : Nat) (hi : i < n) :
    (permInv hn p ⟨i, hi⟩).val = (invList (listOf p) n).getD i 0 := by
  have := congrArg (fun l => l.getD i 0) (listOf_permInv hn hn30 p)
  simpa [listOf, hi, List.getD] using this

theorem listOfOri_inverse_co (g : Position) :
    listOfOri (Em.inverse g).co =
      (List.range 20).map (oriCell (invList (listOf g.cp) 20) (listOfOri g.co) 3) := by
  apply listOfOri_eq_map
  intro i hi
  show (3 - (g.co (permInv _ g.cp ⟨i, hi⟩)).val) % 3 = _
  unfold oriCell
  rw [← permInv_val (by decide) (by decide) g.cp i hi,
    getD_listOfOri g.co _ (permInv _ g.cp ⟨i, hi⟩).isLt, Nat.mod_eq_of_lt (g.co _).isLt]

theorem listOfOri_inverse_eo (g : Position) :
    listOfOri (Em.inverse g).eo =
      (List.range 30).map (oriCell (invList (listOf g.ep) 30) (listOfOri g.eo) 2) := by
  apply listOfOri_eq_map
  intro i hi
  show (2 - (g.eo (permInv _ g.ep ⟨i, hi⟩)).val) % 2 = _
  unfold oriCell
  rw [← permInv_val (by decide) (by decide) g.ep i hi,
    getD_listOfOri g.eo _ (permInv _ g.ep ⟨i, hi⟩).isLt, Nat.mod_eq_of_lt (g.eo _).isLt]

/-- `embedPos (Em.inverse g)` as the four emitted tables. -/
theorem embedPos_inverse (g : Position) :
    embedPos (Em.inverse g) =
      { sudo_8Position_2cp := embed (invList (listOf g.cp) 20)
        sudo_8Position_2co := embed ((List.range 20).map
          (oriCell (invList (listOf g.cp) 20) (listOfOri g.co) 3))
        sudo_8Position_2ep := embed (invList (listOf g.ep) 30)
        sudo_8Position_2eo := embed ((List.range 30).map
          (oriCell (invList (listOf g.ep) 30) (listOfOri g.eo) 2)) } := by
  unfold embedPos
  rw [listOfOri_inverse_co, listOfOri_inverse_eo]
  simp only [Em.inverse, inverseWith]
  rw [listOf_permInv (by decide) (by decide), listOf_permInv (by decide) (by decide)]


/-! ## The four chained loops -/

private theorem listOf_len20 (f : Fin 20 → Fin 20) : (listOf f).length = 19 + 1 := listOf_length f
private theorem listOf_len30 (f : Fin 30 → Fin 30) : (listOf f).length = 29 + 1 := listOf_length f
private theorem listOfOri_len20 (f : Fin 20 → Fin 3) : (listOfOri f).length = 19 + 1 :=
  listOfOri_length f
private theorem listOfOri_len30 (f : Fin 30 → Fin 2) : (listOfOri f).length = 29 + 1 :=
  listOfOri_length f
private theorem listOf_b {n : Nat} (f : Fin n → Fin n) : ∀ x ∈ listOf f, x < n := by
  intro x hx
  rw [listOf, List.mem_map] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [List.mem_range] at hi
  simp [hi]

/-- `Generated.inverse` on any embedded algebraic position is the embedded
    algebraic `Em.inverse` (no injectivity or legality hypothesis). -/
theorem inverse_refines (g : Position) :
    Megadreifach.inverse (embedPos g) = .ok (embedPos (Em.inverse g)) := by
  rw [embedPos_inverse]
  unfold Megadreifach.inverse
  simp only [show (20 : Int) = Int.ofNat 20 from rfl, show (30 : Int) = Int.ofNat 30 from rfl,
    filledL_ofNat, ok_bind, mkArray_zero_embed]
  rw [except_bind_pure]
  apply chain_loop (f := fun i => embed (invPre (listOf g.cp) (19 + 1) i))
    (fromN := 0) (toN := 19) (hle := by decide)
  · intro i _ hi
    exact invPermStep_hit (listOf g.cp) 19 (by decide) (listOf_len20 _) (listOf_b _) i hi
  · dsimp only
    rw [except_bind_pure]
    apply chain_loop (f := fun i => embed (setPre (oriCell (invPre (listOf g.cp) (19 + 1) (19 + 1))
        (listOfOri g.co) 3) (19 + 1) i)) (fromN := 0) (toN := 19) (hle := by decide)
    · intro i _ hi
      exact invOriStep_hit _ _ 3 19 (by decide) (by decide) (by decide) (invPre_length _ _ _)
        (invPre_bound _ _ _ (Nat.le_refl _) (by decide)) (listOfOri_len20 _) i hi
    · dsimp only
      rw [except_bind_pure]
      apply chain_loop (f := fun i => embed (invPre (listOf g.ep) (29 + 1) i))
        (fromN := 0) (toN := 29) (hle := by decide)
      · intro i _ hi
        exact invPermStep_hit (listOf g.ep) 29 (by decide) (listOf_len30 _) (listOf_b _) i hi
      · dsimp only
        rw [except_bind_pure]
        apply chain_loop (f := fun i => embed (setPre (oriCell
            (invPre (listOf g.ep) (29 + 1) (29 + 1)) (listOfOri g.eo) 2) (29 + 1) i))
          (fromN := 0) (toN := 29) (hle := by decide)
        · intro i _ hi
          exact invOriStep_hit _ _ 2 29 (by decide) (by decide) (by decide) (invPre_length _ _ _)
            (invPre_bound _ _ _ (Nat.le_refl _) (by decide)) (listOfOri_len30 _) i hi
        · dsimp only
          rw [setPre_full, setPre_full, invPre_full, invPre_full]
          rfl

end MegaDreifachV1.Link2
