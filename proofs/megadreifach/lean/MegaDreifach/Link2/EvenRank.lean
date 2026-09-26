/-
  LINK 2. `Generated.even_perm_rank_big` refines algebraic `evenRank` on a
  length-20 permutation whose Lehmer rank is `< 2 · 10^9` (`Rank20Wf`).

  The emitted loop is the Lehmer prefix: for `i = 0 .. n-3`,
  `rank = rank * (n - i) + index of perm[i] in the remaining symbols`.
  That is `mixEncode` on radices `n, n-1, …, 3`, i.e. `evenRank`.

  `20!/2` fits in an i64 and in three base-10^9 limbs, but this slice reuses
  the one-limb multiply and two-limb add proved for `pack_ori3`. The domain
  is therefore `evenRank perm < 2 · limbBase`, which forces every prefix
  accumulator into one limb. Length 30 (`30!/2`) needs a fourth limb and is
  not this slice. Evenness is not required: the loop reads only the first
  `n - 2` symbols.

  Algebraic Link 2 only. Not `v_Hash`. Not emitter soundness.
  Not collision resistance. Not even-permutation injectivity (M3 glue).
-/
import Megadreifach
import MegaDreifach.Rank
import MegaDreifach.Link2.PackOri

namespace MegaDreifach.Link2

/-! ## Left-to-right Horner, variable radices -/

/-- `acc = acc * r + d` down the two lists. Stops if either list runs out. -/
def hornerZip : Nat → List Nat → List Nat → Nat
  | acc, [], _ => acc
  | acc, _ :: _, [] => acc
  | acc, r :: rs, d :: ds => hornerZip (acc * r + d) rs ds

theorem hornerZip_nil_left (acc : Nat) (ds : List Nat) :
    hornerZip acc [] ds = acc := by
  cases ds <;> rfl

theorem hornerZip_acc (acc : Nat) (rs ds : List Nat) (h : ds.length = rs.length) :
    hornerZip acc rs ds = acc * product rs + mixEncode rs ds := by
  induction rs generalizing acc ds with
  | nil =>
    cases ds with
    | nil => simp [hornerZip, product, mixEncode]
    | cons _ _ => simp at h
  | cons r rs ih =>
    cases ds with
    | nil => simp at h
    | cons d ds =>
      have hlen : ds.length = rs.length := by simp at h; exact h
      rw [hornerZip, ih (acc * r + d) ds hlen, mixEncode_cons, product_cons]
      have hmul : (acc * r + d) * product rs =
          acc * (r * product rs) + d * product rs := by
        rw [Nat.add_mul, Nat.mul_assoc]
      omega

theorem hornerZip_mix (rs ds : List Nat) (h : ds.length = rs.length) :
    hornerZip 0 rs ds = mixEncode rs ds := by
  simpa using hornerZip_acc 0 rs ds h

theorem hornerZip_snoc (acc : Nat) (rs ds : List Nat) (r d : Nat)
    (h : ds.length = rs.length) :
    hornerZip acc (rs ++ [r]) (ds ++ [d]) = hornerZip acc rs ds * r + d := by
  induction rs generalizing acc ds with
  | nil =>
    cases ds with
    | nil => simp [hornerZip]
    | cons _ _ => simp at h
  | cons r0 rs ih =>
    cases ds with
    | nil => simp at h
    | cons d0 ds =>
      have hlen : ds.length = rs.length := by simp at h; exact h
      simp only [List.cons_append, hornerZip]
      exact ih (acc * r0 + d0) ds hlen

theorem product_append (xs ys : List Nat) :
    product (xs ++ ys) = product xs * product ys := by
  induction xs with
  | nil => simp [product]
  | cons x xs ih =>
    simp only [List.cons_append, product_cons, ih]
    rw [Nat.mul_assoc]

/-! ## Radices `n, n-1, …, 3` -/

theorem descending_two : descending 2 = [2, 1] := by
  simp [descending, factorial]

theorem drop_descending_two (n : Nat) (hn : 2 ≤ n) :
    (descending n).drop (n - 2) = descending 2 := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero =>
        simp [descending]
      | succ n =>
        have hn' : 2 ≤ n + 2 := by omega
        have ih' := ih hn'
        simp only [descending_succ, List.drop_succ_cons, Nat.succ_sub_succ]
        exact ih'

theorem evenRadices_take (n : Nat) (hn : 2 ≤ n) :
    evenRadices n = (descending n).take (n - 2) := by
  match n with
  | 0 => omega
  | 1 => omega
  | n + 2 =>
    simp [evenRadices]

theorem descending_eq_even (n : Nat) (hn : 2 ≤ n) :
    descending n = evenRadices n ++ descending 2 := by
  rw [← List.take_append_drop (n - 2) (descending n), drop_descending_two n hn,
    ← evenRadices_take n hn]

theorem product_evenRadices (n : Nat) (hn : 2 ≤ n) :
    product (evenRadices n) = evenPermCount n := by
  have hdesc := descending_eq_even n hn
  have hp := product_descending n
  rw [hdesc, product_append, descending_two] at hp
  simp only [product_cons, product_nil, Nat.mul_one] at hp
  unfold evenPermCount
  have htwo : 0 < 2 := by decide
  rw [← hp]
  exact (Nat.mul_div_cancel _ htwo).symm

theorem descending_get (n i : Nat) (hi : i < n) :
    (descending n)[i]'(by rw [descending_length]; exact hi) = n - i := by
  induction n generalizing i with
  | zero => cases hi
  | succ n ih =>
    cases i with
    | zero => simp [descending]
    | succ i =>
      have hi' : i < n := Nat.lt_of_succ_lt_succ hi
      have ih' := ih i hi'
      simp only [descending_succ, List.getElem_cons_succ] at ih' ⊢
      rw [ih']
      omega

theorem evenRadix_get (n i : Nat) (hn : 2 ≤ n) (hi : i < n - 2) :
    (evenRadices n)[i]'(by rw [evenRadices_length n hn]; exact hi) = n - i := by
  have hlen : i < n := by omega
  simp only [evenRadices_take n hn, List.getElem_take]
  exact descending_get n i hlen

/-! ## Lehmer prefix -/

/-- Symbols still available after consuming `vs` (first-hit index, then erase). -/
def dropUsed : List Nat → List Nat → List Nat
  | avail, [] => avail
  | avail, v :: vs =>
    dropUsed (avail.eraseIdx (avail.findIdx (· == v))) vs

def availAt (perm : List Nat) (k : Nat) : List Nat :=
  dropUsed (List.range perm.length) (perm.take k)

def evenDigits (perm : List Nat) : List Nat :=
  (lehmerDigits (List.range perm.length) perm).take (perm.length - 2)

def rankAcc (perm : List Nat) (k : Nat) : Nat :=
  hornerZip 0 ((evenRadices perm.length).take k) ((evenDigits perm).take k)

theorem lehmerDigits_length (avail perm : List Nat) :
    (lehmerDigits avail perm).length = perm.length := by
  induction perm generalizing avail with
  | nil => rfl
  | cons v vs ih =>
    simp only [lehmerDigits, List.length_cons, ih]

theorem lehmer_split (avail p q : List Nat) :
    lehmerDigits avail (p ++ q) =
      lehmerDigits avail p ++ lehmerDigits (dropUsed avail p) q := by
  induction p generalizing avail with
  | nil => simp [lehmerDigits, dropUsed]
  | cons v p ih =>
    rw [List.cons_append]
    simp only [lehmerDigits, dropUsed, ih, List.cons_append]

private theorem getElem_congr {α : Type} {xs ys : List α} (h : xs = ys) (i : Nat)
    (hi : i < xs.length) : xs[i] = ys[i]'(h ▸ hi) := by
  subst h
  rfl

theorem digit_eq_find (perm : List Nat) (k : Nat) (hk : k < perm.length) :
    (lehmerDigits (List.range perm.length) perm)[k]'(by
        rw [lehmerDigits_length]; exact hk) =
      (availAt perm k).findIdx (· == perm[k]) := by
  have hsplit : perm = perm.take k ++ perm.drop k := (List.take_append_drop k perm).symm
  have hlenTake : (perm.take k).length = k := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hdrop : perm.drop k = perm[k] :: perm.drop (k + 1) :=
    List.drop_eq_getElem_cons hk
  have hsplitD := lehmer_split (List.range perm.length) (perm.take k) (perm.drop k)
  rw [← hsplit] at hsplitD
  have hlen1 : (lehmerDigits (List.range perm.length) (perm.take k)).length = k := by
    rw [lehmerDigits_length, hlenTake]
  have hhead : lehmerDigits (availAt perm k) (perm.drop k) =
      (availAt perm k).findIdx (· == perm[k]) ::
        lehmerDigits
          ((availAt perm k).eraseIdx ((availAt perm k).findIdx (· == perm[k])))
          (perm.drop (k + 1)) := by
    rw [hdrop]
    rfl
  have hidx :=
    getElem_congr hsplitD k (by rw [lehmerDigits_length]; exact hk)
  unfold availAt at hhead
  rw [hidx, List.getElem_append_right (by rw [hlen1]; exact Nat.le_refl _)]
  simp only [hlen1, Nat.sub_self]
  have hge := getElem_congr hhead 0 (by rw [hhead]; exact Nat.succ_pos _)
  unfold availAt
  rw [hge, List.getElem_cons_zero]

theorem dropUsed_snoc (avail vs : List Nat) (v : Nat) :
    dropUsed avail (vs ++ [v]) =
      (dropUsed avail vs).eraseIdx ((dropUsed avail vs).findIdx (· == v)) := by
  induction vs generalizing avail with
  | nil => simp [dropUsed]
  | cons x xs ih =>
    rw [List.cons_append]
    simp only [dropUsed]
    rw [ih]

/-! ## Length-20 permutations (corner width) -/

/-- Trap-free domain for corner `even_perm_rank_big`.

    Length 20 is the corner permutation. Entries are a permutation of
    `0..19`, so every Lehmer lookup hits. The rank is `< 20!/2`, which fits
    in an i64 and in three base-10^9 limbs. Evenness is not required: the
    emitted loop only reads the first 18 symbols. -/
structure Perm20Wf (perm : List Nat) : Prop where
  len : perm.length = 20
  nodup : perm.Nodup
  bound : ∀ a ∈ perm, a < 20

structure WellFormedPerm20 (a : Array Int) : Prop where
  len : a.size = 20
  nn : Nonneg a
  nodup : (decode a).Nodup
  bound : ∀ x ∈ decode a, x < 20

theorem perm20_embed (perm : List Nat) (h : Perm20Wf perm) :
    WellFormedPerm20 (embed perm) where
  len := by simp [size_embed, h.len]
  nn := nonneg_embed perm
  nodup := by rw [decode_embed]; exact h.nodup
  bound := by rw [decode_embed]; exact h.bound

theorem perm20_decode (a : Array Int) (h : WellFormedPerm20 a) :
    Perm20Wf (decode a) where
  len := by simp [decode, h.len]
  nodup := h.nodup
  bound := h.bound

theorem not_mem_take_self (perm : List Nat) (hnd : perm.Nodup) {i : Nat}
    (hi : i < perm.length) : perm[i] ∉ perm.take i := by
  induction perm generalizing i with
  | nil => cases hi
  | cons a as ih =>
    cases i with
    | zero => simp [List.take_zero]
    | succ i =>
      rw [List.nodup_cons] at hnd
      have hi' : i < as.length := Nat.lt_of_succ_lt_succ hi
      intro hmem
      rw [List.take_succ_cons, List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
        exact hnd.1 (heq ▸ List.getElem_mem hi')
      | inr hm =>
        exact ih hnd.2 hi' hm

theorem nodup_getElem_ne (xs : List Nat) (h : xs.Nodup) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) (hij : i ≠ j) : xs[i] ≠ xs[j] := by
  unfold List.Nodup at h
  rw [List.pairwise_iff_getElem] at h
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · exact h i j hi hj hlt
  · exact (h j i hj hi hgt).symm

theorem mem_eraseIdx_of_nodup (xs : List Nat) (h : xs.Nodup) {i : Nat}
    (hi : i < xs.length) {x : Nat} :
    x ∈ xs.eraseIdx i ↔ x ∈ xs ∧ x ≠ xs[i] := by
  constructor
  · intro hx
    rw [List.mem_eraseIdx_iff_getElem] at hx
    obtain ⟨j, hj, hne, rfl⟩ := hx
    exact ⟨List.getElem_mem hj, nodup_getElem_ne xs h hj hi hne⟩
  · intro ⟨hx, hne⟩
    rw [List.mem_iff_getElem] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hne' : j ≠ i := by
      intro heq
      apply hne
      cases heq
      rfl
    rw [List.mem_eraseIdx_iff_getElem]
    exact ⟨j, hj, hne', rfl⟩

theorem findIdx_lt_mem (xs : List Nat) {v : Nat} (hv : v ∈ xs) :
    xs.findIdx (· == v) < xs.length := by
  rw [List.findIdx_lt_length]
  exact ⟨v, hv, by simp⟩

theorem get_findIdx (xs : List Nat) {v : Nat} (hv : v ∈ xs) :
    xs[xs.findIdx (· == v)]'(findIdx_lt_mem xs hv) = v := by
  have hp := List.findIdx_getElem (w := findIdx_lt_mem xs hv)
  simpa using hp

theorem availAt_erase (perm : List Nat) (k : Nat) (hk : k < perm.length) :
    availAt perm (k + 1) =
      (availAt perm k).eraseIdx ((availAt perm k).findIdx (· == perm[k])) := by
  unfold availAt
  rw [take_succ_get perm k hk, dropUsed_snoc]

theorem availAt_spec (perm : List Nat) (h : Perm20Wf perm) :
    ∀ k, k ≤ 20 →
      (availAt perm k).Nodup ∧
      (availAt perm k).length = 20 - k ∧
      (∀ x, x ∈ availAt perm k ↔ x < 20 ∧ x ∉ perm.take k) := by
  intro k hk
  induction k with
  | zero =>
    have hlen : perm.length = 20 := h.len
    simp only [availAt, dropUsed, hlen, List.take_zero]
    refine ⟨List.nodup_range 20, by simp [List.length_range], ?_⟩
    intro x
    simp [List.mem_range]
  | succ k ih =>
    have hk0 : k ≤ 20 := Nat.le_trans (Nat.le_succ k) hk
    have hklt : k < 20 := by omega
    have hklen : k < perm.length := by rw [h.len]; exact hklt
    obtain ⟨hnd, hlen, hmem⟩ := ih hk0
    have hnot : perm[k] ∉ perm.take k := not_mem_take_self perm h.nodup hklen
    have hin : perm[k] ∈ availAt perm k := by
      rw [hmem]
      exact ⟨h.bound _ (List.getElem_mem hklen), hnot⟩
    have hidx : (availAt perm k).findIdx (· == perm[k]) < (availAt perm k).length :=
      findIdx_lt_mem _ hin
    have hget := get_findIdx (availAt perm k) hin
    refine ⟨?_, ?_, ?_⟩
    · rw [availAt_erase perm k hklen]
      exact List.Nodup.eraseIdx _ hnd
    · rw [availAt_erase perm k hklen, List.length_eraseIdx_of_lt hidx, hlen]
      omega
    · intro x
      rw [availAt_erase perm k hklen, mem_eraseIdx_of_nodup _ hnd hidx, hmem, hget]
      have htake : perm.take (k + 1) = perm.take k ++ [perm[k]] :=
        take_succ_get perm k hklen
      constructor
      · intro ⟨⟨hx, hnin⟩, hne⟩
        refine ⟨hx, ?_⟩
        rw [htake, List.mem_append]
        intro hbad
        cases hbad with
        | inl hm => exact hnin hm
        | inr hm =>
          simp at hm
          exact hne hm
      · intro ⟨hx, hnin⟩
        have hnin0 : x ∉ perm.take k := by
          intro hm
          exact hnin (by rw [htake, List.mem_append]; exact Or.inl hm)
        have hne : x ≠ perm[k] := by
          intro heq
          exact hnin (by rw [htake, List.mem_append]; exact Or.inr (by simp [heq]))
        exact ⟨⟨hx, hnin0⟩, hne⟩

theorem availAt_length (perm : List Nat) (h : Perm20Wf perm) (k : Nat) (hk : k ≤ 20) :
    (availAt perm k).length = 20 - k :=
  (availAt_spec perm h k hk).2.1

theorem availAt_nodup (perm : List Nat) (h : Perm20Wf perm) (k : Nat) (hk : k ≤ 20) :
    (availAt perm k).Nodup :=
  (availAt_spec perm h k hk).1

theorem mem_availAt (perm : List Nat) (h : Perm20Wf perm) (k : Nat) (hk : k < 20) :
    perm[k]'(by rw [h.len]; exact hk) ∈ availAt perm k := by
  have hmem := (availAt_spec perm h k (Nat.le_of_lt hk)).2.2
  have hklen : k < perm.length := by rw [h.len]; exact hk
  rw [hmem]
  exact ⟨h.bound _ (List.getElem_mem hklen), not_mem_take_self perm h.nodup hklen⟩

theorem digit_lt_len (perm : List Nat) (h : Perm20Wf perm) (k : Nat) (hk : k < 18) :
    (evenDigits perm)[k]'(by
        simp [evenDigits, List.length_take, lehmerDigits_length, h.len]; omega) =
      (availAt perm k).findIdx (· == perm[k]'(by rw [h.len]; omega)) ∧
      (evenDigits perm)[k]'(by
        simp [evenDigits, List.length_take, lehmerDigits_length, h.len]; omega) < 20 - k := by
  have hklen : k < perm.length := by rw [h.len]; omega
  have hdig := digit_eq_find perm k hklen
  have hlt := findIdx_lt_mem _ (mem_availAt perm h k (by omega))
  have hlen := availAt_length perm h k (by omega)
  refine ⟨?_, ?_⟩
  · have hidx :
        (evenDigits perm)[k]'(by
          simp [evenDigits, List.length_take, lehmerDigits_length, h.len]; omega) =
        (lehmerDigits (List.range perm.length) perm)[k]'(by
          rw [lehmerDigits_length]; exact hklen) := by
      simp [evenDigits, List.getElem_take, hk]
    rw [hidx, hdig]
  · have hidx :
        (evenDigits perm)[k]'(by
          simp [evenDigits, List.length_take, lehmerDigits_length, h.len]; omega) =
        (lehmerDigits (List.range perm.length) perm)[k]'(by
          rw [lehmerDigits_length]; exact hklen) := by
      simp [evenDigits, List.getElem_take, hk]
    rw [hidx, hdig, ← hlen]
    exact hlt

theorem evenDigit_getD (perm : List Nat) (h : Perm20Wf perm) (k : Nat) (hk : k < 18) :
    (evenDigits perm)[k]?.getD 0 =
      (availAt perm k).findIdx (· == perm[k]'(by rw [h.len]; omega)) ∧
      (evenDigits perm)[k]?.getD 0 < 20 - k := by
  have hlen : k < (evenDigits perm).length := by
    simp [evenDigits, List.length_take, lehmerDigits_length, h.len]
    omega
  have hpair := digit_lt_len perm h k hk
  rw [List.getElem?_eq_getElem hlen]
  simp only [Option.getD_some]
  exact hpair

theorem rankAcc_zero (perm : List Nat) : rankAcc perm 0 = 0 := by
  simp [rankAcc, hornerZip, List.take_zero]

theorem evenDigits_length (perm : List Nat) (hn : 2 ≤ perm.length) :
    (evenDigits perm).length = perm.length - 2 := by
  simp [evenDigits, List.length_take, lehmerDigits_length]
  omega

theorem rankAcc_succ (perm : List Nat) (k : Nat) (hk : k < perm.length - 2) :
    rankAcc perm (k + 1) =
      rankAcc perm k *
        (evenRadices perm.length)[k]'(by
          have hn : 2 ≤ perm.length := by omega
          rw [evenRadices_length perm.length hn]; exact hk) +
        (evenDigits perm)[k]'(by
          rw [evenDigits_length perm (by omega)]; exact hk) := by
  have hn : 2 ≤ perm.length := by omega
  unfold rankAcc
  have hradLen : k < (evenRadices perm.length).length := by
    rw [evenRadices_length perm.length hn]; exact hk
  have hdigLen : k < (evenDigits perm).length := by
    rw [evenDigits_length perm hn]; exact hk
  rw [take_succ_get (evenRadices perm.length) k hradLen,
    take_succ_get (evenDigits perm) k hdigLen, hornerZip_snoc]
  · simp [List.length_take, evenRadices_length, evenDigits_length, hn]

theorem evenRank_eq_acc (perm : List Nat) (hn : 2 ≤ perm.length) :
    evenRank perm = rankAcc perm (perm.length - 2) := by
  unfold evenRank rankAcc
  have hlenR : (evenRadices perm.length).length = perm.length - 2 :=
    evenRadices_length _ hn
  have htakeR : (evenRadices perm.length).take (perm.length - 2) = evenRadices perm.length := by
    rw [← hlenR, List.take_length]
  have htakeD : (evenDigits perm).take (perm.length - 2) = evenDigits perm := by
    rw [← evenDigits_length perm hn, List.take_length]
  rw [htakeR, htakeD, hornerZip_mix]
  · rfl
  · rw [evenDigits_length perm hn, hlenR]

private theorem getD_get (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    xs[i]?.getD 0 = xs[i] := by
  rw [List.getElem?_eq_getElem hi]
  rfl

theorem rankAcc_bound (perm : List Nat) (h : Perm20Wf perm) (k : Nat) (hk : k ≤ 18) :
    rankAcc perm k < product ((evenRadices 20).take k) := by
  have hn : 2 ≤ perm.length := by rw [h.len]; decide
  have hlenD : ((evenDigits perm).take k).length = k := by
    rw [List.length_take, evenDigits_length perm hn, h.len]
    exact Nat.min_eq_left (by omega)
  have hlenR : ((evenRadices 20).take k).length = k := by
    rw [List.length_take, evenRadices_length 20 (by decide)]
    exact Nat.min_eq_left (by omega)
  have hmix : rankAcc perm k =
      mixEncode ((evenRadices 20).take k) ((evenDigits perm).take k) := by
    unfold rankAcc
    rw [h.len, hornerZip_mix _ _ (by rw [hlenD, hlenR])]
  rw [hmix]
  apply mixEncode_lt
  · rw [hlenD, hlenR]
  · intro i hi
    have hi' : i < k := by rw [hlenD] at hi; exact hi
    have hdg := evenDigit_getD perm h i (by omega)
    have hrad := evenRadix_get 20 i (by decide) (by omega)
    rw [List.getElem?_take_of_lt hi', List.getElem?_take_of_lt hi', hdg.1]
    have hrD : (evenRadices 20)[i]?.getD 0 = 20 - i := by
      rw [List.getElem?_eq_getElem (by
        rw [evenRadices_length 20 (by decide)]; omega)]
      simp only [Option.getD_some, hrad]
    rw [hrD, ← hdg.1]
    exact hdg.2

theorem product_take_even (k : Nat) (_hk : k ≤ 18) :
    product ((evenRadices 20).take k) ≤ evenPermCount 20 := by
  have hall : product (evenRadices 20) = evenPermCount 20 :=
    product_evenRadices 20 (by decide)
  have happ := product_append ((evenRadices 20).take k) ((evenRadices 20).drop k)
  rw [List.take_append_drop] at happ
  rw [happ] at hall
  have hpos : 0 < product ((evenRadices 20).drop k) := by
    apply product_pos
    intro r hr
    have hmem : r ∈ evenRadices 20 := List.mem_of_mem_drop hr
    have hdesc : r ∈ descending 20 := by
      rw [descending_eq_even 20 (by decide)]
      exact List.mem_append.mpr (Or.inl hmem)
    exact mem_descending hdesc
  have hmul : product ((evenRadices 20).take k) ≤
      product ((evenRadices 20).take k) * product ((evenRadices 20).drop k) :=
    Nat.le_mul_of_pos_right _ hpos
  rw [hall] at hmul
  exact hmul

theorem evenCount_20_lt_i64 : evenPermCount 20 ≤ i64MaxNat := by
  unfold evenPermCount i64MaxNat factorial
  decide

theorem evenCount_20_lt_limb3 : evenPermCount 20 < limbBase ^ 3 := by
  unfold evenPermCount limbBase factorial
  decide

theorem fact20_div6_lt_limb2 : factorial 20 / 6 < limbBase ^ 2 := by
  unfold factorial limbBase
  decide

theorem product_take17 :
    product ((evenRadices 20).take 17) = factorial 20 / 6 := by
  have hall : product (evenRadices 20) = evenPermCount 20 :=
    product_evenRadices 20 (by decide)
  have hlast : (evenRadices 20)[17]'(by
      rw [evenRadices_length 20 (by decide)]; decide) = 3 := by
    rw [evenRadix_get 20 17 (by decide) (by decide)]
  have hsplit : evenRadices 20 =
      (evenRadices 20).take 17 ++ [(evenRadices 20)[17]'(by
        rw [evenRadices_length 20 (by decide)]; decide)] := by
    have hlen : (evenRadices 20).length = 18 := evenRadices_length 20 (by decide)
    have := take_succ_get (evenRadices 20) 17 (by rw [hlen]; decide)
    simpa [hlen, List.take_length] using this
  rw [hsplit, product_append, hlast] at hall
  simp only [product_cons, product_nil, Nat.mul_one] at hall
  unfold evenPermCount at hall
  have hdiv : factorial 20 / 2 = product ((evenRadices 20).take 17) * 3 := hall
  have h6 : factorial 20 / 6 = (factorial 20 / 2) / 3 := by
    have hmul : (factorial 20 / 2) / 3 = factorial 20 / (2 * 3) :=
      Nat.div_div_eq_div_mul _ _ _
    have hsix : factorial 20 / (2 * 3) = factorial 20 / 6 := by
      have : 2 * 3 = 6 := by decide
      rw [this]
    exact hsix.symm.trans hmul.symm
  rw [h6, hdiv]
  exact (Nat.mul_div_cancel _ (by decide)).symm

theorem rankAcc_lt_limb2 (perm : List Nat) (h : Perm20Wf perm) (k : Nat) (hk : k ≤ 17) :
    rankAcc perm k < limbBase ^ 2 := by
  have hlt := rankAcc_bound perm h k (by omega)
  have hle : product ((evenRadices 20).take k) ≤ product ((evenRadices 20).take 17) := by
    have happ := product_append
      ((evenRadices 20).take k)
      (((evenRadices 20).take 17).drop k)
    have htake : (evenRadices 20).take k ++ ((evenRadices 20).take 17).drop k =
        (evenRadices 20).take 17 := by
      have htk : (evenRadices 20).take k = ((evenRadices 20).take 17).take k := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      rw [htk]
      exact List.take_append_drop k ((evenRadices 20).take 17)
    rw [htake] at happ
    have hpos : 0 < product (((evenRadices 20).take 17).drop k) := by
      apply product_pos
      intro r hr
      have hmem : r ∈ evenRadices 20 :=
        List.mem_of_mem_take (List.mem_of_mem_drop hr)
      have hdesc : r ∈ descending 20 := by
        rw [descending_eq_even 20 (by decide)]
        exact List.mem_append.mpr (Or.inl hmem)
      exact mem_descending hdesc
    have hmul := Nat.le_mul_of_pos_right
      (product ((evenRadices 20).take k)) hpos
    rw [← happ] at hmul
    exact hmul
  rw [product_take17] at hle
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt hle) (Nat.le_of_lt fact20_div6_lt_limb2)

theorem rankAcc_lt_count (perm : List Nat) (h : Perm20Wf perm) (k : Nat) (hk : k ≤ 18) :
    rankAcc perm k < evenPermCount 20 := by
  exact Nat.lt_of_lt_of_le (rankAcc_bound perm h k hk) (product_take_even k hk)

theorem evenRank_lt_count (perm : List Nat) (h : Perm20Wf perm) :
    evenRank perm < evenPermCount 20 := by
  rw [evenRank_eq_acc perm (by rw [h.len]; decide), h.len]
  exact rankAcc_lt_count perm h 18 (by decide)

theorem evenRank_fits (perm : List Nat) (h : Perm20Wf perm) : FitsLen (evenRank perm) :=
  FitsLen.of_le evenCount_20_lt_i64 (Nat.le_of_lt (evenRank_lt_count perm h))

theorem evenRank_lt_limb3 (perm : List Nat) (h : Perm20Wf perm) :
    evenRank perm < limbBase ^ 3 :=
  Nat.lt_of_lt_of_le (evenRank_lt_count perm h) (Nat.le_of_lt evenCount_20_lt_limb3)

/-! ## `range_list` -/

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem push_range (i : Nat) :
    (embed (List.range i)).push (i : Int) = embed (List.range (i + 1)) := by
  rw [← ofNat_eq_natCast i, push_embed, ← List.range_succ]

def rangeStep (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  let i := σ.1
  let xs := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (i, xs))
    else
      match ← ((do
        let mb := SudoRt.appendL xs i
        let xs := mb.1
        let u : Unit := ()
        let _ := u
        pure (SudoRt.Flow.cont (ρ := Array Int) xs)) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

private theorem rangeStep_hit (n i : Nat) (hn : 0 < n) (hi : i < n) (hfits : FitsLen n) :
    rangeStep (Int.ofNat (n - 1)) (Int.ofNat i, embed (List.range i)) =
      if i = n - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, embed (List.range (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), embed (List.range (i + 1)))) := by
  unfold rangeStep
  dsimp
  have hle : i ≤ n - 1 := by omega
  have hngt : ¬ (i : Int) > ((n - 1 : Nat) : Int) := ofNat_not_gt hle
  rw [if_neg hngt]
  simp only [appendL_spec, push_range, pure_eq_ok]
  by_cases heq : i = n - 1
  · simp [heq, beq_int_iff]
  · have hneI : ¬ (i : Int) = ((n - 1 : Nat) : Int) := fun h => heq (Int.ofNat.inj h)
    have hadd := addI_ofNat_one i (by
      have : i + 1 ≤ n := by omega
      exact FitsLen.of_le hfits this)
    rw [ofNat_eq_natCast i] at hadd
    simp [beq_int_iff, hneI, hadd, heq]

private theorem rangeRun (n : Nat) (hn : 0 < n) (hfits : FitsLen n) :
    SudoRt.runLoopOn (ρ := Array Int)
      ((0 : Int), embed (List.range 0))
      (fuelRange (0 : Int) (Int.ofNat (n - 1)))
      (rangeStep (Int.ofNat (n - 1)))
      (fun σ => pure σ.2)
      (fun r => pure r) =
      .ok (embed (List.range n)) := by
  have h0 : embed (List.range 0) = embed (List.range 0) := rfl
  apply chain_loop (f := fun i => embed (List.range i)) (fromN := 0) (toN := n - 1)
    (hle := by omega) (goal := .ok (embed (List.range n)))
  · intro i _ hi
    have hi' : i < n := by omega
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)] using rangeStep_hit n i hn hi' hfits
  · have : (n - 1) + 1 = n := by omega
    rw [this]
    rfl

theorem range_list_refines (n : Nat) (hn : 0 < n) (hfits : FitsLen n) :
    Megadreifach.range_list (Int.ofNat n) = .ok (embed (List.range n)) := by
  unfold Megadreifach.range_list
  rw [subI_ofNat_one n hn hfits, ok_bind]
  dsimp
  rw [show (0 : Int) = Int.ofNat 0 from rfl, fuelRange_eq, except_bind_pure,
    show (#[] : Array Int) = embed (List.range 0) by simp [List.range_zero, embed]]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := rangeStep (Int.ofNat (n - 1)))
    intro σ
    unfold rangeStep
    dsimp
    rfl
  · exact rangeRun n hn hfits

/-! ## First-hit index -/

def findStep (avail : Array Int) (target toV : Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) Megadreifach.BigInt) :=
  let t := σ.1
  let found := σ.2
  do
    if t > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (t, found))
    else
      match ← ((do
        let flag ← (if decide (found < (0 : Int)) then do
          let a ← SudoRt.atL avail t
          pure (SudoRt.SEq.beq a target)
        else
          pure false)
        if flag then
          pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) t)
        else
          pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) found)) :
          Except SudoRt.Trap (SudoRt.Flow Int Megadreifach.BigInt)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (t, fs))
      | .cont fs => do
          if t == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (t, fs))
          else do
            let t' ← SudoRt.addI t (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (t', fs))

private theorem beq_ofNat (a b : Nat) :
    SudoRt.SEq.beq (a : Int) (b : Int) = decide (a = b) := by
  rw [sEq_int, decide_eq_decide]
  constructor
  · intro h
    exact Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h)
  · intro h
    simp [h, ofNat_eq_natCast]

private def foundAt (idx t : Nat) : Int :=
  if t ≤ idx then -1 else Int.ofNat idx

private def foundNext (idx t : Nat) : Int :=
  if t < idx then -1 else Int.ofNat idx

private theorem contFinish (t toV : Nat) (st : Int) (_hle : t ≤ toV)
    (hfits : FitsLen (t + 1)) :
    (if ((t : Int) == (toV : Int)) = true then
        Except.ok (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) ((t : Int), st))
      else do
        let t' ← SudoRt.addI (t : Int) (1 : Int)
        Except.ok (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (t', st))) =
      if t = toV then
        .ok (SudoRt.Flow.brk (Int.ofNat t, st))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (t + 1), st)) := by
  by_cases heq : t = toV
  · simp [heq, beq_int_iff]
  · have hneI : ¬ (t : Int) = (toV : Int) := fun h => heq (Int.ofNat.inj h)
    have hadd := addI_ofNat_one t hfits
    rw [ofNat_eq_natCast t] at hadd
    simp [beq_int_iff, hneI, hadd, heq, ofNat_eq_natCast]

private theorem findStep_hit (avail : List Nat) (v : Nat) (hv : v ∈ avail)
    (hfits : FitsLen avail.length) (t : Nat) (ht : t < avail.length) :
    let idx := avail.findIdx (· == v)
    findStep (embed avail) (Int.ofNat v) (Int.ofNat (avail.length - 1))
        (Int.ofNat t, foundAt idx t) =
      if t = avail.length - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat t, foundNext idx t))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (t + 1), foundNext idx t)) := by
  intro idx
  have hidxLt : idx < avail.length := findIdx_lt_mem avail hv
  have hget : avail[idx] = v := get_findIdx avail hv
  have hle : t ≤ avail.length - 1 := by omega
  have hstep : FitsLen (t + 1) := FitsLen.of_le hfits (by omega)
  unfold findStep
  dsimp
  have hngt : ¬ (t : Int) > ((avail.length - 1 : Nat) : Int) := by
    simpa [ofNat_eq_natCast] using ofNat_not_gt hle
  rw [if_neg hngt]
  have hat := atL_embed avail t ht
  simp only [ofNat_eq_natCast] at hat
  have hneg : decide ((-1 : Int) < 0) = true := by decide
  have htail := contFinish t (avail.length - 1) (foundNext idx t) hle hstep
  by_cases hbefore : t < idx
  · have hfound : foundAt idx t = -1 := by simp [foundAt, Nat.le_of_lt hbefore]
    have hnext : foundNext idx t = -1 := by simp [foundNext, hbefore]
    have hne : decide (avail[t] = v) = false := by
      have hp := List.not_of_lt_findIdx (xs := avail) (p := (· == v)) hbefore
      simpa [BEq.beq] using hp
    rw [hfound, hneg, hat, ok_bind, beq_ofNat, hne, pure_eq_ok, hnext]
    simp only [if_true, Bool.false_eq_true, ite_false, ok_bind, pure_eq_ok]
    rw [hnext] at htail
    exact htail
  · have hge : idx ≤ t := Nat.le_of_not_lt hbefore
    have hnext : foundNext idx t = Int.ofNat idx := by simp [foundNext, hbefore]
    by_cases heq : t = idx
    · have hfound : foundAt idx t = -1 := by simp [foundAt, heq]
      have hvEq : avail[t] = v := by simpa [heq] using hget
      rw [hfound, hneg, hat, ok_bind, beq_ofNat]
      simp only [hvEq, decide_True, if_true, pure_eq_ok, ok_bind, hnext]
      rw [hnext] at htail
      rw [heq] at htail ⊢
      exact htail
    · have hgt : idx < t := Nat.lt_of_le_of_ne hge (Ne.symm heq)
      have hfound : foundAt idx t = Int.ofNat idx := by simp [foundAt, hgt]
      have hnn : decide (Int.ofNat idx < 0) = false := by
        simp [Int.not_lt.mpr (Int.ofNat_nonneg idx)]
      rw [hfound, hnn, pure_eq_ok, hnext]
      simp only [Bool.false_eq_true, ite_false, ok_bind, pure_eq_ok]
      rw [hnext] at htail
      exact htail

private theorem foundAt_zero (idx : Nat) : foundAt idx 0 = -1 := by
  simp [foundAt]

private theorem foundAt_succ (idx i : Nat) : foundNext idx i = foundAt idx (i + 1) := by
  simp only [foundNext, foundAt]
  by_cases h : i < idx
  · simp [h, Nat.succ_le_of_lt h]
  · have : ¬ i + 1 ≤ idx := by omega
    simp [h, this]

private theorem foundAt_done (avail : List Nat) (idx : Nat) (h : idx < avail.length) :
    foundAt idx avail.length = Int.ofNat idx := by
  simp [foundAt, Nat.not_le.mpr h]

theorem find_loop (avail : List Nat) (v : Nat) (hv : v ∈ avail)
    (hfits : FitsLen avail.length) :
    let idx := avail.findIdx (· == v)
    SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
      ((0 : Int), (-1 : Int))
      (fuelRange (0 : Int) (Int.ofNat (avail.length - 1)))
      (findStep (embed avail) ((v : Int)) (Int.ofNat (avail.length - 1)))
      (fun σ => (pure σ.2 : Except SudoRt.Trap Int))
      (fun _ => pure (0 : Int)) =
      .ok (Int.ofNat idx) := by
  intro idx
  have hidxLt : idx < avail.length := findIdx_lt_mem avail hv
  have hpos : 0 < avail.length := Nat.zero_lt_of_lt hidxLt
  rw [show (-1 : Int) = foundAt idx 0 from (foundAt_zero idx).symm]
  apply chain_loop (f := fun i => foundAt idx i) (fromN := 0) (toN := avail.length - 1)
    (hle := Nat.zero_le _) (goal := .ok (Int.ofNat idx))
  · intro i _ hi
    have hi' : i < avail.length := by omega
    have hs := findStep_hit avail v hv hfits i hi'
    simp only [ofNat_eq_natCast] at hs ⊢
    simp only [hs, foundAt_succ]
  · rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos), foundAt_done avail idx hidxLt, pure_eq_ok]

/-! ## Drop one index -/

def takeSkip (xs : List Nat) (idx k : Nat) : List Nat :=
  if k ≤ idx then xs.take k
  else xs.take idx ++ (xs.take k).drop (idx + 1)

theorem takeSkip_zero (xs : List Nat) (idx : Nat) : takeSkip xs idx 0 = [] := by
  simp [takeSkip, List.take_zero]

theorem takeSkip_succ (xs : List Nat) (idx k : Nat) (hk : k < xs.length) :
    takeSkip xs idx (k + 1) =
      if k = idx then takeSkip xs idx k else takeSkip xs idx k ++ [xs[k]] := by
  have htake := take_succ_get xs k hk
  by_cases hle1 : k + 1 ≤ idx
  · have hle : k ≤ idx := by omega
    have hne : k ≠ idx := by omega
    simp [takeSkip, hle1, hle, hne, htake]
  · by_cases hle : k ≤ idx
    · have heq : k = idx := by omega
      have hnot : ¬ idx + 1 ≤ idx := by omega
      have hnil : (xs.take (idx + 1)).drop (idx + 1) = [] := by
        apply List.drop_eq_nil_of_le
        rw [List.length_take]
        omega
      simp [takeSkip, hle1, hle, heq, hnot, hnil]
    · have hne : k ≠ idx := by omega
      have hdrop : idx + 1 ≤ (xs.take k).length := by
        rw [List.length_take, Nat.min_eq_left (by omega)]
        omega
      simp [takeSkip, hle1, hle, hne, htake, List.drop_append_of_le_length hdrop]

theorem takeSkip_erase (xs : List Nat) (idx : Nat) (h : idx < xs.length) :
    takeSkip xs idx xs.length = xs.eraseIdx idx := by
  have hgt : ¬ xs.length ≤ idx := Nat.not_le_of_gt h
  simp [takeSkip, hgt, List.take_length, List.eraseIdx_eq_take_drop_succ]

def eraseStep (avail : Array Int) (idx toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) Megadreifach.BigInt) :=
  let t := σ.1
  let fresh := σ.2
  do
    if t > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (t, fresh))
    else
      match ← ((do
        if !(SudoRt.SEq.beq t idx) then
          do
            let x ← SudoRt.atL avail t
            let mb := SudoRt.appendL fresh x
            let fresh := mb.1
            let u : Unit := ()
            let _ := u
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) fresh)
        else
          pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) fresh)) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (t, fs))
      | .cont fs => do
          if t == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (t, fs))
          else do
            let t' ← SudoRt.addI t (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (t', fs))

private theorem eraseFinish (t toV : Nat) (st : Array Int) (_hle : t ≤ toV)
    (hfits : FitsLen (t + 1)) :
    (if ((t : Int) == (toV : Int)) = true then
        Except.ok (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) ((t : Int), st))
      else do
        let t' ← SudoRt.addI (t : Int) (1 : Int)
        Except.ok (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (t', st))) =
      if t = toV then
        .ok (SudoRt.Flow.brk (Int.ofNat t, st))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (t + 1), st)) := by
  by_cases heq : t = toV
  · simp [heq, beq_int_iff]
  · have hneI : ¬ (t : Int) = (toV : Int) := fun h => heq (Int.ofNat.inj h)
    have hadd := addI_ofNat_one t hfits
    rw [ofNat_eq_natCast t] at hadd
    simp [beq_int_iff, hneI, hadd, heq, ofNat_eq_natCast]

private theorem eraseStep_hit (xs : List Nat) (idx t : Nat)
    (_hidx : idx < xs.length) (ht : t < xs.length) (hfits : FitsLen xs.length) :
    eraseStep (embed xs) (Int.ofNat idx) (Int.ofNat (xs.length - 1))
        (Int.ofNat t, embed (takeSkip xs idx t)) =
      if t = xs.length - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat t, embed (takeSkip xs idx (t + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (t + 1), embed (takeSkip xs idx (t + 1)))) := by
  have hle : t ≤ xs.length - 1 := by omega
  have hstep : FitsLen (t + 1) := FitsLen.of_le hfits (by omega)
  have hnext := takeSkip_succ xs idx t ht
  unfold eraseStep
  dsimp
  have hngt : ¬ (t : Int) > ((xs.length - 1 : Nat) : Int) := by
    simpa [ofNat_eq_natCast] using ofNat_not_gt hle
  rw [if_neg hngt]
  have htail := eraseFinish t (xs.length - 1) (embed (takeSkip xs idx (t + 1))) hle hstep
  by_cases heq : t = idx
  · rw [beq_ofNat, heq]
    simp only [decide_True, Bool.not_true, Bool.false_eq_true, ite_false, pure_eq_ok,
      ok_bind]
    have hsame : takeSkip xs idx (idx + 1) = takeSkip xs idx idx := by
      simpa using takeSkip_succ xs idx idx (heq ▸ ht)
    rw [heq] at htail
    rw [hsame] at htail ⊢
    exact htail
  · have hat := atL_embed xs t ht
    simp only [ofNat_eq_natCast] at hat
    rw [beq_ofNat, hat, ok_bind]
    simp only [heq, decide_False, Bool.not_false, if_true, appendL_spec, pure_eq_ok, ok_bind]
    have hpush : (embed (takeSkip xs idx t)).push (xs[t] : Int) =
        embed (takeSkip xs idx t ++ [xs[t]]) := by
      rw [← ofNat_eq_natCast (xs[t]), push_embed]
    rw [hpush]
    rw [hnext, if_neg heq] at htail ⊢
    exact htail

theorem erase_loop (xs : List Nat) (idx : Nat) (hidx : idx < xs.length)
    (hfits : FitsLen xs.length) :
    SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
      ((0 : Int), embed (takeSkip xs idx 0))
      (fuelRange (0 : Int) (Int.ofNat (xs.length - 1)))
      (eraseStep (embed xs) (Int.ofNat idx) (Int.ofNat (xs.length - 1)))
      (fun σ => (pure σ.2 : Except SudoRt.Trap (Array Int)))
      (fun _ => pure (#[] : Array Int)) =
      .ok (embed (xs.eraseIdx idx)) := by
  apply chain_loop (f := fun i => embed (takeSkip xs idx i)) (fromN := 0)
    (toN := xs.length - 1) (hle := Nat.zero_le _)
    (goal := .ok (embed (xs.eraseIdx idx)))
  · intro i _ hi
    have hi' : i < xs.length := by omega
    have hs := eraseStep_hit xs idx i hidx hi' hfits
    simp only [ofNat_eq_natCast] at hs ⊢
    simp only [hs]
  · rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hidx)),
      takeSkip_erase xs idx hidx, pure_eq_ok]

/-! ## Loop break states -/

theorem find_breaks {α : Type} (avail : List Nat) (v : Nat) (hv : v ∈ avail)
    (hfits : FitsLen avail.length)
    (after : Int × Int → Except SudoRt.Trap α)
    (onRet : Megadreifach.BigInt → Except SudoRt.Trap α) :
    let idx := avail.findIdx (· == v)
    SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
      ((0 : Int), (-1 : Int))
      (fuelRange (0 : Int) (Int.ofNat (avail.length - 1)))
      (findStep (embed avail) (v : Int) (Int.ofNat (avail.length - 1)))
      after onRet =
      after (Int.ofNat (avail.length - 1), Int.ofNat idx) := by
  intro idx
  have hidxLt : idx < avail.length := findIdx_lt_mem avail hv
  have hpos : 0 < avail.length := Nat.zero_lt_of_lt hidxLt
  rw [show (-1 : Int) = foundAt idx 0 from (foundAt_zero idx).symm]
  apply chain_loop (f := fun i => foundAt idx i) (fromN := 0) (toN := avail.length - 1)
    (hle := Nat.zero_le _)
    (goal := after (Int.ofNat (avail.length - 1), Int.ofNat idx))
  · intro i _ hi
    have hi' : i < avail.length := by omega
    have hs := findStep_hit avail v hv hfits i hi'
    simp only [ofNat_eq_natCast] at hs ⊢
    simp only [hs, foundAt_succ]
  · rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos), foundAt_done avail idx hidxLt]

theorem erase_breaks {α : Type} (xs : List Nat) (idx : Nat) (hidx : idx < xs.length)
    (hfits : FitsLen xs.length)
    (after : Int × Array Int → Except SudoRt.Trap α)
    (onRet : Megadreifach.BigInt → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
      ((0 : Int), embed (takeSkip xs idx 0))
      (fuelRange (0 : Int) (Int.ofNat (xs.length - 1)))
      (eraseStep (embed xs) (Int.ofNat idx) (Int.ofNat (xs.length - 1)))
      after onRet =
      after (Int.ofNat (xs.length - 1), embed (xs.eraseIdx idx)) := by
  apply chain_loop (f := fun i => embed (takeSkip xs idx i)) (fromN := 0)
    (toN := xs.length - 1) (hle := Nat.zero_le _)
    (goal := after (Int.ofNat (xs.length - 1), embed (xs.eraseIdx idx)))
  · intro i _ hi
    have hi' : i < xs.length := by omega
    have hs := eraseStep_hit xs idx i hidx hi' hfits
    simp only [ofNat_eq_natCast] at hs ⊢
    simp only [hs]
  · rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hidx)),
      takeSkip_erase xs idx hidx]

/-! ## Rank stays in the proved bigint fragment -/

/-- Length-20 permutations whose even-Lehmer value is `< 2 · 10^9`.

    Corner width is 20, but an arbitrary corner rank is `< 20!/2` (three
    limbs). This bound keeps every Horner step inside the one-limb multiply
    and two-limb add already proved for `pack_ori3`. -/
structure Rank20Wf (perm : List Nat) : Prop where
  base : Perm20Wf perm
  small : evenRank perm < 2 * limbBase

structure WellFormedRank20 (a : Array Int) : Prop where
  base : WellFormedPerm20 a
  small : evenRank (decode a) < 2 * limbBase

theorem rank20_embed (perm : List Nat) (h : Rank20Wf perm) :
    WellFormedRank20 (embed perm) where
  base := perm20_embed perm h.base
  small := by rw [decode_embed]; exact h.small

theorem rank20_decode (a : Array Int) (h : WellFormedRank20 a) :
    Rank20Wf (decode a) where
  base := perm20_decode a h.base
  small := h.small

theorem rankAcc_le_succ (perm : List Nat) (h : Perm20Wf perm) (k : Nat) (hk : k < 18) :
    rankAcc perm k ≤ rankAcc perm (k + 1) := by
  have hs := rankAcc_succ perm k (by rw [h.len]; omega)
  rw [hs]
  refine Nat.le_trans ?_ (Nat.le_add_right _ _)
  refine Nat.le_mul_of_pos_right _ ?_
  have hn : 2 ≤ perm.length := by rw [h.len]; decide
  have hv := evenRadix_get perm.length k hn (by rw [h.len]; omega)
  rw [hv, h.len]
  omega

theorem rankAcc_le_even (perm : List Nat) (h : Perm20Wf perm) (k : Nat) (hk : k ≤ 18) :
    rankAcc perm k ≤ evenRank perm := by
  have he := evenRank_eq_acc perm (by rw [h.len]; decide)
  rw [he, h.len]
  suffices ∀ j, j ≤ 18 → rankAcc perm (18 - j) ≤ rankAcc perm 18 by
    have happ := this (18 - k) (Nat.sub_le 18 k)
    have hk' : 18 - (18 - k) = k := by omega
    simpa [hk'] using happ
  intro j
  induction j with
  | zero =>
    intro _
    simp
  | succ j ih =>
    intro hj
    have hk' : 18 - (j + 1) < 18 := by omega
    have hstep := rankAcc_le_succ perm h (18 - (j + 1)) hk'
    have heq : 18 - (j + 1) + 1 = 18 - j := by omega
    rw [heq] at hstep
    exact Nat.le_trans hstep (ih (by omega))

theorem rankAcc_lt_limb (perm : List Nat) (h : Rank20Wf perm) (k : Nat) (hk : k ≤ 17) :
    rankAcc perm k < limbBase := by
  rcases Nat.lt_or_ge (rankAcc perm k) limbBase with hlt | hge'
  · exact hlt
  · have hs := rankAcc_succ perm k (by rw [h.base.len]; omega)
    have hn : 2 ≤ perm.length := by rw [h.base.len]; decide
    have hv := evenRadix_get perm.length k hn (by rw [h.base.len]; omega)
    have hnext : limbBase * 3 ≤ rankAcc perm (k + 1) := by
      rw [hs, hv]
      simp only [h.base.len]
      have h3 : 3 ≤ 20 - k := by omega
      have hmul : limbBase * 3 ≤ rankAcc perm k * (20 - k) := Nat.mul_le_mul hge' h3
      exact Nat.le_trans hmul (Nat.le_add_right _ _)
    have hrest : rankAcc perm (k + 1) ≤ evenRank perm :=
      rankAcc_le_even perm h.base (k + 1) (by omega)
    have hthree : 2 * limbBase < limbBase * 3 := by
      unfold limbBase
      decide
    have hsmall := h.small
    omega

theorem rankAcc_lt_two (perm : List Nat) (h : Rank20Wf perm) (k : Nat) (hk : k ≤ 18) :
    rankAcc perm k < 2 * limbBase :=
  Nat.lt_of_le_of_lt (rankAcc_le_even perm h.base k hk) h.small

theorem negI_one : SudoRt.negI (1 : Int) = .ok (-1) := by
  unfold SudoRt.negI SudoRt.narrowI
  have hmin : ¬ (-1 : Int) < SudoRt.i64Min := by decide
  have hmax : ¬ (-1 : Int) > SudoRt.i64Max := by decide
  simp [hmin, hmax]

private theorem decide_nat_ge_zero (n : Nat) : decide ((n : Int) ≥ 0) = true := by
  simpa [ofNat_eq_natCast] using decide_eq_true (Int.ofNat_nonneg n)

private theorem subI_cast (a b : Nat) (hfits : FitsLen a) (hle : b ≤ a) :
    SudoRt.subI (a : Int) (b : Int) = .ok ((a - b : Nat) : Int) := by
  rw [← ofNat_eq_natCast a, ← ofNat_eq_natCast b, subI_ofNat a b hfits hle, ofNat_eq_natCast]

private theorem subI_cast_one (n : Nat) (hpos : 0 < n) (h : FitsLen n) :
    SudoRt.subI (n : Int) 1 = .ok ((n - 1 : Nat) : Int) := by
  rw [← ofNat_eq_natCast n, subI_ofNat_one n hpos h, ofNat_eq_natCast]

private theorem big_from_int_cast (v : Nat) (hv : FitsLen v) :
    Megadreifach.big_from_int (v : Int) = .ok (bigNat v) := by
  simpa [ofNat_eq_natCast] using big_from_int_refines v hv

private theorem addI_cast_one (n : Nat) (h : FitsLen (n + 1)) :
    SudoRt.addI (n : Int) 1 = .ok ((n + 1 : Nat) : Int) := by
  rw [← ofNat_eq_natCast n, addI_ofNat_one n h, ofNat_eq_natCast]

private theorem subI_20_3 :
    SudoRt.subI (20 : Int) (3 : Int) = .ok (17 : Int) := by
  have h : FitsLen 20 := by unfold FitsLen i64MaxNat; decide
  simpa using subI_ofNat 20 3 h (by decide)

private theorem fits20 : FitsLen 20 := by
  unfold FitsLen i64MaxNat
  decide

/-- One outer step of `even_perm_rank_big` on a concrete index. -/
private theorem rank_step_nat (perm : List Nat) (h : Rank20Wf perm) (i : Nat) (hi : i ≤ 17) :
    let avail := availAt perm i
    let idx := avail.findIdx (· == perm[i]'(by rw [h.base.len]; omega))
    let rad := 20 - i
    Megadreifach.big_mul (bigNat (rankAcc perm i)) (bigNat rad) = .ok (bigNat (rankAcc perm i * rad)) ∧
    Megadreifach.big_add (bigNat (rankAcc perm i * rad)) (bigNat idx) =
      .ok (bigNat (rankAcc perm (i + 1))) := by
  intro avail idx rad
  have hbase := h.base
  have hacc : rankAcc perm i < limbBase := rankAcc_lt_limb perm h i hi
  have hrad0 : 0 < rad := by simp [rad]; omega
  have hradL : rad < limbBase := by simp [rad, limbBase]; omega
  have hidxLt : idx < avail.length :=
    findIdx_lt_mem avail (mem_availAt perm hbase i (by omega))
  have hidxB : idx < limbBase := by
    have hlen := availAt_length perm hbase i (by omega)
    have : idx < 20 - i := by simpa [hlen] using hidxLt
    unfold limbBase
    omega
  have hn : 2 ≤ perm.length := by rw [hbase.len]; decide
  have hv := evenRadix_get perm.length i hn (by rw [hbase.len]; omega)
  have hidxEq : idx =
      (evenDigits perm)[i]'(by
        simp [evenDigits, List.length_take, lehmerDigits_length, hbase.len]; omega) := by
    simpa [avail, idx] using ((digit_lt_len perm hbase i (by omega)).1).symm
  have heq : rankAcc perm i * rad + idx = rankAcc perm (i + 1) := by
    have hs := rankAcc_succ perm i (by rw [hbase.len]; omega)
    rw [hs, hv]
    simp [hbase.len, rad, hidxEq]
  have hprod : rankAcc perm i * rad < 2 * limbBase := by
    have hsum := rankAcc_lt_two perm h (i + 1) (by omega)
    have : rankAcc perm i * rad ≤ rankAcc perm i * rad + idx := Nat.le_add_right _ _
    exact Nat.lt_of_le_of_lt (Nat.le_trans this (Nat.le_of_eq heq)) hsum
  have hsumLt : rankAcc perm i * rad + idx < 2 * limbBase := by
    rw [heq]
    exact rankAcc_lt_two perm h (i + 1) (by omega)
  refine ⟨?_, ?_⟩
  · exact big_mul_acc (rankAcc perm i) rad hrad0 hradL hacc
  · rw [big_add_wide (rankAcc perm i * rad) idx hprod hidxB hsumLt, heq]

/-- Find loop as emitted: the sought value is `perm[i]`. -/
def findPerm (avail permA : Array Int) (ix toV : Int) (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Int) Megadreifach.BigInt) :=
  let t := σ.1
  let found := σ.2
  do
    if t > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (t, found))
    else
      match ← ((do
        let flag ← (if decide (found < (0 : Int)) then do
          let a ← SudoRt.atL avail t
          let b ← SudoRt.atL permA ix
          pure (SudoRt.SEq.beq a b)
        else
          pure false)
        if flag then
          do
            let found := t
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) found)
        else
          do
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) found)) :
          Except SudoRt.Trap (SudoRt.Flow Int Megadreifach.BigInt)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (t, fs))
      | .cont fs => do
          if t == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (t, fs))
          else do
            let t' ← SudoRt.addI t (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (t', fs))

theorem findPerm_eq (avail : Array Int) (perm : List Nat) (i : Nat)
    (hi : i < perm.length) (toV : Int) (σ : Int × Int) :
    findPerm avail (embed perm) (Int.ofNat i) toV σ =
      findStep avail (Int.ofNat perm[i]) toV σ := by
  unfold findPerm findStep
  dsimp
  rw [← ofNat_eq_natCast i, atL_embed perm i hi]
  simp [ok_bind, pure_eq_ok, ofNat_eq_natCast]

def rankAfter (n i : Int) (rank : Megadreifach.BigInt) (avail : Array Int)
    (σ : Int × Int) :
    Except SudoRt.Trap (SudoRt.Flow (Megadreifach.BigInt × Array Int) Megadreifach.BigInt) := do
  let found := σ.2
  let _ ← SudoRt.sudoAssert (decide (found ≥ (0 : Int))) 556
  let idx := found
  let rad ← SudoRt.subI n i
  let rb ← Megadreifach.big_from_int rad
  let prod ← Megadreifach.big_mul rank rb
  let db ← Megadreifach.big_from_int idx
  let rank' ← Megadreifach.big_add prod db
  let fresh : Array Int := #[]
  let toE ← SudoRt.subI (SudoRt.listLen avail) 1
  let fromE : Int := 0
  let fuel := if fromE > toE then 1 else (toE - fromE).natAbs + 1
  let init := (fromE, fresh)
  let _out ← SudoRt.runLoopOn (ρ := Megadreifach.BigInt) init fuel
    (eraseStep avail idx toE)
    (fun σ2 =>
      let fresh := σ2.2
      do
        let avail := fresh
        pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (rank', avail)))
    (fun r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r))
  pure _out

def rankStep (permA : Array Int) (n toV : Int)
    (σ : Int × (Megadreifach.BigInt × Array Int)) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × (Megadreifach.BigInt × Array Int)) Megadreifach.BigInt) :=
  let i := σ.1
  let rank := σ.2.1
  let sp := σ.2.2
  let avail := sp
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, rank, avail))
    else
      match ← ((do
        let found0 ← SudoRt.negI (1 : Int)
        let found := found0
        let toA ← SudoRt.subI (SudoRt.listLen avail) 1
        let fromA : Int := 0
        let fuel := if fromA > toA then 1 else (toA - fromA).natAbs + 1
        let init := (fromA, found)
        let _out ← SudoRt.runLoopOn (ρ := Megadreifach.BigInt) init fuel
          (findPerm avail permA i toA)
          (rankAfter n i rank avail)
          (fun r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r))
        pure _out) : Except SudoRt.Trap (SudoRt.Flow _ Megadreifach.BigInt)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (i', fs))

private theorem rankStep_hit (perm : List Nat) (h : Rank20Wf perm) (i : Nat) (hi : i ≤ 17) :
    rankStep (embed perm) (20 : Int) (17 : Int)
        (Int.ofNat i, bigNat (rankAcc perm i), embed (availAt perm i)) =
      if i = 17 then
        .ok (SudoRt.Flow.brk (Int.ofNat i,
          bigNat (rankAcc perm (i + 1)), embed (availAt perm (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
          bigNat (rankAcc perm (i + 1)), embed (availAt perm (i + 1)))) := by
  have hbase := h.base
  have hi20 : i < 20 := by omega
  have hlenA := availAt_length perm hbase i (by omega)
  have hmem := mem_availAt perm hbase i hi20
  have hfitsA : FitsLen (availAt perm i).length := by
    rw [hlenA]
    exact FitsLen.of_le fits20 (by omega)
  unfold rankStep
  dsimp
  have hngt : ¬ (i : Int) > (17 : Int) := ofNat_not_gt hi
  rw [if_neg hngt, negI_one, ok_bind, listLen_embed, hlenA]
  have hposA : 0 < 20 - i := by omega
  have hsubA := subI_ofNat_one (20 - i) hposA (FitsLen.of_le fits20 (by omega))
  rw [hsubA, ok_bind]
  have hfun : findPerm (embed (availAt perm i)) (embed perm) (Int.ofNat i)
        (Int.ofNat (20 - i - 1)) =
      findStep (embed (availAt perm i)) (Int.ofNat (perm[i]'(by rw [hbase.len]; exact hi20)))
        (Int.ofNat (20 - i - 1)) := by
    funext σ
    exact findPerm_eq _ perm i (by rw [hbase.len]; exact hi20) _ σ
  simp only [ofNat_eq_natCast] at hfun ⊢
  rw [hfun]
  rw [show (20 - i - 1) = (availAt perm i).length - 1 by rw [hlenA]]
  rw [fuelRange_eq, ← ofNat_eq_natCast ((availAt perm i).length - 1)]
  rw [find_breaks (availAt perm i) (perm[i]'(by rw [hbase.len]; exact hi20)) hmem hfitsA]
  -- continuation at the found index
  dsimp [rankAfter]
  have hidxLt := findIdx_lt_mem (availAt perm i) hmem
  rw [decide_nat_ge_zero, sudoAssert_true, ok_bind]
  have hsubN : SudoRt.subI (20 : Int) (i : Int) = .ok ((20 - i : Nat) : Int) := by
    rw [show (20 : Int) = Int.ofNat 20 from rfl, ← ofNat_eq_natCast i]
    simpa [ofNat_eq_natCast] using subI_ofNat 20 i fits20 (by omega)
  rw [hsubN, ok_bind]
  have hradFit : FitsLen (20 - i) := FitsLen.of_le fits20 (by omega)
  rw [big_from_int_cast (20 - i) hradFit, ok_bind]
  have hpair := rank_step_nat perm h i hi
  have hmul := hpair.1
  simp only [hbase.len] at hmul
  rw [hmul, ok_bind]
  have hidxFit : FitsLen ((availAt perm i).findIdx (· == perm[i]'(by rw [hbase.len]; exact hi20))) := by
    exact FitsLen.of_le fits20 (by
      have := hidxLt
      rw [hlenA] at this
      omega)
  rw [big_from_int_cast _ hidxFit, ok_bind]
  have hadd := hpair.2
  simp only [hbase.len] at hadd
  rw [hadd, ok_bind, listLen_embed, hlenA]
  rw [subI_ofNat_one (20 - i) hposA (FitsLen.of_le fits20 (by omega)), ok_bind]
  have hidxL : (availAt perm i).findIdx (· == perm[i]'(by rw [hbase.len]; exact hi20)) <
      (availAt perm i).length := hidxLt
  rw [show (#[] : Array Int) = embed (takeSkip (availAt perm i)
        ((availAt perm i).findIdx (· == perm[i]'(by rw [hbase.len]; exact hi20))) 0) by
      rw [takeSkip_zero, embed_nil]]
  rw [fuelRange_eq]
  rw [show (20 - i - 1) = (availAt perm i).length - 1 by rw [hlenA]]
  rw [← ofNat_eq_natCast ((availAt perm i).findIdx (· == perm[i]'(by rw [hbase.len]; exact hi20)))]
  rw [erase_breaks (availAt perm i) _ hidxL hfitsA]
  simp only [availAt_erase perm i (by rw [hbase.len]; exact hi20), pure_eq_ok, ok_bind]
  -- outer break / continue
  by_cases heq : i = 17
  · simp [heq, beq_int_iff, pure_eq_ok]
  · have hneI : ¬ (i : Int) = (17 : Int) := fun hq => heq (Int.ofNat.inj hq)
    have haddI := addI_cast_one i (FitsLen.of_le fits20 (by omega))
    simp [beq_int_iff, hneI, haddI, pure_eq_ok, ok_bind, heq]

private theorem availAt_zero (perm : List Nat) (h : Perm20Wf perm) :
    availAt perm 0 = List.range 20 := by
  simp [availAt, dropUsed, List.take_zero, h.len]

/-- Outer Lehmer loop, `i = 0` to `17`, on a small length-20 rank. -/
private theorem rankRun (perm : List Nat) (h : Rank20Wf perm) :
    SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
      (Int.ofNat 0, (bigNat (rankAcc perm 0), embed (availAt perm 0)))
      (fuelRange (Int.ofNat 0) (Int.ofNat 17))
      (rankStep (embed perm) (Int.ofNat 20) (Int.ofNat 17))
      (fun σ => pure σ.2.1)
      (fun r => pure r) =
      .ok (bigNat (evenRank perm)) := by
  apply chain_loop
    (f := fun i => (bigNat (rankAcc perm i), embed (availAt perm i)))
    (fromN := 0) (toN := 17) (hle := by decide)
    (goal := .ok (bigNat (evenRank perm)))
  · intro i _ hi
    simpa using rankStep_hit perm h i hi
  · rw [evenRank_eq_acc perm (by rw [h.base.len]; decide), h.base.len]
    rfl

/-- `Generated.even_perm_rank_big` is algebraic `evenRank` on `Rank20Wf`. -/
theorem even_perm_rank_big_refines (perm : List Nat) (h : Rank20Wf perm) :
    Megadreifach.even_perm_rank_big (embed perm) = .ok (bigNat (evenRank perm)) := by
  unfold Megadreifach.even_perm_rank_big
  rw [listLen_embed, h.base.len]
  dsimp
  rw [show (20 : Int) = Int.ofNat 20 from rfl]
  rw [range_list_refines 20 (by decide) fits20, ok_bind]
  rw [big_zero_spec, ok_bind]
  rw [show (3 : Int) = Int.ofNat 3 from rfl]
  rw [subI_ofNat 20 3 fits20 (by decide), ok_bind]
  dsimp
  have hfuel : fuelRange (Int.ofNat 0) (Int.ofNat 17) = 18 := by
    rw [fuelRange_le (by decide)]
  rw [← hfuel, except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := rankStep (embed perm) (Int.ofNat 20) (Int.ofNat 17))
    intro σ
    unfold rankStep findPerm rankAfter eraseStep
    dsimp
    rfl
  · rw [show bigOf [] = bigNat (rankAcc perm 0) by rw [rankAcc_zero, bigNat_zero],
      show embed (List.range 20) = embed (availAt perm 0) from
        (congrArg embed (availAt_zero perm h.base)).symm]
    exact rankRun perm h

theorem even_perm_rank_big_refines_array (a : Array Int) (h : WellFormedRank20 a) :
    Megadreifach.even_perm_rank_big a = .ok (bigNat (evenRank (decode a))) := by
  have hr := even_perm_rank_big_refines (decode a) (rank20_decode a h)
  simpa [embed_decode a h.base.nn] using hr

end MegaDreifach.Link2
