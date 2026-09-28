/-
  LINK 2 (private copy). Pure-Nat model of the emitted schoolbook `big_mul`
  for arbitrary multi-limb factors: `rowRun`/`innerRun` and their value
  invariants. No Generated code here.
-/
import MegaDreifach.Link2.MulLeft

namespace MegaDreifach.Link2

/-- `getD` at an in-range index. Core Lean v4.14 has no `List.getD_eq_getElem`
    (only `getD_eq_getElem?_getD`), so it is stated here. -/
theorem getD_eq_getElem' (l : List Nat) (i : Nat) (h : i < l.length) :
    l.getD i 0 = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem h]

theorem limbVal_append (a b : List Nat) :
    limbVal (a ++ b) = limbVal a + limbBase ^ a.length * limbVal b := by
  induction a with
  | nil => simp [limbVal]
  | cons x xs ih =>
    show x + limbBase * limbVal (xs ++ b) =
      (x + limbBase * limbVal xs) + limbBase ^ (xs.length + 1) * limbVal b
    rw [ih, Nat.pow_succ, Nat.mul_add, Nat.mul_comm (limbBase ^ xs.length) limbBase,
      Nat.mul_assoc]
    omega

theorem limbVal_replicate_zero (n : Nat) : limbVal (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, limbVal, ih]

theorem limbVal_set (l : List Nat) (k v : Nat) (hk : k < l.length) :
    limbVal (l.set k v) + l.getD k 0 * limbBase ^ k = limbVal l + v * limbBase ^ k := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero => simp [limbVal]; omega
    | succ k =>
      have hk' : k < as.length := by simpa using hk
      have := ih k hk'
      simp only [List.set_cons_succ, limbVal, List.getD_cons_succ, Nat.pow_succ]
      have e1 : as.getD k 0 * (limbBase ^ k * limbBase) =
          limbBase * (as.getD k 0 * limbBase ^ k) := by
        rw [Nat.mul_comm (limbBase ^ k) limbBase, ← Nat.mul_assoc, Nat.mul_comm _ limbBase,
          Nat.mul_assoc]
      have e2 : v * (limbBase ^ k * limbBase) = limbBase * (v * limbBase ^ k) := by
        rw [Nat.mul_comm (limbBase ^ k) limbBase, ← Nat.mul_assoc, Nat.mul_comm _ limbBase,
          Nat.mul_assoc]
      rw [e1, e2]
      have h2 : limbBase * limbVal (as.set k v) + limbBase * (as.getD k 0 * limbBase ^ k) =
          limbBase * limbVal as + limbBase * (v * limbBase ^ k) := by
        rw [← Nat.mul_add, ← Nat.mul_add, this]
      omega

theorem getD_replicate_zero (n k : Nat) : (List.replicate n 0).getD k 0 = 0 := by
  induction n generalizing k with
  | zero => simp [List.getD]
  | succ n ih => cases k with
    | zero => simp [List.replicate_succ]
    | succ k => simp only [List.replicate_succ, List.getD_cons_succ, ih]

theorem getD_set_ne (l : List Nat) (k j v : Nat) (h : k ≠ j) :
    (l.set k v).getD j 0 = l.getD j 0 := by
  simp [List.getD, List.getElem?_set_ne h]

theorem getD_set_eq (l : List Nat) (k v : Nat) (h : k < l.length) :
    (l.set k v).getD k 0 = v := by
  simp [List.getD, List.getElem?_set_self h]

theorem mem_set_digits (l : List Nat) (k v : Nat) (hl : ∀ d ∈ l, d < limbBase)
    (hv : v < limbBase) : ∀ d ∈ l.set k v, d < limbBase := by
  intro d hd
  rcases List.mem_or_eq_of_mem_set hd with h | h
  · exact hl d h
  · subst h; exact hv

theorem getD_lt_of_digits (l : List Nat) (hl : ∀ d ∈ l, d < limbBase) (k : Nat) :
    l.getD k 0 < limbBase := by
  by_cases hk : k < l.length
  · rw [getD_eq_getElem' l k hk]; exact hl _ (List.getElem_mem hk)
  · simp [List.getD, List.getElem?_eq_none (Nat.le_of_not_lt hk)]; exact limbBase_pos

/-- One schoolbook cell at row `i`, column `j`. -/
def mulCell (x i : Nat) (ys : List Nat) (st : List Nat × Nat) (j : Nat) : List Nat × Nat :=
  let cur := st.1.getD (i + j) 0 + x * ys.getD j 0 + st.2
  (st.1.set (i + j) (cur % limbBase), cur / limbBase)

def innerRun (x i : Nat) (ys out : List Nat) : Nat → List Nat × Nat
  | 0 => (out, 0)
  | j + 1 => mulCell x i ys (innerRun x i ys out j) j

def rowRun (xs ys : List Nat) : Nat → List Nat
  | 0 => List.replicate (xs.length + ys.length) 0
  | i + 1 =>
    let st := innerRun (xs.getD i 0) i ys (rowRun xs ys i) ys.length
    st.1.set (i + ys.length) st.2

theorem cell_fits (a x y c : Nat) (ha : a < limbBase) (hx : x < limbBase)
    (hy : y < limbBase) (hc : c < limbBase) :
    a + x * y + c < limbBase * limbBase := by
  have hxy : x * y ≤ (limbBase - 1) * (limbBase - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hB : 2 ≤ limbBase := by unfold limbBase; decide
  have e : (limbBase - 1) * (limbBase - 1) + 2 * (limbBase - 1) + 1 = limbBase * limbBase := by
    obtain ⟨b, hb⟩ : ∃ b, limbBase = b + 1 := ⟨limbBase - 1, by omega⟩
    rw [hb]; simp only [Nat.add_sub_cancel]
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
  omega

theorem cell_carry_lt (a x y c : Nat) (ha : a < limbBase) (hx : x < limbBase)
    (hy : y < limbBase) (hc : c < limbBase) :
    (a + x * y + c) / limbBase < limbBase :=
  Nat.div_lt_of_lt_mul (cell_fits a x y c ha hx hy hc)

theorem inner_inv (x i : Nat) (ys out0 : List Nat) (hx : x < limbBase)
    (hys : ∀ d ∈ ys, d < limbBase) (hout : ∀ d ∈ out0, d < limbBase)
    (hroom : i + ys.length ≤ out0.length) :
    ∀ j, j ≤ ys.length →
      (innerRun x i ys out0 j).1.length = out0.length ∧
      (∀ d ∈ (innerRun x i ys out0 j).1, d < limbBase) ∧
      (innerRun x i ys out0 j).2 < limbBase ∧
      limbVal (innerRun x i ys out0 j).1 + (innerRun x i ys out0 j).2 * limbBase ^ (i + j) =
        limbVal out0 + x * limbVal (ys.take j) * limbBase ^ i ∧
      (∀ k, i + j ≤ k → (innerRun x i ys out0 j).1.getD k 0 = out0.getD k 0) := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨rfl, hout, limbBase_pos, by simp [innerRun, limbVal], fun _ _ => rfl⟩
  | succ j ih =>
    intro hj
    obtain ⟨hlen, hdig, hc, hval, hsame⟩ := ih (by omega)
    show (mulCell x i ys (innerRun x i ys out0 j) j).1.length = out0.length ∧
      (∀ d ∈ (mulCell x i ys (innerRun x i ys out0 j) j).1, d < limbBase) ∧
      (mulCell x i ys (innerRun x i ys out0 j) j).2 < limbBase ∧
      limbVal (mulCell x i ys (innerRun x i ys out0 j) j).1 +
          (mulCell x i ys (innerRun x i ys out0 j) j).2 * limbBase ^ (i + (j + 1)) =
        limbVal out0 + x * limbVal (ys.take (j + 1)) * limbBase ^ i ∧
      (∀ k, i + (j + 1) ≤ k →
        (mulCell x i ys (innerRun x i ys out0 j) j).1.getD k 0 = out0.getD k 0)
    generalize innerRun x i ys out0 j = st at hlen hdig hc hval hsame
    have hjlt : j < ys.length := by omega
    have hy : ys.getD j 0 < limbBase := getD_lt_of_digits ys hys j
    have ha : st.1.getD (i + j) 0 < limbBase := getD_lt_of_digits st.1 hdig _
    have hidx : i + j < st.1.length := by omega
    have hcur := cell_fits _ _ _ _ ha hx hy hc
    simp only [mulCell]
    refine ⟨by rw [List.length_set, hlen], mem_set_digits _ _ _ hdig (Nat.mod_lt _ limbBase_pos),
      Nat.div_lt_of_lt_mul hcur, ?_, ?_⟩
    · -- value
      have hset := limbVal_set st.1 (i + j) ((st.1.getD (i + j) 0 + x * ys.getD j 0 + st.2) % limbBase) hidx
      have htake : ys.take (j + 1) = ys.take j ++ [ys.getD j 0] := by
        rw [take_succ_get ys j hjlt, getD_eq_getElem' ys j hjlt]
      have hlenT : (ys.take j).length = j := by simp [List.length_take]; omega
      rw [htake, limbVal_append, hlenT]
      simp only [limbVal, Nat.mul_zero, Nat.add_zero]
      generalize hcurv : st.1.getD (i + j) 0 + x * ys.getD j 0 + st.2 = cur at hset
      have hdm := Nat.mod_add_div cur limbBase
      -- atoms
      have hP : limbBase ^ (i + (j + 1)) = limbBase ^ (i + j) * limbBase := by
        rw [← Nat.add_assoc, Nat.pow_succ]
      have hQ : limbBase ^ (i + j) = limbBase ^ j * limbBase ^ i := by
        rw [Nat.pow_add, Nat.mul_comm]
      rw [hP]
      have e1 : cur / limbBase * (limbBase ^ (i + j) * limbBase) =
          (limbBase * (cur / limbBase)) * limbBase ^ (i + j) := by
        rw [Nat.mul_comm (limbBase ^ (i + j)) limbBase, Nat.mul_comm limbBase (cur / limbBase),
          Nat.mul_assoc]
      have e2 : x * (limbVal (ys.take j) + limbBase ^ j * ys.getD j 0) * limbBase ^ i =
          x * limbVal (ys.take j) * limbBase ^ i + (x * ys.getD j 0) * limbBase ^ (i + j) := by
        rw [hQ, Nat.mul_add, Nat.add_mul]
        congr 1
        ac_rfl
      rw [e1, e2]
      have hsum : cur % limbBase * limbBase ^ (i + j) +
          limbBase * (cur / limbBase) * limbBase ^ (i + j) =
          st.1.getD (i + j) 0 * limbBase ^ (i + j) + x * ys.getD j 0 * limbBase ^ (i + j) +
            st.2 * limbBase ^ (i + j) := by
        rw [← Nat.add_mul, hdm, ← hcurv, Nat.add_mul, Nat.add_mul]
      omega
    · intro k hk
      rw [getD_set_ne _ _ _ _ (by omega)]
      exact hsame k (by omega)

theorem row_inv (xs ys : List Nat) (hxs : ∀ d ∈ xs, d < limbBase)
    (hys : ∀ d ∈ ys, d < limbBase) :
    ∀ i, i ≤ xs.length →
      (rowRun xs ys i).length = xs.length + ys.length ∧
      (∀ d ∈ rowRun xs ys i, d < limbBase) ∧
      limbVal (rowRun xs ys i) = limbVal (xs.take i) * limbVal ys ∧
      (∀ k, i + ys.length ≤ k → (rowRun xs ys i).getD k 0 = 0) := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨by simp [rowRun], ?_, ?_, ?_⟩
    · intro d hd; simp [rowRun] at hd; rw [hd.2]; exact limbBase_pos
    · simp [rowRun, limbVal_replicate_zero, limbVal]
    · intro k _
      exact getD_replicate_zero _ k
  | succ i ih =>
    intro hi
    obtain ⟨hlen, hdig, hval, hzero⟩ := ih (by omega)
    have hilt : i < xs.length := by omega
    have hx : xs.getD i 0 < limbBase := getD_lt_of_digits xs hxs i
    have hroom : i + ys.length ≤ (rowRun xs ys i).length := by omega
    obtain ⟨hlen2, hdig2, hc2, hval2, hsame2⟩ :=
      inner_inv (xs.getD i 0) i ys (rowRun xs ys i) hx hys hdig hroom ys.length (Nat.le_refl _)
    show ((innerRun (xs.getD i 0) i ys (rowRun xs ys i) ys.length).1.set (i + ys.length)
        (innerRun (xs.getD i 0) i ys (rowRun xs ys i) ys.length).2).length =
          xs.length + ys.length ∧
      (∀ d ∈ (innerRun (xs.getD i 0) i ys (rowRun xs ys i) ys.length).1.set (i + ys.length)
        (innerRun (xs.getD i 0) i ys (rowRun xs ys i) ys.length).2, d < limbBase) ∧
      limbVal ((innerRun (xs.getD i 0) i ys (rowRun xs ys i) ys.length).1.set (i + ys.length)
        (innerRun (xs.getD i 0) i ys (rowRun xs ys i) ys.length).2) =
          limbVal (xs.take (i + 1)) * limbVal ys ∧
      (∀ k, i + 1 + ys.length ≤ k →
        ((innerRun (xs.getD i 0) i ys (rowRun xs ys i) ys.length).1.set (i + ys.length)
          (innerRun (xs.getD i 0) i ys (rowRun xs ys i) ys.length).2).getD k 0 = 0)
    generalize innerRun (xs.getD i 0) i ys (rowRun xs ys i) ys.length = st
      at hlen2 hdig2 hc2 hval2 hsame2
    have hidx : i + ys.length < st.1.length := by omega
    have hz : st.1.getD (i + ys.length) 0 = 0 := by
      rw [hsame2 _ (Nat.le_refl _)]; exact hzero _ (Nat.le_refl _)
    refine ⟨by rw [List.length_set, hlen2, hlen], mem_set_digits _ _ _ hdig2 hc2, ?_, ?_⟩
    · have hset := limbVal_set st.1 (i + ys.length) st.2 hidx
      rw [hz, Nat.zero_mul, Nat.add_zero] at hset
      rw [hset, hval2, hval, List.take_length, take_succ_get xs i hilt, limbVal_append,
        ← getD_eq_getElem' xs i hilt]
      have hlenT : (xs.take i).length = i := by simp [List.length_take]; omega
      rw [hlenT]
      simp only [limbVal, Nat.mul_zero, Nat.add_zero]
      rw [Nat.add_mul]
      congr 1
      ac_rfl
    · intro k hk
      rw [getD_set_ne _ _ _ _ (by omega), hsame2 k (by omega)]
      exact hzero k (by omega)

theorem rowRun_final (xs ys : List Nat) (hxs : ∀ d ∈ xs, d < limbBase)
    (hys : ∀ d ∈ ys, d < limbBase) :
    dropTrail (rowRun xs ys xs.length) = natLimbs (limbVal xs * limbVal ys) := by
  obtain ⟨_, hdig, hval, _⟩ := row_inv xs ys hxs hys xs.length (Nat.le_refl _)
  have hmem : ∀ d ∈ dropTrail (rowRun xs ys xs.length), d < limbBase :=
    fun d hd => hdig d (mem_dropTrail _ hd)
  have heq := trimmed_eq_natLimbs _ hmem (dropTrail_idem _)
  rw [limbVal_dropTrail, hval, List.take_length] at heq
  exact heq

end MegaDreifach.Link2
