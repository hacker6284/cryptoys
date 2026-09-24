/-
  M3 — Digest rank packing (not a full bijection theorem yet).
  Layout matches SPEC §6:
    even cp (20!/2) | co[0..18] (3^19) | even ep (30!/2) | eo[0..28] (2^29).
  Proved at the packing layer. Open glue: evenRank injectivity on even S_n
  (Lehmer prefix + even completion). Zero sorry. No native_decide.
-/
import MegaDreifach.Position
import MegaDreifach.Factoradic
import MegaDreifach.Pad

namespace MegaDreifach

/-! ## Even completion of a prefix -/

def nGt (xs : List Nat) (a : Nat) : Nat :=
  (xs.filter (fun y => decide (y > a))).length

theorem nGt_cons (x : Nat) (xs : List Nat) (a : Nat) :
    nGt (x :: xs) a = (if x > a then 1 else 0) + nGt xs a := by
  simp [nGt, List.filter]
  by_cases h : x > a
  · simp [h]; rw [Nat.add_comm]
  · simp [h]

theorem nGt_append (xs ys : List Nat) (a : Nat) :
    nGt (xs ++ ys) a = nGt xs a + nGt ys a := by
  simp [nGt, List.filter_append]

theorem nGt_pair (a b x : Nat) :
    nGt [a, b] x = (if a > x then 1 else 0) + (if b > x then 1 else 0) := by
  simp [nGt, List.filter]
  by_cases ha : a > x
  · by_cases hb : b > x
    · simp [ha, hb]
    · simp [ha, hb]
  · by_cases hb : b > x
    · simp [ha, hb]
    · simp [ha, hb]

/-- Count of later elements *smaller* than `a` (the inversion contribution). -/
def nLt (xs : List Nat) (a : Nat) : Nat :=
  (xs.filter (fun y => decide (a > y))).length

theorem nLt_append (xs ys : List Nat) (a : Nat) :
    nLt (xs ++ ys) a = nLt xs a + nLt ys a := by
  simp [nLt, List.filter_append]

theorem nLt_pair (a b x : Nat) :
    nLt [a, b] x = (if x > a then 1 else 0) + (if x > b then 1 else 0) := by
  simp [nLt, List.filter]
  by_cases ha : x > a
  · by_cases hb : x > b
    · simp [ha, hb]
    · simp [ha, hb]
  · by_cases hb : x > b
    · simp [ha, hb]
    · simp [ha, hb]

theorem inversions_append_two (xs : List Nat) (a b : Nat) :
    inversions (xs ++ [a, b]) =
      inversions xs + nGt xs a + nGt xs b + (if a > b then 1 else 0) := by
  induction xs with
  | nil =>
      simp [inversions, nGt]
      by_cases h : a > b
      · simp [h, inversions]
      · simp [h, inversions]
  | cons x xs ih =>
      rw [List.cons_append, inversions, ih]
      have hn : nLt (xs ++ [a, b]) x =
          nLt xs x + (if x > a then 1 else 0) + (if x > b then 1 else 0) := by
        rw [nLt_append, nLt_pair]
        omega
      have hxa : nGt (x :: xs) a = (if x > a then 1 else 0) + nGt xs a :=
        nGt_cons x xs a
      have hxb : nGt (x :: xs) b = (if x > b then 1 else 0) + nGt xs b :=
        nGt_cons x xs b
      have hinv : (List.filter (fun y => decide (x > y)) (xs ++ [a, b])).length =
          nLt (xs ++ [a, b]) x := rfl
      have hixs : inversions (x :: xs) = nLt xs x + inversions xs := rfl
      rw [hinv, hn, hixs, hxa, hxb]
      omega

/-- The two orderings of a distinct last pair differ by exactly one inversion. -/
theorem inversions_swap_last (xs : List Nat) (a b : Nat) (hne : a ≠ b) :
    inversions (xs ++ [a, b]) + 1 = inversions (xs ++ [b, a]) ∨
    inversions (xs ++ [b, a]) + 1 = inversions (xs ++ [a, b]) := by
  have ha := inversions_append_two xs a b
  have hb := inversions_append_two xs b a
  cases Nat.lt_or_gt_of_ne hne with
  | inl hab =>
      -- a < b, so ¬ (a > b) and (b > a)
      have h1 : (if a > b then 1 else 0) = 0 := by
        have : ¬ a > b := Nat.not_lt.mpr (Nat.le_of_lt hab)
        simp [this]
      have h2 : (if b > a then 1 else 0) = 1 := by
        simp [hab]
      omega
  | inr hba =>
      -- a > b
      have h1 : (if a > b then 1 else 0) = 1 := by
        simp [hba]
      have h2 : (if b > a then 1 else 0) = 0 := by
        have : ¬ b > a := Nat.not_lt.mpr (Nat.le_of_lt hba)
        simp [this]
      omega

theorem permParity_swap_last (xs : List Nat) (a b : Nat) (hne : a ≠ b) :
    permParity (xs ++ [a, b]) ≠ permParity (xs ++ [b, a]) := by
  have h := inversions_swap_last xs a b hne
  simp only [permParity]
  cases h with
  | inl h =>
      have : (inversions (xs ++ [a, b]) + 1) % 2 =
          inversions (xs ++ [b, a]) % 2 := by rw [h]
      rw [Nat.add_mod] at this
      omega
  | inr h =>
      have : (inversions (xs ++ [b, a]) + 1) % 2 =
          inversions (xs ++ [a, b]) % 2 := by rw [h]
      rw [Nat.add_mod] at this
      omega

/-- Force the last two leftover items into the unique even order. -/
def evenComplete (pref leftover : List Nat) : List Nat :=
  match leftover with
  | [a, b] =>
      if permParity (pref ++ [a, b]) = 0 then pref ++ [a, b]
      else pref ++ [b, a]
  | _ => pref ++ leftover

/-- M3 fragment: the even completion of a distinct pair is even. -/
theorem evenComplete_even (pref : List Nat) (a b : Nat) (hne : a ≠ b) :
    permParity (evenComplete pref [a, b]) = 0 := by
  simp [evenComplete]
  split
  · next h => exact h
  · next h =>
      have hne' := permParity_swap_last pref a b hne
      have hb : permParity (pref ++ [b, a]) < 2 := Nat.mod_lt _ (by decide)
      have ha : permParity (pref ++ [a, b]) < 2 := Nat.mod_lt _ (by decide)
      omega

/-- Two even completions of the same prefix and the same two leftover values
    coincide: the last two positions are uniquely determined by even parity. -/
theorem evenComplete_unique (pref : List Nat) (a b : Nat) (hne : a ≠ b)
    (p : List Nat) (hp : p = pref ++ [a, b] ∨ p = pref ++ [b, a])
    (heven : permParity p = 0) :
    p = evenComplete pref [a, b] := by
  simp [evenComplete]
  cases hp with
  | inl h =>
      split
      · next h0 => exact h
      · next hodd =>
          rw [h] at heven
          exact (hodd heven).elim
  | inr h =>
      split
      · next h0 =>
          have : permParity (pref ++ [a, b]) ≠ permParity (pref ++ [b, a]) :=
            permParity_swap_last pref a b hne
          rw [h] at heven
          exact (this (by rw [h0, heven])).elim
      · next _ => exact h

/-! ## Orientation packing -/

def packOri3 (co : List Nat) : Nat :=
  mixEncode (List.replicate 19 3) (co.take 19)

def unpackOri3 (val : Nat) : List Nat :=
  let front := mixDecode (List.replicate 19 3) val
  front ++ [(3 - sumNats front % 3) % 3]

def packOri2 (eo : List Nat) : Nat :=
  mixEncode (List.replicate 29 2) (eo.take 29)

def unpackOri2 (val : Nat) : List Nat :=
  let front := mixDecode (List.replicate 29 2) val
  front ++ [sumNats front % 2]

theorem replicate_3_pos (k : Nat) : ∀ r ∈ List.replicate k 3, 0 < r := by
  intro r hr
  have := List.eq_of_mem_replicate hr
  subst this; decide

theorem replicate_2_pos (k : Nat) : ∀ r ∈ List.replicate k 2, 0 < r := by
  intro r hr
  have := List.eq_of_mem_replicate hr
  subst this; decide

theorem packOri3_unpack (val : Nat) (h : val < 3 ^ 19) :
    packOri3 (unpackOri3 val) = val := by
  have hval : val < product (List.replicate 19 3) := by
    simpa [product_replicate] using h
  have hdec := mixEncode_decode (List.replicate 19 3) val hval (replicate_3_pos 19)
  have hlen : (mixDecode (List.replicate 19 3) val).length = 19 := by
    simp [mixDecode_length, List.length_replicate]
  unfold packOri3 unpackOri3
  rw [List.take_left' hlen]
  exact hdec

theorem packOri2_unpack (val : Nat) (h : val < 2 ^ 29) :
    packOri2 (unpackOri2 val) = val := by
  have hval : val < product (List.replicate 29 2) := by
    simpa [product_replicate] using h
  have hdec := mixEncode_decode (List.replicate 29 2) val hval (replicate_2_pos 29)
  have hlen : (mixDecode (List.replicate 29 2) val).length = 29 := by
    simp [mixDecode_length, List.length_replicate]
  unfold packOri2 unpackOri2
  rw [List.take_left' hlen]
  exact hdec

theorem unpackOri3_sum (val : Nat) : sumNats (unpackOri3 val) % 3 = 0 := by
  simp [unpackOri3, sumNats_append, sumNats]
  omega

theorem unpackOri2_sum (val : Nat) : sumNats (unpackOri2 val) % 2 = 0 := by
  simp [unpackOri2, sumNats_append, sumNats]
  omega

/-- Last ternary digit is determined by `sum ≡ 0 (mod 3)`. -/
theorem last_ori3_unique (front : List Nat) (a b : Nat)
    (ha : a < 3) (hb : b < 3)
    (sa : (sumNats front + a) % 3 = 0) (sb : (sumNats front + b) % 3 = 0) :
    a = b := by
  have : a % 3 = b % 3 := by
    have ha' : a % 3 = a := Nat.mod_eq_of_lt ha
    have hb' : b % 3 = b := Nat.mod_eq_of_lt hb
    omega
  omega

/-- M3: `packOri3` is injective on length-20, digits `< 3`, sum ≡ 0 (mod 3). -/
theorem packOri3_inj (co1 co2 : List Nat)
    (h1 : co1.length = 20) (h2 : co2.length = 20)
    (b1 : ∀ o ∈ co1, o < 3) (b2 : ∀ o ∈ co2, o < 3)
    (_s1 : sumNats co1 % 3 = 0) (_s2 : sumNats co2 % 3 = 0)
    (heq : packOri3 co1 = packOri3 co2) : co1.take 19 = co2.take 19 := by
  have hlen1 : (co1.take 19).length = 19 := by simp [List.length_take]; omega
  have hlen2 : (co2.take 19).length = 19 := by simp [List.length_take]; omega
  have bound (co : List Nat) (hco : co.length = 20) (hb : ∀ o ∈ co, o < 3) :
      ∀ i, i < (co.take 19).length →
        (co.take 19)[i]?.getD 0 < (List.replicate 19 3)[i]?.getD 0 := by
    intro i hi
    have hi19 : i < 19 := by simp [List.length_take, hco] at hi; omega
    have hico : i < co.length := by omega
    have hget : (co.take 19)[i]?.getD 0 = co[i] := by
      simp [List.getElem?_take, hi19, List.getElem?_eq_getElem hico]
    have hmem : co[i] ∈ co := List.getElem_mem hico
    have hr : (List.replicate 19 3)[i]?.getD 0 = 3 := by
      have hi' : i < (List.replicate 19 3).length := by
        simp [List.length_replicate]; exact hi19
      rw [List.getElem?_eq_getElem hi', Option.getD]
      exact List.getElem_replicate (n := 19) (a := 3) hi'
    rw [hget, hr]
    exact hb _ hmem
  exact mixEncode_inj (List.replicate 19 3) (co1.take 19) (co2.take 19)
    (by simp [hlen1]) (by simp [hlen2])
    (bound co1 h1 b1) (bound co2 h2 b2) heq

/-- M3: `packOri2` is injective on the first 29 edge-ori bits. -/
theorem packOri2_inj (eo1 eo2 : List Nat)
    (h1 : eo1.length = 30) (h2 : eo2.length = 30)
    (b1 : ∀ o ∈ eo1, o < 2) (b2 : ∀ o ∈ eo2, o < 2)
    (heq : packOri2 eo1 = packOri2 eo2) : eo1.take 29 = eo2.take 29 := by
  have hlen1 : (eo1.take 29).length = 29 := by simp [List.length_take]; omega
  have hlen2 : (eo2.take 29).length = 29 := by simp [List.length_take]; omega
  have bound (eo : List Nat) (heo : eo.length = 30) (hb : ∀ o ∈ eo, o < 2) :
      ∀ i, i < (eo.take 29).length →
        (eo.take 29)[i]?.getD 0 < (List.replicate 29 2)[i]?.getD 0 := by
    intro i hi
    have hi29 : i < 29 := by simp [List.length_take, heo] at hi; omega
    have hieo : i < eo.length := by omega
    have hget : (eo.take 29)[i]?.getD 0 = eo[i] := by
      simp [List.getElem?_take, hi29, List.getElem?_eq_getElem hieo]
    have hmem : eo[i] ∈ eo := List.getElem_mem hieo
    have hr : (List.replicate 29 2)[i]?.getD 0 = 2 := by
      have hi' : i < (List.replicate 29 2).length := by
        simp [List.length_replicate]; exact hi29
      rw [List.getElem?_eq_getElem hi', Option.getD]
      exact List.getElem_replicate (n := 29) (a := 2) hi'
    rw [hget, hr]
    exact hb _ hmem
  exact mixEncode_inj (List.replicate 29 2) (eo1.take 29) (eo2.take 29)
    (by simp [hlen1]) (by simp [hlen2])
    (bound eo1 h1 b1) (bound eo2 h2 b2) heq

/-! ## Full rank packing of the four components -/

def evenRank (perm : List Nat) : Nat :=
  mixEncode (evenRadices perm.length)
    ((lehmerDigits (List.range perm.length) perm).take (perm.length - 2))

def rankRadices : List Nat :=
  [evenPermCount 20, 3 ^ 19, evenPermCount 30, 2 ^ 29]

def rankLists (cp co ep eo : List Nat) : Nat :=
  mixEncode rankRadices [evenRank cp, packOri3 co, evenRank ep, packOri2 eo]

def rankPosition (p : Position) : Nat :=
  rankLists (listOf p.cp) (listOfOri p.co) (listOf p.ep) (listOfOri p.eo)

/-- 29-byte big-endian digest encoding. -/
def positionToBytes (p : Position) : List Nat :=
  toBE digestLen (rankPosition p)

/-- `|G| < 256^29`, so the 29-byte encoding is injective on ranks in range. -/
theorem groupOrder_lt_digest : groupOrder < 256 ^ digestLen := by
  decide

/-- M3 (bytes): equal 29-byte encodings of in-range ranks imply equal ranks. -/
theorem positionToBytes_rank_inj (p q : Position)
    (hp : rankPosition p < groupOrder) (hq : rankPosition q < groupOrder)
    (heq : positionToBytes p = positionToBytes q) :
    rankPosition p = rankPosition q := by
  have h1 : rankPosition p < 256 ^ digestLen := Nat.lt_trans hp groupOrder_lt_digest
  have h2 : rankPosition q < 256 ^ digestLen := Nat.lt_trans hq groupOrder_lt_digest
  exact toBE_inj digestLen _ _ h1 h2 heq

/-- Four-component mixed-radix encode is injective on in-range digit lists. -/
theorem rankLists_mix_inj (d1 d2 : List Nat)
    (h1 : d1.length = 4) (h2 : d2.length = 4)
    (b1 : ∀ i, i < 4 → d1[i]?.getD 0 < rankRadices[i]?.getD 0)
    (b2 : ∀ i, i < 4 → d2[i]?.getD 0 < rankRadices[i]?.getD 0)
    (heq : mixEncode rankRadices d1 = mixEncode rankRadices d2) : d1 = d2 := by
  have hr : rankRadices.length = 4 := by simp [rankRadices]
  exact mixEncode_inj rankRadices d1 d2 (by omega) (by omega)
    (by intro i hi; exact b1 i (by omega))
    (by intro i hi; exact b2 i (by omega))
    heq

/-- M3: if two legal-shaped list tuples pack to the same rank and each
    component is in range, the four packed integers agree. Combined with
    `packOri3_inj` / `evenComplete_unique` this is the digest bijection. -/
theorem rankLists_components_eq (cp1 co1 ep1 eo1 cp2 co2 ep2 eo2 : List Nat)
    (b0 : evenRank cp1 < evenPermCount 20) (b0' : evenRank cp2 < evenPermCount 20)
    (b1 : packOri3 co1 < 3 ^ 19) (b1' : packOri3 co2 < 3 ^ 19)
    (b2 : evenRank ep1 < evenPermCount 30) (b2' : evenRank ep2 < evenPermCount 30)
    (b3 : packOri2 eo1 < 2 ^ 29) (b3' : packOri2 eo2 < 2 ^ 29)
    (heq : rankLists cp1 co1 ep1 eo1 = rankLists cp2 co2 ep2 eo2) :
    evenRank cp1 = evenRank cp2 ∧ packOri3 co1 = packOri3 co2 ∧
    evenRank ep1 = evenRank ep2 ∧ packOri2 eo1 = packOri2 eo2 := by
  let d1 := [evenRank cp1, packOri3 co1, evenRank ep1, packOri2 eo1]
  let d2 := [evenRank cp2, packOri3 co2, evenRank ep2, packOri2 eo2]
  have hd : d1 = d2 := by
    refine rankLists_mix_inj d1 d2 (by simp [d1]) (by simp [d2]) ?_ ?_ heq
    · intro i hi
      match i with
      | 0 => simpa [d1, rankRadices] using b0
      | 1 => simpa [d1, rankRadices] using b1
      | 2 => simpa [d1, rankRadices] using b2
      | 3 => simpa [d1, rankRadices] using b3
      | k + 4 => omega
    · intro i hi
      match i with
      | 0 => simpa [d2, rankRadices] using b0'
      | 1 => simpa [d2, rankRadices] using b1'
      | 2 => simpa [d2, rankRadices] using b2'
      | 3 => simpa [d2, rankRadices] using b3'
      | k + 4 => omega
  simp [d1, d2] at hd
  exact hd

end MegaDreifach
