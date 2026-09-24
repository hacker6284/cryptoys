/-
  M4 — Factoradic / Lehmer φ: injective on `n < 2^224` into 52-card deals.
  Mixed-radix digits + apply-to-remaining. Zero sorry. No native_decide.
-/
import MegaDreifach.Basic
import MegaDreifach.NatUtil

namespace MegaDreifach

/-- Pick remaining items by Lehmer digits (index into the leftover list). -/
def applyDigits : List Nat → List Nat → List Nat
  | [], _ => []
  | avail, [] => avail
  | avail, d :: ds =>
      if h : d < avail.length then
        avail[d] :: applyDigits (avail.eraseIdx d) ds
      else
        avail

/-- Lehmer unrank: `rank ↦` permutation of `0..n-1`. -/
def lehmerUnrank (n rank : Nat) : List Nat :=
  applyDigits (List.range n) (mixDecode (descending n) rank)

/-- Lehmer digits of `perm` relative to `avail`. -/
def lehmerDigits : List Nat → List Nat → List Nat
  | _, [] => []
  | avail, v :: rest =>
      avail.findIdx (· == v) :: lehmerDigits (avail.eraseIdx (avail.findIdx (· == v))) rest

/-- Factoradic / Lehmer rank of a list. -/
def lehmerRank (perm : List Nat) : Nat :=
  mixEncode (descending perm.length) (lehmerDigits (List.range perm.length) perm)

/-- φ on a 28-byte integer: unrank in `S_52`. -/
def phiUnrank (n : Nat) : List Nat := lehmerUnrank 52 n

theorem descending_pos (n : Nat) : ∀ r ∈ descending n, 0 < r :=
  fun _r hr => mem_descending hr

/-- Digits of `val < n!` are in range for radices `n,…,1`. -/
theorem lehmerDigits_unrank_bound (n rank : Nat) (h : rank < factorial n) :
    ∀ i, i < n →
      (mixDecode (descending n) rank)[i]?.getD 0 < (descending n)[i]?.getD 0 := by
  intro i hi
  have hlen : (mixDecode (descending n) rank).length = n := by
    simp [mixDecode_length, descending_length]
  have hi' : i < (mixDecode (descending n) rank).length := by simp [hlen]; exact hi
  have hval : rank < product (descending n) := by
    simpa [product_descending] using h
  exact mixDecode_bound (descending n) rank hval (descending_pos n) i hi'

/-- M4 core: mixed-radix decode then encode recovers `rank` when `rank < n!`. -/
theorem lehmerRank_unrank (n rank : Nat) (h : rank < factorial n) :
    mixEncode (descending n) (mixDecode (descending n) rank) = rank := by
  have hval : rank < product (descending n) := by
    simpa [product_descending] using h
  exact mixEncode_decode (descending n) rank hval (descending_pos n)

/-- Two ranks below `n!` with the same mixed-radix digits are equal. -/
theorem mixDecode_descending_inj (n r1 r2 : Nat)
    (h1 : r1 < factorial n) (h2 : r2 < factorial n)
    (heq : mixDecode (descending n) r1 = mixDecode (descending n) r2) : r1 = r2 := by
  have e1 := lehmerRank_unrank n r1 h1
  have e2 := lehmerRank_unrank n r2 h2
  rw [← e1, ← e2, heq]

/-- Distinct in-range indices pick distinct heads from a nodup list. -/
theorem nodup_get_inj (avail : List Nat) (hn : avail.Nodup) (d1 d2 : Nat)
    (hd1 : d1 < avail.length) (hd2 : d2 < avail.length)
    (heq : avail[d1] = avail[d2]) : d1 = d2 := by
  induction avail generalizing d1 d2 with
  | nil => cases hd1
  | cons a xs ih =>
      have ⟨hnotin, hntail⟩ := List.nodup_cons.mp hn
      match d1, d2 with
      | 0, 0 => rfl
      | 0, j + 1 =>
          have hj : j < xs.length := Nat.lt_of_succ_lt_succ hd2
          have : a = xs[j] := by simpa using heq
          have : a ∈ xs := this ▸ List.getElem_mem hj
          exact (hnotin this).elim
      | i + 1, 0 =>
          have hi : i < xs.length := Nat.lt_of_succ_lt_succ hd1
          have : xs[i] = a := by simpa using heq
          have : a ∈ xs := this ▸ List.getElem_mem hi
          exact (hnotin this).elim
      | i + 1, j + 1 =>
          have hi : i < xs.length := Nat.lt_of_succ_lt_succ hd1
          have hj : j < xs.length := Nat.lt_of_succ_lt_succ hd2
          have : xs[i] = xs[j] := by simpa using heq
          exact congrArg Nat.succ (ih hntail i j hi hj this)

/-- Apply-digits is injective on in-range digit lists of matching length. -/
theorem applyDigits_inj (avail d1 d2 : List Nat)
    (hn : avail.Nodup)
    (h1 : d1.length = avail.length) (h2 : d2.length = avail.length)
    (b1 : ∀ i, i < d1.length → d1[i]?.getD 0 < avail.length - i)
    (b2 : ∀ i, i < d2.length → d2[i]?.getD 0 < avail.length - i)
    (heq : applyDigits avail d1 = applyDigits avail d2) : d1 = d2 := by
  induction d1 generalizing avail d2 with
  | nil =>
      cases avail <;> cases d2 <;> simp_all [applyDigits]
  | cons x xs ih =>
      match avail, d2 with
      | [], _ => simp at h1
      | _ :: _, [] => simp at h2
      | a :: rest, y :: ys =>
          have hx : x < (a :: rest).length := by
            have := b1 0 (Nat.zero_lt_succ xs.length)
            simpa [List.getElem?_cons_zero] using this
          have hy : y < (a :: rest).length := by
            have := b2 0 (Nat.zero_lt_succ ys.length)
            simpa [List.getElem?_cons_zero] using this
          have heq' : (a :: rest)[x] :: applyDigits ((a :: rest).eraseIdx x) xs =
              (a :: rest)[y] :: applyDigits ((a :: rest).eraseIdx y) ys := by
            simpa only [applyDigits, dif_pos hx, dif_pos hy] using heq
          have hhead : (a :: rest)[x] = (a :: rest)[y] := by
            have := congrArg (fun l : List Nat => l.headD 0) heq'
            simpa using this
          have hxy : x = y := nodup_get_inj (a :: rest) hn x y hx hy hhead
          subst hxy
          have htail : applyDigits ((a :: rest).eraseIdx x) xs =
              applyDigits ((a :: rest).eraseIdx x) ys := by
            have := congrArg List.tail heq'
            simpa using this
          have hn' : ((a :: rest).eraseIdx x).Nodup :=
            hn.sublist (List.eraseIdx_sublist (a :: rest) x)
          have hxlt : x < (a :: rest).length := hx
          have hxs : xs.length = ((a :: rest).eraseIdx x).length := by
            rw [List.length_eraseIdx_of_lt hxlt]
            simp at h1; exact h1
          have hys : ys.length = ((a :: rest).eraseIdx x).length := by
            rw [List.length_eraseIdx_of_lt hxlt]
            simp at h2; exact h2
          have bxs : ∀ i, i < xs.length →
              xs[i]?.getD 0 < ((a :: rest).eraseIdx x).length - i := by
            intro i hi
            rw [List.length_eraseIdx_of_lt hxlt]
            have := b1 (i + 1) (Nat.succ_lt_succ hi)
            simpa [List.getElem?_cons_succ] using this
          have bys : ∀ i, i < ys.length →
              ys[i]?.getD 0 < ((a :: rest).eraseIdx x).length - i := by
            intro i hi
            rw [List.length_eraseIdx_of_lt hxlt]
            have := b2 (i + 1) (Nat.succ_lt_succ hi)
            simpa [List.getElem?_cons_succ] using this
          have := ih ((a :: rest).eraseIdx x) ys hn' hxs hys bxs bys htail
          simp [this]

/-- `range n` is nodup. -/
theorem range_nodup (n : Nat) : (List.range n).Nodup := List.nodup_range n

/-- Digit `i` of `descending n` is `n - i` (for `i < n`). -/
theorem descending_get (n i : Nat) (hi : i < n) :
    (descending n)[i]?.getD 0 = n - i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [descending, List.getElem?_cons_zero]
      | succ i =>
          have hi' : i < n := Nat.lt_of_succ_lt_succ hi
          have := ih i hi'
          simpa [descending, List.getElem?_cons_succ, Nat.succ_sub_succ] using this

/-- M4: `lehmerUnrank n` is injective on `[0, n!)`. -/
theorem lehmerUnrank_inj (n r1 r2 : Nat)
    (h1 : r1 < factorial n) (h2 : r2 < factorial n)
    (heq : lehmerUnrank n r1 = lehmerUnrank n r2) : r1 = r2 := by
  have hd :=
    applyDigits_inj (List.range n)
      (mixDecode (descending n) r1) (mixDecode (descending n) r2)
      (range_nodup n)
      (by simp [mixDecode_length, descending_length])
      (by simp [mixDecode_length, descending_length])
      ?b1 ?b2 heq
  · exact mixDecode_descending_inj n r1 r2 h1 h2 hd
  · intro i hi
    have hlen : (mixDecode (descending n) r1).length = n := by
      simp [mixDecode_length, descending_length]
    have hi' : i < n := by simp [hlen] at hi; exact hi
    have hb := lehmerDigits_unrank_bound n r1 h1 i hi'
    have hr : (descending n)[i]?.getD 0 = n - i := descending_get n i hi'
    simpa [List.length_range, hr] using hb
  · intro i hi
    have hlen : (mixDecode (descending n) r2).length = n := by
      simp [mixDecode_length, descending_length]
    have hi' : i < n := by simp [hlen] at hi; exact hi
    have hb := lehmerDigits_unrank_bound n r2 h2 i hi'
    have hr : (descending n)[i]?.getD 0 = n - i := descending_get n i hi'
    simpa [List.length_range, hr] using hb

/-- `2^224 < 52!`. Kernel `decide` on closed numerals (same policy as TwoDeck S5). -/
theorem two_pow_224_lt_fact_52 : phiMax < factorial 52 := by
  decide

/-- M4: φ is injective on its image domain `n < 2^224`. -/
theorem phiUnrank_inj (r1 r2 : Nat)
    (h1 : r1 < phiMax) (h2 : r2 < phiMax)
    (heq : phiUnrank r1 = phiUnrank r2) : r1 = r2 := by
  have h1' : r1 < factorial 52 := Nat.lt_trans h1 two_pow_224_lt_fact_52
  have h2' : r2 < factorial 52 := Nat.lt_trans h2 two_pow_224_lt_fact_52
  exact lehmerUnrank_inj 52 r1 r2 h1' h2' heq

/-- `getElem :: eraseIdx` is a permutation of the original list. -/
theorem perm_getElem_eraseIdx (l : List Nat) (i : Nat) (hi : i < l.length) :
    List.Perm (l[i] :: l.eraseIdx i) l := by
  rw [List.eraseIdx_eq_take_drop_succ]
  have hdrop : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi
  have hmid : List.Perm (l[i] :: (l.take i ++ l.drop (i + 1)))
                        (l.take i ++ l[i] :: l.drop (i + 1)) :=
    (List.perm_middle (l₁ := l.take i) (a := l[i]) (l₂ := l.drop (i + 1))).symm
  refine hmid.trans ?_
  rw [← hdrop, List.take_append_drop]

theorem applyDigits_perm (avail digits : List Nat)
    (hlen : digits.length = avail.length)
    (hbound : ∀ i, i < digits.length → digits[i]?.getD 0 < avail.length - i) :
    List.Perm (applyDigits avail digits) avail := by
  revert avail
  induction digits with
  | nil =>
      intro avail hlen hbound
      have : avail = [] := by cases avail <;> simp_all
      subst this; simp [applyDigits]
  | cons d ds ih =>
      intro avail hlen hbound
      match avail with
      | [] => simp at hlen
      | a :: rest =>
          have hd : d < (a :: rest).length := by
            have := hbound 0 (Nat.zero_lt_succ ds.length)
            simpa [List.getElem?_cons_zero] using this
          have hlen' : ds.length = ((a :: rest).eraseIdx d).length := by
            rw [List.length_eraseIdx_of_lt hd]
            simp at hlen; exact hlen
          have hbound' : ∀ i, i < ds.length →
              ds[i]?.getD 0 < ((a :: rest).eraseIdx d).length - i := by
            intro i hi
            rw [List.length_eraseIdx_of_lt hd]
            have := hbound (i + 1) (Nat.succ_lt_succ hi)
            simpa [List.getElem?_cons_succ] using this
          have ih' := ih ((a :: rest).eraseIdx d) hlen' hbound'
          have hcons :
              applyDigits (a :: rest) (d :: ds) =
                (a :: rest)[d] :: applyDigits ((a :: rest).eraseIdx d) ds := by
            simp only [applyDigits, dif_pos hd]
          rw [hcons]
          exact (ih'.cons _).trans (perm_getElem_eraseIdx (a :: rest) d hd)

theorem lehmerUnrank_perm (n rank : Nat) (h : rank < factorial n) :
    List.Perm (lehmerUnrank n rank) (List.range n) := by
  apply applyDigits_perm
  · simp [mixDecode_length, descending_length]
  · intro i hi
    have hlen : (mixDecode (descending n) rank).length = n := by
      simp [mixDecode_length, descending_length]
    have hi' : i < n := by simp [hlen] at hi; exact hi
    have hb := lehmerDigits_unrank_bound n rank h i hi'
    have hr : (descending n)[i]?.getD 0 = n - i := descending_get n i hi'
    simpa [List.length_range, hr] using hb

theorem phiUnrank_perm (n : Nat) (h : n < phiMax) :
    List.Perm (phiUnrank n) (List.range 52) :=
  lehmerUnrank_perm 52 n (Nat.lt_trans h two_pow_224_lt_fact_52)

end MegaDreifach
