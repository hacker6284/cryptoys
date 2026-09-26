/-
  LINK 2. `big_divmod_small` on a canonical limb list of any width.

  The divisor is one limb. Each step's `rem * 10^9 + digit` stays below
  `10^18`, so it fits in an i64. The countdown is the one-step bridge
  `divGenStep_at`, stacked by `chain_down`. The quotient trims to
  `natLimbs (value / d)`.

  Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.DivWide
import MegaDreifach.Link2.MulSmall

namespace MegaDreifach.Link2

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

theorem replicate_snoc (n a : Nat) :
    List.replicate (n + 1) a = List.replicate n a ++ [a] := by
  induction n with
  | zero => simp [List.replicate_succ]
  | succ n ih =>
    rw [List.replicate_succ, ih]
    have hcons : a :: List.replicate n a = List.replicate n a ++ [a] := by
      rw [← List.replicate_succ, ih]
    calc
      a :: (List.replicate n a ++ [a])
          = (a :: List.replicate n a) ++ [a] := by simp [List.cons_append]
      _ = (List.replicate n a ++ [a]) ++ [a] := by rw [hcons]

theorem set_append_left (xs ys : List Nat) (i v : Nat) (hi : i < xs.length) :
    (xs ++ ys).set i v = xs.set i v ++ ys := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [List.set_cons_zero]
    | succ i =>
      simp [List.set_cons_succ]
      exact ih i (by
        rw [List.length_cons] at hi
        omega)

theorem set_append_right (xs ys : List Nat) (i v : Nat)
    (hi : xs.length ≤ i) (h : i < xs.length + ys.length) :
    (xs ++ ys).set i v = xs ++ ys.set (i - xs.length) v := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => simp at hi
    | succ i =>
      simp [List.set_cons_succ]
      exact ih i (by
        rw [List.length_cons] at hi
        omega) (by
        rw [List.length_cons] at h
        omega)

/-- Low `i` limbs zero; limb `i` and above copied from `qs`. -/
def fillHigh (qs : List Nat) (i : Nat) : List Nat :=
  List.replicate i 0 ++ qs.drop i

theorem fillHigh_zero (qs : List Nat) : fillHigh qs 0 = qs := by
  simp [fillHigh]

theorem fillHigh_length (qs : List Nat) (i : Nat) (hi : i ≤ qs.length) :
    (fillHigh qs i).length = qs.length := by
  unfold fillHigh
  rw [List.length_append, List.length_replicate, List.length_drop]
  omega

theorem fillHigh_top (qs : List Nat) :
    fillHigh qs qs.length = List.replicate qs.length 0 := by
  unfold fillHigh
  simp

theorem drop_succ_cons_get (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    xs.drop i = xs[i] :: xs.drop (i + 1) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [List.drop_succ_cons]
      exact ih i (Nat.lt_of_succ_lt_succ (by simpa [List.length_cons] using hi))

theorem replicate_set_at (i v : Nat) :
    (List.replicate (i + 1) (0 : Nat)).set i v = List.replicate i 0 ++ [v] := by
  rw [replicate_snoc i 0]
  have hle : (List.replicate i (0 : Nat)).length ≤ i := by
    simp [List.length_replicate]
  have hlt : i < (List.replicate i (0 : Nat)).length + [0].length := by
    simp [List.length_replicate, List.length_singleton]
  rw [set_append_right (List.replicate i 0) [0] i v hle hlt]
  simp [List.length_replicate, Nat.sub_self, List.set_cons_zero]

theorem fillHigh_set_digit (qs : List Nat) (i digit : Nat) (_hi : i < qs.length)
    (hd : qs.drop i = digit :: qs.drop (i + 1)) :
    (fillHigh qs (i + 1)).set i digit = fillHigh qs i := by
  unfold fillHigh
  rw [set_append_left (List.replicate (i + 1) 0) (qs.drop (i + 1)) i digit
    (by simp [List.length_replicate])]
  rw [replicate_set_at i digit]
  rw [List.append_assoc, List.singleton_append, ← hd]

theorem divLE_cons_quot (d x : Nat) (xs : List Nat) :
    (divLE d (x :: xs) 0).1 =
      ((divLE d xs 0).2 * limbBase + x) / d :: (divLE d xs 0).1 := rfl

theorem divLE_cons_rem (d x : Nat) (xs : List Nat) :
    (divLE d (x :: xs) 0).2 = ((divLE d xs 0).2 * limbBase + x) % d := rfl

theorem divLE_nil (d rem : Nat) : divLE d [] rem = ([], rem) := rfl

theorem divLE_drop_quot (d : Nat) :
    ∀ (xs : List Nat) (i : Nat), i ≤ xs.length →
      (divLE d xs 0).1.drop i = (divLE d (xs.drop i) 0).1
  | _, 0, _ => by simp
  | [], _ + 1, hi => by simp at hi
  | x :: xs, i + 1, hi => by
      have hi' : i ≤ xs.length :=
        Nat.le_of_succ_le_succ (by simpa [List.length_cons] using hi)
      have ih := divLE_drop_quot d xs i hi'
      rw [divLE_cons_quot, List.drop_succ_cons, ih, List.drop_succ_cons]

theorem quot_drop_cons (d : Nat) (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    (divLE d xs 0).1.drop i =
      ((divLE d (xs.drop (i + 1)) 0).2 * limbBase + xs[i]) / d ::
        (divLE d xs 0).1.drop (i + 1) := by
  rw [divLE_drop_quot d xs i (Nat.le_of_lt hi), drop_succ_cons_get xs i hi, divLE_cons_quot,
    divLE_drop_quot d xs (i + 1) (Nat.succ_le_of_lt hi)]

theorem divLE_rem_at (d : Nat) (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    (divLE d (xs.drop i) 0).2 =
      ((divLE d (xs.drop (i + 1)) 0).2 * limbBase + xs[i]) % d := by
  rw [drop_succ_cons_get xs i hi, divLE_cons_rem]

theorem dropTrail_divLE (d : Nat) (hd : 0 < d) (xs : List Nat)
    (hxs : ∀ a ∈ xs, a < limbBase) :
    dropTrail (divLE d xs 0).1 = natLimbs (limbVal xs / d) := by
  have hdig := divLE_digits d hd 0 hd xs hxs
  have hq := (divLE_quot d hd xs).1
  have hmem : ∀ a ∈ dropTrail (divLE d xs 0).1, a < limbBase :=
    fun a ha => hdig a (mem_dropTrail _ ha)
  have heq := trimmed_eq_natLimbs (dropTrail (divLE d xs 0).1) hmem
    (dropTrail_idem _)
  rw [limbVal_dropTrail, hq] at heq
  exact heq

/-- A trimmed list's last limb is nonzero. -/
theorem trimmed_getLast_ne_zero (xs : List Nat) (htr : dropTrail xs = xs) (hne : xs ≠ []) :
    xs.getLast hne ≠ 0 := by
  induction xs with
  | nil => exact (hne rfl).elim
  | cons a as ih =>
    cases as with
    | nil =>
      simp [dropTrail] at htr
      simpa [List.getLast] using htr
    | cons b bs =>
      have htail := trimmed_tail a (b :: bs) htr
      exact ih htail (by simp)

theorem limbVal_high (xs : List Nat) (hne : xs ≠ []) (hz : xs.getLast hne ≠ 0) :
    limbBase ^ (xs.length - 1) ≤ limbVal xs := by
  induction xs with
  | nil => exact (hne rfl).elim
  | cons a as ih =>
    cases as with
    | nil =>
      simp [limbVal, List.getLast, Nat.pow_zero] at hz ⊢
      exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz)
    | cons b bs =>
      have hz' : (b :: bs).getLast (by simp) ≠ 0 := hz
      have ih' := ih (by simp) hz'
      have hlen : (b :: bs).length = (a :: b :: bs).length - 1 := by
        simp [List.length_cons]
      rw [← hlen]
      have hpos : 0 < (b :: bs).length := by simp
      have hsucc : (b :: bs).length - 1 + 1 = (b :: bs).length := by omega
      calc
        limbBase ^ (b :: bs).length
            = limbBase ^ ((b :: bs).length - 1 + 1) := by rw [hsucc]
        _ = limbBase ^ ((b :: bs).length - 1) * limbBase := by rw [Nat.pow_succ]
        _ = limbBase * limbBase ^ ((b :: bs).length - 1) := by rw [Nat.mul_comm]
        _ ≤ limbBase * limbVal (b :: bs) := Nat.mul_le_mul_left _ ih'
        _ ≤ a + limbBase * limbVal (b :: bs) := Nat.le_add_left _ _
        _ = limbVal (a :: b :: bs) := by simp [limbVal]

theorem pow_lt_pow_len (n m : Nat) (h : limbBase ^ n < limbBase ^ m) : n < m := by
  match Nat.lt_or_ge n m with
  | Or.inl hlt => exact hlt
  | Or.inr hge =>
    have hle : limbBase ^ m ≤ limbBase ^ n := Nat.pow_le_pow_right limbBase_pos hge
    omega

theorem natLimbs_length_le (n k : Nat) (hk : n < limbBase ^ k) :
    (natLimbs n).length ≤ k := by
  by_cases hn : n = 0
  · simp [hn, natLimbs_zero]
  · have htr := dropTrail_natLimbs n
    have hne : natLimbs n ≠ [] := by
      intro hempty
      have hv := limbVal_natLimbs n
      rw [hempty] at hv
      simp [limbVal] at hv
      exact hn hv.symm
    have hz := trimmed_getLast_ne_zero (natLimbs n) htr hne
    have hge := limbVal_high (natLimbs n) hne hz
    rw [limbVal_natLimbs] at hge
    have hlt : limbBase ^ ((natLimbs n).length - 1) < limbBase ^ k :=
      Nat.lt_of_le_of_lt hge hk
    have hpow := pow_lt_pow_len _ _ hlt
    omega

private theorem array_set_pr {α} (a : Array α) (i : Nat) (h1 h2 : i < a.size) (v : α) :
    a.set ⟨i, h1⟩ v = a.set ⟨i, h2⟩ v := rfl

/-- One countdown step writes quotient limb `i`. -/
private theorem divGen_fill (d : Nat) (xs : List Nat) (i : Nat)
    (hd0 : 0 < d) (hd : d < limbBase) (hi : i < xs.length)
    (hx : xs[i] < limbBase) (hfiti : FitsLen i) :
    divGenStep (Int.ofNat d) (embed xs)
        (Int.ofNat i,
          embed (fillHigh (divLE d xs 0).1 (i + 1)),
          Int.ofNat ((divLE d (xs.drop (i + 1)) 0).2)) =
      if i = 0 then
        .ok (SudoRt.Flow.brk
          (Int.ofNat i,
            embed (fillHigh (divLE d xs 0).1 i),
            Int.ofNat ((divLE d (xs.drop i) 0).2)))
      else
        .ok (SudoRt.Flow.cont
          (Int.ofNat (i - 1),
            embed (fillHigh (divLE d xs 0).1 i),
            Int.ofNat ((divLE d (xs.drop i) 0).2))) := by
  have hr : (divLE d (xs.drop (i + 1)) 0).2 < d :=
    divLE_rem_lt d hd0 0 hd0 (xs.drop (i + 1))
  have hqsLen : (divLE d xs 0).1.length = xs.length := divLE_length d 0 xs
  have hsz : i < (embed (fillHigh (divLE d xs 0).1 (i + 1))).size := by
    rw [size_embed, fillHigh_length _ _ (by rw [hqsLen]; omega), hqsLen]
    exact hi
  have hlenF : i < (fillHigh (divLE d xs 0).1 (i + 1)).length := by
    rw [fillHigh_length _ _ (by rw [hqsLen]; omega), hqsLen]
    exact hi
  rw [divGenStep_at d xs (embed (fillHigh (divLE d xs 0).1 (i + 1))) i
    ((divLE d (xs.drop (i + 1)) 0).2) hd0 hd hi hr hx hsz hfiti]
  dsimp only
  have hcons := quot_drop_cons d xs i hi
  have hset :=
    fillHigh_set_digit (divLE d xs 0).1 i
      (((divLE d (xs.drop (i + 1)) 0).2 * limbBase + xs[i]) / d)
      (by rw [hqsLen]; exact hi) hcons
  have harr :
      (embed (fillHigh (divLE d xs 0).1 (i + 1))).set ⟨i, hsz⟩
          (Int.ofNat ((((divLE d (xs.drop (i + 1)) 0).2 * limbBase + xs[i]) / d))) =
        embed (fillHigh (divLE d xs 0).1 i) := by
    have hembed := embed_set_nat (fillHigh (divLE d xs 0).1 (i + 1)) i
      (((divLE d (xs.drop (i + 1)) 0).2 * limbBase + xs[i]) / d) hlenF
    have hpr := array_set_pr (embed (fillHigh (divLE d xs 0).1 (i + 1))) i hsz
      (by rw [size_embed]; exact hlenF)
      (Int.ofNat (((divLE d (xs.drop (i + 1)) 0).2 * limbBase + xs[i]) / d))
    rw [hpr, hembed, hset]
  have hrem := divLE_rem_at d xs i hi
  rw [harr, ← hrem]
  by_cases hi0 : i = 0
  · simp [hi0]
  · simp [hi0]

/-- `big_divmod_small` of any digit string by a positive one-limb divisor. -/
theorem big_divmod_small_refines (d : Nat) (xs : List Nat)
    (hd0 : 0 < d) (hd : d < limbBase)
    (hxs : ∀ a ∈ xs, a < limbBase) (hfits : FitsLen xs.length) :
    Megadreifach.big_divmod_small (bigOf xs) (Int.ofNat d) =
      .ok (bigOf (natLimbs (limbVal xs / d)), Int.ofNat (limbVal xs % d)) := by
  by_cases hnil : xs = []
  · subst hnil
    simpa [limbVal, Nat.zero_div, Nat.zero_mod, natLimbs_zero] using
      big_divmod_empty d hd0 hd
  · have hpos : 0 < xs.length :=
      Nat.pos_of_ne_zero (fun h => hnil (List.eq_nil_of_length_eq_zero h))
    let qs := (divLE d xs 0).1
    have hqsLen : qs.length = xs.length := divLE_length d 0 xs
    unfold Megadreifach.big_divmod_small
    dsimp [bigOf]
    have hgt : decide ((d : Int) > (0 : Int)) = true := by
      rw [decide_eq_true_eq]
      exact (ofNat_pos_iff d).mpr hd0
    have hlt : decide ((d : Int) < Megadreifach.limb_base) = true := by
      rw [limb_base_eq, decide_eq_true_eq]
      exact (ofNat_lt_iff d limbBase).mpr hd
    rw [hgt]
    simp only [ite_true, hlt]
    rw [show (pure true : Except SudoRt.Trap Bool) = .ok true from rfl, ok_bind,
      sudoAssert_true, ok_bind, listLen_embed, sEq_ofNat_zero,
      decide_eq_false_iff_not.mpr (fun h => hnil (List.eq_nil_of_length_eq_zero h))]
    rw [if_neg (by decide : ¬ ((false : Bool) = true))]
    rw [filledL_ofNat, ok_bind, embed_replicate_zero,
      subI_ofNat_one xs.length hpos hfits, ok_bind]
    dsimp
    rw [fuelDown_eq, show (0 : Int) = Int.ofNat 0 from rfl, except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise
        (step' := divGenStep (Int.ofNat d) (embed xs))
      intro σ
      unfold divGenStep
      rfl
    have htop : fillHigh qs xs.length = List.replicate xs.length 0 := by
      rw [← hqsLen]
      exact fillHigh_top qs
    have hstart :
        ((Int.ofNat (xs.length - 1), embed (List.replicate xs.length 0), Int.ofNat 0) :
            Int × Array Int × Int) =
          (Int.ofNat (xs.length - 1),
            embed (fillHigh qs xs.length),
            Int.ofNat ((divLE d (xs.drop xs.length) 0).2)) := by
      simp [htop, divLE_nil, List.drop_eq_nil_of_le (Nat.le_refl _)]
    have hcast : (↑(xs.length - 1) : Int) = Int.ofNat (xs.length - 1) := rfl
    have hsucc : (xs.length - 1) + 1 = xs.length := by omega
    have hfill : fillHigh qs xs.length = fillHigh qs ((xs.length - 1) + 1) := by
      rw [hsucc]
    have hdropEq : xs.drop xs.length = xs.drop ((xs.length - 1) + 1) := by
      rw [hsucc]
    have hmodI : ((limbVal xs : Int) % (d : Int)) = Int.ofNat (limbVal xs % d) := by
      rw [← Int.ofNat_emod]
      rfl
    rw [hcast, hstart, hfill, hdropEq, hmodI, show Int.ofNat 0 = (0 : Int) from rfl]
    apply chain_down
      (f := fun i =>
        (embed (fillHigh qs (i + 1)),
          Int.ofNat ((divLE d (xs.drop (i + 1)) 0).2)))
      (g := fun i =>
        (embed (fillHigh qs i),
          Int.ofNat ((divLE d (xs.drop i) 0).2)))
      (fromN := xs.length - 1)
      (goal := .ok (bigOf (natLimbs (limbVal xs / d)), Int.ofNat (limbVal xs % d)))
    · intro i hiLe
      have hi : i < xs.length := by omega
      have hx : xs[i] < limbBase := hxs _ (List.getElem_mem hi)
      have hfiti : FitsLen i := FitsLen.of_le hfits (Nat.le_of_lt hi)
      simpa using divGen_fill d xs i hd0 hd hi hx hfiti
    · intro i hp _
      dsimp
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hp)]
    · dsimp
      rw [fillHigh_zero]
      have hfitq : FitsLen qs.length := by rw [hqsLen]; exact hfits
      rw [make_big_false qs hfitq, ok_bind]
      have hrem := (divLE_quot d hd0 xs).2
      have hdrop := dropTrail_divLE d hd0 xs hxs
      rw [hrem, hdrop]
      rfl

/-- Same statement on the canonical limbs of a natural number. -/
theorem big_divmod_nat (d n : Nat) (hd0 : 0 < d) (hd : d < limbBase)
    (hfits : FitsLen (natLimbs n).length) :
    Megadreifach.big_divmod_small (bigOf (natLimbs n)) (Int.ofNat d) =
      .ok (bigOf (natLimbs (n / d)), Int.ofNat (n % d)) := by
  simpa [limbVal_natLimbs] using
    big_divmod_small_refines d (natLimbs n) hd0 hd (natLimbs_digits n) hfits

end MegaDreifach.Link2
