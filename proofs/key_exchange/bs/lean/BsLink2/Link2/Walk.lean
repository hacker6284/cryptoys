/-
  BS Link 2: B7 the walk (`cube`, `start_accumulator`, `walk`) and the public value and
  shared secret it computes, against the model `Spec.publicValue` / `Spec.sharedSecret`.
  The lemmas here take the key reader's output as a hypothesis
  (`Bs.read_key key = .ok (embed cells)`); `Exchange.lean` discharges it with
  `read_key_spec` (`Key.lean`) for the headline `public_value_refines` and
  `shared_secret_refines`. Proof-only.
-/
import BsLink2.Link2.Send

namespace BsLink2.Link2

open MegaDreifach.Link2

theorem emod_sub_mul (a K P : Int) : (a - K * P) % P = a % P := by
  rw [Int.sub_eq_add_neg, ← Int.neg_mul, Int.add_mul_emod_self]

theorem emod_mul_cong {P a a' b b' : Int} (h1 : a % P = a' % P) (h2 : b % P = b' % P) :
    (a * b) % P = (a' * b') % P := by
  rw [Int.mul_emod, h1, h2, ← Int.mul_emod]

/-- A register of `n` trits as the multiply/tidy lemmas need it. -/
structure Reg (n : Nat) (x : Array Int) : Prop where
  size : x.size = n
  trits : Trits x

theorem cube_spec (f : Bs.Field) (n : Nat) (toll : Array Int)
    (hn : f.sudo_5Field_1n = Int.ofNat n) (ht : f.sudo_5Field_4toll = toll)
    (htt : Trits toll) (hts : 0 < toll.size) (htn : toll.size < n)
    (hfit : FitsLen (2 * n + 2)) (x y : Array Int) (hx : Reg n x) (hy : Reg n y)
    (nudge : Nat) (hnu : nudge ≤ 2) :
    ∃ x' y', Bs.cube f x (Int.ofNat nudge) y = .ok (x', y') ∧ Reg n x' ∧ Reg n y' ∧
      val x' % (pw n - val toll) = (val x * val x * val x * pw nudge) % (pw n - val toll) := by
  obtain ⟨y1, hm1, hs1, ht1, _, K1, hK1⟩ := multiply_spec f n toll hn ht htt hts htn x x
    hx.trits hx.trits hx.size hx.size 0 (by decide) (FitsLen.of_le hfit (by omega))
  obtain ⟨x1, hm2, hs2, ht2, _, K2, hK2⟩ := multiply_spec f n toll hn ht htt hts htn y1 x
    ht1 hx.trits hs1 hx.size nudge hnu (FitsLen.of_le hfit (by omega))
  have hn0 : 0 < n := by omega
  have hfn : FitsLen n := FitsLen.of_le hfit (by omega)
  refine ⟨x1, y1, ?_, ⟨hs2, ht2⟩, ⟨hs1, ht1⟩, ?_⟩
  · unfold Bs.cube
    rw [show (0 : Int) = Int.ofNat 0 from rfl, hm1, ok_bind,
      slide_spec y y1 (by rw [hy.size, hs1]) (by rw [hy.size]; exact hn0) (by rw [hy.size]; exact hfn),
      ok_bind]
    dsimp only
    rw [hm2, ok_bind,
      slide_spec x x1 (by rw [hx.size, hs2]) (by rw [hx.size]; exact hn0) (by rw [hx.size]; exact hfn),
      ok_bind]
    rfl
  · rw [hK2, emod_sub_mul]
    have : (val y1 * val x * pw nudge) % (pw n - val toll) =
        (val x * val x * pw 0 * val x * pw nudge) % (pw n - val toll) := by
      apply emod_mul_cong _ rfl
      apply emod_mul_cong _ rfl
      rw [hK1, emod_sub_mul]
    rw [this, pw_zero, Int.mul_one]

theorem empty_register_spec (f : Bs.Field) (n : Nat) (hn : f.sudo_5Field_1n = Int.ofNat n) :
    Bs.empty_register f = .ok (Array.mkArray n 0) := by
  unfold Bs.empty_register; rw [hn, filledL_ofNat]; rfl

theorem expOf_take_succ (cs : List Nat) (j : Nat) (h : j < cs.length) :
    Spec.expOf (cs.take (j + 1)) = 3 * Spec.expOf (cs.take j) + cs[j] := by
  unfold Spec.expOf
  rw [List.take_succ, List.getElem?_eq_getElem h, Option.toList_some, List.foldl_append]
  rfl

theorem pw_cube (E c : Nat) : pw (3 * E + c) = pw E * pw E * pw E * pw c := by
  rw [pw_add, show 3 * E = E + E + E by omega, pw_add, pw_add]

theorem tidy_eq_in_place (f : Bs.Field) (x : Array Int) : Bs.tidy f x = Bs.tidy_in_place f x := by
  unfold Bs.tidy; exact except_bind_pure _

theorem walk_public_spec (f : Bs.Field) (n : Nat) (toll : Array Int)
    (hn : f.sudo_5Field_1n = Int.ofNat n) (ht : f.sudo_5Field_4toll = toll)
    (htt : Trits toll) (hts : 0 < toll.size) (htn : toll.size < n) (h3 : 3 ≤ n)
    (hfit : FitsLen (2 * n + 2)) (cs : List Nat) (hcs : ∀ c ∈ cs, c ≤ 2)
    (hfc : FitsLen cs.length) (hstart : 0 < Spec.expOf cs)
    (y : Array Int) (hy : Reg n y) :
    ∃ r, Bs.walk f (embed cs) Bs.Phase.Sudo_5Phase_6Public y = .ok r ∧
      Reg n r.1 ∧ Reg n r.2 ∧ val r.1 = pw (Spec.expOf cs) % (pw n - val toll) := by
  have hcl : 0 < cs.length := by
    rcases cs with _ | ⟨c, cs⟩
    · simp [Spec.expOf] at hstart
    · simp
  have hfn : FitsLen n := FitsLen.of_le hfit (by omega)
  have hn0 : 0 < n := by omega
  unfold Bs.walk
  simp only [empty_register_spec f n hn, ok_bind, listLen_eq, size_embed]
  rw [subI_ofNat_one _ hcl hfc]
  simp only [ok_bind]
  rw [except_bind_pure, fuelRange_eq]
  refine asc_exists (fromN := 0) (toN := cs.length - 1) (s0 := (Array.mkArray n 0, y, false))
    (fun j (st : Array Int × Array Int × Bool) => Reg n st.1 ∧ Reg n st.2.1 ∧
      st.2.2 = decide (0 < Spec.expOf (cs.take j)) ∧
      (0 < Spec.expOf (cs.take j) →
        val st.1 % (pw n - val toll) = pw (Spec.expOf (cs.take j)) % (pw n - val toll)))
    (Nat.zero_le _) ⟨⟨by simp, trits_mkArray_zero n⟩, hy, by simp [Spec.expOf],
      fun h => by simp [Spec.expOf] at h⟩ ?_ ?_
  · intro j st _ hj hI
    obtain ⟨x, y, st⟩ := st
    obtain ⟨hx, hy, hst, hmod⟩ := hI
    dsimp only at hx hy hst hmod ⊢
    have hjl : j < cs.length := by omega
    have hje : j < (embed cs).size := by rw [size_embed]; exact hjl
    have hfj : FitsLen (j + 1) := FitsLen.of_le hfc (by omega)
    have hc2 : cs[j] ≤ 2 := hcs _ (List.getElem_mem _)
    have hE := expOf_take_succ cs j hjl
    rw [if_neg (ofNat_not_gt hj), atL_ofNat _ j hje, get_embed cs j hje, ok_bind]
    rw [show decide (Int.ofNat cs[j] ≥ 0) = true from decide_eq_true (Int.ofNat_nonneg _),
      show decide (Int.ofNat cs[j] ≤ 2) = true from decide_eq_true
        (show Int.ofNat cs[j] ≤ Int.ofNat 2 from (ofNat_le_iff _ _).mpr hc2)]
    simp only [if_true, pure_eq_ok, ok_bind, sudoAssert_true]
    cases st with
    | true =>
      have hE0 : 0 < Spec.expOf (cs.take j) := by simpa using hst.symm
      obtain ⟨x', y', hcube, hx', hy', hv'⟩ := cube_spec f n toll hn ht htt hts htn hfit x y hx hy
        cs[j] hc2
      refine ⟨(x', y', true), ⟨hx', hy', by simp [hE]; omega, fun _ => ?_⟩, ?_⟩
      · rw [hv', hE, pw_cube]
        exact emod_mul_cong (emod_mul_cong (emod_mul_cong (hmod hE0) (hmod hE0)) (hmod hE0)) rfl
      · simp only [if_true, hcube, ok_bind]
        exact asc_tail _ j hfj _
    | false =>
      have hE0 : Spec.expOf (cs.take j) = 0 := by simpa using hst.symm
      rw [hE0] at hE
      simp only [Bool.false_eq_true, if_false]
      rcases (by omega : cs[j] = 0 ∨ 0 < cs[j]) with hc | hc
      · refine ⟨(x, y, false), ⟨hx, hy, by simp [hE, hc], fun h => by omega⟩, ?_⟩
        simp only [hc, sEq_int, show Int.ofNat 0 = 0 from rfl, decide_True, Bool.not_true,
          Bool.false_eq_true, if_false, pure_eq_ok]
        exact asc_tail _ j hfj _
      · have hcn : cs[j] < (Array.mkArray n (0 : Int)).size := by simp; omega
        have hacc : Bs.start_accumulator f (Int.ofNat cs[j]) Bs.Phase.Sudo_5Phase_6Public =
            .ok ((Array.mkArray n (0 : Int)).set ⟨cs[j], hcn⟩ 1) := by
          unfold Bs.start_accumulator
          simp only [empty_register_spec f n hn, ok_bind]
          rw [putL_ofNat _ _ _ hcn]; rfl
        have hasz : ((Array.mkArray n (0 : Int)).set ⟨cs[j], hcn⟩ 1).size = n := by simp
        have hslide := slide_spec x ((Array.mkArray n (0 : Int)).set ⟨cs[j], hcn⟩ 1) (by simp [hx.size]) (by rw [hx.size]; exact hn0)
          (by rw [hx.size]; exact hfn)
        have hav : val ((Array.mkArray n (0 : Int)).set ⟨cs[j], hcn⟩ 1) = pw cs[j] := by
          rw [val_set, val_mkArray_zero]; simp
        refine ⟨((Array.mkArray n (0 : Int)).set ⟨cs[j], hcn⟩ 1, y, true),
          ⟨⟨hasz, trits_set (trits_mkArray_zero n) _ hcn (by decide)⟩, hy,
            by simp [hE]; omega, fun _ => by rw [hav, hE]; simp⟩, ?_⟩
        have hne : (!SudoRt.SEq.beq (Int.ofNat cs[j]) 0) = true := by
          simp [sEq_int]; omega
        simp only [hne, if_true, hacc, ok_bind, hslide]
        exact asc_tail _ j hfj _
  · intro st hI
    obtain ⟨x, y, st⟩ := st
    obtain ⟨hx, hy, hst, hmod⟩ := hI
    dsimp only at hx hy hst hmod ⊢
    rw [show cs.length - 1 + 1 = cs.length by omega, List.take_length] at hst hmod
    have hstt : st = true := by rw [hst]; simpa using hstart
    subst hstt
    obtain ⟨t, htid, hts', htt', htv⟩ := tidy_spec f n toll hn ht htt hts htn
      (FitsLen.of_le hfit (by omega)) x hx.trits hx.size
    refine ⟨(t, y), ?_, ⟨hts', htt'⟩, hy, ?_⟩
    · rw [sudoAssert_true, ok_bind, ← tidy_eq_in_place, htid, ok_bind]; rfl
    · rw [htv, hmod hstart]

def powI (b : Int) : Nat → Int
  | 0 => 1
  | e + 1 => b * powI b e

theorem powI_add (b : Int) (i j : Nat) : powI b (i + j) = powI b i * powI b j := by
  induction j with
  | zero => simp [powI]
  | succ j ih => rw [← Nat.add_assoc, powI, powI, ih, Int.mul_left_comm]

theorem powI_cube (b : Int) (E c : Nat) :
    powI b (3 * E + c) = powI b E * powI b E * powI b E * powI b c := by
  rw [powI_add, show 3 * E = E + E + E by omega, powI_add, powI_add]

theorem powI_natCast (v e : Nat) : powI (v : Int) e = ((v ^ e : Nat) : Int) := by
  induction e with
  | zero => rfl
  | succ e ih => rw [powI, ih, Nat.pow_succ, Int.ofNat_mul, Int.mul_comm]

theorem walk_shared_spec (f : Bs.Field) (n : Nat) (toll : Array Int)
    (hn : f.sudo_5Field_1n = Int.ofNat n) (ht : f.sudo_5Field_4toll = toll)
    (htt : Trits toll) (hts : 0 < toll.size) (htn : toll.size < n)
    (hfit : FitsLen (2 * n + 2)) (cs : List Nat) (hcs : ∀ c ∈ cs, c ≤ 2)
    (hfc : FitsLen cs.length) (hstart : 0 < Spec.expOf cs)
    (base : Array Int) (hb : Reg n base) (y : Array Int) (hy : Reg n y) :
    ∃ r, Bs.walk f (embed cs) (Bs.Phase.Sudo_5Phase_6Shared base) y = .ok r ∧
      Reg n r.1 ∧ Reg n r.2 ∧
      val r.1 = powI (val base) (Spec.expOf cs) % (pw n - val toll) := by
  have hcl : 0 < cs.length := by
    rcases cs with _ | ⟨c, cs⟩
    · simp [Spec.expOf] at hstart
    · simp
  have hfn : FitsLen n := FitsLen.of_le hfit (by omega)
  have hn0 : 0 < n := by omega
  unfold Bs.walk
  simp only [empty_register_spec f n hn, ok_bind, listLen_eq, size_embed]
  rw [subI_ofNat_one _ hcl hfc]
  simp only [ok_bind]
  rw [except_bind_pure, fuelRange_eq]
  refine asc_exists (fromN := 0) (toN := cs.length - 1) (s0 := (Array.mkArray n 0, y, false))
    (fun j (st : Array Int × Array Int × Bool) => Reg n st.1 ∧ Reg n st.2.1 ∧
      st.2.2 = decide (0 < Spec.expOf (cs.take j)) ∧
      (0 < Spec.expOf (cs.take j) →
        val st.1 % (pw n - val toll) =
          powI (val base) (Spec.expOf (cs.take j)) % (pw n - val toll)))
    (Nat.zero_le _) ⟨⟨by simp, trits_mkArray_zero n⟩, hy, by simp [Spec.expOf],
      fun h => by simp [Spec.expOf] at h⟩ ?_ ?_
  · intro j st _ hj hI
    obtain ⟨x, y, st⟩ := st
    obtain ⟨hx, hy, hst, hmod⟩ := hI
    dsimp only at hx hy hst hmod ⊢
    have hjl : j < cs.length := by omega
    have hje : j < (embed cs).size := by rw [size_embed]; exact hjl
    have hfj : FitsLen (j + 1) := FitsLen.of_le hfc (by omega)
    have hc2 : cs[j] ≤ 2 := hcs _ (List.getElem_mem _)
    have hE := expOf_take_succ cs j hjl
    rw [if_neg (ofNat_not_gt hj), atL_ofNat _ j hje, get_embed cs j hje, ok_bind]
    rw [show decide (Int.ofNat cs[j] ≥ 0) = true from decide_eq_true (Int.ofNat_nonneg _),
      show decide (Int.ofNat cs[j] ≤ 2) = true from decide_eq_true
        (show Int.ofNat cs[j] ≤ Int.ofNat 2 from (ofNat_le_iff _ _).mpr hc2)]
    simp only [if_true, pure_eq_ok, ok_bind, sudoAssert_true]
    cases st with
    | true =>
      have hE0 : 0 < Spec.expOf (cs.take j) := by simpa using hst.symm
      obtain ⟨x1, y1, hcube, hx1, hy1, hv1⟩ := cube_spec f n toll hn ht htt hts htn hfit x y hx hy
        0 (by decide)
      have hmb : ∀ z : Array Int, Reg n z → ∃ z', Bs.multiply f z base 0 = .ok z' ∧
          Bs.slide z z' = .ok z' ∧ Reg n z' ∧ val z' % (pw n - val toll) =
            (val z * val base) % (pw n - val toll) := by
        intro z hz
        obtain ⟨m, hm, hms, hmt, _, K, hK⟩ := multiply_spec f n toll hn ht htt hts htn z base
          hz.trits hb.trits hz.size hb.size 0 (by decide) (FitsLen.of_le hfit (by omega))
        refine ⟨m, hm, ?_, ⟨hms, hmt⟩, ?_⟩
        · exact slide_spec z m (by rw [hz.size, hms]) (by rw [hz.size]; exact hn0)
            (by rw [hz.size]; exact hfn)
        · rw [hK, emod_sub_mul, pw_zero, Int.mul_one]
      have hgoal : ∀ x' : Array Int, Reg n x' → val x' % (pw n - val toll) =
          (val x1 * powI (val base) cs[j]) % (pw n - val toll) →
          Reg n x' ∧ Reg n y1 ∧ true = decide (0 < Spec.expOf (cs.take (j + 1))) ∧
            (0 < Spec.expOf (cs.take (j + 1)) → val x' % (pw n - val toll) =
              powI (val base) (Spec.expOf (cs.take (j + 1))) % (pw n - val toll)) := by
        intro x' hx' hv'
        refine ⟨hx', hy1, by simp [hE]; omega, fun _ => ?_⟩
        rw [hv', hE, powI_cube]
        refine emod_mul_cong ?_ rfl
        rw [hv1, pw_zero, Int.mul_one]
        exact emod_mul_cong (emod_mul_cong (hmod hE0) (hmod hE0)) (hmod hE0)
      simp only [if_true, show (0 : Int) = Int.ofNat 0 from rfl, hcube, ok_bind]
      rcases (by omega : cs[j] = 0 ∨ cs[j] = 1 ∨ cs[j] = 2) with hc | hc | hc
      · refine ⟨(x1, y1, true), hgoal x1 hx1 (by rw [hc]; simp [powI]), ?_⟩
        rw [hc]
        rw [show (if (1:Int) > Int.ofNat 0 then 1 else (Int.ofNat 0 - 1).natAbs + 1) = 0 + 1 from rfl,
          runLoopOn_succ]
        simp
        exact asc_tail_cast _ _ hfj _
      · obtain ⟨x2, hm2, hs2, hx2, hv2⟩ := hmb x1 hx1
        refine ⟨(x2, y1, true), hgoal x2 hx2 (by rw [hv2, hc]; simp [powI]), ?_⟩
        rw [hc]
        rw [show (if (1:Int) > Int.ofNat 1 then 1 else (Int.ofNat 1 - 1).natAbs + 1) = 0 + 1 from rfl,
          runLoopOn_succ]
        simp [hm2, hs2]
        exact asc_tail_cast _ _ hfj _
      · obtain ⟨x2, hm2, hs2, hx2, hv2⟩ := hmb x1 hx1
        obtain ⟨x3, hm3, hs3, hx3, hv3⟩ := hmb x2 hx2
        refine ⟨(x3, y1, true), hgoal x3 hx3 ?_, ?_⟩
        · rw [hv3, emod_mul_cong hv2 rfl, hc]; simp [powI, Int.mul_assoc]
        rw [hc]
        rw [show (if (1:Int) > Int.ofNat 2 then 1 else (Int.ofNat 2 - 1).natAbs + 1) = 1 + 1 from rfl,
          runLoopOn_succ]
        simp [hm2, hs2, hm3, hs3, addI_1_1, runLoopOn_succ]
        exact asc_tail_cast _ _ hfj _
    | false =>
      have hE0 : Spec.expOf (cs.take j) = 0 := by simpa using hst.symm
      rw [hE0] at hE
      simp only [Bool.false_eq_true, if_false]
      rcases (by omega : cs[j] = 0 ∨ cs[j] = 1 ∨ cs[j] = 2) with hc | hc | hc
      · refine ⟨(x, y, false), ⟨hx, hy, by simp [hE, hc], fun h => by omega⟩, ?_⟩
        simp only [hc, sEq_int, show Int.ofNat 0 = 0 from rfl, decide_True, Bool.not_true,
          Bool.false_eq_true, if_false, pure_eq_ok]
        exact asc_tail _ j hfj _
      · have hacc : Bs.start_accumulator f (Int.ofNat cs[j]) (Bs.Phase.Sudo_5Phase_6Shared base) =
            .ok base := by
          unfold Bs.start_accumulator; rw [hc]; rfl
        have hslide := slide_spec x base (by rw [hx.size, hb.size]) (by rw [hx.size]; exact hn0)
          (by rw [hx.size]; exact hfn)
        refine ⟨(base, y, true), ⟨hb, hy, by simp [hE, hc], fun _ => by rw [hE, hc]; simp [powI]⟩, ?_⟩
        have hne : (!SudoRt.SEq.beq (Int.ofNat cs[j]) 0) = true := by
          simp [sEq_int]; omega
        simp only [hne, if_true, hacc, ok_bind, hslide]
        exact asc_tail _ j hfj _
      · obtain ⟨m, hm, hms, hmt, _, K, hK⟩ := multiply_spec f n toll hn ht htt hts htn base base
          hb.trits hb.trits hb.size hb.size 0 (by decide) (FitsLen.of_le hfit (by omega))
        have hacc : Bs.start_accumulator f (Int.ofNat cs[j]) (Bs.Phase.Sudo_5Phase_6Shared base) =
            .ok m := by
          unfold Bs.start_accumulator; rw [hc]
          have hm' : Bs.multiply f base base 0 = .ok m := hm
          simp only [sEq_int, hm', ok_bind]
          rfl
        have hslide := slide_spec x m (by rw [hx.size, hms]) (by rw [hx.size]; exact hn0)
          (by rw [hx.size]; exact hfn)
        refine ⟨(m, y, true), ⟨⟨hms, hmt⟩, hy, by simp [hE, hc], fun _ => ?_⟩, ?_⟩
        · rw [hK, emod_sub_mul, hE, hc]; simp [powI, pw_zero]
        have hne : (!SudoRt.SEq.beq (Int.ofNat cs[j]) 0) = true := by
          simp [sEq_int]; omega
        simp only [hne, if_true, hacc, ok_bind, hslide]
        exact asc_tail _ j hfj _
  · intro st hI
    obtain ⟨x, y, st⟩ := st
    obtain ⟨hx, hy, hst, hmod⟩ := hI
    dsimp only at hx hy hst hmod ⊢
    rw [show cs.length - 1 + 1 = cs.length by omega, List.take_length] at hst hmod
    have hstt : st = true := by rw [hst]; simpa using hstart
    subst hstt
    obtain ⟨t, htid, hts', htt', htv⟩ := tidy_spec f n toll hn ht htt hts htn
      (FitsLen.of_le hfit (by omega)) x hx.trits hx.size
    refine ⟨(t, y), ?_, ⟨hts', htt'⟩, hy, ?_⟩
    · rw [sudoAssert_true, ok_bind, ← tidy_eq_in_place, htid, ok_bind]; rfl
    · rw [htv, hmod hstart]

/-- B7, public phase, **given what the key reader returned**: if `read_key key` returns
    the cells `cells` (trits, with at least one white or red cell), the emitted
    `public_value` is the register holding `3^e mod p`, where `e` is the cells read as a
    base-3 number. The headline `public_value_refines` discharges the reader hypotheses. -/
theorem public_value_refines_of_read (F : Spec.Field) (hF : F.Wf) (h3 : 3 ≤ F.n)
    (hfit : FitsLen (2 * F.n + 2)) (key : Array Bs.KeyGrid) (cells : List Nat)
    (hread : Bs.read_key key = .ok (embed cells)) (hcells : ∀ c ∈ cells, c ≤ 2)
    (hfc : FitsLen cells.length) (hstart : 0 < Spec.expOf cells) :
    Bs.public_value (emb F) key = .ok (embed (Spec.publicValue F cells)) := by
  obtain ⟨htt, hts, htn⟩ := hF.embed_parts
  obtain ⟨r, hw, hr1, _, hv⟩ := walk_public_spec (emb F) F.n (embed F.toll) rfl rfl htt hts htn
    h3 hfit cells hcells hfc hstart (Array.mkArray F.n 0) ⟨by simp, trits_mkArray_zero _⟩
  unfold Bs.public_value Bs.public_walk
  rw [empty_register_spec (emb F) F.n rfl, ok_bind]
  dsimp only
  rw [hread, ok_bind, hw]
  show Except.ok r.1 = _
  congr 1
  apply eq_embed_toReg hr1.trits hr1.size
  rw [hv, ← p_cast F hF, pw_natCast]
  rfl

/-- B7, shared phase, **given what the key reader returned**: for a base register `C` of
    `n` trits, the emitted `shared_secret` is the register holding `C^e mod p`. The
    headline `shared_secret_refines` discharges the reader hypotheses. -/
theorem shared_secret_refines_of_read (F : Spec.Field) (hF : F.Wf)
    (hfit : FitsLen (2 * F.n + 2)) (key : Array Bs.KeyGrid) (base : List Nat)
    (hbase : Spec.IsReg F.n base) (cells : List Nat)
    (hread : Bs.read_key key = .ok (embed cells)) (hcells : ∀ c ∈ cells, c ≤ 2)
    (hfc : FitsLen cells.length) (hstart : 0 < Spec.expOf cells) :
    Bs.shared_secret (emb F) key (embed base) = .ok (embed (Spec.sharedSecret F base cells)) := by
  obtain ⟨htt, hts, htn⟩ := hF.embed_parts
  have hbs : (embed base).size = F.n := by rw [size_embed]; exact hbase.1
  obtain ⟨r, hw, hr1, _, hv⟩ := walk_shared_spec (emb F) F.n (embed F.toll) rfl rfl htt hts htn
    hfit cells hcells hfc hstart (embed base) ⟨hbs, trits_embed hbase.2⟩
    (Array.mkArray F.n 0) ⟨by simp, trits_mkArray_zero _⟩
  unfold Bs.shared_secret Bs.shared_walk
  rw [empty_register_spec (emb F) F.n rfl, ok_bind]
  dsimp only
  rw [sudoAssertEq_int (a := SudoRt.listLen (embed base)) (b := (emb F).sudo_5Field_1n)
    (by simp only [listLen_eq, hbs]; simp [emb]), ok_bind, hread, ok_bind, hw]
  show Except.ok r.1 = _
  congr 1
  apply eq_embed_toReg hr1.trits hr1.size
  rw [hv, ← p_cast F hF, val_embed, powI_natCast]
  rfl

end BsLink2.Link2
