/-
  LINK 2. `big_from_be` ≃ algebraic `fromBE` on byte strings that fit in
  two base-10^9 limbs.

  Domain `BeLimb2Wf`: length `≤ 7` and every byte `≤ 255`. Then
  `fromBE < 256^7 < 10^18`, so the value is at most two limbs (empty when
  zero). `256^3 < 10^9`, so a prefix of length `≤ 3` is still one limb.
  The fourth byte is where a second limb can appear. Each Horner step is
  `acc * 256 + b`: the multiply is the proved one-limb or two-limb product
  (`big_mul_acc` / `big_mul_two`, product below `10^18`), and the add is
  `big_add_byte`.

  Length 8 is out: `256^8 > 10^18`. The 28-byte pad block is out. Not
  `phi_chunk`. Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Link2.FromBeShort
import MegaDreifach.Link2.FactTwo

namespace MegaDreifach.Link2

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem toPure_eq_ok {α} (a : α) :
    (Applicative.toPure.1 a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem match_ok_cont {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.cont s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onCont s := by
  rfl

private theorem bind_pure_flow {σ ρ β} (fl : SudoRt.Flow σ ρ)
    (f : SudoRt.Flow σ ρ → Except SudoRt.Trap β) :
    (pure fl >>= f) = f fl := rfl

private theorem subI_two_one : SudoRt.subI (2 : Int) (1 : Int) = .ok (1 : Int) := by
  have h : FitsLen 2 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 2 1 h (by decide)]
  rfl

private theorem addI_zero_one : SudoRt.addI (0 : Int) (1 : Int) = .ok (1 : Int) := by
  erw [addI_ofNat 0 1 FitsLen.one]
  simp [Nat.zero_add]

private theorem addI_zero_nat (n : Nat) (h : FitsLen n) :
    SudoRt.addI (0 : Int) (Int.ofNat n) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (0 + n) := by simpa [Nat.zero_add] using h
  erw [addI_ofNat 0 n h0]
  simp [Nat.zero_add]

private theorem modI_nat_base (n : Nat) :
    SudoRt.modI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n % limbBase)) := by
  erw [limb_base_eq, modI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem divI_nat_base (n : Nat) :
    SudoRt.divI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n / limbBase)) := by
  erw [limb_base_eq, divI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem atL_head (xs : List Nat) (h : 0 < xs.length) :
    SudoRt.atL (embed xs) (0 : Int) = .ok (Int.ofNat xs[0]) := by
  erw [atL_embed xs 0 h]

private theorem atL_second (x0 x1 : Nat) :
    SudoRt.atL (embed [x0, x1]) (1 : Int) = .ok (Int.ofNat x1) := by
  erw [atL_embed [x0, x1] 1 (by simp)]
  simp

private theorem append_nat (xs : List Nat) (d : Nat) :
    (SudoRt.appendL (embed xs) (Int.ofNat d)).1 = embed (xs ++ [d]) := by
  rw [appendL_spec]
  exact push_embed xs d

private theorem fitsLen_list2 (a b : Nat) :
    FitsLen ([a, b] : List Nat).length := by
  have : ([a, b] : List Nat).length = 2 := by simp
  simpa [this] using (fits_le3 (by decide : (2 : Nat) ≤ 3))

/-- `256^7` still fits in two limbs. `256^8` does not. -/
theorem pow256_seven_lt_sq : 256 ^ 7 < limbBase ^ 2 := by
  unfold limbBase
  decide

theorem pow256_eight_ge_sq : limbBase ^ 2 ≤ 256 ^ 8 := by
  unfold limbBase
  decide

private theorem pow256_le {a b : Nat} (h : a ≤ b) : 256 ^ a ≤ 256 ^ b :=
  Nat.pow_le_pow_of_le_right (by decide : 256 > 0) h

private theorem fits7 : FitsLen 7 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits255 : FitsLen 255 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits_byte {b : Nat} (hb : b ≤ 255) : FitsLen b :=
  FitsLen.of_le fits255 hb

private theorem two56_lt_limb : 256 < limbBase := by
  unfold limbBase
  decide

private theorem two56_nat : bigNat 256 = bigOf [256] :=
  bigNat_limb 256 two56_lt_limb (by decide)

private theorem byte_lt_base {b : Nat} (hb : b ≤ 255) : b < limbBase := by
  have : (255 : Nat) < limbBase := by unfold limbBase; decide
  exact Nat.lt_of_le_of_lt hb this

private theorem sum_lt_two (x b : Nat) (hx : x < limbBase) (hb : b < limbBase) :
    x + b < 2 * limbBase := by
  have h : x + b < limbBase + limbBase := Nat.add_lt_add hx hb
  simpa [Nat.two_mul] using h

private theorem lo_byte_lt_two (lo b : Nat) (hlo : lo < limbBase) (hb : b < limbBase) :
    lo + b < 2 * limbBase :=
  sum_lt_two lo b hlo hb

private theorem fits_lt_two {n : Nat} (h : n < 2 * limbBase) : FitsLen n := by
  have hb : 2 * limbBase ≤ i64MaxNat := by
    unfold i64MaxNat limbBase
    decide
  exact Nat.le_trans (Nat.le_of_lt h) hb

private theorem div_byte_one (lo b : Nat) (hlo : lo < limbBase) (hb : b < limbBase)
    (hge : limbBase ≤ lo + b) : (lo + b) / limbBase = 1 := by
  have hlt : (lo + b) / limbBase < 2 :=
    div_lt_of_lt_mul limbBase_pos (lo_byte_lt_two lo b hlo hb)
  have hpos : 0 < (lo + b) / limbBase := div_pos_of_le limbBase_pos hge
  omega

private theorem mod_byte_sub (lo b : Nat) (hlo : lo < limbBase) (hb : b < limbBase)
    (hge : limbBase ≤ lo + b) : (lo + b) % limbBase = lo + b - limbBase := by
  have hdiv := div_byte_one lo b hlo hb hge
  have h := Nat.mod_add_div (lo + b) limbBase
  rw [hdiv, Nat.mul_one] at h
  omega

/-- Little-endian pair `[lo, hi]` is `lo + hi · 10^9`. -/
private theorem bigNat_pair (lo hi : Nat) (hlo : lo < limbBase) (hhi0 : 0 < hi)
    (hhi : hi < limbBase) :
    bigNat (lo + hi * limbBase) = bigOf [lo, hi] := by
  have hge : limbBase ≤ lo + hi * limbBase := by
    have hmul : limbBase ≤ hi * limbBase := by
      have : 1 * limbBase ≤ hi * limbBase := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hhi0)
      simpa [Nat.one_mul] using this
    exact Nat.le_trans hmul (Nat.le_add_left _ _)
  have hlt : lo + hi * limbBase < limbBase ^ 2 := by
    have h1 : lo + hi * limbBase < limbBase + hi * limbBase := Nat.add_lt_add_right hlo _
    have h2 : limbBase + hi * limbBase = (hi + 1) * limbBase := by
      rw [Nat.add_comm limbBase, Nat.succ_mul]
    have h3 : (hi + 1) * limbBase ≤ limbBase * limbBase :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hhi)
    have h4 : lo + hi * limbBase < limbBase * limbBase := by
      exact Nat.lt_of_lt_of_le (by simpa [h2] using h1) h3
    simpa [Nat.pow_two, Nat.mul_comm] using h4
  have hmod : (lo + hi * limbBase) % limbBase = lo := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlo]
  have hdiv : (lo + hi * limbBase) / limbBase = hi := by
    rw [Nat.add_mul_div_right lo hi limbBase_pos, Nat.div_eq_of_lt hlo, Nat.zero_add]
  rw [bigNat_two (lo + hi * limbBase) hge hlt, hmod, hdiv]

private theorem pair_add_comm (lo hi b : Nat) :
    lo + b + hi * limbBase = lo + hi * limbBase + b := by
  omega

private theorem carry_reassoc (lo hi b : Nat) (hge : limbBase ≤ lo + b) :
    lo + b - limbBase + (1 + hi) * limbBase = lo + hi * limbBase + b := by
  have hdist : (1 + hi) * limbBase = limbBase + hi * limbBase := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [hdist, ← Nat.add_assoc, Nat.sub_add_cancel hge]
  omega

private theorem high_succ_lt (lo hi b : Nat) (hge : limbBase ≤ lo + b)
    (hs : lo + hi * limbBase + b < limbBase ^ 2) : 1 + hi < limbBase := by
  have heq := carry_reassoc lo hi b hge
  have hres : lo + b - limbBase + (1 + hi) * limbBase < limbBase ^ 2 := by
    simpa [heq] using hs
  have hmul : (1 + hi) * limbBase < limbBase ^ 2 :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ (lo + b - limbBase)) hres
  have hmul' : (1 + hi) * limbBase < limbBase * limbBase := by
    simpa [Nat.pow_two] using hmul
  have hdiv : (1 + hi) * limbBase / limbBase < limbBase :=
    div_lt_of_lt_mul limbBase_pos hmul'
  simpa [Nat.mul_div_left (1 + hi) limbBase_pos] using hdiv

set_option maxHeartbeats 4000000 in
private theorem big_add_two_zero (lo hi : Nat) (hlo : lo < limbBase) (hhi0 : 0 < hi)
    (hhi : hi < limbBase) :
    Megadreifach.big_add (bigOf [lo, hi]) (bigOf []) =
      .ok (bigNat (lo + hi * limbBase)) := by
  unfold Megadreifach.big_add Megadreifach.mag_add
  dsimp [bigOf]
  have hlenx : SudoRt.listLen (embed [lo, hi]) = (2 : Int) := by rw [listLen_embed]; rfl
  have hleny : SudoRt.listLen (embed ([] : List Nat)) = (0 : Int) := by rw [listLen_embed]; rfl
  rw [hlenx, hleny]
  have hcmp : decide ((0 : Int) > (2 : Int)) = false := by decide
  rw [hcmp, if_neg (by decide : ¬ ((false : Bool) = true)), subI_two_one, ok_bind]
  dsimp
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
  dsimp
  rw [atL_head [lo, hi] (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [addI_zero_nat lo (fits_of_lt_limb hlo), ok_bind, modI_nat_base lo, ok_bind]
  have hmod : lo % limbBase = lo := Nat.mod_eq_of_lt hlo
  have hdiv : lo / limbBase = 0 := Nat.div_eq_of_lt hlo
  have happ : (SudoRt.appendL (#[] : Array Int) (Int.ofNat lo)).1 = embed [lo] := by
    simp [appendL_spec, embed]
  rw [hmod, happ, divI_nat_base lo, ok_bind, hdiv, bind_pure_flow]
  simp only [show ((0 : Int) == (1 : Int)) = false from by decide, toPure_eq_ok,
    addI_zero_one, ok_bind, match_ok_cont]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  rw [atL_second lo hi, ok_bind, addI_zero_nat hi (fits_of_lt_limb hhi), ok_bind,
    modI_nat_base hi, ok_bind, divI_nat_base hi, ok_bind]
  have hmod1 : hi % limbBase = hi := Nat.mod_eq_of_lt hhi
  have hdiv1 : hi / limbBase = 0 := Nat.div_eq_of_lt hhi
  rw [hmod1, hdiv1, append_nat [lo] hi, ok_bind]
  have hlist : [lo] ++ [hi] = [lo, hi] := rfl
  rw [hlist]
  dsimp
  rw [make_big_false [lo, hi] (fitsLen_list2 lo hi), ok_bind]
  have hdrop : dropTrail [lo, hi] = [lo, hi] := by
    rw [dropTrail_two, if_neg (Nat.ne_of_gt hhi0)]
  rw [hdrop, ← bigNat_pair lo hi hlo hhi0 hhi]

set_option maxHeartbeats 4000000 in
private theorem big_add_two_nocarry (lo hi b : Nat) (hlo : lo < limbBase) (hhi0 : 0 < hi)
    (hhi : hi < limbBase) (_hb0 : 0 < b) (_hb : b < limbBase) (hsum : lo + b < limbBase) :
    Megadreifach.big_add (bigOf [lo, hi]) (bigOf [b]) =
      .ok (bigNat (lo + hi * limbBase + b)) := by
  have hfit : FitsLen (lo + b) := fits_of_lt_limb hsum
  unfold Megadreifach.big_add Megadreifach.mag_add
  dsimp [bigOf]
  have hlenx : SudoRt.listLen (embed [lo, hi]) = (2 : Int) := by rw [listLen_embed]; rfl
  have hleny : SudoRt.listLen (embed [b]) = (1 : Int) := by rw [listLen_embed]; rfl
  rw [hlenx, hleny]
  have hcmp : decide ((1 : Int) > (2 : Int)) = false := by decide
  rw [hcmp, if_neg (by decide : ¬ ((false : Bool) = true)), subI_two_one, ok_bind]
  dsimp
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
  dsimp
  rw [atL_head [lo, hi] (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [addI_zero_nat lo (fits_of_lt_limb hlo), ok_bind, atL_head [b] (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [addI_ofNat lo b hfit, ok_bind, modI_nat_base (lo + b), ok_bind]
  have hmod : (lo + b) % limbBase = lo + b := Nat.mod_eq_of_lt hsum
  have hdiv : (lo + b) / limbBase = 0 := Nat.div_eq_of_lt hsum
  rw [hmod]
  have happ :
      (SudoRt.appendL (#[] : Array Int) (Int.ofNat (lo + b))).1 = embed [lo + b] := by
    simp [appendL_spec, embed]
  rw [happ, divI_nat_base (lo + b), ok_bind, hdiv, bind_pure_flow]
  simp only [show ((0 : Int) == (1 : Int)) = false from by decide, toPure_eq_ok,
    addI_zero_one, ok_bind, match_ok_cont]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  rw [atL_second lo hi, ok_bind, addI_zero_nat hi (fits_of_lt_limb hhi), ok_bind,
    modI_nat_base hi, ok_bind, divI_nat_base hi, ok_bind]
  have hmod1 : hi % limbBase = hi := Nat.mod_eq_of_lt hhi
  have hdiv1 : hi / limbBase = 0 := Nat.div_eq_of_lt hhi
  rw [hmod1, hdiv1, append_nat [lo + b] hi, ok_bind]
  have hlist : [lo + b] ++ [hi] = [lo + b, hi] := rfl
  rw [hlist]
  dsimp
  rw [make_big_false [lo + b, hi] (fitsLen_list2 (lo + b) hi), ok_bind]
  have hdrop : dropTrail [lo + b, hi] = [lo + b, hi] := by
    rw [dropTrail_two, if_neg (Nat.ne_of_gt hhi0)]
  have hpair := bigNat_pair (lo + b) hi hsum hhi0 hhi
  rw [hdrop, ← hpair, pair_add_comm lo hi b]

set_option maxHeartbeats 4000000 in
private theorem big_add_two_carry (lo hi b : Nat) (hlo : lo < limbBase) (hhi0 : 0 < hi)
    (_hhi : hi < limbBase) (_hb0 : 0 < b) (hb : b < limbBase)
    (hge : limbBase ≤ lo + b) (hs : lo + hi * limbBase + b < limbBase ^ 2) :
    Megadreifach.big_add (bigOf [lo, hi]) (bigOf [b]) =
      .ok (bigNat (lo + hi * limbBase + b)) := by
  have htwo : lo + b < 2 * limbBase := lo_byte_lt_two lo b hlo hb
  have hfit : FitsLen (lo + b) := fits_lt_two htwo
  have hmodn : (lo + b) % limbBase = lo + b - limbBase := mod_byte_sub lo b hlo hb hge
  have hdivn : (lo + b) / limbBase = 1 := div_byte_one lo b hlo hb hge
  have hhi1 : 1 + hi < limbBase := high_succ_lt lo hi b hge hs
  have hfitH : FitsLen (1 + hi) := fits_of_lt_limb hhi1
  unfold Megadreifach.big_add Megadreifach.mag_add
  dsimp [bigOf]
  have hlenx : SudoRt.listLen (embed [lo, hi]) = (2 : Int) := by rw [listLen_embed]; rfl
  have hleny : SudoRt.listLen (embed [b]) = (1 : Int) := by rw [listLen_embed]; rfl
  rw [hlenx, hleny]
  have hcmp : decide ((1 : Int) > (2 : Int)) = false := by decide
  rw [hcmp, if_neg (by decide : ¬ ((false : Bool) = true)), subI_two_one, ok_bind]
  dsimp
  rw [show (2 : Nat) = 1 + 1 from rfl, runLoopOn_succ]
  dsimp
  rw [atL_head [lo, hi] (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [addI_zero_nat lo (fits_of_lt_limb hlo), ok_bind, atL_head [b] (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [addI_ofNat lo b hfit, ok_bind, modI_nat_base (lo + b), ok_bind]
  rw [hmodn]
  have happ :
      (SudoRt.appendL (#[] : Array Int) (Int.ofNat (lo + b - limbBase))).1 =
        embed [lo + b - limbBase] := by
    simp [appendL_spec, embed]
  rw [happ, divI_nat_base (lo + b), ok_bind, hdivn, bind_pure_flow]
  simp only [show ((0 : Int) == (1 : Int)) = false from by decide, toPure_eq_ok,
    addI_zero_one, ok_bind, match_ok_cont]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  rw [atL_second lo hi, ok_bind]
  erw [addI_ofNat 1 hi hfitH]
  rw [ok_bind, modI_nat_base (1 + hi), ok_bind, divI_nat_base (1 + hi), ok_bind]
  have hmod1 : (1 + hi) % limbBase = 1 + hi := Nat.mod_eq_of_lt hhi1
  have hdiv1 : (1 + hi) / limbBase = 0 := Nat.div_eq_of_lt hhi1
  rw [hmod1, hdiv1, append_nat [lo + b - limbBase] (1 + hi), ok_bind]
  have hlist : [lo + b - limbBase] ++ [1 + hi] = [lo + b - limbBase, 1 + hi] := rfl
  rw [hlist]
  dsimp
  rw [make_big_false [lo + b - limbBase, 1 + hi]
      (fitsLen_list2 (lo + b - limbBase) (1 + hi)), ok_bind]
  have hpos : 0 < 1 + hi := by omega
  have hdrop : dropTrail [lo + b - limbBase, 1 + hi] =
      [lo + b - limbBase, 1 + hi] := by
    rw [dropTrail_two, if_neg (Nat.ne_of_gt hpos)]
  have hlow : lo + b - limbBase < limbBase := by
    have hlt2 : lo + b < 2 * limbBase := htwo
    omega
  have hpair := bigNat_pair (lo + b - limbBase) (1 + hi) hlow hpos hhi1
  rw [hdrop, ← hpair, carry_reassoc lo hi b hge]

/-- Add a one-limb digit. Both the left value and the sum stay below `10^18`. -/
theorem big_add_byte (x b : Nat) (hx : x < limbBase ^ 2) (hb : b < limbBase)
    (hs : x + b < limbBase ^ 2) :
    Megadreifach.big_add (bigNat x) (bigNat b) = .ok (bigNat (x + b)) := by
  by_cases hxL : x < limbBase
  · have h2 : x < 2 * limbBase := Nat.lt_trans hxL (by
      have : limbBase < 2 * limbBase := by
        have := limbBase_pos
        omega
      exact this)
    have hs2 : x + b < 2 * limbBase := sum_lt_two x b hxL hb
    exact big_add_wide x b h2 hb hs2
  · have hge : limbBase ≤ x := Nat.le_of_not_lt hxL
    have hlo : x % limbBase < limbBase := Nat.mod_lt _ limbBase_pos
    have hhiLt : x / limbBase < limbBase := by
      rw [limbBase_pow2] at hx
      exact div_lt_of_lt_mul limbBase_pos hx
    have hhi0 : 0 < x / limbBase := div_pos_of_le limbBase_pos hge
    have hrepr : x % limbBase + (x / limbBase) * limbBase = x := by
      simpa [Nat.mul_comm] using Nat.mod_add_div x limbBase
    rw [bigNat_two x hge hx]
    by_cases hb0 : b = 0
    · rw [hb0, Nat.add_zero, bigNat_zero]
      have h := big_add_two_zero (x % limbBase) (x / limbBase) hlo hhi0 hhiLt
      simpa [hrepr] using h
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      rw [bigNat_limb b hb hb0]
      have hs' : x % limbBase + (x / limbBase) * limbBase + b < limbBase ^ 2 := by
        simpa [hrepr] using hs
      by_cases hnoc : x % limbBase + b < limbBase
      · have h := big_add_two_nocarry (x % limbBase) (x / limbBase) b
          hlo hhi0 hhiLt hbpos hb hnoc
        simpa [hrepr] using h
      · have hgeB : limbBase ≤ x % limbBase + b := Nat.le_of_not_lt hnoc
        have h := big_add_two_carry (x % limbBase) (x / limbBase) b
          hlo hhi0 hhiLt hbpos hb hgeB hs'
        simpa [hrepr] using h

/-! ## Horner domain -/

/-- Trap-free domain for a two-limb `big_from_be`.

    Length `≤ 7` keeps every prefix of the base-256 Horner below `256^7`,
    hence below `10^18`. Bytes `≤ 255` are the digits `fromBE` expects. -/
structure BeLimb2Wf (bs : List Nat) : Prop where
  len : bs.length ≤ 7
  byte : ∀ b ∈ bs, b ≤ 255

/-- Array-side two-limb big-endian domain. -/
structure WellFormedBeLimb2 (a : Array Int) : Prop where
  len : a.size ≤ 7
  nn : Nonneg a
  byte : ∀ x ∈ decode a, x ≤ 255

theorem beLimb2_decode (a : Array Int) (h : WellFormedBeLimb2 a) :
    BeLimb2Wf (decode a) where
  len := by
    have : (decode a).length = a.size := by simp [decode]
    rw [this]
    exact h.len
  byte := h.byte

private theorem byte_lt (bs : List Nat) (h : BeLimb2Wf bs) :
    ∀ b ∈ bs, b < 256 := by
  intro b hb
  exact Nat.lt_of_le_of_lt (h.byte b hb) (by decide : 255 < 256)

private theorem fromBE_nil : fromBE [] = 0 := by
  simp [fromBE, mixEncode]

private theorem fromBE_eq_acc (bs : List Nat) :
    fromBE bs = oriAcc 256 bs bs.length := by
  rw [oriAcc, List.take_length]
  unfold fromBE
  exact (hornerAcc_mix 256 bs).symm

private theorem ori_limb2_lt (bs : List Nat) (hb : ∀ b ∈ bs, b < 256)
    (i : Nat) (hi7 : i ≤ 7) (hlen : i ≤ bs.length) :
    oriAcc 256 bs i < limbBase ^ 2 := by
  have h1 := oriAcc_lt (r := 256) bs hb i hlen
  have h2 : 256 ^ i ≤ 256 ^ 7 := pow256_le hi7
  exact Nat.lt_trans (Nat.lt_of_lt_of_le h1 h2) pow256_seven_lt_sq

theorem fromBE_limb2_lt_sq (bs : List Nat) (h : BeLimb2Wf bs) :
    fromBE bs < limbBase ^ 2 := by
  rw [fromBE_eq_acc]
  exact ori_limb2_lt bs (byte_lt bs h) bs.length h.len (Nat.le_refl _)

private theorem beFromStep_gt (bs : Array Int) (two56 : Megadreifach.BigInt)
    (toV i : Int) (n : Megadreifach.BigInt) (h : i > toV) :
    beFromStep bs two56 toV (i, n) = .ok (SudoRt.Flow.brk (i, n)) := by
  unfold beFromStep
  rw [if_pos h]
  rfl

private theorem mul_256 (a : Nat) (ha : a < limbBase ^ 2) (hp : a * 256 < limbBase ^ 2) :
    Megadreifach.big_mul (bigNat a) (bigNat 256) = .ok (bigNat (a * 256)) := by
  by_cases hlt : a < limbBase
  · exact big_mul_acc a 256 (by decide) two56_lt_limb hlt
  · exact big_mul_two a 256 (by decide) two56_lt_limb (Nat.le_of_not_lt hlt) ha hp

/-- One Horner step `acc * 256 + byte` while the value stays below `10^18`. -/
private theorem beLimb2Step (bs : List Nat) (h : BeLimb2Wf bs) (i : Nat)
    (hi : i < bs.length) :
    beFromStep (embed bs) (bigOf [256]) (Int.ofNat (bs.length - 1))
        (Int.ofNat i, bigNat (oriAcc 256 bs i)) =
      if i = bs.length - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, bigNat (oriAcc 256 bs (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), bigNat (oriAcc 256 bs (i + 1)))) := by
  unfold beFromStep
  dsimp
  have hlen7 : bs.length ≤ 7 := h.len
  have hle : i ≤ bs.length - 1 := by omega
  have hngt : ¬ (i : Int) > ((bs.length - 1 : Nat) : Int) := ofNat_not_gt hle
  rw [if_neg hngt]
  have hb := byte_lt bs h
  have hi7 : i ≤ 7 := by omega
  have hacc : oriAcc 256 bs i < limbBase ^ 2 :=
    ori_limb2_lt bs hb i hi7 (Nat.le_of_lt hi)
  have hmem : bs[i] ∈ bs := List.getElem_mem hi
  have hble : bs[i] ≤ 255 := h.byte _ hmem
  have hblimb : bs[i] < limbBase := byte_lt_base hble
  have hsum_eq : oriAcc 256 bs i * 256 + bs[i] = oriAcc 256 bs (i + 1) :=
    (oriAcc_succ 256 bs i hi).symm
  have hi1 : i + 1 ≤ 7 := by omega
  have hnext : oriAcc 256 bs (i + 1) < limbBase ^ 2 :=
    ori_limb2_lt bs hb (i + 1) hi1 (Nat.succ_le_of_lt hi)
  have hprod : oriAcc 256 bs i * 256 < limbBase ^ 2 := by
    have hleP : oriAcc 256 bs i * 256 ≤ oriAcc 256 bs i * 256 + bs[i] :=
      Nat.le_add_right _ _
    rw [hsum_eq] at hleP
    exact Nat.lt_of_le_of_lt hleP hnext
  have hsum : oriAcc 256 bs i * 256 + bs[i] < limbBase ^ 2 := by
    rw [hsum_eq]; exact hnext
  rw [show bigOf [256] = bigNat 256 from two56_nat.symm]
  rw [mul_256 (oriAcc 256 bs i) hacc hprod, ok_bind]
  have hat := atL_embed bs i hi
  rw [ofNat_eq_natCast i] at hat
  rw [hat, ok_bind]
  rw [big_from_int_refines (bs[i]) (fits_byte hble), ok_bind]
  rw [show bigOf (limbsOfNat (bs[i])) = bigNat (bs[i]) from rfl]
  rw [big_add_byte (oriAcc 256 bs i * 256) (bs[i]) hprod hblimb hsum, ok_bind,
    hsum_eq, pure_eq_ok]
  simp only [ok_bind]
  by_cases heq : i = bs.length - 1
  · have hbeq : ((i : Int) == ((bs.length - 1 : Nat) : Int)) = true := by
      simp [beq_int_iff, heq]
    rw [if_pos hbeq, if_pos heq]
    exact pure_eq_ok _
  · have hneI : (i : Int) ≠ ((bs.length - 1 : Nat) : Int) :=
      fun hq => heq (Int.ofNat.inj hq)
    have hbeq : ((i : Int) == ((bs.length - 1 : Nat) : Int)) = false := by
      simpa [beq_int_iff] using hneI
    have hneB : ¬ ((i : Int) == ((bs.length - 1 : Nat) : Int)) = true := by
      rw [hbeq]; decide
    have hadd := addI_ofNat_one i (FitsLen.of_le fits7 (by omega))
    rw [ofNat_eq_natCast i] at hadd
    rw [if_neg hneB, hadd, ok_bind, pure_eq_ok, if_neg heq]
    rfl

/-- `big_from_be` agrees with `fromBE` on `BeLimb2Wf` (length `≤ 7`). -/
theorem big_from_be_limb2 (bs : List Nat) (h : BeLimb2Wf bs) :
    Megadreifach.big_from_be (embed bs) = .ok (bigNat (fromBE bs)) := by
  unfold Megadreifach.big_from_be
  rw [big_zero_spec, ok_bind, two56_refines, ok_bind, listLen_embed]
  cases hlen : bs.length with
  | zero =>
    have hempty : bs = [] := List.length_eq_zero.mp hlen
    subst hempty
    rw [show SudoRt.subI (Int.ofNat 0) (1 : Int) = .ok (-1) from subI_zero_one,
      ok_bind]
    dsimp
    rw [except_bind_pure]
    have hgt : (0 : Int) > (-1) := by decide
    rw [show (1 : Nat) = fuelRange (0 : Int) (-1) from (fuelRange_gt hgt).symm]
    apply Eq.trans
    · apply runLoopOn_step_pointwise
        (step' := beFromStep (embed ([] : List Nat)) (bigOf [256]) (-1))
      intro σ
      unfold beFromStep
      dsimp
      rfl
    · rw [asc_break (0 : Int) (-1) (bigOf []) _ _ _ hgt
          (beFromStep_gt (embed ([] : List Nat)) (bigOf [256]) (-1) 0 (bigOf []) hgt),
        pure_eq_ok, fromBE_nil, bigNat_zero]
  | succ k =>
    have hpos : 0 < k + 1 := Nat.succ_pos k
    have hfits : FitsLen (k + 1) :=
      FitsLen.of_le fits7 (by rw [← hlen]; exact h.len)
    rw [subI_ofNat_one (k + 1) hpos hfits, ok_bind]
    dsimp
    rw [fuelRange_eq (0 : Int) (k : Int), except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise
        (step' := beFromStep (embed bs) (bigOf [256]) (k : Int))
      intro σ
      unfold beFromStep
      dsimp
      rfl
    · have hstate :
          ((0 : Int), bigOf []) =
            (Int.ofNat 0, bigNat (oriAcc 256 bs 0)) := by
        rw [oriAcc_zero, bigNat_zero]
        rfl
      rw [hstate]
      apply chain_loop
        (f := fun j => bigNat (oriAcc 256 bs j))
        (fromN := 0) (toN := k)
        (hle := Nat.zero_le _)
        (goal := .ok (bigNat (fromBE bs)))
      · intro i _hlo hhi
        have hi : i < bs.length := by
          have hklen : k + 1 = bs.length := hlen.symm
          omega
        have hs := beLimb2Step bs h i hi
        have hto : bs.length - 1 = k := by
          have hklen : k + 1 = bs.length := hlen.symm
          omega
        rw [hto] at hs
        exact hs
      · have hk : k + 1 = bs.length := hlen.symm
        rw [hk, fromBE_eq_acc, pure_eq_ok]

/-- Same refinement on a nonnegative `Array Int` in `WellFormedBeLimb2`. -/
theorem big_from_be_limb2_array (a : Array Int) (h : WellFormedBeLimb2 a) :
    Megadreifach.big_from_be a = .ok (bigNat (fromBE (decode a))) := by
  have hr := big_from_be_limb2 (decode a) (beLimb2_decode a h)
  simpa [embed_decode a h.nn] using hr

end MegaDreifach.Link2
