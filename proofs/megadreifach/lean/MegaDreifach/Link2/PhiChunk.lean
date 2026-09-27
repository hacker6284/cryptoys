/-
  LINK 2. `phi_chunk` ≃ algebraic `phiUnrank` on the 28-byte pad block.

  Domain `PhiChunkWf` / `WellFormedPhiChunk`: length exactly 28 and every
  byte `≤ 255`. Then `big_from_be` reads the block as `fromBE bs < 256^28 =
  2^224 < 52!`, so every legal pad block is a legal Lehmer rank.

  The generated loop peels `51!, 50!, …, 1!` off the running remainder
  (`peel_leading_51`, `big_from_be_pad`), appends `avail[digit]`, and
  rebuilds `avail` by copying every index `t ≠ digit` (`erase_loop`). Its
  output is `applyDigits` of `mixDecode (descending 52)`, i.e. `phiUnrank`.

  Algebraic Link 2 only. Not `phi_inv`. Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.FromBePad
import MegaDreifach.Link2.Peel51
import MegaDreifach.Link2.EvenRank
import MegaDreifach.Factoradic

namespace MegaDreifach.Link2

set_option maxHeartbeats 8000000

/-! ## Domain -/

/-- Trap-free domain for a length-28 pad block.

    Length exactly 28 (the emitted `phi_chunk` asserts `listLen = pad_block`)
    and bytes `≤ 255` keep `fromBE bs < 2^224 < 52!`. -/
structure PhiChunkWf (bs : List Nat) : Prop where
  len : bs.length = 28
  byte : ∀ b ∈ bs, b ≤ 255

/-- Array-side pad-block domain: `phi_chunk` asserts `size = 28`. -/
structure WellFormedPhiChunk (a : Array Int) : Prop where
  size : a.size = 28
  nn : Nonneg a
  byte : ∀ x ∈ decode a, x ≤ 255

theorem phiChunk_bePadWf (bs : List Nat) (h : PhiChunkWf bs) : BePadWf bs where
  len := by rw [h.len]; decide
  byte := h.byte

theorem phiChunk_decode (a : Array Int) (h : WellFormedPhiChunk a) :
    PhiChunkWf (decode a) where
  len := by
    have : (decode a).length = a.size := by simp [decode]
    rw [this, h.size]
  byte := h.byte

/-! ## Rank bound -/

private theorem fromBE_eq_oriAcc (bs : List Nat) :
    fromBE bs = oriAcc 256 bs bs.length := by
  unfold fromBE oriAcc
  rw [List.take_length]
  exact (hornerAcc_mix 256 bs).symm

private theorem fromBE_lt_pow_len (bs : List Nat) (hb : ∀ b ∈ bs, b < 256) :
    fromBE bs < 256 ^ bs.length := by
  rw [fromBE_eq_oriAcc]
  exact oriAcc_lt (r := 256) bs hb bs.length (Nat.le_refl _)

private theorem pow256_28_eq_phiMax : (256 : Nat) ^ 28 = phiMax := by
  have h256 : (256 : Nat) = 2 ^ 8 := by decide
  unfold phiMax
  rw [h256, ← Nat.pow_mul]

/-- A length-28 byte string is a legal Lehmer rank: `fromBE bs < 52!`. -/
theorem phiChunk_rank_lt (bs : List Nat) (h : PhiChunkWf bs) :
    fromBE bs < factorial 52 := by
  have hb : ∀ b ∈ bs, b < 256 := by
    intro b hbmem
    exact Nat.lt_of_le_of_lt (h.byte b hbmem) (by decide : 255 < 256)
  have hlt := fromBE_lt_pow_len bs hb
  rw [h.len, pow256_28_eq_phiMax] at hlt
  exact Nat.lt_trans hlt two_pow_224_lt_fact_52

/-! ## Mixed-radix digits of a rank

  `digitsOf rank = mixDecode (descending 52) rank`, radices `52, 51, …, 1`.
  At position `i` the radix is `52 - i` and the remaining value is
  `rank % (52 - i)!`, so the digit is `rank % (52 - i)! / (51 - i)!`. -/

/-- The 52 mixed-radix digits of `rank`. -/
def digitsOf (rank : Nat) : List Nat := mixDecode (descending 52) rank

theorem mixDecode_cons (r : Nat) (rs : List Nat) (val : Nat) :
    mixDecode (r :: rs) val = val / product rs :: mixDecode rs (val % product rs) := rfl

/-- Lehmer digit fed to the loop at step `i` (`i < 52`). -/
def digitAt (rank i : Nat) : Nat := rank % factorial (52 - i) / factorial (51 - i)

theorem digitsOf_length (rank : Nat) : (digitsOf rank).length = 52 := by
  simp [digitsOf, mixDecode_length, descending_length]

theorem descending_getElem? (n i : Nat) (hi : i < n) :
    (descending n)[i]? = some (n - i) := by
  induction i generalizing n with
  | zero =>
    cases n with
    | zero => omega
    | succ m => simp [descending]
  | succ i ih =>
    cases n with
    | zero => omega
    | succ m =>
      have hi' : i < m := by omega
      rw [show descending (m + 1) = (m + 1) :: descending m from rfl,
        List.getElem?_cons_succ, ih m hi']
      congr 1
      omega

/-- `drop` of the digit list is the decode of the mixed-radix remainder. -/
theorem digitsOf_drop (rank i : Nat) (hrank : rank < factorial 52) (hi : i ≤ 52) :
    (digitsOf rank).drop i =
      mixDecode (descending (52 - i)) (rank % factorial (52 - i)) := by
  induction i with
  | zero =>
    rw [Nat.sub_zero, Nat.mod_eq_of_lt hrank]
    rfl
  | succ i ih =>
    have hi' : i ≤ 52 := by omega
    have hstep : 52 - i = (51 - i) + 1 := by omega
    have h52 : 52 - (i + 1) = 51 - i := by omega
    have hdesc : descending (52 - i) = (52 - i) :: descending (51 - i) := by
      rw [show 52 - i = (51 - i) + 1 from hstep, descending_succ]
    rw [← List.drop_drop 1 i (digitsOf rank), ih hi', h52, hdesc, mixDecode_cons,
      product_descending]
    have hdvd : factorial (51 - i) ∣ factorial (52 - i) := by
      rw [show 52 - i = (51 - i) + 1 from hstep]
      exact factorial_dvd_succ (51 - i)
    rw [Nat.mod_mod_of_dvd _ hdvd]
    rfl

/-- The digit at `i` is `digitAt`. -/
theorem digitsOf_getElem (rank i : Nat) (hrank : rank < factorial 52) (hi : i < 52) :
    (digitsOf rank)[i] = digitAt rank i := by
  have hdrop := digitsOf_drop rank i hrank (by omega)
  have hstep : 52 - i = (51 - i) + 1 := by omega
  have hdesc : descending (52 - i) = (52 - i) :: descending (51 - i) := by
    rw [show 52 - i = (51 - i) + 1 from hstep, descending_succ]
  rw [hdesc, mixDecode_cons, product_descending] at hdrop
  have hhead : ((digitsOf rank).drop i).head? = some (digitAt rank i) := by
    rw [hdrop]
    rfl
  rw [List.head?_drop] at hhead
  rw [List.getElem?_eq_getElem (by rw [digitsOf_length]; exact hi)] at hhead
  exact Option.some.inj hhead

/-- Every digit is below its radix `52 - i`. -/
theorem digitsOf_lt (rank i : Nat) (hrank : rank < factorial 52) (hi : i < 52) :
    (digitsOf rank)[i] < 52 - i := by
  have hlp : rank < product (descending 52) := by
    simpa [product_descending] using hrank
  have hb := mixDecode_bound (descending 52) rank hlp (descending_pos 52) i
    (by rw [mixDecode_length, descending_length]; exact hi)
  have hget : (mixDecode (descending 52) rank)[i]?.getD 0 =
      (mixDecode (descending 52) rank)[i] := by
    rw [List.getElem?_eq_getElem (by rw [mixDecode_length, descending_length]; exact hi)]
    rfl
  have hrad : (descending 52)[i]?.getD 0 = 52 - i := by
    rw [descending_getElem? 52 i hi]
    rfl
  rw [hget, hrad] at hb
  simpa only [digitsOf] using hb

/-- The digit read through `getElem?` is below its radix. -/
theorem digitsOf_getD_lt (rank i : Nat) (hrank : rank < factorial 52) (hi : i < 52) :
    (digitsOf rank)[i]?.getD 0 < 52 - i := by
  rw [List.getElem?_eq_getElem (by rw [digitsOf_length]; exact hi)]
  simp only [Option.getD_some]
  exact digitsOf_lt rank i hrank hi

/-- `drop i` of the digit list starts with `digitAt rank i`. -/
theorem digitsOf_drop_cons (rank i : Nat) (hrank : rank < factorial 52) (hi : i < 52) :
    (digitsOf rank).drop i = digitAt rank i :: (digitsOf rank).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [digitsOf_length]; omega),
    digitsOf_getElem rank i hrank hi]

/-! ## Leftover of `applyDigits`

  `leftoverFrom avail ds` is the list left in `applyDigits avail ds` after
  consuming the valid digits `ds`. The emitted inner loop rebuilds exactly
  this leftover by copying every index that is not the picked one. -/

def leftoverFrom : List Nat → List Nat → List Nat
  | [], _ => []
  | avail, [] => avail
  | avail, d :: ds =>
      if d < avail.length then leftoverFrom (avail.eraseIdx d) ds else avail

theorem leftoverFrom_nil (avail : List Nat) : leftoverFrom avail [] = avail := by
  cases avail <;> rfl

theorem leftoverFrom_nil_left (ds : List Nat) : leftoverFrom [] ds = [] := by
  cases ds <;> rfl

theorem leftoverFrom_cons (avail : List Nat) (d : Nat) (ds : List Nat) :
    leftoverFrom avail (d :: ds) =
      if d < avail.length then leftoverFrom (avail.eraseIdx d) ds else avail := by
  cases avail <;> simp [leftoverFrom]

/-- `leftoverFrom` of `ds ++ [d]`, when every digit of `ds` is in range. -/
theorem leftoverFrom_snoc (avail ds : List Nat) (d : Nat)
    (hvalid : ∀ j, j < ds.length →
      ds[j]?.getD 0 < (leftoverFrom avail (ds.take j)).length) :
    leftoverFrom avail (ds ++ [d]) =
      if d < (leftoverFrom avail ds).length then (leftoverFrom avail ds).eraseIdx d
      else leftoverFrom avail ds := by
  induction ds generalizing avail with
  | nil => simp only [List.nil_append, leftoverFrom_cons, leftoverFrom_nil]
  | cons d' ds' ih =>
    have h0 : d' < avail.length := by
      have := hvalid 0 (Nat.zero_lt_succ _)
      simpa [List.getElem?_cons_zero, List.take_zero, leftoverFrom_nil] using this
    have hval' : ∀ j, j < ds'.length →
        ds'[j]?.getD 0 < (leftoverFrom (avail.eraseIdx d') (ds'.take j)).length := by
      intro j hj
      have h1 := hvalid (j + 1) (Nat.succ_lt_succ hj)
      simpa [List.getElem?_cons_succ, List.take_succ_cons, leftoverFrom_cons, h0] using h1
    rw [List.cons_append, leftoverFrom_cons, if_pos h0,
      ih (avail.eraseIdx d') hval', leftoverFrom_cons, if_pos h0]

/-- Leftover of the first `i` digits of `rank`. -/
def phiLeftover (rank i : Nat) : List Nat :=
  leftoverFrom (List.range 52) ((digitsOf rank).take i)

/-- Mixed-radix remainder after the first `i` digits. -/
def phiRem (rank i : Nat) : Nat := rank % factorial (52 - i)

@[simp] theorem phiLeftover_def (rank i : Nat) :
    phiLeftover rank i = leftoverFrom (List.range 52) ((digitsOf rank).take i) := rfl

@[simp] theorem phiRem_def (rank i : Nat) :
    phiRem rank i = rank % factorial (52 - i) := rfl

theorem phiLeftover_zero (rank : Nat) : phiLeftover rank 0 = List.range 52 := by
  simp [phiLeftover, leftoverFrom_nil]

/-- The leftover loses exactly one element per digit. -/
theorem phiLeftover_length (rank : Nat) (hrank : rank < factorial 52) :
    ∀ i, i ≤ 52 → (phiLeftover rank i).length = 52 - i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    cases i with
    | zero => rw [phiLeftover_zero, List.length_range]
    | succ j =>
      have hj : j ≤ 52 := by omega
      have hlt : j < 52 := by omega
      have hlen_j : (phiLeftover rank j).length = 52 - j := ih j (by omega) hj
      have hvalid : ∀ k, k < ((digitsOf rank).take j).length →
          ((digitsOf rank).take j)[k]?.getD 0 <
            (leftoverFrom (List.range 52) (((digitsOf rank).take j).take k)).length := by
        intro k hk
        rw [List.length_take] at hk
        have hk' : k < j := by omega
        have htake : ((digitsOf rank).take j).take k = (digitsOf rank).take k := by
          rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hk')]
        have hget : ((digitsOf rank).take j)[k]?.getD 0 = (digitsOf rank)[k]?.getD 0 := by
          rw [List.getElem?_take, if_pos hk']
        have hlen_k : (phiLeftover rank k).length = 52 - k :=
          ih k (by omega) (by omega)
        rw [htake, hget, ← phiLeftover_def, hlen_k]
        exact digitsOf_getD_lt rank k hrank (by omega)
      have hd : (digitsOf rank)[j] < (phiLeftover rank j).length := by
        rw [hlen_j]
        exact digitsOf_lt rank j hrank hlt
      rw [phiLeftover_def] at hd
      have hsucc : phiLeftover rank (j + 1) =
          leftoverFrom (List.range 52)
            ((digitsOf rank).take j ++ [(digitsOf rank)[j]]) := by
        rw [phiLeftover, take_succ_get (digitsOf rank) j
          (by rw [digitsOf_length]; omega)]
      rw [hsucc, leftoverFrom_snoc (List.range 52) ((digitsOf rank).take j) _ hvalid,
        if_pos hd, List.length_eraseIdx, if_pos hd, ← phiLeftover_def, hlen_j]
      omega

/-- Every digit is below the current leftover length. -/
theorem phiDigit_lt_leftover (rank i : Nat) (hrank : rank < factorial 52) (hi : i < 52) :
    (digitsOf rank)[i] < (phiLeftover rank i).length := by
  rw [phiLeftover_length rank hrank i (by omega)]
  exact digitsOf_lt rank i hrank hi

/-- One step of `leftoverFrom` on the digit list. -/
theorem phiLeftover_succ (rank i : Nat) (hrank : rank < factorial 52) (hi : i < 52) :
    phiLeftover rank (i + 1) = (phiLeftover rank i).eraseIdx ((digitsOf rank)[i]) := by
  have hvalid : ∀ k, k < ((digitsOf rank).take i).length →
      ((digitsOf rank).take i)[k]?.getD 0 <
        (leftoverFrom (List.range 52) (((digitsOf rank).take i).take k)).length := by
    intro k hk
    rw [List.length_take] at hk
    have hk' : k < i := by omega
    have htake : ((digitsOf rank).take i).take k = (digitsOf rank).take k := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hk')]
    have hget : ((digitsOf rank).take i)[k]?.getD 0 = (digitsOf rank)[k]?.getD 0 := by
      rw [List.getElem?_take, if_pos hk']
    rw [htake, hget, ← phiLeftover_def, phiLeftover_length rank hrank k (by omega)]
    exact digitsOf_getD_lt rank k hrank (by omega)
  have hd : (digitsOf rank)[i] < (phiLeftover rank i).length :=
    phiDigit_lt_leftover rank i hrank hi
  rw [phiLeftover_def] at hd
  rw [phiLeftover, take_succ_get (digitsOf rank) i
    (by rw [digitsOf_length]; omega)]
  rw [leftoverFrom_snoc (List.range 52) ((digitsOf rank).take i) _ hvalid, if_pos hd,
    ← phiLeftover_def]

/-- The leftover after all 52 digits is empty. -/
theorem phiLeftover_full (rank : Nat) (hrank : rank < factorial 52) :
    phiLeftover rank 52 = [] := by
  apply List.length_eq_zero.mp
  rw [phiLeftover_length rank hrank 52 (Nat.le_refl _)]

/-! ## Inner copy loop

  The generated inner loop copies every index `t ≠ idx` of `avail` into a
  fresh array, i.e. `List.eraseIdx`. Same shape as `EvenRank.eraseStep`, but
  the emitter's return payload is `Array Int`. -/

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem beq_ofNat (a b : Nat) :
    SudoRt.SEq.beq (a : Int) (b : Int) = decide (a = b) := by
  rw [sEq_int, decide_eq_decide]
  constructor
  · intro h
    exact Int.ofNat.inj (by simpa [ofNat_eq_natCast] using h)
  · intro h
    simp [h, ofNat_eq_natCast]

/-- Generated inner rebuild closure, in the shape the emitter leaves it. -/
def phiEraseStep (avail : Array Int) (idx toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) (Array Int)) :=
  let t := σ.1
  let fresh := σ.2
  do
    if t > toV then
      pure (SudoRt.Flow.brk (ρ := Array Int) (t, fresh))
    else
      match ← ((do
        if !(SudoRt.SEq.beq t idx) then
          do
            let x ← SudoRt.atL avail t
            let mb := SudoRt.appendL fresh x
            let fresh := mb.1
            let u : Unit := ()
            let _ := u
            pure (SudoRt.Flow.cont (ρ := Array Int) fresh)
        else
          pure (SudoRt.Flow.cont (ρ := Array Int) fresh)) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (t, fs))
      | .cont fs => do
          if t == toV then
            pure (SudoRt.Flow.brk (ρ := Array Int) (t, fs))
          else do
            let t' ← SudoRt.addI t (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (t', fs))

private theorem phiEraseFinish (t toV : Nat) (st : Array Int) (_hle : t ≤ toV)
    (hfits : FitsLen (t + 1)) :
    (if ((t : Int) == (toV : Int)) = true then
        Except.ok (SudoRt.Flow.brk (ρ := Array Int) ((t : Int), st))
      else do
        let t' ← SudoRt.addI (t : Int) (1 : Int)
        Except.ok (SudoRt.Flow.cont (ρ := Array Int) (t', st))) =
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

theorem phiEraseStep_hit (xs : List Nat) (idx t : Nat)
    (_hidx : idx < xs.length) (ht : t < xs.length) (hfits : FitsLen xs.length) :
    phiEraseStep (embed xs) (Int.ofNat idx) (Int.ofNat (xs.length - 1))
        (Int.ofNat t, embed (takeSkip xs idx t)) =
      if t = xs.length - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat t, embed (takeSkip xs idx (t + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (t + 1), embed (takeSkip xs idx (t + 1)))) := by
  have hle : t ≤ xs.length - 1 := by omega
  have hstep : FitsLen (t + 1) := FitsLen.of_le hfits (by omega)
  have hnext := takeSkip_succ xs idx t ht
  unfold phiEraseStep
  dsimp
  have hngt : ¬ (t : Int) > ((xs.length - 1 : Nat) : Int) := by
    simpa [ofNat_eq_natCast] using ofNat_not_gt hle
  rw [if_neg hngt]
  have htail := phiEraseFinish t (xs.length - 1) (embed (takeSkip xs idx (t + 1))) hle hstep
  by_cases heq : t = idx
  · rw [beq_ofNat, heq]
    simp only [decide_True, Bool.not_true, Bool.false_eq_true, ite_false, pure_eq_ok, ok_bind]
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

/-- The inner copy loop lands on `List.eraseIdx`. -/
theorem phiErase_breaks {α : Type} (xs : List Nat) (idx : Nat) (hidx : idx < xs.length)
    (hfits : FitsLen xs.length)
    (after : Int × Array Int → Except SudoRt.Trap α)
    (onRet : Array Int → Except SudoRt.Trap α) :
    SudoRt.runLoopOn (ρ := Array Int)
      ((0 : Int), embed (takeSkip xs idx 0))
      (fuelRange (0 : Int) (Int.ofNat (xs.length - 1)))
      (phiEraseStep (embed xs) (Int.ofNat idx) (Int.ofNat (xs.length - 1)))
      after onRet =
      after (Int.ofNat (xs.length - 1), embed (xs.eraseIdx idx)) := by
  apply chain_loop (f := fun i => embed (takeSkip xs idx i)) (fromN := 0)
    (toN := xs.length - 1) (hle := Nat.zero_le _)
    (goal := after (Int.ofNat (xs.length - 1), embed (xs.eraseIdx idx)))
  · intro i _ hi
    have hi' : i < xs.length := by omega
    have hs := phiEraseStep_hit xs idx i hidx hi' hfits
    simp only [ofNat_eq_natCast] at hs ⊢
    simp only [hs]
  · rw [Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.zero_lt_of_lt hidx)),
      takeSkip_erase xs idx hidx]

/-! ## Picks of `applyDigits`

  `applyDigits avail ds` is the picks followed by the leftover, so the picks
  alone (what the emitted loop accumulates in `out`) are `take ds.length`. -/

/-- The chosen elements of `applyDigits`, i.e. what `phi_chunk` accumulates. -/
def picksOf (avail ds : List Nat) : List Nat := (applyDigits avail ds).take ds.length

/-- Every digit of `ds` stays below the current leftover length. -/
def ValidDigits (avail ds : List Nat) : Prop :=
  ∀ i, i < ds.length → ds[i]?.getD 0 < (leftoverFrom avail (ds.take i)).length

theorem validDigits_head (avail : List Nat) (d : Nat) (ds : List Nat)
    (h : ValidDigits avail (d :: ds)) : d < avail.length := by
  have h1 := h 0 (Nat.zero_lt_succ _)
  simpa [List.getElem?_cons_zero, List.take_zero, leftoverFrom_nil] using h1

theorem validDigits_erase (avail : List Nat) (d : Nat) (ds : List Nat)
    (h : ValidDigits avail (d :: ds)) (hd : d < avail.length) :
    ValidDigits (avail.eraseIdx d) ds := by
  intro k hk
  have h1 := h (k + 1) (Nat.succ_lt_succ hk)
  simpa [List.getElem?_cons_succ, List.take_succ_cons, leftoverFrom_cons, hd] using h1

theorem validDigits_digitsOf_take (rank i : Nat) (hrank : rank < factorial 52) (hi : i ≤ 52) :
    ValidDigits (List.range 52) ((digitsOf rank).take i) := by
  intro k hk
  rw [List.length_take] at hk
  have hk' : k < i := by omega
  have hk52 : k < 52 := by omega
  have htake : ((digitsOf rank).take i).take k = (digitsOf rank).take k := by
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hk')]
  have hget : ((digitsOf rank).take i)[k]?.getD 0 = (digitsOf rank)[k]?.getD 0 := by
    rw [List.getElem?_take, if_pos hk']
  rw [htake, hget, ← phiLeftover_def, phiLeftover_length rank hrank k (by omega)]
  exact digitsOf_getD_lt rank k hrank hk52

theorem applyDigits_nil (avail : List Nat) : applyDigits avail [] = avail := by
  cases avail <;> rfl

theorem applyDigits_singleton (avail : List Nat) (d : Nat) (hd : d < avail.length) :
    applyDigits avail [d] = avail[d] :: avail.eraseIdx d := by
  cases avail with
  | nil => simp at hd
  | cons a rest =>
    rw [List.length_cons] at hd
    simp only [applyDigits, List.length_cons, dif_pos hd, applyDigits_nil]

theorem picksOf_cons (avail : List Nat) (d : Nat) (ds : List Nat) (hd : d < avail.length) :
    picksOf avail (d :: ds) = avail[d] :: picksOf (avail.eraseIdx d) ds := by
  cases avail with
  | nil => simp at hd
  | cons a rest =>
    rw [List.length_cons] at hd
    unfold picksOf
    simp only [applyDigits, List.length_cons, List.take_succ_cons, dif_pos hd]

theorem picksOf_append (avail ds₁ ds₂ : List Nat) (h : ValidDigits avail ds₁) :
    picksOf avail (ds₁ ++ ds₂) = picksOf avail ds₁ ++ picksOf (leftoverFrom avail ds₁) ds₂ := by
  induction ds₁ generalizing avail with
  | nil => cases avail <;> rfl
  | cons d ds ih =>
    have hd := validDigits_head avail d ds h
    have hv := validDigits_erase avail d ds h hd
    rw [List.cons_append, picksOf_cons avail d (ds ++ ds₂) hd, ih (avail.eraseIdx d) hv,
      picksOf_cons avail d ds hd, leftoverFrom_cons, if_pos hd]
    rfl

theorem applyDigits_length (avail ds : List Nat) (h : ValidDigits avail ds)
    (hlen : ds.length ≤ avail.length) :
    (applyDigits avail ds).length = avail.length := by
  induction ds generalizing avail with
  | nil => cases avail <;> rfl
  | cons d ds ih =>
    cases avail with
    | nil => rfl
    | cons a rest =>
      have hd : d < (a :: rest).length := validDigits_head (a :: rest) d ds h
      have hv : ValidDigits ((a :: rest).eraseIdx d) ds :=
        validDigits_erase (a :: rest) d ds h hd
      have hlen' : ds.length ≤ ((a :: rest).eraseIdx d).length := by
        rw [List.length_cons] at hlen
        rw [List.length_eraseIdx_of_lt hd]; omega
      have hdl : d < rest.length + 1 := by simpa only [List.length_cons] using hd
      simp only [applyDigits, List.length_cons]
      rw [dif_pos hdl]
      rw [List.length_cons, ih ((a :: rest).eraseIdx d) hv hlen',
        List.length_eraseIdx_of_lt hd]
      simp only [List.length_cons]
      omega

theorem picksOf_eq_applyDigits (avail ds : List Nat) (h : ValidDigits avail ds)
    (hlen : ds.length = avail.length) :
    picksOf avail ds = applyDigits avail ds := by
  have hl : (applyDigits avail ds).length = ds.length := by
    rw [applyDigits_length avail ds h (Nat.le_of_eq hlen)]
    exact hlen.symm
  unfold picksOf
  rw [← hl, List.take_length]

/-! ## Outer `phi_chunk` loop -/

abbrev PhiSt := Int × (Array Int × (Megadreifach.BigInt × Array Int))

private theorem fits52 : FitsLen 52 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits51 : FitsLen 51 := FitsLen.of_le fits52 (by decide)

private theorem sudoAssertEq_ofNat (n : Nat) (line : Nat) :
    SudoRt.sudoAssertEq (Int.ofNat n) (Int.ofNat n) line = .ok () := by
  have hb : SudoRt.SEq.beq (Int.ofNat n) (Int.ofNat n) = true := by simp [sEq_int]
  unfold SudoRt.sudoAssertEq
  rw [hb]
  rfl

/-- Generated outer closure of `phi_chunk`, in the shape the emitter leaves it. -/
def phiChunkStep (σ : PhiSt) :
    Except SudoRt.Trap (SudoRt.Flow PhiSt (Array Int)) :=
  let i := σ.1
  let out := σ.2.1
  let rem := σ.2.2.1
  let avail := σ.2.2.2
  do
    if i > (51 : Int) then
      pure (SudoRt.Flow.brk (ρ := Array Int) (i, (out, rem, avail)))
    else
      match ← ((do
        let d ← SudoRt.subI (51 : Int) i
        if (SudoRt.SEq.beq d (0 : Int)) then
          do
            let x ← SudoRt.atL avail (0 : Int)
            let out := (SudoRt.appendL out x).1
            let u : Unit := ()
            let _ := u
            pure (SudoRt.Flow.cont (ρ := Array Int) (out, rem, avail))
        else
          do
            let ⟨rem, idx⟩ ← Megadreifach.peel_leading rem d
            let ok ← (if (decide (idx ≥ (0 : Int))) then
                (pure (decide (idx < SudoRt.listLen avail))) else pure false)
            let _ ← SudoRt.sudoAssert ok 508
            let x ← SudoRt.atL avail idx
            let out := (SudoRt.appendL out x).1
            let u : Unit := ()
            let _ := u
            let fresh := (#[] : Array Int)
            let toV ← SudoRt.subI (SudoRt.listLen avail) (1 : Int)
            let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
            let _out ← (SudoRt.runLoopOn (ρ := Array Int) ((0 : Int), fresh) fuel
              (phiEraseStep avail idx toV)
              (fun σ =>
                let fresh := σ.2
                let avail := fresh
                pure (SudoRt.Flow.cont (ρ := Array Int) (out, rem, avail)))
              (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r)))
            pure _out) : Except SudoRt.Trap
              (SudoRt.Flow (Array Int × (Megadreifach.BigInt × Array Int)) (Array Int))) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
      | .cont fs => do
          if i == (51 : Int) then
            pure (SudoRt.Flow.brk (ρ := Array Int) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Array Int) (i', fs))

/-- Loop state after `i` steps: picks, running remainder, remaining cards. -/
def phiState (rank i : Nat) : Array Int × (Megadreifach.BigInt × Array Int) :=
  if i ≤ 51 then
    (embed (picksOf (List.range 52) ((digitsOf rank).take i)),
     bigOf (natLimbs (rank % factorial (52 - i))),
     embed (leftoverFrom (List.range 52) ((digitsOf rank).take i)))
  else
    (embed (phiUnrank rank),
     bigOf (natLimbs (rank % factorial 1)),
     embed (leftoverFrom (List.range 52) ((digitsOf rank).take 51)))

theorem phiState_of_le (rank i : Nat) (hi : i ≤ 51) :
    phiState rank i =
      (embed (picksOf (List.range 52) ((digitsOf rank).take i)),
       bigOf (natLimbs (rank % factorial (52 - i))),
       embed (leftoverFrom (List.range 52) ((digitsOf rank).take i))) := by
  simp [phiState, hi]

theorem phiState_52 (rank : Nat) :
    phiState rank 52 =
      (embed (phiUnrank rank),
       bigOf (natLimbs (rank % factorial 1)),
       embed (leftoverFrom (List.range 52) ((digitsOf rank).take 51))) := by
  simp [phiState]

/-! ## One outer step -/

/-- The digit at the last position is zero. -/
theorem digitAt_51 (rank : Nat) : digitAt rank 51 = 0 := by
  unfold digitAt
  rw [show 52 - 51 = 1 from rfl, show 51 - 51 = 0 from rfl,
    show factorial 1 = 1 from rfl, show factorial 0 = 1 from rfl,
    Nat.mod_one, Nat.div_one]

/-- The running remainder drops one factorial. -/
theorem phiRem_succ_eq (rank i : Nat) (hi : i ≤ 51) :
    rank % factorial (52 - i) % factorial (51 - i) = rank % factorial (51 - i) := by
  have h : factorial (51 - i) ∣ factorial (52 - i) := by
    rw [show 52 - i = (51 - i) + 1 from by omega]
    exact factorial_dvd_succ (51 - i)
  exact Nat.mod_mod_of_dvd _ h

/-- Picks after one more digit. -/
theorem picksOf_take_succ (rank i : Nat) (hrank : rank < factorial 52) (hi : i < 52) :
    picksOf (List.range 52) ((digitsOf rank).take (i + 1)) =
      picksOf (List.range 52) ((digitsOf rank).take i) ++
        [(phiLeftover rank i)[(digitsOf rank)[i]'(by rw [digitsOf_length]; exact hi)]'
          (phiDigit_lt_leftover rank i hrank hi)] := by
  have hvalid := validDigits_digitsOf_take rank i hrank (by omega)
  have hd : (digitsOf rank)[i] < (phiLeftover rank i).length :=
    phiDigit_lt_leftover rank i hrank hi
  have hlt : (digitsOf rank)[i] <
      (leftoverFrom (List.range 52) ((digitsOf rank).take i)).length := by
    simpa [phiLeftover_def] using hd
  rw [take_succ_get (digitsOf rank) i (by rw [digitsOf_length]; exact hi)]
  rw [picksOf_append (List.range 52) ((digitsOf rank).take i) [(digitsOf rank)[i]] hvalid]
  congr 1
  rw [picksOf_cons (leftoverFrom (List.range 52) ((digitsOf rank).take i))
    ((digitsOf rank)[i]) [] hlt]
  simp [picksOf, applyDigits_nil]

/-- `picksOf` on the full digit list is `phiUnrank`. -/
theorem picksOf_full (rank : Nat) (hrank : rank < factorial 52) :
    picksOf (List.range 52) (digitsOf rank) = phiUnrank rank := by
  rw [show phiUnrank rank = applyDigits (List.range 52) (digitsOf rank) from rfl]
  exact picksOf_eq_applyDigits (List.range 52) (digitsOf rank)
    (validDigits_digitsOf_take rank 52 hrank (Nat.le_refl _))
    (by rw [digitsOf_length, List.length_range])

/-- Close the outer continuation when `i < 51` (no break). -/
private theorem phiOuterFinish (i : Nat) (hi : i < 51)
    (st : Array Int × (Megadreifach.BigInt × Array Int)) :
    (if (Int.ofNat i == Int.ofNat 51) = true then
        Except.ok (SudoRt.Flow.brk (ρ := Array Int) (Int.ofNat i, st))
      else do
        let i' ← SudoRt.addI (Int.ofNat i) (1 : Int)
        Except.ok (SudoRt.Flow.cont (ρ := Array Int) (i', st))) =
      .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), st)) := by
  have hne : ¬ ((Int.ofNat i == Int.ofNat 51) = true) := by
    intro h
    have h' : Int.ofNat i = Int.ofNat 51 := (beq_int_iff _ _).mp h
    exact absurd (Int.ofNat.inj h') (by omega)
  have hadd := addI_ofNat_one i (FitsLen.of_le fits52 (by omega))
  rw [if_neg hne, hadd, ok_bind]

/-- One step of the outer loop, `i < 51`. -/
theorem phiChunkStep_lt (rank : Nat) (hrank : rank < factorial 52) (i : Nat) (hi : i < 51) :
    phiChunkStep (Int.ofNat i, phiState rank i) =
      .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), phiState rank (i + 1))) := by
  have hi52 : i < 52 := by omega
  have hile : i ≤ 51 := by omega
  have hdgt : (digitsOf rank)[i] < (phiLeftover rank i).length :=
    phiDigit_lt_leftover rank i hrank hi52
  have hlen : (phiLeftover rank i).length = 52 - i :=
    phiLeftover_length rank hrank i (by omega)
  have hfits : FitsLen (phiLeftover rank i).length := by
    rw [hlen]; exact FitsLen.of_le fits52 (by omega)
  have hfac : (52 - i) * factorial (51 - i) = factorial (52 - i) := by
    rw [show 52 - i = (51 - i) + 1 from by omega, factorial_succ]
  have hq : (rank % factorial (52 - i)) / factorial (51 - i) < limbBase := by
    have hlt : rank % factorial (52 - i) < (52 - i) * factorial (51 - i) := by
      rw [hfac]; exact Nat.mod_lt _ (factorial_pos _)
    have hq52 : (rank % factorial (52 - i)) / factorial (51 - i) < 52 - i :=
      (Nat.div_lt_iff_lt_mul (factorial_pos (51 - i))).mpr hlt
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hq52 (by omega))
      (by decide : 52 < limbBase)
  have hidx : (rank % factorial (52 - i)) / factorial (51 - i) = (digitsOf rank)[i] := by
    show digitAt rank i = (digitsOf rank)[i]
    exact (digitsOf_getElem rank i hrank hi52).symm
  have hrem : (rank % factorial (52 - i)) % factorial (51 - i) =
      rank % factorial (52 - (i + 1)) := by
    rw [show 52 - (i + 1) = 51 - i from by omega]
    exact phiRem_succ_eq rank i hile
  have hbeq : SudoRt.SEq.beq (Int.ofNat (51 - i)) (0 : Int) = false := by
    rw [sEq_int, decide_eq_false_iff_not, ofNat_eq_zero_iff]
    omega
  rw [phiState_of_le rank i hile]
  unfold phiChunkStep
  dsimp only
  rw [show (51 : Int) = Int.ofNat 51 from rfl]
  rw [if_neg (ofNat_not_gt hile)]
  rw [subI_ofNat 51 i fits51 hile, ok_bind]
  rw [if_neg (by rw [hbeq]; decide)]
  rw [ofNat_eq_natCast (51 - i)]
  rw [peel_leading_51 (rank % factorial (52 - i)) (51 - i) (by omega) hq, ok_bind]
  dsimp only
  rw [hidx, hrem, ← phiLeftover_def]
  have hge : decide (Int.ofNat ((digitsOf rank)[i]) ≥ (0 : Int)) = true :=
    decide_eq_true (Int.ofNat_zero_le _)
  have hlt : decide (Int.ofNat ((digitsOf rank)[i]) <
      SudoRt.listLen (embed (phiLeftover rank i))) = true := by
    rw [listLen_embed, decide_eq_true_eq, ofNat_lt_iff]
    exact hdgt
  rw [if_pos hge, hlt, pure_eq_ok, ok_bind, sudoAssert_true, ok_bind]
  rw [atL_embed (phiLeftover rank i) ((digitsOf rank)[i]) hdgt, ok_bind]
  rw [appendL_spec]
  dsimp only
  rw [push_embed (picksOf (List.range 52) ((digitsOf rank).take i))
    ((phiLeftover rank i)[(digitsOf rank)[i]])]
  rw [show (#[] : Array Int) =
      embed (takeSkip (phiLeftover rank i) ((digitsOf rank)[i]) 0) from by
    rw [takeSkip_zero]; exact embed_nil.symm]
  rw [listLen_embed, subI_ofNat_one (phiLeftover rank i).length
    (by rw [hlen]; omega) hfits, ok_bind]
  rw [fuelRange_eq]
  rw [phiErase_breaks (phiLeftover rank i) ((digitsOf rank)[i]) hdgt hfits]
  rw [← phiLeftover_succ rank i hrank hi52]
  dsimp only
  simp only [except_bind_pure, pure_eq_ok, ok_bind]
  rw [phiOuterFinish i hi]
  rw [phiState_of_le rank (i + 1) (by omega)]
  rw [picksOf_take_succ rank i hrank hi52]
  rfl

/-- Close the outer continuation at `i = 51` (break). -/
private theorem phiOuterFinish51
    (st : Array Int × (Megadreifach.BigInt × Array Int)) :
    (if (Int.ofNat 51 == Int.ofNat 51) = true then
        Except.ok (SudoRt.Flow.brk (ρ := Array Int) (Int.ofNat 51, st))
      else do
        let i' ← SudoRt.addI (Int.ofNat 51) (1 : Int)
        Except.ok (SudoRt.Flow.cont (ρ := Array Int) (i', st))) =
      .ok (SudoRt.Flow.brk (Int.ofNat 51, st)) := by
  rw [if_pos (by rw [beq_int_iff])]

/-- One step of the outer loop at `i = 51` (stores the full picks, breaks). -/
theorem phiChunkStep_51 (rank : Nat) (hrank : rank < factorial 52) :
    phiChunkStep (Int.ofNat 51, phiState rank 51) =
      .ok (SudoRt.Flow.brk (Int.ofNat 51, phiState rank 52)) := by
  have hlen : (phiLeftover rank 51).length = 1 :=
    phiLeftover_length rank hrank 51 (by omega)
  have hdgt : 0 < (phiLeftover rank 51).length := by rw [hlen]; decide
  have hdigit : (digitsOf rank)[51]'(by rw [digitsOf_length]; decide) = 0 := by
    rw [digitsOf_getElem rank 51 hrank (by decide)]
    exact digitAt_51 rank
  have hcard : (phiLeftover rank 51)[(digitsOf rank)[51]'(by rw [digitsOf_length]; decide)]'
        (phiDigit_lt_leftover rank 51 hrank (by decide)) = (phiLeftover rank 51)[0]'hdgt := by
    have hd' : (phiLeftover rank 51)[(digitsOf rank)[51]'(by rw [digitsOf_length]; decide)]? =
        (phiLeftover rank 51)[0]? := by rw [hdigit]
    rw [List.getElem?_eq_getElem (phiDigit_lt_leftover rank 51 hrank (by decide)),
        List.getElem?_eq_getElem hdgt] at hd'
    exact Option.some.inj hd'
  have h1 : (digitsOf rank).take (51 + 1) = digitsOf rank := by
    rw [show (51 : Nat) + 1 = 52 from rfl, ← digitsOf_length, List.take_length]
  have hout : embed (picksOf (List.range 52) ((digitsOf rank).take 51) ++
        [(phiLeftover rank 51)[0]'hdgt]) = embed (phiUnrank rank) := by
    rw [← hcard]
    rw [← picksOf_take_succ rank 51 hrank (by decide)]
    rw [h1, picksOf_full rank hrank]
  rw [phiState_of_le rank 51 (by omega)]
  unfold phiChunkStep
  dsimp only
  rw [← phiLeftover_def]
  rw [show (51 : Int) = Int.ofNat 51 from rfl]
  rw [if_neg (ofNat_not_gt (Nat.le_refl 51))]
  rw [subI_ofNat 51 51 fits51 (Nat.le_refl 51), ok_bind]
  rw [if_pos (by rw [sEq_int, decide_eq_true_eq]; rfl)]
  rw [show (0 : Int) = Int.ofNat 0 from rfl]
  rw [atL_embed (phiLeftover rank 51) 0 hdgt, ok_bind]
  rw [appendL_spec]
  dsimp only
  rw [push_embed (picksOf (List.range 52) ((digitsOf rank).take 51)) ((phiLeftover rank 51)[0])]
  dsimp only
  simp only [except_bind_pure, pure_eq_ok, ok_bind]
  rw [phiOuterFinish51]
  rw [phiState_52 rank, hout]
  rfl

/-! ## Refinement -/

/-- `phi_chunk` refines `phiUnrank` on the 28-byte pad block. -/
theorem phi_chunk_refines (bs : List Nat) (h : PhiChunkWf bs) :
    Megadreifach.phi_chunk (embed bs) = .ok (embed (phiUnrank (fromBE bs))) := by
  have hrank := phiChunk_rank_lt bs h
  have hinit : ((0 : Int), (#[] : Array Int), bigOf (natLimbs (fromBE bs)),
      embed (List.range 52)) = (Int.ofNat 0, phiState (fromBE bs) 0) := by
    rw [phiState_of_le (fromBE bs) 0 (by omega)]
    simp only [List.take_zero, List.length_nil, leftoverFrom_nil, picksOf,
      applyDigits_nil, embed_nil, Nat.sub_zero, Nat.mod_eq_of_lt hrank]
    rfl
  unfold Megadreifach.phi_chunk
  rw [listLen_embed, h.len, show Megadreifach.pad_block = Int.ofNat 28 from rfl,
    sudoAssertEq_ofNat 28 498, ok_bind]
  rw [big_from_be_pad bs (phiChunk_bePadWf bs h), ok_bind]
  rw [show (52 : Int) = Int.ofNat 52 from rfl, range_list_refines 52 (by decide) fits52, ok_bind]
  dsimp only
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := phiChunkStep)
    intro σ
    unfold phiChunkStep
    dsimp
    rfl
  · rw [hinit]
    rw [show (0 : Int) = Int.ofNat 0 from rfl,
      show (51 : Int) = Int.ofNat 51 from rfl, fuelRange_eq]
    apply chain_loop (f := phiState (fromBE bs)) (fromN := 0) (toN := 51)
      (hle := by decide) (goal := .ok (embed (phiUnrank (fromBE bs))))
    · intro i _ hhi
      rcases (by omega : i < 51 ∨ i = 51) with hlt | heq
      · rw [if_neg (by omega)]
        exact phiChunkStep_lt (fromBE bs) hrank i hlt
      · subst heq
        rw [if_pos rfl]
        exact phiChunkStep_51 (fromBE bs) hrank
    · rw [phiState_52 (fromBE bs)]
      rfl

/-- Same refinement on a nonnegative `Array Int` in `WellFormedPhiChunk`. -/
theorem phi_chunk_refines_array (a : Array Int) (h : WellFormedPhiChunk a) :
    Megadreifach.phi_chunk a = .ok (embed (phiUnrank (fromBE (decode a)))) := by
  have hr := phi_chunk_refines (decode a) (phiChunk_decode a h)
  simpa [embed_decode a h.nn] using hr

end MegaDreifach.Link2
