/-
  LINK 2. `Generated.pack_ori3` / `pack_ori2` refine algebraic `packOri3` /
  `packOri2` on orientation lists.

  Corner orientations have length 20 and entries `< 3`. Edge orientations have
  length 30 and entries `< 2`. The emitted Horner loop (`n = n * r + d`)
  stays below `3^19` / `2^29`, so every limb product fits in an i64 and the
  bigint has at most two base-10^9 limbs.

  Algebraic Link 2 only. Not `v_Hash`. Not emitter soundness.
  Not collision resistance. `phi_chunk` stays open (it builds `51!`).
-/
import Megadreifach
import MegaDreifach.Rank
import MegaDreifach.Link2.Be

namespace MegaDreifach.Link2

/-! ## Horner form of mixed-radix encode -/

/-- Left-to-right Horner: `acc = 0; for d in ds: acc = acc * r + d`. -/
def hornerAcc (r acc : Nat) : List Nat → Nat
  | [] => acc
  | d :: ds => hornerAcc r (acc * r + d) ds

theorem hornerAcc_nil (r acc : Nat) : hornerAcc r acc [] = acc := rfl

theorem hornerAcc_cons (r acc d : Nat) (ds : List Nat) :
    hornerAcc r acc (d :: ds) = hornerAcc r (acc * r + d) ds := rfl

theorem hornerAcc_shift (r acc : Nat) :
    ∀ ds, hornerAcc r acc ds = acc * r ^ ds.length + hornerAcc r 0 ds
  | [] => by simp [hornerAcc, Nat.pow_zero]
  | d :: ds => by
    simp only [hornerAcc, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [hornerAcc_shift r (acc * r + d) ds, hornerAcc_shift r d ds]
    have hpow : r * r ^ ds.length = r ^ (ds.length + 1) := by
      rw [Nat.mul_comm, ← Nat.pow_succ]
    calc
      (acc * r + d) * r ^ ds.length + hornerAcc r 0 ds
          = (acc * r) * r ^ ds.length + d * r ^ ds.length + hornerAcc r 0 ds := by
            rw [Nat.add_mul]
      _ = acc * (r * r ^ ds.length) + d * r ^ ds.length + hornerAcc r 0 ds := by
            rw [Nat.mul_assoc]
      _ = acc * r ^ (ds.length + 1) + d * r ^ ds.length + hornerAcc r 0 ds := by
            rw [hpow]
      _ = acc * r ^ (ds.length + 1) + (d * r ^ ds.length + hornerAcc r 0 ds) := by
            rw [Nat.add_assoc]

theorem hornerAcc_mix (r : Nat) (ds : List Nat) :
    hornerAcc r 0 ds = mixEncode (List.replicate ds.length r) ds := by
  induction ds with
  | nil => simp [hornerAcc, mixEncode, List.replicate]
  | cons d ds ih =>
    rw [hornerAcc_cons, Nat.zero_mul, Nat.zero_add, hornerAcc_shift, ih]
    rw [List.length_cons, List.replicate_succ, mixEncode_cons, product_replicate]

theorem hornerAcc_snoc (r acc : Nat) (xs : List Nat) (d : Nat) :
    hornerAcc r acc (xs ++ [d]) = hornerAcc r acc xs * r + d := by
  induction xs generalizing acc with
  | nil => simp [hornerAcc]
  | cons x xs ih => simp [hornerAcc, ih]

theorem take_succ_get (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    xs.take (i + 1) = xs.take i ++ [xs[i]] := by
  induction xs generalizing i with
  | nil => cases hi
  | cons x xs ih =>
    cases i with
    | zero => simp [List.take]
    | succ i =>
      simp only [List.take_succ_cons, List.getElem_cons_succ]
      exact congrArg (fun t => x :: t) (ih i (Nat.lt_of_succ_lt_succ hi))

/-- Value of the Horner accumulator after `i` digits. -/
def oriAcc (r : Nat) (xs : List Nat) (i : Nat) : Nat :=
  hornerAcc r 0 (xs.take i)

theorem oriAcc_zero (r : Nat) (xs : List Nat) : oriAcc r xs 0 = 0 := by
  simp [oriAcc, List.take, hornerAcc]

theorem oriAcc_succ (r : Nat) (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    oriAcc r xs (i + 1) = oriAcc r xs i * r + xs[i] := by
  unfold oriAcc
  rw [take_succ_get xs i hi, hornerAcc_snoc]

theorem hornerAcc_lt {r : Nat} (ds : List Nat)
    (hb : ∀ d ∈ ds, d < r) : hornerAcc r 0 ds < r ^ ds.length := by
  induction ds with
  | nil =>
    simp [hornerAcc]
  | cons d ds ih =>
    have hd : d < r := hb d (List.mem_cons_self _ _)
    have hds : ∀ x ∈ ds, x < r := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have ih' := ih hds
    rw [hornerAcc_cons, hornerAcc_shift]
    have hlt := mul_add_lt_mul d (hornerAcc r 0 ds) r (r ^ ds.length) hd ih'
    simpa [Nat.pow_succ, Nat.mul_comm] using hlt

theorem oriAcc_lt {r : Nat} (xs : List Nat)
    (hb : ∀ o ∈ xs, o < r) (i : Nat) (hi : i ≤ xs.length) :
    oriAcc r xs i < r ^ i := by
  have hlen : (xs.take i).length = i := by
    simp [List.length_take, Nat.min_eq_left hi]
  have hmem : ∀ d ∈ xs.take i, d < r := fun d hd => hb d (List.mem_of_mem_take hd)
  simpa [oriAcc, hlen] using hornerAcc_lt (xs.take i) hmem

theorem packOri2_horner (eo : List Nat) (hlen : 29 ≤ eo.length) :
    packOri2 eo = hornerAcc 2 0 (eo.take 29) := by
  have htake : (eo.take 29).length = 29 := by
    simp [List.length_take, Nat.min_eq_left hlen]
  unfold packOri2
  rw [hornerAcc_mix, htake]

theorem packOri3_horner (co : List Nat) (hlen : 19 ≤ co.length) :
    packOri3 co = hornerAcc 3 0 (co.take 19) := by
  have htake : (co.take 19).length = 19 := by
    simp [List.length_take, Nat.min_eq_left hlen]
  unfold packOri3
  rw [hornerAcc_mix, htake]

theorem oriAcc_pack2 (eo : List Nat) (hlen : 29 ≤ eo.length) :
    oriAcc 2 eo 29 = packOri2 eo := by
  rw [oriAcc, packOri2_horner eo hlen]

theorem oriAcc_pack3 (co : List Nat) (hlen : 19 ≤ co.length) :
    oriAcc 3 co 19 = packOri3 co := by
  rw [oriAcc, packOri3_horner co hlen]

/-! ## Orientation domain -/

/-- Trap-free domain for `Generated.pack_ori2`.

    Length 30 is the edge-orientation width. Entries `< 2` keep the Horner
    value below `2^29`, inside one limb, with every index and product inside
    an i64. -/
structure Ori2Wf (eo : List Nat) : Prop where
  len : eo.length = 30
  bound : ∀ o ∈ eo, o < 2

/-- Trap-free domain for `Generated.pack_ori3`.

    Length 20 is the corner-orientation width. Entries `< 3` keep the Horner
    value below `3^19`, inside two limbs. -/
structure Ori3Wf (co : List Nat) : Prop where
  len : co.length = 20
  bound : ∀ o ∈ co, o < 3

structure WellFormedOri2 (a : Array Int) : Prop where
  len : a.size = 30
  nn : Nonneg a
  bound : ∀ x ∈ decode a, x < 2

structure WellFormedOri3 (a : Array Int) : Prop where
  len : a.size = 20
  nn : Nonneg a
  bound : ∀ x ∈ decode a, x < 3

theorem ori2Wf_embed (eo : List Nat) (h : Ori2Wf eo) : WellFormedOri2 (embed eo) where
  len := by simp [size_embed, h.len]
  nn := nonneg_embed eo
  bound := by rw [decode_embed]; exact h.bound

theorem ori2Wf_decode (a : Array Int) (h : WellFormedOri2 a) : Ori2Wf (decode a) where
  len := by simp [decode, h.len]
  bound := h.bound

theorem ori3Wf_embed (co : List Nat) (h : Ori3Wf co) : WellFormedOri3 (embed co) where
  len := by simp [size_embed, h.len]
  nn := nonneg_embed co
  bound := by rw [decode_embed]; exact h.bound

theorem ori3Wf_decode (a : Array Int) (h : WellFormedOri3 a) : Ori3Wf (decode a) where
  len := by simp [decode, h.len]
  bound := h.bound

/-! ## Small bigint (at most two limbs) -/

def bigNat (v : Nat) : Megadreifach.BigInt := bigOf (limbsOfNat v)

theorem two_pow29_lt_limb : 2 ^ 29 < limbBase := by decide

theorem two_pow29_fits : FitsLen (2 ^ 29) := by
  unfold FitsLen i64MaxNat
  decide

theorem three_pow18_lt_limb : 3 ^ 18 < limbBase := by decide

theorem three_pow19_lt_twoLimb : 3 ^ 19 < 2 * limbBase := by decide

theorem three_pow19_fits : FitsLen (3 ^ 19) := by
  unfold FitsLen i64MaxNat
  decide

theorem limb_sq_fits : limbBase ^ 2 ≤ i64MaxNat := by
  unfold i64MaxNat limbBase
  decide

theorem fits_lt_pow2_29 {n : Nat} (h : n ≤ 2 ^ 29) : FitsLen n :=
  FitsLen.of_le two_pow29_fits h

theorem fits_lt_pow3_19 {n : Nat} (h : n ≤ 3 ^ 19) : FitsLen n :=
  FitsLen.of_le three_pow19_fits h

theorem bigNat_zero : bigNat 0 = bigOf [] := by
  simp [bigNat, limbsOfNat]

theorem bigNat_limb (v : Nat) (hv : v < limbBase) (h0 : v ≠ 0) :
    bigNat v = bigOf [v] := by
  have hq : v / limbBase = 0 := Nat.div_eq_of_lt hv
  simp [bigNat, limbsOfNat, h0, hq, Nat.mod_eq_of_lt hv]

theorem bigNat_two (v : Nat) (hlo : limbBase ≤ v) (hhi : v < limbBase ^ 2) :
    bigNat v = bigOf [v % limbBase, v / limbBase] := by
  have hv0 : v ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le limbBase_pos hlo)
  have hq0 : v / limbBase ≠ 0 := by
    intro hz
    exact Nat.not_le_of_gt (lt_of_div_eq_zero limbBase_pos hz) hlo
  have hq2 : (v / limbBase) / limbBase = 0 := by
    rw [limbBase_pow2] at hhi
    exact Nat.div_eq_of_lt (div_lt_of_lt_mul limbBase_pos hhi)
  have hmod : (v / limbBase) % limbBase = v / limbBase :=
    Nat.mod_eq_of_lt (lt_of_div_eq_zero limbBase_pos hq2)
  simp [bigNat, limbsOfNat, hv0, hq0, hq2, hmod]

theorem dropTrail_two (a b : Nat) :
    dropTrail [a, b] =
      if b = 0 then (if a = 0 then [] else [a]) else [a, b] := by
  by_cases hb : b = 0 <;> by_cases ha : a = 0 <;> simp [dropTrail, hb, ha]

theorem limbs_prod (v : Nat) (hv : 0 < v) (hlt : v < limbBase ^ 2) :
    dropTrail [v % limbBase, v / limbBase] = limbsOfNat v := by
  have hq2 : (v / limbBase) / limbBase = 0 := by
    rw [limbBase_pow2] at hlt
    exact Nat.div_eq_of_lt (div_lt_of_lt_mul limbBase_pos hlt)
  have hmodHi : (v / limbBase) % limbBase = v / limbBase :=
    Nat.mod_eq_of_lt (lt_of_div_eq_zero limbBase_pos hq2)
  by_cases hhi : v / limbBase = 0
  · have hlt' : v < limbBase := lt_of_div_eq_zero limbBase_pos hhi
    have hlo : v % limbBase = v := Nat.mod_eq_of_lt hlt'
    have hv0 : v ≠ 0 := Nat.ne_of_gt hv
    simp [dropTrail, hhi, hlo, hv0, limbsOfNat, hhi]
  · simp [dropTrail, hhi, limbsOfNat, Nat.ne_of_gt hv, hhi, hq2, hmodHi]

/-! ## `big_mul` on a zero or one-limb left factor -/

private def mulIStep (a b : Megadreifach.BigInt) (toV : Int) (σ : Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int) Megadreifach.BigInt) :=
  if σ.fst > toV then
    pure (SudoRt.Flow.brk (σ.fst, σ.snd))
  else do
    let lift ←
      (do
        let toJ ← SudoRt.subI (SudoRt.listLen b.sudo_6BigInt_5limbs) 1
        let inner ←
          SudoRt.runLoopOn ((0 : Int), σ.snd, (0 : Int))
            (if (0 : Int) > toJ then 1 else (toJ - 0).natAbs + 1)
            (fun σ1 =>
              if σ1.fst > toJ then
                pure (SudoRt.Flow.brk (σ1.fst, σ1.snd.fst, σ1.snd.snd))
              else do
                let liftJ ←
                  (do
                    let ij ← SudoRt.addI σ.fst σ1.fst
                    let cur0 ← SudoRt.atL σ1.snd.fst ij
                    let ai ← SudoRt.atL a.sudo_6BigInt_5limbs σ.fst
                    let bj ← SudoRt.atL b.sudo_6BigInt_5limbs σ1.fst
                    let prod ← SudoRt.mulI ai bj
                    let s1 ← SudoRt.addI cur0 prod
                    let cur ← SudoRt.addI s1 σ1.snd.snd
                    let ij2 ← SudoRt.addI σ.fst σ1.fst
                    let digit ← SudoRt.modI cur Megadreifach.limb_base
                    let out ← SudoRt.putL σ1.snd.fst ij2 digit
                    let carry ← SudoRt.divI cur Megadreifach.limb_base
                    pure (SudoRt.Flow.cont (out, carry)))
                match liftJ with
                | .ret r => pure (SudoRt.Flow.ret r)
                | .brk fs => pure (SudoRt.Flow.brk (σ1.fst, fs))
                | .cont fs =>
                  if (σ1.fst == toJ) = true then
                    pure (SudoRt.Flow.brk (σ1.fst, fs))
                  else do
                    let i' ← SudoRt.addI σ1.fst 1
                    pure (SudoRt.Flow.cont (i', fs)))
            (fun σ1 => do
              let k0 ← SudoRt.addI σ.fst (SudoRt.listLen b.sudo_6BigInt_5limbs)
              let toK ← SudoRt.subI (SudoRt.listLen σ1.snd.fst) 1
              let kLoop ←
                SudoRt.runLoopOn (k0, σ1.snd.fst, σ1.snd.snd)
                  (if k0 > toK then 1 else (toK - k0).natAbs + 1)
                  (fun σk =>
                    if σk.fst > toK then
                      pure (SudoRt.Flow.brk (σk.fst, σk.snd.fst, σk.snd.snd))
                    else do
                      let liftK ←
                        (if decide (σk.snd.snd > 0) = true then do
                          let cur0 ← SudoRt.atL σk.snd.fst σk.fst
                          let cur ← SudoRt.addI cur0 σk.snd.snd
                          let digit ← SudoRt.modI cur Megadreifach.limb_base
                          let out ← SudoRt.putL σk.snd.fst σk.fst digit
                          let carry ← SudoRt.divI cur Megadreifach.limb_base
                          pure (SudoRt.Flow.cont (out, carry))
                        else
                          pure (SudoRt.Flow.cont (σk.snd.fst, σk.snd.snd)))
                      match liftK with
                      | .ret r => pure (SudoRt.Flow.ret r)
                      | .brk fs => pure (SudoRt.Flow.brk (σk.fst, fs))
                      | .cont fs =>
                        if (σk.fst == toK) = true then
                          pure (SudoRt.Flow.brk (σk.fst, fs))
                        else do
                          let i' ← SudoRt.addI σk.fst 1
                          pure (SudoRt.Flow.cont (i', fs)))
                  (fun σk => pure (SudoRt.Flow.cont σk.snd.fst))
                  (fun r => pure (SudoRt.Flow.ret r))
              pure kLoop)
            (fun r => pure (SudoRt.Flow.ret r))
        pure inner :
        Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt))
    match lift with
    | .ret r => pure (SudoRt.Flow.ret r)
    | .brk fs => pure (SudoRt.Flow.brk (σ.fst, fs))
    | .cont fs =>
      if (σ.fst == toV) = true then
        pure (SudoRt.Flow.brk (σ.fst, fs))
      else do
        let i' ← SudoRt.addI σ.fst 1
        pure (SudoRt.Flow.cont (i', fs))

theorem big_mul_zero_left (b : Megadreifach.BigInt) :
    Megadreifach.big_mul (bigOf []) b = .ok (bigOf []) := by
  unfold Megadreifach.big_mul
  dsimp [bigOf]
  have hlen : SudoRt.listLen (embed ([] : List Nat)) = (0 : Int) := by
    rw [listLen_embed, List.length_nil]; rfl
  rw [hlen]
  have hb : SudoRt.SEq.beq (0 : Int) (0 : Int) = true := by simp [sEq_int]
  rw [hb]
  dsimp
  rw [big_zero_spec, except_bind_pure]
  rfl

private theorem zeros2_size0 : 0 < (Array.mkArray 2 (0 : Int)).size := by
  simp [Array.size_mkArray]

private theorem zeros2_size1 : 1 < (Array.mkArray 2 (0 : Int)).size := by
  simp [Array.size_mkArray]

private theorem zeros_set0 (x : Nat) :
    (Array.mkArray 2 (0 : Int)).set ⟨0, zeros2_size0⟩ (Int.ofNat x) = embed [x, 0] := by
  apply Array.ext'
  simp [embed, Array.toList_set, Array.toList_mkArray, List.replicate, List.set_cons_zero]

private theorem embed_set_high (lo hi : Nat) :
    (embed [lo, 0]).set ⟨1, by simp [size_embed]⟩ (Int.ofNat hi) = embed [lo, hi] := by
  apply Array.ext'
  simp [embed, Array.toList_set, List.set]

private theorem prod_lt_sq {a b : Nat} (ha : a < limbBase) (hb : b < limbBase) :
    a * b < limbBase ^ 2 := by
  have ha' : a ≤ limbBase - 1 := by
    have : 0 < limbBase := limbBase_pos
    omega
  have hb' : b ≤ limbBase - 1 := by
    have : 0 < limbBase := limbBase_pos
    omega
  have hmul : a * b ≤ (limbBase - 1) * (limbBase - 1) := Nat.mul_le_mul ha' hb'
  have hconst : (limbBase - 1) * (limbBase - 1) < limbBase ^ 2 := by
    unfold limbBase
    decide
  exact Nat.lt_of_le_of_lt hmul hconst

private theorem prod_fits {a b : Nat} (ha : a < limbBase) (hb : b < limbBase) :
    FitsLen (a * b) := by
  have hsq : a * b < limbBase ^ 2 := prod_lt_sq ha hb
  exact Nat.le_trans (Nat.le_of_lt hsq) limb_sq_fits

private theorem fuel_point (n : Int) :
    (if n > n then (1 : Nat) else (n - n).natAbs + 1) = 1 := by
  simp [Int.lt_irrefl, Int.sub_self]

private theorem subI_one_one : SudoRt.subI (1 : Int) (1 : Int) = .ok (0 : Int) := by
  erw [subI_ofNat_one 1 (by decide) FitsLen.one]
  rfl

private theorem subI_two_one : SudoRt.subI (2 : Int) (1 : Int) = .ok (1 : Int) := by
  have h : FitsLen 2 := by unfold FitsLen i64MaxNat; decide
  erw [subI_ofNat 2 1 h (by decide)]
  simp

private theorem addI_one_one : SudoRt.addI (1 : Int) (1 : Int) = .ok (2 : Int) := by
  have h : FitsLen (1 + 1) := by unfold FitsLen i64MaxNat; decide
  erw [addI_ofNat 1 1 h]
  rfl

private theorem addI_zero_one : SudoRt.addI (0 : Int) (1 : Int) = .ok (1 : Int) := by
  erw [addI_ofNat 0 1 FitsLen.one]
  simp [Nat.zero_add]

private theorem addI_zero_zero : SudoRt.addI (0 : Int) (0 : Int) = .ok (0 : Int) := by
  erw [addI_ofNat 0 0 FitsLen.zero]
  simp

private theorem addI_zero_nat (n : Nat) (_h : FitsLen n) :
    SudoRt.addI (0 : Int) (Int.ofNat n) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (0 + n) := by simpa [Nat.zero_add] using _h
  erw [addI_ofNat 0 n h0]
  simp [Nat.zero_add]

private theorem addI_nat_zero (n : Nat) (_h : FitsLen n) :
    SudoRt.addI (Int.ofNat n) (0 : Int) = .ok (Int.ofNat n) := by
  have h0 : FitsLen (n + 0) := by simpa [Nat.add_zero] using _h
  erw [addI_ofNat n 0 h0]
  simp [Nat.add_zero]

private theorem modI_nat_base (n : Nat) :
    SudoRt.modI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n % limbBase)) := by
  erw [limb_base_eq, modI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem divI_nat_base (n : Nat) :
    SudoRt.divI (Int.ofNat n) Megadreifach.limb_base =
      .ok (Int.ofNat (n / limbBase)) := by
  erw [limb_base_eq, divI_ofNat n (Nat.ne_of_gt limbBase_pos)]

private theorem putL_at0 (a : Array Int) (v : Int) (h : 0 < a.size) :
    SudoRt.putL a (0 : Int) v = .ok (a.set ⟨0, h⟩ v) := by
  erw [putL_ofNat a 0 v h]

private theorem putL_at1 (x0 x1 : Nat) (v : Int)
    (h : 1 < (embed [x0, x1]).size) :
    SudoRt.putL (embed [x0, x1]) (1 : Int) v =
      .ok ((embed [x0, x1]).set ⟨1, h⟩ v) := by
  erw [putL_ofNat (embed [x0, x1]) 1 v h]

private theorem atL_head (xs : List Nat) (h : 0 < xs.length) :
    SudoRt.atL (embed xs) (0 : Int) = .ok (Int.ofNat xs[0]) := by
  erw [atL_embed xs 0 h]

private theorem filledL_two :
    SudoRt.filledL (2 : Int) (0 : Int) = .ok (Array.mkArray 2 (0 : Int)) := by
  erw [filledL_ofNat 2 (0 : Int)]

private def rawProd (a b : Nat) : Array Int :=
  embed [a * b % limbBase, a * b / limbBase]

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

private theorem match_ok_brk {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.brk s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onBrk s := by
  rfl

private theorem match_pure_brk {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match (pure (SudoRt.Flow.brk s) : Except SudoRt.Trap (SudoRt.Flow σ ρ)) with
      | Except.error e => Except.error e
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onBrk s := by
  rfl

private theorem bind_pure_flow {σ ρ β} (fl : SudoRt.Flow σ ρ)
    (f : SudoRt.Flow σ ρ → Except SudoRt.Trap β) :
    (pure fl >>= f) = f fl := rfl

private theorem flowCont_brk (x : Array Int × Int) :
    (match SudoRt.Flow.cont (σ := Array Int × Int) (ρ := Megadreifach.BigInt) x with
      | SudoRt.Flow.ret r =>
        pure (SudoRt.Flow.ret (σ := Int × (Array Int × Int)) (ρ := Megadreifach.BigInt) r)
      | SudoRt.Flow.brk fs =>
        pure (SudoRt.Flow.brk (σ := Int × (Array Int × Int)) (ρ := Megadreifach.BigInt)
          ((0 : Int), fs))
      | SudoRt.Flow.cont fs =>
        pure (SudoRt.Flow.brk (σ := Int × (Array Int × Int)) (ρ := Megadreifach.BigInt)
          ((0 : Int), fs))) =
      (pure (SudoRt.Flow.brk (σ := Int × (Array Int × Int)) (ρ := Megadreifach.BigInt)
          ((0 : Int), x)) :
        Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Int)) Megadreifach.BigInt)) := by
  rfl

/-- The 1×1 schoolbook step breaks with limbs `[prod % base, prod / base]`. -/
private theorem mulIStep_11 (a b : Nat)
    (ha : a < limbBase) (hb : b < limbBase) :
    mulIStep (bigOf [a]) (bigOf [b]) 0 (0, Array.mkArray 2 (0 : Int)) =
      .ok (SudoRt.Flow.brk (0, rawProd a b)) := by
  have hfit : FitsLen (a * b) := prod_fits ha hb
  have hsq : a * b < limbBase ^ 2 := prod_lt_sq ha hb
  have hlenb : SudoRt.listLen (embed [b]) = (1 : Int) := by
    rw [listLen_embed]; rfl
  have hsz0 := zeros2_size0
  unfold mulIStep
  dsimp [bigOf]
  rw [hlenb, subI_one_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  have hat0 : SudoRt.atL (Array.mkArray 2 (0 : Int)) (0 : Int) = .ok (0 : Int) := by
    erw [atL_ofNat (Array.mkArray 2 (0 : Int)) 0 (by simp [Array.size_mkArray])]
    simp [Array.getElem_mkArray]
  rw [addI_zero_zero, ok_bind, hat0, ok_bind,
    atL_head [a] (by simp), ok_bind, atL_head [b] (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [mulI_ofNat a b hfit, ok_bind,
    addI_zero_nat (a * b) hfit, ok_bind, addI_nat_zero (a * b) hfit, ok_bind,
    ok_bind, modI_nat_base (a * b), ok_bind,
    putL_at0 (Array.mkArray 2 (0 : Int)) (Int.ofNat ((a * b) % limbBase)) hsz0, ok_bind,
    divI_nat_base (a * b), ok_bind]
  simp only [beq_int_iff]
  rw [zeros_set0 ((a * b) % limbBase), bind_pure_flow, flowCont_brk]
  simp only [toPure_eq_ok, match_ok_brk]
  have hlenOut : SudoRt.listLen (embed [a * b % limbBase, 0]) = (2 : Int) := by
    rw [listLen_embed]; rfl
  rw [addI_zero_one, ok_bind, hlenOut, subI_two_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  by_cases hsmall : a * b < limbBase
  · have hdiv0 : a * b / limbBase = 0 := Nat.div_eq_of_lt hsmall
    have hmod : a * b % limbBase = a * b := Nat.mod_eq_of_lt hsmall
    have hdivI : (↑(a * b) / ↑limbBase : Int) = 0 := by
      erw [(Int.ofNat_ediv (a * b) limbBase).symm]
      rw [hdiv0]
      rfl
    rw [hdivI]
    simp only [show decide ((0 : Int) > 0) = false from by decide, decide_False,
      Bool.false_eq_true, ite_false]
    -- k after returns `cont`, and i = toV so the outer match breaks.
    simp [rawProd, hdiv0, hmod, beq_int_iff]
  · have hdivpos : 0 < a * b / limbBase :=
      div_pos_of_le limbBase_pos (Nat.le_of_not_lt hsmall)
    have hdivlt : a * b / limbBase < limbBase := by
      rw [limbBase_pow2] at hsq
      exact div_lt_of_lt_mul limbBase_pos hsq
    have hcarry : (↑(a * b) / ↑limbBase : Int) = Int.ofNat (a * b / limbBase) := by
      erw [(Int.ofNat_ediv (a * b) limbBase).symm]
      rfl
    have hdec : decide ((↑(a * b) / ↑limbBase : Int) > 0) = true := by
      rw [hcarry, decide_ofNat_pos, decide_eq_true_eq]
      exact hdivpos
    rw [hdec, hcarry]
    have hszE : 1 < (embed [a * b % limbBase, 0]).size := by simp [size_embed]
    have hat1 : SudoRt.atL (embed [a * b % limbBase, 0]) (1 : Int) = .ok (0 : Int) := by
      erw [atL_embed [a * b % limbBase, 0] 1 (by simp)]
      simp
    rw [hat1, ok_bind]
    have hcur : FitsLen (a * b / limbBase) := fits_of_lt_limb hdivlt
    rw [addI_zero_nat (a * b / limbBase) hcur, ok_bind, modI_nat_base (a * b / limbBase),
      ok_bind,
      putL_at1 (a * b % limbBase) 0 (Int.ofNat ((a * b / limbBase) % limbBase)) hszE,
      ok_bind, divI_nat_base (a * b / limbBase), ok_bind]
    have hmodHi : (a * b / limbBase) % limbBase = a * b / limbBase :=
      Nat.mod_eq_of_lt hdivlt
    have hdivHi : (a * b / limbBase) / limbBase = 0 := Nat.div_eq_of_lt hdivlt
    simp only [hmodHi, hdivHi, Nat.zero_add]
    rw [embed_set_high (a * b % limbBase) (a * b / limbBase)]
    simp [rawProd, toPure_eq_ok, match_ok_brk]

/-- One-limb times one-limb. Product fits in an i64 (`(10^9-1)^2 < 2^63`). -/
theorem big_mul_limb (a b : Nat) (ha0 : 0 < a) (hb0 : 0 < b)
    (ha : a < limbBase) (hb : b < limbBase) :
    Megadreifach.big_mul (bigOf [a]) (bigOf [b]) = .ok (bigNat (a * b)) := by
  have hsq : a * b < limbBase ^ 2 := prod_lt_sq ha hb
  have hv : 0 < a * b := Nat.mul_pos ha0 hb0
  unfold Megadreifach.big_mul
  dsimp [bigOf]
  have hlen1 : SudoRt.listLen (embed [a]) = (1 : Int) := by
    rw [listLen_embed]; rfl
  have hlenb : SudoRt.listLen (embed [b]) = (1 : Int) := by
    rw [listLen_embed]; rfl
  rw [hlen1]
  have hbeq : SudoRt.SEq.beq (1 : Int) (0 : Int) = false := by simp [sEq_int]
  rw [hbeq]
  dsimp
  rw [hlenb, hbeq]
  rw [show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind,
    if_neg (by decide : ¬ ((false : Bool) = true))]
  rw [addI_one_one, ok_bind, filledL_two, ok_bind, subI_one_one, ok_bind]
  dsimp
  rw [except_bind_pure, show (1 : Nat) = 0 + 1 from rfl]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := mulIStep (bigOf [a]) (bigOf [b]) (0 : Int))
    intro σ
    unfold mulIStep
    dsimp [bigOf]
    rfl
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, mulIStep_11 a b ha hb]
  dsimp
  rw [except_bind_pure, rawProd,
    make_big_false [a * b % limbBase, a * b / limbBase] (by simp [fits_le3]),
    limbs_prod (a * b) hv hsq]
  simp [bigNat]

/-- Multiply a one-limb accumulator by a positive one-limb radix. -/
theorem big_mul_acc (a r : Nat) (hr0 : 0 < r) (hr : r < limbBase) (ha : a < limbBase) :
    Megadreifach.big_mul (bigNat a) (bigNat r) = .ok (bigNat (a * r)) := by
  by_cases ha0 : a = 0
  · simp [ha0, bigNat_zero, big_mul_zero_left, Nat.zero_mul]
  · rw [bigNat_limb a ha ha0, bigNat_limb r hr (Nat.ne_of_gt hr0)]
    exact big_mul_limb a r (Nat.pos_of_ne_zero ha0) hr0 ha hr

/-! ## `big_add` on one limb, no carry -/

private def pushNat (out : Array Int) (d : Nat) : Array Int :=
  (SudoRt.appendL out (Int.ofNat d)).1

private theorem push_nil (d : Nat) : pushNat (#[] : Array Int) d = embed [d] := by
  simp [pushNat, appendL_spec, embed, Array.push, List.concat_eq_append]

private theorem big_add_limb (x y : Nat) (hx0 : 0 < x) (_hy0 : 0 < y)
    (hx : x < limbBase) (_hy : y < limbBase) (hxy : x + y < limbBase) :
    Megadreifach.big_add (bigOf [x]) (bigOf [y]) = .ok (bigNat (x + y)) := by
  have hfit : FitsLen (x + y) := fits_of_lt_limb hxy
  unfold Megadreifach.big_add Megadreifach.mag_add
  dsimp [bigOf]
  have hlenx : SudoRt.listLen (embed [x]) = (1 : Int) := by rw [listLen_embed]; rfl
  have hleny : SudoRt.listLen (embed [y]) = (1 : Int) := by rw [listLen_embed]; rfl
  rw [hlenx, hleny]
  have hcmp : decide ((1 : Int) > (1 : Int)) = false := by decide
  rw [hcmp, if_neg (by decide : ¬ ((false : Bool) = true))]
  rw [subI_one_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  rw [atL_head [x] (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [addI_zero_nat x (fits_of_lt_limb hx), ok_bind, atL_head [y] (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  have hsum0 : FitsLen (x + y) := hfit
  rw [addI_ofNat x y hsum0, ok_bind, modI_nat_base (x + y), ok_bind]
  have hmod : (x + y) % limbBase = x + y := Nat.mod_eq_of_lt hxy
  have hdiv : (x + y) / limbBase = 0 := Nat.div_eq_of_lt hxy
  rw [hmod]
  have happ : (SudoRt.appendL (#[] : Array Int) (Int.ofNat (x + y))).1 = embed [x + y] := by
    simp [appendL_spec, embed]
  rw [happ, divI_nat_base (x + y), ok_bind, hdiv]
  simp only [ok_bind, Int.ofNat_zero, show decide ((0 : Int) > 0) = false from by decide,
    match_ok_cont, match_ok_brk, toPure_eq_ok]
  simp only [show decide (Int.ofNat 0 > (0 : Int)) = false from by decide]
  rw [if_neg (by decide : ¬ ((false : Bool) = true)), ok_bind, ok_bind]
  rw [make_big_false [x + y] (by simp [fits_le3])]
  have hdrop : dropTrail [x + y] = [x + y] := by
    have hne : x + y ≠ 0 := Nat.ne_of_gt (Nat.add_pos_left hx0 y)
    simp [dropTrail, hne]
  rw [hdrop, bigNat_limb (x + y) hxy (Nat.ne_of_gt (Nat.add_pos_left hx0 y)), ok_bind]

private theorem big_add_zeros :
    Megadreifach.big_add (bigOf []) (bigOf []) = .ok (bigOf []) := by
  unfold Megadreifach.big_add Megadreifach.mag_add
  dsimp [bigOf]
  have h0 : SudoRt.listLen (embed ([] : List Nat)) = (0 : Int) := by
    rw [listLen_embed]; rfl
  rw [h0, subI_zero_one, ok_bind]
  have hgt : (0 : Int) > (-1 : Int) := by decide
  simp only [hgt, ite_true]
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ, if_pos hgt]
  simp only [toPure_eq_ok, match_ok_brk,
    show decide ((0 : Int) > (0 : Int)) = false from by decide]
  rw [if_neg (by decide : ¬ ((false : Bool) = true)), ok_bind, ok_bind,
    ← embed_nil, make_big_false [] FitsLen.zero, ok_bind]
  rfl

private theorem big_add_right0 (x : Nat) (hx0 : 0 < x) (hx : x < limbBase) :
    Megadreifach.big_add (bigOf [x]) (bigOf []) = .ok (bigNat x) := by
  unfold Megadreifach.big_add Megadreifach.mag_add
  dsimp [bigOf]
  have hlenx : SudoRt.listLen (embed [x]) = (1 : Int) := by rw [listLen_embed]; rfl
  have hleny : SudoRt.listLen (embed ([] : List Nat)) = (0 : Int) := by rw [listLen_embed]; rfl
  rw [hlenx, hleny]
  have hcmp : decide ((0 : Int) > (1 : Int)) = false := by decide
  rw [hcmp, if_neg (by decide : ¬ ((false : Bool) = true)), subI_one_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  rw [atL_head [x] (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [addI_zero_nat x (fits_of_lt_limb hx), ok_bind, modI_nat_base x, ok_bind]
  have hmod : x % limbBase = x := Nat.mod_eq_of_lt hx
  have hdiv : x / limbBase = 0 := Nat.div_eq_of_lt hx
  have happ : (SudoRt.appendL (#[] : Array Int) (Int.ofNat x)).1 = embed [x] := by
    simp [appendL_spec, embed]
  rw [hmod, happ, divI_nat_base x, ok_bind, hdiv, bind_pure_flow]
  simp only [flowCont_brk, toPure_eq_ok, match_ok_brk,
    show decide (Int.ofNat 0 > (0 : Int)) = false from by decide]
  rw [if_neg (by decide : ¬ ((false : Bool) = true)), ok_bind, ok_bind,
    make_big_false [x] (by simp [fits_le3])]
  have hdrop : dropTrail [x] = [x] := by
    simp [dropTrail, Nat.ne_of_gt hx0]
  rw [hdrop, bigNat_limb x hx (Nat.ne_of_gt hx0), ok_bind]

private theorem big_add_left0 (y : Nat) (hy0 : 0 < y) (hy : y < limbBase) :
    Megadreifach.big_add (bigOf []) (bigOf [y]) = .ok (bigNat y) := by
  unfold Megadreifach.big_add Megadreifach.mag_add
  dsimp [bigOf]
  have hlenx : SudoRt.listLen (embed ([] : List Nat)) = (0 : Int) := by rw [listLen_embed]; rfl
  have hleny : SudoRt.listLen (embed [y]) = (1 : Int) := by rw [listLen_embed]; rfl
  rw [hlenx, hleny]
  have hcmp : decide ((1 : Int) > (0 : Int)) = true := by decide
  rw [hcmp, if_pos rfl, subI_one_one, ok_bind]
  dsimp
  rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  rw [atL_head [y] (by simp), ok_bind]
  simp only [List.getElem_cons_zero]
  rw [addI_zero_nat y (fits_of_lt_limb hy), ok_bind, modI_nat_base y, ok_bind]
  have hmod : y % limbBase = y := Nat.mod_eq_of_lt hy
  have hdiv : y / limbBase = 0 := Nat.div_eq_of_lt hy
  have happ : (SudoRt.appendL (#[] : Array Int) (Int.ofNat y)).1 = embed [y] := by
    simp [appendL_spec, embed]
  rw [hmod, happ, divI_nat_base y, ok_bind, hdiv, bind_pure_flow]
  simp only [flowCont_brk, toPure_eq_ok, match_ok_brk,
    show decide (Int.ofNat 0 > (0 : Int)) = false from by decide]
  rw [if_neg (by decide : ¬ ((false : Bool) = true)), ok_bind, ok_bind,
    make_big_false [y] (by simp [fits_le3])]
  have hdrop : dropTrail [y] = [y] := by simp [dropTrail, Nat.ne_of_gt hy0]
  rw [hdrop, bigNat_limb y hy (Nat.ne_of_gt hy0), ok_bind]

/-- `bigNat x + bigNat y` when both values and their sum sit in one limb. -/
theorem big_add_small (x y : Nat) (hx : x < limbBase) (hy : y < limbBase)
    (hxy : x + y < limbBase) :
    Megadreifach.big_add (bigNat x) (bigNat y) = .ok (bigNat (x + y)) := by
  by_cases hx0 : x = 0
  · by_cases hy0 : y = 0
    · simp [hx0, hy0, bigNat_zero, big_add_zeros, Nat.zero_add]
    · have hy0' : 0 < y := Nat.pos_of_ne_zero hy0
      have h := big_add_left0 y hy0' hy
      rw [← bigNat_limb y hy hy0] at h
      rw [hx0, Nat.zero_add, bigNat_zero]
      exact h
  · by_cases hy0 : y = 0
    · have hx0' : 0 < x := Nat.pos_of_ne_zero hx0
      have h := big_add_right0 x hx0' hx
      rw [← bigNat_limb x hx hx0] at h
      rw [hy0, Nat.add_zero, bigNat_zero]
      exact h
    · have h :=
        big_add_limb x y (Nat.pos_of_ne_zero hx0) (Nat.pos_of_ne_zero hy0) hx hy hxy
      rw [← bigNat_limb x hx hx0, ← bigNat_limb y hy hy0] at h
      exact h

/-! ## Pack loop -/

private def packBody (radix : Megadreifach.BigInt) (digits : Array Int)
    (n : Megadreifach.BigInt) (i : Int) :
    Except SudoRt.Trap (SudoRt.Flow Megadreifach.BigInt Megadreifach.BigInt) := do
  let n1 ← Megadreifach.big_mul n radix
  let d ← SudoRt.atL digits i
  let di ← Megadreifach.big_from_int d
  let n2 ← Megadreifach.big_add n1 di
  pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) n2)

private def packStep (radix : Megadreifach.BigInt) (digits : Array Int) (toV : Int)
    (σ : Int × Megadreifach.BigInt) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × Megadreifach.BigInt) Megadreifach.BigInt) :=
  let i := σ.1
  let n := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, n))
    else
      match ← packBody radix digits n i with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (i', fs))

private theorem fits_two : FitsLen 2 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits_three : FitsLen 3 := by
  unfold FitsLen i64MaxNat
  decide

private theorem two_pow28_lt_limb : 2 ^ 28 < limbBase := by
  have h : 2 ^ 28 < 2 ^ 29 := by decide
  exact Nat.lt_trans h two_pow29_lt_limb

private theorem pow_le_pow_two {i : Nat} (hi : i ≤ 28) : 2 ^ i ≤ 2 ^ 28 :=
  Nat.pow_le_pow_right (by decide) hi

private theorem ori2_acc_limb (eo : List Nat) (h : Ori2Wf eo) (i : Nat) (hi : i ≤ 28) :
    oriAcc 2 eo i < limbBase := by
  have hlen : i ≤ eo.length := by rw [h.len]; omega
  have hlt := oriAcc_lt eo h.bound i hlen
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt (pow_le_pow_two hi))
    (Nat.le_of_lt two_pow28_lt_limb)

private theorem ori2_sum_limb (eo : List Nat) (h : Ori2Wf eo) (i : Nat)
    (hi : i ≤ 28) (hiLen : i < eo.length) :
    oriAcc 2 eo i * 2 + eo[i] < limbBase := by
  have hlt := oriAcc_succ 2 eo i hiLen
  have hnext : oriAcc 2 eo (i + 1) < 2 ^ (i + 1) := by
    have hlen : i + 1 ≤ eo.length := by rw [h.len]; omega
    exact oriAcc_lt eo h.bound (i + 1) hlen
  have hpow : 2 ^ (i + 1) ≤ 2 ^ 29 := by
    have : i + 1 ≤ 29 := by omega
    exact Nat.pow_le_pow_right (by decide) this
  rw [← hlt]
  exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hnext hpow) (Nat.le_of_lt two_pow29_lt_limb)

private theorem packStep_ori2 (eo : List Nat) (h : Ori2Wf eo) (i : Nat) (hi : i ≤ 28) :
    packStep (bigNat 2) (embed eo) (28 : Int) (Int.ofNat i, bigNat (oriAcc 2 eo i)) =
      if i = 28 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, bigNat (oriAcc 2 eo (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), bigNat (oriAcc 2 eo (i + 1)))) := by
  have hiLen : i < eo.length := by rw [h.len]; omega
  have hacc := ori2_acc_limb eo h i hi
  have hdig : eo[i] < 2 := h.bound _ (List.getElem_mem hiLen)
  have hsum := ori2_sum_limb eo h i hi hiLen
  have hprod : oriAcc 2 eo i * 2 < limbBase :=
    Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hsum
  unfold packStep packBody
  dsimp
  have hngt : ¬ (i : Int) > (28 : Int) := ofNat_not_gt hi
  have hat : SudoRt.atL (embed eo) (i : Int) = .ok (Int.ofNat (eo[i])) := by
    erw [atL_embed eo i hiLen]
  rw [if_neg hngt, big_mul_acc (oriAcc 2 eo i) 2 (by decide) (by decide) hacc, ok_bind,
    hat, ok_bind]
  have hfitD : FitsLen (eo[i]) := fits_lt_pow2_29 (by omega)
  rw [big_from_int_refines (eo[i]) hfitD, ok_bind]
  have hbig : bigOf (limbsOfNat (eo[i])) = bigNat (eo[i]) := rfl
  rw [hbig, big_add_small (oriAcc 2 eo i * 2) (eo[i]) hprod (by omega) hsum, ok_bind,
    oriAcc_succ 2 eo i hiLen]
  by_cases heq : i = 28
  · simp [heq, toPure_eq_ok]
  · have hneI : ¬ (i : Int) = (28 : Int) := fun hq => heq (Int.ofNat.inj hq)
    have hadd := addI_ofNat_one i (by
      unfold FitsLen i64MaxNat
      omega)
    rw [ofNat_eq_natCast i] at hadd
    have hbeq : ((i : Int) == (28 : Int)) = false := by
      simpa [beq_int_iff] using hneI
    rw [hbeq, toPure_eq_ok, hadd, ok_bind]
    simp [heq]

private theorem packRun2 (eo : List Nat) (h : Ori2Wf eo) :
    SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
      ((0 : Int), bigNat 0)
      (fuelRange (0 : Int) (28 : Int))
      (packStep (bigNat 2) (embed eo) (28 : Int))
      (fun σ => pure σ.2)
      (fun r => pure r) =
      .ok (bigNat (packOri2 eo)) := by
  have h0 : bigNat 0 = bigNat (oriAcc 2 eo 0) := by simp [oriAcc_zero]
  rw [h0]
  apply chain_loop (f := fun i => bigNat (oriAcc 2 eo i)) (fromN := 0) (toN := 28)
    (hle := by decide) (goal := .ok (bigNat (packOri2 eo)))
  · intro i _ hi
    simpa using packStep_ori2 eo h i hi
  · rw [oriAcc_pack2 eo (by rw [h.len]; omega)]
    rfl

/-- `Generated.pack_ori2` is algebraic `packOri2` on length-30 edge orientations. -/
theorem pack_ori2_refines (eo : List Nat) (h : Ori2Wf eo) :
    Megadreifach.pack_ori2 (embed eo) = .ok (bigNat (packOri2 eo)) := by
  unfold Megadreifach.pack_ori2
  rw [big_zero_spec, ok_bind, show (2 : Int) = Int.ofNat 2 from rfl,
    big_from_int_refines 2 fits_two, ok_bind]
  dsimp
  have hfuel : fuelRange (0 : Int) (28 : Int) = 29 := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl, show (28 : Int) = Int.ofNat 28 from rfl,
      fuelRange_le (by decide)]
  rw [except_bind_pure, ← hfuel]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := packStep (bigNat 2) (embed eo) (28 : Int))
    intro σ
    unfold packStep packBody
    dsimp
    rfl
  · rw [← bigNat_zero]
    exact packRun2 eo h

theorem pack_ori2_refines_array (a : Array Int) (h : WellFormedOri2 a) :
    Megadreifach.pack_ori2 a = .ok (bigNat (packOri2 (decode a))) := by
  have hr := pack_ori2_refines (decode a) (ori2Wf_decode a h)
  simpa [embed_decode a h.nn] using hr

end MegaDreifach.Link2

