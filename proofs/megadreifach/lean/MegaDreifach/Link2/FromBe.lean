/-
  LINK 2. `big_from_be` on an all-zero byte string.

  `phi_chunk` reads the pad block with `big_from_be`. The zero block is the
  identity deal's integer: every byte is `0`, the Horner value is `0`, and
  the emitted bigint is the empty limb list. Length must fit in an i64 so
  the index loop does not overflow (includes `0` and the 28-byte pad block).

  Not a general 28-byte integer (`2^224` is many limbs). Not `phi_chunk`.
  Not `phi_inv`. Not `v_Hash`.
-/
import MegaDreifach.Pad
import Megadreifach
import MegaDreifach.Link2.PackOri

namespace MegaDreifach.Link2

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem toPure_eq_ok {α} (a : α) :
    (Applicative.toPure.1 a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem match_ok_brk {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.brk s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onBrk s := by
  rfl

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

private theorem limbs_256 : limbsOfNat 256 = [256] := by
  have hne : 256 ≠ 0 := by decide
  have hq : 256 / limbBase = 0 := by unfold limbBase; decide
  have hmod : 256 % limbBase = 256 := by unfold limbBase; decide
  simp [limbsOfNat, hne, hq, hmod]

private theorem fits_256 : FitsLen 256 := by
  unfold FitsLen i64MaxNat
  decide

theorem two56_refines :
    Megadreifach.big_from_int 256 = .ok (bigOf [256]) := by
  rw [show (256 : Int) = Int.ofNat 256 from rfl, big_from_int_refines 256 fits_256,
    limbs_256]

theorem fromBE_zeros (k : Nat) : fromBE (List.replicate k 0) = 0 := by
  induction k with
  | zero => simp [fromBE, mixEncode]
  | succ k ih =>
    rw [List.replicate_succ]
    simp only [fromBE, List.length_cons, List.length_replicate, List.replicate_succ,
      mixEncode, Nat.zero_mul, Nat.zero_add]
    simpa [fromBE, List.length_replicate] using ih

/-- Horner step of `big_from_be`, in the shape the emitter leaves. -/
def beFromStep (bs : Array Int) (two56 : Megadreifach.BigInt) (toV : Int)
    (σ : Int × Megadreifach.BigInt) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Megadreifach.BigInt) Megadreifach.BigInt) :=
  let i := σ.1
  let n := σ.2
  do
    if i > toV then
      pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, n))
    else
      match ← ((do
        let t1 ← Megadreifach.big_mul n two56
        let b ← SudoRt.atL bs i
        let t2 ← Megadreifach.big_from_int b
        let n ← Megadreifach.big_add t1 t2
        pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) n)) :
          Except SudoRt.Trap (SudoRt.Flow _ Megadreifach.BigInt)) with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r)
      | .brk fs => pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, fs))
      | .cont fs => do
          if i == toV then
            pure (SudoRt.Flow.brk (ρ := Megadreifach.BigInt) (i, fs))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) (i', fs))

private theorem beFromStep_gt (bs : Array Int) (two56 : Megadreifach.BigInt)
    (toV i : Int) (n : Megadreifach.BigInt) (h : i > toV) :
    beFromStep bs two56 toV (i, n) = .ok (SudoRt.Flow.brk (i, n)) := by
  unfold beFromStep
  rw [if_pos h]
  rfl

private theorem beFromStep_hit (k i : Nat) (hi : i < k) (hfits : FitsLen k)
    (two56 : Megadreifach.BigInt) :
    beFromStep (embed (List.replicate k 0)) two56 (Int.ofNat (k - 1))
        (Int.ofNat i, bigOf []) =
      if i = k - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat i, bigOf []))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), bigOf [])) := by
  unfold beFromStep
  dsimp
  have hle : i ≤ k - 1 := by omega
  have hngt : ¬ (i : Int) > ((k - 1 : Nat) : Int) := ofNat_not_gt hle
  rw [if_neg hngt, big_mul_zero_left, ok_bind]
  have hlen : i < (List.replicate k 0).length := by simpa [List.length_replicate] using hi
  have hat := atL_embed (List.replicate k 0) i hlen
  rw [ofNat_eq_natCast i] at hat
  rw [hat, List.getElem_replicate, ok_bind, big_from_int_refines 0 FitsLen.zero,
    show limbsOfNat 0 = [] by simp [limbsOfNat], ok_bind, big_add_zeros, ok_bind, pure_eq_ok]
  by_cases heq : i = k - 1
  · subst heq
    have hbeq : (((k - 1 : Nat) : Int) == ((k - 1 : Nat) : Int)) = true := by
      simp [beq_int_iff]
    rw [hbeq]
    simp only [ite_true]
    exact pure_eq_ok _
  · have hneI : ¬ ((i : Int) = ((k - 1 : Nat) : Int)) := fun h => heq (Int.ofNat.inj h)
    have hbeq : ((i : Int) == ((k - 1 : Nat) : Int)) = false := by
      simpa [beq_int_iff] using hneI
    have hadd := addI_ofNat_one i (FitsLen.of_le hfits (by omega))
    rw [ofNat_eq_natCast i] at hadd
    rw [hbeq, ok_bind]
    dsimp
    rw [hadd, ok_bind, if_neg heq, pure_eq_ok, ofNat_eq_natCast (i + 1)]

private theorem beFrom_loop (k : Nat) (hk : 0 < k) (hfits : FitsLen k)
    (two56 : Megadreifach.BigInt) :
    SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
      ((0 : Int), bigOf [])
      (fuelRange (0 : Int) (Int.ofNat (k - 1)))
      (beFromStep (embed (List.replicate k 0)) two56 (Int.ofNat (k - 1)))
      (fun σ => pure σ.2) (fun r => pure r) =
      .ok (bigOf []) := by
  rw [show (0 : Int) = Int.ofNat 0 from rfl]
  apply chain_loop (f := fun _ => bigOf []) (fromN := 0) (toN := k - 1)
    (hle := Nat.zero_le _) (goal := .ok (bigOf []))
  · intro i _ hi
    have hi' : i < k := by omega
    exact beFromStep_hit k i hi' hfits two56
  · rw [pure_eq_ok]

private theorem beFrom_break (two56 : Megadreifach.BigInt) :
    SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
      ((0 : Int), bigOf [])
      (fuelRange (0 : Int) (-1))
      (beFromStep (embed (List.replicate 0 0)) two56 (-1))
      (fun σ => pure σ.2) (fun r => pure r) =
      .ok (bigOf []) := by
  have hgt : (0 : Int) > (-1) := by decide
  rw [asc_break (0 : Int) (-1) (bigOf []) _ _ _ hgt
      (beFromStep_gt _ two56 (-1) 0 (bigOf []) hgt), pure_eq_ok]

/-- `big_from_be` of `k` zero bytes is the zero bigint, for `k` that fits in an i64. -/
theorem big_from_be_zeros (k : Nat) (hk : FitsLen k) :
    Megadreifach.big_from_be (embed (List.replicate k 0)) = .ok (bigOf []) := by
  unfold Megadreifach.big_from_be
  rw [big_zero_spec, ok_bind, two56_refines, ok_bind, listLen_embed,
    List.length_replicate]
  cases k with
  | zero =>
    rw [show SudoRt.subI (Int.ofNat 0) (1 : Int) = .ok (-1) from subI_zero_one, ok_bind]
    dsimp
    rw [except_bind_pure]
    have hgt : (0 : Int) > (-1) := by decide
    rw [show (1 : Nat) = fuelRange (0 : Int) (-1) from (fuelRange_gt hgt).symm]
    apply Eq.trans
    · apply runLoopOn_step_pointwise
        (step' := beFromStep (embed (List.replicate 0 0)) (bigOf [256]) (-1))
      intro σ
      unfold beFromStep
      dsimp
      rfl
    · exact beFrom_break (bigOf [256])
  | succ k =>
    have hpos : 0 < k + 1 := Nat.succ_pos k
    rw [subI_ofNat_one (k + 1) hpos hk, ok_bind]
    dsimp
    rw [fuelRange_eq (0 : Int) (k : Int), except_bind_pure]
    apply Eq.trans
    · apply runLoopOn_step_pointwise
        (step' := beFromStep (embed (List.replicate (k + 1) 0)) (bigOf [256]) (k : Int))
      intro σ
      unfold beFromStep
      dsimp
      rfl
    · exact beFrom_loop (k + 1) hpos hk (bigOf [256])

/-- Same statement against algebraic `fromBE` (the value is `0`). -/
theorem big_from_be_zeros_fromBE (k : Nat) (hk : FitsLen k) :
    Megadreifach.big_from_be (embed (List.replicate k 0)) =
      .ok (bigNat (fromBE (List.replicate k 0))) := by
  rw [fromBE_zeros, bigNat_zero]
  exact big_from_be_zeros k hk

/-- The 28-byte pad block of zeros. This is the integer `phi_chunk` reads for rank `0`. -/
theorem big_from_be_zero_pad :
    Megadreifach.big_from_be (embed (List.replicate 28 0)) = .ok (bigOf []) := by
  have hk : FitsLen 28 := by unfold FitsLen i64MaxNat; decide
  exact big_from_be_zeros 28 hk

end MegaDreifach.Link2
