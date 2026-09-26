/-
  LINK 2. `big_mul` of a one-limb left factor by a wide canonical limb list.

  This is the orientation `peel_leading` emits: `big_from_int` of the
  factoradic digit on the left, `big_factorial` on the right. The right
  factor may have any number of base-`10^9` limbs. Each cell
  `digit * q + carry` stays below `10^18`, so it fits in an i64. The
  single outer digit runs `scanMul`; `make_big` trims to `natLimbs`.

  Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.MulWide

namespace MegaDreifach.Link2

set_option maxHeartbeats 8000000

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem sum_limb_fits (x q c : Nat) (hx : x < limbBase) (hq : q < limbBase)
    (hc : c < limbBase) : FitsLen (x * q + c) := by
  have hx' : x ≤ limbBase - 1 := by omega
  have hq' : q ≤ limbBase - 1 := by omega
  have hc' : c ≤ limbBase - 1 := by omega
  have hmul : x * q ≤ (limbBase - 1) * (limbBase - 1) := Nat.mul_le_mul hx' hq'
  have hpair : (limbBase - 1) * (limbBase - 1) + (limbBase - 1) = (limbBase - 1) * limbBase := by
    calc
      (limbBase - 1) * (limbBase - 1) + (limbBase - 1)
        = (limbBase - 1) * (limbBase - 1) + (limbBase - 1) * 1 := by rw [Nat.mul_one]
      _ = (limbBase - 1) * ((limbBase - 1) + 1) := by rw [← Nat.mul_add]
      _ = (limbBase - 1) * limbBase := by
          have : (limbBase - 1) + 1 = limbBase := by omega
          rw [this]
  have hle : x * q + c ≤ (limbBase - 1) * limbBase := by omega
  have hlt : (limbBase - 1) * limbBase < limbBase ^ 2 := by
    rw [limbBase_pow2]
    exact Nat.mul_lt_mul_of_pos_right (by omega : limbBase - 1 < limbBase) limbBase_pos
  exact Nat.le_trans (Nat.le_of_lt (Nat.lt_of_le_of_lt hle hlt)) limb_sq_fits

private theorem match_ok_cont {σ ρ α} (s : σ)
    (onRet : ρ → Except SudoRt.Trap α)
    (onBrk onCont : σ → Except SudoRt.Trap α) :
    (match Except.ok (SudoRt.Flow.cont s) with
      | Except.error e => (Except.error e : Except SudoRt.Trap α)
      | Except.ok (SudoRt.Flow.ret r) => onRet r
      | Except.ok (SudoRt.Flow.brk s') => onBrk s'
      | Except.ok (SudoRt.Flow.cont s') => onCont s') = onCont s := by
  rfl

private theorem take_succ_limb (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    xs.take (j + 1) = xs.take j ++ [xs[j]] := by
  rw [List.take_succ]
  simp [List.getElem?_eq_getElem hj]

private theorem getElem_irrel (xs : List Nat) (i : Nat) (h1 h2 : i < xs.length) :
    xs[i]'h1 = xs[i]'h2 := by
  induction xs generalizing i with
  | nil => simp at h1
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp [List.getElem_cons_succ,
        ih i (Nat.lt_of_succ_lt_succ h1) (Nat.lt_of_succ_lt_succ h2)]

private theorem set_eq_val (xs : List Nat) (i v : Nat) {hi : i < xs.length}
    (h : xs[i] = v) : xs.set i v = xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getElem_cons_zero] at h ⊢
      simp [h]
    | succ i =>
      simp only [List.set_cons_succ, List.getElem_cons_succ] at h ⊢
      rw [ih i (hi := Nat.lt_of_succ_lt_succ hi) h]

private theorem kCarry_fun (toK : Int) :
    (fun σ : Int × (Array Int × Int) =>
      if σ.fst > toK then
        pure (SudoRt.Flow.brk (σ.fst, σ.snd.fst, σ.snd.snd))
      else do
        let liftK ←
          (if decide (σ.snd.snd > 0) = true then do
            let cur0 ← SudoRt.atL σ.snd.fst σ.fst
            let cur ← SudoRt.addI cur0 σ.snd.snd
            let digit ← SudoRt.modI cur Megadreifach.limb_base
            let out ← SudoRt.putL σ.snd.fst σ.fst digit
            let carry ← SudoRt.divI cur Megadreifach.limb_base
            pure (SudoRt.Flow.cont (out, carry))
          else
            pure (SudoRt.Flow.cont (σ.snd.fst, σ.snd.snd)))
        match liftK with
        | .ret r => pure (SudoRt.Flow.ret r)
        | .brk fs => pure (SudoRt.Flow.brk (σ.fst, fs))
        | .cont fs =>
          if (σ.fst == toK) = true then
            pure (SudoRt.Flow.brk (σ.fst, fs))
          else do
            let i' ← SudoRt.addI σ.fst 1
            pure (SudoRt.Flow.cont (i', fs))) =
      kCarryStep toK := by
  unfold kCarryStep
  rfl

/-- The buffer after the digit scan, before the final carry is stored. -/
private def scanBuf (q : Nat) (xs : List Nat) : List Nat :=
  padZero (scanMul q 0 xs).1 (1 + xs.length)

private theorem scanBuf_length (q : Nat) (xs : List Nat) :
    (scanBuf q xs).length = 1 + xs.length := by
  unfold scanBuf
  have hlen : (scanMul q 0 xs).1.length = xs.length := by rw [scanMul_length]
  exact padZero_length _ _ (by rw [hlen]; omega)

private theorem pad_at_len (ds : List Nat) (total i : Nat)
    (hlt : ds.length < total) (hi : i = ds.length) :
    (padZero ds total)[i]'(by
      rw [hi, padZero_length _ _ (Nat.le_of_lt hlt)]; exact hlt) = 0 := by
  subst hi
  exact padZero_get ds total hlt

private theorem scanBuf_high_zero (q : Nat) (xs : List Nat) (_hpos : 0 < xs.length) :
    (scanBuf q xs)[xs.length]'(by rw [scanBuf_length]; omega) = 0 := by
  unfold scanBuf
  have hlen : (scanMul q 0 xs).1.length = xs.length := by rw [scanMul_length]
  exact pad_at_len (scanMul q 0 xs).1 (1 + xs.length) xs.length
    (by rw [hlen]; omega) hlen.symm

private theorem scan_set_raw (q : Nat) (xs : List Nat) :
    (scanBuf q xs).set xs.length (scanMul q 0 xs).2 =
      (scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2] := by
  unfold scanBuf
  have hlen : (scanMul q 0 xs).1.length = xs.length := by rw [scanMul_length]
  have hset := padZero_set (scanMul q 0 xs).1 (1 + xs.length) (scanMul q 0 xs).2
    (by rw [hlen]; omega)
  rw [hlen] at hset
  rw [hset]
  have happ : ((scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]).length = 1 + xs.length := by
    rw [List.length_append, hlen, List.length_singleton]
    omega
  simp [padZero, happ, Nat.sub_self, List.replicate, List.append_nil]

/-- Park the final `scanMul` carry in the high limb. A zero carry is already there. -/
private theorem kFinish (xs out : List Nat) (c : Nat)
    (hc : c < limbBase) (hlen : out.length = 1 + xs.length)
    (h0 : out[xs.length]'(by rw [hlen]; omega) = 0)
    (hfits : FitsLen (xs.length + 1)) (hpos : 0 < xs.length) :
    ((do
      let k0 ← SudoRt.addI (0 : Int) (SudoRt.listLen (embed xs))
      let toK ← SudoRt.subI (SudoRt.listLen (embed out)) 1
      let kLoop ←
        SudoRt.runLoopOn (k0, embed out, Int.ofNat c)
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
      pure kLoop) :
        Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt)) =
      pure (SudoRt.Flow.cont (embed (out.set xs.length c))) := by
  have hlenB : SudoRt.listLen (embed xs) = Int.ofNat xs.length := listLen_embed xs
  have hfitK : FitsLen xs.length := FitsLen.of_le hfits (Nat.le_succ _)
  have hadd : SudoRt.addI (0 : Int) (Int.ofNat xs.length) = .ok (Int.ofNat xs.length) := by
    have : FitsLen (0 + xs.length) := by simpa using hfitK
    simpa [Nat.zero_add] using addI_ofNat 0 xs.length this
  rw [hlenB, hadd, ok_bind]
  have hposL : 0 < out.length := by omega
  have hlenE : SudoRt.listLen (embed out) = Int.ofNat out.length := listLen_embed out
  have hfitOut : FitsLen out.length := by rw [hlen]; simpa [Nat.add_comm] using hfits
  rw [hlenE, subI_ofNat_one out.length hposL hfitOut, ok_bind]
  have hto : out.length - 1 = xs.length := by omega
  rw [hto]
  have hfuel :
      (if (Int.ofNat xs.length) > (Int.ofNat xs.length) then 1
        else ((Int.ofNat xs.length) - (Int.ofNat xs.length)).natAbs + 1) =
        fuelRange (Int.ofNat xs.length) (Int.ofNat xs.length) :=
    fuelRange_eq _ _
  rw [hfuel, kCarry_fun (Int.ofNat xs.length)]
  have hafter :
      (fun σk : Int × (Array Int × Int) =>
        (pure (SudoRt.Flow.cont (ρ := Megadreifach.BigInt) σk.snd.fst) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt))) =
      (fun σk : Int × (Array Int × Int) =>
        (pure (SudoRt.Flow.cont σk.snd.fst) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt))) := rfl
  rw [← hafter]
  have hon :
      (fun r : Megadreifach.BigInt =>
        (pure (SudoRt.Flow.ret (ρ := Megadreifach.BigInt) r) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt))) =
      (fun r : Megadreifach.BigInt =>
        (pure (SudoRt.Flow.ret r) :
          Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt))) := rfl
  rw [← hon]
  have hIdx : xs.length < out.length := by rw [hlen]; omega
  by_cases hc0 : c = 0
  · subst hc0
    rw [except_bind_pure]
    erw [kLoop_idle out xs.length xs.length (Nat.le_refl _) (by simpa [Nat.add_comm] using hfits)]
    rw [set_eq_val out xs.length 0 h0]
  · have hposC : 0 < c := Nat.pos_of_ne_zero hc0
    rw [except_bind_pure]
    erw [kLoop_write out xs.length xs.length c (Nat.le_refl _) hposC hc hIdx h0
      (by simpa [Nat.add_comm] using hfits)]

private theorem jCarry (q : Nat) (xs : List Nat) (j : Nat) (_hj : j ≤ xs.length)
    (hq : q < limbBase) (hxs : ∀ d ∈ xs, d < limbBase) :
    (scanMul q 0 (xs.take j)).2 < limbBase :=
  (scanMul_bounds q 0 hq limbBase_pos (xs.take j)
    (fun d hd => hxs d (List.mem_of_mem_take hd))).2

private theorem jBuf_len (q : Nat) (xs : List Nat) (j : Nat) (hj : j ≤ xs.length) :
    (padZero (scanMul q 0 (xs.take j)).1 (1 + xs.length)).length = 1 + xs.length := by
  have hlen : (scanMul q 0 (xs.take j)).1.length = j := by
    rw [scanMul_length, List.length_take, Nat.min_eq_left hj]
  exact padZero_length _ _ (by omega)

private theorem jBuf_zero (q : Nat) (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    (padZero (scanMul q 0 (xs.take j)).1 (1 + xs.length))[j]'
      (by rw [jBuf_len q xs j (Nat.le_of_lt hj)]; omega) = 0 := by
  have hlen : (scanMul q 0 (xs.take j)).1.length = j := by
    rw [scanMul_length, List.length_take]; omega
  exact pad_at_len (scanMul q 0 (xs.take j)).1 (1 + xs.length) j
    (by rw [hlen]; omega) hlen.symm

private theorem jSt_succ (q : Nat) (xs : List Nat) (j : Nat)
    (hj : j < xs.length) :
    (embed ((padZero (scanMul q 0 (xs.take j)).1 (1 + xs.length)).set j
        ((xs[j] * q + (scanMul q 0 (xs.take j)).2) % limbBase)),
      Int.ofNat ((xs[j] * q + (scanMul q 0 (xs.take j)).2) / limbBase)) =
      jSt q xs (j + 1) := by
  unfold jSt
  rw [take_succ_limb xs j hj, scanMul_snoc]
  dsimp
  have hlen : (scanMul q 0 (xs.take j)).1.length = j := by
    rw [scanMul_length, List.length_take]; omega
  have hset := padZero_set (scanMul q 0 (xs.take j)).1 (1 + xs.length)
    ((xs[j] * q + (scanMul q 0 (xs.take j)).2) % limbBase) (by rw [hlen]; omega)
  rw [hlen] at hset
  rw [hset]

/-- One inner digit of a one-limb-left multiply. -/
private theorem mulJ_at (q : Nat) (xs : List Nat) (j : Nat)
    (hj : j < xs.length) (hq : q < limbBase)
    (hxs : ∀ d ∈ xs, d < limbBase) (hfits : FitsLen (xs.length + 1)) :
    mulJStep (bigOf [q]) (bigOf xs) (0 : Int) (Int.ofNat (xs.length - 1))
        (Int.ofNat j, jSt q xs j) =
      if j = xs.length - 1 then
        .ok (SudoRt.Flow.brk (Int.ofNat j, jSt q xs (j + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (j + 1), jSt q xs (j + 1))) := by
  have hto : j ≤ xs.length - 1 := by omega
  have hngt : ¬ ((j : Int) > ((xs.length - 1 : Nat) : Int)) := by omega
  let s := scanMul q 0 (xs.take j)
  let buf := padZero s.1 (1 + xs.length)
  have hc : s.2 < limbBase := jCarry q xs j (Nat.le_of_lt hj) hq hxs
  have hx : xs[j] < limbBase := hxs _ (List.getElem_mem hj)
  have hlenB : j < buf.length := by
    rw [show buf.length = 1 + xs.length from jBuf_len q xs j (Nat.le_of_lt hj)]
    omega
  have h0 : buf[j] = 0 := jBuf_zero q xs j hj
  have hfitj : FitsLen (j + 1) :=
    FitsLen.of_le hfits (by omega)
  unfold mulJStep
  dsimp [bigOf]
  rw [if_neg hngt]
  dsimp [jSt]
  have hsum := sum_limb_fits (xs[j]) q s.2 hx hq hc
  have hprod : FitsLen (q * xs[j]) := by
    simpa [Nat.mul_comm] using FitsLen.of_le hsum (Nat.le_add_right _ _)
  have hsumq : FitsLen (q * xs[j] + s.2) := by simpa [Nat.mul_comm] using hsum
  have hadd0 : SudoRt.addI (0 : Int) (Int.ofNat j) = .ok (Int.ofNat j) := by
    have : FitsLen (0 + j) := by simpa using FitsLen.of_le hfitj (Nat.le_succ _)
    simpa [Nat.zero_add] using addI_ofNat 0 j this
  erw [hadd0]
  simp only [ok_bind]
  have hat0 :
      SudoRt.atL (embed (padZero (scanMul q 0 (xs.take j)).1 (1 + xs.length)))
          (Int.ofNat j) = .ok (0 : Int) := by
    have hbuf : padZero (scanMul q 0 (xs.take j)).1 (1 + xs.length) = buf := rfl
    rw [hbuf, atL_embed buf j hlenB, h0]
    rfl
  erw [hat0]
  simp only [ok_bind]
  have haj : 0 < ([q] : List Nat).length := by simp
  erw [atL_embed [q] 0 haj]
  simp only [ok_bind, List.getElem_cons_zero]
  erw [atL_embed xs j hj]
  simp only [ok_bind]
  erw [mulI_ofNat q (xs[j]) hprod]
  simp only [ok_bind]
  have hprod0 : FitsLen (0 + q * xs[j]) := by simpa [Nat.zero_add] using hprod
  erw [addI_ofNat 0 (q * xs[j]) hprod0, Nat.zero_add]
  simp only [ok_bind]
  have hcur : SudoRt.addI (Int.ofNat (q * xs[j])) (Int.ofNat s.2) =
      .ok (Int.ofNat (q * xs[j] + s.2)) := addI_ofNat (q * xs[j]) s.2 hsumq
  erw [hcur]
  simp only [ok_bind]
  erw [modI_ofNat (q * xs[j] + s.2) (Nat.ne_of_gt limbBase_pos)]
  simp only [ok_bind]
  have hidx : j < (embed (padZero (scanMul q 0 (xs.take j)).1 (1 + xs.length))).size := by
    rw [size_embed]; exact hlenB
  erw [putL_ofNat (embed (padZero (scanMul q 0 (xs.take j)).1 (1 + xs.length))) j
    (Int.ofNat ((q * xs[j] + s.2) % limbBase)) hidx]
  simp only [ok_bind]
  erw [divI_ofNat (q * xs[j] + s.2) (Nat.ne_of_gt limbBase_pos)]
  simp only [ok_bind]
  have hcomm : q * xs[j] = xs[j] * q := Nat.mul_comm _ _
  erw [hcomm]
  erw [embed_set_nat buf j ((xs[j] * q + s.2) % limbBase) hlenB]
  simp only [pure_eq_ok, ok_bind]
  erw [jSt_succ q xs j hj]
  by_cases heq : j = xs.length - 1
  · simp [heq, beq_int_iff, pure_eq_ok]
    subst heq
    unfold jSt
    rfl
  · have hneI : (j : Int) ≠ ((xs.length - 1 : Nat) : Int) :=
      fun h => heq (Int.ofNat.inj h)
    have hbeq : ((j : Int) == ((xs.length - 1 : Nat) : Int)) = false := by
      simpa [beq_int_iff] using hneI
    simp only [hbeq, heq, pure_eq_ok]
    have hadd := addI_ofNat_one j hfitj
    erw [hadd]
    rw [ok_bind]
    rfl

private theorem raw_of_scan (q : Nat) (xs : List Nat) :
    (scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2] =
      (scanBuf q xs).set xs.length (scanMul q 0 xs).2 :=
  (scan_set_raw q xs).symm

/-- Carry propagation after the single left-hand digit. Captures the outer index. -/
private def kAfter (limbs : Array Int) (i : Int) (σ1 : Int × (Array Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int) Megadreifach.BigInt) :=
  do
    let k0 ← SudoRt.addI i (SudoRt.listLen limbs)
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
    pure kLoop

private theorem kAfter_finish (q : Nat) (xs : List Nat)
    (hq : q < limbBase) (hxs : ∀ d ∈ xs, d < limbBase) (hpos : 0 < xs.length)
    (hfits : FitsLen (xs.length + 1)) :
    kAfter (embed xs) (0 : Int)
        (Int.ofNat (xs.length - 1), jSt q xs xs.length) =
      .ok (SudoRt.Flow.cont
        (embed ((scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]))) := by
  have hfull : xs.take xs.length = xs := List.take_length xs
  have hc : (scanMul q 0 xs).2 < limbBase := by
    have h := jCarry q xs xs.length (Nat.le_refl _) hq hxs
    simpa [hfull] using h
  have hst : jSt q xs xs.length =
      (embed (scanBuf q xs), Int.ofNat (scanMul q 0 xs).2) := by
    simp [jSt, scanBuf, hfull]
  rw [hst]
  unfold kAfter
  dsimp
  have h0 := scanBuf_high_zero q xs hpos
  have hlenS := scanBuf_length q xs
  have hk := kFinish xs (scanBuf q xs) (scanMul q 0 xs).2 hc hlenS h0 hfits hpos
  refine Eq.trans hk ?_
  rw [scan_set_raw, pure_eq_ok]

private theorem jLoop_ok (q : Nat) (xs : List Nat)
    (hq : q < limbBase) (hxs : ∀ d ∈ xs, d < limbBase)
    (hfits : FitsLen (xs.length + 1)) (hpos : 0 < xs.length) :
    SudoRt.runLoopOn (Int.ofNat 0, jSt q xs 0)
      (fuelRange (Int.ofNat 0) (Int.ofNat (xs.length - 1)))
      (mulJStep (bigOf [q]) (bigOf xs) (0 : Int) (Int.ofNat (xs.length - 1)))
      (kAfter (embed xs) (0 : Int))
      (fun r => pure (SudoRt.Flow.ret r)) =
      .ok (SudoRt.Flow.cont
        (embed ((scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]))) := by
  apply chain_loop
    (f := fun i => jSt q xs i)
    (fromN := 0) (toN := xs.length - 1)
    (hle := Nat.zero_le _)
    (goal := .ok (SudoRt.Flow.cont
      (embed ((scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]))))
  · intro i _ hi2
    have hi : i < xs.length := by omega
    simpa using mulJ_at q xs i hi hq hxs hfits
  · have hlen1 : (xs.length - 1) + 1 = xs.length := by omega
    rw [hlen1]
    exact kAfter_finish q xs hq hxs hpos hfits

private theorem mulJ_fun (q : Nat) (xs : List Nat) :
    (fun σ1 : Int × (Array Int × Int) =>
      if σ1.fst > Int.ofNat (xs.length - 1) then
        pure (SudoRt.Flow.brk (σ1.fst, σ1.snd.fst, σ1.snd.snd))
      else
        mulJStep (bigOf [q]) (bigOf xs) (0 : Int) (Int.ofNat (xs.length - 1)) σ1) =
      mulJStep (bigOf [q]) (bigOf xs) (0 : Int) (Int.ofNat (xs.length - 1)) := by
  funext σ1
  unfold mulJStep
  split
  · rfl
  · rfl

/-- The schoolbook body for a positive one-limb left factor. -/
private theorem mulSchool_left (q : Nat) (xs : List Nat)
    (_hq0 : 0 < q) (hq : q < limbBase) (hne : xs ≠ [])
    (hxs : ∀ d ∈ xs, d < limbBase) (hfits : FitsLen (xs.length + 1)) :
    mulSchoolStep (bigOf [q]) (bigOf xs) 0
        ((0 : Int), embed (List.replicate (1 + xs.length) 0)) =
      .ok (SudoRt.Flow.brk
        ((0 : Int), embed ((scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]))) := by
  have hpos : 0 < xs.length :=
    Nat.pos_of_ne_zero (fun h => hne (List.eq_nil_of_length_eq_zero h))
  have hngt : ¬ ((0 : Int) > (0 : Int)) := by decide
  unfold mulSchoolStep
  rw [if_neg hngt]
  dsimp [bigOf]
  have hlenB : SudoRt.listLen (embed xs) = Int.ofNat xs.length := listLen_embed xs
  conv =>
    lhs
    pattern SudoRt.subI (SudoRt.listLen (embed xs)) (1 : Int)
    rw [hlenB]
  rw [subI_ofNat_one xs.length hpos (FitsLen.of_le hfits (Nat.le_succ _)), ok_bind]
  have hfuel :
      (if (0 : Int) > Int.ofNat (xs.length - 1) then 1
        else (Int.ofNat (xs.length - 1) - (0 : Int)).natAbs + 1) =
        fuelRange (Int.ofNat 0) (Int.ofNat (xs.length - 1)) := by
    simpa using (fuelRange_eq (Int.ofNat 0) (Int.ofNat (xs.length - 1))).symm
  rw [hfuel]
  have hstart :
      ((0 : Int), embed (List.replicate (1 + xs.length) 0), (0 : Int)) =
        (Int.ofNat 0, jSt q xs 0) := by
    rw [jSt_zero]
    rfl
  rw [hstart]
  conv =>
    lhs
    arg 1
    arg 1
    arg 3
    change mulJStep (bigOf [q]) (bigOf xs) (0 : Int) (Int.ofNat (xs.length - 1))
  conv =>
    lhs
    arg 1
    arg 1
    arg 4
    change kAfter (embed xs) (0 : Int)
  rw [jLoop_ok q xs hq hxs hfits hpos]
  simp only [pure_eq_ok, ok_bind, beq_int_iff]

/--
  `big_mul` of one limb `q` on the left by a canonical digit string on the
  right is `natLimbs (q * value)`.

  The right factor is the wide one (`peel_leading`'s factorial). Not the
  accumulator-on-the-left product. Not `v_Hash`.
-/
theorem big_mul_left_refines (q : Nat) (xs : List Nat)
    (hq : q < limbBase) (hxs : ∀ d ∈ xs, d < limbBase)
    (hfits : FitsLen (xs.length + 1)) :
    Megadreifach.big_mul (bigOf (natLimbs q)) (bigOf xs) =
      .ok (bigOf (natLimbs (q * limbVal xs))) := by
  by_cases hq0 : q = 0
  · simp [hq0, natLimbs_zero, Nat.zero_mul, big_mul_zero_left]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    rw [natLimbs_of_pos_lt q hqpos hq]
    by_cases hnil : xs = []
    · simp [hnil, limbVal, Nat.mul_zero, natLimbs_zero, big_mul_zero_right]
    · rw [big_mul_left_loop q xs hqpos hq hnil hfits]
      rw [show (1 : Nat) = 0 + 1 from rfl, runLoopOn_succ]
      have hstep := mulSchool_left q xs hqpos hq hnil hxs hfits
      rw [hstep]
      dsimp
      rw [except_bind_pure]
      have hrawLen :
          ((scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]).length = xs.length + 1 := by
        rw [List.length_append, scanMul_length, List.length_singleton]
      have hfitRaw : FitsLen
          ((scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]).length := by
        rw [hrawLen]; exact hfits
      rw [make_big_false _ hfitRaw, scan_raw_trim q xs hq hxs]

/-- Same product on the canonical limbs of a natural number. -/
theorem big_mul_left_nat (q n : Nat) (hq : q < limbBase)
    (hfits : FitsLen ((natLimbs n).length + 1)) :
    Megadreifach.big_mul (bigOf (natLimbs q)) (bigOf (natLimbs n)) =
      .ok (bigOf (natLimbs (q * n))) := by
  simpa [limbVal_natLimbs] using
    big_mul_left_refines q (natLimbs n) hq (natLimbs_digits n) hfits

end MegaDreifach.Link2

