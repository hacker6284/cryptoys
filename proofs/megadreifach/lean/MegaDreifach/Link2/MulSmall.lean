/-
  LINK 2. `big_mul` of a one-limb factor and a canonical limb list.

  Both orientations. The product of two base-`10^9` digits fits in an i64,
  and the running carry stays below one limb, so the length is not capped
  at three. Used for `n!` through `51!` and for Horner `* 256`.

  Not `v_Hash`. Not emitter soundness.
-/
import MegaDreifach.Link2.NatLimbs
import MegaDreifach.Link2.PackOri

namespace MegaDreifach.Link2

def padZero (ds : List Nat) (total : Nat) : List Nat :=
  ds ++ List.replicate (total - ds.length) 0

theorem padZero_length (ds : List Nat) (total : Nat) (h : ds.length ≤ total) :
    (padZero ds total).length = total := by
  simp [padZero, List.length_append, List.length_replicate, Nat.add_sub_of_le h]

theorem replicate_set_zero (k v : Nat) (hk : 0 < k) :
    (List.replicate k 0).set 0 v = v :: List.replicate (k - 1) 0 := by
  cases k with
  | zero => omega
  | succ k => simp [List.replicate_succ, List.set_cons_zero]

theorem padZero_set (ds : List Nat) (total v : Nat) (h : ds.length < total) :
    (padZero ds total).set ds.length v = padZero (ds ++ [v]) total := by
  unfold padZero
  rw [List.set_append]
  have hlt : ¬ ds.length < ds.length := Nat.lt_irrefl _
  simp only [hlt, ite_false, Nat.sub_self]
  rw [replicate_set_zero (total - ds.length) v (by omega)]
  have hsub : total - ds.length - 1 = total - (ds.length + 1) := by omega
  rw [hsub]
  simp [List.length_append, List.length_singleton, List.append_assoc]

theorem padZero_get (ds : List Nat) (total : Nat) (h : ds.length < total) :
    (padZero ds total)[ds.length]'(by
      rw [padZero_length _ _ (Nat.le_of_lt h)]; exact h) = 0 := by
  unfold padZero
  rw [List.getElem_append_right (by omega)]
  have h0 : ds.length - ds.length = 0 := Nat.sub_self _
  have hk : 0 < total - ds.length := by omega
  simp [h0, List.getElem_replicate]

theorem embed_set_nat (xs : List Nat) (i v : Nat) (h : i < xs.length) :
    (embed xs).set ⟨i, by rw [size_embed]; exact h⟩ (Int.ofNat v) =
      embed (xs.set i v) := by
  apply Array.ext'
  simp [embed, Array.toList_set, h]

theorem embed_replicate_zero (n : Nat) :
    Array.mkArray n (0 : Int) = embed (List.replicate n 0) := by
  apply Array.ext'
  simp [embed, Array.toList_mkArray, List.map_replicate]

theorem scanMul_snoc (q c : Nat) (ys : List Nat) (x : Nat) :
    scanMul q c (ys ++ [x]) =
      ((scanMul q c ys).1 ++ [(x * q + (scanMul q c ys).2) % limbBase],
        (x * q + (scanMul q c ys).2) / limbBase) := by
  induction ys generalizing c with
  | nil => simp [scanMul]
  | cons y ys ih =>
    simp only [List.cons_append, scanMul]
    have happ : ys.append [x] = ys ++ [x] := rfl
    rw [happ, ih ((y * q + c) / limbBase)]

/-- `dropTrail (digits ++ [carry])` is the canonical limb list of `q * value`. -/
theorem scan_raw_trim (q : Nat) (xs : List Nat) (hq : q < limbBase)
    (hxs : ∀ d ∈ xs, d < limbBase) :
    dropTrail ((scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]) = natLimbs (q * limbVal xs) := by
  have hc0 : (0 : Nat) < limbBase := limbBase_pos
  obtain ⟨hds, hr⟩ := scanMul_bounds q 0 hq hc0 xs hxs
  have hval := scanMul_val q 0 xs
  simp only [Nat.add_zero] at hval
  let raw := (scanMul q 0 xs).1 ++ [(scanMul q 0 xs).2]
  have hdig : ∀ d ∈ raw, d < limbBase := by
    intro d hd
    simp [raw, List.mem_append, List.mem_singleton] at hd
    cases hd with
    | inl h => exact hds d h
    | inr h =>
      subst h
      exact hr
  have hmem : ∀ d ∈ dropTrail raw, d < limbBase :=
    fun d hd => hdig d (mem_dropTrail raw hd)
  have htr : dropTrail (dropTrail raw) = dropTrail raw := dropTrail_idem raw
  have heq := trimmed_eq_natLimbs (dropTrail raw) hmem htr
  have hv : limbVal (dropTrail raw) = q * limbVal xs := by
    rw [limbVal_dropTrail, hval]
  rw [hv] at heq
  simpa [raw] using heq


def mulSchoolStep (a b : Megadreifach.BigInt) (toV : Int) (σ : Int × Array Int) :
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

theorem big_mul_zero_right (xs : List Nat) :
    Megadreifach.big_mul (bigOf xs) (bigOf []) = .ok (bigOf []) := by
  by_cases h0 : xs = []
  · simp [h0, big_mul_zero_left]
  · unfold Megadreifach.big_mul
    dsimp [bigOf]
    have hlenA : SudoRt.listLen (embed xs) = Int.ofNat xs.length := listLen_embed xs
    have hpos : xs.length ≠ 0 := by
      intro h
      exact h0 (List.eq_nil_of_length_eq_zero h)
    rw [hlenA, sEq_ofNat_zero, decide_eq_false_iff_not.mpr hpos]
    dsimp
    have hlenB : SudoRt.listLen (embed ([] : List Nat)) = (0 : Int) := by
      rw [listLen_embed, List.length_nil]; rfl
    rw [hlenB]
    have hb : SudoRt.SEq.beq (0 : Int) (0 : Int) = true := by simp [sEq_int]
    rw [hb]
    rw [show (pure true : Except SudoRt.Trap Bool) = .ok true from rfl, ok_bind,
      if_pos rfl, big_zero_spec, except_bind_pure]
    rfl

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

/-- Expose the emitted schoolbook loop for a positive one-limb left factor. -/
theorem big_mul_left_loop (q : Nat) (xs : List Nat) (hq0 : 0 < q) (hq : q < limbBase)
    (hne : xs ≠ []) (hfits : FitsLen (xs.length + 1)) :
    Megadreifach.big_mul (bigOf [q]) (bigOf xs) =
      SudoRt.runLoopOn ((0 : Int), embed (List.replicate (1 + xs.length) 0))
        1 (mulSchoolStep (bigOf [q]) (bigOf xs) 0)
        (fun σ => do
          let t ← Megadreifach.make_big false σ.2
          pure t)
        (fun r => pure r) := by
  have hlen1 : SudoRt.listLen (embed [q]) = (1 : Int) := by rw [listLen_embed]; rfl
  have hlenB : SudoRt.listLen (embed xs) = Int.ofNat xs.length := listLen_embed xs
  have hposL : xs.length ≠ 0 := fun h => hne (List.eq_nil_of_length_eq_zero h)
  have hadd : FitsLen (1 + xs.length) := by simpa [Nat.add_comm] using hfits
  unfold Megadreifach.big_mul
  dsimp [bigOf]
  rw [hlen1]
  have hbeq : SudoRt.SEq.beq (1 : Int) (0 : Int) = false := by simp [sEq_int]
  rw [hbeq]
  dsimp
  conv =>
    pattern SudoRt.SEq.beq (SudoRt.listLen (embed xs)) _
    rw [hlenB]
  rw [sEq_ofNat_zero, decide_eq_false_iff_not.mpr hposL]
  rw [show (pure false : Except SudoRt.Trap Bool) = .ok false from rfl, ok_bind,
    if_neg (by decide : ¬ ((false : Bool) = true))]
  conv =>
    pattern SudoRt.addI _ (SudoRt.listLen (embed xs))
    rw [hlenB]
  have hAI : SudoRt.addI (1 : Int) (Int.ofNat xs.length) =
      .ok (Int.ofNat (1 + xs.length)) := addI_cast 1 xs.length hadd
  conv =>
    pattern SudoRt.addI 1 (Int.ofNat xs.length)
    rw [hAI]
  rw [ok_bind]
  rw [filledL_ofNat (1 + xs.length) (0 : Int), ok_bind, embed_replicate_zero]
  have hsub : SudoRt.subI 1 1 = .ok (0 : Int) := by
    erw [subI_ofNat_one 1 (by decide) FitsLen.one]
    rfl
  conv =>
    pattern SudoRt.subI 1 1
    rw [hsub]
  rw [ok_bind]
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := mulSchoolStep (bigOf [q]) (bigOf xs) 0)
    intro σ
    unfold mulSchoolStep
    dsimp [bigOf]
    rfl
  rfl

private theorem take_succ_limb (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    xs.take (j + 1) = xs.take j ++ [xs[j]] := by
  rw [List.take_succ]
  simp [List.getElem?_eq_getElem hj]

/-- One schoolbook digit of `big_mul` when the left factor is the single limb `q`
    and position `j` of the accumulator is still zero. -/
private theorem jDigit (q x c : Nat) (out : List Nat) (j : Nat)
    (hj : j < out.length) (h0 : out[j] = 0)
    (hx : x < limbBase) (hq : q < limbBase) (hc : c < limbBase)
    (hfits : FitsLen (j + 1)) :
    (do
      let ij ← SudoRt.addI (0 : Int) (Int.ofNat j)
      let cur0 ← SudoRt.atL (embed out) ij
      let ai ← SudoRt.atL (embed [q]) (0 : Int)
      let bj ← SudoRt.atL (embed [x]) (0 : Int)
      let prod ← SudoRt.mulI ai bj
      let s1 ← SudoRt.addI cur0 prod
      let cur ← SudoRt.addI s1 (Int.ofNat c)
      let ij2 ← SudoRt.addI (0 : Int) (Int.ofNat j)
      let digit ← SudoRt.modI cur Megadreifach.limb_base
      let out ← SudoRt.putL (embed out) ij2 digit
      let carry ← SudoRt.divI cur Megadreifach.limb_base
      pure (out, carry)) =
      .ok (embed (out.set j ((x * q + c) % limbBase)),
        Int.ofNat ((x * q + c) / limbBase)) := by
  have hsum := sum_limb_fits x q c hx hq hc
  have hprod : FitsLen (q * x) := by simpa [Nat.mul_comm] using FitsLen.of_le hsum (Nat.le_add_right _ _)
  have hsumq : FitsLen (q * x + c) := by simpa [Nat.mul_comm] using hsum
  have hidx : j < (embed out).size := by rw [size_embed]; exact hj
  have hat0 : SudoRt.atL (embed out) (Int.ofNat j) = .ok (0 : Int) := by
    rw [atL_embed out j hj, h0]
    rfl
  have haj : 0 < ([q] : List Nat).length := by simp
  have hbj : 0 < ([x] : List Nat).length := by simp
  have hadd0 : SudoRt.addI (0 : Int) (Int.ofNat j) = .ok (Int.ofNat j) := by
    have : FitsLen (0 + j) := by simpa using FitsLen.of_le hfits (Nat.le_succ j)
    simpa [Nat.zero_add] using addI_ofNat 0 j this
  rw [hadd0, ok_bind, hat0, ok_bind]
  erw [atL_embed [q] 0 haj, ok_bind, atL_embed [x] 0 hbj, ok_bind]
  simp only [List.getElem_cons_zero]
  rw [mulI_ofNat q x hprod, ok_bind]
  have hprod0 : FitsLen (0 + q * x) := by simpa [Nat.zero_add] using hprod
  erw [addI_ofNat 0 (q * x) hprod0, Nat.zero_add, ok_bind]
  have hcur : SudoRt.addI (Int.ofNat (q * x)) (Int.ofNat c) =
      .ok (Int.ofNat (q * x + c)) := addI_ofNat (q * x) c hsumq
  conv =>
    pattern SudoRt.addI (Int.ofNat (q * x)) (Int.ofNat c)
    rw [hcur]
  rw [ok_bind, ok_bind]
  erw [modI_ofNat (q * x + c) (Nat.ne_of_gt limbBase_pos), ok_bind]
  erw [putL_ofNat (embed out) j (Int.ofNat ((q * x + c) % limbBase)) hidx, ok_bind]
  erw [divI_ofNat (q * x + c) (Nat.ne_of_gt limbBase_pos), ok_bind]
  rw [embed_set_nat out j ((q * x + c) % limbBase) hj, Nat.mul_comm q x]
  rfl

private theorem jDigitAt (q : Nat) (xs out : List Nat) (j c : Nat)
    (hj : j < out.length) (hjx : j < xs.length) (h0 : out[j] = 0)
    (hx : xs[j] < limbBase) (hq : q < limbBase) (hc : c < limbBase)
    (hfits : FitsLen (j + 1)) :
    (do
      let ij ← SudoRt.addI (0 : Int) (Int.ofNat j)
      let cur0 ← SudoRt.atL (embed out) ij
      let ai ← SudoRt.atL (embed [q]) (0 : Int)
      let bj ← SudoRt.atL (embed xs) (Int.ofNat j)
      let prod ← SudoRt.mulI ai bj
      let s1 ← SudoRt.addI cur0 prod
      let cur ← SudoRt.addI s1 (Int.ofNat c)
      let ij2 ← SudoRt.addI (0 : Int) (Int.ofNat j)
      let digit ← SudoRt.modI cur Megadreifach.limb_base
      let out ← SudoRt.putL (embed out) ij2 digit
      let carry ← SudoRt.divI cur Megadreifach.limb_base
      pure (out, carry)) =
      .ok (embed (out.set j ((xs[j] * q + c) % limbBase)),
        Int.ofNat ((xs[j] * q + c) / limbBase)) := by
  have hat : SudoRt.atL (embed xs) (Int.ofNat j) =
      SudoRt.atL (embed [xs[j]]) (0 : Int) := by
    erw [atL_embed xs j hjx, atL_embed [xs[j]] 0 (by simp)]
    rfl
  -- The index `ij` is `j`, so the read of `xs` is the head of `[xs[j]]`.
  have hbody := jDigit q (xs[j]) c out j hj h0 hx hq hc hfits
  -- Replace the singleton read by the `xs` read inside `jDigit`'s script.
  conv at hbody =>
    lhs
    pattern SudoRt.atL (embed [xs[j]]) (0 : Int)
    rw [← hat]
  -- `jDigit` reads with literal `0`, while this loop reuses `ij`.
  -- Both are `j` after the first `addI`, so unfold that equality by `jDigit`'s proof shape:
  exact hbody

/-- Accumulator after consuming the first `j` limbs of a small-left multiply. -/
private def jSt (q : Nat) (xs : List Nat) (j : Nat) : Array Int × Int :=
  let s := scanMul q 0 (xs.take j)
  (embed (padZero s.1 (1 + xs.length)), Int.ofNat s.2)

private theorem jSt_zero (q : Nat) (xs : List Nat) :
    jSt q xs 0 = (embed (List.replicate (1 + xs.length) 0), (0 : Int)) := by
  simp [jSt, scanMul, padZero, List.replicate_succ, Nat.add_comm]

private def mulJStep (a b : Megadreifach.BigInt) (i toJ : Int)
    (σ1 : Int × (Array Int × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Array Int × Int)) Megadreifach.BigInt) :=
  if σ1.fst > toJ then
    pure (SudoRt.Flow.brk (σ1.fst, σ1.snd.fst, σ1.snd.snd))
  else do
    let liftJ ←
      (do
        let ij ← SudoRt.addI i σ1.fst
        let cur0 ← SudoRt.atL σ1.snd.fst ij
        let ai ← SudoRt.atL a.sudo_6BigInt_5limbs i
        let bj ← SudoRt.atL b.sudo_6BigInt_5limbs σ1.fst
        let prod ← SudoRt.mulI ai bj
        let s1 ← SudoRt.addI cur0 prod
        let cur ← SudoRt.addI s1 σ1.snd.snd
        let ij2 ← SudoRt.addI i σ1.fst
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
        pure (SudoRt.Flow.cont (i', fs))

end MegaDreifach.Link2
