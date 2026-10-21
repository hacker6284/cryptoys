/-
  `fold` and `fold_key` on the four shipped tiers. The two loops are
  `Spec.foldKey`: each source row is added into the destination row in
  GF(3), reading the original across, and the result is the
  `keeprows * w` prefix. Moves on the board `fold_key` returns are the
  incoming count plus one per nonzero cell that row drops. Demo is
  unconditional. The fold does not invert, so `FieldOk` is not a
  hypothesis. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.OpenBoard
import EcbsLink2.Link2.FoldKey

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

private theorem withMoves_eq (b : Ecbs.Board) (m : Int) :
    (withMoves b m).sudo_5Board_4cost.sudo_5Costs_5moves = m := by
  unfold withMoves
  rfl

private theorem withMoves_withMoves (b : Ecbs.Board) (m₁ m₂ : Int) :
    withMoves (withMoves b m₁) m₂ = withMoves b m₂ := by
  unfold withMoves
  rfl

private theorem withMoves_id (b : Ecbs.Board) {m : Int}
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = m) :
    withMoves b m = b := by
  rw [← hm]
  unfold withMoves
  rfl

private theorem set_irrel {α : Type} (a : Array α) (i : Nat) (h₁ h₂ : i < a.size) (v : α) :
    a.set ⟨i, h₁⟩ v = a.set ⟨i, h₂⟩ v := by
  have : (⟨i, h₁⟩ : Fin a.size) = ⟨i, h₂⟩ := Fin.ext rfl
  simp [this]

private theorem trits_of_all (xs : List Nat) (h : allTritList xs) :
    ∀ i (hi : i < xs.length), xs[i] ≤ 2 := by
  intro i hi
  exact h _ (List.getElem_mem hi)

private theorem getD_of (xs : List Nat) (i : Nat) (hi : i < xs.length) :
    xs.getD i 0 = xs[i] := by
  simp [List.getD, hi]

def colBump (w : Nat) (x : List Nat) (src c : Nat) : Nat :=
  if h : src * w + c < x.length then
    if x[src * w + c] = 0 then 0 else 1
  else
    0

private theorem colBump_le (w : Nat) (x : List Nat) (src c : Nat) : colBump w x src c ≤ 1 := by
  unfold colBump
  split
  · split <;> decide
  · decide

def foldBumpAt (w : Nat) (x : List Nat) (src : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => foldBumpAt w x src k + colBump w x src k

private theorem foldBumpAt_le (w : Nat) (x : List Nat) (src c : Nat) :
    foldBumpAt w x src c ≤ c := by
  induction c with
  | zero => simp [foldBumpAt]
  | succ c ih =>
    rw [foldBumpAt]
    have := colBump_le w x src c
    omega

def foldColAt (w : Nat) (x : List Nat) (src dst : Nat) (out : List Nat) : Nat → List Nat
  | 0 => out
  | k + 1 => dropCol w x src dst k (foldColAt w x src dst out k)

private theorem foldColAt_eq_aux (w src dst k : Nat) (x out : List Nat) :
    foldColAt w x src dst out k =
      (List.range k).foldl (fun o c => dropCol w x src dst c o) out := by
  induction k generalizing out with
  | zero => simp [foldColAt]
  | succ k ih =>
    rw [foldColAt, List.range_succ, List.foldl_append, ih]
    simp [List.foldl_cons, List.foldl_nil]

private theorem foldColAt_eq (w src dst : Nat) (x out : List Nat) :
    foldColAt w x src dst out w =
      (List.range w).foldl (fun o c => dropCol w x src dst c o) out :=
  foldColAt_eq_aux w src dst w x out

private theorem foldColAt_row (w src dst : Nat) (x out : List Nat) :
    foldColAt w x src dst out w = dropRow w x src dst out := by
  rw [foldColAt_eq]
  rfl

def foldBumpRows (w : Nat) (x srcs : List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => foldBumpRows w x srcs k + foldBumpAt w x (srcs.getD k 0) w

private theorem foldBumpRows_le (w : Nat) (x srcs : List Nat) (k : Nat) :
    foldBumpRows w x srcs k ≤ k * w := by
  induction k with
  | zero => simp [foldBumpRows]
  | succ k ih =>
    rw [foldBumpRows, Nat.succ_mul]
    have := foldBumpAt_le w x (srcs.getD k 0) w
    omega

def foldPairAt (w : Nat) (x srcs dsts : List Nat) : Nat → List Nat
  | 0 => x
  | k + 1 => dropRow w x (srcs.getD k 0) (dsts.getD k 0) (foldPairAt w x srcs dsts k)

private theorem foldPairAt_rows (w : Nat) (x srcs dsts : List Nat) (k : Nat)
    (hk : k ≤ srcs.length) (hlen : srcs.length = dsts.length) :
    foldPairAt w x srcs dsts k = foldRows w x ((srcs.zip dsts).take k) := by
  induction k generalizing x with
  | zero => simp [foldPairAt, foldRows]
  | succ k ih =>
    have hk' : k < srcs.length := by omega
    have hk2 : k < dsts.length := by rw [← hlen]; exact hk'
    have htake : (srcs.zip dsts).take (k + 1) =
        (srcs.zip dsts).take k ++ [(srcs[k], dsts[k])] := by
      rw [List.take_succ]
      have hz : k < (srcs.zip dsts).length := by
        rw [List.length_zip]
        omega
      simp [List.getElem?_eq_getElem hz, List.getElem_zip]
    unfold foldPairAt
    rw [getD_of srcs k hk', getD_of dsts k hk2, ih x (by omega), htake]
    unfold foldRows
    simp [List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem dropCol_length (w src dst c : Nat) (x out : List Nat) :
    (dropCol w x src dst c out).length = out.length := by
  unfold dropCol
  dsimp
  split
  · split <;> simp [List.length_set]
  · rfl

private theorem dropCol_hi (w src dst c : Nat) (x out : List Nat)
    (hix : ¬ src * w + c < x.length) :
    dropCol w x src dst c out = out := by
  unfold dropCol
  rw [dif_neg hix]

private theorem dropCol_zero (w src dst c : Nat) (x out : List Nat)
    (hix : src * w + c < x.length) (hz : x[src * w + c] = 0) :
    dropCol w x src dst c out = out := by
  unfold dropCol
  rw [dif_pos hix]
  simp [hz]

private theorem dropCol_of (w src dst c : Nat) (x out : List Nat)
    (hix : src * w + c < x.length) (hj : dst * w + c < out.length)
    (hnz : x[src * w + c] ≠ 0) :
    dropCol w x src dst c out =
      out.set (dst * w + c) ((out[dst * w + c] + x[src * w + c]) % 3) := by
  unfold dropCol add3
  rw [dif_pos hix]
  simp [hnz, List.getD, hj]

private theorem trits_set (out : List Nat) (j v : Nat) (hj : j < out.length)
    (hot : ∀ i (hi : i < out.length), out[i] ≤ 2) (hv : v ≤ 2) :
    ∀ i (hi : i < out.length), (out.set j v)[i]'(by simp [List.length_set]; exact hi) ≤ 2 := by
  intro i hi
  have _ : j < out.length := hj
  rw [List.getElem_set]
  split
  · exact hv
  · exact hot i hi

private theorem dropCol_trits (w src dst c : Nat) (x out : List Nat)
    (hj : dst * w + c < out.length)
    (hot : ∀ i (hi : i < out.length), out[i] ≤ 2) :
    ∀ i (hi : i < out.length),
      (dropCol w x src dst c out)[i]'(by rw [dropCol_length]; exact hi) ≤ 2 := by
  intro i hi
  by_cases hix : src * w + c < x.length
  · by_cases hz : x[src * w + c] = 0
    · simpa [dropCol_zero w src dst c x out hix hz] using hot i hi
    · have hlist := dropCol_of w src dst c x out hix hj hz
      have hv : (out[dst * w + c] + x[src * w + c]) % 3 ≤ 2 := by
        have := Nat.mod_lt (out[dst * w + c] + x[src * w + c]) (by decide : 0 < 3)
        omega
      simpa [hlist] using trits_set out (dst * w + c)
        ((out[dst * w + c] + x[src * w + c]) % 3) hj hot hv i hi
  · simpa [dropCol_hi w src dst c x out hix] using hot i hi

private theorem not_gt_last {i w : Nat} (hi : i < w) :
    ¬ Int.ofNat i > Int.ofNat (w - 1) := by
  rw [ofNat_eq_natCast, ofNat_eq_natCast]
  omega

/-- Move bump. Irreducible in the fold proofs so a record update is not copied
    into every field of the board. -/
def foldMove (b : Ecbs.Board) (m : Int) : Ecbs.Board :=
  { b with sudo_5Board_4cost := { b.sudo_5Board_4cost with sudo_5Costs_5moves := m } }

private theorem foldMove_moves (b : Ecbs.Board) (m : Int) :
    (foldMove b m).sudo_5Board_4cost.sudo_5Costs_5moves = m := by
  unfold foldMove
  rfl

private theorem foldMove_comp (b : Ecbs.Board) (m₁ m₂ : Int) :
    foldMove (foldMove b m₁) m₂ = foldMove b m₂ := by
  unfold foldMove
  rfl

private theorem foldMove_withMoves (b : Ecbs.Board) (m : Int) :
    foldMove b m = withMoves b m := by
  unfold foldMove withMoves
  rfl

section

attribute [local irreducible] foldMove

/-- One column of the emitted inner loop. -/
def foldColBody (t : Ecbs.Tier) (x out : Array Int) (b : Ecbs.Board) (p c : Int) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int × Ecbs.Board) (Array Int × Ecbs.Board)) := do
  let src ← SudoRt.atL t.sudo_4Tier_7foldsrc p
  let i0 ← SudoRt.mulI src t.sudo_4Tier_1w
  let i ← SudoRt.addI i0 c
  let dst ← SudoRt.atL t.sudo_4Tier_7folddst p
  let j0 ← SudoRt.mulI dst t.sudo_4Tier_1w
  let j ← SudoRt.addI j0 c
  let hot ← (if decide (i < t.sudo_4Tier_1n) then do
      let xv ← SudoRt.atL x i
      pure (!(SudoRt.SEq.beq xv (0 : Int)))
    else
      pure false)
  if hot then
    do
      let cur ← SudoRt.atL out j
      let xv ← SudoRt.atL x i
      let sum ← SudoRt.addI cur xv
      let m ← SudoRt.modI sum (3 : Int)
      let out ← SudoRt.putL out j m
      let mv ← SudoRt.addI b.sudo_5Board_4cost.sudo_5Costs_5moves (1 : Int)
      pure (SudoRt.Flow.cont (out, foldMove b mv))
  else
    pure (SudoRt.Flow.cont (out, b))

theorem foldColBody_at (t : Ecbs.Tier) (x out : List Nat) (b0 : Ecbs.Board)
    (srcs dsts : List Nat) (pN cN srcN dstN n w mv : Nat)
    (htn : t.sudo_4Tier_1n = Int.ofNat n)
    (htw : t.sudo_4Tier_1w = Int.ofNat w)
    (hsrcA : t.sudo_4Tier_7foldsrc = embed srcs)
    (hdstA : t.sudo_4Tier_7folddst = embed dsts)
    (hp : pN < srcs.length) (hp2 : pN < dsts.length)
    (hsrc : srcs[pN] = srcN) (hdst : dsts[pN] = dstN)
    (hx : x.length = n) (ho : out.length = n)
    (hxt : ∀ i (hi : i < x.length), x[i] ≤ 2)
    (hot : ∀ i (hi : i < out.length), out[i] ≤ 2)
    (hc : cN < w)
    (hsw : FitsLen (srcN * w + w)) (hdw : FitsLen (dstN * w + w))
    (hjN : (dstN + 1) * w ≤ n)
    (hfit : FitsLen (mv + 1)) :
    foldColBody t (embed x) (embed out) (withMoves b0 (Int.ofNat mv))
        (Int.ofNat pN) (Int.ofNat cN) =
      .ok (SudoRt.Flow.cont
        (embed (dropCol w x srcN dstN cN out),
          withMoves b0 (Int.ofNat (mv + colBump w x srcN cN)))) := by
  rw [← foldMove_withMoves]
  unfold foldColBody
  rw [hsrcA, hdstA, htw, htn]
  rw [atL_embed srcs pN hp, ok_bind, hsrc]
  rw [mulI_ofNat srcN w (FitsLen.of_le hsw (Nat.le_add_right _ _)), ok_bind]
  rw [addI_ofNat (srcN * w) cN (FitsLen.of_le hsw (by omega)), ok_bind]
  rw [atL_embed dsts pN hp2, ok_bind, hdst]
  rw [mulI_ofNat dstN w (FitsLen.of_le hdw (Nat.le_add_right _ _)), ok_bind]
  rw [addI_ofNat (dstN * w) cN (FitsLen.of_le hdw (by omega)), ok_bind]
  have hj : dstN * w + cN < out.length := by
    rw [ho]
    have hltw : dstN * w + cN < (dstN + 1) * w := by
      rw [Nat.succ_mul]
      omega
    omega
  by_cases hlt : srcN * w + cN < n
  · have hix : srcN * w + cN < x.length := by rw [hx]; exact hlt
    have hdec : decide (Int.ofNat (srcN * w + cN) < Int.ofNat n) = true :=
      decide_eq_true (Int.ofNat_lt.mpr hlt)
    rw [if_pos hdec, atL_embed x (srcN * w + cN) hix, ok_bind, sEq_int]
    by_cases hz : x[srcN * w + cN] = 0
    · rw [hz, decide_eq_true (by rfl : Int.ofNat 0 = (0 : Int)), Bool.not_true, pure_eq_ok, ok_bind]
      rw [if_neg (by decide : ¬ ((false : Bool) = true)), pure_eq_ok]
      have hskip := dropCol_zero w srcN dstN cN x out hix hz
      have hbump : colBump w x srcN cN = 0 := by
        unfold colBump
        rw [dif_pos hix, hz, if_pos rfl]
      rw [hskip, hbump, Nat.add_zero, foldMove_withMoves]
    · have hne : ¬ Int.ofNat (x[srcN * w + cN]) = 0 := by
        intro h
        exact hz (Int.ofNat.inj h)
      rw [decide_eq_false hne, Bool.not_false, pure_eq_ok, ok_bind]
      rw [if_pos (rfl : true = true)]
      rw [atL_embed out (dstN * w + cN) hj, ok_bind]
      rw [ok_bind]
      have hsum : FitsLen (out[dstN * w + cN] + x[srcN * w + cN]) :=
        fits_small (by
          have ho2 := hot _ hj
          have hx2 := hxt _ hix
          omega)
      rw [addI_ofNat _ _ hsum, ok_bind]
      rw [show (3 : Int) = Int.ofNat 3 from rfl, modI_ofNat _ (by decide), ok_bind]
      have hjA : dstN * w + cN < (embed out).size := by rw [size_embed]; exact hj
      rw [putL_ofNat _ _ _ hjA, set_irrel _ _ _ (by rw [size_embed]; exact hj)]
      rw [embed_set out (dstN * w + cN) ((out[dstN * w + cN] + x[srcN * w + cN]) % 3) hj]
      rw [ok_bind, foldMove_moves, addI_ofNat_one mv hfit, ok_bind, pure_eq_ok, foldMove_comp]
      have hlist := dropCol_of w srcN dstN cN x out hix hj hz
      have hbump : colBump w x srcN cN = 1 := by
        unfold colBump
        rw [dif_pos hix, if_neg hz]
      rw [hlist, hbump, foldMove_withMoves]
  · have hge : ¬ Int.ofNat (srcN * w + cN) < Int.ofNat n := fun h => hlt (Int.ofNat_lt.mp h)
    rw [if_neg (by simpa [decide_eq_false hge] : ¬ (decide
        (Int.ofNat (srcN * w + cN) < Int.ofNat n) = true))]
    rw [pure_eq_ok, ok_bind, if_neg (by decide : ¬ ((false : Bool) = true)), pure_eq_ok]
    have hix : ¬ srcN * w + cN < x.length := by rw [hx]; exact hlt
    have hskip := dropCol_hi w srcN dstN cN x out hix
    have hbump : colBump w x srcN cN = 0 := by
      unfold colBump
      rw [dif_neg hix]
    rw [hskip, hbump, Nat.add_zero, foldMove_withMoves]

def foldColAfter (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int × Ecbs.Board) (Array Int × Ecbs.Board)) := do
  pure (SudoRt.Flow.cont σ.2)

def foldColStep (t : Ecbs.Tier) (x : Array Int) (p toV : Int)
    (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) (Array Int × Ecbs.Board)) := do
  let c := σ.1
  let out := σ.2.1
  let b := σ.2.2
  if c > toV then
    pure (SudoRt.Flow.brk (c, (out, b)))
  else
    match ← foldColBody t x out b p c with
    | .ret r => pure (SudoRt.Flow.ret r)
    | .brk fs => pure (SudoRt.Flow.brk (c, fs))
    | .cont fs => do
        if c == toV then
          pure (SudoRt.Flow.brk (c, fs))
        else
          let i' ← SudoRt.addI c (1 : Int)
          pure (SudoRt.Flow.cont (i', fs))

private theorem row_inv_step (t : Ecbs.Tier) (x : List Nat) (b0 : Ecbs.Board)
    (srcs dsts : List Nat) (pN srcN dstN n w mv0 : Nat) (out0 : List Nat)
    (htn : t.sudo_4Tier_1n = Int.ofNat n) (htw : t.sudo_4Tier_1w = Int.ofNat w)
    (hsrcA : t.sudo_4Tier_7foldsrc = embed srcs)
    (hdstA : t.sudo_4Tier_7folddst = embed dsts)
    (hp : pN < srcs.length) (hp2 : pN < dsts.length)
    (hsrc : srcs[pN] = srcN) (hdst : dsts[pN] = dstN)
    (hx : x.length = n) (ho0 : out0.length = n)
    (hxt : ∀ i (hi : i < x.length), x[i] ≤ 2)
    (hsw : FitsLen (srcN * w + w)) (hdw : FitsLen (dstN * w + w))
    (hjN : (dstN + 1) * w ≤ n)
    (hroom : FitsLen (mv0 + w))
    (c : Nat) (st : Array Int × Ecbs.Board)
    (hc : c < w)
    (hI : ∃ out mv,
      st.1 = embed out ∧ st.2 = withMoves b0 (Int.ofNat mv) ∧
      out = foldColAt w x srcN dstN out0 c ∧
      mv = mv0 + foldBumpAt w x srcN c ∧
      out.length = n ∧ (∀ i (hi : i < out.length), out[i] ≤ 2)) :
    ∃ st',
      (∃ out mv,
        st'.1 = embed out ∧ st'.2 = withMoves b0 (Int.ofNat mv) ∧
        out = foldColAt w x srcN dstN out0 (c + 1) ∧
        mv = mv0 + foldBumpAt w x srcN (c + 1) ∧
        out.length = n ∧ (∀ i (hi : i < out.length), out[i] ≤ 2)) ∧
      foldColStep t (embed x) (Int.ofNat pN) (Int.ofNat (w - 1))
          (Int.ofNat c, st) =
        if c = w - 1 then .ok (SudoRt.Flow.brk (Int.ofNat c, st'))
        else .ok (SudoRt.Flow.cont (Int.ofNat (c + 1), st')) := by
  obtain ⟨out, mv, harr, hb, hpref, hmv, hlen, htrit⟩ := hI
  have hfit : FitsLen (mv + 1) := by
    apply FitsLen.of_le hroom
    rw [hmv]
    have := foldBumpAt_le w x srcN c
    omega
  have hbody := foldColBody_at t x out b0 srcs dsts pN c srcN dstN n w mv
    htn htw hsrcA hdstA hp hp2 hsrc hdst hx hlen hxt htrit hc hsw hdw hjN hfit
  have hpair : st = (embed out, withMoves b0 (Int.ofNat mv)) := Prod.ext harr hb
  refine ⟨(embed (dropCol w x srcN dstN c out),
      withMoves b0 (Int.ofNat (mv + colBump w x srcN c))), ?_, ?_⟩
  · refine ⟨dropCol w x srcN dstN c out, mv + colBump w x srcN c, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · rw [foldColAt, hpref]
    · rw [foldBumpAt, hmv, Nat.add_assoc]
    · rw [dropCol_length, hlen]
    · intro i hi
      have hj : dstN * w + c < out.length := by
        rw [hlen]
        have hltw : dstN * w + c < (dstN + 1) * w := by
          rw [Nat.succ_mul]
          omega
        omega
      simpa [dropCol_length] using dropCol_trits w srcN dstN c x out hj htrit i
        (by rw [dropCol_length] at hi; exact hi)
  · rw [hpair]
    unfold foldColStep
    conv => lhs; zeta
    have hng := not_gt_last hc
    rw [if_neg hng, hbody, ok_bind]
    have hfi : FitsLen (c + 1) :=
      FitsLen.of_le hroom (Nat.le_trans (Nat.succ_le_of_lt hc) (Nat.le_add_left w mv0))
    simpa using asc_tail (w - 1) c hfi
      (embed (dropCol w x srcN dstN c out),
        withMoves b0 (Int.ofNat (mv + colBump w x srcN c)))

/-- One source row: columns `0 .. w - 1`. -/
theorem foldRow_at (t : Ecbs.Tier) (x : List Nat) (b0 : Ecbs.Board)
    (srcs dsts : List Nat) (pN srcN dstN n w mv0 : Nat) (out0 : List Nat)
    (htn : t.sudo_4Tier_1n = Int.ofNat n) (htw : t.sudo_4Tier_1w = Int.ofNat w)
    (hsrcA : t.sudo_4Tier_7foldsrc = embed srcs)
    (hdstA : t.sudo_4Tier_7folddst = embed dsts)
    (hp : pN < srcs.length) (hp2 : pN < dsts.length)
    (hsrc : srcs[pN] = srcN) (hdst : dsts[pN] = dstN)
    (hx : x.length = n) (ho0 : out0.length = n)
    (hxt : ∀ i (hi : i < x.length), x[i] ≤ 2)
    (hot0 : ∀ i (hi : i < out0.length), out0[i] ≤ 2)
    (hsw : FitsLen (srcN * w + w)) (hdw : FitsLen (dstN * w + w))
    (hjN : (dstN + 1) * w ≤ n) (hw : 0 < w) (hwFit : FitsLen w)
    (hroom : FitsLen (mv0 + w)) :
    (do
        let toV ← SudoRt.subI (Int.ofNat w) (1 : Int)
        let fuel := if (0 : Int) > toV then 1 else (toV - 0).natAbs + 1
        SudoRt.runLoopOn (Int.ofNat 0, (embed out0, withMoves b0 (Int.ofNat mv0))) fuel
          (foldColStep t (embed x) (Int.ofNat pN) toV)
          foldColAfter (fun r => pure (SudoRt.Flow.ret r))) =
      .ok (SudoRt.Flow.cont
        (embed (dropRow w x srcN dstN out0),
          withMoves b0 (Int.ofNat (mv0 + foldBumpAt w x srcN w)))) := by
  rw [subI_ofNat_one w hw hwFit, ok_bind, fuelRange_eq]
  refine asc_goal
      (fun c st => ∃ out mv,
        st.1 = embed out ∧ st.2 = withMoves b0 (Int.ofNat mv) ∧
        out = foldColAt w x srcN dstN out0 c ∧
        mv = mv0 + foldBumpAt w x srcN c ∧
        out.length = n ∧ (∀ i (hi : i < out.length), out[i] ≤ 2))
      (Nat.zero_le (w - 1)) ?_ ?_ ?_
  · refine ⟨out0, mv0, rfl, rfl, rfl, by simp [foldBumpAt], ho0, hot0⟩
  · intro c st _ hc hI
    have hlt : c < w := by omega
    obtain ⟨st', hinv, hstep⟩ := row_inv_step t x b0 srcs dsts pN srcN dstN n w mv0
      out0 htn htw hsrcA hdstA hp hp2 hsrc hdst hx ho0 hxt hsw hdw hjN hroom c st hlt hI
    exact ⟨st', hinv, hstep⟩
  · intro st hI
    obtain ⟨out, mv, harr, hb, hpref, hmv, _, _⟩ := hI
    have hst : st = (embed out, withMoves b0 (Int.ofNat mv)) := Prod.ext harr hb
    have hw1 : w - 1 + 1 = w := by omega
    unfold foldColAfter
    rw [pure_eq_ok, hst, hpref, hw1, foldColAt_row, hmv, hw1]

/-- The outer `fold_key` step: one source row, then the next index. -/
def foldPairStep (t : Ecbs.Tier) (x : Array Int) (toV : Int)
    (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap
      (SudoRt.Flow (Int × (Array Int × Ecbs.Board)) (Array Int × Ecbs.Board)) := do
  let p := σ.1
  let out := σ.2.1
  let b := σ.2.2
  if p > toV then
    pure (SudoRt.Flow.brk (p, (out, b)))
  else
    match ← (do
        let toC ← SudoRt.subI t.sudo_4Tier_1w (1 : Int)
        let fuel := if (0 : Int) > toC then 1 else (toC - 0).natAbs + 1
        let row ← SudoRt.runLoopOn (Int.ofNat 0, (out, b)) fuel
          (foldColStep t x p toC) foldColAfter
          (fun r => pure (SudoRt.Flow.ret r))
        pure row) with
    | .ret r => pure (SudoRt.Flow.ret r)
    | .brk fs => pure (SudoRt.Flow.brk (p, fs))
    | .cont fs => do
        if p == toV then
          pure (SudoRt.Flow.brk (p, fs))
        else
          let i' ← SudoRt.addI p (1 : Int)
          pure (SudoRt.Flow.cont (i', fs))

def foldTail (t : Ecbs.Tier) (σ : Int × (Array Int × Ecbs.Board)) :
    Except SudoRt.Trap (Array Int × Ecbs.Board) := do
  let out := σ.2.1
  let b := σ.2.2
  let m ← SudoRt.mulI t.sudo_4Tier_8keeprows t.sudo_4Tier_1w
  let pref ← Ecbs.prefix out m
  pure (pref, b)

private theorem foldColAt_len (w src dst c : Nat) (x out : List Nat) :
    (foldColAt w x src dst out c).length = out.length := by
  induction c generalizing out with
  | zero => simp [foldColAt]
  | succ c ih =>
    rw [foldColAt, dropCol_length, ih]

private theorem foldColAt_trits (w src dst c n : Nat) (x out : List Nat)
    (ho : out.length = n) (hjN : (dst + 1) * w ≤ n) (hc : c ≤ w)
    (hot : ∀ i (hi : i < out.length), out[i] ≤ 2) :
    ∀ i (hi : i < out.length),
      (foldColAt w x src dst out c)[i]'(by rw [foldColAt_len]; exact hi) ≤ 2 := by
  induction c generalizing out with
  | zero =>
    intro i hi
    simp [foldColAt]
    exact hot i hi
  | succ c ih =>
    intro i hi
    have hprev : ∀ j (hj : j < out.length),
        (foldColAt w x src dst out c)[j]'(by rw [foldColAt_len]; exact hj) ≤ 2 :=
      ih out ho (by omega) hot
    have hlen := foldColAt_len w src dst c x out
    have hj : dst * w + c < (foldColAt w x src dst out c).length := by
      rw [hlen, ho]
      have hltw : dst * w + c < (dst + 1) * w := by
        rw [Nat.succ_mul]
        omega
      exact Nat.lt_of_lt_of_le hltw hjN
    have hhot : ∀ j (hj : j < (foldColAt w x src dst out c).length),
        (foldColAt w x src dst out c)[j] ≤ 2 := by
      intro j hj'
      have hj0 : j < out.length := by rw [← hlen]; exact hj'
      simpa [hlen] using hprev j hj0
    simp only [foldColAt]
    have hi' : i < (foldColAt w x src dst out c).length := by rw [hlen]; exact hi
    exact dropCol_trits w src dst c x (foldColAt w x src dst out c) hj hhot i hi'

private theorem row_room (w : Nat) (x srcs : List Nat) (mv0 len p mv : Nat)
    (hmv : mv = mv0 + foldBumpRows w x srcs p) (hp : p < len)
    (hroom : FitsLen (mv0 + len * w)) :
    FitsLen (mv + w) := by
  have hb := foldBumpRows_le w x srcs p
  have hmul : (p + 1) * w ≤ len * w :=
    Nat.mul_le_mul_right w (Nat.succ_le_of_lt hp)
  have h1 : mv + w ≤ mv0 + p * w + w := by
    rw [hmv]
    exact Nat.add_le_add_right (Nat.add_le_add_left hb mv0) w
  have h2 : mv0 + p * w + w = mv0 + (p + 1) * w := by
    rw [Nat.succ_mul, Nat.add_assoc]
  have h3 : mv0 + (p + 1) * w ≤ mv0 + len * w := Nat.add_le_add_left hmul mv0
  exact FitsLen.of_le hroom (Nat.le_trans (by rw [← h2]; exact h1) h3)

/-- Every source row. The list is `foldRows`, and moves grow by one per
    nonzero cell. -/
theorem foldPairs_at (t : Ecbs.Tier) (x : List Nat) (b0 : Ecbs.Board)
    (srcs dsts : List Nat) (n w kr mv0 : Nat)
    (htn : t.sudo_4Tier_1n = Int.ofNat n) (htw : t.sudo_4Tier_1w = Int.ofNat w)
    (htk : t.sudo_4Tier_8keeprows = Int.ofNat kr)
    (hsrcA : t.sudo_4Tier_7foldsrc = embed srcs)
    (hdstA : t.sudo_4Tier_7folddst = embed dsts)
    (hlen : srcs.length = dsts.length) (hpos : 0 < srcs.length)
    (hx : x.length = n)
    (hxt : ∀ i (hi : i < x.length), x[i] ≤ 2)
    (hsw : ∀ i (hi : i < srcs.length), FitsLen (srcs[i] * w + w))
    (hdw : ∀ i (hi : i < dsts.length), FitsLen (dsts[i] * w + w))
    (hjD : ∀ i (hi : i < dsts.length), (dsts[i] + 1) * w ≤ n)
    (hw : 0 < w) (hwFit : FitsLen w) (hlenFit : FitsLen srcs.length)
    (hkeep : kr * w ≤ n) (hkeepFit : FitsLen (kr * w))
    (hroom : FitsLen (mv0 + srcs.length * w)) :
    (do
        let toV ← SudoRt.subI (SudoRt.listLen (embed srcs)) (1 : Int)
        let fuel := if (0 : Int) > toV then 1 else (toV - 0).natAbs + 1
        SudoRt.runLoopOn (Int.ofNat 0, (embed x, withMoves b0 (Int.ofNat mv0))) fuel
          (foldPairStep t (embed x) toV) (foldTail t) (fun r => pure r)) =
      .ok (embed ((foldRows w x (srcs.zip dsts)).take (kr * w)),
        withMoves b0 (Int.ofNat (mv0 + foldBumpRows w x srcs srcs.length))) := by
  rw [listLen_embed, subI_ofNat_one _ hpos hlenFit, ok_bind, fuelRange_eq]
  refine asc_goal
      (fun p st => ∃ out mv,
        st.1 = embed out ∧ st.2 = withMoves b0 (Int.ofNat mv) ∧
        out = foldPairAt w x srcs dsts p ∧
        mv = mv0 + foldBumpRows w x srcs p ∧
        out.length = n ∧ (∀ i (hi : i < out.length), out[i] ≤ 2))
      (Nat.zero_le (srcs.length - 1)) ?_ ?_ ?_
  · refine ⟨x, mv0, rfl, rfl, rfl, by simp [foldBumpRows], hx, hxt⟩
  · intro p st _ hp hI
    have hlt : p < srcs.length := by omega
    have hlt2 : p < dsts.length := by rw [← hlen]; exact hlt
    obtain ⟨out, mv, harr, hb, hpref, hmv, hlenO, htrit⟩ := hI
    have hrowR := row_room w x srcs mv0 srcs.length p mv hmv hlt hroom
    have hrow := foldRow_at t x b0 srcs dsts p (srcs[p]) (dsts[p]) n w mv out
      htn htw hsrcA hdstA hlt hlt2 rfl rfl hx hlenO hxt htrit
      (hsw p hlt) (hdw p hlt2) (hjD p hlt2) hw hwFit hrowR
    have hpair : st = (embed out, withMoves b0 (Int.ofNat mv)) := Prod.ext harr hb
    refine ⟨(embed (dropRow w x (srcs[p]) (dsts[p]) out),
        withMoves b0 (Int.ofNat (mv + foldBumpAt w x (srcs[p]) w))), ?_, ?_⟩
    · refine ⟨dropRow w x (srcs[p]) (dsts[p]) out,
        mv + foldBumpAt w x (srcs[p]) w, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · rw [foldPairAt, getD_of srcs p hlt, getD_of dsts p hlt2, hpref]
      · rw [foldBumpRows, getD_of srcs p hlt, hmv, Nat.add_assoc]
      · rw [← foldColAt_row, foldColAt_len, hlenO]
      · intro i hi
        have hlenR : (dropRow w x (srcs[p]) (dsts[p]) out).length = out.length := by
          rw [← foldColAt_row, foldColAt_len]
        have hi0 : i < out.length := by rw [hlenR] at hi; exact hi
        have hle := foldColAt_trits w (srcs[p]) (dsts[p]) w n x out hlenO
          (hjD p hlt2) (Nat.le_refl _) htrit i hi0
        simpa [foldColAt_row] using hle
    · rw [hpair]
      unfold foldPairStep
      conv => lhs; zeta
      rw [htw]
      have hng := not_gt_last hlt
      rw [if_neg hng]
      simp only [bind_pure]
      rw [hrow, ok_bind]
      have hfi : FitsLen (p + 1) := FitsLen.of_le hlenFit (Nat.succ_le_of_lt hlt)
      simpa using asc_tail (srcs.length - 1) p hfi
        (embed (dropRow w x (srcs[p]) (dsts[p]) out),
          withMoves b0 (Int.ofNat (mv + foldBumpAt w x (srcs[p]) w)))
  · intro st hI
    obtain ⟨out, mv, harr, hb, hpref, hmv, hlenO, _⟩ := hI
    have hst : st = (embed out, withMoves b0 (Int.ofNat mv)) := Prod.ext harr hb
    have hdone : srcs.length - 1 + 1 = srcs.length := by omega
    unfold foldTail
    conv => lhs; zeta
    rw [htk, htw, hst, mulI_ofNat kr w hkeepFit, ok_bind]
    rw [prefix_refines out (kr * w) (by rw [hlenO]; exact hkeep) hkeepFit, ok_bind, pure_eq_ok]
    rw [hpref, hdone, foldPairAt_rows w x srcs dsts _ (Nat.le_refl _) hlen, hmv, hdone]
    have hzip : (srcs.zip dsts).take srcs.length = srcs.zip dsts := by
      have hzl : (srcs.zip dsts).length = srcs.length := by
        rw [List.length_zip, hlen, Nat.min_self]
      rw [← hzl]
      exact List.take_length (srcs.zip dsts)
    rw [hzip]

end

/-- `fold_key` after the across read is the row loop. -/
theorem fold_key_loop (b : Ecbs.Board) (t : Ecbs.Tier) (xs : List Nat)
    (htr : b.sudo_5Board_1t = t)
    (hval : Ecbs.value b across = .ok (embed xs)) :
    Ecbs.fold_key b =
      (do
        let toV ← SudoRt.subI (SudoRt.listLen t.sudo_4Tier_7foldsrc) (1 : Int)
        let fuel := if (0 : Int) > toV then 1 else (toV - 0).natAbs + 1
        let row ← SudoRt.runLoopOn ((0 : Int), (embed xs, b)) fuel
          (foldPairStep t (embed xs) toV) (foldTail t) (fun r => pure r)
        pure row) := by
  unfold Ecbs.fold_key
  rw [hval, ok_bind, htr]
  conv =>
    lhs
    zeta
  conv =>
    rhs
    unfold foldPairStep foldTail foldColStep foldColBody foldMove
    zeta
  rfl

private theorem occ_home0 :
    countHeld ((Array.mkArray 8 false).set ⟨0, by simp [Array.size_mkArray]⟩ true) 7 = 1 := by
  decide

private theorem put_occ0 (t : Spec.Tier) :
    countHeld ((builtBoard t).sudo_5Board_4held.set ⟨0, heldIx t 0 (by decide)⟩ true) 7 = 1 := by
  simpa [heldIx, ← built_held_arr] using occ_home0

private theorem built_held0 (t : Spec.Tier) :
    (builtBoard t).sudo_5Board_4held[0]'(heldIx t 0 (by decide)) = false := by
  simp [built_held_arr, Array.getElem_mkArray]

/-- The fresh board with the key in across. Peak stays 1. -/
def putFold (t : Spec.Tier) (x : List Nat) : Ecbs.Board :=
  let b := builtBoard t
  { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨0, homeIx t 0 (by decide)⟩ (embed x)
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨0, heldIx t 0 (by decide)⟩ true
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (pegCount x) } }

private theorem putFold_place (t : Spec.Tier) (x : List Nat) :
    placeBoard (builtBoard t) 0 (homeIx t 0 (by decide)) (heldIx t 0 (by decide)) x 0 1 =
      putFold t x := by
  have hge : ¬ 1 < countHeld
      ((builtBoard t).sudo_5Board_4held.set ⟨0, heldIx t 0 (by decide)⟩ true) 7 := by
    rw [put_occ0]
    decide
  rw [place_stay (builtBoard t) 0 (homeIx t 0 (by decide)) (heldIx t 0 (by decide)) x 0 1 hge]
  simp [putFold, Nat.zero_add]

private theorem fold_put (t : Spec.Tier) (hOk : BoardOk t) (x : List Nat)
    (hx : x.length = t.n) :
    put (builtBoard t) across (embed x) = .ok (putFold t x) := by
  have hput := put_refines (builtBoard t) 0 x 0 1
    (homeIx t 0 (by decide)) (heldIx t 0 (by decide))
    (by rw [built_szD]; decide) (built_held0 t)
    (by rw [built_tier_eq, hx]; rfl)
    (by rw [hx]; exact FitsLen.of_le (fits_of hOk.fits_n) (by omega))
    (built_moves0 t) (built_peak1 t)
    (by
      have hfn : FitsLen t.n := FitsLen.of_le (fits_of hOk.fits_n) (by omega)
      exact FitsLen.of_le hfn (by rw [← hx, Nat.zero_add]; exact pegCount_le x))
  unfold across
  erw [hput]
  rw [putFold_place]

/-- `fold_key` on a board whose across holds `x` is `Spec.foldKey`, and the
    move counter grows by one for each nonzero cell the rows drop. -/
theorem fold_key_refines (t : Spec.Tier) (b : Ecbs.Board) (x : List Nat) (mv : Nat)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (htr : b.sudo_5Board_1t = embTier t)
    (hval : value b across = .ok (embed x))
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv)
    (hx : x.length = t.n) (htrit : allTritList x)
    (hroom : FitsLen (mv + t.foldsrc.length * t.w)) :
    fold_key b =
      .ok (embed (foldKey t x),
        withMoves b (Int.ofNat (mv + foldBumpRows t.w x t.foldsrc t.foldsrc.length))) := by
  have hFold : FoldOk t := by
    rcases hship with rfl | rfl | rfl | rfl
    · exact demo_fold
    · exact toy_fold
    · exact hobby_fold
    · exact serious_fold
  have hpos : 0 < t.foldsrc.length := by
    rcases hship with rfl | rfl | rfl | rfl <;> decide
  have hlenFit : FitsLen t.foldsrc.length := by
    rcases hship with rfl | rfl | rfl | rfl <;> exact fits_small (by decide)
  have hwFit : FitsLen t.w := by
    rcases hship with rfl | rfl | rfl | rfl <;> exact fits_small (by decide)
  have hkeepFit : FitsLen (t.keeprows * t.w) :=
    FitsLen.of_le (fits_of hFold.fits_keep) (Nat.le_succ _)
  rw [fold_key_loop b (embTier t) x htr hval]
  simp only [bind_pure]
  rw [show (embTier t).sudo_4Tier_7foldsrc = embed t.foldsrc from rfl]
  rw [← withMoves_id b hmv]
  rw [show (0 : Int) = Int.ofNat 0 from rfl]
  have hpairs := foldPairs_at (embTier t) x b t.foldsrc t.folddst t.n t.w t.keeprows mv
    rfl rfl rfl rfl rfl hFold.same hpos hx (trits_of_all x htrit)
    (fun i hi => fits_of (hFold.fits_src _ (List.getElem_mem hi)))
    (fun i hi => fits_of (hFold.fits_dst _ (List.getElem_mem hi)))
    (fun i hi => hFold.dst _ (List.getElem_mem hi))
    hFold.w_pos hwFit hlenFit hFold.keep hkeepFit hroom
  simpa [foldKey] using hpairs

/-- `fold` on a shipped tier is `Spec.foldKey`. -/
theorem fold_refines (t : Spec.Tier) (x : List Nat)
    (hship : t = demo ∨ t = toy ∨ t = hobby ∨ t = serious)
    (hx : x.length = t.n) (htrit : allTritList x) :
    fold (embTier t) (embed x) = .ok (embed (foldKey t x)) := by
  have hOk : BoardOk t := by
    rcases hship with rfl | rfl | rfl | rfl
    · exact demo_board
    · exact toy_board
    · exact hobby_board
    · exact serious_board
  have hput := fold_put t hOk x hx
  have hroom : FitsLen (pegCount x + t.foldsrc.length * t.w) := by
    have hpeg := pegCount_le x
    rw [hx] at hpeg
    have hbound : t.n + t.foldsrc.length * t.w ≤ 4 * t.n + 8 := by
      rcases hship with rfl | rfl | rfl | rfl <;> decide
    exact FitsLen.of_le (fits_of hOk.fits_n) (by omega)
  have hkey := fold_key_refines t (putFold t x) x (pegCount x) hship
    (by simp [putFold, built_tier_eq])
    (by
      have hv := value_held_refines (putFold t x) 0 x t.n
        (by rw [putFold]; simp [Array.size_set, built_szD])
        (by rw [putFold]; simp [Array.size_set, built_szH])
        (by simp [putFold, Array.getElem_set])
        (by simp [putFold, Array.getElem_set])
        (by rw [putFold, built_tier_eq]; rfl)
        (by rw [hx]; exact Nat.le_refl _)
        (by exact FitsLen.of_le (fits_of hOk.fits_n) (by omega))
      unfold across at hv
      erw [hv]
      rw [← hx, List.take_length])
    (by simp [putFold])
    hx htrit hroom
  unfold fold
  conv => lhs; zeta
  rw [new_board_refines t hOk, ok_bind, hput, ok_bind, hkey, ok_bind]
  dsimp
  rw [pure_eq_ok]

/-- Demo's `fold` is `Spec.foldKey`. -/
theorem demo_fold_refines (x : List Nat) (hx : x.length = demo.n) (htrit : allTritList x) :
    fold (embTier demo) (embed x) = .ok (embed (foldKey demo x)) :=
  fold_refines demo x (Or.inl rfl) hx htrit

end EcbsLink2.Link2
