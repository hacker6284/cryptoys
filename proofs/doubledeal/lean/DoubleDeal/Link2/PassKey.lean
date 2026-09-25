/-
  LINK 2. Generated `passkey` refines algebraic `passToKeyCutFallback`
  on the well-formed domain. Proof-only. Not emitter soundness.
-/
import Doubledeal
import DoubleDeal.PassKey
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Append
import DoubleDeal.Link2.Helpers
import DoubleDeal.Link2.Rotate

set_option maxHeartbeats 800000

namespace DoubleDeal.Link2

/-- Empty deck: both sides return `[]`. Trap does not fire. -/
theorem passkey_nil :
    Doubledeal.passkey (embed []) = .ok (embed (passToKeyCutFallback [])) := by
  unfold Doubledeal.passkey passToKeyCutFallback passKeyGoN
  simp [listLen_embed, embed_nil, listLen_eq]
  rw [show 1 = 0 + 1 from rfl, runLoopOn_succ]
  simp [listLen_eq]
  rfl

/-- Singleton: controller is pushed onto an empty key pile (no rotate / cut). -/
theorem passkey_singleton (c : Nat) :
    Doubledeal.passkey (embed [c]) =
      .ok (embed (passToKeyCutFallback [c])) := by
  have hpk : passToKeyCutFallback [c] = [c] := by
    simp [passToKeyCutFallback, passKeyGoN, passKeyStep, maybeRotate, maybeCut]
  rw [hpk]
  unfold Doubledeal.passkey
  have hlen : SudoRt.listLen (embed [c]) = (1 : Int) := by
    rw [listLen_embed]; rfl
  simp [hlen, embed_nil, listLen_eq]
  rw [show 1 = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  rw [drop_front_singleton]
  simp only [ok_bind]
  -- hand is empty: skip suit-rotate; empty key: skip cuts; push c
  simp [embed_nil, listLen_eq]
  have hpush : Doubledeal.push_front #[] (c : Int) = .ok (embed [c]) := by
    simpa [embed_nil, ofNat_eq_natCast] using push_front_nil c
  rw [hpush, map_ok]
  rfl

/-- Length ≤ 1 is the first well-formed slice of `passkey` ≃ `passToKeyCutFallback`. -/
theorem passkey_refines_nil_and_singleton (deck : List Nat)
    (h : deck.length ≤ 1) :
    Doubledeal.passkey (embed deck) =
      .ok (embed (passToKeyCutFallback deck)) := by
  match deck with
  | [] => exact passkey_nil
  | [c] => exact passkey_singleton c
  | _ :: _ :: _ =>
    simp at h

/-- Generated suit-rotate prefix refines `maybeRotate`. -/
theorem maybeRotate_refines (c : Nat) (hand : List Nat)
    (hfits : FitsLen hand.length) :
    (if decide (SudoRt.listLen (embed hand) > (0 : Int)) then
      (do
        let s ← Doubledeal.suit_of (Int.ofNat c)
        let k ← SudoRt.modI s (SudoRt.listLen (embed hand))
        if decide (k > (0 : Int)) then
          Doubledeal.left_rotate (embed hand) k
        else
          pure (embed hand))
     else
      pure (embed hand)) =
      .ok (embed (maybeRotate hand c)) := by
  rw [listLen_pos_decide]
  by_cases hpos : 0 < hand.length
  · rw [decide_eq_true hpos]
    simp only [if_true]
    rw [suit_of_refines]
    simp only [ok_bind, listLen_embed]
    have hne : hand.length ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    have hmod : SudoRt.modI (Int.ofNat (suit c)) (Int.ofNat hand.length) =
        .ok (Int.ofNat (suit c % hand.length)) :=
      modI_ofNat (suit c) hne
    rw [hmod]
    simp only [ok_bind]
    by_cases hk0 : suit c % hand.length = 0
    · have hdec : decide (Int.ofNat (suit c % hand.length) > (0 : Int)) = false := by
        rw [hk0, decide_ofNat_pos]
        decide
      have hneB : ¬ (decide (Int.ofNat (suit c % hand.length) > (0 : Int)) = true) := by
        rw [hdec]; decide
      rw [if_neg hneB]
      apply congrArg Except.ok
      apply congrArg embed
      unfold maybeRotate rotateLeft
      rw [if_neg hne, hk0]
      exact (rotL_mod_zero hand 0 hne (Nat.zero_mod _)).symm
    · have hdec : decide (Int.ofNat (suit c % hand.length) > (0 : Int)) = true := by
        rw [decide_ofNat_pos]
        exact decide_eq_true (Nat.pos_of_ne_zero hk0)
      rw [if_pos hdec]
      rw [left_rotate_refines hand (suit c % hand.length) hfits]
      apply congrArg Except.ok
      apply congrArg embed
      unfold maybeRotate rotateLeft
      rw [if_neg hne]
  · have hneg : ¬ (decide (0 < hand.length) = true) := by
      rw [decide_eq_false hpos]; decide
    rw [if_neg hneg]
    apply congrArg Except.ok
    apply congrArg embed
    unfold maybeRotate
    have : hand.length = 0 :=
      Nat.le_antisymm (Nat.not_lt.mp hpos) (Nat.zero_le _)
    rw [if_pos this]

/-- Generated cut then `push_front` refines `maybeCut` + controller on the key. -/
theorem maybeCut_push_refines (c : Nat) (hand key : List Nat)
    (hh : FitsLen hand.length) (hk : FitsLen key.length) :
    (do
      let cutH ← (if decide (SudoRt.listLen (embed hand) > (0 : Int)) then
        (do
          let r ← Doubledeal.rank_of (Int.ofNat c)
          pure (decide (r < SudoRt.listLen (embed hand))))
        else pure false)
      let cutK ← (if decide (SudoRt.listLen (embed key) > (0 : Int)) then
        (do
          let r ← Doubledeal.rank_of (Int.ofNat c)
          pure (decide (r < SudoRt.listLen (embed key))))
        else pure false)
      if cutH then do
        let r ← Doubledeal.rank_of (Int.ofNat c)
        let hand ← Doubledeal.left_rotate (embed hand) r
        let key ← Doubledeal.push_front (embed key) (Int.ofNat c)
        pure (hand, key)
      else if cutK then do
        let r ← Doubledeal.rank_of (Int.ofNat c)
        let key ← Doubledeal.left_rotate (embed key) r
        let key ← Doubledeal.push_front key (Int.ofNat c)
        pure (embed hand, key)
      else do
        let key ← Doubledeal.push_front (embed key) (Int.ofNat c)
        pure (embed hand, key)) =
      .ok (embed (maybeCut hand key c).1,
           embed (c :: (maybeCut hand key c).2)) := by
  rw [rank_lt_flag, rank_lt_flag]
  simp only [ok_bind]
  by_cases hH : 0 < hand.length ∧ rank c < hand.length
  · simp [decide_eq_true hH]
    rw [rank_of_refines_natCast]
    simp only [ok_bind]
    rw [left_rotate_refines hand (rank c) hh]
    rw [← ofNat_eq_natCast c]
    rw [push_front_refines c key hk]
    simp only [ok_bind]
    unfold maybeCut
    rw [dif_pos hH]
    have hcut : cutProper hand (rank c) = rotL hand (rank c) := by
      unfold cutProper
      simp [hH.2]
    rw [hcut]
    rfl
  · have hnotH : ¬ (decide (0 < hand.length ∧ rank c < hand.length) = true) := by
      rw [decide_eq_false hH]; decide
    rw [if_neg hnotH]
    by_cases hK : 0 < key.length ∧ rank c < key.length
    · simp [decide_eq_true hK]
      rw [rank_of_refines_natCast]
      simp only [ok_bind]
      rw [left_rotate_refines key (rank c) hk]
      simp only [ok_bind]
      have hk' : FitsLen (rotL key (rank c)).length := by
        rw [length_rotL]; exact hk
      rw [← ofNat_eq_natCast c]
      rw [push_front_refines c (rotL key (rank c)) hk']
      unfold maybeCut
      rw [dif_neg hH, dif_pos hK]
      have hcut : cutProper key (rank c) = rotL key (rank c) := by
        unfold cutProper
        simp [hK.2]
      rw [hcut]
      rfl
    · have hnotK : ¬ (decide (0 < key.length ∧ rank c < key.length) = true) := by
        rw [decide_eq_false hK]; decide
      rw [if_neg hnotK]
      rw [push_front_refines c key hk]
      unfold maybeCut
      rw [dif_neg hH, dif_neg hK]
      rfl

/-- One generated PassKey body (rotate / cut / push) refines `passKeyStep`. -/
theorem passKeyStep_refines (c : Nat) (hand key : List Nat)
    (hh : FitsLen hand.length) (hk : FitsLen key.length) :
    (do
      let hand ← (if decide (SudoRt.listLen (embed hand) > (0 : Int)) then
        (do
          let s ← Doubledeal.suit_of (Int.ofNat c)
          let k ← SudoRt.modI s (SudoRt.listLen (embed hand))
          if decide (k > (0 : Int)) then
            Doubledeal.left_rotate (embed hand) k
          else
            pure (embed hand))
        else
          pure (embed hand))
      let cutH ← (if decide (SudoRt.listLen hand > (0 : Int)) then
        (do
          let r ← Doubledeal.rank_of (Int.ofNat c)
          pure (decide (r < SudoRt.listLen hand)))
        else pure false)
      let cutK ← (if decide (SudoRt.listLen (embed key) > (0 : Int)) then
        (do
          let r ← Doubledeal.rank_of (Int.ofNat c)
          pure (decide (r < SudoRt.listLen (embed key))))
        else pure false)
      if cutH then do
        let r ← Doubledeal.rank_of (Int.ofNat c)
        let hand ← Doubledeal.left_rotate hand r
        let key ← Doubledeal.push_front (embed key) (Int.ofNat c)
        pure (hand, key)
      else if cutK then do
        let r ← Doubledeal.rank_of (Int.ofNat c)
        let key ← Doubledeal.left_rotate (embed key) r
        let key ← Doubledeal.push_front key (Int.ofNat c)
        pure (hand, key)
      else do
        let key ← Doubledeal.push_front (embed key) (Int.ofNat c)
        pure (hand, key)) =
      .ok (embed (passKeyStep hand key c).1,
           embed (passKeyStep hand key c).2) := by
  have hr := maybeRotate_refines c hand hh
  rw [hr]
  simp only [ok_bind]
  have hlen : (maybeRotate hand c).length = hand.length := length_maybeRotate hand c
  have hh' : FitsLen (maybeRotate hand c).length := by rw [hlen]; exact hh
  have hc := maybeCut_push_refines c (maybeRotate hand c) key hh' hk
  -- `maybeCut_push_refines` starts from `embed (maybeRotate ...)`.
  -- After `ok_bind` the bound `hand` is that array.
  simpa [passKeyStep, embed] using hc

/-- Proof-side twin of one generated PassKey iteration: `drop_front` then
    the sequential body in `passKeyStep_refines`. Not a second algorithm. -/
def passkeyStepGen (toV : Int) (σ : Int × Array Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int × Array Int) (Array Int)) :=
  let i := σ.1
  let hand := σ.2.1
  let key := σ.2.2
  if i > toV then
    pure (SudoRt.Flow.brk (i, (hand, key)))
  else do
    let ⟨c, hand⟩ ← Doubledeal.drop_front hand
    let piles ← (do
      let hand ← (if decide (SudoRt.listLen hand > (0 : Int)) then
        (do
          let s ← Doubledeal.suit_of c
          let k ← SudoRt.modI s (SudoRt.listLen hand)
          if decide (k > (0 : Int)) then
            Doubledeal.left_rotate hand k
          else
            pure hand)
        else
          pure hand)
      let cutH ← (if decide (SudoRt.listLen hand > (0 : Int)) then
        (do
          let r ← Doubledeal.rank_of c
          pure (decide (r < SudoRt.listLen hand)))
        else pure false)
      let cutK ← (if decide (SudoRt.listLen key > (0 : Int)) then
        (do
          let r ← Doubledeal.rank_of c
          pure (decide (r < SudoRt.listLen key)))
        else pure false)
      if cutH then do
        let r ← Doubledeal.rank_of c
        let hand ← Doubledeal.left_rotate hand r
        let key ← Doubledeal.push_front key c
        pure (hand, key)
      else if cutK then do
        let r ← Doubledeal.rank_of c
        let key ← Doubledeal.left_rotate key r
        let key ← Doubledeal.push_front key c
        pure (hand, key)
      else do
        let key ← Doubledeal.push_front key c
        pure (hand, key))
    if i == toV then
      pure (SudoRt.Flow.brk (i, piles))
    else do
      let i' ← SudoRt.addI i (1 : Int)
      pure (SudoRt.Flow.cont (i', piles))

theorem passkeyStepGen_gt (toV i : Int) (hand key : Array Int) (h : i > toV) :
    passkeyStepGen toV (i, (hand, key)) = .ok (.brk (i, (hand, key))) := by
  unfold passkeyStepGen
  rw [if_pos h]
  rfl

theorem passkeyStepGen_hit (c : Nat) (rest key : List Nat) (fromN toN : Nat)
    (hfrom : fromN ≤ toN) (hfitsH : FitsLen (rest.length + 1))
    (hfitsK : FitsLen key.length)
    (hfitsI : fromN = toN ∨ FitsLen (fromN + 1)) :
    passkeyStepGen (Int.ofNat toN)
        (Int.ofNat fromN, (embed (c :: rest), embed key)) =
      if fromN = toN then
        .ok (.brk (Int.ofNat fromN,
          (embed (passKeyStep rest key c).1,
           embed (passKeyStep rest key c).2)))
      else
        .ok (.cont (Int.ofNat (fromN + 1),
          (embed (passKeyStep rest key c).1,
           embed (passKeyStep rest key c).2))) := by
  unfold passkeyStepGen
  have hngt : ¬ (Int.ofNat fromN > Int.ofNat toN) :=
    Int.not_lt.mpr (Int.ofNat_le.mpr hfrom)
  rw [if_neg hngt]
  rw [drop_front_refines c rest hfitsH]
  simp only [ok_bind]
  -- controller is `Int.ofNat c`; piles refine `passKeyStep`
  have hbody := passKeyStep_refines c rest key
    (FitsLen.of_le hfitsH (Nat.le_succ _)) hfitsK
  -- align `Int.ofNat c` vs residual `c` from drop_front
  have hbody' :
      (do
        let hand ← (if decide (SudoRt.listLen (embed rest) > (0 : Int)) then
          (do
            let s ← Doubledeal.suit_of (Int.ofNat c)
            let k ← SudoRt.modI s (SudoRt.listLen (embed rest))
            if decide (k > (0 : Int)) then
              Doubledeal.left_rotate (embed rest) k
            else
              pure (embed rest))
          else
            pure (embed rest))
        let cutH ← (if decide (SudoRt.listLen hand > (0 : Int)) then
          (do
            let r ← Doubledeal.rank_of (Int.ofNat c)
            pure (decide (r < SudoRt.listLen hand)))
          else pure false)
        let cutK ← (if decide (SudoRt.listLen (embed key) > (0 : Int)) then
          (do
            let r ← Doubledeal.rank_of (Int.ofNat c)
            pure (decide (r < SudoRt.listLen (embed key))))
          else pure false)
        if cutH then do
          let r ← Doubledeal.rank_of (Int.ofNat c)
          let hand ← Doubledeal.left_rotate hand r
          let key ← Doubledeal.push_front (embed key) (Int.ofNat c)
          pure (hand, key)
        else if cutK then do
          let r ← Doubledeal.rank_of (Int.ofNat c)
          let key ← Doubledeal.left_rotate (embed key) r
          let key ← Doubledeal.push_front key (Int.ofNat c)
          pure (hand, key)
        else do
          let key ← Doubledeal.push_front (embed key) (Int.ofNat c)
          pure (hand, key)) =
        .ok (embed (passKeyStep rest key c).1,
             embed (passKeyStep rest key c).2) := hbody
  rw [hbody']
  simp only [ok_bind]
  by_cases heq : fromN = toN
  · subst heq
    have hbeq : (Int.ofNat fromN == Int.ofNat fromN) = true := by simp
    simp [hbeq]
    rfl
  · have hne : ¬ (Int.ofNat fromN = Int.ofNat toN) := fun h =>
      heq (Int.ofNat.inj h)
    have hbeq : (Int.ofNat fromN == Int.ofNat toN) = false :=
      decide_eq_false hne
    rw [if_neg (by rw [hbeq]; decide)]
    have hfitsI' : FitsLen (fromN + 1) := by
      cases hfitsI with
      | inl h => exact (heq h).elim
      | inr h => exact h
    have hadd : SudoRt.addI (Int.ofNat fromN) 1 = .ok (Int.ofNat (fromN + 1)) :=
      addI_ofNat_one fromN hfitsI'
    rw [hadd]
    simp only [ok_bind, if_neg heq]
    rfl

/-- Empty remaining range: the stepper breaks and `after` returns the key pile. -/
theorem passkey_loop_gt (fromV toV : Int) (hand key : Array Int)
    (hgt : fromV > toV) :
    SudoRt.runLoopOn (ρ := Array Int) (fromV, (hand, key))
        (fuelRange fromV toV) (passkeyStepGen toV)
        (fun σ => .ok σ.2.2) (fun r => .ok r) =
      .ok key := by
  rw [fuelRange_gt hgt, show 1 = 0 + 1 from rfl, runLoopOn_succ]
  rw [passkeyStepGen_gt toV fromV hand key hgt]

/-- Inclusive PassKey loop on embed-image piles refines `passKeyGoN`.
    Remaining seats equal remaining hand cards (`toN + 1 - fromN`). -/
theorem passkey_loop_refines (hand key : List Nat) (fromN toN : Nat)
    (hcard : toN + 1 - fromN = hand.length)
    (hsum : FitsLen (hand.length + key.length))
    (hto : FitsLen toN) :
    SudoRt.runLoopOn (ρ := Array Int)
        (Int.ofNat fromN, (embed hand, embed key))
        (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        (passkeyStepGen (Int.ofNat toN))
        (fun σ => .ok σ.2.2) (fun r => .ok r) =
      .ok (embed (passKeyGoN hand.length hand key)) := by
  generalize hrem : toN + 1 - fromN = rem
  induction rem generalizing fromN hand key with
  | zero =>
    have hlen0 : hand.length = 0 := by omega
    have hhand : hand = [] := List.eq_nil_of_length_eq_zero hlen0
    subst hhand
    have hgt : Int.ofNat fromN > Int.ofNat toN := by
      have : toN + 1 ≤ fromN := by omega
      exact Int.ofNat_lt.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self toN) this)
    rw [passkey_loop_gt (Int.ofNat fromN) (Int.ofNat toN) (embed []) (embed key) hgt]
    simp [passKeyGoN]
  | succ rem ih =>
    have hlen : hand.length = rem + 1 := by omega
    match hand with
    | [] =>
      simp at hlen
    | c :: rest =>
      have hrest : rest.length = rem := by
        simp [List.length_cons] at hlen
        exact hlen
      have hle : fromN ≤ toN := by omega
      have hfitsH : FitsLen (rest.length + 1) := by
        have : FitsLen ((c :: rest).length + key.length) := hsum
        simp [List.length_cons] at this
        exact FitsLen.of_le this (Nat.le_add_right _ _)
      have hfitsK : FitsLen key.length :=
        FitsLen.of_le hsum (Nat.le_add_left _ _)
      have hfitsI : fromN = toN ∨ FitsLen (fromN + 1) := by
        by_cases heq : fromN = toN
        · exact Or.inl heq
        · have : fromN < toN := Nat.lt_of_le_of_ne hle heq
          exact Or.inr (FitsLen.of_le hto (Nat.succ_le_of_lt this))
      rw [fuelRange_le hle, runLoopOn_succ]
      rw [passkeyStepGen_hit c rest key fromN toN hle hfitsH hfitsK hfitsI]
      by_cases heq : fromN = toN
      · rw [if_pos heq]
        have hrem0 : rem = 0 := by omega
        have hnil : rest = [] :=
          List.eq_nil_of_length_eq_zero (hrest.trans hrem0)
        subst hnil
        simp [passKeyGoN]
      · rw [if_neg heq]
        have hlt : fromN < toN := Nat.lt_of_le_of_ne hle heq
        have hfuel : toN - fromN =
            fuelRange (Int.ofNat (fromN + 1)) (Int.ofNat toN) := by
          rw [fuelRange_le (Nat.succ_le_of_lt hlt)]
          omega
        rw [hfuel]
        simp only [passKeyGoN]
        have hlen1 := length_passKeyStep_fst rest key c
        have hlen2 := length_passKeyStep_snd rest key c
        have ih' := ih
            (passKeyStep rest key c).1 (passKeyStep rest key c).2 (fromN + 1)
            (by rw [hlen1]; omega)
            (by
              rw [hlen1, hlen2]
              have : FitsLen (rest.length + 1 + key.length) := by
                simpa [List.length_cons] using hsum
              exact (Eq.mp (congrArg FitsLen (by omega)) this))
            (by omega)
        rw [hlen1] at ih'
        exact ih'

/-- Twin loop at the generated `fromV = 1`, `toV = n`, empty key pile. -/
theorem passkey_twin_refines (deck : List Nat) (hfits : FitsLen deck.length) :
    SudoRt.runLoopOn (ρ := Array Int)
        (Int.ofNat 1, (embed deck, embed []))
        (fuelRange (Int.ofNat 1) (Int.ofNat deck.length))
        (passkeyStepGen (Int.ofNat deck.length))
        (fun σ => .ok σ.2.2) (fun r => .ok r) =
      .ok (embed (passToKeyCutFallback deck)) := by
  simpa [passToKeyCutFallback] using
    passkey_loop_refines deck [] 1 deck.length (by omega) (by simpa using hfits) hfits

/-- Residual cut-predicate on one pile (unfolded `if decide (listLen > 0)`). -/
def passkeyCutFlag (c : Int) (xs : Array Int) : Except SudoRt.Trap Bool :=
  if decide (SudoRt.listLen xs > (0 : Int)) = true then do
    let r ← Doubledeal.rank_of c
    pure (decide (r < SudoRt.listLen xs))
  else
    pure false

/-- Sequential cut / push body of one PassKey iteration (same residual as
    `passkeyStepGen`, not a second algorithm). -/
def passkeyCutPush (c : Int) (hand key : Array Int) :
    Except SudoRt.Trap (Array Int × Array Int) :=
  do
    let cutH ← passkeyCutFlag c hand
    let cutK ← passkeyCutFlag c key
    if cutH = true then do
      let r ← Doubledeal.rank_of c
      let hand ← Doubledeal.left_rotate hand r
      let key ← Doubledeal.push_front key c
      pure (hand, key)
    else if cutK = true then do
      let r ← Doubledeal.rank_of c
      let key ← Doubledeal.left_rotate key r
      let key ← Doubledeal.push_front key c
      pure (hand, key)
    else do
      let key ← Doubledeal.push_front key c
      pure (hand, key)

/-- Nested residual cut / push wraps each leaf as `Flow.cont`. -/
def passkeyCutPushCont (c : Int) (hand key : Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int × Array Int) (Array Int)) :=
  do
    let cutH ← passkeyCutFlag c hand
    let cutK ← passkeyCutFlag c key
    if cutH = true then do
      let r ← Doubledeal.rank_of c
      let hand ← Doubledeal.left_rotate hand r
      let key ← Doubledeal.push_front key c
      pure (SudoRt.Flow.cont (hand, key))
    else if cutK = true then do
      let r ← Doubledeal.rank_of c
      let key ← Doubledeal.left_rotate key r
      let key ← Doubledeal.push_front key c
      pure (SudoRt.Flow.cont (hand, key))
    else do
      let key ← Doubledeal.push_front key c
      pure (SudoRt.Flow.cont (hand, key))

/-- Residual nested cut / push is sequential `passkeyCutPush` then `Flow.cont`. -/
theorem passkeyCutPushCont_eq (c : Int) (hand key : Array Int) :
    passkeyCutPushCont c hand key =
      (do
        let piles ← passkeyCutPush c hand key
        pure (SudoRt.Flow.cont (ρ := Array Int) piles)) := by
  unfold passkeyCutPushCont passkeyCutPush
  cases hH : passkeyCutFlag c hand with
  | error e => simp [hH]; try rfl
  | ok cutH =>
    simp only [hH, ok_bind]
    cases hK : passkeyCutFlag c key with
    | error e => simp [hK]; try rfl
    | ok cutK =>
      simp only [hK, ok_bind]
      cases cutH with
      | false =>
        cases cutK with
        | false =>
          cases hP : Doubledeal.push_front key c with
          | error e => simp [hP]; try rfl
          | ok key' => simp [hP]
        | true =>
          cases hR : Doubledeal.rank_of c with
          | error e => simp [hR]; try rfl
          | ok r =>
            simp only [hR, ok_bind]
            cases hL : Doubledeal.left_rotate key r with
            | error e => simp [hL]; try rfl
            | ok key' =>
              simp only [hL, ok_bind]
              cases hP : Doubledeal.push_front key' c with
              | error e => simp [hP]; try rfl
              | ok key'' => simp [hP]
      | true =>
        cases hR : Doubledeal.rank_of c with
        | error e => simp [hR]; try rfl
        | ok r =>
          simp only [hR, ok_bind]
          cases hL : Doubledeal.left_rotate hand r with
          | error e => simp [hL]; try rfl
          | ok hand' =>
            simp only [hL, ok_bind]
            cases hP : Doubledeal.push_front key c with
            | error e => simp [hP]; try rfl
            | ok key' => simp [hP]

/-- Suit-rotate prefix of `passkeyStepGen` (sequential residual). -/
def passkeyRotateIf (c : Int) (hand : Array Int) : Except SudoRt.Trap (Array Int) :=
  if decide (SudoRt.listLen hand > (0 : Int)) = true then do
    let s ← Doubledeal.suit_of c
    let k ← SudoRt.modI s (SudoRt.listLen hand)
    if decide (k > (0 : Int)) = true then
      Doubledeal.left_rotate hand k
    else
      pure hand
  else
    pure hand

/-- Nested residual after `drop_front`: suit-rotate branches each contain
    cut / push (do-elaboration). Equals sequential rotate then cut / push,
    wrapped as `Flow.cont`. -/
theorem passkey_nested_as_seq (c : Int) (hand key : Array Int) :
    (if decide (SudoRt.listLen hand > (0 : Int)) = true then do
      let s ← Doubledeal.suit_of c
      let k ← SudoRt.modI s (SudoRt.listLen hand)
      if decide (k > (0 : Int)) = true then do
        let hand ← Doubledeal.left_rotate hand k
        passkeyCutPushCont c hand key
      else
        passkeyCutPushCont c hand key
     else
      passkeyCutPushCont c hand key) =
      (do
        let hand ← passkeyRotateIf c hand
        let piles ← passkeyCutPush c hand key
        pure (SudoRt.Flow.cont (ρ := Array Int) piles)) := by
  unfold passkeyRotateIf
  by_cases hp : decide (SudoRt.listLen hand > (0 : Int)) = true
  · rw [if_pos hp]
    simp only [if_pos hp]
    cases hs : Doubledeal.suit_of c with
    | error e => simp [hs]
    | ok s =>
      simp only [hs, ok_bind]
      cases hk : SudoRt.modI s (SudoRt.listLen hand) with
      | error e => simp [hk]
      | ok k =>
        simp only [hk, ok_bind]
        by_cases hq : decide (k > (0 : Int)) = true
        · rw [if_pos hq]
          simp only [if_pos hq]
          cases hr : Doubledeal.left_rotate hand k with
          | error e => simp [hr]
          | ok hand' =>
            simp only [hr, ok_bind]
            exact passkeyCutPushCont_eq c hand' key
        · rw [if_neg hq]
          simp only [if_neg hq, ok_bind]
          exact passkeyCutPushCont_eq c hand key
  · rw [if_neg hp]
    simp only [if_neg hp, ok_bind]
    exact passkeyCutPushCont_eq c hand key

/-- Sequential body after `drop_front` in `passkeyStepGen`. -/
def passkeyPiles (c : Int) (hand key : Array Int) :
    Except SudoRt.Trap (Array Int × Array Int) :=
  do
    let hand ← passkeyRotateIf c hand
    passkeyCutPush c hand key

theorem passkeyPiles_cont (c : Int) (hand key : Array Int) :
    (do
      let hand ← passkeyRotateIf c hand
      let piles ← passkeyCutPush c hand key
      pure (SudoRt.Flow.cont (ρ := Array Int) piles)) =
      (do
        let piles ← passkeyPiles c hand key
        pure (SudoRt.Flow.cont (ρ := Array Int) piles)) := by
  unfold passkeyPiles
  cases passkeyRotateIf c hand with
  | error e => rfl
  | ok hand' =>
    simp only [ok_bind]
    try rfl

theorem passkeyPiles_eq (c : Int) (hand key : Array Int) :
    passkeyPiles c hand key =
      (do
        let hand ←
          (if decide (SudoRt.listLen hand > (0 : Int)) = true then do
            let s ← Doubledeal.suit_of c
            let k ← SudoRt.modI s (SudoRt.listLen hand)
            if decide (k > (0 : Int)) = true then
              Doubledeal.left_rotate hand k
            else
              pure hand
           else
            pure hand)
        let cutH ←
          (if decide (SudoRt.listLen hand > (0 : Int)) = true then do
            let r ← Doubledeal.rank_of c
            pure (decide (r < SudoRt.listLen hand))
           else
            pure false)
        let cutK ←
          (if decide (SudoRt.listLen key > (0 : Int)) = true then do
            let r ← Doubledeal.rank_of c
            pure (decide (r < SudoRt.listLen key))
           else
            pure false)
        if cutH = true then do
          let r ← Doubledeal.rank_of c
          let hand ← Doubledeal.left_rotate hand r
          let key ← Doubledeal.push_front key c
          pure (hand, key)
        else if cutK = true then do
          let r ← Doubledeal.rank_of c
          let key ← Doubledeal.left_rotate key r
          let key ← Doubledeal.push_front key c
          pure (hand, key)
        else do
          let key ← Doubledeal.push_front key c
          pure (hand, key)) := by
  unfold passkeyPiles passkeyRotateIf passkeyCutPush passkeyCutFlag
  rfl

/-- Residual `else` branch of `Doubledeal.passkey` equals `passkeyStepGen`'s. -/
theorem passkey_step_else (toV i : Int) (hand key : Array Int) :
    (do
      let __do_lift ←
        (do
          let t ← Doubledeal.drop_front hand
          match t with
          | (c, hand) =>
            if decide (SudoRt.listLen hand > (0 : Int)) = true then do
              let s ← Doubledeal.suit_of c
              let k ← SudoRt.modI s (SudoRt.listLen hand)
              if decide (k > (0 : Int)) = true then do
                let hand ← Doubledeal.left_rotate hand k
                passkeyCutPushCont c hand key
              else
                passkeyCutPushCont c hand key
            else
              passkeyCutPushCont c hand key)
      match __do_lift with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (i, fs))
      | .cont fs =>
        if (i == toV) = true then
          pure (SudoRt.Flow.brk (i, fs))
        else do
          let i' ← SudoRt.addI i (1 : Int)
          pure (SudoRt.Flow.cont (i', fs))) =
      (do
        let t ← Doubledeal.drop_front hand
        match t with
        | (c, hand) => do
          let piles ← passkeyPiles c hand key
          if (i == toV) = true then
            pure (SudoRt.Flow.brk (i, piles))
          else do
            let i' ← SudoRt.addI i (1 : Int)
            pure (SudoRt.Flow.cont (i', piles))) := by
  cases hd : Doubledeal.drop_front hand with
  | error e => simp [hd]
  | ok t =>
    simp only [hd, ok_bind]
    cases t with
    | mk c hand' =>
      simp only
      have hn := passkey_nested_as_seq c hand' key
      rw [hn, passkeyPiles_cont]
      cases hp : passkeyPiles c hand' key with
      | error e => simp [hp]
      | ok piles => simp [hp]

/-- `passkeyCutPushCont` always yields `.cont`; matching it is `passkeyCutPush`. -/
theorem passkeyCutPushCont_match (c : Int) (hand key : Array Int)
    {α : Type}
    (onRet : Array Int → Except SudoRt.Trap α)
    (onBrk : Array Int × Array Int → Except SudoRt.Trap α)
    (onCont : Array Int × Array Int → Except SudoRt.Trap α) :
    (do
      let y ← passkeyCutPushCont c hand key
      match y with
      | .ret r => onRet r
      | .brk fs => onBrk fs
      | .cont fs => onCont fs) =
      (do
        let piles ← passkeyCutPush c hand key
        onCont piles) := by
  rw [passkeyCutPushCont_eq]
  cases hp : passkeyCutPush c hand key with
  | error e => simp [hp]
  | ok piles => simp [hp]

/-- Nested residual after a successful `drop_front` (join-point / leaf match)
    equals sequential `passkeyPiles` then the loop tail. -/
theorem passkey_nested_match (c : Int) (hand key : Array Int) (i toV : Int) :
    (if 0 < SudoRt.listLen hand then do
      let s ← Doubledeal.suit_of c
      let k ← SudoRt.modI s (SudoRt.listLen hand)
      if 0 < k then do
        let hand ← Doubledeal.left_rotate hand k
        let y ← passkeyCutPushCont c hand key
        match y with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
        | .brk fs => pure (SudoRt.Flow.brk (i, fs))
        | .cont fs =>
          if i = toV then
            pure (SudoRt.Flow.brk (i, fs))
          else
            (fun a => SudoRt.Flow.cont (a, fs)) <$> SudoRt.addI i (1 : Int)
      else do
        let y ← passkeyCutPushCont c hand key
        match y with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
        | .brk fs => pure (SudoRt.Flow.brk (i, fs))
        | .cont fs =>
          if i = toV then
            pure (SudoRt.Flow.brk (i, fs))
          else
            (fun a => SudoRt.Flow.cont (a, fs)) <$> SudoRt.addI i (1 : Int)
     else do
      let y ← passkeyCutPushCont c hand key
      match y with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (i, fs))
      | .cont fs =>
        if i = toV then
          pure (SudoRt.Flow.brk (i, fs))
        else
          (fun a => SudoRt.Flow.cont (a, fs)) <$> SudoRt.addI i (1 : Int)) =
      (do
        let piles ← passkeyPiles c hand key
        if i = toV then
          pure (SudoRt.Flow.brk (i, piles))
        else
          (fun a => SudoRt.Flow.cont (a, piles)) <$> SudoRt.addI i (1 : Int)) := by
  have htail (hand' : Array Int) :
      (do
        let y ← passkeyCutPushCont c hand' key
        match y with
        | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
        | .brk fs => pure (SudoRt.Flow.brk (i, fs))
        | .cont fs =>
          if i = toV then
            pure (SudoRt.Flow.brk (i, fs))
          else
            (fun a => SudoRt.Flow.cont (a, fs)) <$> SudoRt.addI i (1 : Int)) =
        (do
          let piles ← passkeyCutPush c hand' key
          if i = toV then
            pure (SudoRt.Flow.brk (i, piles))
          else
            (fun a => SudoRt.Flow.cont (a, piles)) <$> SudoRt.addI i (1 : Int)) :=
    passkeyCutPushCont_match c hand' key
      (fun r => pure (SudoRt.Flow.ret (ρ := Array Int) r))
      (fun fs => pure (SudoRt.Flow.brk (i, fs)))
      (fun fs =>
        if i = toV then
          pure (SudoRt.Flow.brk (i, fs))
        else
          (fun a => SudoRt.Flow.cont (a, fs)) <$> SudoRt.addI i (1 : Int))
  unfold passkeyPiles passkeyRotateIf
  by_cases hp : 0 < SudoRt.listLen hand
  · simp [hp]
    cases hs : Doubledeal.suit_of c with
    | error e => simp [hs]
    | ok s =>
      simp only [hs, ok_bind]
      cases hk : SudoRt.modI s (SudoRt.listLen hand) with
      | error e => simp [hk]
      | ok k =>
        simp only [hk, ok_bind]
        by_cases hq : 0 < k
        · simp [hq]
          cases hr : Doubledeal.left_rotate hand k with
          | error e => simp [hr]
          | ok hand' =>
            simp only [hr, ok_bind]
            exact htail hand'
        · simp [hq, ok_bind]
          exact htail hand
  · simp [hp, ok_bind]
    exact htail hand

/-- Residual stepper after unfold / `dsimp` equals `passkeyStepGen`.
    Nested suit-rotate (do-elaboration) is the emitted shape; `passkeyStepGen`
    is the sequential twin, not a second algorithm. -/
theorem passkey_step_eq (toV : Int) (σ : Int × Array Int × Array Int) :
    (if σ.fst > toV then
       (pure (SudoRt.Flow.brk (σ.fst, σ.snd.fst, σ.snd.snd)) :
          Except SudoRt.Trap (SudoRt.Flow (Int × Array Int × Array Int) (Array Int)))
     else do
       let t ← Doubledeal.drop_front σ.snd.fst
       if 0 < SudoRt.listLen t.snd then do
         let s ← Doubledeal.suit_of t.fst
         let k ← SudoRt.modI s (SudoRt.listLen t.snd)
         if 0 < k then do
           let hand ← Doubledeal.left_rotate t.snd k
           let y ← passkeyCutPushCont t.fst hand σ.snd.snd
           match y with
           | .ret r => pure (SudoRt.Flow.ret r)
           | .brk fs => pure (SudoRt.Flow.brk (σ.fst, fs))
           | .cont fs =>
             if σ.fst = toV then
               pure (SudoRt.Flow.brk (σ.fst, fs))
             else
               (fun a => SudoRt.Flow.cont (a, fs)) <$> SudoRt.addI σ.fst (1 : Int)
         else do
           let y ← passkeyCutPushCont t.fst t.snd σ.snd.snd
           match y with
           | .ret r => pure (SudoRt.Flow.ret r)
           | .brk fs => pure (SudoRt.Flow.brk (σ.fst, fs))
           | .cont fs =>
             if σ.fst = toV then
               pure (SudoRt.Flow.brk (σ.fst, fs))
             else
               (fun a => SudoRt.Flow.cont (a, fs)) <$> SudoRt.addI σ.fst (1 : Int)
       else do
         let y ← passkeyCutPushCont t.fst t.snd σ.snd.snd
         match y with
         | .ret r => pure (SudoRt.Flow.ret r)
         | .brk fs => pure (SudoRt.Flow.brk (σ.fst, fs))
         | .cont fs =>
           if σ.fst = toV then
             pure (SudoRt.Flow.brk (σ.fst, fs))
           else
             (fun a => SudoRt.Flow.cont (a, fs)) <$> SudoRt.addI σ.fst (1 : Int)) =
      passkeyStepGen toV σ := by
  unfold passkeyStepGen
  dsimp
  by_cases hgt : σ.fst > toV
  · simp [hgt]
  · simp [hgt]
    cases hd : Doubledeal.drop_front σ.snd.fst with
    | error e => simp [hd]
    | ok t =>
      simp only [hd, ok_bind]
      cases t with
      | mk c hand =>
        simp only
        have hn := passkey_nested_match c hand σ.snd.snd σ.fst toV
        -- unfold proof-side names to the residual `dsimp` of `passkeyStepGen`
        simpa [passkeyPiles, passkeyRotateIf, passkeyCutPush, passkeyCutFlag] using hn

/-- Residual cut / push after `dsimp` (`<$>` flags) equals `passkeyCutPushCont`. -/
theorem passkey_inlined_cut_eq (c : Int) (hand key : Array Int) :
    (do
      let x ←
        if 0 < SudoRt.listLen hand then
          (fun a => decide (a < SudoRt.listLen hand)) <$> Doubledeal.rank_of c
        else pure false
      let x_1 ←
        if 0 < SudoRt.listLen key then
          (fun a => decide (a < SudoRt.listLen key)) <$> Doubledeal.rank_of c
        else pure false
      if x then do
        let r ← Doubledeal.rank_of c
        let hand ← Doubledeal.left_rotate hand r
        (fun a => SudoRt.Flow.cont (hand, a)) <$> Doubledeal.push_front key c
      else if x_1 then do
        let r ← Doubledeal.rank_of c
        let key ← Doubledeal.left_rotate key r
        (fun a => SudoRt.Flow.cont (hand, a)) <$> Doubledeal.push_front key c
      else
        (fun a => SudoRt.Flow.cont (hand, a)) <$> Doubledeal.push_front key c) =
      passkeyCutPushCont c hand key := by
  unfold passkeyCutPushCont passkeyCutFlag
  by_cases hp : 0 < SudoRt.listLen hand
  · simp [hp]
    first | done | {
      by_cases hk : 0 < SudoRt.listLen key
      · simp [hk]
        first | done | {
          cases hR : Doubledeal.rank_of c with
          | error e => simp [hR]
          | ok r => simp [hR]
        }
      · simp [hk]
        first | done | {
          cases hR : Doubledeal.rank_of c with
          | error e => simp [hR]
          | ok r => simp [hR]
        }
    }
  · simp [hp]
    first | done | {
      by_cases hk : 0 < SudoRt.listLen key
      · simp [hk]
        first | done | {
          cases hR : Doubledeal.rank_of c with
          | error e => simp [hR]
          | ok r => simp [hR]
        }
      · simp [hk]
        first | done | {
          cases hP : Doubledeal.push_front key c with
          | error e => simp [hP]
          | ok key' => simp [hP]
        }
    }

/-- Unfolded `Doubledeal.passkey` is the twin `runLoopOn` at `fromV = 1`. -/
theorem passkey_eq_twin_loop (deck : Array Int) :
    Doubledeal.passkey deck =
      SudoRt.runLoopOn (ρ := Array Int)
        ((1 : Int), (deck, (#[] : Array Int)))
        (fuelRange (1 : Int) (SudoRt.listLen deck))
        (passkeyStepGen (SudoRt.listLen deck))
        (fun σ => .ok σ.2.2)
        (fun r => .ok r) := by
  unfold Doubledeal.passkey
  dsimp (config := { zeta := true })
  rw [except_bind_pure, fuelRange_eq]
  have hafter :
      (fun σ : Int × Array Int × Array Int =>
        (pure σ.snd.snd : Except SudoRt.Trap (Array Int))) =
        fun σ => .ok σ.2.2 := rfl
  have hon :
      (fun r : Array Int => (pure r : Except SudoRt.Trap (Array Int))) =
        fun r => .ok r := rfl
  rw [hafter, hon]
  apply runLoopOn_step_pointwise (step' := passkeyStepGen (SudoRt.listLen deck))
  intro σ
  refine Eq.trans ?_ (passkey_step_eq (SudoRt.listLen deck) σ)
  -- generated residual (inlined cut / push) vs `passkeyCutPushCont` form
  by_cases hgt : σ.fst > SudoRt.listLen deck
  · simp [hgt]
  · simp [hgt]
    cases hd : Doubledeal.drop_front σ.snd.fst with
    | error e => simp [hd]
    | ok t =>
      simp [hd]
      cases t with
      | mk c hand =>
        simp
        by_cases hp : 0 < SudoRt.listLen hand
        · simp [hp]
          cases hs : Doubledeal.suit_of c with
          | error e => simp [hs]
          | ok s =>
            simp [hs]
            cases hk : SudoRt.modI s (SudoRt.listLen hand) with
            | error e => simp [hk]
            | ok k =>
              simp [hk]
              by_cases hq : 0 < k
              · simp [hq]
                cases hr : Doubledeal.left_rotate hand k with
                | error e => simp [hr]
                | ok hand' =>
                  simp [hr]
                  unfold passkeyCutPushCont passkeyCutFlag
                  by_cases hH : 0 < SudoRt.listLen hand'
                  · simp [hH]
                    first | done | {
                      by_cases hK : 0 < SudoRt.listLen σ.snd.snd
                      · simp [hK]
                        first | done | {
                          cases hR : Doubledeal.rank_of c with
                          | error e => simp [hR]
                          | ok r =>
                            simp [hR, ite_int_beq, beq_int_iff]
                            try rfl
                        }
                      · simp [hK]
                        first | done | {
                          cases hR : Doubledeal.rank_of c with
                          | error e => simp [hR]
                          | ok r =>
                            simp [hR, ite_int_beq, beq_int_iff]
                            try rfl
                        }
                    }
                  · simp [hH]
                    first | done | {
                      by_cases hK : 0 < SudoRt.listLen σ.snd.snd
                      · simp [hK]
                        first | done | {
                          cases hR : Doubledeal.rank_of c with
                          | error e => simp [hR]
                          | ok r =>
                            simp [hR, ite_int_beq, beq_int_iff]
                            try rfl
                        }
                      · simp [hK]
                        first | done | {
                          cases hP : Doubledeal.push_front σ.snd.snd c with
                          | error e => simp [hP]
                          | ok key' => simp [hP, ite_int_beq, beq_int_iff]
                        }
                    }
              · simp [hq]
                unfold passkeyCutPushCont passkeyCutFlag
                simp [hp]
                first | done | {
                  by_cases hK : 0 < SudoRt.listLen σ.snd.snd
                  · simp [hK]
                    first | done | {
                      cases hR : Doubledeal.rank_of c with
                      | error e => simp [hR]
                      | ok r =>
                            simp [hR, ite_int_beq, beq_int_iff]
                            try rfl
                    }
                  · simp [hK]
                    first | done | {
                      cases hR : Doubledeal.rank_of c with
                      | error e => simp [hR]
                      | ok r =>
                            simp [hR, ite_int_beq, beq_int_iff]
                            try rfl
                    }
                }
        · simp [hp]
          unfold passkeyCutPushCont passkeyCutFlag
          simp [hp]
          first | done | {
            by_cases hK : 0 < SudoRt.listLen σ.snd.snd
            · simp [hK, hp]
              first | done | {
                cases hR : Doubledeal.rank_of c with
                | error e => simp [hR, hp]
                | ok r =>
                    simp [hR, hp, ite_int_beq, beq_int_iff]
                    try rfl
              }
            · simp [hK, hp]
              first | done | {
                cases hP : Doubledeal.push_front σ.snd.snd c with
                | error e => simp [hP, hp]
                | ok key' => simp [hP, hp, ite_int_beq, beq_int_iff]
              }
          }

/-- On every well-formed list, emitted `passkey` equals the algebraic ledger. -/
theorem passkey_refines (deck : List Nat) (hfits : FitsLen deck.length) :
    Doubledeal.passkey (embed deck) =
      .ok (embed (passToKeyCutFallback deck)) := by
  rw [passkey_eq_twin_loop, listLen_embed]
  simpa [embed_nil] using passkey_twin_refines deck hfits

end DoubleDeal.Link2
