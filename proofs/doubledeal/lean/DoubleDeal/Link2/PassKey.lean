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

/-- Twin loop at the generated `fromV = 1`, `toV = n`, empty key pile.
    `Doubledeal.passkey` residual-stepper glue (do-elaboration / nested
    suit-rotate) is still OPEN; length ≤ 1 uses `passkey_refines_nil_and_singleton`. -/
theorem passkey_twin_refines (deck : List Nat) (hfits : FitsLen deck.length) :
    SudoRt.runLoopOn (ρ := Array Int)
        (Int.ofNat 1, (embed deck, embed []))
        (fuelRange (Int.ofNat 1) (Int.ofNat deck.length))
        (passkeyStepGen (Int.ofNat deck.length))
        (fun σ => .ok σ.2.2) (fun r => .ok r) =
      .ok (embed (passToKeyCutFallback deck)) := by
  simpa [passToKeyCutFallback] using
    passkey_loop_refines deck [] 1 deck.length (by omega) (by simpa using hfits) hfits

end DoubleDeal.Link2
