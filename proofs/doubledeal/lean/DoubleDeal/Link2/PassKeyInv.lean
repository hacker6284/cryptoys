/-
  LINK 2. Generated `passkey_inv` refines algebraic `passToKeyCutFallbackInv`
  on the well-formed domain. Proof-only. Not emitter soundness.

  Reuses #26/#28 twin-loop / `runLoopOn` infrastructure and
  `right_rotate_refines`. Does not re-prove `left_rotate` ≃ `rotL`,
  one forward PassKey body, or `passkey_refines`.
-/
import Doubledeal
import DoubleDeal.PassKey
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Append
import DoubleDeal.Link2.Helpers
import DoubleDeal.Link2.Rotate
import DoubleDeal.Link2.PassKey

set_option maxHeartbeats 800000

namespace DoubleDeal.Link2

/-- Sequential undo of the cut (same residual as emitted `passkey_inv`). -/
def passkeyInvCut (c : Int) (hand key : Array Int) :
    Except SudoRt.Trap (Array Int × Array Int) :=
  do
    let cutH ← passkeyCutFlag c hand
    let cutK ← passkeyCutFlag c key
    if cutH = true then do
      let r ← Doubledeal.rank_of c
      let hand ← Doubledeal.right_rotate hand r
      pure (key, hand)
    else if cutK = true then do
      let r ← Doubledeal.rank_of c
      let key ← Doubledeal.right_rotate key r
      pure (key, hand)
    else
      pure (key, hand)

/-- Undo suit-rotate, using the captured pre-cut hand length `n`. -/
def passkeyInvRotateIf (c : Int) (n : Int) (hand : Array Int) :
    Except SudoRt.Trap (Array Int) :=
  if decide (n > (0 : Int)) then do
    let s ← Doubledeal.suit_of c
    let k ← SudoRt.modI s n
    if decide (k > (0 : Int)) then
      Doubledeal.right_rotate hand k
    else
      pure hand
  else
    pure hand

/-- Sequential inverse body after `drop_front`: undo cut, undo suit-rotate,
    push the controller onto the hand. Not a second algorithm. -/
def passkeyInvPiles (c : Int) (hand key : Array Int) :
    Except SudoRt.Trap (Array Int × Array Int) :=
  do
    let n := SudoRt.listLen hand
    let piles ← passkeyInvCut c hand key
    let hand ← passkeyInvRotateIf c n piles.2
    let hand ← Doubledeal.push_front hand c
    pure (piles.1, hand)

/-- Proof-side twin of one generated inverse iteration. State is
    `(i, (key, hand))` matching emitted `passkey_inv`. -/
def passkeyInvStepGen (toV : Int) (σ : Int × Array Int × Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Int × Array Int × Array Int) (Array Int)) :=
  let i := σ.1
  let key := σ.2.1
  let hand := σ.2.2
  if i > toV then
    pure (SudoRt.Flow.brk (i, (key, hand)))
  else do
    let ⟨c, key⟩ ← Doubledeal.drop_front key
    let piles ← passkeyInvPiles c hand key
    if i == toV then
      pure (SudoRt.Flow.brk (i, piles))
    else do
      let i' ← SudoRt.addI i (1 : Int)
      pure (SudoRt.Flow.cont (i', piles))

theorem passkeyCutFlag_refines (c : Nat) (xs : List Nat) :
    passkeyCutFlag (Int.ofNat c) (embed xs) =
      .ok (decide (0 < xs.length ∧ DoubleDeal.rank c < xs.length)) := by
  unfold passkeyCutFlag
  simpa using rank_lt_flag c xs

theorem maybeCutInv_refines (c : Nat) (hand key : List Nat)
    (hh : FitsLen hand.length) (hk : FitsLen key.length) :
    passkeyInvCut (Int.ofNat c) (embed hand) (embed key) =
      .ok (embed (maybeCutInv hand key c).2,
           embed (maybeCutInv hand key c).1) := by
  unfold passkeyInvCut
  rw [passkeyCutFlag_refines, passkeyCutFlag_refines]
  simp only [ok_bind]
  by_cases hH : 0 < hand.length ∧ rank c < hand.length
  · simp [decide_eq_true hH]
    rw [rank_of_refines_natCast]
    simp only [ok_bind, map_ok]
    rw [right_rotate_refines hand (rank c) hh]
    unfold maybeCutInv
    rw [dif_pos hH]
    have hcut : cutProperInv hand (rank c) = rotR hand (rank c) := by
      unfold cutProperInv
      simp [hH.2]
    rw [hcut]
    rfl
  · have hnotH : ¬ (decide (0 < hand.length ∧ rank c < hand.length) = true) := by
      rw [decide_eq_false hH]; decide
    rw [if_neg hnotH]
    by_cases hK : 0 < key.length ∧ rank c < key.length
    · simp [decide_eq_true hK]
      rw [rank_of_refines_natCast]
      simp only [ok_bind, map_ok]
      rw [right_rotate_refines key (rank c) hk]
      unfold maybeCutInv
      rw [dif_neg hH, dif_pos hK]
      have hcut : cutProperInv key (rank c) = rotR key (rank c) := by
        unfold cutProperInv
        simp [hK.2]
      rw [hcut]
      rfl
    · have hnotK : ¬ (decide (0 < key.length ∧ rank c < key.length) = true) := by
        rw [decide_eq_false hK]; decide
      rw [if_neg hnotK]
      unfold maybeCutInv
      rw [dif_neg hH, dif_neg hK]
      rfl

theorem maybeRotateInv_refines (c : Nat) (hand : List Nat)
    (hfits : FitsLen hand.length) :
    passkeyInvRotateIf (Int.ofNat c) (SudoRt.listLen (embed hand)) (embed hand) =
      .ok (embed (maybeRotateInv hand c)) := by
  unfold passkeyInvRotateIf
  rw [listLen_embed]
  by_cases hpos : 0 < hand.length
  · have hdec : decide (Int.ofNat hand.length > (0 : Int)) = true := by
      rw [decide_ofNat_pos]
      exact decide_eq_true hpos
    rw [if_pos hdec]
    rw [suit_of_refines]
    simp only [ok_bind]
    have hne : hand.length ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    have hmod : SudoRt.modI (Int.ofNat (suit c)) (Int.ofNat hand.length) =
        .ok (Int.ofNat (suit c % hand.length)) :=
      modI_ofNat (suit c) hne
    rw [hmod]
    simp only [ok_bind]
    by_cases hk0 : suit c % hand.length = 0
    · have hdec0 : decide (Int.ofNat (suit c % hand.length) > (0 : Int)) = false := by
        rw [hk0, decide_ofNat_pos]
        decide
      have hneB : ¬ (decide (Int.ofNat (suit c % hand.length) > (0 : Int)) = true) := by
        rw [hdec0]; decide
      rw [if_neg hneB]
      apply congrArg Except.ok
      apply congrArg embed
      unfold maybeRotateInv
      rw [if_neg hne, hk0]
      exact (rotR_mod_zero hand 0 hne (Nat.zero_mod _)).symm
    · have hdec0 : decide (Int.ofNat (suit c % hand.length) > (0 : Int)) = true := by
        rw [decide_ofNat_pos]
        exact decide_eq_true (Nat.pos_of_ne_zero hk0)
      rw [if_pos hdec0]
      rw [right_rotate_refines hand (suit c % hand.length) hfits]
      apply congrArg Except.ok
      apply congrArg embed
      unfold maybeRotateInv
      rw [if_neg hne]
  · have hneg : ¬ (decide (Int.ofNat hand.length > (0 : Int)) = true) := by
      rw [decide_ofNat_pos, decide_eq_false hpos]; decide
    rw [if_neg hneg]
    apply congrArg Except.ok
    apply congrArg embed
    unfold maybeRotateInv
    have : hand.length = 0 :=
      Nat.le_antisymm (Nat.not_lt.mp hpos) (Nat.zero_le _)
    rw [if_pos this]

theorem maybeRotateInv_refines_len (c : Nat) (hand : List Nat) (n : Nat)
    (hfits : FitsLen hand.length) (hn : n = hand.length) :
    passkeyInvRotateIf (Int.ofNat c) (Int.ofNat n) (embed hand) =
      .ok (embed (maybeRotateInv hand c)) := by
  subst hn
  simpa [listLen_embed] using maybeRotateInv_refines c hand hfits

/-- One generated inverse body refines `invPassKeyStep`. Piles are
    `(key, hand)` matching emitted state, opposite the algebraic pair. -/
theorem invPassKeyStep_refines (c : Nat) (rest hand : List Nat)
    (hh : FitsLen hand.length) (hk : FitsLen rest.length) :
    passkeyInvPiles (Int.ofNat c) (embed hand) (embed rest) =
      .ok (embed (invPassKeyStep hand (c :: rest)).2,
           embed (invPassKeyStep hand (c :: rest)).1) := by
  unfold passkeyInvPiles
  have hc := maybeCutInv_refines c hand rest hh hk
  rw [hc]
  simp only [ok_bind]
  have hlen1 := length_maybeCutInv_fst hand rest c
  have hh' : FitsLen (maybeCutInv hand rest c).1.length := by
    rw [hlen1]; exact hh
  rw [listLen_embed]
  have hr := maybeRotateInv_refines_len c (maybeCutInv hand rest c).1
    hand.length hh' (by rw [hlen1])
  rw [hr]
  simp only [ok_bind]
  have hrotlen : (maybeRotateInv (maybeCutInv hand rest c).1 c).length = hand.length := by
    rw [length_maybeRotateInv, hlen1]
  have hh'' : FitsLen (maybeRotateInv (maybeCutInv hand rest c).1 c).length := by
    rw [hrotlen]; exact hh
  rw [push_front_refines c _ hh'']
  simp [invPassKeyStep]

theorem passkeyInvStepGen_gt (toV i : Int) (key hand : Array Int) (h : i > toV) :
    passkeyInvStepGen toV (i, (key, hand)) = .ok (.brk (i, (key, hand))) := by
  unfold passkeyInvStepGen
  rw [if_pos h]
  rfl

theorem passkeyInvStepGen_hit (c : Nat) (rest hand : List Nat) (fromN toN : Nat)
    (hfrom : fromN ≤ toN) (hfitsK : FitsLen (rest.length + 1))
    (hfitsH : FitsLen hand.length)
    (hfitsI : fromN = toN ∨ FitsLen (fromN + 1)) :
    passkeyInvStepGen (Int.ofNat toN)
        (Int.ofNat fromN, (embed (c :: rest), embed hand)) =
      if fromN = toN then
        .ok (.brk (Int.ofNat fromN,
          (embed (invPassKeyStep hand (c :: rest)).2,
           embed (invPassKeyStep hand (c :: rest)).1)))
      else
        .ok (.cont (Int.ofNat (fromN + 1),
          (embed (invPassKeyStep hand (c :: rest)).2,
           embed (invPassKeyStep hand (c :: rest)).1))) := by
  unfold passkeyInvStepGen
  have hngt : ¬ (Int.ofNat fromN > Int.ofNat toN) :=
    Int.not_lt.mpr (Int.ofNat_le.mpr hfrom)
  rw [if_neg hngt]
  rw [drop_front_refines c rest hfitsK]
  simp only [ok_bind]
  have hbody := invPassKeyStep_refines c rest hand hfitsH
    (FitsLen.of_le hfitsK (Nat.le_succ _))
  rw [hbody]
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

/-- Empty remaining range: the stepper breaks and `after` returns the hand. -/
theorem passkey_inv_loop_gt (fromV toV : Int) (key hand : Array Int)
    (hgt : fromV > toV) :
    SudoRt.runLoopOn (ρ := Array Int) (fromV, (key, hand))
        (fuelRange fromV toV) (passkeyInvStepGen toV)
        (fun σ => .ok σ.2.2) (fun r => .ok r) =
      .ok hand := by
  rw [fuelRange_gt hgt, show 1 = 0 + 1 from rfl, runLoopOn_succ]
  rw [passkeyInvStepGen_gt toV fromV key hand hgt]

/-- Inclusive inverse loop on embed-image piles refines `passKeyInvGoN`.
    Remaining seats equal remaining key cards (`toN + 1 - fromN`). -/
theorem passkey_inv_loop_refines (key hand : List Nat) (fromN toN : Nat)
    (hcard : toN + 1 - fromN = key.length)
    (hsum : FitsLen (key.length + hand.length))
    (hto : FitsLen toN) :
    SudoRt.runLoopOn (ρ := Array Int)
        (Int.ofNat fromN, (embed key, embed hand))
        (fuelRange (Int.ofNat fromN) (Int.ofNat toN))
        (passkeyInvStepGen (Int.ofNat toN))
        (fun σ => .ok σ.2.2) (fun r => .ok r) =
      .ok (embed (passKeyInvGoN key.length key hand)) := by
  generalize hrem : toN + 1 - fromN = rem
  induction rem generalizing fromN key hand with
  | zero =>
    have hlen0 : key.length = 0 := by omega
    have hkey : key = [] := List.eq_nil_of_length_eq_zero hlen0
    subst hkey
    have hgt : Int.ofNat fromN > Int.ofNat toN := by
      have : toN + 1 ≤ fromN := by omega
      exact Int.ofNat_lt.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self toN) this)
    rw [passkey_inv_loop_gt (Int.ofNat fromN) (Int.ofNat toN) (embed []) (embed hand) hgt]
    simp [passKeyInvGoN]
  | succ rem ih =>
    have hlen : key.length = rem + 1 := by omega
    match key with
    | [] =>
      simp at hlen
    | c :: rest =>
      have hrest : rest.length = rem := by
        simp [List.length_cons] at hlen
        exact hlen
      have hle : fromN ≤ toN := by omega
      have hfitsK : FitsLen (rest.length + 1) := by
        have : FitsLen ((c :: rest).length + hand.length) := hsum
        simp [List.length_cons] at this
        exact FitsLen.of_le this (Nat.le_add_right _ _)
      have hfitsH : FitsLen hand.length :=
        FitsLen.of_le hsum (Nat.le_add_left _ _)
      have hfitsI : fromN = toN ∨ FitsLen (fromN + 1) := by
        by_cases heq : fromN = toN
        · exact Or.inl heq
        · have : fromN < toN := Nat.lt_of_le_of_ne hle heq
          exact Or.inr (FitsLen.of_le hto (Nat.succ_le_of_lt this))
      rw [fuelRange_le hle, runLoopOn_succ]
      rw [passkeyInvStepGen_hit c rest hand fromN toN hle hfitsK hfitsH hfitsI]
      by_cases heq : fromN = toN
      · rw [if_pos heq]
        have hrem0 : rem = 0 := by omega
        have hnil : rest = [] :=
          List.eq_nil_of_length_eq_zero (hrest.trans hrem0)
        subst hnil
        simp [passKeyInvGoN]
      · rw [if_neg heq]
        have hlt : fromN < toN := Nat.lt_of_le_of_ne hle heq
        have hfuel : toN - fromN =
            fuelRange (Int.ofNat (fromN + 1)) (Int.ofNat toN) := by
          rw [fuelRange_le (Nat.succ_le_of_lt hlt)]
          omega
        rw [hfuel]
        simp only [passKeyInvGoN]
        have hlen1 := length_invPassKeyStep_fst hand c rest
        have hlen2 := length_invPassKeyStep_snd hand c rest
        have ih' := ih
            (invPassKeyStep hand (c :: rest)).2
            (invPassKeyStep hand (c :: rest)).1 (fromN + 1)
            (by rw [hlen2]; omega)
            (by
              rw [hlen1, hlen2]
              have : FitsLen (rest.length + 1 + hand.length) := by
                simpa [List.length_cons] using hsum
              exact (Eq.mp (congrArg FitsLen (by omega)) this))
            (by omega)
        rw [hlen2] at ih'
        exact ih'

/-- Twin loop at the generated `fromV = 1`, `toV = n`, empty hand pile. -/
theorem passkey_inv_twin_refines (deck : List Nat) (hfits : FitsLen deck.length) :
    SudoRt.runLoopOn (ρ := Array Int)
        (Int.ofNat 1, (embed deck, embed []))
        (fuelRange (Int.ofNat 1) (Int.ofNat deck.length))
        (passkeyInvStepGen (Int.ofNat deck.length))
        (fun σ => .ok σ.2.2) (fun r => .ok r) =
      .ok (embed (passToKeyCutFallbackInv deck)) := by
  simpa [passToKeyCutFallbackInv] using
    passkey_inv_loop_refines deck [] 1 deck.length (by omega) (by simpa using hfits) hfits

/-- Residual rotate+push suffix of emitted `passkey_inv` (nested `decide`). -/
def passkeyInvRotatePushCont (c n : Int) (key hand : Array Int) :
    Except SudoRt.Trap (SudoRt.Flow (Array Int × Array Int) (Array Int)) :=
  if decide (n > (0 : Int)) = true then do
    let s ← Doubledeal.suit_of c
    let k ← SudoRt.modI s n
    if decide (k > (0 : Int)) = true then do
      let hand ← Doubledeal.right_rotate hand k
      let hand ← Doubledeal.push_front hand c
      pure (SudoRt.Flow.cont (ρ := Array Int) (key, hand))
    else do
      let hand ← Doubledeal.push_front hand c
      pure (SudoRt.Flow.cont (ρ := Array Int) (key, hand))
  else do
    let hand ← Doubledeal.push_front hand c
    pure (SudoRt.Flow.cont (ρ := Array Int) (key, hand))

/-- Nested rotate+push is sequential `passkeyInvRotateIf` then `push_front`. -/
theorem passkeyInvRotatePushCont_seq (c n : Int) (key hand : Array Int) :
    passkeyInvRotatePushCont c n key hand =
      (do
        let hand ← passkeyInvRotateIf c n hand
        let hand ← Doubledeal.push_front hand c
        pure (SudoRt.Flow.cont (ρ := Array Int) (key, hand))) := by
  unfold passkeyInvRotatePushCont passkeyInvRotateIf
  by_cases hn : 0 < n
  · simp [hn]
    cases hs : Doubledeal.suit_of c with
    | error e => simp [hs]
    | ok s =>
      simp [hs]
      cases hk : SudoRt.modI s n with
      | error e => simp [hk]
      | ok k =>
        simp [hk]
        by_cases hkpos : 0 < k <;> simp [hkpos]
  · simp [hn]

theorem passkeyCutFlag_eq (c : Int) (xs : Array Int) :
    (if 0 < SudoRt.listLen xs then do
      let r ← Doubledeal.rank_of c
      pure (decide (r < SudoRt.listLen xs))
     else (pure false : Except SudoRt.Trap Bool)) =
    passkeyCutFlag c xs := by
  unfold passkeyCutFlag
  by_cases hp : 0 < SudoRt.listLen xs <;> simp [hp]

theorem passkeyCutFlag_eq_decide (c : Int) (xs : Array Int) :
    (if decide (SudoRt.listLen xs > (0 : Int)) = true then do
      let r ← Doubledeal.rank_of c
      pure (decide (r < SudoRt.listLen xs))
     else pure false) = passkeyCutFlag c xs := by
  unfold passkeyCutFlag
  rfl

/-- Residual cut flags plus rotate+push equal sequential `passkeyInvPiles`
    wrapped as `Flow.cont`. Uses the pre-cut hand length as `n`. -/
theorem passkey_inv_nested_as_piles (c : Int) (hand key : Array Int) :
    (do
      let cutH ←
        if decide (SudoRt.listLen hand > (0 : Int)) = true then do
          let r ← Doubledeal.rank_of c
          pure (decide (r < SudoRt.listLen hand))
        else pure false
      let cutK ←
        if decide (SudoRt.listLen key > (0 : Int)) = true then do
          let r ← Doubledeal.rank_of c
          pure (decide (r < SudoRt.listLen key))
        else pure false
      if cutH = true then do
        let r ← Doubledeal.rank_of c
        let hand' ← Doubledeal.right_rotate hand r
        passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand'
      else if cutK = true then do
        let r ← Doubledeal.rank_of c
        let key' ← Doubledeal.right_rotate key r
        passkeyInvRotatePushCont c (SudoRt.listLen hand) key' hand
      else
        passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand) =
      (do
        let piles ← passkeyInvPiles c hand key
        pure (SudoRt.Flow.cont (ρ := Array Int) piles)) := by
  unfold passkeyInvPiles passkeyInvCut passkeyCutFlag
  by_cases hHpos : 0 < SudoRt.listLen hand
  · simp [hHpos]
    cases hR : Doubledeal.rank_of c with
    | error e => simp [hR]
    | ok r =>
      simp [hR]
      by_cases hKpos : 0 < SudoRt.listLen key
      · simp [hKpos]
        by_cases hHcut : r < SudoRt.listLen hand
        · simp [hHcut]
          cases hRot : Doubledeal.right_rotate hand r with
          | error e => simp [hRot]
          | ok hand' =>
            simp [hRot]
            rw [passkeyInvRotatePushCont_seq]
            rfl
        · simp [hHcut]
          by_cases hKcut : r < SudoRt.listLen key
          · simp [hKcut]
            cases hRot : Doubledeal.right_rotate key r with
            | error e => simp [hRot]
            | ok key' =>
              simp [hRot]
              rw [passkeyInvRotatePushCont_seq]
              rfl
          · simp [hKcut]
            rw [passkeyInvRotatePushCont_seq]
            rfl
      · simp [hKpos]
        by_cases hHcut : r < SudoRt.listLen hand
        · simp [hHcut]
          cases hRot : Doubledeal.right_rotate hand r with
          | error e => simp [hRot]
          | ok hand' =>
            simp [hRot]
            rw [passkeyInvRotatePushCont_seq]
            rfl
        · simp [hHcut]
          rw [passkeyInvRotatePushCont_seq]
          rfl
  · simp [hHpos]
    by_cases hKpos : 0 < SudoRt.listLen key
    · simp [hKpos]
      cases hR : Doubledeal.rank_of c with
      | error e => simp [hR]
      | ok r =>
        simp [hR]
        by_cases hKcut : r < SudoRt.listLen key
        · simp [hKcut]
          cases hRot : Doubledeal.right_rotate key r with
          | error e => simp [hRot]
          | ok key' =>
            simp [hRot]
            rw [passkeyInvRotatePushCont_seq]
            rfl
        · simp [hKcut]
          rw [passkeyInvRotatePushCont_seq]
          rfl
    · simp [hKpos]
      rw [passkeyInvRotatePushCont_seq]
      rfl

theorem passkey_inv_flag_map (c n : Int) :
    (if 0 < n then (fun a => decide (a < n)) <$> Doubledeal.rank_of c
     else (pure false : Except SudoRt.Trap Bool)) =
    (if 0 < n then do
      let r ← Doubledeal.rank_of c
      pure (decide (r < n))
     else pure false) := by
  by_cases hp : 0 < n <;> simp [hp]

theorem passkeyInvRotatePushCont_map (c n : Int) (key hand : Array Int) :
    (if 0 < n then do
      let s ← Doubledeal.suit_of c
      let k ← SudoRt.modI s n
      if 0 < k then do
        let hand ← Doubledeal.right_rotate hand k
        (fun a => SudoRt.Flow.cont (ρ := Array Int) (key, a)) <$>
          Doubledeal.push_front hand c
      else
        (fun a => SudoRt.Flow.cont (ρ := Array Int) (key, a)) <$>
          Doubledeal.push_front hand c
     else
      (fun a => SudoRt.Flow.cont (ρ := Array Int) (key, a)) <$>
        Doubledeal.push_front hand c) =
    passkeyInvRotatePushCont c n key hand := by
  unfold passkeyInvRotatePushCont
  by_cases hn : 0 < n <;> simp [hn]

/-- Do-elaboration flattens bound cut flags into nested `if 0 < listLen`. -/
theorem passkey_inv_flags_flatten (c : Int) (hand key : Array Int) :
    (do
      let x ←
        if 0 < SudoRt.listLen hand then do
          let r ← Doubledeal.rank_of c
          pure (decide (r < SudoRt.listLen hand))
        else pure false
      let x_1 ←
        if 0 < SudoRt.listLen key then do
          let r ← Doubledeal.rank_of c
          pure (decide (r < SudoRt.listLen key))
        else pure false
      if x = true then do
        let r ← Doubledeal.rank_of c
        let hand' ← Doubledeal.right_rotate hand r
        passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand'
      else if x_1 = true then do
        let r ← Doubledeal.rank_of c
        let key' ← Doubledeal.right_rotate key r
        passkeyInvRotatePushCont c (SudoRt.listLen hand) key' hand
      else
        passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand) =
    (if 0 < SudoRt.listLen hand then do
      let r ← Doubledeal.rank_of c
      if 0 < SudoRt.listLen key then do
        let r_1 ← Doubledeal.rank_of c
        if r < SudoRt.listLen hand then do
          let r ← Doubledeal.rank_of c
          let hand' ← Doubledeal.right_rotate hand r
          passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand'
        else if r_1 < SudoRt.listLen key then do
          let r ← Doubledeal.rank_of c
          let key' ← Doubledeal.right_rotate key r
          passkeyInvRotatePushCont c (SudoRt.listLen hand) key' hand
        else
          passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand
      else
        if r < SudoRt.listLen hand then do
          let r ← Doubledeal.rank_of c
          let hand' ← Doubledeal.right_rotate hand r
          passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand'
        else
          passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand
     else
      if 0 < SudoRt.listLen key then do
        let r ← Doubledeal.rank_of c
        if r < SudoRt.listLen key then do
          let r ← Doubledeal.rank_of c
          let key' ← Doubledeal.right_rotate key r
          passkeyInvRotatePushCont c (SudoRt.listLen hand) key' hand
        else
          passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand
      else
        passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand) := by
  by_cases hHpos : 0 < SudoRt.listLen hand <;> simp [hHpos]

theorem map_addI_cont (i : Int) (fs : Array Int × Array Int) :
    ((fun a =>
        SudoRt.Flow.cont (ρ := Array Int) (σ := Int × Array Int × Array Int)
          (a, fs)) <$>
      SudoRt.addI i (1 : Int)) =
      (do
        let i' ← SudoRt.addI i (1 : Int)
        pure (SudoRt.Flow.cont (ρ := Array Int) (σ := Int × Array Int × Array Int)
          (i', fs))) := by
  cases h : SudoRt.addI i (1 : Int) with
  | error e => simp [h]
  | ok i' => simp [h]

/-- Matching a `Flow.cont` piles update is sequential `passkeyInvPiles`
    then the loop tail. -/
theorem passkey_inv_nested_match (c : Int) (hand key : Array Int) (i toV : Int) :
    (do
      let y ←
        (do
          let cutH ←
            if decide (SudoRt.listLen hand > (0 : Int)) = true then do
              let r ← Doubledeal.rank_of c
              pure (decide (r < SudoRt.listLen hand))
            else pure false
          let cutK ←
            if decide (SudoRt.listLen key > (0 : Int)) = true then do
              let r ← Doubledeal.rank_of c
              pure (decide (r < SudoRt.listLen key))
            else pure false
          if cutH = true then do
            let r ← Doubledeal.rank_of c
            let hand' ← Doubledeal.right_rotate hand r
            passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand'
          else if cutK = true then do
            let r ← Doubledeal.rank_of c
            let key' ← Doubledeal.right_rotate key r
            passkeyInvRotatePushCont c (SudoRt.listLen hand) key' hand
          else
            passkeyInvRotatePushCont c (SudoRt.listLen hand) key hand)
      match y with
      | .ret r => pure (SudoRt.Flow.ret (ρ := Array Int) r)
      | .brk fs => pure (SudoRt.Flow.brk (i, fs))
      | .cont fs =>
        if (i == toV) = true then
          pure (SudoRt.Flow.brk (i, fs))
        else do
          let i' ← SudoRt.addI i (1 : Int)
          pure (SudoRt.Flow.cont (i', fs))) =
      (do
        let piles ← passkeyInvPiles c hand key
        if (i == toV) = true then
          pure (SudoRt.Flow.brk (i, piles))
        else do
          let i' ← SudoRt.addI i (1 : Int)
          pure (SudoRt.Flow.cont (i', piles))) := by
  rw [passkey_inv_nested_as_piles]
  cases hp : passkeyInvPiles c hand key with
  | error e => simp [hp]
  | ok piles => simp [hp]

/-- Residual stepper after unfold / `dsimp` equals `passkeyInvStepGen`.
    Nested cut / suit-rotate is the emitted shape; the sequential twin is
    not a second algorithm. -/
theorem passkey_inv_step_eq (toV : Int) (σ : Int × Array Int × Array Int) :
    (if σ.fst > toV then
       (pure (SudoRt.Flow.brk (σ.fst, σ.snd.fst, σ.snd.snd)) :
          Except SudoRt.Trap (SudoRt.Flow (Int × Array Int × Array Int) (Array Int)))
     else do
       let t ← Doubledeal.drop_front σ.snd.fst
       let y ←
         (do
           let cutH ←
             if decide (SudoRt.listLen σ.snd.snd > (0 : Int)) = true then do
               let r ← Doubledeal.rank_of t.fst
               pure (decide (r < SudoRt.listLen σ.snd.snd))
             else pure false
           let cutK ←
             if decide (SudoRt.listLen t.snd > (0 : Int)) = true then do
               let r ← Doubledeal.rank_of t.fst
               pure (decide (r < SudoRt.listLen t.snd))
             else pure false
           if cutH = true then do
             let r ← Doubledeal.rank_of t.fst
             let hand' ← Doubledeal.right_rotate σ.snd.snd r
             passkeyInvRotatePushCont t.fst (SudoRt.listLen σ.snd.snd) t.snd hand'
           else if cutK = true then do
             let r ← Doubledeal.rank_of t.fst
             let key' ← Doubledeal.right_rotate t.snd r
             passkeyInvRotatePushCont t.fst (SudoRt.listLen σ.snd.snd) key' σ.snd.snd
           else
             passkeyInvRotatePushCont t.fst (SudoRt.listLen σ.snd.snd) t.snd σ.snd.snd)
       match y with
       | .ret r => pure (SudoRt.Flow.ret r)
       | .brk fs => pure (SudoRt.Flow.brk (σ.fst, fs))
       | .cont fs =>
         if (σ.fst == toV) = true then
           pure (SudoRt.Flow.brk (σ.fst, fs))
         else do
           let i' ← SudoRt.addI σ.fst (1 : Int)
           pure (SudoRt.Flow.cont (i', fs))) =
      passkeyInvStepGen toV σ := by
  unfold passkeyInvStepGen
  dsimp
  by_cases hgt : σ.fst > toV
  · simp [hgt]
  · simp [hgt]
    cases hd : Doubledeal.drop_front σ.snd.fst with
    | error e => simp [hd]
    | ok t =>
      simp only [hd, ok_bind]
      simpa using passkey_inv_nested_match t.fst σ.snd.snd t.snd σ.fst toV

/-- Loop tail after a `Flow.cont` piles update. Explicit so residual
    `__do_lift` binds match this, not a do-elaborated join-point. -/
def passkeyInvLoopTail (i toV : Int) :
    SudoRt.Flow (Array Int × Array Int) (Array Int) →
      Except SudoRt.Trap (SudoRt.Flow (Int × Array Int × Array Int) (Array Int)) :=
  fun y =>
    match y with
    | .ret r => pure (SudoRt.Flow.ret r)
    | .brk fs => pure (SudoRt.Flow.brk (i, fs))
    | .cont fs =>
      if i = toV then
        pure (SudoRt.Flow.brk (i, fs))
      else
        (fun a => SudoRt.Flow.cont (a, fs)) <$> SudoRt.addI i (1 : Int)

/-- Inlined residual suit-rotate+push+tail equals `Cont` then match. -/
theorem passkey_inv_rotate_inlined_eq_cont (c n : Int) (key hand : Array Int)
    (i toV : Int) (hn : 0 < n) :
    (do
      let x ← Doubledeal.suit_of c
      let x ← SudoRt.modI x n
      if 0 < x then do
        let x ← Doubledeal.right_rotate hand x
        let a ← Doubledeal.push_front x c
        if i = toV then
          pure (SudoRt.Flow.brk (i, key, a))
        else
          (fun a_1 => SudoRt.Flow.cont (a_1, key, a)) <$> SudoRt.addI i (1 : Int)
      else do
        let a ← Doubledeal.push_front hand c
        if i = toV then
          pure (SudoRt.Flow.brk (i, key, a))
        else
          (fun a_1 => SudoRt.Flow.cont (a_1, key, a)) <$> SudoRt.addI i (1 : Int)) =
    (do
      let y ← passkeyInvRotatePushCont c n key hand
      match y with
      | .ret r => pure (SudoRt.Flow.ret r)
      | .brk fs => pure (SudoRt.Flow.brk (i, fs))
      | .cont fs =>
        if i = toV then
          pure (SudoRt.Flow.brk (i, fs))
        else
          (fun a => SudoRt.Flow.cont (a, fs)) <$> SudoRt.addI i (1 : Int)) := by
  unfold passkeyInvRotatePushCont
  simp [hn]
  cases hs : Doubledeal.suit_of c with
  | error e => simp [hs]
  | ok s =>
    simp [hs]
    cases hk : SudoRt.modI s n with
    | error e => simp [hk]
    | ok k =>
      simp [hk]
      by_cases hkpos : 0 < k
      · simp [hkpos]
        first | done | {
          cases hr : Doubledeal.right_rotate hand k with
          | error e => simp [hr]
          | ok hand' =>
            simp [hr]
            first | done | {
              cases hp : Doubledeal.push_front hand' c with
              | error e => simp [hp]
              | ok hand'' => simp [hp]
            }
        }
      · simp [hkpos]
        first | done | {
          cases hp : Doubledeal.push_front hand c with
          | error e => simp [hp]
          | ok hand' => simp [hp]
        }

/-- Empty-hand residual (push then loop tail) equals `Cont >>= tail`. -/
theorem passkey_inv_empty_bind_eq_cont (c n : Int) (key hand : Array Int)
    (i toV : Int) (hn : ¬ 0 < n) :
    (Doubledeal.push_front hand c >>= fun a =>
      if i = toV then
        (pure (SudoRt.Flow.brk (i, key, a)) :
          Except SudoRt.Trap (SudoRt.Flow (Int × Array Int × Array Int) (Array Int)))
      else
        (fun a_1 => SudoRt.Flow.cont (a_1, key, a)) <$>
          SudoRt.addI i (1 : Int)) =
      (passkeyInvRotatePushCont c n key hand >>= passkeyInvLoopTail i toV) := by
  unfold passkeyInvRotatePushCont passkeyInvLoopTail
  simp [hn]
  first | done | {
    cases hp : Doubledeal.push_front hand c with
    | error e => simp [hp]
    | ok a => simp [hp]
  }

/-- Unfolded `Doubledeal.passkey_inv` is the twin `runLoopOn` at `fromV = 1`. -/
theorem passkey_inv_eq_twin_loop (deck : Array Int) :
    Doubledeal.passkey_inv deck =
      SudoRt.runLoopOn (ρ := Array Int)
        ((1 : Int), (deck, (#[] : Array Int)))
        (fuelRange (1 : Int) (SudoRt.listLen deck))
        (passkeyInvStepGen (SudoRt.listLen deck))
        (fun σ => .ok σ.2.2)
        (fun r => .ok r) := by
  unfold Doubledeal.passkey_inv
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
  apply runLoopOn_step_pointwise (step' := passkeyInvStepGen (SudoRt.listLen deck))
  intro σ
  refine Eq.trans ?_ (passkey_inv_step_eq (SudoRt.listLen deck) σ)
  by_cases hgt : σ.fst > SudoRt.listLen deck
  · simp [hgt]
  · simp [hgt]
    cases hd : Doubledeal.drop_front σ.snd.fst with
    | error e => simp [hd]
    | ok t =>
      simp only [hd, ok_bind]
      rw [passkey_inv_flag_map, passkey_inv_flag_map]
      by_cases hHpos : 0 < SudoRt.listLen σ.snd.snd
      · simp [hHpos, except_ite_bind]
        cases hR : Doubledeal.rank_of t.fst with
        | error e => simp [hR]
        | ok r =>
          simp [hR, except_ite_bind]
          by_cases hKpos : 0 < SudoRt.listLen t.snd
          · simp [hKpos, except_ite_bind]
            by_cases hHcut : r < SudoRt.listLen σ.snd.snd
            · simp [hHcut, except_ite_bind]
              cases hRot : Doubledeal.right_rotate σ.snd.snd r with
              | error e => simp [hRot]
              | ok hand' =>
                simp [hRot]
                exact passkey_inv_rotate_inlined_eq_cont t.fst
                  (SudoRt.listLen σ.snd.snd) t.snd hand'
                  σ.fst (SudoRt.listLen deck) hHpos
            · simp [hHcut, except_ite_bind]
              by_cases hKcut : r < SudoRt.listLen t.snd
              · simp [hKcut, except_ite_bind]
                cases hRot : Doubledeal.right_rotate t.snd r with
                | error e => simp [hRot]
                | ok key' =>
                  simp [hRot]
                  exact passkey_inv_rotate_inlined_eq_cont t.fst
                    (SudoRt.listLen σ.snd.snd) key' σ.snd.snd
                    σ.fst (SudoRt.listLen deck) hHpos
              · simp [hKcut, except_ite_bind]
                exact passkey_inv_rotate_inlined_eq_cont t.fst
                  (SudoRt.listLen σ.snd.snd) t.snd σ.snd.snd
                  σ.fst (SudoRt.listLen deck) hHpos
          · simp [hKpos, except_ite_bind]
            by_cases hHcut : r < SudoRt.listLen σ.snd.snd
            · simp [hHcut, except_ite_bind]
              cases hRot : Doubledeal.right_rotate σ.snd.snd r with
              | error e => simp [hRot]
              | ok hand' =>
                simp [hRot]
                exact passkey_inv_rotate_inlined_eq_cont t.fst
                  (SudoRt.listLen σ.snd.snd) t.snd hand'
                  σ.fst (SudoRt.listLen deck) hHpos
            · simp [hHcut, except_ite_bind]
              exact passkey_inv_rotate_inlined_eq_cont t.fst
                (SudoRt.listLen σ.snd.snd) t.snd σ.snd.snd
                σ.fst (SudoRt.listLen deck) hHpos
      · simp [hHpos, except_ite_bind]
        by_cases hKpos : 0 < SudoRt.listLen t.snd
        · simp [hKpos, except_ite_bind]
          cases hR : Doubledeal.rank_of t.fst with
          | error e => simp [hR]
          | ok r =>
            simp [hR, except_ite_bind]
            by_cases hKcut : r < SudoRt.listLen t.snd
            · simp [hKcut, except_ite_bind]
              cases hRot : Doubledeal.right_rotate t.snd r with
              | error e => simp [hRot]
              | ok key' =>
                simp [hRot]
                exact passkey_inv_empty_bind_eq_cont t.fst
                  (SudoRt.listLen σ.snd.snd) key' σ.snd.snd
                  σ.fst (SudoRt.listLen deck) hHpos
            · simp [hKcut, except_ite_bind]
              exact passkey_inv_empty_bind_eq_cont t.fst
                (SudoRt.listLen σ.snd.snd) t.snd σ.snd.snd
                σ.fst (SudoRt.listLen deck) hHpos
        · simp [hKpos, except_ite_bind]
          exact passkey_inv_empty_bind_eq_cont t.fst
            (SudoRt.listLen σ.snd.snd) t.snd σ.snd.snd
            σ.fst (SudoRt.listLen deck) hHpos

/-- On every well-formed list, emitted `passkey_inv` equals the algebraic ledger. -/
theorem passkey_inv_refines (deck : List Nat) (hfits : FitsLen deck.length) :
    Doubledeal.passkey_inv (embed deck) =
      .ok (embed (passToKeyCutFallbackInv deck)) := by
  rw [passkey_inv_eq_twin_loop, listLen_embed]
  simpa [embed_nil] using passkey_inv_twin_refines deck hfits

end DoubleDeal.Link2
