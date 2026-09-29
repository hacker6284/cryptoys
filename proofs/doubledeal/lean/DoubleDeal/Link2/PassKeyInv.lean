/-
  LINK 2. Generated `passkey_inv` refines algebraic `passToKeyCutFallbackInv`
  on the well-formed domain (length fits i64, every card fits i64).
  Proof-only. Not emitter soundness.

  v12: each inverse iteration is `drop_front` on the key pile, undo the rank
  cut (`right_rotate`), then `undeal_step` (Link2/Deal.lean), then the
  controller back on top of the hand. Reuses the #26/#28 twin-loop /
  `runLoopOn` infrastructure and `right_rotate_refines`.
-/
import Doubledeal
import DoubleDeal.PassKey
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Append
import DoubleDeal.Link2.Helpers
import DoubleDeal.Link2.Rotate
import DoubleDeal.Link2.Deal
import DoubleDeal.Link2.PassKey

set_option maxHeartbeats 800000

namespace DoubleDeal.Link2

/-- Sequential undo of the cut (same residual as emitted `passkey_inv`).
    Returns `(key, hand)`. -/
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

/-- Sequential inverse body after `drop_front`: undo cut, undo deal, push the
    controller onto the hand. Returns `(key, hand)`. Not a second algorithm. -/
def passkeyInvPiles (c : Int) (hand key : Array Int) :
    Except SudoRt.Trap (Array Int × Array Int) :=
  do
    let piles ← passkeyInvCut c hand key
    let p ← Doubledeal.undeal_step c piles.2 piles.1
    let hand ← Doubledeal.push_front p.1 c
    pure (p.2, hand)

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
    unfold maybeCutInv onPile
    rw [if_pos hH]
    have hcut : cutProperInv hand (rank c) = rotR hand (rank c) := by
      unfold cutProperInv
      simp [hH.2]
    simp only [hcut]
    rfl
  · have hnotH : ¬ (decide (0 < hand.length ∧ rank c < hand.length) = true) := by
      rw [decide_eq_false hH]; decide
    rw [if_neg hnotH]
    by_cases hK : 0 < key.length ∧ rank c < key.length
    · simp [decide_eq_true hK]
      rw [rank_of_refines_natCast]
      simp only [ok_bind, map_ok]
      rw [right_rotate_refines key (rank c) hk]
      unfold maybeCutInv onPile
      rw [if_neg hH, if_pos hK]
      have hcut : cutProperInv key (rank c) = rotR key (rank c) := by
        unfold cutProperInv
        simp [hK.2]
      simp only [hcut]
      rfl
    · have hnotK : ¬ (decide (0 < key.length ∧ rank c < key.length) = true) := by
        rw [decide_eq_false hK]; decide
      rw [if_neg hnotK]
      unfold maybeCutInv onPile
      rw [if_neg hH, if_neg hK]
      rfl


/-- One generated inverse body refines `invPassKeyStep`. Piles are
    `(key, hand)` matching emitted state, opposite the algebraic pair. -/
theorem invPassKeyStep_refines (c : Nat) (rest hand : List Nat) (hc : FitsLen c)
    (hh : FitsLen hand.length) (hk : FitsLen rest.length) :
    passkeyInvPiles (Int.ofNat c) (embed hand) (embed rest) =
      .ok (embed (invPassKeyStep hand (c :: rest)).2,
           embed (invPassKeyStep hand (c :: rest)).1) := by
  unfold passkeyInvPiles
  rw [maybeCutInv_refines c hand rest hh hk]
  simp only [ok_bind]
  have hh' : FitsLen (maybeCutInv hand rest c).1.length := by
    rw [length_maybeCutInv_fst]; exact hh
  have hk' : FitsLen (maybeCutInv hand rest c).2.length := by
    rw [length_maybeCutInv_snd]; exact hk
  rw [undeal_step_refines c _ _ hc hh' hk']
  simp only [ok_bind]
  have hh'' : FitsLen (maybeDealInv (maybeCutInv hand rest c).1
      (maybeCutInv hand rest c).2 c).1.length := by
    rw [length_maybeDealInv_fst, length_maybeCutInv_fst]; exact hh
  rw [push_front_refines c _ hh'']
  simp [invPassKeyStep]

theorem passkeyInvStepGen_gt (toV i : Int) (key hand : Array Int) (h : i > toV) :
    passkeyInvStepGen toV (i, (key, hand)) = .ok (.brk (i, (key, hand))) := by
  unfold passkeyInvStepGen
  rw [if_pos h]
  rfl

theorem passkeyInvStepGen_hit (c : Nat) (rest hand : List Nat) (fromN toN : Nat)
    (hfrom : fromN ≤ toN) (hc : FitsLen c) (hfitsK : FitsLen (rest.length + 1))
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
  have hbody := invPassKeyStep_refines c rest hand hc hfitsH
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
    Remaining seats equal remaining key cards (`toN + 1 - fromN`). Every card
    in either pile fits i64 (the deal count `suit + 2` is an i64 addition). -/
theorem passkey_inv_loop_refines (key hand : List Nat) (fromN toN : Nat)
    (hcard : toN + 1 - fromN = key.length)
    (hsum : FitsLen (key.length + hand.length))
    (hto : FitsLen toN)
    (hcards : ∀ x ∈ hand ++ key, FitsLen x) :
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
      have hc : FitsLen c := hcards c (by simp)
      rw [fuelRange_le hle, runLoopOn_succ]
      rw [passkeyInvStepGen_hit c rest hand fromN toN hle hc hfitsK hfitsH hfitsI]
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
        have hperm := invPassKeyStep_perm hand c rest
        have ih' := ih
            (invPassKeyStep hand (c :: rest)).2
            (invPassKeyStep hand (c :: rest)).1 (fromN + 1)
            (by rw [hlen2]; omega)
            (by
              rw [hlen1, hlen2]
              have : FitsLen (rest.length + 1 + hand.length) := by
                simpa [List.length_cons] using hsum
              exact (Eq.mp (congrArg FitsLen (by omega)) this))
            (fun x hx => hcards x (hperm.mem_iff.mp hx))
            (by omega)
        rw [hlen2] at ih'
        exact ih'

/-- Twin loop at the generated `fromV = 1`, `toV = n`, empty hand pile. -/
theorem passkey_inv_twin_refines (deck : List Nat) (hfits : FitsLen deck.length)
    (hcards : ∀ x ∈ deck, FitsLen x) :
    SudoRt.runLoopOn (ρ := Array Int)
        (Int.ofNat 1, (embed deck, embed []))
        (fuelRange (Int.ofNat 1) (Int.ofNat deck.length))
        (passkeyInvStepGen (Int.ofNat deck.length))
        (fun σ => .ok σ.2.2) (fun r => .ok r) =
      .ok (embed (passToKeyCutFallbackInv deck)) := by
  simpa [passToKeyCutFallbackInv] using
    passkey_inv_loop_refines deck [] 1 deck.length (by omega) (by simpa using hfits) hfits
      (by simpa using hcards)

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
  unfold passkeyInvStepGen passkeyInvPiles passkeyInvCut passkeyCutFlag
  by_cases hgt : σ.fst > SudoRt.listLen deck
  · simp [hgt]
  · simp [hgt]
    cases hd : Doubledeal.drop_front σ.snd.fst with
    | error e => simp [hd]
    | ok t =>
      simp [hd]
      cases t with
      | mk c key =>
        simp
        by_cases hH : 0 < SudoRt.listLen σ.snd.snd <;>
          by_cases hK : 0 < SudoRt.listLen key <;>
          simp [hH, hK] <;>
          cases hR : Doubledeal.rank_of c <;> simp [hR]
        all_goals
          rename_i r
          by_cases h1 : r < SudoRt.listLen σ.snd.snd <;>
            by_cases h2 : r < SudoRt.listLen key <;>
            simp only [h1, h2, ↓reduceIte, bind_assoc, map_eq_pure_bind, pure_bind]

/-- On every well-formed list whose cards fit i64, emitted `passkey_inv`
    equals the algebraic ledger. -/
theorem passkey_inv_refines (deck : List Nat) (hfits : FitsLen deck.length)
    (hcards : ∀ c ∈ deck, FitsLen c) :
    Doubledeal.passkey_inv (embed deck) =
      .ok (embed (passToKeyCutFallbackInv deck)) := by
  rw [passkey_inv_eq_twin_loop, listLen_embed]
  simpa [embed_nil] using passkey_inv_twin_refines deck hfits hcards

end DoubleDeal.Link2
