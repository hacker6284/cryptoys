/-
  LINK 2. Generated `passkey` refines algebraic `passToKeyCutFallback`
  on the well-formed domain (length fits i64, every card fits i64).
  Proof-only. Not emitter soundness.

  v12: each iteration is `drop_front`, then `deal_step` (Link2/Deal.lean),
  then the rank cut and `push_front` (unchanged from v11).
-/
import Doubledeal
import DoubleDeal.PassKey
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Append
import DoubleDeal.Link2.Helpers
import DoubleDeal.Link2.Rotate
import DoubleDeal.Link2.Deal

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


/-- Sequential form of `passkeyCutPush` on embedded piles: `maybeCut`, then the
    controller on top of the key pile. -/
theorem passkeyCutPush_refines (c : Nat) (hand key : List Nat)
    (hh : FitsLen hand.length) (hk : FitsLen key.length) :
    passkeyCutPush (Int.ofNat c) (embed hand) (embed key) =
      .ok (embed (maybeCut hand key c).1,
           embed (c :: (maybeCut hand key c).2)) := by
  unfold passkeyCutPush passkeyCutFlag
  exact maybeCut_push_refines c hand key hh hk

/-- One generated PassKey body (deal / cut / push) refines `passKeyStep`. -/
theorem passKeyStep_refines (c : Nat) (hand key : List Nat) (hc : FitsLen c)
    (hh : FitsLen hand.length) (hk : FitsLen key.length) :
    (do
      let p ← Doubledeal.deal_step (Int.ofNat c) (embed hand) (embed key)
      passkeyCutPush (Int.ofNat c) p.1 p.2) =
      .ok (embed (passKeyStep hand key c).1,
           embed (passKeyStep hand key c).2) := by
  rw [deal_step_refines c hand key hc hh hk]
  simp only [ok_bind]
  have hh' : FitsLen (maybeDeal hand key c).1.length := by
    rw [length_maybeDeal_fst]; exact hh
  have hk' : FitsLen (maybeDeal hand key c).2.length := by
    rw [length_maybeDeal_snd]; exact hk
  rw [passkeyCutPush_refines c _ _ hh' hk']
  rfl

/-- Proof-side twin of one generated PassKey iteration: `drop_front`, then
    `deal_step`, then the cut / push body. Not a second algorithm. -/
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
      let p ← Doubledeal.deal_step c hand key
      passkeyCutPush c p.1 p.2)
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
    (hfrom : fromN ≤ toN) (hc : FitsLen c) (hfitsH : FitsLen (rest.length + 1))
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
  have hbody := passKeyStep_refines c rest key hc
    (FitsLen.of_le hfitsH (Nat.le_succ _)) hfitsK
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
    Remaining seats equal remaining hand cards (`toN + 1 - fromN`). Every card
    in either pile fits i64 (the deal count `suit + 2` is an i64 addition). -/
theorem passkey_loop_refines (hand key : List Nat) (fromN toN : Nat)
    (hcard : toN + 1 - fromN = hand.length)
    (hsum : FitsLen (hand.length + key.length))
    (hto : FitsLen toN)
    (hcards : ∀ x ∈ hand ++ key, FitsLen x) :
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
      have hc : FitsLen c := hcards c (by simp)
      rw [fuelRange_le hle, runLoopOn_succ]
      rw [passkeyStepGen_hit c rest key fromN toN hle hc hfitsH hfitsK hfitsI]
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
        have hperm := passKeyStep_perm rest key c
        have ih' := ih
            (passKeyStep rest key c).1 (passKeyStep rest key c).2 (fromN + 1)
            (by rw [hlen1]; omega)
            (by
              rw [hlen1, hlen2]
              have : FitsLen (rest.length + 1 + key.length) := by
                simpa [List.length_cons] using hsum
              exact (Eq.mp (congrArg FitsLen (by omega)) this))
            (fun x hx => hcards x (hperm.mem_iff.mp hx))
            (by omega)
        rw [hlen1] at ih'
        exact ih'

/-- Twin loop at the generated `fromV = 1`, `toV = n`, empty key pile. -/
theorem passkey_twin_refines (deck : List Nat) (hfits : FitsLen deck.length)
    (hcards : ∀ x ∈ deck, FitsLen x) :
    SudoRt.runLoopOn (ρ := Array Int)
        (Int.ofNat 1, (embed deck, embed []))
        (fuelRange (Int.ofNat 1) (Int.ofNat deck.length))
        (passkeyStepGen (Int.ofNat deck.length))
        (fun σ => .ok σ.2.2) (fun r => .ok r) =
      .ok (embed (passToKeyCutFallback deck)) := by
  simpa [passToKeyCutFallback] using
    passkey_loop_refines deck [] 1 deck.length (by omega) (by simpa using hfits) hfits
      (by simpa using hcards)

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

/-- A `Flow.cont`-mapped result matched against the loop tail is the plain
    result fed to the `.cont` branch. -/
theorem map_cont_bind {α β γ ρ : Type} (m : Except SudoRt.Trap α) (g : α → β)
    (k : SudoRt.Flow β ρ → Except SudoRt.Trap γ) :
    (do
      let y ← (fun a => SudoRt.Flow.cont (ρ := ρ) (g a)) <$> m
      k y) =
      (do
        let fs ← g <$> m
        k (.cont fs)) := by
  cases m <;> rfl

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
  unfold passkeyStepGen
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
        cases hs : Doubledeal.deal_step c hand σ.snd.snd with
        | error e => simp [hs]
        | ok p =>
          simp [hs]
          unfold passkeyCutPush passkeyCutFlag
          by_cases hH : 0 < SudoRt.listLen p.fst <;>
            by_cases hK : 0 < SudoRt.listLen p.snd <;>
            simp [hH, hK] <;>
            cases hR : Doubledeal.rank_of c <;> simp [hR]
          all_goals
            rename_i r
            by_cases h1 : r < SudoRt.listLen p.fst <;>
              by_cases h2 : r < SudoRt.listLen p.snd <;>
              simp only [h1, h2, ↓reduceIte, bind_assoc] <;>
              first
                | (rw [map_cont_bind])
                | (congr 1; funext x; rw [map_cont_bind])

/-- On every well-formed list whose cards fit i64, emitted `passkey` equals
    the algebraic ledger. -/
theorem passkey_refines (deck : List Nat) (hfits : FitsLen deck.length)
    (hcards : ∀ c ∈ deck, FitsLen c) :
    Doubledeal.passkey (embed deck) =
      .ok (embed (passToKeyCutFallback deck)) := by
  rw [passkey_eq_twin_loop, listLen_embed]
  simpa [embed_nil] using passkey_twin_refines deck hfits hcards

/-- Singleton: the controller is pushed onto an empty key pile (no deal / cut). -/
theorem passkey_singleton (c : Nat) (hc : FitsLen c) :
    Doubledeal.passkey (embed [c]) =
      .ok (embed (passToKeyCutFallback [c])) :=
  passkey_refines [c] FitsLen.one (by simpa using hc)

/-- Length ≤ 1 is the first well-formed slice of `passkey` ≃ `passToKeyCutFallback`. -/
theorem passkey_refines_nil_and_singleton (deck : List Nat)
    (h : deck.length ≤ 1) (hcards : ∀ c ∈ deck, FitsLen c) :
    Doubledeal.passkey (embed deck) =
      .ok (embed (passToKeyCutFallback deck)) := by
  match deck with
  | [] => exact passkey_nil
  | [c] => exact passkey_singleton c (hcards c (by simp))
  | _ :: _ :: _ =>
    simp at h

end DoubleDeal.Link2
