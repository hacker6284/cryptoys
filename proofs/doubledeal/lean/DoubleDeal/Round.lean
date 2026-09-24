/-
  Round / encrypt structure for DoubleDeal (Nr = 6).
  Peel lemma S12 is definitional.
  Proved: encryptNoMix_rt, invUnkeyedWithMix_rt, encrypt1WithMix_rt,
  invFullRound_fullRound, invFullRoundNoMix_fullRoundNoMix,
  applyInvFullRounds_applyFullRounds, encryptN_rt, encrypt6_rt.
  Round keys are abstract pos bijections (PassKey is not required for this stone).
  These are correctness / algebraic theorems, not bit-security.
-/
import DoubleDeal.Basic
import DoubleDeal.Grid
import DoubleDeal.SumRanks
import DoubleDeal.ShiftRows
import DoubleDeal.GridCycle
import DoubleDeal.Compose

namespace DoubleDeal

/-- CHaSeD rank function on Nat card ids. -/
def cardRank (c : Nat) : Nat := rank c

/-- Unkeyed stem without GridCycle: scoopCM ∘ ShiftRows ∘ SumRanks ∘ layCM. -/
def unkeyedNoMix (m : Fin 52 → Nat) : Fin 52 → Nat :=
  scoopColumnMajor (shiftRows (sumRanks cardRank (layColumnMajor m)))

/-- Inverse of unkeyedNoMix. -/
def invUnkeyedNoMix (c : Fin 52 → Nat) : Fin 52 → Nat :=
  scoopColumnMajor (invSumRanks cardRank (invShiftRows (layColumnMajor c)))

theorem invUnkeyedNoMix_unkeyedNoMix (m : Fin 52 → Nat) :
    invUnkeyedNoMix (unkeyedNoMix m) = m := by
  simp only [invUnkeyedNoMix, unkeyedNoMix]
  rw [lay_scoop_columnMajor, invShiftRows_shiftRows, invSumRanks_sumRanks,
      scoop_lay_columnMajor]

/-- Unkeyed stem with MixColumns (matches SPEC §3.9 full round body before Compose):
    mixColumns ∘ scoopCM ∘ ShiftRows ∘ SumRanks ∘ layCM. -/
def unkeyedWithMix (m : Fin 52 → Nat) : Fin 52 → Nat :=
  mixColumns (unkeyedNoMix m)

/-- Inverse: invUnkeyedNoMix ∘ invMixColumns. -/
def invUnkeyedWithMix (c : Fin 52 → Nat) : Fin 52 → Nat :=
  invUnkeyedNoMix (invMixColumns c)

theorem invUnkeyedWithMix_rt (m : Fin 52 → Nat) :
    invUnkeyedWithMix (unkeyedWithMix m) = m := by
  simp only [invUnkeyedWithMix, unkeyedWithMix]
  rw [invMixColumns_mixColumns, invUnkeyedNoMix_unkeyedNoMix]

/-- S12 peel (no-mix): fullRoundNoMix = Compose ∘ unkeyedNoMix. -/
def fullRoundNoMix (m : Fin 52 → Nat) (pos : Fin 52 → Fin 52) : Fin 52 → Nat :=
  DoubleDeal.composeVec 52 Nat (unkeyedNoMix m) pos

theorem fullRoundNoMix_peel (m : Fin 52 → Nat) (pos : Fin 52 → Fin 52) :
    fullRoundNoMix m pos = DoubleDeal.composeVec 52 Nat (unkeyedNoMix m) pos := rfl

/-- Full round with mix: Compose ∘ unkeyedWithMix (SPEC §3.9 full round). -/
def fullRound (m : Fin 52 → Nat) (pos : Fin 52 → Fin 52) : Fin 52 → Nat :=
  DoubleDeal.composeVec 52 Nat (unkeyedWithMix m) pos

theorem fullRound_peel (m : Fin 52 → Nat) (pos : Fin 52 → Fin 52) :
    fullRound m pos = DoubleDeal.composeVec 52 Nat (unkeyedWithMix m) pos := rfl

def invFullRoundNoMix (c : Fin 52 → Nat) (_pos invPos : Fin 52 → Fin 52) : Fin 52 → Nat :=
  invUnkeyedNoMix (fun i => c (invPos i))

def invFullRound (c : Fin 52 → Nat) (_pos invPos : Fin 52 → Fin 52) : Fin 52 → Nat :=
  invUnkeyedWithMix (fun i => c (invPos i))

/-- Reduced encrypt: whitening Compose + one no-mix round. -/
def encryptNoMix (m : Fin 52 → Nat)
    (pos0 pos1 : Fin 52 → Fin 52)
    (invPos0 invPos1 : Fin 52 → Fin 52)
    (_h0L : ∀ j, invPos0 (pos0 j) = j) (_h0R : ∀ i, pos0 (invPos0 i) = i)
    (_h1L : ∀ j, invPos1 (pos1 j) = j) (_h1R : ∀ i, pos1 (invPos1 i) = i) :
    Fin 52 → Nat :=
  let m1 := DoubleDeal.composeVec 52 Nat m pos0
  fullRoundNoMix m1 pos1

def decryptNoMix (c : Fin 52 → Nat)
    (pos0 pos1 : Fin 52 → Fin 52)
    (invPos0 invPos1 : Fin 52 → Fin 52)
    (_h0L : ∀ j, invPos0 (pos0 j) = j) (_h0R : ∀ i, pos0 (invPos0 i) = i)
    (_h1L : ∀ j, invPos1 (pos1 j) = j) (_h1R : ∀ i, pos1 (invPos1 i) = i) :
    Fin 52 → Nat :=
  let m1 := invFullRoundNoMix c pos1 invPos1
  DoubleDeal.composeVec 52 Nat m1 invPos0

theorem encryptNoMix_rt (m : Fin 52 → Nat)
    (pos0 pos1 invPos0 invPos1 : Fin 52 → Fin 52)
    (h0L : ∀ j, invPos0 (pos0 j) = j) (h0R : ∀ i, pos0 (invPos0 i) = i)
    (h1L : ∀ j, invPos1 (pos1 j) = j) (h1R : ∀ i, pos1 (invPos1 i) = i) :
    decryptNoMix (encryptNoMix m pos0 pos1 invPos0 invPos1 h0L h0R h1L h1R)
      pos0 pos1 invPos0 invPos1 h0L h0R h1L h1R = m := by
  simp only [encryptNoMix, decryptNoMix, fullRoundNoMix, invFullRoundNoMix]
  have step1 :
      (fun i =>
        DoubleDeal.composeVec 52 Nat (unkeyedNoMix (DoubleDeal.composeVec 52 Nat m pos0)) pos1
          (invPos1 i)) =
      unkeyedNoMix (DoubleDeal.composeVec 52 Nat m pos0) := by
    funext i
    simp only [DoubleDeal.composeVec, h1R]
  rw [step1, invUnkeyedNoMix_unkeyedNoMix]
  funext j
  simp only [DoubleDeal.composeVec, h0R]

/-- Whitening + one full round with MixColumns (Nr=1 skeleton matching SPEC §3.9
    without the final no-mix round). -/
def encrypt1WithMix (m : Fin 52 → Nat)
    (pos0 pos1 : Fin 52 → Fin 52)
    (invPos0 invPos1 : Fin 52 → Fin 52)
    (_h0L : ∀ j, invPos0 (pos0 j) = j) (_h0R : ∀ i, pos0 (invPos0 i) = i)
    (_h1L : ∀ j, invPos1 (pos1 j) = j) (_h1R : ∀ i, pos1 (invPos1 i) = i) :
    Fin 52 → Nat :=
  let m1 := DoubleDeal.composeVec 52 Nat m pos0
  fullRound m1 pos1

def decrypt1WithMix (c : Fin 52 → Nat)
    (pos0 pos1 : Fin 52 → Fin 52)
    (invPos0 invPos1 : Fin 52 → Fin 52)
    (_h0L : ∀ j, invPos0 (pos0 j) = j) (_h0R : ∀ i, pos0 (invPos0 i) = i)
    (_h1L : ∀ j, invPos1 (pos1 j) = j) (_h1R : ∀ i, pos1 (invPos1 i) = i) :
    Fin 52 → Nat :=
  let m1 := invFullRound c pos1 invPos1
  DoubleDeal.composeVec 52 Nat m1 invPos0

theorem encrypt1WithMix_rt (m : Fin 52 → Nat)
    (pos0 pos1 invPos0 invPos1 : Fin 52 → Fin 52)
    (h0L : ∀ j, invPos0 (pos0 j) = j) (h0R : ∀ i, pos0 (invPos0 i) = i)
    (h1L : ∀ j, invPos1 (pos1 j) = j) (h1R : ∀ i, pos1 (invPos1 i) = i) :
    decrypt1WithMix (encrypt1WithMix m pos0 pos1 invPos0 invPos1 h0L h0R h1L h1R)
      pos0 pos1 invPos0 invPos1 h0L h0R h1L h1R = m := by
  simp only [encrypt1WithMix, decrypt1WithMix, fullRound, invFullRound]
  have step1 :
      (fun i =>
        DoubleDeal.composeVec 52 Nat (unkeyedWithMix (DoubleDeal.composeVec 52 Nat m pos0)) pos1
          (invPos1 i)) =
      unkeyedWithMix (DoubleDeal.composeVec 52 Nat m pos0) := by
    funext i
    simp only [DoubleDeal.composeVec, h1R]
  rw [step1, invUnkeyedWithMix_rt]
  funext j
  simp only [DoubleDeal.composeVec, h0R]

/-- Single full-round (with MixColumns) is inverted by invFullRound under pos bijection. -/
theorem invFullRound_fullRound (m : Fin 52 → Nat)
    (pos invPos : Fin 52 → Fin 52)
    (_hL : ∀ j, invPos (pos j) = j) (hR : ∀ i, pos (invPos i) = i) :
    invFullRound (fullRound m pos) pos invPos = m := by
  simp only [invFullRound, fullRound]
  have step :
      (fun i => DoubleDeal.composeVec 52 Nat (unkeyedWithMix m) pos (invPos i)) =
      unkeyedWithMix m := by
    funext i
    simp only [DoubleDeal.composeVec, hR]
  rw [step, invUnkeyedWithMix_rt]

/-- Single no-mix final round is inverted by invFullRoundNoMix under pos bijection. -/
theorem invFullRoundNoMix_fullRoundNoMix (m : Fin 52 → Nat)
    (pos invPos : Fin 52 → Fin 52)
    (_hL : ∀ j, invPos (pos j) = j) (hR : ∀ i, pos (invPos i) = i) :
    invFullRoundNoMix (fullRoundNoMix m pos) pos invPos = m := by
  simp only [invFullRoundNoMix, fullRoundNoMix]
  have step :
      (fun i => DoubleDeal.composeVec 52 Nat (unkeyedNoMix m) pos (invPos i)) =
      unkeyedNoMix m := by
    funext i
    simp only [DoubleDeal.composeVec, hR]
  rw [step, invUnkeyedNoMix_unkeyedNoMix]

/-- Apply `n` successive full (with-mix) rounds keyed by `pos 0 .. pos (n-1)`. -/
def applyFullRounds : Nat → (Fin 52 → Nat) → (Nat → Fin 52 → Fin 52) → (Fin 52 → Nat)
  | 0, m, _ => m
  | n + 1, m, pos => fullRound (applyFullRounds n m pos) (pos n)

/-- Peel `n` inv-full rounds from highest index down (`pos (n-1)` first). -/
def applyInvFullRounds : Nat → (Fin 52 → Nat) → (Nat → Fin 52 → Fin 52) →
    (Nat → Fin 52 → Fin 52) → (Fin 52 → Nat)
  | 0, c, _, _ => c
  | n + 1, c, pos, invPos =>
    applyInvFullRounds n (invFullRound c (pos n) (invPos n)) pos invPos

theorem applyInvFullRounds_applyFullRounds (n : Nat) (m : Fin 52 → Nat)
    (pos invPos : Nat → Fin 52 → Fin 52)
    (hL : ∀ r j, invPos r (pos r j) = j)
    (hR : ∀ r i, pos r (invPos r i) = i) :
    applyInvFullRounds n (applyFullRounds n m pos) pos invPos = m := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    simp only [applyFullRounds, applyInvFullRounds]
    have peel :
        invFullRound (fullRound (applyFullRounds n m pos) (pos n)) (pos n) (invPos n) =
        applyFullRounds n m pos :=
      invFullRound_fullRound (applyFullRounds n m pos) (pos n) (invPos n) (hL n) (hR n)
    rw [peel]
    exact ih m

/-- DoubleDeal encrypt with `nMix` MixColumns rounds then one final no-mix round.
    Matches SPEC §3.9 encrypt with Nr = nMix + 1:
    whitening (pos0) → fullRound × nMix (posMix) → finalRound (posFinal). -/
def encryptN (nMix : Nat) (m : Fin 52 → Nat)
    (pos0 : Fin 52 → Fin 52)
    (posMix : Nat → Fin 52 → Fin 52)
    (posFinal : Fin 52 → Fin 52) : Fin 52 → Nat :=
  let m0 := DoubleDeal.composeVec 52 Nat m pos0
  let mm := applyFullRounds nMix m0 posMix
  fullRoundNoMix mm posFinal

/-- Matching decrypt: inv final → invFullRound × nMix → InverseCompose whitening. -/
def decryptN (nMix : Nat) (c : Fin 52 → Nat)
    (_pos0 : Fin 52 → Fin 52) (invPos0 : Fin 52 → Fin 52)
    (posMix invPosMix : Nat → Fin 52 → Fin 52)
    (posFinal invPosFinal : Fin 52 → Fin 52) : Fin 52 → Nat :=
  let mm := invFullRoundNoMix c posFinal invPosFinal
  let m0 := applyInvFullRounds nMix mm posMix invPosMix
  DoubleDeal.composeVec 52 Nat m0 invPos0

theorem encryptN_rt (nMix : Nat) (m : Fin 52 → Nat)
    (pos0 invPos0 : Fin 52 → Fin 52)
    (posMix invPosMix : Nat → Fin 52 → Fin 52)
    (posFinal invPosFinal : Fin 52 → Fin 52)
    (_h0L : ∀ j, invPos0 (pos0 j) = j) (h0R : ∀ i, pos0 (invPos0 i) = i)
    (hMixL : ∀ r j, invPosMix r (posMix r j) = j)
    (hMixR : ∀ r i, posMix r (invPosMix r i) = i)
    (hFL : ∀ j, invPosFinal (posFinal j) = j)
    (hFR : ∀ i, posFinal (invPosFinal i) = i) :
    decryptN nMix (encryptN nMix m pos0 posMix posFinal)
      pos0 invPos0 posMix invPosMix posFinal invPosFinal = m := by
  simp only [encryptN, decryptN]
  have peelFinal :
      invFullRoundNoMix
        (fullRoundNoMix (applyFullRounds nMix (DoubleDeal.composeVec 52 Nat m pos0) posMix)
          posFinal)
        posFinal invPosFinal =
      applyFullRounds nMix (DoubleDeal.composeVec 52 Nat m pos0) posMix :=
    invFullRoundNoMix_fullRoundNoMix
      (applyFullRounds nMix (DoubleDeal.composeVec 52 Nat m pos0) posMix)
      posFinal invPosFinal hFL hFR
  rw [peelFinal]
  have peelMix :
      applyInvFullRounds nMix
        (applyFullRounds nMix (DoubleDeal.composeVec 52 Nat m pos0) posMix)
        posMix invPosMix =
      DoubleDeal.composeVec 52 Nat m pos0 :=
    applyInvFullRounds_applyFullRounds nMix (DoubleDeal.composeVec 52 Nat m pos0)
      posMix invPosMix hMixL hMixR
  rw [peelMix]
  funext j
  simp only [DoubleDeal.composeVec, h0R]

/-- Nr=6: whitening + 5 mix rounds + 1 final no-mix (`nMix = 5`). -/
def encrypt6 (m : Fin 52 → Nat)
    (pos0 : Fin 52 → Fin 52)
    (posMix : Nat → Fin 52 → Fin 52)
    (posFinal : Fin 52 → Fin 52) : Fin 52 → Nat :=
  encryptN 5 m pos0 posMix posFinal

def decrypt6 (c : Fin 52 → Nat)
    (pos0 invPos0 : Fin 52 → Fin 52)
    (posMix invPosMix : Nat → Fin 52 → Fin 52)
    (posFinal invPosFinal : Fin 52 → Fin 52) : Fin 52 → Nat :=
  decryptN 5 c pos0 invPos0 posMix invPosMix posFinal invPosFinal

theorem encrypt6_rt (m : Fin 52 → Nat)
    (pos0 invPos0 : Fin 52 → Fin 52)
    (posMix invPosMix : Nat → Fin 52 → Fin 52)
    (posFinal invPosFinal : Fin 52 → Fin 52)
    (h0L : ∀ j, invPos0 (pos0 j) = j) (h0R : ∀ i, pos0 (invPos0 i) = i)
    (hMixL : ∀ r j, invPosMix r (posMix r j) = j)
    (hMixR : ∀ r i, posMix r (invPosMix r i) = i)
    (hFL : ∀ j, invPosFinal (posFinal j) = j)
    (hFR : ∀ i, posFinal (invPosFinal i) = i) :
    decrypt6 (encrypt6 m pos0 posMix posFinal)
      pos0 invPos0 posMix invPosMix posFinal invPosFinal = m :=
  encryptN_rt 5 m pos0 invPos0 posMix invPosMix posFinal invPosFinal
    h0L h0R hMixL hMixR hFL hFR

end DoubleDeal
