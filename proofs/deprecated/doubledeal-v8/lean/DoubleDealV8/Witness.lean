/-
  VULNERABILITY PROOF (deprecated DoubleDeal v8 only). Proof-only data.

  Witness for the same-rank relabelling distinguisher (README.md next to
  this package). tau swaps KC (id 12) and KD (id 51). The data lives in
  `WitnessData.lean`, generated from ../witness_v8.json by
  witness_to_lean.py (CI runs `--check`). `enc` is the EMITTED frozen v8
  program `Doubledeal_v8.encrypt` (Generated/ from
  primitives/cipher/doubledeal/v8/doubledeal_v8.sudo).

  Checking: `lake exe doubledeal_v8_witness` evaluates `enc` on the witness
  (compiled code; TAP-style evidence, like Generated TAP). Kernel `decide`
  of the full 6-round `enc` was attempted and exceeded ~14 GB RAM, so the
  E_K equalities are NOT kernel theorems here. The small facts below
  (the JSON's tau-images are tau applied cardwise, and tau moves the
  cipher) are kernel `decide`. Not a probability bound; not a sudo<->Lean
  theorem (Link 1 open).
-/
import Doubledeal_v8
import DoubleDealV8.WitnessData

namespace DoubleDealV8.Witness

/-- tau = KC(12) <-> KD(51), as a relabelling of card values. -/
def tau (c : Nat) : Nat := if c = tauA then tauB else if c = tauB then tauA else c

def embed (xs : List Nat) : Array Int := Array.mk (xs.map Int.ofNat)

/-- Relabelled message and relabelled cipher (tau applied cardwise). -/
def messageTau : List Nat := message.map tau
def cipherTau : List Nat := cipher.map tau

/-- Emitted v8 encrypt, as an Option (Trap has no DecidableEq). -/
def enc (m k : List Nat) : Option (Array Int) :=
  (Doubledeal_v8.encrypt (embed m) (embed k)).toOption

/-- The witness is for K♣ ↔ K♦. -/
theorem tau_is_kc_kd : tauA = 12 ∧ tauB = 51 := by decide

/-- The JSON's `message_tau` is tau applied to `message`. -/
theorem messageTauJson_eq : messageTauJson = messageTau := by decide

/-- The JSON's `cipher_tau` (recorded E_K(tau M)) is tau applied to `cipher`:
    the relation itself, as a fact about the recorded data. -/
theorem cipherTauJson_eq : cipherTauJson = cipherTau := by decide

/-- The relabelling is not trivial on this ciphertext: tau moves KC/KD in it. -/
theorem cipherTau_ne : cipherTau ≠ cipher := by decide

end DoubleDealV8.Witness
