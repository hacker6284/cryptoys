/-
  VULNERABILITY PROOF (deprecated DoubleDeal v8 only). Proof-only data.

  Witness for the same-rank relabelling distinguisher (README.md next to
  this package). tau swaps KC (id 12) and KD (id 51). `enc` is the EMITTED
  frozen v8 program `Doubledeal_v8.encrypt` (Generated/ from
  primitives/cipher/doubledeal/v8/doubledeal_v8.sudo).

  Checking: `lake exe doubledeal_v8_witness` evaluates `enc` on the witness
  (compiled code; TAP-style evidence, like Generated TAP). Kernel `decide`
  of the full 6-round `enc` was attempted and exceeded ~14 GB RAM, so the
  E_K equalities are NOT kernel theorems here. `cipherTau_ne` below is a
  small kernel-checked fact about the data. Not a probability bound; not a
  sudo<->Lean theorem (Link 1 open).
-/
import Doubledeal_v8

namespace DoubleDealV8.Witness

/-- tau = KC(12) <-> KD(51), as a relabelling of card values. -/
def tau (c : Nat) : Nat := if c = 12 then 51 else if c = 51 then 12 else c

def embed (xs : List Nat) : Array Int := Array.mk (xs.map Int.ofNat)

def key : List Nat := [18, 9, 29, 34, 51, 39, 5, 21, 38, 22, 30, 36, 43, 49, 33, 20, 41, 17, 24, 13, 0, 46, 42, 48, 45, 44, 16, 35, 25, 27, 6, 10, 28, 12, 19, 3, 26, 8, 47, 15, 31, 23, 7, 50, 40, 11, 32, 14, 37, 1, 2, 4]
def message : List Nat := [49, 40, 34, 14, 18, 16, 6, 45, 23, 37, 29, 3, 11, 9, 21, 30, 7, 20, 32, 46, 48, 47, 17, 36, 33, 41, 2, 42, 38, 26, 31, 51, 25, 10, 13, 35, 5, 24, 19, 22, 4, 8, 15, 39, 50, 43, 28, 0, 44, 12, 27, 1]
def cipher : List Nat := [42, 23, 9, 29, 19, 30, 6, 21, 41, 7, 18, 8, 27, 20, 34, 37, 13, 5, 48, 1, 51, 11, 49, 44, 24, 2, 38, 26, 43, 25, 46, 32, 36, 50, 15, 45, 12, 3, 22, 14, 16, 10, 0, 35, 39, 47, 31, 40, 28, 17, 33, 4]

/-- Relabelled message and relabelled cipher (tau applied cardwise). -/
def messageTau : List Nat := message.map tau
def cipherTau : List Nat := cipher.map tau

/-- Emitted v8 encrypt, as an Option (Trap has no DecidableEq). -/
def enc (m k : List Nat) : Option (Array Int) :=
  (Doubledeal_v8.encrypt (embed m) (embed k)).toOption

/-- The relabelling is not trivial on this ciphertext: tau moves KC/KD in it. -/
theorem cipherTau_ne : cipherTau ≠ cipher := by decide

end DoubleDealV8.Witness
