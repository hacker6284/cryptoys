/-
  VULNERABILITY PROOF (deprecated DoubleDeal v9 only).

  Witness for the K♣↔Q♥ related-plaintext distinguisher (README.md next to
  this package). sigma swaps K♣ (id 12) and Q♥ (id 24). The data lives in
  `WitnessData.lean`, generated from ../witness_v9.json by witness_to_lean.py
  (CI runs `--check`). `Doubledeal_v9.encrypt` is the EMITTED frozen v9 program
  (Generated/ from primitives/cipher/doubledeal/v9/doubledeal_v9.sudo).

  Everything here is checked by the Lean kernel: the stage facts in `Keys`,
  `RunM`, `RunSigma` are `decide!` (kernel reduction), chained by the generic
  lemmas in `Glue`. Nothing is trusted to compiled code (no native decision).

  What this proves: for THIS key and message, E_K(sigma M) = sigma E_K(M) on the
  full 6-round emitted encrypt, and sigma really moves the ciphertext. It is not
  a probability bound: the rate (~3.5e-8 per random pair, vs ~1/52! for an ideal
  cipher) is measured, see ../README.md. Not a sudo<->Lean theorem (Link 1 open).
-/
import DoubleDealV9.Glue
import DoubleDealV9.WitnessData
import DoubleDealV9.Keys
import DoubleDealV9.RunM
import DoubleDealV9.RunSigma

namespace DoubleDealV9.Witness
open DoubleDealV9.Glue

/-- sigma = K♣(12) ↔ Q♥(24), as a relabelling of card values. -/
def sigma (c : Nat) : Nat := if c = sigmaA then sigmaB else if c = sigmaB then sigmaA else c

/-- The witness is for K♣ ↔ Q♥. -/
theorem sigma_is_KC_QH : sigmaA = 12 ∧ sigmaB = 24 := by decide

/-- The key and the message are decks: 52 distinct card ids below 52. -/
theorem key_is_deck : key.length = 52 ∧ key.Nodup ∧ ∀ c ∈ key, c < 52 := by decide
theorem message_is_deck : message.length = 52 ∧ message.Nodup ∧ ∀ c ∈ message, c < 52 := by decide

/-- The JSON's `message_sigma` is sigma applied to `message`. -/
theorem messageSigmaJson_eq : messageSigmaJson = message.map sigma := by decide

/-- The JSON's `cipher_sigma` is sigma applied to `cipher`. -/
theorem cipherSigmaJson_eq : cipherSigmaJson = cipher.map sigma := by decide

/-- The relabelling is not trivial: sigma moves the message and the ciphertext. -/
theorem messageSigma_ne : message.map sigma ≠ message := by decide
theorem cipherSigma_ne : cipher.map sigma ≠ cipher := by decide

/-- (kernel) E_K(M) = C on the emitted full 6-round v9 `encrypt`. -/
theorem encrypt_message :
    Doubledeal_v9.encrypt (embed message) (embed key) = .ok (embed cipher) :=
  encrypt_of_stages _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ expand_keys_key
    msg_whiten msg_round1 msg_round2 msg_round3 msg_round4 msg_round5 msg_final

/-- (kernel) E_K(sigma M) = sigma C on the emitted full 6-round v9 `encrypt`. -/
theorem encrypt_message_sigma :
    Doubledeal_v9.encrypt (embed (message.map sigma)) (embed key) =
      .ok (embed (cipher.map sigma)) := by
  rw [← messageSigmaJson_eq, ← cipherSigmaJson_eq]
  exact encrypt_of_stages _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ expand_keys_key
    sig_whiten sig_round1 sig_round2 sig_round3 sig_round4 sig_round5 sig_final

/-- **Headline (kernel-checked witness).** On the emitted, frozen DoubleDeal v9
    `encrypt` (whitening, 5 full rounds, final round, PassKey schedule), the
    witness key K and message M satisfy E_K(sigma M) = sigma E_K(M) for
    sigma = K♣↔Q♥, and sigma E_K(M) ≠ E_K(M). One input pair; the rate of
    such pairs is a measured claim, not proved here. -/
theorem v9_KC_QH_swap_commutes_on_witness :
    ∃ C : List Nat,
      Doubledeal_v9.encrypt (embed message) (embed key) = .ok (embed C) ∧
      Doubledeal_v9.encrypt (embed (message.map sigma)) (embed key) = .ok (embed (C.map sigma)) ∧
      C.map sigma ≠ C :=
  ⟨cipher, encrypt_message, encrypt_message_sigma, cipherSigma_ne⟩

end DoubleDealV9.Witness
