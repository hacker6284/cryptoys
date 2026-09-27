/-
  HEAVY (not in the default build target): kernel witnesses for
  `generated_encrypt_realKey_not_v10Sym_equivariant`. Five full real-schedule
  encryptions evaluated by `decide!`.
  Built and audited by the `doubledeal-security-heavy` CI job
  (`lake build DoubleDealSecurityHeavy`, `check_axioms.py security-heavy`).
  The expected outputs are from the Python port (`checks/ddport.py`, v10); the
  kernel checks them, so a wrong value fails the build.
-/
import DoubleDealSecurity.RealKey

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-- (PROVED, kernel `decide!`) Identity message, identity master key. -/
theorem realKey_enc_id :
    encryptDeck (toDeck idDeck) (List.range 52) = [21, 18, 4, 13, 22, 44, 34, 39, 30, 23, 38, 48, 24, 27, 40, 45, 41, 5, 31, 16, 28, 2, 20, 29, 11, 50, 1, 12, 37, 26, 9, 25, 33, 49, 3, 51, 10, 35, 17, 7, 0, 6, 43, 32, 42, 19, 46, 36, 47, 14, 8, 15] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 1 0 · id`, identity master key. -/
theorem realKey_enc_v10Sym10 :
    encryptDeck (toDeck (rel (v10Sym 1 0) idDeck)) (List.range 52) = [5, 15, 25, 6, 30, 39, 37, 44, 2, 24, 1, 11, 47, 29, 35, 7, 26, 38, 14, 21, 22, 17, 48, 31, 46, 45, 18, 43, 36, 23, 28, 13, 41, 51, 34, 16, 42, 50, 33, 19, 32, 4, 0, 49, 3, 10, 40, 20, 12, 8, 9, 27] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 0 1 · id`, identity master key. -/
theorem realKey_enc_v10Sym01 :
    encryptDeck (toDeck (rel (v10Sym 0 1) idDeck)) (List.range 52) = [37, 30, 5, 15, 13, 43, 49, 35, 26, 18, 23, 17, 10, 34, 50, 40, 25, 0, 3, 21, 38, 41, 44, 51, 4, 27, 11, 39, 31, 8, 20, 46, 32, 14, 7, 36, 28, 33, 1, 24, 6, 9, 29, 47, 2, 12, 19, 22, 45, 16, 42, 48] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 0 2 · id`, identity master key. -/
theorem realKey_enc_v10Sym02 :
    encryptDeck (toDeck (rel (v10Sym 0 2) idDeck)) (List.range 52) = [21, 31, 36, 49, 45, 7, 4, 17, 50, 43, 16, 26, 32, 6, 37, 29, 28, 35, 11, 5, 41, 34, 33, 0, 27, 1, 48, 42, 19, 14, 44, 2, 20, 8, 18, 25, 51, 24, 9, 47, 13, 12, 38, 30, 10, 15, 22, 3, 23, 46, 40, 39] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 0 3 · id`, identity master key. -/
theorem realKey_enc_v10Sym03 :
    encryptDeck (toDeck (rel (v10Sym 0 3) idDeck)) (List.range 52) = [31, 21, 46, 45, 17, 37, 48, 30, 13, 4, 28, 36, 6, 23, 33, 14, 11, 32, 16, 1, 8, 42, 29, 50, 22, 19, 27, 51, 43, 40, 34, 18, 35, 5, 38, 2, 3, 0, 9, 25, 47, 12, 20, 49, 39, 7, 44, 10, 41, 15, 24, 26] := by
  decide!

/-- (PROVED) `v10Sym 1 0` does not commute with the identity-key encrypt. -/
theorem v10Sym10_not_commutes_realE : ¬ CommutesOnDecks (v10Sym 1 0) realE :=
  not_commutesOnDecks_of_witness _ (by rw [realKey_enc_v10Sym10, realKey_enc_id]; decide)

/-- (PROVED) `v10Sym 0 1` does not commute with the identity-key encrypt. -/
theorem v10Sym01_not_commutes_realE : ¬ CommutesOnDecks (v10Sym 0 1) realE :=
  not_commutesOnDecks_of_witness _ (by rw [realKey_enc_v10Sym01, realKey_enc_id]; decide)

/-- (PROVED) `v10Sym 0 2` does not commute with the identity-key encrypt. -/
theorem v10Sym02_not_commutes_realE : ¬ CommutesOnDecks (v10Sym 0 2) realE :=
  not_commutesOnDecks_of_witness _ (by rw [realKey_enc_v10Sym02, realKey_enc_id]; decide)

/-- (PROVED) `v10Sym 0 3` does not commute with the identity-key encrypt. -/
theorem v10Sym03_not_commutes_realE : ¬ CommutesOnDecks (v10Sym 0 3) realE :=
  not_commutesOnDecks_of_witness _ (by rw [realKey_enc_v10Sym03, realKey_enc_id]; decide)

/-- (PROVED) One real master key breaks every nontrivial v10Sym relabelling.

    Under the master key `List.range 52` (the identity deck), expanded by the
    real PassKey chain exactly as the emitted `Doubledeal.encrypt` does, no
    nontrivial `v10Sym a x` commutes with encryption: some deck message `M`
    has `E_K(σM) ≠ σ E_K(M)`.

    Scope. Read this narrowly:
    - One key, and an atypical one: the identity deck. Nothing is claimed
      about any other master key.
    - The message is shown to exist but is not named. The proof goes through
      the subgroup of commuting relabellings and four witnesses
      (`v10Sym 1 0`, `v10Sym 0 1`, `v10Sym 0 2`, `v10Sym 0 3`), so for a given
      σ it does not say which deck breaks it.
    - The key is never relabelled; σ acts on the message and ciphertext only.
    - It rules out exact algebraic symmetry only. It says nothing about
      near-symmetries or statistical distinguishers; v8 and v9 were each
      broken by one (the same-rank and the K♣↔Q♥ swap distinguishers).
    - It is NOT the per-key statement "for every valid master key, no
      nontrivial v10Sym (or σ) commutes". That is open. -/
theorem generated_encrypt_realKey_not_v10Sym_equivariant (a : Fin 13) (x : Fin 4)
    (hax : (a, x) ≠ (0, 0)) :
    ∃ message : List Nat, Perm52 message ∧
      Doubledeal.encrypt (Link2.embed (message.map (v10Sym a x).app))
          (Link2.embed (List.range 52)) ≠
        .ok (Link2.embed ((encryptDeck message (List.range 52)).map (v10Sym a x).app)) := by
  by_contra hne
  push_neg at hne
  have h := commutesOnDecks_v10Sym_reduce a x hax (commutesOnDecks_realE_of_generated _ hne)
  unfold v10SymWitness at h
  split at h
  · exact v10Sym10_not_commutes_realE h
  · rcases x with ⟨x, hx⟩
    match x, hx with
    | 0, _ => contradiction
    | 1, _ => exact v10Sym01_not_commutes_realE h
    | 2, _ => exact v10Sym02_not_commutes_realE h
    | 3, _ => exact v10Sym03_not_commutes_realE h

end DoubleDeal.Security
