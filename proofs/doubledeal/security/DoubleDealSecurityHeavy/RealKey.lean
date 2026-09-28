/-
  HEAVY (not in the default build target): kernel witnesses for
  `generated_encrypt_realKey_not_v10Sym_equivariant`. Five full real-schedule
  encryptions evaluated by `decide!`.
  Built and audited by the `doubledeal-security-heavy` CI job
  (`lake build DoubleDealSecurityHeavy`, `check_axioms.py security-heavy`).
  The expected outputs are from the Python port (`checks/ddport.py`, v11;
  `checks/realkeys/v10sym_subgroup.py`); the kernel checks them, so a wrong value fails the build.
-/
import DoubleDealSecurity.RealKey

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-- (PROVED, kernel `decide!`) Identity message, identity master key. -/
theorem realKey_enc_id :
    encryptDeck (toDeck idDeck) (List.range 52) = [49, 27, 15, 34, 40, 11, 1, 47, 26, 43, 50, 9, 7, 29, 36, 21, 25, 30, 24, 42, 35, 8, 51, 16, 41, 10, 17, 48, 5, 12, 14, 32, 3, 45, 0, 18, 44, 6, 39, 46, 23, 13, 31, 28, 22, 37, 19, 20, 4, 33, 38, 2] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 1 0 · id`, identity master key. -/
theorem realKey_enc_v10Sym10 :
    encryptDeck (toDeck (rel (v10Sym 1 0) idDeck)) (List.range 52) = [38, 46, 3, 25, 40, 30, 41, 24, 50, 26, 2, 27, 7, 13, 1, 9, 31, 44, 43, 23, 12, 49, 45, 0, 47, 28, 10, 51, 29, 42, 18, 32, 37, 21, 48, 8, 6, 4, 15, 35, 5, 17, 16, 11, 39, 36, 34, 20, 14, 19, 22, 33] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 0 1 · id`, identity master key. -/
theorem realKey_enc_v10Sym01 :
    encryptDeck (toDeck (rel (v10Sym 0 1) idDeck)) (List.range 52) = [42, 29, 15, 47, 6, 43, 12, 23, 16, 40, 24, 14, 10, 25, 39, 33, 13, 46, 26, 28, 49, 27, 34, 35, 20, 30, 3, 41, 36, 45, 48, 31, 11, 7, 38, 4, 8, 0, 44, 17, 51, 9, 18, 22, 19, 37, 1, 5, 21, 2, 50, 32] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 0 2 · id`, identity master key. -/
theorem realKey_enc_v10Sym02 :
    encryptDeck (toDeck (rel (v10Sym 0 2) idDeck)) (List.range 52) = [12, 8, 49, 15, 9, 22, 0, 30, 6, 36, 14, 32, 31, 18, 45, 38, 39, 3, 47, 25, 40, 35, 16, 26, 19, 24, 33, 7, 46, 4, 44, 23, 20, 41, 37, 29, 10, 51, 28, 27, 17, 5, 42, 13, 1, 21, 34, 43, 11, 2, 48, 50] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 0 3 · id`, identity master key. -/
theorem realKey_enc_v10Sym03 :
    encryptDeck (toDeck (rel (v10Sym 0 3) idDeck)) (List.range 52) = [37, 47, 15, 23, 41, 35, 43, 50, 16, 18, 39, 24, 51, 21, 38, 11, 14, 19, 9, 44, 25, 7, 45, 12, 33, 20, 10, 8, 31, 49, 22, 4, 40, 36, 26, 30, 48, 28, 6, 3, 32, 5, 34, 17, 1, 0, 29, 2, 46, 27, 42, 13] := by
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
