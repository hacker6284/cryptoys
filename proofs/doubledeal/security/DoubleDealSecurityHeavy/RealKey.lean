/-
  HEAVY (not in the default build target): kernel witnesses for
  `generated_encrypt_realKey_not_v10Sym_equivariant`. Five full real-schedule
  encryptions evaluated by `decide!`.
  Built and audited by the `doubledeal-security-heavy` CI job
  (`lake build DoubleDealSecurityHeavy`, `check_axioms.py security-heavy`).
  The expected outputs are from the Python port (`checks/ddport.py`, v12;
  `checks/realkeys/v10sym_subgroup.py`); the kernel checks them, so a wrong value fails the build.
-/
import DoubleDealSecurity.RealKey

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-- (PROVED, kernel `decide!`) Identity message, identity master key. -/
theorem realKey_enc_id :
    encryptDeck (toDeck idDeck) (List.range 52) = [31, 20, 3, 25, 49, 48, 43, 9, 17, 11, 23, 38, 47, 21, 14, 15, 5, 19, 0, 2, 16, 27, 46, 6, 39, 12, 10, 42, 13, 8, 4, 44, 32, 36, 7, 40, 45, 33, 35, 28, 37, 34, 29, 24, 26, 30, 1, 50, 51, 18, 22, 41] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 1 0 · id`, identity master key. -/
theorem realKey_enc_v10Sym10 :
    encryptDeck (toDeck (rel (v10Sym 1 0) idDeck)) (List.range 52) = [47, 9, 19, 5, 26, 29, 38, 20, 0, 18, 4, 24, 25, 7, 17, 32, 41, 50, 34, 10, 40, 28, 37, 22, 43, 16, 21, 51, 46, 11, 12, 23, 3, 36, 48, 44, 30, 14, 33, 35, 15, 2, 49, 8, 27, 31, 1, 39, 6, 45, 13, 42] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 0 1 · id`, identity master key. -/
theorem realKey_enc_v10Sym01 :
    encryptDeck (toDeck (rel (v10Sym 0 1) idDeck)) (List.range 52) = [23, 8, 51, 3, 20, 32, 19, 11, 33, 16, 31, 6, 17, 9, 14, 12, 46, 2, 4, 0, 34, 39, 22, 15, 48, 29, 45, 28, 44, 36, 43, 21, 38, 1, 27, 10, 42, 26, 13, 40, 47, 5, 35, 24, 7, 30, 50, 18, 37, 49, 25, 41] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 0 2 · id`, identity master key. -/
theorem realKey_enc_v10Sym02 :
    encryptDeck (toDeck (rel (v10Sym 0 2) idDeck)) (List.range 52) = [39, 37, 23, 15, 7, 9, 3, 29, 4, 42, 34, 22, 47, 18, 40, 38, 17, 5, 31, 45, 27, 50, 14, 44, 10, 43, 16, 12, 49, 41, 51, 46, 6, 33, 36, 0, 19, 32, 8, 11, 26, 2, 20, 25, 28, 1, 30, 13, 35, 24, 21, 48] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v10Sym 0 3 · id`, identity master key. -/
theorem realKey_enc_v10Sym03 :
    encryptDeck (toDeck (rel (v10Sym 0 3) idDeck)) (List.range 52) = [30, 6, 42, 1, 38, 46, 26, 31, 14, 17, 27, 12, 29, 5, 7, 28, 16, 50, 20, 45, 47, 10, 22, 15, 25, 4, 24, 37, 19, 13, 33, 34, 35, 41, 51, 23, 0, 43, 49, 36, 39, 9, 11, 21, 32, 18, 40, 3, 2, 8, 48, 44] := by
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
