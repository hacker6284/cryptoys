/-
  HEAVY (not in the default build target): kernel witnesses for
  `generated_encrypt_realKey_not_v9Sym_equivariant`. Three full real-schedule
  encryptions evaluated by `decide!` (about 45 s of kernel time each).
  Built and audited by the `doubledeal-security-heavy` CI job
  (`lake build DoubleDealSecurityHeavy`, `check_axioms.py security-heavy`).
  The expected outputs are from the Python port (`checks/ddport.py`); the kernel
  checks them, so a wrong value fails the build.
-/
import DoubleDealSecurity.RealKey

namespace DoubleDeal.Security

open DoubleDeal Relabel

/-- The identity deck `A♣, 2♣, …, K♦`. -/
def idDeck : Fin 52 → Nat := fun i => i.val

theorem isDeck_idDeck : IsDeck idDeck := ⟨fun i => i.isLt, fun _ _ h => Fin.ext h⟩

/-- (PROVED, kernel `decide!`) Identity message, identity master key. -/
theorem realKey_enc_id :
    encryptDeck (toDeck idDeck) (List.range 52) = [27, 31, 21, 15, 3, 30, 22, 19, 44, 20, 38, 12, 6, 11, 25, 10, 35, 2, 14, 8, 24, 51, 43, 32, 18, 4, 29, 49, 17, 23, 9, 0, 45, 42, 16, 28, 26, 46, 47, 34, 1, 13, 36, 48, 50, 39, 5, 37, 41, 7, 40, 33] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v9Sym 0 2 · id`, identity master key. -/
theorem realKey_enc_v9Sym02 :
    encryptDeck (toDeck (rel (v9Sym 0 2) idDeck)) (List.range 52) = [38, 5, 37, 16, 33, 11, 27, 6, 24, 32, 44, 42, 19, 26, 9, 18, 50, 51, 49, 21, 36, 13, 14, 8, 25, 30, 46, 4, 23, 7, 29, 1, 2, 28, 35, 48, 31, 22, 3, 45, 41, 47, 40, 12, 0, 10, 34, 39, 20, 15, 17, 43] := by
  decide!

/-- (PROVED, kernel `decide!`) Message `v9Sym 1 0 · id`, identity master key. -/
theorem realKey_enc_v9Sym10 :
    encryptDeck (toDeck (rel (v9Sym 1 0) idDeck)) (List.range 52) = [46, 32, 30, 16, 27, 23, 9, 42, 21, 5, 44, 51, 18, 2, 6, 43, 19, 35, 15, 7, 12, 25, 8, 26, 47, 4, 11, 0, 49, 34, 40, 17, 20, 41, 24, 1, 48, 29, 28, 10, 22, 39, 50, 36, 33, 45, 31, 14, 38, 3, 13, 37] := by
  decide!

theorem realE_toDeck (m : Fin 52 → Nat) :
    toDeck (realE m) = encryptDeck (toDeck m) (List.range 52) := by
  rw [encryptDeck_eq_encryptDeckFn _ _ (length_toDeck m), Link2.ofDeck_toDeck]; rfl

theorem not_commutesOnDecks_of_witness (σ : Relabel)
    (h : encryptDeck (toDeck (rel σ idDeck)) (List.range 52) ≠
      (encryptDeck (toDeck idDeck) (List.range 52)).map σ.app) :
    ¬ CommutesOnDecks σ realE := by
  intro hc
  apply h
  rw [← realE_toDeck, ← realE_toDeck, hc idDeck isDeck_idDeck]
  exact toDeck_map σ.app (realE idDeck)

/-- (PROVED) `v9Sym 0 2` does not commute with the identity-key encrypt. -/
theorem v9Sym02_not_commutes_realE : ¬ CommutesOnDecks (v9Sym 0 2) realE :=
  not_commutesOnDecks_of_witness _ (by rw [realKey_enc_v9Sym02, realKey_enc_id]; decide)

/-- (PROVED) `v9Sym 1 0` does not commute with the identity-key encrypt. -/
theorem v9Sym10_not_commutes_realE : ¬ CommutesOnDecks (v9Sym 1 0) realE :=
  not_commutesOnDecks_of_witness _ (by rw [realKey_enc_v9Sym10, realKey_enc_id]; decide)

/-- (PROVED) One real master key breaks every nontrivial v9Sym relabelling.

    Under the master key `List.range 52` (the identity deck), expanded by the
    real PassKey chain exactly as the emitted `Doubledeal.encrypt` does, no
    nontrivial `v9Sym a b` commutes with encryption: some deck message `M`
    has `E_K(σM) ≠ σ E_K(M)`.

    Scope. Read this narrowly:
    - One key, and an atypical one: the identity deck. Nothing is claimed
      about any other master key.
    - The message is shown to exist but is not named. The proof goes through
      the subgroup of commuting relabellings and two witnesses
      (`v9Sym 0 2`, `v9Sym 1 0`), so for a given σ it does not say which deck
      breaks it.
    - The key is never relabelled; σ acts on the message and ciphertext only.
    - It rules out exact algebraic symmetry only. It says nothing about
      near-symmetries or statistical distinguishers; v8 was broken by one
      (the same-rank distinguisher).
    - It is NOT the per-key statement "for every valid master key, no
      nontrivial v9Sym (or σ) commutes". That is open. -/
theorem generated_encrypt_realKey_not_v9Sym_equivariant (a : Fin 13) (b : Fin 4)
    (hab : (a, b) ≠ (0, 0)) :
    ∃ message : List Nat, Perm52 message ∧
      Doubledeal.encrypt (Link2.embed (message.map (v9Sym a b).app))
          (Link2.embed (List.range 52)) ≠
        .ok (Link2.embed ((encryptDeck message (List.range 52)).map (v9Sym a b).app)) := by
  by_contra hne
  push_neg at hne
  rcases commutesOnDecks_v9Sym_reduce a b hab (commutesOnDecks_realE_of_generated _ hne) with h | h
  · exact v9Sym02_not_commutes_realE h
  · exact v9Sym10_not_commutes_realE h

end DoubleDeal.Security
