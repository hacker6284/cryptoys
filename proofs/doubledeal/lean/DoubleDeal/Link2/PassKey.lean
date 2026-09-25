/-
  LINK 2. Generated `passkey` refines algebraic `passToKeyCutFallback`
  on the well-formed domain. Proof-only. Not emitter soundness.
-/
import Doubledeal
import DoubleDeal.PassKey
import DoubleDeal.Link2.Embed
import DoubleDeal.Link2.Sudo
import DoubleDeal.Link2.Append

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

/-- Singleton: controller is pushed onto an empty key pile (no rotate / cut). -/
theorem passkey_singleton (c : Nat) :
    Doubledeal.passkey (embed [c]) =
      .ok (embed (passToKeyCutFallback [c])) := by
  have hpk : passToKeyCutFallback [c] = [c] := by
    simp [passToKeyCutFallback, passKeyGoN, passKeyStep, maybeRotate, maybeCut]
  rw [hpk]
  unfold Doubledeal.passkey
  have hlen : SudoRt.listLen (embed [c]) = (1 : Int) := by
    rw [listLen_embed]; rfl
  simp [hlen, embed_nil, listLen_eq]
  rw [show 1 = 0 + 1 from rfl, runLoopOn_succ]
  dsimp
  rw [drop_front_singleton]
  simp only [ok_bind]
  -- hand is empty: skip suit-rotate; empty key: skip cuts; push c
  simp [embed_nil, listLen_eq]
  have hpush : Doubledeal.push_front #[] (c : Int) = .ok (embed [c]) := by
    simpa [embed_nil, ofNat_eq_natCast] using push_front_nil c
  rw [hpush, map_ok]
  rfl

/-- Length ≤ 1 is the first well-formed slice of `passkey` ≃ `passToKeyCutFallback`. -/
theorem passkey_refines_nil_and_singleton (deck : List Nat)
    (h : deck.length ≤ 1) :
    Doubledeal.passkey (embed deck) =
      .ok (embed (passToKeyCutFallback deck)) := by
  match deck with
  | [] => exact passkey_nil
  | [c] => exact passkey_singleton c
  | _ :: _ :: _ =>
    simp at h

end DoubleDeal.Link2
