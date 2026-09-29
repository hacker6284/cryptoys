/-
  SECURITY (weakness, proved) — RESULT ABOUT v1 OF THE GRIP RULE.

  A concrete IV-anchored collision of the full hash, kernel-checked: two
  distinct 28-byte messages with the same generated `Megadreifach.v_Hash`.

      M  = e132ebb03ed19b3949820c68d22d8b5004867c3c0ea79f44269e19fb
      M' = e132ebd9724a3c582fca2e7f51a1a34dd82b8afcfcf71344269e19fb

  Both digests are 0084d6d1…c34e82 (computed by the KAT-checked
  `proofs/megadreifach/security/md.py`; the digest value itself is not
  evaluated here, only the equality).

  Mechanism (`security/suit_blind_collision.py`, REPORT §3): φ maps M and M'
  to deals that differ only by swapping cards 5 and 7, Q♥ and Q♠ (same rank,
  so the same held face).  In v1 the Recipe A read comes after the noon turn,
  so here the grips after cards 5, 6, 7 do not depend on which queen comes
  first, and the held-face turns commute with card 6's turns: after card 7 the
  position and the grip are equal, and the remaining 45 cards and the F3
  rounds are identical.  Both messages have the same length, so the padding
  block is the same.

  Cost of the proof: only the 7-card prefixes are evaluated (plain `decide`;
  a few seconds), not the whole block.  `phiUnrank` of the two blocks, the
  pad, and the block split are small `decide`s.  The rest is `List.foldl_append`
  and `v_Hash_refines` (Link 2).

  Grip-rule status: v1.  The statement is about the published hash; it uses
  the concrete `Em.g2Step` (the proof evaluates it) and would simply fail for
  a changed E_m.  It does not use `recipeA_sameCorners`.

  Zero sorry.  No native_decide.
-/
import MegaDreifach.Link2.VHash
import MegaDreifach.Link2.EmIv
import MegaDreifach.Hex

namespace MegaDreifach.Security.SwapCollision

open MegaDreifach MegaDreifach.Link2

/-- The two colliding messages. -/
def msgA : List Nat := hexBytes "e132ebb03ed19b3949820c68d22d8b5004867c3c0ea79f44269e19fb"
def msgB : List Nat := hexBytes "e132ebd9724a3c582fca2e7f51a1a34dd82b8afcfcf71344269e19fb"

/-- First 7 cards of the two deals (cards 5 and 7 swapped: 46 = Q♥, 47 = Q♠). -/
def preA : List Nat := [15, 14, 40, 44, 46, 3, 47]
def preB : List Nat := [15, 14, 40, 44, 47, 3, 46]
/-- The common last 45 cards. -/
def rest : List Nat := [20, 28, 17, 50, 18, 1, 35, 39, 10, 21, 26, 25, 19, 22, 29, 33, 36,
  0, 27, 4, 48, 37, 9, 31, 6, 49, 13, 51, 11, 42, 43, 38, 12, 5, 7, 30, 45, 24, 16, 34, 23, 8,
  41, 32, 2]

/-- Start of a block from IV-COOK12: the IV and the identity grip. -/
def s0 : Position × Em.Grip :=
  (Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo, Em.gripId)

/-- The common state after card 7. -/
def midPos : Position :=
  Em.posOfLists [5, 4, 6, 0, 12, 11, 17, 3, 10, 9, 13, 16, 19, 15, 1, 7, 14, 18, 8, 2]
    [0, 2, 0, 2, 0, 0, 1, 0, 2, 2, 1, 2, 1, 2, 1, 0, 2, 2, 2, 2]
    [8, 5, 18, 7, 26, 11, 0, 29, 22, 9, 24, 10, 13, 27, 1, 20, 15, 16, 4, 23, 19, 3, 17, 6, 25,
      12, 14, 28, 2, 21]
    [0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1]
def midGrip : Em.Grip := fun h => Em.rd [4, 3, 9, 10, 5, 0, 2, 8, 11, 6, 1, 7] 12 (by decide) h.val

theorem dealA : phiUnrank (fromBE msgA) = preA ++ rest := by decide
theorem dealB : phiUnrank (fromBE msgB) = preB ++ rest := by decide

set_option maxRecDepth 100000 in
theorem prefixA : preA.foldl Em.g2Step s0 = (midPos, midGrip) := by
  refine Prod.ext (eq_posOfLists_of_posL _ _ _ _ _ (by decide)) ?_
  funext i; revert i; decide

set_option maxRecDepth 100000 in
theorem prefixB : preB.foldl Em.g2Step s0 = (midPos, midGrip) := by
  refine Prod.ext (eq_posOfLists_of_posL _ _ _ _ _ (by decide)) ?_
  funext i; revert i; decide

/-- The block map rejoins after card 7: equal compression outputs from IV-COOK12. -/
theorem dmBlock_iv_collision : dmBlock Em.ivCook12 msgA = dmBlock Em.ivCook12 msgB := by
  unfold dmBlock Em.dmStep Em.emBlock
  rw [dealA, dealB, show (preA ++ rest).take 52 = preA ++ rest from by decide,
    show (preB ++ rest).take 52 = preB ++ rest from by decide]
  have hs : (Em.ivCook12, Em.gripId) = s0 := by rw [ivCook12_eq_lists]; rfl
  rw [hs, List.foldl_append, List.foldl_append, prefixA, prefixB]

/-- Algebraic hash collision (both messages are 2 blocks after padding; the
second, padding-only block is the same). -/
theorem vhashAlg_collision : vhashAlg msgA = vhashAlg msgB := by
  unfold vhashAlg
  rw [show (pad msgA).length / 28 = 2 from by decide,
    show (pad msgB).length / 28 = 2 from by decide,
    chainPre_succ, chainPre_succ, chainPre_zero,
    chainPre_succ (pad msgB), chainPre_succ (pad msgB), chainPre_zero,
    show blockAt (pad msgA) 0 = msgA from by decide,
    show blockAt (pad msgB) 0 = msgB from by decide,
    show blockAt (pad msgA) 1 = blockAt (pad msgB) 1 from by decide,
    dmBlock_iv_collision]

/-- **IV-anchored collision of MegaDreifach v1 (generated `v_Hash`).** Two
distinct well-formed 28-byte messages with the same digest. -/
theorem v_Hash_swap_collision :
    embed msgA ≠ embed msgB ∧
      Megadreifach.v_Hash (embed msgA) = Megadreifach.v_Hash (embed msgB) := by
  refine ⟨by decide, ?_⟩
  rw [v_Hash_refines _ ⟨by unfold Byte; decide, by unfold FitsBitlen i64MaxNat; decide⟩,
    v_Hash_refines _ ⟨by unfold Byte; decide, by unfold FitsBitlen i64MaxNat; decide⟩,
    vhashAlg_collision]

end MegaDreifach.Security.SwapCollision
