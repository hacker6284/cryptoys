/-
  M13: the eight exported hash KATs as theorems about Generated `v_Hash`.

  Each KAT is stated once, on the strings of the generated `Vectors.lean`
  (`vectors/json_to_lean.py --check` ties those to the v1 KAT JSON):

    kat_<name> : Megadreifach.v_Hash (embed (hexBytes Vectors.vec_<name>.msgHex))
                   = .ok (embed (hexBytes Vectors.vec_<name>.digestHex))

  The generated `KatSpecCheck.lean` (a program run after the heavy build) pins
  the type of each `kat_<name>` to an `Expr` over the real constants, reading no
  syntax from this file, and rejects any `[init]` / `[builtin_init]` in the
  package. A local shadow of `Vectors.vec_*`, `hexBytes`, `embed` or `v_Hash`, or
  an import-time hook, fails it (planted negatives: vectors/katspec_negatives.py).

  Proof: `v_Hash_refines` reduces it to `alg_<name> : vhashAlg msg = digest`,
  kernel-checked (`decide!`; no `native_decide`). One-block KATs are evaluated
  directly. Multi-block KATs go through literal chaining values: each `step_*`
  lemma is one kernel `decide!` on `posL (dmBlock (posOfLists L_k) block_k) =
  L_{k+1}`, and `eq_posOfLists_of_posL` (EmHelpers) turns it back into a
  `Position` equation. Without this, the closure depth of the chained positions
  exhausts memory for 3 or more blocks. The intermediate lists are chaining
  values, not digests; a wrong one fails its `step_*` lemma.

  Cost: roughly 25 s of kernel evaluation per block (16 blocks in total), so
  this module lives in the non-default lean_lib `MegaDreifachHeavy`: build it
  with `lake build MegaDreifachHeavy` (CI job `megadreifach-heavy`,
  proofs-heavy.yml). `maxHeartbeats 0` / `maxRecDepth` are scoped per theorem.
-/
import MegaDreifach.Link2.VHash
import MegaDreifach.Vectors
import MegaDreifach.Hex

namespace MegaDreifach.Link2.Kat

open MegaDreifach MegaDreifach.Link2

/-! ### KAT `empty` (1 block(s)) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem alg_empty : vhashAlg (hexBytes Vectors.vec_empty.msgHex) = hexBytes Vectors.vec_empty.digestHex := by decide!

theorem kat_empty : Megadreifach.v_Hash (embed (hexBytes Vectors.vec_empty.msgHex)) =
    .ok (embed (hexBytes Vectors.vec_empty.digestHex)) := by
  rw [v_Hash_refines _ ⟨by unfold Byte; decide!, by unfold FitsBitlen i64MaxNat; decide!⟩, alg_empty]

/-! ### KAT `short_abc` (1 block(s)) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem alg_short_abc : vhashAlg (hexBytes Vectors.vec_short_abc.msgHex) = hexBytes Vectors.vec_short_abc.digestHex := by decide!

theorem kat_short_abc : Megadreifach.v_Hash (embed (hexBytes Vectors.vec_short_abc.msgHex)) =
    .ok (embed (hexBytes Vectors.vec_short_abc.digestHex)) := by
  rw [v_Hash_refines _ ⟨by unfold Byte; decide!, by unfold FitsBitlen i64MaxNat; decide!⟩, alg_short_abc]

/-! ### KAT `short_one` (1 block(s)) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem alg_short_one : vhashAlg (hexBytes Vectors.vec_short_one.msgHex) = hexBytes Vectors.vec_short_one.digestHex := by decide!

theorem kat_short_one : Megadreifach.v_Hash (embed (hexBytes Vectors.vec_short_one.msgHex)) =
    .ok (embed (hexBytes Vectors.vec_short_one.digestHex)) := by
  rw [v_Hash_refines _ ⟨by unfold Byte; decide!, by unfold FitsBitlen i64MaxNat; decide!⟩, alg_short_one]

/-! ### KAT `edge_27` (2 block(s)) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_edge_27_0 :
    dmBlock (Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo) (blockAt (pad (hexBytes Vectors.vec_edge_27.msgHex)) 0) =
      Em.posOfLists [1, 3, 4, 7, 14, 11, 13, 8, 5, 2, 10, 18, 16, 15, 6, 19, 9, 17, 0, 12] [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 2, 1, 1, 1, 2, 0, 1, 2, 1, 1] [28, 18, 17, 1, 23, 29, 10, 9, 24, 3, 20, 2, 12, 11, 22, 6, 21, 13, 27, 14, 16, 25, 15, 26, 5, 8, 0, 7, 19, 4] [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_edge_27_1 :
    dmBlock (Em.posOfLists [1, 3, 4, 7, 14, 11, 13, 8, 5, 2, 10, 18, 16, 15, 6, 19, 9, 17, 0, 12] [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 2, 1, 1, 1, 2, 0, 1, 2, 1, 1] [28, 18, 17, 1, 23, 29, 10, 9, 24, 3, 20, 2, 12, 11, 22, 6, 21, 13, 27, 14, 16, 25, 15, 26, 5, 8, 0, 7, 19, 4] [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1]) (blockAt (pad (hexBytes Vectors.vec_edge_27.msgHex)) 1) =
      Em.posOfLists [9, 17, 4, 5, 2, 7, 15, 3, 11, 19, 6, 12, 8, 1, 16, 10, 18, 14, 13, 0] [1, 0, 1, 0, 0, 1, 1, 0, 1, 2, 2, 0, 0, 2, 0, 2, 0, 1, 2, 2] [13, 29, 25, 16, 22, 8, 18, 24, 5, 4, 19, 27, 23, 6, 28, 3, 15, 12, 14, 21, 7, 26, 17, 2, 10, 9, 20, 1, 0, 11] [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem alg_edge_27 : vhashAlg (hexBytes Vectors.vec_edge_27.msgHex) = hexBytes Vectors.vec_edge_27.digestHex := by
  unfold vhashAlg
  rw [show (pad (hexBytes Vectors.vec_edge_27.msgHex)).length / 28 = 2 from by decide!]
  rw [chainPre_succ, chainPre_succ, chainPre_zero, ivCook12_eq_lists, step_edge_27_0, step_edge_27_1]
  decide!

theorem kat_edge_27 : Megadreifach.v_Hash (embed (hexBytes Vectors.vec_edge_27.msgHex)) =
    .ok (embed (hexBytes Vectors.vec_edge_27.digestHex)) := by
  rw [v_Hash_refines _ ⟨by unfold Byte; decide!, by unfold FitsBitlen i64MaxNat; decide!⟩, alg_edge_27]

/-! ### KAT `edge_28` (2 block(s)) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_edge_28_0 :
    dmBlock (Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo) (blockAt (pad (hexBytes Vectors.vec_edge_28.msgHex)) 0) =
      Em.posOfLists [13, 6, 7, 8, 1, 14, 15, 12, 11, 17, 3, 5, 0, 19, 18, 9, 2, 16, 10, 4] [1, 1, 2, 0, 1, 2, 2, 2, 0, 0, 1, 2, 2, 0, 1, 1, 1, 1, 2, 2] [10, 19, 23, 16, 25, 3, 7, 15, 22, 5, 1, 17, 21, 9, 0, 8, 13, 24, 29, 28, 26, 27, 14, 18, 20, 12, 6, 11, 2, 4] [0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_edge_28_1 :
    dmBlock (Em.posOfLists [13, 6, 7, 8, 1, 14, 15, 12, 11, 17, 3, 5, 0, 19, 18, 9, 2, 16, 10, 4] [1, 1, 2, 0, 1, 2, 2, 2, 0, 0, 1, 2, 2, 0, 1, 1, 1, 1, 2, 2] [10, 19, 23, 16, 25, 3, 7, 15, 22, 5, 1, 17, 21, 9, 0, 8, 13, 24, 29, 28, 26, 27, 14, 18, 20, 12, 6, 11, 2, 4] [0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0]) (blockAt (pad (hexBytes Vectors.vec_edge_28.msgHex)) 1) =
      Em.posOfLists [17, 15, 14, 7, 19, 6, 18, 8, 5, 16, 0, 4, 2, 11, 1, 12, 13, 10, 3, 9] [1, 0, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 0, 2, 2, 1, 1, 0, 1, 1] [1, 12, 19, 26, 7, 8, 29, 3, 18, 10, 2, 21, 23, 25, 9, 5, 11, 6, 22, 4, 20, 14, 15, 16, 28, 24, 27, 0, 17, 13] [1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem alg_edge_28 : vhashAlg (hexBytes Vectors.vec_edge_28.msgHex) = hexBytes Vectors.vec_edge_28.digestHex := by
  unfold vhashAlg
  rw [show (pad (hexBytes Vectors.vec_edge_28.msgHex)).length / 28 = 2 from by decide!]
  rw [chainPre_succ, chainPre_succ, chainPre_zero, ivCook12_eq_lists, step_edge_28_0, step_edge_28_1]
  decide!

theorem kat_edge_28 : Megadreifach.v_Hash (embed (hexBytes Vectors.vec_edge_28.msgHex)) =
    .ok (embed (hexBytes Vectors.vec_edge_28.digestHex)) := by
  rw [v_Hash_refines _ ⟨by unfold Byte; decide!, by unfold FitsBitlen i64MaxNat; decide!⟩, alg_edge_28]

/-! ### KAT `edge_29` (2 block(s)) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_edge_29_0 :
    dmBlock (Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo) (blockAt (pad (hexBytes Vectors.vec_edge_29.msgHex)) 0) =
      Em.posOfLists [13, 6, 7, 8, 1, 14, 15, 12, 11, 17, 3, 5, 0, 19, 18, 9, 2, 16, 10, 4] [1, 1, 2, 0, 1, 2, 2, 2, 0, 0, 1, 2, 2, 0, 1, 1, 1, 1, 2, 2] [10, 19, 23, 16, 25, 3, 7, 15, 22, 5, 1, 17, 21, 9, 0, 8, 13, 24, 29, 28, 26, 27, 14, 18, 20, 12, 6, 11, 2, 4] [0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_edge_29_1 :
    dmBlock (Em.posOfLists [13, 6, 7, 8, 1, 14, 15, 12, 11, 17, 3, 5, 0, 19, 18, 9, 2, 16, 10, 4] [1, 1, 2, 0, 1, 2, 2, 2, 0, 0, 1, 2, 2, 0, 1, 1, 1, 1, 2, 2] [10, 19, 23, 16, 25, 3, 7, 15, 22, 5, 1, 17, 21, 9, 0, 8, 13, 24, 29, 28, 26, 27, 14, 18, 20, 12, 6, 11, 2, 4] [0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0]) (blockAt (pad (hexBytes Vectors.vec_edge_29.msgHex)) 1) =
      Em.posOfLists [9, 4, 11, 13, 12, 8, 3, 10, 2, 1, 19, 7, 16, 17, 15, 0, 18, 5, 14, 6] [2, 0, 2, 0, 1, 1, 0, 1, 2, 2, 2, 0, 2, 1, 1, 0, 0, 1, 2, 1] [15, 8, 19, 28, 16, 21, 4, 5, 18, 14, 29, 24, 9, 17, 7, 0, 6, 10, 26, 11, 1, 27, 12, 2, 22, 23, 3, 25, 13, 20] [1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem alg_edge_29 : vhashAlg (hexBytes Vectors.vec_edge_29.msgHex) = hexBytes Vectors.vec_edge_29.digestHex := by
  unfold vhashAlg
  rw [show (pad (hexBytes Vectors.vec_edge_29.msgHex)).length / 28 = 2 from by decide!]
  rw [chainPre_succ, chainPre_succ, chainPre_zero, ivCook12_eq_lists, step_edge_29_0, step_edge_29_1]
  decide!

theorem kat_edge_29 : Megadreifach.v_Hash (embed (hexBytes Vectors.vec_edge_29.msgHex)) =
    .ok (embed (hexBytes Vectors.vec_edge_29.digestHex)) := by
  rw [v_Hash_refines _ ⟨by unfold Byte; decide!, by unfold FitsBitlen i64MaxNat; decide!⟩, alg_edge_29]

/-! ### KAT `multi_56` (3 block(s)) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_56_0 :
    dmBlock (Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo) (blockAt (pad (hexBytes Vectors.vec_multi_56.msgHex)) 0) =
      Em.posOfLists [11, 9, 8, 7, 4, 12, 18, 15, 13, 10, 16, 2, 14, 1, 0, 6, 17, 3, 19, 5] [0, 2, 1, 0, 0, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 0, 0, 1, 1] [29, 6, 5, 2, 22, 24, 19, 17, 25, 10, 0, 14, 27, 21, 4, 3, 26, 11, 8, 16, 1, 12, 28, 23, 13, 20, 18, 7, 15, 9] [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_56_1 :
    dmBlock (Em.posOfLists [11, 9, 8, 7, 4, 12, 18, 15, 13, 10, 16, 2, 14, 1, 0, 6, 17, 3, 19, 5] [0, 2, 1, 0, 0, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 0, 0, 1, 1] [29, 6, 5, 2, 22, 24, 19, 17, 25, 10, 0, 14, 27, 21, 4, 3, 26, 11, 8, 16, 1, 12, 28, 23, 13, 20, 18, 7, 15, 9] [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]) (blockAt (pad (hexBytes Vectors.vec_multi_56.msgHex)) 1) =
      Em.posOfLists [3, 18, 11, 19, 7, 13, 15, 17, 14, 6, 5, 10, 2, 4, 12, 1, 16, 8, 9, 0] [0, 0, 0, 0, 1, 2, 1, 2, 2, 1, 0, 2, 1, 2, 1, 1, 1, 0, 1, 0] [20, 16, 29, 17, 28, 7, 11, 1, 25, 22, 5, 27, 21, 8, 3, 4, 6, 0, 14, 10, 19, 24, 13, 26, 2, 23, 9, 12, 18, 15] [1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_56_2 :
    dmBlock (Em.posOfLists [3, 18, 11, 19, 7, 13, 15, 17, 14, 6, 5, 10, 2, 4, 12, 1, 16, 8, 9, 0] [0, 0, 0, 0, 1, 2, 1, 2, 2, 1, 0, 2, 1, 2, 1, 1, 1, 0, 1, 0] [20, 16, 29, 17, 28, 7, 11, 1, 25, 22, 5, 27, 21, 8, 3, 4, 6, 0, 14, 10, 19, 24, 13, 26, 2, 23, 9, 12, 18, 15] [1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1]) (blockAt (pad (hexBytes Vectors.vec_multi_56.msgHex)) 2) =
      Em.posOfLists [3, 9, 12, 16, 13, 17, 7, 2, 11, 8, 14, 0, 15, 4, 10, 18, 19, 6, 5, 1] [1, 2, 0, 2, 1, 2, 0, 0, 2, 0, 1, 0, 2, 0, 2, 1, 1, 2, 2, 0] [26, 20, 4, 16, 13, 2, 15, 29, 18, 17, 22, 27, 5, 8, 24, 1, 25, 19, 0, 7, 28, 11, 3, 6, 23, 21, 12, 14, 9, 10] [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem alg_multi_56 : vhashAlg (hexBytes Vectors.vec_multi_56.msgHex) = hexBytes Vectors.vec_multi_56.digestHex := by
  unfold vhashAlg
  rw [show (pad (hexBytes Vectors.vec_multi_56.msgHex)).length / 28 = 3 from by decide!]
  rw [chainPre_succ, chainPre_succ, chainPre_succ, chainPre_zero, ivCook12_eq_lists, step_multi_56_0, step_multi_56_1, step_multi_56_2]
  decide!

theorem kat_multi_56 : Megadreifach.v_Hash (embed (hexBytes Vectors.vec_multi_56.msgHex)) =
    .ok (embed (hexBytes Vectors.vec_multi_56.digestHex)) := by
  rw [v_Hash_refines _ ⟨by unfold Byte; decide!, by unfold FitsBitlen i64MaxNat; decide!⟩, alg_multi_56]

/-! ### KAT `multi_100` (4 block(s)) -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_100_0 :
    dmBlock (Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo) (blockAt (pad (hexBytes Vectors.vec_multi_100.msgHex)) 0) =
      Em.posOfLists [5, 2, 3, 16, 9, 6, 19, 7, 8, 11, 15, 14, 13, 1, 4, 17, 12, 18, 10, 0] [2, 2, 2, 2, 1, 2, 1, 0, 0, 1, 2, 2, 1, 0, 1, 2, 2, 1, 1, 2] [10, 19, 9, 0, 5, 16, 24, 21, 17, 23, 12, 7, 15, 27, 11, 20, 14, 8, 18, 25, 28, 2, 13, 3, 4, 29, 26, 1, 22, 6] [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_100_1 :
    dmBlock (Em.posOfLists [5, 2, 3, 16, 9, 6, 19, 7, 8, 11, 15, 14, 13, 1, 4, 17, 12, 18, 10, 0] [2, 2, 2, 2, 1, 2, 1, 0, 0, 1, 2, 2, 1, 0, 1, 2, 2, 1, 1, 2] [10, 19, 9, 0, 5, 16, 24, 21, 17, 23, 12, 7, 15, 27, 11, 20, 14, 8, 18, 25, 28, 2, 13, 3, 4, 29, 26, 1, 22, 6] [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]) (blockAt (pad (hexBytes Vectors.vec_multi_100.msgHex)) 1) =
      Em.posOfLists [11, 12, 6, 18, 13, 3, 1, 17, 8, 4, 7, 2, 9, 10, 0, 5, 19, 16, 14, 15] [1, 1, 1, 1, 1, 0, 2, 0, 2, 2, 0, 0, 2, 2, 2, 2, 0, 0, 1, 1] [7, 19, 26, 15, 16, 10, 18, 27, 23, 29, 20, 5, 0, 6, 12, 2, 3, 28, 22, 17, 11, 1, 4, 8, 25, 24, 13, 14, 9, 21] [1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_100_2 :
    dmBlock (Em.posOfLists [11, 12, 6, 18, 13, 3, 1, 17, 8, 4, 7, 2, 9, 10, 0, 5, 19, 16, 14, 15] [1, 1, 1, 1, 1, 0, 2, 0, 2, 2, 0, 0, 2, 2, 2, 2, 0, 0, 1, 1] [7, 19, 26, 15, 16, 10, 18, 27, 23, 29, 20, 5, 0, 6, 12, 2, 3, 28, 22, 17, 11, 1, 4, 8, 25, 24, 13, 14, 9, 21] [1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1]) (blockAt (pad (hexBytes Vectors.vec_multi_100.msgHex)) 2) =
      Em.posOfLists [1, 3, 14, 12, 0, 15, 10, 5, 9, 7, 4, 17, 13, 6, 18, 19, 8, 16, 11, 2] [0, 2, 2, 2, 2, 2, 1, 1, 2, 0, 1, 2, 2, 1, 2, 1, 0, 2, 2, 0] [24, 21, 5, 11, 12, 10, 6, 18, 28, 3, 1, 25, 8, 14, 16, 13, 22, 7, 9, 29, 4, 27, 17, 23, 0, 15, 20, 19, 26, 2] [0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_100_3 :
    dmBlock (Em.posOfLists [1, 3, 14, 12, 0, 15, 10, 5, 9, 7, 4, 17, 13, 6, 18, 19, 8, 16, 11, 2] [0, 2, 2, 2, 2, 2, 1, 1, 2, 0, 1, 2, 2, 1, 2, 1, 0, 2, 2, 0] [24, 21, 5, 11, 12, 10, 6, 18, 28, 3, 1, 25, 8, 14, 16, 13, 22, 7, 9, 29, 4, 27, 17, 23, 0, 15, 20, 19, 26, 2] [0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0]) (blockAt (pad (hexBytes Vectors.vec_multi_100.msgHex)) 3) =
      Em.posOfLists [7, 3, 6, 14, 18, 17, 13, 2, 4, 8, 16, 19, 10, 0, 5, 9, 15, 12, 11, 1] [1, 0, 1, 1, 1, 1, 0, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0] [16, 13, 29, 14, 17, 18, 7, 22, 9, 23, 19, 24, 25, 1, 26, 0, 3, 5, 12, 10, 2, 8, 11, 15, 28, 6, 27, 4, 21, 20] [0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem alg_multi_100 : vhashAlg (hexBytes Vectors.vec_multi_100.msgHex) = hexBytes Vectors.vec_multi_100.digestHex := by
  unfold vhashAlg
  rw [show (pad (hexBytes Vectors.vec_multi_100.msgHex)).length / 28 = 4 from by decide!]
  rw [chainPre_succ, chainPre_succ, chainPre_succ, chainPre_succ, chainPre_zero, ivCook12_eq_lists, step_multi_100_0, step_multi_100_1, step_multi_100_2, step_multi_100_3]
  decide!

theorem kat_multi_100 : Megadreifach.v_Hash (embed (hexBytes Vectors.vec_multi_100.msgHex)) =
    .ok (embed (hexBytes Vectors.vec_multi_100.digestHex)) := by
  rw [v_Hash_refines _ ⟨by unfold Byte; decide!, by unfold FitsBitlen i64MaxNat; decide!⟩, alg_multi_100]

end MegaDreifach.Link2.Kat
