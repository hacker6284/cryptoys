/-
  M13: the eight exported hash KATs as theorems about Generated `v_Hash`.

  Each KAT is stated once, on the strings of the generated `Vectors.lean`
  (`vectors/json_to_lean.py --check` ties those to the v2 KAT JSON):

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

  Cost: roughly 45 s of kernel evaluation per block (16 blocks in total), so
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
      Em.posOfLists [19, 3, 4, 10, 6, 16, 14, 9, 12, 8, 13, 0, 1, 15, 17, 7, 5, 11, 18, 2] [2, 2, 2, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 2, 1, 0] [13, 10, 14, 0, 7, 5, 11, 4, 9, 27, 17, 28, 18, 22, 1, 8, 21, 6, 25, 26, 24, 19, 16, 2, 15, 20, 23, 3, 12, 29] [1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_edge_27_1 :
    dmBlock (Em.posOfLists [19, 3, 4, 10, 6, 16, 14, 9, 12, 8, 13, 0, 1, 15, 17, 7, 5, 11, 18, 2] [2, 2, 2, 2, 0, 1, 0, 2, 2, 0, 1, 1, 0, 2, 0, 1, 0, 2, 1, 0] [13, 10, 14, 0, 7, 5, 11, 4, 9, 27, 17, 28, 18, 22, 1, 8, 21, 6, 25, 26, 24, 19, 16, 2, 15, 20, 23, 3, 12, 29] [1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0]) (blockAt (pad (hexBytes Vectors.vec_edge_27.msgHex)) 1) =
      Em.posOfLists [13, 7, 5, 12, 8, 6, 4, 10, 1, 14, 2, 9, 16, 11, 18, 17, 19, 15, 0, 3] [2, 1, 1, 1, 2, 1, 0, 2, 1, 0, 1, 2, 0, 0, 2, 1, 2, 2, 1, 2] [1, 6, 19, 0, 15, 25, 12, 11, 3, 29, 16, 2, 21, 8, 14, 13, 10, 4, 5, 9, 18, 28, 20, 27, 22, 17, 7, 26, 24, 23] [0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1] :=
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
      Em.posOfLists [1, 15, 8, 19, 14, 13, 18, 17, 5, 6, 4, 16, 3, 10, 0, 2, 9, 12, 7, 11] [0, 1, 0, 0, 1, 1, 0, 0, 2, 2, 1, 1, 1, 0, 2, 1, 2, 2, 2, 2] [4, 14, 20, 18, 1, 13, 5, 15, 23, 21, 10, 8, 25, 9, 29, 24, 11, 12, 17, 28, 2, 16, 3, 19, 27, 7, 22, 26, 0, 6] [0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_edge_28_1 :
    dmBlock (Em.posOfLists [1, 15, 8, 19, 14, 13, 18, 17, 5, 6, 4, 16, 3, 10, 0, 2, 9, 12, 7, 11] [0, 1, 0, 0, 1, 1, 0, 0, 2, 2, 1, 1, 1, 0, 2, 1, 2, 2, 2, 2] [4, 14, 20, 18, 1, 13, 5, 15, 23, 21, 10, 8, 25, 9, 29, 24, 11, 12, 17, 28, 2, 16, 3, 19, 27, 7, 22, 26, 0, 6] [0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1]) (blockAt (pad (hexBytes Vectors.vec_edge_28.msgHex)) 1) =
      Em.posOfLists [10, 9, 11, 1, 14, 12, 8, 17, 3, 7, 5, 16, 19, 2, 0, 4, 15, 13, 18, 6] [0, 1, 0, 1, 0, 0, 1, 2, 2, 0, 0, 0, 2, 1, 1, 0, 1, 2, 1, 0] [28, 3, 1, 29, 13, 11, 7, 12, 19, 15, 5, 24, 16, 18, 10, 4, 25, 14, 21, 0, 20, 27, 8, 23, 2, 22, 17, 9, 26, 6] [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0] :=
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
      Em.posOfLists [1, 15, 8, 19, 14, 13, 18, 17, 5, 6, 4, 16, 3, 10, 0, 2, 9, 12, 7, 11] [0, 1, 0, 0, 1, 1, 0, 0, 2, 2, 1, 1, 1, 0, 2, 1, 2, 2, 2, 2] [4, 14, 20, 18, 1, 13, 5, 15, 23, 21, 10, 8, 25, 9, 29, 24, 11, 12, 17, 28, 2, 16, 3, 19, 27, 7, 22, 26, 0, 6] [0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_edge_29_1 :
    dmBlock (Em.posOfLists [1, 15, 8, 19, 14, 13, 18, 17, 5, 6, 4, 16, 3, 10, 0, 2, 9, 12, 7, 11] [0, 1, 0, 0, 1, 1, 0, 0, 2, 2, 1, 1, 1, 0, 2, 1, 2, 2, 2, 2] [4, 14, 20, 18, 1, 13, 5, 15, 23, 21, 10, 8, 25, 9, 29, 24, 11, 12, 17, 28, 2, 16, 3, 19, 27, 7, 22, 26, 0, 6] [0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1]) (blockAt (pad (hexBytes Vectors.vec_edge_29.msgHex)) 1) =
      Em.posOfLists [5, 0, 8, 15, 14, 3, 2, 11, 17, 6, 9, 19, 1, 13, 10, 12, 16, 18, 7, 4] [1, 2, 1, 0, 1, 1, 2, 2, 0, 1, 2, 1, 2, 2, 2, 0, 0, 2, 1, 1] [1, 22, 7, 6, 2, 21, 8, 23, 11, 28, 5, 19, 15, 26, 25, 0, 24, 20, 3, 13, 18, 14, 10, 4, 29, 27, 17, 12, 16, 9] [1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0] :=
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
      Em.posOfLists [18, 7, 11, 0, 3, 19, 9, 14, 2, 8, 12, 17, 5, 6, 1, 4, 13, 15, 10, 16] [1, 1, 2, 1, 2, 0, 1, 0, 2, 1, 2, 2, 2, 0, 1, 1, 0, 0, 2, 0] [27, 20, 6, 24, 4, 21, 17, 13, 19, 12, 16, 3, 23, 18, 11, 26, 2, 15, 22, 29, 1, 10, 8, 14, 9, 0, 7, 25, 28, 5] [1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_56_1 :
    dmBlock (Em.posOfLists [18, 7, 11, 0, 3, 19, 9, 14, 2, 8, 12, 17, 5, 6, 1, 4, 13, 15, 10, 16] [1, 1, 2, 1, 2, 0, 1, 0, 2, 1, 2, 2, 2, 0, 1, 1, 0, 0, 2, 0] [27, 20, 6, 24, 4, 21, 17, 13, 19, 12, 16, 3, 23, 18, 11, 26, 2, 15, 22, 29, 1, 10, 8, 14, 9, 0, 7, 25, 28, 5] [1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1]) (blockAt (pad (hexBytes Vectors.vec_multi_56.msgHex)) 1) =
      Em.posOfLists [14, 12, 6, 3, 4, 10, 2, 16, 11, 5, 7, 18, 15, 19, 9, 13, 17, 1, 0, 8] [1, 1, 0, 1, 0, 1, 0, 0, 2, 2, 1, 0, 2, 0, 1, 1, 2, 2, 2, 2] [12, 11, 8, 20, 29, 19, 10, 27, 0, 21, 4, 1, 13, 14, 16, 26, 28, 25, 23, 15, 22, 24, 17, 9, 5, 3, 6, 18, 2, 7] [0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_56_2 :
    dmBlock (Em.posOfLists [14, 12, 6, 3, 4, 10, 2, 16, 11, 5, 7, 18, 15, 19, 9, 13, 17, 1, 0, 8] [1, 1, 0, 1, 0, 1, 0, 0, 2, 2, 1, 0, 2, 0, 1, 1, 2, 2, 2, 2] [12, 11, 8, 20, 29, 19, 10, 27, 0, 21, 4, 1, 13, 14, 16, 26, 28, 25, 23, 15, 22, 24, 17, 9, 5, 3, 6, 18, 2, 7] [0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1]) (blockAt (pad (hexBytes Vectors.vec_multi_56.msgHex)) 2) =
      Em.posOfLists [8, 9, 5, 13, 11, 0, 19, 14, 1, 10, 4, 17, 7, 16, 15, 12, 6, 2, 18, 3] [1, 2, 1, 0, 1, 0, 0, 0, 2, 2, 2, 1, 2, 2, 0, 0, 1, 0, 1, 0] [18, 27, 19, 1, 11, 9, 7, 4, 12, 21, 28, 6, 8, 5, 14, 23, 25, 16, 15, 13, 2, 3, 22, 20, 24, 17, 26, 10, 29, 0] [0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0] :=
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
      Em.posOfLists [11, 14, 7, 18, 2, 13, 19, 16, 8, 1, 4, 6, 12, 3, 17, 15, 10, 0, 5, 9] [1, 2, 0, 1, 1, 2, 2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 2, 1, 0, 2] [18, 17, 5, 29, 21, 0, 16, 23, 27, 4, 26, 14, 15, 20, 11, 10, 3, 12, 7, 24, 2, 6, 13, 9, 19, 8, 28, 22, 1, 25] [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_100_1 :
    dmBlock (Em.posOfLists [11, 14, 7, 18, 2, 13, 19, 16, 8, 1, 4, 6, 12, 3, 17, 15, 10, 0, 5, 9] [1, 2, 0, 1, 1, 2, 2, 1, 1, 1, 1, 0, 0, 0, 0, 0, 2, 1, 0, 2] [18, 17, 5, 29, 21, 0, 16, 23, 27, 4, 26, 14, 15, 20, 11, 10, 3, 12, 7, 24, 2, 6, 13, 9, 19, 8, 28, 22, 1, 25] [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1]) (blockAt (pad (hexBytes Vectors.vec_multi_100.msgHex)) 1) =
      Em.posOfLists [0, 19, 2, 5, 10, 3, 17, 9, 4, 15, 16, 13, 14, 8, 11, 6, 12, 1, 18, 7] [2, 0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 2, 2, 2, 0, 0, 0, 0] [13, 4, 25, 1, 2, 11, 22, 29, 19, 26, 14, 9, 6, 16, 8, 3, 23, 17, 20, 28, 12, 5, 27, 15, 18, 24, 21, 10, 0, 7] [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_100_2 :
    dmBlock (Em.posOfLists [0, 19, 2, 5, 10, 3, 17, 9, 4, 15, 16, 13, 14, 8, 11, 6, 12, 1, 18, 7] [2, 0, 1, 0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 2, 2, 2, 0, 0, 0, 0] [13, 4, 25, 1, 2, 11, 22, 29, 19, 26, 14, 9, 6, 16, 8, 3, 23, 17, 20, 28, 12, 5, 27, 15, 18, 24, 21, 10, 0, 7] [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1]) (blockAt (pad (hexBytes Vectors.vec_multi_100.msgHex)) 2) =
      Em.posOfLists [12, 18, 1, 11, 17, 2, 19, 16, 14, 4, 0, 3, 10, 7, 13, 15, 5, 9, 8, 6] [2, 0, 2, 0, 1, 1, 2, 2, 0, 1, 1, 0, 0, 1, 2, 0, 2, 2, 0, 2] [20, 24, 0, 7, 1, 16, 21, 10, 3, 17, 15, 22, 9, 5, 18, 23, 27, 4, 19, 6, 12, 14, 25, 13, 2, 28, 11, 26, 8, 29] [0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem step_multi_100_3 :
    dmBlock (Em.posOfLists [12, 18, 1, 11, 17, 2, 19, 16, 14, 4, 0, 3, 10, 7, 13, 15, 5, 9, 8, 6] [2, 0, 2, 0, 1, 1, 2, 2, 0, 1, 1, 0, 0, 1, 2, 0, 2, 2, 0, 2] [20, 24, 0, 7, 1, 16, 21, 10, 3, 17, 15, 22, 9, 5, 18, 23, 27, 4, 19, 6, 12, 14, 25, 13, 2, 28, 11, 26, 8, 29] [0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1]) (blockAt (pad (hexBytes Vectors.vec_multi_100.msgHex)) 3) =
      Em.posOfLists [13, 4, 17, 19, 10, 11, 5, 8, 7, 3, 1, 18, 15, 9, 2, 0, 14, 12, 6, 16] [0, 2, 2, 1, 1, 0, 0, 2, 0, 1, 2, 1, 0, 2, 1, 0, 0, 2, 0, 1] [5, 18, 16, 24, 9, 17, 15, 22, 25, 12, 27, 20, 28, 0, 1, 14, 10, 26, 13, 3, 6, 8, 19, 21, 4, 23, 2, 11, 7, 29] [1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0] :=
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
