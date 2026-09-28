/-
  M13: the eight exported hash KATs as theorems about Generated `v_Hash`.

  * `kat_*_alg : vhashAlg msg = digest` is kernel-checked (`decide!`; no
    `native_decide`). One-block KATs are evaluated directly. Multi-block KATs
    go through literal chaining values: each `step_*` lemma is one kernel
    `decide!` on `posL (dmBlock (posOfLists L_k) block_k) = L_{k+1}`, and
    `eq_posOfLists_of_posL` turns it back into a `Position` equation.
    Without this, the closure depth of the chained positions exhausts memory
    for 3 or more blocks.
  * `kat_*_hex` ties the byte list to the hex string in `Vectors.lean`.
  * `kat_*` is the Generated statement, through `v_Hash_refines`.

  Cost: roughly 25 s of kernel evaluation per block (16 blocks in total), so
  this module lives in the non-default lean_lib `MegaDreifachHeavy`: build it
  with `lake build MegaDreifachHeavy` (CI job `megadreifach-heavy`,
  proofs-heavy.yml). The theorem names stay in `MegaDreifach.Link2(.Kat)`.
-/
import MegaDreifach.Link2.VHash
import MegaDreifach.Vectors
import MegaDreifach.IV

namespace MegaDreifach.Link2

open MegaDreifach

theorem listOfOri_getD {n m : Nat} (f : Fin n → Fin m) (s : Fin n) :
    (listOfOri f).getD s.val 0 = (f s).val := by
  have hs : s.val < (List.range n).length := by rw [List.length_range]; exact s.isLt
  unfold listOfOri
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hs]
  simp [s.isLt]

theorem rd_listOfOri {n m : Nat} (hm : 0 < m) (f : Fin n → Fin m) (s : Fin n) :
    Em.rd (listOfOri f) m hm s.val = f s := by
  apply Fin.ext
  show (listOfOri f).getD s.val 0 % m = (f s).val
  rw [listOfOri_getD]
  exact Nat.mod_eq_of_lt (f s).isLt

theorem listOf_eq_listOfOri {n : Nat} (f : Fin n → Fin n) : listOf f = listOfOri f := rfl

theorem posOfLists_listOf (p : Position) :
    Em.posOfLists (listOf p.cp) (listOfOri p.co) (listOf p.ep) (listOfOri p.eo) = p := by
  apply Position.ext <;> funext s <;> simp only [Em.posOfLists, listOf_eq_listOfOri] <;>
    exact rd_listOfOri _ _ s

/-- List view of a position. -/
def posL (p : Position) : List (List Nat) :=
  [listOf p.cp, listOfOri p.co, listOf p.ep, listOfOri p.eo]

theorem eq_posOfLists_of_posL (p : Position) (a b c d : List Nat)
    (h : posL p = [a, b, c, d]) : p = Em.posOfLists a b c d := by
  unfold posL at h
  simp only [List.cons.injEq] at h
  obtain ⟨ha, hb, hc, hd, -⟩ := h
  rw [← ha, ← hb, ← hc, ← hd, posOfLists_listOf]


theorem ivCook12_eq_lists :
    Em.ivCook12 = Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo := by
  have h := posOfLists_listOf Em.ivCook12
  rw [ivCook12_lists.1, ivCook12_lists.2.1, ivCook12_lists.2.2.1, ivCook12_lists.2.2.2] at h
  exact h.symm

end MegaDreifach.Link2

namespace MegaDreifach.Link2.Kat

open MegaDreifach MegaDreifach.Link2

def hexNib (c : Char) : Nat :=
  if c.toNat ≤ 57 then c.toNat - 48 else c.toNat - 87

/-- Lower-case hex string (as chars) to bytes. -/
def hexBytes : List Char → List Nat
  | a :: b :: rest => (16 * hexNib a + hexNib b) :: hexBytes rest
  | _ => []

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ### KAT `empty` (1 block(s)) -/

def msg_empty : List Nat := []

theorem kat_empty_hex : (Vectors.vectors.get? 0).map (fun v => (v.name, hexBytes v.digestHex.toList)) =
    some ("empty", [3, 126, 245, 39, 78, 235, 234, 110, 216, 71, 130, 21, 115, 213, 117, 249, 215, 160, 213, 147, 211, 23, 135, 216, 165, 11, 237, 245, 94]) := by decide

theorem kat_empty_alg : vhashAlg msg_empty = [3, 126, 245, 39, 78, 235, 234, 110, 216, 71, 130, 21, 115, 213, 117, 249, 215, 160, 213, 147, 211, 23, 135, 216, 165, 11, 237, 245, 94] := by decide!

theorem kat_empty : Megadreifach.v_Hash (embed msg_empty) = .ok (embed [3, 126, 245, 39, 78, 235, 234, 110, 216, 71, 130, 21, 115, 213, 117, 249, 215, 160, 213, 147, 211, 23, 135, 216, 165, 11, 237, 245, 94]) := by
  rw [v_Hash_refines msg_empty ⟨by unfold Byte; decide, by unfold FitsBitlen i64MaxNat; decide⟩,
    kat_empty_alg]

/-! ### KAT `short_abc` (1 block(s)) -/

def msg_short_abc : List Nat := [97, 98, 99]

theorem kat_short_abc_hex : (Vectors.vectors.get? 1).map (fun v => (v.name, hexBytes v.digestHex.toList)) =
    some ("short_abc", [2, 89, 89, 192, 171, 44, 218, 215, 83, 105, 86, 227, 73, 12, 236, 107, 39, 17, 181, 215, 60, 87, 49, 175, 45, 78, 207, 245, 80]) := by decide

theorem kat_short_abc_alg : vhashAlg msg_short_abc = [2, 89, 89, 192, 171, 44, 218, 215, 83, 105, 86, 227, 73, 12, 236, 107, 39, 17, 181, 215, 60, 87, 49, 175, 45, 78, 207, 245, 80] := by decide!

theorem kat_short_abc : Megadreifach.v_Hash (embed msg_short_abc) = .ok (embed [2, 89, 89, 192, 171, 44, 218, 215, 83, 105, 86, 227, 73, 12, 236, 107, 39, 17, 181, 215, 60, 87, 49, 175, 45, 78, 207, 245, 80]) := by
  rw [v_Hash_refines msg_short_abc ⟨by unfold Byte; decide, by unfold FitsBitlen i64MaxNat; decide⟩,
    kat_short_abc_alg]

/-! ### KAT `short_one` (1 block(s)) -/

def msg_short_one : List Nat := [0]

theorem kat_short_one_hex : (Vectors.vectors.get? 2).map (fun v => (v.name, hexBytes v.digestHex.toList)) =
    some ("short_one", [2, 232, 120, 94, 71, 20, 158, 160, 208, 60, 195, 156, 79, 253, 92, 62, 226, 21, 104, 25, 115, 148, 164, 135, 68, 204, 60, 83, 245]) := by decide

theorem kat_short_one_alg : vhashAlg msg_short_one = [2, 232, 120, 94, 71, 20, 158, 160, 208, 60, 195, 156, 79, 253, 92, 62, 226, 21, 104, 25, 115, 148, 164, 135, 68, 204, 60, 83, 245] := by decide!

theorem kat_short_one : Megadreifach.v_Hash (embed msg_short_one) = .ok (embed [2, 232, 120, 94, 71, 20, 158, 160, 208, 60, 195, 156, 79, 253, 92, 62, 226, 21, 104, 25, 115, 148, 164, 135, 68, 204, 60, 83, 245]) := by
  rw [v_Hash_refines msg_short_one ⟨by unfold Byte; decide, by unfold FitsBitlen i64MaxNat; decide⟩,
    kat_short_one_alg]

/-! ### KAT `edge_27` (2 block(s)) -/

def msg_edge_27 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26]

theorem kat_edge_27_hex : (Vectors.vectors.get? 3).map (fun v => (v.name, hexBytes v.digestHex.toList)) =
    some ("edge_27", [1, 215, 1, 4, 58, 178, 29, 136, 165, 47, 254, 217, 75, 70, 137, 109, 193, 142, 21, 247, 117, 195, 214, 97, 254, 195, 249, 254, 216]) := by decide

theorem step_edge_27_0 :
    dmBlock (Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo) (blockAt (pad msg_edge_27) 0) =
      Em.posOfLists [1, 3, 4, 7, 14, 11, 13, 8, 5, 2, 10, 18, 16, 15, 6, 19, 9, 17, 0, 12] [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 2, 1, 1, 1, 2, 0, 1, 2, 1, 1] [28, 18, 17, 1, 23, 29, 10, 9, 24, 3, 20, 2, 12, 11, 22, 6, 21, 13, 27, 14, 16, 25, 15, 26, 5, 8, 0, 7, 19, 4] [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem step_edge_27_1 :
    dmBlock (Em.posOfLists [1, 3, 4, 7, 14, 11, 13, 8, 5, 2, 10, 18, 16, 15, 6, 19, 9, 17, 0, 12] [0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 2, 1, 1, 1, 2, 0, 1, 2, 1, 1] [28, 18, 17, 1, 23, 29, 10, 9, 24, 3, 20, 2, 12, 11, 22, 6, 21, 13, 27, 14, 16, 25, 15, 26, 5, 8, 0, 7, 19, 4] [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1]) (blockAt (pad msg_edge_27) 1) =
      Em.posOfLists [9, 17, 4, 5, 2, 7, 15, 3, 11, 19, 6, 12, 8, 1, 16, 10, 18, 14, 13, 0] [1, 0, 1, 0, 0, 1, 1, 0, 1, 2, 2, 0, 0, 2, 0, 2, 0, 1, 2, 2] [13, 29, 25, 16, 22, 8, 18, 24, 5, 4, 19, 27, 23, 6, 28, 3, 15, 12, 14, 21, 7, 26, 17, 2, 10, 9, 20, 1, 0, 11] [0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem kat_edge_27_alg : vhashAlg msg_edge_27 = [1, 215, 1, 4, 58, 178, 29, 136, 165, 47, 254, 217, 75, 70, 137, 109, 193, 142, 21, 247, 117, 195, 214, 97, 254, 195, 249, 254, 216] := by
  unfold vhashAlg
  rw [show (pad msg_edge_27).length / 28 = 2 from by decide]
  rw [chainPre_succ, chainPre_succ, chainPre_zero, ivCook12_eq_lists, step_edge_27_0, step_edge_27_1]
  decide!

theorem kat_edge_27 : Megadreifach.v_Hash (embed msg_edge_27) = .ok (embed [1, 215, 1, 4, 58, 178, 29, 136, 165, 47, 254, 217, 75, 70, 137, 109, 193, 142, 21, 247, 117, 195, 214, 97, 254, 195, 249, 254, 216]) := by
  rw [v_Hash_refines msg_edge_27 ⟨by unfold Byte; decide, by unfold FitsBitlen i64MaxNat; decide⟩,
    kat_edge_27_alg]

/-! ### KAT `edge_28` (2 block(s)) -/

def msg_edge_28 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

theorem kat_edge_28_hex : (Vectors.vectors.get? 4).map (fun v => (v.name, hexBytes v.digestHex.toList)) =
    some ("edge_28", [3, 84, 72, 142, 144, 32, 31, 49, 11, 135, 235, 76, 221, 163, 172, 31, 171, 205, 150, 113, 253, 8, 244, 131, 107, 50, 92, 248, 241]) := by decide

theorem step_edge_28_0 :
    dmBlock (Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo) (blockAt (pad msg_edge_28) 0) =
      Em.posOfLists [13, 6, 7, 8, 1, 14, 15, 12, 11, 17, 3, 5, 0, 19, 18, 9, 2, 16, 10, 4] [1, 1, 2, 0, 1, 2, 2, 2, 0, 0, 1, 2, 2, 0, 1, 1, 1, 1, 2, 2] [10, 19, 23, 16, 25, 3, 7, 15, 22, 5, 1, 17, 21, 9, 0, 8, 13, 24, 29, 28, 26, 27, 14, 18, 20, 12, 6, 11, 2, 4] [0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem step_edge_28_1 :
    dmBlock (Em.posOfLists [13, 6, 7, 8, 1, 14, 15, 12, 11, 17, 3, 5, 0, 19, 18, 9, 2, 16, 10, 4] [1, 1, 2, 0, 1, 2, 2, 2, 0, 0, 1, 2, 2, 0, 1, 1, 1, 1, 2, 2] [10, 19, 23, 16, 25, 3, 7, 15, 22, 5, 1, 17, 21, 9, 0, 8, 13, 24, 29, 28, 26, 27, 14, 18, 20, 12, 6, 11, 2, 4] [0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0]) (blockAt (pad msg_edge_28) 1) =
      Em.posOfLists [17, 15, 14, 7, 19, 6, 18, 8, 5, 16, 0, 4, 2, 11, 1, 12, 13, 10, 3, 9] [1, 0, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 0, 2, 2, 1, 1, 0, 1, 1] [1, 12, 19, 26, 7, 8, 29, 3, 18, 10, 2, 21, 23, 25, 9, 5, 11, 6, 22, 4, 20, 14, 15, 16, 28, 24, 27, 0, 17, 13] [1, 0, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem kat_edge_28_alg : vhashAlg msg_edge_28 = [3, 84, 72, 142, 144, 32, 31, 49, 11, 135, 235, 76, 221, 163, 172, 31, 171, 205, 150, 113, 253, 8, 244, 131, 107, 50, 92, 248, 241] := by
  unfold vhashAlg
  rw [show (pad msg_edge_28).length / 28 = 2 from by decide]
  rw [chainPre_succ, chainPre_succ, chainPre_zero, ivCook12_eq_lists, step_edge_28_0, step_edge_28_1]
  decide!

theorem kat_edge_28 : Megadreifach.v_Hash (embed msg_edge_28) = .ok (embed [3, 84, 72, 142, 144, 32, 31, 49, 11, 135, 235, 76, 221, 163, 172, 31, 171, 205, 150, 113, 253, 8, 244, 131, 107, 50, 92, 248, 241]) := by
  rw [v_Hash_refines msg_edge_28 ⟨by unfold Byte; decide, by unfold FitsBitlen i64MaxNat; decide⟩,
    kat_edge_28_alg]

/-! ### KAT `edge_29` (2 block(s)) -/

def msg_edge_29 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem kat_edge_29_hex : (Vectors.vectors.get? 5).map (fun v => (v.name, hexBytes v.digestHex.toList)) =
    some ("edge_29", [1, 185, 145, 166, 219, 98, 151, 135, 124, 124, 79, 114, 40, 60, 243, 246, 200, 231, 163, 249, 31, 10, 130, 193, 65, 86, 43, 152, 53]) := by decide

theorem step_edge_29_0 :
    dmBlock (Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo) (blockAt (pad msg_edge_29) 0) =
      Em.posOfLists [13, 6, 7, 8, 1, 14, 15, 12, 11, 17, 3, 5, 0, 19, 18, 9, 2, 16, 10, 4] [1, 1, 2, 0, 1, 2, 2, 2, 0, 0, 1, 2, 2, 0, 1, 1, 1, 1, 2, 2] [10, 19, 23, 16, 25, 3, 7, 15, 22, 5, 1, 17, 21, 9, 0, 8, 13, 24, 29, 28, 26, 27, 14, 18, 20, 12, 6, 11, 2, 4] [0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem step_edge_29_1 :
    dmBlock (Em.posOfLists [13, 6, 7, 8, 1, 14, 15, 12, 11, 17, 3, 5, 0, 19, 18, 9, 2, 16, 10, 4] [1, 1, 2, 0, 1, 2, 2, 2, 0, 0, 1, 2, 2, 0, 1, 1, 1, 1, 2, 2] [10, 19, 23, 16, 25, 3, 7, 15, 22, 5, 1, 17, 21, 9, 0, 8, 13, 24, 29, 28, 26, 27, 14, 18, 20, 12, 6, 11, 2, 4] [0, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0]) (blockAt (pad msg_edge_29) 1) =
      Em.posOfLists [9, 4, 11, 13, 12, 8, 3, 10, 2, 1, 19, 7, 16, 17, 15, 0, 18, 5, 14, 6] [2, 0, 2, 0, 1, 1, 0, 1, 2, 2, 2, 0, 2, 1, 1, 0, 0, 1, 2, 1] [15, 8, 19, 28, 16, 21, 4, 5, 18, 14, 29, 24, 9, 17, 7, 0, 6, 10, 26, 11, 1, 27, 12, 2, 22, 23, 3, 25, 13, 20] [1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem kat_edge_29_alg : vhashAlg msg_edge_29 = [1, 185, 145, 166, 219, 98, 151, 135, 124, 124, 79, 114, 40, 60, 243, 246, 200, 231, 163, 249, 31, 10, 130, 193, 65, 86, 43, 152, 53] := by
  unfold vhashAlg
  rw [show (pad msg_edge_29).length / 28 = 2 from by decide]
  rw [chainPre_succ, chainPre_succ, chainPre_zero, ivCook12_eq_lists, step_edge_29_0, step_edge_29_1]
  decide!

theorem kat_edge_29 : Megadreifach.v_Hash (embed msg_edge_29) = .ok (embed [1, 185, 145, 166, 219, 98, 151, 135, 124, 124, 79, 114, 40, 60, 243, 246, 200, 231, 163, 249, 31, 10, 130, 193, 65, 86, 43, 152, 53]) := by
  rw [v_Hash_refines msg_edge_29 ⟨by unfold Byte; decide, by unfold FitsBitlen i64MaxNat; decide⟩,
    kat_edge_29_alg]

/-! ### KAT `multi_56` (3 block(s)) -/

def msg_multi_56 : List Nat := [109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109, 109]

theorem kat_multi_56_hex : (Vectors.vectors.get? 6).map (fun v => (v.name, hexBytes v.digestHex.toList)) =
    some ("multi_56", [0, 165, 5, 147, 25, 173, 34, 83, 59, 194, 21, 111, 161, 64, 220, 23, 216, 150, 157, 250, 107, 175, 231, 81, 132, 142, 235, 231, 36]) := by decide

theorem step_multi_56_0 :
    dmBlock (Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo) (blockAt (pad msg_multi_56) 0) =
      Em.posOfLists [11, 9, 8, 7, 4, 12, 18, 15, 13, 10, 16, 2, 14, 1, 0, 6, 17, 3, 19, 5] [0, 2, 1, 0, 0, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 0, 0, 1, 1] [29, 6, 5, 2, 22, 24, 19, 17, 25, 10, 0, 14, 27, 21, 4, 3, 26, 11, 8, 16, 1, 12, 28, 23, 13, 20, 18, 7, 15, 9] [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem step_multi_56_1 :
    dmBlock (Em.posOfLists [11, 9, 8, 7, 4, 12, 18, 15, 13, 10, 16, 2, 14, 1, 0, 6, 17, 3, 19, 5] [0, 2, 1, 0, 0, 2, 2, 1, 2, 2, 2, 1, 2, 1, 2, 2, 0, 0, 1, 1] [29, 6, 5, 2, 22, 24, 19, 17, 25, 10, 0, 14, 27, 21, 4, 3, 26, 11, 8, 16, 1, 12, 28, 23, 13, 20, 18, 7, 15, 9] [1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]) (blockAt (pad msg_multi_56) 1) =
      Em.posOfLists [3, 18, 11, 19, 7, 13, 15, 17, 14, 6, 5, 10, 2, 4, 12, 1, 16, 8, 9, 0] [0, 0, 0, 0, 1, 2, 1, 2, 2, 1, 0, 2, 1, 2, 1, 1, 1, 0, 1, 0] [20, 16, 29, 17, 28, 7, 11, 1, 25, 22, 5, 27, 21, 8, 3, 4, 6, 0, 14, 10, 19, 24, 13, 26, 2, 23, 9, 12, 18, 15] [1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem step_multi_56_2 :
    dmBlock (Em.posOfLists [3, 18, 11, 19, 7, 13, 15, 17, 14, 6, 5, 10, 2, 4, 12, 1, 16, 8, 9, 0] [0, 0, 0, 0, 1, 2, 1, 2, 2, 1, 0, 2, 1, 2, 1, 1, 1, 0, 1, 0] [20, 16, 29, 17, 28, 7, 11, 1, 25, 22, 5, 27, 21, 8, 3, 4, 6, 0, 14, 10, 19, 24, 13, 26, 2, 23, 9, 12, 18, 15] [1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1]) (blockAt (pad msg_multi_56) 2) =
      Em.posOfLists [3, 9, 12, 16, 13, 17, 7, 2, 11, 8, 14, 0, 15, 4, 10, 18, 19, 6, 5, 1] [1, 2, 0, 2, 1, 2, 0, 0, 2, 0, 1, 0, 2, 0, 2, 1, 1, 2, 2, 0] [26, 20, 4, 16, 13, 2, 15, 29, 18, 17, 22, 27, 5, 8, 24, 1, 25, 19, 0, 7, 28, 11, 3, 6, 23, 21, 12, 14, 9, 10] [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem kat_multi_56_alg : vhashAlg msg_multi_56 = [0, 165, 5, 147, 25, 173, 34, 83, 59, 194, 21, 111, 161, 64, 220, 23, 216, 150, 157, 250, 107, 175, 231, 81, 132, 142, 235, 231, 36] := by
  unfold vhashAlg
  rw [show (pad msg_multi_56).length / 28 = 3 from by decide]
  rw [chainPre_succ, chainPre_succ, chainPre_succ, chainPre_zero, ivCook12_eq_lists, step_multi_56_0, step_multi_56_1, step_multi_56_2]
  decide!

theorem kat_multi_56 : Megadreifach.v_Hash (embed msg_multi_56) = .ok (embed [0, 165, 5, 147, 25, 173, 34, 83, 59, 194, 21, 111, 161, 64, 220, 23, 216, 150, 157, 250, 107, 175, 231, 81, 132, 142, 235, 231, 36]) := by
  rw [v_Hash_refines msg_multi_56 ⟨by unfold Byte; decide, by unfold FitsBitlen i64MaxNat; decide⟩,
    kat_multi_56_alg]

/-! ### KAT `multi_100` (4 block(s)) -/

def msg_multi_100 : List Nat := [0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255, 16, 33, 50, 67, 84, 101, 118, 135, 152, 169, 186, 203, 220, 237, 254, 15, 32, 49, 66, 83, 100, 117, 134, 151, 168, 185, 202, 219, 236, 253, 14, 31, 48, 65, 82, 99, 116, 133, 150, 167, 184, 201, 218, 235, 252, 13, 30, 47, 64, 81, 98, 115, 132, 149, 166, 183, 200, 217, 234, 251, 12, 29, 46, 63, 80, 97, 114, 131, 148, 165, 182, 199, 216, 233, 250, 11, 28, 45, 62, 79, 96, 113, 130, 147]

theorem kat_multi_100_hex : (Vectors.vectors.get? 7).map (fun v => (v.name, hexBytes v.digestHex.toList)) =
    some ("multi_100", [1, 86, 233, 243, 42, 86, 94, 88, 88, 147, 234, 181, 34, 158, 166, 161, 44, 149, 156, 116, 61, 156, 62, 66, 8, 39, 19, 158, 32]) := by decide

theorem step_multi_100_0 :
    dmBlock (Em.posOfLists ivCook12Cp ivCook12Co ivCook12Ep ivCook12Eo) (blockAt (pad msg_multi_100) 0) =
      Em.posOfLists [5, 2, 3, 16, 9, 6, 19, 7, 8, 11, 15, 14, 13, 1, 4, 17, 12, 18, 10, 0] [2, 2, 2, 2, 1, 2, 1, 0, 0, 1, 2, 2, 1, 0, 1, 2, 2, 1, 1, 2] [10, 19, 9, 0, 5, 16, 24, 21, 17, 23, 12, 7, 15, 27, 11, 20, 14, 8, 18, 25, 28, 2, 13, 3, 4, 29, 26, 1, 22, 6] [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem step_multi_100_1 :
    dmBlock (Em.posOfLists [5, 2, 3, 16, 9, 6, 19, 7, 8, 11, 15, 14, 13, 1, 4, 17, 12, 18, 10, 0] [2, 2, 2, 2, 1, 2, 1, 0, 0, 1, 2, 2, 1, 0, 1, 2, 2, 1, 1, 2] [10, 19, 9, 0, 5, 16, 24, 21, 17, 23, 12, 7, 15, 27, 11, 20, 14, 8, 18, 25, 28, 2, 13, 3, 4, 29, 26, 1, 22, 6] [1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0]) (blockAt (pad msg_multi_100) 1) =
      Em.posOfLists [11, 12, 6, 18, 13, 3, 1, 17, 8, 4, 7, 2, 9, 10, 0, 5, 19, 16, 14, 15] [1, 1, 1, 1, 1, 0, 2, 0, 2, 2, 0, 0, 2, 2, 2, 2, 0, 0, 1, 1] [7, 19, 26, 15, 16, 10, 18, 27, 23, 29, 20, 5, 0, 6, 12, 2, 3, 28, 22, 17, 11, 1, 4, 8, 25, 24, 13, 14, 9, 21] [1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem step_multi_100_2 :
    dmBlock (Em.posOfLists [11, 12, 6, 18, 13, 3, 1, 17, 8, 4, 7, 2, 9, 10, 0, 5, 19, 16, 14, 15] [1, 1, 1, 1, 1, 0, 2, 0, 2, 2, 0, 0, 2, 2, 2, 2, 0, 0, 1, 1] [7, 19, 26, 15, 16, 10, 18, 27, 23, 29, 20, 5, 0, 6, 12, 2, 3, 28, 22, 17, 11, 1, 4, 8, 25, 24, 13, 14, 9, 21] [1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1]) (blockAt (pad msg_multi_100) 2) =
      Em.posOfLists [1, 3, 14, 12, 0, 15, 10, 5, 9, 7, 4, 17, 13, 6, 18, 19, 8, 16, 11, 2] [0, 2, 2, 2, 2, 2, 1, 1, 2, 0, 1, 2, 2, 1, 2, 1, 0, 2, 2, 0] [24, 21, 5, 11, 12, 10, 6, 18, 28, 3, 1, 25, 8, 14, 16, 13, 22, 7, 9, 29, 4, 27, 17, 23, 0, 15, 20, 19, 26, 2] [0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem step_multi_100_3 :
    dmBlock (Em.posOfLists [1, 3, 14, 12, 0, 15, 10, 5, 9, 7, 4, 17, 13, 6, 18, 19, 8, 16, 11, 2] [0, 2, 2, 2, 2, 2, 1, 1, 2, 0, 1, 2, 2, 1, 2, 1, 0, 2, 2, 0] [24, 21, 5, 11, 12, 10, 6, 18, 28, 3, 1, 25, 8, 14, 16, 13, 22, 7, 9, 29, 4, 27, 17, 23, 0, 15, 20, 19, 26, 2] [0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0]) (blockAt (pad msg_multi_100) 3) =
      Em.posOfLists [7, 3, 6, 14, 18, 17, 13, 2, 4, 8, 16, 19, 10, 0, 5, 9, 15, 12, 11, 1] [1, 0, 1, 1, 1, 1, 0, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0] [16, 13, 29, 14, 17, 18, 7, 22, 9, 23, 19, 24, 25, 1, 26, 0, 3, 5, 12, 10, 2, 8, 11, 15, 28, 6, 27, 4, 21, 20] [0, 0, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0] :=
  eq_posOfLists_of_posL _ _ _ _ _ (by decide!)

theorem kat_multi_100_alg : vhashAlg msg_multi_100 = [1, 86, 233, 243, 42, 86, 94, 88, 88, 147, 234, 181, 34, 158, 166, 161, 44, 149, 156, 116, 61, 156, 62, 66, 8, 39, 19, 158, 32] := by
  unfold vhashAlg
  rw [show (pad msg_multi_100).length / 28 = 4 from by decide]
  rw [chainPre_succ, chainPre_succ, chainPre_succ, chainPre_succ, chainPre_zero, ivCook12_eq_lists, step_multi_100_0, step_multi_100_1, step_multi_100_2, step_multi_100_3]
  decide!

theorem kat_multi_100 : Megadreifach.v_Hash (embed msg_multi_100) = .ok (embed [1, 86, 233, 243, 42, 86, 94, 88, 88, 147, 234, 181, 34, 158, 166, 161, 44, 149, 156, 116, 61, 156, 62, 66, 8, 39, 19, 158, 32]) := by
  rw [v_Hash_refines msg_multi_100 ⟨by unfold Byte; decide, by unfold FitsBitlen i64MaxNat; decide⟩,
    kat_multi_100_alg]

end MegaDreifach.Link2.Kat
