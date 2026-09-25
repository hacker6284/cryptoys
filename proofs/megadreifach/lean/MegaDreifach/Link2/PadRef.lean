/-
  LINK 2. `pad_z` / `pad_message` refine algebraic `pad` on `PadWf`:
  every byte is `≤ 255`, and `8 * length` fits in an i64.
  Not collision resistance. Not `v_Hash`.
-/
import Megadreifach
import MegaDreifach.Pad
import MegaDreifach.Link2.Be
import MegaDreifach.Link2.Big
import MegaDreifach.Link2.Loop

namespace MegaDreifach.Link2

private theorem replicate_succ_append (n a : Nat) :
    List.replicate (n + 1) a = List.replicate n a ++ [a] := by
  induction n with
  | zero => simp [List.replicate_succ]
  | succ n ih =>
    rw [List.replicate_succ]
    conv =>
      lhs
      rw [ih]
    rw [List.replicate_succ, List.cons_append]

private theorem push_zero_acc (pref : List Nat) (i : Nat) (hi : 1 ≤ i) :
    (embed (pref ++ List.replicate (i - 1) 0)).push (0 : Int) =
      embed (pref ++ List.replicate i 0) := by
  have hsub : (i - 1) + 1 = i := Nat.sub_add_cancel hi
  rw [show (0 : Int) = Int.ofNat 0 from rfl, push_embed, List.append_assoc,
    ← replicate_succ_append, hsub]

/-- Byte scan ignores its break index: on `PadWf` every cell passes the assert. -/
theorem pad_check_then {α} (msg : List Nat) (hp : PadWf msg)
    (k : Except SudoRt.Trap α)
    (onRet : Array Int → Except SudoRt.Trap α) :
    (do
      let toV ← SudoRt.subI (SudoRt.listLen (embed msg)) (1 : Int)
      let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
      let out ← SudoRt.runLoopOn (ρ := Array Int) (0 : Int) fuel
        (byteCheckStep (embed msg) toV) (fun _ => k) onRet
      pure out) = k := by
  by_cases h0 : msg.length = 0
  · have hempty : msg = [] := List.length_eq_zero.mp h0
    subst hempty
    rw [listLen_embed, show (([] : List Nat).length) = 0 from rfl,
      show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind,
      fuelRange_eq (0 : Int) (-1), except_bind_pure]
    have hgt : (0 : Int) > -1 := by decide
    rw [idx_break (0 : Int) (-1) (byteCheckStep (embed []) (-1)) (fun _ => k) onRet hgt
      (byteCheckStep_gt (embed []) (-1) 0 hgt)]
  · have hpos : 0 < msg.length := Nat.pos_of_ne_zero h0
    have hfits : FitsLen msg.length := FitsBitlen.fitsLen hp.bitlen
    rw [listLen_embed, subI_ofNat_one _ hpos hfits, ok_bind,
      fuelRange_eq (0 : Int) (Int.ofNat (msg.length - 1)), except_bind_pure]
    apply chain_idx (byteCheckStep (embed msg) (Int.ofNat (msg.length - 1)))
      (fun _ => k) onRet 0 (msg.length - 1) (Nat.zero_le _)
      (by
        intro i _ hiN
        have hlt : i < msg.length := by omega
        exact byteCheckStep_hit msg (msg.length - 1) i hiN hlt
          (hp.bytes _ (List.getElem_mem hlt)) hfits)
      k rfl

/-- Copy `xs` onto an empty buffer. Empty messages break before the body. -/
theorem copy_msg {α} (xs : List Nat)
    (after : Array Int → Except SudoRt.Trap α)
    (onRet : Array Int → Except SudoRt.Trap α)
    (hfits : FitsLen xs.length)
    (goal : Except SudoRt.Trap α)
    (hafter : after (embed xs) = goal) :
    (do
      let toV ← SudoRt.subI (SudoRt.listLen (embed xs)) (1 : Int)
      let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
      let out ← SudoRt.runLoopOn (ρ := Array Int) ((0 : Int), (#[] : Array Int)) fuel
        (copyStep (Array Int) (embed xs) toV) (fun σ => after σ.2) onRet
      pure out) = goal := by
  by_cases h0 : xs.length = 0
  · have hempty : xs = [] := List.length_eq_zero.mp h0
    subst hempty
    rw [listLen_embed, show (([] : List Nat).length) = 0 from rfl,
      show Int.ofNat 0 = (0 : Int) from rfl, subI_zero_one, ok_bind,
      fuelRange_eq (0 : Int) (-1), except_bind_pure]
    have hgt : (0 : Int) > -1 := by decide
    rw [copy_loop_gt_after (embed []) (0 : Int) (-1) #[] after onRet hgt, ← embed_nil]
    exact hafter
  · have hpos : 0 < xs.length := Nat.pos_of_ne_zero h0
    rw [listLen_embed, subI_ofNat_one _ hpos hfits, ok_bind,
      fuelRange_eq (0 : Int) (Int.ofNat (xs.length - 1)), except_bind_pure]
    have hrun := copy_loop_after (embed xs) 0 (xs.length - 1) (#[] : Array Int)
      after onRet (by omega) (Or.inl (by rw [size_embed]; omega))
      (by rw [size_embed]; exact hfits) (by rw [size_embed]; exact Nat.zero_le _)
    rw [show (0 : Int) = Int.ofNat 0 from rfl, hrun]
    have harr :
        Array.mk ((#[] : Array Int).toList ++
          List.take (xs.length - 1 + 1 - 0) ((embed xs).toList.drop 0)) = embed xs := by
      rw [show (#[] : Array Int).toList = [] from rfl, List.nil_append, toList_embed,
        List.drop_zero, take_map_ofNat]
      have : xs.length - 1 + 1 - 0 = xs.length := by omega
      rw [this, List.take_length]
      rfl
    rw [harr]
    exact hafter

def zeroAcc (pref : List Nat) (i : Nat) : Array Int :=
  embed (pref ++ List.replicate (i - 1) 0)

/-- `for i = 1 to z: out.append(0)`, including the `z = 0` break. -/
theorem push_zeros {α} (pref : List Nat) (z : Nat) (hz : z ≤ 27)
    (after : Array Int → Except SudoRt.Trap α)
    (onRet : Array Int → Except SudoRt.Trap α)
    (goal : Except SudoRt.Trap α)
    (hafter : after (embed (pref ++ List.replicate z 0)) = goal) :
    SudoRt.runLoopOn (ρ := Array Int) ((1 : Int), embed pref)
        (fuelRange (1 : Int) (Int.ofNat z))
        (pushStep (Array Int) (0 : Int) (Int.ofNat z))
        (fun σ => after σ.2) onRet = goal := by
  by_cases hz0 : z = 0
  · subst hz0
    rw [show Int.ofNat 0 = (0 : Int) from rfl]
    have hgt : (1 : Int) > (0 : Int) := by decide
    have hs := pushStep_gt (Array Int) (0 : Int) (0 : Int) (1 : Int) (embed pref) hgt
    rw [asc_break (1 : Int) (0 : Int) (embed pref)
        (pushStep (Array Int) (0 : Int) (0 : Int))
        (fun σ => after σ.2) onRet hgt hs]
    have : embed pref = embed (pref ++ List.replicate 0 0) := by
      simp [List.replicate, List.append_nil]
    rw [this]
    exact hafter
  · have hpos : 1 ≤ z := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz0)
    rw [show (1 : Int) = Int.ofNat 1 from rfl]
    have hstart : zeroAcc pref 1 = embed pref := by
      simp [zeroAcc, List.replicate, List.append_nil]
    rw [← hstart]
    apply chain_loop (pushStep (Array Int) (0 : Int) (Int.ofNat z))
      (fun σ => after σ.2) onRet (zeroAcc pref) 1 z hpos
      (by
        intro i hi1 hiZ
        unfold zeroAcc
        have hfits : FitsLen (i + 1) := by
          have : i + 1 ≤ 28 := by omega
          exact FitsLen.of_le (by unfold FitsLen i64MaxNat; decide) this
        rw [pushStep_hit (Array Int) (0 : Int) z i
            (embed (pref ++ List.replicate (i - 1) 0)) hiZ hfits,
          push_zero_acc pref i hi1]
        rfl)
      goal
      (by
        have : zeroAcc pref (z + 1) = embed (pref ++ List.replicate z 0) := by
          simp [zeroAcc, Nat.add_sub_cancel]
        rw [this]
        exact hafter)

/-- Copy eight big-endian bytes onto `pref`. -/
theorem copy_be {α} (pref : List Nat) (v : Nat)
    (after : Array Int → Except SudoRt.Trap α)
    (onRet : Array Int → Except SudoRt.Trap α)
    (goal : Except SudoRt.Trap α)
    (hafter : after (embed (pref ++ toBE 8 v)) = goal) :
    SudoRt.runLoopOn (ρ := Array Int) ((0 : Int), embed pref)
        (fuelRange (0 : Int) (7 : Int))
        (copyStep (Array Int) (embed (toBE 8 v)) (7 : Int))
        (fun σ => after σ.2) onRet = goal := by
  have hsz : FitsLen (embed (toBE 8 v)).size := by
    rw [size_embed, toBE_length]
    exact fits_le9 (by decide)
  have hto : 7 < (embed (toBE 8 v)).size := by
    rw [size_embed, toBE_length]
    decide
  have hrun := copy_loop_after (embed (toBE 8 v)) 0 7 (embed pref) after onRet
    (by decide) (Or.inl hto) hsz (by rw [size_embed]; exact Nat.zero_le _)
  rw [show (0 : Int) = Int.ofNat 0 from rfl, show (7 : Int) = Int.ofNat 7 from rfl, hrun]
  have harr :
      Array.mk ((embed pref).toList ++
        List.take (7 + 1 - 0) ((embed (toBE 8 v)).toList.drop 0)) =
        embed (pref ++ toBE 8 v) := by
    rw [toList_embed, toList_embed, List.drop_zero]
    rw [show 7 + 1 - 0 = 8 by decide, take_map_ofNat]
    have hlen := toBE_length 8 v
    have htake : List.take (toBE 8 v).length (toBE 8 v) = toBE 8 v := List.take_length _
    rw [hlen] at htake
    rw [htake]
    apply Array.ext'
    simp [embed, List.map_append]
  rw [harr]
  exact hafter

/-- Append `0x80`, the zero fill, and the 8-byte bit length. -/
def padLenPart (bitlen : Int) (arr : Array Int) : Except SudoRt.Trap (Array Int) :=
  do
    let n ← Megadreifach.big_from_int bitlen
    let lenb ← Megadreifach.big_to_be n (8 : Int)
    let fuel : Nat :=
      if (0 : Int) > (7 : Int) then 1 else ((7 : Int) - (0 : Int)).natAbs + 1
    let done ← SudoRt.runLoopOn (ρ := Array Int) ((0 : Int), arr) fuel
      (copyStep (Array Int) lenb (7 : Int))
      (fun σ => (pure σ.2 : Except SudoRt.Trap (Array Int)))
      (fun r => pure r)
    pure done

def padFromOut (bitlen z : Int) (out0 : Array Int) : Except SudoRt.Trap (Array Int) :=
  do
    let out := (SudoRt.appendL out0 (128 : Int)).1
    let fuel : Nat := if (1 : Int) > z then 1 else (z - (1 : Int)).natAbs + 1
    let zeroed ← SudoRt.runLoopOn (ρ := Array Int) ((1 : Int), out) fuel
      (pushStep (Array Int) (0 : Int) z)
      (fun σ => padLenPart bitlen σ.2)
      (fun r => pure r)
    pure zeroed

def padAfter (msg : List Nat) : Except SudoRt.Trap (Array Int) :=
  do
    let bitlen ← SudoRt.mulI (8 : Int) (SudoRt.listLen (embed msg))
    let z ← Megadreifach.pad_z (SudoRt.listLen (embed msg))
    let toV ← SudoRt.subI (SudoRt.listLen (embed msg)) (1 : Int)
    let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
    let copied ← SudoRt.runLoopOn (ρ := Array Int) ((0 : Int), (#[] : Array Int)) fuel
      (copyStep (Array Int) (embed msg) toV)
      (fun σ => padFromOut bitlen z σ.2)
      (fun r => pure r)
    pure copied

def padRun (msg : List Nat) : Except SudoRt.Trap (Array Int) :=
  do
    let toV ← SudoRt.subI (SudoRt.listLen (embed msg)) (1 : Int)
    let fuel : Nat := if (0 : Int) > toV then 1 else (toV - (0 : Int)).natAbs + 1
    let out ← SudoRt.runLoopOn (ρ := Array Int) (0 : Int) fuel
      (byteCheckStep (embed msg) toV) (fun _ => padAfter msg) (fun r => pure r)
    pure out

theorem padLenPart_eq (msg : List Nat) (hp : PadWf msg) :
    padLenPart (Int.ofNat (8 * msg.length))
        (embed ((msg ++ [0x80]) ++ List.replicate (padZ msg.length) 0)) =
      .ok (embed (pad msg)) := by
  unfold padLenPart
  rw [big_from_int_refines (8 * msg.length) hp.bitlen, ok_bind,
    big_to_be_8 (8 * msg.length) hp.bitlen, ok_bind, fuelRange_eq (0 : Int) (7 : Int),
    except_bind_pure]
  apply copy_be ((msg ++ [0x80]) ++ List.replicate (padZ msg.length) 0) (8 * msg.length)
    (fun a => (pure a : Except SudoRt.Trap (Array Int))) (fun r => pure r)
    (.ok (embed (pad msg)))
    (by
      rw [show ((msg ++ [0x80]) ++ List.replicate (padZ msg.length) 0) ++
            toBE 8 (8 * msg.length) = pad msg from rfl]
      rfl)

theorem padFromOut_eq (msg : List Nat) (hp : PadWf msg) :
    padFromOut (Int.ofNat (8 * msg.length)) (Int.ofNat (padZ msg.length)) (embed msg) =
      .ok (embed (pad msg)) := by
  unfold padFromOut
  rw [appendL_spec, show (128 : Int) = Int.ofNat 128 from rfl, push_embed,
    show (128 : Nat) = 0x80 from ox80_eq.symm]
  have hz : padZ msg.length ≤ 27 := by
    have h := padZ_lt_block msg.length
    simp [padBlock] at h
    omega
  rw [fuelRange_eq (1 : Int) (Int.ofNat (padZ msg.length)), except_bind_pure]
  apply push_zeros (msg ++ [0x80]) (padZ msg.length) hz
    (padLenPart (Int.ofNat (8 * msg.length))) (fun r => pure r)
    (.ok (embed (pad msg))) (padLenPart_eq msg hp)

theorem pad_z_refines (n : Nat) (h : FitsBitlen n) :
    Megadreifach.pad_z (Int.ofNat n) = .ok (Int.ofNat (padZ n)) := by
  unfold Megadreifach.pad_z padZ
  rw [show Megadreifach.len_field = (8 : Int) from rfl,
    show Megadreifach.pad_block = (28 : Int) from rfl]
  have h1 : FitsLen (n + 1) :=
    FitsLen.of_le (FitsBitlen.fitsRoom h) (Nat.le_add_right (n + 1) 8)
  rw [addI_ofNat_one n h1, ok_bind]
  have h9 : FitsLen ((n + 1) + 8) := by
    simpa [Nat.add_assoc] using (FitsBitlen.fitsRoom h)
  rw [show (8 : Int) = Int.ofNat 8 from rfl, addI_ofNat (n + 1) 8 h9, ok_bind]
  rw [show (28 : Int) = Int.ofNat 28 from rfl,
    modI_ofNat ((n + 1) + 8) (by decide), ok_bind]
  have hr : ((n + 1) + 8) % 28 ≤ 28 := Nat.le_of_lt (Nat.mod_lt _ (by decide))
  have h28 : FitsLen 28 := by unfold FitsLen i64MaxNat; decide
  rw [subI_ofNat 28 (((n + 1) + 8) % 28) h28 hr, ok_bind]
  rw [modI_ofNat (28 - ((n + 1) + 8) % 28) (by decide)]
  simp [lenField, padBlock, Nat.add_assoc]

theorem padAfter_eq (msg : List Nat) (hp : PadWf msg) :
    padAfter msg = .ok (embed (pad msg)) := by
  unfold padAfter
  rw [show (8 : Int) = Int.ofNat 8 from rfl]
  rw [show SudoRt.mulI (Int.ofNat 8) (SudoRt.listLen (embed msg)) =
      SudoRt.mulI (Int.ofNat 8) (Int.ofNat msg.length) by rw [listLen_embed]]
  rw [mulI_ofNat 8 msg.length hp.bitlen, ok_bind]
  rw [show Megadreifach.pad_z (SudoRt.listLen (embed msg)) =
      Megadreifach.pad_z (Int.ofNat msg.length) by rw [listLen_embed]]
  rw [pad_z_refines msg.length hp.bitlen, ok_bind]
  exact copy_msg msg
    (padFromOut (Int.ofNat (8 * msg.length)) (Int.ofNat (padZ msg.length)))
    (fun r => pure r) (FitsBitlen.fitsLen hp.bitlen)
    (.ok (embed (pad msg))) (padFromOut_eq msg hp)

theorem padRun_eq (msg : List Nat) (hp : PadWf msg) :
    padRun msg = .ok (embed (pad msg)) := by
  unfold padRun
  rw [pad_check_then msg hp (padAfter msg) (fun r => pure r)]
  exact padAfter_eq msg hp

/-- `pad_message (embed msg) = ok (embed (pad msg))` when every byte is `≤ 255`
    and `8 * length` fits in an i64. Algebraic Link 2 only: not `v_Hash`,
    not collision resistance. -/
theorem pad_message_refines (msg : List Nat) (hp : PadWf msg) :
    Megadreifach.pad_message (embed msg) = .ok (embed (pad msg)) := by
  have h := padRun_eq msg hp
  unfold padRun padAfter padFromOut padLenPart at h
  dsimp at h
  unfold byteCheckStep copyStep pushStep at h
  unfold Megadreifach.pad_message
  dsimp
  -- Splitters are per definition; unfolding makes the branches compare.
  unfold byteCheckStep.match_1 copyStep.match_1 at h
  unfold Megadreifach.pad_message.match_1 Megadreifach.rot_slice.match_2
  exact h

theorem pad_message_refines_array (a : Array Int) (h : WellFormedPad a) :
    Megadreifach.pad_message a = .ok (embed (pad (decode a))) := by
  have hr := pad_message_refines (decode a) (padWf_decode a h)
  simpa [embed_decode a h.nonneg] using hr

end MegaDreifach.Link2
