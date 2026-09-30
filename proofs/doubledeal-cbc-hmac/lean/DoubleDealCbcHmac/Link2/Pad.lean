import DoubleDealCbcHmac.Link2.Hmac

/-!
  LINK 2 for `pad_iso7816` (SPEC §3.1): the emitted function equals `pad` on byte lists.
-/

namespace DoubleDealCbcHmac.Link2
open MegaDreifach.Link2

theorem range'_map_const (s n c : Nat) : (List.range' s n).map (fun _ => c) = List.replicate n c := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [List.range'_succ, ih, List.replicate_succ]

theorem pad_length_mod (m : List Nat) : (pad m).length % msgBlock = 0 := by
  simp only [pad, List.length_append, List.length_replicate, List.length_singleton, msgBlock]
  omega

/-- SPEC §3.1 ISO/IEC 7816-4 padding, on byte lists whose length fits an i64. -/
theorem pad_iso7816_refines (msg : List Nat) (hb : Bytes msg) (hfit : FitsLen msg.length) :
    Doubledeal_cbc_hmac.pad_iso7816 (embed msg) = .ok (embed (pad msg)) := by
  unfold Doubledeal_cbc_hmac.pad_iso7816
  have h128 : (#[(128 : Int)] : Array Int) = embed [128] := rfl
  simp only [require_bytes_refines msg hb hfit, ok_bind, h128, concatL_embed, listLen_embed,
    hmacBlock_int, pure_eq_ok, fuelRange_eq, bind_ok_right]
  rw [modI_ofNat _ (by decide : hmacBlock ≠ 0), ok_bind,
    subI_ofNat hmacBlock _ fits28 (Nat.le_of_lt (Nat.mod_lt _ (by decide))), ok_bind,
    modI_ofNat _ (by decide : hmacBlock ≠ 0), ok_bind]
  generalize hnz : (hmacBlock - (msg ++ [128]).length % hmacBlock) % hmacBlock = nz
  have hpad : pad msg = msg ++ [128] ++ List.replicate nz 0 := by
    rw [← hnz, pad, msgBlock_eq_hmacBlock]
  have hmod : ((msg ++ [128]).length + nz) % hmacBlock = 0 := by
    rw [← hnz]; simp only [List.length_append, List.length_singleton, hmacBlock]; omega
  have hnzlt : nz < hmacBlock := by rw [← hnz]; exact Nat.mod_lt _ (by decide)
  have hfin : ∀ l : List Nat, (l.length + 0) % hmacBlock = 0 →
      (SudoRt.modI (Int.ofNat l.length) (Int.ofNat hmacBlock) >>= fun t =>
        SudoRt.sudoAssertEq t (0 : Int) 119 >>= fun _ => Except.ok (embed l)) = .ok (embed l) := by
    intro l hl
    rw [modI_ofNat _ (by decide : hmacBlock ≠ 0), ok_bind]
    simp only [SudoRt.sudoAssertEq, sEq_int, show (0 : Int) = Int.ofNat 0 from rfl,
      Int.ofNat.injEq, Nat.add_zero] at hl ⊢
    simp [hl]
  rw [hpad]
  rcases Nat.eq_zero_or_pos nz with rfl | hpos
  · rw [asc_break _ _ _ _ _ _ (by decide) (by rfl)]
    simp only [List.replicate_zero, List.append_nil]
    have := hfin (msg ++ [128]) hmod
    simp only [listLen_embed]
    exact this
  · rw [show ((1 : Int), embed (msg ++ [128])) = (Int.ofNat 1, embed (msg ++ [128])) from rfl]
    refine (push_loop 1 nz hpos (fun _ => 0) (msg ++ [128]) _ _ _ ?_).trans ?_
    · intro i l _ hi
      have hfi : FitsLen (i + 1) := FitsLen.of_le fits28 (by unfold hmacBlock at hnzlt ⊢; omega)
      rw [if_neg (ofNat_not_gt hi)]
      simp only [ok_bind, SudoRt.appendL, show (0 : Int) = Int.ofNat 0 from rfl, push_embed]
      rw [asc_tail nz i hfi]
    · rw [range'_map_const, show nz + 1 - 1 = nz by omega]
      simp only [listLen_embed]
      apply hfin
      have h := hmod
      simp only [List.length_append, List.length_singleton, List.length_replicate, hmacBlock] at h ⊢
      omega
