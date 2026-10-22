/-
  Demo `FieldOk` from the climb table. Each band is a kernel `decide`
  of 9 rows. The zero home is not claimed.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FieldOk
import EcbsLink2.Link2.DemoFieldJoin

namespace EcbsLink2.Link2

open EcbsLink2.Spec

private theorem andEq {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

/-- A checked row is the Demo climb, so `specInv` returns its answer. -/
theorem spec_of_row (r : DemoRow) (h : rowOk r = true) :
    specInv 7 5 20 r.x = some r.ans := by
  unfold rowOk at h
  rcases andEq h with ⟨habc, hv⟩
  rcases andEq habc with ⟨hab, hc⟩
  rcases andEq hab with ⟨h1, h2⟩
  have h1e := eq_of_beq h1
  have h2e := eq_of_beq h2
  have hce := eq_of_beq hc
  cases hw : r.white with
  | true =>
    rw [hw] at hv
    rcases andEq hv with ⟨hm, ha⟩
    have hs := specInv_white_7 r.x r.g1 r.g2 r.gap h1e h2e hce (eq_of_beq hm)
    rw [eq_of_beq ha] at hs
    exact hs
  | false =>
    rw [hw] at hv
    rcases andEq hv with ⟨hm, ha⟩
    exact specInv_mirror_7 r.x r.g1 r.g2 r.gap r.ans h1e h2e hce
      (eq_of_beq hm) (eq_of_beq ha)

theorem row_of_checked (r : DemoRow)
    (hne : r.x ≠ [0, 0, 0, 0, 0, 0, 0]) (h : checked r = true) :
    rowOk r = true := by
  unfold checked at h
  by_cases hx : (r.x == [0, 0, 0, 0, 0, 0, 0]) = true
  · exact absurd (eq_of_beq hx) hne
  · simp [hx] at h
    exact h

theorem checked_at (rs : List DemoRow) (i : Nat) (hi : i < rs.length)
    (h : demoChecked rs = true) : checked rs[i] = true := by
  induction rs generalizing i with
  | nil =>
    simp at hi
  | cons r rs ih =>
    unfold demoChecked at h
    rw [List.all_cons] at h
    rcases andEq h with ⟨h0, ht⟩
    cases i with
    | zero =>
      simpa using h0
    | succ i =>
      exact ih i (Nat.lt_of_succ_lt_succ hi) ht

/-- Every nonzero Demo trit home inverts. The table is the kernel check. -/
theorem demo_fieldOk : FieldOk demo := by
  intro x ht hlen hne
  have hn : demo.n = 7 := by decide
  have hkT : demo.k = 5 := by decide
  have hb : demo.benchlen = 20 := by decide
  have hx : x.length = 7 := by simpa [hn] using hlen
  obtain ⟨a, b, c, d, e, f, g_, rfl⟩ := cons7 x hx
  have ha : a < 3 := by have hmem := ht a (by simp); omega
  have hb2 : b < 3 := by have hmem := ht b (by simp); omega
  have hc : c < 3 := by have hmem := ht c (by simp); omega
  have hd : d < 3 := by have hmem := ht d (by simp); omega
  have he : e < 3 := by have hmem := ht e (by simp); omega
  have hf : f < 3 := by have hmem := ht f (by simp); omega
  have hg : g_ < 3 := by have hmem := ht g_ (by simp); omega
  have hi : tri a b c d e f g_ < 2187 := tri_lt a b c d e f g_ ha hb2 hc hd he hf hg
  let i := tri a b c d e f g_
  let k := i / 9
  let j := i % 9
  have hk : k < 243 := by
    dsimp [k, i]
    omega
  have hj : j < 9 := Nat.mod_lt i (by decide)
  have hsplit : i = 9 * k + j := by
    unfold k j
    exact (Nat.div_add_mod i 9).symm
  have hlt : j < (demoBand k).length := by rw [demoBandLen k hk]; exact hj
  have hxeq := demoBandX k j hk hj
  have hdig := expected_tri a b c d e f g_ ha hb2 hc hd he hf hg
  have hchk := checked_at (demoBand k) j hlt (demoClimbBand k hk)
  have hne0 : ((demoBand k)[j]'hlt).x ≠ [0, 0, 0, 0, 0, 0, 0] := by
    rw [hxeq, ← hsplit]
    change expected i ≠ [0, 0, 0, 0, 0, 0, 0]
    rw [show i = tri a b c d e f g_ from rfl, hdig]
    simpa [hn, zeroHome, zeroPeg, List.replicate] using hne
  have hok := row_of_checked ((demoBand k)[j]) hne0 hchk
  have hspec := spec_of_row ((demoBand k)[j]) hok
  have hxrow : ((demoBand k)[j]'hlt).x = a :: b :: c :: d :: e :: f :: g_ :: [] := by
    rw [hxeq, ← hsplit]
    change expected i = a :: b :: c :: d :: e :: f :: g_ :: []
    rw [show i = tri a b c d e f g_ from rfl]
    exact hdig
  simpa [hxrow, hn, hkT, hb] using field_of_spec _ _ hspec

end EcbsLink2.Link2
