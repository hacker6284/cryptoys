/-
  HEAVY (not in the default build target): kernel `decide!` discharge of the two
  finite checks `Check3 KC LKC` and `Check3 KS LKS` behind the three-step
  GridCycle survival bound for `v10Sym 0 3` (DoubleDealSecurity/GridCycleSurvival.lean).
  Each check is 52 · 52 evaluations of the first three seats of the GridCycle walk
  (`seats3`), split into four chunks of 13 values of `c1` so that each `decide!`
  fits in memory (about 30 s and a few GB each, measured on the dev box).
  Built and audited by the `doubledeal-security-heavy` CI job
  (`lake build DoubleDealSecurityHeavy`, `check_axioms.py security-heavy`).
  The lists `LKC` / `LKS` come from `analysis/v12-diffusion/prefix_survival.py`; the
  kernel checks them, so a wrong list fails the build.
-/
import DoubleDealSecurity.GridCycleSurvival

namespace DoubleDeal.Security.GCSurvival

open DoubleDeal Finset

/-- One chunk of the finite check: `c1 ∈ [13k, 13k + 13)`, every `c2`. -/
def chunkOK (c0 : Fin 52) (L : List (Nat × Nat)) (k : Nat) : Bool :=
  (List.range' (13 * k) 13).all fun c1 => (List.finRange 52).all fun c2 => check3 c0 L (finOf c1) c2

theorem of_chunks {c0 : Fin 52} {L : List (Nat × Nat)}
    (h0 : chunkOK c0 L 0 = true) (h1 : chunkOK c0 L 1 = true)
    (h2 : chunkOK c0 L 2 = true) (h3 : chunkOK c0 L 3 = true) : Check3 c0 L := by
  intro c1 c2
  have hk : c1.val / 13 < 4 := by omega
  have hc : chunkOK c0 L (c1.val / 13) = true := by
    have : c1.val / 13 = 0 ∨ c1.val / 13 = 1 ∨ c1.val / 13 = 2 ∨ c1.val / 13 = 3 := by omega
    rcases this with e | e | e | e <;> rw [e] <;> assumption
  simp only [chunkOK, List.all_eq_true] at hc
  have hmem : c1.val ∈ List.range' (13 * (c1.val / 13)) 13 := by
    rw [List.mem_range'_1]; omega
  have := hc _ hmem c2 (List.mem_finRange c2)
  rwa [finOf_val] at this

/-- (PROVED, kernel `decide!`) Chunk 0 of `Check3 KC LKC`. -/
theorem chunk_KC_0 : chunkOK KC LKC 0 = true := by decide!
/-- (PROVED, kernel `decide!`) Chunk 1 of `Check3 KC LKC`. -/
theorem chunk_KC_1 : chunkOK KC LKC 1 = true := by decide!
/-- (PROVED, kernel `decide!`) Chunk 2 of `Check3 KC LKC`. -/
theorem chunk_KC_2 : chunkOK KC LKC 2 = true := by decide!
/-- (PROVED, kernel `decide!`) Chunk 3 of `Check3 KC LKC`. -/
theorem chunk_KC_3 : chunkOK KC LKC 3 = true := by decide!
/-- (PROVED, kernel `decide!`) Chunk 0 of `Check3 KS LKS`. -/
theorem chunk_KS_0 : chunkOK KS LKS 0 = true := by decide!
/-- (PROVED, kernel `decide!`) Chunk 1 of `Check3 KS LKS`. -/
theorem chunk_KS_1 : chunkOK KS LKS 1 = true := by decide!
/-- (PROVED, kernel `decide!`) Chunk 2 of `Check3 KS LKS`. -/
theorem chunk_KS_2 : chunkOK KS LKS 2 = true := by decide!
/-- (PROVED, kernel `decide!`) Chunk 3 of `Check3 KS LKS`. -/
theorem chunk_KS_3 : chunkOK KS LKS 3 = true := by decide!

/-- (PROVED) The K♣ check. -/
theorem check3_KC : Check3 KC LKC := of_chunks chunk_KC_0 chunk_KC_1 chunk_KC_2 chunk_KC_3

/-- (PROVED) The K♠ check. -/
theorem check3_KS : Check3 KS LKS := of_chunks chunk_KS_0 chunk_KS_1 chunk_KS_2 chunk_KS_3

/-- (PROVED, unconditional) `v10Sym 0 3` survives GridCycle (seat walk unchanged)
    on at most `52!/4420` of the `52!` decks. A counting statement about GridCycle
    alone, for one fixed relabelling; not a statement about the cipher. -/
theorem gc_survival_v10Sym03_le :
    4420 * (gcSurvivors (v10Sym 0 3)).card ≤ Nat.factorial 52 :=
  gc_survival_v10Sym03_le_of_check check3_KC check3_KS

/-- (PROVED, unconditional) Every nontrivial SumRanks symmetry `v10Sym a x`
    survives GridCycle on at most `52!/4420` decks. -/
theorem gc_survival_v10Sym_le (a : Fin 13) (x : Fin 4) (hne : ¬ (a = 0 ∧ x = 0)) :
    4420 * (gcSurvivors (v10Sym a x)).card ≤ Nat.factorial 52 :=
  gc_survival_v10Sym_le_of_check check3_KC check3_KS a x hne

end DoubleDeal.Security.GCSurvival
