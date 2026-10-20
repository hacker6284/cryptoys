/-
  The base-point search, one hole at a time. A `SearchAt` hole is
  `searchRoot`: a hit returns that basis peg and its root up, a miss
  moves one hole on. Every miss through the fuel is `none`, and the
  card then fails the `found > 0` assert. The peg the card plants is
  `basisPeg`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchAt
import EcbsLink2.Link2.PowLoop
import EcbsLink2.Link2.Lists
import EcbsLink2.Link2.School

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- `filledL` then `putL` is a white peg in hole `j`. -/
theorem basis_fill (n j : Nat) (hj : j < n) :
    (do
        let x ← SudoRt.filledL (Int.ofNat n) (0 : Int)
        SudoRt.putL x (Int.ofNat j) (1 : Int)) =
      .ok (embed (basisPeg n j)) := by
  rw [filledL_ofNat, ok_bind, ← embed_replicate_zero]
  have hlen : j < (List.replicate n 0).length := by
    rw [List.length_replicate]
    exact hj
  have hsz : j < (embed (List.replicate n 0)).size := by
    rw [size_embed]
    exact hlen
  rw [putL_ofNat _ j (1 : Int) hsz]
  rw [show (1 : Int) = Int.ofNat 1 from (ofNat_eq_natCast 1).symm]
  rw [embed_set _ j 1 hlen]
  unfold basisPeg
  rfl

theorem basisPeg_length (n j : Nat) : (basisPeg n j).length = n := by
  unfold basisPeg
  rw [List.length_set, List.length_replicate]

theorem basisPeg_trits (n j : Nat) : allTritList (basisPeg n j) := by
  intro a ha
  unfold basisPeg at ha
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  by_cases h : i = j
  · simp [List.getElem_set, h]
  · have hne : ¬ (j = i) := by intro he; exact h he.symm
    simp [List.getElem_set, hne, List.getElem_replicate]

/-- The first hitting hole inside the fuel is the root `searchRoot` returns.
    Earlier holes are misses. -/
theorem searchRoot_first (n k bench fuel j m : Nat)
    (hn : j + m < n) (hf : m < fuel)
    (hmiss : ∀ i, j ≤ i → i < j + m → rootHit n k bench (basisPeg n i) = false)
    (hhit : rootHit n k bench (basisPeg n (j + m)) = true) :
    searchRoot n k bench fuel j =
      some (basisPeg n (j + m), rootY n k bench (basisPeg n (j + m))) := by
  induction m generalizing j fuel with
  | zero =>
    have hj : j < n := by omega
    have hfuel : fuel = (fuel - 1) + 1 := by omega
    have hh : rootHit n k bench (basisPeg n j) = true := by
      rw [Nat.add_zero] at hhit
      exact hhit
    rw [hfuel]
    exact searchRoot_hit n k bench (fuel - 1) j hj hh
  | succ m ih =>
    have hj : j < n := by omega
    have h0 : rootHit n k bench (basisPeg n j) = false :=
      hmiss j (Nat.le_refl _) (by omega)
    have hfuel : fuel = (fuel - 1) + 1 := by omega
    rw [hfuel, searchRoot_miss n k bench (fuel - 1) j hj h0]
    have hsum : (j + 1) + m = j + (m + 1) := by omega
    have hstep := ih (fuel - 1) (j + 1) (by omega) (by omega)
      (by
        intro i hi1 hi2
        exact hmiss i (by omega) (by omega))
      (by simpa [hsum] using hhit)
    simpa [hsum] using hstep

/-- No hit in the fuel. `searchRoot` refuses. -/
theorem searchRoot_misses (n k bench fuel j : Nat)
    (hmiss : ∀ i, j ≤ i → i < j + fuel → i < n →
      rootHit n k bench (basisPeg n i) = false) :
    searchRoot n k bench fuel j = none := by
  induction fuel generalizing j with
  | zero =>
    exact searchRoot_zero n k bench j
  | succ fuel ih =>
    by_cases hj : j < n
    · have h0 : rootHit n k bench (basisPeg n j) = false :=
        hmiss j (Nat.le_refl _) (by omega) hj
      rw [searchRoot_miss n k bench fuel j hj h0]
      exact ih (j + 1) (by
        intro i hi1 hi2 hi3
        exact hmiss i (by omega) (by omega) hi3)
    · exact searchRoot_past n k bench fuel j hj

/-- `basePoint` is the cofactor walk of whatever the search returned. -/
theorem basePoint_of_root (t : Spec.Tier) (root : List Nat × List Nat)
    (h : searchRoot t.n t.k t.benchlen t.n 1 = some root) :
    basePoint t = cofactorWalk t.n t.k t.benchlen root := by
  unfold basePoint
  rw [h]

/-- A search that misses every hole from 1 is `basePoint = none`. -/
theorem basePoint_none (t : Spec.Tier)
    (hmiss : ∀ i, 1 ≤ i → i < 1 + t.n → i < t.n →
      rootHit t.n t.k t.benchlen (basisPeg t.n i) = false) :
    basePoint t = none := by
  unfold basePoint
  rw [searchRoot_misses t.n t.k t.benchlen t.n 1 hmiss]

/-- The card's not-found check. `found` stayed 0, so line 963 fails. -/
theorem search_refuse {α : Type} (b : Ecbs.Board) (k : Ecbs.Board → Except SudoRt.Trap α) :
    (do
        let _ ← SudoRt.sudoAssert (decide (((0 : Int) > (0 : Int)))) 963
        k b) =
      .error { kind := "AssertFailed", detail := s!"line {963}" } := by
  have hdec : decide (((0 : Int) > (0 : Int))) = false := by decide
  rw [hdec]
  unfold SudoRt.sudoAssert SudoRt.fail
  have hne : ¬ ((false : Bool) = true) := by decide
  rw [if_neg hne, error_bind]

/-- One seated hole. The compare is `rootHit` of that basis peg, and
    `searchRoot` either returns the root or moves one hole on. -/
theorem search_hole (b : Ecbs.Board) (t : Spec.Tier) (j : Nat)
    (gapXs ax bx : List Nat) (left : Nat)
    (h : SearchAt b t (basisPeg t.n j)
      (rootY t.n t.k t.benchlen (basisPeg t.n j))
      (curveSide t.n t.k t.benchlen (basisPeg t.n j)) gapXs ax bx left)
    (hj : j < t.n) :
    (∃ b', searchCheck b = .ok (true, b') ∧
        HitAt b' t (basisPeg t.n j) ax bx ∧
        rootHit t.n t.k t.benchlen (basisPeg t.n j) = true ∧
        searchRoot t.n t.k t.benchlen left j =
          some (basisPeg t.n j, rootY t.n t.k t.benchlen (basisPeg t.n j))) ∨
    (∃ b' bM, searchCheck b = .ok (false, b') ∧
        searchMiss b' = .ok bM ∧ MissAt bM ∧
        rootHit t.n t.k t.benchlen (basisPeg t.n j) = false ∧
        searchRoot t.n t.k t.benchlen left j =
          searchRoot t.n t.k t.benchlen (left - 1) (j + 1)) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hleft, _, _, _, _⟩ := h.pack
  have hfuel : left = (left - 1) + 1 := by omega
  rcases search_step_at b t (basisPeg t.n j)
      (rootY t.n t.k t.benchlen (basisPeg t.n j))
      (curveSide t.n t.k t.benchlen (basisPeg t.n j)) gapXs ax bx left h with
    hhit | hmiss
  · left
    obtain ⟨b', hck, hAt, hh⟩ := hhit
    refine ⟨b', hck, hAt, hh, ?_⟩
    rw [hfuel]
    exact searchRoot_hit t.n t.k t.benchlen (left - 1) j hj hh
  · right
    obtain ⟨b', bM, hck, _, hm, hMiss, hf⟩ := hmiss
    refine ⟨b', bM, hck, hm, hMiss, hf, ?_⟩
    rw [hfuel]
    exact searchRoot_miss t.n t.k t.benchlen (left - 1) j hj hf

/-- The board `pow_root` leaves is the board the hit test reads, once the
    across and the base home are still seated and one more hole fits. -/
theorem search_of_pow (b : Ecbs.Board) (t : Spec.Tier) (x ax bx : List Nat) (left : Nat)
    (h : PowAt b t (curveSide t.n t.k t.benchlen x) (rootY t.n t.k t.benchlen x) [])
    (hx : x.length = t.n)
    (hax : b.sudo_5Board_4home[searchAcross]? = some (embed ax))
    (haxD : b.sudo_5Board_4held[searchAcross]? = some true)
    (haxL : ax.length = t.n)
    (hbx : b.sudo_5Board_4home[searchBase]? = some (embed bx))
    (hbxD : b.sudo_5Board_4held[searchBase]? = some true)
    (hbxL : bx.length = t.n)
    (hleft : 0 < left)
    (hM : ∀ moves, b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves →
      FitsLen (moves + searchMove t.n t.benchlen * left))
    (hS : ∀ slides, b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides →
      FitsLen (slides + searchSlide t.n * left))
    (hC : ∀ ctrl, b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl →
      FitsLen (ctrl + left))
    (hOp : ∀ c0, b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat c0) →
      FitsLen (c0 + left)) :
    SearchAt b t x (rootY t.n t.k t.benchlen x) (curveSide t.n t.k t.benchlen x)
      (fieldMul t.n t.k t.benchlen (curveSide t.n t.k t.benchlen x)
        (curveSide t.n t.k t.benchlen x)) ax bx left where
  tier := h.tier
  shape := h.shape
  sat := h.sat
  nPos := h.nPos
  markerOn := h.markerOn
  benchOff := h.benchOff
  xLen := hx
  yIs := rfl
  sideIs := rfl
  yLen := h.accLen
  sideLen := h.rhsLen
  yT := h.accT
  sideT := h.rhsT
  gapLen := by
    have hnb := mul_span_n t.n t.benchlen h.nPos h.sat.mul_span
    exact fieldMul_length t.n t.k t.benchlen
      (curveSide t.n t.k t.benchlen x) (curveSide t.n t.k t.benchlen x) hnb
  axLen := haxL
  bxLen := hbxL
  upHome := h.upHome
  upHeld := h.upHeld
  botHome := h.botHome
  botHeld := h.botHeld
  gapHome := h.gapHome
  gapHeld := h.gapHeld
  axHome := hax
  axHeld := haxD
  bxHome := hbx
  bxHeld := hbxD
  spareOff := h.spareOff
  homeWide := h.homeWide
  pack := by
    obtain ⟨moves, slides, ctrl, mark, _, pk, ps, hole, c0, _, hmv, hsl, hc, hm, _, _,
        hpk, hps, hhole, hsz, hop0, _, _, _, _, _, _⟩ := h.pack
    refine ⟨moves, slides, ctrl, mark, pk, ps, hole, c0, hmv, hsl, hc, hm, hpk, hps, hhole,
      ?_, hop0, hleft, hM moves hmv, hS slides hsl, hC ctrl hc, hOp c0 hop0⟩
    rw [hsz]
    decide

end EcbsLink2.Link2
