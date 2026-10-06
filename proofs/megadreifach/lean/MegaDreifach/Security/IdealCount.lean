/-
  SECURITY (ideal-cipher bookkeeping, not a security claim).  The
  combinatorial core of the Black–Rogaway–Shrimpton Davies–Meyer bounds, for
  the group-DM `h ↦ compose h y` on megaminx positions:

  * `compose_left_cancel`: for `InjPos h`, `y ↦ compose h y` is injective.
    The lemma and its `Fin` pigeonhole `injective_surjective_fin` live in
    `Link2/InjPos.lean` (one copy). This file calls `compose_left_cancel`.
    For `InjPos y`, `h ↦ compose h y` is injective: that is
    `Group.leftMul_cancel`, used directly.
  * `dm_forward_bad_count`: among any duplicate-free list `Y` of cipher answers
    to a forward query `(h, m)`, at most `|Z|` make the DM output land in a
    given set `Z` (earlier outputs, or a preimage target).
  * `dm_inverse_bad_count`: the same for inverse queries `(y, m)`.

  With the ideal-cipher answer uniform over ≥ |G| − i values at query i, these
  give the paper bounds Adv^coll ≤ q(q+1)/(|G| − q), Adv^pre ≤ q/(|G| − q)
  (≈ q²/|G| and q/|G| for q ≪ |G|; the same form is used in the report)
  (probability arithmetic on paper; see
  `proofs/megadreifach/security/REPORT.md`).  These bounds assume an ideal
  cipher, which MegaDreifach is not claimed to be (SPEC §9).  They do NOT apply
  to v1, whose block map has a proved 2-query distinguisher
  (`MegaDreifachV1.Security.emBlock_word`, `proofs/deprecated/megadreifach-v1/`),
  and nothing here says they apply to v2 (free-start pseudo-collisions of v2 are
  easy, SPEC §8).

  Grip-rule status: INDEPENDENT of the grip rule.  The cancellation and
  counting lemmas are group facts about `compose` and need no repair if E_m
  changes.  `reachable_rank_lt_group` goes through `MDReduction.injPos_chR`
  (see the note there).

  Zero sorry.  No native_decide.
-/
import MegaDreifach.Security.MDReduction
import MegaDreifach.Link2.InjPos

namespace MegaDreifach.Security

open MegaDreifach MegaDreifach.Link2

/-- Counting lemma: an injective map sends at most `|Z|` elements of a
    duplicate-free list into `Z`. -/
theorem count_inj_le {α β : Type} [DecidableEq β] (φ : α → β)
    (hφ : ∀ a b, φ a = φ b → a = b) :
    ∀ (Y : List α), Y.Nodup → ∀ (Z : List β),
      (Y.filter (fun y => decide (φ y ∈ Z))).length ≤ Z.length
  | [], _, Z => by simp
  | y :: Y, hY, Z => by
      have hY' := (List.nodup_cons.mp hY).2
      have hy := (List.nodup_cons.mp hY).1
      by_cases hm : φ y ∈ Z
      · rw [List.filter_cons_of_pos (by simpa using hm), List.length_cons]
        have hcongr : Y.filter (fun y' => decide (φ y' ∈ Z)) =
            Y.filter (fun y' => decide (φ y' ∈ Z.erase (φ y))) := by
          apply List.filter_congr
          intro y' hy'
          have hne : φ y' ≠ φ y := by
            intro e; rw [hφ _ _ e] at hy'; exact hy hy'
          simp only [List.mem_erase_of_ne hne]
        rw [hcongr]
        have ih := count_inj_le φ hφ Y hY' (Z.erase (φ y))
        rw [List.length_erase_of_mem hm] at ih
        have hpos : 0 < Z.length := List.length_pos_of_mem hm
        omega
      · rw [List.filter_cons_of_neg (by simpa using hm)]
        exact count_inj_le φ hφ Y hY' Z

/-- Forward query `(h, m)`: at most `|Z|` candidate cipher answers `y` put the
    DM output `compose h y` into `Z`. -/
theorem dm_forward_bad_count (h : Position) (hh : InjPos h) (Y : List Position) (hY : Y.Nodup)
    (Z : List Position) :
    (Y.filter (fun y => decide (compose h y ∈ Z))).length ≤ Z.length :=
  count_inj_le (compose h) (fun a b e => compose_left_cancel h a b hh e) Y hY Z

/-- Inverse query `(y, m)`: at most `|Z|` candidate answers `h` put
    `compose h y` into `Z`. -/
theorem dm_inverse_bad_count (y : Position) (hy : InjPos y) (Hs : List Position) (hH : Hs.Nodup)
    (Z : List Position) :
    (Hs.filter (fun h => decide (compose h y ∈ Z))).length ≤ Z.length :=
  count_inj_le (fun h => compose h y) (fun a b e => leftMul_cancel a b y hy.1 hy.2 e) Hs hH Z

/-- Every reachable chaining value has digest rank `< |G|` (`groupOrder`).
    Only this bound is proved here (with injectivity in `DigestInj`); that
    the encoding hits every rank `< |G|` (surjectivity, an unrank) is not. -/
theorem reachable_rank_lt_group (r : List (List Nat)) :
    rankPosition (chR dmBlock Em.ivCook12 r) < groupOrder :=
  rankPosition_lt_group _ (injPos_chR r)

end MegaDreifach.Security
