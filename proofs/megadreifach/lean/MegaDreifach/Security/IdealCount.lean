/-
  SECURITY (ideal-cipher bookkeeping, not a security claim).  The
  combinatorial core of the Black–Rogaway–Shrimpton Davies–Meyer bounds, for
  the group-DM `h ↦ compose h y` on megaminx positions:

  * `compose_left_cancel`: for `InjPos h`, `y ↦ compose h y` is injective
    (uses pigeonhole `injective_surjective_fin`, proved via `availAt_specN`).
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
  `proofs/megadreifach/security/REPORT.md`).  These bounds do NOT apply to
  MegaDreifach v1: its block map is not an ideal cipher
  (`CornerDriven.emBlock_word` gives a 2-query distinguisher).

  Grip-rule status: INDEPENDENT of the grip rule.  The cancellation and
  counting lemmas are group facts about `compose` and need no repair if E_m
  changes.  `reachable_rank_lt_group` goes through `MDReduction.injPos_chR`
  (see the note there).

  Zero sorry.  No native_decide.
-/
import MegaDreifach.Security.MDReduction

namespace MegaDreifach.Security

open MegaDreifach MegaDreifach.Link2

/-- Pigeonhole on `Fin n`: injective ⇒ surjective. -/
theorem injective_surjective_fin {n : Nat} (f : Fin n → Fin n) (hf : Injective f) (t : Fin n) :
    ∃ s, f s = t := by
  have wf := permNWf_listOf f hf
  have spec := availAt_specN n (listOf f) wf n (Nat.le_refl _)
  obtain ⟨_, hlen, hmem⟩ := spec
  rw [Nat.sub_self] at hlen
  have hnil : availAt (listOf f) n = [] := List.eq_nil_of_length_eq_zero hlen
  have ht : t.val ∈ (listOf f).take n := by
    have h := hmem t.val
    rw [hnil] at h
    exact Decidable.byContradiction fun hc => List.not_mem_nil _ (h.mpr ⟨t.isLt, hc⟩)
  rw [List.take_of_length_le (by rw [listOf_length]; exact Nat.le_refl _)] at ht
  unfold listOf at ht
  obtain ⟨i, hi, he⟩ := List.mem_map.mp ht
  have hi' : i < n := List.mem_range.mp hi
  refine ⟨⟨i, hi'⟩, Fin.ext ?_⟩
  simp only [hi', dite_true] at he
  exact he

/-- Left cancellation: `y ↦ compose h y` is injective when `h` is. -/
theorem compose_left_cancel (h y y' : Position) (hh : InjPos h)
    (heq : compose h y = compose h y') : y = y' := by
  have hcp : y.cp ∘ h.cp = y'.cp ∘ h.cp := congrArg Position.cp heq
  have hep : y.ep ∘ h.ep = y'.ep ∘ h.ep := congrArg Position.ep heq
  have hco := congrArg Position.co heq
  have heo := congrArg Position.eo heq
  apply Position.ext
  · funext t
    obtain ⟨s, rfl⟩ := injective_surjective_fin h.cp hh.1 t
    exact congrFun hcp s
  · funext t
    obtain ⟨s, rfl⟩ := injective_surjective_fin h.cp hh.1 t
    have e := congrFun hco s
    simp only [compose] at e
    apply Fin.ext
    have e' := congrArg Fin.val e
    simp only [Fin.val_add] at e'
    have a := (y.co (h.cp s)).isLt
    have b := (y'.co (h.cp s)).isLt
    have c := (h.co s).isLt
    omega
  · funext t
    obtain ⟨s, rfl⟩ := injective_surjective_fin h.ep hh.2 t
    exact congrFun hep s
  · funext t
    obtain ⟨s, rfl⟩ := injective_surjective_fin h.ep hh.2 t
    have e := congrFun heo s
    simp only [compose] at e
    apply Fin.ext
    have e' := congrArg Fin.val e
    simp only [Fin.val_add] at e'
    have a := (y.eo (h.ep s)).isLt
    have b := (y'.eo (h.ep s)).isLt
    have c := (h.eo s).isLt
    omega

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
