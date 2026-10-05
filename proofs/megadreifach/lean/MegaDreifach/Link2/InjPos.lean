/-
  Invariant `InjPos` (injective corner / edge permutation tables) is preserved by
  `compose`, `faceMove` and `faceTurn`, and holds at `identity` and at `ivCook12` (the
  identity cooked by twelve unit face turns, so only `faceTurn` is needed). Model only, version-neutral: v2's InjInv (grips,
  `emBlock`, `dmStep`, `ivCook12`) and v3's RunStep (card phase) both import it.

  `injective_surjective_fin` is the `Fin n` pigeonhole. `compose_left_cancel` is left
  cancellation of `compose` at an `InjPos` factor (`y ↦ compose h y` injective). v2
  `Security.IdealCount` and v3 `Security.DmStepSameH` call that one lemma.
  `Group.leftMul_cancel` is the other cancellation.
  Zero sorry. No native_decide.
-/
import MegaDreifach.Em
import MegaDreifach.Link2.PosBytesGen
import MegaDreifach.Link2.EvenRankGen

namespace MegaDreifach.Link2

open MegaDreifach

theorem injective_comp {α β γ : Type _} {f : β → γ} {g : α → β}
    (hf : Injective f) (hg : Injective g) : Injective (f ∘ g) :=
  fun h => hg (hf h)

theorem injPos_compose (g h : Position) (hg : InjPos g) (hh : InjPos h) :
    InjPos (compose g h) :=
  ⟨injective_comp hh.1 hg.1, injective_comp hh.2 hg.2⟩

/-- Pigeonhole on `Fin n`: injective ⇒ surjective. One copy; v3's piece-search
    proofs and `compose_left_cancel` both use it. -/
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

/-- Left cancellation: `y ↦ compose h y` is injective when `h` is `InjPos`.
    `Group.leftMul_cancel` is the other cancellation (an injective right factor). -/
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

theorem faceMove_cp_inj_dec :
    ∀ f : Fin 12, ∀ x y : Fin 20, (Em.faceMove f).cp x = (Em.faceMove f).cp y → x = y := by
  decide

theorem faceMove_ep_inj_dec :
    ∀ f : Fin 12, ∀ x y : Fin 30, (Em.faceMove f).ep x = (Em.faceMove f).ep y → x = y := by
  decide

theorem injPos_faceMove (f : Fin 12) : InjPos (Em.faceMove f) :=
  ⟨fun h => faceMove_cp_inj_dec f _ _ h, fun h => faceMove_ep_inj_dec f _ _ h⟩

theorem injPos_leftIter (T : Position) (hT : InjPos T) :
    ∀ n g, InjPos g → InjPos (Em.leftIter T n g)
  | 0, _, hg => hg
  | n + 1, g, hg => injPos_compose _ _ hT (injPos_leftIter T hT n g hg)

theorem injPos_faceTurn (g : Position) (f : Fin 12) (a : Nat) (hg : InjPos g) :
    InjPos (Em.faceTurn g f a) :=
  injPos_leftIter _ (injPos_faceMove f) _ _ hg

/-- The identity position has bijective tables. -/
theorem injPos_identity : InjPos MegaDreifach.identity := by
  constructor <;> intro a b h <;> exact h

/-- IV-COOK12 has bijective tables: it is the identity after twelve unit face turns. -/
theorem injPos_ivCook12 : InjPos Em.ivCook12 := by
  unfold Em.ivCook12
  generalize List.range 12 = l
  have key : ∀ (l : List Nat) (g : Position), InjPos g →
      InjPos (l.foldl (fun g f => if hf : f < 12 then Em.faceTurn g ⟨f, hf⟩ 1 else g) g) := by
    intro l
    induction l with
    | nil => intro g hg; exact hg
    | cons f l ih =>
      intro g hg
      apply ih
      dsimp only
      split
      · exact injPos_faceTurn g _ 1 hg
      · exact hg
  exact key l _ injPos_identity

end MegaDreifach.Link2
