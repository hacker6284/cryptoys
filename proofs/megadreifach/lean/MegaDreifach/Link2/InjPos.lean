/-
  Invariant `InjPos` (injective corner / edge permutation tables) is preserved by
  `compose`, `faceMove` and `faceTurn`, and holds at `identity` and at `ivCook12` (the
  identity cooked by twelve unit face turns, so only `faceTurn` is needed). Model only, version-neutral: v2's InjInv (grips,
  `emBlock`, `dmStep`, `ivCook12`) and v3's RunStep (card phase) both import it.
  Zero sorry. No native_decide.
-/
import MegaDreifach.Em
import MegaDreifach.Link2.PosBytesGen

namespace MegaDreifach.Link2

open MegaDreifach

theorem injective_comp {α β γ : Type _} {f : β → γ} {g : α → β}
    (hf : Injective f) (hg : Injective g) : Injective (f ∘ g) :=
  fun h => hg (hf h)

theorem injPos_compose (g h : Position) (hg : InjPos g) (hh : InjPos h) :
    InjPos (compose g h) :=
  ⟨injective_comp hh.1 hg.1, injective_comp hh.2 hg.2⟩

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
