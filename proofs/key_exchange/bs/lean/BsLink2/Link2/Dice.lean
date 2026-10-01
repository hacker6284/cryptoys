/-
  BS Link 2: §4.2 the dice record. The emitted `dice` refines `Spec.dice`.
  The build itself (`build_key_grid`, `build_letting_go`) is not covered here.
-/
import BsLink2.Link2.Key

namespace BsLink2.Link2

/-- Model dice as the emitted `Dice` (read counts as non-negative `Int`s). -/
def embDice (d : Spec.Dice) : Bs.Dice :=
  { sudo_4Dice_3d12 := d.d12.toArray, sudo_4Dice_2d6 := d.d6.toArray,
    sudo_4Dice_3d10 := d.d10.toArray, sudo_4Dice_6next12 := Int.ofNat d.next12,
    sudo_4Dice_5next6 := Int.ofNat d.next6, sudo_4Dice_6next10 := Int.ofNat d.next10 }

/-- §4.2. For any three face streams, the emitted `dice` is the model's fresh dice. -/
theorem dice_refines (d12 d6 d10 : List Int) :
    Bs.dice d12.toArray d6.toArray d10.toArray = .ok (embDice (Spec.dice d12 d6 d10)) := rfl

end BsLink2.Link2
