/-
  SECURITY. Same-`h` cancellation for the software Davies–Meyer step of MegaDreifach v3.
  Not a collision-resistance claim and not a PRF claim. A green build of this file is
  not a security claim.

  `Em.dmStep h deal = compose h (Em.emBlock h deal)`. In `MegaDreifach.Group` that is
  `leftMul h (Em.emBlock h deal)`: the block's permutations are on the left of `h`'s
  (`(emBlock h deal).cp ∘ h.cp`). With `W = emBlock h deal`, that is the software
  feed-forward (left-multiplication by `W` in that sense). It is not the hand 3-solve
  product `h·W·h`.

  For one fixed chaining value, `dmStep h b = dmStep h b'` if and only if
  `emBlock h b = emBlock h b'`, once `h.cp` and `h.ep` are injective. Those two
  hypotheses are exactly `InjPos h` (`MegaDreifach.Link2.InjPos`). They are not
  assumed for a bare `Position`. `isLegal` is the same two injectivities plus even
  permutations and orientation parities; this lemma does not use the parities.
  Every reachable v3 chaining value is `InjPos`: `injPos_ivCook12`, then `dmStep_inj`
  and `injPos_chainPre`. Nothing is said when the two chaining values differ.

  `Group.leftMul_cancel` is the other cancellation. From `leftMul T g = leftMul T' g`
  and `Injective g.cp`, `Injective g.ep` it concludes `T = T'` (the shared factor is
  the right one, and that factor must be injective). A same-`h` collision is
  `leftMul h W = leftMul h W'`, so `leftMul_cancel` does not apply. The injectivity
  has to be assumed of `h`, and the proof is surjectivity of an injective `Fin` map
  (`MegaDreifachV3.Link2.surj_of_inj_fin`) plus cancellation in `Fin 3` and `Fin 2`.

  Zero sorry. No native_decide.
-/
import MegaDreifachV3.Em
import MegaDreifachV3.Link2.FaceOfFound

namespace MegaDreifachV3.Security

open MegaDreifach
open MegaDreifachV3.Link2 (surj_of_inj_fin)

/-- `dmStep` is left multiplication by the chaining value, in `Group.leftMul`:
    the block output is the right factor. -/
private theorem dmStep_leftMul (h : Position) (b : List Nat) :
    Em.dmStep h b = leftMul h (Em.emBlock h b) := by
  unfold Em.dmStep
  exact (leftMul_eq_compose h (Em.emBlock h b)).symm

/-- Cancel a shared left factor of `compose` when that factor's permutation tables
    are injective. See the module note for why this is not `leftMul_cancel`. -/
private theorem compose_cancel_left (h y y' : Position) (hcp : Injective h.cp)
    (hep : Injective h.ep) (heq : compose h y = compose h y') : y = y' := by
  have hcpEq : y.cp ∘ h.cp = y'.cp ∘ h.cp := congrArg Position.cp heq
  have hepEq : y.ep ∘ h.ep = y'.ep ∘ h.ep := congrArg Position.ep heq
  have hco := congrArg Position.co heq
  have heo := congrArg Position.eo heq
  apply Position.ext
  · funext t
    obtain ⟨s, rfl⟩ := surj_of_inj_fin h.cp hcp t
    exact congrFun hcpEq s
  · funext t
    obtain ⟨s, rfl⟩ := surj_of_inj_fin h.cp hcp t
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
    obtain ⟨s, rfl⟩ := surj_of_inj_fin h.ep hep t
    exact congrFun hepEq s
  · funext t
    obtain ⟨s, rfl⟩ := surj_of_inj_fin h.ep hep t
    have e := congrFun heo s
    simp only [compose] at e
    apply Fin.ext
    have e' := congrArg Fin.val e
    simp only [Fin.val_add] at e'
    have a := (y.eo (h.ep s)).isLt
    have b := (y'.eo (h.ep s)).isLt
    have c := (h.eo s).isLt
    omega

/-- Same-h cancellation for software DM.
    `dmStep h b = dmStep h b'` iff `emBlock h b = emBlock h b'`,
    when `Injective h.cp` and `Injective h.ep` (exactly `InjPos h`).
    Says nothing when the chaining values differ.
    Not a collision-resistance claim and not a PRF claim.
    A green build is not a security claim. -/
theorem dmStep_same_h_iff (h : Position) (hcp : Injective h.cp) (hep : Injective h.ep)
    (b b' : List Nat) :
    Em.dmStep h b = Em.dmStep h b' ↔ Em.emBlock h b = Em.emBlock h b' := by
  constructor
  · intro hstep
    -- `leftMul_cancel h ? ?` does not match: the shared factor is the left one.
    have hmul : leftMul h (Em.emBlock h b) = leftMul h (Em.emBlock h b') := by
      simpa [dmStep_leftMul] using hstep
    exact compose_cancel_left h _ _ hcp hep (by simpa [leftMul] using hmul)
  · intro hW
    simp [Em.dmStep, hW]

/-- The contentful direction of `dmStep_same_h_iff`: a same-`h` `dmStep` collision
    is an `emBlock` collision. The other direction is congruence and needs no
    hypothesis on `h`. Not a collision-resistance claim and not a PRF claim. -/
theorem emBlock_eq_of_dmStep_eq (h : Position) (hcp : Injective h.cp) (hep : Injective h.ep)
    (b b' : List Nat) (hstep : Em.dmStep h b = Em.dmStep h b') :
    Em.emBlock h b = Em.emBlock h b' :=
  (dmStep_same_h_iff h hcp hep b b').mp hstep

end MegaDreifachV3.Security
