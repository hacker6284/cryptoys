/-
  M8 for v2 — concrete one-card net distinctness (G2_PROOF Theorem A, instantiated).

  The v2 card step `Em.g2Step` left-multiplies the position by a face-turn word that
  depends only on the grip and the card (`net2 o card`, the step from the identity;
  `g2Step_fst_net`).  This file checks, by kernel `decide!` (no `native_decide`),
  that for each of the 60 grips `rotAt s` the 52 nets are pairwise distinct — already
  their corner permutations `listOf (net2 (rotAt s) c).cp` are (`nets_nodup_<s>`,
  one small kernel evaluation per grip).  Consequences:

  * `net2_ne`: on every `GripOk` grip (one of the 60 rotations), distinct cards
    `< 52` have distinct nets;
  * `g2Step_fst_ne` / `g2Step_ne`: from any position with injective `cp` / `ep`
    (e.g. every `InjPos` chaining value), two different cards at the same grip give
    different positions after one card step, whatever the read positions;
  * `phiCard_net2_ne`: the abstract M8 reduction (`phiCard_inj_of_distinct_nets`)
    instantiated with the v2 nets.

  Scope: one card, fixed grip.  Not M9 (two-card local collisions), not collision
  resistance.  Zero sorry.  No native_decide.
-/
import MegaDreifach.G2
import MegaDreifach.Link2.EmInv
import MegaDreifach.Security.StepWord

namespace MegaDreifach.G2Nets

open MegaDreifach MegaDreifach.Em MegaDreifach.Link2

/-- The v2 one-card net at grip `o`: the position part of a G2 step from the
    identity (it does not depend on the read position). -/
def net2 (o : Grip) (card : Nat) : Position := (g2Step (identity, o) card 1).1

theorem g2Step_fst_indep (o : Grip) (card pos : Nat) :
    (g2Step (identity, o) card pos).1 = net2 o card := by
  unfold net2 g2Step
  rfl

/-- A card step is left multiplication by the net. -/
theorem g2Step_fst_net (g : Position) (o : Grip) (card pos : Nat) :
    (g2Step (g, o) card pos).1 = compose (net2 o card) g := by
  rw [Security.g2Step_fst, g2Step_fst_indep]

/-- Corner-permutation fingerprints of the 52 nets at grip `rotAt s`. -/
def netCps (s : Nat) : List (List Nat) :=
  (List.range 52).map (fun c => listOf (net2 (rotAt s) c).cp)

/-! ## Kernel checks, one per grip -/

theorem nets_nodup_0 : (netCps 0).Nodup := by decide!
theorem nets_nodup_1 : (netCps 1).Nodup := by decide!
theorem nets_nodup_2 : (netCps 2).Nodup := by decide!
theorem nets_nodup_3 : (netCps 3).Nodup := by decide!
theorem nets_nodup_4 : (netCps 4).Nodup := by decide!
theorem nets_nodup_5 : (netCps 5).Nodup := by decide!
theorem nets_nodup_6 : (netCps 6).Nodup := by decide!
theorem nets_nodup_7 : (netCps 7).Nodup := by decide!
theorem nets_nodup_8 : (netCps 8).Nodup := by decide!
theorem nets_nodup_9 : (netCps 9).Nodup := by decide!
theorem nets_nodup_10 : (netCps 10).Nodup := by decide!
theorem nets_nodup_11 : (netCps 11).Nodup := by decide!
theorem nets_nodup_12 : (netCps 12).Nodup := by decide!
theorem nets_nodup_13 : (netCps 13).Nodup := by decide!
theorem nets_nodup_14 : (netCps 14).Nodup := by decide!
theorem nets_nodup_15 : (netCps 15).Nodup := by decide!
theorem nets_nodup_16 : (netCps 16).Nodup := by decide!
theorem nets_nodup_17 : (netCps 17).Nodup := by decide!
theorem nets_nodup_18 : (netCps 18).Nodup := by decide!
theorem nets_nodup_19 : (netCps 19).Nodup := by decide!
theorem nets_nodup_20 : (netCps 20).Nodup := by decide!
theorem nets_nodup_21 : (netCps 21).Nodup := by decide!
theorem nets_nodup_22 : (netCps 22).Nodup := by decide!
theorem nets_nodup_23 : (netCps 23).Nodup := by decide!
theorem nets_nodup_24 : (netCps 24).Nodup := by decide!
theorem nets_nodup_25 : (netCps 25).Nodup := by decide!
theorem nets_nodup_26 : (netCps 26).Nodup := by decide!
theorem nets_nodup_27 : (netCps 27).Nodup := by decide!
theorem nets_nodup_28 : (netCps 28).Nodup := by decide!
theorem nets_nodup_29 : (netCps 29).Nodup := by decide!
theorem nets_nodup_30 : (netCps 30).Nodup := by decide!
theorem nets_nodup_31 : (netCps 31).Nodup := by decide!
theorem nets_nodup_32 : (netCps 32).Nodup := by decide!
theorem nets_nodup_33 : (netCps 33).Nodup := by decide!
theorem nets_nodup_34 : (netCps 34).Nodup := by decide!
theorem nets_nodup_35 : (netCps 35).Nodup := by decide!
theorem nets_nodup_36 : (netCps 36).Nodup := by decide!
theorem nets_nodup_37 : (netCps 37).Nodup := by decide!
theorem nets_nodup_38 : (netCps 38).Nodup := by decide!
theorem nets_nodup_39 : (netCps 39).Nodup := by decide!
theorem nets_nodup_40 : (netCps 40).Nodup := by decide!
theorem nets_nodup_41 : (netCps 41).Nodup := by decide!
theorem nets_nodup_42 : (netCps 42).Nodup := by decide!
theorem nets_nodup_43 : (netCps 43).Nodup := by decide!
theorem nets_nodup_44 : (netCps 44).Nodup := by decide!
theorem nets_nodup_45 : (netCps 45).Nodup := by decide!
theorem nets_nodup_46 : (netCps 46).Nodup := by decide!
theorem nets_nodup_47 : (netCps 47).Nodup := by decide!
theorem nets_nodup_48 : (netCps 48).Nodup := by decide!
theorem nets_nodup_49 : (netCps 49).Nodup := by decide!
theorem nets_nodup_50 : (netCps 50).Nodup := by decide!
theorem nets_nodup_51 : (netCps 51).Nodup := by decide!
theorem nets_nodup_52 : (netCps 52).Nodup := by decide!
theorem nets_nodup_53 : (netCps 53).Nodup := by decide!
theorem nets_nodup_54 : (netCps 54).Nodup := by decide!
theorem nets_nodup_55 : (netCps 55).Nodup := by decide!
theorem nets_nodup_56 : (netCps 56).Nodup := by decide!
theorem nets_nodup_57 : (netCps 57).Nodup := by decide!
theorem nets_nodup_58 : (netCps 58).Nodup := by decide!
theorem nets_nodup_59 : (netCps 59).Nodup := by decide!

theorem nets_nodup : ∀ s, s < 60 → (netCps s).Nodup
  | 0, _ => nets_nodup_0
  | 1, _ => nets_nodup_1
  | 2, _ => nets_nodup_2
  | 3, _ => nets_nodup_3
  | 4, _ => nets_nodup_4
  | 5, _ => nets_nodup_5
  | 6, _ => nets_nodup_6
  | 7, _ => nets_nodup_7
  | 8, _ => nets_nodup_8
  | 9, _ => nets_nodup_9
  | 10, _ => nets_nodup_10
  | 11, _ => nets_nodup_11
  | 12, _ => nets_nodup_12
  | 13, _ => nets_nodup_13
  | 14, _ => nets_nodup_14
  | 15, _ => nets_nodup_15
  | 16, _ => nets_nodup_16
  | 17, _ => nets_nodup_17
  | 18, _ => nets_nodup_18
  | 19, _ => nets_nodup_19
  | 20, _ => nets_nodup_20
  | 21, _ => nets_nodup_21
  | 22, _ => nets_nodup_22
  | 23, _ => nets_nodup_23
  | 24, _ => nets_nodup_24
  | 25, _ => nets_nodup_25
  | 26, _ => nets_nodup_26
  | 27, _ => nets_nodup_27
  | 28, _ => nets_nodup_28
  | 29, _ => nets_nodup_29
  | 30, _ => nets_nodup_30
  | 31, _ => nets_nodup_31
  | 32, _ => nets_nodup_32
  | 33, _ => nets_nodup_33
  | 34, _ => nets_nodup_34
  | 35, _ => nets_nodup_35
  | 36, _ => nets_nodup_36
  | 37, _ => nets_nodup_37
  | 38, _ => nets_nodup_38
  | 39, _ => nets_nodup_39
  | 40, _ => nets_nodup_40
  | 41, _ => nets_nodup_41
  | 42, _ => nets_nodup_42
  | 43, _ => nets_nodup_43
  | 44, _ => nets_nodup_44
  | 45, _ => nets_nodup_45
  | 46, _ => nets_nodup_46
  | 47, _ => nets_nodup_47
  | 48, _ => nets_nodup_48
  | 49, _ => nets_nodup_49
  | 50, _ => nets_nodup_50
  | 51, _ => nets_nodup_51
  | 52, _ => nets_nodup_52
  | 53, _ => nets_nodup_53
  | 54, _ => nets_nodup_54
  | 55, _ => nets_nodup_55
  | 56, _ => nets_nodup_56
  | 57, _ => nets_nodup_57
  | 58, _ => nets_nodup_58
  | 59, _ => nets_nodup_59
  | _ + 60, h => absurd h (by omega)

/-! ## Consequences -/

theorem eq_of_nodup_map {α β : Type} (f : α → β) : ∀ (l : List α), (l.map f).Nodup →
    ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => absurd hx (List.not_mem_nil x)
  | a :: l, hnd, x, hx, y, hy, hxy => by
      rw [List.map_cons, List.nodup_cons] at hnd
      have hnot : ∀ z ∈ l, f z ≠ f a := fun z hz he => hnd.1 (List.mem_map.mpr ⟨z, hz, he⟩)
      rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
      · rfl
      · exact absurd hxy.symm (hnot y hy')
      · exact absurd hxy (hnot x hx')
      · exact eq_of_nodup_map f l hnd.2 x hx' y hy' hxy

/-- M8 (v2 nets): on each of the 60 grips, distinct cards have distinct nets. -/
theorem net2_ne (o : Grip) (ho : GripOk o) {c1 c2 : Nat} (h1 : c1 < 52) (h2 : c2 < 52)
    (hne : c1 ≠ c2) : net2 o c1 ≠ net2 o c2 := by
  obtain ⟨s, hs, rfl⟩ := ho
  intro heq
  apply hne
  exact eq_of_nodup_map (fun c => listOf (net2 (rotAt s) c).cp) (List.range 52)
    (nets_nodup s hs) c1 (List.mem_range.mpr h1) c2 (List.mem_range.mpr h2)
    (by simp only [heq])

/-- One card step from a position with injective `cp` / `ep` (e.g. `InjPos`): two
    different cards at the same `GripOk` grip give different positions. -/
theorem g2Step_fst_ne (g : Position) (hcp : Injective g.cp) (hep : Injective g.ep)
    (o : Grip) (ho : GripOk o) {c1 c2 : Nat} (h1 : c1 < 52) (h2 : c2 < 52)
    (hne : c1 ≠ c2) (pos1 pos2 : Nat) :
    (g2Step (g, o) c1 pos1).1 ≠ (g2Step (g, o) c2 pos2).1 := by
  rw [g2Step_fst_net, g2Step_fst_net]
  intro heq
  exact net2_ne o ho h1 h2 hne (leftMul_cancel _ _ g hcp hep heq)

theorem g2Step_ne (g : Position) (hg : InjPos g) (o : Grip) (ho : GripOk o)
    {c1 c2 : Nat} (h1 : c1 < 52) (h2 : c2 < 52) (hne : c1 ≠ c2) (pos : Nat) :
    g2Step (g, o) c1 pos ≠ g2Step (g, o) c2 pos := fun heq =>
  g2Step_fst_ne g hg.1 hg.2 o ho h1 h2 hne pos pos (congrArg Prod.fst heq)

/-- The M8 statement in the shape of `phiCard` (G2.lean), with the v2 nets: for card
    ids `< 52` on a `GripOk` grip, `card ↦ phiCard net2 reorient g o card` is
    injective, for any grip update `reorient`. -/
theorem phiCard_net2_ne (reorient : Grip → Position → Nat → Grip) (g : Position)
    (hgcp : Injective g.cp) (hgep : Injective g.ep) (o : Grip) (ho : GripOk o)
    {c1 c2 : Nat} (h1 : c1 < 52) (h2 : c2 < 52) (hne : c1 ≠ c2) :
    phiCard net2 reorient g o c1 ≠ phiCard net2 reorient g o c2 := fun heq =>
  net2_ne o ho h1 h2 hne (leftMul_cancel _ _ g hgcp hgep (congrArg Prod.fst heq))

/-! ## M9 (partial): two-card windows -/

theorem g2Step_fst_net' (st : Position × Grip) (card pos : Nat) :
    (g2Step st card pos).1 = compose (net2 st.2 card) st.1 := by
  obtain ⟨g, o⟩ := st
  exact g2Step_fst_net g o card pos

/-- M9, same-first-card half: two 2-card windows that share the first card and differ
    in the second never give the same state (M8 at the intermediate grip). -/
theorem twoCard_same_first_ne (g : Position) (hg : InjPos g) (o : Grip) (ho : GripOk o)
    (a pos1 : Nat) {b d : Nat} (hb : b < 52) (hd : d < 52) (hne : b ≠ d) (pos2 : Nat) :
    g2Step (g2Step (g, o) a pos1) b pos2 ≠ g2Step (g2Step (g, o) a pos1) d pos2 :=
  g2Step_ne _ (injPos_g2Step (g, o) a pos1 hg) _ (gripOk_g2Step (g, o) a pos1 ho) hb hd hne pos2

/-- M9 reduction: if two 2-card windows from an injective position reach the same
    position, the two products of nets at the intermediate grips are equal (the
    position `g` cancels).  This is the finite condition the M9 search enumerates. -/
theorem twoCard_collision_nets (g : Position) (hcp : Injective g.cp) (hep : Injective g.ep)
    (o : Grip) (a b c d pos1 pos2 : Nat)
    (heq : (g2Step (g2Step (g, o) a pos1) b pos2).1 = (g2Step (g2Step (g, o) c pos1) d pos2).1) :
    compose (net2 (g2Step (g, o) a pos1).2 b) (net2 o a) =
      compose (net2 (g2Step (g, o) c pos1).2 d) (net2 o c) := by
  rw [g2Step_fst_net' (g2Step (g, o) a pos1) b pos2, g2Step_fst_net' (g2Step (g, o) c pos1) d pos2,
    g2Step_fst_net g o a pos1, g2Step_fst_net g o c pos1,
    ← compose_assoc, ← compose_assoc] at heq
  exact leftMul_cancel _ _ g hcp hep heq

end MegaDreifach.G2Nets
