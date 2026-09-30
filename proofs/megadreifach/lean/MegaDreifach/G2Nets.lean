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

  The file also holds the M9 same-first-card half (`twoCard_same_first_ne`) and the
  net-product reduction for different first cards (`twoCard_collision_nets`).  The
  different-first-card half and the full 2-card M9 statement (`twoCard_ne`) are in
  `M9.lean`.  Not collision resistance.  Zero sorry.  No native_decide.
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

/-! ## Kernel checks, one per grip

`gen_nets_nodup` emits 60 separate theorems `nets_nodup_0` … `nets_nodup_59`, each
`(netCps s).Nodup := by decide!`. They stay separate declarations on purpose: one
`decide!` over all 60 grips at once runs out of memory. `nets_nodup` collects them;
its proof term (`grip_cases% "nets_nodup"`) is a 60-way case split on `s`. Both generators
are core `macro`s (no `import Lean`). -/

/-- Emit the 60 per-grip kernel checks `nets_nodup_<s>`. -/
macro "gen_nets_nodup" : command => do
  let mut cmds : Array (Lean.TSyntax `command) := #[]
  for s in List.range 60 do
    let id := Lean.mkIdent (Lean.Name.mkSimple s!"nets_nodup_{s}")
    let n := Lean.Syntax.mkNumLit (toString s)
    cmds := cmds.push (← `(command| theorem $id : (netCps $n).Nodup := by decide!))
  return ⟨Lean.mkNullNode cmds⟩

/-- `grip_cases% "p"` is
    `fun s hs => if h : s = 0 then … p_0 else … if h : s = 59 then … p_59 else absurd hs …`,
    a 60-way case split collecting per-grip theorems `p_0` … `p_59` (resolved at the use
    site). Used for `nets_nodup` here and for `M9.dec_all`. -/
macro "grip_cases%" pfx:str : term => do
  let mut body ← `(absurd hs (by omega))
  for s in (List.range 60).reverse do
    let id := Lean.mkIdent (Lean.Name.mkSimple s!"{pfx.getString}_{s}")
    let n := Lean.Syntax.mkNumLit (toString s)
    body ← `(if h : s = $n then by subst h; exact $id else $body)
  `(fun s hs => $body)

gen_nets_nodup

theorem nets_nodup : ∀ s, s < 60 → (netCps s).Nodup := grip_cases% "nets_nodup"

/-! ## Consequences -/

theorem eq_of_nodup_map {α β : Type} (f : α → β) : ∀ (l : List α), (l.map f).Nodup →
    ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => absurd hx (List.not_mem_nil x)
  | a :: l, hnd, x, hx, y, hy, hxy => by
      rw [List.map_cons, List.nodup_cons] at hnd
      have hnot : ∀ z ∈ l, f z ≠ f a :=
        fun z hz he => hnd.1 (List.mem_map.mpr ⟨z, hz, he⟩)
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
