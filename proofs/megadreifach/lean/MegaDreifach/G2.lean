/-
  M8 / M9 — one-card G2 injectivity (algebraic reduction) and L2 scaffolding.

  Shipped sorry-free:
    * left-multiplication cancellation (from Group)
    * Theorem A *reduction*: card ↦ φ_card(g,o) is injective as soon as
      the face-turn nets `T_card(o)` are pairwise distinct
    * same-first-card 2-card states differ once the second-card nets differ
      (G2_PROOF.md §3 corollary, as a reduction)

  Not shipped (see STONES.md — OPEN, no `sorry` theorems):
    * pairwise distinctness of the 60×52 concrete nets (computer-checked
      in `g2_proof_core.prove_one_card`; too large for kernel `decide`)
    * abs-G2 L2 mid-block = 0 for distinct first cards (M9)

  Zero sorry. No native_decide.
-/
import MegaDreifach.Group
import MegaDreifach.Basic

namespace MegaDreifach

/-- Held-face amount `k = suit+1 ∈ {1,2,3,4}`. -/
def cardAmount (suit : Nat) : Nat := suit + 1

/-- King (`rank = 12`) uses `king_up`: turn Up by `-k` (mod 5). -/
def kingUpAmount (k : Nat) : Nat := (5 - k % 5) % 5

/-- Ace-of-suit turns Up by `+k`; King of the same suit turns Up by `-k`.
    These amounts differ for every legal `k ∈ {1,2,3,4}` — the reason the
    soft-lock forbids treating King as Ace. Not a full net-distinctness proof. -/
theorem kingUpAmount_ne_ace (k : Nat) (h1 : 1 ≤ k) (h4 : k ≤ 4) :
    kingUpAmount k ≠ k := by
  simp [kingUpAmount]
  have hk : k % 5 = k := Nat.mod_eq_of_lt (by omega)
  rw [hk]
  have : (5 - k) % 5 = 5 - k := Nat.mod_eq_of_lt (by omega)
  rw [this]
  omega

/-- One-card G2 step: left-multiply by the face-turn net, then reorient the grip.
    `ω` is the grip type (60 rotations in the Python model). -/
def phiCard {ω : Type _}
    (net : ω → Nat → Position)
    (reorient : ω → Position → Nat → ω)
    (g : Position) (o : ω) (card : Nat) : Position × ω :=
  (compose (net o card) g, reorient o (compose (net o card) g) card)

/-- M8 reduction (G2_PROOF Theorem A): if nets at a fixed grip are pairwise
    distinct, `card ↦ φ_card(g,o)` is injective for injective `g`. -/
theorem phiCard_inj_of_distinct_nets {ω : Type _}
    (net : ω → Nat → Position)
    (reorient : ω → Position → Nat → ω)
    (g : Position) (o : ω)
    (hgcp : Injective g.cp) (hgep : Injective g.ep)
    (hdist : ∀ c1 c2 : Nat, c1 ≠ c2 → net o c1 ≠ net o c2)
    {c1 c2 : Nat} (hne : c1 ≠ c2) :
    phiCard net reorient g o c1 ≠ phiCard net reorient g o c2 := by
  intro heq
  have hT : compose (net o c1) g = compose (net o c2) g :=
    congrArg Prod.fst heq
  have : net o c1 = net o c2 :=
    leftMul_cancel (net o c1) (net o c2) g hgcp hgep hT
  exact hdist c1 c2 hne this

/-- Two-card nets with the same first card collide at `g` only if the
    composed nets `T_b ∘ T_a` and `T_d ∘ T_a` are equal. Left-cancel `g`. -/
theorem two_card_net_eq_of_state_eq {ω : Type _}
    (net : ω → Nat → Position)
    (gripAfter : ω → Nat → ω)
    (g : Position) (o : ω) (a b d : Nat)
    (hgcp : Injective g.cp) (hgep : Injective g.ep)
    (heq :
      compose (net (gripAfter o a) b) (compose (net o a) g) =
      compose (net (gripAfter o a) d) (compose (net o a) g)) :
    compose (net (gripAfter o a) b) (net o a) =
    compose (net (gripAfter o a) d) (net o a) := by
  have hb : compose (net (gripAfter o a) b) (compose (net o a) g) =
      compose (compose (net (gripAfter o a) b) (net o a)) g := by
    rw [← compose_assoc]
  have hd : compose (net (gripAfter o a) d) (compose (net o a) g) =
      compose (compose (net (gripAfter o a) d) (net o a)) g := by
    rw [← compose_assoc]
  rw [hb, hd] at heq
  exact leftMul_cancel _ _ g hgcp hgep heq

/-- G2_PROOF §3 corollary, as a reduction: if the second-card nets at the
    shared intermediate grip are distinct and that first-net position is
    injective, the two-card states differ. -/
theorem no_same_first_two_card_of_nets {ω : Type _}
    (net : ω → Nat → Position)
    (o1 : ω) (b d : Nat)
    (hdist : net o1 b ≠ net o1 d)
    (first : Position)
    (hfirst_cp : Injective first.cp)
    (hfirst_ep : Injective first.ep) :
    compose (net o1 b) first ≠ compose (net o1 d) first := by
  intro heq
  exact hdist (leftMul_cancel (net o1 b) (net o1 d) first hfirst_cp hfirst_ep heq)

end MegaDreifach
