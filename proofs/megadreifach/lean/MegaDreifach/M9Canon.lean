import MegaDreifach.G2CovRead
import MegaDreifach.M9Cert

/-!
# M9 at the canonical grip: the decoder check

Owns: the kernel decoder for the M9 canonical-grip search (the definitions checked
per intermediate grip in `M9Dec*.lean`) and the lemmas that turn a passed check
into a statement about net products.

At grip `gripId`, a 2-card window `(a, b)` whose intermediate grip is `rotAt s1` has
net product `compose (conj s1 (N0 b)) (N0 a)` (`N0 a = net2 gripId a`, `n0_table`;
`G2Cov.net2_cov`).  The certificate `M9Cert` is a decision tree over the slot codes of
such a product.  `chkB s1 b = true` says: for every first card `a < 52`, the tree,
walked on the codes of the product, ends at the leaf `a`, or at an ambiguity group
that lists `(a, s1, b)` together with the two `W`-slots its second read sees.  The
tree is untrusted data; only the checked walk matters (`decode_spec`).

Cost notes (kernel, Lean v4.14.0): values that are used more than once are forced
once through `force` / `forceB` (the kernel substitutes `let`s and arguments
unevaluated); the tree words live in one big `Nat` (`M9Cert.m9big`) read by shift
and mask; the conjugated net is packed into four `Nat`s once per `(s1, b)`.
-/

namespace MegaDreifach.M9

open MegaDreifach MegaDreifach.Em MegaDreifach.Link2 MegaDreifach.G2Cov MegaDreifach.M9Cert

/-- The 52 nets at `gripId`, from the packed certificate tables. -/
def N0 (b : Nat) : Position := posN n0CpN n0CoN n0EpN n0EoN b

theorem n0_table : allN 52 (fun b => posEqN (G2Nets.net2 gripId b) (N0 b)) = true := by decide!

theorem net2_gripId (b : Nat) (hb : b < 52) : G2Nets.net2 gripId b = N0 b :=
  posEqN_spec (allN_spec n0_table b hb)

/-- Slot code `t` of a position: corner slot `t < 20` gives `3 cp + co`, edge slot
    `t - 20 < 30` gives `60 + 2 ep + eo` (as `m9_search.code`). -/
def codeOf (P : Position) (t : Nat) : Nat :=
  if h : t < 20 then 3 * (P.cp ⟨t, h⟩).val + (P.co ⟨t, h⟩).val
  else if h2 : t - 20 < 30 then 60 + 2 * (P.ep ⟨t - 20, h2⟩).val + (P.eo ⟨t - 20, h2⟩).val else 0

/-- `force n k = k n`, evaluating `n` once. -/
def force (n : Nat) (k : Nat → Nat) : Nat :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

/-- `forceB n k = k n`, evaluating `n` once. -/
def forceB (n : Nat) (k : Nat → Bool) : Bool :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem forceB_eq (n : Nat) (k : Nat → Bool) : forceB n k = k n := by
  cases n <;> rfl

/-- Tree word `i`. -/
def tw (i : Nat) : Nat := Nat.land (Nat.shiftRight m9big (26 * i)) 67108863

/-- Binary search for the entry with value `v` among the sorted entries
    `base + lo … base + hi - 1` (`0` if absent). -/
def bs (v base : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, lo, hi =>
    if Nat.blt lo hi then
      force (tw (base + (lo + hi) / 2)) fun e =>
      force (Nat.shiftRight e 19) fun ev =>
      if Nat.beq ev v then e
      else if Nat.blt ev v then bs v base f ((lo + hi) / 2 + 1) hi else bs v base f lo ((lo + hi) / 2)
    else 0

/-- The entry for value `v` at the node at offset `o`. -/
def step (o v : Nat) : Nat :=
  force (tw (o + 1)) fun k =>
    if Nat.beq k 1000 then tw (o + 2 + v) else bs v (o + 2) 8 0 k

/-- Walk the tree from offset `o`, querying slot codes with `q`; the leaf payload, or
    `999999` on a missing entry or when the fuel runs out. -/
def walk (q : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 999999
  | f + 1, o =>
    force (q (tw o)) fun v =>
    force (step o v) fun e =>
    if Nat.beq e 0 then 999999
    else if Nat.beq (Nat.shiftRight e 18 % 2) 1 then e % 262144
    else walk q f (e % 262144)

/-- The read configuration of the second card `b` at grip `rotAt s1` after the first
    card `a` at `gripId`, from the identity: `(g1, oW, held)`. -/
def mid (a s1 b : Nat) : Position × Grip × Fin 12 := g2Mid (N0 a, rotAt s1) b

/-- The `W`-slots the second read sees, packed `corner · 100 + edge`. -/
def wsl (a s1 b : Nat) : Nat :=
  let m := mid a s1 b
  let phys := m.2.1 m.2.2
  let noon := visualNoon m.2.2 m.2.1
  (m.1.cp (cornerSlot phys noon (cornerAfterNoon phys noon))).val * 100 +
    (m.1.ep (edgeSlot phys noon)).val

/-- Membership of `(a, s1, b)`, with its read slots, in ambiguity group `r - 100`. -/
def inAmb (a s1 b r : Nat) : Bool :=
  (ambG.getD (r - 100) []).any (fun e =>
    Nat.beq (e / 10000) (a * 10000 + s1 * 100 + b) && Nat.beq (e % 10000) (wsl a s1 b))

/-- The walk on the codes of `compose M (N0 a)` names `a`, or an ambiguity group
    holding `(a, s1, b)`. -/
def decOk (a s1 b : Nat) (M : Position) : Bool :=
  forceB (walk (codeOf (compose M (N0 a))) 40 0) fun r =>
    Nat.beq r a || (Nat.ble 100 r && inAmb a s1 b r)

def packF (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.lor (packF w f n) (Nat.shiftLeft (f n) (w * n))

def cpv (M : Position) (i : Nat) : Nat := if h : i < 20 then (M.cp ⟨i, h⟩).val else 0
def cov (M : Position) (i : Nat) : Nat := if h : i < 20 then (M.co ⟨i, h⟩).val else 0
def epv (M : Position) (i : Nat) : Nat := if h : i < 30 then (M.ep ⟨i, h⟩).val else 0
def eov (M : Position) (i : Nat) : Nat := if h : i < 30 then (M.eo ⟨i, h⟩).val else 0

/-- The check for intermediate grip `s1` and second card `b`, over all first cards
    `a < 52`.  The conjugated net is packed once (and the packing checked). -/
def chkB (s1 b : Nat) : Bool :=
  forceB (packF 5 (cpv (conj s1 (N0 b))) 20) fun mc =>
  forceB (packF 2 (cov (conj s1 (N0 b))) 20) fun mo =>
  forceB (packF 5 (epv (conj s1 (N0 b))) 30) fun me =>
  forceB (packF 1 (eov (conj s1 (N0 b))) 30) fun mf =>
  posEqN (conj s1 (N0 b)) (posN mc mo me mf 0) &&
    allN 52 (fun a => decOk a s1 b (posN mc mo me mf 0))

/-- Emit `m9dec_<s>` for `lo ≤ s < hi`: `allN 52 (chkB s) = true` by kernel `decide!`. -/
macro "gen_m9_dec" lo:num hi:num : command => do
  let mut cmds : Array (Lean.TSyntax `command) := #[]
  for s in List.range (hi.getNat - lo.getNat) do
    let s := s + lo.getNat
    let id := Lean.mkIdent (Lean.Name.mkSimple s!"m9dec_{s}")
    let n := Lean.Syntax.mkNumLit (toString s)
    cmds := cmds.push (← `(command| theorem $id : allN 52 (fun b => chkB $n b) = true := by decide!))
  return ⟨Lean.mkNullNode cmds⟩

/-- What a passed `chkB s1 b` gives for one first card `a < 52`. -/
theorem chkB_spec {s1 b : Nat} (h : chkB s1 b = true) (a : Nat) (ha : a < 52) :
    decOk a s1 b (conj s1 (N0 b)) = true := by
  unfold chkB at h
  simp only [forceB_eq, Bool.and_eq_true] at h
  rw [posEqN_spec h.1]
  exact allN_spec h.2 a ha

/-- A passed decoder check, unfolded: the walk result `r` on the product's codes is
    `a`, or `≥ 100` with `(a, s1, b)` and its read slots listed in group `r - 100`. -/
theorem decOk_spec {a s1 b : Nat} {M : Position} (h : decOk a s1 b M = true) :
    walk (codeOf (compose M (N0 a))) 40 0 = a ∨
      (100 ≤ walk (codeOf (compose M (N0 a))) 40 0 ∧
        inAmb a s1 b (walk (codeOf (compose M (N0 a))) 40 0) = true) := by
  unfold decOk at h
  rw [forceB_eq] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  exact h

end MegaDreifach.M9
