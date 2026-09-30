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
once through `force` (the kernel substitutes `let`s and arguments
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
  else if h2 : t - 20 < 30 then 60 + 2 * (P.ep ⟨t - 20, h2⟩).val + (P.eo ⟨t - 20, h2⟩).val
  else 0

/-- `force n k = k n`, evaluating `n` once (the match makes the kernel reduce `n` to a
    literal before substituting it into `k`). -/
def force {α : Type} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

theorem force_eq {α : Type} (n : Nat) (k : Nat → α) : force n k = k n := by
  cases n <;> rfl

/-! ## Certificate layout

These constants must match `m9/m9_cert.py`; the names in backquotes in each docstring are
the matching Python constants ("Certificate layout" block there). -/

/-- Bits per tree word (`WORD`). -/
abbrev wordBits : Nat := 26
/-- `2 ^ wordBits - 1`. -/
abbrev wordMask : Nat := 67108863
/-- A tree entry is `v <<< valShift ||| leaf <<< leafBit ||| payload` (`VAL_SHIFT`,
    `LEAF_BIT`): `v` the slot-code value, `leaf` set when the payload is a leaf label,
    else the payload is the word offset of the child node. -/
abbrev valShift : Nat := 19
abbrev leafBit : Nat := 18
/-- `2 ^ leafBit`: the payload field. -/
abbrev payMod : Nat := 262144
/-- Count word of a densely laid out node (`DENSE_TAG`): its entries are indexed by `v`. -/
abbrev denseTag : Nat := 1000
/-- Leaf labels `≥ ambBase` name ambiguity group `label - ambBase` (`AMB_BASE`); smaller
    labels are first cards. -/
abbrev ambBase : Nat := 100
/-- Walk result on a missing entry or when the fuel runs out. -/
abbrev noLeaf : Nat := 999999
/-- Base of the two-digit decimal fields of ambiguity entries and `wsl` (`FIELD`): an entry
    is `a·10⁸ + s1·10⁶ + b·10⁴ + w1·100 + w0`. -/
abbrev fieldB : Nat := 100
/-- `fieldB ^ 2`: the entry's slot part `w1·100 + w0` is `e % slotsB`, its item part
    `a·10⁴ + s1·100 + b` is `e / slotsB`. -/
abbrev slotsB : Nat := 10000
/-- `fieldB ^ 4`: an entry's first card is `e / cardB` (used in `M9.pairOk`). -/
abbrev cardB : Nat := 100000000
/-- Bits per packed net entry, `cp`/`co`/`ep`/`eo` (`CP_BITS` … `EO_BITS`); the widths of
    `G2Cov.posN`. -/
abbrev cpBits : Nat := 5
abbrev coBits : Nat := 2
abbrev epBits : Nat := 5
abbrev eoBits : Nat := 1

theorem layout_consts :
    wordMask = 2 ^ wordBits - 1 ∧ payMod = 2 ^ leafBit ∧ leafBit + 1 = valShift ∧
      slotsB = fieldB ^ 2 ∧ cardB = fieldB ^ 4 := by decide

/-- Tree word `i`. -/
def tw (i : Nat) : Nat := Nat.land (Nat.shiftRight m9big (wordBits * i)) wordMask

/-- Binary search for the entry with value `v` among the sorted entries
    `base + lo … base + hi - 1` (`0` if absent). -/
def bs (v base : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, lo, hi =>
    if Nat.blt lo hi then
      force (tw (base + (lo + hi) / 2)) fun e =>
      force (Nat.shiftRight e valShift) fun ev =>
      if Nat.beq ev v then e
      else if Nat.blt ev v then bs v base f ((lo + hi) / 2 + 1) hi
      else bs v base f lo ((lo + hi) / 2)
    else 0

/-- The entry for value `v` at the node at offset `o`. -/
def step (o v : Nat) : Nat :=
  force (tw (o + 1)) fun k =>
    if Nat.beq k denseTag then tw (o + 2 + v) else bs v (o + 2) 8 0 k

/-- Walk the tree from offset `o`, querying slot codes with `q`; the leaf payload, or
    `noLeaf` on a missing entry or when the fuel runs out. -/
def walk (q : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => noLeaf
  | f + 1, o =>
    force (q (tw o)) fun v =>
    force (step o v) fun e =>
    if Nat.beq e 0 then noLeaf
    else if Nat.beq (Nat.shiftRight e leafBit % 2) 1 then e % payMod
    else walk q f (e % payMod)

/-- The read configuration of the second card `b` at grip `rotAt s1` after the first
    card `a` at `gripId`, from the identity: `(g1, oW, held)`. -/
def mid (a s1 b : Nat) : Position × Grip × Fin 12 := g2Mid (N0 a, rotAt s1) b

/-- The `W`-slots the second read sees, packed `corner · fieldB + edge`. -/
def wsl (a s1 b : Nat) : Nat :=
  let m := mid a s1 b
  let phys := m.2.1 m.2.2
  let noon := visualNoon m.2.2 m.2.1
  (m.1.cp (cornerSlot phys noon (cornerAfterNoon phys noon))).val * fieldB +
    (m.1.ep (edgeSlot phys noon)).val

/-- Membership of `(a, s1, b)`, with its read slots, in ambiguity group `r - ambBase`. -/
def inAmb (a s1 b r : Nat) : Bool :=
  (ambG.getD (r - ambBase) []).any (fun e =>
    Nat.beq (e / slotsB) (a * slotsB + s1 * fieldB + b) && Nat.beq (e % slotsB) (wsl a s1 b))

/-- The walk on the codes of `compose M (N0 a)` names `a`, or an ambiguity group
    holding `(a, s1, b)`. -/
def decOk (a s1 b : Nat) (M : Position) : Bool :=
  force (walk (codeOf (compose M (N0 a))) 40 0) fun r =>
    Nat.beq r a || (Nat.ble ambBase r && inAmb a s1 b r)

def packF (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.lor (packF w f n) (Nat.shiftLeft (f n) (w * n))

def cpv (M : Position) (i : Nat) : Nat := if h : i < 20 then (M.cp ⟨i, h⟩).val else 0
def coVal (M : Position) (i : Nat) : Nat := if h : i < 20 then (M.co ⟨i, h⟩).val else 0
def epv (M : Position) (i : Nat) : Nat := if h : i < 30 then (M.ep ⟨i, h⟩).val else 0
def eov (M : Position) (i : Nat) : Nat := if h : i < 30 then (M.eo ⟨i, h⟩).val else 0

/-- The check for intermediate grip `s1` and second card `b`, over all first cards
    `a < 52`.  The conjugated net is packed once (and the packing checked). -/
def chkB (s1 b : Nat) : Bool :=
  force (packF cpBits (cpv (conj s1 (N0 b))) 20) fun mc =>
  force (packF coBits (coVal (conj s1 (N0 b))) 20) fun mo =>
  force (packF epBits (epv (conj s1 (N0 b))) 30) fun me =>
  force (packF eoBits (eov (conj s1 (N0 b))) 30) fun mf =>
  posEqN (conj s1 (N0 b)) (posN mc mo me mf 0) &&
    allN 52 (fun a => decOk a s1 b (posN mc mo me mf 0))

/-- Emit `m9dec_<s>` for `lo ≤ s < hi`: `allN 52 (chkB s) = true` by kernel `decide!`. -/
macro "gen_m9_dec" lo:num hi:num : command => do
  let mut cmds : Array (Lean.TSyntax `command) := #[]
  for s in List.range (hi.getNat - lo.getNat) do
    let s := s + lo.getNat
    let id := Lean.mkIdent (Lean.Name.mkSimple s!"m9dec_{s}")
    let n := Lean.Syntax.mkNumLit (toString s)
    cmds := cmds.push
      (← `(command| theorem $id : allN 52 (fun b => chkB $n b) = true := by decide!))
  return ⟨Lean.mkNullNode cmds⟩

/-- What a passed `chkB s1 b` gives for one first card `a < 52`. -/
theorem chkB_spec {s1 b : Nat} (h : chkB s1 b = true) (a : Nat) (ha : a < 52) :
    decOk a s1 b (conj s1 (N0 b)) = true := by
  unfold chkB at h
  simp only [force_eq, Bool.and_eq_true] at h
  rw [posEqN_spec h.1]
  exact allN_spec h.2 a ha

/-- A passed decoder check, unfolded: the walk result `r` on the product's codes is
    `a`, or `≥ ambBase` with `(a, s1, b)` and its read slots listed in group `r - ambBase`. -/
theorem decOk_spec {a s1 b : Nat} {M : Position} (h : decOk a s1 b M = true) :
    walk (codeOf (compose M (N0 a))) 40 0 = a ∨
      (ambBase ≤ walk (codeOf (compose M (N0 a))) 40 0 ∧
        inAmb a s1 b (walk (codeOf (compose M (N0 a))) 40 0) = true) := by
  unfold decOk at h
  rw [force_eq] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at h
  exact h

end MegaDreifach.M9
