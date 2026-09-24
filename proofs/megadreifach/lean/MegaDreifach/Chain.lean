/-
  M12 — Merkle–Damgård chaining is the fold of DM compressions;
  the digest is the rank-encoding of the final chaining value.
  Zero sorry. No native_decide.
-/
import MegaDreifach.DaviesMeyer
import MegaDreifach.Pad

namespace MegaDreifach

/-- One padded 28-byte block, as a Nat (big-endian). -/
abbrev BlockNat := Nat

/-- MD chain: `h₀ = iv`; `hᵢ = dm hᵢ₋₁ mᵢ`. -/
def mdChain (dm : Position → BlockNat → Position) (iv : Position)
    (blocks : List BlockNat) : Position :=
  blocks.foldl dm iv

@[simp] theorem mdChain_nil (dm : Position → BlockNat → Position) (iv : Position) :
    mdChain dm iv [] = iv := rfl

theorem mdChain_cons (dm : Position → BlockNat → Position) (iv : Position)
    (b : BlockNat) (bs : List BlockNat) :
    mdChain dm iv (b :: bs) = mdChain dm (dm iv b) bs := rfl

theorem mdChain_append (dm : Position → BlockNat → Position) (iv : Position)
    (xs ys : List BlockNat) :
    mdChain dm iv (xs ++ ys) = mdChain dm (mdChain dm iv xs) ys := by
  induction xs generalizing iv with
  | nil => simp [mdChain]
  | cons x xs ih =>
      simp [mdChain, ih]

/-- Digest of a chaining value: 29-byte big-endian rank (encoding defined
    in `Rank.lean`; here we take an abstract rank so M12 does not depend
    on the even-perm unrank construction). -/
def digestOf (rank : Position → Nat) (h : Position) : List Nat :=
  toBE digestLen (rank h)

theorem digestOf_length (rank : Position → Nat) (h : Position) :
    (digestOf rank h).length = digestLen :=
  toBE_length _ _

/-- M12: the hash of a block list is the digest of the final chaining value. -/
def hashBlocks (dm : Position → BlockNat → Position) (rank : Position → Nat)
    (iv : Position) (blocks : List BlockNat) : List Nat :=
  digestOf rank (mdChain dm iv blocks)

theorem hashBlocks_eq_digest_of_final
    (dm : Position → BlockNat → Position) (rank : Position → Nat)
    (iv : Position) (blocks : List BlockNat) :
    hashBlocks dm rank iv blocks = digestOf rank (mdChain dm iv blocks) :=
  rfl

end MegaDreifach
