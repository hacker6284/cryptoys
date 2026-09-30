/-
  PROOF-ONLY. The hand-written model of DoubleDeal-CBC-HMAC's byte helpers, written
  from primitives/aead/doubledeal-cbc-hmac/SPEC.md (§2 parameters, §3.1 pad, §3.3
  chain, §4 HMAC, §5 key schedule, §6.1 MAC input, §6.3 tag compare). Sudo does not
  emit this file.

  Plain `List Nat` byte strings, no traps, no i64. The hash is a parameter `H`
  (SPEC §4: "Standard HMAC with MegaDreifach as H"); the Link 2 theorems
  (`DoubleDealCbcHmac.Link2`) instantiate it with the algebraic MegaDreifach hash
  `MegaDreifach.Link2.vhashAlg`, which `v_Hash_refines` proves equal to the
  generated `Megadreifach.v_Hash`. `vhashAlg` is a transliteration of the MegaDreifach
  sudo, not an independent specification of the hash: the Link 2 theorems prove the
  HMAC / KDF wiring around the hash; the hash itself is only as independent as
  `vhashAlg`.

  Not the byte-domain CBC encrypt / decrypt (that ranks a deck and stays in JS,
  SPEC §3.3 / §3.4), not an AEAD or PRF claim.
-/
namespace DoubleDealCbcHmac

/-- SPEC §2: HMAC block size `B` (the MegaDreifach pad block). -/
def hmacBlock : Nat := 28
/-- SPEC §2: a CBC message block (the §5.3 injective 28-byte encoding). Numerically
    equal to `hmacBlock`, but a different parameter: pad / unpad and `K_enc_bytes`
    use this one. -/
def msgBlock : Nat := 28
/-- SPEC §2: a CBC ciphertext block is the 29-byte rank. -/
def cipherBlock : Nat := 29
/-- SPEC §4: `ipad = 0x36^B`, `opad = 0x5c^B`. -/
def ipadByte : Nat := 0x36
def opadByte : Nat := 0x5c

/-- ASCII bytes of a label. -/
def ascii (s : String) : List Nat := s.toList.map Char.toNat

/-- SPEC §2 / §6.1: the version label. -/
def versionLabel : List Nat := ascii "DoubleDeal-CBC-HMAC/v1"
/-- SPEC §5: the two key-schedule labels. -/
def encLabel : List Nat := ascii "DoubleDeal-CBC-HMAC/v1/enc"
def macLabel : List Nat := ascii "DoubleDeal-CBC-HMAC/v1/mac"

/-- Bytewise XOR of two strings of the same length. -/
def xorBytes (a b : List Nat) : List Nat := List.zipWith (· ^^^ ·) a b

/-- The last `w` base-256 digits of `n`, most significant first. -/
def beBytes (w n : Nat) : List Nat := (List.range w).reverse.map fun i => n / 256 ^ i % 256

/-- SPEC §5: big-endian 16- and 64-bit lengths. -/
def u16be (n : Nat) : List Nat := beBytes 2 n
def u64be (n : Nat) : List Nat := beBytes 8 n

/-- SPEC §4.1, steps 1-3: hash a key longer than `B`, cut a still-longer key to its
    first `B` bytes, then right-pad with `0x00` to `B`. -/
def normalizeKey (H : List Nat → List Nat) (k : List Nat) : List Nat :=
  let k1 := if hmacBlock < k.length then H k else k
  let k2 := if hmacBlock < k1.length then k1.take hmacBlock else k1
  k2 ++ List.replicate (hmacBlock - k2.length) 0

/-- SPEC §4.2: `HMAC(K, m) = H((K' ⊕ opad) ‖ H((K' ⊕ ipad) ‖ m))`. -/
def hmac (H : List Nat → List Nat) (k m : List Nat) : List Nat :=
  let k' := normalizeKey H k
  H (xorBytes k' (List.replicate hmacBlock opadByte) ++
    H (xorBytes k' (List.replicate hmacBlock ipadByte) ++ m))

/-- SPEC §3.1: append `0x80`, then `0x00` until the length is a multiple of 28. -/
def pad (m : List Nat) : List Nat :=
  let out := m ++ [0x80]
  out ++ List.replicate ((msgBlock - out.length % msgBlock) % msgBlock) 0

/-- SPEC §3.1 unpad: a nonempty stream whose length is a multiple of 28 and which
    ends in `0x80` followed only by `0x00`; strip that suffix. Anything else is
    rejected (`none`). -/
def unpad (m : List Nat) : Option (List Nat) :=
  if m.length = 0 ∨ m.length % msgBlock ≠ 0 then none
  else
    match m.reverse.dropWhile (· == 0) with
    | 0x80 :: rest => some rest.reverse
    | _ => none

/-- SPEC §6.1: the length-delimited Encrypt-then-MAC input. -/
def macInput (aad iv c : List Nat) : List Nat :=
  u16be versionLabel.length ++ versionLabel ++ u64be aad.length ++ aad ++
    u64be iv.length ++ iv ++ u64be c.length ++ c

/-- SPEC §5: `(K_enc_bytes, K_mac)` from one master secret (nonempty; the empty
    master is rejected, which is a domain condition here). -/
def deriveKeys (H : List Nat → List Nat) (mk : List Nat) : List Nat × List Nat :=
  ((H (u16be encLabel.length ++ encLabel ++ u64be mk.length ++ mk)).take msgBlock,
    H (u16be macLabel.length ++ macLabel ++ u64be mk.length ++ mk))

/-- SPEC §3.3: `chain_{i+1} = C_i[1..28]`, dropping the most significant rank byte. -/
def cbcChain (block : List Nat) : List Nat := block.drop 1

/-- SPEC §6.3 step 4: full-length tag comparison. -/
def tagsEqual (a b : List Nat) : Bool := decide (a = b)

end DoubleDealCbcHmac
