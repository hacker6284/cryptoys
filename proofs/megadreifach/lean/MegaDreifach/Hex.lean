/-
  Lower-case hex strings to byte lists. Used to state the hash KATs directly on
  the `msgHex` / `digestHex` strings of `Vectors.lean` (generated from the
  v1 KAT JSON), so each digest is written exactly once
  (`MegaDreifachHeavy/Kat.lean`), and by the compiled metadata checks
  (`VectorCheck.lean`). `vectors/json_to_lean.py` only admits lower-case hex.
-/
namespace MegaDreifach

/-- Value of a lower-case hex digit (`0-9`, `a-f`). -/
def hexNib (c : Char) : Nat :=
  if c.toNat ≤ 57 then c.toNat - 48 else c.toNat - 87

/-- Hex digits (as chars), two per byte, to bytes. -/
def hexBytesL : List Char → List Nat
  | a :: b :: rest => (16 * hexNib a + hexNib b) :: hexBytesL rest
  | _ => []

/-- Lower-case hex string to bytes. -/
def hexBytes (s : String) : List Nat := hexBytesL s.toList

end MegaDreifach
