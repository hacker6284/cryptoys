/-
  KAT metadata next to the proof-only package. Hexes refreshed 2026-09-24
  to current megadreifach.sudo (Python and emitted Lean agree).
  Full digest evaluation in *this* package is still M13 OPEN; algorithm
  Hash is Generated.v_Hash. See proofs/ANTI_DRIFT.md.
-/
namespace MegaDreifach.Vectors

structure HashVec where
  name : String
  msgLen : Nat
  paddedLen : Nat
  nBlocks : Nat
  digestHex : String
deriving Repr, Inhabited

def digestLen : Nat := 29
def padBlock : Nat := 28

/-- From `kats/megaminx_hash_kats.json` (`group_order_hex`). -/
def groupOrderHex : String :=
  "0x3bbea482ed28698b1ec5fb346d240d1433047d5800000000000000000"

/-- IV-COOK12 digest hex from the same KAT file. -/
def ivCook12DigestHex : String :=
  "0000021aeb876eb76dd8bf833457a2c02613e55656963e02d8dfedb5aa"

def vectors : List HashVec :=
  [ { name := "empty",     msgLen := 0,   paddedLen := 28,  nBlocks := 1, digestHex := "037ef5274eebea6ed847821573d575f9d7a0d593d31787d8a50bedf55e" }
  , { name := "short_abc", msgLen := 3,   paddedLen := 28,  nBlocks := 1, digestHex := "025959c0ab2cdad7536956e3490cec6b2711b5d73c5731af2d4ecff550" }
  , { name := "short_one", msgLen := 1,   paddedLen := 28,  nBlocks := 1, digestHex := "02e8785e47149ea0d03cc39c4ffd5c3ee21568197394a48744cc3c53f5" }
  , { name := "edge_27",   msgLen := 27,  paddedLen := 56,  nBlocks := 2, digestHex := "01d701043ab21d88a52ffed94b46896dc18e15f775c3d661fec3f9fed8" }
  , { name := "edge_28",   msgLen := 28,  paddedLen := 56,  nBlocks := 2, digestHex := "0354488e90201f310b87eb4cdda3ac1fabcd9671fd08f4836b325cf8f1" }
  , { name := "edge_29",   msgLen := 29,  paddedLen := 56,  nBlocks := 2, digestHex := "01b991a6db6297877c7c4f72283cf3f6c8e7a3f91f0a82c141562b9835" }
  , { name := "multi_56",  msgLen := 56,  paddedLen := 84,  nBlocks := 3, digestHex := "00a5059319ad22533bc2156fa140dc17d8969dfa6bafe751848eebe724" }
  , { name := "multi_100", msgLen := 100, paddedLen := 112, nBlocks := 4, digestHex := "0156e9f32a565e585893eab5229ea6a12c959c743d9c3e420827139e20" }
  ]

end MegaDreifach.Vectors
