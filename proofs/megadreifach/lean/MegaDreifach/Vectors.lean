/-
  KAT metadata committed next to the Lean model (layer (b) evidence).
  Trust base is compiled Lean evaluation (`lake exe megadreifach`), not
  kernel `decide`. Full digest agreement (M13) needs the G2 runner and is
  OPEN; this file checks pad lengths, block counts, digest width, and
  `|G|` against `kats/megaminx_hash_kats.json`.
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
  [ { name := "empty",     msgLen := 0,   paddedLen := 28,  nBlocks := 1, digestHex := "02c61941965591f80bc8745dbd40b49d4f1b472577831237e56786337a" }
  , { name := "short_abc", msgLen := 3,   paddedLen := 28,  nBlocks := 1, digestHex := "020edc31b9adaa4c48ea1f923c52628dad132ac97c4505eab6d00eb61f" }
  , { name := "short_one", msgLen := 1,   paddedLen := 28,  nBlocks := 1, digestHex := "01f8b3eefdff0e0784675521c4e904aa11abcc7a1a1a9d50940607fc93" }
  , { name := "edge_27",   msgLen := 27,  paddedLen := 56,  nBlocks := 2, digestHex := "0186323895f62c1abe61b59620cbadd66593f8454c7e25ce79d6920cbc" }
  , { name := "edge_28",   msgLen := 28,  paddedLen := 56,  nBlocks := 2, digestHex := "01ee6c5410a01d9a257f6d0852aeab2c1f0379d91e3bfa2d6acba66d24" }
  , { name := "edge_29",   msgLen := 29,  paddedLen := 56,  nBlocks := 2, digestHex := "02a0a2b9009cada74ea8de85add20a08c288023b76289724bf089b1132" }
  , { name := "multi_56",  msgLen := 56,  paddedLen := 84,  nBlocks := 3, digestHex := "002184ae974e5828d00ced7e9c0b974674dcd0dc06700f12b3664a98bf" }
  , { name := "multi_100", msgLen := 100, paddedLen := 112, nBlocks := 4, digestHex := "03653417a3db817cdd0df1398ca93f957c0d78f7887ffca8f0b116ebcd" }
  ]

end MegaDreifach.Vectors
