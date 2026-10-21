/-
  `exchange` follows the card: length and trit asserts, two publishes, then
  swap, curve, certify, rebuild, swap, compare, and the shared walk. A
  nonempty failure text returns that text. The emitted term also pastes the
  later steps into the failing branch; those copies test the same text and
  return it. The exchange does not invert, so it takes no `FieldOk`.
  Proof-only. Not a security claim.
-/
import Ecbs

namespace EcbsLink2.Link2

open Ecbs

/-- The same guard in the else is not taken. -/
private theorem collapse_mid {α : Type} (c : Bool) (live mid rest : α) :
    (if c then live else if c then mid else rest) = (if c then live else rest) := by
  cases c <;> rfl

/-- A false guard's last copy returns the error arm. -/
private theorem drop0 {α : Type} (c : Bool) (live err ok : α) :
    (if c then live else if !c then err else ok) = (if c then live else err) := by
  cases c <;> rfl

/-- The card's exchange. "A: reroll (empty key or exceptional case)" and the
    same text for B are the two publish refusals. Later steps return the text
    the step produced. -/
def exchangeCard (t : Tier) (cells_a cells_b : Array Int) :
    Except SudoRt.Trap (SudoRt.SResult (Array Int) Exchange) :=
  do
    let _t1956 ← (if (SudoRt.SEq.beq (SudoRt.listLen cells_a) (t).sudo_4Tier_5cells) then (do
  pure (SudoRt.SEq.beq (SudoRt.listLen cells_b) (t).sudo_4Tier_5cells)) else pure false)
    let _as1959 ← SudoRt.sudoAssert _t1956 1428
    let _t1960 ← is_trits cells_a
    let _t1961 ← (if _t1960 then (do
  let _t1962 ← is_trits cells_b
  pure _t1962) else pure false)
    let _as1963 ← SudoRt.sudoAssert _t1961 1429
    let _t1964 ← new_board t
    let ba := _t1964
    let _t1965 ← new_board t
    let bb := _t1965
    let _t1966 ← blank_player ba
    let pa := _t1966
    let _t1967 ← blank_player bb
    let pb := _t1967
    let _io1968 ← publish ba cells_a pa
    let ⟨_ret1969, _iw01970, _iw11971⟩ := _io1968
    let ba := _iw01970
    let pa := _iw11971
    let _sudo_h0 := _ret1969
    if (!( _sudo_h0 )) then
      do
        pure (SudoRt.SResult.err (#[65, 58, 32, 114, 101, 114, 111, 108, 108, 32, 40, 101, 109, 112, 116, 121, 32, 107, 101, 121, 32, 111, 114, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 97, 108, 32, 99, 97, 115, 101, 41] : Array Int))
    else
      do
        let _io1972 ← publish bb cells_b pb
        let ⟨_ret1973, _iw01974, _iw11975⟩ := _io1972
        let bb := _iw01974
        let pb := _iw11975
        let _sudo_h1 := _ret1973
        if (!( _sudo_h1 )) then
          do
            pure (SudoRt.SResult.err (#[66, 58, 32, 114, 101, 114, 111, 108, 108, 32, 40, 101, 109, 112, 116, 121, 32, 107, 101, 121, 32, 111, 114, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 97, 108, 32, 99, 97, 115, 101, 41] : Array Int))
        else
          do
            let _io1976 ← swap_both ba bb
            let ⟨_iw01977, _iw11978⟩ := _io1976
            let ba := _iw01977
            let bb := _iw11978
            let _io1979 ← curve_tests ba bb pa pb
            let ⟨_ret1980, _iw01981, _iw11982, _iw21983, _iw31984⟩ := _io1979
            let ba := _iw01981
            let bb := _iw11982
            let pa := _iw21983
            let pb := _iw31984
            let fail := _ret1980
            if (SudoRt.SEq.beq fail (#[] : Array Int)) then
              do
                let _io1986 ← certify_own ba bb pa pb
                let ⟨_ret1987, _iw01988, _iw11989, _iw21990, _iw31991⟩ := _io1986
                let ba := _iw01988
                let bb := _iw11989
                let pa := _iw21990
                let pb := _iw31991
                let fail := _ret1987
                if (SudoRt.SEq.beq fail (#[] : Array Int)) then
                  do
                    let _io1993 ← rebuild_theirs ba bb pa pb
                    let ⟨_ret1994, _iw01995, _iw11996, _iw21997, _iw31998⟩ := _io1993
                    let ba := _iw01995
                    let bb := _iw11996
                    let pa := _iw21997
                    let pb := _iw31998
                    let fail := _ret1994
                    if (SudoRt.SEq.beq fail (#[] : Array Int)) then
                      do
                        let _io2000 ← swap_both ba bb
                        let ⟨_iw02001, _iw12002⟩ := _io2000
                        let ba := _iw02001
                        let bb := _iw12002
                        let _io2003 ← compare_both ba bb pa pb
                        let ⟨_ret2004, _iw02005, _iw12006, _iw22007, _iw32008⟩ := _io2003
                        let ba := _iw02005
                        let bb := _iw12006
                        let pa := _iw22007
                        let pb := _iw32008
                        let fail := _ret2004
                        if (SudoRt.SEq.beq fail (#[] : Array Int)) then
                          do
                            let _io2010 ← walk_and_fold ba bb pa pb cells_a cells_b
                            let ⟨_ret2011, _iw02012, _iw12013, _iw22014, _iw32015⟩ := _io2010
                            let ba := _iw02012
                            let bb := _iw12013
                            let pa := _iw22014
                            let pb := _iw32015
                            let fail := _ret2011
                            if (!(SudoRt.SEq.beq fail (#[] : Array Int))) then
                              do
                                pure (SudoRt.SResult.err fail)
                            else
                              do
                                let _io2017 ← report ba pa
                                let pa := _io2017
                                let _io2018 ← report bb pb
                                let pb := _io2018
                                pure (SudoRt.SResult.ok ({ sudo_8Exchange_1a := pa, sudo_8Exchange_1b := pb } : Exchange))
                        else
                          do
                            pure (SudoRt.SResult.err fail)
                    else
                      do
                        pure (SudoRt.SResult.err fail)
                else
                  do
                    pure (SudoRt.SResult.err fail)
            else
              do
                pure (SudoRt.SResult.err fail)


/-- The emitted `exchange` is the card. Failing branches do not run the later step. -/
theorem exchange_card (t : Tier) (cells_a cells_b : Array Int) :
    exchange t cells_a cells_b = exchangeCard t cells_a cells_b := by
  unfold exchange exchangeCard
  simp only [collapse_mid, drop0]

end EcbsLink2.Link2
