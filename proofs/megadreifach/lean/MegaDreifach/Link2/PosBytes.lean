/-
  LINK 2. `Generated.position_to_bytes` refines algebraic `positionToBytes`
  on `PosBytesWf`.

  The emitted digest is the mixed-radix Horner
  `(((cpRank * 3^19 + coPack) * (30!/2) + epRank) * 2^29 + eoPack)`
  then 29-byte big-endian. Proved bigint multiply is one limb times one
  limb, and proved add stays under `2 · 10^9`. On this domain the corner
  Lehmer rank, the corner-orientation pack, and the edge Lehmer rank are
  all zero, so those multiplies are the zero short-circuit (they still run).
  The 29 bytes are `toBE 29 (packOri2 eo)` for any `Ori2Wf` edge orientation.

  `even30` is the constant `30!/2` (four base-10^9 limbs). Not every legal
  position: a positive corner or edge rank leaves this limb fragment.
  Not `v_Hash`. Not emitter soundness. Not collision resistance.
-/
import Megadreifach
import MegaDreifach.Rank
import MegaDreifach.Link2.EvenRank
import MegaDreifach.Link2.Be
import MegaDreifach.Link2.Compose

namespace MegaDreifach.Link2

deriving instance DecidableEq for SudoRt.Trap
deriving instance DecidableEq for Megadreifach.BigInt

instance [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) := fun a b =>
  match a, b with
  | .ok x, .ok y =>
      if h : x = y then isTrue (by cases h; rfl)
      else isFalse (by intro h2; cases h2; exact h rfl)
  | .error e, .error f =>
      if h : e = f then isTrue (by cases h; rfl)
      else isFalse (by intro h2; cases h2; exact h rfl)
  | .ok _, .error _ => isFalse (by intro h; cases h)
  | .error _, .ok _ => isFalse (by intro h; cases h)

/-! ## `even30` is `30!/2` -/

/-- Little-endian base-10^9 limbs of `30!/2`. -/
def even30Limbs : List Nat := [240000000, 529318154, 429906095, 132626]

set_option maxHeartbeats 0 in
theorem even30_refines :
    Megadreifach.even30 = .ok (bigOf even30Limbs) := by
  decide

set_option maxHeartbeats 0 in
theorem even30Limbs_val : limbVal even30Limbs = evenPermCount 30 := by
  decide

theorem ori3_span_eq : Megadreifach.ori3_span = Int.ofNat (3 ^ 19) := by
  have h : (3 ^ 19 : Nat) = 1162261467 := by decide
  simp [Megadreifach.ori3_span, h]

theorem ori2_span_eq : Megadreifach.ori2_span = Int.ofNat (2 ^ 29) := by
  have h : (2 ^ 29 : Nat) = 536870912 := by decide
  simp [Megadreifach.ori2_span, h]

theorem digest_len_eq : Megadreifach.digest_len = Int.ofNat digestLen := by
  simp [Megadreifach.digest_len, digestLen]

/-! ## 29-byte `big_to_be` for an i64 -/

private theorem fits29 : FitsLen 29 := by
  unfold FitsLen i64MaxNat
  decide

private theorem fits30 : FitsLen 30 := by
  unfold FitsLen i64MaxNat
  decide

theorem two_pow29_lt_limbBase : 2 ^ 29 < limbBase := by
  decide

theorem two_pow29_lt_be : 2 ^ 29 < 256 ^ digestLen := by
  have h : 2 ^ 29 < 256 ^ 29 := by decide
  simp [digestLen, h]

theorem beStep_width (w v i : Nat) (hv : FitsLen v) (hwf : FitsLen w)
    (hi1 : 1 ≤ i) (hiw : i ≤ w) :
    beStep (Int.ofNat w) (Int.ofNat i, beAcc v i) =
      if i = w then
        .ok (SudoRt.Flow.brk (Int.ofNat i, beAcc v (i + 1)))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), beAcc v (i + 1))) := by
  unfold beStep beAcc
  dsimp
  rw [← ofNat_eq_natCast i, ← ofNat_eq_natCast w, if_neg (ofNat_not_gt hiw)]
  have hv' : FitsLen (v / 256 ^ (i - 1)) := FitsLen.of_le hv (Nat.div_le_self _ _)
  rw [divmod256_refines _ hv', ok_bind, appendL_spec]
  have hdiv : (v / 256 ^ (i - 1)) / 256 = v / 256 ^ i := by
    have hi : (i - 1) + 1 = i := by omega
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← pow256_succ, hi]
  erw [← Int.ofNat_emod (v / 256 ^ (i - 1)) 256]
  rw [← ofNat_eq_natCast ((v / 256 ^ (i - 1)) % 256),
    push_embed (leBytes (i - 1) v) ((v / 256 ^ (i - 1)) % 256), hdiv]
  have hle :
      leBytes (i - 1) v ++ [(v / 256 ^ (i - 1)) % 256] = leBytes ((i - 1) + 1) v :=
    (leBytes_succ_append (i - 1) v).symm
  have hidx : (i - 1) + 1 = i := by omega
  rw [hle, hidx]
  have hnext : (i + 1) - 1 = i := by omega
  by_cases hi : i = w
  · simp [hi, hle, hnext, beq_int_iff]
    rfl
  · have hne : ¬ (i : Int) = (w : Int) := fun h => hi (Int.ofNat.inj h)
    have hadd := addI_ofNat_one i (FitsLen.of_le hwf (by omega))
    rw [ofNat_eq_natCast i] at hadd
    simp [hi, hle, hnext, ite_int_beq, hne, hadd, ok_bind]

theorem be_down_width (w v : Nat) (hw : 0 < w) (hwf : FitsLen w)
    (hbyte : v < 256 ^ w) :
    SudoRt.runLoopOn (Int.ofNat (w - 1), embed ((leBytes w v).drop w).reverse)
        (fuelDown (Int.ofNat (w - 1)) 0)
        (downCopyStep (embed (leBytes w v)))
        (fun σ => (pure σ.2 : Except SudoRt.Trap (Array Int)))
        (fun r => pure r) =
      .ok (embed (toBE w v)) := by
  have hidx : (w - 1) + 1 = w := Nat.sub_add_cancel (Nat.succ_le_of_lt hw)
  conv in (List.drop w (leBytes w v)) =>
    arg 1
    rw [← hidx]
  apply chain_down (downCopyStep (embed (leBytes w v)))
    (f := fun i => embed ((leBytes w v).drop (i + 1)).reverse)
    (g := fun i => embed ((leBytes w v).drop i).reverse)
    (fromN := w - 1)
    (hstep := by
      intro i hi
      have hlt : i < (leBytes w v).length := by
        rw [leBytes_length]
        omega
      exact down_hit (leBytes w v) i hlt (FitsLen.of_le hwf (by omega)))
    (hlink := by
      intro i hp _
      dsimp
      rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hp)])
    (goal := .ok (embed (toBE w v)))
    (hafter := by
      simp only [List.drop_zero]
      rw [← toBE_eq_leRev w v hbyte]
      rfl)

/-- `big_to_be` of an i64 at width `w ≥ 1`, when the value fits in `w` bytes. -/
theorem big_to_be_width (w v : Nat) (hw : 0 < w) (hwf : FitsLen w) (hv : FitsLen v)
    (hbyte : v < 256 ^ w) :
    Megadreifach.big_to_be (bigNat v) (Int.ofNat w) =
      .ok (embed (toBE w v)) := by
  unfold Megadreifach.big_to_be bigNat
  dsimp
  rw [except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise (step' := beStep (Int.ofNat w))
    intro σ
    unfold beStep
    rfl
  rw [← ofNat_eq_natCast w, fuelRange_eq (1 : Int) (Int.ofNat w)]
  rw [show (1 : Int) = Int.ofNat 1 from rfl,
    show (#[] : Array Int) = embed ([] : List Nat) from rfl, ← beAcc_one v]
  apply chain_loop (beStep (Int.ofNat w))
    (f := beAcc v) (fromN := 1) (toN := w) (hle := by omega)
    (hstep := fun i hi1 hiw => beStep_width w v i hv hwf hi1 hiw)
    (goal := .ok (embed (toBE w v)))
    (hafter := by
      dsimp [beAcc]
      rw [listLen_embed, leBytes_length, subI_ofNat_one w hw hwf, ok_bind]
      rw [fuelDown_eq (Int.ofNat (w - 1)) 0]
      have hdrop : (leBytes w v).drop w = [] := by
        have h := List.drop_length (leBytes w v)
        rwa [leBytes_length w v] at h
      rw [show (embed [] : Array Int) =
          embed ((leBytes w v).drop w).reverse by rw [hdrop]; rfl]
      rw [except_bind_pure]
      apply Eq.trans
      · apply runLoopOn_step_pointwise (step' := downCopyStep (embed (leBytes w v)))
        intro σ
        unfold downCopyStep
        rfl
      exact be_down_width w v hw hwf hbyte)

/-! ## Edge permutations whose Lehmer prefix is zero -/

/-- Length-30 lists whose first 28 entries are `0..27`.

    That is exactly `evenRank = 0`: the emitted loop reads only `n - 2`
    symbols, and a zero digit at each step picks the next identity symbol.
    The last pair is unread, so it may be swapped. -/
structure EdgeZero (ep : List Nat) : Prop where
  len : ep.length = 30
  pref : ep.take 28 = List.range 28

private theorem findIdx_head (x : Nat) (xs : List Nat) :
    (x :: xs).findIdx (· == x) = 0 := by
  simp [List.findIdx_cons]

private theorem range_drop_succ (k : Nat) (hk : k < 30) :
    (List.range 30).drop k = k :: (List.range 30).drop (k + 1) := by
  have hk' : k < (List.range 30).length := by simpa [List.length_range] using hk
  rw [List.drop_eq_getElem_cons hk']
  simp [List.getElem_range]

private theorem drop_range_len (k : Nat) :
    ((List.range 30).drop k).length = 30 - k := by
  simp [List.length_drop, List.length_range]

theorem edge_get (ep : List Nat) (h : EdgeZero ep) (k : Nat) (hk : k < 28) :
    ep[k]'(by rw [h.len]; omega) = k := by
  have hlen : k < (ep.take 28).length := by
    rw [List.length_take, h.len]
    omega
  have htake := List.getElem_take ep (j := 28) (i := k) (h := hlen)
  have hrng : (List.range 28)[k]'(by rw [List.length_range]; exact hk) = k :=
    List.getElem_range k (by rw [List.length_range]; exact hk)
  have hpref :
      (ep.take 28)[k]'(hlen) =
        (List.range 28)[k]'(by rw [List.length_range]; exact hk) := by
    simp [h.pref]
  rw [← htake, hpref, hrng]

theorem avail_edge (ep : List Nat) (h : EdgeZero ep) :
    ∀ k, k ≤ 28 → availAt ep k = (List.range 30).drop k := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [availAt, dropUsed, List.take_zero, h.len, List.drop_zero]
  | succ k ih =>
    intro hk
    have hk28 : k < 28 := by omega
    have hklen : k < ep.length := by rw [h.len]; omega
    rw [availAt_erase ep k hklen, ih (Nat.le_of_lt hk28)]
    have hget := edge_get ep h k hk28
    rw [range_drop_succ k (by omega), hget, findIdx_head]
    rfl

theorem evenDigits_edge (ep : List Nat) (h : EdgeZero ep) :
    evenDigits ep = List.replicate 28 0 := by
  have hlen : (evenDigits ep).length = 28 := by
    rw [evenDigits_length ep (by rw [h.len]; omega), h.len]
  apply List.ext_getElem
  · rw [hlen, List.length_replicate]
  · intro i hi1 hi2
    have hi28 : i < 28 := by rw [List.length_replicate] at hi2; exact hi2
    have hklen : i < ep.length := by rw [h.len]; omega
    have hdig := digit_eq_find ep i hklen
    have hidx :
        (evenDigits ep)[i]'(by rw [hlen]; exact hi28) =
          (lehmerDigits (List.range ep.length) ep)[i]'(by
            rw [lehmerDigits_length]; exact hklen) := by
      simp [evenDigits, List.getElem_take, hi28]
    have hi1' : i < (evenDigits ep).length := by rw [hlen]; exact hi28
    rw [show (evenDigits ep)[i] = (evenDigits ep)[i]'hi1' from rfl]
    rw [hidx, hdig, avail_edge ep h i (Nat.le_of_lt hi28), edge_get ep h i hi28,
      range_drop_succ i (by omega), findIdx_head, List.getElem_replicate]

private theorem mixEncode_replicate_zero : ∀ rs, mixEncode rs (List.replicate rs.length 0) = 0
  | [] => by simp [mixEncode, List.replicate]
  | r :: rs => by
    rw [List.length_cons, List.replicate_succ, mixEncode_cons, mixEncode_replicate_zero rs]
    simp

theorem evenRank_edge (ep : List Nat) (h : EdgeZero ep) : evenRank ep = 0 := by
  rw [evenRank_eq_acc ep (by rw [h.len]; omega)]
  have h28 : ep.length - 2 = 28 := by rw [h.len]
  rw [h28]
  unfold rankAcc
  rw [h.len, evenDigits_edge ep h]
  have htakeD : (List.replicate 28 0).take 28 = List.replicate 28 0 := by
    simp
  have hlenR : (evenRadices 30).length = 28 := evenRadices_length 30 (by decide)
  have htakeR : (evenRadices 30).take 28 = evenRadices 30 := by
    rw [← hlenR, List.take_length]
  rw [htakeD, htakeR, hornerZip_mix _ _ (by rw [hlenR, List.length_replicate])]
  rw [← hlenR]
  exact mixEncode_replicate_zero (evenRadices 30)

/-! ## `even_perm_rank_big` on that edge prefix -/

private theorem pure_eq_ok {α} (a : α) :
    (pure a : Except SudoRt.Trap α) = Except.ok a := rfl

private theorem zero_lt_limb : (0 : Nat) < limbBase := by decide

private theorem edgeRankStep (ep : List Nat) (h : EdgeZero ep) (i : Nat) (hi : i ≤ 27) :
    rankStep (embed ep) (Int.ofNat 30) (Int.ofNat 27)
        (Int.ofNat i, bigNat 0, embed ((List.range 30).drop i)) =
      if i = 27 then
        .ok (SudoRt.Flow.brk (Int.ofNat i,
          bigNat 0, embed ((List.range 30).drop (i + 1))))
      else
        .ok (SudoRt.Flow.cont (Int.ofNat (i + 1),
          bigNat 0, embed ((List.range 30).drop (i + 1)))) := by
  have hi30 : i < 30 := by omega
  have hi28 : i < 28 := by omega
  have hlenE : i < ep.length := by rw [h.len]; exact hi30
  have hget := edge_get ep h i hi28
  have hlenA : ((List.range 30).drop i).length = 30 - i := drop_range_len i
  have hmem : ep[i] ∈ (List.range 30).drop i := by
    rw [hget, range_drop_succ i hi30]
    exact List.mem_cons_self _ _
  have hidx0 : ((List.range 30).drop i).findIdx (· == ep[i]) = 0 := by
    rw [range_drop_succ i hi30, hget, findIdx_head]
  have hfitsA : FitsLen ((List.range 30).drop i).length := by
    rw [hlenA]
    exact FitsLen.of_le fits30 (by omega)
  unfold rankStep
  dsimp
  have hngt : ¬ (i : Int) > (27 : Int) := ofNat_not_gt hi
  rw [if_neg hngt, negI_one, ok_bind, listLen_embed, hlenA]
  have hposA : 0 < 30 - i := by omega
  have hsubA := subI_ofNat_one (30 - i) hposA (FitsLen.of_le fits30 (by omega))
  rw [hsubA, ok_bind]
  have hfun : findPerm (embed ((List.range 30).drop i)) (embed ep) (Int.ofNat i)
        (Int.ofNat (30 - i - 1)) =
      findStep (embed ((List.range 30).drop i)) (Int.ofNat (ep[i]))
        (Int.ofNat (30 - i - 1)) := by
    funext σ
    exact findPerm_eq _ ep i hlenE _ σ
  simp only [ofNat_eq_natCast] at hfun ⊢
  rw [hfun]
  rw [show (30 - i - 1) = ((List.range 30).drop i).length - 1 by rw [hlenA]]
  rw [fuelRange_eq, ← ofNat_eq_natCast (((List.range 30).drop i).length - 1)]
  rw [find_breaks ((List.range 30).drop i) (ep[i]) hmem hfitsA]
  dsimp [rankAfter]
  rw [hidx0]
  have hcast0 : (↑(0 : Nat) : Int) = 0 := rfl
  have hnn : decide ((0 : Int) ≥ 0) = true := by decide
  rw [hcast0, hnn, sudoAssert_true, ok_bind]
  have hsubN : SudoRt.subI (30 : Int) (↑i) = .ok (↑(30 - i)) := by
    rw [show (30 : Int) = Int.ofNat 30 from rfl]
    simpa [ofNat_eq_natCast] using subI_ofNat 30 i fits30 (by omega)
  rw [hsubN, ok_bind]
  have hradFit : FitsLen (30 - i) := FitsLen.of_le fits30 (by omega)
  rw [show (↑(30 - i) : Int) = Int.ofNat (30 - i) from rfl,
    big_from_int_refines (30 - i) hradFit, ok_bind]
  rw [show bigOf (limbsOfNat (30 - i)) = bigNat (30 - i) from rfl,
    bigNat_zero, big_mul_zero_left (bigNat (30 - i)), ok_bind]
  rw [show (0 : Int) = Int.ofNat 0 from rfl, big_from_int_refines 0 FitsLen.zero, ok_bind]
  rw [show bigOf (limbsOfNat 0) = bigNat 0 from rfl, ← bigNat_zero,
    big_add_small 0 0 zero_lt_limb zero_lt_limb zero_lt_limb, ok_bind]
  rw [Nat.zero_add, listLen_embed, hlenA]
  rw [subI_ofNat_one (30 - i) hposA (FitsLen.of_le fits30 (by omega)), ok_bind]
  have hidxL : 0 < ((List.range 30).drop i).length := by rw [hlenA]; omega
  rw [show (#[] : Array Int) =
      embed (takeSkip ((List.range 30).drop i) 0 0) by rw [takeSkip_zero, embed_nil]]
  rw [fuelRange_eq]
  rw [show (30 - i - 1) = ((List.range 30).drop i).length - 1 by rw [hlenA]]
  have hfuel0 :
      fuelRange (Int.ofNat 0)
          (Int.ofNat (((List.range 30).drop i).length - 1)) =
        fuelRange (0 : Int)
          (Int.ofNat (((List.range 30).drop i).length - 1)) := rfl
  have hstart :
      (Int.ofNat 0, embed (takeSkip ((List.range 30).drop i) 0 0)) =
        ((0 : Int), embed (takeSkip ((List.range 30).drop i) 0 0)) := rfl
  rw [hfuel0, hstart]
  rw [erase_breaks ((List.range 30).drop i) 0 hidxL hfitsA]
  have herase : ((List.range 30).drop i).eraseIdx 0 = (List.range 30).drop (i + 1) := by
    rw [range_drop_succ i hi30]
    rfl
  rw [herase, pure_eq_ok, ok_bind]
  by_cases heq : i = 27
  · simp [heq, beq_int_iff, pure_eq_ok]
  · have hneI : ¬ (i : Int) = (27 : Int) := fun hq => heq (Int.ofNat.inj hq)
    have haddI := addI_ofNat_one i (FitsLen.of_le fits30 (by omega))
    rw [ofNat_eq_natCast i] at haddI
    simp [beq_int_iff, hneI, haddI, pure_eq_ok, ok_bind, heq]

private theorem edgeRun (ep : List Nat) (h : EdgeZero ep) :
    SudoRt.runLoopOn (ρ := Megadreifach.BigInt)
      (Int.ofNat 0, (bigNat 0, embed ((List.range 30).drop 0)))
      (fuelRange (Int.ofNat 0) (Int.ofNat 27))
      (rankStep (embed ep) (Int.ofNat 30) (Int.ofNat 27))
      (fun σ => pure σ.2.1)
      (fun r => pure r) =
      .ok (bigNat 0) := by
  apply chain_loop
    (f := fun i => (bigNat 0, embed ((List.range 30).drop i)))
    (fromN := 0) (toN := 27) (hle := by decide)
    (goal := .ok (bigNat 0))
  · intro i _ hi
    simpa using edgeRankStep ep h i hi
  · rfl

/-- `even_perm_rank_big` is zero on an edge list whose Lehmer prefix is the identity. -/
theorem even_perm_rank_big_edge (ep : List Nat) (h : EdgeZero ep) :
    Megadreifach.even_perm_rank_big (embed ep) = .ok (bigNat 0) := by
  unfold Megadreifach.even_perm_rank_big
  rw [listLen_embed, h.len]
  dsimp
  rw [show (30 : Int) = Int.ofNat 30 from rfl]
  rw [range_list_refines 30 (by decide) fits30, ok_bind]
  rw [big_zero_spec, ok_bind]
  rw [show (3 : Int) = Int.ofNat 3 from rfl]
  rw [subI_ofNat 30 3 fits30 (by decide), ok_bind]
  dsimp
  have hfuel : fuelRange (Int.ofNat 0) (Int.ofNat 27) = 28 := by
    rw [fuelRange_le (by decide)]
  rw [← hfuel, except_bind_pure]
  apply Eq.trans
  · apply runLoopOn_step_pointwise
      (step' := rankStep (embed ep) (Int.ofNat 30) (Int.ofNat 27))
    intro σ
    unfold rankStep findPerm rankAfter eraseStep
    dsimp
    rfl
  · rw [show bigOf [] = bigNat 0 from bigNat_zero.symm]
    rw [show embed (List.range 30) = embed ((List.range 30).drop 0) by simp]
    exact edgeRun ep h

/-! ## Domain -/

/-- Trap-free slice of `position_to_bytes` inside the proved limb fragment.

    Corner permutation: `Rank20` shape and `evenRank = 0` (first 18 symbols
    are `0..17`). Corner orientations: `Ori3Wf` and `packOri3 = 0` (first 19
    digits are 0). Edge permutation: `EdgeZero` (`evenRank = 0`). Edge
    orientations: any `Ori2Wf`. The digest is the 29-byte encoding of
    `packOri2 eo`, which is `< 2^29`. -/
structure PosBytesWf (p : Position) : Prop where
  cp : Perm20Wf (listOf p.cp)
  cpZero : evenRank (listOf p.cp) = 0
  co : Ori3Wf (listOfOri p.co)
  coZero : packOri3 (listOfOri p.co) = 0
  ep : EdgeZero (listOf p.ep)
  eo : Ori2Wf (listOfOri p.eo)

structure BytesWf (g : Megadreifach.Position) : Prop where
  cp : WellFormedPerm20 g.sudo_8Position_2cp
  cpZero : evenRank (decode g.sudo_8Position_2cp) = 0
  co : WellFormedOri3 g.sudo_8Position_2co
  coZero : packOri3 (decode g.sudo_8Position_2co) = 0
  ep : EdgeZero (decode g.sudo_8Position_2ep)
  epNn : Nonneg g.sudo_8Position_2ep
  eo : WellFormedOri2 g.sudo_8Position_2eo

private theorem rank20_zero (perm : List Nat) (h : Perm20Wf perm) (hz : evenRank perm = 0) :
    Rank20Wf perm where
  base := h
  small := by
    rw [hz]
    unfold limbBase
    decide

theorem packOri2_lt (eo : List Nat) (h : Ori2Wf eo) : packOri2 eo < 2 ^ 29 := by
  rw [← oriAcc_pack2 eo (by rw [h.len]; omega)]
  exact oriAcc_lt eo h.bound 29 (by rw [h.len]; omega)

theorem packOri2_fits (eo : List Nat) (h : Ori2Wf eo) : FitsLen (packOri2 eo) :=
  FitsLen.of_le two_pow29_fits (Nat.le_of_lt (packOri2_lt eo h))

theorem packOri2_lt_limb (eo : List Nat) (h : Ori2Wf eo) : packOri2 eo < limbBase :=
  Nat.lt_trans (packOri2_lt eo h) two_pow29_lt_limbBase

theorem packOri2_lt_digest (eo : List Nat) (h : Ori2Wf eo) :
    packOri2 eo < 256 ^ digestLen :=
  Nat.lt_trans (packOri2_lt eo h) two_pow29_lt_be

theorem rankPosition_bytes (p : Position) (h : PosBytesWf p) :
    rankPosition p = packOri2 (listOfOri p.eo) := by
  unfold rankPosition rankLists rankRadices
  rw [h.cpZero, h.coZero, evenRank_edge (listOf p.ep) h.ep]
  simp [mixEncode, product]

theorem positionToBytes_bytes (p : Position) (h : PosBytesWf p) :
    positionToBytes p = toBE digestLen (packOri2 (listOfOri p.eo)) := by
  unfold positionToBytes
  rw [rankPosition_bytes p h]

/-! ## Glue -/

theorem position_to_bytes_lists (cp co ep eo : List Nat)
    (hcp : Perm20Wf cp) (hcp0 : evenRank cp = 0)
    (hco : Ori3Wf co) (hco0 : packOri3 co = 0)
    (hep : EdgeZero ep) (heo : Ori2Wf eo) :
    Megadreifach.position_to_bytes
        { sudo_8Position_2cp := embed cp
          sudo_8Position_2co := embed co
          sudo_8Position_2ep := embed ep
          sudo_8Position_2eo := embed eo } =
      .ok (embed (toBE digestLen (packOri2 eo))) := by
  have hcpR : Rank20Wf cp := rank20_zero cp hcp hcp0
  unfold Megadreifach.position_to_bytes
  rw [even_perm_rank_big_refines cp hcpR, hcp0, ok_bind]
  rw [ori3_span_eq, big_from_int_refines (3 ^ 19) three_pow19_fits, ok_bind]
  rw [show bigOf (limbsOfNat (3 ^ 19)) = bigNat (3 ^ 19) from rfl,
    bigNat_zero, big_mul_zero_left (bigNat (3 ^ 19)), ok_bind]
  rw [pack_ori3_refines co hco, hco0, ok_bind]
  rw [← bigNat_zero, big_add_small 0 0 zero_lt_limb zero_lt_limb zero_lt_limb, ok_bind]
  rw [Nat.zero_add, even30_refines, ok_bind]
  rw [bigNat_zero, big_mul_zero_left (bigOf even30Limbs), ok_bind]
  rw [even_perm_rank_big_edge ep hep, ok_bind]
  rw [← bigNat_zero, big_add_small 0 0 zero_lt_limb zero_lt_limb zero_lt_limb, ok_bind]
  rw [Nat.zero_add, ori2_span_eq, big_from_int_refines (2 ^ 29) two_pow29_fits, ok_bind]
  rw [show bigOf (limbsOfNat (2 ^ 29)) = bigNat (2 ^ 29) from rfl,
    bigNat_zero, big_mul_zero_left (bigNat (2 ^ 29)), ok_bind]
  rw [pack_ori2_refines eo heo, ok_bind]
  have hpackL : packOri2 eo < limbBase := packOri2_lt_limb eo heo
  have hsum : 0 + packOri2 eo < limbBase := by simpa using hpackL
  rw [← bigNat_zero, big_add_small 0 (packOri2 eo) zero_lt_limb hpackL hsum, ok_bind]
  rw [Nat.zero_add, digest_len_eq, except_bind_pure]
  exact big_to_be_width digestLen (packOri2 eo) (by decide : 0 < digestLen) fits29
    (packOri2_fits eo heo) (packOri2_lt_digest eo heo)

/-- `Generated.position_to_bytes` is algebraic `positionToBytes` on `PosBytesWf`. -/
theorem position_to_bytes_refines (p : Position) (h : PosBytesWf p) :
    Megadreifach.position_to_bytes (embedPos p) =
      .ok (embed (positionToBytes p)) := by
  have hlist := position_to_bytes_lists (listOf p.cp) (listOfOri p.co)
    (listOf p.ep) (listOfOri p.eo) h.cp h.cpZero h.co h.coZero h.ep h.eo
  rw [positionToBytes_bytes p h]
  simpa [embedPos] using hlist

theorem position_to_bytes_refines_array (g : Megadreifach.Position) (h : BytesWf g) :
    Megadreifach.position_to_bytes g =
      .ok (embed (toBE digestLen (packOri2 (decode g.sudo_8Position_2eo)))) := by
  cases g with
  | mk cp co ep eo =>
    have hcp := embed_decode cp h.cp.nn
    have hco := embed_decode co h.co.nn
    have hep := embed_decode ep h.epNn
    have heo := embed_decode eo h.eo.nn
    have hg : Megadreifach.position_to_bytes ⟨cp, co, ep, eo⟩ =
        Megadreifach.position_to_bytes
          ⟨embed (decode cp), embed (decode co), embed (decode ep), embed (decode eo)⟩ := by
      simp [hcp, hco, hep, heo]
    rw [hg]
    exact position_to_bytes_lists (decode cp) (decode co) (decode ep) (decode eo)
      (perm20_decode cp h.cp) h.cpZero (ori3Wf_decode co h.co) h.coZero h.ep
      (ori2Wf_decode eo h.eo)

end MegaDreifach.Link2
