/-
  A cube or a multiply with the script marker on is the marker-off run on the
  board `marker_step` would leave, with the marker flag put back.
  The arithmetic stays `cube_off_eq` / `lane_fold_refines` / `comb_loop_refines`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.Cube
import EcbsLink2.Link2.Marker

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

/-- Board fed to the marker-off cube after `marker_lift`: marker seated at 0. -/
def markerDownFeed (b : Ecbs.Board) (ctrl mx : Nat) : Ecbs.Board :=
  { b with
    sudo_5Board_9marker_on := false
    sudo_5Board_6marker := 0
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1)
      sudo_5Costs_17script_marker_max := Int.ofNat (max mx 1) } }

/-- Board fed to the marker-off cube when the marker is already seated at `m`. -/
def markerUpFeed (b : Ecbs.Board) (m ctrl mx : Nat) : Ecbs.Board :=
  { b with
    sudo_5Board_9marker_on := false
    sudo_5Board_6marker := Int.ofNat (m + 1)
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2)
      sudo_5Costs_17script_marker_max := Int.ofNat (max mx (m + 2)) } }

theorem clear_flag (b : Ecbs.Board) (h : b.sudo_5Board_9marker_on = false) :
    { { b with sudo_5Board_9marker_on := true } with sudo_5Board_9marker_on := false } = b := by
  apply board_ext
  case hmon => exact h.symm
  all_goals rfl

theorem withMoves_flag (b : Ecbs.Board) (m : Int) :
    withMoves { b with sudo_5Board_9marker_on := true } m =
      { withMoves b m with sudo_5Board_9marker_on := true } := by
  unfold withMoves
  rfl

theorem noteBench_held (b : Ecbs.Board) (top mv : Int) :
    (noteBench b top mv).sudo_5Board_4held = b.sudo_5Board_4held := by
  unfold noteBench withMoves withHole
  split <;> rfl

theorem noteBench_home (b : Ecbs.Board) (top mv : Int) :
    (noteBench b top mv).sudo_5Board_4home = b.sudo_5Board_4home := by
  unfold noteBench withMoves withHole
  split <;> rfl

theorem noteBench_peak (b : Ecbs.Board) (top mv : Int) :
    (noteBench b top mv).sudo_5Board_4cost.sudo_5Costs_4peak =
      b.sudo_5Board_4cost.sudo_5Costs_4peak := by
  unfold noteBench withMoves withHole
  split <;> rfl

theorem noteBench_moves (b : Ecbs.Board) (top mv : Int) :
    (noteBench b top mv).sudo_5Board_4cost.sudo_5Costs_5moves = mv := by
  unfold noteBench withMoves withHole
  split <;> rfl

theorem noteBench_tier (b : Ecbs.Board) (top mv : Int) :
    (noteBench b top mv).sudo_5Board_1t = b.sudo_5Board_1t := by
  unfold noteBench withMoves withHole
  split <;> rfl

theorem noteBench_hole (b : Ecbs.Board) (top mv : Int) :
    (noteBench b top mv).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
      (if decide (top > b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) then top
        else b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole) := by
  unfold noteBench withMoves withHole
  split <;> rfl

theorem noteBench_flag (b : Ecbs.Board) (top mv : Int) (h : b.sudo_5Board_9marker_on = true) :
    noteBench b top mv =
      { noteBench { b with sudo_5Board_9marker_on := false } top mv with
          sudo_5Board_9marker_on := true } := by
  unfold noteBench withMoves withHole
  have hh :
      ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole := rfl
  rw [hh]
  split <;> apply board_ext <;> (first | exact h | rfl)

theorem strictBoard_flag (b : Ecbs.Board) (peakS : Nat) :
    strictBoard { b with sudo_5Board_9marker_on := true } peakS =
      { strictBoard b peakS with sudo_5Board_9marker_on := true } := by
  unfold strictBoard
  rfl

theorem peakBoard_flag (b : Ecbs.Board) (peak : Nat) (h : b.sudo_5Board_9marker_on = true) :
    peakBoard b peak =
      { peakBoard { b with sudo_5Board_9marker_on := false } peak with
          sudo_5Board_9marker_on := true } := by
  unfold peakBoard
  apply board_ext
  case hcost =>
    apply cost_ext <;> rfl
  case hmon => exact h
  all_goals rfl

/-- `note_strict` does not read the marker flag. -/
theorem note_strict_flag (b : Ecbs.Board) (peakS : Nat)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int)) :
    Ecbs.note_strict b =
      (do
        let r ← Ecbs.note_strict { b with sudo_5Board_9marker_on := false }
        pure { r with sudo_5Board_9marker_on := b.sudo_5Board_9marker_on }) := by
  have h7' : 7 ≤ ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_4held.size := by
    simpa using h7
  have hp' :
      ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_4cost.sudo_5Costs_11peak_strict =
        (peakS : Int) := by
    simpa using hp
  rw [note_strict_eq b peakS h7 hp, note_strict_eq _ peakS h7' hp', ok_bind, pure_eq_ok]
  simp [strictBoard]

theorem note_peak_flag (b : Ecbs.Board) (peak : Nat)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (h : b.sudo_5Board_9marker_on = true) :
    Ecbs.note_peak b =
      (do
        let r ← Ecbs.note_peak { b with sudo_5Board_9marker_on := false }
        pure { r with sudo_5Board_9marker_on := true }) := by
  have h7' : 7 ≤ ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_4held.size := by
    simpa using h7
  have hp' :
      ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_4cost.sudo_5Costs_4peak =
        (peak : Int) := by
    simpa using hp
  rw [note_peak_eq b peak h7 hp, note_peak_eq _ peak h7' hp', ok_bind, pure_eq_ok]
  exact congrArg Except.ok (peakBoard_flag b peak h)

/-- The op-count bump and the marker frame touch different fields. -/
theorem down_bump (b : Ecbs.Board) (ctrl mx cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hmk : b.sudo_5Board_9marker_on = true) :
    { bumpOp (markerDownFeed b ctrl mx) 1 cOps (by simpa [markerDownFeed] using hops) with
        sudo_5Board_9marker_on := true } =
      { bumpOp b 1 cOps hops with
        sudo_5Board_6marker := 0
        sudo_5Board_4cost := { (bumpOp b 1 cOps hops).sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 1)
          sudo_5Costs_17script_marker_max := Int.ofNat (max mx 1) } } := by
  unfold bumpOp markerDownFeed
  simp [hmk]

theorem up_bump (b : Ecbs.Board) (m ctrl mx cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hmk : b.sudo_5Board_9marker_on = true) :
    { bumpOp (markerUpFeed b m ctrl mx) 1 cOps (by simpa [markerUpFeed] using hops) with
        sudo_5Board_9marker_on := true } =
      { bumpOp b 1 cOps hops with
        sudo_5Board_6marker := Int.ofNat (m + 1)
        sudo_5Board_4cost := { (bumpOp b 1 cOps hops).sudo_5Board_4cost with
          sudo_5Costs_4ctrl := Int.ofNat (ctrl + 2)
          sudo_5Costs_17script_marker_max := Int.ofNat (max mx (m + 2)) } } := by
  unfold bumpOp markerUpFeed
  simp [hmk]

/-- `Ecbs.cube` from `note_strict` through the comb, as `combStep` and `combAfter`. -/
def cubeTail (b : Ecbs.Board) (dst src : Int) : Except SudoRt.Trap Ecbs.Board :=
  do
    let b ← Ecbs.note_strict b
    let held ← SudoRt.atL b.sudo_5Board_4held src
    SudoRt.sudoAssert held 605
    let v ← SudoRt.atL b.sudo_5Board_4home src
    let heldA ← SudoRt.putL b.sudo_5Board_4held src false
    let b := { b with sudo_5Board_4held := heldA }
    let homeA ← SudoRt.putL b.sudo_5Board_4home src (#[] : Array Int)
    let b := { b with sudo_5Board_4home := homeA }
    let strip ← SudoRt.filledL b.sudo_5Board_1t.sudo_4Tier_8benchlen (0 : Int)
    let toV ← SudoRt.subI b.sudo_5Board_1t.sudo_4Tier_1n (1 : Int)
    let fromV : Int := 0
    let fuel : Nat := if fromV > toV then 1 else (toV - fromV).natAbs + 1
    let out ← SudoRt.runLoopOn (ρ := Ecbs.Board) (fromV, (strip, b)) fuel
      (combStep v toV) (combAfter dst) (fun r => pure r)
    pure out

/-- Home cleared, `peak_strict` noted, marker flag left as it stood. -/
def cubeClear (b : Ecbs.Board) (src : Nat) (peakS : Nat)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size) : Ecbs.Board :=
  { strictBoard b peakS with
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨src, hF⟩ false
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨src, hHome⟩ #[] }

theorem cubeClear_flag (b : Ecbs.Board) (src peakS : Nat)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hF' : src < ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_4held.size)
    (hHome' : src < ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_4home.size) :
    cubeClear { b with sudo_5Board_9marker_on := true } src peakS hF' hHome' =
      { cubeClear b src peakS hF hHome with sudo_5Board_9marker_on := true } := by
  unfold cubeClear strictBoard
  apply board_ext
  case hheld =>
    have hfin : (⟨src, hF'⟩ : Fin _) = ⟨src, hF⟩ := Fin.ext rfl
    simp [hfin]
  case hhome =>
    have hfin : (⟨src, hHome'⟩ : Fin _) = ⟨src, hHome⟩ := Fin.ext rfl
    simp [hfin]
  all_goals rfl

/-- `lane_fold` does not read the marker flag. The arithmetic is `lane_fold_refines`. -/
theorem lane_fold_flag (xs : List Nat) (w h r n k moves hole benchlen : Nat) (b : Ecbs.Board)
    (hflag : b.sudo_5Board_9marker_on = true)
    (hfit : FitsLen xs.length)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat benchlen)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hs : allTritList xs)
    (hm : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ xs.length ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfm : FitsLen (moves + 3 * (xs.length - n)))
    (hlen : xs.length ≤ benchlen) (hpos : 0 < benchlen) :
    Ecbs.lane_fold b (embed xs) =
      (do
        let p ← Ecbs.lane_fold { b with sudo_5Board_9marker_on := false } (embed xs)
        pure ({ p.1 with sudo_5Board_9marker_on := true }, p.2)) := by
  have hw' :
      ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simpa using hw
  have hh' :
      ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simpa using hh
  have hr' :
      ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simpa using hr
  have hn' :
      ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by
    simpa using hn
  have hk' :
      ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simpa using hk
  have hbl' :
      ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_1t.sudo_4Tier_8benchlen =
        Int.ofNat benchlen := by
    simpa using hbl
  have hm' :
      ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_4cost.sudo_5Costs_5moves =
        Int.ofNat moves := by
    simpa using hm
  have hhole' :
      ({ b with sudo_5Board_9marker_on := false }).sudo_5Board_4cost.sudo_5Costs_14max_bench_hole =
        Int.ofNat hole := by
    simpa using hhole
  rw [lane_fold_eq xs w h r n k benchlen b hfit hw hh hr hn hk hbl]
  rw [lane_fold_eq xs w h r n k benchlen { b with sudo_5Board_9marker_on := false }
      hfit hw' hh' hr' hn' hk' hbl']
  rw [lane_fold_refines xs w h r n k moves hole benchlen b
      hw0 hh0 hrR hrP hnE hkLe hgap hs hm hhole hsm hnsm hfm hfit hlen hpos]
  rw [lane_fold_refines xs w h r n k moves hole benchlen
      { b with sudo_5Board_9marker_on := false }
      hw0 hh0 hrR hrP hnE hkLe hgap hs hm' hhole' hsm hnsm hfm hfit hlen hpos]
  simp only [ok_bind, pure_eq_ok]
  apply congrArg Except.ok
  refine Prod.ext ?_ rfl
  exact noteBench_flag b (Int.ofNat (topIdx xs))
    (Int.ofNat (moves + foldCharge n (n - k) xs)) hflag

/-- The comb-gap check, the lane fold, and `note_peak` do not read the marker flag. -/
theorem combAfter_flag (dst : Int) (b : Ecbs.Board) (sch : List Nat)
    (w h r n k mv hole bench peak cg : Nat)
    (hflag : b.sudo_5Board_9marker_on = false)
    (hn0 : 0 < n) (hf : FitsLen n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hmov : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv)
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hlenS : sch.length = bench)
    (htri : allTritList sch)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (mv + 3 * (sch.length - n))) :
    combAfter dst (Int.ofNat (n - 1), (embed sch, { b with sudo_5Board_9marker_on := true })) =
      (do
        let r ← combAfter dst (Int.ofNat (n - 1), (embed sch, b))
        pure { r with sudo_5Board_9marker_on := true }) := by
  have hOn : ({ b with sudo_5Board_9marker_on := true }).sudo_5Board_9marker_on = true := rfl
  unfold combAfter
  dsimp only
  conv =>
    lhs
    pattern (SudoRt.subI _ _)
    rw [hn, ← ofNat_eq_natCast n, subI_ofNat_one n hn0 hf]
  conv =>
    rhs
    pattern (SudoRt.subI _ _)
    rw [hn, ← ofNat_eq_natCast n, subI_ofNat_one n hn0 hf]
  simp only [ok_bind]
  conv =>
    lhs
    pattern (SudoRt.mulI _ _)
    rw [show (3 : Int) = Int.ofNat 3 from rfl, mulI_ofNat 3 (n - 1) h3]
  conv =>
    rhs
    pattern (SudoRt.mulI _ _)
    rw [show (3 : Int) = Int.ofNat 3 from rfl, mulI_ofNat 3 (n - 1) h3]
  simp only [ok_bind]
  have hfitSum : FitsLen (3 * (n - 1) + cg) := FitsLen.of_le hfitB (Nat.le_of_lt hspan)
  conv =>
    lhs
    pattern (SudoRt.addI _ _)
    rw [hcg, addI_ofNat (3 * (n - 1)) cg hfitSum]
  conv =>
    rhs
    pattern (SudoRt.addI _ _)
    rw [hcg, addI_ofNat (3 * (n - 1)) cg hfitSum]
  simp only [ok_bind]
  have hdec : decide (Int.ofNat (3 * (n - 1) + cg) < Int.ofNat bench) = true :=
    decide_eq_true ((ofNat_lt_iff _ _).mpr hspan)
  conv =>
    lhs
    rw [hbl, hdec, sudoAssert_true]
  conv =>
    rhs
    rw [hbl, hdec, sudoAssert_true]
  simp only [ok_bind]
  have hpos : 0 < bench := by omega
  have hsmS : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ sch.length ≤ 1000001 := by
    rw [hlenS]; exact hsm
  have hlen : sch.length ≤ bench := by rw [hlenS]; exact Nat.le_refl _
  have hnI : b.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by rw [hn, ofNat_eq_natCast]
  let bOn := { { b with sudo_5Board_9marker_on := true } with
    sudo_5Board_8bench_on := true
    sudo_5Board_8bench_to := dst }
  let bOff := { b with
    sudo_5Board_8bench_on := true
    sudo_5Board_8bench_to := dst }
  have hAim : bOn = { bOff with sudo_5Board_9marker_on := true } := by
    simp [bOn, bOff, hflag]
  conv =>
    lhs
    pattern (Ecbs.lane_fold _ _)
    change Ecbs.lane_fold bOn (embed sch)
  conv =>
    rhs
    pattern (Ecbs.lane_fold _ _)
    change Ecbs.lane_fold bOff (embed sch)
  have hwB : bOff.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by simp [bOff, hw]
  have hhB : bOff.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by simp [bOff, hh]
  have hrB : bOff.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by simp [bOff, hr]
  have hnB : bOff.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by simp [bOff, hnI]
  have hkB : bOff.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by simp [bOff, hk]
  have hblB : bOff.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by simp [bOff, hbl]
  have hmB : bOff.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by simp [bOff, hmov]
  have hholeB : bOff.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bOff, hhole]
  have hflagB : bOn.sudo_5Board_9marker_on = true := by simp [bOn]
  have hwO : bOn.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by simp [bOn, hw]
  have hhO : bOn.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by simp [bOn, hh]
  have hrO : bOn.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by simp [bOn, hr]
  have hnO : bOn.sudo_5Board_1t.sudo_4Tier_1n = Int.ofNat n := by simp [bOn, hnI]
  have hkO : bOn.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by simp [bOn, hk]
  have hblO : bOn.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by simp [bOn, hbl]
  have hmO : bOn.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv := by simp [bOn, hmov]
  have hholeO : bOn.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bOn, hhole]
  have hfit : FitsLen sch.length := by simpa [hlenS] using hfitB
  rw [lane_fold_eq sch w h r n k bench bOn hfit hwO hhO hrO hnO hkO hblO]
  rw [lane_fold_eq sch w h r n k bench bOff hfit hwB hhB hrB hnB hkB hblB]
  rw [lane_fold_refines sch w h r n k mv hole bench bOn
      hw0 hh0 hrR hrP hnE hkLe hgap htri hmO hholeO hsmS hnsm hfold hfit hlen hpos]
  rw [lane_fold_refines sch w h r n k mv hole bench bOff
      hw0 hh0 hrR hrP hnE hkLe hgap htri hmB hholeB hsmS hnsm hfold hfit hlen hpos]
  simp only [ok_bind, pure_eq_ok, Prod.fst, Prod.snd]
  let top := Int.ofNat (topIdx sch)
  let mvF := Int.ofNat (mv + foldCharge n (n - k) sch)
  let folded := embed (laneFold n (n - k) sch)
  have hnb : noteBench bOn top mvF =
      { noteBench bOff top mvF with sudo_5Board_9marker_on := true } := by
    rw [hAim, noteBench_flag { bOff with sudo_5Board_9marker_on := true } top mvF rfl]
    rw [clear_flag bOff (by simp [bOff, hflag])]
  let nOn := { noteBench bOn top mvF with sudo_5Board_5bench := folded }
  let nOff := { noteBench bOff top mvF with sudo_5Board_5bench := folded }
  have hnN : nOn = { nOff with sudo_5Board_9marker_on := true } := by
    simp [nOn, nOff, hnb]
  have h7N : 7 ≤ nOn.sudo_5Board_4held.size := by
    simp only [nOn, noteBench_held, bOn]
    simpa using h7
  have hpN : nOn.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simpa [nOn, noteBench_peak, bOn] using hpeak
  have h7F : 7 ≤ nOff.sudo_5Board_4held.size := by
    simp only [nOff, noteBench_held, bOff]
    simpa using h7
  have hpF : nOff.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simpa [nOff, noteBench_peak, bOff] using hpeak
  conv =>
    lhs
    pattern (Ecbs.note_peak _)
    change Ecbs.note_peak nOn
  conv =>
    rhs
    pattern (Ecbs.note_peak _)
    change Ecbs.note_peak nOff
  rw [note_peak_eq nOn peak h7N hpN, note_peak_eq nOff peak h7F hpF]
  simp only [ok_bind, pure_eq_ok]
  have hoffN : nOff.sudo_5Board_9marker_on = false := by
    simp only [nOff, bOff, hflag]
    unfold noteBench withMoves withHole
    split <;> rfl
  rw [hnN, peakBoard_flag { nOff with sudo_5Board_9marker_on := true } peak rfl]
  rw [clear_flag nOff hoffN]

private theorem bind_ok_id {α : Type} (m : Except SudoRt.Trap α) :
    (do let r ← m; Except.ok r) = m := by
  cases m <;> rfl

/-- From `note_strict` to the end of the comb. The lane fold stays inside `combAfter`. -/
theorem cube_tail_eq (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (n moves bench peakS : Nat)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hspan3 : 3 * (n - 1) < bench) :
    cubeTail b ((dst : Nat) : Int) ((src : Nat) : Int) =
      combAfter ((dst : Nat) : Int) (Int.ofNat (n - 1),
        (embed (combStrip n bench xs),
          withMoves (cubeClear b src peakS hF hHome)
            (Int.ofNat (moves + 2 * laidCount xs n)))) := by
  unfold cubeTail
  rw [note_strict_eq b peakS h7 hp]
  simp only [ok_bind, pure_eq_ok]
  let bS := strictBoard b peakS
  have hheldS : bS.sudo_5Board_4held = b.sudo_5Board_4held := rfl
  have hhomeS : bS.sudo_5Board_4home = b.sudo_5Board_4home := rfl
  have htS : bS.sudo_5Board_1t = b.sudo_5Board_1t := rfl
  rw [hheldS, ← ofNat_eq_natCast src, atL_ofNat _ src hF, hHF]
  simp only [sudoAssert_true, ok_bind]
  rw [hhomeS, atL_ofNat _ src hHome, hArr, ok_bind]
  rw [putL_ofNat _ src false hF, ok_bind]
  rw [putL_ofNat _ src (#[] : Array Int) hHome, ok_bind]
  conv =>
    pattern (SudoRt.filledL _ _)
    rw [htS, hbl, filledL_ofNat]
  rw [ok_bind, ← embed_replicate_zero]
  conv =>
    pattern (SudoRt.subI _ _)
    rw [htS, hn, ← ofNat_eq_natCast n, subI_ofNat_one n hn0 hf]
  rw [ok_bind]
  have hfuel :
      (if (0 : Int) > Int.ofNat (n - 1) then 1
        else (Int.ofNat (n - 1) - (0 : Int)).natAbs + 1) =
        fuelRange (Int.ofNat 0) (Int.ofNat (n - 1)) := by
    rw [show (0 : Int) = Int.ofNat 0 from rfl]
    rfl
  rw [hfuel]
  let bC := cubeClear b src peakS hF hHome
  conv =>
    pattern ((0 : Int), _)
    change (Int.ofNat 0, (embed (List.replicate bench 0), bC))
  have hmC : bC.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves := by
    simpa [bC, cubeClear, strictBoard, ofNat_eq_natCast] using hmoves
  rw [comb_loop_refines xs moves bench n bC _ _ hn0
      (by rw [hlenx]; exact Nat.le_refl _) hspan3 hmC hf h3 hfm]
  rw [bind_ok_id]

/-- The op bump, then `log_op`, `settle`, and `cubeTail`. -/
theorem cube_open (b : Ecbs.Board) (dst src : Int) (cOps : Nat)
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1)) :
    Ecbs.cube b dst src =
      (do
        let b ← Ecbs.log_op (bumpOp b 1 cOps hops)
        let b ← Ecbs.settle b
        cubeTail b dst src) := by
  unfold Ecbs.cube
  dsimp
  rw [show Ecbs.op_cube = Int.ofNat 1 from rfl, atL_ofNat _ 1 hops, hop1, ok_bind,
    ← ofNat_eq_natCast cOps, addI_ofNat_one cOps hfops, ok_bind,
    putL_ofNat _ 1 (Int.ofNat (cOps + 1)) hops, ok_bind]
  dsimp
  conv =>
    lhs
    pattern (Ecbs.log_op _)
    change Ecbs.log_op (bumpOp b 1 cOps hops)
  unfold cubeTail
  rfl

/-- `cubeTail` does not read the marker flag. Both sides are `comb_loop_refines`
    and then `combAfter_flag`. -/
theorem cube_tail_flag (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves hole bench peak peakS cg : Nat)
    (hflag : b.sudo_5Board_9marker_on = false)
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList xs)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n))) :
    cubeTail { b with sudo_5Board_9marker_on := true } ((dst : Nat) : Int) ((src : Nat) : Int) =
      (do
        let r ← cubeTail b ((dst : Nat) : Int) ((src : Nat) : Int)
        pure { r with sudo_5Board_9marker_on := true }) := by
  have hspan3 : 3 * (n - 1) < bench := by omega
  let bOn := { b with sudo_5Board_9marker_on := true }
  have hF' : src < bOn.sudo_5Board_4held.size := hF
  have hHome' : src < bOn.sudo_5Board_4home.size := hHome
  have hHF' : bOn.sudo_5Board_4held[src] = true := hHF
  have hArr' : bOn.sudo_5Board_4home[src] = embed xs := hArr
  have h7' : 7 ≤ bOn.sudo_5Board_4held.size := h7
  have hp' : bOn.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := hp
  have hn' : bOn.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := hn
  have hmoves' : bOn.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := hmoves
  have hbl' : bOn.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := hbl
  rw [cube_tail_eq bOn dst src xs n moves bench peakS
      hF' hHome' hHF' hArr' h7' hp' hn0 hn' hlenx hf hmoves' hbl' h3 hfm hspan3]
  rw [cube_tail_eq b dst src xs n moves bench peakS
      hF hHome hHF hArr h7 hp hn0 hn hlenx hf hmoves hbl h3 hfm hspan3]
  rw [cubeClear_flag b src peakS hF hHome hF' hHome', withMoves_flag]
  let mvN := moves + 2 * laidCount xs n
  let bW := withMoves (cubeClear b src peakS hF hHome) (Int.ofNat mvN)
  have hflagW : bW.sudo_5Board_9marker_on = false := by
    simp [bW, withMoves, cubeClear, strictBoard, hflag]
  have hnW : bW.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simp [bW, withMoves, cubeClear, strictBoard, hn]
  have hcgW : bW.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
    simp [bW, withMoves, cubeClear, strictBoard, hcg]
  have hblW : bW.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simp [bW, withMoves, cubeClear, strictBoard, hbl]
  have hmovW : bW.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mvN := by
    simp [bW, withMoves]
  have hholeW : bW.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simp [bW, withMoves, cubeClear, strictBoard, hhole]
  have hpeakW : bW.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simp [bW, withMoves, cubeClear, strictBoard, hpeak]
  have h7W : 7 ≤ bW.sudo_5Board_4held.size := by
    simp [bW, withMoves, cubeClear, strictBoard, Array.size_set, h7]
  have hlenS : (combStrip n bench xs).length = bench := combStrip_length n bench xs
  have htri : allTritList (combStrip n bench xs) := combStrip_trits xs n bench hxsT hspan3
  have hwW : bW.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simp [bW, withMoves, cubeClear, strictBoard, hw]
  have hhW : bW.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simp [bW, withMoves, cubeClear, strictBoard, hh]
  have hrW : bW.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simp [bW, withMoves, cubeClear, strictBoard, hr]
  have hkW : bW.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simp [bW, withMoves, cubeClear, strictBoard, hk]
  have hfitF : FitsLen (mvN + 3 * ((combStrip n bench xs).length - n)) := by
    have hlaid := laidCount_le xs n
    rw [combStrip_length]
    exact FitsLen.of_le hfold (by omega)
  exact combAfter_flag ((dst : Nat) : Int) bW (combStrip n bench xs)
    w h r n k mvN hole bench peak cg hflagW hn0 hf hnW hcgW hblW hspan h3 hmovW hholeW
    hpeakW h7W hlenS htri hw0 hh0 hrR hrP hnE hkLe hgap hwW hhW hrW hkW hsm hnsm hfitB hfitF

theorem bumpOp_irrel (b : Ecbs.Board) (i cOps : Nat)
    (h₁ h₂ : i < b.sudo_5Board_4cost.sudo_5Costs_3ops.size) :
    bumpOp b i cOps h₁ = bumpOp b i cOps h₂ := by
  unfold bumpOp
  have hfin : (⟨i, h₁⟩ : Fin _) = ⟨i, h₂⟩ := Fin.ext rfl
  simp [hfin]

/-- `cube` with the marker on, after the marker has been lifted (`marker < 0`),
    is `cube` on `markerDownFeed` with the flag put back. -/
theorem cube_down_comm (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves hole bench peak peakS cOps cg ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfit : FitsLen (ctrl + 1))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList xs)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n))) :
    Ecbs.cube b ((dst : Nat) : Int) ((src : Nat) : Int) =
      (do
        let r ← Ecbs.cube (markerDownFeed b ctrl mx) ((dst : Nat) : Int) ((src : Nat) : Int)
        pure { r with sudo_5Board_9marker_on := true }) := by
  let feed := markerDownFeed b ctrl mx
  have hopsF : 1 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerDownFeed] using hops
  have hop1F : feed.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hopsF) = (cOps : Int) := by
    simpa [feed, markerDownFeed] using hop1
  rw [cube_open b ((dst : Nat) : Int) ((src : Nat) : Int) cOps hops hop1 hfops]
  rw [cube_open feed ((dst : Nat) : Int) ((src : Nat) : Int) cOps hopsF hop1F hfops]
  have hmkB : (bumpOp b 1 cOps hops).sudo_5Board_9marker_on = true := by simp [bumpOp, hmk]
  rw [log_op_on _ hmkB]
  have hmB : (bumpOp b 1 cOps hops).sudo_5Board_6marker < 0 := by simpa [bumpOp] using hm
  have hcB : (bumpOp b 1 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simpa [bumpOp] using hc
  have hxB : (bumpOp b 1 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx := by simpa [bumpOp] using hx
  have hsB : (bumpOp b 1 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simpa [bumpOp] using hs
  rw [marker_step_down (bumpOp b 1 cOps hops) ctrl mx script hmB hcB hxB hsB hpos hfit]
  rw [← down_bump b ctrl mx cOps hops hmk]
  simp only [ok_bind]
  let bF := bumpOp feed 1 cOps hopsF
  have hsame : bumpOp feed 1 cOps (by simpa [markerDownFeed] using hops) = bF := by
    simpa [bF] using (bumpOp_irrel feed 1 cOps (by simpa [markerDownFeed] using hops) hopsF)
  rw [hsame]
  have hfeedB : bF.sudo_5Board_9marker_on = false := by simp [bF, bumpOp, feed, markerDownFeed]
  rw [log_op_off _ hfeedB]
  simp only [ok_bind]
  have hoffF : bF.sudo_5Board_8bench_on = false := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hoff
  have hoffO : ({ bF with sudo_5Board_9marker_on := true }).sudo_5Board_8bench_on = false := by
    simp [hoffF]
  conv =>
    lhs
    pattern (Ecbs.settle _)
    rw [settle_off _ hoffO]
  conv =>
    rhs
    pattern (Ecbs.settle _)
    rw [settle_off _ hoffF]
  simp only [ok_bind]
  have hFT : src < bF.sudo_5Board_4held.size := by simpa [bF, bumpOp, feed, markerDownFeed] using hF
  have hHomeT : src < bF.sudo_5Board_4home.size := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hHome
  have hHFT : bF.sudo_5Board_4held[src] = true := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hHF
  have hArrT : bF.sudo_5Board_4home[src] = embed xs := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hArr
  have h7T : 7 ≤ bF.sudo_5Board_4held.size := by
    simpa [bF, bumpOp, feed, markerDownFeed] using h7
  have hpT : bF.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hp
  have hpeakT : bF.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hpeak
  have hnT : bF.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hn
  have hmovesT : bF.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hmoves
  have hblT : bF.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hbl
  have hcgT : bF.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hcg
  have hholeT : bF.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hhole
  have hwT : bF.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hw
  have hhT : bF.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hh
  have hrT : bF.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hr
  have hkT : bF.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simpa [bF, bumpOp, feed, markerDownFeed] using hk
  exact cube_tail_flag bF dst src xs w h r n k moves hole bench peak peakS cg
    hfeedB hFT hHomeT hHFT hArrT h7T hpT hpeakT hn0 hnT hlenx hf hmovesT hblT hcgT hspan h3 hfm
    hholeT hxsT hw0 hh0 hrR hrP hnE hkLe hgap hwT hhT hrT hkT hsm hnsm hfitB hfold

/-- `cube` with the marker on, when the marker is already seated at `m`,
    is `cube` on `markerUpFeed` with the flag put back. -/
theorem cube_up_comm (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves hole bench peak peakS cOps cg m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList xs)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n))) :
    Ecbs.cube b ((dst : Nat) : Int) ((src : Nat) : Int) =
      (do
        let r ← Ecbs.cube (markerUpFeed b m ctrl mx) ((dst : Nat) : Int) ((src : Nat) : Int)
        pure { r with sudo_5Board_9marker_on := true }) := by
  let feed := markerUpFeed b m ctrl mx
  have hopsF : 1 < feed.sudo_5Board_4cost.sudo_5Costs_3ops.size := by
    simpa [feed, markerUpFeed] using hops
  have hop1F : feed.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hopsF) = (cOps : Int) := by
    simpa [feed, markerUpFeed] using hop1
  rw [cube_open b ((dst : Nat) : Int) ((src : Nat) : Int) cOps hops hop1 hfops]
  rw [cube_open feed ((dst : Nat) : Int) ((src : Nat) : Int) cOps hopsF hop1F hfops]
  have hmkB : (bumpOp b 1 cOps hops).sudo_5Board_9marker_on = true := by simp [bumpOp, hmk]
  rw [log_op_on _ hmkB]
  have hmB : (bumpOp b 1 cOps hops).sudo_5Board_6marker = Int.ofNat m := by simpa [bumpOp] using hm
  have hcB : (bumpOp b 1 cOps hops).sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl := by
    simpa [bumpOp] using hc
  have hxB : (bumpOp b 1 cOps hops).sudo_5Board_4cost.sudo_5Costs_17script_marker_max =
      Int.ofNat mx := by simpa [bumpOp] using hx
  have hsB : (bumpOp b 1 cOps hops).sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script := by
    simpa [bumpOp] using hs
  rw [marker_step_up (bumpOp b 1 cOps hops) m ctrl mx script hmB hcB hxB hsB hbound hfitM hfitC hfit2]
  rw [← up_bump b m ctrl mx cOps hops hmk]
  simp only [ok_bind]
  let bF := bumpOp feed 1 cOps hopsF
  have hsame : bumpOp feed 1 cOps (by simpa [markerUpFeed] using hops) = bF := by
    simpa [bF] using (bumpOp_irrel feed 1 cOps (by simpa [markerUpFeed] using hops) hopsF)
  rw [hsame]
  have hfeedB : bF.sudo_5Board_9marker_on = false := by simp [bF, bumpOp, feed, markerUpFeed]
  rw [log_op_off _ hfeedB]
  simp only [ok_bind]
  have hoffF : bF.sudo_5Board_8bench_on = false := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hoff
  have hoffO : ({ bF with sudo_5Board_9marker_on := true }).sudo_5Board_8bench_on = false := by
    simp [hoffF]
  conv =>
    lhs
    pattern (Ecbs.settle _)
    rw [settle_off _ hoffO]
  conv =>
    rhs
    pattern (Ecbs.settle _)
    rw [settle_off _ hoffF]
  simp only [ok_bind]
  have hFT : src < bF.sudo_5Board_4held.size := by simpa [bF, bumpOp, feed, markerUpFeed] using hF
  have hHomeT : src < bF.sudo_5Board_4home.size := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hHome
  have hHFT : bF.sudo_5Board_4held[src] = true := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hHF
  have hArrT : bF.sudo_5Board_4home[src] = embed xs := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hArr
  have h7T : 7 ≤ bF.sudo_5Board_4held.size := by
    simpa [bF, bumpOp, feed, markerUpFeed] using h7
  have hpT : bF.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int) := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hp
  have hpeakT : bF.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int) := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hpeak
  have hnT : bF.sudo_5Board_1t.sudo_4Tier_1n = (n : Int) := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hn
  have hmovesT : bF.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int) := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hmoves
  have hblT : bF.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hbl
  have hcgT : bF.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hcg
  have hholeT : bF.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hhole
  have hwT : bF.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hw
  have hhT : bF.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hh
  have hrT : bF.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hr
  have hkT : bF.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k := by
    simpa [bF, bumpOp, feed, markerUpFeed] using hk
  exact cube_tail_flag bF dst src xs w h r n k moves hole bench peak peakS cg
    hfeedB hFT hHomeT hHFT hArrT h7T hpT hpeakT hn0 hnT hlenx hf hmovesT hblT hcgT hspan h3 hfm
    hholeT hxsT hw0 hh0 hrR hrP hnE hkLe hgap hwT hhT hrT hkT hsm hnsm hfitB hfold

/-- Marker-on cube, marker lifted. The card is `cubeOffBoard` of the seated feed;
    the flag stays on. Arithmetic is `cube_off_eq`. -/
theorem cube_down_eq (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves hole bench peak peakS cOps cg ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker < 0)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hpos : 0 < script) (hfit : FitsLen (ctrl + 1))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList xs)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n))) :
    Ecbs.cube b ((dst : Nat) : Int) ((src : Nat) : Int) =
      .ok { cubeOffBoard (markerDownFeed b ctrl mx) dst src xs n k moves hole bench
          peak peakS cOps hops hF hHome with
        sudo_5Board_9marker_on := true } := by
  rw [cube_down_comm b dst src xs w h r n k moves hole bench peak peakS cOps cg ctrl mx script
      hmk hoff hm hc hx hs hpos hfit hops hop1 hfops hF hHome hHF hArr h7 hp hpeak
      hn0 hn hlenx hf hmoves hbl hcg hspan h3 hfm hhole hxsT hw0 hh0 hrR hrP hnE hkLe hgap
      hw hh hr hk hsm hnsm hfitB hfold]
  rw [cube_off_eq (markerDownFeed b ctrl mx) dst src xs w h r n k moves hole bench peak peakS
      cOps cg rfl hoff hops hop1 hfops hbl hcg hspan hF hHome hHF hArr h7 hn0 hn hlenx hf
      hmoves hpeak hp hxsT h3 hfm ⟨hw0, hh0, hrR, hrP, hnE, hkLe, hgap⟩ hw hh hr hk hhole
      hsm hnsm hfitB hfold]
  simp only [ok_bind, pure_eq_ok]

/-- Marker-on cube, marker seated at `m`. The card is `cubeOffBoard` of the advanced feed;
    the flag stays on. Arithmetic is `cube_off_eq`. -/
theorem cube_up_eq (b : Ecbs.Board) (dst src : Nat) (xs : List Nat)
    (w h r n k moves hole bench peak peakS cOps cg m ctrl mx script : Nat)
    (hmk : b.sudo_5Board_9marker_on = true)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hm : b.sudo_5Board_6marker = Int.ofNat m)
    (hc : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl)
    (hx : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx)
    (hs : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script)
    (hbound : m + 1 < script) (hfitM : FitsLen (m + 1))
    (hfitC : FitsLen (ctrl + 2)) (hfit2 : FitsLen (m + 2))
    (hops : 1 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size)
    (hop1 : b.sudo_5Board_4cost.sudo_5Costs_3ops[1]'(hops) = (cOps : Int))
    (hfops : FitsLen (cOps + 1))
    (hF : src < b.sudo_5Board_4held.size)
    (hHome : src < b.sudo_5Board_4home.size)
    (hHF : b.sudo_5Board_4held[src] = true)
    (hArr : b.sudo_5Board_4home[src] = embed xs)
    (h7 : 7 ≤ b.sudo_5Board_4held.size)
    (hp : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int))
    (hpeak : b.sudo_5Board_4cost.sudo_5Costs_4peak = (peak : Int))
    (hn0 : 0 < n)
    (hn : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int))
    (hlenx : xs.length = n)
    (hf : FitsLen n)
    (hmoves : b.sudo_5Board_4cost.sudo_5Costs_5moves = (moves : Int))
    (hbl : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench)
    (hcg : b.sudo_5Board_1t.sudo_4Tier_7combgap = Int.ofNat cg)
    (hspan : 3 * (n - 1) + cg < bench)
    (h3 : FitsLen (3 * (n - 1)))
    (hfm : FitsLen (moves + 2 * n))
    (hhole : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole)
    (hxsT : allTritList xs)
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgap : n - k = w * r)
    (hw : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w)
    (hh : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h)
    (hr : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r)
    (hk : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000)
    (hfitB : FitsLen bench)
    (hfold : FitsLen (moves + 2 * n + 3 * (bench - n))) :
    Ecbs.cube b ((dst : Nat) : Int) ((src : Nat) : Int) =
      .ok { cubeOffBoard (markerUpFeed b m ctrl mx) dst src xs n k moves hole bench
          peak peakS cOps hops hF hHome with
        sudo_5Board_9marker_on := true } := by
  rw [cube_up_comm b dst src xs w h r n k moves hole bench peak peakS cOps cg m ctrl mx script
      hmk hoff hm hc hx hs hbound hfitM hfitC hfit2 hops hop1 hfops hF hHome hHF hArr h7 hp hpeak
      hn0 hn hlenx hf hmoves hbl hcg hspan h3 hfm hhole hxsT hw0 hh0 hrR hrP hnE hkLe hgap
      hw hh hr hk hsm hnsm hfitB hfold]
  rw [cube_off_eq (markerUpFeed b m ctrl mx) dst src xs w h r n k moves hole bench peak peakS
      cOps cg rfl hoff hops hop1 hfops hbl hcg hspan hF hHome hHF hArr h7 hn0 hn hlenx hf
      hmoves hpeak hp hxsT h3 hfm ⟨hw0, hh0, hrR, hrP, hnE, hkLe, hgap⟩ hw hh hr hk hhole
      hsm hnsm hfitB hfold]
  simp only [ok_bind, pure_eq_ok]

end EcbsLink2.Link2
