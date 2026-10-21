/-
  The base-point search, one planted hole at a time. A miss leaves the next
  plant. A hit stops on that hole. Every miss through the last hole is the
  line 963 refusal, and `Spec.basePoint` is `none`. A hit is the root
  `Spec.searchRoot` returns, so `Spec.basePoint` is the cofactor walk of it.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.SearchMiss
import EcbsLink2.Link2.Loop

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs
open EcbsLink2.Spec

/-- The curve, the root power, and the hit test, from a planted board. -/
def searchReadyDo (b0 : Ecbs.Board) (t : Spec.Tier) (j : Nat) :
    Except SudoRt.Trap Ecbs.Board :=
  do
    let b ← (do
      let b ← (do
        let b ← (do
          let b ← (do
            let x ← SudoRt.filledL (Int.ofNat t.n) (0 : Int)
            let x ← SudoRt.putL x (Int.ofNat j) (1 : Int)
            let b ← Ecbs.put b0 Ecbs.base_across x
            Ecbs.curve_side b Ecbs.base_across Ecbs.bottom)
          let b ← Ecbs.mul b Ecbs.gap Ecbs.bottom Ecbs.bottom true false false
          Ecbs.settle b)
        Ecbs.white0 b Ecbs.up)
      let strip ← emittedStrip t.n
      let b ← Ecbs.put b Ecbs.across strip
      pure ({ b with sudo_5Board_9marker_on := true }))
    powRun b (rootDigits t.n)

/-- Hit test, then either stop or empty the five homes. `ρ` is the loop's
    return payload. The body never returns, so every `ρ` is the same step. -/
def searchBody {ρ : Type} (b0 : Ecbs.Board) (t : Spec.Tier) (j : Nat) (found : Int) :
    Except SudoRt.Trap (SudoRt.Flow (Ecbs.Board × Int) ρ) :=
  do
    let b ← searchReadyDo b0 t j
    let r ← searchCheck b
    if r.1 = true then
      pure (SudoRt.Flow.brk (r.2, Int.ofNat j))
    else
      let b ← searchMiss r.2
      pure (SudoRt.Flow.cont (b, found))

/-- One index of the emitted search. The last index breaks; a hit breaks early.
    `ρ` matches the emitted loop: the card stamps `Int × Board`, and a proof
    that the return arm is dead instantiates `Empty`. -/
def searchStep {ρ : Type} (t : Spec.Tier) (toN : Nat) (σ : Int × (Ecbs.Board × Int)) :
    Except SudoRt.Trap (SudoRt.Flow (Int × (Ecbs.Board × Int)) ρ) :=
  if σ.1 > Int.ofNat toN then
    pure (SudoRt.Flow.brk σ)
  else
    searchBody σ.2.1 t σ.1.toNat σ.2.2 >>= fun fl =>
      match fl with
      | .ret r => pure (SudoRt.Flow.ret r)
      | .brk fs => pure (SudoRt.Flow.brk (σ.1, fs))
      | .cont fs =>
          if (σ.1 == Int.ofNat toN) = true then
            pure (SudoRt.Flow.brk (σ.1, fs))
          else
            SudoRt.addI σ.1 1 >>= fun i' =>
              pure (SudoRt.Flow.cont (i', fs))

/-- The card's join. `found` stayed 0, so line 963 fails; a positive hole continues. -/
def searchJoin {α : Type} (k : Ecbs.Board → Int → Except SudoRt.Trap α)
    (σ : Int × (Ecbs.Board × Int)) : Except SudoRt.Trap α :=
  do
    let _ ← SudoRt.sudoAssert (decide (σ.2.2 > (0 : Int))) 963
    k σ.2.1 σ.2.2

private theorem holes_left (n i : Nat) (hi : 1 ≤ i) (hle : i ≤ n - 1) :
    1 < n - (i - 1) := by
  omega

private theorem holes_step (n i : Nat) (hi : 1 ≤ i) :
    n - ((i + 1) - 1) = (n - (i - 1)) - 1 := by
  omega

private theorem nat_to (i : Nat) : (Int.ofNat i).toNat = i :=
  rfl

private theorem len_one (n i : Nat) (hn : n ≤ 1000000) (hi : i ≤ n) : FitsLen (i + 1) := by
  have hbig : 1000001 ≤ 9223372036854775807 := by decide
  have h : i + 1 ≤ 1000001 := by omega
  unfold FitsLen i64MaxNat
  omega

/-- A missed hole. The loop either breaks on the last index or steps one on. -/
theorem search_step_miss (b0 : Ecbs.Board) (t : Spec.Tier)
    (holesLeft i toN mv0 sl0 c0 : Nat)
    (hp : PlantAt b0 t holesLeft)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (hi0 : 0 < i) (hi : i ≤ toN) (hn : toN < t.n) (hn3 : 3 ≤ t.n)
    (hnext : 1 < holesLeft)
    (hmiss : rootHit t.n t.k t.benchlen (basisPeg t.n i) = false)
    (hmv0 : b0.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv0)
    (hsl0 : b0.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl0)
    (hc0 : b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)) :
    ∃ bM,
      searchStep (ρ := Empty) t toN (Int.ofNat i, (b0, 0)) =
        (if i = toN then .ok (SudoRt.Flow.brk (Int.ofNat i, (bM, 0)))
          else .ok (SudoRt.Flow.cont (Int.ofNat (i + 1), (bM, 0)))) ∧
        PlantAt bM t (holesLeft - 1) ∧
        ∃ c0', bM.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0' + tierR t) := by
  obtain ⟨bM, hplant, hMiss, hpM, hctrl⟩ :=
    miss_plantAt b0 t holesLeft hp hOk hsh sat i hi0 (Nat.lt_of_le_of_lt hi hn) hn3
      mv0 sl0 c0 hmv0 hsl0 hc0 hmiss hnext
  have hleft1 : (1 : Nat) ≤ holesLeft := Nat.le_of_lt hnext
  obtain ⟨bR, _, _, hready, hAt, _⟩ :=
    search_ready_at b0 t holesLeft hp hOk hsh sat i hi0 (Nat.lt_of_le_of_lt hi hn) hn3
      mv0 sl0 c0 hmv0 hsl0 hc0 1 (by decide) hleft1
  let x := basisPeg t.n i
  obtain ⟨bC, bit, _, hck, hbit, _, _, _, _, _⟩ :=
    search_check_at bR t x (rootY t.n t.k t.benchlen x) (curveSide t.n t.k t.benchlen x)
      (fieldMul t.n t.k t.benchlen (curveSide t.n t.k t.benchlen x)
        (curveSide t.n t.k t.benchlen x))
      (rootStrip t.n) x 1 hAt
  have hfalse : bit = false := by rw [hbit, hmiss]
  have hck' : searchCheck bR = .ok (false, bC) := by simpa [hfalse] using hck
  unfold searchStep
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng]
  have hdrop : searchMiss bC = .ok bM := by
    have hdo :
        (searchReadyDo b0 t i >>= fun b => searchCheck b >>= fun r => searchMiss r.2) =
          .ok bM := by
      simpa [searchReadyDo] using hplant
    unfold searchReadyDo at hdo
    rw [hready, ok_bind, hck', ok_bind] at hdo
    exact hdo
  have hbody : searchBody (ρ := Empty) b0 t i 0 = .ok (SudoRt.Flow.cont (bM, 0)) := by
    unfold searchBody searchReadyDo
    rw [hready, ok_bind, hck', ok_bind]
    have hne : ¬ ((false : Bool) = true) := by decide
    rw [if_neg hne, hdrop, ok_bind, pure_eq_ok]
  rw [nat_to, hbody, ok_bind]
  refine ⟨bM, ?_, hpM, hctrl⟩
  · dsimp only
    exact asc_tail toN i (len_one t.n i hsh.n_small (Nat.le_of_lt (Nat.lt_of_le_of_lt hi hn)))
      (bM, (0 : Int))

/-- Every hole from 1 misses. The join is line 963, and `basePoint` is `none`. -/
theorem search_loop_miss {α : Type} (b0 : Ecbs.Board) (t : Spec.Tier)
    (k : Ecbs.Board → Int → Except SudoRt.Trap α)
    (hp : PlantAt b0 t t.n)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t) (hn3 : 3 ≤ t.n)
    (hctrl : ∃ c0, b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t))
    (hmiss : ∀ i, 1 ≤ i → i < t.n → rootHit t.n t.k t.benchlen (basisPeg t.n i) = false) :
    SudoRt.runLoopOn (Int.ofNat 1, (b0, (0 : Int)))
        (fuelRange (Int.ofNat 1) (Int.ofNat (t.n - 1)))
        (searchStep (ρ := Empty) t (t.n - 1)) (searchJoin k) (fun r => nomatch r) =
      .error { kind := "AssertFailed", detail := s!"line {963}" } ∧
      basePoint t = none := by
  have hle : 1 ≤ t.n - 1 := by omega
  let Inv : Nat → (Ecbs.Board × Int) → Prop := fun i s =>
    s.2 = 0 ∧ PlantAt s.1 t (t.n - (i - 1)) ∧
      (∃ c0, s.1.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)) ∧
      ∀ k, 1 ≤ k → k < i → rootHit t.n t.k t.benchlen (basisPeg t.n k) = false
  have hloop : SudoRt.runLoopOn (Int.ofNat 1, (b0, (0 : Int)))
      (fuelRange (Int.ofNat 1) (Int.ofNat (t.n - 1)))
      (searchStep (ρ := Empty) t (t.n - 1)) (searchJoin k) (fun r => nomatch r) =
      .error { kind := "AssertFailed", detail := s!"line {963}" } :=
    asc_goal (α := Ecbs.Board × Int) (ρ := Empty) Inv (fromN := 1) (toN := t.n - 1)
    (s0 := (b0, (0 : Int))) (hle := hle)
    (h0 := by
      refine ⟨rfl, ?_, hctrl, ?_⟩
      · have hz : t.n - (1 - 1) = t.n := by omega
        simpa [hz] using hp
      · intro k hk1 hk2
        omega)
    (hstep := by
      intro i s hi1 hi2 hI
      rcases hI with ⟨hf, hpI, hcI, hprev⟩
      have hf0 : s.2 = 0 := hf
      rcases s with ⟨b, found⟩
      have hfound : found = 0 := hf0
      subst hfound
      rcases hpI.moves with ⟨mv, hmv, _⟩
      rcases hpI.slides with ⟨sl, hsl, _⟩
      rcases hcI with ⟨c0, hc⟩
      obtain ⟨bM, hst, hpM, hcM⟩ :=
        search_step_miss b t (t.n - (i - 1)) i (t.n - 1) mv sl c0 hpI hOk hsh sat
          (by omega) hi2 (by omega) hn3 (holes_left t.n i hi1 hi2)
          (hmiss i hi1 (by omega)) hmv hsl hc
      refine ⟨(bM, 0), ?_, ?_⟩
      · refine ⟨rfl, ?_, hcM, ?_⟩
        · rw [holes_step t.n i hi1]
          exact hpM
        · intro k hk1 hk2
          by_cases hk : k = i
          · simpa [hk] using hmiss i hi1 (by omega)
          · exact hprev k hk1 (by omega)
      · exact hst)
    (hpost := by
      intro s hI
      rcases hI with ⟨hf, _, _, _⟩
      rcases s with ⟨b, found⟩
      have hfound : found = 0 := hf
      subst hfound
      simpa [searchJoin] using search_refuse b (fun b => k b 0))
  refine ⟨hloop, ?_⟩
  · exact basePoint_none t (by
      intro i hi1 _ hi3
      exact hmiss i hi1 hi3)

private theorem join_hit {α : Type} (k : Ecbs.Board → Int → Except SudoRt.Trap α)
    (b : Ecbs.Board) (j : Nat) (hj : 0 < j) :
    searchJoin k (Int.ofNat j, (b, Int.ofNat j)) = k b (Int.ofNat j) := by
  unfold searchJoin
  have hdec : decide (Int.ofNat j > (0 : Int)) = true :=
    decide_eq_true (Int.ofNat_pos.mpr hj)
  rw [hdec, sudoAssert_true, ok_bind]

/-- A hit. The loop breaks on this hole with the squared root still seated. -/
theorem search_step_hit (b0 : Ecbs.Board) (t : Spec.Tier)
    (holesLeft i toN mv0 sl0 c0 : Nat)
    (hp : PlantAt b0 t holesLeft)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t)
    (hi0 : 0 < i) (hi : i ≤ toN) (hn : toN < t.n) (hn3 : 3 ≤ t.n)
    (hhit : rootHit t.n t.k t.benchlen (basisPeg t.n i) = true)
    (hmv0 : b0.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv0)
    (hsl0 : b0.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat sl0)
    (hc0 : b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)) :
    ∃ bH,
      searchStep (ρ := Empty) t toN (Int.ofNat i, (b0, 0)) =
        .ok (SudoRt.Flow.brk (Int.ofNat i, (bH, Int.ofNat i))) ∧
        HitAt bH t (basisPeg t.n i) (rootStrip t.n) (basisPeg t.n i) := by
  have hpos : 0 < holesLeft := hp.holesPos
  obtain ⟨bR, _, _, hready, hAt, _⟩ :=
    search_ready_at b0 t holesLeft hp hOk hsh sat i hi0 (Nat.lt_of_le_of_lt hi hn) hn3
      mv0 sl0 c0 hmv0 hsl0 hc0 1 (by decide) (Nat.succ_le_of_lt hpos)
  obtain ⟨bH, hck, hhitAt⟩ :=
    search_hit_at bR t (basisPeg t.n i) (rootY t.n t.k t.benchlen (basisPeg t.n i))
      (curveSide t.n t.k t.benchlen (basisPeg t.n i))
      (fieldMul t.n t.k t.benchlen (curveSide t.n t.k t.benchlen (basisPeg t.n i))
        (curveSide t.n t.k t.benchlen (basisPeg t.n i)))
      (rootStrip t.n) (basisPeg t.n i) 1 hAt hhit
  unfold searchStep
  have hng : ¬ (Int.ofNat i > Int.ofNat toN) := ofNat_not_gt hi
  rw [if_neg hng, nat_to]
  unfold searchBody searchReadyDo
  rw [hready, ok_bind, hck, ok_bind, if_pos rfl]
  refine ⟨bH, ?_, hhitAt⟩
  · simp only [ok_bind, pure_eq_ok]

/-- Some hole hits. The loop stops there, and `basePoint` is that root's cofactor walk. -/
theorem search_loop_hit {α : Type} (b0 : Ecbs.Board) (t : Spec.Tier)
    (k : Ecbs.Board → Int → Except SudoRt.Trap α)
    (hp : PlantAt b0 t t.n)
    (hOk : BoardOk t) (hsh : TierShape t) (sat : TierSat t) (hn3 : 3 ≤ t.n)
    (hctrl : ∃ c0, b0.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t))
    (hhit : ∃ j, 1 ≤ j ∧ j < t.n ∧ rootHit t.n t.k t.benchlen (basisPeg t.n j) = true) :
    ∃ j b,
      0 < j ∧ j < t.n ∧
        SudoRt.runLoopOn (Int.ofNat 1, (b0, (0 : Int)))
          (fuelRange (Int.ofNat 1) (Int.ofNat (t.n - 1)))
          (searchStep (ρ := Empty) t (t.n - 1)) (searchJoin k) (fun r => nomatch r) =
          k b (Int.ofNat j) ∧
        HitAt b t (basisPeg t.n j) (rootStrip t.n) (basisPeg t.n j) ∧
        (∀ i, 1 ≤ i → i < j → rootHit t.n t.k t.benchlen (basisPeg t.n i) = false) ∧
        searchRoot t.n t.k t.benchlen t.n 1 =
          some (basisPeg t.n j, rootY t.n t.k t.benchlen (basisPeg t.n j)) ∧
        basePoint t =
          cofactorWalk t.n t.k t.benchlen
            (basisPeg t.n j, rootY t.n t.k t.benchlen (basisPeg t.n j)) := by
  have hle : 1 ≤ t.n - 1 := by omega
  let Inv : Nat → (Ecbs.Board × Int) → Prop := fun i s =>
    s.2 = 0 ∧ PlantAt s.1 t (t.n - (i - 1)) ∧
      (∃ c0, s.1.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat (c0 + tierR t)) ∧
      ∀ q, 1 ≤ q → q < i → rootHit t.n t.k t.benchlen (basisPeg t.n q) = false
  let Done : Nat → (Ecbs.Board × Int) → Prop := fun i s =>
    s.2 = Int.ofNat i ∧
      HitAt s.1 t (basisPeg t.n i) (rootStrip t.n) (basisPeg t.n i) ∧
      rootHit t.n t.k t.benchlen (basisPeg t.n i) = true ∧
      ∀ q, 1 ≤ q → q < i → rootHit t.n t.k t.benchlen (basisPeg t.n q) = false
  obtain ⟨j, s, hj1, hj2, hs, heq⟩ :=
    asc_brk_inv (searchStep (ρ := Empty) t (t.n - 1)) (searchJoin k) (fun r => nomatch r)
      Inv Done 1 (t.n - 1) hle
      (by
        intro i s hi1 hi2 hI
        rcases hI with ⟨hf, hpI, hcI, hprev⟩
        rcases s with ⟨b, found⟩
        have hfound : found = 0 := hf
        subst hfound
        rcases hpI.moves with ⟨mv, hmv, _⟩
        rcases hpI.slides with ⟨sl, hsl, _⟩
        rcases hcI with ⟨c0, hc⟩
        by_cases hh : rootHit t.n t.k t.benchlen (basisPeg t.n i) = true
        · right
          obtain ⟨bH, hst, hAt⟩ :=
            search_step_hit b t (t.n - (i - 1)) i (t.n - 1) mv sl c0 hpI hOk hsh sat
              (by omega) hi2 (by omega) hn3 hh hmv hsl hc
          refine ⟨(bH, Int.ofNat i), ?_, ?_⟩
          · exact ⟨rfl, hAt, hh, hprev⟩
          · exact hst
        · left
          have hfmiss : rootHit t.n t.k t.benchlen (basisPeg t.n i) = false := by
            cases hb : rootHit t.n t.k t.benchlen (basisPeg t.n i) with
            | false => rfl
            | true => exact absurd hb hh
          obtain ⟨bM, hst, hpM, hcM⟩ :=
            search_step_miss b t (t.n - (i - 1)) i (t.n - 1) mv sl c0 hpI hOk hsh sat
              (by omega) hi2 (by omega) hn3 (holes_left t.n i hi1 hi2) hfmiss hmv hsl hc
          refine ⟨(bM, 0), ?_, ?_⟩
          · refine ⟨rfl, ?_, hcM, ?_⟩
            · rw [holes_step t.n i hi1]
              exact hpM
            · intro q hq1 hq2
              by_cases hq : q = i
              · simpa [hq] using hfmiss
              · exact hprev q hq1 (by omega)
          · exact hst)
      (b0, 0)
      (by
        refine ⟨rfl, ?_, hctrl, ?_⟩
        · have hz : t.n - (1 - 1) = t.n := by omega
          simpa [hz] using hp
        · intro q hq1 hq2
          omega)
  rcases hs with hbad | hdone
  · rcases hhit with ⟨j0, hj0, hjN, hh0⟩
    rcases hbad with ⟨_, _, _, hprev⟩
    exact absurd hh0 (by simpa using hprev j0 hj0 (by omega))
  · rcases s with ⟨b, found⟩
    rcases hdone with ⟨hf, hAt, hh, hprev⟩
    have hfound : found = Int.ofNat j := hf
    have hpos : 0 < j := by omega
    have hjN : j < t.n := Nat.lt_of_le_of_lt hj2 (by omega)
    have hidx : 1 + (j - 1) = j := by
      rw [Nat.add_comm, Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    have hroot := searchRoot_first t.n t.k t.benchlen t.n 1 (j - 1)
      (by omega) (by omega)
      (by
        intro q hq1 hq2
        exact hprev q hq1 (by omega))
      (by simpa [hidx] using hh)
    refine ⟨j, b, hpos, hjN, ?_, hAt, hprev, ?_, ?_⟩
    · rw [heq]
      simpa [hfound] using join_hit k b j hpos
    · simpa [hidx] using hroot
    · rw [basePoint_of_root]
      simpa [hidx] using hroot

end EcbsLink2.Link2
