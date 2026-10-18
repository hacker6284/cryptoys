/-
  The onto sum, packed as `SumAt`, is what `Ecbs.add` reads. This module
  turns that into the board `fform_add_on_proj` reads: the bench prefix is
  `fformF`, still aimed at the empty gap, and the homes are unchanged.
  `Ecbs.add` stays folded. Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformApply
import EcbsLink2.Link2.FformGapAdd

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

attribute [local irreducible] Ecbs.add addOnBench laneAdd

/-- `a[i]? = some v` is an in-range read. -/
private theorem read_some {α : Type} (a : Array α) (i : Nat) {v : α}
    (h : a[i]? = some v) : ∃ hlt : i < a.size, a[i]'hlt = v := by
  if hlt : i < a.size then
    refine ⟨hlt, ?_⟩
    have heq := Array.getElem?_eq_getElem hlt
    rw [h] at heq
    exact Option.some.inj heq.symm
  else
    rw [getElem?_neg a i hlt] at h
    injection h

private theorem q_eq {α : Type} (a c : Array α) (i : Nat) (h : a = c) :
    a[i]? = c[i]? := h ▸ rfl

/-- The board after adding `v²Z` into the bench prefix. `fform_add_on_proj`
    reads this shape. -/
structure AddAt (b : Ecbs.Board) (lane : List Nat) (n k bench : Nat)
    (u v z x2 y2 : List Nat) (script w h r : Nat)
    (m ctrl mx cOps moves slides hole peak peakS : Nat) : Prop where
  on : b.sudo_5Board_8bench_on = true
  to5 : b.sudo_5Board_8bench_to = (5 : Int)
  markOn : b.sudo_5Board_9marker_on = true
  marker : b.sudo_5Board_6marker = Int.ofNat m
  ctrlEq : b.sudo_5Board_4cost.sudo_5Costs_4ctrl = Int.ofNat ctrl
  mxEq : b.sudo_5Board_4cost.sudo_5Costs_17script_marker_max = Int.ofNat mx
  movesEq : b.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat moves
  slidesEq : b.sudo_5Board_4cost.sudo_5Costs_6slides = Int.ofNat slides
  peakEq : b.sudo_5Board_4cost.sudo_5Costs_4peak = Int.ofNat peak
  strictEq : b.sudo_5Board_4cost.sudo_5Costs_11peak_strict = (peakS : Int)
  holeEq : b.sudo_5Board_4cost.sudo_5Costs_14max_bench_hole = Int.ofNat hole
  opsSz : 0 < b.sudo_5Board_4cost.sudo_5Costs_3ops.size
  ops0 : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat cOps)
  nEq : b.sudo_5Board_1t.sudo_4Tier_1n = (n : Int)
  kEq : b.sudo_5Board_1t.sudo_4Tier_1k = Int.ofNat k
  benchEq : b.sudo_5Board_1t.sudo_4Tier_8benchlen = Int.ofNat bench
  scriptEq : b.sudo_5Board_1t.sudo_4Tier_6script = Int.ofNat script
  wEq : b.sudo_5Board_1t.sudo_4Tier_1w = Int.ofNat w
  hEq : b.sudo_5Board_1t.sudo_4Tier_1h = Int.ofNat h
  rEq : b.sudo_5Board_1t.sudo_4Tier_1r = Int.ofNat r
  home7 : 7 ≤ b.sudo_5Board_4home.size
  held7 : 7 ≤ b.sudo_5Board_4held.size
  home0 : b.sudo_5Board_4home[0]? = some (embed v)
  held0 : b.sudo_5Board_4held[0]? = some true
  home1 : b.sudo_5Board_4home[1]? = some (embed u)
  held1 : b.sudo_5Board_4held[1]? = some true
  home2 : b.sudo_5Board_4home[2]? =
    some (embed (fieldMul n k bench (fieldMul n k bench v v) z))
  held2 : b.sudo_5Board_4held[2]? = some true
  home3 : b.sudo_5Board_4home[3]? = some (embed x2)
  held3 : b.sudo_5Board_4held[3]? = some true
  home4 : b.sudo_5Board_4home[4]? = some (embed y2)
  held4 : b.sudo_5Board_4held[4]? = some true
  held5 : b.sudo_5Board_4held[5]? = some false
  held6 : b.sudo_5Board_4held[6]? = some false
  benchArr : b.sudo_5Board_5bench = embed lane
  posL : 0 < lane.length
  nle : n ≤ lane.length
  fitL : FitsLen lane.length
  zero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i]'hi = 0
  take : lane.take n = fformF n k bench u v z
  lenU : u.length = n
  lenV : v.length = n
  lenZ : z.length = n
  lenX : x2.length = n
  lenY : y2.length = n
  triU : allTritList u
  triV : allTritList v
  triZ : allTritList z
  triX : allTritList x2
  triY : allTritList y2
  span : 2 * (n - 1) < bench
  npos : 0 < n
  nbench : n ≤ bench
  peak7 : 7 ≤ peak
  peakS7 : 7 ≤ peakS
  fi : FitsLen (2 * (n - 1))

/-- `gap_add_on_sum`, read off `SumAt`. The bench prefix becomes `fformF`. -/
theorem add_on_sum (b : Ecbs.Board) (lane : List Nat) (n k bench : Nat)
    (u v z x2 y2 : List Nat) (script w h r : Nat)
    (m ctrl mx cOps moves slides hole peak peakS : Nat)
    (s : SumAt b lane n k bench u v z x2 y2 script w h r
      m ctrl mx cOps moves slides hole peak peakS) :
    ∃ (b' : Ecbs.Board) (lane' : List Nat) (moves' : Nat),
      Ecbs.add b (5 : Int) (2 : Int) false = .ok b' ∧
      moves' = moves + pegCount (fieldMul n k bench (fieldMul n k bench v v) z) ∧
      AddAt b' lane' n k bench u v z x2 y2 script w h r
        m ctrl mx cOps moves' slides hole peak peakS := by
  obtain ⟨h5, hempty⟩ := read_some b.sudo_5Board_4held 5 s.held5
  obtain ⟨h2D, hheldB⟩ := read_some b.sudo_5Board_4held 2 s.held2
  obtain ⟨h2H, harrB⟩ := read_some b.sudo_5Board_4home 2 s.home2
  obtain ⟨b', lane', hok, hb, ht, hon, hto, hhome, hheld, _hgap, _hbot,
      hmk, hflag, htier, hctrl, hmx, hsl, hpk, hst, hhole, hops, hmv, _hlen,
      hpos, hnle, hfit, hzero⟩ :=
    gap_add_on_sum b 5 2 u v z lane n k bench moves
      h5 hempty s.on s.to5 s.benchArr h2H h2D hheldB harrB
      s.nEq s.nle s.npos s.nbench s.take s.triU s.triV s.triZ s.span
      s.movesEq s.fitN s.posL s.fitL s.zero
  let moves' := moves + pegCount (fieldMul n k bench (fieldMul n k bench v v) z)
  refine ⟨b', lane', moves', hok, rfl, ?_⟩
  exact {
    on := hon
    to5 := hto
    markOn := hflag.trans s.markOn
    marker := hmk.trans s.marker
    ctrlEq := hctrl.trans s.ctrlEq
    mxEq := hmx.trans s.mxEq
    movesEq := by simpa [moves'] using hmv
    slidesEq := hsl.trans s.slidesEq
    peakEq := hpk.trans s.peakEq
    strictEq := hst.trans s.strictEq
    holeEq := hhole.trans s.holeEq
    opsSz := by rw [hops]; exact s.opsSz
    ops0 := by
      have hs : b.sudo_5Board_4cost.sudo_5Costs_3ops[0]? = some (Int.ofNat cOps) :=
        (Array.getElem?_eq_getElem s.opsSz).trans (congrArg some s.ops0)
      exact (q_eq _ _ 0 hops).trans hs
    nEq := by rw [htier]; exact s.nEq
    kEq := by rw [htier]; exact s.kEq
    benchEq := by rw [htier]; exact s.benchEq
    scriptEq := by rw [htier]; exact s.scriptEq
    wEq := by rw [htier]; exact s.wEq
    hEq := by rw [htier]; exact s.hEq
    rEq := by rw [htier]; exact s.rEq
    home7 := by rw [hhome]; exact s.home7
    held7 := by
      have h6 := read_some b.sudo_5Board_4held 6 s.held6
      obtain ⟨h6, _⟩ := h6
      rw [hheld]
      exact Nat.succ_le_of_lt h6
    home0 := (q_eq _ _ 0 hhome).trans s.home0
    held0 := (q_eq _ _ 0 hheld).trans s.held0
    home1 := (q_eq _ _ 1 hhome).trans s.home1
    held1 := (q_eq _ _ 1 hheld).trans s.held1
    home2 := (q_eq _ _ 2 hhome).trans s.home2
    held2 := (q_eq _ _ 2 hheld).trans s.held2
    home3 := (q_eq _ _ 3 hhome).trans s.home3
    held3 := (q_eq _ _ 3 hheld).trans s.held3
    home4 := (q_eq _ _ 4 hhome).trans s.home4
    held4 := (q_eq _ _ 4 hheld).trans s.held4
    held5 := (q_eq _ _ 5 hheld).trans s.held5
    held6 := (q_eq _ _ 6 hheld).trans s.held6
    benchArr := hb
    posL := hpos
    nle := hnle
    fitL := hfit
    zero := hzero
    take := ht
    lenU := s.lenU
    lenV := s.lenV
    lenZ := s.lenZ
    lenX := s.lenX
    lenY := s.lenY
    triU := s.triU
    triV := s.triV
    triZ := s.triZ
    triX := s.triX
    triY := s.triY
    span := s.span
    npos := s.npos
    nbench := s.nbench
    peak7 := s.peak7
    peakS7 := s.peakS7
    fi := s.fi
  }

end EcbsLink2.Link2
