/-
  One nonzero cell, from the board `add_on_sum` leaves. `fform_add_on_f`
  runs the six multiplies and the clear. `add_board_proj` rewrites the
  across, the bottom, and the bench prefix as `x₃·Z₃`, `Z₃`, and `y₃·Z₃`.
  Proof-only. Not a security claim.
-/
import EcbsLink2.Link2.FformAddApply
import EcbsLink2.Link2.FformAddTie

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open EcbsLink2.Spec

attribute [local irreducible] Ecbs.add addOnBench laneAdd

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

/-- The projective triple the nonzero cell writes. Home 0 holds `x₃·Z₃`,
    home 2 holds `Z₃`, and the bench prefix is `y₃·Z₃`. -/
structure CellAt (b : Ecbs.Board) (lane : List Nat) (n k bench : Nat)
    (v z x2 y2 x3 yUp : List Nat) (tier : Ecbs.Tier) (szHome szHeld : Nat) : Prop where
  home0 : ∀ h0 : 0 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[0]'h0 = embed (fieldMul n k bench x3 (fformBottom n k bench v z))
  home2 : ∀ h2 : 2 < b.sudo_5Board_4home.size,
    b.sudo_5Board_4home[2]'h2 = embed (fformBottom n k bench v z)
  benchArr : b.sudo_5Board_5bench = embed lane
  take : lane.take n = fieldMul n k bench yUp (fformBottom n k bench v z)
  held5 : ∀ hg : 5 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[5]'hg = false
  on : b.sudo_5Board_8bench_on = true
  to1 : b.sudo_5Board_8bench_to = (1 : Int)
  held1 : ∀ h1 : 1 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[1]'h1 = false
  held2 : ∀ h2 : 2 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[2]'h2 = true
  nle : n ≤ lane.length
  zero : ∀ i, n ≤ i → ∀ hi : i < lane.length, lane[i]'hi = 0
  home3 : ∀ h3 : 3 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[3]'h3 = embed x2
  held3 : ∀ h3 : 3 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[3]'h3 = true
  home4 : ∀ h4 : 4 < b.sudo_5Board_4home.size, b.sudo_5Board_4home[4]'h4 = embed y2
  held4 : ∀ h4 : 4 < b.sudo_5Board_4held.size, b.sudo_5Board_4held[4]'h4 = true
  tierEq : b.sudo_5Board_1t = tier
  szH : b.sudo_5Board_4home.size = szHome
  szD : b.sudo_5Board_4held.size = szHeld

/-- `fform_add_on_f`, then `add_board_proj`, on the board `AddAt` describes. -/
theorem cell_on_add (b : Ecbs.Board) (lane : List Nat) (n k bench : Nat)
    (u v z x2 y2 : List Nat) (script w h r : Nat)
    (m ctrl mx cOps moves slides hole peak peakS : Nat) (red : Bool)
    (x3 yUp : List Nat)
    (s : AddAt b lane n k bench u v z x2 y2 script w h r
      m ctrl mx cOps moves slides hole peak peakS)
    (hbound : m + 5 < script)
    (hfitM6 : FitsLen (m + 6)) (hfitC6 : FitsLen (ctrl + 12)) (hfops6 : FitsLen (cOps + 6))
    (hf : FitsLen n)
    (hBig : FitsLen (moves + 8 * stepBudget n bench))
    (hSlide : FitsLen (slides + 8 * n))
    (hw0 : 0 < w) (hh0 : 0 < h) (hrR : r < h) (hrP : 0 < r)
    (hnE : n = w * h - 1) (hkLe : k ≤ n) (hgapN : n - k = w * r)
    (hsm : w ≤ 1000000 ∧ h ≤ 1000000 ∧ r ≤ 1000000 ∧ bench ≤ 1000001)
    (hnsm : n ≤ 1000000) (hfitB : FitsLen bench)
    (hx : fformAcross n k bench x2 u v z =
      fieldMul n k bench x3 (fformBottom n k bench v z))
    (hy : addUp n k bench red y2 u v z =
      fieldMul n k bench yUp (fformBottom n k bench v z)) :
    ∃ b' lane',
      (Ecbs.mul b Ecbs.bottom Ecbs.across Ecbs.bottom false false false >>= fun b =>
        Ecbs.mul b Ecbs.across Ecbs.gap Ecbs.across false false false >>= fun b =>
        Ecbs.mul b Ecbs.across Ecbs.base_across Ecbs.bottom true true false >>= fun b =>
        Ecbs.mul b Ecbs.up Ecbs.gap Ecbs.up false false true >>= fun b =>
        Ecbs.mul b Ecbs.up Ecbs.base_up Ecbs.bottom true true (! red) >>= fun b =>
        Ecbs.clear b Ecbs.gap >>= fun b =>
        pure (true, b)) = .ok (true, b') ∧
      CellAt b' lane' n k bench v z x2 y2 x3 yUp b.sudo_5Board_1t
        b.sudo_5Board_4home.size b.sudo_5Board_4held.size := by
  obtain ⟨_, hvH⟩ := read_some b.sudo_5Board_4held 0 s.held0
  obtain ⟨_, hvA⟩ := read_some b.sudo_5Board_4home 0 s.home0
  obtain ⟨_, huH⟩ := read_some b.sudo_5Board_4held 1 s.held1
  obtain ⟨_, huA⟩ := read_some b.sudo_5Board_4home 1 s.home1
  obtain ⟨_, hzH⟩ := read_some b.sudo_5Board_4held 2 s.held2
  obtain ⟨_, hzA⟩ := read_some b.sudo_5Board_4home 2 s.home2
  obtain ⟨_, hxH⟩ := read_some b.sudo_5Board_4held 3 s.held3
  obtain ⟨_, hxA⟩ := read_some b.sudo_5Board_4home 3 s.home3
  obtain ⟨_, hyH⟩ := read_some b.sudo_5Board_4held 4 s.held4
  obtain ⟨_, hyA⟩ := read_some b.sudo_5Board_4home 4 s.home4
  obtain ⟨_, hgH⟩ := read_some b.sudo_5Board_4held 5 s.held5
  obtain ⟨_, hsH⟩ := read_some b.sudo_5Board_4held 6 s.held6
  obtain ⟨hops, hop0⟩ := read_some b.sudo_5Board_4cost.sudo_5Costs_3ops 0 s.ops0
  obtain ⟨b', lane', hdo, h0, h2, hbench, htake, hheld, hon, hto, h1, h2h, hnle, hzero,
      h3a, h3h, h4a, h4h, htier, hszH, hszD⟩ :=
    fform_add_on_f b red v z x2 u y2 lane
      m ctrl mx script cOps n k w h r moves slides hole peak peakS bench
      s.held7 s.home7 hvH hvA huH huA hzH hzA hxH hxA hyH hyA hgH hsH
      s.markOn s.on s.to5 s.marker s.ctrlEq s.mxEq s.scriptEq hbound
      hfitM6 hfitC6 hfops6 s.nEq hops hop0 s.benchArr s.posL s.nle s.zero s.take
      hf s.fitL s.movesEq s.slidesEq s.peakEq hBig hSlide s.benchEq s.npos s.nbench
      s.lenV s.lenU s.lenX s.lenY s.peak7 s.peakS7 s.strictEq s.span s.triV s.triU
      s.triX s.triY s.fi s.holeEq hw0 hh0 hrR hrP hnE hkLe hgapN s.wEq s.hEq s.rEq
      s.kEq hsm hnsm hfitB
  have htake' : lane'.take n = addUp n k bench red y2 u v z := by
    simpa [addUp] using htake
  obtain ⟨h0', h2', hy'⟩ :=
    add_board_proj n k bench x2 u v z x3 yUp red y2 b' lane' h0 h2 htake' hx hy
  exact ⟨b', lane', hdo, {
    home0 := h0'
    home2 := h2'
    benchArr := hbench
    take := hy'
    held5 := hheld
    on := hon
    to1 := hto
    held1 := h1
    held2 := h2h
    nle := hnle
    zero := hzero
    home3 := h3a
    held3 := h3h
    home4 := h4a
    held4 := h4h
    tierEq := htier
    szH := hszH
    szD := hszD
  }⟩

/-- `CellAt` is `ProjOn` in the `yBench` layout: `X = x₃·Z₃` in home 0,
    `Z₃` in home 2, and `Y = y₃·Z₃` on the bench aimed at home 1. -/
theorem cell_proj (t : Spec.Tier) (b : Ecbs.Board) (lane : List Nat)
    (v z x2 y2 x3 yUp : List Nat) (tier : Ecbs.Tier) (szH szD : Nat)
    (c : CellAt b lane t.n t.k t.benchlen v z x2 y2 x3 yUp tier szH szD)
    (hspan : 2 * (t.n - 1) < t.benchlen) (hnb : t.n ≤ t.benchlen)
    (hne : fformBottom t.n t.k t.benchlen v z ≠ List.replicate t.n 0)
    (hinv : ∃ w, w.length = t.n ∧ allTritList w ∧
      fieldMul t.n t.k t.benchlen (fformBottom t.n t.k t.benchlen v z) w = onePeg t.n) :
    ProjOn t b x3 yUp := by
  let n := t.n
  let k := t.k
  let bench := t.benchlen
  let zP := fformBottom n k bench v z
  let xP := fieldMul n k bench x3 zP
  let yP := fieldMul n k bench yUp zP
  have hzT : allTritList zP := prod_trits n k bench v
    (fieldMul n k bench (fieldMul n k bench v v) z) hspan hnb
  have hxT : allTritList xP := prod_trits n k bench x3 zP hspan hnb
  have hyT : allTritList yP := prod_trits n k bench yUp zP hspan hnb
  have hzL : zP.length = n := fieldMul_len n k bench v _ hnb
  have hxL : xP.length = n := fieldMul_len n k bench x3 zP hnb
  have hyL : yP.length = n := fieldMul_len n k bench yUp zP hnb
  refine ⟨xP, yP, zP, .yBench, hxL, hyL, hzL, hxT, hyT, hzT, rfl, rfl, hne, ?_, ?_, hinv⟩
  · intro h
    simpa [xP, zP, n, k, bench] using c.home0 h
  · refine ⟨c.on, c.to1, ⟨lane, c.benchArr, c.nle, ?_, c.zero⟩, c.held1, c.home2, c.held2⟩
    simpa [yP, zP, n, k, bench] using c.take

end EcbsLink2.Link2
