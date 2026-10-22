/-
  After the cofactor walk the point sits in across and up. Demo skips
  `finish`. Both tiers then clear the base homes and `move_band` the point
  back. The boards stay variables: each step is a projection. Proof-only.
  Not a security claim.
-/
import EcbsLink2.Link2.ChordUp
import EcbsLink2.Link2.Place

namespace EcbsLink2.Link2

open MegaDreifach.Link2
open Ecbs

private theorem kept {α : Type} (a b : Array α) (i j : Nat) (hi : i < a.size) (v x : α)
    (hj : j < a.size) (hset : b = a.set ⟨i, hi⟩ v) (hne : i ≠ j) (h : a[j]'hj = x)
    (hk : j < b.size) : b[j]'hk = x := by
  subst hset
  rw [Array.getElem_set_ne]
  · exact h
  · exact hne

private theorem wrote {α : Type} (a b : Array α) (i : Nat) (hi : i < a.size) (v : α)
    (hset : b = a.set ⟨i, hi⟩ v) (hk : i < b.size) : b[i]'hk = v := by
  subst hset
  rw [Array.getElem_set]
  simp

private theorem open_outer {α : Type} {c a : Array α} {i : Nat} {hi : i < a.size} {v w : α}
    {j : Nat} {hj : j < (a.set ⟨i, hi⟩ v).size}
    (h : c = (a.set ⟨i, hi⟩ v).set ⟨j, hj⟩ w) (hc : j < c.size) : c[j]'hc = w := by
  subst h
  rw [Array.getElem_set]
  simp

private theorem open_inner {α : Type} {c a : Array α} {i : Nat} {hi : i < a.size} {v w : α}
    {j : Nat} {hj : j < (a.set ⟨i, hi⟩ v).size}
    (h : c = (a.set ⟨i, hi⟩ v).set ⟨j, hj⟩ w) {k : Nat} (hne : k ≠ j) (hki : k = i)
    (hc : k < c.size) : c[k]'hc = v := by
  subst hki
  subst h
  rw [Array.getElem_set_ne]
  · rw [Array.getElem_set]
    simp
  · exact Ne.symm hne

private theorem open_else {α : Type} {c a : Array α} {i : Nat} {hi : i < a.size} {v w x : α}
    {j : Nat} {hj : j < (a.set ⟨i, hi⟩ v).size}
    (h : c = (a.set ⟨i, hi⟩ v).set ⟨j, hj⟩ w) {k : Nat} (hkj : k ≠ j) (hki : k ≠ i)
    (ha : k < a.size) (hx : a[k]'ha = x) (hc : k < c.size) : c[k]'hc = x := by
  subst h
  rw [Array.getElem_set_ne]
  · rw [Array.getElem_set_ne]
    · exact hx
    · exact Ne.symm hki
  · exact Ne.symm hkj

/-- One clear. The home array and the held array are the one `set`. The bench, the slides,
    and the peak stay. Moves grow by the pegs in the cleared home. -/
private theorem clear_step (b : Board) (home : Nat) (xs : List Nat) (mv : Nat)
    (hH : home < b.sudo_5Board_4home.size) (hD : home < b.sudo_5Board_4held.size)
    (hheld : b.sudo_5Board_4held[home]'hD = true)
    (harr : b.sudo_5Board_4home[home]'hH = embed xs)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int))
    (hf : FitsLen xs.length) (hfit : FitsLen (mv + pegCount xs)) :
    ∃ b',
      clear b (home : Int) = .ok b' ∧
      b'.sudo_5Board_4home = b.sudo_5Board_4home.set ⟨home, hH⟩ (#[] : Array Int) ∧
      b'.sudo_5Board_4held = b.sudo_5Board_4held.set ⟨home, hD⟩ false ∧
      b'.sudo_5Board_8bench_on = b.sudo_5Board_8bench_on ∧
      b'.sudo_5Board_4cost.sudo_5Costs_6slides = b.sudo_5Board_4cost.sudo_5Costs_6slides ∧
      b'.sudo_5Board_4cost.sudo_5Costs_4peak = b.sudo_5Board_4cost.sudo_5Costs_4peak ∧
      b'.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat (mv + pegCount xs) := by
  let b' := { b with
    sudo_5Board_4home := b.sudo_5Board_4home.set ⟨home, hH⟩ #[]
    sudo_5Board_4held := b.sudo_5Board_4held.set ⟨home, hD⟩ false
    sudo_5Board_4cost := { b.sudo_5Board_4cost with
      sudo_5Costs_5moves := Int.ofNat (mv + pegCount xs) } }
  refine ⟨b', ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simpa [b', ofNat_eq_natCast] using
      clear_held_refines b home xs mv hH hD hheld harr hmv hf hfit

/-- Clear the two base homes, then move across into base-across and up into
    base-up. Homes 3 and 4 hold the point. Homes 0 and 1 are empty. -/
theorem point_back (b : Board) (px py bx baseY : List Nat) (mv sl pk : Nat)
    (hoff : b.sudo_5Board_8bench_on = false)
    (hszH : b.sudo_5Board_4home.size = 8) (hszD : b.sudo_5Board_4held.size = 8)
    (h0t : b.sudo_5Board_4held[0]'(by rw [hszD]; decide) = true)
    (h0a : b.sudo_5Board_4home[0]'(by rw [hszH]; decide) = embed px)
    (h1t : b.sudo_5Board_4held[1]'(by rw [hszD]; decide) = true)
    (h1a : b.sudo_5Board_4home[1]'(by rw [hszH]; decide) = embed py)
    (h3t : b.sudo_5Board_4held[3]'(by rw [hszD]; decide) = true)
    (h3a : b.sudo_5Board_4home[3]'(by rw [hszH]; decide) = embed bx)
    (h4t : b.sudo_5Board_4held[4]'(by rw [hszD]; decide) = true)
    (h4a : b.sudo_5Board_4home[4]'(by rw [hszH]; decide) = embed baseY)
    (hmv : b.sudo_5Board_4cost.sudo_5Costs_5moves = (mv : Int))
    (hsl : b.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int))
    (hpk : b.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int))
    (hfpx : FitsLen px.length) (hfpy : FitsLen py.length)
    (hfbx : FitsLen bx.length) (hfby : FitsLen baseY.length)
    (hcx : FitsLen (mv + pegCount bx))
    (hcy : FitsLen (mv + pegCount bx + pegCount baseY))
    (h2px : FitsLen (2 * pegCount px)) (h2py : FitsLen (2 * pegCount py))
    (hm1 : FitsLen (mv + pegCount bx + pegCount baseY + 2 * pegCount px))
    (hs1 : FitsLen (sl + 2 * pegCount px))
    (hm2 : FitsLen (mv + pegCount bx + pegCount baseY + 2 * pegCount px + 2 * pegCount py))
    (hs2 : FitsLen (sl + 2 * pegCount px + 2 * pegCount py)) :
    ∃ b',
      (do
          let b ← clear b base_across
          let b ← clear b base_up
          let b ← move_band b base_across across
          move_band b base_up up) = .ok b' ∧
      (∀ h : 3 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[3] = embed px) ∧
      (∀ h : 4 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[4] = embed py) ∧
      (∀ h : 0 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[0] = (#[] : Array Int)) ∧
      (∀ h : 1 < b'.sudo_5Board_4home.size, b'.sudo_5Board_4home[1] = (#[] : Array Int)) ∧
      (∀ h : 3 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[3] = true) ∧
      (∀ h : 4 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[4] = true) ∧
      (∀ h : 0 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[0] = false) ∧
      (∀ h : 1 < b'.sudo_5Board_4held.size, b'.sudo_5Board_4held[1] = false) := by
  have h3H : 3 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h3D : 3 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h4H : 4 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h4D : 4 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h0H : 0 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h0D : 0 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  have h1H : 1 < b.sudo_5Board_4home.size := by rw [hszH]; decide
  have h1D : 1 < b.sudo_5Board_4held.size := by rw [hszD]; decide
  obtain ⟨b3, hc3, hhome3, hheld3, hbench3, hsl3, hpk3, hmv3⟩ :=
    clear_step b 3 bx mv h3H h3D h3t h3a hmv hfbx hcx
  have hszH3 : b3.sudo_5Board_4home.size = 8 := by rw [hhome3, Array.size_set, hszH]
  have hszD3 : b3.sudo_5Board_4held.size = 8 := by rw [hheld3, Array.size_set, hszD]
  have h4H3 : 4 < b3.sudo_5Board_4home.size := by rw [hszH3]; decide
  have h4D3 : 4 < b3.sudo_5Board_4held.size := by rw [hszD3]; decide
  have h0H3 : 0 < b3.sudo_5Board_4home.size := by rw [hszH3]; decide
  have h0D3 : 0 < b3.sudo_5Board_4held.size := by rw [hszD3]; decide
  have h1H3 : 1 < b3.sudo_5Board_4home.size := by rw [hszH3]; decide
  have h1D3 : 1 < b3.sudo_5Board_4held.size := by rw [hszD3]; decide
  have h4a3 := kept b.sudo_5Board_4home b3.sudo_5Board_4home 3 4 h3H (#[] : Array Int)
    (embed baseY) h4H hhome3 (by decide) h4a h4H3
  have h4t3 := kept b.sudo_5Board_4held b3.sudo_5Board_4held 3 4 h3D false true h4D
    hheld3 (by decide) h4t h4D3
  have h0a3 := kept b.sudo_5Board_4home b3.sudo_5Board_4home 3 0 h3H (#[] : Array Int)
    (embed px) h0H hhome3 (by decide) h0a h0H3
  have h0t3 := kept b.sudo_5Board_4held b3.sudo_5Board_4held 3 0 h3D false true h0D
    hheld3 (by decide) h0t h0D3
  have h1a3 := kept b.sudo_5Board_4home b3.sudo_5Board_4home 3 1 h3H (#[] : Array Int)
    (embed py) h1H hhome3 (by decide) h1a h1H3
  have h1t3 := kept b.sudo_5Board_4held b3.sudo_5Board_4held 3 1 h3D false true h1D
    hheld3 (by decide) h1t h1D3
  have h3D3 : 3 < b3.sudo_5Board_4held.size := by rw [hszD3]; decide
  have h3e3 := wrote b.sudo_5Board_4held b3.sudo_5Board_4held 3 h3D false hheld3 h3D3
  obtain ⟨b4, hc4, hhome4, hheld4, hbench4, hsl4, hpk4, hmv4⟩ :=
    clear_step b3 4 baseY (mv + pegCount bx) h4H3 h4D3 h4t3 h4a3 hmv3 hfby hcy
  have hszH4 : b4.sudo_5Board_4home.size = 8 := by rw [hhome4, Array.size_set, hszH3]
  have hszD4 : b4.sudo_5Board_4held.size = 8 := by rw [hheld4, Array.size_set, hszD3]
  have h0H4 : 0 < b4.sudo_5Board_4home.size := by rw [hszH4]; decide
  have h0D4 : 0 < b4.sudo_5Board_4held.size := by rw [hszD4]; decide
  have h1H4 : 1 < b4.sudo_5Board_4home.size := by rw [hszH4]; decide
  have h1D4 : 1 < b4.sudo_5Board_4held.size := by rw [hszD4]; decide
  have h3H4 : 3 < b4.sudo_5Board_4home.size := by rw [hszH4]; decide
  have h3D4 : 3 < b4.sudo_5Board_4held.size := by rw [hszD4]; decide
  have h4D4 : 4 < b4.sudo_5Board_4held.size := by rw [hszD4]; decide
  have h0a4 := kept b3.sudo_5Board_4home b4.sudo_5Board_4home 4 0 h4H3 (#[] : Array Int)
    (embed px) h0H3 hhome4 (by decide) h0a3 h0H4
  have h0t4 := kept b3.sudo_5Board_4held b4.sudo_5Board_4held 4 0 h4D3 false true h0D3
    hheld4 (by decide) h0t3 h0D4
  have h1a4 := kept b3.sudo_5Board_4home b4.sudo_5Board_4home 4 1 h4H3 (#[] : Array Int)
    (embed py) h1H3 hhome4 (by decide) h1a3 h1H4
  have h1t4 := kept b3.sudo_5Board_4held b4.sudo_5Board_4held 4 1 h4D3 false true h1D3
    hheld4 (by decide) h1t3 h1D4
  have h3e4 := kept b3.sudo_5Board_4held b4.sudo_5Board_4held 4 3 h4D3 false false
    (by rw [hszD3]; decide) hheld4 (by decide) h3e3 h3D4
  have h4blank := wrote b3.sudo_5Board_4held b4.sudo_5Board_4held 4 h4D3 false hheld4 h4D4
  have hoff4 : b4.sudo_5Board_8bench_on = false := (hbench4.trans hbench3).trans hoff
  have hsl4' : b4.sudo_5Board_4cost.sudo_5Costs_6slides = (sl : Int) :=
    (hsl4.trans hsl3).trans hsl
  have hpk4' : b4.sudo_5Board_4cost.sudo_5Costs_4peak = (pk : Int) :=
    (hpk4.trans hpk3).trans hpk
  let mv4 := mv + pegCount bx + pegCount baseY
  have hmv4' : b4.sudo_5Board_4cost.sudo_5Costs_5moves = Int.ofNat mv4 := by
    simpa [mv4, ofNat_eq_natCast] using hmv4
  have hband1 := move_band_off b4 3 0 px mv4 sl pk hoff4 h3H4 h3D4 h0H4 h0D4
    (by rw [hszD4]; decide) (by simpa using h3e4) (by simpa using h0t4)
    (by simpa [h0a3] using h0a4) hfpx hmv4'
    (by simpa [ofNat_eq_natCast] using hsl4') (by simpa [ofNat_eq_natCast] using hpk4')
    h2px hm1 hs1
  have hbA : move_band b4 base_across across =
      .ok (moveBandBoard b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk) := by
    simpa [across, base_across] using hband1
  let bA := moveBandBoard b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk
  have hhomeA := moveBand_home b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk
  have hheldA := moveBand_held b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk
  have hmvA := moveBand_moves b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk
  have hslA := moveBand_slides b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk
  obtain ⟨pkA, hpkA⟩ := moveBand_peak_nat b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk
    (by simpa [ofNat_eq_natCast] using hpk4')
  have hoffA : bA.sudo_5Board_8bench_on = false := by
    dsimp only [bA]; rw [ moveBand_on b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk, hoff4]
  have hszHA : bA.sudo_5Board_4home.size = 8 := by
    dsimp only [bA]; rw [ hhomeA, Array.size_set, Array.size_set, hszH4]
  have hszDA : bA.sudo_5Board_4held.size = 8 := by
    dsimp only [bA]; rw [ hheldA, Array.size_set, Array.size_set, hszD4]
  have h1HA : 1 < bA.sudo_5Board_4home.size := by rw [hszHA]; decide
  have h1DA : 1 < bA.sudo_5Board_4held.size := by rw [hszDA]; decide
  have h4HA : 4 < bA.sudo_5Board_4home.size := by rw [hszHA]; decide
  have h4DA : 4 < bA.sudo_5Board_4held.size := by rw [hszDA]; decide
  have h1q : bA.sudo_5Board_4home[1]? = some (embed py) := by
    have harr : bA.sudo_5Board_4home =
        (moveBandBoard b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk).sudo_5Board_4home := rfl
    rw [harr, hhomeA]
    simp
    simpa [Array.getElem?_eq_getElem h1H4] using h1a4
  have h1aA : bA.sudo_5Board_4home[1]'h1HA = embed py := by
    simpa [Array.getElem?_eq_getElem h1HA] using h1q
  have h1tq : bA.sudo_5Board_4held[1]? = some true := by
    have harr : bA.sudo_5Board_4held =
        (moveBandBoard b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk).sudo_5Board_4held := rfl
    rw [harr, hheldA]
    simp
    simpa [Array.getElem?_eq_getElem h1D4] using h1t4
  have h1tA : bA.sudo_5Board_4held[1]'h1DA = true := by
    simpa [Array.getElem?_eq_getElem h1DA] using h1tq
  have h4eq : bA.sudo_5Board_4held[4]? = some false := by
    have harr : bA.sudo_5Board_4held =
        (moveBandBoard b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk).sudo_5Board_4held := rfl
    rw [harr, hheldA]
    simp
    simpa [Array.getElem?_eq_getElem h4D4] using h4blank
  have h4eA : bA.sudo_5Board_4held[4]'h4DA = false := by
    simpa [Array.getElem?_eq_getElem h4DA] using h4eq
  have hmvAn : bA.sudo_5Board_4cost.sudo_5Costs_5moves =
      Int.ofNat (mv4 + 2 * pegCount px) := by dsimp only [bA]; exact hmvA
  have hslAn : bA.sudo_5Board_4cost.sudo_5Costs_6slides =
      Int.ofNat (sl + 2 * pegCount px) := by dsimp only [bA]; exact hslA
  have hband2 := move_band_off bA 4 1 py (mv4 + 2 * pegCount px) (sl + 2 * pegCount px) pkA
    hoffA h4HA h4DA h1HA h1DA (by rw [hszDA]; decide) h4eA h1tA h1aA hfpy
    hmvAn hslAn hpkA h2py hm2 hs2
  have hbU : move_band bA base_up up =
      .ok (moveBandBoard bA 4 1 h1HA h1DA h4HA h4DA py (mv4 + 2 * pegCount px)
        (sl + 2 * pegCount px) pkA) := by
    simpa [up, base_up] using hband2
  let bU := moveBandBoard bA 4 1 h1HA h1DA h4HA h4DA py (mv4 + 2 * pegCount px)
    (sl + 2 * pegCount px) pkA
  have hhomeU := moveBand_home bA 4 1 h1HA h1DA h4HA h4DA py (mv4 + 2 * pegCount px)
    (sl + 2 * pegCount px) pkA
  have hheldU := moveBand_held bA 4 1 h1HA h1DA h4HA h4DA py (mv4 + 2 * pegCount px)
    (sl + 2 * pegCount px) pkA
  have hdo :
      (do
          let b ← clear b base_across
          let b ← clear b base_up
          let b ← move_band b base_across across
          move_band b base_up up) = .ok bU := by
    rw [show base_across = (3 : Int) from rfl]
    rw [show base_up = (4 : Int) from rfl]
    rw [show across = (0 : Int) from rfl]
    rw [show up = (1 : Int) from rfl]
    erw [hc3]
    rw [ok_bind]
    erw [hc4]
    rw [ok_bind]
    erw [hbA]
    rw [ok_bind]
    exact hbU
  have hAU : bA.sudo_5Board_4home =
      (moveBandBoard b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk).sudo_5Board_4home := rfl
  have hAUh : bA.sudo_5Board_4held =
      (moveBandBoard b4 3 0 h0H4 h0D4 h3H4 h3D4 px mv4 sl pk).sudo_5Board_4held := rfl
  have hUU : bU.sudo_5Board_4home =
      (moveBandBoard bA 4 1 h1HA h1DA h4HA h4DA py (mv4 + 2 * pegCount px)
        (sl + 2 * pegCount px) pkA).sudo_5Board_4home := rfl
  have hUUh : bU.sudo_5Board_4held =
      (moveBandBoard bA 4 1 h1HA h1DA h4HA h4DA py (mv4 + 2 * pegCount px)
        (sl + 2 * pegCount px) pkA).sudo_5Board_4held := rfl
  have hAhome := hAU.trans hhomeA
  have hAheld := hAUh.trans hheldA
  have hUhome := hUU.trans hhomeU
  have hUheld := hUUh.trans hheldU
  have h3A : 3 < bA.sudo_5Board_4home.size := by rw [hszHA]; decide
  have h0A : 0 < bA.sudo_5Board_4home.size := by rw [hszHA]; decide
  have h3Ah : 3 < bA.sudo_5Board_4held.size := by rw [hszDA]; decide
  have h0Ah : 0 < bA.sudo_5Board_4held.size := by rw [hszDA]; decide
  have hA3 := open_outer hAhome h3A
  have hA0 := open_inner hAhome (by decide : (0 : Nat) ≠ 3) rfl h0A
  have hA0h := open_inner hAheld (by decide : (0 : Nat) ≠ 3) rfl h0Ah
  have hA3h := open_outer hAheld h3Ah
  refine ⟨bU, hdo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact open_else hUhome (by decide : (3 : Nat) ≠ 4) (by decide) h3A hA3 h
  · intro h
    exact open_outer hUhome h
  · intro h
    exact open_else hUhome (by decide : (0 : Nat) ≠ 4) (by decide) h0A hA0 h
  · intro h
    exact open_inner hUhome (by decide : (1 : Nat) ≠ 4) rfl h
  · intro h
    exact open_else hUheld (by decide : (3 : Nat) ≠ 4) (by decide) h3Ah hA3h h
  · intro h
    exact open_outer hUheld h
  · intro h
    exact open_else hUheld (by decide : (0 : Nat) ≠ 4) (by decide) h0Ah hA0h h
  · intro h
    exact open_inner hUheld (by decide : (1 : Nat) ≠ 4) rfl h

end EcbsLink2.Link2
