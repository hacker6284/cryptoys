/-
  HEAVY (not in the default build target): kernel `decide!` discharge of the
  finite checks of DoubleDealSecurity/CovariantNarrow.lean.
  * `SwapChecks` (commuting case): for each of the 51 representatives `e`, the stem
    does not commute with `swap 0 e` at `invUnkeyedNoMix (xE e)` (two stem
    evaluations: inverse, then forward).
  * `Cov0Checks` (covariant case): `goodPairsCheck` (five stem evaluations) and, for
    each `e`, `cov0Check e` (two stem evaluations: stem cell 0 of the `swap 0 e`-images
    of the identity deck and of the witness deck).
  One theorem per `e` (both checks), because kernel memory is released between
  declarations but grows with the number of stem evaluations inside one `decide!`
  (measured on the dev box: about 5.3 GB peak for the whole file process, about
  8 s per `e`, about 7 min in total). Measurements of the build, not claims.
  Built and audited by the `doubledeal-security-heavy` CI job.
  Python reproductions: `analysis/v12-covariant/swap_tail_witness.py`,
  `analysis/v12-covariant/cell0_witness.py`.
-/
import DoubleDealSecurity.CovariantNarrow

namespace DoubleDeal.Security.CovNarrow

open DoubleDeal Relabel

/-- (PROVED, kernel `decide!`) Finite check A of `Cov0Checks`. -/
theorem goodPairsCheck_ok : goodPairsCheck = true := by decide!

/-- (PROVED, kernel `decide!`) Both checks for `e = 1`. -/
theorem check_e1 : (swapCheck ⟨1, by decide⟩ && cov0Check ⟨1, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 2`. -/
theorem check_e2 : (swapCheck ⟨2, by decide⟩ && cov0Check ⟨2, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 3`. -/
theorem check_e3 : (swapCheck ⟨3, by decide⟩ && cov0Check ⟨3, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 4`. -/
theorem check_e4 : (swapCheck ⟨4, by decide⟩ && cov0Check ⟨4, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 5`. -/
theorem check_e5 : (swapCheck ⟨5, by decide⟩ && cov0Check ⟨5, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 6`. -/
theorem check_e6 : (swapCheck ⟨6, by decide⟩ && cov0Check ⟨6, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 7`. -/
theorem check_e7 : (swapCheck ⟨7, by decide⟩ && cov0Check ⟨7, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 8`. -/
theorem check_e8 : (swapCheck ⟨8, by decide⟩ && cov0Check ⟨8, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 9`. -/
theorem check_e9 : (swapCheck ⟨9, by decide⟩ && cov0Check ⟨9, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 10`. -/
theorem check_e10 : (swapCheck ⟨10, by decide⟩ && cov0Check ⟨10, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 11`. -/
theorem check_e11 : (swapCheck ⟨11, by decide⟩ && cov0Check ⟨11, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 12`. -/
theorem check_e12 : (swapCheck ⟨12, by decide⟩ && cov0Check ⟨12, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 13`. -/
theorem check_e13 : (swapCheck ⟨13, by decide⟩ && cov0Check ⟨13, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 14`. -/
theorem check_e14 : (swapCheck ⟨14, by decide⟩ && cov0Check ⟨14, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 15`. -/
theorem check_e15 : (swapCheck ⟨15, by decide⟩ && cov0Check ⟨15, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 16`. -/
theorem check_e16 : (swapCheck ⟨16, by decide⟩ && cov0Check ⟨16, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 17`. -/
theorem check_e17 : (swapCheck ⟨17, by decide⟩ && cov0Check ⟨17, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 18`. -/
theorem check_e18 : (swapCheck ⟨18, by decide⟩ && cov0Check ⟨18, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 19`. -/
theorem check_e19 : (swapCheck ⟨19, by decide⟩ && cov0Check ⟨19, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 20`. -/
theorem check_e20 : (swapCheck ⟨20, by decide⟩ && cov0Check ⟨20, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 21`. -/
theorem check_e21 : (swapCheck ⟨21, by decide⟩ && cov0Check ⟨21, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 22`. -/
theorem check_e22 : (swapCheck ⟨22, by decide⟩ && cov0Check ⟨22, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 23`. -/
theorem check_e23 : (swapCheck ⟨23, by decide⟩ && cov0Check ⟨23, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 24`. -/
theorem check_e24 : (swapCheck ⟨24, by decide⟩ && cov0Check ⟨24, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 25`. -/
theorem check_e25 : (swapCheck ⟨25, by decide⟩ && cov0Check ⟨25, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 26`. -/
theorem check_e26 : (swapCheck ⟨26, by decide⟩ && cov0Check ⟨26, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 27`. -/
theorem check_e27 : (swapCheck ⟨27, by decide⟩ && cov0Check ⟨27, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 28`. -/
theorem check_e28 : (swapCheck ⟨28, by decide⟩ && cov0Check ⟨28, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 29`. -/
theorem check_e29 : (swapCheck ⟨29, by decide⟩ && cov0Check ⟨29, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 30`. -/
theorem check_e30 : (swapCheck ⟨30, by decide⟩ && cov0Check ⟨30, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 31`. -/
theorem check_e31 : (swapCheck ⟨31, by decide⟩ && cov0Check ⟨31, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 32`. -/
theorem check_e32 : (swapCheck ⟨32, by decide⟩ && cov0Check ⟨32, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 33`. -/
theorem check_e33 : (swapCheck ⟨33, by decide⟩ && cov0Check ⟨33, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 34`. -/
theorem check_e34 : (swapCheck ⟨34, by decide⟩ && cov0Check ⟨34, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 35`. -/
theorem check_e35 : (swapCheck ⟨35, by decide⟩ && cov0Check ⟨35, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 36`. -/
theorem check_e36 : (swapCheck ⟨36, by decide⟩ && cov0Check ⟨36, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 37`. -/
theorem check_e37 : (swapCheck ⟨37, by decide⟩ && cov0Check ⟨37, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 38`. -/
theorem check_e38 : (swapCheck ⟨38, by decide⟩ && cov0Check ⟨38, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 39`. -/
theorem check_e39 : (swapCheck ⟨39, by decide⟩ && cov0Check ⟨39, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 40`. -/
theorem check_e40 : (swapCheck ⟨40, by decide⟩ && cov0Check ⟨40, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 41`. -/
theorem check_e41 : (swapCheck ⟨41, by decide⟩ && cov0Check ⟨41, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 42`. -/
theorem check_e42 : (swapCheck ⟨42, by decide⟩ && cov0Check ⟨42, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 43`. -/
theorem check_e43 : (swapCheck ⟨43, by decide⟩ && cov0Check ⟨43, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 44`. -/
theorem check_e44 : (swapCheck ⟨44, by decide⟩ && cov0Check ⟨44, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 45`. -/
theorem check_e45 : (swapCheck ⟨45, by decide⟩ && cov0Check ⟨45, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 46`. -/
theorem check_e46 : (swapCheck ⟨46, by decide⟩ && cov0Check ⟨46, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 47`. -/
theorem check_e47 : (swapCheck ⟨47, by decide⟩ && cov0Check ⟨47, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 48`. -/
theorem check_e48 : (swapCheck ⟨48, by decide⟩ && cov0Check ⟨48, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 49`. -/
theorem check_e49 : (swapCheck ⟨49, by decide⟩ && cov0Check ⟨49, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 50`. -/
theorem check_e50 : (swapCheck ⟨50, by decide⟩ && cov0Check ⟨50, by decide⟩) = true := by decide!
/-- (PROVED, kernel `decide!`) Both checks for `e = 51`. -/
theorem check_e51 : (swapCheck ⟨51, by decide⟩ && cov0Check ⟨51, by decide⟩) = true := by decide!

/-- (PROVED) Both checks for every `e ≠ 0`. -/
theorem checks_all : ∀ e : Fin 52, e ≠ 0 → (swapCheck e && cov0Check e) = true
  | ⟨0, _⟩, h => absurd rfl h
  | ⟨1, _⟩, _ => check_e1
  | ⟨2, _⟩, _ => check_e2
  | ⟨3, _⟩, _ => check_e3
  | ⟨4, _⟩, _ => check_e4
  | ⟨5, _⟩, _ => check_e5
  | ⟨6, _⟩, _ => check_e6
  | ⟨7, _⟩, _ => check_e7
  | ⟨8, _⟩, _ => check_e8
  | ⟨9, _⟩, _ => check_e9
  | ⟨10, _⟩, _ => check_e10
  | ⟨11, _⟩, _ => check_e11
  | ⟨12, _⟩, _ => check_e12
  | ⟨13, _⟩, _ => check_e13
  | ⟨14, _⟩, _ => check_e14
  | ⟨15, _⟩, _ => check_e15
  | ⟨16, _⟩, _ => check_e16
  | ⟨17, _⟩, _ => check_e17
  | ⟨18, _⟩, _ => check_e18
  | ⟨19, _⟩, _ => check_e19
  | ⟨20, _⟩, _ => check_e20
  | ⟨21, _⟩, _ => check_e21
  | ⟨22, _⟩, _ => check_e22
  | ⟨23, _⟩, _ => check_e23
  | ⟨24, _⟩, _ => check_e24
  | ⟨25, _⟩, _ => check_e25
  | ⟨26, _⟩, _ => check_e26
  | ⟨27, _⟩, _ => check_e27
  | ⟨28, _⟩, _ => check_e28
  | ⟨29, _⟩, _ => check_e29
  | ⟨30, _⟩, _ => check_e30
  | ⟨31, _⟩, _ => check_e31
  | ⟨32, _⟩, _ => check_e32
  | ⟨33, _⟩, _ => check_e33
  | ⟨34, _⟩, _ => check_e34
  | ⟨35, _⟩, _ => check_e35
  | ⟨36, _⟩, _ => check_e36
  | ⟨37, _⟩, _ => check_e37
  | ⟨38, _⟩, _ => check_e38
  | ⟨39, _⟩, _ => check_e39
  | ⟨40, _⟩, _ => check_e40
  | ⟨41, _⟩, _ => check_e41
  | ⟨42, _⟩, _ => check_e42
  | ⟨43, _⟩, _ => check_e43
  | ⟨44, _⟩, _ => check_e44
  | ⟨45, _⟩, _ => check_e45
  | ⟨46, _⟩, _ => check_e46
  | ⟨47, _⟩, _ => check_e47
  | ⟨48, _⟩, _ => check_e48
  | ⟨49, _⟩, _ => check_e49
  | ⟨50, _⟩, _ => check_e50
  | ⟨51, _⟩, _ => check_e51
  | ⟨n + 52, h⟩, _ => absurd h (by omega)

/-- (PROVED) All 51 commuting-case checks. -/
theorem swapChecks_ok : SwapChecks := fun e he =>
  (Bool.and_eq_true _ _ ▸ checks_all e he).1

/-- (PROVED) Both covariant-case checks. -/
theorem cov0Checks_ok : Cov0Checks :=
  ⟨goodPairsCheck_ok, fun e he => (Bool.and_eq_true _ _ ▸ checks_all e he).2⟩

/-- (PROVED, unconditional) No transposition of two card values commutes with the
    unkeyed v12 round body `unkeyedWithMix` (GridCycle ∘ stem) on every deck.
    Commuting case only (output relabelling = input relabelling); implied by
    `roundBody_not_covariant_swap`, kept as the separate, simpler argument. -/
theorem roundBody_not_commutes_swap (a b : Fin 52) (hab : a ≠ b) :
    ¬ CommutesOnDecks (Equiv.swap a b) unkeyedWithMix :=
  not_commutes_swap_of_check swapChecks_ok a b hab

/-- (PROVED, unconditional) The covariant round conjecture holds for every
    transposition: for all card values `a ≠ b` there is NO relabelling `τ` with
    `unkeyedWithMix (swap a b · m) = τ · unkeyedWithMix m` on every deck. This is
    the statement of `roundBody_covariant_iff_id` restricted to `σ = swap a b`; the
    general conjecture (all σ) stays open and keeps its `sorry`. -/
theorem roundBody_not_covariant_swap (a b : Fin 52) (hab : a ≠ b) :
    ¬ Covariant (Equiv.swap a b) unkeyedWithMix :=
  not_covariant_swap_of_check cov0Checks_ok a b hab

end DoubleDeal.Security.CovNarrow
