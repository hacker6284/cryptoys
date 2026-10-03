import MegaDreifachV3.Link2.RunStep

/-
  MegaDreifach v3 Link 2: `echo_colour`, `em_run` and `em_block`.
  `cardStep` keeps bijective tables and adds at most 10 to each counter; an echo adds at most
  12. Hence every run of `em_run` (52 card steps, then 26 echoes) stays below `counterCap`, and
  the `card_step_refines` side conditions hold at every iteration. `em_run_refines`: on a
  position with bijective corner and edge tables and a deal of at least 52 cards, each < 52,
  the emitted `em_run` returns the model `emRun`; both loops are driven by `chain_loop`.
-/

namespace MegaDreifachV3.Link2
open MegaDreifach MegaDreifach.Em MegaDreifach.Link2 MegaDreifachV3.Em

theorem cardStep_inj (r : Run) (hg : InjPos r.g) (base : Fin 12) (rank k : Nat) (c : Fin 12) :
    InjPos (cardStep r base rank k c).g := by
  simp only [cardStep, turnRun_g, countFind_g, countRelook_g]
  repeat (first | assumption | apply injPos_faceTurn')

theorem cardStep_counters (r : Run) (m : Nat) (hb : CountersLe r m) (base : Fin 12)
    (rank k : Nat) (hk : k ≤ 4) (c : Fin 12) :
    CountersLe (cardStep r base rank k c) (m + 10) := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := hb
  simp only [CountersLe, cardStep, turnRun_turns, turnRun_clicks, turnRun_finds, turnRun_relooks,
    turnRun_registerLooks, countFind_turns, countFind_clicks, countFind_finds, countFind_relooks,
    countFind_registerLooks, countRelook_turns, countRelook_clicks, countRelook_finds,
    countRelook_relooks, countRelook_registerLooks]
  omega

theorem dealFold_inv (l : List Nat) (r : Run) (m : Nat) (hg : InjPos r.g) (hb : CountersLe r m) :
    InjPos (l.foldl dealStep r).g ∧ CountersLe (l.foldl dealStep r) (m + 10 * l.length) := by
  induction l generalizing r m with
  | nil => exact ⟨hg, by simpa using hb⟩
  | cons a l ih =>
    have h := ih (dealStep r a) (m + 10) (cardStep_inj r hg _ _ _ _)
      (cardStep_counters r m hb _ _ _ (by omega) _)
    refine ⟨h.1, ?_⟩
    have e : m + 10 + 10 * l.length = m + 10 * (a :: l).length := by
      simp [List.length_cons]; omega
    rw [← e]; exact h.2

theorem echoRun_succ' (held n : Nat) (r : Run) :
    echoRun held (n + 1) r = echoStep held (echoRun held n r) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => exact ih (echoStep held r)

theorem echoStep_inv (held : Nat) (r : Run) (m : Nat) (hg : InjPos r.g) (hb : CountersLe r m) :
    InjPos (echoStep held r).g ∧ CountersLe (echoStep held r) (m + 12) := by
  have hb' : CountersLe (countRegisterLooks r) (m + 2) := by
    obtain ⟨b1, b2, b3, b4, b5⟩ := hb
    simp only [CountersLe, countRegisterLooks_turns, countRegisterLooks_clicks,
      countRegisterLooks_finds, countRegisterLooks_relooks, countRegisterLooks_registerLooks]
    omega
  unfold echoStep
  dsimp only
  exact ⟨cardStep_inj (countRegisterLooks r) hg _ _ _ _,
    cardStep_counters (countRegisterLooks r) _ hb' _ _ _ (by omega) _⟩

theorem echoRun_inv (held n : Nat) (r : Run) (m : Nat) (hg : InjPos r.g) (hb : CountersLe r m) :
    InjPos (echoRun held n r).g ∧ CountersLe (echoRun held n r) (m + 12 * n) := by
  induction n generalizing r m with
  | zero => exact ⟨hg, by simpa using hb⟩
  | succ n ih =>
    have h := ih (echoStep held r) (m + 12) (echoStep_inv held r m hg hb).1
      (echoStep_inv held r m hg hb).2
    refine ⟨h.1, ?_⟩
    have e : m + 12 + 12 * n = m + 12 * (n + 1) := by omega
    rw [← e]; exact h.2

theorem countersLe_mono {r : Run} {m m' : Nat} (h : CountersLe r m) (hm : m ≤ m') :
    CountersLe r m' := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := h
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem countersLe_start (h : Position) : CountersLe (startRun h) 0 := by
  simp [CountersLe, startRun]

theorem echo_colour_refines (g : Position) (hg : InjPos g) (held : Nat) :
    Megadreifach.echo_colour (embedPos g) (Int.ofNat held) =
      .ok (Int.ofNat (echoColour g held).val) := by
  unfold Megadreifach.echo_colour
  have hk1 : 1 ≤ held % 4 + 1 := by omega
  have hk4 : held % 4 + 1 ≤ 4 := by omega
  rw [card_colour_refines, ok_bind, show (4 : Int) = Int.ofNat 4 from rfl,
    modI_ofNat _ 4 (by decide), ok_bind, show (1 : Int) = Int.ofNat 1 from rfl,
    addI_ofNat _ _ (fits_of_cap (by unfold counterCap; omega)), ok_bind,
    suit_nbrs_refines _ _ hk1 hk4, ok_bind]
  dsimp only
  erw [edge_face_of_run (startRun g) hg _ _ hk1 hk4 _ (Or.inr rfl), ok_bind,
    corner_face_of_run (startRun g) hg _ _ hk1 hk4 _ (Or.inr rfl), ok_bind]
  rw [addI_ofNat _ _ (fits_of_cap (by
      have := (edgeFaceOf g (cardColour held) (suitNbrs (cardColour held) (held % 4 + 1)).1
        (suitNbrs (cardColour held) (held % 4 + 1)).1).isLt
      have := (cornerFaceOf g (cardColour held) (suitNbrs (cardColour held) (held % 4 + 1)).1
        (suitNbrs (cardColour held) (held % 4 + 1)).2
        (suitNbrs (cardColour held) (held % 4 + 1)).1).isLt
      unfold counterCap; simp only [startRun]; omega)), ok_bind,
    show (12 : Int) = Int.ofNat 12 from rfl, modI_ofNat _ 12 (by decide)]
  rfl


theorem dealPrefix_succ (deal : List Nat) (s : Run) (i : Nat) (hi : i < deal.length) :
    (deal.take (i + 1)).foldl dealStep s = dealStep ((deal.take i).foldl dealStep s) deal[i] := by
  rw [List.take_succ, List.foldl_append, List.getElem?_eq_getElem hi]
  rfl

theorem dealPrefix_inv (h : Position) (hh : InjPos h) (deal : List Nat) (i : Nat) (hi : i ≤ 52) :
    InjPos ((deal.take i).foldl dealStep (startRun h)).g ∧
      CountersLe ((deal.take i).foldl dealStep (startRun h)) 520 := by
  have := dealFold_inv (deal.take i) (startRun h) 0 hh (countersLe_start h)
  refine ⟨this.1, countersLe_mono this.2 ?_⟩
  have : (deal.take i).length ≤ i := by simp only [List.length_take]; exact Nat.min_le_left _ _
  omega

theorem em_run_refines (h : Position) (hh : InjPos h) (deal : List Nat)
    (hlen : 52 ≤ deal.length) (hcards : ∀ c ∈ deal, c < 52) :
    Megadreifach.em_run (embedPos h) (embed deal) = .ok (embedRun (emRun h deal)) := by
  unfold Megadreifach.em_run
  rw [start_run_refines, ok_bind]
  dsimp only
  rw [except_bind_pure]
  refine chain_loop _ _ _ (fun i => embedRun ((deal.take i).foldl dealStep (startRun h))) 0 51
    (by decide) ?_ _ ?_
  · intro i _ hi
    have hil : i < deal.length := by omega
    have hcard : deal[i] < 52 := hcards _ (List.getElem_mem hil)
    obtain ⟨hinj, hcnt⟩ := dealPrefix_inv h hh deal i (by omega)
    have hgt : ¬ (Int.ofNat i > (51 : Int)) := by rw [Int.ofNat_eq_coe]; omega
    have hfit : FitsLen (i + 1) := by unfold FitsLen i64MaxNat; omega
    have hadd : SudoRt.addI (Int.ofNat i) 1 = .ok (Int.ofNat (i + 1)) := addI_ofNat i 1 hfit
    have hbeq : (Int.ofNat i == 51) = decide (i = 51) := by
      rw [Int.ofNat_eq_coe]
      by_cases h : i = 51 <;> simp [h] <;> omega
    dsimp only
    rw [if_neg hgt, atL_embed deal i hil, ok_bind, show (4 : Int) = Int.ofNat 4 from rfl,
      divI_ofNat _ 4 (by decide), ok_bind, modI_ofNat _ 4 (by decide), ok_bind,
      addI_ofNat_one _ (by unfold FitsLen i64MaxNat; omega), ok_bind, card_colour_refines, ok_bind,
      show (embedRun ((deal.take i).foldl dealStep (startRun h))).sudo_3Run_4last =
        Int.ofNat ((deal.take i).foldl dealStep (startRun h)).last.val from rfl,
      card_step_refines _ hinj (countersLe_mono hcnt (by unfold counterCap; omega)) _ _ _
        (by omega) (by omega) (by omega), ok_bind,
      dealPrefix_succ deal _ i hil]
    simp only [pure_bind, hbeq, hadd, ok_bind]
    by_cases h51 : i = 51 <;> simp [h51] <;> rfl
  · have h51 : 51 < deal.length := by omega
    have hheld : deal[51] < 52 := hcards _ (List.getElem_mem h51)
    obtain ⟨hinj52, hcnt52⟩ := dealPrefix_inv h hh deal 52 (by omega)
    dsimp only
    rw [show SudoRt.atL (embed deal) 51 = .ok (Int.ofNat deal[51]) from atL_embed deal 51 h51,
      ok_bind, except_bind_pure]
    refine chain_loop _ _ _
      (fun j => embedRun (echoRun deal[51] (j - 1)
        ((deal.take 52).foldl dealStep (startRun h)))) 1 26 (by decide) ?_ _ ?_
    · intro j hj1 hj
      obtain ⟨hinj, hcnt⟩ := echoRun_inv deal[51] (j - 1)
        ((deal.take 52).foldl dealStep (startRun h)) 520 hinj52 hcnt52
      have hgt : ¬ (Int.ofNat j > (26 : Int)) := by rw [Int.ofNat_eq_coe]; omega
      have hfit : FitsLen (j + 1) := by unfold FitsLen i64MaxNat; omega
      have hadd : SudoRt.addI (Int.ofNat j) 1 = .ok (Int.ofNat (j + 1)) := addI_ofNat j 1 hfit
      have hbeq : (Int.ofNat j == 26) = decide (j = 26) := by
        rw [Int.ofNat_eq_coe]
        by_cases h : j = 26 <;> simp [h] <;> omega
      have hcnt' := hcnt
      obtain ⟨b1, b2, b3, b4, b5⟩ := hcnt'
      have hrl : CountersLe (countRegisterLooks (echoRun deal[51] (j - 1)
          ((deal.take 52).foldl dealStep (startRun h)))) counterCap := by
        simp only [CountersLe, countRegisterLooks_turns, countRegisterLooks_clicks,
          countRegisterLooks_finds, countRegisterLooks_relooks, countRegisterLooks_registerLooks,
          counterCap]
        omega
      dsimp only
      simp only [Megadreifach.echo_count]
      rw [if_neg hgt,
        show (embedRun (echoRun deal[51] (j - 1) ((deal.take 52).foldl dealStep (startRun h)))).sudo_3Run_1g =
          embedPos (echoRun deal[51] (j - 1) ((deal.take 52).foldl dealStep (startRun h))).g from rfl,
        echo_colour_refines _ hinj, ok_bind,
        count_register_looks_refines _ (fits_of_cap (by unfold counterCap; omega)), ok_bind,
        show (4 : Int) = Int.ofNat 4 from rfl,
        divI_ofNat _ 4 (by decide), ok_bind, modI_ofNat _ 4 (by decide), ok_bind,
        addI_ofNat_one _ (by unfold FitsLen i64MaxNat; omega), ok_bind,
        card_step_refines _ (by exact hinj) hrl _ _ _ (by omega) (by omega) (by omega), ok_bind,
        show j + 1 - 1 = (j - 1) + 1 by omega, echoRun_succ']
      simp only [pure_bind, hbeq, hadd, ok_bind]
      by_cases h26 : j = 26 <;> simp [h26, echoStep] <;> rfl
    · have hgd : deal.getD 51 0 = deal[51] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h51]; rfl
      dsimp only
      rw [emRun, hgd]
      rfl


theorem em_block_refines (h : Position) (hh : InjPos h) (deal : List Nat)
    (hlen : 52 ≤ deal.length) (hcards : ∀ c ∈ deal, c < 52) :
    Megadreifach.em_block (embedPos h) (embed deal) = .ok (embedPos (MegaDreifachV3.Em.emBlock h deal)) := by
  unfold Megadreifach.em_block
  rw [em_run_refines h hh deal hlen hcards, ok_bind]
  rfl

/-- `E_m` keeps bijective corner and edge tables (for the Davies–Meyer chain). -/
theorem emBlock_inj (h : Position) (hh : InjPos h) (deal : List Nat) :
    InjPos (MegaDreifachV3.Em.emBlock h deal) := by
  obtain ⟨hinj, hcnt⟩ := dealFold_inv (deal.take 52) (startRun h) 0 hh (countersLe_start h)
  exact (echoRun_inv _ echoCount _ _ hinj hcnt).1

end MegaDreifachV3.Link2
