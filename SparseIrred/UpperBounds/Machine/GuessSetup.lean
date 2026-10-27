import SparseIrred.UpperBounds.Machine.GuessPipeline

/-!
# A deterministic setup prefix for the fixed-length guessing machine

Counter construction and input rewind do not inspect the random choices. Their
common endpoint therefore determines a fixed schedule for all subsequent random
writing steps, independently of the computation path.
-/

namespace SparseIrred.UpperBounds.Machine

open Complexity Complexity.NTM Complexity.SAT

variable {k : ℕ}

set_option backward.isDefEq.respectTransparency false

/-- The coarse phase order of the concrete guess-and-verify pipeline. -/
def guessPipelinePhaseRank {Q : Type} : GuessVerifyPhase Q → ℕ
  | .counter _ => 0
  | .rewindInput _ => 1
  | .guess _ => 2
  | .pair _ => 3
  | .verify _ => 4

theorem satGuessVerify_phaseRank_trace_one (M : TM k) (b : Bool)
    (c : Cfg (k + 3) (GuessVerifyPhase M.Q)) :
    guessPipelinePhaseRank c.state ≤
      guessPipelinePhaseRank ((satGuessVerifyNTM M).trace 1 (fun _ ↦ b) c).state := by
  rcases c with ⟨q, inp, work, out⟩
  cases q <;>
    simp [NTM.trace, satGuessVerifyNTM, satGuessVerifyDelta, guessPipelinePhaseRank,
      satVerifyTransition, phaseBoundary] <;>
    split_ifs <;> simp

theorem satGuessVerify_phaseRank_trace (M : TM k) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg (k + 3) (GuessVerifyPhase M.Q)) :
    guessPipelinePhaseRank c.state ≤
      guessPipelinePhaseRank ((satGuessVerifyNTM M).trace T choices c).state := by
  induction T generalizing c with
  | zero => exact le_rfl
  | succ T ih =>
      rw [NTM.trace_succ]
      exact (satGuessVerify_phaseRank_trace_one M _ c).trans (ih _ _)

/-- Before guessing starts, a single transition ignores both supplied choice bits. -/
theorem fixedGuessVerify_trace_one_setup (M : TM k) (b₁ b₂ : Bool)
    (c : Cfg (k + 3) (GuessVerifyPhase M.Q))
    (hc : guessPipelinePhaseRank c.state ≤ 1) :
    (fixedGuessVerifyNTM M).trace 1 (fun _ ↦ b₁) c =
      (satGuessVerifyNTM M).trace 1 (fun _ ↦ b₂) c := by
  rcases c with ⟨q, inp, work, out⟩
  cases q <;> simp [guessPipelinePhaseRank] at hc
  all_goals
    simp [NTM.trace, fixedGuessVerifyNTM, satGuessVerifyNTM, satGuessVerifyDelta,
      pipelineChoice]

/-- An endpoint still in counter/rewind ensures that the entire prefix is deterministic. -/
theorem fixedGuessVerify_trace_setup_eq (M : TM k) (T : ℕ)
    (reference choices : Fin T → Bool) (c : Cfg (k + 3) (GuessVerifyPhase M.Q))
    (hfinal : guessPipelinePhaseRank
      ((satGuessVerifyNTM M).trace T reference c).state ≤ 1) :
    (fixedGuessVerifyNTM M).trace T choices c =
      (satGuessVerifyNTM M).trace T reference c := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
      have hc := (satGuessVerify_phaseRank_trace M (T + 1) reference c).trans hfinal
      rw [NTM.trace_succ] at hfinal
      rw [NTM.trace_succ (fixedGuessVerifyNTM M), NTM.trace_succ (satGuessVerifyNTM M)]
      rw [fixedGuessVerify_trace_one_setup M _ (reference ⟨0, by omega⟩) c hc]
      exact ih _ _ _ hfinal

/-- Rewind has a single time and endpoint for every choice sequence, preserving all frames. -/
theorem fixedGuessVerify_rewind_uniform (M : TM k) (B : ℕ) (x : List Bool)
    (inp : Tape) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre : inp.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧ inp.head ≤ B)
    (hinput : inp.cells = (Tape.init (x.map Γ.ofBool)).cells)
    (hout : out.read ≠ Γ.start ∧ out.head ≥ 1)
    (hwork : ∀ i, (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) :
    ∃ t ≤ B + 2, ∀ choices : Fin (t + 1) → Bool,
      (fixedGuessVerifyNTM M).trace (t + 1) choices
        (satRewindInputWrap M { state := .moveLeft, input := inp, work := work, output := out }) =
        satGuessWrap M
          { state := NTM.GuessBoundedPhase.choose,
            input := (Tape.init (x.map Γ.ofBool)).move .right, work := work, output := out } := by
  let P : Tape → (Fin (k + 3) → Tape) → Tape → Prop :=
    fun _ w o ↦ w = work ∧ o = out
  have hP : ∀ (i₀ : Tape) (w₀ : Fin (k + 3) → Tape) (o₀ : Tape)
      (i₁ : Tape) (w₁ : Fin (k + 3) → Tape) (o₁ : Tape),
      P i₀ w₀ o₀ → i₁.cells = i₀.cells → i₁.head = 1 → w₁ = w₀ → o₁ = o₀ →
      P i₁ w₁ o₁ := by
    intro _ w₀ o₀ _ w₁ o₁ hp _ _ hw ho
    exact ⟨hw.trans hp.1, ho.trans hp.2⟩
  have hrewind := TM.rewindInputTM_toNTM_hoareTime_frame (n := k + 3) B (P := P) hP
  have hpreRich : inp.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → inp.cells j ≠ Γ.start) ∧ inp.head ≤ B ∧
      out.read ≠ Γ.start ∧ out.head ≥ 1 ∧
      (∀ i, (work i).read ≠ Γ.start ∧ (work i).head ≥ 1) ∧ P inp work out :=
    ⟨hpre.1, hpre.2.1, hpre.2.2, hout.1, hout.2, hwork, rfl, rfl⟩
  obtain ⟨t, ht, hhalt, hpost, hfirst⟩ :=
    hrewind.exists_first_halt_time_with_post
      (inp := inp) (work := work) (out := out) hpreRich (fun _ ↦ false)
  let c₀ : Cfg (k + 3) TM.RewindPhase :=
    { state := .moveLeft, input := inp, work := work, output := out }
  let rewind := (TM.rewindInputTM (n := k + 3)).toNTM
  let cT := rewind.trace t (fun _ ↦ false) c₀
  have hdone : cT.state = .done := hhalt
  have hnot : ∀ s (hs : s < t),
      (rewind.trace s (fun _ ↦ false) c₀).state ≠ .done := by
    intro s hs
    exact hfirst s hs
  have hprefix : (satGuessVerifyNTM M).trace t (fun _ ↦ false)
      (satRewindInputWrap M c₀) = satRewindInputWrap M cT :=
    satGuessVerify_rewindInput_trace_prefix M t (fun _ ↦ false) c₀ hnot
  have hexit := satGuessVerify_rewindInput_trace_exit M t (fun _ ↦ false) c₀ hnot hdone
  change (satGuessVerifyNTM M).trace (t + 1) (fun _ ↦ false)
      (satRewindInputWrap M c₀) = satGuessWrap M
        { state := NTM.GuessBoundedPhase.choose, input := satBoundaryInput cT.input,
          work := satBoundaryWork cT.work, output := satBoundaryOutput cT.output } at hexit
  rw [NTM.trace_snoc, hprefix] at hexit
  have hpost' : cT.input.head = 1 ∧ cT.work = work ∧ cT.output = out := hpost
  have hcells : cT.input.cells = inp.cells := NTM.input_cells_trace rewind t (fun _ ↦ false) c₀
  have hnostart : ∀ j, j ≥ 1 → cT.input.cells j ≠ Γ.start := by
    rw [hcells]
    exact hpre.2.1
  have hinputT : satBoundaryInput cT.input = (Tape.init (x.map Γ.ofBool)).move .right := by
    rw [satBoundaryInput_stable cT.input (by omega) hnostart]
    have hhead : cT.input.head = ((Tape.init (x.map Γ.ofBool)).move .right).head := by
      simpa [Tape.move, Tape.init] using hpost'.1
    have hcell : cT.input.cells = ((Tape.init (x.map Γ.ofBool)).move .right).cells := by
      simpa only [Tape.move_cells] using hcells.trans hinput
    cases h₁ : cT.input
    cases h₂ : (Tape.init (x.map Γ.ofBool)).move .right
    simp only [h₁, h₂] at hhead hcell
    simp_all
  have hworkT : satBoundaryWork cT.work = work := by
    rw [hpost'.2.1]
    funext i
    exact satBoundaryWork_stable_of_read_ne_start work i (hwork i).1
  have houtT : satBoundaryOutput cT.output = out := by
    rw [hpost'.2.2]
    exact satBoundaryOutput_stable_of_read_ne_start out hout.1
  rw [hinputT, hworkT, houtT] at hexit
  refine ⟨t, ht, ?_⟩
  intro choices
  have hrank : guessPipelinePhaseRank
      ((satGuessVerifyNTM M).trace t (fun _ ↦ false) (satRewindInputWrap M c₀)).state ≤ 1 := by
    rw [hprefix]
    exact le_rfl
  rw [NTM.trace_snoc]
  rw [fixedGuessVerify_trace_setup_eq M t (fun _ ↦ false) _ _ hrank, hprefix]
  rw [fixedGuessVerify_trace_one_setup M _ false _ (by exact le_rfl)]
  exact hexit

/-- All computation paths enter guessing at one common time with the same tapes. -/
theorem fixedGuessVerify_setup_uniform (M : TM k) (x : List Bool) :
    ∃ t₀ ≤ 2 * TM.inputLengthPlusOneCounterTime x.length + 5,
      ∃ cGuess : Cfg (k + 3) GuessBoundedPhase,
        (∀ choices : Fin t₀ → Bool,
          (fixedGuessVerifyNTM M).trace t₀ choices ((fixedGuessVerifyNTM M).initCfg x) =
            satGuessWrap M cGuess) ∧
        cGuess.state = GuessBoundedPhase.choose ∧
        cGuess.input = (Tape.init (x.map Γ.ofBool)).move Dir3.right ∧
        (cGuess.work (satCounterIdx k)).HasUnaryCounter (x.length + 1) ∧
        (∀ i, i ≠ satCounterIdx k → cGuess.work i = (Tape.init []).move Dir3.right) ∧
        cGuess.output = (Tape.init []).move Dir3.right := by
  let C := TM.inputLengthPlusOneCounterTime x.length
  obtain ⟨tc, htc, hcounter⟩ := satGuessVerify_counter_init_exits M x (fun _ ↦ false)
  let counter := (TM.inputLengthPlusOneCounterTM (satCounterIdx k)).toNTM
  let c₀ : Cfg (k + 3) TM.LinearCounterPhase :=
    { state := .scan, input := Tape.init (x.map Γ.ofBool),
      work := fun _ ↦ Tape.init [], output := Tape.init [] }
  let cC := counter.trace tc (fun _ ↦ false) c₀
  let inpR := satBoundaryInput cC.input
  let workR := satBoundaryWork cC.work
  let outR := satBoundaryOutput cC.output
  have hcounter' :
      (satGuessVerifyNTM M).trace (tc + 1) (fun _ ↦ false)
        ((satGuessVerifyNTM M).initCfg x) =
        satRewindInputWrap M
          { state := .moveLeft, input := inpR, work := workR, output := outR } ∧
      inpR.cells 0 = Γ.start ∧
      (∀ j, j ≥ 1 → inpR.cells j ≠ Γ.start) ∧
      inpR.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      inpR.head ≤ C + 1 ∧
      (workR (satCounterIdx k)).HasUnaryCounter (x.length + 1) ∧
      (∀ i, i ≠ satCounterIdx k → workR i = (Tape.init []).move Dir3.right) ∧
      workR (satWitnessIdx k) = (Tape.init []).move Dir3.right ∧
      workR (satPairIdx k) = (Tape.init []).move Dir3.right ∧
      outR = (Tape.init []).move Dir3.right := by
    simpa only [C, counter, c₀, cC, inpR, workR, outR] using hcounter
  obtain ⟨htraceC, hzero, hns, hcells, hhead, hcounterW, hothers, _, _, hout⟩ := hcounter'
  have houtputR : outR.read ≠ Γ.start ∧ outR.head ≥ 1 := by
    rw [hout]
    constructor <;> simp [Tape.read, Tape.move, Tape.init]
  have hworkR : ∀ i, (workR i).read ≠ Γ.start ∧ (workR i).head ≥ 1 := by
    intro i
    by_cases hi : i = satCounterIdx k
    · subst i
      constructor
      · rw [Tape.hasUnaryCounter_read_pos hcounterW (by omega)]
        simp
      · rw [hcounterW.1]
    · rw [hothers i hi]
      constructor <;> simp [Tape.read, Tape.move, Tape.init]
  obtain ⟨tr, htr, hrewind⟩ := fixedGuessVerify_rewind_uniform M (C + 1) x inpR workR outR
    ⟨hzero, hns, hhead⟩ hcells houtputR hworkR
  let cGuess : Cfg (k + 3) GuessBoundedPhase :=
    { state := GuessBoundedPhase.choose,
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right, work := workR, output := outR }
  refine ⟨(tc + 1) + (tr + 1), by dsimp only [C] at *; omega, cGuess, ?_,
    rfl, rfl, hcounterW, hothers, hout⟩
  intro choices
  have hrank : guessPipelinePhaseRank
      ((satGuessVerifyNTM M).trace (tc + 1) (fun _ ↦ false)
        ((satGuessVerifyNTM M).initCfg x)).state ≤ 1 := by
    rw [htraceC]
    exact le_rfl
  rw [NTM.trace_add]
  erw [fixedGuessVerify_trace_setup_eq M (tc + 1) (fun _ ↦ false) _ _ hrank, htraceC]
  exact hrewind _

end SparseIrred.UpperBounds.Machine
