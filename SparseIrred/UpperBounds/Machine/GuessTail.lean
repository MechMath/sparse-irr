import SparseIrred.UpperBounds.Machine.GuessPipeline

/-! # Deterministic verification after fixed guessing -/

namespace SparseIrred.UpperBounds.Machine

open Complexity Complexity.NTM Complexity.SAT

variable {k : ℕ}

set_option backward.isDefEq.respectTransparency false

/-- Pair construction and verification never return to the random-guess phase. -/
def InVerifierSuffix {Q : Type} : GuessVerifyPhase Q → Prop
  | .pair _ => True
  | .verify _ => True
  | _ => False

private theorem verifierSuffix_step (M : TM k) (choice : Bool)
    (c : Cfg (k + 3) (GuessVerifyPhase M.Q)) (hc : InVerifierSuffix c.state) :
    InVerifierSuffix ((satGuessVerifyNTM M).trace 1 (fun _ ↦ choice) c).state := by
  cases c with
  | mk state inp work out =>
      cases state with
      | counter _ => exact False.elim hc
      | rewindInput _ => exact False.elim hc
      | guess _ => exact False.elim hc
      | pair q =>
          by_cases hq : q = TM.PairBuildPhase.done <;>
            simp [NTM.trace, satGuessVerifyNTM, satGuessVerifyDelta, InVerifierSuffix,
              phaseBoundary, hq]
      | verify q =>
          by_cases hq : q = M.qhalt <;>
            simp [NTM.trace, satGuessVerifyNTM, satGuessVerifyDelta, satVerifyTransition,
              InVerifierSuffix, hq]

/-- The original pipeline stays within its deterministic suffix. -/
theorem verifierSuffix_trace (M : TM k) (T : ℕ) (choices : Fin T → Bool)
    (c : Cfg (k + 3) (GuessVerifyPhase M.Q)) (hc : InVerifierSuffix c.state) :
    InVerifierSuffix ((satGuessVerifyNTM M).trace T choices c).state := by
  apply NTM.trace_invariant (satGuessVerifyNTM M) T choices c
    (fun _ current ↦ InVerifierSuffix current.state) hc
  intro time htime current hcurrent
  exact verifierSuffix_step M _ current hcurrent

/-- The fixed-guess modification leaves the entire pair/verifier suffix unchanged. -/
theorem fixedGuessVerifyNTM_suffix_eq (M : TM k) (T : ℕ) (choices : Fin T → Bool)
    (c : Cfg (k + 3) (GuessVerifyPhase M.Q)) (hc : InVerifierSuffix c.state) :
    (fixedGuessVerifyNTM M).trace T choices c = (satGuessVerifyNTM M).trace T choices c := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [NTM.trace_snoc (fixedGuessVerifyNTM M) T,
        NTM.trace_snoc (satGuessVerifyNTM M) T, ih]
      rw [fixedGuessVerifyNTM_trace_one]
      have hcurrent := verifierSuffix_trace M T (fun i ↦ choices i.castSucc) c hc
      have hchoice : pipelineChoice M
          ((satGuessVerifyNTM M).trace T (fun i ↦ choices i.castSucc) c).state
          (choices (Fin.last T)) = choices (Fin.last T) := by
        generalize ((satGuessVerifyNTM M).trace T (fun i ↦ choices i.castSucc) c).state = q
          at hcurrent ⊢
        cases q <;> simp_all [InVerifierSuffix, pipelineChoice]
      rw [hchoice]

/-- Once the guessed string is staged, the actual pipeline computes the
deterministic verifier's answer and halts within its uniform suffix budget. -/
theorem fixedGuessVerifyNTM_pair_start_decides (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f)
    (x y : List Bool) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre : work (satWitnessIdx k) = (Tape.init (y.map Γ.ofBool)).move Dir3.right ∧
      work (satPairIdx k) = (Tape.init []).move Dir3.right)
    (hout : out = (Tape.init []).move Dir3.right)
    (hwork : ∀ i : Fin k, work (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right)
    (hlen : y.length ≤ x.length + 1)
    (choices : Fin (TM.pairBuildTime x.length (x.length + 1) +
      satVerifierWindowTime f x.length) → Bool) :
    let c0 : Cfg (k + 3) TM.PairBuildPhase :=
      { state := .init, input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
        work := work, output := out }
    let result := (fixedGuessVerifyNTM M).trace
      (TM.pairBuildTime x.length (x.length + 1) + satVerifierWindowTime f x.length)
      choices (satPairWrap M c0)
    (fixedGuessVerifyNTM M).halted result ∧
      ((pair x y ∈ L → result.output.cells 1 = Γ.one) ∧
        (pair x y ∉ L → result.output.cells 1 = Γ.zero)) := by
  dsimp only
  rw [fixedGuessVerifyNTM_suffix_eq M _ choices _ (by trivial)]
  exact satGuessVerify_pair_start_decides_within_bound_of_decidesInTime M hM x y work out
    hpre hout hwork hlen choices

/-- The full machine simulates fixed guessing up to its first halt. -/
theorem fixedGuessVerifyNTM_guess_trace_prefix (M : TM k) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg (k + 3) GuessBoundedPhase)
    (hnot : ∀ t (ht : t < T),
      ((guessFixedNTM (satWitnessIdx k) (satCounterIdx k)).trace t
        (fun i ↦ choices ⟨i.val, Nat.lt_trans i.isLt ht⟩) c).state ≠ .done) :
    (fixedGuessVerifyNTM M).trace T choices (satGuessWrap M c) =
      satGuessWrap M
        ((guessFixedNTM (satWitnessIdx k) (satCounterIdx k)).trace T choices c) := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [NTM.trace_snoc (fixedGuessVerifyNTM M) T,
        NTM.trace_snoc (guessFixedNTM (satWitnessIdx k) (satCounterIdx k)) T]
      have hp := ih (fun i ↦ choices i.castSucc) (by
        intro t ht
        exact hnot t (by omega))
      rw [hp]
      apply fixedGuessVerifyNTM_guess_trace_one
      exact hnot T (Nat.lt_succ_self T)

/-- The step after the fixed-guess subroutine halts enters pair construction. -/
theorem fixedGuessVerifyNTM_guess_trace_exit (M : TM k) (T : ℕ)
    (choices : Fin (T + 1) → Bool) (c : Cfg (k + 3) GuessBoundedPhase)
    (hnot : ∀ t (ht : t < T),
      ((guessFixedNTM (satWitnessIdx k) (satCounterIdx k)).trace t
        (fun i ↦ choices ⟨i.val, by omega⟩) c).state ≠ .done)
    (hdone : ((guessFixedNTM (satWitnessIdx k) (satCounterIdx k)).trace T
      (fun i ↦ choices ⟨i.val, by omega⟩) c).state = .done) :
    let result := (guessFixedNTM (satWitnessIdx k) (satCounterIdx k)).trace T
      (fun i ↦ choices ⟨i.val, by omega⟩) c
    (fixedGuessVerifyNTM M).trace (T + 1) choices (satGuessWrap M c) =
      satPairWrap M
        { state := .init, input := satBoundaryInput result.input,
          work := satBoundaryWork result.work, output := satBoundaryOutput result.output } := by
  have hp := fixedGuessVerifyNTM_guess_trace_prefix M T (fun i ↦ choices i.castSucc) c
    (by intro t ht; exact hnot t ht)
  dsimp only
  rw [NTM.trace_snoc, hp, fixedGuessVerifyNTM_trace_one]
  have hd : ((guessFixedNTM (satWitnessIdx k) (satCounterIdx k)).trace T
      (fun i ↦ choices i.castSucc) c).state = .done := hdone
  simp only [satGuessWrap, hd, pipelineChoice]
  exact satGuessVerify_guess_done_trace_one M _ _ _ _

/-- A uniform bound for fixed guessing, the phase handoff, pairing, and verification. -/
def fixedGuessTailTime (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  3 * (n + 1) + 4 +
    (TM.pairBuildTime n (n + 1) + satVerifierWindowTime f n)

/-- From the prepared guess-phase configuration, the complete machine decides
the deterministic verifier on precisely the uniformly selected fixed-length seed. -/
theorem fixedGuessVerifyNTM_guess_start_decides (M : TM k)
    {L : Language} {f : ℕ → ℕ} (hM : M.DecidesInTime L f)
    (x : List Bool) (work : Fin (k + 3) → Tape) (out : Tape)
    (hpre : (work (satWitnessIdx k)).HasBinaryPrefix [] ∧
      (work (satWitnessIdx k)).cells 0 = Γ.start ∧
      (work (satCounterIdx k)).HasUnaryCounter (x.length + 1))
    (hpair : work (satPairIdx k) = (Tape.init []).move Dir3.right)
    (hout : out = (Tape.init []).move Dir3.right)
    (hwork : ∀ i : Fin k, work (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right)
    (choices : ℕ → Bool) :
    let y := fixedGuessBits (x.length + 1) choices
    let c0 : Cfg (k + 3) GuessBoundedPhase :=
      { state := .choose, input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
        work := work, output := out }
    let result := (fixedGuessVerifyNTM M).trace (fixedGuessTailTime f x.length)
      (fun i ↦ choices i.val) (satGuessWrap M c0)
    (fixedGuessVerifyNTM M).halted result ∧
      ((pair x y ∈ L → result.output.cells 1 = Γ.one) ∧
        (pair x y ∉ L → result.output.cells 1 = Γ.zero)) := by
  let B := x.length + 1
  let G := 3 * B + 3
  let S := TM.pairBuildTime x.length (x.length + 1) + satVerifierWindowTime f x.length
  let guessTM := guessFixedNTM (satWitnessIdx k) (satCounterIdx k)
  let c0 : Cfg (k + 3) GuessBoundedPhase :=
    { state := .choose, input := (Tape.init (x.map Γ.ofBool)).move Dir3.right,
      work := work, output := out }
  let y := fixedGuessBits B choices
  have hguess := guessFixedNTM_halts_with_bits (satWitnessIdx k) (satCounterIdx k)
    (Ne.symm (satCounterIdx_ne_witnessIdx k)) B c0 rfl hpre.1 hpre.2.1 hpre.2.2 choices
  obtain ⟨t, ht, hhalt, hfirst⟩ := guessTM.exists_first_halt_time_of_trace_halted G
    (fun i ↦ choices i.val) c0 hguess.1
  let cT := guessTM.trace t (fun i ↦ choices i.val) c0
  have hfrozen : guessTM.trace G (fun i ↦ choices i.val) c0 = cT :=
    guessTM.trace_mono ht (fun _ ↦ rfl) hhalt
  have hguessT : guessTM.halted cT ∧ (cT.work (satWitnessIdx k)).HasBinaryString y ∧
      (cT.work (satWitnessIdx k)).cells 0 = Γ.start := by
    change guessTM.halted (guessTM.trace G (fun i ↦ choices i.val) c0) ∧ _ at hguess
    rw [hfrozen] at hguess
    exact hguess
  have hwitnessT : cT.work (satWitnessIdx k) =
      (Tape.init (y.map Γ.ofBool)).move Dir3.right :=
    Tape.eq_init_move_right_of_hasBinaryString hguessT.2.1 hguessT.2.2
  let pairWork := satBoundaryWork cT.work
  have hinputTrace : cT.input = c0.input :=
    guessFixedNTM_preserves_input _ _ t _ c0
      (Tape.init_ofBool_move_right_cells_ne_start x 1 (by omega))
  have hinputBoundary : satBoundaryInput cT.input = c0.input := by
    rw [hinputTrace]
    exact satBoundaryInput_stable c0.input (by simp [c0, Tape.move, Tape.init])
      (Tape.init_ofBool_move_right_cells_ne_start x)
  have houtputTrace : cT.output = out :=
    guessFixedNTM_preserves_output _ _ t _ c0 (by simp [c0, hout, Tape.read, Tape.move, Tape.init])
  have houtputBoundary : satBoundaryOutput cT.output = out := by
    rw [houtputTrace]
    exact satBoundaryOutput_stable_of_read_ne_start out
      (by simp [hout, Tape.read, Tape.move, Tape.init])
  have hother : ∀ i : Fin (k + 3), i ≠ satWitnessIdx k → i ≠ satCounterIdx k →
      work i = (Tape.init []).move Dir3.right →
      pairWork i = (Tape.init []).move Dir3.right := by
    intro i hiw hic hi
    have htrace : cT.work i = work i := guessFixedNTM_preserves_other_work _ _ i t _ c0
      hiw hic (by simp [c0, hi, Tape.read, Tape.move, Tape.init])
    have hread : (cT.work i).read ≠ Γ.start := by
      rw [htrace, hi]
      simp [Tape.read, Tape.move, Tape.init]
    exact (satBoundaryWork_stable_of_read_ne_start _ i hread).trans (htrace.trans hi)
  have hwitnessBoundary : pairWork (satWitnessIdx k) =
      (Tape.init (y.map Γ.ofBool)).move Dir3.right := by
    have hread : (cT.work (satWitnessIdx k)).read ≠ Γ.start := by
      rw [hwitnessT]
      exact Tape.init_ofBool_move_right_cells_ne_start y 1 (by omega)
    exact (satBoundaryWork_stable_of_read_ne_start _ _ hread).trans hwitnessT
  have hpairBoundary := hother (satPairIdx k) (Ne.symm (satWitnessIdx_ne_pairIdx k))
    (Ne.symm (satCounterIdx_ne_pairIdx k)) hpair
  have hworkBoundary : ∀ i : Fin k, pairWork (satVerifierWorkIdx i) =
      (Tape.init []).move Dir3.right := fun i ↦
    hother _ (satVerifierWorkIdx_ne_witnessIdx i) (satVerifierWorkIdx_ne_counterIdx i) (hwork i)
  let cPair : Cfg (k + 3) TM.PairBuildPhase :=
    { state := .init, input := c0.input, work := pairWork, output := out }
  have hexit : (fixedGuessVerifyNTM M).trace (t + 1) (fun i ↦ choices i.val)
      (satGuessWrap M c0) = satPairWrap M cPair := by
    have he := fixedGuessVerifyNTM_guess_trace_exit M t (fun i ↦ choices i.val) c0
      (fun s hs ↦ hfirst s hs) hhalt
    change (fixedGuessVerifyNTM M).trace (t + 1) (fun i ↦ choices i.val)
        (satGuessWrap M c0) = satPairWrap M
          { state := .init, input := satBoundaryInput cT.input,
            work := satBoundaryWork cT.work, output := satBoundaryOutput cT.output } at he
    rw [hinputBoundary, houtputBoundary] at he
    exact he
  have htail := fixedGuessVerifyNTM_pair_start_decides M hM x y pairWork out
    ⟨hwitnessBoundary, hpairBoundary⟩ hout hworkBoundary (by simp [y, B])
    (fun i ↦ choices (t + 1 + i.val))
  have hshort :
      let result := (fixedGuessVerifyNTM M).trace (t + 1 + S) (fun i ↦ choices i.val)
        (satGuessWrap M c0)
      (fixedGuessVerifyNTM M).halted result ∧
        ((pair x y ∈ L → result.output.cells 1 = Γ.one) ∧
          (pair x y ∉ L → result.output.cells 1 = Γ.zero)) := by
    dsimp only
    rw [NTM.trace_add_fun, hexit]
    exact htail
  have hle : t + 1 + S ≤ fixedGuessTailTime f x.length := by
    dsimp [G, B, S, fixedGuessTailTime] at ht ⊢
    omega
  have hfull := (fixedGuessVerifyNTM M).trace_mono hle
    (choices := fun i ↦ choices i.val) (choices' := fun i ↦ choices i.val)
    (c := satGuessWrap M c0) (fun _ ↦ rfl) hshort.1
  dsimp only
  rw [hfull]
  exact hshort

end SparseIrred.UpperBounds.Machine
