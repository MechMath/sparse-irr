import SparseIrred.UpperBounds.Machine.GuessFixed
import Complexitylib.SAT.Internal.GuessVerify

/-!
# The complete fixed-guess verifier machine

The finite control sequences counter construction, input rewind, fixed-length
random guessing, pair construction, and a deterministic verifier. It reuses
complexitylib's concrete SAT machine with the early-stop choices disabled.
This file constructs the actual machine and proves its all-path polynomial
running-time bound. Exact probability additionally requires connecting the
input-dependent setup boundary to the fixed guessing schedule.
-/

namespace SparseIrred.UpperBounds.Machine

open Complexity Complexity.NTM Complexity.SAT

variable {k : ℕ}

/-- Administrative continue decisions are forced; all writing choices remain fair. -/
def pipelineChoice (M : TM k) (state : GuessVerifyPhase M.Q) (choice : Bool) : Bool :=
  match state with
  | .guess .choose => true
  | _ => choice

/-- The concrete counter/guess/pair/verify machine, with exactly `|x| + 1` guessed bits. -/
def fixedGuessVerifyNTM (M : TM k) : NTM (k + 3) where
  Q := (satGuessVerifyNTM M).Q
  qstart := (satGuessVerifyNTM M).qstart
  qhalt := (satGuessVerifyNTM M).qhalt
  δ := fun choice state ↦ (satGuessVerifyNTM M).δ (pipelineChoice M state choice) state
  δ_right_of_start := fun choice state ↦
    (satGuessVerifyNTM M).δ_right_of_start (pipelineChoice M state choice) state

set_option backward.isDefEq.respectTransparency false

/-- One pipeline step is a step of the existing composed machine with the
continue decision forced only in the guessing phase. -/
theorem fixedGuessVerifyNTM_trace_one (M : TM k) (choice : Bool)
    (c : Cfg (k + 3) (GuessVerifyPhase M.Q)) :
    (fixedGuessVerifyNTM M).trace 1 (fun _ ↦ choice) c =
      (satGuessVerifyNTM M).trace 1 (fun _ ↦ pipelineChoice M c.state choice) c := by
  by_cases h : c.state = (satGuessVerifyNTM M).qhalt <;>
    simp [NTM.trace, fixedGuessVerifyNTM, h]

/-- Every trace of the fixed-guess pipeline is a valid trace of the original
bounded-guess pipeline, so all deterministic setup and verifier proofs apply. -/
theorem fixedGuessVerifyNTM_trace_eq_bounded (M : TM k) (T : ℕ)
    (choices : Fin T → Bool) (c : Cfg (k + 3) (GuessVerifyPhase M.Q)) :
    ∃ boundedChoices : Fin T → Bool,
      (fixedGuessVerifyNTM M).trace T choices c =
        (satGuessVerifyNTM M).trace T boundedChoices c := by
  induction T with
  | zero => exact ⟨choices, rfl⟩
  | succ T ih =>
      obtain ⟨seedPrefix, hprefix⟩ := ih (fun i ↦ choices i.castSucc)
      let current := (satGuessVerifyNTM M).trace T seedPrefix c
      refine ⟨Fin.snoc seedPrefix (pipelineChoice M current.state (choices (Fin.last T))), ?_⟩
      rw [NTM.trace_snoc (fixedGuessVerifyNTM M) T,
        NTM.trace_snoc (satGuessVerifyNTM M) T]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rw [hprefix, fixedGuessVerifyNTM_trace_one]

/-- The actual fixed-guess pipeline halts on every computation path whenever its
deterministic verifier does. -/
theorem fixedGuessVerifyNTM_allPathsHaltIn (M : TM k) {L : Language} {f : ℕ → ℕ}
    (hM : M.DecidesInTime L f) :
    (fixedGuessVerifyNTM M).AllPathsHaltIn (satGuessVerifyTime f) := by
  intro x choices
  obtain ⟨boundedChoices, htrace⟩ := fixedGuessVerifyNTM_trace_eq_bounded M
    (satGuessVerifyTime f x.length) choices ((fixedGuessVerifyNTM M).initCfg x)
  rw [htrace]
  exact satGuessVerify_allPathsHaltIn_of_decidesInTime M hM x boundedChoices

/-- A polynomial-time deterministic verifier yields a polynomial all-path clock
for the constructed fixed-guess machine. -/
theorem fixedGuessVerifyNTM_polynomial_time (M : TM k) {L : Language} {f : ℕ → ℕ}
    (hM : M.DecidesInTime L f) {d : ℕ} (hf : f =O (· ^ d)) :
    ∃ e : ℕ, (fixedGuessVerifyNTM M).AllPathsHaltIn (satGuessVerifyTime f) ∧
      satGuessVerifyTime f =O (· ^ e) := by
  obtain ⟨e, he⟩ := satGuessVerifyTime_bigO_of_bigO hf
  exact ⟨e, fixedGuessVerifyNTM_allPathsHaltIn M hM, he⟩

/-- The fixed-guess pipeline retains the original verifier's pointwise decision
specification. Identifying the selected witness with the uniform compact seed is
a separate, stronger statement. -/
theorem fixedGuessVerifyNTM_verifies_some_witness (M : TM k) {L : Language} {f : ℕ → ℕ}
    (hM : M.DecidesInTime L f) (x : List Bool)
    (choices : Fin (satGuessVerifyTime f x.length) → Bool) :
    ∃ y : List Bool, y.length ≤ x.length + 1 ∧
      let result := (fixedGuessVerifyNTM M).trace (satGuessVerifyTime f x.length) choices
        ((fixedGuessVerifyNTM M).initCfg x)
      (fixedGuessVerifyNTM M).halted result ∧
        ((pair x y ∈ L → result.output.cells 1 = Γ.one) ∧
          (pair x y ∉ L → result.output.cells 1 = Γ.zero)) := by
  obtain ⟨boundedChoices, htrace⟩ := fixedGuessVerifyNTM_trace_eq_bounded M
    (satGuessVerifyTime f x.length) choices ((fixedGuessVerifyNTM M).initCfg x)
  have h := satGuessVerify_trace_decides_for_some_setup_witness_of_decidesInTime
    M hM x boundedChoices
  dsimp only
  rw [htrace]
  exact h

/-- The guessing phase of the complete pipeline is the concrete fixed-length
uniform guessing subroutine. -/
theorem fixedGuessVerifyNTM_guess_trace_one (M : TM k) (choice : Bool)
    (c : Cfg (k + 3) GuessBoundedPhase) (hstate : c.state ≠ .done) :
    (fixedGuessVerifyNTM M).trace 1 (fun _ ↦ choice) (satGuessWrap M c) =
      satGuessWrap M
        ((guessFixedNTM (satWitnessIdx k) (satCounterIdx k)).trace 1
          (fun _ ↦ choice) c) := by
  rw [fixedGuessVerifyNTM_trace_one, guessFixedNTM_trace_one]
  have hchoice : pipelineChoice M (satGuessWrap M c).state choice = fixedChoice c.state choice := by
    cases h : c.state <;> simp [pipelineChoice, fixedChoice, satGuessWrap, h]
  rw [hchoice]
  exact satGuessVerify_guess_trace_one M _ c hstate

end SparseIrred.UpperBounds.Machine
