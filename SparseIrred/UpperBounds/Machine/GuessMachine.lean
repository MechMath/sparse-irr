import SparseIrred.UpperBounds.Machine.GuessSetup
import SparseIrred.UpperBounds.Machine.GuessTail

/-!
# Exact probability of the complete fixed-length guessing machine

The deterministic setup fixes the positions of the random writing steps. The
verified suffix then decides the verifier on exactly those bits. Thus the actual
machine, including every administrative transition, has the uniform-seed
acceptance probability.
-/

namespace SparseIrred.UpperBounds.Machine

open Complexity Complexity.NTM Complexity.SAT

variable {k : ℕ}

/-- The actual complete machine has exactly the acceptance probability of a
uniform verifier seed of length `|x| + 1`. -/
theorem fixedGuessVerifyNTM_acceptProb (M : TM k) {L : Language}
    [DecidablePred (fun s ↦ s ∈ L)] {f : ℕ → ℕ}
    (hM : M.DecidesInTime L f) (x : List Bool) :
    (fixedGuessVerifyNTM M).acceptProb x (satGuessVerifyTime f x.length) =
      eventProb (Finset.univ.filter fun seed : Fin (x.length + 1) → Bool ↦
        pair x (List.ofFn seed) ∈ L) := by
  obtain ⟨t₀, ht₀, cGuess, hsetup, hstate, hinput, hcounter, hothers, hout⟩ :=
    fixedGuessVerify_setup_uniform M x
  let T := satGuessVerifyTime f x.length
  have hbudget : t₀ + fixedGuessTailTime f x.length ≤ T := by
    dsimp [T, satGuessVerifyTime, satGuessVerifySetupTime, fixedGuessTailTime,
      guessBoundedTime]
    omega
  let schedule : Fin (x.length + 1) ↪ Fin T :=
    { toFun := fun i ↦ ⟨t₀ + 2 * i.val + 1, by
        have hi := i.isLt
        dsimp [fixedGuessTailTime] at hbudget
        omega⟩
      inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega }
  let verifier : (Fin (x.length + 1) → Bool) → Bool :=
    fun seed ↦ decide (pair x (List.ofFn seed) ∈ L)
  have htrace : ∀ choices : Fin T → Bool,
      let result := (fixedGuessVerifyNTM M).trace T choices
        ((fixedGuessVerifyNTM M).initCfg x)
      result.state = (fixedGuessVerifyNTM M).qhalt ∧
        (result.output.cells 1 = Γ.one ↔ verifier (scheduledSeed schedule choices) = true) := by
    intro choices
    let stream : ℕ → Bool := fun j ↦ if h : j < T then choices ⟨j, h⟩ else false
    have hstream : (fun i : Fin T ↦ stream i.val) = choices := by
      funext i
      simp only [stream, dite_eq_left i.isLt]
    have hwitness := hothers (satWitnessIdx k) (Ne.symm (satCounterIdx_ne_witnessIdx k))
    have hpre : (cGuess.work (satWitnessIdx k)).HasBinaryPrefix [] ∧
        (cGuess.work (satWitnessIdx k)).cells 0 = Γ.start ∧
        (cGuess.work (satCounterIdx k)).HasUnaryCounter (x.length + 1) := by
      rw [hwitness]
      exact ⟨Tape.init_nil_move_right_hasBinaryPrefix_nil, rfl, hcounter⟩
    have htail := fixedGuessVerifyNTM_guess_start_decides M hM x cGuess.work cGuess.output
      hpre (hothers _ (Ne.symm (satCounterIdx_ne_pairIdx k))) hout
      (fun i ↦ hothers _ (satVerifierWorkIdx_ne_counterIdx i))
      (fun j ↦ stream (t₀ + j))
    rw [← hinput, ← hstate] at htail
    have hshort :
        let result := (fixedGuessVerifyNTM M).trace (t₀ + fixedGuessTailTime f x.length)
          (fun i ↦ stream i.val) ((fixedGuessVerifyNTM M).initCfg x)
        (fixedGuessVerifyNTM M).halted result ∧
          ((pair x (fixedGuessBits (x.length + 1) (fun j ↦ stream (t₀ + j))) ∈ L →
              result.output.cells 1 = Γ.one) ∧
            (pair x (fixedGuessBits (x.length + 1) (fun j ↦ stream (t₀ + j))) ∉ L →
              result.output.cells 1 = Γ.zero)) := by
      dsimp only
      rw [NTM.trace_add_fun, hsetup]
      exact htail
    have hfrozen := (fixedGuessVerifyNTM M).trace_mono hbudget
      (choices := fun i ↦ stream i.val) (choices' := fun i ↦ stream i.val)
      (fun _ ↦ rfl) hshort.1
    have hseed : fixedGuessBits (x.length + 1) (fun j ↦ stream (t₀ + j)) =
        List.ofFn (scheduledSeed schedule choices) := by
      apply congrArg List.ofFn
      funext i
      have hi : t₀ + (2 * i.val + 1) < T := by
        have := (schedule i).isLt
        dsimp [schedule] at this
        omega
      simp only [stream, dite_eq_left hi, scheduledSeed, Function.comp_apply, schedule]
      congr 1
    rw [hseed] at hshort
    dsimp only
    rw [← hstream, hfrozen]
    rw [hstream]
    refine ⟨hshort.1, ?_⟩
    simp only [verifier, decide_eq_true_eq]
    constructor
    · intro haccept
      by_contra hreject
      have := hshort.2.2 hreject
      rw [haccept] at this
      cases this
    · exact hshort.2.1
  have hprob := acceptProb_eq_verifier_fraction (fixedGuessVerifyNTM M) x schedule
    verifier htrace
  simpa only [verifier, decide_eq_true_eq, eventProb] using hprob

end SparseIrred.UpperBounds.Machine
