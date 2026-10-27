import SparseIrred.UpperBounds.Machine.GeneralGapPaddedVerifier
import SparseIrred.UpperBounds.Machine.GuessMachine
import SparseIrred.UpperBounds.Machine.Precompose

/-! # Remark 16 with a fully implemented polynomial-time probabilistic machine

For every fixed positive gap the cutoff multiplier and counting constant are
chosen before the input. The probabilistic machine is constructed from the same
verified fixed-width guessing and deterministic string verifier infrastructure.
The only inputs are the cited effective counting estimate and AKS primality in FP.
-/
open Complexity
open SparseIrred.UpperBounds.Machine
namespace SparseIrred.UpperBounds.GeneralGap

/-- The actual machine realizes the larger-cutoff probability in polynomial time. -/
theorem exists_primeCounting_machine (r C₀ : ℕ) (hAKS : BinaryPrimalityInFP) :
    ∃ (k : ℕ) (tm : NTM k) (time : ℕ → ℕ) (d : ℕ),
      tm.AllPathsHaltIn time ∧ time =O (· ^ d) ∧
        ∀ x, tm.acceptProb x (time x.length) = primeCountingAcceptance r C₀ x := by
  classical
  obtain ⟨k, M, f, d, hM, hf⟩ := exists_paddedPrimeVerifier_decider r C₀ hAKS
  obtain ⟨e, hhalt, htime⟩ := fixedGuessVerifyNTM_polynomial_time M hM hf
  have hne : (fixedGuessVerifyNTM M).qstart ≠ (fixedGuessVerifyNTM M).qhalt := by
    simp [fixedGuessVerifyNTM, SAT.satGuessVerifyNTM]
  obtain ⟨j, tm, time, a, hhalt', htime', hprob⟩ :=
    exists_polynomial_precompose (padPrimeInput_mem_FP r C₀) (fixedGuessVerifyNTM M)
      hhalt htime hne
  refine ⟨j, tm, time, a, hhalt', htime', ?_⟩
  intro x
  apply (hprob x).trans
  apply (fixedGuessVerifyNTM_acceptProb M hM (padPrimeInput r C₀ x)).trans
  rw [← paddedPrimeVerifier_eventProb r C₀ x]
  apply congrArg eventProb
  ext seed
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]

/-- The complete complexity conclusion at the fixed integral gap parametrization. -/
theorem irreducibility_mem_PP_and_PSPACE (r C₀ : ℕ) (hr : 1 ≤ r) (hC : 1 ≤ C₀)
    (hExternal : ScaledPrimeIdealEstimate r C₀) (hAKS : BinaryPrimalityInFP) :
    IrredLang ∈ PP ∧ IrredLang ∈ PSPACE := by
  obtain ⟨k, tm, time, d, hhalt, hpoly, hprob⟩ := exists_primeCounting_machine r C₀ hAKS
  have hPP : IrredLang ∈ PP := by
    refine Set.mem_iUnion.mpr ⟨d, k, tm, time, hhalt, ?_, hpoly⟩
    intro x
    rw [hprob x]
    exact (primeCountingAcceptance_gt_half_iff_mem_IrredLang r C₀ hr hC hExternal x).symm
  exact ⟨hPP, PP_subset_PSPACE hPP⟩

/-- Original-paper Remark 16: every fixed positive gap gives the same final classes.
No algorithm certificate or internal mathematical result is assumed. -/
theorem section3_irreducibility_mem_PP_and_PSPACE_of_positive_gap
    (δ : ℝ) (hδ : 0 < δ)
    (hExternal : ∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate δ C)
    (hAKS : BinaryPrimalityInFP) : IrredLang ∈ PP ∧ IrredLang ∈ PSPACE := by
  obtain ⟨r, C₀, hr, hC, hestimate⟩ := exists_integer_scaled_primeIdeal_estimate δ hδ hExternal
  exact irreducibility_mem_PP_and_PSPACE r C₀ hr hC hestimate hAKS

end SparseIrred.UpperBounds.GeneralGap
