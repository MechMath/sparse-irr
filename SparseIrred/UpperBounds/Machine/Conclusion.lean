import SparseIrred.UpperBounds.Machine.PaddedVerifier
import SparseIrred.UpperBounds.Machine.GuessMachine
import SparseIrred.UpperBounds.Machine.Precompose

/-!
# Section 3 with a verified probabilistic machine

The former algorithm implementation interface is constructed here. Binary
primality in polynomial time is the cited AKS theorem, retained as an explicit
external premise. All other preprocessing, sparse modular arithmetic, random
guessing, verification, composition, and exact probability obligations are proved.
The final theorem therefore requires only the two identified literature inputs:
the effective prime-ideal estimate and binary primality in `FP`.
-/

namespace SparseIrred.UpperBounds

open Complexity
open SparseIrred.UpperBounds.Machine

/-- Construct the former implementation certificate from the cited AKS theorem.
No correctness or complexity assumption about the irreducibility algorithm is used. -/
theorem primeCountingAlgorithmCertificate_of_binaryPrimalityInFP (C₀ : ℕ)
    (hAKS : BinaryPrimalityInFP) : PrimeCountingAlgorithmCertificate C₀ := by
  classical
  obtain ⟨k, M, f, d, hM, hf⟩ := exists_paddedPrimeVerifier_decider C₀ hAKS
  obtain ⟨e, hhalt, htime⟩ := fixedGuessVerifyNTM_polynomial_time M hM hf
  have hne : (fixedGuessVerifyNTM M).qstart ≠ (fixedGuessVerifyNTM M).qhalt := by
    simp [fixedGuessVerifyNTM, SAT.satGuessVerifyNTM]
  obtain ⟨j, tm, time, a, hhalt', htime', hprob⟩ :=
    exists_polynomial_precompose (padPrimeInput_mem_FP C₀) (fixedGuessVerifyNTM M)
      hhalt htime hne
  refine ⟨j, tm, time, a, hhalt', htime', ?_⟩
  intro x
  apply (hprob x).trans
  apply (fixedGuessVerifyNTM_acceptProb M hM (padPrimeInput C₀ x)).trans
  rw [← paddedPrimeVerifier_eventProb C₀ x]
  apply congrArg eventProb
  ext seed
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]

/-- The fixed-constant final result with the implementation interface discharged. -/
theorem irreducibility_mem_PP_and_PSPACE_of_external_theorems (C₀ : ℕ)
    (hC : 1 ≤ C₀) (hExternal : UniformPrimeIdealEstimate C₀)
    (hAKS : BinaryPrimalityInFP) : IrredLang ∈ PP ∧ IrredLang ∈ PSPACE :=
  irreducibility_mem_PP_and_PSPACE_of_primeCounting_certificate C₀ hC hExternal
    (primeCountingAlgorithmCertificate_of_binaryPrimalityInFP C₀ hAKS)

/-- Section 3's final conclusion with a proved actual machine implementation.
The two hypotheses are external literature theorems; there is no remaining
algorithm certificate or internal mathematical conclusion among the premises. -/
theorem section3_irreducibility_mem_PP_and_PSPACE_of_external_theorems
    (hExternal : ∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate (1 / 32) C)
    (hAKS : BinaryPrimalityInFP) : IrredLang ∈ PP ∧ IrredLang ∈ PSPACE := by
  obtain ⟨C₀, hC, hestimate⟩ := exists_integer_uniform_primeIdeal_estimate hExternal
  exact irreducibility_mem_PP_and_PSPACE_of_external_theorems C₀ hC hestimate hAKS

end SparseIrred.UpperBounds
