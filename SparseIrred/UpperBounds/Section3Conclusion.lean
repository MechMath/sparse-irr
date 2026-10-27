import SparseIrred.UpperBounds.RawPrimeCountingDecision
import SparseIrred.Sparse.Canonical
import Complexitylib.Classes.Containments.PPSubsetPSPACE

/-!
# The Section 3 conclusion with an explicit algorithm boundary

The cited uniform prime-ideal estimate is an external mathematical premise. The
paper's internal arithmetic argument proves that the concrete finite acceptance
probability below decides the encoded irreducibility language.

`PrimeCountingAlgorithmCertificate` separately records the algorithm implementation
and its polynomial running time. Its existence is an explicit, unformalized
algorithm premise; it contains neither irreducibility nor the target language.
The final theorems derive membership in complexitylib's actual `PP` and `PSPACE`
from those two clearly separated premises.
-/

open Polynomial Complexity SparseDiv SparseDiv.Appendix

namespace SparseIrred.UpperBounds

/-- The finite acceptance probability of the Section 3 test on a polynomial,
including the constant and nonprimitive branches. -/
noncomputable def polynomialPrimeCountingAcceptance (C₀ : ℕ) (f : ℤ[X]) : ℚ := by
  classical
  exact if f.natDegree = 0 then
      if (f.coeff 0).natAbs.Prime then 1 else 0
    else if f.IsPrimitive then
      (witnessCount (majorityGadget
          (positivePrimeWitness (primeCountingCutoff C₀ f))
          (negativePrimeWitness f (primeCountingCutoff C₀ f))) : ℚ) /
        (2 : ℚ) ^ (2 * inputCutoffExponent C₀ f + 5)
    else 0

/-- The same acceptance probability on binary sparse codes; malformed and
noncanonical codes have acceptance probability zero. -/
noncomputable def primeCountingAcceptance (C₀ : ℕ) (x : List Bool) : ℚ :=
  match decodePoly x with
  | none => 0
  | some f => polynomialPrimeCountingAcceptance C₀ f

private theorem primeCounting_majority_count_le (C₀ : ℕ) (f : ℤ[X]) :
    witnessCount (majorityGadget
        (positivePrimeWitness (primeCountingCutoff C₀ f))
        (negativePrimeWitness f (primeCountingCutoff C₀ f))) ≤
      2 ^ (2 * inputCutoffExponent C₀ f + 5) := by
  classical
  have hcard : Fintype.card
      (Fin 8 × PrimeWitness (primeCountingCutoff C₀ f) × Bool) =
        2 ^ (2 * inputCutoffExponent C₀ f + 5) :=
    primeWitness_choice_count (inputCutoffExponent C₀ f)
  rw [← hcard]
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- The finite polynomial test defines a probability in the interval `[0, 1]`. -/
theorem polynomialPrimeCountingAcceptance_mem_Icc (C₀ : ℕ) (f : ℤ[X]) :
    polynomialPrimeCountingAcceptance C₀ f ∈ Set.Icc (0 : ℚ) 1 := by
  classical
  unfold polynomialPrimeCountingAcceptance
  split_ifs <;> try norm_num
  constructor
  · positivity
  · apply (div_le_one (by positivity : (0 : ℚ) < 2 ^
      (2 * inputCutoffExponent C₀ f + 5))).mpr
    exact_mod_cast primeCounting_majority_count_le C₀ f

/-- Rejection of malformed codes preserves the probability bounds. -/
theorem primeCountingAcceptance_mem_Icc (C₀ : ℕ) (x : List Bool) :
    primeCountingAcceptance C₀ x ∈ Set.Icc (0 : ℚ) 1 := by
  cases hdecode : decodePoly x with
  | none => norm_num [primeCountingAcceptance, hdecode]
  | some f =>
      simpa only [primeCountingAcceptance, hdecode] using
        polynomialPrimeCountingAcceptance_mem_Icc C₀ f

private theorem half_lt_nat_ratio_iff (a k : ℕ) :
    (1 / 2 : ℚ) < (a : ℚ) / (2 : ℚ) ^ k ↔ 2 ^ k < 2 * a := by
  have hpos : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  rw [lt_div_iff₀ hpos]
  have hcast : (2 : ℚ) ^ k < 2 * (a : ℚ) ↔ 2 ^ k < 2 * a := by
    exact_mod_cast Iff.rfl
  constructor
  · intro h
    exact hcast.mp (by linarith)
  · intro h
    have := hcast.mpr h
    linarith

/-- The paper's internal arithmetic derivation proves the strict probability
threshold for every polynomial, including all boundary cases. -/
theorem polynomialPrimeCountingAcceptance_gt_half_iff (C₀ : ℕ) (f : ℤ[X])
    (hC : 1 ≤ C₀) (hExternal : UniformPrimeIdealEstimate C₀) :
    polynomialPrimeCountingAcceptance C₀ f > 1 / 2 ↔ Irreducible f := by
  classical
  by_cases hdegree : f.natDegree = 0
  · rw [integer_irreducible_boundary]
    simp only [polynomialPrimeCountingAcceptance, hdegree, ↓reduceIte]
    split_ifs with hp <;> norm_num [hp]
  · by_cases hprimitive : f.IsPrimitive
    · simp only [polynomialPrimeCountingAcceptance, hdegree, hprimitive,
        ↓reduceIte]
      exact (half_lt_nat_ratio_iff _ _).trans
        ((primeCounting_majority_iff_threshold C₀ f).trans
          (integer_irreducible_iff_primeCounting_threshold_of_uniform_estimate
            C₀ f hC hprimitive (Nat.pos_of_ne_zero hdegree) hExternal).symm)
    · have hnot : ¬Irreducible f := by
        intro hi
        exact hprimitive (hi.isPrimitive hdegree)
      norm_num [polynomialPrimeCountingAcceptance, hdegree, hprimitive, hnot]

/-- The concrete finite probability decides the actual canonical sparse-code
language, with malformed strings rejected. -/
theorem primeCountingAcceptance_gt_half_iff_mem_IrredLang (C₀ : ℕ)
    (hC : 1 ≤ C₀) (hExternal : UniformPrimeIdealEstimate C₀) (x : List Bool) :
    primeCountingAcceptance C₀ x > 1 / 2 ↔ x ∈ IrredLang := by
  cases hdecode : decodePoly x with
  | none =>
      have hx := not_mem_IrredLang_of_decodePoly_eq_none hdecode
      simp [primeCountingAcceptance, hdecode, hx]
  | some f =>
      have hcode := decodePoly_eq_some_iff.mp hdecode
      rw [primeCountingAcceptance, hdecode]
      change polynomialPrimeCountingAcceptance C₀ f > 1 / 2 ↔ x ∈ IrredLang
      rw [← hcode, encPoly_mem_IrredLang_iff]
      exact polynomialPrimeCountingAcceptance_gt_half_iff C₀ f hC hExternal

/-- The deliberately unformalized algorithm boundary: one probabilistic machine
realizes the explicit finite probability in polynomial time. This is a premise,
not an asserted external theorem or a premise about the final language. -/
def PrimeCountingAlgorithmCertificate (C₀ : ℕ) : Prop :=
  ∃ (k : ℕ) (tm : NTM k) (time : ℕ → ℕ) (d : ℕ),
    tm.AllPathsHaltIn time ∧ time =O (· ^ d) ∧
      ∀ x, tm.acceptProb x (time x.length) = primeCountingAcceptance C₀ x

/-- The actual `PP` membership conclusion, conditional only on the explicit
external estimate and the separately identified algorithm implementation. -/
theorem irreducibility_mem_PP_of_primeCounting_certificate (C₀ : ℕ)
    (hC : 1 ≤ C₀) (hExternal : UniformPrimeIdealEstimate C₀)
    (hAlgorithm : PrimeCountingAlgorithmCertificate C₀) : IrredLang ∈ PP := by
  obtain ⟨k, tm, time, d, hhalt, hpoly, hprob⟩ := hAlgorithm
  refine Set.mem_iUnion.mpr ⟨d, k, tm, time, hhalt, ?_, hpoly⟩
  intro x
  rw [hprob x]
  exact (primeCountingAcceptance_gt_half_iff_mem_IrredLang C₀ hC hExternal x).symm

/-- `PP ⊆ PSPACE` supplies the second final membership claim without an
additional implementation of the paper's deterministic enumeration algorithm. -/
theorem irreducibility_mem_PP_and_PSPACE_of_primeCounting_certificate (C₀ : ℕ)
    (hC : 1 ≤ C₀) (hExternal : UniformPrimeIdealEstimate C₀)
    (hAlgorithm : PrimeCountingAlgorithmCertificate C₀) :
    IrredLang ∈ PP ∧ IrredLang ∈ PSPACE := by
  have hPP := irreducibility_mem_PP_of_primeCounting_certificate C₀ hC hExternal hAlgorithm
  exact ⟨hPP, PP_subset_PSPACE hPP⟩

/-- The Section 3 conclusion from the cited real-constant estimate and the
unformalized algorithm certificates. One common integer constant is chosen
before the machine and before any input string. -/
theorem section3_irreducibility_mem_PP_and_PSPACE
    (hExternal : ∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate (1 / 32) C)
    (hAlgorithm : ∀ C₀ : ℕ, 1 ≤ C₀ → PrimeCountingAlgorithmCertificate C₀) :
    IrredLang ∈ PP ∧ IrredLang ∈ PSPACE := by
  obtain ⟨C₀, hC, hestimate⟩ := exists_integer_uniform_primeIdeal_estimate hExternal
  exact irreducibility_mem_PP_and_PSPACE_of_primeCounting_certificate
    C₀ hC hestimate (hAlgorithm C₀ hC)

end SparseIrred.UpperBounds
