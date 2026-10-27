import SparseIrred.UpperBounds.GeneralGapDecision
import SparseIrred.UpperBounds.Section3Conclusion

/-! # Remark 16: the finite probability and strict majority criterion -/

open Polynomial Complexity SparseDiv SparseDiv.Appendix

namespace SparseIrred.UpperBounds.GeneralGap

/-- The finite acceptance probability of the Section 3 test on a polynomial,
including the constant and nonprimitive branches. -/
noncomputable def polynomialPrimeCountingAcceptance (r C₀ : ℕ) (f : ℤ[X]) : ℚ := by
  classical
  exact if f.natDegree = 0 then
      if (f.coeff 0).natAbs.Prime then 1 else 0
    else if f.IsPrimitive then
      (witnessCount (majorityGadget
          (positivePrimeWitness (scaledPrimeCountingCutoff r C₀ f))
          (negativePrimeWitness f (scaledPrimeCountingCutoff r C₀ f))) : ℚ) /
        (2 : ℚ) ^ (2 * scaledInputCutoffExponent r C₀ f + 5)
    else 0

/-- The same acceptance probability on binary sparse codes; malformed and
noncanonical codes have acceptance probability zero. -/
noncomputable def primeCountingAcceptance (r C₀ : ℕ) (x : List Bool) : ℚ :=
  match decodePoly x with
  | none => 0
  | some f => polynomialPrimeCountingAcceptance r C₀ f

private theorem primeCounting_majority_count_le (r C₀ : ℕ) (f : ℤ[X]) :
    witnessCount (majorityGadget
        (positivePrimeWitness (scaledPrimeCountingCutoff r C₀ f))
        (negativePrimeWitness f (scaledPrimeCountingCutoff r C₀ f))) ≤
      2 ^ (2 * scaledInputCutoffExponent r C₀ f + 5) := by
  classical
  have hcard : Fintype.card
      (Fin 8 × PrimeWitness (scaledPrimeCountingCutoff r C₀ f) × Bool) =
        2 ^ (2 * scaledInputCutoffExponent r C₀ f + 5) :=
    primeWitness_choice_count (scaledInputCutoffExponent r C₀ f)
  rw [← hcard]
  exact (Finset.card_filter_le _ _).trans_eq Finset.card_univ

/-- The finite polynomial test defines a probability in the interval `[0, 1]`. -/
theorem polynomialPrimeCountingAcceptance_mem_Icc (r C₀ : ℕ) (f : ℤ[X]) :
    polynomialPrimeCountingAcceptance r C₀ f ∈ Set.Icc (0 : ℚ) 1 := by
  classical
  unfold polynomialPrimeCountingAcceptance
  split_ifs <;> try norm_num
  constructor
  · positivity
  · apply (div_le_one (by positivity : (0 : ℚ) < 2 ^
      (2 * scaledInputCutoffExponent r C₀ f + 5))).mpr
    exact_mod_cast primeCounting_majority_count_le r C₀ f

/-- Rejection of malformed codes preserves the probability bounds. -/
theorem primeCountingAcceptance_mem_Icc (r C₀ : ℕ) (x : List Bool) :
    primeCountingAcceptance r C₀ x ∈ Set.Icc (0 : ℚ) 1 := by
  cases hdecode : decodePoly x with
  | none => norm_num [primeCountingAcceptance, hdecode]
  | some f =>
      simpa only [primeCountingAcceptance, hdecode] using
        polynomialPrimeCountingAcceptance_mem_Icc r C₀ f

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
theorem polynomialPrimeCountingAcceptance_gt_half_iff (r C₀ : ℕ) (f : ℤ[X])
    (hr : 1 ≤ r) (hC : 1 ≤ C₀) (hExternal : ScaledPrimeIdealEstimate r C₀) :
    polynomialPrimeCountingAcceptance r C₀ f > 1 / 2 ↔ Irreducible f := by
  classical
  by_cases hdegree : f.natDegree = 0
  · rw [integer_irreducible_boundary]
    simp only [polynomialPrimeCountingAcceptance, hdegree, ↓reduceIte]
    split_ifs with hp <;> norm_num [hp]
  · by_cases hprimitive : f.IsPrimitive
    · simp only [polynomialPrimeCountingAcceptance, hdegree, hprimitive,
        ↓reduceIte]
      exact (half_lt_nat_ratio_iff _ _).trans
        ((scaledPrimeCounting_majority_iff_threshold r C₀ f).trans
          (integer_irreducible_iff_scaledPrimeCounting_threshold
            r C₀ f hr hC hprimitive (Nat.pos_of_ne_zero hdegree) hExternal).symm)
    · have hnot : ¬Irreducible f := by
        intro hi
        exact hprimitive (hi.isPrimitive hdegree)
      norm_num [polynomialPrimeCountingAcceptance, hdegree, hprimitive, hnot]

/-- The concrete finite probability decides the actual canonical sparse-code
language, with malformed strings rejected. -/
theorem primeCountingAcceptance_gt_half_iff_mem_IrredLang (r C₀ : ℕ)
    (hr : 1 ≤ r) (hC : 1 ≤ C₀) (hExternal : ScaledPrimeIdealEstimate r C₀) (x : List Bool) :
    primeCountingAcceptance r C₀ x > 1 / 2 ↔ x ∈ IrredLang := by
  cases hdecode : decodePoly x with
  | none =>
      have hx := not_mem_IrredLang_of_decodePoly_eq_none hdecode
      simp [primeCountingAcceptance, hdecode, hx]
  | some f =>
      have hcode := decodePoly_eq_some_iff.mp hdecode
      rw [primeCountingAcceptance, hdecode]
      change polynomialPrimeCountingAcceptance r C₀ f > 1 / 2 ↔ x ∈ IrredLang
      rw [← hcode, encPoly_mem_IrredLang_iff]
      exact polynomialPrimeCountingAcceptance_gt_half_iff r C₀ f hr hC hExternal

end SparseIrred.UpperBounds.GeneralGap
