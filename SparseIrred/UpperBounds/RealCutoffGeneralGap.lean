import SparseIrred.UpperBounds.RealCutoff

/-!
# Real cutoffs with an arbitrary fixed positive zero-free gap

This combines the two extensions of the original Section 3: the counting
variable is any real `X > 2`, and the literature estimate may use any fixed
positive gap. At `δ = 1/32`, the displayed coefficients are exactly `64` and `4`.
-/

namespace SparseIrred.UpperBounds

open Polynomial NumberField
open scoped BigOperators

/-- Proposition 13, at every real cutoff, with the arbitrary positive gap of Remark 16. -/
theorem integer_prime_root_average_concrete_real_of_gap (f : ℤ[X]) (hf : f.IsPrimitive)
    (hdegree : 1 ≤ f.natDegree) (δ C : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hExternal : EffectivePrimeIdealEstimateReal δ C) (X : ℝ) (hX : 2 < X) :
    |(primeRootSumLEReal f X : ℝ) -
      factorStatistic (f.map (Int.castRingHom ℚ)) * (primeCountLEReal X : ℝ)| ≤
      C * X ^ (1 - δ) *
        (2 * δ⁻¹ * (f.natDegree : ℝ) ^ 2 * inputDelta f +
          4 * f.natDegree * Real.log X) +
        2 * f.natDegree * Real.sqrt X + 4 * (f.natDegree : ℝ) ^ 2 * inputDelta f := by
  let r : ℝ := δ⁻¹ / 32
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hweight : (∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ)) =
      factorStatistic (f.map (Int.castRingHom ℚ)) := by
    exact_mod_cast integerFactorIndex_weight_sum f hf
  have hdiscriminant :
      (∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ) *
        (r * fieldLogDiscriminant (IntegerFactorRootField f hf i))) ≤
          (f.natDegree : ℝ) ^ 2 * (r * inputDelta f) := by
    calc
      _ = r * ∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ) *
          fieldLogDiscriminant (IntegerFactorRootField f hf i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ r * ((f.natDegree : ℝ) ^ 2 * inputDelta f) :=
        mul_le_mul_of_nonneg_left
          (integerFactorIndex_weighted_fieldLogDiscriminant_le f hf hdegree) hr
      _ = _ := by ring
  have hE : 0 ≤ C * X ^ (1 - δ) := by positivity
  have ht : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have havg := prime_root_average_strong Finset.univ
    (fun i : IntegerFactorIndex f ↦ (integerFactorWeight f i.val : ℝ))
    (fun i ↦ (primeIdealCountLEReal (IntegerFactorRootField f hf i) X : ℝ))
    (fun i ↦ r * fieldLogDiscriminant (IntegerFactorRootField f hf i))
    (fun i ↦ (Module.finrank ℚ (IntegerFactorRootField f hf i) : ℝ))
    (primeRootSumLEReal f X : ℝ) (primeCountLEReal X : ℝ)
    (∫ t in (2 : ℝ)..X, 1 / Real.log t) (C * X ^ (1 - δ)) (Real.log X)
    (f.natDegree : ℝ) (r * inputDelta f)
    (2 * f.natDegree * Real.sqrt X + 4 * (f.natDegree : ℝ) ^ 2 * inputDelta f)
    (fun _ _ ↦ by positivity) hE ht
    (by exact_mod_cast integerFactorIndex_weight_sum_le f hf)
    (by exact_mod_cast integerFactorIndex_weighted_finrank_sum_le f hf)
    hdiscriminant (fun i _ ↦ ?_) (rational_primeCountLEReal_estimate δ C hExternal X hX)
    (integer_prime_root_field_comparison_real f hf hdegree X (by linarith))
  · rw [hweight] at havg
    have heq : 32 * (f.natDegree : ℝ) ^ 2 * (r * inputDelta f) =
        δ⁻¹ * (f.natDegree : ℝ) ^ 2 * inputDelta f := by dsimp [r]; ring
    rw [heq] at havg
    have hterm : 0 ≤ δ⁻¹ * (f.natDegree : ℝ) ^ 2 * inputDelta f +
        2 * f.natDegree * Real.log X := by positivity
    nlinarith [mul_nonneg hE hterm]
  · have hlocal := hExternal (IntegerFactorRootField f hf i) X hX
    convert hlocal using 1 <;> dsimp [r] <;> ring

end SparseIrred.UpperBounds
