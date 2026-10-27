import SparseIrred.UpperBounds.PrimeAverageInstantiation

/-!
# Proposition 13 at arbitrary real cutoffs

The analytic counting functions in the original paper use `p ≤ X` and `N(P) ≤ X`
for a real number `X`.  Their finite definitions below use `Nat.floor`; the membership
theorems establish the exact real-cutoff interpretation.  The external input is the
same effective prime-ideal theorem evaluated at real cutoffs.  The passage from that
input to the polynomial root average is proved here, including `2 < X < 3`.
-/

namespace SparseIrred.UpperBounds

open Polynomial NumberField
open scoped BigOperators

/-- Rational primes at most a real cutoff. -/
noncomputable def primesLEReal (X : ℝ) : Finset ℕ := ⌊X⌋₊.primesLE

/-- The usual prime-counting function at a real cutoff. -/
noncomputable def primeCountLEReal (X : ℝ) : ℕ := ⌊X⌋₊.primeCounting

/-- The paper's weighted modular-root sum over `p ≤ X`. -/
noncomputable def primeRootSumLEReal (f : ℤ[X]) (X : ℝ) : ℕ :=
  primeRootSum f (⌊X⌋₊ + 1)

/-- Actual nonzero prime ideals whose absolute norm is at most the real cutoff. -/
noncomputable def primeIdealsLEReal (K : Type*) [Field K] [NumberField K]
    (X : ℝ) : Finset (Ideal (𝓞 K)) := primeIdealsLE K ⌊X⌋₊

/-- The usual number-field prime-ideal counting function at a real cutoff. -/
noncomputable def primeIdealCountLEReal (K : Type*) [Field K] [NumberField K]
    (X : ℝ) : ℕ := primeIdealCountLE K ⌊X⌋₊

/-- Exact interpretation of the finite rational-prime set. -/
theorem mem_primesLEReal (X : ℝ) (hX : 0 ≤ X) (p : ℕ) :
    p ∈ primesLEReal X ↔ (p : ℝ) ≤ X ∧ p.Prime := by
  simp only [primesLEReal, Nat.mem_primesLE, Nat.le_floor_iff hX]

/-- The real prime count is the cardinality of the real-cutoff prime set. -/
theorem primeCountLEReal_eq_card (X : ℝ) :
    primeCountLEReal X = (primesLEReal X).card := by
  simp [primeCountLEReal, primesLEReal, Nat.primesLE_card_eq_primeCounting]

/-- The real root count sums exactly over the real-cutoff prime set. -/
theorem primeRootSumLEReal_eq_sum (f : ℤ[X]) (X : ℝ) :
    primeRootSumLEReal f X = ∑ p ∈ primesLEReal X, primeRootWeight f p := by
  simp only [primeRootSumLEReal, primeRootSum, primesLEReal,
    Nat.primesLE_eq_filter_range]

/-- Exact interpretation of the finite prime-ideal set. -/
theorem mem_primeIdealsLEReal (K : Type*) [Field K] [NumberField K]
    (X : ℝ) (hX : 0 ≤ X) (P : Ideal (𝓞 K)) :
    P ∈ primeIdealsLEReal K X ↔ (P.absNorm : ℝ) ≤ X ∧ P.IsPrime ∧ P ≠ ⊥ := by
  simp only [primeIdealsLEReal, mem_primeIdealsLE, Nat.le_floor_iff hX]

/-- The real prime-ideal count counts the actual norm-bounded finite set. -/
theorem primeIdealCountLEReal_eq_card (K : Type*) [Field K] [NumberField K]
    (X : ℝ) : primeIdealCountLEReal K X = (primeIdealsLEReal K X).card := rfl

@[simp] theorem primeCountLEReal_natCast (X : ℕ) :
    primeCountLEReal (X : ℝ) = X.primeCounting := by
  simp [primeCountLEReal]

@[simp] theorem primeRootSumLEReal_natCast (f : ℤ[X]) (X : ℕ) :
    primeRootSumLEReal f (X : ℝ) = primeRootSum f (X + 1) := by
  simp [primeRootSumLEReal]

@[simp] theorem primeIdealCountLEReal_natCast (K : Type*) [Field K] [NumberField K]
    (X : ℕ) : primeIdealCountLEReal K (X : ℝ) = primeIdealCountLE K X := by
  simp [primeIdealCountLEReal]

/-- The external effective prime-ideal theorem, with its original real-cutoff
quantifier. This is a literature input, not the polynomial root-average conclusion. -/
def EffectivePrimeIdealEstimateReal (δ C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : ℝ), 2 < X →
    |(primeIdealCountLEReal K X : ℝ) - ∫ t in (2 : ℝ)..X, 1 / Real.log t| ≤
      C * X ^ (1 - δ) *
        (δ⁻¹ * fieldLogDiscriminant K + Module.finrank ℚ K * Real.log X)

/-- Restricting the real-cutoff literature input recovers the existing integer interface. -/
theorem effectivePrimeIdealEstimateReal_to_integer {δ C : ℝ}
    (h : EffectivePrimeIdealEstimateReal δ C) : EffectivePrimeIdealEstimate δ C := by
  intro K _ _ X hX
  simpa only [primeIdealCountLEReal_natCast] using h K (X : ℝ) (by exact_mod_cast hX)

/-- The fixed-gap specialization of the real-cutoff literature theorem. -/
theorem effectivePrimeIdealEstimateReal_fixed_gap (C : ℝ)
    (h : EffectivePrimeIdealEstimateReal (1 / 32) C)
    (K : Type) [Field K] [NumberField K] (X : ℝ) (hX : 2 < X) :
    |(primeIdealCountLEReal K X : ℝ) - ∫ t in (2 : ℝ)..X, 1 / Real.log t| ≤
      C * X ^ (31 / 32 : ℝ) *
        (32 * fieldLogDiscriminant K + Module.finrank ℚ K * Real.log X) := by
  simpa only [show (1 - 1 / 32 : ℝ) = 31 / 32 by norm_num,
    show (1 / 32 : ℝ)⁻¹ = 32 by norm_num] using h K X hX

/-- Specialization to the rational field yields the actual real prime count. -/
theorem rational_primeCountLEReal_estimate (δ C : ℝ)
    (h : EffectivePrimeIdealEstimateReal δ C) (X : ℝ) (hX : 2 < X) :
    |(primeCountLEReal X : ℝ) - ∫ t in (2 : ℝ)..X, 1 / Real.log t| ≤
      C * X ^ (1 - δ) * Real.log X := by
  simpa [primeIdealCountLEReal, primeCountLEReal, rational_primeIdealCountLE,
    fieldLogDiscriminant] using h ℚ X hX

/-- Equation (40), with genuine real cutoff and no restriction on its integer part. -/
theorem integer_prime_root_field_comparison_real (f : ℤ[X]) (hf : f.IsPrimitive)
    (hdegree : 1 ≤ f.natDegree) (X : ℝ) (hX : 0 ≤ X) :
    |(primeRootSumLEReal f X : ℝ) -
      ∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ) *
        primeIdealCountLEReal (IntegerFactorRootField f hf i) X| ≤
      2 * f.natDegree * Real.sqrt X + 4 * (f.natDegree : ℝ) ^ 2 * inputDelta f := by
  have h := integer_prime_root_field_comparison f hf ⌊X⌋₊ (inputDelta f)
    (integerSquarefreeExceptionalPrimes f) (by
      intro p hpX hpnot
      obtain ⟨_, hp⟩ := Nat.mem_primesLE.mp hpX
      let : Fact p.Prime := ⟨hp⟩
      exact integerFactorization_good_prime_root_weight_eq_degreeOne
        f hf hdegree p hp hpnot)
    (integerSquarefreeExceptionalPrimes_card_le f hf hdegree)
  refine h.trans ?_
  apply add_le_add_left
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le hX)) (by positivity)

/-- Original-paper Proposition 13 for every real `X > 2`, including the interval
`(2,3)`. The only unproved input is the explicitly named literature theorem. -/
theorem integer_prime_root_average_concrete_real (f : ℤ[X]) (hf : f.IsPrimitive)
    (hdegree : 1 ≤ f.natDegree) (C : ℝ) (hC : 0 ≤ C)
    (hExternal : EffectivePrimeIdealEstimateReal (1 / 32) C)
    (X : ℝ) (hX : 2 < X) :
    |(primeRootSumLEReal f X : ℝ) -
      factorStatistic (f.map (Int.castRingHom ℚ)) * (primeCountLEReal X : ℝ)| ≤
      C * X ^ (31 / 32 : ℝ) *
        (64 * (f.natDegree : ℝ) ^ 2 * inputDelta f +
          4 * f.natDegree * Real.log X) +
        2 * f.natDegree * Real.sqrt X + 4 * (f.natDegree : ℝ) ^ 2 * inputDelta f := by
  have hweight : (∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ)) =
      factorStatistic (f.map (Int.castRingHom ℚ)) := by
    exact_mod_cast integerFactorIndex_weight_sum f hf
  have hQ := rational_primeCountLEReal_estimate (1 / 32) C hExternal X hX
  norm_num only [show (1 - 1 / 32 : ℝ) = 31 / 32 by norm_num] at hQ
  have havg := prime_root_average_bound Finset.univ
    (fun i : IntegerFactorIndex f ↦ (integerFactorWeight f i.val : ℝ))
    (fun i ↦ (primeIdealCountLEReal (IntegerFactorRootField f hf i) X : ℝ))
    (fun i ↦ fieldLogDiscriminant (IntegerFactorRootField f hf i))
    (fun i ↦ (Module.finrank ℚ (IntegerFactorRootField f hf i) : ℝ))
    (primeRootSumLEReal f X : ℝ) (primeCountLEReal X : ℝ)
    (∫ t in (2 : ℝ)..X, 1 / Real.log t) C (f.natDegree : ℝ)
    (inputDelta f : ℝ) X
    (fun _ _ ↦ by positivity) hC (by positivity) (by positivity) hX
    (by exact_mod_cast integerFactorIndex_weight_sum_le f hf)
    (by exact_mod_cast integerFactorIndex_weighted_finrank_sum_le f hf)
    (integerFactorIndex_weighted_fieldLogDiscriminant_le f hf hdegree)
    (fun i _ ↦ effectivePrimeIdealEstimateReal_fixed_gap C hExternal
      (IntegerFactorRootField f hf i) X hX) hQ
    (integer_prime_root_field_comparison_real f hf hdegree X (by linarith))
  simpa only [hweight] using havg

end SparseIrred.UpperBounds
