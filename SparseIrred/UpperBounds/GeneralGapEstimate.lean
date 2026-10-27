import SparseIrred.UpperBounds.PrimeAverageInstantiation

/-! # The external estimate at an arbitrary fixed positive gap

The parameter `r` is fixed before the input. Weakening a positive gap to
`1 / (32*r)` permits the same elementary counting argument with a longer,
still linearly bounded binary cutoff.
-/
namespace SparseIrred.UpperBounds

/-- Convenient integral parametrization of a positive zero-free gap. -/
def ScaledPrimeIdealEstimate (r : ℕ) (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : ℕ), 2 < X →
    |(primeIdealCountLE K X : ℝ) - ∫ t in (2 : ℝ)..(X : ℝ), 1 / Real.log t| ≤
      C * (X : ℝ) ^ (1 - 1 / (32 * r : ℝ)) *
        (32 * r * fieldLogDiscriminant K + Module.finrank ℚ K * Real.log X)

theorem effectivePrimeIdealEstimate_scaled (δ C : ℝ) (r : ℕ)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hr : 1 ≤ r) (hgap : 1 ≤ 32 * r * δ)
    (h : EffectivePrimeIdealEstimate δ C) : ScaledPrimeIdealEstimate r C := by
  intro K _ _ X hX
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hrecip : δ⁻¹ ≤ 32 * r := (inv_le_iff_one_le_mul₀ hδ).2 (by nlinarith [hgap])
  have hsmall : 1 / (32 * r : ℝ) ≤ δ :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * r)).2 (by nlinarith [hgap])
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hdisc := fieldLogDiscriminant_nonneg K
  apply (h K X hX).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ X))
        (by linarith : 1 - δ ≤ 1 - 1 / (32 * r : ℝ))) hC
  · nlinarith [mul_le_mul_of_nonneg_right hrecip hdisc]
  · positivity
  · positivity

theorem scaledPrimeIdealEstimate_mono {r : ℕ} {C D : ℝ} (hCD : C ≤ D)
    (h : ScaledPrimeIdealEstimate r C) : ScaledPrimeIdealEstimate r D := by
  intro K _ _ X hX
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hdisc := fieldLogDiscriminant_nonneg K
  exact (h K X hX).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCD (by positivity)) (by positivity))

/-- The constants are selected uniformly, before any input polynomial. -/
theorem exists_integer_scaled_primeIdeal_estimate (δ : ℝ) (hδ : 0 < δ)
    (hExternal : ∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate δ C) :
    ∃ r C₀ : ℕ, 1 ≤ r ∧ 1 ≤ C₀ ∧ ScaledPrimeIdealEstimate r C₀ := by
  obtain ⟨C, hC, h⟩ := hExternal
  let r := max 1 ⌈δ⁻¹⌉₊
  have hr : 1 ≤ r := le_max_left _ _
  have hinv : δ⁻¹ ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 ⌈δ⁻¹⌉₊)
  have hprod : 1 ≤ (r : ℝ) * δ := (inv_le_iff_one_le_mul₀ hδ).1 hinv
  have hgap : 1 ≤ 32 * (r : ℝ) * δ := by nlinarith
  refine ⟨r, max 1 ⌈C⌉₊, hr, le_max_left _ _, ?_⟩
  apply scaledPrimeIdealEstimate_mono (C := C)
    ((Nat.le_ceil C).trans (by exact_mod_cast le_max_right 1 ⌈C⌉₊))
  exact effectivePrimeIdealEstimate_scaled δ C r hδ hC.le hr hgap h

theorem rational_primeCount_estimate_scaled (r : ℕ) (C : ℝ)
    (h : ScaledPrimeIdealEstimate r C) (X : ℕ) (hX : 2 < X) :
    |(X.primeCounting : ℝ) - ∫ t in (2 : ℝ)..(X : ℝ), 1 / Real.log t| ≤
      C * (X : ℝ) ^ (1 - 1 / (32 * r : ℝ)) * Real.log X := by
  simpa [rational_primeIdealCountLE, fieldLogDiscriminant] using h ℚ X hX

/-- Proposition 13 with the arbitrary fixed gap and actual polynomial factors. -/
theorem integer_prime_root_average_concrete_scaled (f : Polynomial ℤ)
    (hf : f.IsPrimitive) (hdegree : 1 ≤ f.natDegree) (r : ℕ) (hr : 1 ≤ r)
    (C : ℝ) (hC : 0 ≤ C) (hExternal : ScaledPrimeIdealEstimate r C)
    (X : ℕ) (hX : 2 < X) :
    |(primeRootSum f (X + 1) : ℝ) -
      factorStatistic (f.map (Int.castRingHom ℚ)) * (X.primeCounting : ℝ)| ≤
      C * (X : ℝ) ^ (1 - 1 / (32 * r : ℝ)) *
        (64 * r * (f.natDegree : ℝ) ^ 2 * inputDelta f +
          4 * f.natDegree * Real.log X) +
        2 * f.natDegree * Real.sqrt X + 4 * r * (f.natDegree : ℝ) ^ 2 * inputDelta f := by
  let n : ℝ := f.natDegree
  let Δ : ℝ := inputDelta f
  let E := C * (X : ℝ) ^ (1 - 1 / (32 * r : ℝ))
  let D := fun i : IntegerFactorIndex f ↦ fieldLogDiscriminant (IntegerFactorRootField f hf i)
  have hn : 0 ≤ n := by positivity
  have hΔ : 0 ≤ Δ := by positivity
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have ht : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hdisc := integerFactorIndex_weighted_fieldLogDiscriminant_le f hf hdegree
  have hcompare := integer_prime_root_field_comparison f hf X (inputDelta f)
    (integerSquarefreeExceptionalPrimes f)
    (by
      intro p hpX hpnot
      obtain ⟨_, hp⟩ := Nat.mem_primesLE.mp hpX
      let : Fact p.Prime := ⟨hp⟩
      exact integerFactorization_good_prime_root_weight_eq_degreeOne f hf hdegree p hp hpnot)
    (integerSquarefreeExceptionalPrimes_card_le f hf hdegree)
  have h := prime_root_average_strong Finset.univ
    (fun i : IntegerFactorIndex f ↦ (integerFactorWeight f i.val : ℝ))
    (fun i ↦ (primeIdealCountLE (IntegerFactorRootField f hf i) X : ℝ))
    (fun i ↦ r * D i)
    (fun i ↦ (Module.finrank ℚ (IntegerFactorRootField f hf i) : ℝ))
    (primeRootSum f (X + 1) : ℝ) (X.primeCounting : ℝ)
    (∫ t in (2 : ℝ)..(X : ℝ), 1 / Real.log t) E (Real.log X) n (r * Δ)
    (2 * n * Real.sqrt X + 4 * r * n ^ 2 * Δ)
    (fun _ _ ↦ by positivity) hE ht
    (by dsimp [n]; exact_mod_cast integerFactorIndex_weight_sum_le f hf)
    (by dsimp [n]; exact_mod_cast integerFactorIndex_weighted_finrank_sum_le f hf)
    (by
      simp only [show ∀ i : IntegerFactorIndex f,
        (integerFactorWeight f i.val : ℝ) * (r * D i) =
          r * ((integerFactorWeight f i.val : ℝ) * D i) from fun i ↦ by ring,
        ← Finset.mul_sum]
      nlinarith [mul_le_mul_of_nonneg_left hdisc (show (0 : ℝ) ≤ r by positivity)])
    (by intro i _; simpa only [E, D, mul_assoc] using hExternal (IntegerFactorRootField f hf i) X hX)
    (rational_primeCount_estimate_scaled r C hExternal X hX)
    (hcompare.trans (by
      dsimp [n, Δ]
      have hh := mul_nonneg (show (0 : ℝ) ≤ (f.natDegree : ℝ) ^ 2 * inputDelta f by positivity)
        (show 0 ≤ (r : ℝ) - 1 by linarith)
      nlinarith))
  have hweight : (∑ i : IntegerFactorIndex f, (integerFactorWeight f i.val : ℝ)) =
      factorStatistic (f.map (Int.castRingHom ℚ)) := by
    exact_mod_cast integerFactorIndex_weight_sum f hf
  rw [hweight] at h
  apply h.trans
  change E * (32 * n ^ 2 * (r * Δ) + 2 * n * Real.log X) + _ ≤ _
  dsimp only [E, n, Δ] at *
  nlinarith [mul_nonneg hE (show 0 ≤ 32 * (f.natDegree : ℝ) ^ 2 * ((r : ℝ) * inputDelta f) +
    2 * f.natDegree * Real.log (X : ℝ) by positivity)]

end SparseIrred.UpperBounds
