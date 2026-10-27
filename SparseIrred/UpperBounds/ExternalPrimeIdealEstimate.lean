import SparseIrred.UpperBounds.RationalPrimeIdeals
import SparseIrred.UpperBounds.PrimeCountingDecision

/-!
# The external effective prime-ideal theorem and its specialization

`EffectivePrimeIdealEstimate` states the conclusion of the external effective
prime-ideal theorem after supplying its uniform zero-free hypothesis. It counts
actual nonzero prime ideals, uses the actual absolute field discriminant, and
quantifies over all number fields and cutoffs before any input polynomial is chosen.

The external estimate is a named proposition used as an explicit hypothesis,
not a new global axiom. This file proves the paper's substitution `δ = 1/32`,
choice of one integer constant, and specialization to rational prime counting.
The paper's own global root-average estimate is not an external assumption here.
-/

namespace SparseIrred.UpperBounds

open NumberField

/-- Logarithm of the actual absolute number-field discriminant. -/
noncomputable def fieldLogDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.log ((NumberField.discr K).natAbs : ℝ)

theorem fieldLogDiscriminant_nonneg (K : Type*) [Field K] [NumberField K] :
    0 ≤ fieldLogDiscriminant K := by
  apply Real.log_nonneg
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (discr_ne_zero K))

/-- The external prime-ideal estimate (3), for integer cutoffs and a fixed zero-free gap.
The real constant is uniform in the field and in the cutoff. All fields used below
are carried by types in `Type`; this includes the polynomial root fields over `ℚ`. -/
def EffectivePrimeIdealEstimate (δ C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : ℕ), 2 < X →
    |(primeIdealCountLE K X : ℝ) - ∫ t in (2 : ℝ)..(X : ℝ), 1 / Real.log t| ≤
      C * (X : ℝ) ^ (1 - δ) *
        (δ⁻¹ * fieldLogDiscriminant K + Module.finrank ℚ K * Real.log X)

/-- The fixed-gap form (4), still an explicit external input at the real constant `C`. -/
def UniformPrimeIdealEstimate (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : ℕ), 2 < X →
    |(primeIdealCountLE K X : ℝ) - ∫ t in (2 : ℝ)..(X : ℝ), 1 / Real.log t| ≤
      C * (X : ℝ) ^ (31 / 32 : ℝ) *
        (32 * fieldLogDiscriminant K + Module.finrank ℚ K * Real.log X)

/-- Substituting the external zero-free gap yields exactly the paper's exponent and factor 32. -/
theorem effectivePrimeIdealEstimate_fixed_gap (C : ℝ)
    (h : EffectivePrimeIdealEstimate (1 / 32) C) : UniformPrimeIdealEstimate C := by
  intro K _ _ X hX
  simpa only [show (1 - 1 / 32 : ℝ) = 31 / 32 by norm_num,
    show (1 / 32 : ℝ)⁻¹ = 32 by norm_num] using h K X hX

/-- Increasing the common constant preserves every field estimate simultaneously. -/
theorem uniformPrimeIdealEstimate_mono {C D : ℝ} (hCD : C ≤ D)
    (h : UniformPrimeIdealEstimate C) : UniformPrimeIdealEstimate D := by
  intro K _ _ X hX
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  have hdisc := fieldLogDiscriminant_nonneg K
  exact (h K X hX).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hCD (by positivity)) (by positivity))

/-- One fixed integer constant works for every field and cutoff. No polynomial is
quantified before the choice of `C₀`, so this is the uniformity required by the algorithm. -/
theorem exists_integer_uniform_primeIdeal_estimate
    (hExternal : ∃ C : ℝ, 0 < C ∧ EffectivePrimeIdealEstimate (1 / 32) C) :
    ∃ C₀ : ℕ, 1 ≤ C₀ ∧ UniformPrimeIdealEstimate C₀ := by
  obtain ⟨C, _hC, h⟩ := hExternal
  refine ⟨max 1 ⌈C⌉₊, le_max_left _ _, ?_⟩
  apply uniformPrimeIdealEstimate_mono (C := C)
  · exact (Nat.le_ceil C).trans (by exact_mod_cast le_max_right 1 ⌈C⌉₊)
  · exact effectivePrimeIdealEstimate_fixed_gap C h

/-- Equation (5) follows by specializing to the actual field `ℚ` and its prime ideals. -/
theorem rational_primeCount_estimate (C : ℝ) (h : UniformPrimeIdealEstimate C)
    (X : ℕ) (hX : 2 < X) :
    |(X.primeCounting : ℝ) - ∫ t in (2 : ℝ)..(X : ℝ), 1 / Real.log t| ≤
      C * (X : ℝ) ^ (31 / 32 : ℝ) * Real.log X := by
  simpa [rational_primeIdealCountLE, fieldLogDiscriminant] using h ℚ X hX

/-- The external estimate supplies the rational-prime input of the cutoff theorem;
the composite cutoff reconciles inclusive analytic and strict streaming counts. -/
theorem primeCountingCutoff_prime_estimate (C₀ : ℕ) (hC : 1 ≤ C₀)
    (h : UniformPrimeIdealEstimate C₀) (f : Polynomial ℤ) (hdeg : 0 < f.natDegree) :
    |(primeCountBelow (primeCountingCutoff C₀ f) : ℝ) -
        ∫ t in (2 : ℝ)..(primeCountingCutoff C₀ f : ℝ), 1 / Real.log t| ≤
      C₀ * (primeCountingCutoff C₀ f : ℝ) ^ (31 / 32 : ℝ) *
        Real.log (primeCountingCutoff C₀ f) := by
  have hm := inputCutoffExponent_ge C₀ f hC hdeg
  have hX : 2 < primeCountingCutoff C₀ f := by
    have hp : 2 ^ 2 ≤ 2 ^ inputCutoffExponent C₀ f :=
      Nat.pow_le_pow_right (by decide) (by omega)
    unfold primeCountingCutoff
    omega
  rw [show primeCountBelow (primeCountingCutoff C₀ f) =
    (primeCountingCutoff C₀ f).primeCounting from (inputCutoff_counts C₀ f hC hdeg).1]
  exact rational_primeCount_estimate C₀ h _ hX

end SparseIrred.UpperBounds
