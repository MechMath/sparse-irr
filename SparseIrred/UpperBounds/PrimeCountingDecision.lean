import SparseIrred.UpperBounds.CutoffError
import SparseIrred.UpperBounds.PrimeCutoffCounts
import SparseIrred.UpperBounds.PrimeWitnessCount

/-!
# From analytic counting estimates to the concrete majority predicate

This file combines the independent note's cutoff analysis with actual sparse
integer polynomials and actual prime/residue witnesses. The two analytic counting
inequalities are explicit hypotheses; the quarter-error estimate, decision
inequality and majority count are proved consequences. No complexity-class
membership or Turing-machine running-time bound is asserted here.
-/

open Polynomial

namespace SparseIrred.UpperBounds

/-- The actual cutoff integer of the standalone prime-counting proof. -/
noncomputable def primeCountingCutoff (C₀ : ℕ) (f : ℤ[X]) : ℕ :=
  2 ^ inputCutoffExponent C₀ f

theorem primeCountingCutoff_cast (C₀ : ℕ) (f : ℤ[X]) :
    (primeCountingCutoff C₀ f : ℝ) =
      (2 : ℝ) ^ (32 * (4 * cutoffLog C₀ f.natDegree (inputDelta f))) := by
  unfold primeCountingCutoff inputCutoffExponent
  push_cast
  congr 1
  omega

/-- Lemma 5.1 specialized to the real root counters and the actual sparse-input cutoff. -/
theorem primeCounting_relative_error_of_estimates (C₀ : ℕ) (f : ℤ[X]) (hC : 1 ≤ C₀)
    (hf : 0 < f.natDegree)
    (hprime : |(primeCountBelow (primeCountingCutoff C₀ f) : ℝ) -
      ∫ t in (2 : ℝ)..(primeCountingCutoff C₀ f : ℝ), 1 / Real.log t| ≤
        C₀ * (primeCountingCutoff C₀ f : ℝ) ^ (31 / 32 : ℝ) *
          Real.log (primeCountingCutoff C₀ f))
    (haverage : |(primeRootSum f (primeCountingCutoff C₀ f) : ℝ) -
      factorStatistic (f.map (Int.castRingHom ℚ)) *
        (primeCountBelow (primeCountingCutoff C₀ f) : ℝ)| ≤
      C₀ * (primeCountingCutoff C₀ f : ℝ) ^ (31 / 32 : ℝ) *
        (64 * (f.natDegree : ℝ) ^ 2 * inputDelta f +
          4 * f.natDegree * Real.log (primeCountingCutoff C₀ f)) +
        2 * f.natDegree * Real.sqrt (primeCountingCutoff C₀ f) +
        4 * (f.natDegree : ℝ) ^ 2 * inputDelta f) :
    |(primeRootSum f (primeCountingCutoff C₀ f) : ℝ) /
      primeCountBelow (primeCountingCutoff C₀ f) -
        factorStatistic (f.map (Int.castRingHom ℚ))| < 1 / 4 := by
  let k := 4 * cutoffLog C₀ f.natDegree (inputDelta f)
  have hk : 1 ≤ k := by
    have := cutoffLog_ge_twenty C₀ f.natDegree (inputDelta f) hC hf
    dsimp [k]
    omega
  have hamp : 2 ^ 20 * (C₀ : ℝ) * (f.natDegree : ℝ) ^ 2 *
      ((inputDelta f : ℝ) + k) ^ 2 ≤ (2 : ℝ) ^ k := by
    exact_mod_cast cutoff_amplification C₀ f.natDegree (inputDelta f) hC hf
  have hcast : (primeCountingCutoff C₀ f : ℝ) = (2 : ℝ) ^ (32 * k) :=
    primeCountingCutoff_cast C₀ f
  rw [hcast] at hprime haverage
  exact relative_error_lt_quarter_of_counting_estimates C₀ f.natDegree (inputDelta f)
    (primeRootSum f (primeCountingCutoff C₀ f))
    (factorStatistic (f.map (Int.castRingHom ℚ)))
    (primeCountBelow (primeCountingCutoff C₀ f)) k
    (by exact_mod_cast hC) (by exact_mod_cast hf) (by positivity) hk hamp hprime haverage

/-- The exact decision inequality follows from the analytic estimates, rather than
from an assumed quarter-unit approximation. This is still conditional on those estimates. -/
theorem integer_irreducible_iff_primeCounting_threshold (C₀ : ℕ) (f : ℤ[X])
    (hC : 1 ≤ C₀) (hf : f.IsPrimitive) (hdeg : 0 < f.natDegree)
    (hprime : |(primeCountBelow (primeCountingCutoff C₀ f) : ℝ) -
      ∫ t in (2 : ℝ)..(primeCountingCutoff C₀ f : ℝ), 1 / Real.log t| ≤
        C₀ * (primeCountingCutoff C₀ f : ℝ) ^ (31 / 32 : ℝ) *
          Real.log (primeCountingCutoff C₀ f))
    (haverage : |(primeRootSum f (primeCountingCutoff C₀ f) : ℝ) -
      factorStatistic (f.map (Int.castRingHom ℚ)) *
        (primeCountBelow (primeCountingCutoff C₀ f) : ℝ)| ≤
      C₀ * (primeCountingCutoff C₀ f : ℝ) ^ (31 / 32 : ℝ) *
        (64 * (f.natDegree : ℝ) ^ 2 * inputDelta f +
          4 * f.natDegree * Real.log (primeCountingCutoff C₀ f)) +
        2 * f.natDegree * Real.sqrt (primeCountingCutoff C₀ f) +
        4 * (f.natDegree : ℝ) ^ 2 * inputDelta f) :
    Irreducible f ↔ 2 * primeRootSum f (primeCountingCutoff C₀ f) <
      3 * primeCountBelow (primeCountingCutoff C₀ f) := by
  have hm := inputCutoffExponent_ge C₀ f hC hdeg
  have hX : 2 < primeCountingCutoff C₀ f := by
    have hp : 2 ^ 2 ≤ 2 ^ inputCutoffExponent C₀ f :=
      Nat.pow_le_pow_right (by decide) (by omega)
    unfold primeCountingCutoff
    omega
  exact integer_irreducible_iff_root_threshold_of_approximation f hf hdeg _
    (primeCountBelow_pos _ hX)
    (primeCounting_relative_error_of_estimates C₀ f hC hdeg hprime haverage)

/-- Exactly the majority predicate from the independent manuscript, at its actual cutoff. -/
theorem primeCounting_majority_iff_threshold (C₀ : ℕ) (f : ℤ[X]) :
    2 ^ (2 * inputCutoffExponent C₀ f + 5) <
      2 * witnessCount (majorityGadget
        (positivePrimeWitness (primeCountingCutoff C₀ f))
        (negativePrimeWitness f (primeCountingCutoff C₀ f))) ↔
      2 * primeRootSum f (primeCountingCutoff C₀ f) <
        3 * primeCountBelow (primeCountingCutoff C₀ f) :=
  primeWitness_binary_majority_iff f _

/-- The number of binary choices needed by the majority predicate is linear in input length. -/
theorem primeCounting_choice_bits_le (C₀ : ℕ) (f : ℤ[X]) :
    2 * inputCutoffExponent C₀ f + 5 ≤
      256 * (38 + Nat.clog 2 C₀) + 1536 * (encPoly f).length + 5 := by
  have := inputCutoffExponent_le C₀ f
  omega

end SparseIrred.UpperBounds
