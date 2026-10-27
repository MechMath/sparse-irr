import SparseIrred.UpperBounds.GeneralGapEstimate
import SparseIrred.UpperBounds.GeneralGapError
import SparseIrred.UpperBounds.RawInputBounds

/-! # Remark 16: an explicit cutoff for every fixed positive gap -/
open Polynomial SparseDiv SparseDiv.Appendix
namespace SparseIrred.UpperBounds

noncomputable def scaledInputCutoffExponent (r C₀ : ℕ) (f : ℤ[X]) : ℕ :=
  128 * r * cutoffLog C₀ (r * f.natDegree) (inputDelta f)

noncomputable def scaledPrimeCountingCutoff (r C₀ : ℕ) (f : ℤ[X]) : ℕ :=
  2 ^ scaledInputCutoffExponent r C₀ f

theorem scaledInputCutoffExponent_ge (r C₀ : ℕ) (f : ℤ[X])
    (hr : 1 ≤ r) (hC : 1 ≤ C₀) (hf : 0 < f.natDegree) :
    2560 ≤ scaledInputCutoffExponent r C₀ f := by
  have h := cutoffLog_ge_twenty C₀ (r * f.natDegree) (inputDelta f) hC (by nlinarith)
  unfold scaledInputCutoffExponent
  nlinarith

theorem scaledPrimeCountingCutoff_cast (r C₀ : ℕ) (f : ℤ[X]) :
    (scaledPrimeCountingCutoff r C₀ f : ℝ) =
      (2 : ℝ) ^ (32 * r * (4 * cutoffLog C₀ (r * f.natDegree) (inputDelta f))) := by
  unfold scaledPrimeCountingCutoff scaledInputCutoffExponent
  push_cast
  congr 1
  ring

theorem scaledCutoffLog_le_raw_length (r C₀ : ℕ) (l : ITerms) :
    cutoffLog C₀ (r * (toPolyZ l).natDegree) (inputDelta (toPolyZ l)) ≤
      38 + Nat.clog 2 C₀ + 2 * Nat.clog 2 r + 6 * (encITerms l).length := by
  have h := cutoffLog_le C₀ (r * (toPolyZ l).natDegree) (inputDelta (toPolyZ l))
  have hmul : Nat.clog 2 (r * (toPolyZ l).natDegree) ≤
      Nat.clog 2 r + Nat.clog 2 (toPolyZ l).natDegree := by
    apply Nat.clog_le_of_le_pow
    calc
      _ ≤ 2 ^ Nat.clog 2 r * 2 ^ Nat.clog 2 (toPolyZ l).natDegree :=
        Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _)
      _ = _ := by rw [pow_add]
  have hn := (Nat.clog_mono_right 2 (Nat.le_add_right (toPolyZ l).natDegree 2)).trans
    (raw_input_log_bounds l).1
  have hd : Nat.clog 2 (inputDelta (toPolyZ l) + 1) ≤ inputDelta (toPolyZ l) + 1 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hΔ := inputDelta_le_raw_length l
  omega

/-- Only fixed constants depend on the zero-free gap; the input exponent is linear. -/
theorem scaledInputCutoffExponent_le_raw_length (r C₀ : ℕ) (l : ITerms) :
    scaledInputCutoffExponent r C₀ (toPolyZ l) ≤
      128 * r * (38 + Nat.clog 2 C₀ + 2 * Nat.clog 2 r) +
        768 * r * (encITerms l).length := by
  have h := Nat.mul_le_mul_left (128 * r) (scaledCutoffLog_le_raw_length r C₀ l)
  unfold scaledInputCutoffExponent
  nlinarith

/-- Lemma 14 and Corollary 15, with the larger cutoff required by Remark 16. -/
theorem integer_irreducible_iff_scaledPrimeCounting_threshold
    (r C₀ : ℕ) (f : ℤ[X]) (hr : 1 ≤ r) (hC : 1 ≤ C₀)
    (hf : f.IsPrimitive) (hdegree : 0 < f.natDegree)
    (hExternal : ScaledPrimeIdealEstimate r C₀) :
    Irreducible f ↔
      2 * primeRootSum f (scaledPrimeCountingCutoff r C₀ f) <
        3 * primeCountBelow (scaledPrimeCountingCutoff r C₀ f) := by
  let k := 4 * cutoffLog C₀ (r * f.natDegree) (inputDelta f)
  let X := scaledPrimeCountingCutoff r C₀ f
  have hk : 1 ≤ k := by
    have := cutoffLog_ge_twenty C₀ (r * f.natDegree) (inputDelta f) hC (by nlinarith)
    dsimp [k]
    omega
  have hm := scaledInputCutoffExponent_ge r C₀ f hr hC hdegree
  have hX : 2 < X := by
    have hp : 2 ^ 2 ≤ 2 ^ scaledInputCutoffExponent r C₀ f :=
      Nat.pow_le_pow_right (by decide) (by omega)
    dsimp [X, scaledPrimeCountingCutoff]
    omega
  have hnot : ¬X.Prime := by
    dsimp [X, scaledPrimeCountingCutoff]
    exact Nat.Prime.not_prime_pow (by omega)
  have hcast : (X : ℝ) = (2 : ℝ) ^ (32 * r * k) := scaledPrimeCountingCutoff_cast r C₀ f
  have hamp : 2 ^ 20 * (C₀ : ℝ) * ((r : ℝ) * f.natDegree) ^ 2 *
      ((inputDelta f : ℝ) + k) ^ 2 ≤ (2 : ℝ) ^ k := by
    exact_mod_cast cutoff_amplification C₀ (r * f.natDegree) (inputDelta f) hC (by nlinarith)
  have hprime := rational_primeCount_estimate_scaled r C₀ hExternal X hX
  have herror := integer_prime_root_average_concrete_scaled f hf hdegree r hr C₀
    (by positivity) hExternal X hX
  rw [primeRootSum_succ_of_not_prime f X hnot,
    ← primeCountBelow_eq_primeCounting_of_not_prime X hnot] at herror
  rw [← primeCountBelow_eq_primeCounting_of_not_prime X hnot] at hprime
  rw [hcast] at herror hprime
  have hLi := logIntegral_lower_bound ((2 : ℝ) ^ (32 * r * k)) (by
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ (32 * r * k) := pow_le_pow_right₀ (by norm_num) (by nlinarith))
  have hP := scaled_prime_count_lower_at_cutoff C₀ f.natDegree (inputDelta f)
    (primeCountBelow X) _ r k (by exact_mod_cast hC) (by exact_mod_cast hdegree)
    (by positivity) hr hk hamp hLi hprime
  exact integer_irreducible_iff_root_threshold_of_approximation f hf hdegree X
    (primeCountBelow_pos X hX)
    (scaled_relative_error_lt_quarter C₀ f.natDegree (inputDelta f)
      (primeRootSum f X) (factorStatistic (f.map (Int.castRingHom ℚ)))
      (primeCountBelow X) r k (by exact_mod_cast hC) (by exact_mod_cast hdegree)
      (by positivity) hr hk hamp hP herror)

/-- The actual fixed-width majority gadget retains its exact threshold. -/
theorem scaledPrimeCounting_majority_iff_threshold (r C₀ : ℕ) (f : ℤ[X]) :
    2 ^ (2 * scaledInputCutoffExponent r C₀ f + 5) <
      2 * witnessCount (majorityGadget
        (positivePrimeWitness (scaledPrimeCountingCutoff r C₀ f))
        (negativePrimeWitness f (scaledPrimeCountingCutoff r C₀ f))) ↔
      2 * primeRootSum f (scaledPrimeCountingCutoff r C₀ f) <
        3 * primeCountBelow (scaledPrimeCountingCutoff r C₀ f) :=
  primeWitness_binary_majority_iff f _

end SparseIrred.UpperBounds
