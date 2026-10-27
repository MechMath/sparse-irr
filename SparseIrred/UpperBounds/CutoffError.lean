import Mathlib
import SparseIrred.UpperBounds.PrimeCutoff

/-!
# Numerical error bounds at the prime-count cutoff

This file proves the numerical estimate in Lemma 5.1 of the independent
prime-counting manuscript. The analytic prime-count estimates remain explicit inputs;
the quarter-error conclusion is derived from the amplification inequality.
-/

namespace SparseIrred.UpperBounds

/-- The elementary logarithmic-integral estimate used in Lemma 5.1. -/
theorem logIntegral_lower_bound (X : ℝ) (hX : 4 ≤ X) :
    X / (2 * Real.log X) ≤ ∫ t in (2 : ℝ)..X, 1 / Real.log t := by
  have hc : ∀ a b : ℝ, 1 < a → a ≤ b →
      ContinuousOn (fun t : ℝ ↦ 1 / Real.log t) (Set.Icc a b) := by
    intro a b ha hab t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    exact (continuousAt_const.div (Real.continuousAt_log (by linarith))
      (ne_of_gt (Real.log_pos ht1))).continuousWithinAt
  have hleft : IntervalIntegrable (fun t : ℝ ↦ 1 / Real.log t)
      MeasureTheory.volume 2 (X / 2) :=
    (hc 2 (X / 2) (by norm_num) (by linarith)).intervalIntegrable_of_Icc (by linarith)
  have hright : IntervalIntegrable (fun t : ℝ ↦ 1 / Real.log t)
      MeasureTheory.volume (X / 2) X :=
    (hc (X / 2) X (by linarith) (by linarith)).intervalIntegrable_of_Icc (by linarith)
  have hnonneg : 0 ≤ ∫ t in (2 : ℝ)..(X / 2), 1 / Real.log t := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact one_div_nonneg.mpr (le_of_lt (Real.log_pos (by linarith [ht.1])))
  have hpiece : X / (2 * Real.log X) ≤ ∫ t in (X / 2)..X, 1 / Real.log t := by
    have h := intervalIntegral.integral_mono_on (show X / 2 ≤ X by linarith)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ 1 / Real.log X)
        MeasureTheory.volume (X / 2) X) hright (fun t ht ↦ by
          apply one_div_le_one_div_of_le
          · exact Real.log_pos (by linarith [ht.1])
          · exact Real.log_le_log (by linarith [ht.1]) ht.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul,
      show (X - X / 2) * (1 / Real.log X) = X / (2 * Real.log X) by ring] using h
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

/-- The three normalized error terms in equation (25) of the independent manuscript. -/
noncomputable def cutoffError (C n Δ : ℝ) (k : ℕ) : ℝ :=
  2 ^ 14 * C * n ^ 2 * k * (Δ + k) / 2 ^ k +
    256 * k * n / 2 ^ (16 * k) + 512 * k * n ^ 2 * Δ / 2 ^ (32 * k)

/-- The amplification inequality bounds each summand by `1/64`, with room to spare. -/
theorem cutoffError_le (C n Δ : ℝ) (k : ℕ) (hC : 1 ≤ C) (hn : 1 ≤ n)
    (hΔ : 0 ≤ Δ) (hk : 1 ≤ k)
    (hamp : 2 ^ 20 * C * n ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k) :
    cutoffError C n Δ k ≤ 3 / 64 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hC0 : 0 ≤ C := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hd : 1 ≤ Δ + k := by linarith
  have hd0 : 0 ≤ Δ + k := by linarith
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have hkn : (k : ℝ) * n ≤ C * n ^ 2 * (Δ + k) ^ 2 := by
    have h1 : (k : ℝ) ≤ (Δ + k) ^ 2 := by nlinarith
    calc
      (k : ℝ) * n ≤ (Δ + k) ^ 2 * n := mul_le_mul_of_nonneg_right h1 hn0
      _ ≤ (Δ + k) ^ 2 * n ^ 2 := by gcongr; nlinarith
      _ = 1 * (n ^ 2 * (Δ + k) ^ 2) := by ring
      _ ≤ C * (n ^ 2 * (Δ + k) ^ 2) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      _ = C * n ^ 2 * (Δ + k) ^ 2 := by ring
  have hkd : (k : ℝ) * Δ ≤ (Δ + k) ^ 2 := by nlinarith
  have hfirst : 2 ^ 14 * C * n ^ 2 * k * (Δ + k) / (2 : ℝ) ^ k ≤ 1 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).2
    have h1 : (k : ℝ) * (Δ + k) ≤ (Δ + k) ^ 2 := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ C * n ^ 2)
    norm_num at hamp ⊢
    nlinarith
  have hpow16 : (2 : ℝ) ^ k ≤ 2 ^ (16 * k) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hsecond : 256 * k * n / (2 : ℝ) ^ (16 * k) ≤ 1 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (16 * k))).2
    norm_num at hamp ⊢
    nlinarith
  have hpow32 : (2 : ℝ) ^ k ≤ 2 ^ (32 * k) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hthird : 512 * k * n ^ 2 * Δ / (2 : ℝ) ^ (32 * k) ≤ 1 / 64 := by
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ (32 * k))).2
    have h1 := mul_le_mul_of_nonneg_left hkd (by positivity : 0 ≤ n ^ 2)
    have h2 : n ^ 2 * (Δ + k) ^ 2 ≤ C * n ^ 2 * (Δ + k) ^ 2 := by
      calc
        _ = 1 * (n ^ 2 * (Δ + k) ^ 2) := by ring
        _ ≤ C * (n ^ 2 * (Δ + k) ^ 2) :=
          mul_le_mul_of_nonneg_right hC (by positivity)
        _ = _ := by ring
    norm_num at hamp ⊢
    nlinarith
  unfold cutoffError
  linarith

/-- Equation (25) is strictly smaller than the quarter-error margin. -/
theorem cutoffError_lt_quarter (C n Δ : ℝ) (k : ℕ) (hC : 1 ≤ C) (hn : 1 ≤ n)
    (hΔ : 0 ≤ Δ) (hk : 1 ≤ k)
    (hamp : 2 ^ 20 * C * n ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k) :
    cutoffError C n Δ k < 1 / 4 := by
  have h := cutoffError_le C n Δ k hC hn hΔ hk hamp
  linarith

/-- Clearing the prime-count lower bound produces exactly equation (25). -/
theorem cutoffError_mul_cutoff (C n Δ : ℝ) (k : ℕ) (hk : 0 < k) :
    cutoffError C n Δ k * (2 : ℝ) ^ (32 * k) / (128 * k) =
      128 * C * n ^ 2 * (Δ + k) * (2 : ℝ) ^ (32 * k) / (2 : ℝ) ^ k +
        2 * n * (2 : ℝ) ^ (16 * k) + 4 * n ^ 2 * Δ := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold cutoffError
  rw [show 16 * k = k * 16 by omega, show 32 * k = k * 32 by omega]
  simp only [pow_mul]
  field_simp
  ring

/-- The real logarithm of the cutoff is at most its binary exponent. -/
theorem cutoff_log_le (k : ℕ) : Real.log ((2 : ℝ) ^ (32 * k)) ≤ 32 * k := by
  rw [Real.log_pow]
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  push_cast
  nlinarith

/-- At the chosen cutoff, the analytic exponent becomes an integer-power quotient. -/
theorem cutoff_rpow (k : ℕ) :
    ((2 : ℝ) ^ (32 * k)) ^ (31 / 32 : ℝ) =
      (2 : ℝ) ^ (32 * k) / (2 : ℝ) ^ k := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have he : ((32 * k : ℕ) : ℝ) * (31 / 32 : ℝ) = (32 * k : ℕ) - k := by
    push_cast
    ring
  rw [he, Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast,
    Real.rpow_natCast]

/-- The square root of the cutoff also has an exact binary exponent. -/
theorem cutoff_sqrt (k : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (32 * k)) = (2 : ℝ) ^ (16 * k) := by
  rw [show 32 * k = (16 * k) * 2 by omega, pow_mul, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity)]

/-- The amplification inequality makes the prime-counting analytic error small. -/
theorem cutoff_prime_error_control (C n Δ : ℝ) (k : ℕ)
    (hC : 1 ≤ C) (hn : 1 ≤ n) (hΔ : 0 ≤ Δ)
    (hamp : 2 ^ 20 * C * n ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k) :
    4 * C * Real.log ((2 : ℝ) ^ (32 * k)) ^ 2 ≤ (2 : ℝ) ^ k := by
  have hC0 : 0 ≤ C := by linarith
  have hlog0 : 0 ≤ Real.log ((2 : ℝ) ^ (32 * k)) := by
    rw [Real.log_pow]
    positivity
  have hlog2 : Real.log ((2 : ℝ) ^ (32 * k)) ^ 2 ≤ (32 * (k : ℝ)) ^ 2 := by
    nlinarith [cutoff_log_le k]
  have hlogC := mul_le_mul_of_nonneg_left hlog2 hC0
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hd2 : (k : ℝ) ^ 2 ≤ (Δ + k) ^ 2 := by nlinarith
  have hdC := mul_le_mul_of_nonneg_left hd2 hC0
  have hnC := mul_le_mul_of_nonneg_left (show 1 ≤ n ^ 2 by nlinarith)
    (show 0 ≤ C * (Δ + k) ^ 2 by positivity)
  norm_num at hamp
  nlinarith [mul_nonneg hC0 (sq_nonneg (k : ℝ))]

/-- Equation (23), derived from the logarithmic-integral lower bound and the
analytic prime-counting estimate (5), rather than assuming a prime-count lower bound. -/
theorem prime_count_lower_at_cutoff (C n Δ P Li : ℝ) (k : ℕ)
    (hC : 1 ≤ C) (hn : 1 ≤ n) (hΔ : 0 ≤ Δ) (hk : 1 ≤ k)
    (hamp : 2 ^ 20 * C * n ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k)
    (hLi : (2 : ℝ) ^ (32 * k) / (2 * Real.log ((2 : ℝ) ^ (32 * k))) ≤ Li)
    (hprime : |P - Li| ≤
      C * ((2 : ℝ) ^ (32 * k)) ^ (31 / 32 : ℝ) *
        Real.log ((2 : ℝ) ^ (32 * k))) :
    (2 : ℝ) ^ (32 * k) / (4 * Real.log ((2 : ℝ) ^ (32 * k))) ≤ P ∧
      (2 : ℝ) ^ (32 * k) / (128 * k) ≤
        (2 : ℝ) ^ (32 * k) / (4 * Real.log ((2 : ℝ) ^ (32 * k))) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hlog0 : 0 < Real.log ((2 : ℝ) ^ (32 * k)) := by
    rw [Real.log_pow]
    positivity
  have hcontrol := cutoff_prime_error_control C n Δ k hC hn hΔ hamp
  have hsmall : C * ((2 : ℝ) ^ (32 * k)) ^ (31 / 32 : ℝ) *
      Real.log ((2 : ℝ) ^ (32 * k)) ≤
        (2 : ℝ) ^ (32 * k) / (4 * Real.log ((2 : ℝ) ^ (32 * k))) := by
    rw [cutoff_rpow]
    apply (le_div_iff₀ (by positivity : 0 < 4 *
      Real.log ((2 : ℝ) ^ (32 * k)))).2
    rw [show C * ((2 : ℝ) ^ (32 * k) / (2 : ℝ) ^ k) *
        Real.log ((2 : ℝ) ^ (32 * k)) * (4 * Real.log ((2 : ℝ) ^ (32 * k))) =
      (4 * C * Real.log ((2 : ℝ) ^ (32 * k)) ^ 2 * (2 : ℝ) ^ (32 * k)) /
        (2 : ℝ) ^ k by ring]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).2
    have h := mul_le_mul_of_nonneg_right hcontrol
      (by positivity : 0 ≤ (2 : ℝ) ^ (32 * k))
    nlinarith
  have hleft := (abs_sub_le_iff.1 hprime).2
  have hhalf : (2 : ℝ) ^ (32 * k) / (2 * Real.log ((2 : ℝ) ^ (32 * k))) =
      2 * ((2 : ℝ) ^ (32 * k) / (4 * Real.log ((2 : ℝ) ^ (32 * k)))) := by
    ring
  constructor
  · rw [hhalf] at hLi
    linarith
  · apply div_le_div_of_nonneg_left (by positivity)
      (by positivity : 0 < 4 * Real.log ((2 : ℝ) ^ (32 * k)))
    nlinarith [cutoff_log_le k]

/-- The explicit error in Proposition 4.1 implies the quarter-error conclusion once
the prime-count lower bound of Lemma 5.1 is available. -/
theorem relative_error_lt_quarter (C n Δ A ρ P : ℝ) (k : ℕ)
    (hC : 1 ≤ C) (hn : 1 ≤ n) (hΔ : 0 ≤ Δ) (hk : 1 ≤ k)
    (hamp : 2 ^ 20 * C * n ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k)
    (hP : (2 : ℝ) ^ (32 * k) / (128 * k) ≤ P)
    (herror : |A - ρ * P| ≤
      128 * C * n ^ 2 * (Δ + k) * (2 : ℝ) ^ (32 * k) / (2 : ℝ) ^ k +
        2 * n * (2 : ℝ) ^ (16 * k) + 4 * n ^ 2 * Δ) :
    |A / P - ρ| < 1 / 4 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have herr0 : 0 ≤ cutoffError C n Δ k := by
    unfold cutoffError
    have hC0 : 0 ≤ C := by linarith
    have hn0 : 0 ≤ n := by linarith
    positivity
  have hm := mul_le_mul_of_nonneg_left hP herr0
  rw [← mul_div_assoc, cutoffError_mul_cutoff C n Δ k (by omega)] at hm
  have habs : |A - ρ * P| ≤ cutoffError C n Δ k * P := herror.trans hm
  have hdiv : |A / P - ρ| = |A - ρ * P| / P := by
    rw [show A / P - ρ = (A - ρ * P) / P by field_simp]
    rw [abs_div, abs_of_pos hP0]
  rw [hdiv]
  exact lt_of_le_of_lt ((div_le_iff₀ hP0).2 habs)
    (cutoffError_lt_quarter C n Δ k hC hn hΔ hk hamp)

/-- Proposition 4.1's original analytic error bound gives equation (24), with exactly
the cutoff and constants in the independent manuscript. -/
theorem relative_error_lt_quarter_of_analytic_bound (C n Δ A ρ P : ℝ) (k : ℕ)
    (hC : 1 ≤ C) (hn : 1 ≤ n) (hΔ : 0 ≤ Δ) (hk : 1 ≤ k)
    (hamp : 2 ^ 20 * C * n ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k)
    (hP : (2 : ℝ) ^ (32 * k) / (128 * k) ≤ P)
    (herror : |A - ρ * P| ≤
      C * ((2 : ℝ) ^ (32 * k)) ^ (31 / 32 : ℝ) *
          (64 * n ^ 2 * Δ + 4 * n * Real.log ((2 : ℝ) ^ (32 * k))) +
        2 * n * Real.sqrt ((2 : ℝ) ^ (32 * k)) + 4 * n ^ 2 * Δ) :
    |A / P - ρ| < 1 / 4 := by
  apply relative_error_lt_quarter C n Δ A ρ P k hC hn hΔ hk hamp hP
  apply herror.trans
  rw [cutoff_rpow, cutoff_sqrt]
  have hC0 : 0 ≤ C := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hnk : n * (k : ℝ) ≤ n ^ 2 * k :=
    mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  have hlog := mul_le_mul_of_nonneg_left (cutoff_log_le k) (by positivity : 0 ≤ 4 * n)
  have hbracket : 64 * n ^ 2 * Δ + 4 * n * Real.log ((2 : ℝ) ^ (32 * k)) ≤
      128 * n ^ 2 * (Δ + k) := by
    nlinarith [mul_nonneg (sq_nonneg n) hΔ]
  have hmul := mul_le_mul_of_nonneg_left hbracket
    (by positivity : 0 ≤ C * ((2 : ℝ) ^ (32 * k) / (2 : ℝ) ^ k))
  calc
    _ ≤ C * ((2 : ℝ) ^ (32 * k) / (2 : ℝ) ^ k) *
          (128 * n ^ 2 * (Δ + k)) + 2 * n * (2 : ℝ) ^ (16 * k) + 4 * n ^ 2 * Δ :=
      add_le_add (add_le_add hmul le_rfl) le_rfl
    _ = _ := by ring

/-- The two analytic counting estimates together imply the quarter-error conclusion;
no prime-count lower bound or relative-error estimate is assumed. -/
theorem relative_error_lt_quarter_of_prime_estimates (C n Δ A ρ P Li : ℝ) (k : ℕ)
    (hC : 1 ≤ C) (hn : 1 ≤ n) (hΔ : 0 ≤ Δ) (hk : 1 ≤ k)
    (hamp : 2 ^ 20 * C * n ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k)
    (hLi : (2 : ℝ) ^ (32 * k) / (2 * Real.log ((2 : ℝ) ^ (32 * k))) ≤ Li)
    (hprime : |P - Li| ≤
      C * ((2 : ℝ) ^ (32 * k)) ^ (31 / 32 : ℝ) *
        Real.log ((2 : ℝ) ^ (32 * k)))
    (herror : |A - ρ * P| ≤
      C * ((2 : ℝ) ^ (32 * k)) ^ (31 / 32 : ℝ) *
          (64 * n ^ 2 * Δ + 4 * n * Real.log ((2 : ℝ) ^ (32 * k))) +
        2 * n * Real.sqrt ((2 : ℝ) ^ (32 * k)) + 4 * n ^ 2 * Δ) :
    |A / P - ρ| < 1 / 4 := by
  have hP := prime_count_lower_at_cutoff C n Δ P Li k hC hn hΔ hk hamp hLi hprime
  exact relative_error_lt_quarter_of_analytic_bound C n Δ A ρ P k hC hn hΔ hk hamp
    (hP.2.trans hP.1) herror

/-- Lemma 5.1's quarter-error estimate from the two counting inequalities, taking
`Li(X)` to be the integral of `1/log(t)` from `2` to `X`. -/
theorem relative_error_lt_quarter_of_counting_estimates (C n Δ A ρ P : ℝ) (k : ℕ)
    (hC : 1 ≤ C) (hn : 1 ≤ n) (hΔ : 0 ≤ Δ) (hk : 1 ≤ k)
    (hamp : 2 ^ 20 * C * n ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k)
    (hprime : |P - ∫ t in (2 : ℝ)..((2 : ℝ) ^ (32 * k)), 1 / Real.log t| ≤
      C * ((2 : ℝ) ^ (32 * k)) ^ (31 / 32 : ℝ) *
        Real.log ((2 : ℝ) ^ (32 * k)))
    (herror : |A - ρ * P| ≤
      C * ((2 : ℝ) ^ (32 * k)) ^ (31 / 32 : ℝ) *
          (64 * n ^ 2 * Δ + 4 * n * Real.log ((2 : ℝ) ^ (32 * k))) +
        2 * n * Real.sqrt ((2 : ℝ) ^ (32 * k)) + 4 * n ^ 2 * Δ) :
    |A / P - ρ| < 1 / 4 := by
  have hX : 4 ≤ (2 : ℝ) ^ (32 * k) := by
    calc
      4 = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ (32 * k) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact relative_error_lt_quarter_of_prime_estimates C n Δ A ρ P _ k hC hn hΔ hk hamp
    (logIntegral_lower_bound _ hX) hprime herror

/-- The integer cutoff defined in the manuscript satisfies the normalized numerical
error estimate without further hypotheses on its exponent. -/
theorem cutoffError_lt_quarter_at_cutoff (C n Δ : ℕ) (hC : 1 ≤ C) (hn : 1 ≤ n) :
    cutoffError C n Δ (4 * cutoffLog C n Δ) < 1 / 4 := by
  apply cutoffError_lt_quarter
  · exact_mod_cast hC
  · exact_mod_cast hn
  · positivity
  · have h := cutoffLog_ge_twenty C n Δ hC hn
    omega
  · exact_mod_cast cutoff_amplification C n Δ hC hn

end SparseIrred.UpperBounds
