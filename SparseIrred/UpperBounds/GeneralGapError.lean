import SparseIrred.UpperBounds.CutoffError

/-! # Elementary cutoff analysis for every fixed positive gap -/
namespace SparseIrred.UpperBounds

noncomputable def scaledCutoffError (C n Δ : ℝ) (r k : ℕ) : ℝ :=
  2 ^ 14 * C * (r : ℝ) ^ 2 * n ^ 2 * k * (Δ + k) / 2 ^ k +
    256 * r * k * n / 2 ^ (16 * r * k) +
    512 * (r : ℝ) ^ 2 * k * n ^ 2 * Δ / 2 ^ (32 * r * k)

theorem scaledCutoffError_le (C n Δ : ℝ) (r k : ℕ)
    (_hC : 0 ≤ C) (hn : 0 ≤ n) (hΔ : 0 ≤ Δ) (hr : 1 ≤ r) :
    scaledCutoffError C n Δ r k ≤ cutoffError C (r * n) Δ k := by
  have h16 : (2 : ℝ) ^ (16 * k) ≤ 2 ^ (16 * r * k) := by
    apply pow_le_pow_right₀ (by norm_num)
    nlinarith
  have h32 : (2 : ℝ) ^ (32 * k) ≤ 2 ^ (32 * r * k) := by
    apply pow_le_pow_right₀ (by norm_num)
    nlinarith
  unfold scaledCutoffError cutoffError
  apply add_le_add
  · apply add_le_add
    · apply le_of_eq; ring
    · calc
        _ ≤ 256 * r * k * n / (2 : ℝ) ^ (16 * k) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h16
        _ = _ := by ring
  · calc
      _ ≤ 512 * (r : ℝ) ^ 2 * k * n ^ 2 * Δ / (2 : ℝ) ^ (32 * k) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h32
      _ = _ := by ring

theorem scaledCutoffError_lt_quarter (C n Δ : ℝ) (r k : ℕ)
    (hC : 1 ≤ C) (hn : 1 ≤ n) (hΔ : 0 ≤ Δ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (hamp : 2 ^ 20 * C * ((r : ℝ) * n) ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k) :
    scaledCutoffError C n Δ r k < 1 / 4 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  exact lt_of_le_of_lt (scaledCutoffError_le C n Δ r k (by linarith) (by linarith) hΔ hr)
    (cutoffError_lt_quarter C (r * n) Δ k hC (by nlinarith) hΔ hk hamp)

theorem scaled_cutoff_log (r k : ℕ) :
    Real.log ((2 : ℝ) ^ (32 * r * k)) = r * Real.log ((2 : ℝ) ^ (32 * k)) := by
  simp only [Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem scaled_cutoff_log_le (r k : ℕ) :
    Real.log ((2 : ℝ) ^ (32 * r * k)) ≤ 32 * r * k := by
  rw [scaled_cutoff_log]
  have h := mul_le_mul_of_nonneg_left (cutoff_log_le k) (show (0 : ℝ) ≤ r by positivity)
  nlinarith

theorem scaled_cutoff_rpow (r k : ℕ) (hr : 1 ≤ r) :
    ((2 : ℝ) ^ (32 * r * k)) ^ (1 - 1 / (32 * r : ℝ)) =
      (2 : ℝ) ^ (32 * r * k) / (2 : ℝ) ^ k := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have he : ((32 * r * k : ℕ) : ℝ) * (1 - 1 / (32 * r : ℝ)) =
      (32 * r * k : ℕ) - k := by
    push_cast
    field_simp
  rw [he, Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast,
    Real.rpow_natCast]

theorem scaled_cutoff_sqrt (r k : ℕ) :
    Real.sqrt ((2 : ℝ) ^ (32 * r * k)) = (2 : ℝ) ^ (16 * r * k) := by
  rw [show 32 * r * k = (16 * r * k) * 2 by ring, pow_mul, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by positivity)]

theorem scaled_cutoff_prime_error_control (C n Δ : ℝ) (r k : ℕ)
    (hC : 1 ≤ C) (hn : 1 ≤ n) (hΔ : 0 ≤ Δ) (hr : 1 ≤ r)
    (hamp : 2 ^ 20 * C * ((r : ℝ) * n) ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k) :
    4 * C * Real.log ((2 : ℝ) ^ (32 * r * k)) ^ 2 ≤ (2 : ℝ) ^ k := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hamp' : 2 ^ 20 * (C * (r : ℝ) ^ 2) * n ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k := by
    convert hamp using 1
    ring
  have h := cutoff_prime_error_control (C * (r : ℝ) ^ 2) n Δ k (by nlinarith) hn hΔ hamp'
  rw [scaled_cutoff_log]
  convert h using 1
  ring

theorem scaled_prime_count_lower_at_cutoff (C n Δ P Li : ℝ) (r k : ℕ)
    (hC : 1 ≤ C) (hn : 1 ≤ n) (hΔ : 0 ≤ Δ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (hamp : 2 ^ 20 * C * ((r : ℝ) * n) ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k)
    (hLi : (2 : ℝ) ^ (32 * r * k) / (2 * Real.log ((2 : ℝ) ^ (32 * r * k))) ≤ Li)
    (hprime : |P - Li| ≤
      C * ((2 : ℝ) ^ (32 * r * k)) ^ (1 - 1 / (32 * r : ℝ)) *
        Real.log ((2 : ℝ) ^ (32 * r * k))) :
    (2 : ℝ) ^ (32 * r * k) / (128 * r * k) ≤ P := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog0 : 0 < Real.log ((2 : ℝ) ^ (32 * r * k)) := by
    rw [Real.log_pow]
    positivity
  have hcontrol := scaled_cutoff_prime_error_control C n Δ r k hC hn hΔ hr hamp
  have hsmall : C * ((2 : ℝ) ^ (32 * r * k)) ^ (1 - 1 / (32 * r : ℝ)) *
      Real.log ((2 : ℝ) ^ (32 * r * k)) ≤
        (2 : ℝ) ^ (32 * r * k) / (4 * Real.log ((2 : ℝ) ^ (32 * r * k))) := by
    rw [scaled_cutoff_rpow r k hr]
    apply (le_div_iff₀ (by positivity : 0 < 4 *
      Real.log ((2 : ℝ) ^ (32 * r * k)))).2
    rw [show C * ((2 : ℝ) ^ (32 * r * k) / (2 : ℝ) ^ k) *
        Real.log ((2 : ℝ) ^ (32 * r * k)) * (4 * Real.log ((2 : ℝ) ^ (32 * r * k))) =
      (4 * C * Real.log ((2 : ℝ) ^ (32 * r * k)) ^ 2 * (2 : ℝ) ^ (32 * r * k)) /
        (2 : ℝ) ^ k by ring]
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).2
    have h := mul_le_mul_of_nonneg_right hcontrol (by positivity : 0 ≤ (2 : ℝ) ^ (32 * r * k))
    nlinarith
  have hleft := (abs_sub_le_iff.1 hprime).2
  have hhalf : (2 : ℝ) ^ (32 * r * k) / (2 * Real.log ((2 : ℝ) ^ (32 * r * k))) =
      2 * ((2 : ℝ) ^ (32 * r * k) / (4 * Real.log ((2 : ℝ) ^ (32 * r * k)))) := by ring
  have hP : (2 : ℝ) ^ (32 * r * k) / (4 * Real.log ((2 : ℝ) ^ (32 * r * k))) ≤ P := by
    rw [hhalf] at hLi
    linarith
  apply le_trans _ hP
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [scaled_cutoff_log_le r k]

theorem scaledCutoffError_mul_cutoff (C n Δ : ℝ) (r k : ℕ) (hr : 1 ≤ r) (hk : 1 ≤ k) :
    scaledCutoffError C n Δ r k * (2 : ℝ) ^ (32 * r * k) / (128 * r * k) =
      128 * r * C * n ^ 2 * (Δ + k) * (2 : ℝ) ^ (32 * r * k) / (2 : ℝ) ^ k +
        2 * n * (2 : ℝ) ^ (16 * r * k) + 4 * r * n ^ 2 * Δ := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  unfold scaledCutoffError
  rw [show 32 * r * k = (16 * r * k) * 2 by ring, pow_mul]
  field_simp
  ring

theorem scaled_relative_error_lt_quarter (C n Δ A ρ P : ℝ) (r k : ℕ)
    (hC : 1 ≤ C) (hn : 1 ≤ n) (hΔ : 0 ≤ Δ) (hr : 1 ≤ r) (hk : 1 ≤ k)
    (hamp : 2 ^ 20 * C * ((r : ℝ) * n) ^ 2 * (Δ + k) ^ 2 ≤ (2 : ℝ) ^ k)
    (hP : (2 : ℝ) ^ (32 * r * k) / (128 * r * k) ≤ P)
    (herror : |A - ρ * P| ≤
      C * ((2 : ℝ) ^ (32 * r * k)) ^ (1 - 1 / (32 * r : ℝ)) *
          (64 * r * n ^ 2 * Δ + 4 * n * Real.log ((2 : ℝ) ^ (32 * r * k))) +
        2 * n * Real.sqrt ((2 : ℝ) ^ (32 * r * k)) + 4 * r * n ^ 2 * Δ) :
    |A / P - ρ| < 1 / 4 := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hP0 : 0 < P := lt_of_lt_of_le (by positivity) hP
  have hC0 : 0 ≤ C := by linarith
  have hn0 : 0 ≤ n := by linarith
  have herr0 : 0 ≤ scaledCutoffError C n Δ r k := by unfold scaledCutoffError; positivity
  have hbracket : 64 * r * n ^ 2 * Δ + 4 * n * Real.log ((2 : ℝ) ^ (32 * r * k)) ≤
      128 * r * n ^ 2 * (Δ + k) := by
    have hlog := mul_le_mul_of_nonneg_left (scaled_cutoff_log_le r k) (show 0 ≤ 4 * n by positivity)
    have hnk := mul_le_mul_of_nonneg_right (show n ≤ n ^ 2 by nlinarith)
      (show 0 ≤ (r : ℝ) * k by positivity)
    nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) * n ^ 2 by positivity) hΔ]
  have herr : |A - ρ * P| ≤
      128 * r * C * n ^ 2 * (Δ + k) * (2 : ℝ) ^ (32 * r * k) / (2 : ℝ) ^ k +
        2 * n * (2 : ℝ) ^ (16 * r * k) + 4 * r * n ^ 2 * Δ := by
    apply herror.trans
    rw [scaled_cutoff_rpow r k hr, scaled_cutoff_sqrt]
    have hmul := mul_le_mul_of_nonneg_left hbracket
      (show 0 ≤ C * ((2 : ℝ) ^ (32 * r * k) / (2 : ℝ) ^ k) by positivity)
    calc
      _ ≤ C * ((2 : ℝ) ^ (32 * r * k) / (2 : ℝ) ^ k) *
          (128 * r * n ^ 2 * (Δ + k)) +
          2 * n * (2 : ℝ) ^ (16 * r * k) + 4 * r * n ^ 2 * Δ :=
        add_le_add (add_le_add hmul le_rfl) le_rfl
      _ = _ := by ring
  have hm := mul_le_mul_of_nonneg_left hP herr0
  rw [← mul_div_assoc, scaledCutoffError_mul_cutoff C n Δ r k hr hk] at hm
  have habs : |A - ρ * P| ≤ scaledCutoffError C n Δ r k * P := herr.trans hm
  have hdiv : |A / P - ρ| = |A - ρ * P| / P := by
    rw [show A / P - ρ = (A - ρ * P) / P by field_simp, abs_div, abs_of_pos hP0]
  rw [hdiv]
  exact lt_of_le_of_lt ((div_le_iff₀ hP0).2 habs)
    (scaledCutoffError_lt_quarter C n Δ r k hC hn hΔ hr hk hamp)

end SparseIrred.UpperBounds
