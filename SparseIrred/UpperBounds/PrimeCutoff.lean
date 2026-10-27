import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# The prime-count cutoff has a short binary exponent

The numerical amplification inequality (42) in Section 3.5 is proved over naturals,
with exactly the constants and the ceiling logarithm used in the paper. Analytic
prime-count estimates are not hypotheses or conclusions of this file.
-/

namespace SparseIrred.UpperBounds

theorem two_pow_three_mul_ge (ell : ℕ) (hell : 2 ≤ ell) :
    16 * ell ^ 2 ≤ 2 ^ (3 * ell) := by
  induction ell, hell using Nat.le_induction with
  | base => norm_num
  | succ ell hell ih =>
    have he : 2 ^ (3 * (ell + 1)) = 8 * 2 ^ (3 * ell) := by
      rw [Nat.mul_add, pow_add]
      norm_num
      ring
    rw [he]
    nlinarith

/-- The integer `U` of Section 3.5. -/
def cutoffScale (C₀ n Δ : ℕ) : ℕ := 2 ^ 20 * C₀ * n ^ 2 * (Δ + 1) ^ 2

/-- Ceiling logarithm, as in the paper. -/
def cutoffLog (C₀ n Δ : ℕ) : ℕ := Nat.clog 2 (cutoffScale C₀ n Δ)

theorem cutoffLog_ge_twenty (C₀ n Δ : ℕ) (hC : 1 ≤ C₀) (hn : 1 ≤ n) :
    20 ≤ cutoffLog C₀ n Δ := by
  have hb : 2 ^ 20 ≤ cutoffScale C₀ n Δ := by
    have hn2 : 1 ≤ n ^ 2 := by nlinarith
    have hd : 1 ≤ (Δ + 1) ^ 2 := by
      simpa using Nat.pow_le_pow_left (show 1 ≤ Δ + 1 by omega) 2
    unfold cutoffScale
    calc
      2 ^ 20 ≤ 2 ^ 20 * C₀ := Nat.le_mul_of_pos_right _ hC
      _ ≤ 2 ^ 20 * C₀ * n ^ 2 := Nat.le_mul_of_pos_right _ hn2
      _ ≤ _ := Nat.le_mul_of_pos_right _ hd
  have h := Nat.clog_mono_right 2 hb
  change Nat.clog 2 (2 ^ 20) ≤ cutoffLog C₀ n Δ at h
  rwa [Nat.clog_pow 2 20 (by decide)] at h

/-- Equation (42), with `k = 4 ell`. -/
theorem cutoff_amplification (C₀ n Δ : ℕ) (hC : 1 ≤ C₀) (hn : 1 ≤ n) :
    2 ^ 20 * C₀ * n ^ 2 * (Δ + 4 * cutoffLog C₀ n Δ) ^ 2 ≤
      2 ^ (4 * cutoffLog C₀ n Δ) := by
  let ell := cutoffLog C₀ n Δ
  have hell : 20 ≤ ell := cutoffLog_ge_twenty C₀ n Δ hC hn
  have hu : cutoffScale C₀ n Δ ≤ 2 ^ ell := Nat.le_pow_clog (by decide) _
  have hexp := two_pow_three_mul_ge ell (by omega)
  have hd : Δ + 4 * ell ≤ 4 * ell * (Δ + 1) := by nlinarith
  have hd2 : (Δ + 4 * ell) ^ 2 ≤ 16 * ell ^ 2 * (Δ + 1) ^ 2 := by nlinarith
  calc
    _ ≤ cutoffScale C₀ n Δ * (16 * ell ^ 2) := by
      unfold cutoffScale
      nlinarith [Nat.mul_le_mul_left (2 ^ 20 * C₀ * n ^ 2) hd2]
    _ ≤ 2 ^ ell * 2 ^ (3 * ell) := Nat.mul_le_mul hu hexp
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- A polynomial bound on `U`'s logarithm in the logarithms of its factors.
Consequently the cutoff `X = 2^(128 ell)` enumerates integers of polynomial bit length. -/
theorem cutoffLog_le (C₀ n Δ : ℕ) :
    cutoffLog C₀ n Δ ≤
      20 + Nat.clog 2 C₀ + 2 * Nat.clog 2 n + 2 * Nat.clog 2 (Δ + 1) := by
  apply Nat.clog_le_of_le_pow
  unfold cutoffScale
  calc
    _ ≤ 2 ^ 20 * 2 ^ Nat.clog 2 C₀ * (2 ^ Nat.clog 2 n) ^ 2 *
        (2 ^ Nat.clog 2 (Δ + 1)) ^ 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _
        (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) C₀))
          (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) n) 2))
        (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (Δ + 1)) 2)
    _ = _ := by
      simp_rw [← pow_mul, ← pow_add]
      congr 1
      omega

end SparseIrred.UpperBounds
