import Mathlib

/-!
# Numerical aggregation of discriminant bounds

The inequalities in this file are the elementary weighted-sum steps of Lemma 3.1
of the independent prime-counting manuscript. A bound on each number-field
discriminant is an explicit input. This file does not establish that bound from
Mahler measure, the discriminant of a nonmonic polynomial, or the index of an order.
-/

namespace SparseIrred.UpperBounds

open scoped BigOperators

/-- A positive-weight degree budget bounds each individual degree. -/
theorem degree_le_of_weighted_degree_sum {ι : Type*} [Fintype ι]
    (w d : ι → ℝ) (n : ℝ) (hw : ∀ i, 1 ≤ w i) (hd : ∀ i, 0 ≤ d i)
    (hsum : ∑ i, w i * d i ≤ n) (i : ι) : d i ≤ n := by
  have hw0 : ∀ j, 0 ≤ w j := fun j ↦ le_trans (by norm_num) (hw j)
  have hterm : w i * d i ≤ ∑ j, w j * d j :=
    Finset.single_le_sum (fun j _ ↦ mul_nonneg (hw0 j) (hd j)) (Finset.mem_univ i)
  calc
    d i = 1 * d i := by ring
    _ ≤ w i * d i := mul_le_mul_of_nonneg_right (hw i) (hd i)
    _ ≤ n := hterm.trans hsum

/-- Summing the individual field-discriminant estimates gives the first inequality
of Lemma 3.1; the estimates themselves remain explicit hypotheses. -/
theorem weighted_discriminant_sum_bound {ι : Type*} [Fintype ι]
    (w d Dlog : ι → ℝ) (n S : ℝ)
    (hw : ∀ i, 1 ≤ w i) (hd : ∀ i, 1 ≤ d i) (hn : 1 ≤ n) (hS : 1 ≤ S)
    (hsum : ∑ i, w i * d i ≤ n)
    (hdisc : ∀ i, Dlog i ≤ d i * Real.log (d i) + d i * (d i - 1) * Real.log S) :
    ∑ i, w i * Dlog i ≤ n * Real.log n + n * (n - 1) * Real.log S := by
  have hw0 : ∀ i, 0 ≤ w i := fun i ↦ le_trans (by norm_num) (hw i)
  have hd0 : ∀ i, 0 ≤ d i := fun i ↦ le_trans (by norm_num) (hd i)
  have hdn : ∀ i, d i ≤ n := degree_le_of_weighted_degree_sum w d n hw hd0 hsum
  have hln : 0 ≤ Real.log n := Real.log_nonneg hn
  have hlS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hK : 0 ≤ Real.log n + (n - 1) * Real.log S := by positivity
  calc
    ∑ i, w i * Dlog i ≤
        ∑ i, (w i * d i) * (Real.log n + (n - 1) * Real.log S) := by
      apply Finset.sum_le_sum
      intro i _
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (hw0 i)
      have hlog := mul_le_mul_of_nonneg_left
        (Real.log_le_log (by linarith [hd i]) (hdn i)) (hd0 i)
      have hdegree := mul_le_mul_of_nonneg_left (sub_le_sub_right (hdn i) 1)
        (mul_nonneg (hd0 i) hlS)
      nlinarith [hdisc i]
    _ = (∑ i, w i * d i) * (Real.log n + (n - 1) * Real.log S) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ n * (Real.log n + (n - 1) * Real.log S) :=
      mul_le_mul_of_nonneg_right hsum hK
    _ = n * Real.log n + n * (n - 1) * Real.log S := by ring

/-- Upper bounds on the two logarithms convert the discriminant expression into
the quadratic degree bound used in the prime-root estimate. -/
theorem discriminant_expression_le (n S u v Δ : ℝ) (hn : 1 ≤ n) (hS : 1 ≤ S)
    (hu : Real.log n ≤ u) (hv : Real.log S ≤ v) (hΔ : u + v ≤ Δ) :
    n * Real.log n + n * (n - 1) * Real.log S ≤ n ^ 2 * Δ := by
  have hln := Real.log_nonneg hn
  have hlS := Real.log_nonneg hS
  have h1 := mul_le_mul_of_nonneg_right (show n ≤ n ^ 2 by nlinarith) hln
  have h2 := mul_le_mul_of_nonneg_right (show n * (n - 1) ≤ n ^ 2 by nlinarith) hlS
  calc
    _ ≤ n ^ 2 * (Real.log n + Real.log S) := by nlinarith
    _ ≤ n ^ 2 * Δ := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg n)

/-- The numerical part of the weighted field-discriminant bound `sum w log D ≤ n² Δ`. -/
theorem weighted_discriminant_sum_le {ι : Type*} [Fintype ι]
    (w d Dlog : ι → ℝ) (n S u v Δ : ℝ)
    (hw : ∀ i, 1 ≤ w i) (hd : ∀ i, 1 ≤ d i) (hn : 1 ≤ n) (hS : 1 ≤ S)
    (hsum : ∑ i, w i * d i ≤ n)
    (hdisc : ∀ i, Dlog i ≤ d i * Real.log (d i) + d i * (d i - 1) * Real.log S)
    (hu : Real.log n ≤ u) (hv : Real.log S ≤ v) (hΔ : u + v ≤ Δ) :
    ∑ i, w i * Dlog i ≤ n ^ 2 * Δ := by
  exact (weighted_discriminant_sum_bound w d Dlog n S hw hd hn hS hsum hdisc).trans
    (discriminant_expression_le n S u v Δ hn hS hu hv hΔ)

/-- The numerical estimate for the exceptional integer's logarithm, independent
of the base used to supply the nonnegative logarithmic quantities `a` and `b`. -/
theorem exceptional_expression_le (N n a b u v Δ : ℝ) (hNn : N ≤ n) (hn : 0 ≤ n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hau : a ≤ u) (hbv : b ≤ v) (hΔ : u + v ≤ Δ) :
    N * a + (2 * N - 1) * b ≤ 2 * n * Δ := by
  have h1 := mul_le_mul_of_nonneg_right (show N ≤ 2 * n by linarith) ha
  have h2 := mul_le_mul_of_nonneg_right (show 2 * N - 1 ≤ 2 * n by linarith) hb
  calc
    _ ≤ 2 * n * (a + b) := by nlinarith
    _ ≤ 2 * n * Δ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- The natural-logarithm version of the exceptional-discriminant expression. -/
theorem exceptional_log_expression_le (N n S u v Δ : ℝ)
    (hN : 1 ≤ N) (hNn : N ≤ n) (hS : 1 ≤ S)
    (hu : Real.log n ≤ u) (hv : Real.log S ≤ v) (hΔ : u + v ≤ Δ) :
    N * Real.log N + (2 * N - 1) * Real.log S ≤ 2 * n * Δ := by
  apply exceptional_expression_le N n (Real.log N) (Real.log S) u v Δ hNn
    (by linarith) (Real.log_nonneg hN) (Real.log_nonneg hS) _ hv hΔ
  exact (Real.log_le_log (by linarith) hNn).trans hu

/-- The binary-logarithm version used to bound the number of exceptional primes. -/
theorem exceptional_binary_log_expression_le (N n S u v Δ : ℝ)
    (hN : 1 ≤ N) (hNn : N ≤ n) (hS : 1 ≤ S)
    (hu : Real.logb 2 n ≤ u) (hv : Real.logb 2 S ≤ v) (hΔ : u + v ≤ Δ) :
    N * Real.logb 2 N + (2 * N - 1) * Real.logb 2 S ≤ 2 * n * Δ := by
  apply exceptional_expression_le N n (Real.logb 2 N) (Real.logb 2 S) u v Δ hNn
    (by linarith) (Real.logb_nonneg (by norm_num) hN)
    (Real.logb_nonneg (by norm_num) hS) _ hv hΔ
  exact (Real.logb_le_logb_of_le (by norm_num) (by linarith) hNn).trans hu

end SparseIrred.UpperBounds
