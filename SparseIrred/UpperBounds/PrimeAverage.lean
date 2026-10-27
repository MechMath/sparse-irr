import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# From prime-ideal estimates to the prime-root average

This file formalizes the summation argument in Proposition 4.1 of
`sparse_irreducibility_complete_qrh.pdf`. The individual number-field prime-ideal
estimates and the root/degree-one-prime-ideal correspondence are explicit inputs.
They are not proved by these conditional estimates. No analytic hypothesis is
introduced as an axiom.
-/

namespace SparseIrred.UpperBounds

open scoped BigOperators

/-- A discrepancy supported on finitely many exceptional indices costs at most
the number of exceptional indices times the pointwise discrepancy bound. -/
theorem exceptional_sum_bound {ι : Type*} [DecidableEq ι] (s bad : Finset ι)
    (a b : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hgood : ∀ p ∈ s, p ∉ bad → a p = b p)
    (hbound : ∀ p ∈ s, |a p - b p| ≤ M) :
    |(∑ p ∈ s, a p) - ∑ p ∈ s, b p| ≤ (bad.card : ℝ) * M := by
  have hlocal (p : ι) (hp : p ∈ s) :
      |a p - b p| ≤ if p ∈ bad then M else 0 := by
    by_cases hb : p ∈ bad
    · simpa [hb] using hbound p hp
    · simp [hb, hgood p hp hb]
  have hcard : (s.filter fun p ↦ p ∈ bad).card ≤ bad.card := by
    apply Finset.card_le_card
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  calc
    |(∑ p ∈ s, a p) - ∑ p ∈ s, b p| = |∑ p ∈ s, (a p - b p)| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ p ∈ s, |a p - b p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ s, if p ∈ bad then M else 0 := Finset.sum_le_sum hlocal
    _ = ((s.filter fun p ↦ p ∈ bad).card : ℝ) * M := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (bad.card : ℝ) * M :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM

/-- Equation (20), derived from good-prime equality, the exceptional-prime
cardinality bound, and the separately bounded higher-residue-degree contribution.
The finite index set may be the rational primes up to the cutoff. -/
theorem prime_root_field_comparison {ι : Type*} [DecidableEq ι] (s bad : Finset ι)
    (a b : ι → ℝ) (F n Δ X : ℝ) (hn : 0 ≤ n)
    (hgood : ∀ p ∈ s, p ∉ bad → a p = b p)
    (hbound : ∀ p ∈ s, |a p - b p| ≤ 2 * n)
    (hbad : (bad.card : ℝ) ≤ 2 * n * Δ)
    (hhigher : 0 ≤ F - ∑ p ∈ s, b p)
    (hhigher_le : F - ∑ p ∈ s, b p ≤ n * Real.sqrt X) :
    |(∑ p ∈ s, a p) - F| ≤ 2 * n * Real.sqrt X + 4 * n ^ 2 * Δ := by
  have hex := exceptional_sum_bound s bad a b (2 * n) (by positivity) hgood hbound
  have hex' : |(∑ p ∈ s, a p) - ∑ p ∈ s, b p| ≤ 4 * n ^ 2 * Δ := by
    calc
      _ ≤ (bad.card : ℝ) * (2 * n) := hex
      _ ≤ (2 * n * Δ) * (2 * n) :=
        mul_le_mul_of_nonneg_right hbad (by positivity)
      _ = _ := by ring
  have hfield : |(∑ p ∈ s, b p) - F| ≤ n * Real.sqrt X := by
    rw [abs_sub_comm, abs_of_nonneg hhigher]
    exact hhigher_le
  have htri := abs_sub_le (∑ p ∈ s, a p) (∑ p ∈ s, b p) F
  have hsqrt : 0 ≤ n * Real.sqrt X := mul_nonneg hn (Real.sqrt_nonneg X)
  linarith

/-- Weighted aggregation of the higher-residue-degree contributions. The
pointwise inputs follow from bounding the number of prime ideals above each
rational prime and counting rational primes up to the square root of the cutoff. -/
theorem weighted_higher_degree_bound {ι : Type*} (s : Finset ι)
    (w π π₁ d : ι → ℝ) (n X : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hdegree : (∑ i ∈ s, w i * d i) ≤ n)
    (hnonneg : ∀ i ∈ s, 0 ≤ π i - π₁ i)
    (hhigher : ∀ i ∈ s, π i - π₁ i ≤ d i * Real.sqrt X) :
    0 ≤ (∑ i ∈ s, w i * π i) - ∑ i ∈ s, w i * π₁ i ∧
      (∑ i ∈ s, w i * π i) - (∑ i ∈ s, w i * π₁ i) ≤ n * Real.sqrt X := by
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  constructor
  · exact Finset.sum_nonneg fun i hi ↦ mul_nonneg (hw i hi) (hnonneg i hi)
  · calc
      _ ≤ ∑ i ∈ s, w i * (d i * Real.sqrt X) := by
        exact Finset.sum_le_sum fun i hi ↦
          mul_le_mul_of_nonneg_left (hhigher i hi) (hw i hi)
      _ = (∑ i ∈ s, w i * d i) * Real.sqrt X := by
        simp only [Finset.sum_mul, mul_assoc]
      _ ≤ n * Real.sqrt X :=
        mul_le_mul_of_nonneg_right hdegree (Real.sqrt_nonneg X)

/-- Summation of individual prime-ideal errors with nonnegative weights. This
is an algebraic consequence of the supplied local analytic estimates. -/
theorem weighted_prime_ideal_error {ι : Type*} (s : Finset ι)
    (w π D d : ι → ℝ) (Li E t : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hlocal : ∀ i ∈ s, |π i - Li| ≤ E * (32 * D i + d i * t)) :
    |(∑ i ∈ s, w i * π i) - (∑ i ∈ s, w i) * Li| ≤
      E * (32 * (∑ i ∈ s, w i * D i) + (∑ i ∈ s, w i * d i) * t) := by
  calc
    _ = |∑ i ∈ s, w i * (π i - Li)| := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    _ ≤ ∑ i ∈ s, |w i * (π i - Li)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ s, w i * |π i - Li| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]
    _ ≤ ∑ i ∈ s, w i * (E * (32 * D i + d i * t)) := by
      exact Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hlocal i hi) (hw i hi)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
      congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

/-- The stronger version of Proposition 4.1: local analytic estimates, the
weighted discriminant and degree bounds, and the root/field comparison imply
the global error bound. `D i` denotes `log Dᵢ`, and `t` denotes `log X`. -/
theorem prime_root_average_strong {ι : Type*} (s : Finset ι)
    (w π D d : ι → ℝ) (A P Li E t n Δ R : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hE : 0 ≤ E) (ht : 0 ≤ t)
    (hρ : (∑ i ∈ s, w i) ≤ n)
    (hdegree : (∑ i ∈ s, w i * d i) ≤ n)
    (hdiscriminant : (∑ i ∈ s, w i * D i) ≤ n ^ 2 * Δ)
    (hlocal : ∀ i ∈ s, |π i - Li| ≤ E * (32 * D i + d i * t))
    (hQ : |P - Li| ≤ E * t)
    (hcompare : |A - ∑ i ∈ s, w i * π i| ≤ R) :
    |A - (∑ i ∈ s, w i) * P| ≤ E * (32 * n ^ 2 * Δ + 2 * n * t) + R := by
  let W := ∑ i ∈ s, w i
  let F := ∑ i ∈ s, w i * π i
  have hW : 0 ≤ W := Finset.sum_nonneg hw
  have hρ' : W ≤ n := hρ
  have hfield : |F - W * Li| ≤ E * (32 * n ^ 2 * Δ + n * t) := by
    refine (weighted_prime_ideal_error s w π D d Li E t hw hlocal).trans ?_
    apply mul_le_mul_of_nonneg_left _ hE
    nlinarith [mul_le_mul_of_nonneg_right hdegree ht]
  have hbase : |W * Li - W * P| ≤ E * n * t := by
    calc
      _ = W * |P - Li| := by rw [← mul_sub, abs_mul, abs_of_nonneg hW, abs_sub_comm]
      _ ≤ W * (E * t) := mul_le_mul_of_nonneg_left hQ hW
      _ ≤ n * (E * t) := mul_le_mul_of_nonneg_right hρ' (mul_nonneg hE ht)
      _ = _ := by ring
  have htri₁ := abs_sub_le A F (W * P)
  have htri₂ := abs_sub_le F (W * Li) (W * P)
  change |A - W * P| ≤ _
  change |A - F| ≤ R at hcompare
  nlinarith

/-- The constants `64` and `4` in the displayed estimate (19) follow from the
stronger constants `32` and `2`, whenever all parameters are nonnegative. -/
theorem prime_root_average_bound {ι : Type*} (s : Finset ι)
    (w π D d : ι → ℝ) (A P Li C n Δ X : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hC : 0 ≤ C) (hn : 0 ≤ n) (hΔ : 0 ≤ Δ)
    (hX : 2 < X) (hρ : (∑ i ∈ s, w i) ≤ n)
    (hdegree : (∑ i ∈ s, w i * d i) ≤ n)
    (hdiscriminant : (∑ i ∈ s, w i * D i) ≤ n ^ 2 * Δ)
    (hlocal : ∀ i ∈ s,
      |π i - Li| ≤ C * X ^ ((31 : ℝ) / 32) * (32 * D i + d i * Real.log X))
    (hQ : |P - Li| ≤ C * X ^ ((31 : ℝ) / 32) * Real.log X)
    (hcompare : |A - ∑ i ∈ s, w i * π i| ≤
      2 * n * Real.sqrt X + 4 * n ^ 2 * Δ) :
    |A - (∑ i ∈ s, w i) * P| ≤
      C * X ^ ((31 : ℝ) / 32) * (64 * n ^ 2 * Δ + 4 * n * Real.log X) +
        2 * n * Real.sqrt X + 4 * n ^ 2 * Δ := by
  have hE : 0 ≤ C * X ^ ((31 : ℝ) / 32) := by positivity
  have ht : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have h := prime_root_average_strong s w π D d A P Li
    (C * X ^ ((31 : ℝ) / 32)) (Real.log X) n Δ
    (2 * n * Real.sqrt X + 4 * n ^ 2 * Δ)
    hw hE ht hρ hdegree hdiscriminant hlocal hQ hcompare
  refine h.trans ?_
  have hterm : 0 ≤ 32 * n ^ 2 * Δ + 2 * n * Real.log X := by positivity
  nlinarith [mul_nonneg hE hterm]

/-- Proposition 4.1 assembled from the local good-prime correspondence, the
exceptional-prime bound, higher-degree contributions for each number field, and
the individual analytic prime-ideal estimates. Here `π₁` counts degree-one prime
ideals, `a` is the root contribution at a rational prime, and `b` is the weighted
degree-one contribution. All number-theoretic inputs remain explicit. -/
theorem prime_root_average_of_exceptional_primes {κ ι : Type*} [DecidableEq κ]
    (primes bad : Finset κ) (s : Finset ι) (a b : κ → ℝ) (w π π₁ D d : ι → ℝ)
    (P Li C n Δ X : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hC : 0 ≤ C) (hn : 0 ≤ n) (hΔ : 0 ≤ Δ) (hX : 2 < X)
    (hρ : (∑ i ∈ s, w i) ≤ n)
    (hdegree : (∑ i ∈ s, w i * d i) ≤ n)
    (hdiscriminant : (∑ i ∈ s, w i * D i) ≤ n ^ 2 * Δ)
    (hgood : ∀ p ∈ primes, p ∉ bad → a p = b p)
    (ha : ∀ p ∈ primes, 0 ≤ a p ∧ a p ≤ 2 * n)
    (hb : ∀ p ∈ primes, 0 ≤ b p ∧ b p ≤ 2 * n)
    (hbad : (bad.card : ℝ) ≤ 2 * n * Δ)
    (hdegree_one : (∑ p ∈ primes, b p) = ∑ i ∈ s, w i * π₁ i)
    (hhigher_nonneg : ∀ i ∈ s, 0 ≤ π i - π₁ i)
    (hhigher : ∀ i ∈ s, π i - π₁ i ≤ d i * Real.sqrt X)
    (hlocal : ∀ i ∈ s,
      |π i - Li| ≤ C * X ^ ((31 : ℝ) / 32) * (32 * D i + d i * Real.log X))
    (hQ : |P - Li| ≤ C * X ^ ((31 : ℝ) / 32) * Real.log X) :
    |(∑ p ∈ primes, a p) - (∑ i ∈ s, w i) * P| ≤
      C * X ^ ((31 : ℝ) / 32) * (64 * n ^ 2 * Δ + 4 * n * Real.log X) +
        2 * n * Real.sqrt X + 4 * n ^ 2 * Δ := by
  have hbound (p : κ) (hp : p ∈ primes) : |a p - b p| ≤ 2 * n := by
    obtain ⟨ha₀, ha₁⟩ := ha p hp
    obtain ⟨hb₀, hb₁⟩ := hb p hp
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨hh₀, hh₁⟩ := weighted_higher_degree_bound s w π π₁ d n X hw hdegree
    hhigher_nonneg hhigher
  rw [← hdegree_one] at hh₀ hh₁
  have hcompare := prime_root_field_comparison primes bad a b
    (∑ i ∈ s, w i * π i) n Δ X hn hgood hbound hbad hh₀ hh₁
  exact prime_root_average_bound s w π D d (∑ p ∈ primes, a p) P Li C n Δ X
    hw hC hn hΔ hX hρ hdegree hdiscriminant hlocal hQ hcompare

end SparseIrred.UpperBounds
