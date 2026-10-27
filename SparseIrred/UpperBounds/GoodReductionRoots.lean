import SparseIrred.UpperBounds.ModularRoots
import Mathlib.FieldTheory.Separable

/-!
# The weighted local root identity

Equation (34) of Section 3.2, for any finite family whose reductions are pairwise
coprime and separable. The hypotheses describe good reduction; this file does not
claim a bound on the exceptional rational primes.
-/

open Polynomial
open scoped BigOperators

namespace SparseIrred.UpperBounds

private theorem eval_ne_zero_of_coprime_root {K : Type*} [Field K] {f g : K[X]}
    (h : IsCoprime f g) {a : K} (ha : f.eval a = 0) : g.eval a ≠ 0 := by
  intro hg
  obtain ⟨u, v, huv⟩ := h
  have := congrArg (Polynomial.eval a) huv
  simp [ha, hg] at this

/-- A root of one factor belongs to the product, and the derivative detects exactly
the factors of multiplicity one. -/
theorem factor_product_root_derivative {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (h : ι → K[X]) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise fun i j ↦ IsCoprime (h i) (h j))
    (hsep : ∀ i, (h i).Separable) (i : ι) (a : K) (ha : (h i).eval a = 0) :
    (∏ j, h j ^ m j).eval a = 0 ∧
      ((∏ j, h j ^ m j).derivative.eval a ≠ 0 ↔ m i = 1) := by
  have hprod : ∏ j, h j ^ m j =
      h i ^ m i * ∏ j ∈ Finset.univ.erase i, h j ^ m j :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hrest : (∏ j ∈ Finset.univ.erase i, h j ^ m j).eval a ≠ 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    rw [Polynomial.eval_pow]
    apply pow_ne_zero
    exact eval_ne_zero_of_coprime_root (hcop (Finset.mem_erase.mp hj).1.symm) ha
  have hd : (h i).derivative.eval a ≠ 0 := by
    simpa only [Polynomial.eval₂_id] using (hsep i).eval₂_derivative_ne_zero (RingHom.id K) ha
  rw [hprod]
  refine ⟨by simp [ha, (hm i).ne'], ?_⟩
  exact derivative_at_factor_root _ _ a ha hd hrest _ (hm i)

/-- The pointwise identity underlying the sum of the two root counts. -/
theorem weighted_root_indicator {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    [DecidableEq K] (h : ι → K[X]) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise fun i j ↦ IsCoprime (h i) (h j))
    (hsep : ∀ i, (h i).Separable) (a : K) :
    (if (∏ i, h i ^ m i).eval a = 0 then 1 else 0) +
      (if (∏ i, h i ^ m i).eval a = 0 ∧
        (∏ i, h i ^ m i).derivative.eval a = 0 then 1 else 0) =
      ∑ i, (1 + if 2 ≤ m i then 1 else 0) * (if (h i).eval a = 0 then 1 else 0) := by
  classical
  by_cases hz : (∏ i, h i ^ m i).eval a = 0
  · have hz' : ∏ i, (h i).eval a ^ m i = 0 := by
      simpa only [Polynomial.eval_prod, Polynomial.eval_pow] using hz
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz'
    have hi0 : (h i).eval a = 0 := eq_zero_of_pow_eq_zero hi
    have hd := (factor_product_root_derivative h m hm hcop hsep i a hi0).2
    have hother : ∀ j, j ≠ i → (h j).eval a ≠ 0 := by
      intro j hji
      exact eval_ne_zero_of_coprime_root (hcop hji.symm) hi0
    rw [Finset.sum_eq_single i]
    · by_cases hm1 : m i = 1
      · have hdn := hd.mpr hm1
        simp [hz, hi0, hdn, hm1]
      · have hd0 : (∏ j, h j ^ m j).derivative.eval a = 0 := not_ne_iff.mp (hd.not.mpr hm1)
        have hm2 : 2 ≤ m i := by have := hm i; omega
        simp [hz, hi0, hd0, hm2]
    · intro j _ hji
      simp [hother j hji]
    · simp
  · have hn : ∀ i, (h i).eval a ≠ 0 := by
      intro i hi
      exact hz (factor_product_root_derivative h m hm hcop hsep i a hi).1
    simp [hz, hn]

/-- Equation (34). The weight is two for every multiplicity at least two, including
multiplicities divisible by the characteristic. -/
theorem weighted_root_count {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [DecidableEq ι] (h : ι → K[X]) (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise fun i j ↦ IsCoprime (h i) (h j))
    (hsep : ∀ i, (h i).Separable) :
    rootCount (∏ i, h i ^ m i) + multipleRootCount (∏ i, h i ^ m i) =
      ∑ i, (1 + if 2 ≤ m i then 1 else 0) * rootCount (h i) := by
  classical
  simp only [rootCount, multipleRootCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  simp_rw [weighted_root_indicator h m hm hcop hsep]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact (Finset.mul_sum _ _ _).symm

end SparseIrred.UpperBounds
