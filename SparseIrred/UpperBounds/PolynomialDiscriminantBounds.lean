import Mathlib
import SparseIrred.UpperBounds.ExceptionalPrimeCount
import SparseIrred.UpperBounds.IntegerMahlerBounds
import SparseIrred.UpperBounds.WeightedDiscriminantBounds

/-!
# Vandermonde and polynomial discriminant bounds

This file proves the norm estimates used in the discriminant argument of Lemma 3.1
of the independent prime-counting manuscript.
-/

namespace SparseIrred.UpperBounds

open scoped BigOperators
open Polynomial

/-- Every complex polynomial admits a finite enumeration of all its roots,
with their multiplicities and with precisely its natural degree many entries. -/
theorem exists_complex_root_enumeration (f : ℂ[X]) :
    ∃ r : Fin f.natDegree → ℂ, (List.ofFn r : Multiset ℂ) = f.roots := by
  have hl : f.roots.toList.length = f.natDegree := by
    rw [Multiset.length_toList, ← (IsAlgClosed.splits f).natDegree_eq_card_roots]
  refine ⟨fun i ↦ f.roots.toList.get (Fin.cast hl.symm i), ?_⟩
  rw [← List.ofFn_congr hl f.roots.toList.get, List.ofFn_get]
  exact Multiset.coe_toList _

/-- Hadamard's inequality for the determinant relative to an orthonormal basis. -/
theorem orthonormal_det_norm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {d : ℕ}
    (b : OrthonormalBasis (Fin d) ℂ E) (f : Fin d → E) :
    ‖b.toBasis.det f‖ ≤ ∏ i, ‖f i‖ := by
  classical
  let h := Module.finrank_eq_card_basis b.toBasis
  let a := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  have hdet : b.toBasis.det f = b.toBasis.det a * a.toBasis.det f := by
    have hmap := congrArg (fun g : E [⋀^Fin d]→ₗ[ℂ] ℂ ↦ g f)
      (b.toBasis.det.eq_smul_basis_det a.toBasis)
    simpa using hmap
  rw [hdet, norm_mul, b.det_to_matrix_orthonormalBasis a, one_mul]
  change ‖(InnerProductSpace.gramSchmidtOrthonormalBasis h f).toBasis.det f‖ ≤ _
  rw [InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  apply Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _)
  intro i _
  exact (norm_inner_le_norm _ _).trans_eq (by rw [OrthonormalBasis.norm_eq_one, one_mul])

/-- The Euclidean squared norm of a Vandermonde row has the bound used in Hadamard. -/
theorem vandermonde_row_norm_sq_le (d : ℕ) (α : ℂ) :
    ‖(WithLp.toLp 2 (fun j : Fin d ↦ α ^ (j : ℕ)) : EuclideanSpace ℂ (Fin d))‖ ^ 2 ≤
      d * (max 1 ‖α‖) ^ (2 * d - 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  have hpow : ∀ j : Fin d, ‖α ^ (j : ℕ)‖ ^ 2 ≤ (max 1 ‖α‖) ^ (2 * d - 2) := by
    intro j
    rw [norm_pow, ← pow_mul]
    calc
      ‖α‖ ^ ((j : ℕ) * 2) ≤ (max 1 ‖α‖) ^ ((j : ℕ) * 2) :=
        pow_le_pow_left₀ (norm_nonneg α) (le_max_right _ _) _
      _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) (by omega)
  calc
    ∑ j : Fin d, ‖α ^ (j : ℕ)‖ ^ 2 ≤ ∑ _ : Fin d, (max 1 ‖α‖) ^ (2 * d - 2) :=
      Finset.sum_le_sum (fun j _ ↦ hpow j)
    _ = _ := by simp

/-- Hadamard's inequality and the row estimates give the sharp degree constant
in the squared Vandermonde determinant bound. -/
theorem vandermonde_det_norm_sq_le {d : ℕ} (r : Fin d → ℂ) :
    ‖(Matrix.vandermonde r).det‖ ^ 2 ≤
      (d : ℝ) ^ d * (∏ i, max 1 ‖r i‖) ^ (2 * d - 2) := by
  let b := EuclideanSpace.basisFun (Fin d) ℂ
  let f : Fin d → EuclideanSpace ℂ (Fin d) :=
    fun i ↦ WithLp.toLp 2 (fun j ↦ r i ^ (j : ℕ))
  have hmat : b.toBasis.toMatrix f = (Matrix.vandermonde r).transpose := by
    ext i j
    rfl
  have hhad := orthonormal_det_norm_le b f
  rw [Module.Basis.det_apply, hmat, Matrix.det_transpose] at hhad
  have hsquared := pow_le_pow_left₀ (norm_nonneg _) hhad 2
  rw [← Finset.prod_pow] at hsquared
  calc
    ‖(Matrix.vandermonde r).det‖ ^ 2 ≤ ∏ i, ‖f i‖ ^ 2 := hsquared
    _ ≤ ∏ i, (d : ℝ) * (max 1 ‖r i‖) ^ (2 * d - 2) := by
      apply Finset.prod_le_prod (fun i _ ↦ sq_nonneg _)
      intro i _
      exact vandermonde_row_norm_sq_le d (r i)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Finset.prod_pow]

/-- The polynomial discriminant bound follows from the standard root formula.
The root formula is an explicit algebraic input; neither Hadamard's inequality nor
the claimed discriminant bound is assumed. -/
theorem norm_discr_le_of_vandermonde_formula (f : ℂ[X]) (r : Fin f.natDegree → ℂ)
    (hroots : (List.ofFn r : Multiset ℂ) = f.roots)
    (hformula : f.discr = f.leadingCoeff ^ (2 * f.natDegree - 2) *
      (Matrix.vandermonde r).det ^ 2) :
    ‖f.discr‖ ≤ (f.natDegree : ℝ) ^ f.natDegree *
      f.mahlerMeasure ^ (2 * f.natDegree - 2) := by
  have hprod : (∏ i, max 1 ‖r i‖) = (f.roots.map (fun z ↦ max 1 ‖z‖)).prod := by
    rw [← hroots]
    simp [Fin.prod_ofFn]
  rw [hformula, norm_mul, norm_pow, norm_pow]
  calc
    _ ≤ ‖f.leadingCoeff‖ ^ (2 * f.natDegree - 2) *
        ((f.natDegree : ℝ) ^ f.natDegree * (∏ i, max 1 ‖r i‖) ^
          (2 * f.natDegree - 2)) :=
      mul_le_mul_of_nonneg_left (vandermonde_det_norm_sq_le r) (by positivity)
    _ = (f.natDegree : ℝ) ^ f.natDegree *
        (‖f.leadingCoeff‖ * (∏ i, max 1 ‖r i‖)) ^ (2 * f.natDegree - 2) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hprod, ← Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots]

/-- The exponents from nonmonic scaling and the Vandermonde bound combine exactly. -/
theorem discriminant_scaling_exponents (d : ℕ) :
    (d - 1) * (d - 2) + (2 * d - 2) = d * (d - 1) := by
  rcases d with _ | (_ | d)
  · norm_num
  · norm_num
  · rw [show d + 1 + 1 - 1 = d + 1 by omega, show d + 1 + 1 - 2 = d by omega,
      show 2 * (d + 1 + 1) - 2 = 2 * d + 2 by omega]
    ring

/-- Scaling the nonmonic polynomial contributes exactly the additional powers
needed in the number-field discriminant estimate. -/
theorem scaled_discriminant_norm_le (f : ℂ[X]) (r : Fin f.natDegree → ℂ) (S : ℝ)
    (hroots : (List.ofFn r : Multiset ℂ) = f.roots)
    (hformula : f.discr = f.leadingCoeff ^ (2 * f.natDegree - 2) *
      (Matrix.vandermonde r).det ^ 2)
    (hM : f.mahlerMeasure ≤ S) :
    ‖f.leadingCoeff‖ ^ ((f.natDegree - 1) * (f.natDegree - 2)) * ‖f.discr‖ ≤
      (f.natDegree : ℝ) ^ f.natDegree * S ^ (f.natDegree * (f.natDegree - 1)) := by
  have hS0 : 0 ≤ S := f.mahlerMeasure_nonneg.trans hM
  have hlc : ‖f.leadingCoeff‖ ≤ S := f.leadingCoeff_le_mahlerMeasure.trans hM
  have hpowM := pow_le_pow_left₀ f.mahlerMeasure_nonneg hM (2 * f.natDegree - 2)
  have hdisc : ‖f.discr‖ ≤
      (f.natDegree : ℝ) ^ f.natDegree * S ^ (2 * f.natDegree - 2) :=
    (norm_discr_le_of_vandermonde_formula f r hroots hformula).trans
      (mul_le_mul_of_nonneg_left hpowM (by positivity))
  calc
    _ ≤ S ^ ((f.natDegree - 1) * (f.natDegree - 2)) *
        ((f.natDegree : ℝ) ^ f.natDegree * S ^ (2 * f.natDegree - 2)) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hlc _) hdisc
        (norm_nonneg _) (by positivity)
    _ = (f.natDegree : ℝ) ^ f.natDegree *
        S ^ ((f.natDegree - 1) * (f.natDegree - 2) + (2 * f.natDegree - 2)) := by
      rw [pow_add]
      ring
    _ = _ := by rw [discriminant_scaling_exponents]

/-- Once the standard order/field discriminant comparison is supplied, the
nonmonic field-discriminant logarithmic estimate is a consequence of the proved
Vandermonde bound. The comparison and root identity are explicit algebraic inputs. -/
theorem log_field_discriminant_le (f : ℂ[X]) (r : Fin f.natDegree → ℂ) (S D : ℝ)
    (hdegree : 1 ≤ f.natDegree) (hS : 1 ≤ S) (hD : 0 < D)
    (hroots : (List.ofFn r : Multiset ℂ) = f.roots)
    (hformula : f.discr = f.leadingCoeff ^ (2 * f.natDegree - 2) *
      (Matrix.vandermonde r).det ^ 2)
    (hM : f.mahlerMeasure ≤ S)
    (horder : D ≤ ‖f.leadingCoeff‖ ^ ((f.natDegree - 1) * (f.natDegree - 2)) *
      ‖f.discr‖) :
    Real.log D ≤ f.natDegree * Real.log (f.natDegree : ℝ) +
      f.natDegree * (f.natDegree - 1 : ℕ) * Real.log S := by
  have hd0 : (0 : ℝ) < f.natDegree := by exact_mod_cast (by omega : 0 < f.natDegree)
  have hS0 : 0 < S := by linarith
  have hbound := horder.trans (scaled_discriminant_norm_le f r S hroots hformula hM)
  have hlog := Real.log_le_log hD hbound
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  simpa only [Nat.cast_mul] using hlog

/-- The integer polynomial discriminant is unchanged by embedding its coefficients
in the complex numbers. This is deduced from the resultant identity, including constants. -/
theorem integer_discr_map_complex (f : ℤ[X]) :
    (f.discr : ℂ) = (f.map (Int.castRingHom ℂ)).discr := by
  let φ := Int.castRingHom ℂ
  have hinj : Function.Injective φ := Int.cast_injective
  have hd : (f.map φ).natDegree = f.natDegree := natDegree_map_eq_of_injective hinj f
  by_cases hf0 : f.natDegree = 0
  · obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp hf0
    simp only [Polynomial.map_C, Polynomial.discr_C, Int.cast_one]
  have hf : f ≠ 0 := by intro h; simp [h] at hf0
  have hs := congrArg φ (resultant_deriv
    (natDegree_pos_iff_degree_pos.mp (by omega : 0 < f.natDegree)))
  have ht := resultant_deriv
    (natDegree_pos_iff_degree_pos.mp (by omega : 0 < (f.map φ).natDegree))
  rw [derivative_map, hd, resultant_map_map] at ht
  rw [leadingCoeff_map_of_injective hinj] at ht
  have he : φ ((-1 : ℤ) ^ (f.natDegree * (f.natDegree - 1) / 2)) *
      φ f.leadingCoeff ≠ 0 := by
    apply mul_ne_zero (by simp [φ])
    simpa only [map_zero] using hinj.ne (leadingCoeff_ne_zero.mpr hf)
  apply mul_left_cancel₀ he
  simpa [φ] using hs.symm.trans ht

/-- The actual exceptional integer `Z = lc(f) * Disc(f)` has the size bound
used in Lemma 3.1, derived from the Vandermonde estimate and Mahler measure. -/
theorem integer_exceptional_norm_le (f : ℤ[X]) (S : ℝ) (hd : 1 ≤ f.natDegree)
    (r : Fin (f.map (Int.castRingHom ℂ)).natDegree → ℂ)
    (hroots : (List.ofFn r : Multiset ℂ) = (f.map (Int.castRingHom ℂ)).roots)
    (hformula : (f.map (Int.castRingHom ℂ)).discr =
      (f.map (Int.castRingHom ℂ)).leadingCoeff ^ (2 * f.natDegree - 2) *
        (Matrix.vandermonde r).det ^ 2)
    (hM : f.mapMahlerMeasure (Int.castRingHom ℂ) ≤ S) :
    ((f.leadingCoeff * f.discr).natAbs : ℝ) ≤
      (f.natDegree : ℝ) ^ f.natDegree * S ^ (2 * f.natDegree - 1) := by
  let g := f.map (Int.castRingHom ℂ)
  have hgd : g.natDegree = f.natDegree :=
    natDegree_map_eq_of_injective Int.cast_injective f
  have hM' : g.mahlerMeasure ≤ S := hM
  have hS0 : 0 ≤ S := g.mahlerMeasure_nonneg.trans hM'
  have hformula' : g.discr = g.leadingCoeff ^ (2 * g.natDegree - 2) *
      (Matrix.vandermonde r).det ^ 2 := by simpa only [hgd] using hformula
  have hdisc : ‖g.discr‖ ≤
      (f.natDegree : ℝ) ^ f.natDegree * S ^ (2 * f.natDegree - 2) := by
    have hb := norm_discr_le_of_vandermonde_formula g r hroots hformula'
    rw [hgd] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ g.mahlerMeasure_nonneg hM' _) (by positivity))
  have hZ : ((f.leadingCoeff * f.discr).natAbs : ℝ) =
      ‖g.leadingCoeff‖ * ‖g.discr‖ := by
    dsimp [g]
    rw [leadingCoeff_map_of_injective Int.cast_injective, ← integer_discr_map_complex]
    change ((f.leadingCoeff * f.discr).natAbs : ℝ) =
      ‖(f.leadingCoeff : ℂ)‖ * ‖(f.discr : ℂ)‖
    rw [← norm_mul, ← Int.cast_mul, Complex.norm_intCast, ← Int.cast_abs,
      Int.abs_eq_natAbs, Int.cast_natCast]
  rw [hZ]
  calc
    _ ≤ S * ((f.natDegree : ℝ) ^ f.natDegree * S ^ (2 * f.natDegree - 2)) :=
      mul_le_mul (g.leadingCoeff_le_mahlerMeasure.trans hM') hdisc
        (norm_nonneg _) hS0
    _ = (f.natDegree : ℝ) ^ f.natDegree * S ^ (2 * f.natDegree - 1) := by
      rw [show 2 * f.natDegree - 1 = (2 * f.natDegree - 2) + 1 by omega, pow_succ]
      ring

end SparseIrred.UpperBounds
