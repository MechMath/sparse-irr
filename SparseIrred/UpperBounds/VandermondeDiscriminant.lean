import SparseIrred.UpperBounds.ExceptionalDiscriminant

/-!
# The discriminant root formula and unconditional exceptional-prime bounds

The resultant identity and the ordered product of root differences prove the Vandermonde
formula, including repeated roots and degree zero. The resulting estimates no longer require
the discriminant root identity or a root enumeration as additional inputs.
-/

namespace SparseIrred.UpperBounds

open Polynomial
open scoped BigOperators

/-- Evaluation of the derivative at an enumerated root removes exactly its indexed occurrence. -/
theorem complex_derivative_eval_root (f : ℂ[X]) (r : Fin f.natDegree → ℂ)
    (hroots : (List.ofFn r : Multiset ℂ) = f.roots) (i : Fin f.natDegree) :
    f.derivative.eval (r i) = f.leadingCoeff *
      ∏ j ∈ Finset.univ.erase i, (r i - r j) := by
  classical
  have hrootmem : r i ∈ f.roots := by rw [← hroots]; simp
  have heval : f.derivative.eval (r i) = f.leadingCoeff *
      ((f.roots.erase (r i)).map (r i - ·)).prod := by
    conv_lhs => rw [(IsAlgClosed.splits f).eq_prod_roots]
    rw [derivative_C_mul, eval_mul, eval_C, eval_multiset_prod_X_sub_C_derivative hrootmem]
  rw [heval]
  congr 1
  have henum : Finset.univ.val.map r = f.roots := by
    rw [← hroots]
    simp
  rw [← henum, ← Multiset.map_erase_of_mem r Finset.univ.val (Finset.mem_univ i)]
  simp [Finset.prod, Finset.erase_val, Multiset.map_map]

/-- Each unordered pair contributes one negative sign to the ordered root-difference product. -/
theorem complex_root_differences_prod {d : ℕ} (r : Fin d → ℂ) :
    ∏ i, ∏ j ∈ Finset.univ.erase i, (r i - r j) =
      (-1 : ℂ) ^ (d * (d - 1) / 2) * (Matrix.vandermonde r).det ^ 2 := by
  classical
  have hh := Finset.prod_prod_Ioi_mul_eq_prod_prod_off_diag
    (fun i j : Fin d ↦ r j - r i)
  simp only [Finset.compl_singleton] at hh
  rw [← hh]
  have hp : ∀ i j : Fin d, (r i - r j) * (r j - r i) =
      (-1 : ℂ) * (r j - r i) ^ 2 := by intros; ring
  simp_rw [hp, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]
  rw [Matrix.det_vandermonde, Finset.prod_pow_eq_pow_sum]
  congr 1
  congr 1
  simp_rw [Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range]
  have hpair : (∑ i ∈ Finset.range d, (d - 1 - i)) +
      ∑ i ∈ Finset.range d, i = d * (d - 1) := by
    calc
      _ = ∑ i ∈ Finset.range d, ((d - 1 - i) + i) := by rw [Finset.sum_add_distrib]
      _ = ∑ _ ∈ Finset.range d, (d - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [add_comm]
        exact add_tsub_cancel_of_le (Nat.le_sub_one_of_lt hi)
      _ = _ := by simp [Finset.sum_const]
  have hid := Finset.sum_range_id_mul_two d
  have hrev : (∑ i ∈ Finset.range d, (d - 1 - i)) =
      ∑ i ∈ Finset.range d, i := by omega
  rw [hrev, Finset.sum_range_id]

set_option linter.style.haveILetI false in
/-- The standard discriminant root formula holds for every complex polynomial. -/
theorem complex_discr_eq_vandermonde (f : ℂ[X]) (r : Fin f.natDegree → ℂ)
    (hroots : (List.ofFn r : Multiset ℂ) = f.roots) :
    f.discr = f.leadingCoeff ^ (2 * f.natDegree - 2) *
      (Matrix.vandermonde r).det ^ 2 := by
  classical
  by_cases hd : f.natDegree = 0
  · have hEmpty : IsEmpty (Fin f.natDegree) := by rw [hd]; infer_instance
    letI := hEmpty
    obtain ⟨a, ha⟩ := natDegree_eq_zero.mp hd
    rw [show f.discr = 1 by rw [← ha]; simp, show 2 * f.natDegree - 2 = 0 by omega]
    simp [Matrix.det_isEmpty]
  have hf : f ≠ 0 := by intro h; simp [h] at hd
  have hprod : (f.roots.map f.derivative.eval).prod = ∏ i, f.derivative.eval (r i) := by
    rw [← hroots]
    simp [Fin.prod_ofFn]
  have hres := resultant_eq_prod_eval f f.derivative (f.natDegree - 1)
    (natDegree_derivative_le f) (IsAlgClosed.splits f)
  rw [resultant_deriv (natDegree_pos_iff_degree_pos.mp (by omega)), hprod] at hres
  simp_rw [complex_derivative_eval_root f r hroots] at hres
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    complex_root_differences_prod] at hres
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  have hexp : f.leadingCoeff ^ (f.natDegree - 1) * f.leadingCoeff ^ f.natDegree =
      f.leadingCoeff * f.leadingCoeff ^ (2 * f.natDegree - 2) := by
    rw [← pow_add, ← pow_succ']
    congr 1
    omega
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) hlc)
  calc
    _ = f.leadingCoeff ^ (f.natDegree - 1) * (f.leadingCoeff ^ f.natDegree *
        ((-1 : ℂ) ^ (f.natDegree * (f.natDegree - 1) / 2) *
          (Matrix.vandermonde r).det ^ 2)) := hres
    _ = _ := by rw [← mul_assoc, hexp]; ring

/-- Hadamard's discriminant bound in terms of the actual polynomial Mahler measure. -/
theorem norm_discr_le_natDegree_pow_mul_mahlerMeasure (f : ℂ[X]) :
    ‖f.discr‖ ≤ (f.natDegree : ℝ) ^ f.natDegree *
      f.mahlerMeasure ^ (2 * f.natDegree - 2) := by
  obtain ⟨r, hr⟩ := exists_complex_root_enumeration f
  exact norm_discr_le_of_vandermonde_formula f r hr (complex_discr_eq_vandermonde f r hr)

/-- The scaled discriminant bound follows from a Mahler bound without a root-formula premise. -/
theorem scaled_discriminant_norm_le_of_mahlerMeasure (f : ℂ[X]) (S : ℝ)
    (hM : f.mahlerMeasure ≤ S) :
    ‖f.leadingCoeff‖ ^ ((f.natDegree - 1) * (f.natDegree - 2)) * ‖f.discr‖ ≤
      (f.natDegree : ℝ) ^ f.natDegree * S ^ (f.natDegree * (f.natDegree - 1)) := by
  obtain ⟨r, hr⟩ := exists_complex_root_enumeration f
  exact scaled_discriminant_norm_le f r S hr (complex_discr_eq_vandermonde f r hr) hM

/-- An order-to-field discriminant comparison gives the logarithmic field bound. -/
theorem log_field_discriminant_le_of_order_bound (f : ℂ[X]) (S D : ℝ)
    (hdegree : 1 ≤ f.natDegree) (hS : 1 ≤ S) (hD : 0 < D)
    (hM : f.mahlerMeasure ≤ S)
    (horder : D ≤ ‖f.leadingCoeff‖ ^ ((f.natDegree - 1) * (f.natDegree - 2)) *
      ‖f.discr‖) :
    Real.log D ≤ f.natDegree * Real.log (f.natDegree : ℝ) +
      f.natDegree * (f.natDegree - 1 : ℕ) * Real.log S := by
  obtain ⟨r, hr⟩ := exists_complex_root_enumeration f
  exact log_field_discriminant_le f r S D hdegree hS hD hr
    (complex_discr_eq_vandermonde f r hr) hM horder

/-- The exceptional integer satisfies the real size bound from its Mahler measure. -/
theorem integer_exceptional_norm_le_of_mahlerMeasure (f : ℤ[X]) (S : ℝ)
    (hd : 1 ≤ f.natDegree) (hM : f.mapMahlerMeasure (Int.castRingHom ℂ) ≤ S) :
    ((f.leadingCoeff * f.discr).natAbs : ℝ) ≤
      (f.natDegree : ℝ) ^ f.natDegree * S ^ (2 * f.natDegree - 1) := by
  obtain ⟨r, hr⟩ := exists_complex_root_enumeration (f.map (Int.castRingHom ℂ))
  have hdeg : (f.map (Int.castRingHom ℂ)).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective Int.cast_injective f
  apply integer_exceptional_norm_le f S hd r hr _ hM
  simpa only [hdeg] using complex_discr_eq_vandermonde (f.map (Int.castRingHom ℂ)) r hr

/-- The natural-number exceptional-integer size bound needs no root-formula premise. -/
theorem exceptionalInteger_natAbs_le_of_mahlerMeasure (F : ℤ[X]) (S : ℕ)
    (hdegree : 1 ≤ F.natDegree) (hM : F.mapMahlerMeasure (Int.castRingHom ℂ) ≤ S) :
    (exceptionalInteger F).natAbs ≤ F.natDegree ^ F.natDegree * S ^ (2 * F.natDegree - 1) := by
  exact_mod_cast integer_exceptional_norm_le_of_mahlerMeasure F S hdegree hM

/-- Every positive-degree integer divisor has the required exceptional-integer size bound. -/
theorem exceptionalInteger_le_pow_inputDelta_of_dvd (f F : ℤ[X]) (hf : f ≠ 0) (hFf : F ∣ f)
    (hdegree : 1 ≤ F.natDegree) :
    (exceptionalInteger F).natAbs ≤ 2 ^ (2 * f.natDegree * inputDelta f) := by
  apply exceptional_size_le_inputDelta f F.natDegree _ (natDegree_le_of_dvd hFf hf)
  apply exceptionalInteger_natAbs_le_of_mahlerMeasure F (integerL1 f) hdegree
  exact (integerMahler_le_of_dvd f F hf hFf).trans (integerMahler_le_integerL1 f)

/-- A separable integer divisor has the exceptional-prime bound without algebraic inputs. -/
theorem exceptionalInteger_primeFactors_card_le_of_dvd (f F : ℤ[X]) (hf : f ≠ 0)
    (hFf : F ∣ f) (hdegree : 1 ≤ F.natDegree)
    (hsep : (F.map (Int.castRingHom ℂ)).Separable) :
    (exceptionalInteger F).natAbs.primeFactors.card ≤ 2 * f.natDegree * inputDelta f := by
  apply exceptional_prime_card_bound _ (exceptionalInteger_ne_zero F hsep)
  exact exceptionalInteger_le_pow_inputDelta_of_dvd f F hf hFf hdegree

end SparseIrred.UpperBounds
